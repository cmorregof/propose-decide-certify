"""Libro de gastos: costo real de cada llamada a la API y topes que abortan antes de pasarse (PLAN_rl_verbal.md §9).

Contabiliza los proveedores OpenAI y, desde el 17 oct 2026, Anthropic (Claude Sonnet 5.5 y Opus 5.5).
Cada llamada se registra con los tokens que devuelve la API (entrada, entrada en caché, salida y razonamiento) y
su costo con los precios oficiales. Antes de cada llamada, `autorizar` exige que el total gastado más el peor caso
de la llamada siguiente (entrada estimada + máximo de salida) no pase del tope en dólares, y que la fase no haya
agotado su tope de llamadas. Si no, lanza GastoExcedido, que aborta la corrida (no se registra como PROVIDER_ERROR).
El libro persiste en logs/gasto.json: el tope es para todo el proyecto, no por corrida.
"""

from __future__ import annotations

import contextlib
import fcntl
import json
import os
import tempfile
import threading
import time
from pathlib import Path

from .loop import ProviderFatal, Rechazo

BASE = Path(__file__).resolve().parent.parent
# El libro por defecto es el del proyecto. Una ronda puede usar un libro propio con la variable UNIRL_LIBRO (p. ej.
# logs/gasto_ronda_<fecha>.json), que arranca en cero y deja intacto el histórico (26 sep 2026, lanzar_ronda.sh).
LIBRO = Path(os.environ["UNIRL_LIBRO"]) if os.environ.get("UNIRL_LIBRO") else BASE / "logs" / "gasto.json"

# USD por millón de tokens: (entrada, entrada en caché, salida). Página de precios de OpenAI, consultada el 24 sep 2026.
PRECIOS = {
    "gpt-6-luna": (0.10, 0.01, 0.50),
    "gpt-6-sol": (2.00, 0.20, 10.00),
    "gpt-6-astra": (10.00, 1.00, 50.00),
    "gpt-5.6-terra": (2.00, 0.20, 12.00),
    # Claude: https://platform.claude.com/docs/en/about-claude/pricing, consultada el 17 oct 2026. La entrada en caché
    # es la lectura; el razonamiento (thinking) se cobra como salida y ya viene en output_tokens.
    "claude-sonnet-5-5": (2.00, 0.10, 10.00),
    "claude-opus-5-5": (4.00, 0.20, 20.00),
}
RECARGO_ESCRITURA_CACHE = 1.25  # Anthropic: escribir en la caché de 5 min cuesta 1,25 veces la entrada base
TOPE_USD = float(os.environ.get("UNIRL_TOPE_USD", 25.0))  # decisión de Carlos (24 sep 2026): 25; la ronda del 26 sep lo baja con UNIRL_TOPE_USD


def topes_fase_usd() -> dict[str, float]:
    """Topes duros en dólares por fase, de la variable UNIRL_TOPES_FASE_USD (JSON {fase: usd}). Vacío si no está."""
    raw = os.environ.get("UNIRL_TOPES_FASE_USD")
    return {str(k): float(v) for k, v in json.loads(raw).items()} if raw else {}


class GastoExcedido(ProviderFatal):
    """La llamada siguiente podría pasar del tope en dólares, o la fase agotó su tope de llamadas."""


def costo(modelo: str, tokens_entrada: int, tokens_cache: int, tokens_salida: int, tokens_escritura_cache: int = 0) -> float:
    """`tokens_entrada` es la entrada total; de ella, `tokens_cache` se leyó de la caché y `tokens_escritura_cache` se
    escribió en ella (solo Anthropic; OpenAI no cobra la escritura)."""
    if modelo not in PRECIOS:
        raise GastoExcedido(f"sin precio registrado para {modelo}: no se autoriza la llamada")
    pe, pc, ps = PRECIOS[modelo]
    base = tokens_entrada - tokens_cache - tokens_escritura_cache
    return (base * pe + tokens_cache * pc + tokens_escritura_cache * pe * RECARGO_ESCRITURA_CACHE + tokens_salida * ps) / 1e6


class _CerrojoLibro:
    """Candado de hilos y de procesos (archivo) para el libro: dos corridas en terminales distintas no se pisan."""
    _hilos = threading.Lock()

    def __init__(self, ruta: Path):
        self.ruta = Path(str(ruta) + ".lock")

    @contextlib.contextmanager
    def __call__(self):
        with self._hilos:
            self.ruta.parent.mkdir(parents=True, exist_ok=True)
            with open(self.ruta, "w") as fh:
                fcntl.flock(fh, fcntl.LOCK_EX)
                try:
                    yield
                finally:
                    fcntl.flock(fh, fcntl.LOCK_UN)


class Libro:

    def __init__(self, ruta: Path | None = None, tope_usd: float = TOPE_USD, topes_fase: dict[str, float] | None = None):
        self.ruta = Path(ruta) if ruta else LIBRO
        self.tope_usd = float(tope_usd)
        self.topes_fase = dict(topes_fase) if topes_fase is not None else topes_fase_usd()
        self._cerrojo = _CerrojoLibro(self.ruta)

    def entradas(self) -> list[dict]:
        if not self.ruta.exists():
            return []
        return json.loads(self.ruta.read_text(encoding="utf-8")).get("llamadas", [])

    def total(self) -> float:
        return round(sum(e["usd"] for e in self.entradas()), 6)

    def llamadas(self, fase: str) -> int:
        return sum(1 for e in self.entradas() if e.get("fase") == fase)

    def gastado(self, fase: str) -> float:
        return round(sum(e["usd"] for e in self.entradas() if e.get("fase") == fase), 6)

    def autorizar(self, modelo: str, fase: str, tope_llamadas: int | None, chars_entrada: int, max_salida: int) -> float:
        """Peor caso de la llamada siguiente; GastoExcedido si con él se pasa del tope o la fase agotó sus llamadas."""
        peor = costo(modelo, chars_entrada // 3 + 1, 0, max_salida)
        with self._cerrojo():
            gastado = self.total()
            if gastado + peor > self.tope_usd:
                raise GastoExcedido(f"tope de ${self.tope_usd:.2f}: gastado ${gastado:.4f}, la llamada siguiente puede costar hasta ${peor:.4f}")
            if tope_llamadas is not None and self.llamadas(fase) >= tope_llamadas:
                raise GastoExcedido(f"la fase {fase!r} agotó su tope de {tope_llamadas} llamadas")
            tope_fase = self.topes_fase.get(fase)
            if tope_fase is not None and self.gastado(fase) + peor > tope_fase:
                raise GastoExcedido(f"tope de la fase {fase!r} (${tope_fase:.2f}): gastado ${self.gastado(fase):.4f}, "
                                    f"la llamada siguiente puede costar hasta ${peor:.4f}")
        return peor

    def registrar(self, modelo: str, fase: str, corrida: str, uso: dict) -> float:
        usd = costo(modelo, uso.get("entrada", 0), uso.get("cache", 0), uso.get("salida", 0), uso.get("cache_escritura", 0))
        with self._cerrojo():
            datos = {"llamadas": self.entradas()}
            datos["llamadas"].append({"fecha": time.strftime("%Y-%m-%dT%H:%M:%S"), "modelo": modelo, "fase": fase, "corrida": corrida,
                                      **uso, "usd": round(usd, 6)})
            datos["total_usd"] = round(sum(e["usd"] for e in datos["llamadas"]), 6)
            datos["tope_usd"] = self.tope_usd
            self.ruta.parent.mkdir(parents=True, exist_ok=True)
            fd, tmp = tempfile.mkstemp(dir=str(self.ruta.parent), prefix=".gasto-")
            with os.fdopen(fd, "w", encoding="utf-8") as fh:
                json.dump(datos, fh, ensure_ascii=False, indent=1)
            os.replace(tmp, self.ruta)  # escritura atómica: dos corridas en paralelo no corrompen el libro
        return usd


class ProveedorContable:
    """Envuelve el proveedor OpenAI del 06 (sin modificarlo) o el de Anthropic de steprl: hace la misma llamada, lee
    `usage` y la registra en el libro, autorizando antes cada llamada contra los topes."""

    def __init__(self, interno, libro: Libro, fase: str, corrida: str, tope_llamadas: int | None = None):
        # Anthropic (17 oct 2026): el proveedor de steprl expone `respuesta` (la llamada cruda, con usage) y `texto`
        self._anthropic = callable(getattr(interno, "respuesta", None)) and callable(getattr(interno, "texto", None))
        if not self._anthropic and not hasattr(interno, "_client"):
            raise GastoExcedido("el libro de gastos solo sabe contabilizar los proveedores OpenAI y Anthropic")
        self.interno, self.libro, self.fase, self.corrida, self.tope_llamadas = interno, libro, fase, corrida, tope_llamadas
        self.model = interno.model
        self.calls = 0
        self._local = threading.local()  # uso de la última llamada, por hilo (episodios en paralelo)

    def _ajustes(self) -> dict:
        """El esfuerzo y la temperatura de la llamada, fijos por corrida, para el libro y el registro del intento.
        La temperatura no se envía (None = la de la API por omisión): Opus 5.5 no admite el parámetro, Sonnet 5.5 solo
        su valor por omisión, y los modelos de razonamiento de OpenAI no la usan."""
        effort = getattr(self.interno, "effort", None) if self._anthropic else getattr(self.interno, "reasoning_effort", None)
        return {"effort": effort, "temperatura": None}

    def _complete_anthropic(self, system: str, user: str) -> str:
        resp = self.interno.respuesta(system, user)  # los errores del SDK suben tal cual: loop.clasificar_error los lee
        u = resp.usage
        lectura = int(getattr(u, "cache_read_input_tokens", 0) or 0)
        escritura = int(getattr(u, "cache_creation_input_tokens", 0) or 0)
        det = getattr(u, "output_tokens_details", None)
        uso = {"entrada": int(u.input_tokens or 0) + lectura + escritura, "cache": lectura, "cache_escritura": escritura,
               "salida": int(u.output_tokens or 0), "razonamiento": int(getattr(det, "thinking_tokens", 0) or 0),
               **self._ajustes()}
        usd = self.libro.registrar(self.model, self.fase, self.corrida, uso)  # se registra aunque la respuesta sea inútil: se pagó
        self.calls += 1
        self._local.uso = {**uso, "usd": round(usd, 6)}
        if resp.stop_reason == "refusal":  # el intento cuenta como fallido (REFUSAL), sin reintento ni fallback
            raise Rechazo(getattr(getattr(resp, "stop_details", None), "category", None))
        if resp.stop_reason == "max_tokens":  # como con OpenAI: un texto cortado puede traer la prueba entera
            text = "".join(b.text for b in resp.content if b.type == "text")
            if not text.strip():
                raise RuntimeError("la respuesta se cortó por longitud")
            return text
        return self.interno.texto(resp)

    def complete(self, system: str, user: str) -> str:
        max_salida = int(getattr(self.interno, "max_output_tokens", 64000))
        self.libro.autorizar(self.model, self.fase, self.tope_llamadas, len(system) + len(user), max_salida)
        if self._anthropic:
            return self._complete_anthropic(system, user)
        kwargs = {}
        if getattr(self.interno, "reasoning_effort", None):
            kwargs["reasoning_effort"] = self.interno.reasoning_effort
        resp = self.interno._client.chat.completions.create(
            model=self.model, messages=[{"role": "system", "content": system}, {"role": "user", "content": user}],
            max_completion_tokens=max_salida, **kwargs)
        u = resp.usage
        det_e, det_s = getattr(u, "prompt_tokens_details", None), getattr(u, "completion_tokens_details", None)
        uso = {"entrada": int(u.prompt_tokens or 0), "cache": int(getattr(det_e, "cached_tokens", 0) or 0),
               "salida": int(u.completion_tokens or 0), "razonamiento": int(getattr(det_s, "reasoning_tokens", 0) or 0),
               **self._ajustes()}
        usd = self.libro.registrar(self.model, self.fase, self.corrida, uso)  # se registra aunque la respuesta sea inútil: se pagó
        self.calls += 1
        self._local.uso = {**uso, "usd": round(usd, 6)}  # el episodio lo copia en el registro de cada llamada
        choice = resp.choices[0]
        text = choice.message.content or ""
        if choice.finish_reason == "length" and not text.strip():
            raise RuntimeError("la respuesta se cortó por longitud")
        return text

    @property
    def ultimo_uso(self) -> dict | None:
        return getattr(self._local, "uso", None)

