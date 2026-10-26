"""El selector de modelos (diseño A, bloque 3; 26 oct 2026): un modelo de lenguaje recibe un problema físico en una de
tres modalidades (texto, tabla de datos o imagen) y escoge de un catálogo cerrado el molde que lo describe, con sus
coeficientes. Es la idea de J. C. Riaño Rojas, medida contra la respuesta conocida.

    python -m unirl.selector_modelo humo-imagen [<png>]          # comprueba que el modelo ve una imagen (1 llamada)
    python -m unirl.selector_modelo correr <carpeta bench> --modelo M [--modalidades texto,datos,imagen] [--tope-usd 5]
    python -m unirl.selector_modelo hecha <carpeta bench> --modelo M --modalidad X --problema pNN   # 0 si ya está

Llamadas con `claude -p` sin ninguna herramienta (`--tools ""`), en modo seguro, desde una carpeta vacía y sin
ANTHROPIC_API_KEY: igual que el proveedor de frontera_esquemas. La imagen no se lee de disco: viaja en el mensaje como un
bloque de imagen (base64) por `--input-format stream-json`, así que el modelo no tiene acceso a ningún archivo.
Escribe en runs/unirl/selector_cli/<bench>/<modelo>/<modalidad>/<problema>.json; el libro de gasto es
logs/gasto_selector_cli.json. La respuesta verdadera (verdad.json) NO se lee aquí: la evalúa evaluar_selector.py.
"""
from __future__ import annotations

import argparse, base64, json, os, re, subprocess, sys, tempfile
from pathlib import Path
from types import SimpleNamespace

from . import frontera as F
from . import frontera_esquemas as _FE   # noqa: F401 — registra el precio de Haiku 5.5 en gasto.PRECIOS
from .loop import ProviderFatal

_ENV_FUERA = {"ANTHROPIC_API_KEY", "ANTHROPIC_AUTH_TOKEN", "OPENAI_API_KEY"}
MOLDES = ["calor", "adveccion", "adveccion_difusion", "reaccion_difusion", "adveccion_reaccion_difusion"]

SISTEMA = """You are an applied mathematician. You are given a physical problem on a periodic interval and must choose,
from a closed catalogue, the linear PDE model that describes it, and estimate its coefficients. All models use the
convention
    u_t + v * u_x = alpha * u_xx + lambda * u
with constant coefficients. The catalogue:
  calor                        v = 0, lambda = 0, alpha > 0      (pure diffusion)
  adveccion                    alpha = 0, lambda = 0, v != 0     (pure transport)
  adveccion_difusion           lambda = 0, v != 0, alpha > 0
  reaccion_difusion            v = 0, alpha > 0, lambda < 0      (diffusion with linear decay)
  adveccion_reaccion_difusion  v != 0, alpha > 0, lambda < 0
If no model of the catalogue describes the problem, answer "ninguno" with all coefficients 0.
Answer with ONE JSON object between <<< and >>>, exactly:
<<<
{"plantilla": "<one of the five names, or ninguno>", "coeficientes": {"v": <number>, "alpha": <number>, "lambda": <number>},
 "justificacion": "<one or two sentences>"}
>>>
Coefficients that the chosen model sets to zero must be 0. Units: x in metres, t in seconds."""

PIDE = {
    "texto": "Problem statement:\n\n{texto}",
    "datos": ("Noisy measurements of u(x, t) on [0, 4) x [0, 2] (periodic in x). The table is subsampled: the first "
              "row holds the x values and the first column the t values.\n\n{tabla}"),
    "imagen": ("The attached image is a heat map of noisy measurements of u(x, t) on the periodic interval [0, 4) for "
               "t in [0, 2] (x in metres on the horizontal axis, t in seconds on the vertical axis)."),
}


class ProveedorSelectorCLI:
    """Un `claude -p` de un turno, sin herramientas; con imagen, el mensaje va como stream-json con un bloque image."""

    def __init__(self, model: str, effort: str = "high", timeout_s: int = 1800):
        self.model, self.effort, self.timeout_s = model, effort, timeout_s
        self.binario = os.environ.get("UNIRL_CLAUDE_BIN", "claude")

    def respuesta(self, system: str, user: str, png: Path | None = None):
        env = {k: v for k, v in os.environ.items() if k not in _ENV_FUERA}
        env["CLAUDE_CODE_MAX_OUTPUT_TOKENS"] = "16000"
        with tempfile.TemporaryDirectory(prefix="unirl-sel-") as d:
            sis = Path(d) / ".sistema.txt"
            sis.write_text(system, encoding="utf-8")
            vacio = Path(d) / "cwd"
            vacio.mkdir()
            cmd = [self.binario, "-p", "--model", self.model, "--effort", self.effort, "--system-prompt-file", str(sis),
                   "--tools", "", "--safe-mode", "--strict-mcp-config", "--no-session-persistence"]
            if png is None:
                cmd += ["--output-format", "json"]
                entrada = user
            else:
                cmd += ["--input-format", "stream-json", "--output-format", "stream-json", "--verbose"]
                datos = base64.b64encode(png.read_bytes()).decode()
                entrada = json.dumps({"type": "user", "message": {"role": "user", "content": [
                    {"type": "image", "source": {"type": "base64", "media_type": "image/png", "data": datos}},
                    {"type": "text", "text": user}]}}) + "\n"
            r = subprocess.run(cmd, input=entrada, cwd=vacio, env=env, capture_output=True, text=True,
                               timeout=self.timeout_s)
        j = {}
        for linea in reversed(r.stdout.strip().splitlines()):
            try:
                o = json.loads(linea)
            except json.JSONDecodeError:
                continue
            if o.get("type") == "result" or "result" in o:
                j = o
                break
        if r.returncode != 0 or not j or j.get("is_error"):
            detalle = str(j.get("result") or j.get("subtype") or (r.stderr or r.stdout)[-600:])
            raise ProviderFatal(f"claude -p falló (código {r.returncode}): {detalle[:300]}")
        u = j.get("usage") or {}
        uso = SimpleNamespace(input_tokens=int(u.get("input_tokens", 0) or 0),
                              cache_read_input_tokens=int(u.get("cache_read_input_tokens", 0) or 0),
                              cache_creation_input_tokens=int(u.get("cache_creation_input_tokens", 0) or 0),
                              output_tokens=int(u.get("output_tokens", 0) or 0), output_tokens_details=None)
        return SimpleNamespace(usage=uso, stop_reason=j.get("stop_reason") or "end_turn", stop_details=None,
                               content=[SimpleNamespace(type="text", text=j.get("result") or "")],
                               costo_cli_usd=j.get("total_cost_usd"), turnos=j.get("num_turns"))

    @staticmethod
    def texto(resp) -> str:
        return "".join(b.text for b in resp.content if b.type == "text")


def extraer(texto: str) -> dict:
    m = re.findall(r"<<<(.*?)>>>", texto or "", re.S)
    if not m:
        raise ValueError("sin bloque <<< … >>>")
    d = json.loads(m[-1].strip())
    if d.get("plantilla") not in MOLDES + ["ninguno"]:
        raise ValueError(f"plantilla fuera del catálogo: {d.get('plantilla')!r}")
    cf = d.get("coeficientes") or {}
    d["coeficientes"] = {k: float(cf.get(k, 0) or 0) for k in ("v", "alpha", "lambda")}
    return d


def libro_y_proveedor(modelo: str, corrida: str, tope_usd: float, effort: str):
    from .gasto import Libro
    fase = f"selector:{corrida}"
    libro = Libro(ruta=F.BASE / "logs" / "gasto_selector_cli.json", tope_usd=F.TOPE_GLOBAL_USD,
                  topes_fase={fase: float(tope_usd)})
    return ProveedorSelectorCLI(modelo, effort), libro, fase


def ruta_registro(bench: Path, modelo: str, modalidad: str, pid: str) -> Path:
    return F.BASE / "runs" / "unirl" / "selector_cli" / bench.name / modelo / modalidad / f"{pid}.json"


def correr(bench: Path, modelo: str, modalidades: list[str], tope_usd: float, effort: str) -> int:
    corrida = f"{bench.name}-{modelo}"
    prov, libro, fase = libro_y_proveedor(modelo, corrida, tope_usd, effort)
    problemas = sorted(p for p in bench.iterdir() if p.is_dir() and re.fullmatch(r"p\d\d", p.name))
    for modalidad in modalidades:
        for pdir in problemas:
            reg = ruta_registro(bench, modelo, modalidad, pdir.name)
            if reg.exists():
                continue
            if modalidad == "texto":
                user, png = PIDE["texto"].format(texto=(pdir / "texto.txt").read_text(encoding="utf-8").strip()), None
            elif modalidad == "datos":
                user, png = PIDE["datos"].format(tabla=(pdir / "tabla.csv").read_text(encoding="utf-8").strip()), None
            else:
                user, png = PIDE["imagen"], pdir / "imagen.png"
            libro.autorizar(modelo, fase, None, len(SISTEMA) + len(user) + (40000 if png else 0), 16000)
            resp = prov.respuesta(SISTEMA, user, png=png)
            u = resp.usage
            uso = {"entrada": u.input_tokens + u.cache_read_input_tokens + u.cache_creation_input_tokens,
                   "cache": u.cache_read_input_tokens, "cache_escritura": u.cache_creation_input_tokens,
                   "salida": u.output_tokens, "razonamiento": 0, "effort": effort, "temperatura": None}
            libro.registrar(modelo, fase, corrida, uso)
            texto = prov.texto(resp)
            out = {"problema": pdir.name, "modalidad": modalidad, "modelo": modelo, "respuesta": texto,
                   "usd": resp.costo_cli_usd}
            try:
                out["seleccion"] = extraer(texto)
            except Exception as e:                       # noqa: BLE001 — una respuesta mal formada cuenta como fallo
                out["error"] = f"{type(e).__name__}: {e}"
            reg.parent.mkdir(parents=True, exist_ok=True)
            reg.write_text(json.dumps(out, ensure_ascii=False, indent=1), encoding="utf-8")
            print(json.dumps({k: out.get(k) for k in ("problema", "modalidad", "error")}
                             | {"plantilla": out.get("seleccion", {}).get("plantilla")}, ensure_ascii=False), flush=True)
    return 0


def humo_imagen(png: Path, modelo: str) -> int:
    prov = ProveedorSelectorCLI(modelo, "low", timeout_s=600)
    r = prov.respuesta("Answer in one short sentence.",
                       "What is the title written at the top of the attached image, and what are the axis labels?",
                       png=png)
    t = prov.texto(r).strip()
    print(f"respuesta: {t!r} · turnos {r.turnos} · costo equivalente ${r.costo_cli_usd}")
    bien = "u(x" in t and r.turnos in (None, 1)
    print("HUMO IMAGEN OK" if bien else "HUMO IMAGEN FALLÓ")
    return 0 if bien else 1


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="python -m unirl.selector_modelo")
    sub = ap.add_subparsers(dest="cmd", required=True)
    h = sub.add_parser("humo-imagen"); h.add_argument("png", nargs="?"); h.add_argument("--modelo", default="claude-haiku-5-5")
    c = sub.add_parser("correr"); c.add_argument("bench"); c.add_argument("--modelo", required=True)
    c.add_argument("--modalidades", default="texto,datos,imagen"); c.add_argument("--tope-usd", type=float, default=5.0)
    c.add_argument("--esfuerzo", default="high")
    a = ap.parse_args(argv)
    if a.cmd == "humo-imagen":
        png = Path(a.png) if a.png else next(Path(".").glob("**/imagen.png"))
        return humo_imagen(png, a.modelo)
    try:
        return correr(Path(a.bench).resolve(), a.modelo, a.modalidades.split(","), a.tope_usd, a.esfuerzo)
    except ProviderFatal as e:
        print(f"abortado: {e}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
