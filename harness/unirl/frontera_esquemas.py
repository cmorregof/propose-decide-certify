"""La frontera sobre los esquemas del diseño A (24 oct 2026).

Reutiliza unirl/frontera.py tal cual (el mismo episodio, el mismo cuaderno U1, el mismo juez: compilación en
sandbox, nonce antes de #print axioms, tipo aprobado elaborado antes del texto del modelo → STATEMENT_DRIFT,
tokens prohibidos). Solo cambia de dónde sale la tarea: un teorema de una tanda aprobada de
prometeo_lean/aprobados/Esquemas en vez de una ley del ETP. frontera.py no se modifica: este módulo sustituye
`cargar_tarea`, `_tipo_aprobado` (para enunciados con parámetros) y las rutas de registro, y llama a su `main`.

Contexto que ve el modelo (prefijo): la plantilla A2 DEMOSTRADA (Esquemas/A2_Plantilla.lean, cuyo texto debe
coincidir con la aprobada) y la definición del esquema de la tarea, tomada de la tanda aprobada. No ve las demás
instancias ni los lemas auxiliares de las pruebas de referencia.

    python -m unirl.frontera_esquemas tarea esq_upwind_vonNeumann_iff
    python -m unirl.frontera_esquemas humo esq_upwind_vonNeumann_iff        # sin API
    python -m unirl.frontera_esquemas correr esq_upwind_vonNeumann_iff --seco
    python -m unirl.frontera_esquemas correr esq_upwind_vonNeumann_iff --modelo claude-opus-5-5 --config CC --tope-usd 3

La tanda se elige con UNIRL_TANDA_ESQUEMAS (por defecto A3_Corpus). El cuaderno es uno por tanda: los lemas que
el kernel acepta en un esquema quedan disponibles para los demás. Claude no lanza corridas con API.

Con `--cli` (25 oct 2026) el modelo se llama por `claude -p` (Claude Code en modo no interactivo, con la cuenta de
suscripción) en vez de por la API: sin herramientas, con el prompt de sistema del episodio en lugar del de Claude Code,
en modo seguro (sin CLAUDE.md, skills, hooks ni MCP), en una carpeta temporal vacía y SIN `ANTHROPIC_API_KEY` en el
entorno del subproceso, para que no se cobre a la API. El libro registra el costo equivalente de API (el tope sigue
acotando el consumo). Registros, cuadernos y libro van aparte: runs/unirl/esquemas_cli y logs/gasto_esquemas_cli.json.

    python -m unirl.frontera_esquemas cli-humo                       # una llamada mínima por claude -p
    python -m unirl.frontera_esquemas correr esq_upwind_vonNeumann_iff --cli --config CC --tope-usd 3
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from types import SimpleNamespace

from . import frontera as F

from .gasto import PRECIOS as _PRECIOS

# Haiku 5.5 no está en gasto.PRECIOS (que no se toca: su SHA entra en la huella de código de otras corridas). Se añade
# solo en memoria, con el tramo CARO (prompts de más de 100 000 tokens), para que el tope sea conservador. Fuente:
# https://platform.claude.com/docs/en/about-claude/pricing, consultada el 25 oct 2026: entrada 0,10 / 0,50; caché
# 0,01 / 0,05; salida 0,50 / 2,50 USD por millón (≤ 100 000 / > 100 000 tokens de prompt).
_PRECIOS.setdefault("claude-haiku-5-5", (0.50, 0.05, 2.50))

CIERRE = "\nend PrometeoLean.Esquemas\n"
NS = "PrometeoLean.Esquemas"
PLANTILLA = "A2_Plantilla"


def tanda() -> str:
    return os.environ.get("UNIRL_TANDA_ESQUEMAS", "A3_Corpus")


def _sumas(raiz: Path) -> dict:
    s = {}
    for f in sorted((raiz / "aprobados").glob("SHA256SUMS_esquemas*")):
        for linea in f.read_text(encoding="utf-8").splitlines():
            if linea.strip():
                h, ruta = linea.split(None, 1)
                s[ruta.strip().lstrip("*")] = h
    return s


def _aprobado(raiz: Path, nombre: str) -> str:
    ap = raiz / "aprobados" / "Esquemas" / f"{nombre}.lean"
    if not ap.exists():
        raise FileNotFoundError(f"{ap} no existe: la tanda {nombre} no está aprobada")
    texto = ap.read_text(encoding="utf-8")
    if _sumas(raiz).get(f"aprobados/Esquemas/{nombre}.lean") != F._sha(texto):
        raise ValueError(f"aprobados/Esquemas/{nombre}.lean no coincide con su SHA-256 registrado: no se usa")
    return texto


def _bloque(texto: str, inicio: re.Pattern) -> str:
    """El bloque de nivel superior (con su docstring) que empieza con `inicio`, hasta la siguiente línea en blanco."""
    m = inicio.search(texto)
    if not m:
        raise ValueError(f"no encontré {inicio.pattern}")
    a = texto.rfind("\n\n", 0, m.start()) + 2
    b = texto.find("\n\n", m.start())
    return texto[a: b if b >= 0 else len(texto)].rstrip()


def cargar_tarea(teorema: str, raiz: Path = F.PROMETEO) -> dict:
    raiz = Path(raiz)
    t = tanda()
    ap = _aprobado(raiz, t)
    _aprobado(raiz, PLANTILLA)                       # la plantilla también tiene que estar aprobada
    demo = (raiz / "Esquemas" / f"{PLANTILLA}.lean").read_text(encoding="utf-8")
    sys.path.insert(0, str(raiz / "herramientas"))
    from comprobar import patron_aprobado          # el criterio de texto de comprobar.py
    if not patron_aprobado((raiz / "aprobados" / "Esquemas" / f"{PLANTILLA}.lean").read_text(encoding="utf-8"))[0].fullmatch(demo):
        raise ValueError(f"Esquemas/{PLANTILLA}.lean no corresponde al texto aprobado de la plantilla")
    if not demo.endswith(CIERRE) or not ap.endswith(CIERRE):
        raise ValueError("los archivos no terminan en «end PrometeoLean.Esquemas»")
    # Una tarea es un teorema del corpus, o (25 oct) una de decidir: `esq_<id>_decide_<e>`, con las dos
    # alternativas `…_si` (∀ región → von Neumann) y `…_no` (∃ región ∧ ¬ von Neumann), como las leyes del ETP.
    m = re.fullmatch(r"(esq_[a-z0-9_]+?)_(momentos|vonNeumann_iff|vonNeumann|positivo|inestable)", teorema)
    d = re.fullmatch(r"(esq_[a-z0-9_]+?)_decide_([a-z0-9]+)", teorema)
    if not m and not d:
        raise ValueError(f"{teorema}: solo se admiten teoremas del corpus (esq_<id>_momentos|vonNeumann_iff|…) "
                         "o tareas de decidir (esq_<id>_decide_<e>)")
    esq = (m or d).group(1)
    defn = _bloque(ap, re.compile(rf"^noncomputable def {re.escape(esq)} ", re.M))
    nombres = [teorema] if m else [f"{teorema}_si", f"{teorema}_no"]
    alternativas = []
    for n in nombres:
        enun = _bloque(ap, re.compile(rf"^theorem {re.escape(n)} ", re.M))
        if not enun.endswith(":= by\n  sorry") and not enun.endswith(":= by\n  sorry\n"):
            raise ValueError(f"{n}: el enunciado aprobado no termina en «:= by sorry»")
        alternativas.append({"nombre": n, "enunciado": enun[: enun.rindex(":= by")].rstrip()})
    prefijo = demo[: -len(CIERRE)].rstrip() + "\n\n" + defn + "\n"
    return {"id": teorema, "ley": teorema, "archivo": str(raiz / "aprobados" / "Esquemas" / f"{t}.lean"),
            "sha": F._sha(ap), "prefijo": prefijo, "alternativas": alternativas, "cierre": CIERRE, "ns": NS}


def _tipo_aprobado(enunciado: str, nombre: str) -> str:
    """Como el de frontera.py, pero admite parámetros antes de los dos puntos: `theorem x (a : ℝ) (h : P) : T`
    se convierte en `∀ (a : ℝ) (h : P), T`."""
    m = re.search(rf"\btheorem\s+{re.escape(nombre)}\b(.*)$", enunciado, re.S)
    if not m:
        raise ValueError(f"no encontré el tipo de {nombre}")
    resto, prof = m.group(1), 0
    for i, ch in enumerate(resto):
        if ch in "([{⟨":
            prof += 1
        elif ch in ")]}⟩":
            prof -= 1
        elif ch == ":" and prof == 0 and resto[i + 1: i + 2] != "=":
            binders, tipo = resto[:i].strip(), resto[i + 1:].strip()
            return f"∀ {binders}, {tipo}" if binders else tipo
    raise ValueError(f"no encontré los dos puntos del tipo de {nombre}")


# ============================================================================== claude -p como proveedor

# Variables que harían que `claude` cobre a la API o hable con otro proveedor en vez de usar la suscripción
_ENV_FUERA = ("ANTHROPIC_API_KEY", "ANTHROPIC_AUTH_TOKEN", "ANTHROPIC_BASE_URL", "CLAUDE_CODE_USE_BEDROCK",
              "CLAUDE_CODE_USE_VERTEX", "CLAUDE_CODE_USE_FOUNDRY")


_FATAL_CLI = ("authenticate", "authentication", "oauth", "login", "log in", "usage limit", "limit reached",
              "credit", "not logged", "unauthorized", "forbidden")


class ProveedorClaudeCLI:
    """La misma interfaz que AnthropicProvider de steprl (`respuesta` cruda con `usage`, y `texto`), de modo que
    gasto.ProveedorContable la contabiliza sin cambios. Una llamada = un `claude -p` de un solo turno."""

    def __init__(self, model: str, effort: str = "high", max_output_tokens: int = 64000, timeout_s: int = 3600):
        self.model, self.effort, self.max_output_tokens, self.timeout_s = model, effort, max_output_tokens, timeout_s
        self.binario = os.environ.get("UNIRL_CLAUDE_BIN", "claude")

    def _cmd(self, archivo_sistema: str) -> list[str]:
        return [self.binario, "-p", "--model", self.model, "--effort", self.effort,
                "--system-prompt-file", archivo_sistema, "--tools", "", "--safe-mode", "--strict-mcp-config",
                "--no-session-persistence", "--output-format", "json"]

    def respuesta(self, system: str, user: str):
        env = {k: v for k, v in os.environ.items() if k not in _ENV_FUERA}
        env["CLAUDE_CODE_MAX_OUTPUT_TOKENS"] = str(self.max_output_tokens)
        with tempfile.TemporaryDirectory(prefix="unirl-cli-") as d:
            sis = Path(d) / ".sistema.txt"
            sis.write_text(system, encoding="utf-8")
            vacio = Path(d) / "cwd"
            vacio.mkdir()
            r = subprocess.run(self._cmd(str(sis)), input=user, cwd=vacio, env=env, capture_output=True, text=True,
                               timeout=self.timeout_s)
        try:
            j = json.loads(r.stdout.strip().splitlines()[-1]) if r.stdout.strip() else {}
        except json.JSONDecodeError:
            j = {}
        if r.returncode != 0 or not j or j.get("is_error"):
            detalle = str(j.get("result") or j.get("subtype") or (r.stderr or r.stdout)[-600:])
            # Sesión vencida, sin login o límite de uso: no tiene sentido seguir; se aborta la corrida entera
            # (antes, el 25 oct, 14 corridas se registraron como «no resueltas» con la sesión OAuth vencida).
            # Cualquier otro fallo de claude -p también aborta: con la CLI no hay errores transitorios que valga la pena
            # contar como intentos fallidos del modelo, y una corrida llena de fallos del proveedor mide el arnés, no
            # al modelo (p. ej. un --effort que el modelo no admite).
            from .loop import ProviderFatal
            raise ProviderFatal(f"claude -p falló (código {r.returncode}): {detalle[:300]}")
        u = j.get("usage") or {}
        uso = SimpleNamespace(input_tokens=int(u.get("input_tokens", 0) or 0),
                              cache_read_input_tokens=int(u.get("cache_read_input_tokens", 0) or 0),
                              cache_creation_input_tokens=int(u.get("cache_creation_input_tokens", 0) or 0),
                              output_tokens=int(u.get("output_tokens", 0) or 0), output_tokens_details=None)
        texto = j.get("result") or ""
        return SimpleNamespace(usage=uso, stop_reason=j.get("stop_reason") or "end_turn", stop_details=None,
                               content=[SimpleNamespace(type="text", text=texto)],
                               costo_cli_usd=j.get("total_cost_usd"), turnos=j.get("num_turns"))

    @staticmethod
    def texto(resp) -> str:
        return "".join(b.text for b in resp.content if b.type == "text")

    def complete(self, system: str, user: str) -> str:
        return self.texto(self.respuesta(system, user))


def hacer_proveedor_cli(modelo: str, corrida: str, tope_usd: float, effort: str):
    from .gasto import Libro, ProveedorContable
    fase = f"frontera:{corrida}"
    libro = Libro(ruta=F.LIBRO_FRONTERA, tope_usd=F.TOPE_GLOBAL_USD, topes_fase={fase: float(tope_usd)})
    return ProveedorContable(ProveedorClaudeCLI(modelo, effort), libro, fase=fase, corrida=corrida)


def cli_humo(modelo: str = "claude-opus-5-5", esfuerzo: str = "low") -> int:
    p = ProveedorClaudeCLI(modelo, esfuerzo, max_output_tokens=4000, timeout_s=600)
    r = p.respuesta("Responde únicamente con el número, sin nada más.", "¿Cuánto es 2 + 2?")
    t = p.texto(r).strip()
    print(f"respuesta: {t!r}  · tokens entrada {r.usage.input_tokens}+{r.usage.cache_read_input_tokens} (caché), "
          f"salida {r.usage.output_tokens} · turnos {r.turnos} · costo equivalente de API ${r.costo_cli_usd}")
    bien = t.startswith("4") and r.turnos in (None, 1)
    print("CLI OK" if bien else "CLI FALLÓ: no correr la frontera con --cli")
    return 0 if bien else 1


def hecha(tarea: str, config: str, cli: bool, episodios: int, modelo: str = "claude-opus-5-5") -> int:
    """Para relanzar una tanda sin repetir lo terminado: ¿hay una corrida completa de `tarea` con `config`?
    Completa = motivo_fin «completo» y, o bien se resolvió, o bien corrió todos sus episodios."""
    base = F.BASE / "runs" / "unirl" / ("esquemas_cli" if cli else "esquemas") / "corridas" / tarea
    for m in sorted(base.glob(f"*-{modelo}-{config}/meta.json")):    # la carpeta es <fecha>-<modelo>-<config>
        try:
            d = json.loads(m.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        res = d.get("resultados") or []
        if d.get("motivo_fin") == "completo" and (any(x.get("resuelto") for x in res) or len(res) >= episodios):
            print(f"hecha: {m.parent.name}")
            return 0
    return 1


_MODELO = "claude-opus-5-5"     # lo fija main() a partir de --modelo


def esquema_de(tarea: str) -> str:
    m = re.fullmatch(r"(esq_[a-z0-9_]+?)_(?:momentos|vonNeumann_iff|vonNeumann|positivo|inestable|decide_[a-z0-9]+)", tarea)
    if not m:
        raise ValueError(f"{tarea}: no es una tarea de esquemas")
    return m.group(1)


def carpeta_cuaderno(tarea: str, seco: bool) -> Path:
    """Un cuaderno por ESQUEMA dentro de la tanda (arreglo del 25 oct): los lemas del cuaderno nombran la definición
    de su esquema, y el contexto de una tarea solo trae la definición de ese esquema; con un cuaderno por tanda, los
    lemas de FTCS del calor rompían el contexto de upwind («unknown identifier esq_ftcs_calor»). Las tareas del mismo
    esquema (p. ej. decide_a y decide_b) sí comparten cuaderno. Carpeta nueva para no mezclar con el cuaderno viejo."""
    # Cada modelo tiene sus cuadernos (los lemas de Opus no pueden ayudar a Haiku). Opus conserva la ruta sin
    # segmento de modelo porque así empezaron sus corridas del 25 oct; los demás modelos van en una subcarpeta propia.
    raiz = F.RUNS / ("seco" if seco else "cuadernos_por_esquema")
    if _MODELO != "claude-opus-5-5":
        raiz = raiz / _MODELO
    return raiz / tanda() / esquema_de(tarea)


_axiomas_tras_marca_original = F.axiomas_tras_marca

# ============================================================================== endurecimiento (25 oct, aprobado por Carlos)
# Tres defectos de frontera.py que el arnés v4 del confirmatorio ya cerró en unirl/corpus_confirmatorio.py. Aquí se
# REUTILIZAN esas mismas implementaciones (no se copian): el entorno sin secretos para Lean (LakeSinSecretos), los
# filtros aplicados también al texto sin «» y, en EVAL, la lista de lo que lee el entorno, lanza procesos o toca
# archivos (prohibido_en). Además, defensa en profundidad propia de esta rama: el perfil de sandbox-exec niega a Lean
# la LECTURA de las carpetas con respuestas (pruebas de referencia en prometeo_lean/Esquemas y PrometeoLean, y todo
# rl_metodos: runs/ con los candidatos de otras corridas, logs/ y el .env). frontera.py no se modifica.

def _cc():
    from . import corpus_confirmatorio as CC         # importarlo también instala su lector tolerante en F
    return CC


_filtrar_declaraciones_original = F.filtrar_declaraciones
_filtrar_prueba_original = F.filtrar_prueba
_perfil_original = F._perfil


def filtrar_declaraciones(bloque: str, prefijos: tuple[str, ...], exigir_teorema: bool,
                          permitir_comandos: bool = False, permitir_nativo: bool = False):
    """La de frontera.py y, si pasa, prohibido_en del arnés v4: sobre el texto y sin «», con la lista de EVAL cuando
    el bloque es un EVAL (permitir_comandos) y la lista extra cuando es un LEMA o un AUX (como hace el arnés v4)."""
    motivo, decls = _filtrar_declaraciones_original(bloque, prefijos, exigir_teorema, permitir_comandos,
                                                    permitir_nativo)
    if motivo:
        return motivo, decls
    m = _cc().prohibido_en(bloque, extra=not permitir_comandos, eval_=permitir_comandos)
    return (m, decls) if m else (None, decls)


def filtrar_prueba(prueba: str, permitir_nativo: bool = False):
    motivo = _filtrar_prueba_original(prueba, permitir_nativo)
    if motivo:
        return motivo
    m = _cc().prohibido_en(prueba)
    return f"la prueba {m}" if m else None


def _carpetas_con_respuestas(raiz: Path) -> list[Path]:
    raiz = Path(raiz).resolve()
    return [raiz / "Esquemas", raiz / "PrometeoLean", F.BASE.resolve()]


def perfil(work: Path, raiz: Path) -> str:
    """El perfil de frontera.py (sin red; escritura solo en el directorio de trabajo, .elan, .lake y temporales) más
    la negación de LEER el contenido de las carpetas con respuestas. Solo file-read-data: Lean puede seguir viendo
    que existen (metadatos), no lo que dicen."""
    base = _perfil_original(work, raiz)
    negar = "".join(f' (subpath "{c}")' for c in _carpetas_con_respuestas(raiz))
    return base + f"(deny file-read-data (require-any{negar}))"


def instalar_endurecimiento() -> None:
    CC = _cc()
    F.axiomas_tras_marca = CC.axiomas_tras_marca     # el lector tolerante del arnés v4 (reemplaza al de este módulo)
    F.Lake = CC.LakeSinSecretos
    F.filtrar_declaraciones = filtrar_declaraciones
    F.filtrar_prueba = filtrar_prueba
    F._perfil = perfil


def axiomas_tras_marca(salida: str, nonce: str, nombre_completo: str) -> list[str] | None:
    """La de frontera.py, pero tolerando el corte de línea de Lean (arreglo del 25 oct 2026). Lean formatea los
    mensajes a 120 columnas: con un nombre largo (p. ej. `PrometeoLean.Esquemas.esq_c1_lax_wendroff_1_decide_corrida_si`)
    `#print axioms` parte la lista de axiomas en varias líneas, la de frontera.py lee línea por línea, no la encuentra y
    el juez marcaba UNSOUND una prueba correcta. Aquí se reúnen las líneas de continuación (las que empiezan con
    espacio) antes de buscar; frontera.py no se toca."""
    i = salida.find(f"UNIRL_MARCA_{nonce}")
    if i < 0:
        return None
    unida = re.sub(r"\n[ \t]+", " ", salida[i:])
    return _axiomas_tras_marca_original(salida[:i] + unida, nonce, nombre_completo)


def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv[:1] == ["cli-humo"]:
        return cli_humo(*argv[1:3])                  # cli-humo [modelo] [esfuerzo]
    if argv[:1] == ["hecha"]:                        # hecha <tarea> <CC|SC> [--cli] [--episodios N] [--modelo M]: 0 si
        return hecha(argv[1], argv[2], "--cli" in argv,  # ya hay una corrida completa de ese modelo; 1 si no
                     int(argv[argv.index("--episodios") + 1]) if "--episodios" in argv else 2,
                     argv[argv.index("--modelo") + 1] if "--modelo" in argv else "claude-opus-5-5")
    global _MODELO
    _MODELO = argv[argv.index("--modelo") + 1] if "--modelo" in argv else "claude-opus-5-5"
    cli = "--cli" in argv
    if cli:
        argv.remove("--cli")
        F.hacer_proveedor = hacer_proveedor_cli
    F.cargar_tarea = cargar_tarea
    F._tipo_aprobado = _tipo_aprobado
    F.axiomas_tras_marca = axiomas_tras_marca
    instalar_endurecimiento()
    F.RUNS = F.BASE / "runs" / "unirl" / ("esquemas_cli" if cli else "esquemas")
    F.LIBRO_FRONTERA = F.BASE / "logs" / ("gasto_esquemas_cli.json" if cli else "gasto_esquemas.json")
    F._carpeta_cuaderno = carpeta_cuaderno
    return F.main(argv)


if __name__ == "__main__":
    sys.exit(main())
