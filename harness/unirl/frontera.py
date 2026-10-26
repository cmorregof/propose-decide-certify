"""La frontera con la arquitectura de la tesis (24 oct 2026, decisión (b) de Carlos).

El mismo episodio que reflexion.py —K intentos, reflexión, consultas con tope, un cuaderno que solo crece por
veredicto del kernel— pero en Lean 4 + Mathlib y sobre los enunciados aprobados de prometeo_lean (aprobados/ETP).
Tres cosas nuevas:

  1. Consultas EVAL. El modelo ejecuta código Lean (#eval, #check, #reduce, def, example) en el contexto del
     problema, en sandbox y sin red, para explorar antes de demostrar. No gasta intento; sí una llamada, con tope.
  2. Sublemas propios. Un LEMA que el kernel acepta —compilado solo, con únicamente propext, Classical.choice y
     Quot.sound— entra al cuaderno L y queda disponible por su nombre en los episodios siguientes (regla U1). Una
     refutación es un lema cuyo enunciado es una negación: queda como resultado negativo certificado. Las CONJETURAS
     y las reflexiones son texto: orientan, no valen como verdad.
  3. Siembra. Lemas certificados en otras sesiones entran al cuaderno pasando por el mismo kernel, con su origen.

Condiciones: SC (sin cuaderno: solo la historia del episodio) y CC (con cuaderno). La línea base es frontera.sh de
prometeo_lean (un agente suelto con el mismo presupuesto). Lo que el kernel acepta como prueba de uno de los dos
enunciados aprobados se exporta como candidato a ETP/E<n>.lean; el veredicto final es de comprobar_etp.py (segundo
testigo), que corre Carlos. Claude no lanza corridas con API (CLAUDE.md del repo).

    python -m unirl.frontera tarea 13102                 # la tarea cargada y su SHA-256 (sin Lean ni API)
    python -m unirl.frontera humo 13102                  # compila el contexto aprobado y dos lemas de prueba (sin API)
    python -m unirl.frontera sembrar 13102 semillas.lean --origen "frontera.sh, 18 oct 2026"
    python -m unirl.frontera estado 13102                # qué hay en el cuaderno
    python -m unirl.frontera correr 13102 --seco         # proveedor simulado y cuaderno aparte (sin API)
    python -m unirl.frontera correr 13102 --modelo claude-opus-5-5 --config CC --episodios 3 --tope-usd 15
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import secrets
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import asdict, dataclass
from datetime import datetime
from pathlib import Path

from .juez_lean import LEAN_MINIMO, axiomas, errores, version_lean
from .loop import ProviderFatal, Rechazo, complete_with_retries

BASE = Path(__file__).resolve().parent.parent
PROMETEO = Path(os.environ.get("UNIRL_PROMETEO", str(BASE.parent / "Proyecto Godel" / "prometeo_lean")))
RUNS = BASE / "runs" / "unirl" / "frontera"
LIBRO_FRONTERA = BASE / "logs" / "gasto_frontera.json"
TOPE_GLOBAL_USD = float(os.environ.get("UNIRL_TOPE_FRONTERA_USD", 60.0))  # todo el libro de la frontera
AXIOMAS_OK = {"propext", "Classical.choice", "Quot.sound"}
MAX_REFLEXION_PALABRAS = 150
MAX_SALIDA_EVAL = 4000
MAX_BLOQUE = 40000
MAX_HISTORIA = 6

# Lo que nunca puede escribir el modelo (LEMA, AUX, PRUEBA y EVAL). La lista de comprobar_etp.py, más lo que podría
# cambiar el significado de un enunciado aprobado sin tocar su texto (open, notation, attribute, export, local,
# scoped) o salir del sandbox lógico (IO.Process, IO.FS, initialize).
_NATIVO = re.compile(r"\bnative_decide\b|\bdecide\s*\+\s*native\b|\bLean\.ofReduceBool\b|\bofReduceBool\b")
AXIOMA_NATIVO = "Lean.ofReduceBool"
_PROHIBIDO = re.compile(
    r"\baxiom\b|\badmit\b|\bsorry\b|\bimplemented_by\b|\bextern\b|\bunsafe\b|\bopaque\b"
    r"|\bmacro\b|\bmacro_rules\b|\bsyntax\b|\belab\b|\belab_rules\b|\bnotation\b|\binfix[lr]?\b|\bprefix\b"
    r"|\bpostfix\b|\brun_cmd\b|\brun_elab\b|\brun_meta\b|\brun_tac\b|#exit\b|\bdebug\.|\bskipKernelTC\b"
    r"|\bimport\b|\bnamespace\b|\bsection\b|\bopen\b|\bexport\b|\blocal\b|\bscoped\b|\battribute\b|\bderiving\b"
    r"|\bLean\.Elab\b|\bLean\.Meta\b|\bIO\.Process\b|\bIO\.FS\b|\binitialize\b|\bbuiltin_initialize\b"
    r"|\bsorryAx\b|\bdbg_trace\b|\btrace\b|\blogInfo\b"
    # revisión adversarial del 24 oct: introductores que _DECL no ve y que esquivaban la regla de nombres cu_/aux_
    r"|\bnonrec\b|\birreducible_def\b|\balias\b|\bdeclare_\w+|\badd_decl_doc\b|\bmutual\b"
    r"|\bvariable\b|\buniverse\b|^\s*end\b|\bset_option\s+(?!maxHeartbeats\b|maxRecDepth\b)\S+", re.M)
_DECL = re.compile(r"^[ \t]*(?:@\[[^\]\n]*\]\s*)?(?:(?:private|protected|noncomputable|partial)\s+)*"
                   r"(def|abbrev|theorem|lemma|instance|structure|inductive|class|example)\b[ \t]*([^\s:({\[]*)",
                   re.M)


def _sin_comentarios(t: str) -> str:
    t = re.sub(r"/-.*?-/", " ", t, flags=re.S)
    return re.sub(r"--[^\n]*", " ", t)


def _sha(t: str) -> str:
    return hashlib.sha256(t.encode("utf-8")).hexdigest()


# ============================================================================== la tarea: un enunciado aprobado


def cargar_tarea(n: str, raiz: Path = PROMETEO) -> dict:
    """La ley n de aprobados/ETP, verificada contra los SHA256SUMS_etp*. Falla si el archivo no está aprobado."""
    n = str(n)
    ap = raiz / "aprobados" / "ETP" / f"E{n}.lean"
    if not ap.exists():
        raise FileNotFoundError(f"{ap} no existe: la ley {n} no está aprobada")
    sumas = {}
    for f in sorted((raiz / "aprobados").glob("SHA256SUMS_etp*")):
        for linea in f.read_text(encoding="utf-8").splitlines():
            if linea.strip():
                h, ruta = linea.split(None, 1)
                sumas[ruta.strip().lstrip("*")] = h
    texto = ap.read_text(encoding="utf-8")
    sha = _sha(texto)
    if sumas.get(f"aprobados/ETP/E{n}.lean") != sha:
        raise ValueError(f"aprobados/ETP/E{n}.lean no coincide con su SHA-256 registrado: no se usa")
    corte = texto.index(f"/-- **Ley {n},")
    prefijo = texto[:corte].rstrip() + "\n"
    alternativas = []
    for m in re.finditer(r"(/-- \*\*Ley [^\n]*\n(?:[^\n]*\n)*?theorem ([\w.']+)[^\n]*(?:\n    [^\n]*)*?)\s*:= by",
                         texto):
        alternativas.append({"nombre": m.group(2), "enunciado": m.group(1).rstrip()})
    if not alternativas:
        raise ValueError(f"E{n}: no encontré los enunciados aprobados")
    abiertos = re.findall(r"^namespace\s+(\S+)", prefijo, re.M)
    cierre = "".join(f"\nend {ns}\n" for ns in reversed(abiertos))
    return {"id": f"E{n}", "ley": n, "archivo": str(ap), "sha": sha, "prefijo": prefijo,
            "alternativas": alternativas, "cierre": cierre, "ns": ".".join(abiertos)}


# ============================================================================== Lean con Mathlib (lake env lean)


def _perfil(work: Path, raiz: Path) -> str:
    home = str(Path.home())
    return ('(version 1)(allow default)(deny network*)'
            '(deny file-write* (require-all'
            f' (require-not (subpath "{work.resolve()}"))'
            f' (require-not (subpath "{home}/.elan"))'
            f' (require-not (subpath "{(raiz / ".lake").resolve()}"))'
            ' (require-not (subpath "/private/tmp")) (require-not (subpath "/private/var/folders"))'
            ' (require-not (subpath "/dev"))))')


class Lake:
    """Compila un archivo con `lake env lean` dentro de prometeo_lean (con su Mathlib), en sandbox y sin red."""

    def __init__(self, raiz: Path = PROMETEO, timeout_s: float = 300, aislado: bool = True, scratch: Path | None = None):
        self.raiz = Path(raiz)
        cands = [os.environ.get("UNIRL_LAKE"), str(Path.home() / ".elan" / "bin" / "lake"), shutil.which("lake")]
        self.lake = next((Path(c) for c in cands if c and Path(c).exists()), None)
        self.timeout_s = float(timeout_s)
        self.aislado = aislado and Path("/usr/bin/sandbox-exec").exists()
        self.scratch = Path(scratch) if scratch else Path(tempfile.gettempdir()) / "unirl_frontera"
        self._version: str | None = None

    def version(self) -> str:
        if self._version is None:
            if not self.lake:
                self._version = "lake no encontrado"
            else:
                r = subprocess.run([str(self.lake), "env", "lean", "--version"], cwd=self.raiz, capture_output=True,
                                   text=True, timeout=120)
                self._version = ((r.stdout or r.stderr).strip().splitlines() or ["?"])[0]
        return self._version

    def compilar(self, texto: str) -> dict:
        if not self.lake:
            return {"rc": -1, "salida": "no se encontró lake (UNIRL_LAKE, ~/.elan/bin/lake o PATH)", "s": 0.0}
        v = version_lean(self.version())
        if v is None or v < LEAN_MINIMO:
            return {"rc": -1, "salida": f"{self.version()}: hace falta Lean ≥ {'.'.join(map(str, LEAN_MINIMO))}", "s": 0.0}
        self.scratch.mkdir(parents=True, exist_ok=True)
        w = Path(tempfile.mkdtemp(prefix="intento-", dir=str(self.scratch)))
        f = w / "Intento.lean"
        f.write_text(texto, encoding="utf-8")
        cmd = [str(self.lake), "env", "lean", str(f)]
        if self.aislado:
            cmd = ["/usr/bin/sandbox-exec", "-p", _perfil(w, self.raiz)] + cmd
        t = time.perf_counter()
        p = subprocess.Popen(cmd, cwd=self.raiz, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                             encoding="utf-8", errors="replace", start_new_session=True)
        try:
            out, _ = p.communicate(timeout=self.timeout_s)
            rc = p.returncode
        except subprocess.TimeoutExpired:
            try:
                os.killpg(p.pid, 9)
            except OSError:
                p.kill()
            out, _ = p.communicate()
            rc = -9
        return {"rc": rc, "salida": out or "", "s": round(time.perf_counter() - t, 2)}


# ============================================================================== filtros


def filtrar_declaraciones(bloque: str, prefijos: tuple[str, ...], exigir_teorema: bool,
                          permitir_comandos: bool = False, permitir_nativo: bool = False) -> tuple[str | None, list[dict]]:
    """(motivo de rechazo o None, declaraciones). Toda declaración nombrada empieza por uno de `prefijos`: así nada
    del modelo puede tapar un nombre del contexto aprobado (Finite, Magma, Ley…) y cambiar el significado de un
    enunciado sin tocar su texto. Las instancias tienen que tener nombre."""
    if len(bloque) > MAX_BLOQUE:
        return f"el bloque supera {MAX_BLOQUE} caracteres", []
    limpio = bloque  # crudo: quitar comentarios antes de filtrar dejaba pasar «"/-" … sorry … "-/"» en cadenas
    m = _PROHIBIDO.search(limpio) or (None if permitir_nativo else _NATIVO.search(limpio))
    if m:
        return f"contiene «{m.group(0).strip()}» (prohibido)", []
    if not permitir_comandos and (c := re.search(r"#\w+", limpio)):
        return f"contiene el comando «{c.group(0)}»: los comandos # solo van en EVAL", []
    if not permitir_comandos and '"' in limpio:
        return "contiene una cadena entre comillas: fuera de EVAL no hacen falta y podrían falsear mensajes", []
    decls = [{"tipo": d.group(1), "nombre": d.group(2)} for d in _DECL.finditer(limpio)]
    for d in decls:
        if d["tipo"] == "example":
            continue
        if not d["nombre"]:
            return f"un {d['tipo']} sin nombre (ponle un nombre que empiece por {' o '.join(prefijos)})", decls
        if not d["nombre"].startswith(prefijos):
            return f"el nombre «{d['nombre']}» no empieza por {' o '.join(prefijos)}", decls
    if exigir_teorema and not any(d["tipo"] in ("theorem", "lemma") for d in decls):
        return "no hay ningún theorem o lemma", decls
    return None, decls


def filtrar_prueba(prueba: str, permitir_nativo: bool = False) -> str | None:
    if len(prueba) > MAX_BLOQUE:
        return f"la prueba supera {MAX_BLOQUE} caracteres"
    limpio = prueba
    m = _PROHIBIDO.search(limpio) or (None if permitir_nativo else _NATIVO.search(limpio))
    if m:
        return f"la prueba contiene «{m.group(0).strip()}» (prohibido)"
    if '"' in limpio:
        return "la prueba contiene una cadena entre comillas (no hace falta y podría falsear mensajes)"
    if c := re.search(r"#\w+", limpio):
        return f"la prueba contiene el comando «{c.group(0)}»"
    if _DECL.search(limpio):
        return "la prueba declara algo: las definiciones van en AUX y los lemas en LEMA"
    return None


def _indentar(t: str) -> str:
    return "\n".join(("  " + l) if l.strip() else l for l in t.strip("\n").split("\n"))


def sufijo_axiomas(teoremas: list[str], cierre: str) -> tuple[str, str]:
    """El final del archivo que escribe el juez: una marca con un nonce que el modelo no conoce y, DESPUÉS, los
    #print axioms. Solo se leen las líneas de axiomas que aparecen tras la marca."""
    nonce = secrets.token_hex(8)
    return (f'\n#eval IO.println "UNIRL_MARCA_{nonce}"\n' + "".join(f"#print axioms {n}\n" for n in teoremas)
            + cierre), nonce


def axiomas_tras_marca(salida: str, nonce: str, nombre_completo: str) -> list[str] | None:
    """Axiomas de `nombre_completo` (con su namespace) según las líneas posteriores a la marca, que empiezan por la
    comilla (o por la posición «archivo:l:c: info:»); None si no están."""
    i = salida.find(f"UNIRL_MARCA_{nonce}")
    if i < 0:
        return None
    for l in salida[i:].splitlines()[1:]:
        l = re.sub(r"^[^\n']*?:\d+:\d+: info: ", "", l)
        # Los nombres de Lean pueden llevar apóstrofe (cu_foo'); el nombre va entre comillas simples y la marca de fin
        # es «' depends on», así que se captura de forma ávida hasta ella (arreglo del 24 oct 2026).
        m = re.match(r"'(.+)' depends on axioms: \[(.*)\]\s*$", l)
        if m and m.group(1) == nombre_completo:
            return [a.strip() for a in m.group(2).split(",") if a.strip()]
        m = re.match(r"'(.+)' does not depend on any axioms\s*$", l)
        if m and m.group(1) == nombre_completo:
            return []
    return None


def _veredicto(c: dict, nombre: str, nonce: str | None = None, ns: str = "", permitir_nativo: bool = False) -> dict:
    """ACCEPTED solo si compila sin errores, sin sorry y con axiomas ⊆ {propext, Classical.choice, Quot.sound}."""
    sal = c["salida"]
    if c["rc"] == -9:
        return {"etiqueta": "TIMEOUT", "motivo": "se agotó el tiempo de compilación"}
    if c["rc"] == -1:
        return {"etiqueta": "SIN_LEAN", "motivo": sal}
    if "declaration uses 'sorry'" in sal:
        return {"etiqueta": "UNSOUND", "motivo": "usa sorry"}
    if c["rc"] != 0 or re.search(r":\d+:\d+: error", sal):
        return {"etiqueta": "PROOF_FAILED", "motivo": "Lean dio errores"}
    completo = f"{ns}.{nombre}" if ns else nombre
    ax = axiomas_tras_marca(sal, nonce, completo) if nonce else axiomas(sal, nombre)
    if ax is None:
        return {"etiqueta": "UNSOUND", "motivo": "no apareció la línea de #print axioms"}
    extra = sorted(set(ax) - AXIOMAS_OK)
    if extra == [AXIOMA_NATIVO] and permitir_nativo:
        return {"etiqueta": "ACCEPTED*", "axiomas": ax,
                "motivo": "aceptado confiando en el compilador (native_decide): NO es un veredicto del kernel"}
    if extra:
        return {"etiqueta": "UNSOUND", "motivo": f"axiomas no permitidos: {extra}", "axiomas": ax}
    return {"etiqueta": "ACCEPTED", "motivo": "el kernel de Lean aceptó", "axiomas": ax}


# ============================================================================== el cuaderno (U1 en Lean)


class Cuaderno:
    """L: bloques Lean que el kernel aceptó (lemas.lean + entradas.json). N: notas de texto (notas.json): metas
    propuestas, intentos fallidos y reflexiones; orientan, no son verdad. Nada entra a L sin compilar."""

    def __init__(self, carpeta: Path):
        self.carpeta = Path(carpeta)
        self.carpeta.mkdir(parents=True, exist_ok=True)
        self.f_entradas, self.f_notas = self.carpeta / "entradas.json", self.carpeta / "notas.json"
        self.entradas: list[dict] = json.loads(self.f_entradas.read_text(encoding="utf-8")) if self.f_entradas.exists() else []
        self.notas: dict = (json.loads(self.f_notas.read_text(encoding="utf-8")) if self.f_notas.exists()
                            else {"metas": [], "fallidos": [], "reflexiones": []})

    def lean(self) -> str:
        return "\n\n".join(f"-- [{e['nombre']}] {e['origen']}\n{e['bloque'].strip()}" for e in self.entradas)

    def hash(self) -> str:
        return _sha(self.lean())[:16]

    def nombres(self) -> set[str]:
        return {d for e in self.entradas for d in e["declara"]}

    def guardar(self) -> None:
        self.f_entradas.write_text(json.dumps(self.entradas, ensure_ascii=False, indent=1), encoding="utf-8")
        self.f_notas.write_text(json.dumps(self.notas, ensure_ascii=False, indent=1), encoding="utf-8")
        (self.carpeta / "lemas.lean").write_text(self.lean() + "\n", encoding="utf-8")

    def nota(self, clase: str, texto: str, tope: int = 40) -> None:
        self.notas.setdefault(clase, []).append(texto)
        self.notas[clase] = self.notas[clase][-tope:]


def _enunciado_de(bloque: str, nombre: str) -> str:
    m = re.search(rf"(?:theorem|lemma)\s+{re.escape(nombre)}\b(.*?):=", bloque, re.S)
    return " ".join(m.group(1).split()) if m else "?"


def admitir_bloque(tarea: dict, lake: Lake, contexto_lean: str, bloque: str, nombres_previos: set[str],
                   permitir_nativo: bool = False) -> dict:
    """Regla U1: el bloque (defs/instancias cu_ y al menos un teorema cu_) se compila sobre el contexto aprobado más
    lo ya certificado; entra solo si TODOS sus teoremas pasan el kernel con los axiomas estándar."""
    motivo, decls = filtrar_declaraciones(bloque, ("cu_",), exigir_teorema=True, permitir_nativo=permitir_nativo)
    nombres = [d["nombre"] for d in decls if d["nombre"]]
    if motivo:
        return {"etiqueta": "FORBIDDEN", "motivo": motivo, "nombres": nombres}
    repetidos = sorted(set(nombres) & nombres_previos)
    if repetidos or len(set(nombres)) != len(nombres):
        return {"etiqueta": "FORBIDDEN", "motivo": f"nombres ya usados: {repetidos or nombres}", "nombres": nombres}
    teoremas = [d["nombre"] for d in decls if d["tipo"] in ("theorem", "lemma")]
    sufijo, nonce = sufijo_axiomas(teoremas, tarea["cierre"])
    texto = tarea["prefijo"] + "\n" + contexto_lean + "\n\n" + bloque.strip() + "\n" + sufijo
    c = lake.compilar(texto)
    primera = (tarea["prefijo"] + "\n" + contexto_lean + "\n\n").count("\n") + 1
    vs = {t: _veredicto(c, t, nonce, tarea.get("ns", ""), permitir_nativo) for t in teoremas}
    malos = {t: v for t, v in vs.items() if v["etiqueta"] not in ("ACCEPTED", "ACCEPTED*")}
    if malos:
        t, v = next(iter(malos.items()))
        if "has already been declared" in c["salida"]:
            # Colisión de nombres: Lean no llegó a juzgar la prueba. Se dice así y no se culpa al contexto.
            return {"etiqueta": "NOMBRE_YA_DECLARADO", "motivo": f"{t}: un nombre ya estaba declarado en el archivo; "
                    "la prueba no se juzgó", "nombres": nombres, "s": c["s"], "errores": errores(c["salida"], primera)}
        return {"etiqueta": v["etiqueta"], "motivo": f"{t}: {v['motivo']}", "nombres": nombres, "s": c["s"],
                "errores": errores(c["salida"], primera)}
    etiqueta = "ACCEPTED*" if any(v["etiqueta"] == "ACCEPTED*" for v in vs.values()) else "ACCEPTED"
    return {"etiqueta": etiqueta, "nombres": nombres, "teoremas": teoremas, "s": c["s"],
            "enunciados": {t: _enunciado_de(bloque, t) for t in teoremas}}


def incorporar(cuad: Cuaderno, bloque: str, r: dict, origen: str, episodio: str) -> None:
    enunciados = r["enunciados"]
    cuad.entradas.append({"nombre": r["teoremas"][-1], "declara": r["nombres"], "teoremas": r["teoremas"],
                          "enunciados": enunciados, "bloque": bloque.strip(), "origen": origen, "episodio": episodio,
                          "fecha": datetime.now().isoformat(timespec="seconds"), "sha": _sha(bloque.strip()),
                          "negativo": any(e.lstrip(": ").startswith("¬") for e in enunciados.values())})


def bloques_de_archivo(texto: str) -> list[str]:
    """Parte un archivo de semillas en bloques: cada bloque termina en un theorem/lemma y arrastra las defs previas."""
    limpio = re.sub(r"/--.*?-/", "", texto, flags=re.S)
    inicios = [m.start() for m in _DECL.finditer(limpio)]
    bloques, actual = [], []
    for i, ini in enumerate(inicios):
        fin = inicios[i + 1] if i + 1 < len(inicios) else len(limpio)
        trozo = limpio[ini:fin].rstrip()
        actual.append(trozo)
        if re.match(r"(?:@\[[^\]\n]*\]\s*)?(?:theorem|lemma)\b", trozo.lstrip()):
            bloques.append("\n\n".join(actual))
            actual = []
    return bloques


# ============================================================================== el episodio


SISTEMA = """Eres un matemático que trabaja en un problema ABIERTO con Lean 4 y Mathlib. Nadie sabe la respuesta. El \
kernel de Lean decide qué es verdad; tú nunca afirmas que algo está demostrado. Un problema abierto no se resuelve \
en un intento: avanza con lemas pequeños que el kernel certifique, explora con EVAL antes de demostrar, y descarta \
caminos refutándolos.

Cada respuesta tuya es UNA de dos cosas.

(1) Exploración (no gasta intento; hay un tope de turnos):
EVAL: <<< código Lean: def/abbrev/instance/example, #eval, #check, #reduce >>>
(hasta dos bloques EVAL). El sistema lo compila en el contexto del problema y del cuaderno y te devuelve la salida.

(2) Un intento, con cualquiera de estas partes:
REFLEXION: <<< qué aprendiste del intento anterior y qué cambias (máx. 150 palabras) >>>
LEMA: <<< theorem cu_nombre … := by … >>>  (uno o varios bloques; antes del theorem puedes poner def/instance cu_…)
CONJETURA: <<< un enunciado Lean sin prueba que propones como meta intermedia >>>
LADO: <<< el nombre de UNO de los dos teoremas del problema >>>
AUX: <<< definiciones auxiliares para la prueba principal (nombres aux_… o cu_…) >>>
PRUEBA: <<< las tácticas de la prueba principal, sin `by` >>>

Un LEMA que el kernel acepta entra al cuaderno y queda disponible por su nombre en todo lo que sigue, también en \
episodios futuros. Una refutación es un LEMA cuyo enunciado es una negación. Las CONJETURAS y las reflexiones son \
texto: orientan, no valen como verdad.

Reglas del juez: todo nombre que declares empieza por cu_ (lemas) o aux_ (AUX); las instancias llevan nombre. \
Prohibido: sorry, admit, axiom, native_decide, implemented_by, unsafe, opaque, open, notation, attribute, \
namespace, section, end, import, set_option (salvo maxHeartbeats y maxRecDepth), metaprogramación. Solo se \
admiten los axiomas propext, Classical.choice y Quot.sound."""


@dataclass
class ConfigFrontera:
    nombre: str
    intentos: int = 4
    turnos_exploracion: int = 3
    max_evals_por_turno: int = 2
    max_lemas_por_intento: int = 4
    usa_cuaderno: bool = True
    permitir_nativo: bool = False  # solo por corrida y explícito; lo aceptado así lleva * y nunca entra a L


CONFIGS = {"SC": ConfigFrontera("SC", usa_cuaderno=False), "CC": ConfigFrontera("CC")}


def _bloques(nombre: str, texto: str) -> list[str]:
    return [m.group(1).strip("\n") for m in re.finditer(rf"\b{nombre}:\s*<<<(.*?)>>>(?!>)", texto or "", re.S)]


def leer(texto: str) -> dict:
    un = lambda n: (_bloques(n, texto) or [""])[0].strip()
    reflexion = un("REFLEXION") or un("REFLEXIÓN")
    palabras = reflexion.split()
    if len(palabras) > MAX_REFLEXION_PALABRAS:
        reflexion = " ".join(palabras[:MAX_REFLEXION_PALABRAS]) + " […]"
    return {"evals": _bloques("EVAL", texto), "lemas": _bloques("LEMA", texto), "conjeturas": _bloques("CONJETURA", texto),
            "lado": un("LADO"), "aux": un("AUX"), "prueba": _bloques("PRUEBA", texto)[0] if _bloques("PRUEBA", texto) else "",
            "reflexion": reflexion}


def _md(t: str, n: int = 3000) -> str:
    t = t if len(t) <= n else t[:n] + "\n… (recortado)"
    return f"```lean\n{t}\n```"


def construir_prompt(tarea: dict, cfg: ConfigFrontera, cuad: Cuaderno | None, locales: list[dict], historia: list[dict],
                     intentos_rest: int, turnos_rest: int) -> str:
    alts = "\n\n".join(a["enunciado"] for a in tarea["alternativas"])
    p = [f"# El problema: {tarea['id']}", "", "El contexto aprobado (no se puede cambiar):", _md(tarea["prefijo"], 8000), "",
         "Demuestra UNO de estos teoremas, el que sea cierto (LADO dice cuál):", _md(alts, 4000), ""]
    if cuad is not None and (cuad.entradas or any(cuad.notas.values())):
        p += ["# El cuaderno", ""]
        pos = [e for e in cuad.entradas if not e["negativo"]]
        neg = [e for e in cuad.entradas if e["negativo"]]
        if pos:
            p += ["Lemas certificados por el kernel (úsalos por su nombre):"]
            p += [f"- `{t}` : {e['enunciados'][t]}   ({e['origen']})" for e in pos for t in e["teoremas"]]
            p.append("")
        if neg:
            p += ["Refutaciones certificadas (caminos muertos):"]
            p += [f"- `{t}` : {e['enunciados'][t]}" for e in neg for t in e["teoremas"]]
            p.append("")
        if cuad.notas.get("metas"):
            p += ["Metas propuestas antes (texto, no verificado):"] + [f"- {m}" for m in cuad.notas["metas"][-10:]] + [""]
        if cuad.notas.get("fallidos"):
            p += ["Lemas que no pasaron el kernel (texto):"] + [f"- {m}" for m in cuad.notas["fallidos"][-10:]] + [""]
        if cuad.notas.get("reflexiones"):
            p += ["Reflexiones de episodios anteriores (texto):"] + [f"- {m}" for m in cuad.notas["reflexiones"][-6:]] + [""]
    if locales:
        p += ["# Lemas certificados en este episodio", ""] + [f"- `{t}` : {l['enunciados'][t]}" for l in locales
                                                              for t in l["teoremas"]] + [""]
    if historia:
        p += ["# Lo que pasó en este episodio", ""]
        for h in historia[-MAX_HISTORIA:]:
            p += [f"## {h['tipo']} {h.get('n', '')}", h["resumen"], ""]
    p += ["# Presupuesto", f"Te quedan {intentos_rest} intentos y {turnos_rest} turnos de exploración.", ""]
    return "\n".join(p)


def evaluar_evals(tarea: dict, lake: Lake, contexto_lean: str, codigos: list[str]) -> list[dict]:
    out = []
    for cod in codigos:
        motivo, _ = filtrar_declaraciones(cod, ("cu_", "aux_", "ev_"), exigir_teorema=False, permitir_comandos=True)
        if motivo:
            out.append({"codigo": cod, "salida": f"RECHAZADO: {motivo}", "s": 0.0})
            continue
        c = lake.compilar(tarea["prefijo"] + "\n" + contexto_lean + "\n\n" + cod.strip() + "\n" + tarea["cierre"])
        sal = c["salida"]
        if c["rc"] == -9:
            sal = "TIEMPO AGOTADO\n" + sal
        out.append({"codigo": cod, "salida": sal[-MAX_SALIDA_EVAL:], "s": c["s"]})
    return out


def _tipo_aprobado(enunciado: str, nombre: str) -> str:
    m = re.search(rf"\btheorem\s+{re.escape(nombre)}\s*:(.*)$", enunciado, re.S)
    if not m:
        raise ValueError(f"no encontré el tipo de {nombre}")
    return m.group(1).strip()


def juzgar_principal(tarea: dict, lake: Lake, contexto_lean: str, lado: str, aux: str, prueba: str,
                     permitir_nativo: bool = False) -> dict:
    alt = next((a for a in tarea["alternativas"] if a["nombre"] == lado.strip().split(".")[-1]), None)
    if alt is None:
        return {"etiqueta": "INVALID_PROPOSAL", "motivo": f"LADO debe ser uno de {[a['nombre'] for a in tarea['alternativas']]}"}
    if aux:
        motivo, _ = filtrar_declaraciones(aux, ("aux_", "cu_"), exigir_teorema=False, permitir_nativo=permitir_nativo)
        if motivo:
            return {"etiqueta": "FORBIDDEN", "motivo": f"AUX: {motivo}"}
    motivo = filtrar_prueba(prueba, permitir_nativo)
    if motivo:
        return {"etiqueta": "FORBIDDEN", "motivo": motivo}
    # Fidelidad del enunciado (defensa en profundidad, revisión del 24 oct): el tipo aprobado se elabora como
    # `unirl_ref_<nonce>` ANTES de todo el texto del modelo, y al final se exige `unirl_chk : unirl_ref := teorema`.
    # Si algo del modelo cambió el significado de un nombre del enunciado (Finite, Magma, Ley…), no tipa.
    sufijo, nonce = sufijo_axiomas([alt["nombre"]], tarea["cierre"])
    ref = f"unirl_ref_{nonce}"
    cab = (tarea["prefijo"] + f"\n/-- tipo aprobado, elaborado antes del texto del modelo -/\ndef {ref} : Prop :=\n  "
           + _tipo_aprobado(alt["enunciado"], alt["nombre"]) + "\n\n" + contexto_lean + "\n\n"
           + (aux.strip() + "\n\n" if aux else "") + alt["enunciado"] + " := by\n")
    cuerpo = _indentar(prueba)
    chk = f"\n\ntheorem unirl_chk_{nonce} : {ref} := {alt['nombre']}\n"
    linea_chk = (cab + cuerpo).count("\n") + 3
    c = lake.compilar(cab + cuerpo + chk + sufijo)
    v = _veredicto(c, alt["nombre"], nonce, tarea.get("ns", ""), permitir_nativo)
    errs = errores(c["salida"], cab.count("\n") + 1)
    if v["etiqueta"] == "PROOF_FAILED" and any(f":{linea_chk}:" in l for l in c["salida"].splitlines() if ": error" in l):
        v = {"etiqueta": "STATEMENT_DRIFT", "motivo": "el teorema demostrado ya no tiene el tipo aprobado"}
    v.update({"lado": alt["nombre"], "s": c["s"], "errores": errs})
    if v["etiqueta"] == "ACCEPTED":
        v["candidato"] = candidato(tarea, contexto_lean, aux, alt["nombre"], prueba)
    return v


def candidato(tarea: dict, contexto_lean: str, aux: str, lado: str, prueba: str) -> str:
    """El archivo para ETP/E<n>.lean: el texto aprobado intacto, lo auxiliar, y los dos enunciados tal cual (el
    resuelto con su prueba, el otro con sorry). Lo juzga después comprobar_etp.py (segundo testigo)."""
    partes = [tarea["prefijo"], contexto_lean.strip(), aux.strip()]
    for a in tarea["alternativas"]:
        cuerpo = _indentar(prueba) if a["nombre"] == lado else "  sorry"
        partes.append(a["enunciado"] + " := by\n" + cuerpo)
    return "\n\n".join(p for p in partes if p) + "\n" + tarea["cierre"]


def _resumen_intento(r: dict) -> str:
    l = []
    for lem in r["lemas"]:
        n = ", ".join(lem["resultado"].get("nombres", [])) or "?"
        l.append(f"LEMA {n}: {lem['resultado']['etiqueta']} — {lem['resultado'].get('motivo', '')}")
        l += [f"    {e[:400]}" for e in lem["resultado"].get("errores", [])[:4]]
    if r.get("principal"):
        p = r["principal"]
        l.append(f"PRUEBA ({p.get('lado', '?')}): {p['etiqueta']} — {p.get('motivo', '')}")
        l += [f"    {e[:600]}" for e in p.get("errores", [])[:6]]
    if not l:
        l.append("El intento no traía LEMA ni PRUEBA.")
    return "\n".join(l)


def _registrar(ruta: Path, d: dict) -> None:
    with ruta.open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(d, ensure_ascii=False) + "\n")


def episodio(tarea: dict, cfg: ConfigFrontera, proveedor, lake: Lake, cuad: Cuaderno, carpeta: Path, ep_id: str) -> dict:
    historia, locales = [], []
    intentos, turnos, llamadas = 0, cfg.turnos_exploracion, 0
    resultado = {"episodio": ep_id, "config": cfg.nombre, "resuelto": False, "lemas_admitidos": [], "intentos": 0}
    while intentos < cfg.intentos:
        persistente = cuad.lean() if cfg.usa_cuaderno else ""
        # Arreglo del 24 oct 2026 (hallazgo «contexto duplicado en CC»): en CC, incorporar() ya escribió en el
        # cuaderno cada lema aceptado en este episodio, así que solo se añaden los locales que el cuaderno NO trae.
        # Antes se sumaban todos y, desde el intento siguiente, Lean veía cada lema dos veces ("already declared").
        en_cuaderno = cuad.nombres() if cfg.usa_cuaderno else set()
        contexto = "\n\n".join(t for t in [persistente] + [l["bloque"] for l in locales
                                                             if not set(l["nombres"]) <= en_cuaderno] if t)
        prompt = construir_prompt(tarea, cfg, cuad if cfg.usa_cuaderno else None, locales, historia,
                                  cfg.intentos - intentos, turnos)
        try:
            texto = complete_with_retries(proveedor, SISTEMA, prompt, propagar_rechazo=True)
        except Rechazo as e:
            texto, rechazo = None, str(e)
        else:
            rechazo = None
        llamadas += 1
        _registrar(carpeta / "llamadas.jsonl", {"episodio": ep_id, "llamada": llamadas, "prompt_sha": _sha(prompt),
                                                "prompt": prompt, "respuesta": texto, "rechazo": rechazo,
                                                "fecha": datetime.now().isoformat(timespec="seconds")})
        if texto is None:
            intentos += 1
            historia.append({"tipo": "Intento", "n": intentos, "resumen": "REFUSAL o PROVIDER_ERROR: la llamada no devolvió nada"})
            continue
        r = leer(texto)
        if r["evals"] and not r["lemas"] and not r["prueba"]:
            if turnos <= 0:
                historia.append({"tipo": "Exploración", "resumen": "No quedan turnos de exploración: manda un intento."})
                intentos += 1
                continue
            turnos -= 1
            salidas = evaluar_evals(tarea, lake, contexto, r["evals"][:cfg.max_evals_por_turno])
            _registrar(carpeta / "intentos.jsonl", {"episodio": ep_id, "tipo": "exploracion", "evals": salidas})
            historia.append({"tipo": "Exploración", "resumen": "\n\n".join(
                _md(s["codigo"], 1500) + "\nSalida:\n" + _md(s["salida"], 2500) for s in salidas)})
            continue
        intentos += 1
        reg = {"episodio": ep_id, "tipo": "intento", "n": intentos, "reflexion": r["reflexion"], "lemas": [],
               "conjeturas": r["conjeturas"]}
        nombres_previos = (cuad.nombres() if cfg.usa_cuaderno else set()) | {n for l in locales for n in l["nombres"]}
        for bloque in r["lemas"][:cfg.max_lemas_por_intento]:
            res = admitir_bloque(tarea, lake, contexto, bloque, nombres_previos, cfg.permitir_nativo)
            reg["lemas"].append({"bloque": bloque, "resultado": res})
            if res["etiqueta"] == "ACCEPTED*":
                resultado.setdefault("lemas_asterisco", []).extend(res["teoremas"])
                if cfg.usa_cuaderno:
                    cuad.nota("asterisco", f"{', '.join(res['teoremas'])}* (native_decide; no certificado por el kernel)")
            if res["etiqueta"] == "ACCEPTED":
                locales.append({"bloque": bloque.strip(), **res})
                contexto = "\n\n".join(t for t in [contexto, bloque.strip()] if t)
                nombres_previos |= set(res["nombres"])
                resultado["lemas_admitidos"] += res["teoremas"]
                if cfg.usa_cuaderno:
                    incorporar(cuad, bloque, res, origen=f"{ep_id}, intento {intentos}", episodio=ep_id)
            elif cfg.usa_cuaderno:
                cuad.nota("fallidos", f"{', '.join(res.get('nombres', [])) or '?'}: {res['etiqueta']} — "
                                      f"{(res.get('errores') or [res.get('motivo', '')])[0][:200]}")
        if cfg.usa_cuaderno:
            for c in r["conjeturas"][:3]:
                cuad.nota("metas", " ".join(c.split())[:400])
        if r["prueba"]:
            reg["principal"] = juzgar_principal(tarea, lake, contexto, r["lado"], r["aux"], r["prueba"], cfg.permitir_nativo)
        _registrar(carpeta / "intentos.jsonl", reg)
        historia.append({"tipo": "Intento", "n": intentos, "resumen": _resumen_intento(reg)})
        if cfg.usa_cuaderno:
            cuad.guardar()
        if reg.get("principal", {}).get("etiqueta") == "ACCEPTED*":
            resultado["resuelto_asterisco"] = reg["principal"]["lado"]  # no se exporta candidato: no lo juzgó el kernel
        if reg.get("principal", {}).get("etiqueta") == "ACCEPTED":
            (carpeta / f"candidato_{tarea['id']}.lean").write_text(reg["principal"]["candidato"], encoding="utf-8")
            resultado["resuelto"] = reg["principal"]["lado"]
            break
    if cfg.usa_cuaderno and historia:
        ult = next((h for h in reversed(historia) if h["tipo"] == "Intento"), None)
        if ult:
            cuad.nota("reflexiones", f"{ep_id}: {ult['resumen'][:300]}")
        cuad.guardar()
    resultado.update({"intentos": intentos, "llamadas": llamadas})
    return resultado


# ============================================================================== proveedores


class ProveedorSeco:
    """Sin API: una exploración, un lema verdadero, un lema falso, y nada más. Para el ensayo en seco."""
    model = "seco"

    def __init__(self):
        self.n = 0

    def complete(self, system: str, user: str) -> str:
        self.n += 1
        if self.n == 1:
            return "EVAL: <<<\n#eval (2 + 2 : Nat)\n>>>"
        if self.n == 2:
            return ("REFLEXION: <<< ensayo en seco >>>\nLEMA: <<<\ntheorem cu_seco_verdadero : (2 : Nat) + 2 = 4 := by decide\n>>>\n"
                    "CONJETURA: <<< (2 : Nat) + 2 = 4 >>>")
        return "REFLEXION: <<< lema falso a propósito >>>\nLEMA: <<<\ntheorem cu_seco_falso : (2 : Nat) + 2 = 5 := by decide\n>>>"


def hacer_proveedor(modelo: str, corrida: str, tope_usd: float, effort: str):
    from steprl.providers import make_provider as mk
    from .gasto import Libro, ProveedorContable
    nombre = "anthropic" if modelo.startswith("claude-") else "openai"
    kw = ({"effort": effort, "fallback_model": None, "max_output_tokens": 64000} if nombre == "anthropic"
          else {"reasoning_effort": effort})
    fase = f"frontera:{corrida}"
    libro = Libro(ruta=LIBRO_FRONTERA, tope_usd=TOPE_GLOBAL_USD, topes_fase={fase: float(tope_usd)})
    return ProveedorContable(mk(nombre, modelo, **kw), libro, fase=fase, corrida=corrida)


def _huella_codigo() -> str:
    h = hashlib.sha256()
    for f in ("frontera.py", "juez_lean.py", "loop.py", "gasto.py"):
        p = Path(__file__).resolve().parent / f
        if p.exists():
            h.update(p.read_bytes())
    return h.hexdigest()[:16]


# ============================================================================== comandos


def cmd_tarea(a) -> int:
    t = cargar_tarea(a.ley)
    print(f"{t['id']}  SHA-256 {t['sha']}\n{t['archivo']}\nalternativas: {[x['nombre'] for x in t['alternativas']]}")
    return 0


def cmd_humo(a) -> int:
    t, lake = cargar_tarea(a.ley), Lake()
    print(f"lake: {lake.lake}  ({lake.version()})  sandbox: {lake.aislado}")
    ok = admitir_bloque(t, lake, "", "theorem cu_humo : (2 : Nat) + 2 = 4 := by decide", set())
    falso = admitir_bloque(t, lake, "", "theorem cu_humo_f : (2 : Nat) + 2 = 5 := by decide", set())
    trampa = admitir_bloque(t, lake, "", "theorem cu_humo_t : (2 : Nat) + 2 = 5 := by sorry", set())
    # los tipos aprobados se elaboran como referencia (lo que usa la comprobación de fidelidad de la prueba principal)
    refs = "".join(f"\ndef unirl_ref_humo_{i} : Prop :=\n  {_tipo_aprobado(x['enunciado'], x['nombre'])}\n"
                   for i, x in enumerate(t["alternativas"]))
    cref = lake.compilar(t["prefijo"] + refs + t["cierre"])
    ref_ok = cref["rc"] == 0 and not re.search(r":\d+:\d+: error", cref["salida"])
    print(f"lema verdadero → {ok['etiqueta']} ({ok.get('s')} s)\nlema falso → {falso['etiqueta']}\nsorry → {trampa['etiqueta']}"
          f"\ntipos aprobados como referencia → {'compilan' if ref_ok else 'NO compilan: ' + cref['salida'][-400:]}")
    bien = (ok["etiqueta"] == "ACCEPTED" and falso["etiqueta"] != "ACCEPTED" and trampa["etiqueta"] == "FORBIDDEN"
            and ref_ok)
    print("HUMO OK" if bien else "HUMO FALLÓ: revisar antes de gastar un dólar")
    return 0 if bien else 1


# Enmienda del 24 oct 2026: tras el arreglo del contexto duplicado, CC se repite con cuadernos NUEVOS en otra ruta
# (los de `cuadernos/` traen notas falsas y runs/ es intocable). UNIRL_CUADERNOS_FRONTERA elige la subcarpeta.
CUADERNOS = os.environ.get("UNIRL_CUADERNOS_FRONTERA", "cuadernos")


def _carpeta_cuaderno(ley: str, seco: bool) -> Path:
    return RUNS / ("seco" if seco else CUADERNOS) / f"E{ley}"


def cmd_sembrar(a) -> int:
    t, lake, cuad = cargar_tarea(a.ley), Lake(), Cuaderno(_carpeta_cuaderno(a.ley, False))
    bloques = bloques_de_archivo(Path(a.archivo).read_text(encoding="utf-8"))
    print(f"{len(bloques)} bloques en {a.archivo}")
    for b in bloques:
        r = admitir_bloque(t, lake, cuad.lean(), b, cuad.nombres())
        print(f"  {', '.join(r.get('nombres', [])) or '?'}: {r['etiqueta']} {r.get('motivo', '')}")
        if r["etiqueta"] == "ACCEPTED":
            incorporar(cuad, b, r, origen=f"semilla: {a.origen}", episodio="siembra")
            cuad.guardar()
    print(f"cuaderno {cuad.hash()}: {len(cuad.entradas)} entradas")
    return 0


def cmd_estado(a) -> int:
    cuad = Cuaderno(_carpeta_cuaderno(a.ley, a.seco))
    print(f"cuaderno de E{a.ley} ({cuad.hash()}): {len(cuad.entradas)} entradas")
    for e in cuad.entradas:
        print(f"  {'¬' if e['negativo'] else '✓'} {', '.join(e['teoremas'])}  [{e['origen']}]")
    for k, v in cuad.notas.items():
        print(f"  notas {k}: {len(v)}")
    return 0


def cmd_correr(a) -> int:
    t, lake = cargar_tarea(a.ley), Lake()
    from dataclasses import replace
    cfg = replace(CONFIGS[a.config], permitir_nativo=a.permitir_native_decide)
    modelo = "seco" if a.seco else a.modelo
    corrida = f"{datetime.now().strftime('%Y%m%d-%H%M%S')}-{modelo}-{a.config}"
    carpeta = RUNS / ("seco" if a.seco else "corridas") / t["id"] / corrida
    carpeta.mkdir(parents=True, exist_ok=False)
    cuad = Cuaderno(_carpeta_cuaderno(a.ley, a.seco))
    prov = ProveedorSeco() if a.seco else hacer_proveedor(modelo, corrida, a.tope_usd, a.esfuerzo)
    meta = {"tarea": t["id"], "sha_tarea": t["sha"], "config": asdict(cfg), "modelo": modelo, "esfuerzo": a.esfuerzo,
            "tope_usd": a.tope_usd, "episodios": a.episodios, "cuaderno_inicio": cuad.hash(),
            "lean": lake.version(), "codigo": _huella_codigo(), "inicio": datetime.now().isoformat(timespec="seconds")}
    (carpeta / "meta.json").write_text(json.dumps(meta, ensure_ascii=False, indent=1), encoding="utf-8")
    resultados, motivo_fin = [], "completo"
    for i in range(1, a.episodios + 1):
        try:
            r = episodio(t, cfg, prov, lake, cuad, carpeta, f"{corrida}#ep{i}")
        except ProviderFatal as e:
            motivo_fin = f"abortado: {e}"
            break
        resultados.append(r)
        _registrar(carpeta / "episodios.jsonl", r)
        print(f"episodio {i}: resuelto={r['resuelto']} lemas={r['lemas_admitidos']} intentos={r['intentos']}")
        if r["resuelto"]:
            print(f"CANDIDATO en {carpeta}/candidato_{t['id']}.lean — copiarlo a ETP/{t['id']}.lean y correr "
                  f"python3 herramientas/comprobar_etp.py {t['ley']} (segundo testigo)")
            break
    if not a.seco:
        meta["usd"] = prov.libro.gastado(prov.fase)
    meta.update({"fin": datetime.now().isoformat(timespec="seconds"), "motivo_fin": motivo_fin,
                 "cuaderno_fin": cuad.hash(), "resultados": resultados})
    (carpeta / "meta.json").write_text(json.dumps(meta, ensure_ascii=False, indent=1), encoding="utf-8")
    print(f"{motivo_fin}. Registro en {carpeta}")
    return 0 if motivo_fin == "completo" else 1


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python -m unirl.frontera", description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    for nombre in ("tarea", "humo", "estado"):
        s = sub.add_parser(nombre)
        s.add_argument("ley")
        if nombre == "estado":
            s.add_argument("--seco", action="store_true")
    s = sub.add_parser("sembrar")
    s.add_argument("ley")
    s.add_argument("archivo")
    s.add_argument("--origen", required=True)
    s = sub.add_parser("correr")
    s.add_argument("ley")
    s.add_argument("--modelo", default="claude-opus-5-5")
    s.add_argument("--config", choices=sorted(CONFIGS), default="CC")
    s.add_argument("--episodios", type=int, default=1)
    s.add_argument("--tope-usd", type=float, default=5.0)
    s.add_argument("--esfuerzo", default="high")
    s.add_argument("--seco", action="store_true")
    s.add_argument("--permitir-native-decide", action="store_true",
                   help="solo para esta corrida: lo aceptado con native_decide se marca con * y nunca entra al cuaderno")
    a = ap.parse_args(argv)
    return {"tarea": cmd_tarea, "humo": cmd_humo, "estado": cmd_estado, "sembrar": cmd_sembrar, "correr": cmd_correr}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
