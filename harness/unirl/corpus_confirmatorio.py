"""El arnés del estudio confirmatorio sobre el corpus aprobado en Lean (24–25 oct 2026).

Mismo episodio que unirl/frontera.py (K intentos, reflexión, EVAL con tope, lemas cu_ que solo entran al cuaderno por
veredicto del kernel; con el arreglo del contexto duplicado en CC), pero sobre las tareas de
prometeo_lean/aprobados/Corpus/corpus_v<N>.jsonl, que se compilan en corpus_compilar/corpus_lean (Mathlib v4.34.1 +
FormalConjecturesForMathlib parcheada). Lo nuevo frente a la frontera:

  1. Carga con doble SHA: el archivo del corpus contra SHA256SUMS_corpus<N> y cada tarea contra su sha256_tarea.
  2. Fidelidad del enunciado, por dos vías independientes (revisión adversarial del 24 oct, REVISION_FABLE.md):
     (a) por el kernel: antes de cualquier texto del modelo, el enunciado aprobado se elabora como
         `private axiom unirl_ref_<nonce> <binders> : <tipo>` y, tras la prueba, el archivo exige
         `theorem unirl_chk_<nonce> : type_of% @unirl_ref_<nonce> := @nombre`. Si algo del modelo (una instancia, un
         `include`, una instancia por omisión…) cambió el significado del enunciado sin tocar su texto, el kernel no lo
         acepta (STATEMENT_DRIFT). Sirve para binders, universos, `variable` e `include`.
     (b) por el texto: la salida de `#check @nombre`, elaborado solo, se compara con la del archivo juzgado tras una marca
         con nonce. Es la señal de auditoría; no basta sola (los argumentos de instancia no se imprimen).
     ACCEPTED exige las dos, más los axiomas estándar tanto del teorema como de unirl_chk.
  3. Segundo testigo: toda prueba aceptada se vuelve a compilar sola, en un archivo nuevo, con otra marca; si el
     segundo veredicto no es ACCEPTED, la corrida se DETIENE (regla de parar–auditar–rejuzgar del prerregistro v2): los
     episodios en curso paran en su siguiente llamada y no se registran como resultados.
  4. Calibración: una muestra de tareas verdaderas, fuera de las triviales para el martillo, con una semilla fija y
     registrada; las tareas de la muestra quedan marcadas y no pueden entrar después al conjunto de test.
  5. Revisión 2 (25 oct, REVISION_FABLE_2.md): los imports del prefijo son exactamente los de compilar.py (imports_de);
     la cola de modificadores del final del contexto (`omit … in`, docstring…) se repite delante del axioma de
     referencia y del teorema (cola_contexto); la lista de axiomas de #print axioms se lee aunque Lean la parta en
     varias líneas; una salida incompleta de Lean es SIN_SALIDA_LEAN (no UNSOUND); y, apagadas por omisión, dos
     opciones para los cortes por max_tokens sin texto (--recorte, --task-budget).
  6. Revisión de estructura (25 oct, REVISION_ESTRUCTURA.md): la llamada a la API coincide con la de steprl (sin
     `thinking` explícito); cada llamada registra el modelo que la API devolvió, el id y el stop_reason; el uso de una
     llamada fallida no hereda el de la anterior; la caché de referencias se indexa por el texto compilado (no solo
     por el SHA de la tarea); meta.json lleva huellas de Lean/Mathlib, corpus, muestra, precios y sistema; Lean corre
     sin secretos en el entorno; los filtros de prohibidos se aplican también sin «» (cierre de evasión; CAMBIO DE
     PROTOCOLO menor, ver §J del informe) y EVAL no puede leer el entorno ni lanzar procesos; y, para el diseño
     confirmatorio: --orden-semilla, --continuar, --config SC,CC intercalado por tarea, --serial-familia,
     --cuadernos-de/--cuaderno-fraccion/--cuaderno-congelado, y el tamaño del cuaderno al inicio de cada episodio.
  7. Versión 5 (25 oct, REVISION_V5.md; aprobada por Carlos a las 16:30): la referencia del kernel ya no es un
     `axiom` sino `private theorem unirl_ref_<nonce> <binders> : <tipo> := unirl_sorry_<nonce>`, donde
     `private axiom unirl_sorry_<nonce>.{unirl_u} {α : Sort unirl_u} : α` se declara justo antes. Motivo: `axiom`
     incluye solo las variables de sección que su tipo USA (elabAxiom: mkForallFVars … usedOnly), mientras que
     `theorem` incluye además las instancias `[…]` de `variable` cuyas dependencias están incluidas; con un contexto
     como `variable {C : Type u} [Category C] [HasFiniteLimits C]` la referencia quedaba más fuerte que el teorema
     aprobado y unirl_chk fallaba con Type mismatch (LeanCat 0038, 0044, 0089, 0094, 0095: excluidas sin veredicto
     falso). Como theorem, Lean aplica a la referencia la MISMA regla de inclusión que al teorema. No se usa `sorry`
     (frontera lo marca UNSOUND y sorryAx entraría en los axiomas): el axioma auxiliar lleva nonce, es privado y, si
     una prueba lo usara (directamente o vía unirl_ref_), #print axioms lo delata → UNSOUND. Además, el teorema
     aprobado se nombra `_root_.<ns.>nombre` en unirl_chk, en el #check de la marca y en #print axioms: un nombre
     igual al de Mathlib (LeanCat 0080, `isIso_iff_mono_and_epi` con `open CategoryTheory`) era ambiguo. La caché de
     referencias pasa a .ref5 (clave con el mecanismo): ninguna .ref3 de la v4 se reutiliza.

    python -m unirl.corpus_confirmatorio tarea <id>                   # la tarea, sus SHA y el texto (sin Lean ni API)
    python -m unirl.corpus_confirmatorio humo                         # Lean real + proveedor simulado (sin API)
    python -m unirl.corpus_confirmatorio muestra --n 100 --semilla 20261025
    python -m unirl.corpus_confirmatorio calibrar --modelo claude-haiku-5-5 --config SC --tope-usd 5 --paralelo 5
    python -m unirl.corpus_confirmatorio calibrar --muestra m.json --config SC,CC --orden-semilla 20261025 ...
    python -m unirl.corpus_confirmatorio calibrar --continuar runs/unirl/confirmatorio/calibracion/<corrida> --tope-usd 20

Claude no lanza corridas con API sin la autorización explícita de Carlos registrada en aprobados/FECHA.
"""

from __future__ import annotations

import argparse
import concurrent.futures as cf
import hashlib
import json
import os
import random
import re
import secrets
import subprocess
import sys
import tempfile
import threading
import time
import types
from dataclasses import asdict, dataclass, replace
from datetime import datetime
from pathlib import Path

from . import frontera as F
from .gasto import PRECIOS, GastoExcedido, Libro, ProveedorContable, costo
from .loop import ProviderFatal, Rechazo, complete_with_retries

BASE = F.BASE
PROMETEO = F.PROMETEO
CORPUS_DIR = PROMETEO / "aprobados" / "Corpus"
LEAN_CORPUS = Path(os.environ.get("UNIRL_CORPUS_LEAN",
                                  str(BASE.parent / "Proyecto Godel" / "corpus_compilar" / "corpus_lean")))
MARTILLO = Path(os.environ.get("UNIRL_MARTILLO",
                               str(BASE.parent / "Proyecto Godel" / "corpus_compilar" / "resultados_martillo" / "martillo.jsonl")))
RUNS = BASE / "runs" / "unirl" / "confirmatorio"
LIBRO = BASE / "logs" / "gasto_confirmatorio.json"
TOPE_GLOBAL_USD = float(os.environ.get("UNIRL_TOPE_CONFIRMATORIO_USD", 30.0))
OPCIONES = ["set_option relaxedAutoImplicit false", "set_option maxSynthPendingDepth 3"]
NOMBRE = re.compile(r"^(\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+)([^\s:({\[]+)",
                    re.M)
# `:= by sorry`, admitiendo líneas de comentario entre `by` y `sorry` (5 tareas de variantes_frontera las traen).
SORRY_FIN = re.compile(r":=\s*by(?:\s*--[^\n]*)*\s*sorry\s*$")
# Lo que frontera._PROHIBIDO no cubre y podría falsear la vía textual de la fidelidad o el alcance de los binders:
# delaboradores/unexpanders/opciones pp (cambian cómo se IMPRIME un tipo), include/omit (cambian qué variables entran
# al enunciado aprobado), default_instance (cambia cómo se ELABORA el enunciado).
_PROHIBIDO_EXTRA = re.compile(r"\bdelab\w*\b|\bapp_delab\b|\bapp_unexpander\b|\bunexpander\b|\bpp_\w+|\bLean\.PrettyPrinter\b"
                              r"|\bLean\.Parser\b|\bLean\.Syntax\b|\binclude\b|\bomit\b|\bdefault_instance\b", re.M)
# Solo en EVAL (el único sitio con cadenas y comandos #): leer el entorno del proceso (la clave de la API está en él,
# load_dotenv la pone en os.environ y `lake env lean` la heredaría), lanzar procesos o tocar el sistema de archivos.
_PROHIBIDO_EVAL = re.compile(r"\bIO\.getEnv\b|\bIO\.Process\b|\bIO\.FS\b|\bIO\.appPath\b|\bIO\.currentDir\b"
                             r"|\bSystem\.FilePath\.(?:readDir|walkDir|pathExists|isDir|metadata)\b", re.M)
MIN_FALLOS_PROVEEDOR = 3  # fallos seguidos del proveedor sin ninguna respuesta útil en la corrida: se aborta
_LOCK_REG = threading.Lock()
# Variables de entorno que Lean no necesita y que no deben llegar al subproceso (ni, vía EVAL, al modelo ni al registro).
_ENV_SECRETO = re.compile(r"API_KEY|_TOKEN$|TOKEN_|SECRET|PASSWORD|CREDENTIAL|^ANTHROPIC_|^OPENAI_", re.I)


def sin_guillemets(txt: str) -> str:
    """Lean admite «nombre» como el identificador nombre: `IO.«FS».readFile` o `Lean.«ofReduceBool»` esquivaban los
    filtros de palabras (que son expresiones regulares sobre el texto crudo). Los filtros se aplican al texto tal
    cual Y a esta forma normalizada (cierre de evasión; no añade palabras prohibidas)."""
    return txt.replace("«", "").replace("»", "")


def prohibido_en(texto: str, extra: bool = True, eval_: bool = False) -> str | None:
    """Motivo de rechazo, o None: las listas de frontera (_PROHIBIDO, _NATIVO), la lista extra de este arnés y, en
    EVAL, lo que lee el entorno o lanza procesos; todo sobre el texto normalizado (sin «»)."""
    for txt in (texto, sin_guillemets(texto)):
        m = F._PROHIBIDO.search(txt) or F._NATIVO.search(txt) or (extra and _PROHIBIDO_EXTRA.search(txt)) \
            or (eval_ and _PROHIBIDO_EVAL.search(txt))
        if m:
            return f"contiene «{m.group(0).strip()}» (prohibido)"
    return None


def entorno_sin_secretos(env: dict | None = None) -> dict:
    return {k: v for k, v in (os.environ if env is None else env).items() if not _ENV_SECRETO.search(k)}


class LakeSinSecretos(F.Lake):
    """frontera.Lake, pero el subproceso de Lean recibe el entorno sin claves ni tokens: un EVAL con `IO.getEnv
    "ANTHROPIC_API_KEY"` devolvía la clave al modelo y la dejaba en intentos.jsonl. Mismo sandbox, mismo comando."""

    def compilar(self, texto: str) -> dict:
        if not self.lake:
            return {"rc": -1, "salida": "no se encontró lake (UNIRL_LAKE, ~/.elan/bin/lake o PATH)", "s": 0.0}
        v = F.version_lean(self.version())
        if v is None or v < F.LEAN_MINIMO:
            return {"rc": -1, "salida": f"{self.version()}: hace falta Lean ≥ {'.'.join(map(str, F.LEAN_MINIMO))}", "s": 0.0}
        self.scratch.mkdir(parents=True, exist_ok=True)
        w = Path(tempfile.mkdtemp(prefix="intento-", dir=str(self.scratch)))
        f = w / "Intento.lean"
        f.write_text(texto, encoding="utf-8")
        cmd = [str(self.lake), "env", "lean", str(f)]
        if self.aislado:
            cmd = ["/usr/bin/sandbox-exec", "-p", F._perfil(w, self.raiz)] + cmd
        t = time.perf_counter()
        p = subprocess.Popen(cmd, cwd=self.raiz, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                             encoding="utf-8", errors="replace", start_new_session=True, env=entorno_sin_secretos())
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


class CorridaDetenida(ProviderFatal):
    """El segundo testigo no confirmó una prueba aceptada: se detiene todo para auditar (prerregistro v2, §9)."""


def _registrar(ruta: Path, d: dict) -> None:
    """Como frontera._registrar, pero con cerrojo: con paralelo 5, dos hilos que escriben líneas largas (los prompts
    completos) en el mismo JSONL se entremezclaban."""
    with _LOCK_REG:
        F._registrar(ruta, d)


# ============================================================================== carga con doble SHA


def _sha(t: str) -> str:
    return hashlib.sha256(t.encode()).hexdigest()


def _modulo(m: str) -> str:
    return ".".join(p if (p[:1].isalpha() or p[:1] == "_" or p.startswith("«")) else f"«{p}»" for p in m.split("."))


def _sin_comentarios(txt: str) -> str:
    out, i, prof, n = [], 0, 0, len(txt)
    while i < n:
        if txt.startswith("/-", i):
            prof += 1; i += 2; continue
        if prof and txt.startswith("-/", i):
            prof -= 1; i += 2; continue
        if prof:
            out.append("\n" if txt[i] == "\n" else " "); i += 1; continue
        if txt.startswith("--", i):
            j = txt.find("\n", i); i = n if j < 0 else j; continue
        out.append(txt[i]); i += 1
    return "".join(out)


def scopes_abiertos(txt: str) -> list[tuple[str, str | None]]:
    pila: list[tuple[str, str | None]] = []
    for ln in _sin_comentarios(txt).splitlines():
        s = ln.strip()
        if m := re.match(r"^(?:noncomputable\s+)?section(?:\s+([^\s]+))?\s*$", s):
            pila.append(("section", m.group(1))); continue
        if m := re.match(r"^namespace\s+([^\s]+)", s):
            pila.append(("namespace", m.group(1))); continue
        if re.match(r"^mutual\s*$", s):
            pila.append(("mutual", None)); continue
        if re.match(r"^end(?:\s+([^\s]+))?\s*$", s) and pila:
            pila.pop()
    return pila


def cargar_corpus(version: int = 1, raiz: Path = PROMETEO) -> dict[str, dict]:
    """Las tareas del corpus aprobado v<version>; falla si el archivo o alguna tarea no coincide con su SHA."""
    arch = raiz / "aprobados" / "Corpus" / f"corpus_v{version}.jsonl"
    sumas = raiz / "aprobados" / f"SHA256SUMS_corpus{version}"
    texto = arch.read_text(encoding="utf-8")
    esperado = {l.split(None, 1)[1].strip().lstrip("*"): l.split(None, 1)[0]
                for l in sumas.read_text(encoding="utf-8").splitlines() if l.strip()}
    if esperado.get(f"aprobados/Corpus/corpus_v{version}.jsonl") != _sha(texto):
        raise ValueError(f"corpus_v{version}.jsonl no coincide con SHA256SUMS_corpus{version}: no se usa")
    tareas = {}
    for l in texto.splitlines():
        if not l.strip():
            continue
        r = json.loads(l)
        ctx = (r.get("contexto_lean") or "").rstrip("\n")
        st = r["enunciado_lean"].strip("\n")
        if _sha(ctx + "\n\n" + st) != r["sha256_tarea"]:
            raise ValueError(f"{r['id']}: el texto no coincide con su sha256_tarea")
        tareas[r["id"]] = r
    return tareas


REF_SENTINELA = "UNIRL_NOMBRE_DE_LA_REFERENCIA"
# El cuerpo de la referencia (v5): se sustituye por `unirl_sorry_<nonce>`, el axioma auxiliar que _ref_y_chk declara
# justo antes. Así la referencia es un `theorem` (misma regla de inclusión de variables de sección que el teorema
# aprobado) sin la palabra `sorry` ni el axioma sorryAx.
SORRY_SENTINELA = "UNIRL_CUERPO_DE_LA_REFERENCIA"
# Universo del axioma auxiliar: explícito (no depende de autoImplicit) y con un nombre que ningún contexto declara
# (`universe u` en el contexto + `.{u}` en la declaración sería «universe level already declared»).
UNIVERSO_AUX = "unirl_u"
# Etiqueta del mecanismo de referencia; entra en la clave de la caché de referencia() y en la extensión del archivo
# (.ref5): una referencia calculada con el mecanismo de la v4 (.ref3) no sirve a un archivo juzgado de la v5 aunque
# el texto impreso por #check sea, salvo ambigüedad, el mismo.
MECANISMO_REF = "v5:theorem+unirl_sorry+_root_"
# Comandos que, terminados en `in`, modifican SOLO el comando siguiente (Lean 4): si quedan al final del contexto
# aprobado, en la fase de compilación se aplicaron al teorema; en el archivo juzgado deben aplicarse a la referencia
# Y al teorema, nunca a lo que el modelo escriba en medio.
_COMANDOS_IN = ("open", "omit", "include", "variable", "set_option", "attribute", "universe")


def imports_de(r: dict) -> list[str]:
    """Los imports con los que compilar.py (fase de compilación del corpus) compiló la tarea, reproducidos exactamente:
    Mathlib; si las dependencias nombran FormalConjecturesForMathlib, sus módulos concretos (los que el registro trae
    en `imports`) o, si no trae ninguno, la biblioteca entera; y FormalConjecturesUtil si está en las dependencias.
    Antes se tomaba `imports` tal cual, y 157 tareas del corpus v1 (deps con FCM, `imports` = [Mathlib]) perdían la
    notación ℝ² / ℝ^n de FCM.Geometry: el enunciado aprobado no elaboraba (error_referencia) sin gastar API."""
    deps = " ".join(r.get("dependencias") or [])
    imps = ["Mathlib"]
    if "FormalConjecturesForMathlib" in deps:
        mods = [x for x in (r.get("imports") or []) if x.startswith("FormalConjecturesForMathlib")]
        imps += mods if mods else ["FormalConjecturesForMathlib"]
    if "FormalConjecturesUtil" in deps:
        imps.append("FormalConjecturesUtil")
    return imps


def _comentarios(txt: str) -> list[tuple[int, int, str]]:
    """Tramos de comentario (inicio, fin, clase) de un texto Lean: 'doc' (/-- -/), 'moddoc' (/-! -/), 'bloque' (/- -/,
    anidable) y 'linea' (-- hasta el fin de línea). Aproximado: ignora cadenas, como compilar.py."""
    out, i, n = [], 0, len(txt)
    while i < n:
        if txt.startswith("/-", i):
            clase = "doc" if txt.startswith("/--", i) else ("moddoc" if txt.startswith("/-!", i) else "bloque")
            j, prof = i + 2, 1
            while j < n and prof:
                if txt.startswith("/-", j):
                    prof += 1; j += 2
                elif txt.startswith("-/", j):
                    prof -= 1; j += 2
                else:
                    j += 1
            out.append((i, j, clase)); i = j; continue
        if txt.startswith("--", i):
            j = txt.find("\n", i); j = n if j < 0 else j
            out.append((i, j, "linea")); i = j; continue
        i += 1
    return out


def cola_contexto(ctx: str) -> tuple[str, str]:
    """(cuerpo, cola): la cola son los modificadores del FINAL del contexto que Lean aplica al comando siguiente —
    `omit … in`, `variable … in`, `open … in`, `universe u in`, `attribute […] … in` (también multilínea), atributos
    `@[…]` sueltos y la docstring `/-- … -/` del teorema—, con los comentarios que haya entre ellos. En la fase de
    compilación el teorema iba justo detrás del contexto y recibía esos modificadores; el arnés intercala el axioma de
    referencia (y, en el archivo juzgado, el cuaderno y AUX), así que la cola debe repetirse delante del axioma y
    delante del teorema. Sin esto, `omit [CharZero K] in` caía sobre el axioma: el teorema quedaba con una hipótesis
    de más (más fácil que el aprobado) y unirl_chk fallaba con Type mismatch (tareas 0 y 4 del diagnóstico del 25 oct).
    Si el final no es reconocible, la cola es vacía (conservador: referencia() lo detectaría)."""
    s = ctx.rstrip()
    tramos = {fin: (ini, clase) for ini, fin, clase in _comentarios(s)}
    pos, corte = len(s), None
    while True:
        pos = len(s[:pos].rstrip())
        if pos == 0:
            break
        if pos in tramos:
            ini, clase = tramos[pos]
            pos = ini
            if clase == "doc":
                corte = ini
            elif clase == "moddoc":
                break  # un /-! … -/ es un comentario de módulo: no modifica al comando siguiente
            continue  # comentario corriente: inerte, se salta sin comprometer el corte
        ini_linea = s.rfind("\n", 0, pos) + 1
        linea = s[ini_linea:pos]
        if re.fullmatch(r"\s*@\[[^\]\n]*\]\s*", linea):
            pos = corte = ini_linea
            continue
        if re.search(r"(?:^|[\s\]\)])in\s*$", linea):
            j = ini_linea
            while j > 0 and (s[j:j + 1].isspace() or s[j:j + 1] == ""):  # líneas de continuación (indentadas)
                j = s.rfind("\n", 0, j - 1) + 1
            primera = s[j:s.find("\n", j) if s.find("\n", j) >= 0 else len(s)]
            if primera.split()[:1] and primera.split()[0] in _COMANDOS_IN:
                pos = corte = j
                continue
        break
    if corte is None:
        return s, ""
    return s[:corte].rstrip(), s[corte:].strip("\n")


def tarea_de(r: dict) -> dict:
    """La tarea en la forma que usan admitir_bloque y evaluar_evals de frontera.py, más lo propio del corpus."""
    ctx = (r.get("contexto_lean") or "").rstrip("\n")
    st = r["enunciado_lean"].strip("\n")
    m = NOMBRE.search(st)
    if not m or not SORRY_FIN.search(st):
        raise ValueError(f"{r['id']}: no reconozco el enunciado (theorem … := by sorry)")
    imps = imports_de(r)
    cab = "\n".join([f"import {_modulo(x)}" for x in imps] + OPCIONES) + "\n\n"
    abiertos = scopes_abiertos(ctx + "\n" + st)
    cierre = "".join(f"\nend {n}\n" if n else "\nend\n" for _, n in reversed(abiertos))
    ns = ".".join(n for k, n in abiertos if k == "namespace" and n)
    cuerpo, cola = cola_contexto(ctx)
    pre = cola + "\n" if cola else ""
    # La referencia del kernel (v5): el MISMO encabezado aprobado (binders y tipo, con su `open … in` si lo trae y con
    # la cola de modificadores del contexto), como `private theorem` con nombre de nonce y cuerpo `unirl_sorry_<nonce>`
    # (el axioma auxiliar que _ref_y_chk declara delante). Es theorem y no axiom para que Lean le incluya las mismas
    # variables de sección que al teorema aprobado (ver §7 del módulo). El cuerpo va en línea nueva: si el encabezado
    # terminara en un comentario `-- …`, un `:=` en la misma línea quedaría dentro del comentario. `private` lo esconde
    # de exact?/apply?; si aun así una prueba lo usara, #print axioms muestra unirl_sorry_<nonce> y el veredicto es UNSOUND.
    decl_ref = (SORRY_FIN.sub("", st[:m.start(1)] + f"private theorem {REF_SENTINELA}" + st[m.end(2):]).rstrip()
                + f"\n    := {SORRY_SENTINELA}")
    return {"id": r["id"], "sha": r["sha256_tarea"], "familia": r.get("familia"), "fuente": r.get("fuente"),
            "verdad": r.get("verdad"), "imports": imps, "prefijo": cab + cuerpo + "\n", "cola": cola, "cierre": cierre,
            "ns": ns, "nombre": m.group(2), "cabecera_enunciado": pre + SORRY_FIN.sub(":= by", st),
            "enunciado": pre + st, "decl_ref": pre + decl_ref}


# ============================================================================== fidelidad y juicio


def _texto_tras(salida: str, marca: str, hasta: str | None = None) -> str | None:
    i = salida.find(marca)
    if i < 0:
        return None
    resto = salida[i + len(marca):]
    if hasta and (j := resto.find(hasta)) >= 0:
        resto = resto[:j]
    lineas = [re.sub(r"^[^\n']*?:\d+:\d+: (?:info|information): ", "", l) for l in resto.splitlines()]
    lineas = [l for l in lineas if not re.match(r"^\s*'.*' (?:depends on axioms|does not depend on any axioms)", l)]
    return " ".join(" ".join(lineas).split())


def axiomas_tras_marca(salida: str, nonce: str, nombre_completo: str) -> list[str] | None:
    """Como frontera.axiomas_tras_marca, pero admite la lista de axiomas partida en varias líneas. Lean imprime
    `'{nombre}' depends on axioms: {lista}` con la lista en un `group` separado por `Format.line` (Lean.Message:
    `ofList`/`sbracket`/`joinSep … (ofFormat "," ++ Format.line)`): si la línea pasa del ancho (120), TODAS las comas
    rompen línea. Con nombres completos largos (257 tareas del corpus v1 tienen `ns.nombre` de 60+ caracteres, y
    `ns.unirl_chk_<nonce>` lo pasa en 195) la versión de una sola línea devolvía None y el veredicto era
    UNSOUND «no apareció la línea de #print axioms» sobre una prueba correcta. None si la marca o la línea no están."""
    i = salida.find(f"UNIRL_MARCA_{nonce}")
    if i < 0:
        return None
    resto = "\n".join(re.sub(r"^[^\n']*?:\d+:\d+: (?:info|information): ", "", l)
                      for l in salida[i:].splitlines()[1:])
    for m in re.finditer(r"^'([^\n]+?)' depends on axioms: \[([^\]]*)\]", resto, re.M):
        if m.group(1) == nombre_completo:
            return [a.strip() for a in m.group(2).replace("\n", " ").split(",") if a.strip()]
    for m in re.finditer(r"^'([^\n]+?)' does not depend on any axioms\s*$", resto, re.M):
        if m.group(1) == nombre_completo:
            return []
    return None


# frontera._veredicto busca `axiomas_tras_marca` en su propio módulo; para que los lemas (admitir_bloque) y la prueba
# principal se juzguen con el lector tolerante a listas partidas, se sustituye ahí al importar este módulo. Es un
# superconjunto estricto del original (misma respuesta cuando la lista cabe en una línea; prueba en tests/unirl).
# No afecta a `python -m unirl.frontera`, que no importa este módulo. frontera.py no se modifica.
F.axiomas_tras_marca = axiomas_tras_marca

SIN_SALIDA = "SIN_SALIDA_LEAN"


def _sin_salida(c: dict, v: dict) -> dict | None:
    """Lean no llegó a emitir el veredicto: se cayó (señal distinta del timeout), terminó mal sin reportar ningún
    error, o terminó bien sin imprimir la marca/los axiomas. No es una prueba ni una prueba con axioma ajeno: antes se
    etiquetaba UNSOUND («no apareció la línea de #print axioms») o PROOF_FAILED, y se confundía con el modelo."""
    sal = c["salida"]
    if v["etiqueta"] == "PROOF_FAILED" and c["rc"] < 0 and c["rc"] not in (-9, -1):
        return {"etiqueta": SIN_SALIDA, "motivo": f"Lean murió con la señal {-c['rc']} (sin veredicto)"}
    if v["etiqueta"] == "PROOF_FAILED" and c["rc"] > 0 and not re.search(r":\d+:\d+: error", sal):
        return {"etiqueta": SIN_SALIDA, "motivo": f"Lean terminó con código {c['rc']} sin reportar ningún error (sin veredicto)"}
    if v["etiqueta"] == "UNSOUND" and "no apareció la línea de #print axioms" in v.get("motivo", ""):
        return {"etiqueta": SIN_SALIDA, "motivo": "Lean terminó sin imprimir la marca o los axiomas del teorema (salida incompleta)"}
    return None


def partes_nombre(t: dict) -> tuple[str, str]:
    """(namespace efectivo, nombre efectivo) del teorema aprobado. Si el enunciado lo declara como `_root_.X` dentro de
    un namespace, su nombre completo es `X` y el namespace no cuenta (antes se comparaba contra `ns._root_.X`, que
    #print axioms nunca imprime)."""
    nombre, ns = t["nombre"], t.get("ns", "")
    if nombre.startswith("_root_."):
        return "", nombre[len("_root_."):]
    return ns, nombre


def nombre_completo(t: dict) -> str:
    """`<ns.>nombre`, tal como lo imprime `#print axioms` (sin `_root_`)."""
    ns, nombre = partes_nombre(t)
    return f"{ns}.{nombre}" if ns else nombre


def nombre_root(t: dict) -> str:
    """`_root_.<ns.>nombre`: cómo se nombra al teorema aprobado en todo lo que escribe el juez (unirl_chk, el #check de
    la marca y #print axioms). Resuelve de forma exacta (ResolveName.resolveExact), así que un nombre igual al de un
    teorema de Mathlib abierto con `open` (LeanCat 0080) ya no es ambiguo. El texto que imprime #check no cambia: el
    término elaborado es la misma constante y el delaborador imprime el nombre más corto que no sea ambiguo (con
    ambigüedad, `_root_.nombre`; sin ella, lo mismo que antes)."""
    return "_root_." + nombre_completo(t)


def _axioma_aux(nonce: str) -> str:
    """`private axiom unirl_sorry_<nonce>.{unirl_u} {α : Sort unirl_u} : α`: el cuerpo de la referencia. Universo
    explícito con nombre propio (ver UNIVERSO_AUX). Aparece antes de la cola de modificadores del contexto para que un
    `omit … in` caiga sobre la referencia y no sobre él."""
    return f"private axiom unirl_sorry_{nonce}.{{{UNIVERSO_AUX}}} {{α : Sort {UNIVERSO_AUX}}} : α"


def _ref_y_chk(t: dict, nonce: str) -> tuple[str, str, str, str]:
    """(declaración de la referencia —axioma auxiliar, cola del contexto y `private theorem unirl_ref_<nonce>`—,
    nombre de la referencia, teorema de comprobación, nombre de la comprobación). unirl_chk solo depende del TIPO de la
    referencia (`type_of%` devuelve el tipo elaborado de la constante, no la constante), así que sus axiomas son los de
    la prueba del teorema aprobado: unirl_sorry_<nonce> solo aparece en ellos si la prueba usó la referencia."""
    ref, chk = f"unirl_ref_{nonce}", f"unirl_chk_{nonce}"
    decl = _axioma_aux(nonce) + "\n\n" + t["decl_ref"].replace(REF_SENTINELA, ref).replace(SORRY_SENTINELA, f"unirl_sorry_{nonce}")
    teorema = f"theorem {chk} : (type_of% @{ref}) := @{nombre_root(t)}"
    return decl, ref, teorema, chk


def _lineas_con_error(salida: str) -> set[int]:
    return {int(m.group(1)) for m in re.finditer(r":(\d+):\d+: error", salida)}


def referencia(t: dict, lake, cache: Path | None = None) -> str:
    """El tipo del enunciado aprobado tal como lo imprime `#check @nombre`, elaborado solo (sin texto del modelo).
    De paso comprueba, para esta tarea, que el mecanismo del kernel (axioma de referencia + unirl_chk) elabora sin
    errores con el enunciado aprobado tal cual: si no, la tarea no se juzga (error_referencia) y no gasta API."""
    # La clave de la caché es el texto que se compila (prefijo con sus imports, cola, referencia, enunciado, cierre),
    # la versión de Lean y el mecanismo de referencia (MECANISMO_REF): antes era solo el SHA de la tarea, y una
    # referencia calculada con otros imports (como pasó al corregir imports_de) o con otro Lean habría servido a un
    # archivo juzgado distinto → DRIFT textual falso. La extensión .ref5 (antes .ref3) impide reutilizar la caché de la v4.
    clave = _sha("\n".join([MECANISMO_REF, t["prefijo"], t["decl_ref"], t["enunciado"], t["cierre"],
                            str(getattr(lake, "version", lambda: "")())]))[:24]
    if cache and (p := cache / f"{t['sha'][:24]}-{clave}.ref5").exists():
        return p.read_text(encoding="utf-8")
    nonce = secrets.token_hex(8)
    decl, _, chk, _ = _ref_y_chk(t, nonce)
    texto = (t["prefijo"] + "\n" + decl + "\n\n" + t["enunciado"] + "\n\n" + chk
             + f'\n\n#eval IO.println "UNIRL_REF_{nonce}"\n#check @{nombre_root(t)}\n#eval IO.println "UNIRL_REFFIN_{nonce}"\n'
             + t["cierre"])
    c = lake.compilar(texto)
    ref = _texto_tras(c["salida"], f"UNIRL_REF_{nonce}", f"UNIRL_REFFIN_{nonce}")
    if not ref or c["rc"] != 0 or re.search(r":\d+:\d+: error", c["salida"]):
        raise ValueError(f"{t['id']}: el enunciado aprobado (o su referencia del kernel) no elabora solo: {c['salida'][-600:]}")
    if cache:
        cache.mkdir(parents=True, exist_ok=True)
        (cache / f"{t['sha'][:24]}-{clave}.ref5").write_text(ref, encoding="utf-8")
    return ref


def archivo_principal(t: dict, contexto_lean: str, aux: str, prueba: str) -> tuple[str, str, int]:
    """(archivo, nonce, línea del teorema de comprobación). Orden: contexto aprobado → axioma auxiliar y referencia
    (antes de todo texto del modelo) → cuaderno/lemas → AUX → enunciado aprobado + prueba → unirl_chk → marcas, #check
    y #print axioms del teorema (nombrado `_root_.<ns.>nombre`) y de unirl_chk → cierre de scopes."""
    nonce = secrets.token_hex(8)
    decl, _, chk, chk_nombre = _ref_y_chk(t, nonce)
    cuerpo = (t["prefijo"] + "\n" + decl + "\n\n" + contexto_lean + "\n\n" + (aux.strip() + "\n\n" if aux else "")
              + t["cabecera_enunciado"] + "\n" + F._indentar(prueba) + "\n\n")
    linea_chk = cuerpo.count("\n") + 1
    completo = nombre_root(t)
    sufijo = (chk + f'\n\n#eval IO.println "UNIRL_MARCA_{nonce}"\n#check @{completo}\n'
              f'#eval IO.println "UNIRL_FIN_{nonce}"\n#print axioms {completo}\n#print axioms {chk_nombre}\n' + t["cierre"])
    return cuerpo + sufijo, nonce, linea_chk


def juzgar_principal(t: dict, lake, contexto_lean: str, aux: str, prueba: str, ref: str) -> dict:
    if aux:
        motivo, _ = F.filtrar_declaraciones(aux, ("aux_", "cu_"), exigir_teorema=False)
        if motivo:
            return {"etiqueta": "FORBIDDEN", "motivo": f"AUX: {motivo}"}
    motivo = F.filtrar_prueba(prueba)
    if motivo:
        return {"etiqueta": "FORBIDDEN", "motivo": motivo}
    if motivo := prohibido_en(aux + "\n" + prueba):
        return {"etiqueta": "FORBIDDEN", "motivo": motivo}
    texto, nonce, linea_chk = archivo_principal(t, contexto_lean, aux, prueba)
    c = lake.compilar(texto)
    ns_ef, nombre_ef = partes_nombre(t)
    v = F._veredicto(c, nombre_ef, nonce, ns_ef)
    completo_chk = (t["ns"] + "." if t["ns"] else "") + f"unirl_chk_{nonce}"
    if v["etiqueta"] == "PROOF_FAILED" and (errs := _lineas_con_error(c["salida"])) and errs <= {linea_chk}:
        # el único error es que el teorema demostrado no tiene el tipo que el kernel elaboró antes del texto del modelo
        v = {"etiqueta": "STATEMENT_DRIFT", "motivo": "kernel: el teorema demostrado no tiene el tipo del enunciado aprobado",
             "via": "kernel"}
    if ss := _sin_salida(c, v):
        v = ss
    # v5: la referencia es un theorem cuyo único axioma es unirl_sorry_<nonce>; una prueba que la use (o que use el
    # axioma auxiliar directamente) lo muestra en #print axioms. `unirl_ref_` se conserva por si Lean listara el
    # teorema de referencia como dependencia (no lo hace: solo lista axiomas), sin coste.
    propios = (f"unirl_sorry_{nonce}", f"unirl_ref_{nonce}")
    if v["etiqueta"] == "UNSOUND" and any(p in str(v.get("axiomas", [])) for p in propios):
        v["motivo"] = "la prueba usó la referencia del kernel o su axioma auxiliar (¿exact?/apply?): no es una prueba"
    if v["etiqueta"] == "ACCEPTED":
        ax_chk = axiomas_tras_marca(c["salida"], nonce, completo_chk)
        extra = sorted(set(ax_chk or []) - F.AXIOMAS_OK)
        if ax_chk is None:
            v = {"etiqueta": SIN_SALIDA, "motivo": "unirl_chk: Lean terminó sin imprimir sus axiomas (salida incompleta)"}
        elif extra:
            v = {"etiqueta": "UNSOUND", "motivo": f"unirl_chk: axiomas no permitidos: {extra}", "axiomas_chk": ax_chk}
            if any(p in str(ax_chk) for p in propios):
                v["motivo"] = "unirl_chk depende de la referencia del kernel o de su axioma auxiliar: no es una prueba"
    if v["etiqueta"] == "ACCEPTED":
        tipo = _texto_tras(c["salida"], f"UNIRL_MARCA_{nonce}", f"UNIRL_FIN_{nonce}")
        if tipo != ref:
            v = {"etiqueta": "STATEMENT_DRIFT", "motivo": "texto: el tipo impreso por #check difiere del de la referencia "
                 "(el kernel sí lo aceptó: auditar)", "via": "texto", "tipo": tipo, "referencia": ref}
    # La primera línea «del modelo» para los mensajes de error (AUX o cabecera del teorema): tras el prefijo, la
    # referencia (axioma auxiliar, cola y theorem; su número de líneas no depende del nonce, que siempre tiene 16
    # caracteres) y el cuaderno, como arma archivo_principal. Antes no se contaban las líneas de la referencia y
    # «línea k de tu prueba» salía corrida (en la v5 lo estaría tres líneas más).
    primera = (t["prefijo"] + "\n" + _ref_y_chk(t, "0" * 16)[0] + "\n\n" + contexto_lean + "\n\n").count("\n") + 1
    v.update({"s": c["s"], "errores": F.errores(c["salida"], primera)})
    if v["etiqueta"] == "ACCEPTED":
        v["archivo"] = texto
    return v


def segundo_testigo(t: dict, lake, contexto_lean: str, aux: str, prueba: str, ref: str) -> dict:
    """Recompila la prueba aceptada en un archivo nuevo, con otra marca; debe volver a dar ACCEPTED."""
    return juzgar_principal(t, lake, contexto_lean, aux, prueba, ref)


# ============================================================================== el episodio


SISTEMA = """Eres un matemático que demuestra teoremas en Lean 4 con Mathlib. El kernel de Lean decide qué es verdad; \
tú nunca afirmas que algo está demostrado. Explora con EVAL cuando no sepas qué dice una definición, y parte la \
prueba en lemas pequeños que el kernel certifique.

Cada respuesta tuya es UNA de dos cosas.

(1) Exploración (no gasta intento; hay un tope de turnos):
EVAL: <<< código Lean: def/abbrev/instance/example, #eval, #check, #reduce >>>
(hasta dos bloques EVAL). El sistema lo compila en el contexto del problema y del cuaderno y te devuelve la salida.

(2) Un intento, con cualquiera de estas partes:
REFLEXION: <<< qué aprendiste del intento anterior y qué cambias (máx. 150 palabras) >>>
LEMA: <<< theorem cu_nombre … := by … >>>  (uno o varios bloques; antes del theorem puedes poner def/instance cu_…)
AUX: <<< definiciones auxiliares para la prueba principal (nombres aux_… o cu_…) >>>
PRUEBA: <<< las tácticas de la prueba del teorema pedido, sin `by` >>>

Un LEMA que el kernel acepta entra al cuaderno y queda disponible por su nombre en todo lo que sigue (en la condición \
con cuaderno, también en tareas futuras). Las reflexiones son texto: orientan, no valen como verdad.

Reglas del juez: todo nombre que declares empieza por cu_ (lemas) o aux_ (AUX); las instancias llevan nombre. \
Prohibido: sorry, admit, axiom, native_decide, implemented_by, unsafe, opaque, open, notation, attribute, \
namespace, section, end, import, include, set_option (salvo maxHeartbeats y maxRecDepth), metaprogramación. Solo se \
admiten los axiomas propext, Classical.choice y Quot.sound. El enunciado no se puede cambiar: se compara con el \
aprobado, y una instancia tuya que cambie el significado de un nombre del enunciado lo invalida."""


def construir_prompt(t: dict, cfg, cuad, locales: list[dict], historia: list[dict], intentos_rest: int, turnos_rest: int) -> str:
    p = [f"# La tarea: {t['id']}", "", "El contexto aprobado (no se puede cambiar):", F._md(t["prefijo"], 8000), "",
         "Demuestra este teorema (escribe solo las tácticas en PRUEBA):", F._md(t["cabecera_enunciado"], 4000), ""]
    if cuad is not None and cuad.entradas:
        p += ["# El cuaderno", "", "Lemas certificados por el kernel (úsalos por su nombre):"]
        p += [f"- `{x}` : {e['enunciados'][x]}   ({e['origen']})" for e in cuad.entradas for x in e["teoremas"]] + [""]
    if locales:
        p += ["# Lemas certificados en este episodio", ""] + [f"- `{x}` : {l['enunciados'][x]}" for l in locales
                                                              for x in l["teoremas"]] + [""]
    if historia:
        p += ["# Lo que pasó en este episodio", ""]
        for h in historia[-F.MAX_HISTORIA:]:
            p += [f"## {h['tipo']} {h.get('n', '')}", h["resumen"], ""]
    p += ["# Presupuesto", f"Te quedan {intentos_rest} intentos y {turnos_rest} turnos de exploración.", ""]
    return "\n".join(p)


def _resumen(reg: dict) -> str:
    ls = [f"- LEMA {', '.join(x['resultado'].get('nombres', [])) or '?'}: {x['resultado']['etiqueta']} — "
          f"{(x['resultado'].get('errores') or [x['resultado'].get('motivo', '')])[0][:300]}" for x in reg["lemas"]]
    if "principal" in reg:
        pr = reg["principal"]
        ls.append(f"- PRUEBA: {pr['etiqueta']} — {(pr.get('errores') or [pr.get('motivo', '')])[0][:600]}")
    return "\n".join(ls) or "(sin lemas ni prueba)"


class Vigia:
    """Cuenta, para toda la corrida, las llamadas al proveedor que no devolvieron nada (no los REFUSAL). Si las
    primeras MIN_FALLOS_PROVEEDOR fallan sin que ninguna haya respondido, la corrida se aborta: un max_tokens o un
    modelo mal escrito hacía que las 100 tareas «terminaran» en PROVIDER_ERROR, sin gasto y sin ruido."""

    def __init__(self):
        self.exitos, self.fallos = 0, 0
        self._lock = threading.Lock()

    def anotar(self, exito: bool) -> None:
        with self._lock:
            if exito:
                self.exitos += 1
            else:
                self.fallos += 1
            if self.exitos == 0 and self.fallos >= MIN_FALLOS_PROVEEDOR:
                raise ProviderFatal(f"el proveedor no devolvió ninguna respuesta en {self.fallos} llamadas: revisar modelo, "
                                    "max_tokens y clave antes de seguir")


def _incorporar_cc(t: dict, lake, cuad, lock, hash_inicio: str, bloque: str, rb: dict, origen: str, ep_id: str) -> str:
    """Entra el lema al cuaderno compartido de la familia, bajo cerrojo. Si otro hilo cambió el cuaderno desde que este
    episodio lo leyó, el bloque se recompila sobre el cuaderno ACTUAL (orden final = orden en que se compilará
    después): así ninguna entrada queda certificada contra un cuaderno distinto del que verán las siguientes, y no
    entran dos veces el mismo nombre (que dejaba a toda la familia en «already declared»)."""
    with lock:
        if set(rb["nombres"]) & cuad.nombres():
            return "omitido: el nombre ya estaba en el cuaderno (otro episodio lo certificó antes)"
        if cuad.hash() != hash_inicio:
            rb2 = F.admitir_bloque(t, lake, cuad.lean(), bloque, cuad.nombres())
            if rb2["etiqueta"] != "ACCEPTED":
                return f"omitido: sobre el cuaderno actualizado dio {rb2['etiqueta']}"
            rb = rb2
        F.incorporar(cuad, bloque, rb, origen=origen, episodio=ep_id)
        cuad.guardar()
        return "incorporado"


def episodio(t: dict, cfg, proveedor, lake, cuad, carpeta: Path, ep_id: str, ref: str, lock_cuad=None,
             parar: threading.Event | None = None, vigia: Vigia | None = None, incorporar: bool = True) -> dict:
    """`incorporar=False` (cuaderno congelado): en CC el modelo ve y usa el cuaderno, pero sus lemas no entran a él
    (diseño dosis–respuesta con instantáneas fijas). Por omisión, el comportamiento de siempre."""
    historia, locales = [], []
    intentos, turnos, llamadas = 0, cfg.turnos_exploracion, 0
    res = {"episodio": ep_id, "tarea": t["id"], "config": cfg.nombre, "resuelto": False, "lemas_admitidos": [],
           "intentos": 0, "usd": 0.0, "tokens_salida": 0, "tokens_entrada_no_cache": 0, "fallos_proveedor": 0}
    lock = lock_cuad or threading.Lock()
    if cfg.usa_cuaderno:  # la «dosis»: cuánto cuaderno había al empezar (y al terminar) este episodio
        with lock:
            res["cuaderno_inicio"] = {"n": len(cuad.entradas), "hash": cuad.hash()}
    entradas_vistas: list[dict] = []
    while intentos < cfg.intentos:
        if parar is not None and parar.is_set():
            res["interrumpido"] = True  # la corrida se detuvo (segundo testigo o proveedor): este episodio no vale
            break
        with lock:
            # Una instantánea bajo el cerrojo: el prompt y el contexto Lean deben describir el MISMO cuaderno (otro
            # hilo puede incorporar entre la lectura de lean() y la construcción del prompt).
            entradas_vistas = list(cuad.entradas) if cfg.usa_cuaderno else []
            persistente = cuad.lean() if cfg.usa_cuaderno else ""
            en_cuaderno = cuad.nombres() if cfg.usa_cuaderno else set()
            hash_cuad = cuad.hash() if cfg.usa_cuaderno else ""
        contexto = "\n\n".join(x for x in [persistente] + [l["bloque"] for l in locales
                                                          if not set(l["nombres"]) <= en_cuaderno] if x)
        vista = types.SimpleNamespace(entradas=entradas_vistas) if cfg.usa_cuaderno else None
        prompt = construir_prompt(t, cfg, vista, locales, historia, cfg.intentos - intentos, turnos)
        try:
            texto, rechazo = complete_with_retries(proveedor, SISTEMA, prompt, propagar_rechazo=True), None
        except Rechazo as e:
            texto, rechazo = None, str(e)
        llamadas += 1
        uso = getattr(proveedor, "ultimo_uso", None) or {}
        res["usd"] += float(uso.get("usd", 0) or 0)
        res["tokens_salida"] += int(uso.get("salida", 0) or 0)
        res["tokens_entrada_no_cache"] += int(uso.get("entrada", 0) or 0) - int(uso.get("cache", 0) or 0)
        _registrar(carpeta / "llamadas.jsonl", {"episodio": ep_id, "llamada": llamadas, "prompt_sha": _sha(prompt),
                                                "prompt": prompt, "respuesta": texto, "rechazo": rechazo, "uso": uso,
                                                "fecha": datetime.now().isoformat(timespec="seconds")})
        if texto is None and rechazo is None:
            res["fallos_proveedor"] += 1
        if uso.get("recorte"):  # la llamada se cortó por max_tokens sin texto y se repitió con --recorte (opcional)
            res["recortes"] = res.get("recortes", 0) + 1
        if vigia is not None:
            vigia.anotar(texto is not None or rechazo is not None)
        if texto is None:
            intentos += 1
            historia.append({"tipo": "Intento", "n": intentos, "resumen": "REFUSAL o PROVIDER_ERROR"})
            continue
        r = F.leer(texto)
        if r["evals"] and not r["lemas"] and not r["prueba"]:
            if turnos <= 0:
                historia.append({"tipo": "Exploración", "resumen": "No quedan turnos de exploración: manda un intento."})
                intentos += 1
                continue
            turnos -= 1
            salidas = []
            for cod in r["evals"][:cfg.max_evals_por_turno]:
                if motivo := prohibido_en(cod, extra=False, eval_=True):  # entorno, procesos, archivos; y sin «»
                    salidas.append({"codigo": cod, "salida": f"RECHAZADO: {motivo}", "s": 0.0})
                else:
                    salidas += F.evaluar_evals(t, lake, contexto, [cod])
            _registrar(carpeta / "intentos.jsonl", {"episodio": ep_id, "tipo": "exploracion", "evals": salidas})
            historia.append({"tipo": "Exploración", "resumen": "\n\n".join(
                F._md(s["codigo"], 1500) + "\nSalida:\n" + F._md(s["salida"], 2500) for s in salidas)})
            continue
        intentos += 1
        reg = {"episodio": ep_id, "tipo": "intento", "n": intentos, "reflexion": r["reflexion"], "lemas": []}
        nombres_previos = en_cuaderno | {n for l in locales for n in l["nombres"]}
        for bloque in r["lemas"][:cfg.max_lemas_por_intento]:
            if motivo := prohibido_en(bloque):
                rb = {"etiqueta": "FORBIDDEN", "motivo": motivo, "nombres": []}
            else:
                rb = F.admitir_bloque(t, lake, contexto, bloque, nombres_previos)
            reg["lemas"].append({"bloque": bloque, "resultado": rb})
            if rb["etiqueta"] == "ACCEPTED":
                locales.append({"bloque": bloque.strip(), **rb})
                contexto = "\n\n".join(x for x in [contexto, bloque.strip()] if x)
                nombres_previos |= set(rb["nombres"])
                res["lemas_admitidos"] += rb["teoremas"]
                if cfg.usa_cuaderno and incorporar:
                    reg["lemas"][-1]["cuaderno"] = _incorporar_cc(t, lake, cuad, lock, hash_cuad, bloque, rb,
                                                                  origen=f"{t['id']}, {ep_id}, intento {intentos}", ep_id=ep_id)
                elif cfg.usa_cuaderno:
                    reg["lemas"][-1]["cuaderno"] = "no incorporado: cuaderno congelado"
        if r["prueba"]:
            pr = juzgar_principal(t, lake, contexto, r["aux"], r["prueba"], ref)
            reg["principal"] = {k: v for k, v in pr.items() if k != "archivo"}
            if pr["etiqueta"] == SIN_SALIDA:  # Lean no emitió veredicto: no es una prueba, pero tampoco culpa del modelo
                res["sin_salida_lean"] = res.get("sin_salida_lean", 0) + 1
            if pr["etiqueta"] == "ACCEPTED":
                t2 = segundo_testigo(t, lake, contexto, r["aux"], r["prueba"], ref)
                reg["segundo_testigo"] = t2["etiqueta"]
                if t2["etiqueta"] != "ACCEPTED":
                    reg["segundo_testigo_detalle"] = {k: v for k, v in t2.items() if k != "archivo"}
                    _registrar(carpeta / "intentos.jsonl", reg)
                    raise CorridaDetenida(f"{t['id']}: el segundo testigo dio {t2['etiqueta']} sobre una prueba aceptada")
                (carpeta / "aceptadas").mkdir(exist_ok=True)
                (carpeta / "aceptadas" / f"{re.sub(r'[^A-Za-z0-9_.-]', '_', t['id'])[:150]}.lean").write_text(
                    pr["archivo"], encoding="utf-8")
                # lo que cita es del cuaderno QUE VIO (la instantánea del prompt), no del cuaderno de este instante
                usados = sorted({n for e in entradas_vistas for n in e["teoremas"]
                                 if re.search(rf"\b{re.escape(n)}\b", r["prueba"] + "\n" + r["aux"])})
                res["cita_cuaderno"] = usados
        _registrar(carpeta / "intentos.jsonl", reg)
        historia.append({"tipo": "Intento", "n": intentos, "resumen": _resumen(reg)})
        if reg.get("principal", {}).get("etiqueta") == "ACCEPTED":
            res["resuelto"] = True
            break
    if cfg.usa_cuaderno:
        with lock:
            res["cuaderno_fin"] = {"n": len(cuad.entradas), "hash": cuad.hash()}
    res.update({"intentos": intentos, "llamadas": llamadas, "usd": round(res["usd"], 6)})
    return res


# ============================================================================== proveedores


class ProveedorSeco:
    """Sin API: una exploración, un lema verdadero, una prueba que no sirve y una que se rinde."""
    model = "seco"
    ultimo_uso = None

    def __init__(self):
        self.n = 0

    def complete(self, system: str, user: str) -> str:
        self.n += 1
        if self.n % 4 == 1:
            return "EVAL: <<<\n#eval (2 + 2 : Nat)\n>>>"
        if self.n % 4 == 2:
            return "LEMA: <<<\ntheorem cu_seco : (2 : Nat) + 2 = 4 := by decide\n>>>\nPRUEBA: <<<\nexact absurd rfl rfl\n>>>"
        return "REFLEXION: <<< ensayo en seco >>>\nPRUEBA: <<<\nexact absurd rfl rfl\n>>>"


class LibroConReservas(Libro):
    """El libro de gasto.py más las llamadas EN VUELO de este proceso: con paralelo 5, cinco hilos autorizaban a la vez
    contra el mismo saldo y el tope podía excederse en (paralelo − 1) × peor caso (hasta 4 × 0,64 USD con Sonnet).
    Cada autorización reserva su peor caso hasta que la llamada se registra (o falla)."""

    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self._vuelo: dict[str, float] = {}
        self._reservas = threading.local()
        self._lock_vuelo = threading.Lock()

    def autorizar(self, modelo: str, fase: str, tope_llamadas: int | None, chars_entrada: int, max_salida: int) -> float:
        peor = costo(modelo, chars_entrada // 3 + 1, 0, max_salida)
        with self._lock_vuelo:
            vuelo, vuelo_fase = sum(self._vuelo.values()), self._vuelo.get(fase, 0.0)
            gastado = self.total()
            if gastado + vuelo + peor > self.tope_usd:
                raise GastoExcedido(f"tope de ${self.tope_usd:.2f}: gastado ${gastado:.4f} + en vuelo ${vuelo:.4f}, "
                                    f"la llamada siguiente puede costar hasta ${peor:.4f}")
            if tope_llamadas is not None and self.llamadas(fase) >= tope_llamadas:
                raise GastoExcedido(f"la fase {fase!r} agotó su tope de {tope_llamadas} llamadas")
            tope_fase = self.topes_fase.get(fase)
            if tope_fase is not None and self.gastado(fase) + vuelo_fase + peor > tope_fase:
                raise GastoExcedido(f"tope de la fase {fase!r} (${tope_fase:.2f}): gastado ${self.gastado(fase):.4f} + en vuelo "
                                    f"${vuelo_fase:.4f}, la llamada siguiente puede costar hasta ${peor:.4f}")
            self._vuelo[fase] = vuelo_fase + peor
            self._reservas.pendiente = (fase, peor)
        return peor

    def liberar(self) -> None:
        """Suelta la reserva del hilo actual (tras registrar la llamada, o si falló antes de registrarse)."""
        p = getattr(self._reservas, "pendiente", None)
        if p:
            fase, peor = p
            with self._lock_vuelo:
                self._vuelo[fase] = max(0.0, self._vuelo.get(fase, 0.0) - peor)
            self._reservas.pendiente = None

    def en_vuelo(self) -> float:
        with self._lock_vuelo:
            return round(sum(self._vuelo.values()), 6)

    def registrar(self, modelo: str, fase: str, corrida: str, uso: dict) -> float:
        usd = super().registrar(modelo, fase, corrida, uso)
        self.liberar()
        return usd


RECORTES = ("ninguno", "effort:low", "effort:medium", "sin_pensar")
BETA_TASK_BUDGET = "task-budgets-2026-03-13"  # https://platform.claude.com/docs/en/build-with-claude/task-budgets (25 oct 2026)
CORTE_SIN_TEXTO = "la respuesta se cortó por longitud"  # el mensaje exacto de gasto.ProveedorContable._complete_anthropic


class ProveedorContableReservas(ProveedorContable):
    """Además de soltar la reserva, aplica —solo si el proveedor interno trae `recorte` distinto de None— el reintento
    tras un corte por max_tokens sin texto (REVISION_FABLE_2.md, tarea 2): la misma pregunta se vuelve a hacer UNA vez
    con menos esfuerzo o sin pensamiento previo; las dos llamadas se registran en el libro y `ultimo_uso` suma ambas
    (con el detalle del corte en `recorte`), para que el episodio cargue a la tarea todo lo gastado. Apagado por
    omisión: el comportamiento es el de ayer (PROVIDER_ERROR) salvo que Carlos lo encienda con --recorte."""

    def _anotar_respuesta(self) -> None:
        """Copia a `ultimo_uso` lo que la API dijo de sí misma: el modelo exacto que respondió (`resp.model`, p. ej.
        claude-sonnet-5-5-20261001), el id de la respuesta y el stop_reason. Sin esto, meta y libro solo guardaban
        el nombre PEDIDO; para reproducir una corrida hace falta el que la API devolvió."""
        tl = getattr(self.interno, "_tl", None)
        resp = getattr(tl, "resp", None) if tl is not None else None
        uso = getattr(self._local, "uso", None)
        if resp is not None and isinstance(uso, dict):
            uso.update({"modelo_api": getattr(resp, "model", None), "respuesta_id": getattr(resp, "id", None),
                        "stop_reason": getattr(resp, "stop_reason", None)})
        if tl is not None:
            tl.resp = None

    def complete(self, system: str, user: str) -> str:
        # El uso es por hilo y lo escribe _complete_anthropic DESPUÉS de la respuesta: si el SDK fallaba antes de
        # responder (red, 429 tras los reintentos), `ultimo_uso` seguía siendo el de la llamada anterior del hilo y el
        # episodio lo sumaba otra vez a la tarea y lo copiaba en llamadas.jsonl. El libro no se veía afectado.
        self._local.uso = None
        if (tl := getattr(self.interno, "_tl", None)) is not None:
            tl.resp = None
        try:
            return super().complete(system, user)
        except RuntimeError as e:
            modo = getattr(self.interno, "recorte", None)
            if CORTE_SIN_TEXTO not in str(e) or not modo or modo == "ninguno":
                raise
            corte = dict(self.ultimo_uso or {})
        finally:
            self.libro.liberar()  # si la llamada falló entre autorizar y registrar, la reserva no queda colgada
            self._anotar_respuesta()
        try:
            return self._reintento_tras_corte(system, user, corte, modo)
        finally:
            self.libro.liberar()
            self._anotar_respuesta()

    def _reintento_tras_corte(self, system: str, user: str, corte: dict, modo: str) -> str:
        max_salida = int(getattr(self.interno, "max_output_tokens", 64000))
        self.libro.autorizar(self.model, self.fase, self.tope_llamadas, len(system) + len(user), max_salida)
        resp = self.interno.respuesta(system, user, recorte=True)
        u = resp.usage
        lectura = int(getattr(u, "cache_read_input_tokens", 0) or 0)
        escritura = int(getattr(u, "cache_creation_input_tokens", 0) or 0)
        det = getattr(u, "output_tokens_details", None)
        uso = {"entrada": int(u.input_tokens or 0) + lectura + escritura, "cache": lectura, "cache_escritura": escritura,
               "salida": int(u.output_tokens or 0), "razonamiento": int(getattr(det, "thinking_tokens", 0) or 0),
               **self._ajustes()}
        usd = self.libro.registrar(self.model, self.fase, self.corrida, uso)
        self.calls += 1
        suma = {k: int(corte.get(k, 0) or 0) + uso[k] for k in ("entrada", "cache", "cache_escritura", "salida", "razonamiento")}
        self._local.uso = {**uso, **suma, "usd": round(float(corte.get("usd", 0) or 0) + usd, 6),
                           "recorte": {"modo": modo, "llamada_cortada": corte, "stop_reason": resp.stop_reason}}
        if resp.stop_reason == "refusal":
            raise Rechazo(getattr(getattr(resp, "stop_details", None), "category", None))
        text = "".join(b.text for b in resp.content if getattr(b, "type", "") == "text")
        if resp.stop_reason == "max_tokens" and not text.strip():
            raise RuntimeError(CORTE_SIN_TEXTO + " (también en el reintento)")
        return text if resp.stop_reason == "max_tokens" else self.interno.texto(resp)


def hacer_proveedor(modelo: str, corrida: str, tope_usd: float, effort: str | None, recorte: str | None = None,
                    task_budget: int | None = None):
    from steprl.providers import AnthropicProvider
    if modelo == "claude-haiku-5-5" and modelo not in PRECIOS:
        # https://platform.claude.com/docs/en/about-claude/pricing (consultada el 24 y el 25 oct 2026): $0,10 entrada,
        # $0,01 lectura de caché y $0,50 salida por millón para prompts ≤ 100k tokens. La lectura de caché se cuenta al
        # precio de la entrada (cota superior).
        PRECIOS[modelo] = (0.10, 0.10, 0.50)
    if modelo not in PRECIOS:
        raise GastoExcedido(f"sin precio registrado para {modelo}: no se lanza")
    if recorte not in (None, *RECORTES):
        raise GastoExcedido(f"--recorte debe ser uno de {RECORTES}")
    if task_budget and task_budget < 20000:
        raise GastoExcedido("task_budget.total mínimo: 20 000 tokens (documentación de task budgets)")

    class _Anthropic(AnthropicProvider):
        recorte: str | None = None
        task_budget: int | None = None
        _tl = threading.local()  # la última respuesta cruda de este hilo, para anotar modelo_api/id/stop_reason

        def _kwargs(self, system, user, recorte: bool) -> dict:
            """La misma llamada que steprl.AnthropicProvider.respuesta (comprobado contra steprl/providers.py en la
            revisión de estructura: modelo, max_tokens, system con cache_control, messages y output_config.effort; steprl
            NO envía `thinking`: el pensamiento es adaptativo por omisión en estos modelos), más lo opcional:
            task_budget (beta) y, en el reintento tras un corte, menos esfuerzo (effort:<nivel>) o sin pensamiento
            previo (sin_pensar: `between_tools` en Sonnet 5.5, `disabled` en Haiku 5.5; ambos exigen effort ≤ high).
            Sin esfuerzo (Haiku) no se envía output_config, como hasta hoy."""
            kw = dict(model=self.model, max_tokens=self.max_output_tokens,
                      system=[{"type": "text", "text": system, "cache_control": {"type": "ephemeral"}}],
                      messages=[{"role": "user", "content": user}])
            effort, thinking = self.effort, None
            if recorte and self.recorte and self.recorte.startswith("effort:"):
                effort = self.recorte.split(":", 1)[1]
            elif recorte and self.recorte == "sin_pensar":
                thinking = {"type": "between_tools"} if "sonnet" in self.model else {"type": "disabled"}
                if effort in ("xhigh", "max"):
                    effort = "high"
            oc = {}
            if effort:
                oc["effort"] = effort
            if self.task_budget:
                oc["task_budget"] = {"type": "tokens", "total": int(self.task_budget)}
            if oc:
                kw["output_config"] = oc
            if thinking:
                kw["thinking"] = thinking
            return kw

        def respuesta(self, system, user, recorte: bool = False):
            if self.effort and not recorte and not self.task_budget:
                resp = super().respuesta(system, user)  # la llamada de steprl tal cual (Sonnet con esfuerzo)
            else:
                kw = self._kwargs(system, user, recorte)
                if self.task_budget:
                    with self._client.beta.messages.stream(**kw, betas=[BETA_TASK_BUDGET]) as stream:
                        resp = stream.get_final_message()
                else:
                    with self._client.messages.stream(**kw) as stream:  # sin output_config si no hay esfuerzo (Haiku)
                        resp = stream.get_final_message()
            self._tl.resp = resp
            return resp

    interno = _Anthropic(model=modelo, effort=effort, max_output_tokens=32000 if "haiku" in modelo else 64000)
    interno.recorte = None if recorte in (None, "ninguno") else recorte
    interno.task_budget = int(task_budget) if task_budget else None
    # El modelo es fijo por diseño (modelo congelado): ningún fallback a otro modelo, que además se cobraría al precio
    # equivocado. frontera.hacer_proveedor lo pasa como fallback_model=None; aquí se fuerza el atributo.
    interno.fallback_model = None
    if getattr(interno, "model", modelo) != modelo:
        raise GastoExcedido(f"el proveedor se construyó con {interno.model!r}, no con {modelo!r}")
    fase = f"confirmatorio:{corrida}"
    libro = LibroConReservas(ruta=LIBRO, tope_usd=TOPE_GLOBAL_USD, topes_fase={fase: float(tope_usd)})
    return ProveedorContableReservas(interno, libro, fase=fase, corrida=corrida)


# ============================================================================== muestra de calibración


def triviales_martillo(ruta: Path | None = None) -> set[str] | None:
    ruta = Path(ruta) if ruta else MARTILLO
    if not ruta.exists():
        return None
    return {r["id"] for r in map(json.loads, ruta.read_text(encoding="utf-8").splitlines()) if r.get("cierran")}


def censo_martillo(ruta: Path | None = None) -> dict | None:
    """El censo entero: `triviales` (alguna táctica cierra), `sin_veredicto` (el martillo no pudo decidir:
    sin_evidencia, forma_no_reconocida, excepcion, timeout…; en el v2 real son 11 tareas), `ids` censadas y el SHA del
    archivo (para la meta de la muestra). None si no hay martillo."""
    ruta = Path(ruta) if ruta else MARTILLO
    if not ruta.exists():
        return None
    texto = ruta.read_text(encoding="utf-8")
    tri, sin, ids = set(), set(), set()
    for r in map(json.loads, (l for l in texto.splitlines() if l.strip())):
        ids.add(r["id"])
        if r.get("cierran"):
            tri.add(r["id"])
        elif r.get("estado", "ok") != "ok":
            sin.add(r["id"])
    return {"triviales": tri, "sin_veredicto": sin, "ids": ids, "sha": _sha(texto), "ruta": str(ruta)}


def grupo(r: dict) -> str:
    f = str(r.get("fuente"))
    if "formal" in f and "conjectures" in f:
        return "formal_conjectures"
    if f in ("etp", "pibase", "computacionales"):
        return f
    return "otros"


def _juzgable(r: dict) -> bool:
    try:
        tarea_de(r)
        return True
    except ValueError:
        return False


def clave_familia(r: dict) -> str:
    """Nombre de carpeta del cuaderno de la familia de la tarea r. La familia se identifica por (fuente, familia):
    dos fuentes distintas pueden usar el mismo nombre de familia (p. ej. «logica»), y antes compartían cuaderno.
    Legible (fuente y familia saneadas) y único (sufijo con el hash de la pareja completa)."""
    fuente, familia = str(r.get("fuente")), str(r.get("familia"))
    legible = re.sub(r"[^A-Za-z0-9_.-]", "_", f"{fuente}__{familia}")[:60]
    huella = hashlib.sha256((fuente + "\x00" + familia).encode()).hexdigest()[:8]
    return legible + "_" + huella


def muestra_calibracion(tareas: dict[str, dict], n: int, semilla: int, triviales: set[str] | None) -> list[str]:
    """n tareas verdaderas no triviales para el martillo, estratificadas por fuente y, dentro, por familia. Solo
    entran tareas cuyo enunciado el arnés reconoce (tarea_de): las demás no se pueden juzgar."""
    cuotas = {"formal_conjectures": 0.4, "etp": 0.15, "pibase": 0.15, "computacionales": 0.15, "otros": 0.15}
    rng = random.Random(semilla)
    elegibles: dict[str, dict[str, list[str]]] = {}
    for i, r in tareas.items():
        if r.get("verdad") != "verdadero" or (triviales is not None and i in triviales) or not _juzgable(r):
            continue
        elegibles.setdefault(grupo(r), {}).setdefault(str(r.get("familia")), []).append(i)
    out = []
    for g, cuota in cuotas.items():
        fams = elegibles.get(g, {})
        k = round(n * cuota)
        for f in fams.values():
            f.sort(); rng.shuffle(f)
        orden = sorted(fams); rng.shuffle(orden)
        tomadas, j = [], 0
        while len(tomadas) < k and any(fams[f][j:] for f in orden if len(fams[f]) > j) if orden else False:
            for f in orden:
                if len(tomadas) >= k:
                    break
                if j < len(fams[f]):
                    tomadas.append(fams[f][j])
            j += 1
        out += tomadas
    return sorted(out)


# ============================================================================== comandos


def _lake():
    return LakeSinSecretos(raiz=LEAN_CORPUS, timeout_s=float(os.environ.get("UNIRL_TIMEOUT_LEAN", 300)))


def _huella_codigo() -> str:
    """frontera/juez_lean/loop/gasto (huella de frontera) + este archivo + steprl/providers.py si está (es quien
    construye la llamada a la API: antes no entraba en la huella y un cambio allí era invisible en meta.json)."""
    h = hashlib.sha256(F._huella_codigo().encode())
    h.update(Path(__file__).read_bytes())
    prov = Path(__file__).resolve().parent.parent / "steprl" / "providers.py"
    if prov.exists():
        h.update(prov.read_bytes())
    return h.hexdigest()[:16]


def huella_lean(raiz: Path) -> dict:
    """Lo que fija la biblioteca con la que se juzga: lean-toolchain, lake-manifest.json (SHA) y el `rev` de cada
    paquete (mathlib, FormalConjectures…). `lean --version` solo no distingue dos Mathlib."""
    d: dict = {}
    for f in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
        p = Path(raiz) / f
        if p.exists():
            d[f] = _sha(p.read_text(encoding="utf-8"))
    man = Path(raiz) / "lake-manifest.json"
    if man.exists():
        try:
            for pk in json.loads(man.read_text(encoding="utf-8")).get("packages", []):
                d[f"rev_{pk.get('name')}"] = pk.get("rev")
        except (json.JSONDecodeError, AttributeError):
            d["lake-manifest.json_error"] = "no se pudo leer"
    return d


def _huella_corpus(version: int, raiz: Path | None = None) -> dict:
    raiz = Path(raiz) if raiz else PROMETEO
    arch = raiz / "aprobados" / "Corpus" / f"corpus_v{version}.jsonl"
    sumas = raiz / "aprobados" / f"SHA256SUMS_corpus{version}"
    return {"corpus": _sha(arch.read_text(encoding="utf-8")) if arch.exists() else None,
            "sha256sums": sumas.read_text(encoding="utf-8").strip() if sumas.exists() else None}


def _version_modulo(nombre: str) -> str | None:
    try:
        mod = __import__(nombre)
        return str(getattr(mod, "__version__", "?"))
    except Exception:
        return None


def sembrar_cuadernos(origen: Path, destino: Path, fraccion: float) -> dict:
    """Copia los cuadernos por familia de otra corrida (`<corrida>/cuadernos/<fam>/entradas.json`) a esta, quedándose
    con los primeros ceil(fraccion · n) lemas de cada familia (instantánea al 0/25/50/100 %: las entradas están en el
    orden en que entraron). Devuelve, por familia, cuántas entradas y el hash resultante (para meta.json)."""
    import math
    out = {}
    for ent in sorted(Path(origen).glob("*/entradas.json")):
        entradas = json.loads(ent.read_text(encoding="utf-8"))
        k = min(len(entradas), math.ceil(len(entradas) * fraccion)) if fraccion < 1 else len(entradas)
        cuad = F.Cuaderno(Path(destino) / ent.parent.name)
        cuad.entradas = entradas[:k]
        cuad.guardar()
        out[ent.parent.name] = {"n_origen": len(entradas), "n": k, "hash": cuad.hash()}
    return out


def cmd_tarea(a) -> int:
    r = cargar_corpus(a.version)[a.id]
    t = tarea_de(r)
    print(json.dumps({k: t[k] for k in ("id", "sha", "nombre", "ns", "familia", "verdad", "imports", "cola")}, ensure_ascii=False, indent=1))
    print(t["prefijo"][-1500:] + "\n" + t["enunciado"])
    print("\n-- referencia del kernel que verá el juez:\n" + _ref_y_chk(t, "<nonce>")[0]
          + f"\n\n-- nombre del teorema aprobado en unirl_chk, #check y #print axioms: {nombre_root(t)}")
    return 0


def tarea_debilitada(t: dict, hipotesis: str = "(unirl_h : 0 = 1)") -> dict:
    """Control negativo del mecanismo del kernel: la misma tarea con el ENUNCIADO (no la referencia) debilitado por una
    hipótesis extra. Un teorema así es más fácil que el aprobado y unirl_chk debe fallar con Type mismatch, así que
    referencia() debe lanzar ValueError. Si no lanza, el mecanismo no distingue el enunciado aprobado de uno más débil."""
    m = NOMBRE.search(t["enunciado"])
    if not m:
        raise ValueError(f"{t['id']}: no reconozco el enunciado")
    debil = t["enunciado"][:m.end(2)] + " " + hipotesis + t["enunciado"][m.end(2):]
    return {**t, "id": t["id"] + "#debil", "enunciado": debil, "cabecera_enunciado": SORRY_FIN.sub(":= by", debil)}


def _tarea_sintetica(t: dict, nombre: str, cabecera: str) -> dict:
    """Una tarea con el contexto real de t y un enunciado nuestro, para probar el juez con Lean real sin API."""
    st = f"theorem {nombre} {cabecera} := by sorry"
    base = tarea_de({"id": f"{t['id']}#{nombre}", "sha256_tarea": f"{t['sha']}-{nombre}", "familia": t["familia"],
                     "fuente": t["fuente"], "verdad": "verdadero", "contexto_lean": "", "enunciado_lean": st})
    return {**base, "prefijo": t["prefijo"], "cierre": t["cierre"], "ns": t["ns"]}


def cmd_humo(a) -> int:
    """Lean real, sin API: referencia (con el mecanismo del kernel), un lema verdadero, uno falso, uno con sorry, una
    prueba inválida; sobre el contexto real, un enunciado nuestro que SÍ se demuestra (ACCEPTED + segundo testigo) y
    el ataque de la instancia (`0 + n = n` con una HAdd propia: #check imprime lo mismo, el kernel no lo acepta); el
    nombre largo (lista de axiomas partida); el control debilitado de la v5 (referencia() debe lanzar); y un episodio
    en seco SC y CC sobre tareas reales, con un cuaderno por tarea."""
    tareas = cargar_corpus(a.version)
    lake = _lake()
    print(f"lake: {lake.lake} ({lake.version()}) en {LEAN_CORPUS}; sandbox: {lake.aislado}")
    ids = a.ids or sorted(tareas)[:3]
    bien = True
    carpeta = RUNS / "humo" / datetime.now().strftime("%Y%m%d-%H%M%S")
    carpeta.mkdir(parents=True)
    for i in ids:
        t = tarea_de(tareas[i])
        ref = referencia(t, lake)
        ok = F.admitir_bloque(t, lake, "", "theorem cu_humo : (2 : Nat) + 2 = 4 := by decide", set())
        falso = F.admitir_bloque(t, lake, "", "theorem cu_humo_f : (2 : Nat) + 2 = 5 := by decide", set())
        trampa = F.admitir_bloque(t, lake, "", "theorem cu_humo_t : (2 : Nat) + 2 = 5 := by sorry", set())
        nada = juzgar_principal(t, lake, "", "", "exact absurd rfl rfl", ref)
        print(f"{i}\n  referencia: {ref[:160]}\n  lema verdadero → {ok['etiqueta']}; falso → {falso['etiqueta']}; "
              f"sorry → {trampa['etiqueta']}; prueba inválida → {nada['etiqueta']}")
        bien &= ok["etiqueta"] == "ACCEPTED" and falso["etiqueta"] != "ACCEPTED" and trampa["etiqueta"] == "FORBIDDEN" \
            and nada["etiqueta"] != "ACCEPTED"
        ts = _tarea_sintetica(t, "unirl_humo_ok", "(n : Nat) : 0 + n = n")
        ref_s = referencia(ts, lake)
        acepta = juzgar_principal(ts, lake, "", "", "omega", ref_s)
        testigo = segundo_testigo(ts, lake, "", "", "omega", ref_s)["etiqueta"] if acepta["etiqueta"] == "ACCEPTED" else "-"
        ataque = juzgar_principal(ts, lake, "", "instance cu_bad : HAdd Nat Nat Nat := ⟨fun _ b => b⟩", "intro n\nrfl", ref_s)
        print(f"  enunciado nuestro (0 + n = n): omega → {acepta['etiqueta']} ({acepta.get('motivo', '')[:80]}); segundo testigo → {testigo}; "
              f"ataque con instancia HAdd → {ataque['etiqueta']} ({ataque.get('motivo', '')[:90]})")
        bien &= acepta["etiqueta"] == "ACCEPTED" and testigo == "ACCEPTED" and ataque["etiqueta"] != "ACCEPTED"
        # nombre completo de 100+ caracteres: Lean parte la línea de #print axioms (Format.line); debe seguir ACCEPTED
        tl = _tarea_sintetica(t, "unirl_humo_nombre_largo_" + "x" * 90, "(n : Nat) : 0 + n = n")
        largo = juzgar_principal(tl, lake, "", "", "omega", referencia(tl, lake))
        print(f"  cola del contexto: {t['cola']!r}; imports: {t['imports']}\n  nombre largo (lista de axiomas partida) → "
              f"{largo['etiqueta']} ({largo.get('motivo', '')[:80]})")
        bien &= largo["etiqueta"] == "ACCEPTED"
        # v5: control negativo del mecanismo. El enunciado debilitado con una hipótesis extra (la referencia intacta)
        # debe hacer fallar unirl_chk → referencia() lanza. Sobre la tarea real y sobre la sintética.
        debiles = []
        for td in (tarea_debilitada(t), tarea_debilitada(ts)):
            try:
                referencia(td, lake)
                debiles.append("ACEPTÓ (mal)")
            except ValueError:
                debiles.append("rechazó")
        print(f"  control debilitado (hipótesis 0 = 1 en el enunciado, referencia intacta): real → {debiles[0]}; sintética → {debiles[1]}")
        bien &= debiles == ["rechazó", "rechazó"]
        for cfg in (F.CONFIGS["SC"], F.CONFIGS["CC"]):
            cuad = F.Cuaderno(carpeta / f"cuaderno_{cfg.nombre}_{re.sub(r'[^A-Za-z0-9_.-]', '_', i)[:80]}")
            r = episodio(t, cfg, ProveedorSeco(), lake, cuad, carpeta, f"humo-{cfg.nombre}-{i}", ref)
            print(f"  episodio seco {cfg.nombre}: resuelto={r['resuelto']} lemas={r['lemas_admitidos']} intentos={r['intentos']}")
            bien &= r["lemas_admitidos"][:1] == ["cu_seco"] and not r["resuelto"]
    print("HUMO OK" if bien else "HUMO FALLÓ: revisar antes de gastar un dólar")
    return 0 if bien else 1


def cmd_muestra(a) -> int:
    tareas = cargar_corpus(a.version)
    censo = censo_martillo()
    if censo is None and not a.sin_martillo:
        print(f"no está {MARTILLO}: sin él la muestra incluiría tareas triviales para el martillo. "
              "Pon UNIRL_MARTILLO o, a sabiendas, --sin-martillo.")
        return 2
    tri = censo["triviales"] if censo else None
    # Tareas sin veredicto del martillo (no pudo decidir) o sin censar (p. ej. las 90 nuevas de corpus_v2 frente a un
    # martillo corrido sobre v1): no se sabe si son triviales. Por omisión siguen siendo elegibles (así se generó la
    # muestra del 25 oct: misma semilla → misma muestra); con --excluir-sin-censo quedan fuera. Siempre se anotan.
    sin_censo = (censo["sin_veredicto"] | (set(tareas) - censo["ids"])) if censo else set()
    if censo and a.excluir_sin_censo:
        tri = tri | sin_censo
    ids = muestra_calibracion(tareas, a.n, a.semilla, tri)
    salida = RUNS / "calibracion" / f"muestra_n{a.n}_s{a.semilla}.json"
    salida.parent.mkdir(parents=True, exist_ok=True)
    meta = {"version_corpus": a.version, "n": len(ids), "semilla": a.semilla, "martillo": censo["ruta"] if censo else None,
            "martillo_sha": censo["sha"] if censo else None,
            "excluidas_triviales": len(censo["triviales"]) if censo else None,
            "excluir_sin_censo": bool(a.excluir_sin_censo), "sin_censo_en_corpus": len(sin_censo),
            "sin_censo_en_muestra": sorted(i for i in ids if i in sin_censo), "ids": ids,
            "nota": "Estas tareas son de calibración: NO pueden entrar al conjunto de test del confirmatorio.",
            "fecha": datetime.now().isoformat(timespec="seconds")}
    if meta["sin_censo_en_muestra"]:
        print(f"aviso: {len(meta['sin_censo_en_muestra'])} tareas de la muestra no tienen veredicto del martillo "
              f"(podrían ser triviales): {meta['sin_censo_en_muestra'][:5]}")
    salida.write_text(json.dumps(meta, ensure_ascii=False, indent=1), encoding="utf-8")
    from collections import Counter
    print(f"{len(ids)} tareas en {salida}\n{Counter(grupo(tareas[i]) for i in ids)}")
    return 0


def _leer_jsonl(ruta: Path) -> list[dict]:
    return [json.loads(l) for l in ruta.read_text(encoding="utf-8").splitlines() if l.strip()] if ruta.exists() else []


def cmd_calibrar(a) -> int:
    """Una corrida: un modelo, una o varias configuraciones (SC, CC o `SC,CC` intercaladas por tarea), sobre la muestra.

    - `--orden-semilla N`: el orden de ejecución se baraja aquí con Random(N) sobre los ids ordenados, y queda en
      meta.json (`ids`); antes el barajado lo hacía un script fuera del arnés y no quedaba registrado en la corrida.
    - `--config SC,CC`: la unidad de trabajo es la TAREA: el mismo hilo corre SC y luego CC (o al revés con
      `--orden-configs aleatorio`) antes de pasar a la siguiente. Un corte por tope deja las dos ramas en la misma
      tarea (anoche, en corridas separadas, Sonnet SC y CC se cortaron en puntos distintos y no eran comparables).
    - `--continuar <carpeta>`: reanuda esa corrida tras una caída: mismo nombre de corrida (misma fase del libro),
      salta los (tarea, config) que ya tienen resultado, los cuadernos CC se recargan de disco. Modelo, configs,
      esfuerzo, recorte, task_budget y versión salen de su meta.json; --tope-usd se vuelve a dar (incluye lo gastado).
    - `--serial-familia`: en CC, las tareas de una misma familia se corren en orden (cerrojo por familia), para que
      el cuaderno crezca en un orden reproducible dado --orden-semilla; el paralelismo queda entre familias.
    - `--cuadernos-de <corrida>/cuadernos [--cuaderno-fraccion f] [--cuaderno-congelado]`: CC arranca con los
      cuadernos de otra corrida (los primeros ceil(f·n) lemas por familia) y, si se congela, el modelo los usa pero
      no añade: diseño dosis–respuesta con instantáneas al 0/25/50/100 %."""
    continuar = Path(a.continuar) if a.continuar else None
    meta_prev = json.loads((continuar / "meta.json").read_text(encoding="utf-8")) if continuar else {}
    version = meta_prev.get("version_corpus", a.version)
    tareas = cargar_corpus(version)
    ruta_muestra = meta_prev.get("muestra", a.muestra)
    muestra = json.loads(Path(ruta_muestra).read_text(encoding="utf-8"))
    nombres_cfg = (meta_prev.get("configs") or [meta_prev["config"]["nombre"]]) if meta_prev else a.config.split(",")
    for c in nombres_cfg:
        if c not in F.CONFIGS:
            raise SystemExit(f"--config: {c!r} no es una de {sorted(F.CONFIGS)}")
    cfgs = [F.CONFIGS[c] for c in nombres_cfg]
    orden_semilla = meta_prev.get("orden_semilla", a.orden_semilla) if meta_prev else a.orden_semilla
    if meta_prev.get("ids"):
        ids = list(meta_prev["ids"])
    else:
        ids = list(muestra["ids"])
        if orden_semilla is not None:
            ids = sorted(ids)
            random.Random(int(orden_semilla)).shuffle(ids)
        if a.limite:
            ids = ids[: a.limite]
    lake = _lake()
    seco = bool(meta_prev.get("modelo") == "seco") if meta_prev else a.seco
    modelo = meta_prev.get("modelo") if meta_prev else ("seco" if a.seco else a.modelo)
    if meta_prev:
        corrida, carpeta = meta_prev["corrida"], continuar
        effort, recorte, task_budget = meta_prev.get("esfuerzo"), meta_prev.get("recorte"), meta_prev.get("task_budget")
        hechas = {(r["tarea"], r["config"]) for r in _leer_jsonl(carpeta / "resultados.jsonl")}
    else:
        corrida = f"{datetime.now().strftime('%Y%m%d-%H%M%S')}-{modelo}-{'+'.join(nombres_cfg)}"
        carpeta = RUNS / ("seco" if seco else "calibracion") / corrida
        carpeta.mkdir(parents=True)
        effort = None if (a.esfuerzo in ("", "none") or (a.esfuerzo == "auto" and "haiku" in modelo)) else \
            ("high" if a.esfuerzo == "auto" else a.esfuerzo)
        recorte, task_budget = (None if a.recorte == "ninguno" else a.recorte), (a.task_budget or None)
        hechas = set()
    prov = ProveedorSeco() if seco else hacer_proveedor(modelo, corrida, a.tope_usd, effort, recorte, task_budget)
    usa_cc = any(c.usa_cuaderno for c in cfgs)
    sembrados = None
    if a.cuadernos_de and not meta_prev:
        if not usa_cc:
            raise SystemExit("--cuadernos-de solo tiene sentido con una configuración con cuaderno (CC)")
        sembrados = sembrar_cuadernos(Path(a.cuadernos_de), carpeta / "cuadernos", a.cuaderno_fraccion)
    congelado = bool(meta_prev.get("cuaderno_congelado", a.cuaderno_congelado)) if meta_prev else bool(a.cuaderno_congelado)
    ahora = datetime.now().isoformat(timespec="seconds")
    meta = dict(meta_prev) if meta_prev else {
        "corrida": corrida, "modelo": modelo, "esfuerzo": effort, "config": asdict(cfgs[0]) if len(cfgs) == 1 else "+".join(nombres_cfg),
        "configs": nombres_cfg, "configs_detalle": [asdict(c) for c in cfgs], "orden_configs": a.orden_configs,
        "tope_usd": a.tope_usd, "tope_global_usd": TOPE_GLOBAL_USD, "paralelo": a.paralelo, "serial_familia": bool(a.serial_familia),
        "recorte": recorte, "task_budget": task_budget, "version_corpus": version, "muestra": ruta_muestra,
        "muestra_sha": _sha(Path(ruta_muestra).read_text(encoding="utf-8")), "semilla_muestra": muestra.get("semilla"),
        "orden_semilla": orden_semilla, "n": len(ids), "ids": ids,
        "cuadernos_de": a.cuadernos_de, "cuaderno_fraccion": a.cuaderno_fraccion if a.cuadernos_de else None,
        "cuadernos_sembrados": sembrados, "cuaderno_congelado": congelado,
        "lean": lake.version(), "lean_raiz": str(LEAN_CORPUS), "lean_huella": huella_lean(LEAN_CORPUS),
        "timeout_lean_s": getattr(lake, "timeout_s", None), "sandbox": getattr(lake, "aislado", None), "corpus_huella": _huella_corpus(version),
        "codigo": _huella_codigo(), "sistema_sha": _sha(SISTEMA),
        "precios_usd_por_M": PRECIOS.get(modelo), "max_output_tokens": getattr(getattr(prov, "interno", None), "max_output_tokens", None),
        "python": sys.version.split()[0], "anthropic_sdk": _version_modulo("anthropic"),
        "inicio": ahora}
    if meta_prev:
        meta.setdefault("reanudaciones", []).append({"inicio": ahora, "pendientes": sum(1 for i in ids for c in nombres_cfg if (i, c) not in hechas),
                                                     "codigo": _huella_codigo(), "tope_usd": a.tope_usd, "paralelo": a.paralelo})
        if meta.get("codigo") != _huella_codigo():
            print(f"aviso: el código cambió desde el inicio de la corrida ({meta.get('codigo')} → {_huella_codigo()}); queda anotado")
    (carpeta / "meta.json").write_text(json.dumps(meta, ensure_ascii=False, indent=1), encoding="utf-8")
    (carpeta / "sistema.txt").write_text(SISTEMA, encoding="utf-8")
    refs = carpeta.parent / "referencias"
    lock = threading.Lock()
    locks_fam: dict[str, threading.Lock] = {}
    cuadernos: dict[str, F.Cuaderno] = {}
    sin_cuaderno = F.Cuaderno(carpeta / "sin_cuaderno")
    detener = threading.Event()
    motivo_fin = ["completo"]
    vigia = Vigia() if not seco else None
    orden_cfg_aleatorio = (meta.get("orden_configs") or a.orden_configs) == "aleatorio"

    def configs_de(i: str) -> list:
        if len(cfgs) > 1 and orden_cfg_aleatorio:
            cs = list(cfgs)
            random.Random(f"{orden_semilla}:{i}").shuffle(cs)
            return cs
        return list(cfgs)

    def una(i: str) -> list[dict]:
        if detener.is_set():
            return []
        r = tareas[i]
        pendientes = [c for c in configs_de(i) if (i, c.nombre) not in hechas]
        if not pendientes:
            return []
        try:
            t = tarea_de(r)
            ref = referencia(t, lake, refs)
        except ValueError as e:
            return [{"tarea": i, "error_referencia": str(e)[:400]}]
        fam = clave_familia(r)
        salida = []
        for k, cfg in enumerate(pendientes):
            if detener.is_set():
                break
            if cfg.usa_cuaderno:  # un cuaderno por familia, nuevo y vacío al empezar la corrida (o sembrado/recargado)
                with lock:
                    cuad = cuadernos.setdefault(fam, F.Cuaderno(carpeta / "cuadernos" / fam))
                    lock_fam = locks_fam.setdefault(fam, threading.Lock())
            else:
                cuad, lock_fam = sin_cuaderno, None  # SC: un solo objeto vacío, compartido y nunca escrito
            try:
                if a.serial_familia and lock_fam is not None:
                    with lock_fam:
                        res = episodio(t, cfg, prov, lake, cuad, carpeta, f"{corrida}#{i}#{cfg.nombre}", ref, lock,
                                       parar=detener, vigia=vigia, incorporar=not congelado)
                else:
                    res = episodio(t, cfg, prov, lake, cuad, carpeta, f"{corrida}#{i}#{cfg.nombre}", ref, lock,
                                   parar=detener, vigia=vigia, incorporar=not congelado)
            except CorridaDetenida as e:
                detener.set(); motivo_fin[0] = f"DETENIDA: {e}"; break
            except ProviderFatal as e:
                detener.set(); motivo_fin[0] = f"abortado: {e}"; break
            except Exception as e:  # un fallo de programa en una tarea no debe tumbar la corrida ni perder lo hecho
                _registrar(carpeta / "errores.jsonl", {"tarea": i, "config": cfg.nombre, "error": f"{type(e).__name__}: {e}"[:800]})
                salida.append({"tarea": i, "config": cfg.nombre, "error": f"{type(e).__name__}: {e}"[:400]})
                continue
            res.update({"familia": r.get("familia"), "fuente": r.get("fuente"), "clave_familia": fam, "orden_config": k})
            if res.get("interrumpido"):
                _registrar(carpeta / "interrumpidos.jsonl", res)
                break
            _registrar(carpeta / "resultados.jsonl", res)
            print(f"{i} [{cfg.nombre}]: resuelto={res['resuelto']} intentos={res['intentos']} usd={res['usd']:.4f}", flush=True)
            salida.append(res)
        return salida

    with cf.ThreadPoolExecutor(max(1, a.paralelo)) as ex:
        resultados = [x for xs in ex.map(una, ids) for x in xs]
    todos = _leer_jsonl(carpeta / "resultados.jsonl")  # acumulado (con las reanudaciones)
    hechos = [x for x in todos if "resuelto" in x]
    por_cfg = {c: [x for x in hechos if x.get("config") == c] for c in nombres_cfg}
    pareadas = sorted({x["tarea"] for x in hechos if all(any(y["tarea"] == x["tarea"] for y in por_cfg[c]) for c in nombres_cfg)}) \
        if len(cfgs) > 1 else None
    meta.update({"fin": datetime.now().isoformat(timespec="seconds"), "motivo_fin": motivo_fin[0],
                 "tareas_hechas": len(hechos), "resueltas": sum(x["resuelto"] for x in hechos),
                 "por_config": {c: {"hechas": len(v), "resueltas": sum(x["resuelto"] for x in v)} for c, v in por_cfg.items()},
                 "tareas_pareadas": pareadas,
                 "usd": None if seco else prov.libro.gastado(prov.fase),
                 "errores_referencia": meta.get("errores_referencia", []) + [x for x in resultados if "error_referencia" in x],
                 "errores_programa": meta.get("errores_programa", []) + [x for x in resultados if "error" in x]})
    (carpeta / "meta.json").write_text(json.dumps(meta, ensure_ascii=False, indent=1), encoding="utf-8")
    print(f"{motivo_fin[0]}: {meta['resueltas']}/{len(hechos)} resueltas; USD {meta['usd']}; registro en {carpeta}")
    return 0 if motivo_fin[0] == "completo" else 1


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python -m unirl.corpus_confirmatorio", description=__doc__.split("\n")[0])
    ap.add_argument("--version", type=int, default=1)
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("tarea"); s.add_argument("id")
    s = sub.add_parser("humo"); s.add_argument("ids", nargs="*")
    s = sub.add_parser("muestra"); s.add_argument("--n", type=int, default=100); s.add_argument("--semilla", type=int, default=20261025)
    s.add_argument("--sin-martillo", action="store_true", help="aceptar que no haya martillo.jsonl (la muestra no excluye triviales)")
    s.add_argument("--excluir-sin-censo", action="store_true",
                   help="excluir también las tareas sin veredicto del martillo o sin censar (cambia la muestra para la misma semilla)")
    s = sub.add_parser("calibrar")
    s.add_argument("--muestra", default=None)
    s.add_argument("--modelo", default="claude-haiku-5-5")
    s.add_argument("--config", default="SC", help="SC, CC o varias separadas por coma (SC,CC): intercaladas por tarea")
    s.add_argument("--orden-configs", choices=("fijo", "aleatorio"), default="fijo",
                   help="con varias configs: el orden en que se corren dentro de cada tarea (aleatorio: Random(orden_semilla:tarea))")
    s.add_argument("--tope-usd", type=float, default=5.0)
    s.add_argument("--esfuerzo", default="auto")
    s.add_argument("--paralelo", type=int, default=4)
    s.add_argument("--limite", type=int, default=0)
    s.add_argument("--orden-semilla", type=int, default=None, help="barajar el orden de ejecución con esta semilla (queda en meta.json)")
    s.add_argument("--serial-familia", action="store_true", help="CC: las tareas de una misma familia se corren en orden (cerrojo por familia)")
    s.add_argument("--continuar", default=None, metavar="CARPETA", help="reanudar esa corrida: salta lo ya hecho, misma fase del libro")
    s.add_argument("--cuadernos-de", default=None, metavar="CARPETA/cuadernos", help="CC: arrancar con los cuadernos de otra corrida")
    s.add_argument("--cuaderno-fraccion", type=float, default=1.0, help="con --cuadernos-de: fracción inicial de cada cuaderno (0, 0.25, 0.5, 1)")
    s.add_argument("--cuaderno-congelado", action="store_true", help="CC: el modelo usa el cuaderno pero sus lemas no entran a él")
    s.add_argument("--seco", action="store_true")
    s.add_argument("--recorte", choices=RECORTES, default="ninguno",
                   help="qué hacer si una llamada se corta por max_tokens sin texto: ninguno (PROVIDER_ERROR, como hasta "
                        "hoy), effort:low / effort:medium (repetirla una vez con ese esfuerzo) o sin_pensar (repetirla sin "
                        "pensamiento previo). Cambia el protocolo: solo con la línea de Carlos en FECHA.")
    s.add_argument("--task-budget", type=int, default=0,
                   help="output_config.task_budget.total (beta task-budgets-2026-03-13; mínimo 20000): el modelo recibe "
                        "una cuenta regresiva de tokens y se la pide acabar dentro de ella. 0 = apagado (por omisión).")
    a = ap.parse_args(argv)
    if a.cmd == "calibrar" and not a.muestra and not a.continuar:
        ap.error("calibrar: hace falta --muestra (o --continuar CARPETA)")
    if a.cmd == "calibrar" and a.cuadernos_de and not (0.0 <= a.cuaderno_fraccion <= 1.0):
        ap.error("--cuaderno-fraccion debe estar entre 0 y 1")
    return {"tarea": cmd_tarea, "humo": cmd_humo, "muestra": cmd_muestra, "calibrar": cmd_calibrar}[a.cmd](a)


if __name__ == "__main__":
    raise SystemExit(main())
