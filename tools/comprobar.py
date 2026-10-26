"""¿Está terminado el teorema Tn? (criterio de Carlos, ENUNCIADOS.md, 17 oct 2026)

  python3 herramientas/comprobar.py 1                    (desde la raíz del proyecto; n = 1, 2, 3, 4, 4b o 5 a 9)
  python3 herramientas/comprobar.py 1 --solo-enunciado   (solo el punto 1, sin compilar)

Terminado si se cumplen las cinco cosas:
1. El enunciado aprobado no cambió: `PrometeoLean/Tn.lean` debe contener todo `aprobados/Tn.lean` (solo lectura, con
   su SHA-256 en `aprobados/SHA256SUMS` o `aprobados/SHA256SUMS_tanda2`), intacto y en el mismo orden, salvo dos cosas:
   - cada `  sorry` se reemplaza por una prueba (líneas con sangría);
   - entre dos bloques de nivel superior (separados por una línea en blanco, fuera de comentarios) caben lemas y
     definiciones auxiliares: `lemma`, `theorem`, `def` o `abbrev` (con `private` o `noncomputable`), con docstring
     y `@[simp]` opcionales, cada uno seguido de una línea en blanco. Una `instance`, `notation`, `attribute`,
     `variable` o `set_option` nueva podría cambiar el sentido de un enunciado sin tocar su texto, y por eso no se
     admite. Una `def` auxiliar también podría hacerlo (por ejemplo, tapando un nombre de Mathlib), y eso lo
     detecta el punto 5.
2. `lake build PrometeoLean.Tn` pasa sin avisos de `sorry`.
3. Ni las pruebas ni los lemas auxiliares usan `sorry`, `admit`, `native_decide`, `axiom` ni código no verificado
   (`implemented_by`, `extern`, `unsafe`).
4. `#print axioms` de cada teorema aprobado muestra solo `propext`, `Classical.choice` y `Quot.sound`.
5. El segundo testigo, `herramientas/Comparar.lean`, elabora por separado la copia aprobada y la demostrada y
   confirma que cada constante aprobada (definiciones y enunciados) tiene exactamente el mismo tipo elaborado, y las
   definiciones el mismo cuerpo. Compara lo que Lean entiende, no el texto.
"""

import hashlib
import re
import subprocess
import sys
import tempfile
from pathlib import Path

RAIZ = Path(__file__).resolve().parent.parent
PERMITIDOS = {"propext", "Classical.choice", "Quot.sound"}
PROHIBIDOS = re.compile(r"\bsorry\b|\badmit\b|\bnative_decide\b|^\s*axiom\b|\bimplemented_by\b|@\[\s*extern\b|\bunsafe\b"
                        r"|\bskipKernelTC\b|\bset_option\s+debug\.|\brun_tac\b|\brun_elab\b|\bby_elab\b|\bofReduceBool\b",
                        re.M)
HUECO = re.compile(r"(?<=:= by\n)  sorry\n")  # la prueba de cada teorema aprobado
CORTE = re.compile(r"\n\n(?=\S)")           # el comienzo de un bloque de nivel superior
PRUEBA = r"(?:[ \t][^\n]*\n|\n(?=[ \t]))+"   # líneas con sangría (una línea en blanco solo si sigue la prueba)
AUXILIAR = (r"(?:--[^\n]*\n)*(?:/--(?:(?!-/).)*-/\n)?(?:@\[simp\][ \n])?(?:(?:private|protected|noncomputable) )*"
            r"(?:lemma|theorem|def|abbrev) [^\n]*\n" + r"(?:[ \t][^\n]*\n|\n(?=[ \t]))*" + r"\n")
NOMBRE_AUX = re.compile(r"(?m)^(?:@\[simp\][ \n])?(?:(?:private|protected|noncomputable) )*"
                        r"(?:lemma|theorem|def|abbrev) (\S+)")
IDS = ["1", "2", "3", "4", "4b", "5", "6", "7", "8", "9"]


def patron_aprobado(aprobado: str) -> tuple[re.Pattern, list[str], list[str]]:
    """El patrón que debe cumplir el archivo actual, los trozos literales del aprobado y el tipo de cada grupo."""
    comentarios = [m.span() for m in re.finditer(r"/-.*?-/", aprobado, re.S)]
    cortes = [(m.start(), m.end(), "prueba") for m in HUECO.finditer(aprobado)]
    cortes += [(m.end(), m.end(), "auxiliar") for m in CORTE.finditer(aprobado)
               if not any(a < m.end() < b for a, b in comentarios)]
    partes, literales, tipos, i = [], [], [], 0
    for a, b, tipo in sorted(cortes):
        literales.append(aprobado[i:a])
        partes += [re.escape(aprobado[i:a]), f"({PRUEBA})" if tipo == "prueba" else f"((?:{AUXILIAR})*)"]
        tipos.append(tipo)
        i = b
    literales.append(aprobado[i:])
    partes.append(re.escape(aprobado[i:]))
    return re.compile("".join(partes), re.S), literales, tipos


def diagnostico(aprobado: str, literales: list[str], actual: str) -> str:
    for t in literales:
        if t and t not in actual:
            linea = next((l for l in t.splitlines() if l.strip()), t.strip())
            return f"falta o cambió un trozo aprobado; empieza con «{linea[:90]}»"
    aprobadas = set(aprobado.splitlines())
    raras = [l for l in actual.splitlines() if l and not l[0].isspace() and l not in aprobadas
             and not re.match(r"(lemma|theorem|def|abbrev|noncomputable |@\[simp\]|private |protected |/--|--)", l)]
    if raras:
        return f"se añadió algo que no es lemma, theorem ni def; por ejemplo «{raras[0][:90]}»"
    return "un añadido está fuera de lugar (¿falta la línea en blanco tras un lema, o hay uno dentro de un enunciado?)"


def sin_comentarios(t: str) -> str:
    t = re.sub(r"/-.*?-/", " ", t, flags=re.S)
    return re.sub(r"--[^\n]*", " ", t)


def main() -> int:
    n = sys.argv[1] if len(sys.argv) > 1 else ""
    if n not in IDS:
        print(f"uso: python3 herramientas/comprobar.py <{'|'.join(IDS)}>")
        return 2
    aprobado_p, actual_p = RAIZ / "aprobados" / f"T{n}.lean", RAIZ / "PrometeoLean" / f"T{n}.lean"
    fallos = []

    # 0. la copia aprobada es la de la aprobación (por si alguien la tocó)
    sumas = dict(reversed(l.split(None, 1)) for f in sorted((RAIZ / "aprobados").glob("SHA256SUMS*"))
                 for l in f.read_text().splitlines() if l.strip())
    aprobado = aprobado_p.read_text(encoding="utf-8")
    if hashlib.sha256(aprobado.encode()).hexdigest() != sumas.get(f"aprobados/T{n}.lean"):
        print(f"✘ aprobados/T{n}.lean no coincide con su SHA-256: no se puede comprobar el enunciado")
        return 1

    # 1. el enunciado no cambió
    actual = actual_p.read_text(encoding="utf-8")
    patron, literales, tipos = patron_aprobado(aprobado)
    m = patron.fullmatch(actual)
    if not m:
        fallos.append(f"el enunciado aprobado cambió: {diagnostico(aprobado, literales, actual)}")
        pruebas = ""
    else:
        pruebas = "\n".join(m.groups())
        aux = [x for g, t in zip(m.groups(), tipos) if t == "auxiliar" for x in NOMBRE_AUX.findall(g)]
        print(f"✔ enunciado aprobado intacto ({tipos.count('prueba')} pruebas"
              + (f"; {len(aux)} lemas auxiliares: {', '.join(aux)})" if aux else ")"))
    if "--solo-enunciado" in sys.argv[2:]:
        for f in fallos:
            print(f"  ✘ {f}")
        return 1 if fallos else 0

    # 3. nada prohibido en lo que se escribió
    malos = sorted(set(x.group(0).strip() for x in PROHIBIDOS.finditer(sin_comentarios(pruebas))))
    if malos:
        fallos.append(f"las pruebas usan {', '.join(malos)}")
    elif m:
        print("✔ sin sorry, admit, native_decide, axiom ni código no verificado en las pruebas ni en los lemas")

    # 2. compila
    r = subprocess.run(["nice", "-n", "19", "lake", "build", f"PrometeoLean.T{n}"], cwd=RAIZ, capture_output=True, text=True)
    salida = r.stdout + r.stderr
    if r.returncode != 0:
        fallos.append("lake build falló: " + " | ".join(l for l in salida.splitlines() if "error" in l)[:400])
    elif "declaration uses 'sorry'" in salida or "declaration uses `sorry`" in salida:
        fallos.append("lake build pasa, pero hay declaraciones con sorry")
    else:
        print(f"✔ lake build PrometeoLean.T{n}")

    # 4. axiomas de cada teorema aprobado
    nombres = re.findall(r"(?m)^theorem\s+(\S+)", aprobado)
    if r.returncode == 0:
        with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as fh:
            fh.write(f"import PrometeoLean.T{n}\n" + "".join(f"#print axioms PrometeoLean.{x}\n" for x in nombres))
        ax = subprocess.run(["nice", "-n", "19", "lake", "env", "lean", fh.name], cwd=RAIZ, capture_output=True, text=True)
        Path(fh.name).unlink()
        texto = ax.stdout + ax.stderr
        for x in nombres:
            bloque = re.search(rf"'PrometeoLean\.{re.escape(x)}'\s+(does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])", texto)
            if not bloque:
                fallos.append(f"#print axioms no informó sobre {x}")
                continue
            usados = {a.strip() for a in (bloque.group(2) or "").replace("\n", " ").split(",") if a.strip()}
            if usados - PERMITIDOS:
                fallos.append(f"{x} usa axiomas no permitidos: {', '.join(sorted(usados - PERMITIDOS))}")
            else:
                print(f"✔ {x}: axiomas {', '.join(sorted(usados)) or 'ninguno'}")

    # 5. el segundo testigo: los tipos ya elaborados, no el texto
    if r.returncode == 0 and not fallos:
        cmp = subprocess.run(["nice", "-n", "19", "lake", "env", "lean", "--run", "herramientas/Comparar.lean",
                              f"aprobados/T{n}.lean", f"PrometeoLean/T{n}.lean", f"PrometeoLean.T{n}"],
                             cwd=RAIZ, capture_output=True, text=True)
        salida_cmp = cmp.stdout + cmp.stderr
        if cmp.returncode == 0 and "COMPARACION: OK" in salida_cmp:
            print("✔ segundo testigo: los tipos elaborados coinciden con los aprobados")
        else:
            detalle = " | ".join(l.strip() for l in salida_cmp.splitlines() if "✘" in l or "error" in l)
            fallos.append(f"el segundo testigo (Comparar.lean) no aprobó: {detalle[:400] or salida_cmp[-400:]}")

    if fallos:
        print(f"T{n}: NO TERMINADO")
        for f in fallos:
            print(f"  ✘ {f}")
        return 1
    print(f"T{n}: TERMINADO")
    return 0


if __name__ == "__main__":
    sys.exit(main())
