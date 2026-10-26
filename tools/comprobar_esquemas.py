"""¿Quedó demostrada la tanda X del diseño A (esquemas de diferencias finitas)? (24 oct 2026)

  python3 herramientas/comprobar_esquemas.py A1_FTCS                  (desde la raíz del proyecto)
  python3 herramientas/comprobar_esquemas.py A1_FTCS --solo-enunciado (solo el punto 1, sin compilar)

Mismo criterio que comprobar.py (T1–T9), con estas rutas:
  aprobado:    aprobados/Esquemas/<X>.lean  (SHA-256 en aprobados/SHA256SUMS_esquemas*)
  demostrado:  Esquemas/<X>.lean            (copia del aprobado con cada `  sorry` reemplazado)
1. El texto aprobado está intacto (patrón de comprobar.py: solo cambian las pruebas y caben lemas auxiliares).
2. `lake env lean Esquemas/<X>.lean` compila sin errores ni avisos de sorry.
3. Nada prohibido en pruebas ni auxiliares (lista de comprobar.py).
4. `#print axioms` de cada teorema aprobado: solo propext, Classical.choice y Quot.sound.
5. Segundo testigo: herramientas/Comparar.lean confirma tipos elaborados y cuerpos idénticos.
Los controles falsos de cada tanda se aprueban por su REFUTACIÓN (`..._falso`), que debe quedar demostrada.

Tareas de decidir (25 oct 2026): de cada par `esq_<id>_decide_<e>_si` / `_no` queda demostrado EXACTAMENTE uno, y
el otro se deja con su `sorry` aprobado tal cual (es falso: no se puede probar). Ese `sorry` es el único admitido:
su teorema aparece con `sorryAx` en `#print axioms` y se informa como «la otra alternativa»; cualquier otro teorema
aprobado que dependa de él falla el punto 4, y un `sorry` en cualquier otro lugar falla el punto 3. El segundo
testigo corre entonces en su modo `uno` (tipos idénticos, ningún axioma salvo sorryAx en lo no demostrado); la regla
«exactamente uno por par, y todo lo demás limpio» la impone este programa.
"""
import hashlib, re, subprocess, sys, tempfile
from pathlib import Path

RAIZ = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(RAIZ / "herramientas"))
from comprobar import patron_aprobado, diagnostico, sin_comentarios, PROHIBIDOS, PERMITIDOS, NOMBRE_AUX  # noqa: E402


def main() -> int:
    x = sys.argv[1] if len(sys.argv) > 1 else ""
    aprobado_p, actual_p = RAIZ / "aprobados" / "Esquemas" / f"{x}.lean", RAIZ / "Esquemas" / f"{x}.lean"
    if not x or not aprobado_p.exists():
        print("uso: python3 herramientas/comprobar_esquemas.py <tanda, p. ej. A1_FTCS> [--solo-enunciado]")
        return 2
    rel = f"aprobados/Esquemas/{x}.lean"
    sumas = dict(reversed(l.split(None, 1)) for f in sorted((RAIZ / "aprobados").glob("SHA256SUMS_esquemas*"))
                 for l in f.read_text().splitlines() if l.strip())
    aprobado = aprobado_p.read_text(encoding="utf-8")
    if hashlib.sha256(aprobado.encode()).hexdigest() != sumas.get(rel):
        print(f"✘ {rel} no coincide con su SHA-256: no se puede comprobar el enunciado")
        return 1
    fallos = []
    actual = actual_p.read_text(encoding="utf-8")
    patron, literales, tipos = patron_aprobado(aprobado)
    m = patron.fullmatch(actual)
    if not m:
        fallos.append(f"el enunciado aprobado cambió: {diagnostico(aprobado, literales, actual)}")
        pruebas = ""
    else:
        pruebas = "\n".join(m.groups())
        aux = [a for g, t in zip(m.groups(), tipos) if t == "auxiliar" for a in NOMBRE_AUX.findall(g)]
        print(f"✔ enunciado aprobado intacto ({tipos.count('prueba')} pruebas"
              + (f"; {len(aux)} lemas auxiliares: {', '.join(aux)})" if aux else ")"))
    # tareas de decidir: qué alternativa quedó con su sorry aprobado
    con_hueco = []
    for h in re.finditer(r"(?<=:= by\n)  sorry\n", aprobado):
        previos = re.findall(r"^theorem\s+(\S+)", aprobado[: h.start()], re.M)
        con_hueco.append(previos[-1] if previos else "?")
    pendientes = set()
    if m:
        grupos = [g for g, tp in zip(m.groups(), tipos) if tp == "prueba"]
        if len(grupos) != len(con_hueco):
            fallos.append(f"no pude alinear pruebas y teoremas ({len(grupos)} frente a {len(con_hueco)})")
        else:
            limpias = []
            for nombre, g in zip(con_hueco, grupos):
                if re.fullmatch(r".*_decide_[a-z0-9]+_(si|no)", nombre) and g.strip() == "sorry":
                    pendientes.add(nombre)
                else:
                    limpias.append(g)
            pruebas = "\n".join(limpias + [g for g, tp in zip(m.groups(), tipos) if tp == "auxiliar"])
            pares = {}
            for nombre in con_hueco:
                if d := re.fullmatch(r"(.*_decide_[a-z0-9]+)_(si|no)", nombre):
                    pares.setdefault(d.group(1), []).append(nombre)
            for base, alts in sorted(pares.items()):
                abiertas = [a for a in alts if a in pendientes]
                if len(alts) != 2 or len(abiertas) != 1:
                    fallos.append(f"{base}: de las dos alternativas debe quedar demostrada exactamente una "
                                  f"(sin demostrar: {abiertas or 'ninguna'})")
                else:
                    hecha = next(a for a in alts if a not in pendientes)
                    print(f"✔ {base}: decidida por «{hecha.rsplit('_', 1)[1]}»")

    if "--solo-enunciado" in sys.argv[2:]:
        for f in fallos:
            print(f"  ✘ {f}")
        return 1 if fallos else 0

    malos = sorted(set(y.group(0).strip() for y in PROHIBIDOS.finditer(sin_comentarios(pruebas))))
    if malos:
        fallos.append(f"las pruebas usan {', '.join(malos)}")
    elif m:
        print("✔ sin sorry, admit, native_decide, axiom ni código no verificado en las pruebas ni en los lemas")

    # nombres completos: se sigue la pila de `namespace … / end …` (hay espacios anidados, p. ej. `Esquema`)
    pila, nombres = [], []
    for linea in sin_comentarios(aprobado).splitlines():
        if mm := re.match(r"namespace\s+(\S+)", linea):
            pila.append(mm.group(1))
        elif re.match(r"end\s+\S+", linea) and pila:
            pila.pop()
        elif mm := re.match(r"theorem\s+(\S+)", linea):
            nombres.append(".".join(pila + [mm.group(1)]))
    pref = ""
    # 2 y 4 en una sola elaboración: el demostrado más los #print axioms al final
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=RAIZ / "Esquemas", delete=False,
                                     encoding="utf-8") as fh:
        fh.write(actual + "\n" + "".join(f"#print axioms {pref}{n}\n" for n in nombres))
    r = subprocess.run(["nice", "-n", "19", "lake", "env", "lean", fh.name], cwd=RAIZ, capture_output=True, text=True)
    Path(fh.name).unlink()
    salida = r.stdout + r.stderr
    if r.returncode != 0:
        fallos.append("no compila: " + " | ".join(l for l in salida.splitlines() if "error" in l)[:600])
    elif not pendientes and ("declaration uses 'sorry'" in salida or "declaration uses `sorry`" in salida):
        fallos.append("compila, pero hay declaraciones con sorry")
    else:
        print(f"✔ lake env lean Esquemas/{x}.lean")
        for n in nombres:
            b = re.search(rf"'{re.escape(pref + n)}'\s+(does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",
                          salida)
            if not b:
                fallos.append(f"#print axioms no informó sobre {n}")
                continue
            usados = {a.strip() for a in (b.group(2) or "").replace("\n", " ").split(",") if a.strip()}
            if n.split(".")[-1] in pendientes:
                print(f"· {n}: sin demostrar (la otra alternativa de su par)")
                continue
            if usados - PERMITIDOS:
                fallos.append(f"{n} usa axiomas no permitidos: {', '.join(sorted(usados - PERMITIDOS))}")
            else:
                print(f"✔ {n}: axiomas {', '.join(sorted(usados)) or 'ninguno'}")

    if r.returncode == 0 and not fallos:
        cmp = subprocess.run(["nice", "-n", "19", "lake", "env", "lean", "--run", "herramientas/Comparar.lean",
                              rel, f"Esquemas/{x}.lean", f"Esquemas.{x}"] + (["uno"] if pendientes else []),
                             cwd=RAIZ, capture_output=True, text=True)
        sc = cmp.stdout + cmp.stderr
        if cmp.returncode == 0 and "COMPARACION: OK" in sc:
            print("✔ segundo testigo: los tipos elaborados coinciden con los aprobados")
        else:
            det = " | ".join(l.strip() for l in sc.splitlines() if "✘" in l or "error" in l)
            fallos.append(f"el segundo testigo (Comparar.lean) no aprobó: {det[:400] or sc[-400:]}")

    if fallos:
        print(f"{x}: NO TERMINADO")
        for f in fallos:
            print(f"  ✘ {f}")
        return 1
    print(f"{x}: TERMINADO")
    return 0


if __name__ == "__main__":
    sys.exit(main())
