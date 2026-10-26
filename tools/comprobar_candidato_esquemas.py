"""¿Vale el candidato que dejó el agente para UNA tarea de esquemas? (25 oct 2026)

  python3 herramientas/comprobar_candidato_esquemas.py <tanda> <tarea> <candidato.lean>
  p. ej. A3_Corpus esq_ftcs_calor_vonNeumann_iff ~/Personal/rl_metodos/runs/unirl/esquemas_cli/corridas/…/candidato_….lean

La frontera (rl_metodos/unirl/frontera_esquemas.py) ya juzgó la prueba dentro de su sandbox. Esto es el segundo
testigo, fuera del arnés del agente y con las herramientas de prometeo_lean:

1. Se arma, desde la tanda APROBADA (SHA-256 en aprobados/SHA256SUMS_esquemas*), el archivo de referencia de la
   tarea: la plantilla A2 aprobada, la definición del esquema y el enunciado (o los dos de un par de decidir), con su
   `sorry`. Es exactamente el contexto que vio el agente, pero con el texto aprobado de la plantilla.
2. El candidato se copia a Esquemas/candidatos/<tarea>.lean y debe cumplir el patrón de comprobar.py respecto de esa
   referencia: el texto aprobado intacto; solo cambian pruebas y caben lemas auxiliares entre bloques.
3. Compila; nada prohibido; `#print axioms` del teorema resuelto: solo propext, Classical.choice y Quot.sound. En un
   par de decidir, la otra alternativa queda con su `sorry` y nada puede depender de ella.
4. Comparar.lean (modo `uno`) confirma tipos elaborados idénticos y cuerpos de definición idénticos.
Imprime VALE o NO VALE.
"""
import hashlib, re, subprocess, sys, tempfile
from pathlib import Path

RAIZ = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(RAIZ / "herramientas"))
from comprobar import patron_aprobado, diagnostico, sin_comentarios, PROHIBIDOS, PERMITIDOS  # noqa: E402

CIERRE = "\nend PrometeoLean.Esquemas\n"


def _sumas() -> dict:
    return dict(reversed(l.split(None, 1)) for f in sorted((RAIZ / "aprobados").glob("SHA256SUMS_esquemas*"))
                for l in f.read_text().splitlines() if l.strip())


def _aprobado(nombre: str) -> str:
    rel = f"aprobados/Esquemas/{nombre}.lean"
    t = (RAIZ / rel).read_text(encoding="utf-8")
    if hashlib.sha256(t.encode()).hexdigest() != _sumas().get(rel):
        raise SystemExit(f"✘ {rel} no coincide con su SHA-256")
    return t


def _bloque(texto: str, inicio: str) -> str:
    m = re.search(inicio, texto, re.M)
    if not m:
        raise SystemExit(f"✘ no encontré {inicio!r} en la tanda aprobada")
    a = texto.rfind("\n\n", 0, m.start()) + 2
    b = texto.find("\n\n", m.start())
    return texto[a: b if b >= 0 else len(texto)].rstrip()


def referencia(tanda: str, tarea: str) -> tuple[str, list[str]]:
    ap, plantilla = _aprobado(tanda), _aprobado("A2_Plantilla")
    m = re.fullmatch(r"(esq_[a-z0-9_]+?)_(momentos|vonNeumann_iff|vonNeumann|positivo|inestable)", tarea)
    d = re.fullmatch(r"(esq_[a-z0-9_]+?)_decide_([a-z0-9]+)", tarea)
    if not m and not d:
        raise SystemExit(f"✘ {tarea}: no es una tarea de esquemas")
    esq = (m or d).group(1)
    nombres = [tarea] if m else [f"{tarea}_si", f"{tarea}_no"]
    defn = _bloque(ap, rf"^noncomputable def {re.escape(esq)} ")
    enunciados = [_bloque(ap, rf"^theorem {re.escape(n)} ") for n in nombres]
    for n, e in zip(nombres, enunciados):
        if not e.endswith(":= by\n  sorry"):
            raise SystemExit(f"✘ {n}: el enunciado aprobado no termina en «:= by sorry»")
    texto = plantilla[: -len(CIERRE)].rstrip() + "\n\n" + defn + "\n\n" + "\n\n".join(enunciados) + "\n" + CIERRE
    return texto, nombres


def main() -> int:
    if len(sys.argv) != 4:
        print(__doc__)
        return 2
    tanda, tarea, cand_p = sys.argv[1], sys.argv[2], Path(sys.argv[3]).expanduser()
    ref, nombres = referencia(tanda, tarea)
    dest = RAIZ / "Esquemas" / "candidatos"
    dest.mkdir(exist_ok=True)
    ref_p, act_p = dest / f"{tarea}.referencia.lean", dest / f"{tarea}.lean"
    ref_p.write_text(ref, encoding="utf-8")
    # El arnés une contexto, auxiliares y enunciado con líneas en blanco dobles; se normalizan a una sola (no cambia
    # el significado: Lean no distingue cuántas líneas en blanco separan dos declaraciones).
    actual = re.sub(r"\n{3,}", "\n\n", cand_p.read_text(encoding="utf-8"))
    act_p.write_text(actual, encoding="utf-8")
    fallos = []

    patron, literales, tipos = patron_aprobado(ref)
    mm = patron.fullmatch(actual)
    pendientes = set()
    if not mm:
        fallos.append(f"el texto aprobado cambió: {diagnostico(ref, literales, actual)}")
    else:
        print("✔ texto aprobado intacto (plantilla, definición y enunciado)")
        con_hueco = []
        for h in re.finditer(r"(?<=:= by\n)  sorry\n", ref):
            previos = re.findall(r"^theorem\s+(\S+)", ref[: h.start()], re.M)
            con_hueco.append(previos[-1])
        grupos = [g for g, tp in zip(mm.groups(), tipos) if tp == "prueba"]
        limpias = []
        for n, g in zip(con_hueco, grupos):
            if n in nombres and len(nombres) == 2 and g.strip() == "sorry":
                pendientes.add(n)
            else:
                limpias.append(g)
        if len(nombres) == 2 and len(pendientes) != 1:
            fallos.append(f"de {nombres} debe quedar demostrado exactamente uno (sin demostrar: {sorted(pendientes)})")
        texto = "\n".join(limpias + [g for g, tp in zip(mm.groups(), tipos) if tp == "auxiliar"])
        malos = sorted(set(y.group(0).strip() for y in PROHIBIDOS.finditer(sin_comentarios(texto))))
        if malos:
            fallos.append(f"las pruebas usan {', '.join(malos)}")

    resuelto = [n for n in nombres if n not in pendientes]
    if not fallos:
        with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=dest, delete=False, encoding="utf-8") as fh:
            fh.write(actual + "\n" + "".join(f"#print axioms PrometeoLean.Esquemas.{n}\n" for n in resuelto))
        r = subprocess.run(["nice", "-n", "19", "lake", "env", "lean", fh.name], cwd=RAIZ, capture_output=True, text=True)
        Path(fh.name).unlink()
        salida = r.stdout + r.stderr
        if r.returncode != 0:
            fallos.append("no compila: " + " | ".join(l for l in salida.splitlines() if "error" in l)[:600])
        else:
            for n in resuelto:
                b = re.search(rf"'PrometeoLean\.Esquemas\.{re.escape(n)}'\s+(does not depend on any axioms|depends on "
                              rf"axioms:\s*\[([^\]]*)\])", salida)
                usados = {a.strip() for a in ((b.group(2) or "") if b else "").replace("\n", " ").split(",") if a.strip()}
                if not b:
                    fallos.append(f"#print axioms no informó sobre {n}")
                elif usados - PERMITIDOS:
                    fallos.append(f"{n} usa axiomas no permitidos: {', '.join(sorted(usados - PERMITIDOS))}")
                else:
                    print(f"✔ {n}: compila; axiomas {', '.join(sorted(usados)) or 'ninguno'}")
    if not fallos:
        cmp = subprocess.run(["nice", "-n", "19", "lake", "env", "lean", "--run", "herramientas/Comparar.lean",
                              str(ref_p.relative_to(RAIZ)), str(act_p.relative_to(RAIZ)), f"Esquemas.candidatos.{tarea}",
                              "uno"], cwd=RAIZ, capture_output=True, text=True)
        sc = cmp.stdout + cmp.stderr
        if cmp.returncode == 0 and "COMPARACION: OK" in sc:
            print("✔ segundo testigo: tipos elaborados y definiciones idénticos a los aprobados")
        else:
            det = " | ".join(l.strip() for l in sc.splitlines() if "✘" in l or "error" in l)
            fallos.append(f"Comparar.lean no aprobó: {det[:400] or sc[-400:]}")
    if fallos:
        print(f"{tarea}: NO VALE")
        for f in fallos:
            print(f"  ✘ {f}")
        return 1
    lado = f" (decidido: «{resuelto[0].rsplit('_', 1)[1]}»)" if len(nombres) == 2 else ""
    print(f"{tarea}: VALE{lado}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
