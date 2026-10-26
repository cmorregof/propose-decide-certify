"""Línea base de A5: lo que cierra un guion FIJO, sin pistas propias de cada esquema (25 oct 2026).
Se corre desde la raíz de prometeo_lean:  python3 linea_base_A5.py

Lado «sí»: desplegar el símbolo, partir la región y llamar a nlinarith con sin²+cos²=1 y -1 ≤ cos ≤ 1.
Lado «no»: probar como testigo cada combinación de los extremos numéricos que aparecen en la región (y 0), con
θ ∈ {π, π/2}, y cerrar con simp + norm_num. Es una búsqueda barata, no una prueba con ideas.
Cada intento es un `example` en un solo archivo; un error en uno no afecta a los demás."""
import itertools, json, re, subprocess, sys
from fractions import Fraction
from pathlib import Path

C_ = "\nend PrometeoLean.Esquemas\n"
A2d = Path("Esquemas/A2_Plantilla.lean").read_text()
A5a = Path("aprobados/Esquemas/A5_Decidir.lean").read_text()
bloque = A5a[A5a.index("/-! ## A5."):A5a.rindex(C_)]
defs = "\n\n".join(m.group(0).rstrip() for m in re.finditer(r"/-- \*\*[a-z_]+\.\*\*[^\n]*-/\nnoncomputable def [^\n]*\n(?:  [^\n]*\n)*", bloque))
SIMP = "esq_{i}, Finset.sum_insert, Real.cos_neg, Real.sin_neg, Real.cos_two_mul, Real.sin_two_mul"


def numero(s):
    s = s.strip()
    if not re.fullmatch(r"[-0-9 /().]+", s):
        return None
    try:
        return Fraction(eval(re.sub(r"(\d+)", r"Fraction(\1)", s), {"Fraction": Fraction}, {}))
    except Exception:
        return None


def extremos(region, ps):
    cand = {p: {Fraction(0)} for p in ps}
    for atomo in re.split(r"∧|∨", region):
        lados = re.split(r"≤|<|=|≠", atomo)
        for a, b in itertools.permutations(lados, 2):
            v = numero(b.strip())
            if v is not None:
                for p in ps:
                    if re.fullmatch(rf"\s*\(?\s*{p}\s*\)?\s*", a):
                        cand[p].add(v)
    return cand


def q(v):
    return f"({v.numerator} / {v.denominator} : ℝ)" if v.denominator != 1 else f"({v.numerator} : ℝ)"


ejemplos = []           # (etiqueta, texto)
spec = json.loads(Path("herramientas/esquemas_decidir_A5.json").read_text())["propuestas"]
for p in spec:
    i, ps = p["id"], p["parametros"]
    E = f"(esq_{i} {' '.join(ps)})"
    for d in p["decidir"]:
        e, R = d["etiqueta"], d["region"]
        tarea = f"esq_{i}_decide_{e}"
        ejemplos.append((f"{tarea}|si", f"example : ∀ {' '.join(ps)} : ℝ, ({R}) → {E}.vonNeumann := by\n"
                         f"  intro {' '.join(ps)} hR\n  casesm* _ ∧ _\n  rw [Esquema.vonNeumann_iff_sq]\n  intro θ\n"
                         f"  simp [{SIMP.format(i=i)}]\n"
                         f"  nlinarith [Real.sin_sq_add_cos_sq θ, Real.cos_le_one θ, Real.neg_one_le_cos θ]\n"))
        cand = extremos(R, ps)
        for w in itertools.product(*[sorted(cand[x]) for x in ps]):
            for th, nom in (("Real.pi", "pi"), ("Real.pi / 2", "pi2")):
                ws = ", ".join(q(v) for v in w)
                ejemplos.append((f"{tarea}|no|{ws}|{nom}",
                                 f"example : ∃ {' '.join(ps)} : ℝ, ({R}) ∧ ¬ {E}.vonNeumann := by\n"
                                 f"  refine ⟨{ws}, by norm_num, ?_⟩\n  rw [Esquema.vonNeumann_iff_sq]\n  intro h\n"
                                 f"  have h1 := h ({th})\n"
                                 f"  simp [{SIMP.format(i=i)}, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, "
                                 f"Real.sin_pi_div_two] at h1\n  norm_num at h1\n"))

cab = A2d[: -len(C_)] + "\n" + defs + "\n\n"
lineas, cuerpo = [], ""
for et, t in ejemplos:
    lineas.append((et, cab.count("\n") + cuerpo.count("\n") + 1, cab.count("\n") + cuerpo.count("\n") + t.count("\n")))
    cuerpo += t + "\n"
Path("Esquemas/linea_base_A5.lean").write_text(cab + cuerpo + C_)
r = subprocess.run(["lake", "env", "lean", "Esquemas/linea_base_A5.lean"], capture_output=True, text=True)
errs = [int(m.group(1)) for m in re.finditer(r"linea_base_A5\.lean:(\d+):\d+: error", r.stdout + r.stderr)]
ok = {}
for et, a, b in lineas:
    bien = not any(a <= x <= b + 1 for x in errs)
    tarea, lado = et.split("|")[:2]
    ok.setdefault((tarea, lado), []).append((bien, et))
res = {}
for (tarea, lado), v in sorted(ok.items()):
    gano = [et for b, et in v if b]
    res.setdefault(tarea, {})[lado] = gano[0] if gano else None
etiq = json.loads(Path(sys.argv[1]).read_text()) if len(sys.argv) > 1 else {}
for tarea, d in res.items():
    print(f"{tarea:34s} sí: {'CIERRA' if d.get('si') else '—':7s} no: {('CIERRA ' + d['no'].split('|', 2)[2]) if d.get('no') else '—'}"
          + (f"   (verdad: {etiq[tarea]})" if tarea in etiq else ""))
Path("Esquemas/linea_base_A5.lean").unlink()
