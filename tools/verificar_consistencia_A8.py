"""Verdad (sympy) de las afirmaciones de consistencia de A8: no es prueba; sirve para etiquetar y equilibrar."""
import json, sys, itertools
import sympy as sp
from math import factorial
dt, dx, v, alpha, lam = sp.symbols("dt dx v alpha lam")
FIS = {"calor": [alpha], "adveccion": [v], "adveccion_difusion": [v, alpha], "reaccion_difusion": [lam, alpha],
       "adveccion_reaccion_difusion": [v, lam, alpha]}
C = {"calor": {2: alpha}, "adveccion": {1: -v}, "adveccion_difusion": {1: -v, 2: alpha},
     "reaccion_difusion": {0: lam, 2: alpha}, "adveccion_reaccion_difusion": {0: lam, 1: -v, 2: alpha}}

def coef2(c, m): return sum(c.get(i, 0) * c.get(m - i, 0) for i in range(m + 1))

def residuos(p, d):
    loc = {q: sp.Symbol(q) for q in p["parametros"]}
    sus = {loc[q]: sp.sympify(d["sustitucion"][q], locals={"alpha": alpha, "v": v, "lam": lam, "dt": dt, "dx": dx})
           for q in p["parametros"]}
    st = {int(k): sp.sympify(e.replace("^", "**"), locals=loc).subs(sus) for k, e in p["stencil"].items()}
    c = C[d["molde"]]; out = []
    for m in range(d["n"] + 1):
        M = sum(a * sp.Integer(j) ** m for j, a in st.items())
        obj = (1 if m == 0 else 0) + dt * c.get(m, 0) + (dt ** 2 / 2 * coef2(c, m) if d["orden_tiempo"] == 2 else 0)
        out.append(sp.simplify(M * dx ** m / factorial(m) - obj))
    return out

if __name__ == "__main__":
    js = json.load(open(sys.argv[1]))
    for p in js["propuestas"]:
        for d in p.get("consistente", []):
            r = residuos(p, d)
            ver = all(x == 0 for x in r)
            unos = {s: 1 for s in [dt, dx, v, alpha, lam]}
            todo1 = any(sp.nsimplify(x.subs(unos)) != 0 for x in r)
            mfalla = next((m for m, x in enumerate(r) if x != 0), None)
            print(f"{p['id']:22s} {d['etiqueta']} o{d['orden_tiempo']} n={d['n']} {d['molde']:28s} "
                  f"{'VERDADERA' if ver else 'falsa'}" + ("" if ver else f"  m={mfalla} resto={r[mfalla]}  «todo 1» refuta: {todo1}"))
