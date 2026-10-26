"""Líneas base sin LLM para el banco v2 (26 oct 2026).
  catalogo      regresión de u_t sobre los términos de cada molde, selección por BIC (siempre escoge uno de los cinco)
  catalogo+nl   lo mismo, pero si añadir u² o u·u_x baja el BIC en más de DELTA, responde «ninguno»
Sobre la malla completa (datos.npz) y sobre la tabla que ve el modelo (tabla.csv)."""
import json, sys, itertools
from pathlib import Path
import numpy as np
import base_catalogo as B
from base_tabla import leer_tabla

def regresores_nl(x, t, U, kfrac):
    y, X = B.regresores(x, t, U, kmax_frac=kfrac)
    u, ux = X["lambda"], -X["v"]
    X = dict(X); X["u2"] = u * u; X["uux"] = u * ux
    return y, X

def decidir(y, X, delta):
    res = {m: B.ajustar(y, X, ts) for m, ts in B.ACTIVOS.items()}
    m = min(res, key=lambda q: res[q][1])
    nl = min(B.ajustar(y, X, B.ACTIVOS[mm] + list(extra))[1]
             for mm in B.ACTIVOS for r in (1, 2) for extra in itertools.combinations(["u2", "uux"], r))
    return m, res[m][0], (res[m][1] - nl) > delta

def main(bench, delta=10.0):
    bench = Path(bench)
    verdad = {p["id"]: p for p in json.loads((bench / "verdad.json").read_text())["problemas"]}
    for fuente, kfrac in (("malla", 0.15), ("tabla", 0.5)):
        ac_c = ac_n = 0; fallos_n = []
        for pid in sorted(verdad):
            if fuente == "malla":
                z = np.load(bench / pid / "datos.npz"); x, t, U = z["x"], z["t"], z["u"]
            else:
                x, t, U = leer_tabla(bench / pid / "tabla.csv")
            y, X = regresores_nl(x, t, U, kfrac)
            m, cf, hay_nl = decidir(y, X, delta)
            v = verdad[pid]["molde"]
            ac_c += (m == v)
            mn = "ninguno" if hay_nl else m
            ac_n += (mn == v)
            if mn != v: fallos_n.append((pid, verdad[pid]["modelo_real"], mn))
        print(f"{fuente}: catálogo {ac_c}/{len(verdad)} · catálogo+no lineal (Δ={delta}) {ac_n}/{len(verdad)}  fallos: {fallos_n}")

if __name__ == "__main__":
    main(sys.argv[1], *(float(a) for a in sys.argv[2:]))
