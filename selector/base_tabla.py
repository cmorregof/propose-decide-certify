"""La misma línea base restringida al catálogo, pero sobre la tabla que ve el modelo (41 × 21, 3 cifras)."""
import json, sys
from pathlib import Path
import numpy as np
import base_catalogo as B


def leer_tabla(p):
    filas = [l.split(",") for l in p.read_text().strip().splitlines()]
    x = np.array([float(v) for v in filas[0][1:]])
    t = np.array([float(f[0]) for f in filas[1:]])
    U = np.array([[float(v) for v in f[1:]] for f in filas[1:]])
    return x, t, U


def main(bench, kfrac):
    bench = Path(bench)
    verdad = {p["id"]: p for p in json.loads((bench / "verdad.json").read_text())["problemas"]}
    ac, errs, malos = 0, [], []
    for pid in sorted(verdad):
        x, t, U = leer_tabla(bench / pid / "tabla.csv")
        y, X = B.regresores(x, t, U, kmax_frac=kfrac)
        res = {m: B.ajustar(y, X, ts) for m, ts in B.ACTIVOS.items()}
        m = min(res, key=lambda q: res[q][1]); vv = verdad[pid]
        if m == vv["molde"]:
            ac += 1
            cf = res[m][0]
            errs.append(np.median([abs(cf.get(c, 0) - vv["coeficientes"][c]) / abs(vv["coeficientes"][c])
                                   for c in ("v", "alpha", "lambda") if vv["coeficientes"][c]]))
        else:
            malos.append((pid, vv["molde"], m))
    print(f"kfrac={kfrac}: {ac}/30, error mediano {np.median(errs):.3g}, fallos {malos}")


if __name__ == "__main__":
    for kf in (0.3, 0.5, 1.0):
        main(sys.argv[1], kf)
