"""Línea base sin LLM restringida al catálogo (26 oct 2026): regresión de u_t sobre {u, u_x, u_xx} con derivadas
espectrales filtradas en x (la malla es periódica) y diferencias centradas en t; para cada uno de los 5 moldes, mínimos
cuadrados con los términos activos del molde y selección por BIC. Usa la malla completa (datos.npz), no la tabla."""
import json, sys
from pathlib import Path
import numpy as np

ACTIVOS = {"calor": ["alpha"], "adveccion": ["v"], "adveccion_difusion": ["v", "alpha"],
           "reaccion_difusion": ["lambda", "alpha"], "adveccion_reaccion_difusion": ["v", "lambda", "alpha"]}


def regresores(x, t, U, kmax_frac=0.15):
    NX = len(x); L = NX * (x[1] - x[0])
    k = 2 * np.pi * np.fft.fftfreq(NX, d=L / NX)
    filtro = (np.abs(k) <= kmax_frac * np.abs(k).max()).astype(float)
    Uh = np.fft.fft(U, axis=1) * filtro
    u = np.real(np.fft.ifft(Uh, axis=1))
    ux = np.real(np.fft.ifft(1j * k * Uh, axis=1))
    uxx = np.real(np.fft.ifft(-(k ** 2) * Uh, axis=1))
    ut = (u[2:] - u[:-2]) / (2 * (t[1] - t[0]))
    s = slice(1, -1)
    # u_t = λ u − v u_x + α u_xx
    return ut.ravel(), {"lambda": u[s].ravel(), "v": -ux[s].ravel(), "alpha": uxx[s].ravel()}


def ajustar(y, X, terms):
    A = np.column_stack([X[c] for c in terms])
    coef, *_ = np.linalg.lstsq(A, y, rcond=None)
    rss = float(np.sum((y - A @ coef) ** 2)); n = len(y)
    return dict(zip(terms, coef)), n * np.log(rss / n) + len(terms) * np.log(n)


def main(bench):
    bench = Path(bench)
    verdad = {p["id"]: p for p in json.loads((bench / "verdad.json").read_text())["problemas"]}
    filas = []
    for pid in sorted(verdad):
        z = np.load(bench / pid / "datos.npz")
        y, X = regresores(z["x"], z["t"], z["u"])
        res = {m: ajustar(y, X, ts) for m, ts in ACTIVOS.items()}
        m = min(res, key=lambda q: res[q][1])
        cf = {c: float(res[m][0].get(c, 0.0)) for c in ("v", "alpha", "lambda")}
        vv = verdad[pid]
        err = {c: abs(cf[c] - vv["coeficientes"][c]) / abs(vv["coeficientes"][c])
               for c in ("v", "alpha", "lambda") if vv["coeficientes"][c] != 0} if m == vv["molde"] else None
        filas.append({"id": pid, "verdad": vv["molde"], "escogido": m, "coeficientes": cf, "error_rel": err})
        print(pid, f"{vv['molde']:28s} -> {m:28s}", {c: round(v, 4) for c, v in cf.items()},
              {c: round(v, 3) for c, v in (err or {}).items()})
    ac = sum(f["escogido"] == f["verdad"] for f in filas)
    errs = [np.median(list(f["error_rel"].values())) for f in filas if f["error_rel"]]
    print(f"línea base restringida al catálogo (BIC): {ac}/{len(filas)} moldes; error relativo mediano {np.median(errs):.3g}")
    (bench.parent / f"base_catalogo_{bench.name}.json").write_text(json.dumps(filas, indent=1))


if __name__ == "__main__":
    main(sys.argv[1])
