"""Evaluación del selector de modelos y línea base sin LLM (26 oct 2026).

    python3 evaluar_selector.py base  <bench>                    # línea base: el descubrimiento del framework (sin LLM)
    python3 evaluar_selector.py tabla <bench> <runs/unirl/selector_cli/<bench>>   # tabla de aciertos por modelo y modalidad

Acierto de molde = el molde escogido es el verdadero. Error de coeficientes = error relativo en los coeficientes que el
molde verdadero tiene distintos de cero (solo cuando el molde es correcto).
"""
import json, os, sys
from pathlib import Path
import numpy as np

AQUI = Path(__file__).resolve().parent
MOLDE_DE = {(False, True, False): "calor", (True, False, False): "adveccion", (True, True, False): "adveccion_difusion",
            (False, True, True): "reaccion_difusion", (True, True, True): "adveccion_reaccion_difusion"}


def molde_de_coefs(cf, tol=1e-6):
    return MOLDE_DE.get((abs(cf.get("v", 0)) > tol, abs(cf.get("alpha", 0)) > tol, abs(cf.get("lambda", 0)) > tol),
                        "fuera_del_catalogo")


def err_coefs(verdad, est):
    out = {}
    for k in ("v", "alpha", "lambda"):
        if abs(verdad[k]) > 0:
            out[k] = abs(est.get(k, 0) - verdad[k]) / abs(verdad[k])
    return out


def base(bench: Path):
    sys.path.insert(0, os.environ.get("PINN_SRC", str(AQUI.parent / "trabajo_t0" / "src")))
    from st_pinn_core import STField
    from st_pinn_discovery import ModelDiscovery, coeficientes_modelo
    verdad = {p["id"]: p for p in json.loads((bench / "verdad.json").read_text())["problemas"]}
    filas = []
    for pid in sorted(verdad):
        z = np.load(bench / pid / "datos.npz")
        st = STField(values=z["u"], t=z["t"], x=z["x"], kind="1D+t", var_name="u", space_unit="m")
        try:
            d = ModelDiscovery(verbose=False).discover(st)
            c = coeficientes_modelo(d)
            otros = {k: v for k, v in c.items() if k not in ("v", "alpha", "react") and abs(v) > 1e-6}
            est = {"v": c.get("v", 0.0), "alpha": c.get("alpha", 0.0), "lambda": c.get("react", 0.0)}
            m = "fuera_del_catalogo" if otros else molde_de_coefs(est)
            filas.append({"id": pid, "verdad": verdad[pid]["molde"], "escogido": m, "ecuacion": d.equation,
                          "otros_terminos": otros, "coeficientes": est,
                          "error_rel": err_coefs(verdad[pid]["coeficientes"], est) if m == verdad[pid]["molde"] else None})
        except Exception as e:          # noqa: BLE001
            filas.append({"id": pid, "verdad": verdad[pid]["molde"], "escogido": "error", "error": f"{type(e).__name__}: {e}"})
        print(json.dumps({k: filas[-1].get(k) for k in ("id", "verdad", "escogido", "ecuacion")}, ensure_ascii=False), flush=True)
    ac = sum(f["escogido"] == f["verdad"] for f in filas)
    print(f"línea base (descubrimiento del framework, sin LLM): {ac}/{len(filas)} moldes correctos")
    (bench.parent / f"base_{bench.name}.json").write_text(json.dumps(filas, ensure_ascii=False, indent=1))


def tabla(bench: Path, runs: Path):
    verdad = {p["id"]: p for p in json.loads((bench / "verdad.json").read_text())["problemas"]}
    res = {}
    for modelo in sorted(p.name for p in runs.iterdir() if p.is_dir()):
        for modalidad in ("texto", "datos", "imagen"):
            d = runs / modelo / modalidad
            if not d.exists():
                continue
            ac, n, errs = 0, 0, []
            for f in sorted(d.glob("p*.json")):
                r = json.loads(f.read_text()); v = verdad[r["problema"]]; n += 1
                s = r.get("seleccion")
                if s and s["plantilla"] == v["molde"]:
                    ac += 1
                    e = err_coefs(v["coeficientes"], s["coeficientes"])
                    if e:
                        errs.append(np.median(list(e.values())))
            res[(modelo, modalidad)] = (ac, n, float(np.median(errs)) if errs else None)
            print(f"{modelo:20s} {modalidad:7s} molde {ac}/{n}  error relativo mediano de coeficientes "
                  f"{res[(modelo, modalidad)][2]}")
    return res


if __name__ == "__main__":
    if sys.argv[1] == "base":
        base(Path(sys.argv[2]))
    else:
        tabla(Path(sys.argv[2]), Path(sys.argv[3]))
