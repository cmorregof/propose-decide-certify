"""Tabla E6 (selección de modelo) desde las respuestas registradas; escribe las claves en resultados.json (26 oct 2026).

    python3 tablas_selector.py <bench_v2> <runs/unirl/selector_cli/bench_v2> [resultados.json]

Solo lee los registros. Acierto de plantilla: la plantilla escogida es la verdadera ("ninguno" para los 6 problemas
fuera del catálogo). Error de coeficientes: mediana, sobre los problemas del catálogo con plantilla correcta, de la
mediana del error relativo de los coeficientes no nulos del molde verdadero.
"""
import json, sys
from pathlib import Path
import numpy as np

CORTO = {"claude-opus-5-5": "opus", "claude-sonnet-5-5": "sonnet", "claude-haiku-5-5": "haiku"}
NOMBRE = {"opus": "Opus", "sonnet": "Sonnet", "haiku": "Haiku"}


def main(bench, runs, salida="resultados.json"):
    verdad = {p["id"]: p for p in json.loads((Path(bench) / "verdad.json").read_text())["problemas"]}
    R = json.loads(Path(salida).read_text(encoding="utf-8"))
    errores_txt, resumen = [], {}
    for modelo, m in CORTO.items():
        for mod in ("texto", "datos", "imagen"):
            d = Path(runs) / modelo / mod
            regs = {f.stem: json.loads(f.read_text()) for f in d.glob("p*.json")} if d.exists() else {}
            if len(regs) < len(verdad):
                print(f"{modelo} {mod}: {len(regs)}/{len(verdad)} — incompleto, no se escribe")
                continue
            ac = ninguno = malformadas = 0
            errs = []
            for pid, v in verdad.items():
                s = regs[pid].get("seleccion")
                if s is None:
                    malformadas += 1
                    continue
                if s["plantilla"] == v["molde"]:
                    ac += 1
                    if v["molde"] == "ninguno":
                        ninguno += 1
                    else:
                        e = [abs(s["coeficientes"][c] - v["coeficientes"][c]) / abs(v["coeficientes"][c])
                             for c in ("v", "alpha", "lambda") if v["coeficientes"][c] != 0]
                        errs.append(float(np.median(e)))
            med = float(np.median(errs)) if errs else None
            resumen[(m, mod)] = (ac, ninguno, med, malformadas)
            fuente = f"{runs}/{modelo}/{mod} (tablas_selector.py)"
            R[f"sel{m}{mod}"] = {"valor": str(ac), "nivel": "E", "fuente": fuente, "fecha": "2026-10-26",
                                 "nota": f"de 36; respuestas mal formadas: {malformadas}"}
            R[f"sel{m}{mod}ninguno"] = {"valor": str(ninguno), "nivel": "E", "fuente": fuente, "fecha": "2026-10-26",
                                        "nota": "de 6"}
            print(f"{modelo:18s} {mod:7s} plantilla {ac}/36  ninguno {ninguno}/6  error mediano {med}  mal formadas {malformadas}")
    if len(resumen) == 9:
        partes = []
        for mod, nom in (("texto", "text"), ("datos", "data"), ("imagen", "image")):
            vals = ", ".join(f"{NOMBRE[m]} {100 * resumen[(m, mod)][2]:.1f}\\%" if resumen[(m, mod)][2] is not None
                             else f"{NOMBRE[m]} n/a" for m in ("opus", "sonnet", "haiku"))
            partes.append(f"{nom}: {vals}")
        R["selerrores"] = {"valor": "median relative error " + "; ".join(partes), "nivel": "E",
                           "fuente": "tablas_selector.py", "fecha": "2026-10-26", "nota": ""}
    Path(salida).write_text(json.dumps(R, ensure_ascii=False, indent=1), encoding="utf-8")


if __name__ == "__main__":
    main(*sys.argv[1:])
