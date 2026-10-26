"""Tablas E4 (A8) y E5 (A9 v2) desde los registros de las corridas; solo lee (26 oct 2026).

    python3 tablas_esquemas.py <runs/unirl/esquemas_cli/corridas> <verdad_tandas.json> <salida.json>

Por (tanda, modelo, config): toma la corrida terminada más reciente de cada tarea cuyo sha_tarea es el aprobado.
Decidida = el lado resuelto es el verdadero. Intentos = suma de intentos de los episodios hasta el que resolvió.
"""
import json, sys
from pathlib import Path

CORTO = {"claude-opus-5-5": "opus", "claude-sonnet-5-5": "sonnet", "claude-haiku-5-5": "haiku"}
CLAVE = {"A8_Moldes": "aocho", "A9v2_Aleatorios": "anueve"}


def main(corridas, verdad_js, salida):
    V = json.loads(Path(verdad_js).read_text())
    out, detalle = {}, []
    for tanda, verdad in ((t, V[t]) for t in CLAVE):
        for modelo, m in CORTO.items():
            for cfg in ("CC", "SC"):
                dec = falso = intentos_ok = completas = 0
                primera = 0
                for tarea, lado in sorted(verdad.items()):
                    runs = sorted((Path(corridas) / tarea).glob(f"*-{modelo}-{cfg}"))
                    metas = [json.loads((r / "meta.json").read_text()) for r in runs if (r / "meta.json").exists()]
                    metas = [x for x in metas if x.get("sha_tarea") == V["sha"][tanda] and x.get("motivo_fin") == "completo"]
                    if not metas:
                        continue
                    meta = metas[-1]; completas += 1
                    res = meta.get("resultados", [])
                    n_int, resuelto = 0, None
                    for e in res:
                        n_int += e.get("intentos", 0)
                        if e.get("resuelto"):
                            resuelto = e["resuelto"]; break
                    ok = resuelto == f"{tarea}_{lado}"
                    if resuelto and not ok:
                        falso += 1
                    if ok:
                        dec += 1; intentos_ok += n_int; primera += (n_int == 1)
                    detalle.append({"tanda": tanda, "modelo": modelo, "config": cfg, "tarea": tarea, "verdad": lado,
                                    "resuelto": resuelto, "intentos": n_int, "usd": meta.get("usd")})
                total = len(verdad)
                out[f"{CLAVE[tanda]}{m}{cfg.lower()}n"] = {"completas": completas, "total": total, "decididas": dec,
                                                          "lado_falso_aceptado": falso, "primer_intento": primera,
                                                          "intentos_medios": round(intentos_ok / dec, 2) if dec else None}
                print(f"{tanda:16s} {m:6s} {cfg}: {completas}/{total} corridas, decididas {dec}, "
                      f"primer intento {primera}, media {out[f'{CLAVE[tanda]}{m}{cfg.lower()}n']['intentos_medios']}, "
                      f"lado falso aceptado {falso}")
    Path(salida).write_text(json.dumps({"resumen": out, "detalle": detalle}, ensure_ascii=False, indent=1))


if __name__ == "__main__":
    main(*sys.argv[1:])
