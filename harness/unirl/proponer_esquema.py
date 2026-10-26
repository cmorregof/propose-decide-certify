"""El proponente del lazo del diseño A (25 oct 2026): un modelo de lenguaje propone un esquema de diferencias finitas
para un modelo descubierto que el FD del framework de PINNs no pudo simular.

La propuesta es un DATO en el formato de prometeo_lean/herramientas/generar_esquemas.py. No se cree: la región de
estabilidad que declara se convierte en una tarea de decidir (`esq_<id>_decide_lazo`: ¿∀ región → von Neumann, o
∃ punto de la región sin von Neumann?) y la decide el kernel de Lean a través de frontera_esquemas. El framework
corre la simulación con el número de subpasos que la región declarada permite, y la estabilidad en los parámetros
exactos de esa corrida queda como el par de decidir `esq_<id>_decide_corrida_si/_no`.

    python -m unirl.proponer_esquema --cli --muestras 3                      # el caso por defecto (advección pura)
    python -m unirl.proponer_esquema --cli --muestras 5 --caso advdif        # el caso 2 (advección-difusión)
    python -m unirl.proponer_esquema --cli --muestras 3 --caso caso.json     # otro caso

Escribe en runs/unirl/esquemas_cli/propuestas/<fecha>/ (o runs/unirl/esquemas/propuestas/ sin --cli): el prompt,
cada respuesta cruda, cada propuesta validada (o el motivo del rechazo) y un resumen. Claude no lo ejecuta: lo
corre Carlos. Sin --cli usa la API (con libro de gasto en logs/gasto_esquemas.json y tope por llamada).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import datetime
from pathlib import Path

from . import frontera as F
from . import frontera_esquemas as FE
from .loop import ProviderFatal

# El caso por defecto: lo que devolvió el framework sobre adv_dif_1d() (α = 2·10⁻³, v = 1, solución exacta) el
# 25 oct 2026. El descubrimiento se quedó con la advección pura y el FD respondió «no simulado».
CASO = {
    "modelo_descubierto": "u_t = -0.9998·u_x",
    "coeficientes": {"alpha": 0.0, "v": 0.9998},
    "malla": {"dx": 0.025, "dt": 0.02, "puntos": 161, "pasos": 101},
    "fallo": "FDEstabilidadError: advección centrada sin difusión: FTCS es incondicionalmente inestable (von Neumann)",
    "datos": {"generador": "adv_dif_1d", "alpha": 0.002},
}

# El caso 2 (25 oct): con α = 5·10⁻³ el descubrimiento SÍ conserva la difusión y FTCS corre, pero necesita 5 subpasos
# por paso de datos (ν² ≤ 2r es la restricción que manda). Aquí un esquema de dos parámetros (r, nu) y su región son
# el punto: es donde una región declarada puede estar mal.
CASOS = {
    "adveccion": CASO,
    "advdif": {
        "modelo_descubierto": "u_t = -0.9998·u_x + 0.005001·u_xx",
        "coeficientes": {"alpha": 0.005001, "v": 0.9998},
        "malla": {"dx": 0.025, "dt": 0.02, "puntos": 161, "pasos": 101},
        "fallo": "simulado, pero FTCS centrado (estable si nu² ≤ 2r ≤ 1) necesita 5 subpasos por paso de datos",
        "datos": {"generador": "adv_dif_1d", "alpha": 0.005},
    },
}

SISTEMA = """Eres un analista numérico. Propones esquemas explícitos de diferencias finitas de dos niveles para una \
ecuación en derivadas parciales lineal en la recta. Tu propuesta NO se cree: la región de estabilidad que declares \
la juzgará el kernel de Lean (von Neumann exacto: |g(θ)| ≤ 1 para todo θ real), y la simulación correrá con el \
número de subpasos que tu región permita. Una región equivocada se descubre."""

FORMATO = r"""Convención (la única que entiende el sistema): para u_t + v·u_x = α·u_xx con subpaso h y malla dx,
    r = α·h/dx²     nu = v·h/dx
y un paso del esquema es  u_j ← Σ_k a_k · u_{j+k}  (k entero; el símbolo es g(θ) = Σ_k a_k·e^{i k θ}).

Responde con UN bloque JSON entre <<< y >>>, con exactamente estos campos:
<<<
{"id": "minusculas_y_guiones_bajos",
 "descripcion": "una línea",
 "parametros": ["nu"],                       (subconjunto de ["r", "nu"]; solo los que el stencil usa)
 "stencil": {"-1": "...", "0": "...", "1": "..."},   (k → coeficiente a_k como expresión en los parámetros)
 "momentos": ["M0", "M1", "M2"],             (M_m = Σ_k a_k·k^m, como expresiones; consistencia: M0 = 1, M1 = -nu)
 "estable_sii": "región EXACTA donde |g| ≤ 1 para todo θ",
 "testigos": {"estable_sii": {"nu": "1/2"}}  (un punto de la región, con números)
}
>>>
Si no sabes la región exacta, usa "estable_si" (una región suficiente) en lugar de "estable_sii", con su testigo
en "testigos": {"estable_si": {...}}.
Gramática de las expresiones: números, los parámetros, + - * / ^ (exponente natural literal) y paréntesis; en las
regiones además ∧ ∨ ≤ < = ≠ ¬. Nada más."""


def prompt(caso: dict) -> str:
    c = caso
    return (f"# El caso\n\nEl framework descubrió este modelo a partir de los datos:\n\n    {c['modelo_descubierto']}\n\n"
            f"Coeficientes: {json.dumps(c['coeficientes'])}. Malla de los datos: {json.dumps(c['malla'])}.\n"
            f"El simulador de referencia (FTCS centrado, con subpasos elegidos por estabilidad) respondió:\n\n"
            f"    {c['fallo']}\n\n"
            "Propón UN esquema explícito que permita simular este modelo sobre esa malla con pocos subpasos por paso "
            "de datos y con error pequeño frente a los datos. Declara su región de estabilidad de von Neumann.\n\n"
            + FORMATO)


def extraer(texto: str) -> dict:
    m = re.findall(r"<<<(.*?)>>>", texto or "", re.S)
    if not m:
        raise ValueError("la respuesta no trae un bloque <<< … >>>")
    return json.loads(m[-1].strip())


def validar(p: dict) -> list[str]:
    """Lo que se puede comprobar sin Lean: que el generador acepta la propuesta y que la consistencia declarada es la
    pedida. La región NO se juzga aquí (eso es del kernel); se adjunta un chequeo numérico solo como información."""
    problemas = []
    sys.path.insert(0, str(F.PROMETEO / "herramientas"))
    import generar_esquemas as G
    try:
        G.bloque(p)
    except Exception as e:                       # noqa: BLE001 — el motivo va al registro
        problemas.append(f"el generador la rechaza: {e}")
    if not set(p.get("parametros", [])) <= {"r", "nu"}:
        problemas.append("parámetros fuera de {r, nu}")
    mom = p.get("momentos", [])
    try:
        ok = (len(mom) >= 2 and identicas(str(mom[0]), lambda r, nu: 1) and identicas(str(mom[1]), lambda r, nu: -nu))
    except Exception:                            # noqa: BLE001 — expresión fuera de la gramática
        ok = False
    if not ok:
        problemas.append(f"consistencia: se piden M0 = 1 y M1 = -nu; la propuesta declara {p.get('momentos')}")
    return problemas


# 25 oct: la consistencia se compara por VALOR, no por texto («-1*nu» y «0 - nu» son -nu). Evaluador exacto de la
# gramática del formato (números, r, nu, + - * / ^ con exponente natural literal, paréntesis), en Fraction.
def _eval_exacta(nodo, env):
    import ast
    from fractions import Fraction
    if isinstance(nodo, ast.Expression):
        return _eval_exacta(nodo.body, env)
    if isinstance(nodo, ast.Constant) and type(nodo.value) in (int, float):
        return Fraction(str(nodo.value))
    if isinstance(nodo, ast.Name) and nodo.id in env:
        return env[nodo.id]
    if isinstance(nodo, ast.UnaryOp) and isinstance(nodo.op, (ast.USub, ast.UAdd)):
        x = _eval_exacta(nodo.operand, env)
        return -x if isinstance(nodo.op, ast.USub) else x
    if isinstance(nodo, ast.BinOp):
        a = _eval_exacta(nodo.left, env)
        if isinstance(nodo.op, ast.BitXor):      # «^» de la gramática; el exponente tiene que ser un natural literal
            if not (isinstance(nodo.right, ast.Constant) and type(nodo.right.value) is int and 0 <= nodo.right.value <= 64):
                raise ValueError("exponente no admitido")
            return a ** nodo.right.value
        b = _eval_exacta(nodo.right, env)
        if isinstance(nodo.op, ast.Add):
            return a + b
        if isinstance(nodo.op, ast.Sub):
            return a - b
        if isinstance(nodo.op, ast.Mult):
            return a * b
        if isinstance(nodo.op, ast.Div):
            return a / b
    raise ValueError(f"expresión no admitida: {ast.dump(nodo)[:80]}")


def identicas(expr: str, f, puntos: int = 16) -> bool:
    """¿La expresión en r, nu vale lo mismo que f(r, nu) en `puntos` racionales al azar (aritmética exacta)? Una
    comprobación, no una prueba; el teorema de momentos lo decide Lean."""
    import ast
    import random
    from fractions import Fraction
    if "**" in expr:
        raise ValueError("«**» no es de la gramática")
    arbol = ast.parse(expr.strip(), mode="eval")
    rnd = random.Random(0)
    for _ in range(puntos):
        r = Fraction(rnd.randint(-997, 997), rnd.randint(1, 1009))
        nu = Fraction(rnd.randint(-997, 997), rnd.randint(1, 1009))
        if _eval_exacta(arbol, {"r": r, "nu": nu}) != f(r, nu):
            return False
    return True


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python -m unirl.proponer_esquema")
    ap.add_argument("--cli", action="store_true", help="llamar por claude -p (suscripción) en vez de la API")
    ap.add_argument("--modelo", default="claude-opus-5-5")
    ap.add_argument("--esfuerzo", default="high")
    ap.add_argument("--muestras", type=int, default=3)
    ap.add_argument("--caso", help=f"uno de {sorted(CASOS)} o un JSON con modelo_descubierto, coeficientes, malla, fallo, datos")
    ap.add_argument("--tope-usd", type=float, default=3.0)
    a = ap.parse_args(argv)
    caso = (CASOS[a.caso] if a.caso in CASOS else json.loads(Path(a.caso).read_text(encoding="utf-8"))) if a.caso else CASO
    base = F.BASE / "runs" / "unirl" / ("esquemas_cli" if a.cli else "esquemas") / "propuestas"
    F.LIBRO_FRONTERA = F.BASE / "logs" / ("gasto_esquemas_cli.json" if a.cli else "gasto_esquemas.json")
    carpeta = base / datetime.now().strftime("%Y%m%d-%H%M%S")
    carpeta.mkdir(parents=True, exist_ok=False)
    corrida = f"proponer-{carpeta.name}"
    prov = (FE.hacer_proveedor_cli if a.cli else F.hacer_proveedor)(a.modelo, corrida, a.tope_usd, a.esfuerzo)
    pr = prompt(caso)
    (carpeta / "prompt.md").write_text(SISTEMA + "\n\n---\n\n" + pr, encoding="utf-8")
    (carpeta / "caso.json").write_text(json.dumps(caso, ensure_ascii=False, indent=1), encoding="utf-8")
    resumen = []
    for i in range(1, a.muestras + 1):
        reg = {"muestra": i, "modelo": a.modelo, "cli": a.cli}
        try:
            texto = prov.complete(SISTEMA, pr)
            (carpeta / f"respuesta_{i}.md").write_text(texto, encoding="utf-8")
            p = extraer(texto)
            p["id"] = re.sub(r"[^a-z0-9_]", "_", str(p.get("id", "")).lower()).strip("_") or f"propuesta_{i}"
            p["origen"] = f"proponente {a.modelo}, muestra {i}, {carpeta.name}"
            reg["propuesta"] = p
            reg["problemas"] = validar(p)
        except ProviderFatal as e:               # sesión vencida, sin login o límite de uso: se para aquí
            print(f"abortado: {e}")
            return 1
        except Exception as e:                   # noqa: BLE001
            reg["error"] = f"{type(e).__name__}: {e}"
        (carpeta / f"propuesta_{i}.json").write_text(json.dumps(reg, ensure_ascii=False, indent=1), encoding="utf-8")
        resumen.append({k: reg.get(k) for k in ("muestra", "error", "problemas")}
                       | {"id": reg.get("propuesta", {}).get("id"),
                          "region": (reg.get("propuesta", {}).get("estable_sii") or reg.get("propuesta", {}).get("estable_si"))})
        print(json.dumps(resumen[-1], ensure_ascii=False))
    (carpeta / "resumen.json").write_text(json.dumps(resumen, ensure_ascii=False, indent=1), encoding="utf-8")
    print(f"registro en {carpeta}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
