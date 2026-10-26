"""Línea base sin LLM: z3 decide cada tarea de decidir (26 oct 2026). No produce prueba de kernel.

    python3 linea_base_z3.py <tanda.json> [<tanda.json> …] > resultado.json

Para cada esquema: F(p, c) = R(c)² + (1 − c²)·S(c)² − 1 con c = cos θ (polinomios de Chebyshev), así que
von Neumann(p) ⟺ ∀ c ∈ [−1, 1], F ≤ 0.
  - decidir (contención):  «sí» ⟺ ¬∃ p, c: R(p) ∧ −1 ≤ c ≤ 1 ∧ F > 0      (sin alternancia: nlsat)
  - decidir exacta:         «sí» ⟺ ¬∃ p: (R(p) ∧ ∃c F > 0) ∨ (¬R(p) ∧ ∀c F ≤ 0)   (alternancia: qsat)
"""
import json, sys, time
import sympy as sp
import z3

c = sp.Symbol("c", real=True)


def a_sympy(txt, params):
    s = txt.replace("^", "**").replace("≤", "<=").replace("≠", "!=")
    loc = {p: sp.Symbol(p, real=True) for p in params}
    return sp.sympify(s, locals=loc)


def _split(s, op):
    partes, d, cur = [], 0, ""
    for ch in s:
        d += (ch == "(") - (ch == ")")
        if ch == op and d == 0:
            partes.append(cur); cur = ""
        else:
            cur += ch
    return partes + [cur]


def region_sympy(txt, params):
    loc = {p: sp.Symbol(p, real=True) for p in params}
    ar = lambda e: sp.sympify(e.replace("^", "**"), locals=loc)

    def prop(s):
        s = s.strip()
        if len(o := _split(s, "∨")) > 1:
            return sp.Or(*[prop(x) for x in o])
        if len(a := _split(s, "∧")) > 1:
            return sp.And(*[prop(x) for x in a])
        if s.startswith("¬"):
            return sp.Not(prop(s[1:]))
        if s.startswith("(") and s.endswith(")") and any(x in s for x in "∧∨¬≤<=≠") and _split(s[1:-1], "≤") != [s[1:-1]] or \
                (s.startswith("(") and s.endswith(")") and ("∧" in s or "∨" in s)):
            return prop(s[1:-1])
        for op, f in (("≤", sp.Le), ("≠", sp.Ne), ("<", sp.Lt), ("=", sp.Eq)):
            if op in s:
                l, r = s.split(op, 1)
                return f(ar(l), ar(r))
        raise ValueError(f"no entiendo {s!r}")
    return prop(txt)


def a_z3(e, env):
    if e.is_Symbol:
        return env[e.name]
    if e.is_Rational or e.is_Integer:
        return z3.RealVal(f"{e.p}/{e.q}")
    if e.is_Add:
        return z3.Sum([a_z3(a, env) for a in e.args])
    if e.is_Mul:
        r = a_z3(e.args[0], env)
        for a in e.args[1:]:
            r = r * a_z3(a, env)
        return r
    if e.is_Pow and e.exp.is_Integer and e.exp >= 0:
        b = a_z3(e.base, env); r = z3.RealVal(1)
        for _ in range(int(e.exp)):
            r = r * b
        return r
    if isinstance(e, sp.And):
        return z3.And([a_z3(a, env) for a in e.args])
    if isinstance(e, sp.Or):
        return z3.Or([a_z3(a, env) for a in e.args])
    if isinstance(e, sp.Not):
        return z3.Not(a_z3(e.args[0], env))
    if isinstance(e, sp.LessThan):
        return a_z3(e.lhs, env) <= a_z3(e.rhs, env)
    if isinstance(e, sp.StrictLessThan):
        return a_z3(e.lhs, env) < a_z3(e.rhs, env)
    if isinstance(e, sp.GreaterThan):
        return a_z3(e.lhs, env) >= a_z3(e.rhs, env)
    if isinstance(e, sp.StrictGreaterThan):
        return a_z3(e.lhs, env) > a_z3(e.rhs, env)
    if isinstance(e, sp.Ne):
        return a_z3(e.lhs, env) != a_z3(e.rhs, env)
    if isinstance(e, sp.Eq):
        return a_z3(e.lhs, env) == a_z3(e.rhs, env)
    if e == sp.true:
        return z3.BoolVal(True)
    raise ValueError(f"no sé traducir {e!r}")


def F_de(p):
    params = p["parametros"]
    st = {int(k): a_sympy(v, params) for k, v in p["stencil"].items()}
    R = sum(v * sp.chebyshevt(abs(k), c) for k, v in st.items())
    S = sum((1 if k > 0 else -1) * v * sp.chebyshevu(abs(k) - 1, c) for k, v in st.items() if k != 0)
    return sp.expand(R ** 2 + (1 - c ** 2) * S ** 2 - 1)


def decidir(F, reg, params, exacta, timeout_ms=120000):
    env = {q: z3.Real(q) for q in params}
    env["c"] = z3.Real("c")
    Fz = a_z3(F, env)
    Rz = a_z3(reg, env)
    cz = env["c"]
    rango = z3.And(cz >= -1, cz <= 1)
    if not exacta:
        s = z3.SolverFor("QF_NRA")
        s.set("timeout", timeout_ms)
        s.add(Rz, rango, Fz > 0)
    else:
        inestable = z3.Exists([cz], z3.And(rango, Fz > 0))
        s = z3.Tactic("qsat").solver()
        s.set("timeout", timeout_ms)
        s.add(z3.Or(z3.And(Rz, inestable), z3.And(z3.Not(Rz), z3.Not(inestable))))
    t0 = time.time()
    r = s.check()
    dt = time.time() - t0
    lado = {"unsat": "si", "sat": "no"}.get(str(r), "desconocido")
    return lado, dt


def main():
    out = []
    for js in sys.argv[1:]:
        for p in json.load(open(js))["propuestas"]:
            params = p["parametros"]
            F = F_de(p)
            for campo, exacta in (("decidir", False), ("decidir_exacta", True)):
                for d in p.get(campo, []):
                    reg = region_sympy(d["region"], params)
                    lado, dt = decidir(F, reg, params, exacta)
                    out.append({"tanda": js.split("/")[-1], "tarea": f"esq_{p['id']}_decide_{d['etiqueta']}",
                                "exacta": exacta, "lado_z3": lado, "segundos": round(dt, 3)})
                    print(json.dumps(out[-1], ensure_ascii=False), file=sys.stderr, flush=True)
    print(json.dumps(out, ensure_ascii=False, indent=1))


if __name__ == "__main__":
    main()
