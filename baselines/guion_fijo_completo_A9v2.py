"""Pruebas de referencia de A9 (stencils aleatorios), generadas desde certificados exactos (26 oct 2026).

    python3 pruebas_A9.py <A2 demostrada> <A9 aprobada .lean> <esquemas_aleatorios_A9.json> <informe_A9.json> <salida.lean>

Para cada stencil y cada región [0, q]:
  - «sí»: |g|² − 1 = tᵃ(1 − cos θ)ᵇ G(t, cos θ), y G ≤ 0 en [0, q] × [−1, 1] se prueba caja por caja: en cada caja
    de la subdivisión, −G es una combinación con coeficientes ≥ 0 de productos (t − t₀)ᴵ(t₁ − t)ⁿ⁻ᴵ(c − c₀)ᴶ(c₁ − c)ᵐ⁻ᴶ
    (la base de Bernstein), y `linear_combination` lo comprueba con `ring`;
  - «no»: el testigo racional (t₀, c₀) del informe, con θ₀ = arccos c₀ y `norm_num`.
"""
import json, re, sys
from fractions import Fraction as Fr
from math import comb
from pathlib import Path
import sympy as sp

sys.path.insert(0, str(Path(__file__).parent))
from generar_aleatorios import t, c, factorizar, coef_monomios, a_caja  # noqa: E402

C_ = "\nend PrometeoLean.Esquemas\n"


def lean_num(x: Fr) -> str:
    return f"({x.numerator} : ℝ)" if x.denominator == 1 else f"(({x.numerator} : ℝ) / {x.denominator})"


def lean_expr(e, cvar="c") -> str:
    s = sp.sstr(sp.expand(e), order="lex").replace("**", "^")
    return re.sub(r"\bc\b", cvar, s)


def bernstein_coefs(cu, n, m):
    B = {}
    for I in range(n + 1):
        for J in range(m + 1):
            s = Fr(0)
            for (i, j), v in cu.items():
                if i <= I and j <= J:
                    s += v * Fr(comb(I, i), comb(n, i)) * Fr(comb(J, j), comb(m, j))
            B[(I, J)] = s
    return B


def arbol(P, q, prof=14):
    """Subdivisión hasta que cada caja tenga todos sus coeficientes de Bernstein ≤ 0. Devuelve el árbol."""
    coefs = coef_monomios(P)
    n = max(i for i, _ in coefs); m = max(j for _, j in coefs)

    def rec(t0, t1, c0, c1, d):
        B = bernstein_coefs(a_caja(coefs, t0, t1, c0, c1), n, m)
        if max(B.values()) <= 0:
            return ("hoja", t0, t1, c0, c1, B)
        if d >= prof:
            raise RuntimeError("sin certificado")
        tm, cm = (t0 + t1) / 2, (c0 + c1) / 2
        return ("nodo", t0, t1, c0, c1, tm, cm,
                [rec(t0, tm, c0, cm, d + 1), rec(t0, tm, cm, c1, d + 1), rec(tm, t1, c0, cm, d + 1), rec(tm, t1, cm, c1, d + 1)])
    return rec(Fr(0), Fr(q), Fr(-1), Fr(1), 0), n, m


def hojas(nodo):
    if nodo[0] == "hoja":
        yield nodo
    else:
        for h in nodo[7]:
            yield from hojas(h)


def pruebas_stencil(p, fila, R, S, F, a, b, G):
    i = p["id"]; E = f"esq_{i}"
    Gs = lean_expr(G.as_expr())
    out_aux = []
    out_aux.append(
        f"/-- Parte real del símbolo de `{E}`. -/\ntheorem {E}_re (t θ : ℝ) :\n"
        f"    ∑ k ∈ ({E} t).S, ({E} t).a k * Real.cos ((k : ℝ) * θ) = {lean_expr(R, 'Real.cos θ')} := by\n"
        f"  simp [{E}, Finset.sum_insert, Real.cos_neg, neg_mul, Real.cos_two_mul]\n  ring\n")
    out_aux.append(
        f"/-- Parte imaginaria del símbolo de `{E}`. -/\ntheorem {E}_im (t θ : ℝ) :\n"
        f"    ∑ k ∈ ({E} t).S, ({E} t).a k * Real.sin ((k : ℝ) * θ) = Real.sin θ * ({lean_expr(S, 'Real.cos θ')}) := by\n"
        f"  simp [{E}, Finset.sum_insert, Real.sin_neg, neg_mul, Real.sin_two_mul]\n  ring\n")
    P = {}
    for d in p["decidir"]:
        e = d["etiqueta"]
        q = Fr(re.search(r"t ≤ (\S+)$", d["region"]).group(1))
        verdadera = fila["verdadera"] == "si"
        if verdadera:
            tree, n, m = arbol(G, q)
            lemas = []
            for k, (_, t0, t1, c0, c1, B) in enumerate(hojas(tree)):
                dt, dc = t1 - t0, c1 - c0
                hs, comb_ = [], []
                for (I, J), bij in B.items():
                    if bij == 0:
                        continue
                    w = -bij * comb(n, I) * comb(m, J) / (dt ** n * dc ** m)
                    nm = f"p{I}_{J}"
                    hs.append(f"  have {nm} : 0 ≤ (t - {lean_num(t0)}) ^ {I} * ({lean_num(t1)} - t) ^ {n - I} * "
                              f"(c - {lean_num(c0)}) ^ {J} * ({lean_num(c1)} - c) ^ {m - J} :=\n"
                              f"    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (sub_nonneg.2 h1) _) "
                              f"(pow_nonneg (sub_nonneg.2 h2) _)) (pow_nonneg (sub_nonneg.2 h3) _)) "
                              f"(pow_nonneg (sub_nonneg.2 h4) _)")
                    comb_.append(f"{lean_num(w)} * {nm}")
                lemas.append(
                    f"/-- Auxiliar de A9: `G ≤ 0` en la caja {k} de `{E}`, región {e} (certificado de Bernstein). -/\n"
                    f"theorem {E}_G_{e}_caja{k} (t c : ℝ) (h1 : {lean_num(t0)} ≤ t) (h2 : t ≤ {lean_num(t1)}) "
                    f"(h3 : {lean_num(c0)} ≤ c) (h4 : c ≤ {lean_num(c1)}) :\n    {Gs} ≤ 0 := by\n"
                    + "\n".join(hs) + f"\n  linear_combination {' + '.join(comb_) if comb_ else '0'}\n")

            cnt = [0]

            def arma(nodo, ind, prof=0):
                if nodo[0] == "hoja":
                    k = cnt[0]; cnt[0] += 1
                    return [f"{ind}exact {E}_G_{e}_caja{k} t c (by linarith) (by linarith) (by linarith) (by linarith)"]
                tm, cm = nodo[5], nodo[6]
                L = [f"{ind}rcases le_total t {lean_num(tm)} with ht{prof} | ht{prof} <;> "
                     f"rcases le_total c {lean_num(cm)} with hc{prof} | hc{prof}"]
                for h in nodo[7]:
                    sub = arma(h, ind + "  ", prof + 1)
                    L.append(f"{ind}· " + sub[0].lstrip())
                    L += sub[1:]
                return L
            cuerpo = arma(tree, "  ")
            lemas.append(
                f"/-- Auxiliar de A9: `G ≤ 0` en `[0, {q}] × [−1, 1]` para `{E}`, región {e}. -/\n"
                f"theorem {E}_G_{e} (t c : ℝ) (h1 : 0 ≤ t) (h2 : t ≤ {lean_num(q)}) (h3 : -1 ≤ c) (h4 : c ≤ 1) :\n"
                f"    {Gs} ≤ 0 := by\n" + "\n".join(cuerpo) + "\n")
            out_aux += lemas
            Gc = lean_expr(G.as_expr(), "Real.cos θ")
            P[f"{E}_decide_{e}_si"] = (
                f"  intro t ht\n  rw [Esquema.vonNeumann_iff_sq]\n  intro θ\n  rw [{E}_re, {E}_im]\n"
                f"  have hc1 := Real.cos_le_one θ\n  have hc0 := Real.neg_one_le_cos θ\n"
                f"  have hG := {E}_G_{e} t (Real.cos θ) ht.1 ht.2 hc0 hc1\n"
                f"  have hs : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := Real.sin_sq θ\n"
                f"  have hp : 0 ≤ t ^ {a} * (1 - Real.cos θ) ^ {b} := mul_nonneg (pow_nonneg ht.1 _) (pow_nonneg (by linarith) _)\n"
                f"  have e : ({lean_expr(R, 'Real.cos θ')}) ^ 2 + (Real.sin θ * ({lean_expr(S, 'Real.cos θ')})) ^ 2 - 1\n"
                f"      = t ^ {a} * (1 - Real.cos θ) ^ {b} * ({Gc}) := by\n"
                f"    rw [mul_pow, hs]; ring\n"
                f"  nlinarith [mul_nonneg hp (neg_nonneg.mpr hG)]\n")
        else:
            w = fila["testigo_no"]
            t0, c0 = Fr(w["t"]), Fr(w["c"])
            P[f"{E}_decide_{e}_no"] = (
                f"  refine ⟨{lean_num(t0)}, ⟨by norm_num, by norm_num⟩, ?_⟩\n  intro h\n"
                f"  rw [Esquema.vonNeumann_iff_sq] at h\n  have h0 := h (Real.arccos {lean_num(c0)})\n"
                f"  rw [{E}_re, {E}_im] at h0\n"
                f"  have hc : Real.cos (Real.arccos {lean_num(c0)}) = {lean_num(c0)} := Real.cos_arccos (by norm_num) (by norm_num)\n"
                f"  have hs : Real.sin (Real.arccos {lean_num(c0)}) ^ 2 = 1 - {lean_num(c0)} ^ 2 := by rw [Real.sin_sq, hc]\n"
                f"  rw [mul_pow, hs, hc] at h0\n  norm_num at h0\n")
    return "\n".join(out_aux), P


def main():
    A2d, A9a, js, inf, salida = sys.argv[1:6]
    A2d = Path(A2d).read_text(); A9a = Path(A9a).read_text()
    spec = json.loads(Path(js).read_text())["propuestas"]
    filas = {f["id"]: f for f in json.loads(Path(inf).read_text())["filas"] if "id" in f}
    txt = A9a[A9a.index("/-! ## A9"):A9a.rindex(C_)]
    for p in spec:
        i = p["id"]; E = f"esq_{i}"
        st = {int(k): sp.sympify(v.replace("^", "**"), locals={"t": t}) for k, v in p["stencil"].items()}
        R = sum(v * sp.chebyshevt(abs(k), c) for k, v in st.items())
        S = sum((1 if k > 0 else -1) * v * sp.chebyshevu(abs(k) - 1, c) for k, v in st.items() if k != 0)
        F = sp.expand(R ** 2 + (1 - c ** 2) * S ** 2 - 1)
        a, b, G = factorizar(F)
        aux, P = pruebas_stencil(p, filas[i], sp.expand(R), sp.expand(S), F, a, b, G)
        mdef = re.search(rf"(noncomputable def {E} [^\n]*\n(?:  [^\n]*\n)*\n)", txt)
        txt = txt[:mdef.end()] + aux + "\n" + txt[mdef.end():]
        cuerpos = {f"{E}_momentos": f"  refine ⟨?_, ?_, ?_⟩ <;> simp [{E}, Esquema.momento, Finset.sum_insert] <;> ring\n"}
        for d in p["decidir"]:
            e = d["etiqueta"]
            cuerpos[f"{E}_region_decide_{e}"] = f"  exact ⟨({d['testigo']['t']} : ℝ), by norm_num⟩\n"
        cuerpos.update(P)
        for n_, cuerpo in cuerpos.items():
            pat = re.compile(rf"(theorem {n_} [^\n]*\n(?:    [^\n]*\n)*)  sorry\n")
            txt, k = pat.subn(lambda mm: mm.group(1) + cuerpo, txt, count=1)
            assert k == 1, n_
    out = A2d[: -len(C_)] + "\n" + txt + C_
    Path(salida).write_text(out)
    print("sorry que quedan (los lados falsos):", len(re.findall(r"^  sorry$", out, re.M)))


if __name__ == "__main__":
    main()
