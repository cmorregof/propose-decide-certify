"""A9: stencils aleatorios de cinco puntos con etiquetas exactas (26 oct 2026).

    python3 generar_aleatorios.py <semilla> <n_stencils> <salida.json> <informe.json>

Cada stencil:
  - soporte {-2,…,2}; a₋₂ y a₂ son polinomios pequeños en (r, ν) con coeficientes racionales sorteados; a₋₁, a₀, a₁
    salen de imponer M₀ = 1, M₁ = −ν, M₂ = 2r + ν² (consistente con u_t + c·u_x = α·u_xx, segundo orden en el tiempo);
  - los parámetros recorren una recta (r, ν) = t·(ρ, σ) (número de Péclet de malla fijo, Δt variable), así que la
    región estable que contiene a t = 0⁺ es un intervalo [0, t*];
  - UNA tarea de decidir por esquema, «∀ t ∈ [0, q], von Neumann», con q = u·t*: u ~ U[0,5; 0,97] (verdadera) o
    u ~ U[1,03; 1,5] (falsa). Verdaderas y falsas en igual número, por permutación (v2, 26 oct, tras la revisión de Opus:
    con dos tareas por esquema la verdadera era siempre la región menor).
Filtros (v2): se descarta el esquema si la inestabilidad nace en θ = π y los casi duplicados (|Δt*|/t* < 5 % y
|Δθ*| < 5°). Se probó además descartar las tareas falsas que un ángulo «redondo» refuta (θ = kπ/12 o cos θ = p/q con
q ≤ 6, para algún t ∈ (0, q]): con un margen de al menos 3 % sobre t* ninguna de 5 sobrevivió, así que no se filtra; se
registra en el informe y la línea base fuerte prueba esos ángulos. Refutar es barato; lo que mide la tanda es probar el «sí».

Etiquetas (aritmética exacta en ℚ, sin flotantes en la decisión):
  - «no»: un testigo racional (t₀, c₀) con t₀ ≤ q_fuera, c₀ ∈ [−1, 1] y |g|² − 1 > 0 exacto (c₀ = cos θ₀);
  - «sí»: G(t, c) ≤ 0 en [0, q_dentro] × [−1, 1] certificado por subdivisión con cotas de Bernstein exactas, donde
    |g|² − 1 = tᵃ (1 − c)ᵇ G(t, c).
Los flotantes solo se usan para localizar t* y escoger q; la etiqueta la decide el certificado exacto.
"""
import json, random, sys
from fractions import Fraction as Fr
from math import comb
import numpy as np
import sympy as sp

t, c = sp.symbols("t c", real=True)
r_, nu_ = sp.symbols("r nu", real=True)


def cheb_T(k):  # cos(kθ) en c = cos θ
    return sp.chebyshevt(k, c)


def cheb_U(k):  # sin((k+1)θ)/sin θ
    return sp.chebyshevu(k, c)


def sortear(rng):
    pick = lambda: sp.Rational(rng.randint(-3, 3), rng.choice([4, 8, 12]))
    am2 = pick() * r_ + pick() * nu_ + pick() * nu_ ** 2
    a2 = pick() * r_ + pick() * nu_ + pick() * nu_ ** 2
    am1, a0, a1 = sp.symbols("am1 a0 a1")
    sol = sp.solve([am2 + am1 + a0 + a1 + a2 - 1,
                    -2 * am2 - am1 + a1 + 2 * a2 + nu_,
                    4 * am2 + am1 + a1 + 4 * a2 - (2 * r_ + nu_ ** 2)], [am1, a0, a1], dict=True)[0]
    rho = sp.Rational(rng.randint(1, 4), 4)
    sig = sp.Rational(rng.choice([-1, 1]) * rng.randint(1, 4), 4)
    st = {-2: am2, -1: sol[am1], 0: sol[a0], 1: sol[a1], 2: a2}
    st_t = {k: sp.expand(v.subs({r_: rho * t, nu_: sig * t})) for k, v in st.items()}
    return st, st_t, rho, sig


def simbolo_poly(st_t):
    re = sum(v * cheb_T(abs(k)) for k, v in st_t.items())
    s = sum((1 if k > 0 else -1) * v * cheb_U(abs(k) - 1) for k, v in st_t.items() if k != 0)
    F = sp.expand(re ** 2 + (1 - c ** 2) * s ** 2 - 1)
    return F


def factorizar(F):
    """|g|² − 1 = tᵃ (1 − c)ᵇ G(t, c), con t ≥ 0 y 1 − c ≥ 0: el signo de F es el de G."""
    e, a, b = sp.expand(F), 0, 0
    while e != 0 and sp.expand(e.subs(t, 0)) == 0:
        e = sp.expand(sp.cancel(e / t)); a += 1
    while e != 0 and sp.expand(e.subs(c, 1)) == 0:
        e = sp.expand(sp.cancel(e / (1 - c))); b += 1
    return a, b, sp.Poly(e, t, c)


def max_c(Gf, tv, cs):
    return np.max(Gf(tv, cs))


def t_estrella(G, tmax=4.0):
    Gf = sp.lambdify((t, c), G.as_expr(), "numpy")
    cs = np.linspace(-1, 1, 4001)
    ts = np.linspace(0, tmax, 4001)[1:]
    vals = np.array([max_c(Gf, tv, cs) for tv in ts])
    if vals[0] > 1e-12:
        return None                                    # inestable para t pequeño
    malos = np.where(vals > 1e-12)[0]
    if len(malos) == 0:
        return None                                    # estable en todo [0, tmax]: degenerado
    lo, hi = ts[malos[0] - 1] if malos[0] > 0 else 0.0, ts[malos[0]]
    for _ in range(60):
        mid = (lo + hi) / 2
        if max_c(Gf, mid, cs) > 1e-14:
            hi = mid
        else:
            lo = mid
    return (lo + hi) / 2


# ---------------------------------------------------------------- Bernstein exacto en una caja [t0,t1]×[c0,c1]
def coef_monomios(P):
    d = {}
    for (i, j), v in P.terms():
        d[(i, j)] = Fr(int(sp.numer(v)), int(sp.denom(v)))
    return d


def a_caja(coefs, t0, t1, c0, c1):
    """Coeficientes del polinomio en variables u, w ∈ [0,1] con t = t0 + (t1−t0)u, c = c0 + (c1−c0)w."""
    out = {}
    dt, dc = t1 - t0, c1 - c0
    for (i, j), v in coefs.items():
        for p in range(i + 1):
            ct = comb(i, p) * t0 ** (i - p) * dt ** p
            for q in range(j + 1):
                cc = comb(j, q) * c0 ** (j - q) * dc ** q
                out[(p, q)] = out.get((p, q), Fr(0)) + v * ct * cc
    return out


def bernstein_max(coefs_u, n, m):
    """Máximo de los coeficientes de Bernstein de grado (n, m) del polinomio en [0,1]²."""
    best = None
    for I in range(n + 1):
        for J in range(m + 1):
            s = Fr(0)
            for (i, j), v in coefs_u.items():
                if i <= I and j <= J:
                    s += v * Fr(comb(I, i), comb(n, i)) * Fr(comb(J, j), comb(m, j))
            best = s if best is None or s > best else best
    return best


def certificar_no_positivo(P, q, profundidad=14):
    """¿G ≤ 0 en [0, q] × [−1, 1]? Devuelve (True, nº de cajas) si se certifica, (False, motivo) si no."""
    coefs = coef_monomios(P)
    n = max(i for i, _ in coefs) if coefs else 0
    m = max(j for _, j in coefs) if coefs else 0
    pila = [(Fr(0), Fr(q), Fr(-1), Fr(1), 0)]
    cajas = 0
    while pila:
        t0, t1, c0, c1, d = pila.pop()
        cajas += 1
        if cajas > 200000:
            return False, "demasiadas cajas"
        cu = a_caja(coefs, t0, t1, c0, c1)
        if bernstein_max(cu, n, m) <= 0:
            continue
        # si un vértice es > 0, no es cierto
        for tv in (t0, t1):
            for cv in (c0, c1):
                val = sum(v * tv ** i * cv ** j for (i, j), v in coefs.items())
                if val > 0:
                    return False, f"G({tv},{cv}) = {float(val):.3g} > 0"
        if d >= profundidad:
            return False, "profundidad agotada"
        tm, cm = (t0 + t1) / 2, (c0 + c1) / 2
        pila += [(t0, tm, c0, cm, d + 1), (tm, t1, c0, cm, d + 1), (t0, tm, cm, c1, d + 1), (tm, t1, cm, c1, d + 1)]
    return True, cajas


def racional_cerca(x, maxden=64):
    return Fr(x).limit_denominator(maxden)


def testigo_no(F, tstar, q):
    """Un (t₀, c₀) racional con t* < t₀ ≤ q y F(t₀, c₀) > 0 exacto."""
    Ff = sp.lambdify((t, c), F, "numpy")
    cs = np.linspace(-1, 1, 4001)
    for frac in (0.5, 0.75, 1.0):
        tv = tstar + frac * (float(q) - tstar)
        cv = cs[np.argmax(Ff(tv, cs))]
        for den in (16, 64, 256, 1024):
            t0, c0 = Fr(tv).limit_denominator(den), Fr(cv).limit_denominator(den)
            if not (0 <= t0 <= q and -1 <= c0 <= 1):
                continue
            val = F.subs({t: sp.Rational(t0.numerator, t0.denominator), c: sp.Rational(c0.numerator, c0.denominator)})
            if val > 0:
                return t0, c0, Fr(int(sp.numer(val)), int(sp.denom(val)))
    return None


def texto(e):
    s = sp.sstr(sp.expand(e)).replace("**", "^")
    return s if s else "0"


ANGULOS_C = sorted({round(float(np.cos(k * np.pi / 12)), 15) for k in range(1, 13)} |
                   {p / q for q in range(1, 7) for p in range(-q, q + 1)})


def theta_estrella(G, ts):
    Gf = sp.lambdify((t, c), G.as_expr(), "numpy")
    cs = np.linspace(-1, 1, 20001)
    return float(np.degrees(np.arccos(cs[np.argmax(Gf(ts * 1.0005, cs))])))


def refuta_angulo_redondo(F, q):
    """¿Algún c = cos θ «redondo» da |g|² − 1 > 0 para algún t ∈ (0, q]? (malla fina en t; positivo con margen)"""
    Ff = sp.lambdify((t, c), F, "numpy")
    ts = np.linspace(0, float(q), 2001)[1:]
    for cv in ANGULOS_C:
        if np.max(Ff(ts, cv)) > 1e-12:
            return True
    return False


def testigo_no_v2(F, tstar, q):
    """Testigo racional (t₀, c₀), c₀ con denominador > 6, t* < t₀ ≤ q, F(t₀, c₀) > 0 exacto."""
    Ff = sp.lambdify((t, c), F, "numpy")
    cs = np.linspace(-1, 1, 40001)
    for frac in (1.0, 0.75, 0.5):
        tv = tstar + frac * (float(q) - tstar)
        cv = cs[np.argmax(Ff(tv, cs))]
        for den in (64, 256, 1024, 4096):
            t0, c0 = Fr(tv).limit_denominator(den), Fr(cv).limit_denominator(den)
            if not (0 <= t0 <= q and -1 <= c0 <= 1) or c0.denominator <= 6:
                continue
            val = F.subs({t: sp.Rational(t0.numerator, t0.denominator), c: sp.Rational(c0.numerator, c0.denominator)})
            if val > 0:
                return t0, c0, Fr(int(sp.numer(val)), int(sp.denom(val)))
    return None


def main():
    import platform
    semilla, n_obj, salida, informe = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
    assert n_obj % 2 == 0
    rng = random.Random(semilla)
    verdades = [True] * (n_obj // 2) + [False] * (n_obj // 2)
    rng.shuffle(verdades)
    propuestas, filas, intentos, aceptados = [], [], 0, []
    while len(propuestas) < n_obj and intentos < 5000:
        intentos += 1
        st, st_t, rho, sig = sortear(rng)
        F = simbolo_poly(st_t)
        a, b, G = factorizar(F)
        ts = t_estrella(G)
        if ts is None or not (0.05 < ts < 3.0):
            filas.append({"intento": intentos, "descartado": "sin intervalo [0, t*] útil"}); continue
        Gf = sp.lambdify((t, c), G.as_expr(), "numpy")
        cs = np.linspace(-1, 1, 4001)
        c_crit = cs[np.argmax(Gf(ts * 1.02, cs))]
        if c_crit < -0.95:
            filas.append({"intento": intentos, "descartado": "inestabilidad en θ = π"}); continue
        th = theta_estrella(G, ts)
        if any(abs(ts - x["t"]) / x["t"] < 0.05 and abs(th - x["th"]) < 5 for x in aceptados):
            filas.append({"intento": intentos, "descartado": "casi duplicado"}); continue
        verdadera = verdades[len(propuestas)]
        u = rng.uniform(0.5, 0.97) if verdadera else rng.uniform(1.03, 1.5)
        q = racional_cerca(ts * u)
        if verdadera:
            if not q < Fr(ts):
                filas.append({"intento": intentos, "descartado": "q no queda dentro"}); continue
            ok, info = certificar_no_positivo(G, q)
            if not ok:
                filas.append({"intento": intentos, "descartado": f"«sí» no certificado: {info}"}); continue
            w = None
            redondo = None
        else:
            if not q > Fr(ts):
                filas.append({"intento": intentos, "descartado": "q no queda fuera"}); continue
            redondo = refuta_angulo_redondo(F, q)      # se registra (para la línea base fuerte), no se filtra:
            w = testigo_no_v2(F, ts, q)                  # con este margen siempre hay un ángulo «redondo» que refuta
            if w is None:
                filas.append({"intento": intentos, "descartado": "sin testigo racional del «no»"}); continue
            info = None
        i = f"aleat_{len(propuestas) + 1:02d}"
        reg = f"0 ≤ t ∧ t ≤ {q.numerator}/{q.denominator}" if q.denominator != 1 else f"0 ≤ t ∧ t ≤ {q.numerator}"
        propuestas.append({
            "id": i,
            "descripcion": (f"Esquema explícito de cinco puntos generado al azar (semilla {semilla}), consistente con "
                            f"u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número "
                            f"de Péclet de malla fijo: r = ({rho})·t, ν = ({sig})·t."),
            "origen": f"A9 v2, stencils aleatorios, semilla {semilla}",
            "parametros": ["t"],
            "stencil": {str(k): texto(v) for k, v in sorted(st_t.items())},
            "momentos": ["1", texto(-sig * t), texto(2 * rho * t + sig ** 2 * t ** 2)],
            "decidir": [{"etiqueta": "a", "region": reg,
                         "testigo": {"t": f"{(q / 2).numerator}/{(q / 2).denominator}"}}],
        })
        aceptados.append({"t": ts, "th": th})
        filas.append({"intento": intentos, "id": i, "rho": str(rho), "sigma": str(sig), "t_estrella_aprox": ts,
                      "theta_estrella_grados": th, "u": u, "q": str(q), "verdadera": "si" if verdadera else "no",
                      "factor": {"t": a, "1-c": b}, "cajas_bernstein": info, "angulo_redondo_refuta": redondo,
                      "testigo_no": ({"t": str(w[0]), "c": str(w[1]), "F": str(w[2])} if w else None),
                      "stencil_r_nu": {str(k): str(sp.expand(v)) for k, v in st.items()}})
        print(i, f"t*≈{ts:.4f} θ*≈{th:.1f}°", "verdadera" if verdadera else "falsa", "q", q, flush=True)
    json.dump({"cabecera": f"A9 v2. Stencils aleatorios de cinco puntos (semilla {semilla}): {len(propuestas)} esquemas, "
                           f"una tarea de decidir cada uno",
               "propuestas": propuestas}, open(salida, "w"), ensure_ascii=False, indent=1)
    json.dump({"semilla": semilla, "intentos": intentos, "aceptados": len(propuestas),
               "versiones": {"python": platform.python_version(), "sympy": sp.__version__, "numpy": np.__version__},
               "angulos_redondos_c": ANGULOS_C, "filas": filas}, open(informe, "w"), ensure_ascii=False, indent=1)
    print(f"{len(propuestas)} stencils en {intentos} intentos")


if __name__ == "__main__":
    main()
