"""Benchmark del selector de modelos, versión 2 (más difícil; 26 oct 2026, opción A aprobada por Carlos).

    python3 problemas_v2.py <semilla> <carpeta de salida>

Cambios frente a la v1 (problemas_v1.py), porque una regresión de 40 líneas restringida al catálogo acertaba 27–29/30
sobre la tabla de la v1:
  - ruido gaussiano del 5 % (antes 1 %);
  - tabla más rala: 21 × 11 valores (antes 41 × 21);
  - 6 problemas FUERA del catálogo (3 de Burgers viscoso y 3 de Fisher–KPP), cuya respuesta correcta es «ninguno».
Los 30 del catálogo siguen la misma convención u_t + v·u_x = α·u_xx + λ·u y los mismos rangos de la v1.
Los no lineales se integran con un método pseudoespectral (RK4, paso fino, con desaliasado 2/3) en la misma malla.
La respuesta verdadera (molde, coeficientes, modelo real) va en `verdad.json`, aparte.
"""
import json, random, sys
from pathlib import Path
import numpy as np

L, NX, T, NT = 4.0, 161, 2.0, 101
RUIDO = 0.05
SUB_X, SUB_T = 8, 10
MOLDES = ["calor", "adveccion", "adveccion_difusion", "reaccion_difusion", "adveccion_reaccion_difusion"]
FUERA = ["burgers", "fisher_kpp"]

TEXTOS = {
    "calor": [
        "A thin metal ring of circumference {L:g} m is insulated from its surroundings. At t = 0 a short section is heated. "
        "The metal has thermal diffusivity {alpha} m^2/s; nothing moves and there are no heat sources or losses. "
        "We record the temperature excess u(x, t) around the ring for {T:g} s.",
        "A closed circular tube of length {L:g} m is filled with still water. A small amount of dye is injected at one point. "
        "The dye spreads only by molecular diffusion with coefficient {alpha} m^2/s and does not react or decay. "
        "We measure the dye concentration u(x, t) for {T:g} s.",
    ],
    "adveccion": [
        "A pulse of tracer is released in a circular channel of length {L:g} m in which water circulates at a uniform speed "
        "of {vabs} m/s in the {dir} x direction. Over the {T:g} s of observation diffusion is negligible and the tracer "
        "is conserved. We record its concentration u(x, t).",
        "A localized disturbance is carried around a periodic conveyor loop of length {L:g} m that moves at a constant "
        "{vabs} m/s in the {dir} x direction. The quantity is conserved and does not spread. We record u(x, t) for {T:g} s.",
    ],
    "adveccion_difusion": [
        "A pollutant is released in a circular channel of length {L:g} m. The water moves at a uniform {vabs} m/s in the "
        "{dir} x direction, and turbulent mixing spreads the pollutant with an effective diffusivity of {alpha} m^2/s. "
        "The pollutant does not decay. We record its concentration u(x, t) for {T:g} s.",
        "Warm fluid circulates around a closed pipe loop of length {L:g} m at {vabs} m/s in the {dir} x direction, and heat "
        "diffuses along the pipe with diffusivity {alpha} m^2/s; the pipe is insulated. We record the temperature excess "
        "u(x, t) for {T:g} s.",
    ],
    "reaccion_difusion": [
        "A colony of bacteria lives in a still, closed circular tube of length {L:g} m. The bacteria move randomly with an "
        "effective diffusivity of {alpha} m^2/s and die at a constant per-capita rate of {lamabs} per second; there is no "
        "growth and no flow. We record the population density u(x, t) for {T:g} s.",
        "A short-lived chemical species is injected into a still ring-shaped reactor of length {L:g} m. It diffuses with "
        "coefficient {alpha} m^2/s and is consumed by a first-order reaction with rate constant {lamabs} 1/s. We record its "
        "concentration u(x, t) for {T:g} s.",
    ],
    "adveccion_reaccion_difusion": [
        "A radioactive tracer is released in a circular channel of length {L:g} m where the water flows at {vabs} m/s in "
        "the {dir} x direction. Turbulent mixing spreads it with diffusivity {alpha} m^2/s, and it decays with rate "
        "constant {lamabs} 1/s. We record its concentration u(x, t) for {T:g} s.",
        "A reactive solute is carried around a closed loop of length {L:g} m by a uniform flow of {vabs} m/s in the {dir} x "
        "direction; it diffuses with coefficient {alpha} m^2/s and is removed by a first-order reaction with rate "
        "{lamabs} 1/s. We record its concentration u(x, t) for {T:g} s.",
    ],
    # Fuera del catálogo: el texto describe la física sin la ecuación, como en los demás.
    "burgers": [
        "On a circular road of length {L:g} m, a disturbance in a one-dimensional flow is transported at a speed equal to "
        "its own local amplitude (in m/s), so taller parts move faster and the front steepens; a weak viscosity of "
        "{nu} m^2/s smooths it. There is no background flow and nothing is created or destroyed. We record u(x, t) for {T:g} s.",
        "A pressure pulse travels in a gas-filled ring tube of length {L:g} m. The local propagation speed equals the local "
        "value of the disturbance itself (in m/s), so the pulse steepens into a front, and viscous effects with coefficient "
        "{nu} m^2/s smooth it. We record the disturbance u(x, t) for {T:g} s.",
    ],
    "fisher_kpp": [
        "An invasive plant species spreads along a closed circular strip of length {L:g} m. Seeds disperse with an "
        "effective diffusivity of {alpha} m^2/s and the population grows logistically: per-capita growth rate {r} per "
        "second at low density, saturating at a carrying capacity normalised to 1. We record the density u(x, t) for {T:g} s.",
        "A population of bacteria in a still ring-shaped tube of length {L:g} m moves randomly with diffusivity {alpha} m^2/s "
        "and reproduces with per-capita rate {r} per second when sparse; crowding limits it to a maximum density "
        "normalised to 1. We record the density u(x, t) for {T:g} s.",
    ],
}


def sortear(molde, rng):
    a = round(rng.uniform(0.003, 0.03), 4)
    v = round(rng.choice([-1, 1]) * rng.uniform(0.4, 1.2), 3)
    lam = -round(rng.uniform(0.2, 1.0), 3)
    if molde == "burgers":
        return {"nu": round(rng.uniform(0.02, 0.05), 3), "amplitud": round(rng.uniform(0.6, 1.0), 2)}
    if molde == "fisher_kpp":
        return {"alpha": a, "r": round(rng.uniform(0.8, 1.6), 2), "amplitud": round(rng.uniform(0.15, 0.35), 2)}
    return {"calor": {"v": 0.0, "alpha": a, "lambda": 0.0},
            "adveccion": {"v": v, "alpha": 0.0, "lambda": 0.0},
            "adveccion_difusion": {"v": v, "alpha": a, "lambda": 0.0},
            "reaccion_difusion": {"v": 0.0, "alpha": a, "lambda": lam},
            "adveccion_reaccion_difusion": {"v": v, "alpha": a, "lambda": lam}}[molde]


def malla():
    return np.linspace(0, L, NX, endpoint=False), np.linspace(0, T, NT), 2 * np.pi * np.fft.fftfreq(NX, d=L / NX)


def inicial(x, x0, ancho):
    return sum(np.exp(-((x - x0 + s * L) ** 2) / (2 * ancho ** 2)) for s in (-1, 0, 1))


def lineal(cf, x0, ancho):
    x, t, k = malla()
    U0 = np.fft.fft(inicial(x, x0, ancho))
    simb = cf["lambda"] - 1j * cf["v"] * k - cf["alpha"] * k ** 2
    return x, t, np.array([np.real(np.fft.ifft(U0 * np.exp(tt * simb))) for tt in t])


def no_lineal(molde, cf, x0, ancho, pasos_por_muestra=200):
    """Pseudoespectral con RK4: Burgers u_t + u u_x = ν u_xx; Fisher–KPP u_t = α u_xx + r u (1 − u)."""
    x, t, k = malla()
    corte = np.abs(k) <= (2 / 3) * np.abs(k).max()
    u = cf["amplitud"] * inicial(x, x0, ancho)

    def f(u):
        uh = np.fft.fft(u)
        if molde == "burgers":
            ux = np.real(np.fft.ifft(1j * k * uh * corte))
            return np.real(np.fft.ifft(-cf["nu"] * k ** 2 * uh)) - np.real(np.fft.ifft(np.fft.fft(u * ux) * corte))
        return np.real(np.fft.ifft(-cf["alpha"] * k ** 2 * uh)) + cf["r"] * u * (1 - u)

    dt = (t[1] - t[0]) / pasos_por_muestra
    U = [u.copy()]
    for _ in range(NT - 1):
        for _ in range(pasos_por_muestra):
            k1 = f(u); k2 = f(u + dt / 2 * k1); k3 = f(u + dt / 2 * k2); k4 = f(u + dt * k3)
            u = u + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
        U.append(u.copy())
    U = np.array(U)
    if not np.all(np.isfinite(U)):
        raise RuntimeError(f"{molde}: la integración no es finita")
    return x, t, U


def main():
    semilla, salida = int(sys.argv[1]), Path(sys.argv[2])
    rng = random.Random(semilla); nrng = np.random.default_rng(semilla)
    salida.mkdir(parents=True, exist_ok=False)
    orden = [m for m in MOLDES for _ in range(6)] + [m for m in FUERA for _ in range(3)]
    rng.shuffle(orden)
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    verdad = []
    for n, molde in enumerate(orden, 1):
        pid = f"p{n:02d}"
        cf = sortear(molde, rng)
        x0, ancho = round(rng.uniform(1.0, 3.0), 2), round(rng.uniform(0.15, 0.35), 2)
        x, t, U = lineal(cf, x0, ancho) if molde in MOLDES else no_lineal(molde, cf, x0, ancho)
        Un = U + RUIDO * np.max(np.abs(U)) * nrng.standard_normal(U.shape)
        d = salida / pid
        d.mkdir()
        var = rng.randrange(len(TEXTOS[molde]))
        txt = TEXTOS[molde][var].format(L=L, T=T, alpha=cf.get("alpha"), vabs=abs(cf.get("v", 0)),
                                        dir="positive" if cf.get("v", 0) >= 0 else "negative",
                                        lamabs=abs(cf.get("lambda", 0)), nu=cf.get("nu"), r=cf.get("r"))
        (d / "texto.txt").write_text(txt + "\n", encoding="utf-8")
        np.savez_compressed(d / "datos.npz", x=x, t=t, u=Un)
        xs, ts, sub = x[::SUB_X], t[::SUB_T], Un[::SUB_T, ::SUB_X]
        filas = ["t \\ x," + ",".join(f"{v:.3g}" for v in xs)]
        filas += [f"{tt:.3g}," + ",".join(f"{v:.3g}" for v in fila) for tt, fila in zip(ts, sub)]
        (d / "tabla.csv").write_text("\n".join(filas) + "\n", encoding="utf-8")
        fig, ax = plt.subplots(figsize=(7, 4.2), dpi=110)
        im = ax.imshow(Un, origin="lower", aspect="auto", extent=[0, L, 0, T], cmap="viridis")
        ax.set_xlabel("x (m)"); ax.set_ylabel("t (s)"); ax.set_title("u(x, t)")
        fig.colorbar(im, ax=ax)
        fig.tight_layout(); fig.savefig(d / "imagen.png"); plt.close(fig)
        en_cat = molde in MOLDES
        verdad.append({"id": pid, "molde": molde if en_cat else "ninguno", "modelo_real": molde,
                       "coeficientes": cf if en_cat else {"v": 0.0, "alpha": 0.0, "lambda": 0.0},
                       "parametros_reales": cf, "x0": x0, "ancho": ancho, "variante_texto": var})
        print(pid, molde, cf, flush=True)
    (salida / "verdad.json").write_text(json.dumps({"semilla": semilla, "version": 2, "malla": {"L": L, "NX": NX, "T": T,
                                                     "NT": NT}, "tabla": [NX // SUB_X + 1, (NT - 1) // SUB_T + 1],
                                                     "ruido": RUIDO, "problemas": verdad}, indent=1), encoding="utf-8")


if __name__ == "__main__":
    main()
