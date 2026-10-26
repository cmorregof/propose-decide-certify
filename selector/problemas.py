"""Benchmark del selector de modelos (diseño A, bloque 3; 26 oct 2026).

    python3 problemas.py <semilla> <carpeta de salida>

Cinco moldes lineales de coeficientes constantes en la recta periódica [0, L), con la convención
    u_t + v·u_x = α·u_xx + λ·u :
  calor                     v = 0, λ = 0, α > 0
  adveccion                 α = 0, λ = 0, v ≠ 0
  adveccion_difusion        λ = 0, v ≠ 0, α > 0
  reaccion_difusion         v = 0, α > 0, λ < 0
  adveccion_reaccion_difusion  v ≠ 0, α > 0, λ < 0
Seis instancias por molde (30 problemas). Cada problema sale en tres modalidades:
  texto   un enunciado físico sin ecuación (plantillas de redacción escritas a mano; ningún LLM genera el texto);
  datos   la solución exacta (espectral, periódica) en una malla de 161 × 101, con ruido gaussiano del 1 %;
          al modelo se le da una tabla submuestreada de 41 × 21 valores;
  imagen  el mapa de calor de u(x, t), con ejes y barra de color.
La respuesta verdadera (molde y coeficientes) va en `verdad.json`, aparte; los archivos de cada modalidad no la contienen.
"""
import json, random, sys
from pathlib import Path
import numpy as np

L, NX, T, NT = 4.0, 161, 2.0, 101
MOLDES = ["calor", "adveccion", "adveccion_difusion", "reaccion_difusion", "adveccion_reaccion_difusion"]

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
}


def sortear(molde, rng):
    a = round(rng.uniform(0.003, 0.03), 4)
    v = round(rng.choice([-1, 1]) * rng.uniform(0.4, 1.2), 3)
    lam = -round(rng.uniform(0.2, 1.0), 3)
    return {"calor": {"v": 0.0, "alpha": a, "lambda": 0.0},
            "adveccion": {"v": v, "alpha": 0.0, "lambda": 0.0},
            "adveccion_difusion": {"v": v, "alpha": a, "lambda": 0.0},
            "reaccion_difusion": {"v": 0.0, "alpha": a, "lambda": lam},
            "adveccion_reaccion_difusion": {"v": v, "alpha": a, "lambda": lam}}[molde]


def solucion(cf, x0, ancho):
    x = np.linspace(0, L, NX, endpoint=False)
    t = np.linspace(0, T, NT)
    u0 = sum(np.exp(-((x - x0 + s * L) ** 2) / (2 * ancho ** 2)) for s in (-1, 0, 1))
    k = 2 * np.pi * np.fft.fftfreq(NX, d=L / NX)
    U0 = np.fft.fft(u0)
    simb = cf["lambda"] - 1j * cf["v"] * k - cf["alpha"] * k ** 2
    U = np.array([np.real(np.fft.ifft(U0 * np.exp(tt * simb))) for tt in t])      # (NT, NX)
    return x, t, U


def main():
    semilla, salida = int(sys.argv[1]), Path(sys.argv[2])
    rng = random.Random(semilla); nrng = np.random.default_rng(semilla)
    salida.mkdir(parents=True, exist_ok=False)
    verdad = []
    orden = [m for m in MOLDES for _ in range(6)]
    rng.shuffle(orden)
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    for n, molde in enumerate(orden, 1):
        pid = f"p{n:02d}"
        cf = sortear(molde, rng)
        x0, ancho = round(rng.uniform(1.0, 3.0), 2), round(rng.uniform(0.15, 0.35), 2)
        x, t, U = solucion(cf, x0, ancho)
        Un = U + 0.01 * np.max(np.abs(U)) * nrng.standard_normal(U.shape)
        d = salida / pid
        d.mkdir()
        # texto
        var = rng.randrange(len(TEXTOS[molde]))
        txt = TEXTOS[molde][var].format(L=L, T=T, alpha=cf["alpha"], vabs=abs(cf["v"]),
                                        dir="positive" if cf["v"] >= 0 else "negative", lamabs=abs(cf["lambda"]))
        (d / "texto.txt").write_text(txt + "\n", encoding="utf-8")
        # datos: malla completa (para la línea base sin LLM) y tabla submuestreada (para el modelo)
        np.savez_compressed(d / "datos.npz", x=x, t=t, u=Un)
        xs, ts = x[::4], t[::5]
        sub = Un[::5, ::4]
        filas = ["t \\ x," + ",".join(f"{v:.3g}" for v in xs)]
        filas += [f"{tt:.3g}," + ",".join(f"{v:.3g}" for v in fila) for tt, fila in zip(ts, sub)]
        (d / "tabla.csv").write_text("\n".join(filas) + "\n", encoding="utf-8")
        # imagen
        fig, ax = plt.subplots(figsize=(7, 4.2), dpi=110)
        im = ax.imshow(Un, origin="lower", aspect="auto", extent=[0, L, 0, T], cmap="viridis")
        ax.set_xlabel("x (m)"); ax.set_ylabel("t (s)"); ax.set_title("u(x, t)")
        fig.colorbar(im, ax=ax)
        fig.tight_layout(); fig.savefig(d / "imagen.png"); plt.close(fig)
        verdad.append({"id": pid, "molde": molde, "coeficientes": cf, "x0": x0, "ancho": ancho, "variante_texto": var})
        print(pid, molde, cf)
    (salida / "verdad.json").write_text(json.dumps({"semilla": semilla, "malla": {"L": L, "NX": NX, "T": T, "NT": NT},
                                                     "ruido": 0.01, "problemas": verdad}, indent=1), encoding="utf-8")


if __name__ == "__main__":
    main()
