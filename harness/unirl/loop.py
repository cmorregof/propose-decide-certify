"""Bucle proponente–verificador (estructura de `steprl.evolve.run_evolution`, reducida a episodios).

Cada intento se registra como una línea JSONL en `<out>/attempts.jsonl` con: entorno, juez, modelo,
episodio, paso, propuesta, resultado, crédito parcial, recompensa, segundos del LLM y del juez.
"""

from __future__ import annotations

import json
import time
from dataclasses import asdict
from datetime import datetime
from pathlib import Path

from .env import ProofEnv, Observation


class Memory:
    """Memoria entre episodios del proponente (el modelo sigue congelado; lo que se acumula es contexto):

    * biblioteca de lemas que el agente demostró y cuya demostración verificó el kernel (se añaden solos a cada intento);
    * resumen de cada episodio anterior: mejor intento, su anotación y lo que quedó abierto.

    Con `path`, se guarda en disco y se recupera en la siguiente corrida (transferencia entre corridas)."""

    # Encabezado de la biblioteca. «v1» es el de la corrida de Luna del 23 sep 2026 (20260923-215521); se conserva para
    # que otra corrida con el mismo mensaje sea comparable. «v2» corrige la atribución: el agente demuestra, Isabelle verifica.
    LIBRARY_HEADER = {
        "v1": "Lemas que Isabelle YA DEMOSTRÓ. Se añaden solos a cada intento: úsalos por su nombre y no los "
              "repitas en LEMMAS (si repites un nombre, gana tu versión nueva):",
        "v2": "Lemas que TÚ demostraste en intentos anteriores y cuya demostración Isabelle YA VERIFICÓ. Se añaden "
              "solos a cada intento: úsalos por su nombre y no los repitas en LEMMAS (si repites un nombre, gana tu "
              "versión nueva):",
    }

    def __init__(self, path: Path | None = None, max_chars: int = 9000, wording: str = "v2"):
        if wording not in self.LIBRARY_HEADER:
            raise ValueError(f"memory_prompt ∈ {sorted(self.LIBRARY_HEADER)}")
        self.path, self.max_chars, self.wording = path, max_chars, wording
        self.library: dict[str, str] = {}
        self.episodes: list[dict] = []
        if path and Path(path).exists():
            d = json.loads(Path(path).read_text(encoding="utf-8"))
            self.library, self.episodes = d.get("library", {}), d.get("episodes", [])

    def save(self) -> None:
        if self.path:
            Path(self.path).parent.mkdir(parents=True, exist_ok=True)
            Path(self.path).write_text(json.dumps({"library": self.library, "episodes": self.episodes}, ensure_ascii=False, indent=1), encoding="utf-8")

    def library_text(self) -> str:
        return "\n\n".join(self.library.values())

    def add_lemmas(self, verified: list[dict]) -> None:
        for lem in verified or []:
            self.library.setdefault(lem["name"], lem["text"])  # la primera versión demostrada se conserva

    @staticmethod
    def _judge_kind(attempts: list[dict]) -> str:
        """'pep' (hay τ), 'theorem' (juez de teorema de Isabelle) o 'vc' (juez de programa de Isabelle, y el resto)."""
        raws = [a.get("raw") or {} for a in attempts]
        if any("tau" in r for r in raws):
            return "pep"
        if any(r.get("kind") == "theorem" for r in raws):
            return "theorem"
        return "vc"

    def end_episode(self, ep: int, attempts: list[dict]) -> None:
        kind = self._judge_kind(attempts)

        def score(a):
            raw = a.get("raw") or {}
            if kind == "pep":  # el mejor peor caso: crédito parcial = 1 + log(τ_ref/τ) acotado
                return (a["accepted"], a.get("partial_credit") or 0.0)
            if kind == "theorem":  # más lemas verificados
                return (a["accepted"], len(raw.get("verified_lemmas") or []))
            # juez de programa: exactamente el criterio de la corrida de Luna del 23 sep (no cambiarlo: comparabilidad)
            return (a["accepted"], (raw.get("n_closed_auto") or 0) / (raw.get("n_vcs") or 1) if raw.get("n_vcs") else -1)
        best = max(attempts, key=score)
        braw = best.get("raw") or {}
        entry = {"episode": ep, "accepted": best["accepted"], "best_label": best["outcome_label"],
                 "best_closed": braw.get("n_closed_auto"), "best_vcs": braw.get("n_vcs"),
                 "best_proposal": {k: v for k, v in (best.get("proposal") or {}).items() if k != "lemmas"}
                 if isinstance(best.get("proposal"), dict) else best.get("proposal"),
                 "last_feedback": attempts[-1].get("feedback", "")[:1200]}
        if kind == "pep" and braw.get("tau") is not None:
            entry["best_extra"] = f"τ = {braw['tau']:.7f} frente a τ_ref = {braw['tau_ref']:.7f}; h = {[round(x, 4) for x in braw.get('h') or []]}"
        if kind == "theorem":
            entry["best_extra"] = f"{len(braw.get('verified_lemmas') or [])} lemas verificados"
        self.episodes.append(entry)
        self.save()

    def render(self) -> str:
        if not self.library and not self.episodes:
            return ""
        parts = ["MEMORIA DE EPISODIOS ANTERIORES (mismo objetivo y mismo juez; viene de tus intentos anteriores):"]
        if self.library:
            parts.append(self.LIBRARY_HEADER[self.wording])
            parts.append(self.library_text())
        for e in self.episodes[-3:]:
            res = f"{e['best_label']}" + (f", {e['best_closed']}/{e['best_vcs']} VCs cerradas" if e.get("best_vcs") else "")
            res += f", {e['best_extra']}" if e.get("best_extra") else ""
            parts.append(f"- Episodio {e['episode']}: mejor intento {res}; anotación: {json.dumps(e['best_proposal'], ensure_ascii=False)[:900]}")
            parts.append(f"  Retroalimentación del último intento: {e['last_feedback'][:900]}")
        text = "\n".join(parts)
        return text if len(text) <= self.max_chars else text[: self.max_chars] + "\n[memoria truncada]"

SYSTEM_PROMPT = """Eres un matemático que trabaja con un verificador independiente. Propones un objeto de demostración
(una cadena de lemas, un invariante de bucle o un programa) y solo el verificador decide. No afirmes que tu
propuesta es correcta: enúnciala en el formato pedido. Usa la retroalimentación de los intentos anteriores."""


def build_prompt(env: ProofEnv, obs: Observation, memory: "Memory | None" = None) -> str:
    parts = [env.verifier.describe(obs.target)]
    if memory is not None and memory.render():
        parts.append("\n" + memory.render())
    if obs.history:
        parts.append(f"\nINTENTOS ANTERIORES ({len(obs.history)} de {env.budget}):")
        for i, h in enumerate(obs.history, 1):
            parts.append(f"--- intento {i}: propuesta = {json.dumps(h['proposal'], ensure_ascii=False)[:1500]}\n    resultado: {h['feedback']}")
        parts.append("\nPropón ahora una versión corregida.")
    return "\n".join(parts)


# Errores del proveedor que no se arreglan reintentando: sin créditos, clave inválida o sin permiso. Ante ellos la
# corrida se detiene: seguir solo llenaría el registro de PROVIDER_ERROR (lo que pasó la noche del 23 al 24 sep).
FATAL_PROVIDER = ("insufficient_quota", "credit_balance_exhausted", "no credits", "invalid_api_key", "incorrect api key",
                  "permission_denied", "billing", "credit balance is too low")  # el último: Anthropic sin créditos (400)


class Rechazo(RuntimeError):
    """El modelo rechazó la petición (stop_reason «refusal» de Anthropic). Ya se pagó y se registró; no se reintenta.
    En reflexion, el intento queda como REFUSAL: fallido, pero el episodio sigue siendo válido (no es PROVIDER_ERROR)."""

    def __init__(self, categoria: str | None = None):
        self.categoria = categoria
        super().__init__("el modelo rechazó la petición" + (f" ({categoria})" if categoria else ""))


class ProviderFatal(RuntimeError):
    pass


# Política de reintentos (26 sep 2026, pedido de Carlos): 5 reintentos con espera exponencial de 2 s a 60 s ante
# errores de conexión, límite de tasa (429) y errores del servidor (5xx). Un error de autenticación o de créditos es
# fatal de inmediato: aborta la corrida (ABORTADA.txt), sin reintentar.
ESPERAS_REINTENTO = (2, 5, 11, 26, 60)
TRANSITORIO = ("connection", "timeout", "timed out", "límite de tasa", "rate limit", "ratelimit", "overloaded", "server error",
               "service unavailable", "bad gateway", "gateway timeout", "429", "500", "502", "503", "504", "529")
AUTENTICACION = ("authentication", "invalid_api_key", "incorrect api key", "401", "permission_denied", "403")


def clasificar_error(e: BaseException) -> str:
    """'fatal' (créditos o autenticación), 'transitorio' (red, 429, 5xx) u 'otro'. Mira el código de estado si la
    excepción lo trae (SDK de OpenAI) y, si no, el texto. Lo fatal se decide antes que lo transitorio: la falta de
    créditos de OpenAI llega como un 429 con `insufficient_quota`."""
    msg = str(e).lower()
    if any(k in msg for k in FATAL_PROVIDER) or any(k in msg for k in AUTENTICACION):
        return "fatal"
    status = getattr(e, "status_code", None)
    if status is not None:
        if status in (401, 403):
            return "fatal"
        if status == 429 or status >= 500:
            return "transitorio"
    nombre = type(e).__name__.lower()
    if "connection" in nombre or "timeout" in nombre or "ratelimit" in nombre or any(k in msg for k in TRANSITORIO):
        return "transitorio"
    return "otro"


def complete_with_retries(provider, system: str, user: str, retries: int = len(ESPERAS_REINTENTO), verbose: bool = True,
                          dormir=time.sleep, propagar_rechazo: bool = False) -> str | None:
    """El texto de la respuesta, o None si falló. Un Rechazo no se reintenta: con `propagar_rechazo` sube a quien
    llama (reflexion lo registra como REFUSAL); sin él, cuenta como una falla más (None)."""
    for attempt in range(retries + 1):
        try:
            return provider.complete(system, user)
        except ProviderFatal:
            raise  # sin créditos, sin clave o tope de gasto: se aborta la corrida, no se reintenta
        except Rechazo as e:
            if propagar_rechazo:
                raise
            if verbose:
                print(f"  proveedor: {e}")
            return None
        except Exception as e:
            msg = str(e)
            clase = clasificar_error(e)
            if clase == "fatal":
                if verbose:
                    print(f"  proveedor: error fatal (créditos o autenticación): {msg[:120]}")
                raise ProviderFatal(msg[:300]) from e
            if clase == "transitorio" and attempt < retries:
                wait = ESPERAS_REINTENTO[min(attempt, len(ESPERAS_REINTENTO) - 1)]
                if verbose:
                    print(f"  proveedor: {msg[:80]} → reintento {attempt + 1}/{retries} en {wait} s")
                dormir(wait)
                continue
            if verbose:
                print(f"  proveedor falló: {e}")
            return None
    return None


def run_episodes(env: ProofEnv, provider, n_episodes: int, out_dir: Path, meta: dict, verbose: bool = True, extra: dict | None = None,
                 memory: "Memory | None" = None) -> list[dict]:
    out_dir.mkdir(parents=True, exist_ok=True)
    log_path = out_dir / "attempts.jsonl"
    (out_dir / "meta.json").write_text(json.dumps({**meta, **(extra or {}), "started": datetime.now().isoformat(timespec="seconds"), "target": env.verifier.target()},
                                                  ensure_ascii=False, indent=1), encoding="utf-8")
    episodes = []
    with log_path.open("a", encoding="utf-8") as log:
        for ep in range(1, n_episodes + 1):
            obs = env.reset()
            done, accepted, steps = False, False, 0
            ep_attempts: list[dict] = []
            while not done:
                prompt = build_prompt(env, obs, memory)
                t = time.perf_counter()
                text = complete_with_retries(provider, SYSTEM_PROMPT, prompt, verbose=verbose)
                llm_s = time.perf_counter() - t
                if text is None:
                    proposal, label = None, "PROVIDER_ERROR"
                    rec = {"outcome_label": label, "accepted": False, "partial_credit": 0.0, "reward": 0.0, "cost_s": 0.0, "raw": {}}
                    obs.step += 1  # el fallo consume presupuesto y queda en el historial que ve el modelo
                    obs.history.append({"proposal": None, "outcome_label": label, "feedback": "PROVIDER_ERROR: la llamada al modelo falló; este intento no se juzgó."})
                    done = obs.step >= env.budget
                else:
                    proposal = env.verifier.parse(text)
                    lib = {"lemmas_library": memory.library_text()} if memory is not None and memory.library else None
                    obs, reward, done, out = env.step(proposal, extra=lib)
                    if memory is not None:
                        memory.add_lemmas(out.raw.get("verified_lemmas"))
                        memory.save()
                    rec = {"outcome_label": out.outcome_label, "accepted": out.accepted, "partial_credit": out.partial_credit,
                           "reward": reward, "cost_s": out.cost_s, "raw": out.raw}
                    accepted = out.accepted
                steps += 1
                line = {**meta, "episode": ep, "step": steps, "proposal": proposal, "response": (text or "")[:4000], "llm_s": round(llm_s, 2), **rec,
                        "time": datetime.now().isoformat(timespec="seconds"),
                        "memory_library": sorted(memory.library) if memory is not None else None}
                ep_attempts.append({**line, "feedback": obs.history[-1]["feedback"] if obs.history else ""})
                log.write(json.dumps(line, ensure_ascii=False, default=str) + "\n")
                log.flush()
                if verbose:
                    print(f"[ep {ep} paso {steps}] {rec['outcome_label']}  (llm {llm_s:.1f} s, juez {rec['cost_s']:.1f} s)")
            episodes.append({"episode": ep, "steps": steps, "accepted": accepted})
            if memory is not None and ep_attempts:
                memory.end_episode(ep, ep_attempts)
    return episodes
