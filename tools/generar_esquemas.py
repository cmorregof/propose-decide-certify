"""Generador de enunciados del diseño A (24 oct 2026).

Una propuesta de esquema (del agente o de una persona) es un dato: parámetros, stencil, momentos y regiones
declaradas. Este programa la convierte, siempre de la misma manera, en enunciados Lean sobre la plantilla A2.
Así los enunciados de una propuesta no los escribe nadie a mano: salen de la plantilla aprobada (SHA-256) y de
este generador (SHA-256), y el juez solo tiene que comprobar pruebas.

  python3 herramientas/generar_esquemas.py <plantilla A2.lean> <propuestas.json> <salida.lean>

Para cada propuesta se emite, según lo que declare:
  esq_<id>                       la definición del esquema (stencil con if-else sobre el soporte)
  esq_<id>_momentos              momentos 0, 1 y 2 (consistencia: Σ a_k u(x+kh) = Σ_m M_m h^m/m! u^(m))
  esq_<id>_vonNeumann_iff        von Neumann ⇔ región exacta            (campo "estable_sii")
  esq_<id>_vonNeumann            región ⇒ von Neumann                    (campo "estable_si", si no hay "estable_sii")
  esq_<id>_positivo              región ⇒ esquema positivo (⇒ máximo)   (campo "positivo_si")
  esq_<id>_inestable             condición ⇒ ¬ von Neumann (control)     (campo "inestable_si")
  esq_<id>_region_<…>            ∃ parámetros, región: la región no es vacía (campo "testigos", obligatorio)
  esq_<id>_decide_<e>_si / _no   decidir (25 oct): «∀ parámetros, R → von Neumann» frente a «∃ parámetros, R ∧ ¬ von
                                 Neumann» (campo "decidir": lista de {"etiqueta", "region", "testigo"}). Con R no vacía,
                                 exactamente una de las dos es cierta; quien prueba tiene que decidir cuál.
  esq_<id>_decide_<e>_si / _no   decidir exacta (25 oct): «∀ parámetros, von Neumann ↔ R» frente a «∃ parámetros,
                                 ¬ (von Neumann ↔ R)» (campo "decidir_exacta"; mismo formato que "decidir"). El «no»
                                 puede pedir un punto de R inestable (R demasiado grande) o un punto estable fuera
                                 de R (R demasiado pequeña), y este último exige probar von Neumann en ese punto.
  esq_<id>_decide_<e>_si / _no   instancia: von Neumann, o su negación, en valores concretos de los parámetros, p. ej.
                                 los de una corrida del framework (campo "instancias": lista de {"etiqueta",
                                 "valores"}; solo números). También es un par de decidir: el kernel dice cuál.
  esq_<id>_decide_<e>_si / _no   consistencia con un molde (26 oct, tanda A8; campo "consistente": lista de
                                 {"etiqueta", "molde", "orden_tiempo": 1|2, "n", "sustitucion": {parámetro: expresión en los
                                 coeficientes físicos y dt, dx}}): «∀ físicos dt dx, dx ≠ 0 → E(…).ConsistenteK (molde …) dt dx n»
                                 frente a su negación. Requiere la sección A8 (Molde, Consistente1/2) en la plantilla.
Las expresiones solo pueden usar los parámetros declarados, números y + - * / ^ ( ) y, en las regiones,
∧ ∨ ≤ < = ≠ ¬. Cualquier otra cosa se rechaza: el generador no deja pasar texto Lean arbitrario.
"""
import json, re, sys
from pathlib import Path

IDENT = re.compile(r"^[a-z][a-z0-9_]*$")
# Nombres que la plantilla usa en los enunciados generados (`fun k => …`, `(h : región)`) y palabras clave de Lean:
# un parámetro con uno de estos nombres sería capturado y el enunciado elaboraría con otro significado
# (p. ej. un parámetro `k` dentro de `fun k => if k = -1 then k …` pasa a ser el desplazamiento, con coerción ℤ → ℝ).
RESERVADOS = {"k", "h", "fun", "if", "then", "else", "by", "at", "from", "have", "show", "let", "in", "match",
              "with", "do", "end", "where", "open", "theorem", "lemma", "def", "abbrev", "example", "instance",
              "structure", "class", "namespace", "section", "variable", "universe", "import", "deriving",
              "mutual", "calc", "suffices", "obtain", "sorry", "admit", "true", "false",
              # nombres de la plantilla (revisión adversarial del 24 oct, m4)
              "a", "paso", "pasor", "simbolo", "momento", "vonneumann", "positivo", "esquema", "taylor"}
ARIT = re.compile(r"^[0-9a-zA-Z_ +\-*/^().]*$")
PROP = re.compile(r"^[0-9a-zA-Z_ +\-*/^().∧∨≤<=≠¬]*$")


# Catálogo de moldes de la sección A8 y sus coeficientes físicos, en el orden en que los toma cada `molde_<nombre>`.
CATALOGO = {"calor": ["alpha"], "adveccion": ["v"], "adveccion_difusion": ["v", "alpha"],
            "reaccion_difusion": ["lam", "alpha"], "adveccion_reaccion_difusion": ["v", "lam", "alpha"]}
# Orden espacial de cada molde (el `orden` de `molde_<nombre>`). Revisión Opus de A8: con n < orden la afirmación no ve
# el término más alto del molde (casi vacía), y con orden en el tiempo 2 hace falta n ≥ 2·orden para que (P²)ₘ entre
# entero; el generador rechaza ambos casos.
ORDEN_MOLDE = {"calor": 2, "adveccion": 1, "adveccion_difusion": 2, "reaccion_difusion": 2,
               "adveccion_reaccion_difusion": 2}


def _expr(e: str, params: list[str], prop: bool) -> str:
    e = str(e).strip()
    if not (PROP if prop else ARIT).fullmatch(e) or not e:
        raise ValueError(f"expresión no admitida: {e!r}")
    if "**" in e:
        raise ValueError(f"la potencia se escribe con ^, no con **: {e!r}")
    if "--" in e or "/-" in e or "-/" in e:          # comentarios de Lean (revisión del 24 oct, M1)
        raise ValueError(f"expresión con marcas de comentario de Lean: {e!r}")
    for w in re.findall(r"[A-Za-z_][A-Za-z0-9_]*", e):
        if w not in params:
            raise ValueError(f"identificador no declarado {w!r} en {e!r} (parámetros: {params})")
    if re.search(r"\^\s*[^0-9\s(]", e):
        raise ValueError(f"solo exponentes naturales literales: {e!r}")
    return e


def bloque(p: dict) -> str:
    i = p["id"]
    if not IDENT.fullmatch(i):
        raise ValueError(f"id no admitido: {i!r}")
    ps = p["parametros"]
    if not ps or any(not IDENT.fullmatch(x) for x in ps) or len(set(ps)) != len(ps):
        raise ValueError(f"parámetros no admitidos: {ps!r}")
    if reservados := sorted({x.lower() for x in ps} & RESERVADOS):
        raise ValueError(f"parámetros con nombres reservados por la plantilla o por Lean: {reservados}")
    S = {int(k): _expr(v, ps, False) for k, v in p["stencil"].items()}
    if not S:
        raise ValueError("stencil vacío")
    bind = " ".join(f"({x} : ℝ)" for x in ps)
    args = " ".join(ps)
    E = f"(esq_{i} {args})"
    desc = p.get("descripcion", "").replace("-/", "- /").replace("/-", "/ -")
    orig = p.get("origen", "sin origen declarado").replace("-/", "- /").replace("/-", "/ -")
    ks = sorted(S)
    soporte = ", ".join(str(k) for k in ks)
    ramas = "".join(f"if k = {k} then {S[k]} else " for k in ks)
    out = [f"/-- **{i}.** {desc} Origen: {orig}. -/",
           f"noncomputable def esq_{i} {bind} : Esquema where",
           f"  S := {{{soporte}}}",
           f"  a := fun k => {ramas}0", ""]
    if "momentos" in p:                              # opcional desde el 25 oct (las tandas de decidir no los repiten)
        m = [_expr(x, ps, False) for x in p["momentos"]]
        if len(m) != 3:
            raise ValueError("hacen falta exactamente los momentos 0, 1 y 2")
        out += [f"/-- Momentos 0, 1 y 2 de `esq_{i}`. -/",
                f"theorem esq_{i}_momentos {bind} :",
                f"    {E}.momento 0 = {m[0]} ∧ {E}.momento 1 = {m[1]} ∧ {E}.momento 2 = {m[2]} := by",
                "  sorry", ""]
    if p.get("estable_sii"):
        r = _expr(p["estable_sii"], ps, True)
        out += [f"/-- Región exacta de von Neumann de `esq_{i}`. -/",
                f"theorem esq_{i}_vonNeumann_iff {bind} : {E}.vonNeumann ↔ ({r}) := by", "  sorry", ""]
    elif p.get("estable_si"):
        r = _expr(p["estable_si"], ps, True)
        out += [f"/-- Una región suficiente de von Neumann de `esq_{i}`. -/",
                f"theorem esq_{i}_vonNeumann {bind} (h : {r}) : {E}.vonNeumann := by", "  sorry", ""]
    if p.get("positivo_si"):
        r = _expr(p["positivo_si"], ps, True)
        out += [f"/-- `esq_{i}` es positivo (y cumple el principio del máximo, A2.5) en esta región. -/",
                f"theorem esq_{i}_positivo {bind} (h : {r}) : {E}.Positivo := by", "  sorry", ""]
    if p.get("inestable_si"):
        r = _expr(p["inestable_si"], ps, True)
        out += [f"/-- **Control.** `esq_{i}` no cumple von Neumann si {r}. -/",
                f"theorem esq_{i}_inestable {bind} (h : {r}) : ¬ {E}.vonNeumann := by", "  sorry", ""]
    # No vacuidad (revisión del 24 oct, M2): toda región declarada trae un testigo, y se emite
    # `∃ parámetros, región`, que también hay que probar. Una región vacía haría vacuo el teorema
    # que la usa como hipótesis.
    testigos = p.get("testigos", {})
    cuant = " ".join(ps)
    for campo, sufijo in [("estable_sii", "estable"), ("estable_si", "estable_suf"), ("positivo_si", "positivo"),
                          ("inestable_si", "inestable")]:
        if not p.get(campo):
            continue
        w = testigos.get(campo)
        if not isinstance(w, dict) or set(w) != set(ps):
            raise ValueError(f"{i}: la región {campo} necesita un testigo con valores para {ps}")
        for v in w.values():
            _expr(v, [], False)                      # números, sin parámetros
        r = _expr(p[campo], ps, True)
        out += [f"/-- La región «{campo}» de `esq_{i}` no es vacía. -/",
                f"theorem esq_{i}_region_{sufijo} : ∃ {cuant} : ℝ, {r} := by", "  sorry", ""]
    vistos = set()
    for d in p.get("decidir", []):
        e = d.get("etiqueta", "")
        if not re.fullmatch(r"[a-z0-9]+", e) or e in vistos:
            raise ValueError(f"{i}: etiqueta de decidir no admitida o repetida: {e!r}")
        vistos.add(e)
        r = _expr(d["region"], ps, True)
        w = d.get("testigo")
        if not isinstance(w, dict) or set(w) != set(ps):
            raise ValueError(f"{i}/{e}: la región de decidir necesita un testigo con valores para {ps}")
        for v in w.values():
            _expr(v, [], False)
        out += [f"/-- **Decidir {i}/{e}, sí.** En toda la región, `esq_{i}` cumple von Neumann. -/",
                f"theorem esq_{i}_decide_{e}_si : ∀ {cuant} : ℝ, ({r}) → {E}.vonNeumann := by", "  sorry", "",
                f"/-- **Decidir {i}/{e}, no.** Hay un punto de la región donde `esq_{i}` no cumple von Neumann. -/",
                f"theorem esq_{i}_decide_{e}_no : ∃ {cuant} : ℝ, ({r}) ∧ ¬ {E}.vonNeumann := by", "  sorry", "",
                f"/-- La región de decidir {i}/{e} no es vacía. -/",
                f"theorem esq_{i}_region_decide_{e} : ∃ {cuant} : ℝ, {r} := by", "  sorry", ""]
    for d in p.get("decidir_exacta", []):            # 25 oct: ¿R es EXACTAMENTE la región de von Neumann?
        e = d.get("etiqueta", "")
        if not re.fullmatch(r"[a-z0-9]+", e) or e in vistos:
            raise ValueError(f"{i}: etiqueta de decidir_exacta no admitida o repetida: {e!r}")
        vistos.add(e)
        r = _expr(d["region"], ps, True)
        w = d.get("testigo")
        if not isinstance(w, dict) or set(w) != set(ps):
            raise ValueError(f"{i}/{e}: la región de decidir_exacta necesita un testigo con valores para {ps}")
        for v in w.values():
            _expr(v, [], False)
        out += [f"/-- **Decidir exacta {i}/{e}, sí.** `esq_{i}` cumple von Neumann exactamente en la región. -/",
                f"theorem esq_{i}_decide_{e}_si : ∀ {cuant} : ℝ, ({E}.vonNeumann ↔ ({r})) := by", "  sorry", "",
                f"/-- **Decidir exacta {i}/{e}, no.** Hay un punto donde von Neumann y la región no coinciden. -/",
                f"theorem esq_{i}_decide_{e}_no : ∃ {cuant} : ℝ, ¬ ({E}.vonNeumann ↔ ({r})) := by", "  sorry", "",
                f"/-- La región de decidir exacta {i}/{e} no es vacía. -/",
                f"theorem esq_{i}_region_decide_{e} : ∃ {cuant} : ℝ, {r} := by", "  sorry", ""]
    for d in p.get("consistente", []):              # 26 oct (A8): ¿el esquema es consistente con el molde hasta el orden n?
        e = d.get("etiqueta", "")
        if not re.fullmatch(r"[a-z0-9]+", e) or e in vistos:
            raise ValueError(f"{i}: etiqueta de consistente no admitida o repetida: {e!r}")
        vistos.add(e)
        molde = d.get("molde")
        if molde not in CATALOGO:
            raise ValueError(f"{i}/{e}: molde fuera del catálogo: {molde!r}")
        fis = CATALOGO[molde]
        o, n = d.get("orden_tiempo"), d.get("n")
        if o not in (1, 2) or not isinstance(n, int) or not 0 <= n <= 8:
            raise ValueError(f"{i}/{e}: orden_tiempo debe ser 1 o 2 y n un entero entre 0 y 8")
        if n < o * ORDEN_MOLDE[molde]:
            raise ValueError(f"{i}/{e}: con orden_tiempo {o} y el molde {molde} (orden {ORDEN_MOLDE[molde]}) "
                             f"hace falta n ≥ {o * ORDEN_MOLDE[molde]}")
        sus = d.get("sustitucion")
        if not isinstance(sus, dict) or set(sus) != set(ps):
            raise ValueError(f"{i}/{e}: la sustitución debe dar una expresión para cada parámetro {ps}")
        args_e = " ".join(f"({_expr(sus[x], fis + ['dt', 'dx'], False)})" for x in ps)
        cu = " ".join(fis + ["dt", "dx"])
        Pm = f"(molde_{molde} {' '.join(fis)})"
        C = f"(esq_{i} {args_e}).Consistente{o} {Pm} dt dx {n}"
        paso = "I + dt·P" if o == 1 else "I + dt·P + dt²/2·P²"
        out += [f"/-- **Decidir {i}/{e}, sí.** El paso de `esq_{i}` reproduce exactamente `{paso}` (P = molde "
                f"`{molde}`) sobre los polinomios de grado ≤ {n}: la identidad de momentos `Consistente{o}` vale "
                f"para todo m ≤ {n}. -/",
                f"theorem esq_{i}_decide_{e}_si : ∀ {cu} : ℝ, dx ≠ 0 → {C} := by", "  sorry", "",
                f"/-- **Decidir {i}/{e}, no.** La identidad de momentos `Consistente{o}` falla en algún m ≤ {n} para "
                f"algunos coeficientes y pasos (esto no dice que el esquema sea inconsistente en el sentido usual). -/",
                f"theorem esq_{i}_decide_{e}_no : ∃ {cu} : ℝ, dx ≠ 0 ∧ ¬ {C} := by", "  sorry", ""]
    for d in p.get("instancias", []):
        e = d.get("etiqueta", "")
        if not re.fullmatch(r"[a-z0-9]+", e) or e in vistos:
            raise ValueError(f"{i}: etiqueta de instancia no admitida o repetida: {e!r}")
        vistos.add(e)
        v = d.get("valores")
        if not isinstance(v, dict) or set(v) != set(ps):
            raise ValueError(f"{i}/{e}: la instancia necesita valores para {ps}")
        vals = " ".join(f"({_expr(v[x], [], False)})" for x in ps)
        orig_i = str(d.get("origen", "")).replace("-/", "- /").replace("/-", "/ -")
        out += [f"/-- **Instancia {i}/{e}, sí.** {orig_i} -/",
                f"theorem esq_{i}_decide_{e}_si : (esq_{i} {vals}).vonNeumann := by", "  sorry", "",
                f"/-- **Instancia {i}/{e}, no.** -/",
                f"theorem esq_{i}_decide_{e}_no : ¬ (esq_{i} {vals}).vonNeumann := by", "  sorry", ""]
    return "\n".join(out)


def testigo(p: dict, campo: str) -> list[str]:
    """Los valores del testigo de una región, en el orden de los parámetros (para escribir la prueba)."""
    return [p["testigos"][campo][x] for x in p["parametros"]]


def main() -> int:
    plantilla, propuestas, salida = sys.argv[1:4]
    t = Path(plantilla).read_text(encoding="utf-8")
    cierre = "\nend PrometeoLean.Esquemas\n"
    if not t.endswith(cierre):
        raise ValueError("la plantilla no termina en «end PrometeoLean.Esquemas»")
    data = json.loads(Path(propuestas).read_text(encoding="utf-8"))
    cab = data.get("cabecera", "Corpus de esquemas generado por herramientas/generar_esquemas.py.")
    cuerpo = "\n".join(bloque(p) for p in data["propuestas"])
    nota = (f"/-! ## {cab}\n\nEnunciados generados mecánicamente desde `{Path(propuestas).name}`; no se escriben a "
            f"mano. -/\n\n")
    Path(salida).write_text(t[: -len(cierre)] + "\n" + nota + cuerpo + cierre, encoding="utf-8")
    print(f"{salida}: {len(data['propuestas'])} esquemas")
    return 0


if __name__ == "__main__":
    sys.exit(main())
