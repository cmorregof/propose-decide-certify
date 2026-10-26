"""frontera_esquemas: carga de tareas del diseño A y tipos con parámetros (sin Lean ni API)."""
import hashlib, shutil
from pathlib import Path
import pytest
from unirl import frontera_esquemas as E

RAIZ_REAL = Path(E.F.PROMETEO)


def _raiz(tmp_path, alterar=None):
    """Una copia mínima de prometeo_lean con A2 y A3 «aprobados» en un SHA256SUMS de prueba."""
    if not (RAIZ_REAL / "Esquemas" / "propuestos" / "A3_Corpus.lean").exists():
        pytest.skip("no está prometeo_lean con la propuesta A3")
    r = tmp_path / "pl"
    (r / "aprobados" / "Esquemas").mkdir(parents=True)
    (r / "Esquemas").mkdir()
    shutil.copytree(RAIZ_REAL / "herramientas", r / "herramientas")
    sumas = []
    for x in ("A2_Plantilla", "A3_Corpus"):
        t = (RAIZ_REAL / "Esquemas" / "propuestos" / f"{x}.lean").read_text(encoding="utf-8")
        (r / "aprobados" / "Esquemas" / f"{x}.lean").write_text(t, encoding="utf-8")
        sumas.append(f"{hashlib.sha256(t.encode()).hexdigest()}  aprobados/Esquemas/{x}.lean")
        shutil.copy(RAIZ_REAL / "Esquemas" / f"{x}.lean", r / "Esquemas" / f"{x}.lean")
    (r / "aprobados" / "SHA256SUMS_esquemas_prueba").write_text("\n".join(sumas) + "\n")
    if alterar:
        alterar(r)
    return r


def test_tipo_con_parametros():
    e = "/-- d -/\ntheorem esq_x_vonNeumann (r : ℝ) (h : 0 ≤ r ∧ r ≤ 1 / 2) : (esq_x r).vonNeumann"
    assert E._tipo_aprobado(e, "esq_x_vonNeumann") == "∀ (r : ℝ) (h : 0 ≤ r ∧ r ≤ 1 / 2), (esq_x r).vonNeumann"
    assert E._tipo_aprobado("theorem t : True", "t") == "True"


def test_carga_una_tarea(tmp_path):
    t = E.cargar_tarea("esq_upwind_vonNeumann_iff", raiz=_raiz(tmp_path))
    assert t["alternativas"][0]["nombre"] == "esq_upwind_vonNeumann_iff"
    assert "noncomputable def esq_upwind" in t["prefijo"]
    assert "esq_upwind_re" not in t["prefijo"] and "esq_lax_friedrichs" not in t["prefijo"]
    assert "sorry" not in E.F._sin_comentarios(t["prefijo"])


def test_rechaza_tanda_alterada(tmp_path):
    def alt(r):
        p = r / "aprobados" / "Esquemas" / "A3_Corpus.lean"
        p.write_text(p.read_text().replace("nu ≤ 1)", "nu ≤ 2)", 1))
    with pytest.raises(ValueError, match="SHA-256"):
        E.cargar_tarea("esq_upwind_vonNeumann_iff", raiz=_raiz(tmp_path, alt))


def test_rechaza_plantilla_demostrada_que_no_corresponde(tmp_path):
    def alt(r):
        p = r / "Esquemas" / "A2_Plantilla.lean"
        p.write_text(p.read_text().replace("‖E.simbolo θ‖ ≤ 1", "‖E.simbolo θ‖ ≤ 2", 1))
    with pytest.raises(ValueError, match="no corresponde"):
        E.cargar_tarea("esq_upwind_vonNeumann_iff", raiz=_raiz(tmp_path, alt))


def test_solo_teoremas_del_corpus(tmp_path):
    with pytest.raises(ValueError, match="solo se admiten"):
        E.cargar_tarea("laxWendroff_vonNeumann_iff", raiz=_raiz(tmp_path))


# ---------------------------------------------------------------- claude -p (25 oct 2026), con un `claude` falso

FALSO = r'''#!/usr/bin/env python3
import json, os, sys
args = sys.argv[1:]
sis = open(args[args.index("--system-prompt-file") + 1]).read()
entrada = sys.stdin.read()
json.dump({"argv": args, "cwd": os.getcwd(), "ls": os.listdir("."), "clave": "ANTHROPIC_API_KEY" in os.environ,
           "sis": sis, "user": entrada}, open(os.environ["REGISTRO_FALSO"], "w"))
if "FALLA" in entrada:
    print(json.dumps({"type": "result", "is_error": True, "result": "usage limit reached"})); sys.exit(1)
print(json.dumps({"type": "result", "subtype": "success", "is_error": False, "result": "4", "num_turns": 1,
                  "total_cost_usd": 0.01, "usage": {"input_tokens": 10, "cache_read_input_tokens": 5,
                  "cache_creation_input_tokens": 0, "output_tokens": 3}}))
'''


def _falso(tmp_path, monkeypatch):
    b = tmp_path / "claude"
    b.write_text(FALSO)
    b.chmod(0o755)
    monkeypatch.setenv("UNIRL_CLAUDE_BIN", str(b))
    monkeypatch.setenv("REGISTRO_FALSO", str(tmp_path / "reg.json"))
    monkeypatch.setenv("ANTHROPIC_API_KEY", "no-debe-pasar")
    return tmp_path / "reg.json"


def test_cli_sin_clave_sin_herramientas(tmp_path, monkeypatch):
    import json
    reg = _falso(tmp_path, monkeypatch)
    p = E.ProveedorClaudeCLI("claude-opus-5-5", "high")
    r = p.respuesta("SISTEMA", "USUARIO")
    assert p.texto(r) == "4" and r.usage.input_tokens == 10 and r.usage.cache_read_input_tokens == 5
    v = json.loads(reg.read_text())
    assert v["clave"] is False                                   # no se cobra a la API
    assert v["sis"] == "SISTEMA" and v["user"] == "USUARIO"
    assert v["ls"] == []                                         # carpeta vacía: ningún CLAUDE.md
    a = v["argv"]
    assert a[a.index("--tools") + 1] == "" and "--safe-mode" in a and "--no-session-persistence" in a
    assert a[a.index("--model") + 1] == "claude-opus-5-5"


def test_cli_error_sube(tmp_path, monkeypatch):
    _falso(tmp_path, monkeypatch)
    from unirl.loop import ProviderFatal
    with pytest.raises(ProviderFatal, match="usage limit"):
        E.ProveedorClaudeCLI("claude-opus-5-5").respuesta("s", "FALLA")


def test_cli_contabiliza(tmp_path, monkeypatch):
    _falso(tmp_path, monkeypatch)
    monkeypatch.setattr(E.F, "LIBRO_FRONTERA", tmp_path / "gasto.json")
    prov = E.hacer_proveedor_cli("claude-opus-5-5", "prueba", 5.0, "high")
    assert prov.complete("s", "u") == "4"
    import json
    g = json.loads((tmp_path / "gasto.json").read_text())
    assert g["llamadas"][0]["salida"] == 3 and g["total_usd"] > 0


def test_carga_decidir(tmp_path, monkeypatch):
    """Tarea de decidir (25 oct): dos alternativas, sí y no; el docstring del esquema no delata la respuesta."""
    if not (RAIZ_REAL / "Esquemas" / "propuestos" / "A5_Decidir.lean").exists():
        pytest.skip("no está la propuesta A5")
    r = tmp_path / "pl"
    (r / "aprobados" / "Esquemas").mkdir(parents=True)
    (r / "Esquemas").mkdir()
    shutil.copytree(RAIZ_REAL / "herramientas", r / "herramientas")
    sumas = []
    for x, src in (("A2_Plantilla", "propuestos/A2_Plantilla"), ("A5_Decidir", "propuestos/A5_Decidir")):
        t = (RAIZ_REAL / "Esquemas" / f"{src}.lean").read_text(encoding="utf-8")
        (r / "aprobados" / "Esquemas" / f"{x}.lean").write_text(t, encoding="utf-8")
        sumas.append(f"{hashlib.sha256(t.encode()).hexdigest()}  aprobados/Esquemas/{x}.lean")
    shutil.copy(RAIZ_REAL / "Esquemas" / "A2_Plantilla.lean", r / "Esquemas" / "A2_Plantilla.lean")
    (r / "aprobados" / "SHA256SUMS_esquemas_prueba").write_text("\n".join(sumas) + "\n")
    monkeypatch.setenv("UNIRL_TANDA_ESQUEMAS", "A5_Decidir")
    t = E.cargar_tarea("esq_downwind_decide_a", raiz=r)
    assert [a["nombre"] for a in t["alternativas"]] == ["esq_downwind_decide_a_si", "esq_downwind_decide_a_no"]
    assert "control" not in t["prefijo"].split("noncomputable def esq_downwind")[0][-300:].lower()
    tipo_no = E._tipo_aprobado(t["alternativas"][1]["enunciado"], "esq_downwind_decide_a_no")
    assert tipo_no.startswith("∃ nu : ℝ") and "¬" in tipo_no


def test_proponente_con_claude_falso(tmp_path, monkeypatch):
    """El proponente del lazo (25 oct): extrae el JSON, lo valida con el generador y registra; sin API."""
    from unirl import proponer_esquema as P
    if not (RAIZ_REAL / "herramientas" / "generar_esquemas.py").exists():
        pytest.skip("no está prometeo_lean")
    b = tmp_path / "claude"
    resp = ('Propongo upwind. <<<{"id": "upwind", "descripcion": "x", "parametros": ["nu"], '
            '"stencil": {"-1": "nu", "0": "1 - nu"}, "momentos": ["1", "-nu", "nu"], '
            '"estable_sii": "0 ≤ nu ∧ nu ≤ 1", "testigos": {"estable_sii": {"nu": "1/2"}}}>>>')
    b.write_text("#!/usr/bin/env python3\nimport json,sys\nsys.stdin.read()\n"
                 f"print(json.dumps({{'is_error': False, 'result': {resp!r}, 'num_turns': 1, "
                 "'usage': {'input_tokens': 5, 'output_tokens': 5}}))\n")
    b.chmod(0o755)
    monkeypatch.setenv("UNIRL_CLAUDE_BIN", str(b))
    monkeypatch.setattr(P.F, "BASE", tmp_path)
    assert P.main(["--cli", "--muestras", "2"]) == 0
    reg = sorted((tmp_path / "runs" / "unirl" / "esquemas_cli" / "propuestas").glob("*/propuesta_1.json"))[0]
    import json
    d = json.loads(reg.read_text())
    assert d["propuesta"]["id"] == "upwind" and d["problemas"] == []
    mala = dict(d["propuesta"], momentos=["1", "nu", "nu"])
    assert any("consistencia" in x for x in P.validar(mala))


def test_cli_sesion_vencida_aborta(tmp_path, monkeypatch):
    """25 oct: con la sesión OAuth vencida, claude -p falla; debe abortar la corrida (ProviderFatal), no seguir."""
    from unirl.loop import ProviderFatal
    b = tmp_path / "claude"
    b.write_text("#!/usr/bin/env python3\nimport json,sys\nsys.stdin.read()\nprint(json.dumps({'is_error': True, "
                 "'result': 'Failed to authenticate: OAuth session expired and could not be refreshed'}))\nsys.exit(1)\n")
    b.chmod(0o755)
    monkeypatch.setenv("UNIRL_CLAUDE_BIN", str(b))
    with pytest.raises(ProviderFatal):
        E.ProveedorClaudeCLI("claude-opus-5-5").respuesta("s", "u")


def test_hecha(tmp_path, monkeypatch):
    import json
    monkeypatch.setattr(E.F, "BASE", tmp_path)
    c = tmp_path / "runs" / "unirl" / "esquemas_cli" / "corridas" / "esq_x_vonNeumann_iff"
    (c / "20261025-115232-claude-opus-5-5-CC").mkdir(parents=True)
    (c / "20261025-115232-claude-opus-5-5-CC" / "meta.json").write_text(json.dumps(
        {"motivo_fin": "abortado: x", "resultados": []}))
    assert E.hecha("esq_x_vonNeumann_iff", "CC", True, 2) == 1
    (c / "20261025-120000-claude-opus-5-5-CC").mkdir()
    (c / "20261025-120000-claude-opus-5-5-CC" / "meta.json").write_text(json.dumps(
        {"motivo_fin": "completo", "resultados": [{"resuelto": False}, {"resuelto": False}]}))
    assert E.hecha("esq_x_vonNeumann_iff", "CC", True, 2) == 0
    assert E.hecha("esq_x_vonNeumann_iff", "SC", True, 2) == 1
    assert E.hecha("esq_x_vonNeumann_iff", "CC", True, 2, "claude-haiku-5-5") == 1   # otro modelo: no está hecha


def test_cuaderno_por_esquema(monkeypatch):
    """25 oct: el cuaderno de CC es uno por esquema; tareas del mismo esquema lo comparten, las de otro no."""
    monkeypatch.setenv("UNIRL_TANDA_ESQUEMAS", "A5_Decidir")
    a = E.carpeta_cuaderno("esq_upwind_decide_a", False)
    assert a == E.carpeta_cuaderno("esq_upwind_decide_b", False)
    assert a != E.carpeta_cuaderno("esq_ftcs_calor_decide_a", False)
    assert a.name == "esq_upwind" and a.parent.name == "A5_Decidir" and a.parent.parent.name == "cuadernos_por_esquema"
    assert E.carpeta_cuaderno("esq_ftcs_conv_dif_vonNeumann_iff", False).name == "esq_ftcs_conv_dif"


def test_cuaderno_por_modelo(monkeypatch):
    """25 oct: los cuadernos de otro modelo no se mezclan con los de Opus."""
    monkeypatch.setenv("UNIRL_TANDA_ESQUEMAS", "A5_Decidir")
    monkeypatch.setattr(E, "_MODELO", "claude-opus-5-5")
    opus = E.carpeta_cuaderno("esq_upwind_decide_a", False)
    monkeypatch.setattr(E, "_MODELO", "claude-haiku-5-5")
    haiku = E.carpeta_cuaderno("esq_upwind_decide_a", False)
    assert opus != haiku and "claude-haiku-5-5" in haiku.parts and "claude-opus-5-5" not in opus.parts


def test_axiomas_con_corte_de_linea():
    """25 oct: Lean parte a 120 columnas la salida de #print axioms con nombres largos; el juez debe leerla igual."""
    n = "PrometeoLean.Esquemas.esq_c1_lax_wendroff_1_decide_corrida_si"
    sal = ("x\nUNIRL_MARCA_abc\n'" + n + "' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n")
    # el fallo de frontera.py (si otro módulo de prueba ya importó el arnés v4, el «original» capturado puede ser el
    # tolerante; por eso solo se exige cuando es de verdad el de frontera.py)
    if E._axiomas_tras_marca_original.__module__ == "unirl.frontera":
        assert E._axiomas_tras_marca_original(sal, "abc", n) is None
    assert E.axiomas_tras_marca(sal, "abc", n) == ["propext", "Classical.choice", "Quot.sound"]
    corto = "x\nUNIRL_MARCA_abc\n'A.b' depends on axioms: [propext]\n"
    assert E.axiomas_tras_marca(corto, "abc", "A.b") == ["propext"]


# ---------------------------------------------------------------- endurecimiento (25 oct): implementaciones del arnés v4

@pytest.fixture
def endurecido(monkeypatch):
    for nombre in ("Lake", "filtrar_declaraciones", "filtrar_prueba", "_perfil", "axiomas_tras_marca"):
        monkeypatch.setattr(E.F, nombre, getattr(E.F, nombre))   # se restauran al terminar el test
    E.instalar_endurecimiento()
    return E.F


@pytest.mark.parametrize("cod", ['#eval IO.«FS».readFile "Esquemas/A5_Decidir.lean"',
                                 '#eval IO.getEnv "ANTHROPIC_API_KEY"',
                                 '#eval (IO.Process.output {cmd := "cat", args := #[".env"]})',
                                 '#eval IO.«getEnv» "X"'])
def test_eval_que_lee_entorno_o_archivos_se_rechaza(endurecido, cod):
    out = endurecido.evaluar_evals({"prefijo": "", "cierre": ""}, None, "", [cod])
    assert out[0]["salida"].startswith("RECHAZADO")                  # no llega a compilar (lake = None)


def test_guillemets_en_nombres_con_punto(endurecido):
    """`\\bIO\\.FS\\b` de frontera.py no ve `IO.«FS»`; con el endurecimiento se rechaza también fuera de EVAL."""
    motivo, _ = endurecido.filtrar_declaraciones('def aux_x (p : System.FilePath) : IO String := IO.«FS».readFile p', ("aux_",), False)
    assert motivo and "prohibido" in motivo
    assert endurecido.filtrar_prueba("exact (IO.«Process».spawn {cmd := x})")


def test_guillemets_en_lemas_y_pruebas(endurecido):
    motivo, _ = endurecido.filtrar_declaraciones("theorem cu_x : True := by «sorry»", ("cu_",), True)
    assert motivo and "sorry" in motivo
    assert endurecido.filtrar_prueba("exact Lean.«ofReduceBool» _ _ rfl")
    assert endurecido.filtrar_prueba("simp") is None
    assert endurecido.filtrar_declaraciones("theorem cu_y : (1 : ℕ) + 1 = 2 := by norm_num", ("cu_",), True)[0] is None


def test_lean_sin_secretos_y_sin_leer_respuestas(endurecido, monkeypatch, tmp_path):
    from unirl import corpus_confirmatorio as CC
    assert endurecido.Lake is CC.LakeSinSecretos
    assert endurecido.axiomas_tras_marca is CC.axiomas_tras_marca
    monkeypatch.setenv("ANTHROPIC_API_KEY", "x"); monkeypatch.setenv("OTRA_COSA", "y")
    env = CC.entorno_sin_secretos()
    assert "ANTHROPIC_API_KEY" not in env and env.get("OTRA_COSA") == "y"
    raiz = tmp_path / "prometeo_lean"
    p = endurecido._perfil(tmp_path / "w", raiz)
    assert p.startswith(E._perfil_original(tmp_path / "w", raiz))      # lo de frontera.py intacto
    for c in (raiz.resolve() / "Esquemas", raiz.resolve() / "PrometeoLean", E.F.BASE.resolve()):
        assert f'(subpath "{c}")' in p
    assert "(deny file-read-data (require-any" in p and p.count("(") == p.count(")")
