"""25 oct 2026: la consistencia del proponente del lazo se compara por VALOR, no por texto.

Antes, `validar` pedía literalmente ["1", "-nu"] y descartó dos propuestas correctas de Haiku 5.5 que escribieron
M1 como «-1*nu» y «0 - nu». Sin red ni Lean: el generador solo arma texto."""
import os
from pathlib import Path

import pytest

from unirl import frontera as F
from unirl import proponer_esquema as PE

RAIZ = Path(os.environ.get("PROMETEO_LEAN", str(F.PROMETEO)))
_GEN = RAIZ / "herramientas" / "generar_esquemas.py"


@pytest.mark.parametrize("expr", ["-nu", "-1*nu", "0 - nu", "-(nu)", "nu*(-1)", "(nu - 2*nu)", "-2*nu/2"])
def test_menos_nu_por_valor(expr):
    assert PE.identicas(expr, lambda r, nu: -nu)


@pytest.mark.parametrize("expr", ["nu", "-nu + r", "-nu^2", "1 - nu", "-r"])
def test_no_es_menos_nu(expr):
    assert not PE.identicas(expr, lambda r, nu: -nu)


@pytest.mark.parametrize("expr", ["1", "2/2", "1.0", "1 + 0*nu", "(nu + 1) - nu"])
def test_uno_por_valor(expr):
    assert PE.identicas(expr, lambda r, nu: 1)


@pytest.mark.parametrize("expr", ["nu**1", "__import__('os')", "nu^r", "nu^(1/2)", "f(nu)", "nu.real"])
def test_fuera_de_la_gramatica(expr):
    with pytest.raises(Exception):
        PE.identicas(expr, lambda r, nu: -nu)


def _lw(momentos):
    return {"id": "lw", "descripcion": "Lax-Wendroff", "parametros": ["nu"],
            "stencil": {"-1": "nu*(1+nu)/2", "0": "1-nu^2", "1": "nu*(nu-1)/2"},
            "momentos": momentos, "estable_sii": "nu^2 ≤ 1", "testigos": {"estable_sii": {"nu": "1/2"}}}


@pytest.fixture
def con_generador(monkeypatch):
    if not _GEN.exists():
        pytest.skip(f"no está {_GEN}")
    monkeypatch.setattr(F, "PROMETEO", RAIZ)


@pytest.mark.parametrize("m1", ["-nu", "-1*nu", "0 - nu"])
def test_validar_acepta_las_de_haiku(con_generador, m1):
    assert PE.validar(_lw(["1", m1, "nu^2"])) == []


@pytest.mark.parametrize("mom", [["1", "nu", "nu^2"], ["2", "-nu", "nu^2"], ["1"], [], ["1", "nu**1", "nu^2"]])
def test_validar_sigue_rechazando(con_generador, mom):
    problemas = PE.validar(_lw(mom))
    assert any(p.startswith("consistencia:") for p in problemas)
