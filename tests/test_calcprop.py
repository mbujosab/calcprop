# Copyright (C) 2020-2026  Andrés Bujosa, Marcos Bujosa
# GNU General Public License v3 or later — see <https://www.gnu.org/licenses/>
"""Pruebas de calcprop.  Ejecutar con:  python -m pytest"""

import pytest

import calcprop
from calcprop import (Proposicion, v, alguno, unoDe, noDerivable, atomos, subformulas,
                      tabla_verdad, explica,
                      span, extension, refuta, test)

test.__test__ = False   # que pytest no confunda calcprop.test con una prueba

A, B, C, D = v('A'), v('B'), v('C'), v('D')


# ── test: consecuencia lógica ──────────────────────────────────────────

def test_modus_ponens():
    assert test(B, [A, A >> B])
    assert not test(B, [])


def test_tautologias_y_contradicciones():
    assert test(A | -A)
    assert not test(A & -A)
    assert test(-(A & -A))


def test_transitividad_y_equivalencia():
    assert test(A >> C, [A >> B, B >> C])
    assert test(A >> B, [A ** B])
    assert test(B >> A, [A ** B])
    assert not test(A ** B, [A >> B])


def test_unoDe_y_alguno():
    assert test(unoDe(A, B, C), [A, -B, -C])
    assert not test(unoDe(A, B, C), [A, B])
    assert test(-B, [unoDe(A, B, C), A])
    assert test(alguno(A, B, C), [B])
    assert not test(alguno(A, B, C), [])
    assert test(A, [alguno(A)])


def test_booleanos_como_formula_y_como_premisa():
    assert test(True, []) is True
    assert test(False, []) is False
    assert test(A, [True]) is False
    assert test(A, [False]) is True
    assert test(A, [A, True]) is True


def test_premisas_debe_ser_lista():
    with pytest.raises(TypeError):
        test(A, B)
    with pytest.raises(TypeError):
        test(A, True)


# ── noDerivable ────────────────────────────────────────────────────────

def test_noDerivable():
    assert test(noDerivable(B), [A])          # B no se deduce de A
    assert not test(noDerivable(A), [A])      # A sí se deduce de A
    assert test(-noDerivable(A), [A])         # "A es derivable"
    assert not test(-noDerivable(B), [A])
    assert test(noDerivable(B) | A, [A])
    assert test(noDerivable(A) | B, [A, B])
    assert not test(noDerivable(A) & B, [A, B])


def test_noDerivable_no_admitido_en_premisas():
    with pytest.raises(ValueError):
        test(B, [noDerivable(A)])
    with pytest.raises(ValueError):
        test(B, [A & noDerivable(A)])


# ── repr: debe ser evaluable y reconstruir la misma fórmula ────────────

FORMULAS = [
    A, -A, --A, A & B, A | B, A >> B, A ** B,
    (A | B) & C, A | (B & C), (A & B) | C,
    -(A & B), -(A | B), -A & B, -(A >> B),
    (-A) ** B, -(A ** B), A ** -B,
    (A >> B) >> C, A >> (B >> C),
    (A ** B) ** C, A ** (B ** C),
    A & B >> C, (A & B) >> C,
    alguno(A, B), unoDe(A, B, C), alguno(A & B, -C),
    unoDe(A | B, -(C & D)), noDerivable(A >> B), -noDerivable(A),
    v(1), v(1) & v('1'),
]


@pytest.mark.parametrize("f", FORMULAS, ids=repr)
def test_repr_roundtrip(f):
    g = eval(repr(f), vars(calcprop))
    assert g == f
    assert repr(g) == repr(f)


def test_repr_legible():
    assert repr(A & B) == "v('A') & v('B')"
    assert repr(-A & B) == "-v('A') & v('B')"
    assert repr((A | B) >> C) == "(v('A') | v('B')) >> v('C')"
    assert repr(-(A & B)) == "-(v('A') & v('B'))"
    assert repr((-A) ** B) == "(-v('A')) ** v('B')"
    assert repr(alguno(A, B)) == "alguno(v('A'), v('B'))"
    assert repr(unoDe(A, B)) == "unoDe(v('A'), v('B'))"
    assert repr(noDerivable(A)) == "noDerivable(v('A'))"


def test_repr_operador_desconocido():
    with pytest.raises(ValueError):
        repr(Proposicion(['xor', A, B]))


# ── igualdad, hash y bool ──────────────────────────────────────────────

def test_igualdad_y_hash():
    assert v('A') == v('A')
    assert v('A') != v('B')
    assert v(1) != v('1')
    assert A & B == A & B
    assert A & B != B & A
    assert hash(A & B) == hash(v('A') & v('B'))
    assert len({A, v('A'), A & B, v('A') & v('B')}) == 2
    assert {A & B: 1}[v('A') & v('B')] == 1


def test_and_or_not_de_python_lanzan_error():
    with pytest.raises(TypeError):
        bool(A)
    with pytest.raises(TypeError):
        not A
    with pytest.raises(TypeError):
        A and B
    with pytest.raises(TypeError):
        A or B
    with pytest.raises(TypeError):
        test(A and B, [B])


# ── span ───────────────────────────────────────────────────────────────

def test_span():
    F = {A: True}
    assert span(F, A) is True
    assert span(F, B) is False
    assert span(F, A >> -A) is False
    assert span(F, -A >> A) is True
    assert span(F, A ** B) is False
    assert span(F, alguno(B, A)) is True
    assert span(F, alguno(B, C)) is False
    assert span(F, unoDe(A, B)) is True
    assert span({A: True, B: True}, unoDe(A, B)) is False
    assert span({}, unoDe(A, B)) is False


def test_span_errores():
    with pytest.raises(ValueError):
        span({}, noDerivable(A))
    with pytest.raises(ValueError):
        span({}, Proposicion(['xor', A, B]))


# ── extension y refuta ────────────────────────────────────────────────

def test_extension_y_refuta():
    M = extension([(v('llueve') >> -v('llueve'), True)], {v('basilisco'): True})
    assert M == {v('basilisco'): True, v('llueve'): False}
    assert extension([(A, True), (-A, True)], {}) == {}
    assert refuta(A | -A) == {}
    M = refuta(A >> B, [A])
    assert M[A] is True and M[B] is False
    assert span(M, A >> B) is False


def test_extension_operador_desconocido():
    with pytest.raises(ValueError):
        extension([(Proposicion(['xor', A, B]), True)], {})


# ── precedencia de Python (documentada, no modificable) ───────────────

def test_precedencia_python():
    assert (A & B >> C) == (A & (B >> C))
    assert (A | B >> C) == (A | (B >> C))
    assert (-A ** B) == -(A ** B)
    assert (A >> B >> C) == ((A >> B) >> C)


# ── herramientas didácticas: tabla_verdad y explica ────────────────────

def test_atomos_y_subformulas():
    f = (A | B) >> (-A & C)
    assert atomos(f) == [A, B, C]
    assert subformulas(f) == [A | B, -A, -A & C, f]
    assert atomos(unoDe(A, B, A)) == [A, B]
    assert atomos(A) == [A] and subformulas(A) == []


def test_tabla_verdad_basica():
    t = tabla_verdad(A | -A)
    assert len(t.filas) == 2 and t.tautologia and not t.contradiccion
    t = tabla_verdad(A & -A)
    assert t.contradiccion
    t = tabla_verdad(B, [A, A >> B])
    assert t.atomos == [A, B]
    assert t.columnas == [A, B, A >> B, B]
    assert [t.cumple_premisas(f) for f in t.filas] == [True, False, False, False]
    assert t.consecuencia
    t = tabla_verdad((A | B) >> C, subformulas=True)
    assert t.columnas == [A, B, C, A | B, (A | B) >> C]
    assert "V" in str(t) and "<table" in t._repr_html_()


def test_tabla_verdad_premisas_booleanas():
    assert tabla_verdad(A, [True]).consecuencia is False
    assert tabla_verdad(A, [False]).consecuencia is True
    assert tabla_verdad(A, [B, -B]).consecuencia is True
    with pytest.raises(TypeError):
        tabla_verdad(True)
    with pytest.raises(ValueError):
        tabla_verdad(noDerivable(A))


def _formula_aleatoria(rnd, atoms, prof):
    if prof == 0 or rnd.random() < 0.25:
        return rnd.choice(atoms)
    op = rnd.choice(['-', '&', '|', '>>', '**', 'alguno', 'unoDe'])
    f = lambda: _formula_aleatoria(rnd, atoms, prof - 1)
    if op == '-':
        return -f()
    if op in ('alguno', 'unoDe'):
        return {'alguno': alguno, 'unoDe': unoDe}[op](*[f() for _ in range(rnd.randint(1, 3))])
    x, y = f(), f()
    return {'&': x & y, '|': x | y, '>>': x >> y, '**': x ** y}[op]


def test_tableaux_coincide_con_fuerza_bruta():
    """test (tableaux) y tabla_verdad (todos los mundos) deben coincidir siempre."""
    import random
    rnd = random.Random(2026)
    atoms = [v(c) for c in 'pqrs']
    for _ in range(300):
        P = _formula_aleatoria(rnd, atoms, 3)
        H = [_formula_aleatoria(rnd, atoms, 2) for _ in range(rnd.randint(0, 2))]
        assert test(P, H) == tabla_verdad(P, H).consecuencia, (P, H)
        M = refuta(P, H)
        if M:   # el contraejemplo debe serlo de verdad
            assert span(M, P) is False and all(span(M, Q) for Q in H)


def test_explica():
    r = explica(B, [A, A >> B])
    assert r.resultado is True and r.contraejemplo is None
    s = str(r)
    assert "regla de >>" in s and "rama cerrada" in s and "test → True" in s
    r = explica(A >> C, [A >> B])
    assert r.resultado is False
    assert span(r.contraejemplo, A >> C) is False
    assert "contraejemplo" in str(r) and "<pre" in r._repr_html_()
    r = explica(noDerivable(C), [A])
    assert r.resultado is True and "Lo comprobamos aparte" in str(r)
    assert explica(True).resultado is True and "True" in str(explica(True))
    for P, H in [(unoDe(A, B, C) >> -B, [A]), (alguno(A, B), [A ** B, A]),
                 ((A ** B) ** C, [])]:
        assert explica(P, H).resultado == test(P, H)


def test_extension_sin_traza_no_cambia():
    assert extension([(A & B, True)], {}) == {A: True, B: True}
    traza = []
    extension([(A & B, False)], {}, traza=traza)
    assert traza and any("regla de &" in l for l in traza)
