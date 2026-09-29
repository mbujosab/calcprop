# Copyright (C) 2020-2026  Andrés Bujosa, Marcos Bujosa
#
# This file is part of calcprop.
#
# calcprop is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# calcprop is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

"""calcprop: un motor de cálculo proposicional.

Las fórmulas se construyen con ``v('etiqueta')`` (proposición atómica) y los
operadores ``&`` (y), ``|`` (o), ``-`` (no), ``>>`` (implica) y ``**`` (equivale),
más las funciones ``alguno``, ``unoDe`` y ``noDerivable``. La función ``test(P,
premisas)`` decide si ``P`` es consecuencia lógica de las ``premisas``;
``explica`` muestra el razonamiento paso a paso y ``tabla_verdad`` construye
la tabla de verdad.
"""

import html as _html
import itertools as _itertools

__all__ = ['Proposicion', 'v', 'alguno', 'unoDe', 'noDerivable',
           'span', 'extension', 'refuta', 'test',
           'atomos', 'subformulas', 'tabla_verdad', 'TablaVerdad',
           'explica', 'Razonamiento']

class Proposicion:
    """Fórmula del cálculo proposicional.

    ``data`` es una etiqueta (número o string) si la proposición es atómica
    (véase la subclase ``v``), o una lista ``[operador, operando, ...]`` si es
    compuesta, con ``operador`` en ``'and'``, ``'or'``, ``'not'``, ``'implica'``,
    ``'equivale'``, ``'alguno'``, ``'unoDe'`` o ``'noDerivable'``.

    Las fórmulas se combinan con los operadores ``&``, ``|``, ``-``, ``>>`` y
    ``**`` (nunca con ``and``, ``or`` y ``not``, que Python no permite redefinir).
    """
    def __init__(self, data):
        self.data = data

    def __hash__(self):
        if isinstance(self.data, list):
            return hash(repr(self))
        return hash(self.data)

    def __eq__(self, another):
        return isinstance(another, Proposicion) and self.data == another.data

    def __bool__(self):
        raise TypeError(
            "Una Proposicion no tiene valor de verdad por sí misma: use "
            "test(P, premisas). Para combinar proposiciones use los operadores "
            "&, | y - en lugar de and, or y not.")

    def __and__(self, other):
        return Proposicion(['and', self, other])
    def __or__(self, other):
        return Proposicion(['or', self, other])
    def __neg__(self):
        return Proposicion(['not', self])
    def __rshift__(self, other):
        return Proposicion(['implica', self, other])
    def __pow__(self, other):
        return Proposicion(['equivale', self, other])
    
    _SIMBOLO = {'and': '&', 'or': '|', 'implica': '>>', 'equivale': '**'}
    
    def __repr__(self):
        d = self.data
        if not isinstance(d, list):
            return 'v(' + repr(d) + ')'
        op = d[0]
    
        def operando(x):
            s = repr(x)
            if isinstance(x, Proposicion) and isinstance(x.data, list):
                binaria  = x.data[0] in Proposicion._SIMBOLO
                negacion = x.data[0] == 'not' and op == 'equivale'
                if binaria or negacion:
                    return '(' + s + ')'
            return s
    
        if op == 'not':
            return '-' + operando(d[1])
        if op in Proposicion._SIMBOLO:
            return operando(d[1]) + ' ' + Proposicion._SIMBOLO[op] + ' ' + operando(d[2])
        if op in ('alguno', 'unoDe', 'noDerivable'):
            return op + '(' + ', '.join(repr(x) for x in d[1:]) + ')'
        raise ValueError(f"Operador desconocido: {op!r}")
class v(Proposicion):
    """Proposición atómica (variable proposicional) con etiqueta ``data``.

    Dos llamadas ``v('A')`` producen proposiciones iguales entre sí (misma
    etiqueta), de modo que pueden usarse como claves de un diccionario.
    """
    pass

def alguno(X, *args):
    """``alguno(A, B, ...)``: al menos una de las proposiciones es verdadera."""
    return Proposicion(['alguno', X] + list(args))
def unoDe(X, *args):
    """``unoDe(A, B, ...)``: exactamente una de las proposiciones es verdadera."""
    return Proposicion(['unoDe', X] + list(args))

def noDerivable(X):
    """``noDerivable(P)``: ``P`` no es consecuencia lógica de las premisas.

    Solo tiene sentido en la fórmula que se evalúa con ``test``; no puede
    aparecer dentro de las premisas.
    """
    return Proposicion(['noDerivable', X])

def _contiene(P, operador):
    """True si el ``operador`` aparece en algún subárbol de la fórmula ``P``."""
    if not isinstance(P, Proposicion) or not isinstance(P.data, list):
        return False
    return P.data[0] == operador or any(_contiene(x, operador) for x in P.data[1:])

def span(F, Prop):
    """Valor de verdad de ``Prop`` bajo la valoración parcial ``F``.

    ``F`` es un diccionario ``{v('A'): True, v('B'): False, ...}``; toda
    proposición atómica ausente de ``F`` se considera ``False``.
    """
    if not isinstance(Prop.data, list):
        return bool(Prop in F and F[Prop])
    op = Prop.data[0]
    if op == 'and':
        return span(F, Prop.data[1]) and span(F, Prop.data[2])
    
    elif op == 'or':
        return span(F, Prop.data[1]) or span(F, Prop.data[2])
    
    elif op == 'not':
        return not span(F, Prop.data[1])
    
    elif op == 'implica':
        return (not span(F, Prop.data[1])) or span(F, Prop.data[2])
    
    elif op == 'equivale':
        return span(F, Prop.data[1]) == span(F, Prop.data[2])
    
    elif op == 'alguno':
        A = Prop.data[1]
        if len(Prop.data) == 2:
            return span(F, A)
        else:
            B = Proposicion(['alguno'] + Prop.data[2:])
            return span(F, A | B)
    
    elif op == 'unoDe':
        A = Prop.data[1]
        if len(Prop.data) == 2:
            return span(F, A)
        else:
            B = Proposicion(['alguno'] + Prop.data[2:])
            C = Proposicion(['unoDe']  + Prop.data[2:])
            return span(F, (A & -B) | (-A & C))
    
    elif op == 'noDerivable':
        raise ValueError("span no puede evaluar noDerivable: depende de las "
                         "premisas, no de una valoración; use test(P, premisas).")
    else:
        raise ValueError(f"Operador desconocido: {op!r}")

def _regla_not(P, VF):
    A = P.data[1]
    return [[(A, not VF)]]

def _regla_and(P, VF):
    A, B = P.data[1], P.data[2]
    if VF:
        return [[(A, True), (B, True)]]
    return [[(A, False)], [(B, False)]]

def _regla_or(P, VF):
    A, B = P.data[1], P.data[2]
    if VF:
        return [[(A, True)], [(B, True)]]
    return [[(A, False), (B, False)]]

def _regla_implica(P, VF):
    A, B = P.data[1], P.data[2]
    if VF:
        return [[(A, False)], [(B, True)]]
    return [[(A, True), (B, False)]]

def _regla_equivale(P, VF):
    A, B = P.data[1], P.data[2]
    if VF:
        return [[(A, True), (B, True)], [(A, False), (B, False)]]
    return [[(A, True), (B, False)], [(A, False), (B, True)]]

def _regla_alguno(P, VF):
    alternativas = P.data[1:]
    if VF:
        return [[(A, True)] for A in alternativas]
    return [[(A, False) for A in alternativas]]

def _regla_unoDe(P, VF):
    alternativas = P.data[1:]
    if VF:
        return [[(Aj, j == i) for j, Aj in enumerate(alternativas)]
                for i in range(len(alternativas))]
    ramas = [[(A, False) for A in alternativas]]
    for i, j in _itertools.combinations(range(len(alternativas)), 2):
        ramas.append([(alternativas[i], True), (alternativas[j], True)])
    return ramas

_REGLAS = {'not': _regla_not, 'and': _regla_and, 'or': _regla_or,
           'implica': _regla_implica, 'equivale': _regla_equivale,
           'alguno': _regla_alguno, 'unoDe': _regla_unoDe}
_NOMBRE_REGLA = {'not': '-', 'and': '&', 'or': '|', 'implica': '>>',
                 'equivale': '**', 'alguno': 'alguno', 'unoDe': 'unoDe'}

def _VF(b):
    return 'V' if b else 'F'

def _fmt_suposicion(par):
    return f"{par[0]!r} = {_VF(par[1])}"

def _fmt_ramas(ramas):
    partes = [" y ".join(_fmt_suposicion(s) for s in rama) for rama in ramas]
    if len(partes) == 1:
        return partes[0]
    return "o bien " + ", o bien ".join(partes)

def _es_pseudoatomo(A):
    return isinstance(A.data, str) and A.data.startswith('noDerivable(')

def _fmt_modelo(valores):
    pares = [f"{a!r} = {_VF(b)}" for a, b in valores.items() if not _es_pseudoatomo(a)]
    return "{ " + ", ".join(pares) + " }" if pares else "{ }"

def _anota(traza, nivel, texto):
    if traza is not None:
        traza.append("    " * nivel + texto)

def extension(objetivo, valores, premisas=[], traza=None, nivel=0):
    """Extiende la valoración parcial ``valores`` hasta satisfacer ``objetivo``.

    ``objetivo`` es una lista de pares ``(P, VF)``; ``premisas`` es la lista de
    proposiciones asumidas ciertas (solo la usa ``noDerivable``). Devuelve un
    modelo (diccionario átomo -> bool) que extiende ``valores`` y en el que cada
    ``P`` toma el valor ``VF``, o ``{}`` si no existe tal modelo.  Si ``traza``
    es una lista, se le añaden los pasos del razonamiento como texto.
    """
    if not objetivo:
        _anota(traza, nivel, "✓ No quedan suposiciones por cumplir: el mundo "
               + _fmt_modelo(valores) + " las satisface todas.")
        return valores

    (P, VF), resto = objetivo[0], objetivo[1:]
    if not isinstance(P.data, list):
        if P in valores:
            if valores[P] == VF:
                _anota(traza, nivel, f"{_fmt_suposicion((P, VF))}  ✓ ya estaba anotado.")
                return extension(resto, valores, premisas, traza, nivel)
            _anota(traza, nivel, f"{_fmt_suposicion((P, VF))}  ✗ contradice lo anotado "
                   f"({P!r} = {_VF(valores[P])}): rama cerrada.")
            return {}
        valoresExt    = valores.copy()
        valoresExt[P] = VF
        _anota(traza, nivel, f"{_fmt_suposicion((P, VF))}  → anotamos {P!r} = {_VF(VF)}.")
        return extension(resto, valoresExt, premisas, traza, nivel)
    op = P.data[0]
    if op == 'noDerivable':
        A = P.data[1]
        _anota(traza, nivel, f"{_fmt_suposicion((P, VF))}  ⇒  ¿se deduce {A!r} de las "
               "premisas? Lo comprobamos aparte:")
        subtraza = [] if traza is not None else None
        noDerivableA = bool(refuta(A, premisas, subtraza))
        if traza is not None:
            traza.extend("    " * (nivel + 1) + linea for linea in subtraza)
        _anota(traza, nivel + 1, f"Por tanto {A!r} {'NO' if noDerivableA else 'SÍ'} se deduce "
               f"de las premisas, y {P!r} = {_VF(noDerivableA)}.")
        if noDerivableA != VF:
            _anota(traza, nivel, f"✗ {_fmt_suposicion((P, VF))} es imposible: rama cerrada.")
            return {}
        valoresExt = valores.copy()
        valoresExt[v(repr(P))] = VF       # pseudo-átomo: el modelo nunca queda vacío
        return extension(resto, valoresExt, premisas, traza, nivel)
    if op not in _REGLAS:
        raise ValueError(f"Operador desconocido: {op!r}")
    ramas = _REGLAS[op](P, VF)
    _anota(traza, nivel, f"{_fmt_suposicion((P, VF))}  ⇒  por la regla de "
           f"{_NOMBRE_REGLA[op]}: {_fmt_ramas(ramas)}")
    for k, rama in enumerate(ramas, 1):
        subnivel = nivel
        if len(ramas) > 1:
            _anota(traza, nivel + 1, f"Rama {k} de {len(ramas)}: suponemos "
                   + " y ".join(_fmt_suposicion(s) for s in rama))
            subnivel = nivel + 2
        M = extension(rama + resto, valores, premisas, traza, subnivel)
        if M:
            return M
    if len(ramas) > 1:
        _anota(traza, nivel + 1, f"✗ Las {len(ramas)} ramas se cierran.")
    return {}
def refuta(P, premisas=[], traza=None):
    """Modelo que hace falsa ``P`` y ciertas las ``premisas``, o ``{}`` si no existe.

    Un resultado ``{}`` significa que ``P`` es consecuencia lógica de las
    ``premisas``. Las premisas ``True`` se ignoran; una premisa ``False`` hace
    que nada sea refutable.  Si ``traza`` es una lista, se le añaden los pasos.
    """
    if isinstance(premisas, (Proposicion, bool)):
        raise TypeError("premisas debe ser una lista de proposiciones, "
                        f"por ejemplo test(P, [{premisas!r}]).")
    premisas = [Q for Q in premisas if Q is not True]
    if any(Q is False for Q in premisas):
        _anota(traza, 0, "Una de las premisas es False: de una contradicción se "
               "deduce cualquier cosa, así que no hay contraejemplo posible.")
        return {}
    for Q in premisas:
        if _contiene(Q, 'noDerivable'):
            raise ValueError("noDerivable no puede aparecer en las premisas "
                             f"(premisa: {Q!r}).")
    suposiciones = [(P, False)] + [(Q, True) for Q in premisas]
    _anota(traza, 0, "Buscamos un mundo en el que "
           + ", ".join(_fmt_suposicion(s) for s in suposiciones) + ":")
    return extension(suposiciones, {}, premisas, traza)

def test(P, premisas=[]):
    """¿Es ``P`` consecuencia lógica de las ``premisas``?

    ``P`` puede ser una ``Proposicion`` o directamente ``True``/``False`` (que
    se devuelven tal cual). ``premisas`` es una lista de proposiciones.
    """
    if isinstance(P, bool):
        return P
    return not refuta(P, premisas)

def atomos(P):
    """Proposiciones atómicas de ``P``, sin repetir, en orden de aparición."""
    if not isinstance(P, Proposicion):
        return []
    if not isinstance(P.data, list):
        return [P]
    res = []
    for x in P.data[1:]:
        for a in atomos(x):
            if a not in res:
                res.append(a)
    return res

def subformulas(P):
    """Subfórmulas compuestas de ``P`` (incluida ``P``), de dentro hacia fuera."""
    if not isinstance(P, Proposicion) or not isinstance(P.data, list):
        return []
    res = []
    for x in P.data[1:]:
        for s in subformulas(x):
            if s not in res:
                res.append(s)
    if P not in res:
        res.append(P)
    return res

_lista_subformulas = subformulas   # alias: el parámetro de TablaVerdad se llama igual

class TablaVerdad:
    """Tabla de verdad de una fórmula, opcionalmente bajo unas premisas.

    Se construye con ``tabla_verdad(...)``.  Atributos: ``atomos``,
    ``columnas`` (átomos, subfórmulas, premisas y la fórmula), ``filas``
    (lista de diccionarios columna -> bool), ``consecuencia``, ``tautologia``
    y ``contradiccion``.  Se imprime como texto y, en Jupyter, como HTML.
    """
    def __init__(self, P, premisas=[], subformulas=False):
        if isinstance(P, bool):
            raise TypeError("tabla_verdad necesita una Proposicion, no un bool.")
        self.P = P
        self.premisas = [Q for Q in premisas if Q is not True]
        self._premisa_falsa = any(Q is False for Q in self.premisas)
        self.premisas = [Q for Q in self.premisas if Q is not False]
        formulas = self.premisas + [P]
        conjunto = []
        for f in formulas:
            for a in atomos(f):
                if a not in conjunto:
                    conjunto.append(a)
        self.atomos = sorted(conjunto, key=repr)
        columnas = list(self.atomos)
        if subformulas:
            for f in formulas:
                for s in _lista_subformulas(f):
                    if s not in columnas and s not in formulas:
                        columnas.append(s)
        columnas += [Q for Q in self.premisas if Q not in columnas]
        columnas.append(P)
        self.columnas = columnas
        self.filas = []
        for valores in _itertools.product([True, False], repeat=len(self.atomos)):
            F = dict(zip(self.atomos, valores))
            self.filas.append({c: span(F, c) for c in columnas})

    def cumple_premisas(self, fila):
        """True si en esa fila todas las premisas son verdaderas."""
        return not self._premisa_falsa and all(fila[Q] for Q in self.premisas)

    @property
    def consecuencia(self):
        """True si P es verdadera en todas las filas que cumplen las premisas."""
        return all(fila[self.P] for fila in self.filas if self.cumple_premisas(fila))

    @property
    def tautologia(self):
        return all(fila[self.P] for fila in self.filas)

    @property
    def contradiccion(self):
        return not any(fila[self.P] for fila in self.filas)

    def resumen(self):
        """Frase que interpreta la tabla."""
        n = len(self.filas)
        if not self.premisas and not self._premisa_falsa:
            k = sum(fila[self.P] for fila in self.filas)
            if k == n:
                return (f"{self.P!r} es V en las {n} filas: es una tautología "
                        "(test → True).")
            if k == 0:
                return (f"{self.P!r} es F en las {n} filas: es una contradicción "
                        "(test → False).")
            return (f"{self.P!r} es V en {k} de las {n} filas: es contingente, "
                    "no se deduce sin premisas (test → False).")
        marcadas = [i for i, fila in enumerate(self.filas, 1) if self.cumple_premisas(fila)]
        if not marcadas:
            return ("Ninguna fila cumple todas las premisas: son contradictorias entre "
                    "sí, y de una contradicción se deduce cualquier cosa (test → True).")
        malas = [i for i in marcadas if not self.filas[i - 1][self.P]]
        if not malas:
            donde = ("En la única fila marcada con *" if len(marcadas) == 1
                     else f"En las {len(marcadas)} filas marcadas con *")
            return (f"{donde} (premisas V), {self.P!r} es V: "
                    "se deduce de las premisas (test → True).")
        return (f"En la fila {malas[0]} las premisas son V pero {self.P!r} es F: "
                f"es un contraejemplo, {self.P!r} no se deduce (test → False).")

    def _cabeceras(self):
        return [repr(c) for c in self.columnas]

    def __str__(self):
        cab = self._cabeceras()
        marca = bool(self.premisas) or self._premisa_falsa
        anchos = [max(len(h), 1) for h in cab]
        lineas = []
        if marca:
            lineas.append("   " + " | ".join(h.center(w) for h, w in zip(cab, anchos)))
        else:
            lineas.append(" | ".join(h.center(w) for h, w in zip(cab, anchos)))
        lineas.append(("---" if marca else "") + "-+-".join("-" * w for w in anchos))
        for fila in self.filas:
            celdas = [_VF(fila[c]).center(w) for c, w in zip(self.columnas, anchos)]
            pref = (" * " if self.cumple_premisas(fila) else "   ") if marca else ""
            lineas.append(pref + " | ".join(celdas))
        lineas.append("")
        lineas.append(self.resumen())
        return "\n".join(lineas)

    __repr__ = __str__

    def _repr_html_(self):
        cab = self._cabeceras()
        marca = bool(self.premisas) or self._premisa_falsa
        esc = _html.escape
        h = ['<table style="border-collapse:collapse;font-family:monospace">',
             '<thead><tr>']
        if marca:
            h.append('<th></th>')
        for c, texto in zip(self.columnas, cab):
            estilo = "border-bottom:2px solid #888;padding:2px 8px"
            if c == self.P:
                estilo += ";border-left:2px solid #888"
            h.append(f'<th style="{estilo}">{esc(texto)}</th>')
        h.append('</tr></thead><tbody>')
        for fila in self.filas:
            ok = self.cumple_premisas(fila)
            fondo = "background:#fff3c4" if (marca and ok) else ""
            h.append(f'<tr style="{fondo}">')
            if marca:
                h.append(f'<td style="padding:2px 6px">{"*" if ok else ""}</td>')
            for c in self.columnas:
                estilo = "text-align:center;padding:2px 8px"
                if c == self.P:
                    estilo += ";border-left:2px solid #888;font-weight:bold"
                    if marca and ok and not fila[c]:
                        estilo += ";color:#c00"
                h.append(f'<td style="{estilo}">{_VF(fila[c])}</td>')
            h.append('</tr>')
        h.append('</tbody></table>')
        h.append(f'<p style="font-family:monospace">{esc(self.resumen())}</p>')
        return "".join(h)


def tabla_verdad(P, premisas=[], subformulas=False):
    """Tabla de verdad de ``P`` (bajo ``premisas`` si se dan); véase ``TablaVerdad``.

    Con ``subformulas=True`` se añaden columnas para cada subfórmula, de dentro
    hacia fuera, como en las tablas que se construyen a mano.
    """
    return TablaVerdad(P, premisas, subformulas)

class Razonamiento:
    """Traza del razonamiento de ``test``; se construye con ``explica(...)``.

    Atributos: ``P``, ``premisas``, ``pasos`` (lista de líneas), ``resultado``
    (el valor de ``test``) y ``contraejemplo`` (diccionario o ``None``).
    """
    def __init__(self, P, premisas, pasos, resultado, contraejemplo):
        self.P, self.premisas, self.pasos = P, premisas, pasos
        self.resultado, self.contraejemplo = resultado, contraejemplo

    def _cabecera(self):
        if self.premisas:
            prem = ", ".join(repr(Q) for Q in self.premisas)
            return [f"¿Se deduce  {self.P!r}  de las premisas  {prem} ?",
                    "Método: buscamos un contraejemplo, es decir, un mundo en el que "
                    "las premisas sean V y la fórmula F. Si toda rama se cierra por "
                    "contradicción, no existe tal mundo y la fórmula se deduce."]
        return [f"¿Es  {self.P!r}  una tautología (se deduce sin premisas)?",
                "Método: buscamos un contraejemplo, es decir, un mundo en el que la "
                "fórmula sea F. Si toda rama se cierra por contradicción, no existe "
                "tal mundo y la fórmula es una tautología."]

    def _conclusion(self):
        if isinstance(self.P, bool):
            return [f"La fórmula es directamente {self.P}: test → {self.resultado}."]
        if self.resultado:
            return ["Conclusión: todas las ramas se cierran, no hay contraejemplo. "
                    f"{self.P!r} se deduce de las premisas: test → True."]
        return [f"Conclusión: el mundo {_fmt_modelo(self.contraejemplo)} es un "
                f"contraejemplo (los átomos no listados pueden tomar cualquier valor). "
                f"{self.P!r} no se deduce de las premisas: test → False."]

    def __str__(self):
        if isinstance(self.P, bool):
            return "\n".join(self._conclusion())
        return "\n".join(self._cabecera() + [""] + self.pasos + [""] + self._conclusion())

    __repr__ = __str__

    def _repr_html_(self):
        esc = _html.escape
        if isinstance(self.P, bool):
            return f'<p style="font-family:monospace">{esc(self._conclusion()[0])}</p>'
        cab = "".join(f"<p>{esc(l)}</p>" for l in self._cabecera())
        pasos = []
        for linea in self.pasos:
            color = "#080" if "✓" in linea else ("#c00" if "✗" in linea else "")
            pasos.append(f'<span style="color:{color}">{esc(linea)}</span>')
        fin = self._conclusion()[0]
        color = "#080" if self.resultado else "#c00"
        return (f'<div style="font-family:monospace">{cab}'
                f'<pre style="margin:6px 0 6px 1em">{"<br>".join(pasos)}</pre>'
                f'<p style="color:{color}"><b>{esc(fin)}</b></p></div>')


def explica(P, premisas=[]):
    """Razonamiento paso a paso de ``test(P, premisas)``; véase ``Razonamiento``."""
    if isinstance(P, bool):
        return Razonamiento(P, list(premisas), [], P, None)
    pasos = []
    M = refuta(P, premisas, pasos)
    resultado = not M
    contraejemplo = None if resultado else {a: b for a, b in M.items() if not _es_pseudoatomo(a)}
    return Razonamiento(P, [Q for Q in premisas if not isinstance(Q, bool)],
                        pasos, resultado, contraejemplo)
