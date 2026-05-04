from prop import *
from FormatoPreguntas import *

enunciado = "Indique qué afirmaciones son verdaderas:"
banco = [
     ("Todo alumno que va a clase aprueba",   False),
     ("Todo alumno que suspende va a clase",  False),
     ("Todo alumno que sabe aprueba",         True ),
     ("Si aprueban todos eres buen profesor", False),
     ("Si suspenden todos eres mal profesor", False),
     ("Si suspenden todos es frustrante",     True ),]
GenVar = iter( ProblemaVF (enunciado, banco, 3) ) # tres preguntas por variante

nombre     = "EjemploVF"
directorio = "../ejemplos/"
with open(directorio + nombre + ".tex","w") as f:
    for i in range(4):                            # cuatro variantes
        var = (next(GenVar))
        f.write(AMC_VF(nombre,var[0],var[1],var[2]))

from prop import *
from FormatoPreguntas import *

p = [
  [r"Se dice que un proceso estocástico $\boldsymbol{X}$ sin componentes deterministas es: "],
  [Supuesto("", unoDe(v("I(0)"),v("I(1)"),v("I(2)")))],
  [
    Supuesto(r"$I(0)$ ",                      v("I(0)")),    
    Supuesto(r"$I(1)$ ",                      v("I(1)")),    
    Supuesto(r"$I(2)$ ",                      v("I(2)")),    
  ],
  [r"cuando"],
  [
    Cuestion("tiene representación ARMA estacionaria e invertible",                     v("I(0)") ),
    Cuestion(r"$(1-\mathsf{B})^0*\boldsymbol{X}$ tiene representación ARMA estacionaria e invertible",
                                                                                        v("I(0)") ),
    Cuestion(r"$(1-\mathsf{B})*\boldsymbol{X}$ es I(0)",                                v("I(1)"), -v("I(0)") ),
  ],
  [
    Cuestion(r"$(1-\mathsf{B})*\boldsymbol{X}$ tiene representación ARMA estacionaria e invertible",
                                                                                        v("I(1)") ),
    Cuestion(r"$Var(X_t)<\infty$, para $t\in\mathbb{Z}$",                                     False ),
    Cuestion(r"$(1-\mathsf{B})^2*\boldsymbol{X}$ tiene representación ARMA estacionaria e invertible",
                                                                                        v("I(2)") ),
  ], 
  [
    Cuestion(r"$(1-\mathsf{B})^2*\boldsymbol{X}$ es I(1)",                                  False ),
    Cuestion(r"$(1-\mathsf{B})*\boldsymbol{X}$ es I(1)",                                v("I(2)") ),
    Cuestion(r"$(1-\mathsf{B})^2*\boldsymbol{X}$ es I(0)",                              v("I(2)"), -v("I(0)") ),
  ],
]
preguntas = {}; mc=1;
preguntas[nombre] = ProblemaTipoProfe( p );
nombre     = "Ejemploamc"
directorio = "../ejemplos/"

mc = 1 # preguntas en una columna
with open(directorio + nombre + ".tex","w") as f:
    for var in preguntas[nombre]:
        f.write( AMCmcProfe(nombre, var[0], var[1], var[2], mc) )
