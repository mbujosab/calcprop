from prop import *
from FormatoPreguntas import *
from subprocess import call
p = ProblemaTipo( \
  [
    [  "En el ajuste MCO del modelo lineal " \
       + "$\\mathbf{y}=\\mathbf{X}{\\mathbf{\\beta}}+{\\mathbf{otros}}$, donde " \
       + "$\\mathop{\\mathbf{X}}\\limits_{[{\\scriptscriptstyle N\\times K}]}$, "
    ],
    [
        Supuesto("si $rg(\\mathbf{X}) < k$, donde $k \\leq N$, entonces: ",
                 v("Mcoli")),

        Supuesto("si $rg(\\mathbf{X}) = k$, donde $k \\leq N$, entonces: ",
                 -v("Mcoli")),
    ],
    [
        Cuestion("Ningún regresor es combinación lineal de los demás",
                 -v("Mcoli")),
        
        Cuestion("Las $k$ columnas de $\\mathbf{X}$ son linealmente indep.",
                 -v("Mcoli")),
        
        Cuestion("Las $N$ filas de $\\mathbf{X}$ son linealmente indep.",
                 False),
        
        Cuestion("Algún regresor es combinación lineal del resto",
                 v("Mcoli")),
    ],
    [
        Cuestion("El vector $\\mathbf{y}$ es combinación lineal de los regresores",
                 False, -v("Mcoli")),
        
        Cuestion("Las ecuaciones normales tienen una \\emph{única} solución",
                 -v("Mcoli")),
        
        Cuestion("Es sistema de ecuaciones normales es compatible (tiene solución)",
                 True),
    ],
    [
        Cuestion("El estimador MCO $\\widehat{\\mathbf{\\beta}}$ está definido",
                 -v("Mcoli")),
        
        Cuestion("La correlación entre regresores es 1 en valor absoluto",
                 False),
        
        Cuestion("La correlación entre regresores es menor que 1 en valor absoluto",
                 -v("Mcoli")),
    ],
  ])     

nombre     = "EcNormales-RangoX"
directorio = "../ejemplos/"

QuizMoodleLastCh (nombre + "-Moodle", directorio, p)
cmd = "cd " + directorio + "&& lualatex " + nombre + "-Moodle" + ".tex"
status = call(cmd, cwd=directorio, shell=True)
     
with open(directorio + nombre + ".tex","w") as f:
    for var in p:
        f.write( AMClastCh(nombre, var[0], var[1], var[2]) )
