# calcprop

[![Binder](https://mybinder.org/badge_logo.svg)](https://mybinder.org/v2/gh/mbujosab/calcprop/main?labpath=Introduccion.ipynb)

Librería de cálculo proposicional en Python. Construye fórmulas con
`v('etiqueta')` y los operadores `&`, `|`, `-`, `>>` y `**`, y decide con
`test(P, premisas)` si `P` es consecuencia lógica de las premisas.

```python
from calcprop import *

A, B = v('llueve'), v('suelo mojado')
test(B, [A, A >> B])        # True   (modus ponens)
test(A, [B, A >> B])        # False  (afirmar el consecuente)
test(unoDe(A, B), [A, -B])  # True
```

Cuando se mezclan conectivos distintos conviene poner paréntesis: la precedencia
es la de Python, no la de la lógica (`A & B >> C` se lee `A & (B >> C)`).

Para *ver* el razonamiento hay dos herramientas didácticas:

```python
print(explica(B, [A, A >> B]))       # árbol de refutación paso a paso
print(tabla_verdad(B, [A, A >> B]))  # tabla de verdad con las filas que cumplen las premisas
```

- Introducción al cálculo proposicional, interactiva: [`Introduccion.ipynb`](https://github.com/mbujosab/calcprop/blob/main/Introduccion.ipynb);
  se puede ejecutar sin instalar nada pulsando el botón *launch binder* de arriba.

- Manual de uso: [`Manual.org`](https://github.com/mbujosab/calcprop/blob/main/Manual.org) / [`Manual.pdf`](https://github.com/mbujosab/calcprop/blob/main/Manual.pdf).
- Código fuente documentado (programación literaria): [`CalcProp.org`](https://github.com/mbujosab/calcprop/blob/main/CalcProp.org);
  `src/calcprop/__init__.py` se genera de él mediante `org-babel-tangle`.
- Pruebas: `python -m pytest`.

Es el motor lógico del paquete [`qbank`](https://github.com/mbujosab/calcprop-qbank)
(generación de bancos de preguntas de opción múltiple).

## Instalación

```bash
pip install calcprop
```

## Autoría y licencia

Copyright (C) 2020-2026  Andrés Bujosa, Marcos Bujosa

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

See the [LICENSE](https://github.com/mbujosab/calcprop/blob/main/LICENSE) file for details.
