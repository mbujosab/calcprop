class Proposicion:
    def __init__(self,data):
        self.data = data
        
    def __hash__(self):
        return hash(self.data)
    
    def __eq__(self, another):
        return hasattr(another, 'data') and self.data == another.data

    def __and__(self,other):
        return Proposicion(['and', self, other])
    def __or__(self,other):
        return Proposicion(['or', self, other])
    def __neg__(self):
        return Proposicion(['not', self])
    def __rshift__(self,other):
        return Proposicion(['implica', self, other])
    def __pow__(self,other):
        return Proposicion(['equivale', self, other])
        
    def __repr__(self):
        if isinstance(self.data,list):
            if self.data[0] == "and":
                return repr(self.data[1]) + " & "+ repr(self.data[2])
            if self.data[0] == "or":
                return repr(self.data[1]) + " | "+ repr(self.data[2])
            if self.data[0] == "not":
                return "-" + repr(self.data[1])
            if self.data[0] == "implica":
                return repr(self.data[1]) + " >> "+ repr(self.data[2])
            if self.data[0] == "equivale":
                return repr(self.data[1]) + " ** "+ repr(self.data[2])
            if self.data[0] == "unoDe":
                return "unoDe("+','.join([repr(x) for x in self.data[1:]]) +")"
            if self.data[0] == "noDerivable":
                return "noDerivable("+repr(self.data[1]) +")"            
    
        else:
            return 'v('+repr(self.data)+')'        
class v(Proposicion):
    def __init__(self, data):
        super().__init__(data)
  
def alguno(X,*args):
    return Proposicion(['alguno', X] + [a for a in args])
def unoDe(X,*args):
    return Proposicion(['unoDe',  X] + [a for a in args])

def noDerivable(X):
    return Proposicion(['noDerivable', X])

def span(F, Prop):    
    if type(Prop) == type(v('')):
        return (Prop in F) and F[Prop] 
    elif Prop.data[0] == 'and':
        return span(F, Prop.data[1]) and span(F, Prop.data[2])
    
    elif Prop.data[0] == 'or':
        return span(F, Prop.data[1]) or span(F, Prop.data[2])
    
    elif Prop.data[0] == 'not':
        return not span(F, Prop.data[1])
        
    elif Prop.data[0] == 'implica':
        return (not span(F, Prop.data[1])) or span(F, Prop.data[2]) 
        
    elif Prop.data[0] == 'equivale':
        return span(F, Prop.data[1]) == span(F, Prop.data[2]) 
    
    elif Prop.data[0] == 'alguno':
        return span(F,Prop.data[1]) or span(F,alguno(Prop.data[2:])) if len(Prop.data)>2\
          else span(F,Prop.data[1])
    
    elif Prop.data[0] == 'unoDe':
        A = Prop.data[1]
        if len(Prop.data)==2:
            return span(F, A)
        else:
            B = Proposicion(['alguno'] + Prop.data[2:])
            C = Proposicion(['unoDe']  + Prop.data[2:])
            return span(F, (A&-B) | (-A&C) ) 

def extension(objetivo, valores, premisas=[]):
    if objetivo == []:       
        return valores
    
    Obj = objetivo[0]         
    P   = Obj[0]
    VF  = Obj[1] 
    if isinstance(P.data,list):
        if P.data[0] == 'not' :   
            A = P.data[1]
            return extension( [(A, not VF)] + objetivo[1:], valores, premisas )
        elif P.data[0] == 'and':
            A = P.data[1]
            B = P.data[2]
            if(VF):
                return extension([ (A,True), (B,True) ] + objetivo[1:], valores, premisas)
            else:
                r = extension( [(A,False)] + objetivo[1:],valores,premisas)
                return extension([(B,False)]+objetivo[1:],valores,premisas) if not r else r
        
        elif P.data[0] == "or":
            A = P.data[1]
            B = P.data[2]
            if not VF:
                return extension([(A,False),(B,False)] + objetivo[1:], valores, premisas)
            else:
                r = extension([(A,True)] + objetivo[1:], valores, premisas)
                return extension([(B,True)]+objetivo[1:],valores, premisas) if not r else r
        
        elif P.data[0] == "implica":
            A = P.data[1]
            B = P.data[2]
            return extension([ ( -A|B, VF) ] + objetivo[1:], valores, premisas)
        elif P.data[0] == "equivale":
            A = P.data[1]
            B = P.data[2]
            return extension([( (A>>B) & (B>>A), VF)] + objetivo[1:], valores, premisas)
        elif P.data[0] == "alguno":
            A = P.data[1]
            if len(P.data)==2:
                return extension([(A,VF)] + objetivo[1:], valores, premisas)
            else:
                B = Proposicion(["alguno"] + P.data[2:])
                return extension([( A|B, VF)] + objetivo[1:], valores, premisas)                  
        elif P.data[0] == "unoDe":
            A = P.data[1]
            if len(P.data)==2:
                return extension([(A,VF)] + objetivo[1:], valores, premisas)
            else:
                B = Proposicion(["alguno"] + P.data[2:])
                C = Proposicion(["unoDe"] + P.data[2:])
                return extension([( (A&-B) | (-A&C), VF)] + objetivo[1:], valores, premisas)
        elif P.data[0] == "noDerivable":
            A = P.data[1]
            valoresExt = valores.copy() 
            valoresExt[v(repr(P))] = VF
                             
            derivable = not extension([(A,False)] + premisas, {}, premisas)
                             
            return extension(objetivo[1:],valores2,premisas) if not derivable == VF else {}
                             
    else:      
        if P in valores:
            return extension(objetivo[1:], valores, premisas) if valores[P]==VF else {}
        else:
            valoresExt    = valores.copy() 
            valoresExt[P] = VF          
            return extension(objetivo[1:], valoresExt, premisas)
def refuta(P, premisas=[]):
    h=[(Q,True) for Q in premisas]
    return extension([(P,False)]+h, {}, h) 

def test(P,premisas=[]):
    if P == True:
        return True
    if P == False:
        return False
    else:
        return True if not refuta(P, premisas) else False

class Marcador:
    def __init__(self, data):
        self.data = data
    def __iter__(self):
        self.p = [0 for x in self.data]
        return self                                
    def __next__(self):
        def Siguiente(x,y):
            if x == [] :
                return []    
            s = Siguiente(x[1:],y[1:])
            if s == []:
                if x[0]+1 == y[0]:
                    return []
                else:
                    return [x[0]+1] + [0 for i in x[1:]]
            else:
                return [x[0]] + s
        if self.p == []:
            raise StopIteration                         
        n = self.p
        self.p = Siguiente(self.p, self.data)
        return n

class Supuesto:
    def __init__(self,enunciado, semantica, precond=True):
        self.e = enunciado
        self.s = semantica
        self.p = precond
class Cuestion:
    def __init__(self, enunciado, semantica, precond=True, exp=""):
        self.e = enunciado
        self.s = semantica
        self.p = precond
        self.x = exp
class ProblemaTipo:
    def __init__(self, supuestos_y_cuestiones):
        self.e = supuestos_y_cuestiones

    def __iter__(self):
        self.l    = [x if isinstance(x,list) else [x] for x in self.e]
        self.long = len(self.l)
        self.i    = iter(Marcador([len(x) for x in self.l]))
        self.c    = 0
        return self
    def __next__(self):
        
        self.c += 1
        while True:
            try:
                variante = next(self.i)
            except StopIteration:
                raise StopIteration
    
            enunciado     = ""
            hipotesis     = []
            cuestiones    = []
                         
            for n in range(self.long+1):
                if n == self.long:
                    return (str(self.c), enunciado, cuestiones)
        
                componente = self.l[n][variante[n]]
                if isinstance(componente, str):
                    enunciado = enunciado + componente
                    
                elif isinstance(componente, Supuesto):
                    if test(componente.p, hipotesis):
                        enunciado = enunciado +  componente.e
                        hipotesis = hipotesis + [componente.s]
                    else:
                        print('\n Supuesto: '   + str(componente.e) \
                            + ' rechazado por ' + str(componente.p) + '\n')
                        break
                    
                elif isinstance(componente, Cuestion):
                    if test(componente.p, hipotesis):
                        cuestiones = cuestiones + \
                            [(componente.e,(True if test(componente.s, hipotesis) else False),1,componente.x)]
                    else:
                        cuestiones = cuestiones + \
                            [(componente.e,'rechazada por ' + str(componente.p),0,componente.x)]
                        print('\n Cuestion: '   + str(componente.e) \
                            + ' rechazada por ' + str(componente.p) + '\n')
                        break

class ProblemaTipoProfe:
    def __init__(self, supuestos_y_cuestiones):
        def CuestionesJuntas(l):
            def CreaLista(t):
                return t if isinstance(t, list) else [t]
            p = []
            for e in l:
                if isinstance(e,str):
                    p.append(e)
                elif not isinstance(CreaLista(e)[0],Cuestion): 
                    p.append(e)
                else:
                    p.extend(CreaLista(e))            
            return p
        self.e = CuestionesJuntas(supuestos_y_cuestiones)

    def __iter__(self):
        self.l    = [x if isinstance(x,list) else [x] for x in self.e]
        self.long = len(self.l)
        self.i    = iter(Marcador([len(x) for x in self.l]))
        self.c    = 0
        return self
    def __next__(self):
        
        self.c += 1
        while True:
            try:
                variante = next(self.i)
            except StopIteration:
                raise StopIteration
    
            enunciado     = ""
            hipotesis     = []
            cuestiones    = []
                         
            for n in range(self.long+1):
                if n == self.long:
                    return (str(self.c), enunciado, cuestiones)
        
                componente = self.l[n][variante[n]]
                if isinstance(componente, str):
                    enunciado = enunciado + componente
                    
                elif isinstance(componente, Supuesto):
                    if test(componente.p, hipotesis):
                        enunciado = enunciado +  componente.e
                        hipotesis = hipotesis + [componente.s]
                    else:
                        print('\n Supuesto: '   + str(componente.e) \
                            + ' rechazado por ' + str(componente.p) + '\n')
                        break
                    
                elif isinstance(componente, Cuestion):
                    if test(componente.p, hipotesis):
                        cuestiones = cuestiones + \
                            [(componente.e,(True if test(componente.s, hipotesis) else False),1,componente.x)]
                    else:
                        cuestiones = cuestiones + \
                            [(componente.e,'rechazada por ' + str(componente.p),0)]
from random import sample  
class ProblemaVF():
    def __init__(self, enunciado, cuestiones, NumPreguntas):
        self.e = enunciado
        self.c = cuestiones
        self.NumPreguntas = NumPreguntas

    def __iter__(self):
        self.contador = 0
        return self
    
    def __next__(self):
        cuestiones = sample(self.c, self.NumPreguntas)
        self.contador  += 1
        return (str(self.contador), self.e, cuestiones)
