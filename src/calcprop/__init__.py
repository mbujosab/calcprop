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
