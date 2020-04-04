module Lens

%access public export
-- An Interface is a dependent type
record Interface where
       constructor MkInterface
       output : Type
       input  : output -> Type

OIInterface : (o : Type) -> (i : Type) -> Interface
OIInterface o i = MkInterface o (\_ => i)

SimpleInterface: Type -> Interface
SimpleInterface s = OIInterface s s

OInterface : Type -> Interface
OInterface o = MkInterface o (const ())

IInterface : Type -> Interface
IInterface i = MkInterface () (const i)

Closed : Interface
Closed = OInterface ()

Display : Interface -> Type  
Display i = (o : output i ** input i o)  -- i : Interface

AsFunctor : Interface -> Type -> Type
AsFunctor (MkInterface o i) t = (x : o ** i x -> t)

Lens : (dom : Interface) -> (cod : Interface) -> Type
Lens dom cod = (t : Type) -> (AsFunctor dom) t 
                          -> (AsFunctor cod) t

--bimorphic lenses
record OILens (o1 : Type) (i1 : Type) (o2 : Type) (i2 : Type) where
       constructor MkLens
       forward  : o1 -> o2
       backward : o1 -> i2 -> i1

OILens2Lens : (OILens o1 i1 o2 i2) -> 
                  Lens (OIInterface o1 i1) (OIInterface o2 i2)
  -- forward  : o1 -> o2
  -- backward : o1 -> i2 -> i1 
  -- t : Type
  -- x : o1
  -- f : i1 -> t
  -- y : i2
OILens2Lens (MkLens forward backward) t (x ** f) = 
  ((forward x) ** (\y => f (backward x y)))

-- lens composition

infixr 4 <.> 
(<.>) : Lens int2 int3 -> Lens int1 int2 -> Lens int1 int3
(<.>) lens23 lens12 = \t => (lens23 t) . (lens12 t)



