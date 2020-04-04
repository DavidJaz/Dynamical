module Lens

%access public export

------ The category of arenas ------


--- Objects ---
record Arena where
       constructor MkArena
       pos : Type
       dis : pos -> Type

--- Morphisms---


record Hook (dom : Arena) (cod : Arena) where
       constructor MkHook
       observe   : pos dom -> pos cod
       interpret : (p : pos dom) -> dis cod (observe p) -> dis dom p

--- Identity ---
idHook : (a : Arena) -> Hook a a
idHook a = MkHook id (\_ => id)


--- Composition ---

infixr 4 <.>
(<.>) : Hook a2 a3 -> Hook a1 a2 -> Hook a1 a3
(<.>) hook23 hook12 = MkHook obs int
      where
        obs : pos a1 -> pos a3
        obs = (observe hook23) . (observe hook12)

        int : (p : pos a1) -> (dis a3 (obs p)) -> dis a1 p
        int p = (interpret hook12 p) . (interpret hook23 (observe hook12 p))

--- Manipulations on Arenas ---

Display : Arena -> Type  
Display a = (p : pos a ** dis a p)

AsFunctor : Arena -> Type -> Type
AsFunctor a y = (p : pos a ** dis a p -> y)


--- Special Arenas ---

IOArena : (i : Type) -> (o : Type) -> Arena --positions as output and
IOArena i o = MkArena o (\_ => i)           --distinctions as input

Self : Type -> Arena
Self s = IOArena s s

OArena : Type -> Arena
OArena o = IOArena () o

IArena : Type -> Arena
IArena i = IOArena i ()

Closed : Arena
Closed = IOArena () ()


--- Sum ---

Sum : Arena -> Arena -> Arena
Sum a b = MkArena p d
          where
            p = Left (pos a) | Right (pos b)
            d (Left p)  = dis a p
            d (Right p) = dis b p

SumHook : Hook a b -> Hook a' b' -> Hook (Sum a a') (Sum b b')

--- Product ---

Prod : Arena -> Arena -> Arena

ProdHook : Hook a b -> Hook a' b' -> Hook (Prod a a') (Prod b b')

--- Juxtaposition ---

Juxt : Arena -> Arena -> Arena

JuxtHook : Hook a b -> Hook a' b' -> Hook (Juxt a a') (Juxt b b')

--- Circle product ---

Circ : Arena -> Arena -> Arena

CircHook : Hook a b -> Hook a' b' -> Hook (Circ a a') (Circ b b')
