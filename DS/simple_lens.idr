module Lens

%access public export

------ The category of arenas ------


--- Objects ---
record Arena where
       constructor MkArena
       pos : Type
       dis : pos -> Type

--- Morphisms---


record Lens (dom : Arena) (cod : Arena) where
       constructor MkLens
       observe   : pos dom -> pos cod
       interpret : (p : pos dom) -> dis cod (observe p) -> dis dom p

--- Identity ---

idLens : (a : Arena) -> Lens a a
idLens a = MkLens id (\_ => id)


--- Composition ---

infixr 4 <.>
(<.>) : Lens a2 a3 -> Lens a1 a2 -> Lens a1 a3
(<.>) lens23 lens12 = MkLens obs int
      where
        obs : pos a1 -> pos a3
        obs = (observe lens23) . (observe lens12)

        int : (p : pos a1) -> (dis a3 (obs p)) -> dis a1 p
        int p = (interpret lens12 p) . (interpret lens23 (observe lens12 p))

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

Closed : Arena
Closed = IOArena () ()


--- sum ---

sum : Arena -> Arena -> Arena
sum a b = MkArena posab disab
          where
            posab : Type
            posab = Either (pos a) (pos b)
            disab : posab -> Type
            disab (Left p)  = dis a p
            disab (Right p) = dis b p

infixr 4 <++>
(<++>) : Arena -> Arena -> Arena
(<++>) = sum


sumLens : Lens a1 b1 -> Lens a2 b2 -> Lens (sum a1 a2) (sum b1 b2)
sumLens {a1} {b1} {a2} {b2} l1 l2 = MkLens o i
               where
                 o : pos (sum a1 a2) -> pos (sum b1 b2)
                 o (Left p1)   = Left (observe l1 p1)
                 o (Right p2) = Right (observe l2 p2)
                 i : (p : pos (sum a1 a2)) -> dis (sum b1 b2) (o p) -> dis (sum a1 a2) p
                 i (Left p1) d1  = interpret l1 p1 d1
                 i (Right p2) d2 = interpret l2 p2 d2


--- product ---

prod : Arena -> Arena -> Arena
prod a b = MkArena posab disab
          where
            posab : Type
            posab = (pos a, pos b)
            disab : posab -> Type
            disab (pa, pb) = Either (dis a pa) (dis b pb)

prodLens : Lens a1 b1 -> Lens a2 b2 -> Lens (prod a1 a2) (prod b1 b2)
prodLens {a1} {b1} {a2} {b2} l1 l2 = MkLens o i 
          where
            o : pos (prod a1 a2) -> pos (prod b1 b2)
            o (p1, p2) = (observe l1 p1, observe l2 p2)
            i : (p : pos (prod a1 a2)) -> dis (prod b1 b2) (o p) -> dis (prod a1 a2) p
            i (p1, p2) (Left d1)  = Left (interpret l1 p1 d1)
            i (p1, p2) (Right d2) = Right (interpret l2 p2 d2)


--- Juxtaposition ---

juxt : Arena -> Arena -> Arena
juxt a b = MkArena posab disab
          where 
            posab : Type
            posab = (pos a, pos b)
            disab : posab -> Type
            disab (pa, pb) = (dis a pa, dis b pb)

juxtLens : Lens a1 b1 -> Lens a2 b2 -> Lens (juxt a1 a2) (juxt b1 b2)
juxtLens {a1} {b1} {a2} {b2} l1 l2 = MkLens o i
          where 
            o : pos (juxt a1 a2) -> pos (juxt b1 b2)
            o (p1, p2) = (observe l1 p1, observe l2 p2)
            i : (p : pos (juxt a1 a2)) -> dis (juxt b1 b2) (o p) -> dis (juxt a1 a2) p
            i (p1, p2) (d1, d2) = (interpret l1 p1 d1, interpret l2 p2 d2)


--- Circle product ---

circ : Arena -> Arena -> Arena
circ a b = MkArena posab disab
          where
            posab : Type
            posab = (p : pos a ** dis a p -> pos b)
            disab : posab -> Type
            disab (p ** f) = (d : dis a p ** dis b (f d))



circLens : Lens a1 b1 -> Lens a2 b2 -> Lens (circ a1 a2) (circ b1 b2)
circLens {a1} {b1} {a2} {b2} l1 l2 = MkLens o i
          where
            o : pos (circ a1 a2) -> pos (circ b1 b2)
            o (p ** f) = (observe l1 p ** (observe l2) . f . (interpret l1 p))
            i : (p : pos (circ a1 a2)) -> dis (circ b1 b2) (o p) -> dis (circ a1 a2) p
            i (p ** f) (d1 ** d2) = (e1 ** interpret l2 (f e1) d2)
            where
              e1 : dis a1 p 
              e1 = interpret l1 p d1

{-
counit : (s : Type) -> (Lens (self s) -> closed)
count s = MkLens o i
          where
             o _ = ()
             i s _ = s

-}










