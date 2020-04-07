module Lens

%access public export

--- Code by David I. Spivak and David Jaz Myers
--- © 2020  

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
(<.>) life23 life12 = MkLens obs int
      where
        obs : pos a1 -> pos a3
        obs = (observe life23) . (observe life12)

        int : (p : pos a1) -> (dis a3 (obs p)) -> dis a1 p
        int p = (interpret life12 p) . (interpret life23 (observe life12 p))

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

--- Reflections to Type ---

const : Type -> Arena
const t = IOArena Void t

motor : Type -> Arena
motor t = IOArena () t

sensor : Type -> Arena
sensor t = IOArena t ()

ev0 : Arena -> Arena
ev0 a = const (AsFunctor a Void)

fromEv0 : (a : Arena) -> Lens (ev0 a) a
fromEv0 a = MkLens o i
          where
            o : (p : pos a ** dis a p -> Void) -> pos a
            o = fst
--          i : (x : pos (ev0 a)) -> dis a (o x) -> dis (ev0 a) x
--          i : (x : AsFunctor a Void) -> dis a (o x) -> dis (ev0 a) x
            i : (x : (p : pos a ** dis a p -> Void)) -> dis a (fst x) -> dis (ev0 a) x
            i (p ** f) = f

ev1 : Arena -> Arena
ev1 a = const $ pos a

toEv1 : (a : Arena) -> Lens a (ev1 a)
toEv1 a = MkLens id (\_ => absurd)

ev1y : Arena -> Arena
ev1y a = motor $ pos a

fromEv1y : (a : Arena) -> Lens (ev1y a) a
fromEv1y a = MkLens id (\_, _ => ()) 

constantFunction : {t, u : Type} -> (t -> u) -> Lens (const t) (const u)
constantFunction {t} {u} f = MkLens f (\_ => id)

motorFunction : {t, u : Type} -> (t -> u) -> Lens (motor t) (motor u)
motorFunction {t} {u} f = MkLens f (\_ => id) 

sensorFunction : {t, u: Type} -> (t -> u) -> Lens (sensor u) (sensor t)
sensorFunction {t} {u} f = MkLens id (\_ => f)

--- sum ---

zero : Arena
zero = IOArena Void Void

infixr 4 <++>

(<++>) : Arena -> Arena -> Arena
(<++>) a b = MkArena posab disab
          where
            posab : Type
            posab = Either (pos a) (pos b)
            disab : posab -> Type
            disab (Left p)  = dis a p
            disab (Right p) = dis b p

sum : (ind : Type ** ind -> Arena) -> Arena
sum (ind ** arena) = MkArena psum dsum
          where
            psum : Type
            psum = (i : ind ** pos (arena i))
            dsum : psum -> Type
            dsum (i ** p) = dis (arena i) p



sumLens : Lens a1 b1 -> Lens a2 b2 -> Lens (a1 <++> a2) (b1 <++> b2)
sumLens {a1} {b1} {a2} {b2} l1 l2 = MkLens o i
          where
            o : pos (a1 <++> a2) -> pos (b1 <++> b2)
            o (Left p1)   = Left (observe l1 p1)
            o (Right p2) = Right (observe l2 p2)
            i : (p : pos (a1 <++> a2)) -> dis (b1 <++> b2) (o p) -> dis (a1 <++> a2) p
            i (Left p1) d1  = interpret l1 p1 d1
            i (Right p2) d2 = interpret l2 p2 d2


--- product ---

one : Arena
one = IOArena Void ()

infixr 4 <**>

(<**>) : Arena -> Arena -> Arena
(<**>) a b = MkArena posab disab
          where
            posab : Type
            posab = (pos a, pos b)
            disab : posab -> Type
            disab (pa, pb) = Either (dis a pa) (dis b pb)

prodList : List Arena -> Arena
prodList [] = one
prodList (a :: as) = a <**> (prodList as)

-- functoriality of prod
prodLens : Lens a1 b1 -> Lens a2 b2 -> Lens (a1 <**> a2) (b1 <**> b2)
prodLens {a1} {b1} {a2} {b2} l1 l2 = MkLens o i 
          where
            o : pos (a1 <**> a2) -> pos (b1 <**> b2)
            o (p1, p2) = (observe l1 p1, observe l2 p2)
            i : (p : pos (a1 <**> a2)) -> dis (b1 <**> b2) (o p) -> dis (a1 <**> a2) p
            i (p1, p2) (Left d1)  = Left (interpret l1 p1 d1)
            i (p1, p2) (Right d2) = Right (interpret l2 p2 d2)

-- prod is the dependent product of polynomials; used in both inner homs
prod : (ind : Type ** ind -> Arena) -> Arena
prod (ind ** arena) = MkArena pprod dprod
          where
            pprod : Type
            pprod = (i : ind) -> pos (arena i)
            dprod : pprod -> Type
            dprod p = (i : ind ** dis (arena i) (p i))



--- Juxtaposition ---

infixr 4 &

(&) : Arena -> Arena -> Arena
(&) a b = MkArena posab disab
          where 
            posab : Type
            posab = (pos a, pos b)
            disab : posab -> Type
            disab (pa, pb) = (dis a pa, dis b pb)

juxtList : List Arena -> Arena
juxtList = foldr (&) Closed

juxtLens : Lens a1 b1 -> Lens a2 b2 -> Lens (a1 & a2) (b1 & b2)
juxtLens {a1} {b1} {a2} {b2} l1 l2 = MkLens o i
          where 
            o : pos (a1 & a2) -> pos (b1 & b2)
            o (p1, p2) = (observe l1 p1, observe l2 p2)
            i : (p : pos (a1 & a2)) -> dis (b1 & b2) (o p) -> dis (a1 & a2) p
            i (p1, p2) (d1, d2) = (interpret l1 p1 d1, interpret l2 p2 d2)


{-
juxtSelf : (t : List Type) -> Lens (Self (foldr Pair () t)) (juxtList (map Self t))
juxtSelf t = MkLens id i
          where
            o : (foldr Pair () t) -> pos (juxtList (map Self t))

            i : (p : pos (Self (foldr Pair () t))) -> dis (juxtList (map Self t)) (o p) -> dis (Self (foldr Pair () t)) p

juxtSelf : (ind : Type) -> (s : ind -> Type) -> Lens (Self ((i : ind) -> s i)) (juxt ind (Self . s))
juxtSelf ind s = MkLens id (\_ => id)
-}


{-
juxtLens : (ind : Type) -> 
              (a1 : ind -> Arena) ->
              (a2 : ind -> Arena) -> 
              ((i : ind) -> Lens (a1 i) (a2 i))
              ->
              Lens (juxt ind a1) (juxt ind a2)
juxtLens ind a1 a2 life = MkLens obse inte 
          where
            obse : pos (juxt ind a1) -> pos (juxt ind a2)
            obse p i = observe (life i) (p i)
            inte : (p : pos (juxt ind a1)) -> dis (juxt ind a2) (obse p) -> dis (juxt ind a1) p
            inte p d i = interpret (life i) (p i) (d i)
-}



--- Circle product ---

infixr 4 @@
(@@) : Arena -> Arena -> Arena
(@@) a b = MkArena posab disab
          where
            posab : Type
            posab = (p : pos a ** dis a p -> pos b)
            disab : posab -> Type
            disab (p ** f) = (d : dis a p ** dis b (f d))



circLens : Lens a1 b1 -> Lens a2 b2 -> Lens (a1 @@ a2) (b1 @@ b2)
circLens {a1} {b1} {a2} {b2} l1 l2 = MkLens o i
          where
            o : pos (a1 @@ a2) -> pos (b1 @@ b2)
            o (p ** f) = (observe l1 p ** (observe l2) . f . (interpret l1 p))
            i : (p : pos (a1 @@ a2)) -> dis (b1 @@ b2) (o p) -> dis (a1 @@ a2) p
            i (p ** f) (d1 ** d2) = (e1 ** interpret l2 (f e1) d2)
            where
              e1 : dis a1 p 
              e1 = interpret l1 p d1

--- Selves are comonoids ---

counit : (s : Type) -> Lens (Self s) Closed
counit s = MkLens o i
          where
            o : s -> ()
            o _ = ()
            i : s -> () -> s
            i s _ = s

comult : (s : Type) -> Lens (Self s) ((Self s) @@ (Self s))
comult s = MkLens o i
          where
            o : s -> pos ((Self s) @@ (Self s))
            o x = (x ** id)
            i : (x : s) -> (dis ((Self s) @@ (Self s)) (o x)) -> s
            i x (d1 ** d2) = d2



--- Duoidal ---

duoidal : {a1, a2, b1, b2 : Arena} -> Lens ((a1 @@ a2) & (b1 @@ b2))
                                           ((a1 & b1) @@ (a2 & b2))
duoidal {a1} {a2} {b1} {b2} = MkLens o i
          where
            x : Arena
            x = (a1 @@ a2) & (b1 @@ b2)
            y : Arena
            y = (a1 & b1) @@ (a2 & b2)
            o : pos x -> pos y
            o ((p1 ** p2), (q1 ** q2)) = pp
              where
                pp : (p : (pos a1, pos b1) ** dis (a1 & b1) p -> pos (a2 & b2))
                pp = ((p1, q1) ** (\d : dis (a1 & b1) (p1, q1) => (p2 (fst d), q2 (snd d))))
            i : (p : pos x) -> dis y (o p) -> dis x p
            i ((p1 ** p2), (q1 ** q2)) = ii
              where
--              ii : dis y ((p1, q1) ** (\d : dis (a1 & b1) (p1, q1) => (p2 (fst d), q2 (snd d)))) 
--                      -> dis x ((p1 ** p2), (q1 ** q2))
                ii : (de1 : dis (a1 & b1) (p1, q1) ** dis (a2 & b2) (p2 (fst de1), q2 (snd de1)))
                        -> dis x ((p1 ** p2), (q1 ** q2))
                ii (de1 ** de2) = ((fst de1 ** fst de2), (snd de1 ** snd de2))

--- Exponentiation ---

infixr 4 ^

--prod : (ind : Type ** ind -> Arena) -> Arena
(^) : Arena -> Arena -> Arena
(^) a b = prod (pos a ** arena)
          where
            arena : pos a -> Arena
            arena p = b @@ ((const $ dis a p) <++> Closed)

--- Internal Hom ---

infixr 4 ^^
(^^) : Arena -> Arena -> Arena
(^^) a b = prod (pos a ** arena)
          where 
            arena : pos a -> Arena
            arena p = b @@ (motor $ dis a p)

--- Dynamical systems ---

JazDynam : (state : Type) -> (body : Arena) -> Type
JazDynam state body = Lens (Self state) body

JazMotor : (state : Type) -> (output : Type) -> Type
JazMotor state output = JazDynam state (motor output)

JazMotorToDynam : JazMotor s o -> JazDynam s (motor o)
JazMotorToDynam = id

record Dynam where
       constructor MkDynam
       state : Type
       body  : Arena
       life  : Lens (Self state) body

{- Technical debt:
   MotorDynam was made because these systems "just run":
   they don't require any input. But somehow, this 
   should probably be done by asking a Dynam whether its
   body is a motor or not, rather than by making a whole
   new type.
-}

record MotorDynam where
       constructor MkMotorDynam
       state  : Type
       output : Type
       life   : Lens (Self state) (motor output) 


run : (d : MotorDynam) -> (state d) -> Stream (output d)
run d s = (observe (life d) s) :: (run d next)
        where
          next : state d
          next = interpret (life d) s ()

motorToDynam : MotorDynam -> Dynam
motorToDynam b = MkDynam (state b) (motor (output b)) (life b)
  


static : Dynam
static = MkDynam () Closed (motorFunction id)

infixr 4 &&&
(&&&) : Dynam -> Dynam -> Dynam
(&&&) dyn1 dyn2 = MkDynam state12 body12 life12
          where
            state12 : Type
            body12  : Arena
            life12  : Lens (Self state12) body12
            state12 = (state dyn1, state dyn2)
            body12  = (body dyn1) & (body dyn2)
            life12  = MkLens o i
            where
              o : (state dyn1, state dyn2) -> (pos (body dyn1), pos (body dyn2))
              i : (s12 : (state dyn1, state dyn2)) -> dis body12 (o s12) -> state12 
              o (s1, s2) = (observe (life dyn1) s1, observe (life dyn2) s2)
              i (s1, s2) (d1, d2) = 
                (interpret (life dyn1) s1 d1, interpret (life dyn2) s2 d2)

juxtapose : List Dynam -> Dynam
juxtapose []        = static
juxtapose (d :: ds) = d &&& (juxtapose ds)

install : (d : Dynam) -> (a : Arena) -> Lens (body d) a -> Dynam
install d a l = MkDynam (state d) a (l <.> (life d))

installMotor : (d : Dynam) -> (output : Type) -> Lens (body d) (motor output) -> MotorDynam
installMotor d o l = MkMotorDynam (state d) o (l <.> (life d))


--- Debugging ---

current : (d : Dynam) -> state d -> pos (body d)
current d s = observe (life d) s

feed : (dyn : Dynam) -> (s : state dyn) -> dis (body dyn) (observe (life dyn) s) -> state dyn
feed dyn s d = interpret play s d
          where 
            play : Lens (Self (state dyn)) (body dyn)
            play = life dyn

--- Examples ---


funcToDynam : {s : Type} -> {t : Type} -> (s -> t) -> Dynam
funcToDynam {s} {t} f = MkDynam t bodyf lifef
            where
              bodyf : Arena
              lifef : Lens (Self t) bodyf
              bodyf = IOArena s t
              lifef = MkLens id (const f)




delay : (s : Type) -> Dynam
delay s = funcToDynam (the (s -> s) id)

plus : Dynam
plus = funcToDynam (uncurry (+))


Prefib : Dynam
Prefib = juxtapose [plus, delay Integer, delay Integer]

{-
(&) a b = MkArena posab disab
          where 
            posab : Type
            posab = (pos a, pos b)
            disab : posab -> Type
            disab (pa, pb) = (dis a pa, dis b pb)

-}


fibwd : Lens (body Prefib) (motor Integer)
fibwd = MkLens observe interpret 
          where
            observe : (Integer, Integer, Integer, ()) -> Integer
            interpret : (p : (Integer, Integer, Integer, ())) -> () -> dis (body Prefib) p
            observe (de1, pl, de2, _) = de1
            interpret (de1, pl, de2, _) = \_ => ((de1, de2), pl, de1, ())
              -- This was a cheat. I didn't know which order to put (de1, pl, de2).


Fibonacci : MotorDynam
Fibonacci = installMotor Prefib Integer fibwd

FibSeq : Stream Integer
FibSeq = run Fibonacci (1, 0, 0, ())

-- take 10 FibSequence
-- Slow























































--- Appendix 1 ---



{- Here is <++> in terms of sum

(<++>) : Arena -> Arena -> Arena
(<++>) a b = sum (ind ** arena)
          where
            ind : Type
            ind = Either () ()
            arena : ind -> Arena
            arena (Left ()) = a
            arena (Right ()) = b
-}

{- Here is <**> in terms of prod

(<**>) : Arena -> Arena -> Arena
(<**>) a b = prod (ind ** arena)
          where
            ind : Type
            ind = Either () ()
            arena : ind -> Arena
            arena (Left ()) = a
            arena (Right ()) = b
-}


juxt : (ind : Type) -> (ind -> Arena) -> Arena
juxt ind arena = MkArena pjuxt djuxt
          where
            pjuxt : Type
            pjuxt = (i : ind) -> pos (arena i)
            djuxt : pjuxt -> Type
            djuxt p = (i : ind) -> dis (arena i) (p i)


{-
juxtapose : (ind : Type) -> (ind -> Dynam) -> Dynam
juxtapose ind dynam = MkDynam stjux bojux lejux
          where
            bod : ind -> Arena
            sta : ind -> Type
            sel : ind -> Arena
            len : (i : ind) -> Lens (sel i) (bod i)
            bod = body . dynam
            sta = state . dynam
            sel = Self . sta
            len i = life (dynam i)
            stjux : Type
            bojux : Arena
            lejux : Lens (Self stjux) bojux
            stjux = (i : ind) -> sta i
            bojux = juxt ind bod
            lejux = (juxtLens ind sel bod len) <.> (juxtSelf ind sta)
-}

--- Distributivity ---

prodSum : {a, b, c : Arena} -> Lens (a <**> (b <++> c)) ((a <**> b) <++> (a <**> c))
prodSum {a} {b} {c} = MkLens o i
            where
              a1 : Arena
              a1 = a <**> (b <++> c)
              a2 : Arena
              a2 = (a <**> b) <++> (a <**> c)
              o : pos a1 -> pos a2
              o (p, Left q)  = Left (p, q)
              o (p, Right r) = Right (p, r)
              i : (p : pos a1) -> dis a2 (o p) -> dis a1 p
              i (pa, Left pb) (Left da) = Left da
              i (pa, Left pb) (Right db) = Right db
              i (pa, Right pc) (Left da) = Left da
              i (pa, Right pc) (Right dc) = Right dc

sumProd : {a, b, c : Arena} -> Lens ((a <**> b) <++> (a <**> c)) (a <**> (b <++> c))
sumProd {a} {b} {c} = MkLens o i
            where
              a1 : Arena
              a1 = (a <**> b) <++> (a <**> c)
              a2 : Arena
              a2 = a <**> (b <++> c)
              o : pos a1 -> pos a2
              o (Left (pa, pb)) = (pa, Left pb)
              o (Right (pa, pc)) = (pa, Right pc)
              i : (p : pos a1) -> dis a2 (o p) -> dis a1 p
              i (Left (pa, pb)) (Left da) = Left da
              i (Left (pa, pb)) (Right db) = Right db
              i (Right (pa, pc)) (Left da) = Left da
              i (Right (pa, pc)) (Right dc) = Right dc

juxtSum : {a, b, c : Arena} -> Lens (a & (b <++> c)) ((a & b) <++> (a & c))
juxtSum {a} {b} {c} = MkLens o i
            where
              a1 : Arena
              a1 = a & (b <++> c)
              a2 : Arena
              a2 = (a & b) <++> (a & c)
              o : pos a1 -> pos a2
              o (pa, Left pb) = Left (pa, pb)
              o (pa, Right pc) = Right (pa, pc)
              i : (p : pos a1) -> dis a2 (o p) -> dis a1 p
              i (pa, Left pb) (da, db) = (da, db)
              i (pa, Right pc) (da, dc) = (da, dc)

sumJuxt : {a, b, c : Arena} -> Lens ((a & b) <++> (a & c)) (a & (b <++> c))
sumJuxt {a} {b} {c} = MkLens o i
            where
              a1 : Arena
              a1 = (a & b) <++> (a & c)
              a2 : Arena
              a2 = a & (b <++> c)
              o : pos a1 -> pos a2
              o (Left (pa, pb)) = (pa, Left pb)
              o (Right (pa, pc)) = (pa, Right pc)
              i : (p : pos a1) -> dis a2 (o p) -> dis a1 p
              i (Left (pa, pb)) (da, db) = (da, db)
              i (Right (pa, pc)) (da, dc) = (da, dc)


