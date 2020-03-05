module scratch 

import Control.Monad.Identity
import lens
{-

S = Work Int Int | Ready
O = Input | Busy | Output Int

TS : S -> Type
I  : O -> Type

TS _         = S
I Input      = Int Int
I Busy       = ()
I (Output _) = ()

Add : Poly (S, TS) -> (O, I)
Add : (s : S) -> (o : O, I o -> TS s)

Add (Work 0 n)     = (Output n, \ ()  -> Ready)
Add (Work (m+1) n) = (Busy,     \ ()  -> Work m (n+1))
Add Ready          = (Input, \ (m, n) -> Work mn) 


-} 

-- Example 1:


data S1 = Work Int Int | Ready
State1 : Interface
State1 = SimpleInterface S1 

data O1 = Input | Busy | Output Int
Interface1 : Interface
Interface1 = MkInterface O1 I
   where
    I  : O1 -> Type
    I Input      = (Int, Int) 
    I Busy       = ()
    I (Output _) = ()
 


Add : Lens Identity State1 Interface1
Add = MkLens readout update
   where
    readout : output State1 -> output Interface1
    update  : (s : output State1) -> (input Interface1 (readout s)) -> Identity (input State1 s)

    readout (Work 0 n) = Output n
    readout (Work m n) = Busy
    readout Ready      = Input

    update (Work 0 n) _  = pure Ready
    update (Work m n) _  = pure $ Work (m - 1) n
    update Ready (m , n) = pure $ Work m       n

record LKState where
       constructor MkLK
       rabbits : Int
       foxes   : Int

TLKState : LKState -> Type
TLKState _ = LKState

record Params where
       constructor MkParams
       rabbitBirth : Int
       interaction : Int
       foxDeath    : Int
ILK : LKState -> Type
ILK _ = Params        
        
LK : DMlens Identity LKState TLKState LKState ILK
LK = MkDMlens id update
  where
    update : (s : LKState) -> ILK s -> Identity (TLKState s)
    update s p = pure $ MkLK newrabbits newfoxes
      where 
        newrabbits = (rabbits s) + (rabbitBirth p)*(rabbits s) - (interaction p) * (rabbits s) * (foxes s)
        newfoxes   = (foxes s)   + (interaction p) * (rabbits s) * (foxes s) - (foxDeath p) * (foxes s) 
