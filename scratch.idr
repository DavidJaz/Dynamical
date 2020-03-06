module scratch 

import Control.Monad.Identity
import lens
import system
-- Example 1:
data State1 = Work Int Int | Ready

data O1 = Input | Busy | Output Int
Interface1 : Interface
Interface1 = MkInterface O1 I
   where
    I  : O1 -> Type
    I Input      = (Int, Int) 
    I Busy       = ()
    I (Output _) = ()
 
Add : PureSystem State1 Interface1
Add = MkSystem readout update
   where
    readout : State1 -> output Interface1
    update  : (s : State1) -> (input Interface1 (readout s)) -> Identity State1

    readout (Work 0 n) = Output n
    readout (Work m n) = Busy
    readout Ready      = Input

    update (Work 0 n) _  = pure   Ready
    update (Work m n) _  = pure $ Work (m - 1) n
    update Ready (m , n) = pure $ Work m       n

nextTest : Selection Interface1
nextTest Input      = (10, 0)
nextTest Busy       = ()
nextTest (Output _) = ()

-- Lotka Voltera Predator Prey Model
record LKState where
       constructor MkLK
       rabbits : Int
       foxes   : Int

TLKState : LKState -> Type
TLKState _ = LKState

record LKParams where
       constructor MkParams
       rabbitBirth : Int
       interaction : Int
       foxDeath    : Int
ILK : LKState -> Type
ILK _ = LKParams        
        
LK : DMlens Identity LKState TLKState LKState ILK
LK = MkDMlens id update
  where
    update : (s : LKState) -> ILK s -> Identity (TLKState s)
    update s p = pure $ MkLK newrabbits newfoxes
      where 
        newrabbits = (rabbits s) + (rabbitBirth p)*(rabbits s) - (interaction p) * (rabbits s) * (foxes s)
        newfoxes   = (foxes s)   + (interaction p) * (rabbits s) * (foxes s) - (foxDeath p) * (foxes s) 
