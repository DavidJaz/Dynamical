module Main 

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
 
implementation Show O1 where
  show Input = "Input"
  show Busy = "Busy"
  show (Output n)= "Output: " ++ show n


BusyBeaver : PureSystem State1 Interface1
BusyBeaver = MkSystem readout update
   where
    readout : State1 -> output Interface1
    update  : (s : State1) -> (input Interface1 (readout s)) -> Identity State1

    readout (Work 0 n) = Output n
    readout (Work m n) = Busy
    readout Ready      = Input

    update (Work 0 n) _  = pure   Ready
    update (Work m n) _  = pure $ Work (m - 1) (n + 1)
    update Ready (m , n) = pure $ Work m       n
    
Add : PureSystem Int (SimpleInterface Int (Int, Int)) 
Add = boxUp (pure . uncurry (+))
    
wiring1 : Lens Identity (interfaceOf (Add <+> (OneStepDelay Int))) (ForwardInterface Int)
wiring1 = MkLens fst b
  where
    f : output (interfaceOf (Add <+> (OneStepDelay Int))) -> output (ForwardInterface Int) 
    f = fst
  
    b :  (x : output (interfaceOf (Add <+> (OneStepDelay Int))))
      -> input (ForwardInterface $ output Interface1) (f x)
      -> Identity $ input (interfaceOf (Add <+> (OneStepDelay Int))) x



nextTest : Selection Interface1
nextTest Input      = (10, 13)
nextTest Busy       = ()
nextTest (Output _) = ()

testTraj : Trajectory Interface1
testTraj = runPureSystem BusyBeaver Ready

testStream : Stream (output Interface1)
testStream = toStreamTrajectory testTraj nextTest

testList : List (output Interface1)
testList = take 30 testStream

-- Lotka Voltera Predator Prey Model
record LKState where
       constructor MkLK
       rabbits : Int
       foxes   : Int

record LKParams where
       constructor MkParams
       rabbitBirth : Int
       interaction : Int
       foxDeath    : Int

LKInterface : Interface
LKInterface = MkInterface LKState (const LKParams)
        
LK : PureSystem LKState LKInterface
LK = MkSystem id update
  where
    update : (s : LKState) -> input LKInterface $ s -> Identity LKState 
    update s p = pure $ MkLK newrabbits newfoxes
      where 
        newrabbits = (rabbits s) + (rabbitBirth p)*(rabbits s) - (interaction p) * (rabbits s) * (foxes s)
        newfoxes   = (foxes s)   + (interaction p) * (rabbits s) * (foxes s) - (foxDeath p) * (foxes s) 



main : IO ()
main = printLn $ show testList






