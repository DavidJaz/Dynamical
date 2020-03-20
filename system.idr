module system


import Control.Monad.Identity
import Prelude.Stream

import lens
import monadalgebra


%access public export

System :  (m : Type -> Type)
       -> (s : Type)
       -> (i : Interface)
       -> Type
System m s i = Lens m (SimpleInterface s s) i

MkSystem :  (readout : state -> output i)
         -> (update  : (s : state) -> input i (readout s) -> m state)
         -> System m state i
MkSystem = MkLens

interfaceOf : System m s i -> Interface
interfaceOf _ = i

readout :  (sys : System m s i)
        -> (s -> output i)
readout = forward

update  :  (sys : System m s i)
        -> ((state : s) -> input i (readout sys state) -> m s)
update = back

SimpleSystem :  (m : Type -> Type)
             -> (s : Type)
             -> (o : Type)
             -> (i : Type)
             -> Type
SimpleSystem m s o i = System m s (SimpleInterface o i)

PureSystem : (s : Type) -> (i : Interface) -> Type
PureSystem = System Identity

PureSimpleSystem : (s : Type) -> (o : Type) -> (i : Type) -> Type
PureSimpleSystem = SimpleSystem Identity

runPureSystem :  {i : Interface} 
              -> (sys : PureSystem s i)
              -> (start : s)
              -> Trajectory i 
runPureSystem {i} sys start = current :: rest
              where
                current : output i
                current = readout sys start

                rest : input i (readout sys start) -> Trajectory i 
                rest nextinput = runPureSystem sys (eval $ update sys start nextinput)  
boxUp : (Monad m) => (f : b -> m a) -> System m a (SimpleInterface a b)
boxUp f = MkSystem id (\_ => f)

   
OneStepDelay : (Monad m) => (s : Type) -> System m s (SimpleInterface s s)
OneStepDelay s = MkSystem id (\_ => pure) 
 
(<+>) : (Monad m) => System m s i -> System m t j -> System m (s, t) (pair i j)
(<+>) = (<+>)
