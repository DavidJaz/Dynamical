module system

import Control.Monad.Identity
import Prelude.Stream

import lens
import monadalgebra

public export
System :  (m : Type -> Type)
       -> (s : Type)
       -> (i : Interface)
       -> Type
System m s i = Lens m (SimpleInterface s s) i

export
MkSystem :  (readout : state -> output i)
         -> (update  : (s : state) -> input i (readout s) -> m state)
         -> System m state i
MkSystem = MkLens

readout :  (sys : System m s i)
        -> (s -> output i)
readout = forward

update  :  (sys : System m s i)
        -> ((state : s) -> input i (readout sys state) -> m s)
update = back

public export
SimpleSystem :  (m : Type -> Type)
             -> (s : Type)
             -> (o : Type)
             -> (i : Type)
             -> Type
SimpleSystem m s o i = System m s (SimpleInterface o i)

public export
PureSystem : (s : Type) -> (i : Interface) -> Type
PureSystem = System Identity

public export
PureSimpleSystem : (s : Type) -> (o : Type) -> (i : Type) -> Type
PureSimpleSystem = SimpleSystem Identity

public export 
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
 
 
 
