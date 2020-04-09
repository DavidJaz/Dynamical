module TuringMachine

import dynamicalSystems
%access public export


HeadValue : Type
HeadValue = Either () Bool  -- the read-head is either blank or has a Boolean

data Command = Run (HeadValue, Either () ()) | Halt 
-- when running, print a HeadValue and move left or right
-- Otherwise we halt

TapeState : Type
TapeState = Int -> HeadValue

data TapePos = TapeRun HeadValue | TapeHalt | TapeHalted TapeState
data MachPos = MachRun Command   | MachHalt | MachHalted

TapeArena : Arena
TapeArena = MkArena TapePos dis
        where
          dis : TapePos -> Type
          dis (TapeRun _)    = Maybe Command
          dis TapeHalt       = ()
          dis (TapeHalted _) = Void

MachineArena : Arena
MachineArena = MkArena MachPos dis
        where
          dis : MachPos -> Type
          dis (MachRun _) = HeadValue
          dis MachHalt    = ()
          dis MachHalted  = Void

TuringInternal : Arena
TuringInternal = TapeArena & MachineArena

TuringExternal : Arena
TuringExternal = Closed <++> (const TapeState)

TuringWD : Lens TuringInternal TuringExternal
TuringWD = MkLens obs int
        where
          obs : pos TuringInternal -> Either () TapeState
          obs (TapeHalted tst, _) = Right tst             --finished.
          obs (_, MachHalted)     = Right (\_ => Left ()) --this should never happen
          obs (_, _)              = Left ()
          int : (p : pos TuringInternal) -> 
            dis TuringExternal (obs p) -> dis TuringInternal p
          int (TapeRun hval, MachRun comm) = \_ => (Just comm, hval)  --usual operation
          int (TapeRun _, MachHalt)        = \_ => (Nothing, ())      --machine just declared halt
          int (TapeHalt, MachHalt)         = \_ => ((), ())           -- everything stops
          int (TapeRun _, MachHalted)      = absurd               --this should never happen
          int (TapeHalt, MachHalted)       = absurd               --this should never happen
          int (TapeHalt, MachRun _)        = \_ => ((), Left ())  --this should never happen
          int (TapeHalted _, _)            = absurd               --this should never happen



