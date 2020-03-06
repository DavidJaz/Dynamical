module lens


-- An Interface is a dependent type
public export
record Interface where
       constructor MkInterface
       output : Type
       input  : output -> Type  

-- note: these all have to be public exports
-- otherwise, the type checker can't reduce the types, and you can't really use
-- them
public export
SimpleInterface : (o : Type) -> (i : Type) -> Interface
SimpleInterface o i = MkInterface o (\_ => i)

public export
ForwardInterface : Type -> Interface
ForwardInterface s = MkInterface s (\_ => ())

public export
Closed : Interface
Closed = ForwardInterface ()

public export
Total : Interface -> Type
Total i = (o : output i ** input i o)

public export 
Selection : Interface -> Type
Selection i = (o : output i) -> input i o

-- A trajectory in an interface is a hypothetical stream of outputs,
-- given at each state a choice of compatible inputs.
public export
codata Trajectory : (i : Interface) -> Type where
       (::) :  (head : output i) -> (tail : input i head -> Trajectory i) -> Trajectory i

public export
head : Trajectory i -> output i
head (head :: _) = head

public export
tail : (t : Trajectory i) -> input i (head t) -> Trajectory i
tail (_ :: tail) = tail

-- toStreamTrajectory takes a trajectory and a function which selects the next input
-- and yields a stream of outputs
export 
toStreamTrajectory :  (t : Trajectory i)
                   -> (next : Selection i)
                   -> Stream (output i)
toStreamTrajectory {i} t next = current :: toStreamTrajectory rest next
  where
    current : output i
    current = head t
    
    rest : Trajectory i
    rest = tail t (next current)

-- A Monadic Dependent Lens:
-- It consists of:
-- * a monad m
-- * a upstream passforward type uf
-- * a upstream passback type family ub depending on uf
-- * a downstream passforward type df
-- * a downstream passback type db depending on df
-- * a passforward function which takes upstream passforwards to downstream
-- * a passback function which takes downstream passbacks valid for a given upstream passforward,
--   and passes them back to the upstream passback.
public export
record Lens (m : Type -> Type) (up : Interface) (down : Interface) where
       constructor MkLens
       forward : output up -> output down
       back : (o : output up) -> (input down (forward o)) -> m (input up o)

public export
record DMlens (m : Type -> Type) uf (ub : uf -> Type) df (db : df -> Type) where
       constructor MkDMlens
       passforward : uf -> df
       passback    : (x : uf) -> (db (passforward x)) -> m (ub x)

-- Lens Composition
infixr 4 <.> 
export
(<.>) : (Monad m) => Lens m    mid down 
                  -> Lens m up mid
                  -> Lens m up     down 
(<.>) lens2 lens1 = MkLens f b 
      where
        f : output up -> output down 
        f = (forward lens2) . (forward lens1)
        
        b : (x : output up) -> (input down (f x)) -> m (input up x)
        b x d = do
          middle <- (back lens2) (forward lens1 $ x) d
          (back lens1) x middle

-- fromPairedFunction takes a function of the given type and
-- builds the interfaces and lenses out of it. 
export
fromPairedFunction :  ( (x : uf) -> (y : df ** (db y) -> m (ub x)) )
                   -> Lens m (MkInterface uf ub) (MkInterface df db) 
fromPairedFunction f = MkLens (\x => fst (f x)) (\x => snd (f x))


