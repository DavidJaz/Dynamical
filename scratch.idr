module scratch 


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
record DMlens (m : Type -> Type) uf (ub : uf -> Type) df (db : df -> Type) where
       constructor MkDMlens
       passforward : uf -> df
       passback    : (x : uf) -> (db (passforward x)) -> m (ub x)

-- Lens Composition
infixr 4 <.> 
(<.>) : (Monad m) => DMlens m mf mb df db
                  -> DMlens m uf ub mf mb 
                  -> DMlens m uf ub df db
(<.>) lens2 lens1 = MkDMlens f b 
      where
        f : uf -> df
        f = (passforward lens2) . (passforward lens1)
        
        b : (x : uf) -> (db (f x)) -> (ub x)
        b x d = do
          middle <- (passback lens2) (passforward lens1 $ x) d
          (passback lens1) x middle
 
 
 
 
 
 
