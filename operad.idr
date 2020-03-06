module operad

-- We don't define the notion of operad, but we do make idris behave like one:
infixr 4 :-: 
data Bulletin : (l : List Type) -> Type where
     EmptyBulletin : Bulletin []
     (:-:)         : (x : a) -> (xs : Bulletin l) -> Bulletin (a :: l)

-- A multifunction
infixr 2 >>~>
(>>~>) : List Type -> Type -> Type
(>>~>) [] a = a
(>>~>) (x::xs) a = x -> xs >>~> a 

-- multifunction application
infixr 0 >>$
(>>$) : (l >>~> a) -> Bulletin l -> a
(>>$) a EmptyBulletin = a
(>>$) f (x:-:xs)      = f x >>$ xs 



example : Bulletin [Int, Int, String]
example = 3 :-: 4 :-: "Hi" :-: EmptyBulletin

test : [Int, Int, String] >>~> Int
test a b s = a + b + (toIntNat $ Prelude.Strings.length s)
