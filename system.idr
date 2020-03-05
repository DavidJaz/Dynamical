module system

import lens
import monadalgebra

System :  (m : Type -> Type)
       -> (s : Type)
       -> (i : Interface)
       -> Type
System m s i = Lens m (SimpleInterface s s) i

SimpleSystem :  (m : Type -> Type)
             -> (s : Type)
             -> (o : Type)
             -> (i : Type)
             -> Type
SimpleSystem m s o i = System m s (SimpleInterface o i)


          
 
