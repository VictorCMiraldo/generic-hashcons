{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE TypeFamilies   #-}
module GHC.Generics.Holes where

import Data.Proxy
import GHC.Generics

data H1 h a x
  = Hole (h x)
  | K1_  a
  deriving (Eq , Show)

type family Holes (h :: * -> *) rep :: * -> * where
  Holes h (K1 R a)   = H1 h a
  Holes h (M1 i c f) = M1 i c (Holes h f)
  Holes h U1         = U1
  Holes h (f :*: g)  = Holes h f :*: Holes h g
  Holes h (f :+: g)  = Holes h f :+: Holes h g

class HolesInj rep where
  holesInj :: Proxy h -> rep x -> Holes h rep x

instance HolesInj (K1 R a) where
  holesInj _ (K1 a) = K1_ a

instance HolesInj U1 where
  holesInj _ U1 = U1

instance (HolesInj f) => HolesInj (M1 i c f) where
  holesInj p (M1 f) = M1 (holesInj p f)

instance (HolesInj f, HolesInj g) => HolesInj (f :*: g) where
  holesInj p (f :*: g) = holesInj p f :*: holesInj p g

instance (HolesInj f, HolesInj g) => HolesInj (f :+: g) where
  holesInj p (L1 f) = L1 (holesInj p f)
  holesInj p (R1 g) = R1 (holesInj p g)


{-
class Generic a => GenericH a where
  type family Holes (h :: * -> *) a :: * -> *

  holesInj :: Proxy h -> Proxy a
           -> Rep a x -> Holes h a x

  holesProj :: Proxy h -> Proxy a
            -> (forall y . h y -> Rep a y)
            -> Holes h a x -> Rep a x

-}
