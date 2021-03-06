{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE TypeFamilies   #-}
{-# LANGUAGE PolyKinds   #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module GHC.Generics.Deep where

import Data.Proxy
import Data.Functor.Const
import Control.Monad.Identity
import GHC.Generics

----------------------------
-- The Monster

type family IsElem (a :: *) (as :: [ * ]) :: Bool where
  IsElem a (a ': as) = 'True
  IsElem a (b ': as) = IsElem a as
  IsElem a '[]       = 'False

type Elem    a as = IsElem a as ~ 'True
type NotElem a as = IsElem a as ~ 'False

-- A Value of type @SRep prim f rep@ represents one layer of
-- rep and, for the atoms of rep that are not elems of
-- the primitive types, some custom data dictated by a functor f.
-- You know where this is going.
data SRep (prim :: [ * ]) f (rep :: * -> *) :: * where
  S_D1   :: (NotElem a prim)       => f a -> SRep prim f (K1 R a) 
  S_K1   :: (Elem a prim , Show a) => a   -> SRep prim f (K1 R a)
  S_U1   :: SRep prim f U1
  S_M1   :: SRep prim f a -> SRep prim f (M1 i c a)
  S_L1   :: SRep prim f a -> SRep prim f (a :+: b) 
  S_R1   :: SRep prim f b -> SRep prim f (a :+: b)  
  (:**:) :: SRep prim f a -> SRep prim f b -> SRep prim f (a :*: b) 
deriving instance (forall a . Show (f a)) => Show (SRep prim f rep)

-- This is where this is going! :D
data FixAnn prim ann a :: * where
  FixAnn :: (Generic a)
         => { getAnn :: ann a 
            , unFix  :: SRep prim (FixAnn prim ann) (Rep a)
            }
         -> FixAnn prim ann a
deriving instance (forall a . Show (ann a)) => Show (FixAnn prim ann x)

type Fix prim = FixAnn prim (Const ())

--------------------------------------

mapRepM :: (Monad m)
        => (forall y . f y -> m (g y))
        -> SRep prim f rep -> m (SRep prim g rep)
mapRepM _f (S_K1 x) = return (S_K1 x)
mapRepM _f (S_U1)   = return S_U1
mapRepM f (S_D1 x)  = S_D1 <$> f x
mapRepM f (S_M1 x)  = S_M1 <$> mapRepM f x
mapRepM f (S_L1 x)  = S_L1 <$> mapRepM f x
mapRepM f (S_R1 x)  = S_R1 <$> mapRepM f x
mapRepM f (x :**: y)
  = (:**:) <$> mapRepM f x <*> mapRepM f y

mapRep :: (forall y . f y -> g y)
       -> SRep prim f rep -> SRep prim g rep
mapRep f = runIdentity . mapRepM (return . f)
        
cataM :: (Monad m)
      => (forall b x . Generic b
            => ann b -> SRep prim phi (Rep b) -> m (phi b))
      -> FixAnn prim ann a
      -> m (phi a)
cataM f (FixAnn ann x) = mapRepM (cataM f) x >>= f ann

synthesizeM :: (Monad m)
            => (forall b x . Generic b
                => ann b -> SRep prim phi (Rep b) -> m (phi b))
            -> FixAnn prim ann a
            -> m (FixAnn prim phi a)
synthesizeM f = cataM (\ann r -> flip FixAnn r <$> f ann (mapRep getAnn r))

--------------------------------------


-- Converting values to deep representations is easy and follows
-- almost the usual convention; one top level class
-- and one generic version. This time though, we need
-- special treatment on atoms.
class (Generic a) => Deep prim a where
  dfrom :: a -> Fix prim a
  default dfrom :: (GDeep prim (Rep a)) => a -> Fix prim a
  dfrom = FixAnn (Const ()) . gdfrom . from
  
  dto :: Fix prim a -> a
  default dto :: (GDeep prim (Rep a)) => Fix prim a -> a
  dto (FixAnn _ x) = to . gdto $ x

-- Typesyn to make life easier
type FIX prim = SRep prim (Fix prim)

-- Your usual suspect; the GDeep typeclass
class GDeep prim f where
  gdfrom :: f x -> FIX prim f
  gdto   :: FIX prim f -> f x

-- And the class that disambiguates primitive types
-- from types in the family. This is completely hidden from
-- the user though
class GDeepAtom prim (isPrim :: Bool) a where
  gdfromAtom  :: Proxy isPrim -> a -> FIX prim (K1 R a)
  gdtoAtom    :: Proxy isPrim -> FIX prim (K1 R a) -> a

instance (NotElem a prim , Deep prim a) => GDeepAtom prim 'False a where
  gdfromAtom _ a = S_D1 (dfrom a)
  gdtoAtom _ (S_D1 x) = dto x

instance (Elem a prim , Show a) => GDeepAtom prim 'True a where
  gdfromAtom _ a = (S_K1 a)
  gdtoAtom   _ (S_K1 a) = a

-- This ties the recursive knot
instance (GDeepAtom prim (IsElem a prim) a) => GDeep prim (K1 R a) where
  gdfrom (K1 a)  = gdfromAtom (Proxy :: Proxy (IsElem a prim)) a
  gdto   a       = K1 (gdtoAtom (Proxy :: Proxy (IsElem a prim)) a)

-- The rest of the instances are trivial
instance GDeep prim U1 where
  gdfrom U1  = S_U1
  gdto S_U1 = U1

instance (GDeep prim f) => GDeep prim (M1 i c f) where
  gdfrom (M1 x) = S_M1 (gdfrom x)
  gdto (S_M1 x) = M1 (gdto x)

instance (GDeep prim f , GDeep prim g) => GDeep prim (f :*: g) where
  gdfrom (x :*: y) = gdfrom x :**: gdfrom y
  gdto (x :**: y) = (gdto x) :*: (gdto y)

instance (GDeep prim f , GDeep prim g) => GDeep prim (f :+: g) where
  gdfrom (L1 x) = S_L1 (gdfrom x)
  gdfrom (R1 x) = S_R1 (gdfrom x)

  gdto (S_L1 x) = L1 (gdto x)
  gdto (S_R1 x) = R1 (gdto x)


---------------------------
---------------------------
---------------------------
--                       --
--    The User's View    --
--                       --
---------------------------
---------------------------
---------------------------

data Exp
  = Add Exp Exp
  | Pow Exp Exp
  | Sqrt Exp
  | Let [Decl] Exp
  | Var String
  | Lit Double
  deriving (Eq , Show , Generic)

data Decl
  = Decl String Exp
  deriving (Eq , Show , Generic)

type Prims = '[ String , Double ]

instance Deep Prims Exp
instance Deep Prims [Decl]
instance Deep Prims Decl

pyth :: Exp
pyth = Let [Decl "hypSq" (Add (Pow (Var "x") (Lit 2)) (Pow (Var "y") (Lit 2)))]
           (Sqrt (Var "hypSq"))


dfromPrim :: (Deep Prims a) => a -> Fix Prims a
dfromPrim = dfrom

---------------------------------------
-- Awesome; now, onto things I need: --
---------------------------------------


-- * Hash Cons: works; we can do synthesize; see above


-- * Unification and Anti Unification

{-

data ((f :: (* -> *) -> *) :**: (g :: (* -> *) -> *)) rep
  = f rep :**: g rep

data Down (f :: (* -> *) -> *) x = Down (f (K1 R x))

antiunif :: (NotElem x prim)
         => SRep prim f (K1 R x) -> SRep prim g (K1 R x)
         -> SRep prim (Down (SRep prim f :**: SRep prim g)) (K1 R x)
antiunif r s = S_D1 (Down (r :**: s))

-}
