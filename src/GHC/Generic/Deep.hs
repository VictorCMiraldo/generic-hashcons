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
import GHC.Generics
import Control.Monad.Identity

----------------------------
-- The Monster

type family IsElem (a :: *) (as :: [ * ]) :: Bool where
  IsElem a (a ': as) = 'True
  IsElem a (b ': as) = IsElem a as
  IsElem a '[]       = 'False

type Elem    a as = IsElem a as ~ 'True
type NotElem a as = IsElem a as ~ 'False

-- A Value of type @REP prim f rep@ represents one layer of
-- rep and, for the atoms of rep that are not elems of
-- the primitive types, some custom data dictated by a functor f.
-- You know where this is going.
infixr 5 :**:
data SRep w f where
  S_U1   ::                          SRep w U1
  S_L1   ::              SRep w f -> SRep w (f :+: g)
  S_R1   ::              SRep w g -> SRep w (f :+: g)
  (:**:) ::  SRep w f -> SRep w g -> SRep w (f :*: g)
  S_K1   ::              w a      -> SRep w (K1 i a)
  S_M1   ::              SRep w f -> SRep w (M1 i t f)
--  S_ST   ::         c => SRep w f -> SRep w (c :=>: f)
deriving instance (forall a. Show (w a)) => Show (SRep w f)

-- Applies f to recursive positions only; Recursive here
-- really is just 'NotElem prims'
data OnRec prim f a where
  Prim :: (Elem a prim , Show a)
       => a -> OnRec prim f a
  Rec  :: (NotElem a prim)
       => f a -> OnRec prim f a

-- Representation with primitive types
type PrimRep prim w = SRep (OnRec prim w)

-- Annotated fixpoints
data SFixAnn prim ann a where
  SFix :: (Generic a)
       => { getAnn :: ann
          , unFix  :: PrimRep prim (SFixAnn prim ann) (Rep a)
          } 
       -> SFixAnn prim ann a

type SFix prim = SFixAnn prim ()
       
{-
-- TODO: spli this type in two; Fix (WithPrim ...)
data SFix prim a where
  Prim :: (Elem a prim , Show a)
       => a -> SFix prim a
  SFix :: (NotElem a prim , Generic a)
       => SRep (SFix prim) (Rep a)
       -> SFix prim a
deriving instance Show (SFix prim a)
-}

---------------------------------

mapRepM :: (Monad m)
        => (forall y . f y -> m (g y))
        -> SRep f rep -> m (SRep g rep)
mapRepM _f (S_U1)   = return S_U1
mapRepM f (S_K1 x)  = S_K1 <$> f x
mapRepM f (S_M1 x)  = S_M1 <$> mapRepM f x
mapRepM f (S_L1 x)  = S_L1 <$> mapRepM f x
mapRepM f (S_R1 x)  = S_R1 <$> mapRepM f x
mapRepM f (x :**: y)
  = (:**:) <$> mapRepM f x <*> mapRepM f y

mapRep :: (forall y . f y -> g y)
       -> SRep f rep -> SRep g rep
mapRep f = runIdentity . mapRepM (return . f)

mapOnRecM :: (Monad m)
          => (forall y . f y -> m (g y))
          -> OnRec prim f a -> m (OnRec prim g a)
mapOnRecM f  (Rec  x) = Rec <$> f x
mapOnRecM _f (Prim x) = return (Prim x)

        
{-
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
-}


----------------------------------


data ElemPrf a as where
  EP_Yes :: Elem a as    => ElemPrf a as
  EP_No  :: NotElem a as => ElemPrf a as

class DecideElem a as where
  isElem :: ElemPrf a as

instance DecideElem a '[] where
  isElem = EP_No

instance {-# OVERLAPPING #-} DecideElem a (a ': as) where
  isElem = EP_Yes

instance {-# OVERLAPPABLE #-}
    (DecideElem a as) => DecideElem a (b ': as) where
  isElem = isElem

-- Converting values to deep representations is easy and follows
-- almost the usual convention; one top level class
-- and one generic version. This time though, we need
-- special treatment on atoms.
class (Generic a) => Deep prim a where
  dfrom :: a -> SFix prim a
  default dfrom :: (GDeep prim (Rep a))
                => a -> SFix prim a
  dfrom = SFix () . gdfrom . from
  
  dto :: SFix prim a -> a
  default dto :: (GDeep prim (Rep a)) => SFix prim a -> a
  dto (SFix _ x) = to . gdto $ x

-- Your usual suspect; the GDeep typeclass
class GDeep prim f where
  gdfrom :: f x -> PrimRep prim (SFix prim) f 
  gdto   :: PrimRep prim (SFix prim) f -> f x 

-- And the class that disambiguates primitive types
-- from types in the family. This is completely hidden from
-- the user though
class GDeepAtom prim (isPrim :: Bool) a where
  gdfromAtom  :: Proxy isPrim -> a -> OnRec prim (SFix prim) a
  gdtoAtom    :: Proxy isPrim -> OnRec prim (SFix prim) a -> a

instance (NotElem a prim , Deep prim a) => GDeepAtom prim 'False a where
  gdfromAtom _ a       = Rec . dfrom $ a
  gdtoAtom _   (Rec x) = dto x

instance (Elem a prim , Show a) => GDeepAtom prim 'True a where
  gdfromAtom _ a = Prim a
  gdtoAtom   _ (Prim a) = a

-- This ties the recursive knot
instance (GDeepAtom prim (IsElem a prim) a) => GDeep prim (K1 R a) where
  gdfrom (K1 a)   = S_K1 (gdfromAtom (Proxy :: Proxy (IsElem a prim)) a)
  gdto   (S_K1 a) = K1 (gdtoAtom (Proxy :: Proxy (IsElem a prim)) a)

-- The rest of the instances are trivial
instance GDeep prim U1 where
  gdfrom U1  = S_U1
  gdto S_U1 = U1

instance (GDeep prim f) => GDeep prim (M1 i c f) where
  gdfrom (M1 x) = S_M1 (gdfrom x)
  gdto (S_M1 x) = M1 (gdto x)

instance (GDeep prim f , GDeep prim g) => GDeep prim (f :*: g) where
  gdfrom (x :*: y) = (gdfrom x) :**: (gdfrom y)
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


dfromPrim :: (Deep Prims a) => a -> SFix Prims a
dfromPrim = dfrom
