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
data REP (prim :: [ * ]) f rep :: * -> * where
  REPD1   :: (NotElem a prim)       => f a -> REP prim f (K1 R a) x
  REPK1   :: (Elem a prim , Show a) => a   -> REP prim f (K1 R a) x
  REPU1   :: REP prim f U1 x
  REPM1   :: REP prim f a x -> REP prim f (M1 i c a) x
  REPL1   :: REP prim f a x -> REP prim f (a :+: b) x
  REPR1   :: REP prim f b x -> REP prim f (a :+: b) x 
  REPPair :: REP prim f a x -> REP prim f b x -> REP prim f (a :*: b) x
deriving instance (forall a . Show (f a)) => Show (REP prim f rep x)

-- This is where this is going! :D
data Fix prim a :: * where
  Fix :: (Generic a) => { unFix :: REP prim (Fix prim) (Rep a) x } -> Fix prim a
deriving instance Show (Fix prim a)

-- Converting values to deep representations is easy and follows
-- almost the usual convention; one top level class
-- and one generic version. This time though, we need
-- special treatment on atoms.
class (Generic a) => Deep prim a where
  dfrom :: a -> Fix prim a
  default dfrom :: (GDeep prim (Rep a)) => a -> Fix prim a
  dfrom = Fix . gdfrom . from
  
  dto :: Fix prim a -> a
  default dto :: (GDeep prim (Rep a)) => Fix prim a -> a
  dto (Fix x) = to . gdto $ x

-- Typesyn to make life easier
type FIX prim = REP prim (Fix prim)

-- Your usual suspect; the GDeep typeclass
class GDeep prim f where
  gdfrom :: f x -> FIX prim f x
  gdto   :: FIX prim f x -> f x

-- And the class that disambiguates primitive types
-- from types in the family. This is completely hidden from
-- the user though
class GDeepAtom prim (isPrim :: Bool) a where
  gdfromAtom  :: Proxy isPrim -> a -> FIX prim (K1 R a) x
  gdtoAtom    :: Proxy isPrim -> FIX prim (K1 R a) x -> a

instance (NotElem a prim , Deep prim a) => GDeepAtom prim 'False a where
  gdfromAtom _ a = REPD1 (dfrom a)
  gdtoAtom _ (REPD1 x) = dto x

instance (Elem a prim , Show a) => GDeepAtom prim 'True a where
  gdfromAtom _ a = (REPK1 a)
  gdtoAtom   _ (REPK1 a) = a

-- This ties the recursive knot
instance (GDeepAtom prim (IsElem a prim) a) => GDeep prim (K1 R a) where
  gdfrom (K1 a)  = gdfromAtom (Proxy :: Proxy (IsElem a prim)) a
  gdto   a       = K1 (gdtoAtom (Proxy :: Proxy (IsElem a prim)) a)

-- The rest of the instances are trivial
instance GDeep prim U1 where
  gdfrom U1  = REPU1
  gdto REPU1 = U1

instance (GDeep prim f) => GDeep prim (M1 i c f) where
  gdfrom (M1 x) = REPM1 (gdfrom x)
  gdto (REPM1 x) = M1 (gdto x)

instance (GDeep prim f , GDeep prim g) => GDeep prim (f :*: g) where
  gdfrom (x :*: y) = REPPair (gdfrom x) (gdfrom y)
  gdto (REPPair x y) = (gdto x) :*: (gdto y)

instance (GDeep prim f , GDeep prim g) => GDeep prim (f :+: g) where
  gdfrom (L1 x) = REPL1 (gdfrom x)
  gdfrom (R1 x) = REPR1 (gdfrom x)

  gdto (REPL1 x) = L1 (gdto x)
  gdto (REPR1 x) = R1 (gdto x)


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
