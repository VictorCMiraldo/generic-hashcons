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

-- Now, lets do some magic! I'll be combining the
-- free monad and the cofree comonad on the same type!
-- I call these type HolesAnn
data HolesAnn prim phi h a where
  Hole' :: h a -> HolesAnn prim phi h a
  Prim' :: (Elem a prim , Show a , Eq a)
        => a -> HolesAnn prim phi h a
  Roll' :: (NotElem a prim , Generic a)
        => phi a
        -> SRep (HolesAnn prim phi h) (Rep a)
        -> HolesAnn prim phi h a
deriving instance (forall a . Show (h a) , forall a . Show (phi a))
  => Show (HolesAnn prim phi h x)

-- Here are holes with no annotations:

type Holes prim = HolesAnn prim U1

pattern Hole :: h a -> Holes prim h a
pattern Hole x = Hole' x

pattern Prim :: () => (Elem a prim , Show a , Eq a)
             => a -> Holes prim h a
pattern Prim a = Prim' a

pattern Roll :: () => (NotElem a prim , Generic a)
             => SRep (Holes prim h) (Rep a)
             -> Holes prim h a
pattern Roll x = Roll' U1 x
{-# COMPLETE Hole , Prim , Roll #-}

-- Here are plain fixpoints (Holes with no annotations
-- not holes)

type SFix prim = Holes prim V1

pattern SFix :: () => (NotElem a prim , Generic a)
             => SRep (SFix prim) (Rep a)
             -> SFix prim a
pattern SFix x = Roll x
{-# COMPLETE SFix , Prim #-}

-- Here are annotated fixpoints (Holes with annotations
-- but no holes)

type SFixAnn prim phi = HolesAnn prim phi V1

pattern PrimAnn :: () => (Elem a prim , Show a , Eq a)
                => a -> SFixAnn prim phi a
pattern PrimAnn a = Prim' a


pattern SFixAnn :: () => (NotElem a prim , Generic a)
                => phi a
                -> SRep (SFixAnn prim phi) (Rep a)
                -> SFixAnn prim phi a
pattern SFixAnn ann x = Roll' ann x
{-# COMPLETE SFixAnn , PrimAnn #-}

---------------------------------

data OnRec prim f a where
  NRec :: (Elem a prim , Show a , Eq a)
       => a -> OnRec prim f a
  Rec  :: (NotElem a prim)
       => f a -> OnRec prim f a

data WrapRep f a where
  WrapRep :: (Generic a) => f (Rep a) -> WrapRep f a

unfix :: SFixAnn prim phi a
      -> OnRec prim (phi :*: WrapRep (SRep (SFixAnn prim phi))) a
unfix (PrimAnn x)   = NRec x
unfix (SFixAnn a h) = Rec (a :*: WrapRep h)
      
mapOnRecM :: (Monad m)
          => (forall y . f y -> m (g y))
          -> OnRec prim f a -> m (OnRec prim g a)
mapOnRecM f  (Rec  x) = Rec <$> f x
mapOnRecM _f (NRec x) = return (NRec x)

---------------------------------

zipSRep :: SRep w f -> SRep w f -> Maybe (SRep (w :*: w) f)
zipSRep S_U1         S_U1         = return S_U1
zipSRep (S_L1 x)     (S_L1 y)     = S_L1 <$> zipSRep x y
zipSRep (S_R1 x)     (S_R1 y)     = S_R1 <$> zipSRep x y
zipSRep (S_M1 x)     (S_M1 y)     = S_M1 <$> zipSRep x y
zipSRep (x1 :**: x2) (y1 :**: y2) = (:**:) <$> (zipSRep x1 y1)
                                           <*> (zipSRep x2 y2)
zipSRep (S_K1 x)     (S_K1 y)     = return $ S_K1 (x :*: y)
zipSRep _            _            = Nothing

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
        
{-
option:

cataM :: (Monad m)
      => (forall b . (NotElem b prim , Generic b)
            => ann b -> SRep (OnRec prim phi) (Rep b) -> m (phi b))
      -> (forall b . (Elem b prim , Show b , Eq b)
            => b -> m (phi b))
      -> SFixAnn prim ann a
      -> m (phi a)
cataM f g (SFixAnn ann x) = mapRepM () x >>= f ann
cataM _ g (PrimAnn x)     = g x
-}

cataM :: (Monad m)
      => (forall b . (NotElem b prim , Generic b)
            => ann b -> SRep phi (Rep b) -> m (phi b))
      -> (forall b . (Elem b prim , Show b , Eq b)
            => b -> m (phi b))
      -> SFixAnn prim ann a
      -> m (phi a)
cataM f g (SFixAnn ann x) = mapRepM (cataM f g) x >>= f ann
cataM _ g (PrimAnn x)     = g x

getAnn :: (forall b . (Elem b prim , Show b , Eq b)
            => b -> phi b)
       -> SFixAnn prim phi a
       -> phi a
getAnn _   (SFixAnn ann _) = ann
getAnn def (PrimAnn x)     = def x

synthesizeM :: (Monad m)
            => (forall b . Generic b
                  => ann b -> SRep phi (Rep b) -> m (phi b))
            -> (forall b . (Elem b prim , Show b , Eq b)
                  => b -> phi b)
            -> SFixAnn prim ann a
            -> m (SFixAnn prim phi a)
synthesizeM f def = cataM (\ann r -> flip SFixAnn r
                             <$> f ann (mapRep (getAnn def) r))
                        (return . PrimAnn)

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
class (NotElem a prim , Generic a) => Deep prim a where
  dfrom :: a -> SFix prim a
  default dfrom :: (GDeep prim (Rep a))
                => a -> SFix prim a
  dfrom = SFix . gdfrom . from
  
  dto :: SFix prim a -> a
  default dto :: (GDeep prim (Rep a)) => SFix prim a -> a
  dto (SFix x) = to . gdto $ x

-- Your usual suspect; the GDeep typeclass
class GDeep prim f where
  gdfrom :: f x -> SRep (SFix prim) f 
  gdto   :: SRep (SFix prim) f -> f x 

-- And the class that disambiguates primitive types
-- from types in the family. This is completely hidden from
-- the user though
class GDeepAtom prim (isPrim :: Bool) a where
  gdfromAtom  :: Proxy isPrim -> a -> SFix prim a
  gdtoAtom    :: Proxy isPrim -> SFix prim a -> a

instance (NotElem a prim , Deep prim a) => GDeepAtom prim 'False a where
  gdfromAtom _ a = dfrom $ a
  gdtoAtom _   x = dto x

instance (Elem a prim , Show a , Eq a) => GDeepAtom prim 'True a where
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

ex1 , ex2 :: Exp
ex1 = (Add (Var "x") (Add (Lit 4) (Lit 2)))
ex2 = (Add (Var "z") (Lit 42))

dfromPrim :: (Deep Prims a) => a -> SFix Prims a
dfromPrim = dfrom

------------------
-- Holes

uncurry' :: (f x -> g x -> res) -> (f :*: g) x -> res
uncurry' f (x :*: y) = f x y
       
-- anti unification
au :: SFix prim a -> SFix prim a
   -> Holes prim (SFix prim :*: SFix prim) a
au (Prim x) (Prim y)
 | x == y    = Prim x
 | otherwise = Hole (Prim x :*: Prim y)
au x@(SFix rx) y@(SFix ry) =
  case zipSRep rx ry of
    Nothing -> Hole (x :*: y)
    Just r  -> Roll (mapRep (uncurry' au) r)


------------------
-- Annotate with height

heights :: SFix prim a -> SFixAnn prim (Const Int) a
heights = runIdentity . synthesizeM go (const (Const 0))
  where
    go :: U1 b -> SRep (Const Int) (Rep b) -> Identity (Const Int b)
    go _ x = do
      maxi <- alg x
      return (Const (1 + maxi))
    
    alg :: SRep (Const Int) f -> Identity Int
    alg S_U1 = return 0
    alg (S_L1 x) = alg x
    alg (S_R1 x) = alg x
    alg (S_M1 x) = alg x
    alg (x :**: y) = max <$> alg x <*> alg y
    alg (S_K1 (Const x)) = return x
