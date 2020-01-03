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
module GHC.Generics.Holes where

import Data.Proxy
import GHC.Generics
import GHC.TypeLits

import Control.Arrow (first , (&&&), (***))

import Data.Word (Word8,Word64)
import Data.Bits
import Data.List (splitAt,foldl')
import qualified Data.ByteString        as BS
import qualified Data.ByteString.Char8  as BS8
import qualified Data.ByteArray         as BA
import qualified Data.ByteArray.Mapping as BA

import qualified Crypto.Hash            as Hash
import qualified Crypto.Hash.Algorithms as Hash (Blake2s_256)

import qualified Data.Map as M

import Unsafe.Coerce

-- |Our digests come from Blake2s_256 
newtype Digest
  = Digest { getDigest :: Hash.Digest Hash.Blake2s_256 }
  deriving (Eq , Show, Ord)

-- |Unpacks a digest into a list of Word64.
toW64s :: Digest -> [Word64]
toW64s = map combine . chunksOf 8 . BA.unpack . getDigest
  where
    chunksOf n l
      | length l <= n = [l]
      | otherwise     = let (h , t) = splitAt n l
                         in h : chunksOf n t

    -- precondition: length must be 8!!!
    combine :: [Word8] -> Word64
    combine = foldl' (\acu (n , next)
                       -> shiftL (fromIntegral next) (8*n) .|. acu) 0
            . zip [0,8,16,24,32,40,48,56]
    
-- |Auxiliar hash function with the correct types instantiated.
hash :: BS.ByteString -> Digest
hash = Digest . Hash.hash

-- |Auxiliar hash functions for strings
hashStr :: String -> Digest
hashStr = hash . BS8.pack

-- |Concatenates digests together and hashes the result.
digestConcat :: [Digest] -> Digest
digestConcat = hash . BA.concat . map getDigest

digestSalt :: String -> Digest -> Digest
digestSalt str d = digestConcat [hashStr str , d]

----------------------------
-- The Monster

type family IsElem (a :: *) (as :: [ * ]) :: Bool where
  IsElem a (a ': as) = 'True
  IsElem a (b ': as) = IsElem a as
  IsElem a '[]       = 'False

type Elem    a as = IsElem a as ~ 'True
type NotElem a as = IsElem a as ~ 'False

-- A Value of type @Dig prim rep@ represents one layer of
-- rep and, for the atoms of rep that are not elems of
-- the primitive types, a hash pointer.
data Dig (prim :: [ * ]) rep :: * -> * where
  DigD1   :: (NotElem a prim)       => Digest -> Dig prim (K1 R a) x
  DigK1   :: (Elem a prim , Show a) => a      -> Dig prim (K1 R a) x
  DigU1   :: Dig prim U1 x
  DigM1   :: Dig prim f x -> Dig prim (M1 i c f) x
  DigL1   :: Dig prim f x -> Dig prim (f :+: g) x
  DigR1   :: Dig prim g x -> Dig prim (f :+: g) x 
  DigPair :: Dig prim f x -> Dig prim g x -> Dig prim (f :*: g) x
deriving instance Show (Dig prim rep x)

-- Wrap it in an existential
data ExRep prim where
  ExRep :: (Generic a)
        => Proxy a -> Dig prim (Rep a) x -> ExRep prim

instance Show (ExRep prim) where
  show (ExRep _ x) = show x

-- And define a hash-consed value to be a map from
-- digest into existential rep.
type HashConsed prim
  = M.Map Digest (ExRep prim)

-- HashConsing then consists in traversing the
-- value; returning the digest of the root and
-- a database of hashconsed subtrees!
--
-- TODO: This will be better in a state monad; where
-- we dont need to do M.unions on products
class HashCons prim a where
  hashCons :: a -> (Digest , HashConsed prim)
  default hashCons :: (Generic a , GHashCons prim (Rep a)
                      )
                   => a -> (Digest , HashConsed prim)
  hashCons a = let (digA , m) = ghashCons (from a)
                   root       = ghashDig (Proxy :: Proxy (Rep a)) digA
                in (root , M.insert root (ExRep (Proxy :: Proxy a) digA) m)

-- The usual /default signature' trick for GHC generics with a twist.
-- While we traverse down the structure of the generic type,
-- we construct a @Dig prim rep x@.
class GHashCons prim rep where
  ghashDig  :: Proxy rep -> Dig prim rep x -> Digest
  ghashCons :: rep x -> (Dig prim rep x , HashConsed prim)

-- When we reach a @K1 R a@, we must know whether this
-- type @a@ is a primitive type or not. In case it is, we
-- compute its digest and keep its value there.
-- In case its not, we use the 'HashCons' instance; which
-- inserts a value in the database.
class GHashConsK1 prim (isPrim :: Bool) a where
  ghashDigK1  :: Proxy isPrim -> Dig prim (K1 R a) x -> Digest
  ghashConsK1 :: Proxy isPrim -> (K1 R a) x -> (Dig prim (K1 R a) x , HashConsed prim)

instance (Show a , Elem a prim) => GHashConsK1 prim 'True a where
  ghashDigK1 _  (DigK1 i) = hashStr (show i)
  ghashConsK1 _ (K1 i)    = (DigK1 i , M.empty)

instance (NotElem a prim , HashCons prim a) => GHashConsK1 prim 'False a where
  ghashDigK1 _ (DigD1 d) = d
  ghashConsK1 _ (K1 a)   = first DigD1 $ hashCons a

-- And this is where we decide whether a is primitive or not.
-- Old trick, but fancy as hell! :D
instance (GHashConsK1 prim (IsElem a prim) a) => GHashCons prim (K1 R a) where
  ghashDig _ = ghashDigK1  (Proxy :: Proxy (IsElem a prim))
  ghashCons  = ghashConsK1 (Proxy :: Proxy (IsElem a prim))

instance GHashCons prim U1 where
  ghashDig  _ DigU1 = hashStr "U1"
  ghashCons   U1    = (DigU1 , M.empty)

instance (GHashCons prim f , GHashCons prim g)
    => GHashCons prim (f :*: g) where
  ghashDig _ (DigPair pf pg) = digestConcat
    [ ghashDig (Proxy :: Proxy f) pf
    , ghashDig (Proxy :: Proxy g) pg
    ]

  ghashCons (pf :*: pg)
    = let (pf' , mf) = ghashCons pf
          (pg' , mg) = ghashCons pg
       in (DigPair pf' pg' , M.union mf mg)

instance (GHashCons prim f , GHashCons prim g)
    => GHashCons prim (f :+: g) where
  ghashDig _ (DigL1 f) = ghashDig (Proxy :: Proxy f) f
  ghashDig _ (DigR1 g) = ghashDig (Proxy :: Proxy g) g

  ghashCons (L1 f) = first DigL1 $ ghashCons f
  ghashCons (R1 g) = first DigR1 $ ghashCons g

instance (KnownSymbol dnn , GHashCons prim p)
    => GHashCons prim (D1 ('MetaData dn dnn m f) p) where
  ghashDig _ (DigM1 p) =
    let hp  = ghashDig (Proxy :: Proxy p) p
     in digestSalt (symbolVal (Proxy :: Proxy dnn)) hp

  ghashCons (M1 p) = first DigM1 $ ghashCons p

instance (KnownSymbol cn , GHashCons prim p)
    => GHashCons prim (C1 ('MetaCons cn m f) p) where
  ghashDig _ (DigM1 p) =
    let hp  = ghashDig (Proxy :: Proxy p) p
     in digestSalt (symbolVal (Proxy :: Proxy cn)) hp

  ghashCons (M1 p) = first DigM1 $ ghashCons p

instance (GHashCons prim p)
    => GHashCons prim (S1 s p) where
  ghashDig _ (DigM1 p) = ghashDig (Proxy :: Proxy p) p
  ghashCons (M1 p) = first DigM1 $ ghashCons p

----------------------------
-- Simple test:

data BinT
  = Bin BinT BinT
  | Leaf Bool
  | Other UnT
  deriving (Eq , Show , Generic)

data UnT
  = ZT Int
  | ST BinT
  deriving (Eq , Show , Generic)

type Prims = '[ Int , Bool , Float ]

instance HashCons Prims BinT
instance HashCons Prims UnT

v :: BinT
v = Bin (Leaf False) (Other (ZT 10))

hcp :: HashCons Prims a => a -> (Digest , HashConsed Prims)
hcp = hashCons

v' = let (root , m) = hcp v
      in hashUncons (Proxy :: Proxy BinT) root m

----------------------------------
-- Reconstructing a value?
--
-- Possible with the help of one unsafeCoerce
-- to let GHC rest that we know what we are doing

dig2rep :: Dig prim f x -> HashConsed prim -> Maybe (f x)
dig2rep (DigK1 x) _  = return (K1 x)
dig2rep DigU1     _  = return U1
dig2rep (DigD1 d) db = K1 <$> hashUncons Proxy d db
dig2rep (DigM1 m) db = M1 <$> dig2rep m db
dig2rep (DigL1 x) db = L1 <$> dig2rep x db
dig2rep (DigR1 y) db = R1 <$> dig2rep y db
dig2rep (DigPair x y) db = (:*:) <$> dig2rep x db <*> dig2rep y db

proxyTo :: (Generic a) => Proxy a -> Rep a x -> a
proxyTo _ = to

hashUncons :: Proxy a -> Digest -> HashConsed prim -> Maybe a
hashUncons _ root db = do
  (ExRep ty' r) <- M.lookup root db
  aux <- proxyTo ty' <$> dig2rep r db
  return $ unsafeCoerce aux -- how do we like this unsafeCoerce here? haha
