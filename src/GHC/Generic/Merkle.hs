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

data Dig1 x = Dig1 Digest

data Dig rep :: * -> * where
  DigD1 :: Digest -> Dig (K1 R a) x
  DigK1 :: (Show a) => a -> Dig (K1 R a) x
  DigM1 :: Dig f x  -> Dig (M1 i c f) x
  DigU1 :: Dig U1 x
  DigPair :: Dig f x -> Dig g x -> Dig (f :*: g) x
  DigL1 :: Dig f x ->  Dig (f :+: g) x
  DigR1 :: Dig g x ->  Dig (f :+: g) x 

deriving instance Show (Dig rep x)


data ExRep where
  ExRep :: (Generic a)
        => Proxy a -> Dig (Rep a) x -> ExRep

instance Show ExRep where
  show (ExRep _ x) = show x

type HashConsed
  = M.Map Digest ExRep

class HashCons a where
  hashCons :: a -> (Digest , HashConsed)
  default hashCons :: (Generic a , GHashCons (Rep a)
                      )
                   => a -> (Digest , HashConsed)
  hashCons a = let (digA , m) = ghashCons (from a)
                   root       = ghashDig (Proxy :: Proxy (Rep a)) digA
                in (root , M.insert root (ExRep (Proxy :: Proxy a) digA) m)

class GHashCons rep where
  ghashDig  :: Proxy rep -> Dig rep x -> Digest
  ghashCons :: rep x -> (Dig rep x , HashConsed)

instance {-# OVERLAPPING #-} GHashCons (K1 R Int) where
  ghashDig _ (DigK1 i) = hashStr (show i)
  ghashCons (K1 i) = (DigK1 i , M.empty)
  
instance {-# OVERLAPPABLE #-} (HashCons a)
    => GHashCons (K1 R a) where
  ghashDig _ (DigD1 d) = d
  ghashCons (K1 a) =
    let (root , m) = hashCons a
     in (DigD1 root , m)

instance GHashCons U1 where
  ghashDig  _ DigU1 = hashStr "U1"
  ghashCons   U1 = (DigU1 , M.empty)

instance (GHashCons f , GHashCons g)
    => GHashCons (f :*: g) where
  ghashDig _ (DigPair pf pg) = digestConcat
    [ ghashDig (Proxy :: Proxy f) pf
    , ghashDig (Proxy :: Proxy g) pg
    ]

  ghashCons (pf :*: pg)
    = let (pf' , mf) = ghashCons pf
          (pg' , mg) = ghashCons pg
       in (DigPair pf' pg' , M.union mf mg)

instance (GHashCons f , GHashCons g)
    => GHashCons (f :+: g) where
  ghashDig _ (DigL1 f) = ghashDig (Proxy :: Proxy f) f
  ghashDig _ (DigR1 g) = ghashDig (Proxy :: Proxy g) g

  ghashCons (L1 f) =
    let (dp , m) = ghashCons f
     in (DigL1 dp , m)
  ghashCons (R1 f) =
    let (dp , m) = ghashCons f
     in (DigR1 dp , m)
  

instance (KnownSymbol dnn , GHashCons p)
    => GHashCons (D1 ('MetaData dn dnn m f) p) where
  ghashDig _ (DigM1 p) =
    let hp  = ghashDig (Proxy :: Proxy p) p
     in digestSalt (symbolVal (Proxy :: Proxy dnn)) hp

  ghashCons (M1 p) =
    let (dp , m) = ghashCons p
     in (DigM1 dp , m)

instance (KnownSymbol cn , GHashCons p)
    => GHashCons (C1 ('MetaCons cn m f) p) where
  ghashDig _ (DigM1 p) =
    let hp  = ghashDig (Proxy :: Proxy p) p
     in digestSalt (symbolVal (Proxy :: Proxy cn)) hp

  ghashCons (M1 p) =
    let (dp , m) = ghashCons p
     in (DigM1 dp , m)

instance (GHashCons p)
    => GHashCons (S1 s p) where
  ghashDig _ (DigM1 p) = ghashDig (Proxy :: Proxy p) p
  ghashCons (M1 p) =
    let (dp , m) = ghashCons p
     in (DigM1 dp , m)


----------------------------

data BinT
  = Bin BinT BinT
  | Leaf Int
  | Other UnT
  deriving (Eq , Show , Generic)

data UnT
  = ZT Int
  | ST BinT
  deriving (Eq , Show , Generic)

instance HashCons BinT
instance HashCons UnT

v = Bin (Leaf 10) (Other (ZT 10))
                      


