{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module EVM.Patricia where

import Control.Monad.Free
import qualified Data.Map as Map
import EVM.Types 
import EVM.Keccak
import Control.Monad.State
import Data.ByteString (ByteString)
import EVM.Transaction
import qualified Data.ByteString as BS
import Data.Word
import Data.Foldable (toList)
import Data.List(stripPrefix)

import Data.Bits
import Data.Char
import Data.Monoid ((<>))
import qualified Data.Sequence as Seq
import Data.Sequence(Seq)


newtype Nibble = Nibble { wordToNib :: Word8 }
  deriving (Eq)

instance Show Nibble where
  show = (:[]) . intToDigit . num . wordToNib

data KV k v a
  = Put k v a
  | Get k (v -> a)
  deriving (Functor)

newtype DB k v a = DB (Free (KV k v) a)
  deriving (Functor, Applicative, Monad)

insertDB :: k -> v -> DB k v ()
insertDB k v = DB $ liftF $ Put k v ()

lookupDB :: k -> DB k v v
lookupDB k = DB $ liftF $ Get k id

-- Collapses a series of puts and gets down to the monad of your choice
runDB :: Monad m           
      => (k -> v -> m ()) -- ^ The 'put' function for our desired monad
      -> (k -> m v)       -- ^ The 'get' function for the same monad 
      -> DB k v a         -- ^ The puts and gets to execute 
      -> m a
runDB putt gett (DB ops) = go ops
  where
    go (Pure a) = return a 
    go (Free (Put k v next)) = putt k v >> go next
    go (Free (Get k handler)) = gett k >>= go . handler


--Get first and second Nibble from byte
hi, lo :: Word8 -> Nibble
hi b = Nibble $ b `shiftR` 4
lo b = Nibble $ b .&. 0x0f

toByte :: Nibble -> Nibble -> Word8
toByte  (Nibble high) (Nibble low) = high `shift` 4 .|. low

unpackNibbles :: ByteString -> [Nibble]
unpackNibbles bs = BS.unpack bs >>= unpackByte
  where unpackByte b = [hi b, lo b]

--Well-defined for even length lists only (plz dependent types)
packNibbles :: [Nibble] -> ByteString
packNibbles [] = mempty
packNibbles (n1:n2:ns) = BS.singleton (toByte n1 n2) <> packNibbles ns

--function HP from yellow paper
encodePath :: Path -> Bool -> ByteString
encodePath p isTerminal | even (length p) = packNibbles $ Nibble flag : Nibble 0 : p
                        | otherwise       = packNibbles $ Nibble (flag + 1) : p
                     where flag  = if isTerminal then 2 else 0

type Path = [Nibble]

newtype Digest = Digest ByteString
  deriving (Ord, Eq)

instance Show Digest where
  show (Digest bs) = show $ ByteStringS bs

data Ref = Hash Digest | Literal Node
  deriving (Show, Eq)

data Node = Empty
          | Shortcut Path (Either Ref ByteString)
          | Full (Seq Ref) ByteString
  deriving (Show, Eq)

refer :: Ref -> RLP
refer (Hash (Digest d)) = BS d
refer (Literal n)       = rlpNode n

rlpNode :: Node -> RLP
rlpNode Empty = BS mempty
rlpNode (Shortcut path (Right val)) = List [BS $ encodePath path True, BS val]
rlpNode (Shortcut path (Left  ref)) = List [BS (encodePath path False), refer ref]
rlpNode (Full refs val) = List $ toList (fmap refer refs) <> [BS val]

type NodeDB = DB Digest Node

putNode :: Node -> NodeDB Ref
putNode node =
  let bytes = rlpencode $ rlpNode node
      digest = Digest $ word256Bytes $ keccak bytes
  in if BS.length bytes < 32
    then return $ Literal node
    else do
      insertDB digest node 
      return $ Hash digest

getNode :: Ref -> NodeDB Node
getNode (Hash d) = lookupDB d
getNode (Literal n) = return n
            
lookupPath :: Ref -> Path -> NodeDB ByteString
lookupPath root path = getNode root >>= getVal
  where
    getVal Empty = return BS.empty
    getVal (Shortcut nodePath result) = 
      case (stripPrefix nodePath path, result) of
        (Just [], Right value) -> return value
        (Just remaining, Left ref) -> lookupPath ref remaining
        _ -> return BS.empty
    getVal (Full refs val) = case path of
      [] -> return val
      (w:rest) -> lookupPath (refs `Seq.index` (num $ wordToNib w)) rest

emptyRef :: Ref
emptyRef = Literal Empty

emptyRefs :: Seq Ref
emptyRefs = Seq.replicate 16 emptyRef

toFull :: Node -> NodeDB Node
toFull Empty = return $ Full emptyRefs BS.empty
toFull f@(Full _ _) = return f
toFull (Shortcut [] (Left ref)) = getNode ref >>= toFull
toFull (Shortcut [] (Right bs)) = return $ Full emptyRefs bs
toFull (Shortcut (p:ps) val) = do
  ref <- putNode $ Shortcut ps val
  return $ Full (Seq.update (num $ wordToNib p) ref emptyRefs) BS.empty

insertPath :: Node -> Path -> ByteString -> NodeDB Node
insertPath node path bs = (doInsert node path bs) >>= normalize

doInsert :: Node -> Path -> ByteString -> NodeDB Node
doInsert Empty path val = return $ Shortcut path (Right val)
doInsert (Shortcut nPath nVal) path val = let (pre, nSuffix, suffix) = splitPrefix nPath path in
                                          case (nSuffix, suffix, nVal) of
                                            ([], [], Right _)  -> return $ Shortcut pre $ Right val
                                            ([], _, Left ref) -> do
                                              dbnode <- getNode ref
                                              newNode <- insertPath dbnode suffix val
                                              res <- case pre of
                                                [] -> return newNode
                                                p  -> Shortcut p . Left <$> putNode newNode
                                              return res
                                            _ -> do
                                              full <- toFull (Shortcut nSuffix nVal)
                                              newNode <- insertPath full suffix val
                                              res <- case pre of
                                                [] -> return newNode
                                                p  -> Shortcut p . Left <$> putNode newNode
                                              return res
doInsert (Full refs nVal) [] val = return $ Full refs val
doInsert (Full refs nVal) ((Nibble i):ps) val = let ref = refs `Seq.index` (num i) in do
                                                  newRef <- insertRef ref ps val
                                                  return $ Full (Seq.update (num i) newRef refs) nVal

splitPrefix :: Path -> Path -> (Path, Path, Path)
splitPrefix [] b = ([], [], b)
splitPrefix a [] = ([], a, [])
splitPrefix (a:as) (b:bs) | a == b = let (prefix, aSuffix, bSuffix) = splitPrefix as bs
                                     in (a:prefix, aSuffix, bSuffix)
                          | otherwise = ([], a:as, b:bs)

insertRef :: Ref -> Path -> ByteString -> NodeDB Ref
insertRef ref path bs = do
  node <- getNode ref
  newNode <- insertPath node path bs
  putNode newNode

normalize :: Node -> NodeDB Node
normalize Empty = return Empty
normalize (Shortcut path (Left ref)) = getNode ref >>= addPrefix path
normalize (Shortcut _ (Right val)) | BS.null val = return Empty
normalize s@(Shortcut _ _) = return s
normalize (Full refs val) = let nrmlRefs = toList refs
                                nonEmpty = filter (\x -> snd x /= Literal Empty) $ zip [0..] nrmlRefs
                            in case (BS.null val, nonEmpty) of
                                   (True, []) -> return Empty
                                   (True, (w, ref) : []) -> getNode ref >>= addPrefix [lo w]
                                   (False, []) -> return $ Shortcut [] $ Right val
                                   _ -> return $ Full refs val

addPrefix :: Path -> Node -> NodeDB Node
addPrefix [] n = return n
addPrefix _ Empty = return Empty
addPrefix path (Shortcut p v) = return $ Shortcut (path <> p) v
addPrefix path n = Shortcut path . Left <$> putNode n

insert :: Ref -> ByteString -> ByteString -> NodeDB Ref
insert ref key val = insertRef ref (unpackNibbles key) val

lookupIn :: Ref -> ByteString -> NodeDB ByteString
lookupIn ref bs = lookupPath ref $ unpackNibbles bs 

type Trie = StateT Ref NodeDB

runTrie :: DB ByteString ByteString a -> Trie a
runTrie = runDB putDB getDB
  where
    putDB key val = do
      ref <- get
      newRef <- lift $ insert ref key val
      put newRef
    getDB key = do
      ref <- get
      lift $ lookupIn ref key

type MapDB k v a = StateT (Map.Map k v) Maybe a

runMapDB :: Ord k => DB k v a -> MapDB k v a 
runMapDB = runDB putDB getDB
  where
    getDB key = do
      map <- get
      let value = Map.lookup key map
      lift value
    putDB key value = do
      map <- get
      let newMap = Map.insert key value map
      put newMap

test :: [(ByteString, ByteString)] -> Maybe Ref
test inputs =
  let trie = runTrie $ mapM_ insertPair $ inputs
      mapDB = runMapDB $ runStateT trie (Literal Empty)
      result = snd <$> evalStateT mapDB Map.empty
      insertPair (key, value) = insertDB key value
  in result
