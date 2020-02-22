{-# LANGUAGE BangPatterns #-}

module Helper where

import Network.TLS
import Network.TLS.Internal
import qualified Data.ByteString as B
import Data.List
import Data.Maybe

extensionLookup :: ExtensionID -> [ExtensionRaw] -> Maybe B.ByteString
extensionLookup toFind = fmap (\(ExtensionRaw _ content) -> content)
                       . find (\(ExtensionRaw eid _) -> eid == toFind)
{-
extensionID_NegotiatedGroups :: ExtensionID
extensionID_NegotiatedGroups                    = 0xa -- RFC4492bis and TLS 1.3
extensionID_KeyShare :: ExtensionID
extensionID_KeyShare                            = 0x33 -- TLS 1.3


decodeNegotiatedGroups :: B.ByteString -> Maybe [Group]
decodeNegotiatedGroups =
    runGetMaybe (mapMaybe toEnumSafe16 <$> getWords16)

data KeyShare =
   Build_KeyShare Group B.ByteString
   deriving (Show)

kSgroup :: KeyShare -> Group
kSgroup k =
  case k of {
   Build_KeyShare kSgroup0 _ -> kSgroup0}

decodeKeyShare = runGetMaybe $ do
    len <- fromIntegral <$> getWord16
    grps <- getList len getKeyShare
    return (catMaybes grps)

getKeyShare :: Get (Int, Maybe KeyShare)
getKeyShare = do
    g <- getWord16
    l <- fromIntegral <$> getWord16
    key <- getBytes l
    let !len = l + 4
    case toEnumSafe16 g of
      Nothing  -> return (len, Nothing)
      Just grp -> return (len, Just (Build_KeyShare grp key))
-}
supportedGroups' = [P256,P384,P521,X25519]

serverGroups :: ([]) Group
serverGroups =
  supportedGroups'
