#!/usr/bin/env stack
-- stack --resolver lts-20.04 script
{-# LANGUAGE OverloadedStrings #-}
module Pixelflut (main) where

import qualified Control.Exception as E
import qualified Data.ByteString.Char8 as C
import Network.Socket
import Network.Socket.ByteString (recv, sendAll)

main :: IO ()
main = runTCPClient "127.0.0.1" "3000" $ \s -> do
    fillRect s 0 0 1440 900 "ff0000"

-- fill a rectangular area with a single RRGGBB color
fillRect s originX originY width height color =
    forInt 0 width $ \x ->
        forInt 0 height $ \y ->
            sendString s $ "PX " ++ show (originX + x) ++ " " ++ show (originY + y) ++ " " ++ color ++ "\n"

-- Utility stuff

sendString :: Socket -> String -> IO ()
sendString s str = sendAll s (C.pack str)

forInt :: Int -> Int -> (Int -> IO ()) -> IO ()
forInt a b op
    | a >= b = pure ()
    | otherwise = do
        op a
        forInt (a+1) b op

-- from the "network-run" package.
runTCPClient :: HostName -> ServiceName -> (Socket -> IO a) -> IO a
runTCPClient host port client = withSocketsDo $ do
    addr <- resolve
    E.bracket (open addr) close client
  where
    resolve = do
        let hints = defaultHints { addrSocketType = Stream }
        head <$> getAddrInfo (Just hints) (Just host) (Just port)
    open addr = E.bracketOnError (openSocket addr) close $ \sock -> do
        connect sock $ addrAddress addr
        return sock
