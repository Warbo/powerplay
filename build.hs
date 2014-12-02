#!/usr/bin/runghc
import Control.Monad
import Data.Char
import Data.List
import Data.List.Split
import Data.Graph
import qualified Data.Map as Map
import System.Process

on c a = readProcess c a ""

run c = c `on` []

coqdep f = "coqdep" `on` ["-I", ".", f]

coqc f = "coqc" `on` [f]

coqFiles :: IO [String]
coqFiles = let c = "find" `on` [".", "-name", "*.v"]
               f = return . map stripPath . filter noHash . lines in
               c >>= f

extractDeps :: String -> [String]
extractDeps s = case splitOn ":" s of
                   ns:ds:_ -> map (stripVO . stripPath) $ words ds

deps :: [String] -> IO (Map.Map String [String])
deps [] = return Map.empty
deps (f:fs) = do l   <- coqdep f
                 let ds = filter (f /=) $ extractDeps l
                 dss <- deps fs
                 return $ Map.union (Map.singleton f ds) dss

isV = ("v." ==) . take 2 . reverse

noHash = not . ('#' `elem`)

stripPath x = case x of
                '.':'/':y -> y
                _         -> x

stripVO x = case reverse x of
              'o':'v':'.':x' -> init x
              _              -> x

dropKeys :: (Ord k) => Map.Map k v -> [k] -> Map.Map k v
dropKeys = foldr Map.delete

removeFromElems :: (Eq v) => Map.Map k [v] -> [v] -> Map.Map k [v]
removeFromElems m []     = m
removeFromElems m (v:vs) = removeFromElems (Map.map (filter (/= v)) m) vs

removeFiles m vs = removeFromElems (dropKeys m vs) vs

ordered :: (Ord k, Show k) => Map.Map k [k] -> [k]
ordered m = let fs = Map.keys $ Map.filter (== []) m
                m' = dropKeys m fs in
            case Map.size m of
              0 -> []
              _ -> case fs of
                     [] -> error $ "Cycles: " ++ show m
                     _  -> fs ++ ordered (removeFiles m fs)

main = do fs <- coqFiles
          ds <- deps fs
          sequence_ $ map coqc $ ordered ds
