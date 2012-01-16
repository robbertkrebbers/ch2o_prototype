{-# OPTIONS_GHC -Wall #-}

import Util
import RLValues
import CSemantics
import CMonads
import Parser

import Prelude
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Error
import Control.Applicative
import Language.C hiding (Error)
import System
import System.Random
import System.Exit
import System.IO
import System.Console.GetOpt

parseString :: String -> Either String CTranslUnit
parseString str = case execParser_ translUnitP (inputStreamFromString str) (initPos "") of
  Left e  -> throwError (show e)
  Right s -> return s

parseStringNice :: String -> CTranslationUnit ()
parseStringNice str = case parseString str of
  Left e  -> error e
  Right c -> (\_ -> ()) <$> c
  
parseCMonad :: CMonad m => String -> Either String (m RVal, CEnv, CState)
parseCMonad str = do
  tu <- parseString str
  case runPreCMonad_ (cTranslUnitToProg tu) of
    (Left e, _)    -> throwError ("transformation error: " ++ e)
    (Right _, pst) -> do
      _ <- try "main not found" (Map.lookup "main" (pFuns pst))
      (cenv,state) <- toCState pst
      return (evalFun "main", cenv, state)

evalString :: String -> Either String [Maybe RVal]
evalString str = do
  (m, cenv, state) <- parseCMonad str
  return (fst <$> runCList m cenv state)

evalStringSet :: String -> Either String (Set.Set (Maybe RVal))
evalStringSet str = do
  (m, cenv, state) <- parseCMonad str
  return (Set.map fst (runCSet m cenv state))

evalStringRandom :: Int -> String -> IO [Maybe RVal]
evalStringRandom n str = case parseCMonad str of
  Left e                 -> hPutStrLn stderr e >> exitFailure
  Right (m, cenv, state) -> do
    g <- getStdGen
    return (f n g)
   where 
    f 0 _ = []
    f x g = let (g',g'') = split g in fst (runCRandom m cenv state g'):f (x - 1) g''

data Options = Options { 
  optInput :: IO String,
  optOutput :: String -> IO ()
}

defaultOptions :: Options
defaultOptions = Options { 
  optInput = getContents,
  optOutput = putStr
}
  
options :: [OptDescr (Options -> IO Options)]
options = [
  Option ['i'] ["input"] (ReqArg (\arg opt -> 
    return opt { optInput = readFile arg }) "FILE") "input file, stdin if omitted",
  Option ['o'] ["output"] (ReqArg (\arg opt -> 
    return opt { optOutput = writeFile arg }) "FILE") "output file, stdout if omitted",
  Option ['h'] ["help"] (NoArg (\_ -> 
    usage >> exitSuccess)) "display this help page"]
    
usage :: IO ()
usage = do
  prg <- getProgName
  hPutStrLn stderr $ usageInfo ("Usage: " ++ prg ++" [OPTION...]") options
            
main :: IO ()
main = do
  argv <- getArgs
  case getOpt Permute options argv of
   (actions,_,[]) -> do
     opts <- foldl (>>=) (return defaultOptions) actions
     input <- optInput opts
     case evalString input of
       Left err -> hPutStrLn stderr err >> exitFailure
       Right v -> optOutput opts (show v)
   (_,_,errors) -> do
     hPutStrLn stderr $ concat errors
     usage
     exitFailure

