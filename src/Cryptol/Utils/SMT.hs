-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Cryptol.Utils.SMT
  ( Solver(..)
  , SolverExe(..)
  , SatResult(..)
  , Value(..)
  , cvc4, yices
  , execSolver
  ) where

import System.Process
import System.IO
import System.Exit(ExitCode)
import SMTLib2
import Data.List(unfoldr)
import Text.Read(readMaybe)
import Control.Concurrent(forkIO)
import Control.Monad(forever)
import qualified Control.Exception as X
import Data.Char(isSpace)
import Data.IORef



data Solver = Solver
  { solverDeclareFun  :: Name -> [Type] -> Type -> IO ()
  , solverAssert      :: Expr -> IO ()
  , solverPush        :: IO ()
  , solverPop         :: IO ()
  , solverCheckSat    :: IO SatResult
  , solverGetValue    :: [Ident] -> IO [Value]
  , solverExit        :: IO ExitCode
  }

data SatResult = Unknown | Unsat | Sat
                 deriving (Eq,Show)

data Value     = ValInteger Integer
               | ValBool Bool
               | ValOther String    -- Just a catch-all
                 deriving (Eq,Show)
                  -- XXX: Others

data SolverExe = SolverExe
  { solverExe    :: FilePath
  , solverParams :: [String]
  }

cvc4 :: SolverExe
cvc4 = SolverExe
  { solverExe    = "cvc4"
  , solverParams = ["--lang=smtlib2", "-m"]
  }

yices :: SolverExe
yices = SolverExe
  { solverExe = "yices-smt2"
  , solverParams = ["--incremental", "--interactive"]
  }

-- XXX: This does not do proper error handling
execSolver :: SolverExe -> Name -> IO Solver
execSolver opts logic =
  do (hIn,hOut,hErr,h) <- runInteractiveProcess (solverExe opts)
                                                (solverParams opts)
                                                Nothing Nothing

     -- XXX: Ignore errors for now
     _ <- forkIO $ do forever (hGetLine hErr)
                        `X.catch` \X.SomeException {} -> return ()

     -- XXX: No error checking, just stops on error!
     getNextResp <- sexprs hOut


     let cmd' c = do hPutStrLn hIn (show (pp c))
                     hFlush hIn

         cmd c k = do cmd' c
                      mb <- getNextResp
                      case mb of
                        Nothing -> fail "No response!"
                        Just s  -> k s

         success (Atom "success") = return ()
         success err              = fail (show err) -- XXX

         basicCmd c = cmd c success

     basicCmd $ CmdSetOption (OptPrintSuccess True)
     basicCmd $ CmdSetLogic logic

     return Solver
        { solverDeclareFun = \f ts t -> basicCmd $ CmdDeclareFun f ts t
        , solverAssert     = \e -> basicCmd $ CmdAssert e
        , solverPush       = basicCmd $ CmdPush 1
        , solverPop        = basicCmd $ CmdPop 1
        , solverCheckSat =
            do cmd CmdCheckSat $ \l ->
                 case l of
                   Atom "sat"     -> return Sat
                   Atom "unsat"   -> return Unsat
                   Atom "unknown" -> return Unknown
                   _              -> fail $ "Bad response: " ++ show l

        -- XXX: No error handling
        , solverGetValue = \xs ->
            cmd (CmdGetValue [ app x [] | x <- xs ]) $ \vals ->
                 return $ map snd $ parseValues vals


        , solverExit = do cmd' CmdExit
                          waitForProcess h
        }

  where

  -- XXX: Better parser
  parseValues (List ans) =
     [ (key, parseVal val) | List [ Atom key, Atom val ] <- ans ]
  parseValues val = error ("Failed to understand: " ++ show val)

  parseVal "true"  = ValBool True
  parseVal "false" = ValBool False
  parseVal n | Just i <- readMaybe n = ValInteger i
  parseVal x = ValOther x

--------------------------------------------------------------------------------

sexprs :: Handle -> IO (IO (Maybe SExpr))
sexprs h =
  do ref <- newIORef =<< (unfoldr parseSExpr `fmap` hGetContents h)
     return $
       atomicModifyIORef ref $ \xs ->
          case xs of
            []     -> (xs, Nothing)
            y : ys -> (ys, Just y)


data SExpr = Atom String | List [ SExpr ]
              deriving Show

parseSExpr :: String -> Maybe (SExpr, String)
parseSExpr (c : more) | isSpace c = parseSExpr more
parseSExpr ('(' : more) = do (xs,more1) <- list more
                             return (List xs, more1)
  where
  list (c : txt) | isSpace c = list txt
  list (')' : txt) = return ([], txt)
  list txt         = do (v,txt1) <- parseSExpr txt
                        (vs,txt2) <- list txt1
                        return (v:vs, txt2)
parseSExpr txt          = case break end txt of
                            (as,bs) | not (null as) -> Just (Atom as, bs)
                            _ -> Nothing
  where end x = x == ')' || isSpace x
--------------------------------------------------------------------------------


