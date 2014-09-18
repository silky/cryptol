-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards #-}

module Cryptol.Symbolic where

import Control.Applicative
import Control.Monad (replicateM, when, zipWithM)
import Control.Monad.IO.Class
import Data.List (transpose)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid (Monoid(..))
import Data.Traversable (traverse)
import qualified Control.Exception as X

import qualified Data.SBV as SBV
import Data.SBV.Provers.Prover hiding (verbose)
import Data.SBV.BitVectors.Data hiding (verbose)

import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Env as M

import Cryptol.Symbolic.BitVector
import Cryptol.Symbolic.Prims
import Cryptol.Symbolic.Value

import qualified Cryptol.Eval.Value as Eval
import qualified Cryptol.Eval.Type (evalType)
import qualified Cryptol.Eval.Env (EvalEnv(..))
import Cryptol.TypeCheck.AST
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)

-- External interface ----------------------------------------------------------

proverConfigs :: [(String, SBV.SMTConfig)]
proverConfigs =
  [ ("cvc4"     , SBV.cvc4     )
  , ("yices"    , SBV.yices    )
  , ("z3"       , SBV.z3       )
  , ("boolector", SBV.boolector)
  , ("mathsat"  , SBV.mathSAT  )
  , ("offline"  , SBV.defaultSMTCfg )
  ]

proverNames :: [String]
proverNames = map fst proverConfigs

lookupProver :: String -> SBV.SMTConfig
lookupProver s =
  case lookup s proverConfigs of
    Just cfg -> cfg
    -- should be caught by UI for setting prover user variable
    Nothing  -> panic "Cryptol.Symbolic" [ "invalid prover: " ++ s ]

-- | A prover result is either an error message, or potentially a
-- counterexample or satisfying assignment.
type ProverResult = Either String (Either [Type] [(Type, Expr, Eval.Value)])

satSMTResult :: SatResult -> SMTResult
satSMTResult (SatResult r) = r

thmSMTResult :: ThmResult -> SMTResult
thmSMTResult (ThmResult r) = r

-- | TODO: Clean up ProverResult; it has grown too much to be a proper datatype!
sat :: Bool
    -> (String, Bool, Bool)
    -> [DeclGroup]
    -> Maybe FilePath
    -> (Expr, Schema)
    -> M.ModuleCmd ProverResult -- ^ Returns a list of arguments for a satisfying assignment
sat isSat (proverName, useSolverIte, verbose) edecls mfile (expr, schema) = protectStack useSolverIte $ \modEnv -> do
  let extDgs = allDeclGroups modEnv ++ edecls
  let prover = (lookupProver proverName) { smtFile = mfile }
  let tyFn = if isSat then existsFinType else forallFinType
  let runFn | isSat = fmap satSMTResult . SBV.satWith prover
            | otherwise = fmap thmSMTResult . SBV.proveWith prover
  case predArgTypes schema of
    Left msg -> return (Right (Left msg, modEnv), [])
    Right ts -> do when verbose $ putStrLn "Simulating..."
                   let env = evalDecls (emptyEnv useSolverIte) extDgs
                   let v = evalExpr env expr
                   result <- runFn $ do
                               args <- mapM tyFn ts
                               b <- return $! fromVBit (foldl fromVFun v args)
                               when verbose $ liftIO $ putStrLn $
                                 "Calling " ++ proverName ++ "..."
                               return b
                   esatexprs <- case result of
                     SBV.Satisfiable {} ->
                       let Right (_, cws) = SBV.getModel result
                           (vs, _) = parseValues ts cws
                           sattys = unFinType <$> ts
                           satexprs = zipWithM Eval.toExpr sattys vs
                       in case zip3 sattys <$> satexprs <*> pure vs of
                         Nothing ->
                           panic "Cryptol.Symbolic.sat"
                             [ "unable to make assignment into expression" ]
                         Just tevs -> return $ Right (Right tevs)
                     SBV.Unsatisfiable {} ->
                       return $ Right (Left (unFinType <$> ts))
                     _ -> return $ Left (rshow result)
                            where rshow | isSat = show . SatResult
                                        | otherwise = show . ThmResult
                   return (Right (esatexprs, modEnv), [])

satOffline :: Bool
           -> Bool
           -> Bool
           -> [DeclGroup]
           -> Maybe FilePath
           -> (Expr, Schema)
           -> M.ModuleCmd (Either String ())
satOffline isSat useIte vrb edecls mfile (expr, schema) =
  protectStack useIte $ \modEnv -> do
    let extDgs = allDeclGroups modEnv ++ edecls
    let tyFn = if isSat then existsFinType else forallFinType
    let filename = fromMaybe "standard output" mfile
    case predArgTypes schema of
      Left msg -> return (Right (Left msg, modEnv), [])
      Right ts ->
        do when vrb $ putStrLn "Simulating..."
           let env = evalDecls (emptyEnv useIte) extDgs
           let v = evalExpr env expr
           let satWord | isSat = "satisfiability"
                       | otherwise = "validity"
           txt <- compileToSMTLib True isSat $ do
                    args <- mapM tyFn ts
                    b <- return $! fromVBit (foldl fromVFun v args)
                    liftIO $ putStrLn $
                      "Writing to SMT-Lib file " ++ filename ++ "..."
                    return b
           liftIO $ putStrLn $
             "To determine the " ++ satWord ++
             " of the expression, use an external SMT solver."
           case mfile of
             Just path -> writeFile path txt
             Nothing -> putStr txt
           return (Right (Right (), modEnv), [])

protectStack :: Bool
             -> M.ModuleCmd (Either String a)
             -> M.ModuleCmd (Either String a)
protectStack usingITE cmd modEnv = X.catchJust isOverflow (cmd modEnv) handler
  where isOverflow X.StackOverflow = Just ()
        isOverflow _               = Nothing
        msg | usingITE  = msgBase
            | otherwise = msgBase ++ "\n" ++
                          "Using ':set iteSolver=on' might help."
        msgBase = "Symbolic evaluation failed to terminate."
        handler () = return (Right (Left msg, modEnv), [])

parseValues :: [FinType] -> [SBV.CW] -> ([Eval.Value], [SBV.CW])
parseValues [] cws = ([], cws)
parseValues (t : ts) cws = (v : vs, cws'')
  where (v, cws') = parseValue t cws
        (vs, cws'') = parseValues ts cws'

parseValue :: FinType -> [SBV.CW] -> (Eval.Value, [SBV.CW])
parseValue FTBit [] = panic "Cryptol.Symbolic.parseValue" [ "empty FTBit" ]
parseValue FTBit (cw : cws) = (Eval.VBit (SBV.fromCW cw), cws)
parseValue (FTSeq 0 FTBit) cws = (Eval.VWord (Eval.BV 0 0), cws)
parseValue (FTSeq n FTBit) (cw : cws)
  | SBV.isBounded cw = (Eval.VWord (Eval.BV (toInteger n) (SBV.fromCW cw)), cws)
  | otherwise = panic "Cryptol.Symbolic.parseValue" [ "unbounded concrete word" ]
parseValue (FTSeq n FTBit) cws = (Eval.VSeq True vs, cws')
  where (vs, cws') = parseValues (replicate n FTBit) cws
parseValue (FTSeq n t) cws = (Eval.VSeq False vs, cws')
  where (vs, cws') = parseValues (replicate n t) cws
parseValue (FTTuple ts) cws = (Eval.VTuple vs, cws')
  where (vs, cws') = parseValues ts cws
parseValue (FTRecord fs) cws = (Eval.VRecord (zip ns vs), cws')
  where (ns, ts) = unzip fs
        (vs, cws') = parseValues ts cws

allDeclGroups :: M.ModuleEnv -> [DeclGroup]
allDeclGroups = concatMap mDecls . M.loadedModules

data FinType
    = FTBit
    | FTSeq Int FinType
    | FTTuple [FinType]
    | FTRecord [(Name, FinType)]

numType :: Type -> Maybe Int
numType (TCon (TC (TCNum n)) [])
  | 0 <= n && n <= toInteger (maxBound :: Int) = Just (fromInteger n)
numType (TUser _ _ t) = numType t
numType _ = Nothing

finType :: Type -> Maybe FinType
finType ty =
  case ty of
    TCon (TC TCBit) []       -> Just FTBit
    TCon (TC TCSeq) [n, t]   -> FTSeq <$> numType n <*> finType t
    TCon (TC (TCTuple _)) ts -> FTTuple <$> traverse finType ts
    TRec fields              -> FTRecord <$> traverse (traverseSnd finType) fields
    TUser _ _ t              -> finType t
    _                        -> Nothing

unFinType :: FinType -> Type
unFinType fty =
  case fty of
    FTBit        -> tBit
    FTSeq l ety  -> tSeq (tNum l) (unFinType ety)
    FTTuple ftys -> tTuple (unFinType <$> ftys)
    FTRecord fs  -> tRec (zip fns tys)
      where
        fns = fst <$> fs
        tys = unFinType . snd <$> fs

predArgTypes :: Schema -> Either String [FinType]
predArgTypes schema@(Forall ts ps ty)
  | null ts && null ps =
      case go ty of
        Just fts -> Right fts
        Nothing  -> Left $ "Not a valid predicate type:\n" ++ show (pp schema)
  | otherwise = Left $ "Not a monomorphic type:\n" ++ show (pp schema)
  where
    go (TCon (TC TCBit) []) = Just []
    go (TCon (TC TCFun) [ty1, ty2]) = (:) <$> finType ty1 <*> go ty2
    go (TUser _ _ t) = go t
    go _ = Nothing

forallFinType :: FinType -> Symbolic Value
forallFinType ty =
  case ty of
    FTBit         -> VBit <$> SBV.forall_
    FTSeq 0 FTBit -> return $ VWord (SBV.literal (bv 0 0))
    FTSeq n FTBit -> VWord <$> (forallBV_ n)
    FTSeq n t     -> VSeq False <$> replicateM n (forallFinType t)
    FTTuple ts    -> VTuple <$> mapM forallFinType ts
    FTRecord fs   -> VRecord <$> mapM (traverseSnd forallFinType) fs

existsFinType :: FinType -> Symbolic Value
existsFinType ty =
  case ty of
    FTBit         -> VBit <$> SBV.exists_
    FTSeq 0 FTBit -> return $ VWord (SBV.literal (bv 0 0))
    FTSeq n FTBit -> VWord <$> existsBV_ n
    FTSeq n t     -> VSeq False <$> replicateM n (existsFinType t)
    FTTuple ts    -> VTuple <$> mapM existsFinType ts
    FTRecord fs   -> VRecord <$> mapM (traverseSnd existsFinType) fs

-- Simulation environment ------------------------------------------------------

data Env = Env
  { envVars :: Map.Map QName Value
  , envTypes :: Map.Map TVar TValue
  , envIteSolver :: Bool
  }

instance Monoid Env where
  mempty = Env
    { envVars  = Map.empty
    , envTypes = Map.empty
    , envIteSolver = False
    }

  mappend l r = Env
    { envVars  = Map.union (envVars  l) (envVars  r)
    , envTypes = Map.union (envTypes l) (envTypes r)
    , envIteSolver = envIteSolver l || envIteSolver r
    }

emptyEnv :: Bool -> Env
emptyEnv useIteSolver = Env Map.empty Map.empty useIteSolver

-- | Bind a variable in the evaluation environment.
bindVar :: (QName, Value) -> Env -> Env
bindVar (n, thunk) env = env { envVars = Map.insert n thunk (envVars env) }

-- | Lookup a variable in the environment.
lookupVar :: QName -> Env -> Maybe Value
lookupVar n env = Map.lookup n (envVars env)

-- | Bind a type variable of kind *.
bindType :: TVar -> TValue -> Env -> Env
bindType p ty env = env { envTypes = Map.insert p ty (envTypes env) }

-- | Lookup a type variable.
lookupType :: TVar -> Env -> Maybe TValue
lookupType p env = Map.lookup p (envTypes env)

-- Expressions -----------------------------------------------------------------

evalExpr :: Env -> Expr -> Value
evalExpr env expr =
  case expr of
    ECon econ         -> evalECon econ
    EList es ty       -> VSeq (tIsBit ty) (map eval es)
    ETuple es         -> VTuple (map eval es)
    ERec fields       -> VRecord [ (f, eval e) | (f, e) <- fields ]
    ESel e sel        -> evalSel sel (eval e)
    EIf b e1 e2       -> evalIf (fromVBit (eval b)) (eval e1) (eval e2)
                           where evalIf = if envIteSolver env then SBV.sBranch else SBV.ite
    EComp ty e mss    -> evalComp env (evalType env ty) e mss
    EVar n            -> case lookupVar n env of
                           Just x -> x
                           _ -> panic "Cryptol.Symbolic.evalExpr" [ "Variable " ++ show n ++ " not found" ]
    -- TODO: how to deal with uninterpreted functions?
    ETAbs tv e        -> VPoly $ \ty -> evalExpr (bindType (tpVar tv) ty env) e
    ETApp e ty        -> fromVPoly (eval e) (evalType env ty)
    EApp e1 e2        -> fromVFun (eval e1) (eval e2)
    EAbs n _ty e      -> VFun $ \x -> evalExpr (bindVar (n, x) env) e
    EProofAbs _prop e -> eval e
    EProofApp e       -> eval e
    ECast e _ty       -> eval e
    EWhere e ds       -> evalExpr (evalDecls env ds) e
    where
      eval e = evalExpr env e

evalType :: Env -> Type -> TValue
evalType env ty = Cryptol.Eval.Type.evalType env' ty
  where env' = Cryptol.Eval.Env.EvalEnv Map.empty (envTypes env)


evalSel :: Selector -> Value -> Value
evalSel sel v =
  case sel of
    TupleSel n _  ->
      case v of
        VTuple xs  -> xs !! n -- 0-based indexing
        VSeq b xs  -> VSeq b (map (evalSel sel) xs)
        VStream xs -> VStream (map (evalSel sel) xs)
        VFun f     -> VFun (\x -> evalSel sel (f x))
        _ -> panic "Cryptol.Symbolic.evalSel" [ "Tuple selector applied to incompatible type" ]

    RecordSel n _ ->
      case v of
        VRecord bs  -> case lookup n bs of
                         Just x -> x
                         _ -> panic "Cryptol.Symbolic.evalSel" [ "Selector " ++ show n ++ " not found" ]
        VSeq b xs   -> VSeq b (map (evalSel sel) xs)
        VStream xs  -> VStream (map (evalSel sel) xs)
        VFun f      -> VFun (\x -> evalSel sel (f x))
        _ -> panic "Cryptol.Symbolic.evalSel" [ "Record selector applied to non-record" ]

    ListSel n _   -> case v of
                       VWord s -> VBit (SBV.sbvTestBit s n)
                       _       -> fromSeq v !! n  -- 0-based indexing

-- Declarations ----------------------------------------------------------------

evalDecls :: Env -> [DeclGroup] -> Env
evalDecls = foldl evalDeclGroup

evalDeclGroup :: Env -> DeclGroup -> Env
evalDeclGroup env dg =
  case dg of
    NonRecursive d -> bindVar (evalDecl env d) env
    Recursive ds   -> let env' = foldr bindVar env lazyBindings
                          bindings = map (evalDecl env') ds
                          lazyBindings = [ (qname, copyBySchema env (dSignature d) v)
                                         | (d, (qname, v)) <- zip ds bindings ]
                      in env' -- foldr bindVar env bindings

evalDecl :: Env -> Decl -> (QName, Value)
evalDecl env d = (dName d, evalExpr env (dDefinition d))

-- | Make a copy of the given value, building the spine based only on
-- the type without forcing the value argument. This lets us avoid
-- strictness problems when evaluating recursive definitions.
copyBySchema :: Env -> Schema -> Value -> Value
copyBySchema env0 (Forall params _props ty) = go params env0
  where
    go [] env v = logicUnary id id (evalType env ty) v
    go (p : ps) env v =
      VPoly (\t -> go ps (bindType (tpVar p) t env) (fromVPoly v t))

-- List Comprehensions ---------------------------------------------------------

-- | Evaluate a comprehension.
evalComp :: Env -> TValue -> Expr -> [[Match]] -> Value
evalComp env seqty body ms
  | Just (len,el) <- isTSeq seqty = toSeq len el [ evalExpr e body | e <- envs ]
  | otherwise = evalPanic "Cryptol.Eval" [ "evalComp given a non sequence"
                                         , show seqty
                                         ]

  -- XXX we could potentially print this as a number if the type was available.
  where
  -- generate a new environment for each iteration of each parallel branch
  benvs = map (branchEnvs env) ms

  -- take parallel slices of each environment.  when the length of the list
  -- drops below the number of branches, one branch has terminated.
  allBranches es = length es == length ms
  slices         = takeWhile allBranches (transpose benvs)

  -- join environments to produce environments at each step through the process.
  envs = map mconcat slices

-- | Turn a list of matches into the final environments for each iteration of
-- the branch.
branchEnvs :: Env -> [Match] -> [Env]
branchEnvs env matches =
  case matches of
    []     -> [env]
    m : ms -> do env' <- evalMatch env m
                 branchEnvs env' ms

-- | Turn a match into the list of environments it represents.
evalMatch :: Env -> Match -> [Env]
evalMatch env m = case m of
  From n _ty expr -> [ bindVar (n, v) env | v <- fromSeq (evalExpr env expr) ]
  Let d           -> [ bindVar (evalDecl env d) env ]
