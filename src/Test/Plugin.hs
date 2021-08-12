{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
module Test.Plugin where

import           GHC
import           Control.Monad.State
import           TcType
import           Class
import           TcEvidence
import           GhcPlugins              hiding ( getHscEnv )
import           DsBinds
import qualified Data.Map.Strict               as OM
import           OccName
import           DsExpr
import           FastString
-- import           HsPat
import           ClsInst
import           SrcLoc
import           DsMonad
import           Control.Monad
import           CoreSyn
import           CoreFVs
import           Exception
import           Inst
import           Panic
import           Desugar
import           TcRnMonad
import           TcHsSyn
import           RnExpr
import           GhcMonad
import           TcSimplify
import           PrelNames
import           Outputable
import           GHC.LanguageExtensions.Type
import           HscTypes
import           ErrUtils
import           HscMain
import           TcExpr
-- import           HsExpr
import           RdrName
import           BasicTypes
import           GHC.Paths                      ( libdir )
import           TcOrigin
--GHC.Paths is available via cabal install ghc-paths

import           DynFlags
targetFile :: String
-- targetFile = "c.hs"
targetFile = "functor.hs"




plugin :: Plugin
plugin = defaultPlugin {
  typeCheckResultAction = testHook
  }
  where testHook _ _ gblEnv = do
          -- liftIO $ putStrLn "\nStarting..."
          e  <- elabRnExpr TM_Inst hse
          pp e
          pure gblEnv
        hse = mkHsApp (nlHsVar (mkVarUnqual "testPlus")) (nlHsIntLit 100)


pp e = do
  df <- getDynFlags
  liftIO $ putStrLn $ showSDocDebug df $ ppr e
  liftIO $ putStrLn ""


elabRnExpr
  :: TcRnExprMode -> LHsExpr GhcPs -> TcRn CoreExpr
elabRnExpr mode rdr_expr = withTempModule $ do
    -- pp rdr_expr
    (rn_expr, _fvs) <- rnLExpr rdr_expr
    -- pp rn_expr
    failIfErrsM
    uniq <- newUnique
    let fresh_it = itName uniq (getLoc rdr_expr)
        orig     = lexprCtOrigin rn_expr
    -- pp orig
    (tclvl, lie, (tc_expr, res_ty)) <- pushLevelAndCaptureConstraints $ do
      (_tc_expr, expr_ty) <- tcInferSigma rn_expr
      expr_ty'            <- if inst
        then snd <$> deeplyInstantiate orig expr_ty
        else return expr_ty
      return (_tc_expr, expr_ty')
    -- pp tc_expr
    (_, _, evbs, residual, _) <- simplifyInfer tclvl
                                            infer_mode
                                            []    {- No sig vars -}
                                            [(fresh_it, res_ty)]
                                            lie
    -- pp residual
    -- pp evbs
    evbs' <- perhaps_disable_default_warnings $ simplifyTop residual -- simplifyInteractive residual
    -- pp evbs'
    full_expr <- zonkTopLExpr (mkHsDictLet (EvBinds evbs') (mkHsDictLet evbs tc_expr))
    -- pp full_expr
    globaliseExpr <$> initDsTc (dsLExpr full_expr)
 where
  (inst, infer_mode, perhaps_disable_default_warnings) = case mode of
    TM_Inst    -> (True, NoRestrictions, id)
    TM_NoInst  -> (False, NoRestrictions, id)
    TM_Default -> (True, EagerDefaulting, unsetWOptM Opt_WarnTypeDefaults)

globaliseExpr :: CoreExpr -> CoreExpr
globaliseExpr (Var i) = Var $ globaliseId i
globaliseExpr e@(Lit _) = e
globaliseExpr (App expr arg) = App (globaliseExpr expr) (globaliseExpr arg)
globaliseExpr (Lam x e) = Lam (globaliseId x) (globaliseExpr e)
globaliseExpr (Let x e) = Let (globaliseBind x) (globaliseExpr e)
globaliseExpr (Case e x t alts) = Case (globaliseExpr e) (globaliseId x) (globaliseType t) $ map globaliseAlt alts
globaliseExpr (Cast e coerc) = Cast (globaliseExpr e) (globaliseCoercion coerc)
globaliseExpr (Tick t e) = Tick (globaliseTickish t) (globaliseExpr e)
globaliseExpr (Type t) = Type (globaliseType t)
globaliseExpr (Coercion c) = Coercion (globaliseCoercion c)

globaliseBind = error "TODO"
globaliseType = error "TODO"
globaliseAlt = error "TODO"
globaliseTickish = error "TODO"
globaliseCoercion = error "TODO"

withTempModule m = do
  -- TODO: Can we modify the env to not mark as local?
  env <- getEnv
  setEnv env m

-- myInitDsTc :: DsM a -> TcM a
-- myInitDsTc thing_inside
--   = do  { this_mod <- getModule
--         ; tcg_env  <- getGblEnv
--         ; msg_var  <- getErrsVar
--         ; dflags   <- getDynFlags
--         ; let type_env = tcg_type_env tcg_env
--               rdr_env  = tcg_rdr_env tcg_env
--               hsc_env = env_top tcg_env
--               fam_inst_env = tcg_fam_inst_env tcg_env
--               -- ds_envs  = mkDsEnvs dflags this_mod rdr_env type_env fam_inst_env msg_var
--         -- ; setEnvs ds_envs thing_inside
--         ; liftIO $ initDs hsc_env mod rdr_env type_env fam_inst_env thing_inside
--         }
