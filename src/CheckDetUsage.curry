---------------------------------------------------------------------------
--- Deterministic operations are marked by wrapping the result type
--- of top-level operations with the type synonym `Prelude.DET`.
--- This module defines the operation `checkDetUse` which detects
--- unintended uses of this type synonym.
---
--- See example program `Examples/UsageErrors.curry` for some examples.
---
--- @author Michael Hanus
--- @version May 2016
---------------------------------------------------------------------------

module CheckDetUsage(containsDetOperations, checkDetUse) where

import AbstractCurry.Types
import AbstractCurry.Select

---------------------------------------------------------------------
--- Does a Curr program contains operations with DET annotations?
containsDetOperations :: CurryProg -> Bool
containsDetOperations (CurryProg _ _ _ fdecls _) =
  any (detInTopLevelType . funcType) fdecls
 where
  detInTopLevelType (CTVar _)     = False
  detInTopLevelType (CTCons tc _) = tc == pre "DET"
  detInTopLevelType (CFuncType _ rt) = detInTopLevelType rt

---------------------------------------------------------------------
--- Returns messages about unintended uses of type synonym `DET`
--- in a Curry program.
checkDetUse :: CurryProg -> [(QName,String)]
checkDetUse (CurryProg _ _ _ fdecls _) =
  concatMap (map showDetError . checkDetUseInFDecl) fdecls
 where
  showDetError qf = (qf, "wrong use of DET type synonym!")

checkDetUseInFDecl :: CFuncDecl -> [QName]
checkDetUseInFDecl (CFunc qn _ _ t rs) =
  if checkDetInTopLevelType t || any detInRule rs
  then [qn]
  else []
checkDetUseInFDecl (CmtFunc _  qn ar vis t rs) =
  checkDetUseInFDecl (CFunc qn ar vis t rs)

checkDetInTopLevelType :: CTypeExpr -> Bool
checkDetInTopLevelType (CTVar _)     = False
checkDetInTopLevelType (CTCons _ ts) = any detInTypeExpr ts
checkDetInTopLevelType (CFuncType at rt) =
  detInTypeExpr at || checkDetInTopLevelType rt

detInTypeExpr :: CTypeExpr -> Bool
detInTypeExpr (CTVar _) = False
detInTypeExpr (CTCons tc ts) =
  tc == pre "DET" || any detInTypeExpr ts
detInTypeExpr (CFuncType at rt) = detInTypeExpr at || detInTypeExpr rt

detInRule :: CRule -> Bool
detInRule (CRule _ rhs) = detInRhs rhs

detInRhs :: CRhs -> Bool
detInRhs (CSimpleRhs e ldecls) = detInExp e || any detInLocalDecl ldecls
detInRhs (CGuardedRhs gs ldcls) = any detInGuard gs || any detInLocalDecl ldcls
 where detInGuard (e1,e2) = detInExp e1 || detInExp e2

detInLocalDecl :: CLocalDecl -> Bool
detInLocalDecl (CLocalFunc (CFunc _ _ _ t rs)) =
  detInTypeExpr t || any detInRule rs
detInLocalDecl (CLocalFunc (CmtFunc _ _ _ _ t rs)) =
  detInTypeExpr t || any detInRule rs
detInLocalDecl (CLocalPat _ rhs) = detInRhs rhs
detInLocalDecl (CLocalVars _) = False

detInExp :: CExpr -> Bool
detInExp (CVar _) = False
detInExp (CLit _) = False
detInExp (CSymbol _) = False
detInExp (CApply e1 e2) = detInExp e1 || detInExp e2
detInExp (CLambda _ e) = detInExp e
detInExp (CLetDecl ldecls e) = any detInLocalDecl ldecls || detInExp e
detInExp (CDoExpr stmts) = any detInStatement stmts
detInExp (CListComp e stmts) = detInExp e || any detInStatement stmts
detInExp (CCase _ e branches) = detInExp e || any (detInRhs . snd) branches
detInExp (CTyped e t) = detInExp e || detInTypeExpr t
detInExp (CRecConstr _ fields) = any (detInExp . snd) fields
detInExp (CRecUpdate e fields) = detInExp e || any (detInExp . snd) fields

detInStatement :: CStatement -> Bool
detInStatement (CSExpr e) = detInExp e
detInStatement (CSPat _ e) = detInExp e
detInStatement (CSLet ldecls) = any detInLocalDecl ldecls

---------------------------------------------------------------------
