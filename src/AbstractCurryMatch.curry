---------------------------------------------------------------------------
--- Some useful operations to support selection
--- of AbstractCurry expressions via deep pattern matching.
---------------------------------------------------------------------------

{-# OPTIONS_FRONTEND -Wno-overlapping #-}

import AbstractCurry.Types

--- Returns (non-deterministically) some expression that contains
--- the given expression as a subexpression.
withExp :: CExpr -> CExpr
withExp e = e -- the subexpression is the entire expression
withExp e = CApply (withExp e) _
withExp e = CApply _ (withExp e)
withExp e = CLambda _ (withExp e)
withExp e = CLetDecl _ (withExp e)
withExp e = CLetDecl (_ ++ [ldeclWithExp e] ++ _) _
withExp e = CDoExpr (_ ++ [statWithExp e] ++ _)
withExp e = CListComp (withExp e) _
withExp e = CListComp _ (_ ++ [statWithExp e] ++ _)
withExp e = CCase _ (withExp e) _
withExp e = CCase _ _ (_ ++ [(_,rhsWithExp e)] ++ _)
withExp e = CTyped (withExp e) _
withExp e = CRecConstr _ (_ ++ [(_, withExp e)] ++ _)
withExp e = CRecUpdate _ (_ ++ [(_, withExp e)] ++ _)

ldeclWithExp :: CExpr -> CLocalDecl
ldeclWithExp e = CLocalPat _ (rhsWithExp e)
ldeclWithExp e = CLocalFunc (cfunWithExp _ e)

statWithExp :: CExpr -> CStatement
statWithExp e = CSExpr (withExp e)
statWithExp e = CSPat _  (withExp e)
statWithExp e = CSLet (_ ++ [ldeclWithExp e] ++ _)

rhsWithExp :: CExpr -> CRhs
rhsWithExp e = CSimpleRhs (withExp e) _
rhsWithExp e = CSimpleRhs _ (_ ++ [ldeclWithExp e] ++ _)
rhsWithExp e = CGuardedRhs (_ ++ [(withExp e,_)] ++ _) _
rhsWithExp e = CGuardedRhs (_ ++ [(_,withExp e)] ++ _) _
rhsWithExp e = CGuardedRhs _ (_ ++ [ldeclWithExp e] ++ _)

--- Returns (non-deterministically) a function declaration containing
--- the given expression in the right-hand side.
cfunWithExp :: QName -> CExpr -> CFuncDecl
cfunWithExp qf e = CFunc     qf _ _ _ (_ ++ [CRule _ (rhsWithExp e)] ++ _)
cfunWithExp qf e = CmtFunc _ qf _ _ _ (_ ++ [CRule _ (rhsWithExp e)] ++ _)


---------------------------------------------------------------------------
