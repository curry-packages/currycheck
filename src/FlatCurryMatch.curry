---------------------------------------------------------------------------
--- Some useful operations to support selection
--- of FlatCurry expressions via deep pattern matching.
---------------------------------------------------------------------------

{-# OPTIONS_FRONTEND -Wno-overlapping #-}

module FlatCurryMatch ( withExp, funWithExp, funWithinExp )
 where

import FlatCurry.Types

--- Returns (non-deterministically) some expression that contains
--- the given expression as a subexpression.
withExp :: Expr -> Expr
withExp e = e -- the subexpression is the entire expression
withExp e = Comb _ _ (_ ++ [withExp e] ++ _)
withExp e = Let  _ (withExp e) ? Let (_ ++ [(_,withExp e)] ++ _) _
withExp e = Free _ (withExp e)
withExp e = Or (withExp e) _ ? Or _ (withExp e)
withExp e = Case  _ (withExp e) _ ? Case _ _ (_ ++ [Branch _ (withExp e)] ++ _)
withExp e = Typed (withExp e) _

--- Returns (non-deterministically) a function declaration containing
--- the given expression in the right-hand side.
funWithExp :: QName -> Expr -> FuncDecl
funWithExp qf e = Func qf _ _ _ (Rule _ (withExp e))

-- Returns an expression that contains the given expression (third argument)
-- as a subexpression. Furthermore, the first argument is the complete
-- expression with a hole (free variable, second argument) at the position
-- of the given subexpression.
-- Hence, if e = inExp e' x s, then e = { x |-> s}(e').
inExp :: Expr -> Expr -> Expr -> Expr
inExp x x e = e -- the subexpression is the entire expression
inExp (Comb ct qf args) x e =
  Comb ct qf (withElem (inExp se x e) se args)
 where se free
inExp (Let bs se) x e = Let bs (inExp se x e)
inExp (Let bs le) x e = Let (withElem (lv,inExp se x e) (lv,se) bs) le
 where lv,se free
inExp (Free vars se) x e = Free vars (inExp se x e)
inExp (Or se e2) x e = Or (inExp se x e) e2
inExp (Or e1 se) x e = Or e1 (inExp se x e)
inExp (Case ct se bs) x e = Case ct (inExp se x e) bs
inExp (Case ct ce bs) x e =
  Case ct ce (withElem (Branch pat (inExp se x e)) (Branch pat se) bs)
 where pat,se free
inExp (Typed se te) x e = Typed (inExp se x e) te

--- Returns a list containing the first argument as an element.
--- Furthermore, the third argument is the result list except for
--- the element which is replaced by the second argument. Hence,
--- if `withElem e x os` evaluates to `x1:...:xm:e:ys`,
--- where `os=x1:...:xm:x:ys`.
--- Note that this construction is necessary to achieve a finite search
--- space when matching against a finite expression with the operation
--- `inExp`.
withElem :: Data a => a -> a -> [a] -> [a]
withElem e x zs = prefix ++ e : (zs =:= prefix ++ (x:suffix) &> suffix)
   where prefix,suffix free

--- Returns (non-deterministically) some function declaration for the
--- given function name where the right-hand side is the given
--- expression with a variable hole and a subexression.
---
--- @param qf - The qualified function name
--- @param e  - The right-hand side with a hole containing `x`
--- @param x  - The variable in the hole
--- @param se - The subexpression at the hole in the right-hand side
--- @return The function declaration with `e` as the right-hand side
funWithinExp :: QName -> Expr -> Expr -> Expr -> FuncDecl
funWithinExp qf e x se = Func qf _ _ _ (Rule _ (inExp e x se))

---------------------------------------------------------------------------
