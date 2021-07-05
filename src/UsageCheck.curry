---------------------------------------------------------------------------
--- Set functions are intended to exist for every top-level function.
--- The operation `checkSetUse` detects unintended uses of set funtions.
--- Furthermore, the operation `checkBlacklistUse` checks whether
--- internal operations like `Prelude.=:<=` or `Prelude.prim_` are used
--- in a Curry program.
---
--- See example program `Examples/UsageErrors.curry` for some examples.
---
--- @author Michael Hanus
--- @version July 2021
---------------------------------------------------------------------------

module UsageCheck(checkSetUse, checkBlacklistUse) where

import Data.Char ( isDigit )
import Numeric   ( readNat )

import qualified AbstractCurry.Types as AC
import AbstractCurryMatch
import FlatCurry.Types
import FlatCurryMatch

import Control.SetFunctions

---------------------------------------------------------------------
--- Returns messages about unintended uses of set functions in a
--- FlatCurry program.
checkSetUse :: Prog -> IO [(QName,String)]
checkSetUse (Prog _ _ _ fdecls _) = do
  seterrors <- values2list (set1 setUse fdecls)
  return (map showSetError seterrors)
 where
  showSetError (qf,sar,reason) =
    (qf, "wrong use of set function `set" ++ sar ++ "': " ++ reason ++ "!")

--- Returns some unintended use of a set function occurring in a list
--- of function declarations. The name of the function together with
--- the arity of the set function used and a reason is returned.
--- Set functions are intended to be used only on top-level functions
--- with the correct arity.
---
--- To provide a simple implementation, we exploit functional patterns
--- with the function `funWithinExp`.
setUse :: [FuncDecl] -> (QName, String, String)
setUse (_ ++
        [funWithinExp qf _ _ (Comb ct ("Control.SetFunctions", "set" ++ n) args)]
        ++ _) =
  invalidSetFunCall qf ct n args

--- Checks whether an application of a set function `setn` is unintended.
invalidSetFunCall :: QName -> CombType -> String -> [Expr] -> (QName,String,String)
invalidSetFunCall qf ct sar args
  | not (all isDigit sar)
  = (qf,sar,"suffix of set function is not a number")
  | ct==FuncCall && null args
  = (qf,sar,"missing function argument")
  | ct==FuncCall
  = if arity==0 then isFuncCall (head args)
                else isFuncPartCall arity (head args)
  | otherwise
  = (qf,sar,"partial application of set function")
 where
  arity = case readNat sar of
            [(i,"")] -> i
            _        -> error "UsageCheck.validSetFunCall: illegal number!"

  isFuncCall e = case e of
    Comb FuncCall (_,fn) [] -> checkTopLevelID fn
    _                       -> arityError 0

  isFuncPartCall n e = case e of
    Comb (FuncPartCall p) (_,fn) _ -> if p==n then checkTopLevelID fn
                                              else arityError n
    _                              -> arityError n

  checkTopLevelID fn | isID fn   = failed
                     | otherwise = (qf,sar,"set function not applied to top-level name")

  -- Checks whether the name is a regular top-level name.
  isID fn = all (`elem` infixIDs) fn || '.' `notElem` fn
   where
    infixIDs :: String
    infixIDs =  "~!@#$%^&*+-=<>?./|\\:"

  arityError n = (qf,sar,"set function not applied to " ++ showArity n ++ " top-level function")

  showArity n | n == 0    = "0-ary"
              | n == 1    = "unary"
              | n == 2    = "binary"
              | otherwise = show n ++ "-ary"


---------------------------------------------------------------------
--- Returns messages about uses of black-listed operations occurring
--- in an AbstractCurry program.
checkBlacklistUse :: AC.CurryProg -> IO [(QName,String)]
checkBlacklistUse (AC.CurryProg _ _ _ _ _ _ cfdecls _) = do
  blerrors <- values2list (set1 blacklistUsage cfdecls)
  return (map showBlacklistError blerrors)
 where
  showBlacklistError (qf,(q,f)) =
    (qf, "direct use of `" ++ q++"."++f ++ "' not allowed!")

--- Returns some use of a black-listed operation occurring in a list
--- of function declarations. The name of the defined function together with
--- the black-listed operation is returned.
---
--- To provide a simple implementation, we exploit functional patterns
--- with the function `cfunWithExp`.
---
--- TODO: check also occurrences in functional patterns
blacklistUsage :: [AC.CFuncDecl] -> (AC.QName, AC.QName)
blacklistUsage (_ ++ [cfunWithExp qf (AC.CSymbol qop)] ++ _)
  | isBlacklistedOperation qop
  = (qf,qop)

isBlacklistedOperation :: AC.QName -> Bool
isBlacklistedOperation (q,f) =
  q == AC.preludeName &&
  (take 5 f == "prim_" --no direct call to primitive ops
   || f `elem` ["=:<=", "=:<<="])

---------------------------------------------------------------------
