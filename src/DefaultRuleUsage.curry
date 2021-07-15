------------------------------------------------------------------------
--- This module contains some operations to check and access
--- default rules in a Curry program.
---
--- @author Michael Hanus
--- @version October 2016
------------------------------------------------------------------------

module DefaultRuleUsage
  ( containsDefaultRules, checkDefaultRules
  , isDefaultFunc, isDefaultName, fromDefaultName
  )  where

import AbstractCurry.Types
import AbstractCurry.Select
import Data.List

--- Does a program contains default rules?
containsDefaultRules :: CurryProg -> Bool
containsDefaultRules = not . null . filter isDefaultFunc . functions

--- Check correct usage of default rules and return function names and errors
--- for incorrect uses.
checkDefaultRules :: CurryProg -> [(QName,String)]
checkDefaultRules prog =
  let allfunctions = functions prog
      (defruledecls,fdecls) = partition isDefaultFunc allfunctions
   in concatMap (checkDefaultRule fdecls) defruledecls ++
      concatMap checkLocalDefaultRule allfunctions

checkDefaultRule :: [CFuncDecl] -> CFuncDecl -> [(QName,String)]
checkDefaultRule funcs (CmtFunc _ qf ar vis texp rules) =
  checkDefaultRule funcs (CFunc qf ar vis texp rules)
checkDefaultRule funcs (CFunc defqn@(mn,deffn) ar _ _ rules)
  | null rules
  = [(defqn,"Default rule without right-hand side!")]
  | length rules > 1
  = [(defqn,"More than one default rule for function '" ++ orgfn ++ "'!")]
  | otherwise
  = maybe [(defqn,"Default rule given but function '" ++ orgfn ++ "' not defined!")]
          (\fd -> if funcArity fd == ar
                    then []
                    else [(defqn,"Default rule has wrong arity!")])
          (find (\fd -> funcName fd == orgqn) funcs)
 where
  orgfn = fromDefaultName deffn
  orgqn = (mn, orgfn)

checkLocalDefaultRule :: CFuncDecl -> [(QName,String)]
checkLocalDefaultRule (CmtFunc _ qf ar vis texp rules) =
  checkLocalDefaultRule (CFunc qf ar vis texp rules)
checkLocalDefaultRule (CFunc defqn@(mn,deffn) ar _ _ rules) =
  checkLocalRules (concatMap allLocalDecls rules)
 where
  checkLocalRules ldecls =
    map (\ (_,fn) -> (defqn, "Local default rule '" ++ fn ++ "' is not allowed!"))
        (filter (isDefaultName . snd) (concatMap funcNamesOfLDecl ldecls))

--- Get all local declarations of a rule.
allLocalDecls :: CRule -> [CLocalDecl]
allLocalDecls (CRule _ rhs) = localsInRHS rhs
 where
  localsInRHS (CSimpleRhs  _ ldecls) = concatMap localsInLDecls ldecls
  localsInRHS (CGuardedRhs _ ldecls) = concatMap localsInLDecls ldecls

  localsInLDecls ldecl = ldecl : case ldecl of
    CLocalFunc fd -> concatMap allLocalDecls (funcRules fd)
    CLocalPat _ e -> localsInRHS e
    CLocalVars _  -> []

--- Is this function a declaration of a default rule?
isDefaultFunc :: CFuncDecl -> Bool
isDefaultFunc = isDefaultName . snd . funcName

--- Is this the name of a specification?
isDefaultName :: String -> Bool
isDefaultName f = "'default" `isSuffixOf` f

--- Drop the default rule suffix "'default" from the name:
fromDefaultName :: String -> String
fromDefaultName f =
  let rf = reverse f
   in reverse (drop (if take 8 rf == "tluafed'" then 8 else 0) rf)

------------------------------------------------------------------------
