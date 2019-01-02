------------------------------------------------------------------------
--- This module contains some operations to handle properties in
--- a Curry program.
---
--- @author Michael Hanus
--- @version January 2019
------------------------------------------------------------------------

module PropertyUsage
  ( isProperty, isPropType, isPropIOType, isEquivProperty
  , propModule, propTypesModule, easyCheckModule, easyCheckExecModule
  )  where

import AbstractCurry.Types
import AbstractCurry.Select (funcType, resultType, typeOfQualType, funcRules)

------------------------------------------------------------------------
--- Check whether a function definition is a property,
--- i.e., if the result type is `Prop` or `PropIO`.
isProperty :: CFuncDecl -> Bool
isProperty = isPropertyType . typeOfQualType . funcType
 where
  isPropertyType ct = isPropIOType ct || isPropType (resultType ct)

--- Is the type expression the type Test.EasyCheck.Prop?
isPropType :: CTypeExpr -> Bool
isPropType texp = case texp of
  CTCons (mn,tc) -> tc == "Prop" && mn == propTypesModule
  _              -> False

--- Is the type expression the type Test.EasyCheck.PropIO?
isPropIOType :: CTypeExpr -> Bool
isPropIOType texp = case texp of
  CTCons (mn,tc) -> tc == "PropIO" && mn == propTypesModule
  _              -> False

--- Check whether a function definition is an equivalence property, i.e.,
--- has the form `test = f1 <=> f2`. If yes, returns both operations,
--- otherwise `Nothing` is returned.
isEquivProperty :: CFuncDecl -> Maybe (CExpr,CExpr)
isEquivProperty fdecl =
  case funcRules fdecl of
    [CRule [] (CSimpleRhs (CApply (CApply (CSymbol prop) e1) e2) [])]
      -> if isEquivSymbol prop then Just (e1,e2) else Nothing
    _ -> Nothing
 where
  isEquivSymbol (qn,mn) = isCheckModule qn && mn=="<=>"

-- Is the module name Test.Prop or Test.EasyCheck?
isCheckModule :: String -> Bool
isCheckModule mn = mn == propModule || mn == easyCheckModule

--- Name of the Test.Prop module (the clone of the EasyCheck module).
propModule :: String
propModule = "Test.Prop" 

--- Name of the Test.Prop.Types module (containing property type definitions).
propTypesModule :: String
propTypesModule = "Test.Prop.Types"

--- Name of the EasyCheck module.
easyCheckModule :: String
easyCheckModule = "Test.EasyCheck" 

--- Name of the EasyCheckExec module.
easyCheckExecModule :: String
easyCheckExecModule = "Test.EasyCheck.Exec" 

