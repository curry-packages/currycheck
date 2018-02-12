-------------------------------------------------------------------------
--- This is the implementation of the currycheck tool.
--- It performs various checks on Curry programs:
---
--- * Correct usage of set functions, non-strict unification,
---   default rules, DET annotations, contracts
--- * All EasyCheck tests are extracted and checked
--- * For all functions declared as deterministic,
---   determinism properties are generated and checked.
--- * For functions with postconditions (f'post), checks for postconditions
---   are generated (together with possible preconditions)
--- * For functions with specification (f'spec), checks for satisfaction
---   of these specifications are generated
---   (together with possible preconditions).
---
--- @author Michael Hanus, Jan-Patrick Baye
--- @version February 2018
-------------------------------------------------------------------------

import AnsiCodes
import Char                    ( toUpper )
import Distribution
import FilePath                ( (</>), pathSeparator, takeDirectory )
import GetOpt
import List
import Maybe                   ( fromJust, isJust )
import System                  ( system, exitWith, getArgs, getPID, getEnviron )

import AbstractCurry.Types
import AbstractCurry.Files
import AbstractCurry.Select
import AbstractCurry.Build
import qualified AbstractCurry.Pretty as ACPretty
import AbstractCurry.Transform ( renameCurryModule, trCTypeExpr
                               , updCProg, updQNamesInCProg )
import Analysis.Termination    ( Productivity(..) )
import qualified FlatCurry.Types as FC
import FlatCurry.Files
import qualified FlatCurry.Goodies as FCG
import Text.Pretty             ( pPrint )

import CC.AnalysisHelpers      ( getTerminationInfos, getProductivityInfos )
import CC.Config               ( packagePath, packageVersion )
import CC.Options
import CheckDetUsage           ( checkDetUse, containsDetOperations)
import ContractUsage
import DefaultRuleUsage        ( checkDefaultRules, containsDefaultRules )
import PropertyUsage
import SimplifyPostConds       ( simplifyPostConditionsWithTheorems )
import TheoremUsage
import UsageCheck              ( checkBlacklistUse, checkSetUse )

-- Banner of this tool:
ccBanner :: String
ccBanner = unlines [bannerLine,bannerText,bannerLine]
 where
   bannerText = "CurryCheck: a tool for testing Curry programs (Version " ++
                packageVersion ++ " of 12/02/2018)"
   bannerLine = take (length bannerText) (repeat '-')

-- Help text
usageText :: String
usageText = usageInfo ("Usage: curry-check [options] <module names>\n") options

--- Maximal arity of check functions and tuples currently supported:
maxArity :: Int
maxArity = 5

-------------------------------------------------------------------------
-- The names of suffixes added to specific tests.

defTypeSuffix :: String
defTypeSuffix = "_ON_BASETYPE"

postCondSuffix :: String
postCondSuffix = "SatisfiesPostCondition"

satSpecSuffix :: String
satSpecSuffix = "SatisfiesSpecification"

isDetSuffix :: String
isDetSuffix = "IsDeterministic"

-------------------------------------------------------------------------
-- Internal representation of tests extracted from a Curry module.
-- A test is
-- * a property test (with a name, type, source line number),
-- * an IO test (with a name and source line number), or
-- * an operation equivalence test (with a name, the names of both operations,
--   and their type, and the source line number).
data Test = PropTest  QName CTypeExpr Int
          | IOTest    QName Int
          | EquivTest QName QName QName CTypeExpr Int

-- Is the test an IO test?
isIOTest :: Test -> Bool
isIOTest t = case t of IOTest _ _ -> True
                       _          -> False
-- Is the test a unit test?
isUnitTest :: Test -> Bool
isUnitTest t = case t of PropTest _ texp _ -> null (argTypes texp)
                         _                 -> False

-- Is the test a property test?
isPropTest :: Test -> Bool
isPropTest t = case t of PropTest _ texp _ -> not (null (argTypes texp))
                         _                 -> False

-- Is the test an equivalence test?
isEquivTest :: Test -> Bool
isEquivTest t = case t of EquivTest _ _ _ _ _ -> True
                          _                   -> False

-- Returns the names of the operations of an equivalence test.
equivTestOps :: Test -> [QName]
equivTestOps t = case t of EquivTest _ f1 f2 _ _ -> [f1,f2]
                           _                     -> []

-- The name of a test:
testName :: Test -> QName
testName (PropTest  n _     _) = n
testName (IOTest    n       _) = n
testName (EquivTest n _ _ _ _) = n

-- The line number of a test:
testLine :: Test -> Int
testLine (PropTest  _ _     n) = n
testLine (IOTest    _       n) = n
testLine (EquivTest _ _ _ _ n) = n

-- Generates a useful error message for tests (with module and line number)
genTestMsg :: String -> Test -> String
genTestMsg file test =
  snd (testName test) ++
  " (module " ++ file ++ ", line " ++ show (testLine test) ++ ")"

-- Generates the name of a test in the main test module from the test name.
genTestName :: Test -> String
genTestName test =
  let (modName, fName) = testName test
  in fName ++ "_" ++ modNameToId modName

-------------------------------------------------------------------------
-- Representation of the information about a module to be tested:
-- * the original name of the module to be tested
-- * the name of the transformed (public) test module
-- * static errors (e.g., illegal uses of set functions)
-- * test operations
-- * name of generators defined in this module (i.e., starting with "gen"
--   and of appropriate result type)
data TestModule = TestModule
  { orgModuleName  :: String
  , testModuleName :: String
  , staticErrors   :: [String]
  , propTests      :: [Test]
  , generators     :: [QName]
  }

-- A test module with only static errors.
staticErrorTestMod :: String -> [String] -> TestModule
staticErrorTestMod modname staterrs =
 TestModule modname modname staterrs [] []

-- Is this a test module that should be tested?
testThisModule :: TestModule -> Bool
testThisModule tm = null (staticErrors tm) && not (null (propTests tm))

-- Extracts all user data types used as test data generators.
-- Each type has a flag which is `True` if the test data should contain
-- partial values (for checking equivalence of operations).
userTestDataOfModule :: TestModule -> [(QName,Bool)]
userTestDataOfModule testmod = concatMap testDataOf (propTests testmod)
 where
  testDataOf (IOTest _ _) = []
  testDataOf (PropTest _ texp _) =
    map (\t -> (t,False)) (filter (\ (mn,_) -> mn /= preludeName)
                                  (unionOn tconsOf (argTypes texp)))
  testDataOf (EquivTest _ _ _ texp _) =
    map (\t -> (t,True)) (unionOn tconsOf (argTypes texp))

-- Extracts all result data types used in equivalence properties.
equivPropTypes :: TestModule -> [QName]
equivPropTypes testmod = concatMap equivTypesOf (propTests testmod)
 where
  equivTypesOf (IOTest _ _) = []
  equivTypesOf (PropTest _ _ _) = []
  equivTypesOf (EquivTest _ _ _ texp _) = tconsOf (resultType texp)

-------------------------------------------------------------------------
-- Transform all tests of a module into operations that perform
-- appropriate calls to EasyCheck:
genTestFuncs :: Options -> (QName -> Bool) -> (QName -> Productivity) -> String
             -> TestModule -> IO [CFuncDecl]
genTestFuncs opts terminating productivity mainmod tm =
  liftM (filter (not . null . funcRules))
        (mapM genTestFunc (propTests tm))
 where
  genTestFunc test = case test of
    PropTest  name t _       -> testFuncWithRules (propBody   name t test)
    IOTest    name   _       -> testFuncWithRules (ioTestBody name test)
    EquivTest name f1 f2 t _ ->
      -- if the test name has suffix "'TERMINATE" or the operations
      -- to be tested are terminating, the test for terminating
      -- operations is used:
      if "'TERMINATE" `isSuffixOf` map toUpper (snd name) ||
         (isTerminating f1 && isTerminating f2)
        then do putStrLnIfDebug opts $
                  "Generating equivalence test for TERMINATING " ++
                  "operations for test: " ++ snd name
                testFuncWithRules $ equivBodyTerm f1 f2 t test
        else
          -- if the test name has suffix "'PRODUCTIVE" or the
          -- operations to be tested are productive,
          -- the test for arbitrary operations is used
          -- (which limits the size of computed
          -- results but might find counter-examples later),
          -- otherwise the test is omitted if we are in the "safe"
          -- mode:
          if "'PRODUCTIVE" `isSuffixOf` map toUpper (snd name) ||
             optEquiv opts /= Safe ||
             (isProductive f1 && isProductive f2)
            then do putStrLnIfDebug opts $
                      "Generating equivalence test for PRODUCTIVE " ++
                      "operations for test: " ++ snd name
                    testFuncWithRules $ equivBodyAny f1 f2 t test
            else testFuncWithRules []
   where
     testFuncWithRules rs =
       return $ cfunc (mainmod, genTestName test) 0 Public
                      (emptyClassType (ioType (maybeType stringType))) rs

  isTerminating f = terminating f || productivity f == Terminating
  
  isProductive f = productivity f `notElem` [NoInfo, Looping]
  
  msgOf test = string2ac $ genTestMsg (orgModuleName tm) test

  testmname = testModuleName tm

  easyCheckFuncName arity =
    if arity>maxArity
    then error $ "Properties with more than " ++ show maxArity ++
                 " parameters are currently not supported!"
    else (easyCheckExecModule,"checkWithValues" ++ show arity)

  -- Operation equivalence test for terminating operations:
  equivBodyTerm f1 f2 texp test =
    let xvar = (1,"x")
        pvalOfFunc = ctype2pvalOf mainmod "pvalOf" (resultType texp)
    in propOrEquivBody (map (\t -> (t,True)) (argTypes texp)) test
         (CLambda [CPVar xvar]
            (applyF (easyCheckModule,"<~>")
                    [applyE pvalOfFunc [applyF f1 [CVar xvar]],
                     applyE pvalOfFunc [applyF f2 [CVar xvar]]]))

  -- Operation equivalence test for arbitrary operations:
  equivBodyAny f1 f2 texp test =
    let xvar = (1,"x")
        pvar = (2,"p")
        pvalOfFunc = ctype2pvalOf mainmod "peval" (resultType texp)
    in propOrEquivBody
         (map (\t -> (t,True)) (argTypes texp) ++
          [(ctype2BotType mainmod  (resultType texp), False)])
         test
         (CLambda [CPVar xvar, CPVar pvar]
            (applyF (easyCheckModule,"<~>")
                    [applyE pvalOfFunc [applyF f1 [CVar xvar], CVar pvar],
                     applyE pvalOfFunc [applyF f2 [CVar xvar], CVar pvar]]))

  propBody qname texp test =
    propOrEquivBody (map (\t -> (t,False)) (argTypes texp))
                    test (CSymbol (testmname,snd qname))

  propOrEquivBody argtypes test propexp =
    [simpleRule [] $
      CLetDecl [CLocalPat (CPVar msgvar) (CSimpleRhs (msgOf test) [])]
               (applyF (easyCheckExecModule, "checkPropWithMsg")
                 [ CVar msgvar
                 , applyF (easyCheckFuncName (length argtypes)) $
                    [configOpWithMaxFail, CVar msgvar] ++
                    (map (\ (t,genpart) ->
                          applyF (easyCheckModule,"valuesOfSearchTree")
                            [if isPAKCS || useUserDefinedGen t || isFloatType t
                             then type2genop mainmod tm genpart t
                             else applyF (searchTreeModule,"someSearchTree")
                                         [constF (pre "unknown")]])
                         argtypes) ++
                    [propexp]
                 ])]
   where
    useUserDefinedGen texp = case texp of
      CTVar _       -> error "No polymorphic generator!"
      CFuncType _ _ -> error $ "No generator for functional types:\n" ++
                               showCTypeExpr texp
      CTApply _ _   ->
        maybe (error "No generator for type applications!")
              (\ ((_,tc),_) -> isJust
                         (find (\qn -> "gen"++tc == snd qn) (generators tm)))
              (tconsArgsOfType texp)
      CTCons (_,tc) -> isJust
                         (find (\qn -> "gen"++tc == snd qn) (generators tm))

    configOpWithMaxTest =
      let n = optMaxTest opts
       in if n==0 then stdConfigOp
                  else applyF (easyCheckExecModule,"setMaxTest")
                              [cInt n, stdConfigOp]

    configOpWithMaxFail =
      let n = optMaxFail opts
       in if n==0 then configOpWithMaxTest
                  else applyF (easyCheckExecModule,"setMaxFail")
                              [cInt n, configOpWithMaxTest]

    msgvar = (0,"msg")

  stdConfigOp = constF (easyCheckConfig opts)

  ioTestBody (_, name) test =
    [simpleRule [] $ applyF (easyCheckExecModule,"checkPropIOWithMsg")
                            [stdConfigOp, msgOf test, CSymbol (testmname,name)]]

-- The configuration option for EasyCheck
easyCheckConfig :: Options -> QName
easyCheckConfig opts =
  (easyCheckExecModule,
   if isQuiet opts     then "quietConfig"   else
   if optVerb opts > 2 then "verboseConfig"
                       else "easyConfig")

-- Translates a type expression into calls to generator operations.
-- If the third argument is `True`, calls to partial generators are used.
type2genop :: String -> TestModule -> Bool -> CTypeExpr -> CExpr
type2genop _ _ _ (CTVar _)       = error "No polymorphic generator!"
type2genop _ _ _ te@(CFuncType _ _) =
  error $ "No generator for functional types:\n" ++ showCTypeExpr te
type2genop mainmod tm genpart (CTCons qt) =
  constF (typename2genopname mainmod (generators tm) genpart qt)
type2genop mainmod tm genpart te@(CTApply _ _) =
  maybe (error "No generator for type applications!")
        (\ (qt,targs) ->
           applyF (typename2genopname mainmod (generators tm) genpart qt)
                  (map (type2genop mainmod tm genpart) targs))
        (tconsArgsOfType te)

isFloatType :: CTypeExpr -> Bool
isFloatType texp = case texp of CTCons tc -> tc == (preludeName,"Float")
                                _         -> False

-- Translates the name of a type constructor into the name of the
-- generator operation for values of this type.
-- The first argument is the name of the main module.
-- The second argument contains the user-defined generator operations.
-- If the third argument is `True`, generators for partial values are used.
typename2genopname :: String -> [QName] -> Bool -> QName -> QName
typename2genopname mainmod definedgenops genpart (mn,tc)
  | genpart  -- we use our own generator for partial values:
  = (mainmod, "gen_" ++ modNameToId mn ++ "_" ++ transQN tc ++ "_PARTIAL")
  | isJust maybeuserdefined -- take user-defined generator:
  = fromJust maybeuserdefined
  | mn==preludeName
  = (generatorModule, "gen" ++ transQN tc)
  | otherwise -- we use our own generator:
  = (mainmod, "gen_" ++ modNameToId mn ++ "_" ++ transQN tc ++
              if genpart then "_PARTIAL" else "")
 where
  maybeuserdefined = find (\qn -> "gen"++tc == snd qn) definedgenops

-- Transform a qualified (typ) constructor name into a name
-- with alpha-numeric characters.
transQN :: String -> String
transQN tcons | tcons == "[]"     = "List"
              | tcons == ":"      = "Cons"
              | tcons == "()"     = "Unit"
              | tcons == "(,)"    = "Pair"
              | tcons == "(,,)"   = "Triple"
              | tcons == "(,,,)"  = "Tuple4"
              | tcons == "(,,,,)" = "Tuple5"
              | otherwise         = tcons

-------------------------------------------------------------------------
-- Turn all functions into public ones.
-- This ensures that all tests can be executed.
makeAllPublic :: CurryProg -> CurryProg
makeAllPublic (CurryProg modname imports dfltdecl clsdecls instdecls
                         typedecls functions opdecls) =
  CurryProg modname stimports dfltdecl clsdecls instdecls
            typedecls publicFunctions opdecls
 where
  stimports = if generatorModule `elem` imports &&
                 searchTreeModule `notElem` imports
              then searchTreeModule : imports -- just to be safe if module
                                              -- contains generator definitions
              else imports

  publicFunctions = map makePublic $ map ignoreComment functions

  -- since we create a copy of the module, we can ignore unnecessary data
  ignoreComment :: CFuncDecl -> CFuncDecl
  ignoreComment (CmtFunc _ name arity visibility typeExpr rules) =
    CFunc name arity visibility typeExpr rules
  ignoreComment x@(CFunc      _     _          _        _     _) = x

  makePublic :: CFuncDecl -> CFuncDecl
  makePublic (CFunc name arity _      typeExpr rules) =
              CFunc name arity Public typeExpr rules
  makePublic (CmtFunc cmt name arity _      typeExpr rules) =
              CmtFunc cmt name arity Public typeExpr rules

-- classify the tests as either PropTest or IOTest
classifyTests :: Options -> CurryProg -> [CFuncDecl] -> [Test]
classifyTests opts prog = map makeProperty
 where
  makeProperty test =
    if isPropIOType (typeOfQualType (funcType test))
      then IOTest tname 0
      else maybe (PropTest tname (typeOfQualType (funcType test)) 0)
                 expsToEquivTest
                 (isEquivProperty test)
    where
     tname = funcName test

     expsToEquivTest exps = case exps of
       (CSymbol f1,CSymbol f2) ->
         EquivTest tname f1 f2 (defaultingType (funcTypeOf f1)) 0
       (CTyped (CSymbol f1) qtexp, CSymbol f2) ->
         EquivTest tname f1 f2 (defaultingType qtexp) 0
       (CSymbol f1, CTyped (CSymbol f2) qtexp) ->
         EquivTest tname f1 f2 (defaultingType qtexp) 0
       (CTyped (CSymbol f1) qtexp, CTyped (CSymbol f2) _) ->
         EquivTest tname f1 f2 (defaultingType qtexp) 0
       (e1,e2) -> error $ "Illegal equivalence property:\n" ++
                          showCExpr e1 ++ " <=> " ++ showCExpr e2

  defaultingType = poly2defaultType (optDefType opts) . typeOfQualType
                                                      . defaultQualType
  
  funcTypeOf f = maybe (error $ "Cannot find type of " ++ show f ++ "!")
                       funcType
                       (find (\fd -> funcName fd == f) (functions prog))

-- Extracts all tests from a given Curry module and transforms
-- all polymorphic tests into tests on a base type.
-- The result contains a triple consisting of all actual tests,
-- all ignored tests, and the public version of the original module.
transformTests :: Options -> String -> CurryProg
               -> IO ([CFuncDecl],[CFuncDecl],CurryProg)
transformTests opts srcdir
               prog@(CurryProg mname imps dfltdecl clsdecls instdecls
                               typeDecls functions opDecls) = do
  theofuncs <- if optProof opts then getTheoremFunctions srcdir prog
                                else return []
  simpfuncs <- simplifyPostConditionsWithTheorems (optVerb opts) theofuncs funcs
  let preCondOps  = preCondOperations simpfuncs
      postCondOps = map ((\ (mn,fn) -> (mn, fromPostCondName fn)) . funcName)
                        (funDeclsWith isPostCondName simpfuncs)
      specOps     = map ((\ (mn,fn) -> (mn, fromSpecName fn)) . funcName)
                        (funDeclsWith isSpecName simpfuncs)
      -- generate post condition tests:
      postCondTests = concatMap (genPostCondTest preCondOps postCondOps) funcs
      -- generate specification tests:
      specOpTests   = concatMap (genSpecTest preCondOps specOps) funcs

      (realtests,ignoredtests) = partition fst $
        if not (optProp opts)
        then []
        else concatMap (poly2default (optDefType opts)) $
               -- ignore already proved properties:
               filter (\fd -> funcName fd `notElem` map funcName theofuncs)
                      usertests ++
               (if optSpec opts then postCondTests ++ specOpTests else [])
  return (map snd realtests,
          map snd ignoredtests,
          CurryProg mname
                    (nub (easyCheckModule:imps))
                    dfltdecl clsdecls instdecls
                    typeDecls
                    (simpfuncs ++ map snd (realtests ++ ignoredtests))
                    opDecls)
 where
  (usertests, funcs) = partition isProperty functions


-- Extracts all determinism tests from a given Curry module and
-- transforms deterministic operations back into non-deterministic operations
-- in order to test their determinism property.
-- The result contains a triple consisting of all actual determinism tests,
-- all ignored tests (since they are polymorphic), and the public version
-- of the transformed original module.
transformDetTests :: Options -> [String] -> CurryProg
                  -> ([CFuncDecl],[CFuncDecl],CurryProg)
transformDetTests opts prooffiles
                  (CurryProg mname imports dfltdecl clsdecls instdecls
                             typeDecls functions opDecls) =
  (map snd realtests, map snd ignoredtests,
   CurryProg mname
             (nub (easyCheckModule:imports))
             dfltdecl clsdecls instdecls
             typeDecls
             (map (revertDetOpTrans detOpNames) functions ++
              map snd (realtests ++ ignoredtests))
             opDecls)
 where
  preCondOps = preCondOperations functions

  -- generate determinism tests:
  detOpTests = genDetOpTests prooffiles preCondOps functions

  -- names of deterministic operations:
  detOpNames = map (stripIsDet . funcName) detOpTests

  stripIsDet (mn,fn) = (mn, take (length fn -15) fn)

  (realtests,ignoredtests) = partition fst $
    if not (optProp opts)
    then []
    else concatMap (poly2default (optDefType opts))
                   (if optDet opts then detOpTests else [])

-- Get all operations with a defined precondition from a list of functions.
preCondOperations :: [CFuncDecl] -> [QName]
preCondOperations fdecls =
  map ((\ (mn,fn) -> (mn,fromPreCondName fn)) . funcName)
      (funDeclsWith isPreCondName fdecls)

-- Filter functions having a name satisfying a given predicate.
funDeclsWith :: (String -> Bool) -> [CFuncDecl] -> [CFuncDecl]
funDeclsWith pred = filter (pred . snd . funcName)

-- Transforms a function type into a property type, i.e.,
-- t1 -> ... -> tn -> t  is transformed into  t1 -> ... -> tn -> Prop
propResultType :: CTypeExpr -> CTypeExpr
propResultType te = case te of
  CFuncType from to -> CFuncType from (propResultType to)
  _                 -> baseType (easyCheckModule,"Prop")

-- Transforms a function declaration into a post condition test if
-- there is a post condition for this function (i.e., a relation named
-- f'post). The post condition test is of the form
-- fSatisfiesPostCondition x1...xn y = always (f'post x1...xn (f x1...xn))
genPostCondTest :: [QName] -> [QName] -> CFuncDecl -> [CFuncDecl]
genPostCondTest prefuns postops (CmtFunc _ qf ar vis texp rules) =
  genSpecTest prefuns postops (CFunc qf ar vis texp rules)
genPostCondTest prefuns postops
                (CFunc qf@(mn,fn) _ _ (CQualType clscon texp) _) =
 if qf `notElem` postops then [] else
  [CFunc (mn, fn ++ postCondSuffix) ar Public
    (CQualType clscon (propResultType texp))
    [simpleRule (map CPVar cvars) $
      if qf `elem` prefuns
       then applyF (easyCheckModule,"==>")
                   [applyF (mn,toPreCondName fn) (map CVar cvars), postprop]
       else postprop
    ]]
 where
  ar       = arityOfType texp
  cvars    = map (\i -> (i,"x"++show i)) [1 .. ar]
  rcall    = applyF qf (map CVar cvars)
  postprop = applyF (easyCheckModule,"always")
                    [applyF (mn,toPostCondName fn)
                            (map CVar cvars ++ [rcall])]

-- Transforms a function declaration into a specification test if
-- there is a specification for this function (i.e., an operation named
-- f'spec). The specification test is of the form
-- fSatisfiesSpecification x1...xn =
--   f'pre x1...xn  ==> (f x1...xn <~> f'spec x1...xn)
genSpecTest :: [QName] -> [QName] -> CFuncDecl -> [CFuncDecl]
genSpecTest prefuns specops (CmtFunc _ qf ar vis texp rules) =
  genSpecTest prefuns specops (CFunc qf ar vis texp rules)
genSpecTest prefuns specops
            (CFunc qf@(mn,fn) _ _ (CQualType clscon texp) _) =
 if qf `notElem` specops then [] else
  [CFunc (mn, fn ++ satSpecSuffix) ar Public
    (CQualType (addShowContext clscon) (propResultType texp))
    [simpleRule (map CPVar cvars) $
       addPreCond (applyF (easyCheckModule,"<~>")
                          [applyF qf (map CVar cvars),
                           applyF (mn,toSpecName fn) (map CVar cvars)])]]
 where
  cvars = map (\i -> (i,"x"++show i)) [1 .. ar]
  ar    = arityOfType texp

  addPreCond exp = if qf `elem` prefuns
                   then applyF (easyCheckModule,"==>")
                          [applyF (mn,toPreCondName fn) (map CVar cvars), exp]
                   else exp

-- Revert the transformation for deterministic operations performed
-- by currypp, i.e., replace rule "f x = selectValue (set f_ORGNDFUN x)"
-- with "f = f_ORGNDFUN".
revertDetOpTrans :: [QName] -> CFuncDecl -> CFuncDecl
revertDetOpTrans  detops (CmtFunc _ qf ar vis texp rules) =
  revertDetOpTrans detops (CFunc qf ar vis texp rules)
revertDetOpTrans detops fdecl@(CFunc qf@(mn,fn) ar vis texp _) =
  if qf `elem` detops
  then CFunc qf ar vis texp [simpleRule [] (constF (mn,fn++"_ORGNDFUN"))]
  else fdecl

-- Look for operations named f_ORGNDFUN and create a determinism property
-- for f.
genDetOpTests :: [String] -> [QName] -> [CFuncDecl] -> [CFuncDecl]
genDetOpTests prooffiles prefuns fdecls =
  map (genDetProp prefuns) (filter isDetOrgOp fdecls)
 where
  isDetOrgOp fdecl =
   let fn = snd (funcName fdecl)
    in "_ORGNDFUN" `isSuffixOf` fn &&
       not (existsProofFor (determinismTheoremFor (take (length fn - 9) fn))
                           prooffiles)

-- Transforms a declaration of a deterministic operation f_ORGNDFUN
-- into a determinisim property test of the form
-- fIsDeterministic x1...xn = f x1...xn #< 2
genDetProp :: [QName] -> CFuncDecl -> CFuncDecl
genDetProp prefuns (CmtFunc _ qf ar vis texp rules) =
  genDetProp prefuns (CFunc qf ar vis texp rules)
genDetProp prefuns (CFunc (mn,fn) ar _ (CQualType clscon texp) _) =
  CFunc (mn, forg ++ isDetSuffix) ar Public
   (CQualType (addShowContext clscon) (propResultType texp))
   [simpleRule (map CPVar cvars) $
      if (mn,forg) `elem` prefuns
       then applyF (easyCheckModule,"==>")
                   [applyF (mn,toPreCondName forg) (map CVar cvars), rnumcall]
       else rnumcall ]
 where
  forg     = take (length fn - 9) fn
  cvars    = map (\i -> (i,"x"++show i)) [1 .. ar]
  forgcall = applyF (mn,forg) (map CVar cvars)
  rnumcall = applyF (easyCheckModule,"#<") [forgcall, cInt 2]

-- Generates auxiliary (base-type instantiated) test functions for
-- polymorphically typed test function.
-- The flag indicates whether the test function should be actually passed
-- to the test tool.
poly2default :: String -> CFuncDecl -> [(Bool,CFuncDecl)]
poly2default dt (CmtFunc _ name arity vis ftype rules) =
  poly2default dt (CFunc name arity vis ftype rules)
poly2default dt fdecl@(CFunc (mn,fname) arity vis qftype rs)
  | isPolyType ftype
  = [(False,fdecl)
    ,(True, CFunc (mn,fname++defTypeSuffix) arity vis
                  (emptyClassType (poly2defaultType dt ftype))
                  [simpleRule [] (applyF (mn,fname) [])])
    ]
  | otherwise
  = [(True, CFunc (mn,fname) arity vis (CQualType clscon ftype) rs)]
 where
  CQualType clscon ftype = defaultQualType qftype

poly2defaultType :: String -> CTypeExpr -> CTypeExpr
poly2defaultType dt texp = p2dt texp 
 where
  p2dt (CTVar _)         = baseType (pre dt)
  p2dt (CFuncType t1 t2) = CFuncType (p2dt t1) (p2dt t2)
  p2dt (CTApply t1 t2)   = CTApply (p2dt t1) (p2dt t2)
  p2dt (CTCons ct)       = CTCons ct

-------------------------------------------------------------------------
-- Try to default a qualified type by replacing Num/Integral-constrained
-- types by Int and Fractional-constrained types by Float.
defaultQualType :: CQualTypeExpr -> CQualTypeExpr
defaultQualType (CQualType (CContext allclscon) ftype) =
  CQualType (CContext deffractxt) deffratype
 where
  (numcons,nonnumcons) =
    partition (\ (cls,te) -> (cls == pre "Num" || cls == pre "Integral")
                             && isTVar te)
              allclscon
  defnumtype = def2TConsInType numcons (pre "Int") ftype
  defnumctxt = removeNonTVarClassContexts
                 (map (\ (cls,con) ->
                                (cls, def2TConsInType numcons (pre "Int") con))
                      nonnumcons)

  (fracons,nonfracons) =
    partition (\ (cls,te) -> cls == pre "Fractional" && isTVar te) defnumctxt
  deffratype = def2TConsInType fracons (pre "Float") defnumtype
  deffractxt = removeNonTVarClassContexts
                 (map (\ (cls,con) ->
                              (cls, def2TConsInType fracons (pre "Float") con))
                      nonfracons)

  -- remove constant type class contexts
  removeNonTVarClassContexts = filter (\ (_,te) -> isTVar te)

  -- replace all type variables (occurring in the first list of class
  -- constraints) by the type constructor (second argument) in a given
  -- type expression (third argument)
  def2TConsInType clscons tcons texp =
    foldr (tvar2TCons tcons) texp (map snd clscons)

  -- substitute a type variable by type Int in a type
  tvar2TCons tcons texp = case texp of
    CTVar tv -> substTVar tv (CTCons tcons)
    _        -> id

  -- substitute a type variable by a type expression in a type expression:
  substTVar tvariname texp =
    trCTypeExpr (\tv -> if tv==tvariname then texp else CTVar tv)
                CTCons CFuncType CTApply

  isTVar te = case te of CTVar _ -> True
                         _       -> False

-- Add a "Show" class context to all types occurring in the context.
addShowContext :: CContext -> CContext
addShowContext (CContext clscons) =
  CContext (nub (clscons ++ (map (\t -> (pre "Show",t)) (map snd clscons))))

-------------------------------------------------------------------------

-- Transforms a possibly changed test name (like "test_ON_BASETYPE")
-- back to its original name.
orgTestName :: QName -> QName
orgTestName (mn,tname)
  | defTypeSuffix `isSuffixOf` tname
  = orgTestName (mn, stripSuffix tname defTypeSuffix)
  | isDetSuffix `isSuffixOf` tname
  = orgTestName (mn, take (length tname - 15) tname)
  | postCondSuffix `isSuffixOf` tname
  = orgTestName (mn, stripSuffix tname postCondSuffix)
  | satSpecSuffix `isSuffixOf` tname
  = orgTestName (mn, stripSuffix tname satSpecSuffix)
  | otherwise = (mn,tname)

-- This function implements the first phase of CurryCheck: it analyses
-- a module to be checked, i.e., it finds the tests, creates new tests
-- (e.g., for polymorphic properties, deterministic functions, post
-- conditions, specifications)
-- and generates a copy of the module appropriate for the main operation
-- of CurryCheck (e.g., all operations are made public).
-- If there are determinism tests, it also generates a second copy
-- where all deterministic functions are defined as non-deterministic
-- so that these definitions are tested.
analyseModule :: Options -> String -> IO [TestModule]
analyseModule opts modname = do
  putStrIfNormal opts $ withColor opts blue $
                        "Analyzing module '" ++ modname ++ "'...\n"
  catch (readCurryWithParseOptions modname (setQuiet True defaultParams) >>=
         analyseCurryProg opts modname)
        (\_ -> return [staticErrorTestMod modname
                         ["Module '"++modname++"': incorrect source program"]])

-- Analyse a Curry module for static errors:
staticProgAnalysis :: Options -> String -> String -> CurryProg
                   -> IO ([String],[(QName,String)])
staticProgAnalysis opts modname progtxt prog = do
  putStrIfDetails opts "Checking source code for static errors...\n"
  useerrs <- if optSource opts then checkBlacklistUse prog else return []
  seterrs <- if optSource opts then readFlatCurry modname >>= checkSetUse
                               else return []
  let defruleerrs = if optSource opts then checkDefaultRules prog else []
  untypedprog <- readUntypedCurry modname
  let detuseerrs   = if optSource opts then checkDetUse untypedprog else []
      contracterrs = checkContractUse prog
      staticerrs = concat [seterrs,useerrs,defruleerrs,detuseerrs,contracterrs]
      missingCPP =
       if (containsDefaultRules prog || containsDetOperations untypedprog)
          && not (containsPPOptionLine progtxt)
       then ["'" ++ modname ++
           "' uses default rules or det. operations but not the preprocessor!",
           "Hint: insert line: {-# OPTIONS_CYMAKE -F --pgmF=currypp #-}"]
       else []
  return (missingCPP,staticerrs)

-- Analyse a Curry module and generate property tests:
analyseCurryProg :: Options -> String -> CurryProg -> IO [TestModule]
analyseCurryProg opts modname orgprog = do
  -- First we rename all references to Test.Prop into Test.EasyCheck
  let prog = renameProp2EasyCheck orgprog
  (topdir,srcfilename) <- lookupModuleSourceInLoadPath modname >>=
        return .
        maybe (error $ "Source file of module '"++modname++"' not found!") id
  let srcdir = takeDirectory srcfilename
  putStrLnIfDebug opts $ "Source file: " ++ srcfilename
  prooffiles <- if optProof opts then getProofFiles srcdir else return []
  unless (null prooffiles) $ putStrIfDetails opts $
    unlines ("Proof files found:" : map ("- " ++) prooffiles)
  progtxt <- readFile srcfilename
  (missingCPP,staticoperrs) <- staticProgAnalysis opts modname progtxt prog
  let words      = map firstWord (lines progtxt)
      staticerrs = missingCPP ++ map (showOpError words) staticoperrs
  putStrIfDetails opts "Generating property tests...\n"
  (rawTests,ignoredTests,pubmod) <-
        transformTests opts srcdir . renameCurryModule (modname++"_PUBLIC")
                                   . makeAllPublic $ prog
  let (rawDetTests,ignoredDetTests,pubdetmod) =
        transformDetTests opts prooffiles
              . renameCurryModule (modname++"_PUBLICDET")
              . makeAllPublic $ prog
  unless (not (null staticerrs) || null rawTests && null rawDetTests) $
    putStrIfNormal opts $
      "Properties to be tested:\n" ++
      unwords (map (snd . funcName) (rawTests++rawDetTests)) ++ "\n"
  unless (not (null staticerrs) || null ignoredTests && null ignoredDetTests) $
    putStrIfNormal opts $
      "Properties ignored for testing:\n" ++
      unwords (map (snd . funcName) (ignoredTests++ignoredDetTests)) ++ "\n"
  let tm    = TestModule modname
                         (progName pubmod)
                         staticerrs
                         (addLinesNumbers words
                            (classifyTests opts pubmod rawTests))
                         (generatorsOfProg pubmod)
      dettm = TestModule modname
                         (progName pubdetmod)
                         []
                         (addLinesNumbers words
                            (classifyTests opts pubdetmod rawDetTests))
                         (generatorsOfProg pubmod)
  when (testThisModule tm) $ writeCurryProgram opts topdir pubmod ""
  when (testThisModule dettm) $ writeCurryProgram opts topdir pubdetmod ""
  return (if testThisModule dettm then [tm,dettm] else [tm])
 where
  showOpError words (qf,err) =
    snd qf ++ " (module " ++ modname ++ ", line " ++
    show (getLineNumber words qf) ++"): " ++ err

  addLinesNumbers words = map (addLineNumber words)

  addLineNumber :: [String] -> Test -> Test
  addLineNumber words (PropTest name texp _) =
    PropTest   name texp $ getLineNumber words (orgTestName name)
  addLineNumber words (IOTest name _) =
    IOTest name $ getLineNumber words (orgTestName name)
  addLineNumber words (EquivTest name f1 f2 texp _) =
    EquivTest name f1 f2 texp $ getLineNumber words (orgTestName name)

  getLineNumber :: [String] -> QName -> Int
  getLineNumber words (_, name) = maybe 0 (+1) (elemIndex name words)

-- Extracts all user-defined defined generators defined in a module.
generatorsOfProg :: CurryProg -> [QName]
generatorsOfProg = map funcName . filter isGen . functions
 where
   isGen fdecl = "gen" `isPrefixOf` snd (funcName fdecl) &&
                 isSearchTreeType (resultType (typeOfQualType (funcType fdecl)))

   isSearchTreeType (CTVar _)       = False
   isSearchTreeType (CFuncType _ _) = False
   isSearchTreeType (CTCons _)       = False
   isSearchTreeType te@(CTApply _ _) =
     maybe False ((==searchTreeTC) . fst) (tconsArgsOfType te)

-------------------------------------------------------------------------
-- Auxiliaries to support equivalence checking of operations.

-- Create data type with explicit bottom constructors.
genBottomType :: String -> FC.TypeDecl -> CTypeDecl
genBottomType _ (FC.TypeSyn _ _ _ _) =
  error "genBottomType: cannot translate type synonyms"
genBottomType mainmod (FC.Type qtc@(_,tc) _ tvars consdecls) =
  CType (mainmod,t2bt tc) Public (map transTVar tvars)
        (simpleCCons (mainmod,"Bot_"++transQN tc) Public [] :
         if isBasicExtType qtc
           then [simpleCCons (mainmod,"Value_"++tc) Public [baseType qtc]]
           else map transConsDecl consdecls)
        [(pre "Eq"),(pre "Show")]
 where
  transConsDecl (FC.Cons (_,cons) _ _ argtypes) =
    simpleCCons (mainmod,t2bt cons) Public (map transTypeExpr argtypes)

  transTypeExpr (FC.TVar i) = CTVar (transTVar i)
  transTypeExpr (FC.FuncType t1 t2) =
    CFuncType (transTypeExpr t1) (transTypeExpr t2)
  transTypeExpr (FC.TCons (_,tcons) tes) =
    applyTC (mainmod,t2bt tcons) (map transTypeExpr tes)
  transTypeExpr (FC.ForallType _ _) =
    error "genBottomType: cannot handle forall types"

  transTVar i = (i,'a':show i)

-- Is the type name an external basic prelude type?
isBasicExtType :: QName -> Bool
isBasicExtType (mn,tc) = mn == preludeName && tc `elem` ["Int","Float","Char"]

-- Default value for external basic prelude types.
defaultValueOfBasicExtType :: String -> CLiteral
defaultValueOfBasicExtType qn
  | qn == "Int"   = CIntc   0
  | qn == "Float" = CFloatc 0.0
  | qn == "Char"  = CCharc  'A'
  | otherwise     = error $ "defaultValueOfBasicExtType: unknown type: "++qn
  
ctype2BotType :: String -> CTypeExpr -> CTypeExpr
ctype2BotType _ (CTVar i) = CTVar i
ctype2BotType mainmod (CFuncType t1 t2) =
  CFuncType (ctype2BotType mainmod t1) (ctype2BotType mainmod t2)
ctype2BotType mainmod (CTApply t1 t2) =
  CTApply (ctype2BotType mainmod t1) (ctype2BotType mainmod t2)
ctype2BotType mainmod (CTCons qtc) =
  CTCons (mainmod, t2bt (snd qtc))

-- Translate a type constructor name to its bottom type constructor name
t2bt :: String -> String
t2bt s = "P_" ++ transQN s

-- Create `peval_` operation for a data type with explicit bottom constructors
-- according to the following scheme:
{-
peval_AB :: AB -> P_AB -> P_AB
peval_AB _ Bot_AB = Bot_AB                 -- no evaluation
peval_AB A P_A    = P_A
peval_AB B P_B    = P_B

peval_C :: C -> P_C -> P_C
peval_C _     Bot_C   = Bot_C              -- no evaluation
peval_C (C x) (P_C y) = P_C (peval_AB x y)

f_equiv_g x p = peval_C (f x) p <~> peval_C (g x) p
-}
genPeval :: String -> FC.TypeDecl -> CFuncDecl
genPeval _ (FC.TypeSyn _ _ _ _) =
  error "genPeval: cannot translate type synonyms"
genPeval mainmod (FC.Type qtc@(_,tc) _ tvars consdecls) =
  cmtfunc ("Evaluate a `"++tc++"` value up to a partial approxmiation.")
    (mainmod,"peval_"++transQN tc) 1 Public
    (emptyClassType
      (foldr1 (~>) (map (\ (a,b) -> CTVar a ~> CTVar b ~> CTVar b)
                        (zip polyavars polyrvars) ++
                    [applyTC qtc (map CTVar polyavars),
                     applyTC (mainmod,t2bt tc) (map CTVar polyrvars),
                     applyTC (mainmod,t2bt tc) (map CTVar polyrvars)])))
    (simpleRule (map CPVar (polyavars ++ [(0,"_")]) ++ [CPComb botSym []])
                (constF botSym) :
     if isBasicExtType qtc
       then [valueRule]
       else map genConsRule consdecls)
 where
  botSym = (mainmod,"Bot_"++transQN tc) -- bottom constructor
  
  -- variables for polymorphic type arguments:
  polyavars = [ (i,"a"++show i) | i <- tvars]
  polyrvars = [ (i,"b"++show i) | i <- tvars]
  
  genConsRule (FC.Cons qc@(_,cons) _ _ argtypes) =
    let args  = [(i,"x"++show i) | i <- [0 .. length argtypes - 1]]
        pargs = [(i,"y"++show i) | i <- [0 .. length argtypes - 1]]
        pcons = (mainmod,t2bt cons)
    in simpleRule (map CPVar polyavars ++
                   [CPComb qc (map CPVar args), CPComb pcons (map CPVar pargs)])
         (applyF pcons
                 (map (\ (e1,e2,te) ->
                        applyE (ftype2pvalOf mainmod "peval" polyavars te)
                               [e1,e2])
                      (zip3 (map CVar args) (map CVar pargs) argtypes)))

  valueRule =
    let xvar    = (0,"x")
        yvar    = (1,"y")
        valcons = (mainmod,"Value_"++tc)
    in guardedRule [CPVar xvar, CPComb valcons [CPVar yvar]]
                   [(constF (pre "True"), --applyF (pre "=:=") [CVar xvar, CVar yvar],
                     applyF valcons [CVar xvar])]
                   []

-- Create `pvalOf` operation for a data type with explicit bottom constructors
-- according to the following scheme:
{-
pvalOf_AB :: AB -> P_AB
pvalOf_AB _ = Bot_AB
pvalOf_AB A = P_A
pvalOf_AB B = P_B

pvalOf_C :: C -> P_C
pvalOf_C _     = Bot_C
pvalOf_C (C x) = P_C (pvalOf_AB x)

f_equiv_g x = pvalOf_C (f x) <~> pvalOf_C (g x)
-}
genPValOf :: String -> FC.TypeDecl -> CFuncDecl
genPValOf _ (FC.TypeSyn _ _ _ _) =
  error "genPValOf: cannot translate type synonyms"
genPValOf mainmod (FC.Type qtc@(_,tc) _ tvars consdecls) =
  cmtfunc ("Map a `"++tc++"` value into all its partial approxmiations.")
    (mainmod,"pvalOf_"++transQN tc) 1 Public
    (emptyClassType
      (foldr1 (~>) (map (\ (a,b) -> CTVar a ~> CTVar b)
                        (zip polyavars polyrvars) ++
                    [applyTC qtc (map CTVar polyavars),
                     applyTC (mainmod,t2bt tc) (map CTVar polyrvars)])))
    (simpleRule (map CPVar (polyavars ++ [(0,"_")]))
                (constF (mainmod,"Bot_"++transQN tc)) :
     if isBasicExtType qtc
       then [valueRule]
       else map genConsRule consdecls)
 where
  -- variables for polymorphic type arguments:
  polyavars = [ (i,"a"++show i) | i <- tvars]
  polyrvars = [ (i,"b"++show i) | i <- tvars]
  
  genConsRule (FC.Cons qc@(_,cons) _ _ argtypes) =
    let args = [(i,"x"++show i) | i <- [0 .. length argtypes - 1]]
    in simpleRule (map CPVar polyavars ++ [CPComb qc (map CPVar args)])
         (applyF (mainmod,t2bt cons)
            (map (\ (e,te) ->
                   applyE (ftype2pvalOf mainmod "pvalOf" polyavars te) [e])
                 (zip (map CVar args) argtypes)))

  valueRule =
    let var = (0,"x")
    in simpleRule [CPVar var] (applyF (mainmod,"Value_"++tc) [CVar var])

-- Translate a FlatCurry type into a corresponding call to `pvalOf`:
ftype2pvalOf :: String -> String -> [(Int,String)] -> FC.TypeExpr -> CExpr
ftype2pvalOf mainmod pvalname polyvars (FC.TCons (_,tc) texps) =
  applyF (mainmod,pvalname++"_"++transQN tc)
         (map (ftype2pvalOf mainmod pvalname polyvars) texps)
ftype2pvalOf _ _ _ (FC.FuncType _ _) =
  error "genPValOf: cannot handle functional types in as constructor args"
ftype2pvalOf _ _ polyvars (FC.TVar i) =
  maybe (error "genPValOf: unbound type variable")
        CVar
        (find ((==i) . fst) polyvars)
ftype2pvalOf _ _ _ (FC.ForallType _ _) =
  error "genPValOf: forall type occurred"

-- Translate an AbstractCurry type into a corresponding call to `pvalOf`:
ctype2pvalOf :: String -> String -> CTypeExpr -> CExpr
ctype2pvalOf mainmod pvalname (CTCons (_,tc)) =
  constF (mainmod,pvalname++"_"++transQN tc)
ctype2pvalOf mainmod pvalname te@(CTApply _ _) =
  maybe (error "genPValOf: cannot handle type applications")
        (\ ((_,tc),targs) -> applyF (mainmod,pvalname++"_"++transQN tc)
                                    (map (ctype2pvalOf mainmod pvalname) targs))
        (tconsArgsOfType te)
ctype2pvalOf _ _ (CFuncType _ _) =
  error "genPValOf: cannot handle functional types in as constructor args"
ctype2pvalOf _ _ (CTVar _) = error "genPValOf: unbound type variable"


-- Translate an AbstractCurry type declaration into a FlatCurry type decl:
ctypedecl2ftypedecl :: CTypeDecl -> FC.TypeDecl
ctypedecl2ftypedecl (CTypeSyn _ _ _ _) =
  error "ctypedecl2ftypedecl: cannot translate type synonyms"
ctypedecl2ftypedecl (CNewType _ _ _ _ _) =
  error "ctypedecl2ftypedecl: cannot translate newtype"
ctypedecl2ftypedecl (CType qtc _ tvars consdecls _) =
  FC.Type qtc FC.Public (map fst tvars) (map transConsDecl consdecls)
 where
  transConsDecl (CCons _ _ qc _ argtypes) =
    FC.Cons qc (length argtypes) FC.Public (map transTypeExpr argtypes)
  transConsDecl (CRecord _ _ _ _ _) =
    error "ctypedecl2ftypedecl: cannot translate records"

  transTypeExpr (CTVar (i,_)) = FC.TVar i
  transTypeExpr (CFuncType t1 t2) =
    FC.FuncType (transTypeExpr t1) (transTypeExpr t2)
  transTypeExpr (CTCons qtcons) = FC.TCons qtcons []
  transTypeExpr te@(CTApply _ _) =
    maybe (error "ctypedecl2ftypedecl: cannot translate type applications")
          (\ (qtcons,tes) -> FC.TCons qtcons (map transTypeExpr tes))
          (tconsArgsOfType te)

-------------------------------------------------------------------------
-- Create the main test module containing all tests of all test modules as
-- a Curry program with name `mainmod`.
-- The main test module contains a wrapper operation for each test
-- and a main function to execute these tests.
-- Furthermore, if PAKCS is used, test data generators
-- for user-defined types are automatically generated.
genMainTestModule :: Options -> String -> [TestModule] -> IO [Test]
genMainTestModule opts mainmod testmods = do
  let equivtestops = nub (concatMap equivTestOps (concatMap propTests testmods))
  terminfos <- if optEquiv opts == Autoselect
                 then getTerminationInfos opts (nub (map fst equivtestops))
                 else return (const False)
  prodinfos <- if optEquiv opts == Safe
                 then getProductivityInfos opts (nub (map fst equivtestops))
                 else return (const NoInfo)
  let testtypes = nub (concatMap userTestDataOfModule testmods)
  (fcprogs,testtypedecls) <- collectAllTestTypeDecls opts [] [] testtypes
  equvtypedecls <- collectAllTestTypeDecls opts fcprogs []
                     (map (\t->(t,True))
                          (nub (concatMap equivPropTypes testmods)))
                     >>= return . map fst . snd
  let bottypes  = map (genBottomType mainmod) equvtypedecls
      pevalfuns = map (genPeval mainmod) equvtypedecls
      pvalfuns  = map (genPValOf mainmod) equvtypedecls
      generators   = map (genTestDataGenerator mainmod)
                         (testtypedecls ++
                          map (\td -> (ctypedecl2ftypedecl td,False)) bottypes)
  testfuncs <- liftM concat
                 (mapM (genTestFuncs opts terminfos prodinfos mainmod) testmods)
  let mainFunction = genMainFunction opts mainmod testfuncs
      imports      = nub $ [ easyCheckModule, easyCheckExecModule
                           , searchTreeModule, generatorModule
                           , "AnsiCodes","Maybe","System","Profile"] ++
                           map (fst . fst) testtypes ++
                           map testModuleName testmods
  appendix <- readFile (packagePath </> "src" </> "TestAppendix.curry")
  writeCurryProgram opts "."
    (CurryProg mainmod imports Nothing [] [] bottypes
               (mainFunction : testfuncs ++ generators ++ pvalfuns ++ pevalfuns)
               [])
    appendix
  let (finaltests,droppedtests) =
         partition ((`elem` map (snd . funcName) testfuncs) . genTestName)
                   (concatMap propTests testmods)
  unless (null droppedtests) $ putStrIfNormal opts $
    "\nPOSSIBLY NON-TERMINATING TESTS REMOVED: " ++
    unwords (map (snd . testName) droppedtests) ++ "\n"
  return finaltests

-- Generates the main function which executes all property tests
-- of all test modules.
genMainFunction :: Options -> String -> [CFuncDecl] -> CFuncDecl
genMainFunction opts testModule testfuncs =
  CFunc (testModule, "main") 0 Public (emptyClassType (ioType unitType))
        [simpleRule [] body]
 where
  body = CDoExpr $
     (if isQuiet opts
        then []
        else [CSExpr (applyF (pre "putStrLn")
                             [string2ac "Executing all tests..."])]) ++
     [ CSPat (cpvar "x1") $ -- run all tests:
          applyF (testModule, "runPropertyTests")
                 [constF (pre (if optColor opts then "True" else "False")),
                  constF (pre (if optTime  opts then "True" else "False")),
                  list2ac $ map (constF . funcName) testfuncs]
     , CSExpr $ applyF (pre "when")
                  [applyF (pre "/=") [cvar "x1", cInt 0],
                   applyF ("System", "exitWith") [cvar "x1"]]
     ]

-------------------------------------------------------------------------
-- Collect all type declarations for a given list of type
-- constructor names, including the type declarations which are
-- used in these type declarations.
-- To cache already read FlatCurry programs, it gets a list of
-- FlatCurry programs (second argument) and returns a list of
-- FlatCurry programs.
collectAllTestTypeDecls :: Options -> [FC.Prog] -> [(FC.TypeDecl,Bool)]
                        -> [(QName,Bool)]
                        -> IO ([FC.Prog],[(FC.TypeDecl,Bool)])
collectAllTestTypeDecls opts fcprogs tdecls testtypenames = do
  newprogs <- readFlatProgsIfNecessary fcprogs (map (fst . fst) testtypenames)
  let newtesttypedecls = map (findTypeDecl newprogs) testtypenames
      alltesttypedecls = tdecls ++ newtesttypedecls
      newtcons = filter (\ ((mn,_),genpart) -> genpart || mn /= preludeName)
                        (nub (concatMap allTConsOfType newtesttypedecls)
                         \\ map (\(t,p) -> (FCG.typeName t,p)) alltesttypedecls)
  if null newtcons
    then return (newprogs,alltesttypedecls)
    else collectAllTestTypeDecls opts newprogs alltesttypedecls newtcons
 where
  readFlatProgsIfNecessary progs [] = return progs
  readFlatProgsIfNecessary progs (mn:mns) =
    if mn `elem` map FCG.progName progs
      then readFlatProgsIfNecessary progs mns
      else do putStrIfDetails opts $
                "Reading data types defined in module '" ++ mn ++ "'...\n"
              fprog <- readFlatCurry mn
              readFlatProgsIfNecessary (fprog:progs) mns
  
  -- gets the type declaration for a given type constructor
  -- (could be improved by caching programs that are already read)
  findTypeDecl :: [FC.Prog] -> (QName,Bool) -> (FC.TypeDecl,Bool)
  findTypeDecl fcyprogs (qt@(mn,_),genpartial) =
    let fprog = maybe (error $ "Cannot find module " ++ mn)
                      id
                      (find (\p -> FCG.progName p == mn) fcyprogs)
    in maybe (error $ "Definition of type '" ++ FC.showQNameInModule "" qt ++
                      "' not found!")
             (\td -> (td,genpartial))
             (find (\t -> FCG.typeName t == qt) (FCG.progTypes fprog))

  allTConsOfType :: (FC.TypeDecl,Bool) -> [(QName,Bool)]
  allTConsOfType (td,genpart) = map (\t->(t,genpart)) (allTConsInDecl td)

  -- compute all type constructors used in a type declaration
  allTConsInDecl :: FC.TypeDecl -> [QName]
  allTConsInDecl = FCG.trType (\_ _ _ -> concatMap allTConsInConsDecl)
                              (\_ _ _ -> allTConsInTypeExpr)

  allTConsInConsDecl :: FC.ConsDecl -> [QName]
  allTConsInConsDecl = FCG.trCons (\_ _ _ -> concatMap allTConsInTypeExpr)

  allTConsInTypeExpr :: FC.TypeExpr -> [QName]
  allTConsInTypeExpr =
    FCG.trTypeExpr (\_ -> []) (\tc targs -> tc : concat targs) (++) (flip const)

-- Creates a test data generator for a given type declaration.
-- If the flag of the type declaration is `True`, a generator
-- for partial values is created.
genTestDataGenerator :: String -> (FC.TypeDecl,Bool) -> CFuncDecl
genTestDataGenerator mainmod (tdecl,part) = type2genData tdecl
 where
  qt       = FCG.typeName tdecl
  qtString = FC.showQNameInModule "" qt

  type2genData (FC.TypeSyn _ _ _ _) =
    error $ "Cannot create generator for type synonym " ++ qtString
  type2genData (FC.Type _ _ tvars cdecls)
    | null cdecls && (fst qt /= preludeName || not part)
    = error $ "Cannot create value generator for type '" ++ qtString ++
              "' without constructors!"
    | otherwise
    = cmtfunc
        ("Generator for " ++ (if part then "partial " else "") ++
         "`" ++ qtString ++ "` values.")
        (typename2genopname mainmod [] part qt) (length tvars) Public
        (emptyClassType
          (foldr (~>) (CTApply (CTCons searchTreeTC) (applyTC qt ctvars))
                      (map (\v -> applyTC searchTreeTC [v]) ctvars)))
        [simpleRule (map CPVar cvars)
          (let gencstrs =  foldr1 (\e1 e2 -> applyF choiceGen [e1,e2])
                                  (map cons2gen cdecls)
           in if part
                then applyF choiceGen
                            [ applyF (generatorModule, "genCons0")
                                     [constF (pre "failed")]
                            , if null cdecls
                                then constF (generatorModule,
                                             "gen" ++ transQN (snd qt))
                                else gencstrs ]
                else gencstrs)]
   where
    cons2gen (FC.Cons qn@(mn,cn) ar _ ctypes)
      | ar>maxArity
      = error $ "Test data constructors with more than " ++ show maxArity ++
                " arguments are currently not supported!"
      | not part && mn == mainmod && "Value_" `isPrefixOf` cn
        -- specific generator for bottom types of external basic types
        -- like Int (actually, do not generate values in order to reduce
        -- search space):
      = applyF (generatorModule, "genCons1")
               [CSymbol qn,
                applyF (searchTreeModule,"Value")
                       [CLit (defaultValueOfBasicExtType (drop 6 cn))]]
      | otherwise
      = applyF (generatorModule, "genCons" ++ show ar)
               ([CSymbol qn] ++ map type2gen ctypes)

    type2gen (FC.TVar i) = CVar (i,"a"++show i)
    type2gen (FC.FuncType _ _) =
      error $ "Type '" ++ qtString ++
              "': cannot create value generators for functions!"
    type2gen (FC.TCons qtc argtypes) =
      applyF (typename2genopname mainmod [] part qtc) (map type2gen argtypes)
    type2gen (FC.ForallType _ _) =
      error $ "Type '" ++ qtString ++
              "': cannot create value generators for forall types!"

    ctvars = map (\i -> CTVar (i,"a"++show i)) tvars
    cvars  = map (\i -> (i,"a"++show i)) tvars

-------------------------------------------------------------------------
-- remove the generated files (except if option "--keep" is set)
cleanup :: Options -> String -> [TestModule] -> IO ()
cleanup opts mainmod modules =
  unless (optKeep opts) $ do
    removeCurryModule mainmod
    mapIO_ removeCurryModule (map testModuleName modules)
 where
  removeCurryModule modname = do
    (_,srcfilename) <- lookupModuleSourceInLoadPath modname >>=
        return .
        maybe (error $ "Source file of module '"++modname++"' not found!") id
    system $ installDir </> "bin" </> "cleancurry" ++ " " ++ modname
    system $ "rm -f " ++ srcfilename

-- Show some statistics about number of tests:
showTestStatistics :: [Test] -> String
showTestStatistics tests =
  let numtests  = sumOf (const True)
      unittests = sumOf isUnitTest  
      proptests = sumOf isPropTest  
      equvtests = sumOf isEquivTest 
      iotests   = sumOf isIOTest    
   in "TOTAL NUMBER OF TESTS: " ++ show numtests ++
      " (UNIT: " ++ show unittests ++ ", PROPERTIES: " ++
      show proptests ++ ", EQUIVALENCE: " ++ show equvtests ++
      ", IO: " ++ show iotests ++ ")"
 where
  sumOf p = length . filter p $ tests

-------------------------------------------------------------------------
main :: IO ()
main = do
  argv <- getArgs
  pid  <- getPID
  let (funopts, args, opterrors) = getOpt Permute options argv
  opts <- processOpts (foldl (flip id) defaultOptions funopts)
  unless (null opterrors)
         (putStr (unlines opterrors) >> putStrLn usageText >> exitWith 1)
  putStrIfNormal opts ccBanner
  when (null args || optHelp opts) (putStrLn usageText >> exitWith 1)
  let mods = map stripCurrySuffix args
  mapIO_ checkModuleName mods
  testModules <- mapIO (analyseModule opts) mods
  let staticerrs       = concatMap staticErrors (concat testModules)
      finaltestmodules = filter testThisModule (concat testModules)
      testmodname = if null (optMainProg opts)
                      then "TEST" ++ show pid
                      else optMainProg opts
  if not (null staticerrs)
   then do showStaticErrors opts staticerrs
           putStrLn $ withColor opts red "Testing aborted!"
           cleanup opts testmodname finaltestmodules
           exitWith 1
   else if null finaltestmodules then exitWith 0 else do
    putStrIfNormal opts $ withColor opts blue $
                          "Generating main test module '"++testmodname++"'..."
    putStrIfDetails opts "\n"
    finaltests <- genMainTestModule opts testmodname finaltestmodules
    showGeneratedModule opts "main test" testmodname
    putStrIfNormal opts $ withColor opts blue $ "and compiling it...\n"
    ecurrypath <- getEnviron "CURRYPATH"
    let currypath = case ecurrypath of ':':_ -> '.':ecurrypath
                                       _     -> ecurrypath
    let runcmd = unwords $
                   [ installDir </> "bin" </> "curry"
                   , "--noreadline"
                   , ":set -time"
                   , ":set " ++ if optVerb opts > 3 then "v1" else "v0"
                   , ":set parser -Wnone"
                   , if null currypath then "" else ":set path " ++ currypath
                   , ":l "++testmodname,":eval main :q" ]
    putStrLnIfDebug opts $ "Executing command:\n" ++ runcmd
    ret <- system runcmd
    cleanup opts testmodname finaltestmodules
    unless (isQuiet opts || ret /= 0) $
      putStrLn $ withColor opts green $ showTestStatistics finaltests
    exitWith ret
 where
  showStaticErrors opts errs = putStrLn $ withColor opts red $
    unlines (line : "STATIC ERRORS IN PROGRAMS:" : errs) ++ line

  checkModuleName mn =
    when (pathSeparator `elem` mn) $ do
      putStrLn $ "Module names with path prefixes not allowed: " ++ mn
      exitWith 1

  line = take 78 (repeat '=')

showGeneratedModule :: Options -> String -> String -> IO ()
showGeneratedModule opts mkind modname = when (optVerb opts > 3) $ do
  putStrLn $ '\n' : line
  putStrLn $ "Generated " ++ mkind ++ " module `" ++ modname ++ ".curry':"
  putStrLn line
  readFile (modname ++ ".curry") >>= putStr
  putStrLn line
 where
  line = take 78 (repeat '=')

-------------------------------------------------------------------------
-- Auxiliaries

-- Rename all module references to "Test.Prop" into "Test.EasyCheck"
renameProp2EasyCheck :: CurryProg -> CurryProg
renameProp2EasyCheck prog =
  updCProg id (map rnmMod) id id id id id id
           (updQNamesInCProg (\ (mod,n) -> (rnmMod mod,n)) prog)
 where
  rnmMod mod | mod == propModule = easyCheckModule
             | otherwise         = mod

-- Extracts the first word of a string
firstWord :: String -> String
firstWord = head . splitOn "\t" . head . splitOn " "

-- Strips a suffix from a string.
stripSuffix :: String -> String -> String
stripSuffix str suf = if suf `isSuffixOf` str
                      then take (length str - length suf) str
                      else str

-- Translate a module name to an identifier, i.e., replace '.' by '_':
modNameToId :: String -> String
modNameToId = intercalate "_" . split (=='.')

-- Computes the arity from a type expression.
arityOfType :: CTypeExpr -> Int
arityOfType = length . argTypes

--- Name of the SearchTree module.
searchTreeModule :: String
searchTreeModule = "SearchTree"

--- Name of SearchTree type constructor.
searchTreeTC :: QName
searchTreeTC = (searchTreeModule,"SearchTree")

--- Name of the SearchTreeGenerator module.
generatorModule :: String
generatorModule = "SearchTreeGenerators"

choiceGen :: QName
choiceGen = (generatorModule,"|||")

-- Writes a Curry module (together with an appendix) to its file.
writeCurryProgram :: Options -> String -> CurryProg -> String -> IO ()
writeCurryProgram opts srcdir p appendix = do
  let progfile = srcdir </> modNameToPath (progName p) ++ ".curry"
  putStrLnIfDebug opts $ "Writing program: " ++ progfile
  writeFile progfile
            (ACPretty.showCProg p ++ "\n" ++ appendix ++ "\n")

isPAKCS :: Bool
isPAKCS = curryCompiler == "pakcs"

-- Does a program text contains a OPTIONS_CYMAKE line to call currypp?
containsPPOptionLine :: String -> Bool
containsPPOptionLine = any isOptionLine . lines
 where
   isOptionLine s = "{-# OPTIONS_CYMAKE " `isPrefixOf` s -- -}
                    && "currypp" `isInfixOf` s

tconsOf :: CTypeExpr -> [QName]
tconsOf (CTVar _)           = []
tconsOf (CFuncType from to) = union (tconsOf from) (tconsOf to)
tconsOf (CTCons tc)         = [tc]
tconsOf (CTApply tc ta)     = union (tconsOf tc) (tconsOf ta)

unionOn :: Eq b => (a -> [b]) -> [a] -> [b]
unionOn f = foldr union [] . map f

-- Pretty print an AbstractCurry type expression:
showCTypeExpr :: CTypeExpr -> String
showCTypeExpr = pPrint . ACPretty.ppCTypeExpr ACPretty.defaultOptions

-- Pretty print an AbstractCurry expression:
showCExpr :: CExpr -> String
showCExpr = pPrint . ACPretty.ppCExpr ACPretty.defaultOptions

-------------------------------------------------------------------------
