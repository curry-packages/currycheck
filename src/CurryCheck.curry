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
--- @version February 2023
-------------------------------------------------------------------------

import Control.Monad               ( unless, when )
import Curry.Compiler.Distribution ( curryCompiler, installDir )
import Data.Char                   ( toUpper )
import Data.List
import Data.Maybe                  ( fromJust, isJust )
import System.Directory            ( createDirectoryIfMissing )
import System.FilePath             ( (</>), pathSeparator, takeDirectory )
import System.Console.GetOpt
import System.Environment          ( getArgs, setEnv )
import System.Process              ( system, exitWith, getPID )
import System.Console.ANSI.Codes

import AbstractCurry.Types
import AbstractCurry.Files     ( readCurryWithParseOptions, readUntypedCurry )
import AbstractCurry.Select
import AbstractCurry.Build
import qualified AbstractCurry.Pretty as ACPretty
import AbstractCurry.Transform ( renameCurryModule, trCTypeExpr, updCProg
                               , updQNamesInCProg, updQNamesInCFuncDecl )
import Analysis.Termination    ( Productivity(..) )
import Contract.Names
import Language.Curry.CheckDetUsage   ( checkDetUse, containsDetOperations )
import Language.Curry.CheckOperations ( checkBlacklistUse, checkSetUse )
import qualified FlatCurry.Types as FC
import FlatCurry.Files
import qualified FlatCurry.Goodies as FCG
import System.CurryPath    ( modNameToPath, lookupModuleSourceInLoadPath
                           , runModuleAction, stripCurrySuffix )
import System.FrontendExec ( defaultParams, setQuiet )
import Text.CSV            ( writeCSVFile )
import Text.Pretty         ( pPrint )

import CC.AnalysisHelpers ( getTerminationInfos, getProductivityInfos
                          , getUnsafeModuleInfos, dropPublicSuffix )
import CC.Config          ( packagePath, packageVersion )
import CC.Helpers         ( ccLoadPath )
import CC.Options
import Contract.Usage     ( checkContractUsage )
import DefaultRuleUsage   ( checkDefaultRules, containsDefaultRules )
import PropertyUsage
import SimplifyPostConds  ( simplifyPostConditionsWithTheorems )
import TheoremUsage       ( determinismTheoremFor, existsProofFor
                          , getModuleProofFiles, getTheoremFunctions )

-- Banner of this tool:
ccBanner :: String
ccBanner = unlines [bannerLine,bannerText,bannerLine]
 where
   bannerText = "CurryCheck: a tool for testing Curry programs (Version " ++
                packageVersion ++ " of 30/01/2024)"
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
genTestMsg file test = snd (testName test) ++ showModuleLine file (testLine test)

-- Shows module name and line (if not zero) in brackets.
showModuleLine :: String -> Int -> String
showModuleLine mname ln =
  " (module " ++ mname ++ if ln == 0 then ")"
                                     else ", line " ++ show ln ++ ")"

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
-- * the names of functions with preconditions defined in the test module
data TestModule = TestModule
  { orgModuleName  :: String
  , testModuleName :: String
  , staticErrors   :: [String]
  , propTests      :: [Test]
  , generators     :: [QName]
  , preConditions  :: [QName]
  }

-- A test module with only static errors.
staticErrorTestMod :: String -> [String] -> TestModule
staticErrorTestMod modname staterrs =
 TestModule modname modname staterrs [] [] []

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
  fmap (filter (not . null . funcRules))
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
    let xvars  = map (\i -> (i,"x" ++ show i)) [1 .. arityOfType texp]
        pxvars = map (\i -> (i,"px" ++ show i)) [1 .. arityOfType texp]
        pvalOfFunc = ctype2typeop mainmod "pvalOf_" (resultType texp)
    in propOrEquivBody
         (map (\t -> ctype2BotType mainmod False t) (argTypes texp))
         test
         (cLambda (map CPVar pxvars)
           (letExpr
            (map (\ (x,px,te) -> CLocalPat (CPVar x)
                       (CSimpleRhs (applyE (ctype2typeop mainmod "from_P_" te)
                                           [CVar px]) []))
                 (zip3 xvars pxvars (argTypes texp)))
            (addPreCond (preConditions tm) [f1,f2] xvars
              (applyF (easyCheckModule,"<~>")
                      [applyE pvalOfFunc [applyF f1 (map CVar xvars)],
                       applyE pvalOfFunc [applyF f2 (map CVar xvars)]]))))

  -- Operation equivalence test for arbitrary operations:
  equivBodyAny f1 f2 texp test =
    let xvars  = map (\i -> (i,"x" ++ show i))  [1 .. arityOfType texp]
        pxvars = map (\i -> (i,"px" ++ show i)) [1 .. arityOfType texp]
        pvar   = (2,"p")
        pvalOfFunc = ctype2typeop mainmod "peval_" (resultType texp)
    in propOrEquivBody
         (map (\t -> ctype2BotType mainmod False t) (argTypes texp) ++
          [ctype2BotType mainmod True (resultType texp)])
         test
         (cLambda (map CPVar pxvars ++ [CPVar pvar])
           (letExpr
            (map (\ (x,px,te) -> CLocalPat (CPVar x)
                       (CSimpleRhs (applyE (ctype2typeop mainmod "from_P_" te)
                                           [CVar px]) []))
                 (zip3 xvars pxvars (argTypes texp)))
            (addPreCond (preConditions tm) [f1,f2] xvars
              (applyF (easyCheckModule,"<~>")
                 [applyE pvalOfFunc [applyF f1 (map CVar xvars), CVar pvar],
                  applyE pvalOfFunc [applyF f2 (map CVar xvars), CVar pvar]]))))

  propBody qname texp test =
    propOrEquivBody (map (\t -> t) (argTypes texp))
                    test (CSymbol (testmname,snd qname))

  propOrEquivBody argtypes test propexp =
    [simpleRule [] $
      CLetDecl [CLocalPat (CPVar msgvar) (CSimpleRhs (msgOf test) [])]
               (applyF (easyCheckExecModule, "checkPropWithMsg")
                 [ CVar msgvar
                 , applyF (easyCheckFuncName (length argtypes)) $
                    [configOpWithMaxFail, CVar msgvar] ++
                    (map (\ t ->
                          applyF (easyCheckModule,"valuesOfSearchTree")
                            [if isPAKCS || useUserDefinedGen t || isFloatType t
                             then type2genop mainmod tm True t
                             else applyF (searchTreeModule,"someSearchTree")
                                         [CTyped (constF (pre "unknown"))
                                                 (emptyClassType t)]])
                         argtypes) ++
                    [transFuncArgsInProp mainmod argtypes propexp]
                 ])]
   where
    useUserDefinedGen texp = case texp of
      CTVar _       -> error "No polymorphic generator!"
      CFuncType _ _ -> True
      CTApply _ _   -> maybe (error "No generator for type applications!")
                             (\ (qt,_) -> hasDefinedGen qt)
                             (tconsArgsOfType texp)
      CTCons qt -> hasDefinedGen qt
     where
      hasDefinedGen (mn,tc) =
        isJust (find (\qn -> "gen"++tc == snd qn) (generators tm)) ||
        mn==mainmod && "_Constant" `isSuffixOf` tc

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
-- The fourth argument is `True` when top-level types are translated.
type2genop :: String -> TestModule -> Bool -> CTypeExpr -> CExpr
type2genop _ _ _ (CTVar _) = error "No polymorphic generator!"
type2genop mainmod tm top (CFuncType ta tb) =
  applyF (mainmod, if top then "genFunc" else "genFunction")
         (map (type2genop mainmod tm False) [ta,tb])
type2genop mainmod tm _ (CTCons qt) =
  constF (typename2genopname mainmod (generators tm) qt)
type2genop mainmod tm _ te@(CTApply _ _) =
  maybe (error "No generator for type applications!")
        (\ (qt,targs) ->
           applyF (typename2genopname mainmod (generators tm) qt)
                  (map (type2genop mainmod tm False) targs))
        (tconsArgsOfType te)

isFloatType :: CTypeExpr -> Bool
isFloatType texp = case texp of CTCons tc -> tc == (preludeName,"Float")
                                _         -> False

-- Translates the name of a type constructor into the name of the
-- generator operation for values of this type.
-- The first argument is the name of the main module.
-- The second argument contains the user-defined generator operations.
typename2genopname :: String -> [QName] -> QName -> QName
typename2genopname mainmod definedgenops (mn,tc)
  | isJust maybeuserdefined -- take user-defined generator:
  = fromJust maybeuserdefined
  | mn==preludeName
  = (generatorModule, "gen" ++ transQN tc)
  | otherwise -- we use our own generator:
  = (mainmod, "gen_" ++ modNameToId mn ++ "_" ++ transQN tc)
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
-- If some arguments of a property are functional, translate these
-- arguments (which have generated values of type `[(a,b)]`) into
-- a function by introducing let bindings and use `list2func`.
-- For instance, a property `p` with argument types `[(Int->Int), [Int]]`
-- is translated into the expression
--     \x1 x2 -> let fx1 = list2func x1 in p fx1 x2
transFuncArgsInProp :: String -> [CTypeExpr] -> CExpr -> CExpr
transFuncArgsInProp mainmod argtypes propexp
  | any isFunctionalType argtypes
  = CLambda (map CPVar vars)
            (let (nvars,locals) = unzip (map ftype2let (zip argtypes vars))
             in letExpr (concat locals) (applyE propexp (map CVar nvars)))
  | otherwise = propexp
 where
  vars = map (\i -> (i,"x" ++ show i)) [1 .. length argtypes]

  ftype2let (texp,v@(j,xj)) =
    if isFunctionalType texp
      then let fx = (j + length argtypes, 'f':xj)
           in (fx,
               [CLocalPat (CPVar fx)
                  (CSimpleRhs (applyF (mainmod,"list2Func") [CVar v]) [])])
      else (v,[])

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

-- Classify the test represented by a function declaration
-- as either PropTest or IOTest.
classifyTest :: Options -> CurryProg -> CFuncDecl -> Test
classifyTest opts prog test =
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
    (e1,e2) -> error $ "Illegal equivalence property '" ++
                       snd tname ++ "':\n" ++
                       showCExpr e1 ++ " <=> " ++ showCExpr e2

  defaultingType = poly2defaultType opts . typeOfQualType . defaultQualType
  
  funcTypeOf f = maybe (error $ "Cannot find type of " ++ show f ++ "!")
                       funcType
                       (find (\fd -> funcName fd == f) (functions prog))

-- Extracts all tests from a given Curry module and transforms
-- all polymorphic tests into tests on a base type.
-- The second argument contains the names of existing proof files.
-- It is used to ignore tests when the properties are already proved.
-- The third argument contains the list of function representing
-- proved properties. It is used to simplify post conditions to be tested.
-- The result contains a tuple consisting of all actual tests,
-- all ignored tests, the name of all operations with defined preconditions
-- (needed to generate meaningful equivalence tests),
-- and the public version of the original module.
transformTests :: Options -> [String] -> [CFuncDecl] -> CurryProg
               -> IO ([CFuncDecl],[CFuncDecl],[QName],CurryProg)
transformTests opts prfnames theofuncs
               prog@(CurryProg mname imps dfltdecl clsdecls instdecls
                               typeDecls functions opDecls) = do
  simpfuncs <- simplifyPostConditionsWithTheorems (optVerb opts) theofuncs funcs
  let preCondOps  = preCondOperations simpfuncs
      postCondOps = map ((\ (mn,fn) -> (mn, fromPostCondName fn)) . funcName)
                        (funDeclsWith isPostCondName simpfuncs)
      specOps     = map ((\ (mn,fn) -> (mn, fromSpecName fn)) . funcName)
                        (funDeclsWith isSpecName simpfuncs)
      -- generate post condition tests:
      postCondTests =
        concatMap (genPostCondTest preCondOps postCondOps prfnames) funcs
      -- generate specification tests:
      specOpTests   = concatMap (genSpecTest opts preCondOps specOps prfnames) funcs
      grSpecOpTests = if optEquiv opts == Ground then specOpTests else []

      (realtests,ignoredtests) = partition fst $
        if not (optProp opts)
        then []
        else concatMap (poly2default opts) $
               -- ignore already proved properties:
               filter (\fd -> not (existsProofFor (orgQName (funcName fd))
                                                  prfnames))
                      usertests ++
               (if optSpec opts then grSpecOpTests ++ postCondTests else [])
  return (map snd realtests ++
          (if optSpec opts && optEquiv opts /= Ground then specOpTests else []),
          map snd ignoredtests,
          preCondOps,
          CurryProg mname
                    (nub (easyCheckModule:imps))
                    dfltdecl clsdecls instdecls
                    typeDecls
                    (simpfuncs ++ map snd (realtests ++ ignoredtests))
                    opDecls)
 where
  (rawusertests, funcs) = partition isProperty functions

  usertests = if optEquiv opts == Ground
                then map equivProp2Ground rawusertests
                else rawusertests

  -- transform an equivalence property (f1 <=> f2) into a property
  -- testing ground equivalence, i.e., f1 x1...xn <~> f2 x1...xn
  equivProp2Ground fdecl =
    maybe fdecl
          (\ _ -> case classifyTest opts prog fdecl of
            EquivTest _ f1 f2 texp _ ->
             let ar    = arityOfType texp
                 cvars = map (\i -> (i,"x" ++ show i)) [1 .. ar]
             in stFunc (funcName fdecl) ar Public (propResultType texp)
                  [simpleRule (map CPVar cvars)
                              (applyF (easyCheckModule,"<~>")
                                      [applyF f1 (map CVar cvars),
                                       applyF f2 (map CVar cvars)])]
            _ -> error "transformTests: internal error"
          )
          (isEquivProperty fdecl)

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
    else concatMap (poly2default opts)
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
  _                 -> baseType (propTypesModule,"Prop")

-- Transforms a function declaration into a post condition test if
-- there is a post condition for this function (i.e., a relation named
-- f'post) and there is no proof file for this post condition.
-- The generated post condition test is of the form
--     fSatisfiesPostCondition x1...xn y = always (f'post x1...xn (f x1...xn))
genPostCondTest :: [QName] -> [QName] -> [String] -> CFuncDecl -> [CFuncDecl]
genPostCondTest prefuns postops prooffnames (CmtFunc _ qf ar vis texp rules) =
  genPostCondTest prefuns postops prooffnames (CFunc qf ar vis texp rules)
genPostCondTest prefuns postops prooffnames
                (CFunc qf@(mn,fn) _ _ (CQualType clscon texp) _) =
 if qf `notElem` postops || existsProofFor (orgQName postname) prooffnames
   then []
   else
  [CFunc postname ar Public
    (CQualType clscon (propResultType texp))
    [simpleRule (map CPVar cvars) $
       addPreCond prefuns [qf] cvars postprop ]]
 where
  postname = (mn, fn ++ postCondSuffix) -- name of generated post cond. test
  ar       = arityOfType texp
  cvars    = map (\i -> (i,"x" ++ show i)) [1 .. ar]
  rcall    = applyF qf (map CVar cvars)
  postprop = applyF (easyCheckModule,"always")
                    [applyF (mn,toPostCondName fn)
                            (map CVar cvars ++ [rcall])]

-- Transforms a function declaration into a specification test if
-- there is a specification for this function (i.e., an operation named
-- f'spec). The generated specification test has the form
--     fSatisfiesSpecification = f <=> f'spec
genSpecTest :: Options -> [QName] -> [QName] -> [String] -> CFuncDecl
            -> [CFuncDecl]
genSpecTest opts prefuns specops prooffnames (CmtFunc _ qf ar vis texp rules) =
  genSpecTest opts prefuns specops prooffnames (CFunc qf ar vis texp rules)
genSpecTest opts prefuns specops prooffnames
            (CFunc qf@(mn,fn) _ _ (CQualType clscon texp) _)
 | qf `notElem` specops || existsProofFor (orgQName sptname) prooffnames
 = []
 | optEquiv opts == Ground
 = [genSpecGroundEquivTest prefuns qf clscon texp]
 | otherwise
 = [CFunc sptname 0 Public
          (emptyClassType (propResultType unitType))
          [simpleRule [] (applyF (easyCheckModule,"<=>")
                                 [constF qf, constF (mn,toSpecName fn)])]]
 where
  sptname = (mn, fn ++ satSpecSuffix) -- name of generated specification test

-- Transforms a function declaration into a ground equivalence test
-- against the specification (i.e., an operation named `f'spec` exists).
-- The generated specification test is of the form
-- fSatisfiesSpecification x1...xn =
--   f'pre x1...xn  ==> (f x1...xn <~> f'spec x1...xn)
genSpecGroundEquivTest :: [QName] -> QName -> CContext -> CTypeExpr -> CFuncDecl
genSpecGroundEquivTest prefuns qf@(mn,fn) clscon texp =
  CFunc (mn, fn ++ satSpecSuffix) ar Public
    (CQualType (addShowContext clscon) (propResultType texp))
    [simpleRule (map CPVar cvars) $
       addPreCond prefuns [qf,qfspec] cvars
         (applyF (easyCheckModule,"<~>")
                 [applyF qf (map CVar cvars),
                  applyF (mn,toSpecName fn) (map CVar cvars)])]
 where
  ar     = arityOfType texp
  cvars  = map (\i -> (i,"x" ++ show i)) [1 .. ar]
  qfspec = (mn, toSpecName fn)

-- Adds the preconditions of operations (second argument), if they are
-- present in the list of functions with preconditions in the first argument,
-- on the given variables to the property expression `propexp`.
addPreCond :: [QName] -> [QName] -> [CVarIName] -> CExpr -> CExpr
addPreCond prefuns fs pvars propexp =
 let preconds = concatMap precondCall fs
 in if null preconds
      then propexp
      else applyF (easyCheckModule,"==>")
                  [foldr1 (\x y -> applyF (pre "&&") [x,y]) preconds, propexp]
 where
  precondCall qn@(mn,fn) =
    if qn `elem` prefuns
      then [applyF (mn, toPreCondName fn) (map CVar pvars)]
      else []

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
  map (genDetProp prefuns) (filter (isDetOrgOp . funcName) fdecls)
 where
  isDetOrgOp (mn,fn) =
    "_ORGNDFUN" `isSuffixOf` fn &&
    not (existsProofFor (mnorg, determinismTheoremFor (take (length fn - 9) fn))
                        prooffiles)
   where mnorg = take (length mn - 10) mn -- remove _PUBLICDET suffix

-- Transforms a declaration of a deterministic operation f_ORGNDFUN
-- into a determinisim property test of the form
-- fIsDeterministic x1...xn = f x1...xn #< 2
genDetProp :: [QName] -> CFuncDecl -> CFuncDecl
genDetProp prefuns (CmtFunc _ qf ar vis texp rules) =
  genDetProp prefuns (CFunc qf ar vis texp rules)
genDetProp prefuns (CFunc (mn,fn) ar _ (CQualType clscon texp) _) =
  CFunc (mn, forg ++ isDetSuffix) ar Public
   (CQualType (foldr addEqShowContext (addShowContext clscon) rtypevars)
              (propResultType texp))
   [simpleRule (map CPVar cvars) $
      addPreCond prefuns [(mn,forg)] cvars rnumcall ]
 where
  rtypevars = tvarsOfType (resultType texp)
  forg      = take (length fn - 9) fn
  cvars     = map (\i -> (i,"x" ++ show i)) [1 .. ar]
  forgcall  = applyF (mn,forg) (map CVar cvars)
  rnumcall  = applyF (easyCheckModule,"#<") [forgcall, cInt 2]

-- Generates auxiliary (base-type instantiated) test functions for
-- polymorphically typed test function.
-- The returned flag indicates whether the test function should actually
-- be passed to the test tool.
-- For instance, polymorphic proprerties are not tested, but only
-- their type-instantiated variants.
poly2default :: Options -> CFuncDecl -> [(Bool,CFuncDecl)]
poly2default opts (CmtFunc _ name arity vis ftype rules) =
  poly2default opts (CFunc name arity vis ftype rules)
poly2default opts fdecl@(CFunc (mn,fname) arity vis qftype rs)
  | isPolyType ftype
  = [(False,fdecl)
    ,(True, CFunc (mn,fname++defTypeSuffix) arity vis
                  (emptyClassType (poly2defaultType opts ftype))
                  [simpleRule [] (applyF (mn,fname) [])])
    ]
  | otherwise
  = [(True, CFunc (mn,fname) arity vis (CQualType clscon ftype) rs)]
 where
  CQualType clscon ftype = defaultQualType qftype

poly2defaultType :: Options -> CTypeExpr -> CTypeExpr
poly2defaultType opts texp = p2dt texp 
 where
  p2dt (CTVar _)         = baseType (pre (optDefType opts))
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

-- Adds a "Show" class context to all types occurring in the context.
addShowContext :: CContext -> CContext
addShowContext (CContext clscons) =
  CContext (nub (clscons ++ (map (\t -> (pre "Show",t)) (map snd clscons))))

-- Adds `Eq` and `Show` class contexts for the given type variable.
addEqShowContext :: CTVarIName -> CContext -> CContext
addEqShowContext tvar (CContext clscons) =
  CContext (nub (clscons ++ map (\c -> (pre c, CTVar tvar)) ["Eq","Show"]))

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

-- Transforms a possibly changed qualified name, e.g., `("Mod_PUBLIC","f")`
-- or `("Mod_PUBLICDET","f")`, back to its original name by removing the
-- module suffix.
orgQName :: QName -> QName
orgQName (mn,fn)
  | publicSuffix `isSuffixOf` mn
  = (stripSuffix mn publicSuffix, fn)
  | publicdetSuffix `isSuffixOf` mn
  = (stripSuffix mn publicdetSuffix, fn)
  | otherwise = (mn,fn)
 where
  publicSuffix    = "_PUBLIC"
  publicdetSuffix = "_PUBLICDET"

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
  let parserparams = if optVerb opts < 2
                       then setQuiet True defaultParams
                       else defaultParams
  catch (readCurryWithParseOptions modname parserparams >>=
         analyseCurryProg opts modname)
        (\err -> return
           [staticErrorTestMod modname
              ["Module '" ++ modname ++ "': incorrect source program:\n" ++
               "ERROR: " ++ show err]])

-- Analyse a Curry module for static errors:
staticProgAnalysis :: Options -> String -> String -> CurryProg
                   -> IO ([String],[(QName,String)])
staticProgAnalysis opts modname progtxt prog = do
  putStrIfDetails opts "Checking source code for static errors...\n"
  fcyprog <- readFlatCurry modname
  useerrs <- if optSource opts then checkBlacklistUse prog else return []
  seterrs <- if optSource opts then checkSetUse fcyprog
                               else return []
  let defruleerrs = if optSource opts then checkDefaultRules prog else []
  untypedprog <- readUntypedCurry modname
  let detuseerrs   = if optSource opts then checkDetUse untypedprog else []
      contracterrs = checkContractUsage modname
                       (map (\fd -> (snd (FCG.funcName fd), FCG.funcType fd))
                            (FCG.progFuncs fcyprog))
      staticerrs = concat [seterrs,useerrs,defruleerrs,detuseerrs,contracterrs]
      missingCPP =
       if (containsDefaultRules prog || containsDetOperations untypedprog)
          && not (containsPPOptionLine progtxt)
       then ["'" ++ modname ++
           "' uses default rules or det. operations but not the preprocessor!",
           "Hint: insert line: {-# OPTIONS_FRONTEND -F --pgmF=currypp #-}"]
       else []
  return (missingCPP,staticerrs)

-- Analyse a Curry module and generate property tests:
analyseCurryProg :: Options -> String -> CurryProg -> IO [TestModule]
analyseCurryProg opts modname orgprog = do
  -- First we rename all references to Test.Prop into Test.EasyCheck
  let prog = renameProp2EasyCheck orgprog
  (topdir,srcfilename) <- lookupModuleSourceInLoadPath modname >>=
        return .
        maybe (error $ "Source file of module '" ++ modname ++ "' not found!")
              id
  let srcdir = takeDirectory srcfilename
  putStrLnIfDebug opts $ "Source file: " ++ srcfilename
  prooffiles <- if optProof opts
                  then getModuleProofFiles srcdir modname
                  else return []
  unless (null prooffiles) $ putStrIfDetails opts $
    unlines ("Proof files found:" : map ("- " ++) prooffiles)
  progtxt <- readFile srcfilename
  (missingCPP,staticoperrs) <- staticProgAnalysis opts modname progtxt prog
  let words      = map firstWord (lines progtxt)
      staticerrs = missingCPP ++ map (showOpError words) staticoperrs
  putStrIfDetails opts "Generating property tests...\n"
  theofuncs <- if optProof opts then getTheoremFunctions srcdir prog
                                else return []
  -- compute already proved theorems for public module:
  let pubmodname = modname++"_PUBLIC"
      rnm2pub mn@(mod,n) | mod == modname = (pubmodname,n)
                         | otherwise      = mn
      theopubfuncs = map (updQNamesInCFuncDecl rnm2pub) theofuncs
  (rawTests,ignoredTests,preCondOps,pubmod) <-
        transformTests opts prooffiles theopubfuncs
          . renameCurryModule pubmodname . makeAllPublic $ prog
  let (rawDetTests,ignoredDetTests,pubdetmod) =
        transformDetTests opts prooffiles
              . renameCurryModule (modname ++ "_PUBLICDET")
              . makeAllPublic $ prog
  unless (not (null staticerrs) || null rawTests && null rawDetTests) $
    putStrIfNormal opts $
      "Properties to be tested:\n" ++
      unwords (map (snd . funcName) (rawTests ++ rawDetTests)) ++ "\n"
  unless (not (null staticerrs) || null ignoredTests && null ignoredDetTests) $
    putStrIfNormal opts $
      "Properties ignored for testing:\n" ++
      unwords (map (snd . funcName) (ignoredTests ++ ignoredDetTests)) ++ "\n"
  let tm    = TestModule modname
                         (progName pubmod)
                         staticerrs
                         (addLinesNumbers words
                            (map (classifyTest opts pubmod) rawTests))
                         (generatorsOfProg pubmod)
                         preCondOps
      dettm = TestModule modname
                         (progName pubdetmod)
                         []
                         (addLinesNumbers words
                            (map (classifyTest opts pubdetmod) rawDetTests))
                         (generatorsOfProg pubmod)
                         []
  when (testThisModule tm) $ writeCurryProgram opts topdir pubmod ""
  when (testThisModule dettm) $ writeCurryProgram opts topdir pubdetmod ""
  return (if testThisModule dettm then [tm,dettm] else [tm])
 where
  showOpError words (qf,err) =
    snd qf ++ showModuleLine modname (getLineNumber words qf) ++ ": " ++ err

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

   isSearchTreeType (CTVar _)        = False
   isSearchTreeType (CFuncType _ _)  = False
   isSearchTreeType (CTCons _)       = False
   isSearchTreeType te@(CTApply _ _) =
     maybe False ((==searchTreeTC) . fst) (tconsArgsOfType te)

-------------------------------------------------------------------------
-- Auxiliaries to support equivalence checking of operations.

-- Create data type with explicit bottom constructors.
genBottomType :: String -> FC.TypeDecl -> CTypeDecl
genBottomType _ (FC.TypeSyn _ _ _ _) =
  error "genBottomType: cannot translate type synonyms"
genBottomType _ (FC.TypeNew _ _ _ _) =
  error "genBottomType: cannot translate newtypes"
genBottomType mainmod (FC.Type qtc@(_,tc) _ tvars consdecls) =
  CType (mainmod,t2bt tc) Public (map (transTVar . fst) tvars)
        (simpleCCons (mainmod,"Bot_"++transQN tc) Public [] :
         if isPrimExtType qtc
           then [simpleCCons (mainmod,"Value_"++tc) Public [baseType qtc]]
           else map transConsDecl consdecls)
        [pre "Eq"]
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

-- Is the type name an external primitive prelude type?
isPrimExtType :: QName -> Bool
isPrimExtType (mn,tc) = mn == preludeName && tc `elem` ["Int","Float","Char"]

-- Default value for external basic prelude types.
defaultValueOfBasicExtType :: String -> CLiteral
defaultValueOfBasicExtType tn
  | tn == "Int"   = CIntc   0
  | tn == "Float" = CFloatc 0.0
  | tn == "Char"  = CCharc  'A'
  | otherwise     = error $ "defaultValueOfBasicExtType: unknown type: "++tn

-- Translates a type expression into a similar one where type names
-- are replaced by corresponding bottom type names, e.g., `(Prelude,Ordering)`
-- will be replaced by `(mainmod,P_Ordering)`.
-- If the second argument is `True`, primitive types, like `Int`,
-- will be replaced by `P_Int_Constant` (to select partial constant value
-- generators).
ctype2BotType :: String -> Bool -> CTypeExpr -> CTypeExpr
ctype2BotType _ _ (CTVar i) = CTVar i
ctype2BotType mainmod con (CFuncType t1 t2) =
  CFuncType (ctype2BotType mainmod con t1) (ctype2BotType mainmod con t2)
ctype2BotType mainmod con (CTApply t1 t2) =
  CTApply (ctype2BotType mainmod con t1) (ctype2BotType mainmod con t2)
ctype2BotType mainmod con (CTCons qtc) =
  CTCons (mainmod, t2bt (snd qtc) ++
                   if con && isPrimExtType qtc then "_Constant" else "")

-- Translate a type constructor name to its bottom type constructor name
t2bt :: String -> String
t2bt s = "P_" ++ transQN s

-------------------------------------------------------------------------
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
genPeval _ (FC.TypeNew _ _ _ _) =
  error "genPeval: cannot translate newtypes"
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
     if isPrimExtType qtc
       then [valueRule]
       else map genConsRule consdecls)
 where
  botSym = (mainmod, "Bot_" ++ transQN tc) -- bottom constructor
  
  -- variables for polymorphic type arguments:
  polyavars = [ (i,"a" ++ show i) | i <- map fst tvars]
  polyrvars = [ (i,"b" ++ show i) | i <- map fst tvars]
  
  genConsRule (FC.Cons qc@(_,cons) _ _ argtypes) =
    let args  = [(i,"x" ++ show i) | i <- [0 .. length argtypes - 1]]
        pargs = [(i,"y" ++ show i) | i <- [0 .. length argtypes - 1]]
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

-------------------------------------------------------------------------
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
genPValOf _ (FC.TypeNew _ _ _ _) =
  error "genPValOf: cannot translate newtypes"
genPValOf mainmod (FC.Type qtc@(_,tc) _ tvars consdecls) =
  cmtfunc ("Map a `"++tc++"` value into all its partial approximations.")
    (mainmod,"pvalOf_"++transQN tc) 1 Public
    (emptyClassType
      (foldr1 (~>) (map (\ (a,b) -> CTVar a ~> CTVar b)
                        (zip polyavars polyrvars) ++
                    [applyTC qtc (map CTVar polyavars),
                     applyTC (mainmod,t2bt tc) (map CTVar polyrvars)])))
    (simpleRule (map CPVar (polyavars ++ [(0,"_")]))
                (constF (mainmod,"Bot_"++transQN tc)) :
     if isPrimExtType qtc
       then [valueRule]
       else map genConsRule consdecls)
 where
  -- variables for polymorphic type arguments:
  polyavars = [ (i,"a" ++ show i) | i <- map fst tvars]
  polyrvars = [ (i,"b" ++ show i) | i <- map fst tvars]
  
  genConsRule (FC.Cons qc@(_,cons) _ _ argtypes) =
    let args = [(i,"x" ++ show i) | i <- [0 .. length argtypes - 1]]
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

-- Translate an AbstractCurry type into a corresponding call to the
-- given type-structured operation defined in mainmod,
-- e.g., `pvalOf_` or `from_P_`:
ctype2typeop :: String -> String -> CTypeExpr -> CExpr
ctype2typeop mainmod opname (CTCons (_,tc)) =
  constF (mainmod,opname++transQN tc)
ctype2typeop mainmod opname te@(CTApply _ _) =
  maybe (error "genPValOf: cannot handle type applications")
        (\ ((_,tc),targs) -> applyF (mainmod,opname++transQN tc)
                                    (map (ctype2typeop mainmod opname) targs))
        (tconsArgsOfType te)
ctype2typeop _ _ (CFuncType _ _) =
  error "genPValOf: cannot handle functional types in as constructor args"
ctype2typeop _ _ (CTVar _) = error "genPValOf: unbound type variable"


-------------------------------------------------------------------------
-- Create a instance declaration for `Show` for a data type with
-- explicit bottom constructors according to the following scheme:
{-
instance Show P_AB where
  show Bot_AB = "failed"
  show P_A    = "A"
  show P_B    = "B"
  
instance Show P_C where
  show Bot_C   = "failed"
  show (P_C x) = "(C" ++ show x ")"

-}
genShowP :: String -> FC.TypeDecl -> CInstanceDecl
genShowP _ (FC.TypeSyn _ _ _ _) =
  error "genShowP: cannot translate type synonyms"
genShowP _ (FC.TypeNew _ _ _ _) =
  error "genShowP: cannot translate newtypes"
genShowP mainmod (FC.Type qtc@(_,tc) _ tvars consdecls) =
  CInstance (pre "Show")
            (CContext (map (\tv -> (pre "Show", CTVar tv)) polyavars))
            [applyTC (mainmod,t2bt tc) (map CTVar polyavars)]
   [cfunc
    (pre "show") 1 Public
    (emptyClassType
      (applyTC (mainmod,t2bt tc) (map CTVar polyavars) ~> stringType))
    (simpleRule [CPComb (mainmod, "Bot_" ++ transQN tc) []]
                (constF (mainmod, "bottomValue")) :
     if isPrimExtType qtc
       then [valueRule]
       else map genConsRule consdecls)]
 where
  -- variables for polymorphic type arguments:
  polyavars = [ (i,"a" ++ show i) | i <- map fst tvars]
  
  genConsRule (FC.Cons (_,cons) _ _ argtypes) =
    let args = [(i,"x" ++ show i) | i <- [0 .. length argtypes - 1]]
        showargs = map (\v -> applyF (pre "show") [CVar v]) args
    in simpleRule [CPComb (mainmod,t2bt cons) (map CPVar args)]
         (if null showargs
            then string2ac cons
            else applyF (mainmod,"constrValue")
                        [list2ac (string2ac cons : showargs)])

  valueRule =
    let var = (0,"x")
    in simpleRule [CPComb (mainmod,"Value_"++tc) [CPVar var]]
                  (applyF (pre "show") [CVar var])

-------------------------------------------------------------------------
-- Create `from_P_` operation for a data type with explicit bottom constructors
-- according to the following scheme:
{-
from_P_AB :: P_AB -> AB
from_P_AB Bot_AB = failed
from_P_AB P_A    = A
from_P_AB P_B    = B

from_P_C :: C -> P_C
from_P_C Bot_C   = failed
from_P_C (P_C x) = C (from_P_AB x)

-}
genFromP :: String -> FC.TypeDecl -> CFuncDecl
genFromP _ (FC.TypeSyn _ _ _ _) =
  error "genFromP: cannot translate type synonyms"
genFromP _ (FC.TypeNew _ _ _ _) =
  error "genFromP: cannot translate newtypes"
genFromP mainmod (FC.Type qtc@(_,tc) _ tvars consdecls) =
  cmtfunc ("Map a partial `"++tc++"` value into its real value (or fail).")
    (mainmod,"from_P_"++transQN tc) 1 Public
    (emptyClassType
      (foldr1 (~>) (map (\ (a,b) -> CTVar a ~> CTVar b)
                        (zip polyavars polyrvars) ++
                    [applyTC (mainmod,t2bt tc) (map CTVar polyavars),
                     applyTC qtc (map CTVar polyrvars)])))
    (simpleRule (map CPVar polyavars ++
                 [CPComb (mainmod,"Bot_"++transQN tc) []])
                (constF (pre "failed")) :
     if isPrimExtType qtc
       then [valueRule]
       else map genConsRule consdecls)
 where
  -- variables for polymorphic type arguments:
  polyavars = [ (i,"a" ++ show i) | i <- map fst tvars]
  polyrvars = [ (i,"b" ++ show i) | i <- map fst tvars]
  
  genConsRule (FC.Cons qc@(_,cons) _ _ argtypes) =
    let args = [(i,"x" ++ show i) | i <- [0 .. length argtypes - 1]]
    in simpleRule (map CPVar polyavars ++
                   [CPComb (mainmod,t2bt cons) (map CPVar args)])
         (applyF qc
            (map (\ (e,te) ->
                   applyE (ftype2fromP mainmod "from_P_" polyavars te) [e])
                 (zip (map CVar args) argtypes)))

  valueRule =
    let var = (0,"x")
    in simpleRule [CPComb (mainmod,"Value_"++tc) [CPVar var]] (CVar var)

-- Translate a FlatCurry type into a corresponding call to `fromp`:
ftype2fromP :: String -> String -> [(Int,String)] -> FC.TypeExpr -> CExpr
ftype2fromP mainmod pvalname polyvars (FC.TCons (_,tc) texps) =
  applyF (mainmod,pvalname++transQN tc)
         (map (ftype2fromP mainmod pvalname polyvars) texps)
ftype2fromP _ _ _ (FC.FuncType _ _) =
  error "genFromP: cannot handle functional types in as constructor args"
ftype2fromP _ _ polyvars (FC.TVar i) =
  maybe (error "genFromP: unbound type variable")
        CVar
        (find ((==i) . fst) polyvars)
ftype2fromP _ _ _ (FC.ForallType _ _) =
  error "genFromP: forall type occurred"


-------------------------------------------------------------------------
-- Translate an AbstractCurry type declaration into a FlatCurry type decl:
ctypedecl2ftypedecl :: CTypeDecl -> FC.TypeDecl
ctypedecl2ftypedecl (CTypeSyn _ _ _ _) =
  error "ctypedecl2ftypedecl: cannot translate type synonyms"
ctypedecl2ftypedecl (CNewType _ _ _ _ _) =
  error "ctypedecl2ftypedecl: cannot translate newtype"
ctypedecl2ftypedecl (CType qtc _ tvars consdecls _) =
  FC.Type qtc FC.Public (map (\ (v,_) -> (v,FC.KStar)) tvars)
          (map transConsDecl consdecls)
 where
  transConsDecl (CCons qc _ argtypes) =
    FC.Cons qc (length argtypes) FC.Public (map transTypeExpr argtypes)
  transConsDecl (CRecord  _ _ _) =
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
genMainTestModule opts mainmod orgtestmods = do
  let alltests     = concatMap propTests orgtestmods
      equivtestops = nub (concatMap equivTestOps alltests)
  terminfos <- if optEquiv opts == Autoselect
                 then getTerminationInfos opts (nub (map fst equivtestops))
                 else return (const False)
  prodinfos <- if optEquiv opts == Safe
                 then getProductivityInfos opts (nub (map fst equivtestops))
                 else return (const NoInfo)
  unsafeinfos <- if optIOTest opts
                   then return (const [])
                   else getUnsafeModuleInfos opts
                          (nub (map (fst . testName) alltests))
  let (testmods,rmtestnames) = removeNonExecTests opts unsafeinfos orgtestmods
      testtypes = nub (concatMap userTestDataOfModule testmods)
  unless (null rmtestnames) $ do
    putStrIfNormal opts $ unlines
      [withColor opts red $ "Properties not tested (due to I/O or unsafe):",
       unwords (map snd rmtestnames)]
  (fcprogs,testtypedecls) <- collectAllTestTypeDecls opts [] [] testtypes
  let equvatypes = map fst (filter snd testtypedecls)
  equvrtypes <- collectAllTestTypeDecls opts fcprogs []
                     (map (\t->(t,True))
                          (nub (concatMap equivPropTypes testmods)))
                     >>= return . map fst . snd
  let bottypes   = map (genBottomType mainmod) (union equvatypes equvrtypes)
      showinsts  = map (genShowP  mainmod) (union equvatypes equvrtypes)
      frompfuns  = map (genFromP  mainmod) equvatypes
      pevalfuns  = map (genPeval  mainmod) equvrtypes
      pvalfuns   = map (genPValOf mainmod) equvrtypes
      generators = map (genTestDataGenerator mainmod)
                       (map fst (filter (not . snd) testtypedecls) ++
                        map ctypedecl2ftypedecl bottypes) ++
                   map (genPartialPrimDataGenerator mainmod)
                       (map FCG.typeName
                            (filter (isPrimExtType . FCG.typeName) equvrtypes))
  testfuncs <- fmap concat
                 (mapM (genTestFuncs opts terminfos prodinfos mainmod) testmods)
  let mainFunction = genMainFunction opts mainmod testfuncs
      imports      = nub $ [ easyCheckModule, easyCheckExecModule
                           , searchTreeModule, generatorModule
                           , "Control.Monad"
                           , "Data.List", "Data.Char", "Data.Maybe"
                           , "System.Process", "Debug.Profile"
                           , "System.Console.ANSI.Codes" ] ++
                           map (fst . fst) testtypes ++
                           map testModuleName testmods
  appendix <- readFile (packagePath </> "include" </> "TestAppendix.curry")
  writeCurryProgram opts "."
    (CurryProg mainmod imports Nothing [] showinsts bottypes
               (mainFunction : testfuncs ++ generators ++
                               frompfuns ++ pvalfuns ++ pevalfuns)
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
     , CSExpr $ applyF ("Control.Monad", "when")
                  [applyF (pre "/=") [cvar "x1", cInt 0],
                   applyF ("System.Process", "exitWith") [cvar "x1"]]
     ]

-- Remove all tests that should not be executed.
-- Thus, if option --noiotest is set, IO tests and tests depending on unsafe
-- modules are removed.
-- Returns the test modules where tests are removed and the names of
-- the removed tests.
removeNonExecTests :: Options -> (QName -> [String]) -> [TestModule]
                   -> ([TestModule], [QName])
removeNonExecTests opts unsafeinfos testmods =
  (map removeTests testmods,
   concatMap (map testName . filter (not . isExecTest) . propTests) testmods)
 where
  removeTests tm = tm { propTests = filter isExecTest (propTests tm) }

  isExecTest test = optIOTest opts ||
                    (not (isIOTest test) && null (unsafeinfos (tmod,tmod)))
   where tmod = dropPublicSuffix (fst (testName test))

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
                              (\_ _ _ -> allTConsInNewConsDecl)

  allTConsInConsDecl :: FC.ConsDecl -> [QName]
  allTConsInConsDecl = FCG.trCons (\_ _ _ -> concatMap allTConsInTypeExpr)

  allTConsInNewConsDecl :: FC.NewConsDecl -> [QName]
  allTConsInNewConsDecl = FCG.trNewCons (\_ _ -> allTConsInTypeExpr)

  allTConsInTypeExpr :: FC.TypeExpr -> [QName]
  allTConsInTypeExpr =
    FCG.trTypeExpr (\_ -> []) (\tc targs -> tc : concat targs) (++) (flip const)

-------------------------------------------------------------------------
-- Generates a test data generator for a given type declaration.
genTestDataGenerator :: String -> FC.TypeDecl -> CFuncDecl
genTestDataGenerator mainmod tdecl = type2genData tdecl
 where
  qt       = FCG.typeName tdecl
  qtString = FC.showQNameInModule "" qt

  type2genData (FC.TypeSyn _ _ _ _) =
    error $ "Cannot create generator for type synonym " ++ qtString
  type2genData (FC.TypeNew _ _ _ _) =
    error $ "Cannot create generator for newtype " ++ qtString
  type2genData (FC.Type _ _ tvars cdecls)
    | null cdecls
    = error $ "Cannot create value generator for type '" ++ qtString ++
              "' without constructors!"
    | otherwise
    = cmtfunc
        ("Generator for " ++ "`" ++ qtString ++ "` values.")
        (typename2genopname mainmod [] qt) (length tvars) Public
        (emptyClassType
          (foldr (~>) (CTApply (CTCons searchTreeTC) (applyTC qt ctvars))
                      (map (\v -> applyTC searchTreeTC [v]) ctvars)))
        [simpleRule (map CPVar cvars)
                    (foldr1 (\e1 e2 -> applyF choiceGen [e1,e2])
                            (map cons2gen cdecls))]
   where
    cons2gen (FC.Cons qn ar _ ctypes)
      | ar>maxArity
      = error $ "Test data constructors with more than " ++ show maxArity ++
                " arguments are currently not supported!"
      | otherwise
      = applyF (generatorModule, "genCons" ++ show ar)
               ([CSymbol qn] ++ map type2gen ctypes)

    type2gen (FC.TVar i) = CVar (i,"a" ++ show i)
    type2gen (FC.FuncType _ _) =
      error $ "Type '" ++ qtString ++
              "': cannot create value generators for functions!"
    type2gen (FC.TCons qtc argtypes) =
      applyF (typename2genopname mainmod [] qtc) (map type2gen argtypes)
    type2gen (FC.ForallType _ _) =
      error $ "Type '" ++ qtString ++
              "': cannot create value generators for forall types!"

    ctvars = map (\(i,_) -> CTVar (i,"a" ++ show i)) tvars
    cvars  = map (\(i,_) -> (i,"a" ++ show i)) tvars

-- Generates a test data generator for a partial primitive type
-- where some constant is used as a value (instead of generating all values).
-- This reduces the search space when partial results are needed
-- during equivalence checking.
-- For instance, for integers, the following data generator is created:
--
--     gen_M_P_Int :: SearchTree P_Int
--     gen_M_P_Int = genCons0 Bot_Int ||| genCons1 Value_Int (Value 0)
genPartialPrimDataGenerator :: String -> QName -> CFuncDecl
genPartialPrimDataGenerator mainmod (_,tn) =
  cmtfunc
    ("Generator for (constant) partial " ++ "`" ++ tn ++ "` values.")
    (mainmod, "gen_" ++ mainmod ++ "_P_" ++ tn ++ "_Constant")
    0 Public
    (emptyClassType (applyTC searchTreeTC [baseType (mainmod,t2bt tn)]))
    [simpleRule []
      (applyF choiceGen
        [applyF (generatorModule, "genCons0") [constF (mainmod,"Bot_"++tn)],
         applyF (generatorModule, "genCons1")
           [constF (mainmod,"Value_"++tn),
            applyF (searchTreeModule,"Value")
                   [CLit (defaultValueOfBasicExtType tn)]]])]

-------------------------------------------------------------------------
-- remove the generated files (except if option "--keep" is set)
cleanup :: Options -> String -> [TestModule] -> IO ()
cleanup opts mainmod modules =
  unless (optKeep opts) $ do
    removeCurryModule mainmod
    mapM_ removeCurryModule (map testModuleName modules)
 where
  removeCurryModule modname =
    lookupModuleSourceInLoadPath modname >>=
    maybe (return ())
          (\ (_,srcfilename) -> do
            system $ installDir </> "bin" </> "cleancurry" ++ " " ++ modname
            system $ "rm -f " ++ srcfilename
            return () )

-- Print or store some statistics about number of tests.
printTestStatistics :: Options -> [String] -> String -> Int -> [Test] -> IO ()
printTestStatistics opts mods testmodname retcode tests = do
  let numtests  = sumOf (const True)
      unittests = sumOf isUnitTest  
      proptests = sumOf isPropTest  
      equvtests = sumOf isEquivTest 
      iotests   = sumOf isIOTest    
      outs = "TOTAL NUMBER OF TESTS: " ++ show numtests ++
             " (UNIT: " ++ show unittests ++ ", PROPERTIES: " ++
             show proptests ++ ", EQUIVALENCE: " ++ show equvtests ++
             (if optIOTest opts then ", IO: " ++ show iotests else "") ++ ")"
      csvheader = ["Return code", "Total", "Unit", "Prop", "Equiv", "IO",
                   "Modules"]
      csvdata   = [retcode,numtests,unittests,proptests,equvtests,iotests]
  unless (isQuiet opts || retcode /= 0 || numtests == 0) $
    putStrLn $ withColor opts green outs
  let statfile = optStatFile opts
  unless (null statfile) $ do
    writeCSVFile statfile [csvheader, map show csvdata ++ [unwords mods]]
    putStrIfDetails opts $ "Statistics written to '" ++ show statfile ++ "'.\n"
 where
  sumOf p = length . filter p $ tests

-------------------------------------------------------------------------
main :: IO ()
main = do
  argv <- getArgs
  let (funopts, args, opterrors) = getOpt Permute options argv
  opts <- processOpts (foldl (flip id) defaultOptions funopts)
  unless (null opterrors)
         (putStr (unlines opterrors) >> putStrLn usageText >> exitWith 1)
  putStrIfNormal opts ccBanner
  when (optHelp opts) (putStrLn usageText >> exitWith 0)
  let mods = map stripCurrySuffix args
  case mods of
    []  -> putStrLn usageText >> exitWith 1
    [m] -> runModuleAction (\mn -> checkModules opts [mn]) m
    _   -> do mapM_ checkModuleName mods
              checkModules opts mods
 where
  checkModuleName mn =
    when (pathSeparator `elem` mn) $ do
      putStrLn $
        "More than one module name with path prefixes not allowed:\n" ++ mn
      exitWith 1

checkModules :: Options -> [String] -> IO ()
checkModules opts mods = do
  currypath  <- ccLoadPath
  putStrLnIfDebug opts $ "SET CURRYPATH=" ++ currypath
  setEnv "CURRYPATH" currypath
  testModules <- mapM (analyseModule opts) mods
  pid  <- getPID
  let staticerrs       = concatMap staticErrors (concat testModules)
      finaltestmodules = filter testThisModule (concat testModules)
      testmodname = if null (optMainProg opts)
                      then "TEST" ++ show pid
                      else optMainProg opts
  if not (null staticerrs)
   then do showStaticErrors staticerrs
           putStrLn $ withColor opts red "Testing aborted!"
           cleanup opts testmodname finaltestmodules
           printTestStatistics opts mods testmodname 1 []
           exitWith 1
   else
     if null finaltestmodules
       then do
         printTestStatistics opts mods testmodname 0 []
         exitWith 0
       else do
         putStrIfNormal opts $ withColor opts blue $
           "Generating main test module '"++testmodname++"'..."
         putStrIfDetails opts "\n"
         finaltests <- genMainTestModule opts testmodname finaltestmodules
         showGeneratedModule opts "main test" testmodname
         putStrIfNormal opts $ withColor opts blue $ "and compiling it...\n"
         let runcmd = unwords $
                        [ installDir </> "bin" </> "curry"
                        , "--noreadline" ] ++
                        (if null currypath then [] else ["--nocypm"]) ++
                        [ ":set -time"
                        , ":set " ++ if optVerb opts > 3 then "v1" else "v0"
                        , ":set parser -Wnone" ] ++
                        (if null currypath
                           then []
                           else [":set path \"" ++ currypath ++ "\""]) ++
                        [ ":l "++testmodname, ":eval main :q" ]
         putStrLnIfDebug opts $ "Executing command:\n" ++ runcmd
         ret <- system runcmd
         cleanup opts testmodname finaltestmodules
         printTestStatistics opts mods testmodname ret finaltests
         exitWith ret
 where
  showStaticErrors errs = putStrLn $ withColor opts red $
    unlines (line : "STATIC ERRORS IN PROGRAMS:" : errs) ++ line

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
searchTreeModule = "Control.Search.SearchTree"

--- Name of SearchTree type constructor.
searchTreeTC :: QName
searchTreeTC = (searchTreeModule,"SearchTree")

--- Name of the SearchTreeGenerator module.
generatorModule :: String
generatorModule = "Control.Search.SearchTree.Generators"

choiceGen :: QName
choiceGen = (generatorModule,"|||")

-- Writes a Curry module (together with an appendix) to its file.
writeCurryProgram :: Options -> String -> CurryProg -> String -> IO ()
writeCurryProgram opts srcdir p appendix = do
  let progfile = srcdir </> modNameToPath (progName p) ++ ".curry"
  putStrLnIfDebug opts $ "Writing program: " ++ progfile
  writeFile progfile (ACPretty.showCProg p ++ "\n" ++ appendix ++ "\n")

isPAKCS :: Bool
isPAKCS = curryCompiler == "pakcs"

-- Does a program text contains a OPTIONS_FRONTEND line to call currypp?
containsPPOptionLine :: String -> Bool
containsPPOptionLine = any isOptionLine . lines
 where
  isOptionLine s = ("{-# OPTIONS_CYMAKE "   `isPrefixOf` s ||
                    "{-# OPTIONS_FRONTEND " `isPrefixOf` s )   -- -}
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

-- Builds a lambda abstraction. If the argument list is empty,
-- it builts an expression.
cLambda :: [CPattern] -> CExpr -> CExpr
cLambda pats body | null pats = body
                  | otherwise = CLambda pats body

-------------------------------------------------------------------------
