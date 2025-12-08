------------------------------------------------------------------------------
--- Definition and processing of options for CurryCheck
------------------------------------------------------------------------------

module CC.Options where

import Control.Monad        ( unless, when )
import Curry.Compiler.Distribution
                           ( baseVersion, curryCompiler
                           , curryCompilerMajorVersion
                           , curryCompilerMinorVersion
                           , curryCompilerRevisionVersion
                           , installDir )
import Data.Char            ( toUpper )
import Data.List            ( intercalate, isPrefixOf )
import Numeric              ( readNat )
import System.Console.GetOpt
import System.IO

------------------------------------------------------------------------------
-- Representation of command line options.
data Options = Options
  { optHelp     :: Bool
  , optConfig   :: Bool
  , optVerb     :: Int
  , optKeep     :: Bool
  , optMaxTest  :: Int
  , optMaxFail  :: Int
  , optDefType  :: String
  , optSource   :: Bool
  , optIOTest   :: Bool
  , optProp     :: Bool
  , optSpec     :: Bool
  , optDet      :: Bool
  , optProof    :: Bool
  , optEquiv    :: EquivOption
  , optTime     :: Bool
  , optColor    :: Bool
  , optMainProg :: String
  , optStatFile :: String
  }

-- Default command line options.
defaultOptions :: Options
defaultOptions  = Options
  { optHelp     = False
  , optConfig   = False
  , optVerb     = 1
  , optKeep     = False
  , optMaxTest  = 100
  , optMaxFail  = 10000
  , optDefType  = "Ordering"
  , optSource   = True
  , optIOTest   = True
  , optProp     = True
  , optSpec     = True
  , optDet      = True
  , optProof    = True
  , optEquiv    = Manual
  , optTime     = False
  , optColor    = True
  , optMainProg = ""
  , optStatFile = ""
  }

--- Options for equivalence tests.
data EquivOption = Safe | Autoselect | Manual | Ground
 deriving (Eq, Show)

-- Definition of actual command line options.
options :: [OptDescr (Options -> Options)]
options =
  [ Option "h?" ["help"] (NoArg (\opts -> opts { optHelp = True }))
           "print help and exit"
  , Option "" ["config"] (NoArg (\opts -> opts { optConfig = True }))
           "show current configuration and exit"
  , Option "q" ["quiet"] (NoArg (\opts -> opts { optVerb = 0 }))
           "run quietly (no output, only exit code)"
  , Option "v" ["verbosity"]
            (OptArg (maybe (checkVerb 3) (safeReadNat checkVerb)) "<n>")
            "verbosity level:\n0: quiet (same as `-q')\n1: show test names (default)\n2: show more information about test generation\n3: show test data (same as `-v')\n4: show also some debug information"
  , Option "k" ["keep"] (NoArg (\opts -> opts { optKeep = True }))
           "keep temporarily generated program files"
  , Option "m" ["maxtests"]
           (ReqArg (safeReadNat (\n opts -> opts { optMaxTest = n })) "<n>")
           "maximal number of tests (default: 100)"
  , Option "f" ["maxfails"]
           (ReqArg (safeReadNat (\n opts -> opts { optMaxFail = n })) "<n>")
           "maximal number of condition failures\n(default: 10000)"
  , Option "d" ["deftype"]
           (ReqArg checkDefType "<t>")
           "type for defaulting polymorphic tests:\nBool | Int | Char | Ordering (default)"
  , Option "e" ["equivalence"]
           (ReqArg checkEquivOption "<e>")
           "option for equivalence tests:\nsafe | autoselect | manual (default) | ground"
  , Option "t" ["time"] (NoArg (\opts -> opts { optTime = True }))
           "show run time for executing each property test"
  , Option "" ["nosource"]
           (NoArg (\opts -> opts { optSource = False }))
           "do not perform source code checks"
  , Option "" ["noiotest"]
           (NoArg (\opts -> opts { optIOTest = False }))
           "do not test I/O properties or unsafe modules"
  , Option "" ["noprop"]
           (NoArg (\opts -> opts { optProp = False }))
           "do not perform property tests"
  , Option "" ["nospec"]
           (NoArg (\opts -> opts { optSpec = False }))
           "do not perform specification/postcondition tests"
  , Option "" ["nodet"]
           (NoArg (\opts -> opts { optDet = False }))
           "do not perform determinism tests"
  , Option "" ["noproof"]
           (NoArg (\opts -> opts { optProof = False }))
           "do not consider proofs to simplify properties"
  , Option "" ["nocolor"]
           (NoArg (\opts -> opts { optColor = False }))
           "do not use colors when showing tests"
  , Option "" ["mainprog"]
           (ReqArg (\s opts -> opts { optMainProg = s }) "<prog>")
           "name of generated main program\n(default: TEST<pid>)"
  , Option "" ["statfile"]
           (ReqArg (\s opts -> opts { optStatFile = s }) "<file>")
           "write test statistics in CSV format into <file>"
  ]
 where
  safeReadNat opttrans s opts = case readNat s of
   [(n,"")] -> opttrans n opts
   _        -> error "Illegal number argument (try `-h' for help)"

  checkVerb n opts = if n>=0 && n<5
                     then opts { optVerb = n }
                     else error "Illegal verbosity level (try `-h' for help)"

  checkDefType s opts = if s `elem` ["Bool","Int","Char","Ordering"]
                        then opts { optDefType = s }
                        else error "Illegal default type (try `-h' for help)"

  checkEquivOption s opts
    | ls `isPrefixOf` "SAFE"       = opts { optEquiv = Safe }
    | ls `isPrefixOf` "AUTOSELECT" = opts { optEquiv = Autoselect }
    | ls `isPrefixOf` "MANUAL"     = opts { optEquiv = Manual }
    | ls `isPrefixOf` "GROUND"     = opts { optEquiv = Ground }
    | otherwise = error "Illegal equivalence option (try `-h' for help)"
   where ls = map toUpper s

--- Further option processing, e.g., setting coloring mode.
processOpts :: Options -> IO Options
processOpts opts = do
  isterm <- hIsTerminalDevice stdout
  return $ if isterm then opts else opts { optColor = False}

isQuiet :: Options -> Bool
isQuiet opts = optVerb opts == 0

--- Print second argument if verbosity level is not quiet:
putStrIfNormal :: Options -> String -> IO ()
putStrIfNormal opts s = unless (isQuiet opts) (putStr s >> hFlush stdout)

--- Print second argument if verbosity level > 1:
putStrIfDetails :: Options -> String -> IO ()
putStrIfDetails opts s = when (optVerb opts > 1) (putStr s >> hFlush stdout)

--- Print second argument if verbosity level > 3:
putStrLnIfDebug :: Options -> String -> IO ()
putStrLnIfDebug opts s = when (optVerb opts > 3) (putStrLn s >> hFlush stdout)

--- use some coloring (from System.Console.ANSI.Codes) if color option is on:
withColor :: Options -> (String -> String) -> String -> String
withColor opts coloring = if optColor opts then coloring else id

-- Help text
usageText :: String
usageText = usageInfo ("Usage: curry-check [options] <module names>\n") options

-- Print current configuration.
printConfiguration :: Options -> IO ()
printConfiguration opts = do
  putStrLn $ unlines
    [ "\nCurrent configuration:\n"
    , "Curry compiler      : " ++ curryCompiler ++ " " ++ version
    , "Base version        : " ++ baseVersion
    , "Curry home directory: " ++ installDir
    , ""
    , "Verbosity lebel     : " ++ show (optVerb opts)
    , "Maximal tests       : " ++ show (optMaxTest opts)
    , "Maximal failures    : " ++ show (optMaxFail opts)
    , "Polymorphism default: " ++ optDefType opts
    , "Equivalence testing : " ++ show (optEquiv opts)
    ]
 where
  version =  intercalate "." $ map show
               [curryCompilerMajorVersion, curryCompilerMinorVersion,
                curryCompilerRevisionVersion]

------------------------------------------------------------------------------
