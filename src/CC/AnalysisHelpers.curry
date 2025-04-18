------------------------------------------------------------------------------
-- Some auxiliary operations to analyze programs with CASS
------------------------------------------------------------------------------

module CC.AnalysisHelpers
  ( getTerminationInfos, getProductivityInfos, getUnsafeModuleInfos
  , dropPublicSuffix )
 where

import System.Console.ANSI.Codes ( blue )
import Data.List                 ( intercalate, isSuffixOf )

import AbstractCurry.Types   ( QName )
import Analysis.Types        ( Analysis )
import Analysis.ProgInfo     ( ProgInfo, emptyProgInfo, combineProgInfo
                             , lookupProgInfo )
import Analysis.Termination  ( Productivity(..), productivityAnalysis
                             , terminationAnalysis )
import Analysis.UnsafeModule ( unsafeModuleAnalysis )
import CASS.Server           ( analyzeGeneric )
import RW.Base               ( ReadWrite )

import CC.Options

-- Analyzes a list of modules for their termination behavior.
-- If a module is a `_PUBLIC` module, we analyze the original module
-- and map these results to the `_PUBLIC` names, in order to support
-- caching of analysis results for the original modules.
getTerminationInfos :: Options -> [String] -> IO (QName -> Bool)
getTerminationInfos opts mods = do
  ainfo <- analyzeModules opts "termination" terminationAnalysis
                          (map dropPublicSuffix mods)
  return (\qn -> maybe False id (lookupProgInfo (dropPublicQName qn) ainfo))

-- Analyzes a list of modules for their productivity behavior.
-- If a module is a `_PUBLIC` module, we analyze the original module
-- and map these results to the `_PUBLIC` names, in order to support
-- caching of analysis results for the original modules.
getProductivityInfos :: Options -> [String] -> IO (QName -> Productivity)
getProductivityInfos opts mods = do
  ainfo <- analyzeModules opts "productivity" productivityAnalysis
                          (map dropPublicSuffix mods)
  return (\qn -> maybe NoInfo id (lookupProgInfo (dropPublicQName qn) ainfo))

-- Analyzes a list of modules for their productivity behavior.
-- If a module is a `_PUBLIC` module, we analyze the original module
-- and map these results to the `_PUBLIC` names, in order to support
-- caching of analysis results for the original modules.
getUnsafeModuleInfos :: Options -> [String] -> IO (QName -> [String])
getUnsafeModuleInfos opts mods = do
  ainfo <- analyzeModules opts "unsafe module" unsafeModuleAnalysis
                          (map dropPublicSuffix mods)
  return (\qn -> maybe [] id (lookupProgInfo (dropPublicQName qn) ainfo))


dropPublicSuffix :: String -> String
dropPublicSuffix s = if "_PUBLIC" `isSuffixOf` s
                       then take (length s - 7) s
                       else s

dropPublicQName :: QName -> QName
dropPublicQName (m,f) = (dropPublicSuffix m, f)


-- Analyze a list of modules with some static program analysis.
-- Returns the combined analysis information.
-- Raises an error if something goes wrong.
analyzeModules :: (Read a, Show a, ReadWrite a, Eq a)
               => Options -> String -> Analysis a
               -> [String] -> IO (ProgInfo a)
analyzeModules opts ananame analysis mods = do
  putStrIfNormal opts $ withColor opts blue $
    "\nRunning " ++ ananame ++ " analysis on modules: " ++
    intercalate ", " mods ++ "..."
  anainfos <- mapM (analyzeModule analysis) mods
  putStrIfNormal opts $ withColor opts blue $ "done...\n"
  return $ foldr combineProgInfo emptyProgInfo anainfos

-- Analyze a module with some static program analysis.
-- Raises an error if something goes wrong.
analyzeModule :: (Read a, Show a, ReadWrite a, Eq a)
              => Analysis a -> String -> IO (ProgInfo a)
analyzeModule analysis mod = do
  aresult <- analyzeGeneric analysis mod
  either return
         (\e -> do putStrLn "WARNING: error occurred during analysis:"
                   putStrLn e
                   putStrLn "Ignoring analysis information"
                   return emptyProgInfo)
         aresult

