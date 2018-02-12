------------------------------------------------------------------------------
-- Some auxiliary operations to analyze programs with CASS
------------------------------------------------------------------------------

module CC.AnalysisHelpers
  ( getTerminationInfos, getProductivityInfos )
 where

import AnsiCodes            ( blue )
import List                 ( intercalate, isSuffixOf )

import AbstractCurry.Types  ( QName )
import Analysis.Types       ( Analysis )
import Analysis.ProgInfo    ( ProgInfo, emptyProgInfo, combineProgInfo
                            , lookupProgInfo )
import Analysis.Termination ( Productivity(..), productivityAnalysis
                            , terminationAnalysis )
import CASS.Server          ( analyzeGeneric )

import CC.Options

-- Analyze a list of module for their termination behavior.
-- If a module is a `_PUBLIC` module, we analyze the original module
-- and map these results to the `_PUBLIC` names, in order to support
-- caching of analysis results for the original modules.
getTerminationInfos :: Options -> [String] -> IO (QName -> Bool)
getTerminationInfos opts mods = do
  ainfo <- analyzeModules opts "termination" terminationAnalysis
                          (map dropPublicSuffix mods)
  return (\qn -> maybe False id (lookupProgInfo (dropPublicQName qn) ainfo))

-- Analyze a list of module for their productivity behavior.
-- If a module is a `_PUBLIC` module, we analyze the original module
-- and map these results to the `_PUBLIC` names, in order to support
-- caching of analysis results for the original modules.
getProductivityInfos :: Options -> [String] -> IO (QName -> Productivity)
getProductivityInfos opts mods = do
  ainfo <- analyzeModules opts "productivity" productivityAnalysis
                          (map dropPublicSuffix mods)
  return (\qn -> maybe NoInfo id (lookupProgInfo (dropPublicQName qn) ainfo))


dropPublicSuffix :: String -> String
dropPublicSuffix s = if "_PUBLIC" `isSuffixOf` s
                       then take (length s - 7) s
                       else s

dropPublicQName :: QName -> QName
dropPublicQName (m,f) = (dropPublicSuffix m, f)


-- Analyze a list of modules with some static program analysis.
-- Returns the combined analysis information.
-- Raises an error if something goes wrong.
analyzeModules :: Options -> String -> Analysis a -> [String] -> IO (ProgInfo a)
analyzeModules opts ananame analysis mods = do
  putStrIfNormal opts $ withColor opts blue $
    "\nRunning " ++ ananame ++ " analysis on modules: " ++
    intercalate ", " mods ++ "..."
  anainfos <- mapIO (analyzeModule analysis) mods
  putStrIfNormal opts $ withColor opts blue $ "done...\n"
  return $ foldr combineProgInfo emptyProgInfo anainfos

-- Analyze a module with some static program analysis.
-- Raises an error if something goes wrong.
analyzeModule :: Analysis a -> String -> IO (ProgInfo a)
analyzeModule analysis mod = do
  aresult <- analyzeGeneric analysis mod
  either return
         (\e -> do putStrLn "WARNING: error occurred during analysis:"
                   putStrLn e
                   putStrLn "Ignoring analysis information"
                   return emptyProgInfo)
         aresult

