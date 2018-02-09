-- Some auxiliary operations to analyze programs with CASS

module AnalysisHelpers where

import List ( intercalate, isSuffixOf )

import AbstractCurry.Types  ( QName )
import Analysis.Types       ( Analysis )
import Analysis.ProgInfo    ( ProgInfo, emptyProgInfo, combineProgInfo
                            , lookupProgInfo)
import Analysis.Termination ( terminationAnalysis )
import CASS.Server          ( analyzeGeneric )

-- Analyze termination behavior for a list of modules.
-- If the module is a `_PUBLIC` module, we analyze the original module
-- and map these results to the `_PUBLIC` names, in order to support
-- caching of analysis results for the original modules.
getTerminationInfos :: [String] -> IO (QName -> Bool)
getTerminationInfos mods = do
  ainfo <- analyzeModules "termination" terminationAnalysis
                          (map dropPublicSuffix mods)
  return (\qn -> maybe False id (lookupProgInfo (dropPublicQName qn) ainfo))
 where
  dropPublicSuffix s = if "_PUBLIC" `isSuffixOf` s
                         then take (length s - 7) s
                         else s

  dropPublicQName (m,f) = (dropPublicSuffix m, f)

-- Analyze a list of modules with some static program analysis.
-- Returns the combined analysis information.
-- Raises an error if something goes wrong.
analyzeModules :: String -> Analysis a -> [String] -> IO (ProgInfo a)
analyzeModules ananame analysis mods = do
  putStr $ "\nRunning " ++ ananame ++ " analysis on modules: " ++
           intercalate ", " mods ++ "..."
  anainfos <- mapIO (analyzeModule analysis) mods
  putStrLn "done!"
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

