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
import RW.Base               
import System.IO             ( hPutChar )

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
analyzeModules :: (Read a, Show a, ReadWrite a)
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
analyzeModule :: (Read a, Show a, ReadWrite a)
              => Analysis a -> String -> IO (ProgInfo a)
analyzeModule analysis mod = do
  aresult <- analyzeGeneric analysis mod
  either return
         (\e -> do putStrLn "WARNING: error occurred during analysis:"
                   putStrLn e
                   putStrLn "Ignoring analysis information"
                   return emptyProgInfo)
         aresult

instance ReadWrite Productivity where
  readRW strs xs = case xs of 
    '0':r0 -> (NoInfo,      r0)
    '1':r0 -> (Terminating, r0)
    '2':r0 -> (DCalls a',   r1)
      where
        (a',r1) = readRW strs r0
    '3':r0 -> (Looping, r0)
    _   -> error "ReadWrite Productivity: no parse" 

  showRW _ strs0 NoInfo = (strs0,showChar '0')
  showRW _ strs0 Terminating = (strs0,showChar '1')
  showRW params strs0 (DCalls a') = (strs1,showChar '2' . show1)
    where
      (strs1,show1) = showRW params strs0 a'
  showRW _ strs0 Looping = (strs0,showChar '3')

  writeRW _      h NoInfo      strs = hPutChar h '0' >> return strs
  writeRW _      h Terminating strs = hPutChar h '1' >> return strs
  writeRW params h (DCalls a') strs =
    hPutChar h '2' >> writeRW params h a' strs
  writeRW _      h Looping     strs = hPutChar h '3' >> return strs

  typeOf _ = monoRWType "Productivity"