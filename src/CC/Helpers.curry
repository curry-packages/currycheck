------------------------------------------------------------------------------
-- Some auxiliary operations for CurryCheck
------------------------------------------------------------------------------

module CC.Helpers ( ccLoadPath )
 where

import Data.List          ( intercalate, isInfixOf )
import System.Environment ( getEnv )
import System.FilePath    ( searchPathSeparator )

import CC.Config ( getPackageLoadPath )

--- Computes the load path for executing the
--- generated program that executes all checks.
--- The load path consists of the standard load path (defined by `CURRYPATH`)
--- and the additional load path for packages required by CurryCheck.
ccLoadPath :: IO String
ccLoadPath = do
    ecurrypath <- getEnv "CURRYPATH"
    let ecurrypath' = case ecurrypath of ':':_ -> '.':ecurrypath
                                         _     -> ecurrypath
    execpath <- ccExecLoadPath
    return $ intercalate [searchPathSeparator] $
      if null ecurrypath' then execpath else ecurrypath' : execpath

--- Computes the additional load path for executing the
--- generated program that executes all checks.
ccExecLoadPath :: IO [String]
ccExecLoadPath = fmap (filter isRequiredPackage) getPackageLoadPath
 where
  isRequiredPackage dir =
    any (`isInfixOf` dir)
        [ "allvalues", "ansi-terminal", "directory", "distribution"
        , "easycheck", "filepath", "process", "profiling", "random"
        , "searchtree-extra", "time" ]
