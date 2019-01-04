------------------------------------------------------------------------------
-- Some auxiliary operations for CurryCheck
------------------------------------------------------------------------------

module CC.Helpers ( ccLoadPath )
 where

import FilePath  ( splitSearchPath )
import List      ( intercalate, isInfixOf )
import System    ( getEnviron )

import CC.Config ( packageLoadPath )

--- Computes the load path for executing the
--- generated program that executes all checks.
--- The load path consists of the standard load path (defined by `CURRYPATH`)
--- and the additional load path for packages required by CurryCheck.
ccLoadPath :: IO String
ccLoadPath = do
    ecurrypath <- getEnviron "CURRYPATH"
    let ecurrypath' = case ecurrypath of ':':_ -> '.':ecurrypath
                                         _     -> ecurrypath
    return $ intercalate ":"
                      (if null ecurrypath' then ccExecLoadPath
                                           else ecurrypath' : ccExecLoadPath)

--- Computes the additional load path for executing the
--- generated program that executes all checks.
ccExecLoadPath :: [String]
ccExecLoadPath =
  filter isRequiredPackage (splitSearchPath packageLoadPath)
 where
  isRequiredPackage dir =
    any (`isInfixOf` dir)
        [ "ansi-terminal", "easycheck", "profiling", "random"
        , "searchtree", "setfunctions" ]
