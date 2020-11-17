------------------------------------------------------------------------
--- This module contains some operations to access and check proof
--- for theorems formulated as properties in Curry programs.
---
--- Current assumptions:
--- * A theorem is represented in a source file as a EasyCheck property, e.g.:
---
---       sortPreservesLength xs = length xs -=- length (sort xs)
---
--- * A theorem is considered as proven and, thus, not be checked
---   by CurryCheck or the contract wrapper (see `currypp`), if there exists
---   a file named with prefix "Proof" and the qualified name of the theorem,
---    e.g., `Proof-Sort-sortPreservesLength.agda`.
---   The name is not case sensitive, the file name extension is arbitrary
---   and the special characters in the name are ignored.
---   Hence, a proof for `sortlength` could be also stored in
---   a file named `PROOF_Sort_sort_preserves_length.smt`.
---
---  * A proof that some operation `f` is deterministic has the name
---    `fIsDeterministic` so that a proof for `last` can be stored in
---    `proof-last-is-deterministic.agda` (and also in some other files).
---
--- @author Michael Hanus
--- @version November 2020
------------------------------------------------------------------------

module TheoremUsage
  ( determinismTheoremFor
  , getModuleProofFiles, existsProofFor, isProofFileNameFor
  , getTheoremFunctions
  )  where

import AbstractCurry.Types
import AbstractCurry.Select
import Data.Char
import Data.List
import System.Directory
import System.FilePath      ( dropExtension, takeDirectory )

import System.CurryPath     ( lookupModuleSourceInLoadPath, modNameToPath )

import PropertyUsage

------------------------------------------------------------------------
--- The name of a proof of a determinism annotation for the operation
--- given as the argument.
determinismTheoremFor :: String -> String
determinismTheoremFor funcname = funcname ++ "isdeterministic"

------------------------------------------------------------------------
-- Operations for proof files:

--- Get the names of all files in the directory (first argument) containing
--- proofs of theorems of the module (second argument).
getModuleProofFiles :: String -> String -> IO [String]
getModuleProofFiles dir mod = do
  files <- getDirectoryContents dir
  return (filter (isModuleProofFileName mod) files)

--- Does the list of file names (second argument) contain a proof of the
--- qualified theorem name given as the first argument?
existsProofFor :: QName -> [String] -> Bool
existsProofFor qpropname filenames =
  any (isProofFileNameFor qpropname) filenames

--- Is the second argument a file name with a proof of some theorem of a module
--- (first argument), i.e., start it with `proof` and the module name?
isModuleProofFileName :: String -> String -> Bool
isModuleProofFileName mn fn =
  deleteNonAlphanNum ("proof" ++ map toLower mn)
    `isPrefixOf` deleteNonAlphanNum (map toLower fn)

--- Is this the file name of a proof of property `prop`?
isProofFileNameFor :: QName -> String -> Bool
isProofFileNameFor (mn,prop) fname =
  let lfname = map toLower (dropExtension fname)
      lprop  = map toLower (mn ++ prop)
   in if "proof" `isPrefixOf` lfname
      then deleteNonAlphanNum (drop 5 lfname) == deleteNonAlphanNum lprop
      else False

--- Delete non alphanumeric characters.
deleteNonAlphanNum :: String -> String
deleteNonAlphanNum = filter isAlphaNum

------------------------------------------------------------------------
--- Get all theorems which are contained in a given program.
--- A theorem is a property for which a proof file exists in the
--- directory provided as first argument.
getTheoremFunctions :: String -> CurryProg -> IO [CFuncDecl]
getTheoremFunctions proofdir (CurryProg mn _ _ _ _ _ functions _) = do
  let propfuncs = filter isProperty functions -- all properties
  prooffiles <- getModuleProofFiles proofdir mn
  return $ filter (\fd -> existsProofFor (funcName fd) prooffiles)
                  propfuncs

------------------------------------------------------------------------
