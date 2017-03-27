--- This module contains some specifications of operations from the List
--- module.
--- Since the preprocessor also depends on the list module,
--- we cannot write these specifications directly into the list module.

{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=defaultrules #-}

import qualified List
import Test.Prop

nub :: [a] -> [a]
nub = List.nub

nub'spec :: [a] ->DET [a]
nub'spec (xs++[e]++ys++[e]++zs) = nub'spec (xs++[e]++ys++zs)
nub'spec'default xs = xs

isPrefixOf :: [a] -> [a] -> Bool
isPrefixOf = List.isPrefixOf

isPrefixOf'spec :: [a] -> [a] ->DET Bool
isPrefixOf'spec xs (xs ++ _) = True
isPrefixOf'spec'default _ _  = False


isSuffixOf :: [a] -> [a] -> Bool
isSuffixOf = List.isSuffixOf

isSuffixOf'spec :: [a] -> [a] ->DET Bool
isSuffixOf'spec xs (_ ++ xs) = True
isSuffixOf'spec'default _ _  = False


isInfixOf :: [a] -> [a] -> Bool
isInfixOf = List.isInfixOf

isInfixOf'spec :: [a] -> [a] ->DET Bool
isInfixOf'spec xs (_ ++ xs ++ _) = True
isInfixOf'spec'default _ _       = False

