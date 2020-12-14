--- This module contains some specifications of operations from the List
--- module.
--- Since the Curry preprocessor also depends on the list module,
--- we cannot write these specifications directly into the list module.
---
--- To test it, execute
---
---     > curry-check -e ground ListSpecifications
---
--- Note that the option `-e ground` is only necessary for PAKCS
--- since PAKCS has an incomplete implementation of set functions
--- which results in an intended behavior of default rules.
--- For instance,
---
---     > isPrefixOf      ([]::[Int]) failed   --> True
---     > isPrefixOf'spec ([]::[Int]) failed   --> no value
---
--- whereas both yields in `True` in KiCS2.

{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=defaultrules #-}

import qualified Data.List
import Test.Prop

nub :: (Data a, Eq a) => [a] -> [a]
nub = Data.List.nub

nub'spec :: (Data a, Eq a) => [a] ->DET [a]
nub'spec (xs++[e]++ys++[e]++zs) = nub'spec (xs++[e]++ys++zs)
nub'spec'default xs = xs

isPrefixOf :: (Data a, Eq a) => [a] -> [a] -> Bool
isPrefixOf = Data.List.isPrefixOf

isPrefixOf'spec :: (Data a, Eq a) => [a] -> [a] ->DET Bool
isPrefixOf'spec xs (xs ++ _) = True
isPrefixOf'spec'default _ _  = False


isSuffixOf :: (Data a, Eq a) => [a] -> [a] -> Bool
isSuffixOf = Data.List.isSuffixOf

isSuffixOf'spec :: (Data a, Eq a) => [a] -> [a] ->DET Bool
isSuffixOf'spec xs (_ ++ xs) = True
isSuffixOf'spec'default _ _  = False


isInfixOf :: (Data a, Eq a) => [a] -> [a] -> Bool
isInfixOf = Data.List.isInfixOf

isInfixOf'spec :: (Data a, Eq a) => [a] -> [a] ->DET Bool
isInfixOf'spec xs (_ ++ xs ++ _) = True
isInfixOf'spec'default _ _       = False

