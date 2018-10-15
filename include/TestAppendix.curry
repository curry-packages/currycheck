-------------------------------------------------------------------------
--- Some definitions added as an appendix to the main test module
--- generated by CurryCheck.

--- Runs a sequence of property tests. Outputs the messages of the failed tests
--- messages and returns exit status 0 if all tests are successful,
--- otherwise status 1. If the second argument is `True`, the time
--- needed for checking each property is shown.
runPropertyTests :: Bool -> Bool -> [IO (Maybe String)] -> IO Int
runPropertyTests withcolor withtime props = do
  failedmsgs <- sequenceIO (if withtime then map showRunTimeFor props
                                        else props)
                >>= return . Maybe.catMaybes
  if null failedmsgs
   then return 0
   else do putStrLn $ (if withcolor then AnsiCodes.red else id) $
                      line ++
                      "\nFAILURES OCCURRED IN SOME TESTS:\n" ++
                      unlines failedmsgs ++ line
           return 1
 where
   line = take 78 (repeat '=')

--- Prints the run time needed to execute a given IO action.
showRunTimeFor :: IO a -> IO a
showRunTimeFor action = do
  t0 <- Profile.getProcessInfos >>= return . maybe 0 id . lookup Profile.RunTime
  result <- action
  t1 <- Profile.getProcessInfos >>= return . maybe 0 id . lookup Profile.RunTime
  putStrLn $ "Run time: " ++ show (t1-t0) ++ " msec."
  return result

-------------------------------------------------------------------------
-- Auxiliaries for function generators:

-- Data type to represent a function as a list of (argument,result) pairs.
data Func a b = Func [(a,b)]

-- This can be exploited to show a function in mathematical notation.
instance (Show a, Show b) => Show (Func a b) where
  show (Func abs)
    | null abs  = "{ _ -> failed }"
    | otherwise
    = "{" ++ List.intercalate ", " (map showMap (tail abs) ++
                                    ["_ -> " ++ show (snd (head abs))]) ++ "}"
   where
    showMap (x,y) = show x ++ " -> " ++ show y

--- Generates a search tree for functions represented by non-empty(!)
--- pair list values where the search trees for the arguments and results
--- are given as a parameter.
genFunc :: SearchTree.SearchTree a -> SearchTree.SearchTree b
        -> SearchTree.SearchTree (Func a b)
genFunc gena genb =
  SearchTreeGenerators.genCons1 Func
    (genNEList (SearchTreeGenerators.genPair gena genb))

-- Generates a search tree for non-empty list values where the search tree
-- for the elements is given as a parameter.
genNEList :: SearchTree.SearchTree a -> SearchTree.SearchTree [a]
genNEList genx =
  SearchTreeGenerators.genCons2 (:) genx (SearchTreeGenerators.genList genx)

--- Transforms a function in list presentation into a real function.
list2Func :: Eq a => Func a b -> (a -> b)
list2Func (Func abs) x = maybe (if null abs then failed else snd (head abs))
                               id
                               (lookup x abs)


--- Generates a search tree for functions represented by non-empty(!)
--- pair list values where the search trees for the arguments and results
--- are given as a parameter.
genFunction :: Eq a => SearchTree.SearchTree a -> SearchTree.SearchTree b
                    -> SearchTree.SearchTree (a -> b)
genFunction gena genb =
  SearchTreeGenerators.genCons1 l2f
    (genNEList (SearchTreeGenerators.genPair gena genb))
 where
  l2f abs x = maybe (if null abs then failed else snd (head abs))
                    id
                    (lookup x abs)

instance (Show a, Show b) => Show (a -> b) where
  show f = "<<function>>"

-------------------------------------------------------------------------
