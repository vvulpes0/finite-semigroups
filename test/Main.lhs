> module Main (main) where

> import Data.IntSet(fromList)
> import Test.HUnit
> import Data.Representation.FiniteSemigroup

> main :: IO ()
> main = runTestTTAndExit tests

> tests :: Test
> tests =
>     TestList
>     [ TestLabel "Associativity"
>     $ TestList
>       [ TestCase $ assertAssociative "def1"  def1
>       , TestCase $ assertAssociative "def2"  def2
>       , TestCase $ assertAssociative "rdef2" rdef2
>       , TestCase $ assertAssociative "j" j
>       ]
>     , TestLabel "Equivalence With Table"
>     $ TestList
>       [ 2 ~=? fssize def1
>       , 2 ~=? fssize (fstable def1)
>       , 7 ~=? fssize j
>       , 7 ~=? fssize (fstable j)
>       , 3 ~=? fsnbases j
>       , 3 ~=? fsnbases (fstable j)
>       ]
>     , TestLabel "Bases"
>     $ TestList
>       [ 3 ~=? fsnbases lj1
>       , 2 ~=? length (independentBases lj1)
>       , 2 ~=? fsnbases (fromBases $ independentBases lj1)
>       , 5 ~=? fssize lj1
>       , 5 ~=? fssize (fromBases $ independentBases lj1)
>       ]
>     , TestLabel "Monoids and Adjunction"
>     $ TestList
>       [ 2 ~=? fssize (fromBases [[1,1,1],[2,2,2]])
>       , 3 ~=? fssize (monoid $ fromBases [[1,1,1],[2,2,2]])
>       , 3 ~=? fssize (adjoinOne $ fromBases [[1,1,1],[2,2,2]])
>       , 3 ~=? fssize (adjoinZero $ fromBases [[1,1,1],[2,2,2]])
>       , Nothing ~=? neutralElement (fromBases [[1,1,1],[2,2,2]])
>       , TestCase . assertJust ""
>       $ neutralElement (monoid $ fromBases [[1,1,1],[2,2,2]])
>       , 3 ~=? fssize (fromBases [[0,1,2],[1,1,2],[2,1,2]])
>       , 3 ~=? fssize (monoid $ fromBases [[0,1,2],[1,1,2],[2,1,2]])
>       , 4 ~=? fssize (adjoinOne $ fromBases [[0,1,2],[1,1,2],[2,1,2]])
>       , 4 ~=? fssize (adjoinZero $ fromBases [[0,1,2],[1,1,2],[2,1,2]])
>       , TestCase . assertJust ""
>       $ neutralElement (fromBases [[0,1,2],[1,1,1],[2,2,2]])
>       , TestCase . assertJust ""
>       $ neutralElement (monoid $ fromBases [[0,1,2],[1,1,1],[2,2,2]])
>       ]
>     , TestLabel "Classification"
>     $ TestList
>       [ TestCase . assertBool "def1" $ all ($ def1) class_def1
>       , TestCase . assertBool "def2" $ all ($ def2) class_def2
>       , TestCase . assertBool "rdef2" $ all ($ rdef2) class_rdef2
>       , TestCase . assertBool "j" $ all ($ j) class_j
>       , TestCase . assertBool "z3" $ all ($ z3) class_z3
>       ]
>     , TestLabel "Separators"
>     $ TestList
>       [ TestCase $ assertSeparation "J₁:1"
>         (both isCommutative isBand) isTrivial
>         (fromBases [[1,1,3,3],[2,3,2,3]])
>       , TestCase $ assertSeparation "Acom:J₁"
>         (both isCommutative isAperiodic) (both isCommutative isBand)
>         (fromBases [[1,2,2]])
>       , TestCase $ assertSeparation "J:Acom"
>         isJTrivial (both isCommutative isAperiodic)
>         (fromBases [[0,1,2,3],[1,1,3,3],[0,2,2,3]])
>       , TestCase $ assertSeparation "L:J"
>         isLTrivial isJTrivial
>         def2
>       , TestCase $ assertSeparation "L:R"
>         isLTrivial isRTrivial
>         def2
>       , TestCase $ assertSeparation "R:J"
>         isRTrivial isJTrivial
>         rdef2
>       , TestCase $ assertSeparation "R:L"
>         isRTrivial isLTrivial
>         rdef2
>       , TestCase $ assertSeparation "DA:L"
>         isDA isLTrivial
>         (fromBases [[1,1,2,2,4],[4,2,2,2,4],[4,1,3,3,4]])
>       , TestCase $ assertSeparation "J:N"
>         isJTrivial isNilpotent
>         j
>       , TestCase $ assertSeparation "N:1"
>         isNilpotent isTrivial
>         (fromBases [[1,4,4,4,4],[4,2,3,4,4],[4,4,4,4,4]])
>       , TestCase $ assertSeparation "D:N"
>         (both isLTrivial (locally isTrivial)) isNilpotent
>         def2
>       , TestCase $ assertSeparation "K:N"
>         (both isRTrivial (locally isTrivial)) isNilpotent
>         rdef2
>       , TestCase $ assertSeparation "LI:L"
>         (locally isTrivial) isLTrivial
>         (fromBases [[1,1,1,3],[3,2,2,3],[3,1,1,3]])
>       , TestCase $ assertSeparation "LI:R"
>         (locally isTrivial) isLTrivial
>         (fromBases [[1,1,1,3],[3,2,2,3],[3,1,1,3]])
>       , TestCase $ assertSeparation "LJ₁:LI"
>         (locally (both isCommutative isBand)) (locally isTrivial)
>         (fromBases [[1,1,2],[0,2,2],[0,0,2]])
>       , TestCase $ assertSeparation "LJ₁:DA"
>         (locally (both isCommutative isBand)) isDA
>         (fromBases [[1,1,2],[0,2,2],[0,0,2]])
>       , TestCase $ assertSeparation "LAcom:LJ₁"
>         (locally (both isCommutative isAperiodic))
>         (locally (both isCommutative isBand))
>         (fromBases [[0,2,2,4,4],[1,1,3,3,4],[1,4,4,4,4]])
>       , TestCase $ assertSeparation "LAcom:DA"
>         (locally (both isCommutative isAperiodic))
>         (locally (both isCommutative isBand))
>         (fromBases [[0,2,2,4,4],[1,1,3,3,4],[1,4,4,4,4]])
>       , TestCase $ assertSeparation "LJ:LAcom"
>         (locally isJTrivial)
>         (locally (both isCommutative isAperiodic))
>         (fromBases [[1,1,1,3],[0,2,2,3],[0,1,3,3]])
>       , TestCase $ assertSeparation "LL:LR"
>         (locally isLTrivial) (locally isRTrivial)
>         (fromBases [[1,1,1],[0,2,0],[0,1,1]])
>       , TestCase $ assertSeparation "LR:LL"
>         (locally isRTrivial) (locally isLTrivial)
>         (dual $ fromBases [[1,1,1],[0,2,0],[0,1,1]])
>       , TestCase $ assertSeparation "LDA:LL"
>         (locally isDA) (locally isLTrivial)
>         (fromBases [[1,1,1,4,4,4],[2,1,3,3,5,3],[0,1,0,3,4,4]])
>       , TestCase $ assertSeparation "LDA:LR"
>         (locally isDA) (locally isRTrivial)
>         (fromBases [[1,1,1,4,4,4],[2,1,3,3,5,3],[0,1,0,3,4,4]])
>       , TestCase $ assertSeparation "[J₁]T:LDA"
>         (locally (both isCommutative isBand) . projectedSubsemigroup)
>         (locally isDA)
>         (fromBases [[0,1,2],[0,0,2],[1,2,2]])
>       ]
>     , TestLabel "Order"
>     $ TestList
>       [ TestCase . assertBool "One top of J"
>       . maybe False id . isVariety "[x≤1]" $ fromBasesWith jleq spb
>       , TestCase . assertBool "Zero bottom of J"
>       . maybe False id . isVariety "[x≥0]" $ fromBasesWith jleq spb
>       , TestCase . assertBool "Straubing Half"
>       . maybe False id . isVariety "[1≤x]"
>       $ fromBasesWith (syntacticOrder 0 $ fromList [0,1,2]) spb
>       , TestCase . assertBool "Not Commutative"
>       . maybe False not . isVariety "[xy=yx]"
>       $ fromBasesWith trivialOrder spb
>       , TestCase . assertBool "x<x* for fin"
>       . maybe False id . isVariety "[x≤x*]"
>       $ fromBasesWith (syntacticOrder 0 $ fromList [3])
>         [[1,4,3,4,4],[4,2,4,4,4],[4,4,4,4,4]]
>       , TestCase . assertBool "not x<x* for cofin"
>       . maybe False not . isVariety "[x≤x*]"
>       $ fromBasesWith (syntacticOrder 0 $ fromList [0,1,2,4])
>         [[1,4,3,4,4],[4,2,4,4,4],[4,4,4,4,4]]
>       ]
>     , TestLabel "Order Show/Read"
>     $ TestList
>       [ TestCase . assertReadShow "jleq" $ fromBasesWith jleq spb
>       , TestCase . assertReadShow "synord spb"
>       $ fromBasesWith (syntacticOrder 0 $ fromList [0,1,2]) spb
>       , TestCase . assertReadShow "synord"
>       $ fromBasesWith (syntacticOrder 0 $ fromList [3])
>         [[1,4,3,4,4],[4,2,4,4,4],[4,4,4,4,4]]
>       ]
>     ]

> assertReadShow :: (Eq a, Read a, Show a) => String -> a -> Assertion
> assertReadShow lbl x = assertBool lbl ((read $ show x) == x)

> assertAssociative :: FiniteSemigroupRep s => String -> s -> Assertion
> assertAssociative lbl s
>     = sequence_
>       [ assertEqual lbl (f (f a b) c) (f a (f b c))
>       | a <- xs, b <- xs, c <- xs
>       ]
>     where xs = [0 .. fssize s - 1]
>           f = fsappend s

> assertJust :: String -> Maybe a -> Assertion
> assertJust lbl = assertBool lbl . maybe False (const True)

> assertSeparation :: FiniteSemigroupRep s =>
>                     String -> (s -> Bool) -> (s -> Bool) -> s
>                  -> Assertion
> assertSeparation lbl c_in c_out s
>     = (  assertBool (lbl ++ " (membership)") (c_in s)
>       >> assertBool (lbl ++ " (exclusion)") (not $ c_out s))

> spb :: [[Int]]
> spb = [[0,1,2,3],[1,1,3,3],[0,2,2,3]]

> def1, def2, rdef2, j, lj1, z3 :: GeneratedAction
> def1 = fromBases [[1,1,1],[2,2,2]]
> def2 = fromBases [[0,0,0],[1,2,2]]
> rdef2 = fromBases [[3,3,2,3],[1,2,2,3]]
> j = fromBases [[0,1,2,3],[1,1,3,3],[0,2,2,3]]
> lj1 = fromBases [[0,0,2],[0,2,2],[1,1,2]]
> z3 = fromBases [[0,1,2],[1,2,0]]

> class_def1, class_def2, class_rdef2, class_j, class_z3 ::
>     [GeneratedAction -> Bool]
> class_def1 = [ isAperiodic
>              , isBand
>              , not . isCommutative
>              , isDA
>              , not . isJTrivial
>              , isLTrivial
>              , not . isNilpotent
>              , not . isRTrivial
>              , not . isTrivial
>              , locally isTrivial
>              ]
> class_def2 = [ isAperiodic
>              , not . isBand
>              , not . isCommutative
>              , isDA
>              , not . isJTrivial
>              , isLTrivial
>              , not . isNilpotent
>              , not . isRTrivial
>              , not . isTrivial
>              , locally isTrivial
>              ]
> class_rdef2 = [ isAperiodic
>               , not . isBand
>               , not . isCommutative
>               , isDA
>               , not . isJTrivial
>               , not . isLTrivial
>               , not . isNilpotent
>               , isRTrivial
>               , not . isTrivial
>               , locally isTrivial
>               ]
> class_j = [ isAperiodic
>           , not . isBand
>           , not . isCommutative
>           , isDA
>           , isJTrivial
>           , isLTrivial
>           , not . isNilpotent
>           , isRTrivial
>           , not . isTrivial
>           , not . locally isTrivial
>           ]
> class_z3 = [ not . isAperiodic
>            , not . isBand
>            , isCommutative
>            , not . isDA
>            , not . isJTrivial
>            , not . isLTrivial
>            , not . isNilpotent
>            , not . isRTrivial
>            , not . isTrivial
>            , not . locally isTrivial
>            , not . locally isAperiodic
>            ]

> both :: (a -> Bool) -> (a -> Bool) -> a -> Bool
> both f g x = f x && g x
