# Finite Semigroups
![Current Version](https://img.shields.io/badge/version-0.1-informational.svg)
![License](https://img.shields.io/github/license/vvulpes0/finite-semigroups)
![Issues](https://img.shields.io/github/issues/vvulpes0/finite-semigroups)

A Haskell library for constructing and analyzing finite semigroups.

Originally part of the [Language Toolkit][1],
the systems here allow one to specify a finite semigroup
via some set of generating actions,
with or without an ordering relation,
and decide whether the resulting semigroup has certain properties.

# Features
Construct an action semigroup from bases:
```hs
ghci> s = fromBases [[0,0,2],[1,2,2]]
ghci> s
fromBases [[0,0,2],[1,2,2]]
```

Construct the multiplication table,
either as another semigroup representation
or as an actual table:
```hs
ghci> fstable s
fstable (fromBases [[1,1,3,3,1,5],[2,4,5,2,5,5]])
ghci> printTable = mapM_ print . getTable . fstable
ghci> printTable s
[0,3,0,3,4]
[2,4,4,1,4]
[2,1,2,1,4]
[0,4,4,3,4]
[4,4,4,4,4]
```

Convert a semigroup into a monoid, or vice versa:
```hs
ghci> printTable (monoid s)
[0,1,2,3,4,5]
[1,1,4,1,4,5]
[2,3,5,5,2,5]
[3,3,2,3,2,5]
[4,1,5,5,4,5]
[5,5,5,5,5,5]
ghci> m = monoid s
ghci> printTable (projectedSubsemigroup m)
[0,3,0,3,4]
[2,4,4,1,4]
[2,1,2,1,4]
[0,4,4,3,4]
[4,4,4,4,4]
```

Adjoin an order to a semigroup:
```hs
ghci> import qualified Data.IntSet as IntSet
ghci> os = assignOrderBy (syntacticOrder 0 (IntSet.fromList [0,2])) s
ghci> os
assignOrder [(1,2),(1,3),(2,0),(3,0),(4,1)] (fromBases [[0,0,2],[1,2,2]])
```

Determine whether a semigroup satisifies some predefined properties:
```hs
ghci> isAperiodic s
True
ghci> isDA s
False
ghci> locally isTrivial s
False
ghci> locally isBand s
True
ghci> locally isCommutative s
True
```

Determine if an ordered semigroup is in an ordered pseudovariety:
```hs
ghci> isVariety "[a*xa* < a*]" os
Just True
ghci> isVariety "[a*xa* = a*]" os
Just False
```

[1]: https://hackage.haskell.org/package/language-toolkit
