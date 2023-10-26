> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : Data.Representation.FiniteSemigroup.Classification
> Copyright : (c) 2023 Dakotah Lambert
> License   : MIT

> This module provides classification algorithms for finite semigroups.
> -}

> module Data.Representation.FiniteSemigroup.Classification
>     ( isAperiodic
>     , isBand
>     , isCommutative
>     , isDA
>     , isJTrivial
>     , isLTrivial
>     , isNilpotent
>     , isRTrivial
>     , isTrivial
>     , locally
>     ) where

> import Data.Representation.FiniteSemigroup.Base

> import qualified Data.IntSet as IntSet
> import Data.List (intersect, sort, transpose)
> import qualified Data.List.NonEmpty as NE


> -- |True if and only if all subgroups are trivial.
> -- That is, no two distinct elements
> -- are both \(\mathcal{L}\)-related and \(\mathcal{R}\)-related.
> isAperiodic :: FiniteSemigroupRep s => s -> Bool
> isAperiodic = all (== 1) . groupSizes

> -- |True if and only if all elements are idempotent.
> isBand :: FiniteSemigroupRep s => s -> Bool
> isBand = same (IntSet.size . idempotents) fssize

For commutativity: only the bases need to be checked.

> -- |True if and only if \(xy=yx\) for all \(x\) and \(y\).
> isCommutative :: FiniteSemigroupRep s => s -> Bool
> isCommutative s = same (bs . transpose) bs . getTable $ fstable s
>     where bs = take (fsnbases s)

> -- |True if and only if all regular \(\mathcal{D}\)-classes
> -- are aperiodic semigroups.
> -- Equivalently: all regular elements are idempotent.
> isDA :: FiniteSemigroupRep s => s -> Bool
> isDA s = not . any mixed $ rClasses t
>     where t = fstable s
>           is = idempotents t
>           mixed (x NE.:| xs)
>               | x `IntSet.member` is = any (`IntSet.notMember` is) xs
>               | otherwise            = any (`IntSet.member` is) xs

> -- |True if and only if no two distinct elements
> -- are \(\mathcal{J}\)-related.
> -- Equivalently:
> -- both \(\mathcal{L}\)-trivial and \(\mathcal{R}\)-trivial.
> isJTrivial :: FiniteSemigroupRep s => s -> Bool
> isJTrivial = both isRTrivial isLTrivial

> -- |True if and only if no two distinct elements
> -- are \(\mathcal{L}\)-related.
> isLTrivial :: FiniteSemigroupRep s => s -> Bool
> isLTrivial = all (null . NE.tail) . lClasses

> -- |True if and only if the only idempotent element is zero.
> isNilpotent :: FiniteSemigroupRep s => s -> Bool
> isNilpotent = both isRTrivial ((== 1) . IntSet.size . idempotents)

> -- |True if and only if no two distinct elements
> -- are \(\mathcal{L}\)-related.
> isRTrivial :: FiniteSemigroupRep s => s -> Bool
> isRTrivial = all (null . NE.tail) . rClasses

> -- |True if and only if there is but a single element.
> isTrivial :: FiniteSemigroupRep s => s -> Bool
> isTrivial = (<2) . fssize

> -- |True if and only if each of the 'localSubmonoids'
> -- satisfies the given proposition.
> locally :: FiniteSemigroupRep s => (FSMult -> Bool) -> s -> Bool
> locally f = all f . localSubmonoids


> -- |For each \(\mathcal{D}\)-class,
> -- yields an integer describing how many elements
> -- are in each group within that class.
> groupSizes :: FiniteSemigroupRep s => s -> [Int]
> groupSizes s = map (succ . length) . map (uncurry intersect)
>                $ mergeEmitBy f NE.head rc lc
>     where t = fstable s
>           rc = sort $ rClasses t
>           lc = sort $ lClasses t
>           f x y = (NE.tail x, NE.tail y)


> mergeEmitBy :: Ord c => (a -> a -> b) -> (a -> c) -> [a] -> [a] -> [b]
> mergeEmitBy _ _ [] _ = []
> mergeEmitBy _ _ _ [] = []
> mergeEmitBy emit by (x:xs) (y:ys)
>     = case compare (by x) (by y) of
>         EQ -> emit x y : mergeEmitBy emit by xs ys
>         LT -> mergeEmitBy emit by xs (y:ys)
>         GT -> mergeEmitBy emit by (x:xs) ys

> same :: Eq b => (a -> b) -> (a -> b) -> a -> Bool
> same f g a = f a == g a

> both :: (a -> Bool) -> (a -> Bool) -> a -> Bool
> both f g a = f a && g a
