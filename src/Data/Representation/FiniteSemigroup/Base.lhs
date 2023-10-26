> {-# OPTIONS_HADDOCK hide,show-extensions #-}
> {-# LANGUAGE Safe #-}
> {-|
> Module    : Data.Representation.FiniteSemigroup.Base
> Copyright : (c) 2023 Dakotah Lambert
> License   : MIT

> This module provides the primary operations for finite semigroups.
> -}

> module Data.Representation.FiniteSemigroup.Base
>     ( -- *Representations of Finite Semigroups
>       FiniteSemigroupRep(..)
>     , FSMult(getTable)
>     , GeneratedAction(bases,completion)
>       -- *Generation by Elements
>     , fromBases
>     , mapsInto
>     , independentBases
>     , subsemigroup
>     , asActions
>       -- *Derived Semigroups
>     , localSubsemigroup
>     , localSubmonoids
>     , emee
>     , dual
>     , monoid
>     , projectedSubsemigroup
>       -- *Ideals and Orders
>       -- |Here, an order is a reflexive, transitive relation
>       -- parameterized by semigroup.
>     , ideal2
>     , jleq
>       -- *Special Kinds of Elements
>     , neutralElement
>     , adjoinOne
>     , zeroElement
>     , adjoinZero
>     , idempotents
>     , omega
>     , omegas
>     , lClasses
>     , rClasses
>     ) where

> --import qualified Vector as V
> import Data.List ((\\), elemIndex, sort, sortBy, transpose)
> import Data.Ord (comparing)
> import qualified Data.List.NonEmpty as NE
> import Data.IntSet (IntSet)
> import qualified Data.Set as Set
> import qualified Data.IntSet as IntSet
> import Safe

> -- |A representation of a finite semigroup.
> -- Unlike the @Semigroup@ typeclass,
> -- this does not refer to a type whose objects
> -- collectively form a semigroup.
> -- Instead, it is a type
> -- whose objects individually represent semigroups.
> class FiniteSemigroupRep a where
>     -- |The multiplication of the semigroup.
>     fsappend :: a -> Int -> Int -> Int
>     fsappend s x y = atDef (-1) (atDef [] (getTable (fstable s)) x) y
>     -- |The multiplication table of the semigroup.
>     -- In the list at index @x@, the element at index @y@ is @xy@.
>     fstable :: a -> FSMult
>     fstable s
>         = let es = [0..(fssize s - 1)]
>           in FSMult (fsnbases s)
>              $ map (\x -> map (\y -> fsappend s x y) es) es
>     -- |The number of elements in the semigroup.
>     fssize :: a -> Int
>     fssize = length . getTable . fstable
>     -- |The number of generators (always the first elements).
>     fsnbases :: a -> Int
>     fsnbases = fssize
>     {-# MINIMAL (fsappend,fssize)|fstable #-}

A multiplication table can define a semigroup,
but we shall not allow direct creation of such objects
outside of this module, in order to ensure associativity.

> -- |A semigroup presented as a multiplication table.
> -- Use 'getTable' to extract the actual table;
> -- this type is otherwise opaque.
> data FSMult = FSMult { basisRows :: Int
>                      , getTable :: [[Int]]
>                      } deriving (Eq, Ord)
> instance FiniteSemigroupRep FSMult where
>     fstable t = t
>     fsnbases = basisRows


Operations on Semigroups
========================

> -- |Return the elements that square to themselves
> -- as an ascending list.
> idempotents :: FiniteSemigroupRep s => s -> IntSet
> idempotents = foldr f IntSet.empty . zip [0..] . getTable . fstable
>     where f ~(p,x) = if atMay x p == Just p
>                      then (p `IntSet.insert`)
>                      else id

> -- |Return an action mapping semigroup elements
> -- to their unique idempotent powers.
> omegas :: FiniteSemigroupRep s => s -> [Int]
> omegas s = map (omega s) [0..fssize s - 1]

> -- |Return the unique idempotent power of the given element.
> -- The result of @omega s i@ is the @i@th element of @omegas s@,
> -- if @i@ is a valid element index.
> omega :: FiniteSemigroupRep s => s -> Int -> Int
> omega s x = fst $ until (uncurry (==)) (go . fst) (go x)
>     where go a = let y = fsappend s x a
>                  in (y, fsappend s y y)

> -- |Reverse the multiplication of the semigroup.
> dual :: FiniteSemigroupRep s => s -> FSMult
> dual s = FSMult (fsnbases s) . transpose . getTable $ fstable s

> -- |Partition the elements of the semigroup \(S\)
> -- such that distinct elements \(x\) and \(y\) are in the same region
> -- if and only if there are \(s\) and \(t\)
> -- such that \(y=sx\) and \(x=ty\).
> rClasses :: FiniteSemigroupRep s => s -> [NE.NonEmpty Int]
> rClasses = map (NE.map snd) . NE.groupBy (equal fst)
>            . sort . map (\p -> (row p, fst p)) . zip [0..]
>            . getTable . fstable
>     where row p = IntSet.fromList $ uncurry (:) p

> -- |Partition the elements of the semigroup \(S\)
> -- such that distinct elements \(x\) and \(y\) are in the same region
> -- if and only if there are \(s\) and \(t\)
> -- such that \(y=xs\) and \(x=yt\).
> lClasses :: FiniteSemigroupRep s => s -> [NE.NonEmpty Int]
> lClasses = rClasses . dual

> -- |Return the local subsemigroup of the given semigroup \(S\)
> -- formed by wrapping elements with the given element \(i\).
> -- That is, all and only elements of the form \(isi\) for \(s\in S\)
> -- are included.
> localSubsemigroup :: FiniteSemigroupRep s => s -> Int -> FSMult
> localSubsemigroup s i = restrict t xs
>     where t = fstable s
>           si = flip (atDef []) i . getTable $ dual t
>           xs = map (NE.head) . NE.group . sort
>                . flip backpermute si . flip (atDef []) i $ getTable t

> -- |Return the local subsemigroups of the given semigroup
> -- which happen to be monoids.
> -- These are the ones whose wrapping element is idempotent.
> -- If the semigroup itself is a monoid, it is in the list.
> localSubmonoids :: FiniteSemigroupRep s => s -> [FSMult]
> localSubmonoids s = map (localSubsemigroup s)
>                     . IntSet.toList $ idempotents s

> -- |If the given semigroup is a monoid,
> -- return 'Just' its neutral element.
> -- Otherwise return 'Nothing'.
> neutralElement :: FiniteSemigroupRep s => s -> Maybe Int
> neutralElement s
>     = headMay . map fst . filter (and . snd) . zip [0..]
>       $ zipWith (zipWith (&&)) (proper t) (proper $ dual t)
>     where t = fstable s
>           proper = map (zipWith (==) [0..]) . getTable

> -- |If the given semigroup has an element which is both a left-
> -- and right-zero, that is, an element e where \(ex=e=xe\)
> -- for all \(x\), return 'Just' that zero.
> -- Otherwise, return 'Nothing'.
> zeroElement :: FiniteSemigroupRep s => s -> Maybe Int
> zeroElement s = headMay . map fst . filter snd . zip [0..]
>                 $ zipWith (&&) (f t) (f $ dual t)
>     where alleq x xs = all (== x) xs
>           f = zipWith alleq [0..] . getTable
>           t = fstable s

> -- |If the given semigroup is not a monoid, then it is returned as-is.
> -- Otherwise, the neutral element is removed if possible,
> -- that is, if it cannot be written in terms of other elements.
> projectedSubsemigroup :: FiniteSemigroupRep s => s -> FSMult
> projectedSubsemigroup s = restrict t ([0..fssize t - 1] \\ n)
>     where t = fstable s
>           n = maybe [] f $ neutralElement t
>           f x = if null . drop 1 . filter (==x) . concat $ getTable t
>                 then [x] else []


Ideals and Orders
=================

> -- |Given an element \(x\), return the set of elements
> -- representable as \(sxt\) for some \(s\) and \(t\) in \(S^1\),
> -- as a distinct ascending list.
> ideal2 :: FiniteSemigroupRep s => s -> Int -> IntSet
> ideal2 s i = IntSet.unions . map (IntSet.fromList)
>              . backpermuteDef []
>                (zipWith (:) [0..] . getTable $ dual s)
>              . map (NE.head) . NE.group . sort
>              . (i:) . flip (atDef []) i . getTable $ fstable s

> -- |The \(\mathcal{J}\)-order: \(x\leq y\) if and only if
> -- \(x=syt\) for some \(s\) and \(t\) in \(S^1\).
> jleq :: FiniteSemigroupRep s => s -> Int -> Int -> Bool
> jleq s x y = x `IntSet.member` ideal2 s y

> -- |Return the bases that are greater than or equal to
> -- each idempotent, with respect to the \(\mathcal{J}\)-order.
> me :: FiniteSemigroupRep s => s -> [IntSet]
> me s = foldr f (map (const IntSet.empty) is)
>        [0 .. fsnbases s - 1]
>     where is = IntSet.toList $ idempotents s
>           f b a = zipWith ($) (map (g b (ideal2 s b)) is) a
>           g b p i = if i `IntSet.member` p
>                     then IntSet.insert b else id

> -- |Return a list of subsemigroups of the form
> -- \(e\cdot M_e\cdot e\) for idempotent \(e\),
> -- where \(M_e\) is the set of elements generated by those elements
> -- greater than or equal to \(e\) with respect to
> -- the \(\mathcal{J}\)-order.
> emee :: FiniteSemigroupRep s => s -> [FSMult]
> emee s = zipWith f (IntSet.toList $ idempotents s) (me s)
>     where t = fstable s
>           f e = restrict t
>                 . map (NE.head) . NE.group . sort
>                 . map (\x -> foldr (fsappend s) e [e,x])
>                 . IntSet.toList
>                 . subsemigroup s


Adjoining Elements
==================

> -- |Insert a new element \(e\) such that for all elements \(x\),
> -- it holds that \(ex=x=xe\).
> adjoinOne :: FiniteSemigroupRep s => s -> FSMult
> adjoinOne s = FSMult (fsnbases s + 1) . f
>               . map (uncurry (:)) . zip [1..] . map (map succ)
>               . getTable $ fstable s
>     where f xs = zipWith const [0..] ([]:xs) : xs

> -- |Insert a new element \(e\) such that for all elements \(x\),
> -- it holds that \(ex=e=xe\).
> adjoinZero :: FiniteSemigroupRep s => s -> FSMult
> adjoinZero s = FSMult (fsnbases s + 1) . f . map ((0 :) . map succ)
>                . getTable $ fstable s
>     where f xs = zipWith const (repeat 0) ([]:xs) : xs

> -- |If the given semigroup is already a monoid, returns it.
> -- Otherwise, returns a monoid by adjoining a neutral element.
> monoid :: FiniteSemigroupRep s => s -> FSMult
> monoid s = maybe (adjoinOne s) (const (fstable s)) $ neutralElement s


Generated Actions
=================

> -- |A semigroup presented as a collection of actions.
> -- The 'bases' are the given set of generating actions,
> -- while the 'completion' is the set of other semigroup elements.
> data GeneratedAction
>     = GeneratedAction { bases :: [[Int]]
>                       , completion :: [[Int]]
>                       }
>       deriving (Eq, Ord)

> -- |Construct a semigroup from a set of generating transformations.
> -- Transformations are given as functions over an initial segment
> -- of the nonnegative integers.
> -- The transformation @[a,b,c]@ maps 0 to @a@, 1 to @b@, and 2 to @c@.
> fromBases :: [[Int]] -> GeneratedAction
> fromBases [] = GeneratedAction { bases = [[0]], completion = [[0]] }
> fromBases ys = GeneratedAction
>                { bases = xs
>                , completion = Set.toList . flip Set.difference xs'
>                               $ go Set.empty xs'
>                }
>     where xs = Set.toList xs'
>           xs' = Set.fromList ys
>           go done new
>               | Set.null new = done
>               | otherwise = go d (Set.difference n d)
>               where d = done `Set.union` new
>                     n = Set.unions
>                         $ map (\b -> Set.map (backpermute b) new) xs

> -- |Returns the set of element indices
> -- in the given transformation that map the given object
> -- into the given set.
> mapsInto :: GeneratedAction -> IntSet -> Int -> IntSet
> mapsInto s h q = IntSet.fromList . map fst . filter snd . zip [0..]
>                  . map ( maybe False (`IntSet.member` h)
>                        . flip atMay q )
>                  $ (bases s ++ completion s)

> -- |The subsemigroup of the given semigroup
> -- generated by the indicated elements.
> subsemigroup :: FiniteSemigroupRep s => s -> IntSet -> IntSet
> subsemigroup s xs = go IntSet.empty xs
>     where is = IntSet.toList xs
>           go done new
>               | IntSet.null new = done
>               | otherwise = go d (IntSet.difference n d)
>               where d = done `IntSet.union` new
>                     n = IntSet.unions
>                         $ map (\i -> IntSet.map (fsappend s i) new) is

> -- |Create an action semigroup whose bases correspond
> -- to the given elements; for each element \(i\), there is a basis
> -- representing the transformation \(f(x)=xi\).
> asActions :: FiniteSemigroupRep s => s -> [Int] -> GeneratedAction
> asActions s is = fromBases . flip (backpermuteDef []) is
>                  . drop 1 . getTable . adjoinOne $ dual s

> instance FiniteSemigroupRep GeneratedAction where
>     fsappend s a b = let c = bases s ++ completion s
>                          x = atDef [] c a
>                          y = atDef [] c b
>                      in maybe (-1) id $ elemIndex (backpermute y x) c
>     fssize s = length (bases s) + length (completion s)
>     fsnbases = length . bases

> -- |Find a small set of basis elements such that
> -- none can be written in terms of the others
> -- and the entire semigroup can be written
> -- in terms of these bases.
> independentBases :: FiniteSemigroupRep s => s -> [[Int]]
> independentBases = go [] . drop 1 . getTable . adjoinOne . dual
>     where go keep (x:xs)
>               | x `elem` completion (fromBases (reverse keep ++ xs))
>                   = go keep xs
>               | otherwise = go (x:keep) xs
>           go keep _ = reverse keep

There is almost certainly a more efficient procedure
for basis-extraction that makes use of the J-order.
What it might be is a question for later.


Helper Functions
================

> backpermute :: [Int] -> [Int] -> [Int]
> backpermute = backpermuteDef (-1)

The call 'backpermute xs is' is equivalent to grabbing the elements
of xs at the given indices 'map (flip (atDef (-1)) xs) is';
however, on lists the lookup is a linear-time operation,
so doing it n times becomes quadratic.
We can improve this by first doing an nlgn sort
to get the indices in order.
Then one single linear scan will suffice to extract the elements,
and we can sort again to put things where they belong.

> backpermuteDef  :: a -> [a] -> [Int] -> [a]
> backpermuteDef a xs = map fst . sortBy (comparing snd)
>                       . extract xs . deltas . ((0,0):)
>                       . sort . flip zip [0::Int ..]
>     where deltas (x:y:ys) = (fst y - fst x, snd y) : deltas (y:ys)
>           deltas _ = []
>           extract ys (p:ps) = grab (snd p) (drop (fst p) ys) ps
>           extract _ _ = []
>           grab i ys ns = case ys of
>                            (y:_) -> ( y,i) : extract ys ns
>                            _     -> ( a,i) : extract ys ns

> equal :: Eq b => (a -> b) -> a -> a -> Bool
> equal f x y = f x == f y

> -- |Internal, not for export.
> -- Return a multiplication table by extracting rows and columns
> -- from a larger multiplication table and renaming elements.
> restrict :: FSMult -> [Int] -> FSMult
> restrict t xs
>     = f . map (map (maybe (-1) id . flip elemIndex xs))
>       . map (flip backpermute xs) . flip (backpermuteDef []) xs
>       $ getTable t
>     where f m = FSMult (length m) m


I/O
===

> -- |From the documentation: precedence of function application is 10
> app_prec :: Int
> app_prec = 10

> instance Show GeneratedAction where
>     showsPrec d ga
>         = showParen (d > app_prec) $ showString "fromBases "
>           . showsPrec (app_prec + 1) (bases ga)
> instance Read GeneratedAction where
>     readsPrec d r
>         = readParen (d > app_prec)
>           (\x -> [ (fromBases bs, t)
>                  | ("fromBases",s) <- lex x
>                  , (bs,t) <- readsPrec (app_prec + 1) s]) r

We do not want people giving us arbitrary tables
which might not be associative.
But we really do want to be able to see things.
And since Show/Read are supposed to be inverses,
let's make it happen: go via fromBases and all will be fine.

> instance Show FSMult where
>     showsPrec d mt
>         = showParen (d > app_prec)
>           $ showString "fstable "
>           . ( showParen True
>             $ showString "fromBases " . showsPrec (app_prec + 1) bs)
>         where bs = take (basisRows mt) . drop 1 . getTable
>                    . adjoinOne $ dual mt
> instance Read FSMult where
>     readsPrec d r
>         = readParen (d > app_prec)
>           (\x -> [ (fstable (bs :: GeneratedAction), t)
>                  | ("fstable",s) <- lex x
>                  , (bs,t) <- readsPrec (app_prec + 1) s]) r
