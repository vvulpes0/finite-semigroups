> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : Data.Representation.FiniteSemigroup.Order
> Copyright : (c) 2023 Dakotah Lambert
> License   : MIT

> This module provides support for quasiordered semigroups.
> -}

> module Data.Representation.FiniteSemigroup.Order
>     ( OrderedSemigroup(unordered,orel)
>     , odual, sdual
>     , assignOrder
>     , assignOrderBy
>     , fromBasesWith
>     , syntacticOrder
>     , trivialOrder
>     ) where

> import Data.Representation.FiniteSemigroup.Base

> import Data.IntSet (IntSet)
> import qualified Data.IntMap as IntMap
> import qualified Data.IntSet as IntSet

> -- |A semigroup alongside a preorder (reflexive and transitive).
> -- The constructor itself is not exported
> -- so as to enforce this condition.
> data OrderedSemigroup s
>     = OrderedSemigroup { unordered :: s
>                        , orel :: [(Int,Int)]
>                        } deriving (Eq, Ord)
> instance FiniteSemigroupRep s =>
>     FiniteSemigroupRep (OrderedSemigroup s) where
>         fsappend = fsappend . unordered
>         fstable = fstable . unordered
>         fssize = fssize . unordered
>         fsnbases = fsnbases . unordered

> -- |Associate the reflexive, transitive closure of the given relation
> -- as an order for the given semigroup.
> assignOrder :: FiniteSemigroupRep s =>
>                [(Int,Int)] -> s -> OrderedSemigroup s
> assignOrder o s = OrderedSemigroup s (rtclose o')
>     where o' = map (\x -> (x,x)) [0..fssize s - 1] ++ o

> -- |Derive an order from the given function
> -- and associate it with the given semigroup.
> assignOrderBy :: FiniteSemigroupRep s =>
>               (s -> Int -> Int -> Bool) -> s -> OrderedSemigroup s
> assignOrderBy f s = assignOrder o s
>     where o = [(x,y) | x <- xs, y <- xs, f s x y]
>           xs = [0 .. fssize s - 1]

> -- |Create a 'GeneratedAction' alongside an order
> -- derived from the given function.
> fromBasesWith :: (GeneratedAction -> Int -> Int -> Bool) -> [[Int]]
>               -> OrderedSemigroup GeneratedAction
> fromBasesWith f = assignOrderBy f . fromBases

> -- |The order where \(x\leq y\) if and only if
> -- whenever \(uyv\) maps the given object into the given set,
> -- so too does \(uxv\).
> syntacticOrder :: Int -> IntSet
>                -> GeneratedAction -> Int -> Int -> Bool
> syntacticOrder q0 f s x y = all coimpl ps
>     where final = mapsInto s f q0
>           xs = [0 .. fssize s - 1]
>           ps = [(eval [u,x,v], eval [u,y,v]) | u <- xs, v <- xs]
>           eval = foldr1 (fsappend s)
>           coimpl p = (fst p `IntSet.member` final)
>                      || (snd p `IntSet.notMember` final)

> -- |The order where \(x\leq y\) if and only if \(x=y\).
> trivialOrder :: s -> Int -> Int -> Bool
> trivialOrder _ = (==)

> -- |Return the given semigroup with its order reversed.
> odual :: OrderedSemigroup s -> OrderedSemigroup s
> odual s = s { orel = map (\p -> (snd p, fst p)) $ orel s }
> -- |Return the given semigroup with its multiplication reversed.
> sdual :: FiniteSemigroupRep s =>
>          OrderedSemigroup s -> OrderedSemigroup FSMult
> sdual s = s { unordered = dual (unordered s) }

> -- |Given a relation as a collection of pairs,
> -- return its reflexive transitive closure.
> rtclose :: [(Int,Int)] -> [(Int,Int)]
> rtclose ps = concatMap
>              (\p -> map ((,) (fst p)) . IntSet.toList $ snd p)
>              . IntMap.assocs . fst
>              . until (uncurry (==)) (\(_,a) -> (a, go a))
>              $ (base, go base)
>     where xs = foldr (\p a -> fst p : snd p : a) [] ps
>           base = IntMap.fromListWith IntSet.union
>                  . map (fmap IntSet.singleton)
>                  $ (map (\x -> (x,x)) xs) ++ ps
>           go m = IntMap.map
>                  (IntSet.foldr
>                   (\a b -> IntSet.union (m IntMap.! a) b)
>                   IntSet.empty)
>                  m

> -- |Given a relation, remove all elements of the form $(x,x)$,
> -- then, for each element of the form $(x,z)$,
> -- if, for some $y$, $(x,y)$ and $(y,z)$ are both elements
> -- of what remains after removing $(x,z)$, then remove $(x,z)$.
> rtreduce :: [(Int,Int)] -> [(Int,Int)]
> rtreduce ps = tred [] r
>     where r = filter (not . uncurry (==)) ps
>           tred xs [] = reverse xs
>           tred xs (~(a,b):ys)
>               = let ps' = filter (not . uncurry (==))
>                           $ rtclose (xs ++ ys)
>                     sucs = IntSet.fromList . map snd
>                            $ filter ((== a) . fst) ps'
>                     pres = IntSet.fromList
>                            $ map fst $ filter ((== b) . snd) ps'
>                     xs' = if ( IntSet.null
>                              $ IntSet.intersection sucs pres)
>                           then (a,b):xs
>                           else xs
>                 in tred xs' ys

> -- |From the documentation: precedence of function application is 10
> app_prec :: Int
> app_prec = 10

> instance (FiniteSemigroupRep s, Show s) =>
>     Show (OrderedSemigroup s) where
>         showsPrec d os
>             = showParen (d > app_prec) $ showString "assignOrder "
>               . showsPrec (app_prec + 1) (rtreduce $ orel os)
>               . showString " "
>               . showsPrec (app_prec + 1) (unordered os)

> instance (FiniteSemigroupRep s, Read s) =>
>     Read (OrderedSemigroup s) where
>         readsPrec d r
>             = readParen (d > app_prec)
>               (\x -> [ (assignOrder ps u, z)
>                      | ("assignOrder",s) <- lex x
>                      , (ps,t) <- readsPrec (app_prec + 1) s
>                      , (u,z) <- readsPrec (app_prec + 1) t]) r
