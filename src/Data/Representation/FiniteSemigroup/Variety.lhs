> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : Data.Representation.FiniteSemigroup.Variety
> Copyright : (c) 2023 Dakotah Lambert
> License   : MIT

> This module provides a general mechanism
> for constructing decision procedures
> given an equational characterization of a pseudovariety,
> or an inequational characterization of an ordered pseudovariety.
> One parses the collection of equations,
> quantifies universally over the bound variables,
> and determines whether all specified relationships hold.
> -}

> module Data.Representation.FiniteSemigroup.Variety
>     ( -- * Documentation
>       -- $doc
>       isVariety
>     ) where

> import Data.Char (isSpace)
> import Data.List (transpose)
> import Data.Maybe (isJust,maybeToList)

> import Data.Representation.FiniteSemigroup.Base
> import Data.Representation.FiniteSemigroup.Order

> {- $doc
> A (pseudo)variety is specified here by a system of equations.
> These equations may contain (single-letter) variables,
> which are universally quantified.
> The grammar is as follows:

> >      expr ::= '[' conj-list ']'
> > conj-list ::= rel-list ';' conj-list | rel-list
> >  rel-list ::= value op rel-list | value op value
> >        op ::= '=' | '<' | '≤' | '>' | '≥'
> >     value ::= value value | iter
> >      iter ::= '0' | '1' | LETTER | '(' value ')' | iter '*'

> Here, @LETTER@ refers to any character which Unicode deems a letter.
> Concatenation is denoted by adjacency,
> and @x*@ represents the unique element of the form
> @x@, @xx@, and so on, such that @x*x*=x*@.
> A @LETTER@ represents a universally-quantified variable,
> while @0@ and @1@ refer to the unique elements where for all @x@
> it holds that @0x=0=x0@ and @1x=x=x1@,
> if such elements exist.
> If @0@ or @1@ is used in an equation,
> but the given structure lacks such an element,
> then the structure of course does not satisfy the equality.

> The equality @x=y@ asserts that,
> for all possible variable instantiations,
> the value of @x@ is the same as that of @y@.
> The inequality @x<y@ asserts that,
> for all possible variable instantiations,
> the value @x@ is less than that of @y@ in the specified order.
> For longer chains of relations, adjacent pairs are tested.
> That is, @[a\<b>c]@ is equivalent to @[a\<b;b>c]@.
> Essentially, the semicolon is an "and" operator.

> Suppose we wish to express the \(*\)-variety
> of idempotent and commutative monoids.
> A monoid is idempotent if and only if it holds that @xx=x@
> for all values @x@, which can also be expressed as @x*=x@.
> It is commutative if and only if @ab=ba@ for all @a@ and @b@.
> This variety could then be expressed as @[ab=ba;x*=x]@.
> -}

We shall assume that we are working with forests
wherein each tree represents a set of equalities that must hold
and all variables are universally quantified.
Variables are formal and represented only by integer indices.

> data VRelChain a = VRelChain (VEx a) [(Ordering, VEx a)]
>                    deriving (Eq, Ord, Read, Show)
> data VEx a = VVar Int
>            | VOmega (VEx a)
>            | VConcat (VEx a) [VEx a]
>            | VOne
>            | VZero
>            | VElement a
>              deriving (Eq, Ord, Read, Show)

The VOne and VZero expressions stand in for a neutral element and a zero,
respectively, in the senses typical when discussion semigroups.
VConcat represents the semigroup's multiplication.
And finally, VOmega represents the omega operator, \(x^{\omega}\),
the unique idempotent power of \(x\).

The end goal is a function to decide whether a collection of equalities
always holds true for all possible instantiations:

> satisfiedUniversally :: Eq a => (a -> a -> a) -> (a -> a)
>                      -> Maybe a -> Maybe a -> [a]
>                      -> [(a,a)]
>                      -> [VRelChain a] -> Bool
> satisfiedUniversally cat star zero one xs order vs'
>     = maybe False f vs
>     where f = all (evaluate order)
>               . concatMap (instantiations cat star xs 0)
>           vs = splatMap (fillzo zero one) vs'

We then can use this to decide membership in a variety.

> -- |Determine whether a given semigroup is in the pseudovariety
> -- described by the given equation set.
> -- Returns Nothing if and only if the equation set cannot be parsed.
> -- To check for a \(*\)-variety, pass in a monoid.
> -- For a \(+\)-variety, use a semigroup.
> isVariety :: FiniteSemigroupRep s =>
>              String -> OrderedSemigroup s -> Maybe Bool
> isVariety desc s
>     = flip fmap v
>       $ satisfiedUniversally (fsappend s) (omega s)
>         zero one qs (orel s)
>     where zero = zeroElement s
>           one  = neutralElement s
>           qs   = [0 .. fssize s - 1]
>           v    = fmap (transform '0' '1') . fst $ ckyParse [] desc

In order to make this actually work, we shall attempt,
for each chain of equalities, to find a counterexample.
The first step is to actually instantiate any zeros or ones.
If they are used in the equalities but do not exist,
then clearly the system cannot hold true.

> fillzo :: Maybe a -> Maybe a -> VRelChain a -> Maybe (VRelChain a)
> fillzo zero one (VRelChain v vs) = VRelChain <$> fill v <*> vs'
>     where fill (VOmega x) = VOmega <$> fill x
>           fill (VConcat x y) = VConcat <$> fill x <*> splatMap fill y
>           fill VOne = VElement <$> one
>           fill VZero = VElement <$> zero
>           fill x = Just x
>           vs' = splat $ map (\(a,b) -> fmap ((,) a) $ fill b) vs

Next, we'd like a way to evaluate any levels of the tree
whose children are fully concrete into something concrete.

> mkconcrete :: (a -> a -> a) -> (a -> a) -> VEx a -> VEx a
> mkconcrete cat star (VOmega x)
>     = case mkconcrete cat star x of
>         VElement e -> VElement $ star e
>         y -> VOmega y
> mkconcrete cat star (VConcat x xs) = f (m x) (map m xs)
>     where f (VElement y) ys
>               = case ys of
>                   VElement z : zs  ->  f (VElement $ cat y z) zs
>                   []               ->  VElement y
>                   _                ->  VConcat (VElement y) ys
>           f y ys = VConcat y ys
>           m = mkconcrete cat star
> mkconcrete _ _ v = v

Given a set of elements,
we'd like to instantiate every possible assignment of variables,
until either a counterexample is found or all options are exhausted.
We'll start by instantiating a single given variable to a value

> instantiate :: (a -> a -> a) -> (a -> a) -> a
>             -> Int -> VRelChain a -> VRelChain a
> instantiate cat star x n (VRelChain v vs)
>     = VRelChain (f v) (map (fmap f) vs)
>     where mkc = mkconcrete cat star
>           f (VOmega a) = mkc $ VOmega (f a)
>           f (VConcat a b) = mkc $ VConcat (f a) (map f b)
>           f (VVar m) = if m == n then VElement x else VVar m
>           f a = a

As long as there are variables remaining,
we'd like to instantiate another variable.

> instantiations :: (a -> a -> a) -> (a -> a) -> [a]
>                -> Int -> VRelChain a -> [VRelChain a]
> instantiations cat star xs n (VRelChain v' vs')
>     = if all concrete (mv:map snd mvs) then [v] else concatMap f xs
>     where concrete (VElement _) = True
>           concrete _ = False
>           m = mkconcrete cat star
>           mv = m v'
>           mvs = map (fmap m) vs'
>           v = VRelChain mv mvs
>           f x = instantiations cat star xs (n+1)
>                 $ instantiate cat star x n v

A chain of relations holds if and only if the adjacent elements
compare appropriately.  Equality is checked via true equality,
while inequalities are checked using the supplied ordering relation.

> evaluate :: Eq a => [(a,a)] -> VRelChain a -> Bool
> evaluate order (VRelChain x xs)
>     = case xs of
>         [] -> True
>         (y:ys) -> let rest = evaluate order (VRelChain (snd y) ys)
>                       z = snd y
>                   in case fst y of
>                        EQ -> x == z && rest
>                        LT -> x `leq` z && rest
>                        GT -> z `leq` x && rest
>     where leq (VElement a) (VElement b) = (a,b) `elem` order
>           leq _ _ = False



Parsing Simply: CKY
===================

> data ETag = EXPR | CLOSE_EXP
>           | CONJ_LIST | CONJUNCT
>           | REL_LIST | ELEM_REL
>           | ITER | ELEM | CLOSE_EL
>           | SOE | EOE | OPEN | CLOSE | AND | OMEGA
>           | EQU | LTE | GTE
>             deriving (Eq, Ord, Read, Show)
> data ETree a = Leaf ETag
>              | VLeaf a ETag
>              | Node ETag (ETree a) (ETree a)
>                deriving (Eq, Ord, Read, Show)

> tag :: ETree a -> ETag
> tag (Leaf x) = x
> tag (VLeaf _ x) = x
> tag (Node x _ _) = x

There is a one-to-one mapping between tokens and symbols;
use that and we don't need a tokenizer.
We'll allow for whitespace in expressions
by simply stripping it before parsing.

> mkunary :: Char -> [ETree Char]
> mkunary x = case x of
>               '[' -> [Leaf SOE]
>               ']' -> [Leaf EOE]
>               '(' -> [Leaf OPEN]
>               ')' -> [Leaf CLOSE]
>               ';' -> [Leaf AND]
>               '=' -> [Leaf EQU]
>               '<' -> [Leaf LTE]
>               '≤' -> [Leaf LTE]
>               '>' -> [Leaf GTE]
>               '≥' -> [Leaf GTE]
>               '*' -> [Leaf OMEGA]
>               _   -> [ VLeaf x ITER
>                      , VLeaf x ELEM
>                      ]

The combine function handles the binary branches in our CNF.

> combine :: ETree a -> ETree a -> [ETree a]
> combine x y = map (\t -> Node t x y)
>               $ case (tag x, tag y) of
>                   (SOE,        CLOSE_EXP)  ->  [EXPR]
>                   (CONJ_LIST,  EOE)        ->  [CLOSE_EXP]
>                   (REL_LIST,   EOE)        ->  [CLOSE_EXP]
>                   (CONJUNCT,   CONJ_LIST)  ->  [CONJ_LIST]
>                   (CONJUNCT,   REL_LIST)   ->  [CONJ_LIST]
>                   (REL_LIST,   AND)        ->  [CONJUNCT]
>                   (ELEM_REL,   REL_LIST)   ->  [REL_LIST]
>                   (ELEM_REL,   ELEM)       ->  [REL_LIST]
>                   (ELEM,       EQU)        ->  [ELEM_REL]
>                   (ELEM,       LTE)        ->  [ELEM_REL]
>                   (ELEM,       GTE)        ->  [ELEM_REL]
>                   (ELEM,       ELEM)       ->  [ELEM]
>                   (ITER,       OMEGA)      ->  [ITER, ELEM]
>                   (OPEN,       CLOSE_EL)   ->  [ITER, ELEM]
>                   (ELEM,       CLOSE)      ->  [CLOSE_EL]
>                   _                        ->  []

With that out of the way, we now have a complete grammar for expressions.
As the grammar is CNF, we can incrementally parse with CKY.
We'll grab the smallest expression out of a stream of input characters
and return the remainder.

> type Cell a = [ETree a]
> ckyExtend :: Cell a -> [[Cell a]] -> [[Cell a]]
> ckyExtend a xs = zipWith (:) nexts ([] : xs)
>     where nexts = a : map f xs
>           f x = concat $ zipWith combineCells nexts x

> combineCells :: Cell a -> Cell a -> Cell a
> combineCells q p = concatMap (uncurry combine) $ cartesian p q

> extractExpr :: [[Cell a]] -> Maybe (ETree a)
> extractExpr [] = Nothing
> extractExpr t = extract (last t)
>     where extract [] = Nothing
>           extract (x:_) = case filter ((== EXPR) . tag) x of
>                             (e:_)  ->  Just e
>                             _      ->  Nothing

> ckyParse :: [[Cell Char]] -> String -> (Maybe (ETree Char), String)
> ckyParse t [] = (extractExpr t, [])
> ckyParse t (x:xs)
>     | isJust output  =  (output, x:xs)
>     | isSpace x      =  try t
>     | otherwise      =  try $ ckyExtend (mkunary x) t
>     where output = extractExpr t
>           try t' = let ~(me, s) = ckyParse t' xs
>                    in case me of
>                         Nothing  ->  (me, x:xs)
>                         _        ->  (me, s)

To parse a string @s@, call @ckyParse [] s@.


The preceding CNF generates a grammar that is easy to parse,
but not necessarily easy to compute with.
Here we transform these trees into our originally-specified forests
wherein the trees are better suited for computation.

For each equality we'll be doing variable renaming.
Rather than carrying around arbitrary symbols,
we use formal variables numbered consecutively from 0.
Then we would say that [ab=ba;x*=x] truly uses only two variables,
rather than the three that one might first expect.

> vars :: Eq a => [a] -> ETree a -> [a]
> vars excl (Node _ x y)
>     = let v = vars excl x
>       in v ++ filter (`notElem` v) (vars excl y)
> vars excl (VLeaf a _) = filter (`notElem` excl) [a]
> vars _ _  = []

Now we are ready to translate between the tree formats.
At a high level, we either have a single equality
or a conjunction of several.
Each equality becomes a tree, and the whole is a forest.

> transform :: Eq a => a -> a -> ETree a -> [VRelChain b]
> transform zero one e
>     = case e of
>         (Node EXPR _ (Node CLOSE_EXP x _))
>             -> case tag x of
>                  CONJ_LIST -> forestFromConjList zero one x
>                  REL_LIST -> maybeToList $ treeFromEqList zero one x
>                  _ -> []
>         _ -> []
 
> forestFromConjList :: Eq a => a -> a -> ETree a -> [VRelChain b]
> forestFromConjList zero one t
>     = case t of
>         (Node CONJ_LIST (Node CONJUNCT x _) y)
>             -> case tag y of
>                  CONJ_LIST -> maybe []
>                               (: forestFromConjList zero one y)
>                               $ treeFromEqList zero one x
>                  REL_LIST -> let xs = treeFromEqList zero one x
>                                  ys = treeFromEqList zero one y
>                              in maybe [] (maybe (const []) f xs) ys
>                  _ -> []
>         _ -> []
>       where f x y = [x,y]

> treeFromEqList :: Eq a => a -> a -> ETree a -> Maybe (VRelChain b)
> treeFromEqList zero one t
>     = case tag t of
>         REL_LIST -> treesFromCons zero one vs t
>         _ -> Nothing
>     where vs = vars [zero, one] t

> treesFromCons :: Eq a => a -> a -> [a] -> ETree a
>               -> Maybe (VRelChain b)
> treesFromCons zero one vs t
>     = case tag t of
>         ELEM -> (flip VRelChain []) <$> (treeFromEx zero one vs t)
>         REL_LIST -> case t of
>                       (Node REL_LIST (Node ELEM_REL x (Leaf EQU)) y)
>                           -> f EQ x y
>                       (Node REL_LIST (Node ELEM_REL x (Leaf LTE)) y)
>                           -> f LT x y
>                       (Node REL_LIST (Node ELEM_REL x (Leaf GTE)) y)
>                           -> f GT x y
>                       _ -> Nothing
>         _ -> Nothing
>     where f o x y = let a = treeFromEx zero one vs x
>                         b = g o <$> treesFromCons zero one vs y
>                     in VRelChain <$> a <*> b
>           g o ~(VRelChain a bs) = (o,a):bs

The meat of the system lies in collapsing interior nodes
and removing unnecessary levels introduced for the sake of the CNF.
Originally explicit, parentheses are made implicit.
Chains of relations or concatenation are each lifted to a single level.

> treeFromEx :: Eq a => a -> a -> [a] -> ETree a -> Maybe (VEx b)
> treeFromEx zero one vs (Node _ x y)
>     | tag x == tag y && tag x == ELEM
>         = merge <$> next x <*> next y
>     | tag y == OMEGA = VOmega <$> next x
>     | tag x == OPEN
>         = case y of
>             Node CLOSE_EL a _ -> next a
>             _ -> Nothing
>     where next = treeFromEx zero one vs
>           mklist (VConcat a b) = a:b
>           mklist a = [a]
>           merge (VConcat f fs) v = VConcat f (fs ++ mklist v)
>           merge v (VConcat f fs) = VConcat v (f:fs)
>           merge f g = VConcat f [g]
> treeFromEx zero one vs (VLeaf a _)
>     | a == zero  =  Just VZero
>     | a == one   =  Just VOne
>     | otherwise  =  VVar <$> ind a vs 0
>     where ind _ [] _ = Nothing
>           ind x (y:ys) n = if x == y then Just n else ind x ys (n + 1)
> treeFromEx _ _ _ _ = Nothing


Appendix: Helpers
=================

Beyond this point are some helpful functions that are used by this module
but do not necessarily flow with its narrative.
This includes various utilities,
a mechanism for finding one / zero in a semigroup,
and a cartesian product for the CKY parser.

> splat :: [Maybe a] -> Maybe [a]
> splat = foldr (maybe (const Nothing) (fmap . (:))) (Just [])

> splatMap :: (a -> Maybe b) -> [a] -> Maybe [b]
> splatMap f = splat . map f


Streamable Cartesian Product
----------------------------

> cartesian :: [a] -> [b] -> [(a, b)]
> cartesian = curry (concat . diagonalize . uncurry basicProduct)

> diagonalize :: [[a]] -> [[a]]
> diagonalize = drop 1 . f []
>     where f crows rest
>               = heads
>                 : case rest of
>                     []   -> transpose crows'
>                     r:rs -> f (r:crows') rs
>               where ~(heads, crows') = g crows
>                     g [] = ([], [])
>                     g (x:xs) = let ~(hs, ts) = g xs
>                                in case x of
>                                     [] -> (hs, ts)
>                                     [y] -> (y : hs, ts)
>                                     (y:ys) -> (y : hs, ys : ts)

> basicProduct :: [a] -> [b] -> [[(a, b)]]
> basicProduct as bs = map (\a -> map ((,) a) bs) as
