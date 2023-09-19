module BellmanFord where

import Data.Map.Strict as Map
import Data.Group -- needs `build-depends: groups` in `stratt.cabal`

data Weight = Infinity | Finite Int | NInfinity deriving Eq

instance Ord Weight where
  _ <= Infinity = True
  Infinity <= _ = False
  NInfinity <= _ = True
  _ <= NInfinity = False
  Finite n <= Finite m = n <= m

instance Semigroup Weight where
  Finite n <> Finite m = Finite (n + m)
  _ <> _ = Infinity

instance Monoid Weight where
  mempty = Finite 0

instance Group Weight where
  invert (Finite n) = Finite (- n)
  invert Infinity = NInfinity
  invert NInfinity = Infinity

type Graph a = Map a (a, Weight)
type Distances a = Map a Weight

data BFState a = BFState {
  graph :: Graph a,
  distances :: Distances a
}

-- Given some edge (from, to) of weight w,
-- if distance(from) + w < distance (t0),
-- then we've found a shorter path through (from, to).
relaxEdge :: Ord a => a -> (a, Weight) -> BFState a -> BFState a
relaxEdge from (to, weight) bfstate@(BFState {distances = dists}) =
  let newDist = dists ! from <> weight in
  if newDist < dists ! to
    then bfstate {distances = insert to newDist dists}
    else bfstate

-- Relax the distances by checking each edge.
relaxEdges :: Ord a => BFState a -> BFState a
relaxEdges bfstate = foldrWithKey' relaxEdge bfstate (graph bfstate)

-- Relax the distances |V| times (longest path is no longer than |V|).
relax :: Ord a => BFState a -> BFState a
relax bfstate = iterate relaxEdges bfstate !! size (graph bfstate)

-- Does the graph have a negative-weight cycle?
-- If there is some edge (from, to) of weight w such that distance(from) + w < distance(to),
-- then there must be a path whose weight keeps decreasing,
-- meaning that there is a negative cycle.
hasCycle :: Ord a => BFState a -> Bool
hasCycle bfstate@(BFState {distances = dists}) =
  not . Map.null $ filterWithKey (\from (to, weight) -> dists ! from <> weight < dists ! to) (graph bfstate)

bf :: Ord a => (() -> a) -> Graph a -> Maybe (Distances a)
bf mkDummy graph =
      -- 0. Create a dummy source node.
  let dummy = mkDummy ()
      -- 1. For each vertex v, add a zero-weight edge (dummy, v).
      graph' = Prelude.foldr (\from -> insert dummy (from, Finite 0)) graph (keys graph)
      -- 2. Initial distance from dummy to itself is 0 and to all others is infinite.
      dists = insert dummy (Finite 0) $ Map.map (const Infinity) graph
      -- 3. Relax the distances from infinity until shortest path weights are found.
      --    Postcondition: All distances are finite.
      bfstate@(BFState {distances = dists'}) = relax BFState {graph = graph', distances = dists}
      -- 4. Shift upwards so smallest distance is zero.
      dists'' = Map.map (<> (invert . minimum $ elems dists')) dists'
  in if hasCycle bfstate then Nothing else Just dists''