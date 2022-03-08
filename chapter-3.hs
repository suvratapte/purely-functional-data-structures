module Chapter_3 where

{-
Leftist heaps are heap-ordered binary trees that satisfy the leftist property:
the rank of any left child is at least as large as the rank of its right
sibling. The rank of a node is defined to be the length of its right
spine (i.e., the rightmost path from the node in question to an empty node). A
simple consequence of the leftist property is that the right spine of any node
is always the shortest path to an empty node.
-}

data LeftistHeap a =
    Empty
  | Node Int a (LeftistHeap a) (LeftistHeap a)
  -- Rank, value, left heap, right heap
  deriving (Show, Eq)

rank :: LeftistHeap a -> Int
rank Empty = 0
rank (Node r _ _ _) = r

merge :: Ord a => LeftistHeap a -> LeftistHeap a -> LeftistHeap a
merge t Empty = t
merge Empty t = t
merge nx@(Node _ x xl xr) ny@(Node _ y yl yr) =
  if x < y
  then makeNode x xl $ merge xr ny
  else makeNode y yl $ merge yr nx
  where
    -- Creates a new node by looking at the ranks of the left and right nodes
    -- and swapping the left and right nodes if required; to maintain the
    -- leftist heap property
    makeNode value left right =
      let rl = rank left
          rr = rank right
      in
        if rl >= rr
        then Node (1 + rl) value left right
        else Node (1 + rr) value right left

insert :: Ord a => a -> LeftistHeap a -> LeftistHeap a
insert value t = merge t $ Node 1 value Empty Empty

findMin :: LeftistHeap a -> a
findMin Empty = error "Empty heap"
findMin (Node _ value _ _) = value

deleteMin :: Ord a => LeftistHeap a -> LeftistHeap a
deleteMin Empty = error "Empty heap"
deleteMin (Node _ _ l r) = merge l r
