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
  deriving (Eq, Show)

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

---

{- Binomial Heaps -}

data BinomialTree a =
  BinomTNode Int a [BinomialTree a]
  -- Rank value children
  -- children are stored in decreasing order of rank
  deriving (Eq, Show)

-- This function should be used to link two trees of the same rank.
-- One might want to add a check for that and raise an error if that is not the
-- case.
link :: Ord a => BinomialTree a -> BinomialTree a -> BinomialTree a
link node@(BinomTNode rank value children) node'@(BinomTNode _ value' children')
  | value < value' = BinomTNode (rank + 1) value $ node' : children
  | otherwise = BinomTNode (rank + 1) value' $ node : children'

bRank :: BinomialTree a -> Int
bRank (BinomTNode rank _ _) = rank

bElem :: BinomialTree a -> a
bElem (BinomTNode _ a _) = a

bChildren :: BinomialTree a -> [BinomialTree a]
bChildren (BinomTNode _ _ children) = children

type BinomialHeap a = [BinomialTree a]

insertBinomTreeInBinomHeap :: Ord a
  => BinomialTree a -> BinomialHeap a -> BinomialHeap a
insertBinomTreeInBinomHeap tree [] = [tree]
insertBinomTreeInBinomHeap
  tree@(BinomTNode rank value children)
  heap@( tree'@(BinomTNode rank' value' children') : hs)
  | rank < rank' = tree : heap
  | rank == rank' = insertBinomTreeInBinomHeap (link tree tree') hs
  -- TODO: Do we expect the below case?
  -- rank > rank' otherwise = tree' : insertBinomTree tree hs

insertElemBinomHeap :: Ord a => a -> BinomialHeap a -> BinomialHeap a
insertElemBinomHeap elem heap =
  insertBinomTreeInBinomHeap (BinomTNode 0 elem []) heap

mergeBinomHeaps :: Ord a => BinomialHeap a -> BinomialHeap a -> BinomialHeap a
mergeBinomHeaps h [] = h
mergeBinomHeaps [] h = h
mergeBinomHeaps heap@(t : ts) heap'@(t' : ts')
  | bRank t < bRank t' = t : mergeBinomHeaps ts heap'
  | bRank t > bRank t' = t' : mergeBinomHeaps heap ts'
  | otherwise = insertBinomTreeInBinomHeap (link t t') $ mergeBinomHeaps ts ts'

removeMinTreeFromHeap :: Ord a => BinomialHeap a -> (BinomialTree a, BinomialHeap a)
removeMinTreeFromHeap [t] = (t, [])
removeMinTreeFromHeap (t : ts) =
  let (t', ts') = removeMinTreeFromHeap ts
  in
    if bElem t < bElem t'
    then (t, ts)
    else (t', t : ts')

findMinimumFromHeap :: Ord a => BinomialHeap a -> a
findMinimumFromHeap heap =
  let (t, _) = removeMinTreeFromHeap heap
  in bElem t

deleteMinimumFromHeap :: Ord a => BinomialHeap a -> BinomialHeap a
deleteMinimumFromHeap heap =
  let (t, heap') = removeMinTreeFromHeap heap
  in
    -- Reversing is very important here since children are stored in decreasing
    -- order and binomial heaps are supposed to be in increasing order.
    mergeBinomHeaps (reverse (bChildren t)) heap'

{- Red Black Trees -}

data Color = R | B
  deriving (Eq, Show)

data RBTree a =
    E
  | RBTNode Color (RBTree a) a (RBTree a)
  deriving (Eq, Show)

memberRBT :: Ord a => a -> RBTree a -> Bool
memberRBT x E = False
memberRBT x (RBTNode _ left value right)
  | x < value = memberRBT x left
  | x > value = memberRBT x right
  | otherwise = True

-- Balances Black-Red-Red paths.
balanceRBT :: RBTree a -> RBTree a

-- Left-Left path
balanceRBT
  (RBTNode B (RBTNode R (RBTNode R a x b) y c) z d) =
    RBTNode R (RBTNode B a x b) y (RBTNode B c z d)

-- Left-Right path
balanceRBT
  (RBTNode B (RBTNode R a x (RBTNode R b y c)) z d) =
    RBTNode R (RBTNode B a x b) y (RBTNode B c z d)

-- Right-Left path
balanceRBT
  (RBTNode B a x (RBTNode R (RBTNode R b y c) z d)) =
    RBTNode R (RBTNode B a x b) y (RBTNode B c z d)

-- Right-Right path
balanceRBT
  (RBTNode B a x (RBTNode R b y (RBTNode R c z d))) =
    RBTNode R (RBTNode B a x b) y (RBTNode B c z d)

balanceRBT somethingElse = somethingElse

insertRBT :: Ord a => a -> RBTree a -> RBTree a
insertRBT x s =
  let (RBTNode _ l v r) = go s -- We are sure that this will never return E.
  in
    RBTNode B l v r
  where
   go E = RBTNode R E x E
   go node@(RBTNode color left value right)
     | x < value = balanceRBT $ RBTNode color (go left) value right
     | x > value = balanceRBT $ RBTNode color left value (go right)
     | otherwise = node
