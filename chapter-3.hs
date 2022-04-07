module Chapter_3 where

{-
Leftist heaps are heap-ordered binary trees that satisfy the leftist property:
the rank of any left child is at least as large as the rank of its right
sibling. The rank of a node is defined to be the length of its right
spine (i.e., the rightmost path from the node in question to an empty node). A
simple consequence of the leftist property is that the right spine of any node
is always the shortest path to an empty node.
-}

{-
Exercise 3.1

Prove that the right spine of a leftist heap of size n contains at most
floor (log(n +1)) elements.

(All logarithms in this book are base 2 unless otherwiseindicated.)
-}

{-
Let's figure out what's the minimum size of a leftist heap of rank n.

For any parent, we know these two things:

1. Rank (parent) = Rank (right child) + 1
2. Rank (left child) >= Rank (right child)

Since we are figuring out the "minimum" size, we can change the ">=" to "=" in
the second point above. So:

1. Rank (parent) = Rank (right child) + 1
2. Rank (left child) = Rank (right child)

With this, we can see that minimum size of leftist heap of rank n is:

2^n - 1

If we less nodes than 2^n - 1, the second property above stops holding true or
in case where the right most leaf node is removed, the rank does not remain n
anymore.

So the size, s, of a leftist heap with rank n has to be greater than or equal to
its minimum possible size (2^n - 1):

s >= 2^n - 1

s + 1 >= 2^n

log (s + 1) >= s             -- Log to the base 2

And since size, s, has to be an integer,

floor (log (s + 1)) >= s

-}

data LeftistHeap a =
    Empty
  | Node Int a (LeftistHeap a) (LeftistHeap a)
  -- Rank, value, left heap, right heap
  deriving (Eq, Show)

rank :: LeftistHeap a -> Int
rank Empty = 0
rank (Node r _ _ _) = r

-- Creates a new node by looking at the ranks of the left and right nodes
-- and swapping the left and right nodes if required; to maintain the
-- leftist heap property
makeNode :: a -> LeftistHeap a -> LeftistHeap a -> LeftistHeap a
makeNode value left right
  | rank left >= rank right = Node (1 + rank right) value left right
  | otherwise = Node (1 + rank left) value right left

merge :: Ord a => LeftistHeap a -> LeftistHeap a -> LeftistHeap a
merge t Empty = t
merge Empty t = t
merge nx@(Node _ x xl xr) ny@(Node _ y yl yr)
  | x < y = makeNode x xl $ merge xr ny
  | otherwise = makeNode y yl $ merge nx yr

insert :: Ord a => a -> LeftistHeap a -> LeftistHeap a
insert value t = merge t $ Node 1 value Empty Empty

{-
Exercise 3.2

Define insert directly rather than via a call to merge.
-}

insert' :: Ord a => a -> LeftistHeap a -> LeftistHeap a
insert' x Empty = Node 1 x Empty Empty
insert' x node@(Node r value left right)
  | x < value = Node (r + 1) x node Empty
  | otherwise = makeNode value left $ insert' x right

{-
Exercise 3.3

Implement a function fromList of type list a -> Heap a that produces a leftist
heap from an unordered list of elements by first converting each element into a
singleton heap and then merging the heaps until only one heap remains. Instead
of merging the heaps in one right-to-left or left-to-right pass using foldr or
foldl, merge the heaps in "ceil (log (n))" passes, where each pass merges
adjacent pairs of heaps. Show that fromList takes only O(n) time.
-}

heapFromList :: Ord a => [a] -> LeftistHeap a
heapFromList as = head . go $ map (`insert` Empty) as
  where
    go :: Ord a => [LeftistHeap a] -> [LeftistHeap a]
    go [] = []
    go [a] = [a]
    go (a : b : bs) = go (merge a b : go bs)

findMin :: LeftistHeap a -> a
findMin Empty = error "Empty heap"
findMin (Node _ value _ _) = value

deleteMin :: Ord a => LeftistHeap a -> LeftistHeap a
deleteMin Empty = error "Empty heap"
deleteMin (Node _ _ l r) = merge l r

{-
Exercise 3.4

(Cho and Sahni [CS96]) Weight-biased leftist heaps are an alternative to leftist
heaps that replace the leftist property with the weight-biased leftist property:
the size of any left child is at least as large as the size of its right
sibling.

(a) Prove that the right spine of a weight-biased leftist heap contains at most
floor ( log (n + 1) ) elements.

(b) Modify the implementation to obtain weight-biased leftist heaps.

(c) Currently, merge operates in two passes: a top-down pass consisting of calls
to merge, and a bottom-up pass consisting of calls to the helper function
makeT. Modify merge for weight-biased leftist heaps to operate in a single,
top-down pass.

(d) What advantages would the top-down version of merge have in a lazy
environment? In a concurrent environment?
-}

data WBLeftistHeap a =
    EmptyWb
  | NodeWb Int a (WBLeftistHeap a) (WBLeftistHeap a)
  -- Size, value, left heap, right heap
  deriving (Eq, Show)

size :: WBLeftistHeap a -> Int
size EmptyWb = 0
size (NodeWb r _ _ _) = r

-- Creates a new node by looking at the ranks of the left and right nodes
-- and swapping the left and right nodes if required; to maintain the
-- leftist heap property
makeNodeWb :: a -> WBLeftistHeap a -> WBLeftistHeap a -> WBLeftistHeap a
makeNodeWb value left right
  | size left >= size right = NodeWb (1 + size left + size right) value left right
  | otherwise = NodeWb (1 + size left + size right) value right left

mergeWb :: Ord a => WBLeftistHeap a -> WBLeftistHeap a -> WBLeftistHeap a
mergeWb t EmptyWb = t
mergeWb EmptyWb t = t
mergeWb nx@(NodeWb _ x xl xr) ny@(NodeWb _ y yl yr)
  | x < y = makeNodeWb x xl $ mergeWb xr ny
  | otherwise = makeNodeWb y yl $ mergeWb nx yr

insertWb :: Ord a => a -> WBLeftistHeap a -> WBLeftistHeap a
insertWb value t = mergeWb t $ NodeWb 1 value EmptyWb EmptyWb

findMinWb :: WBLeftistHeap a -> a
findMinWb EmptyWb = error "Empty heap"
findMinWb (NodeWb _ value _ _) = value

deleteMinWb :: Ord a => WBLeftistHeap a -> WBLeftistHeap a
deleteMinWb EmptyWb = error "Empty heap"
deleteMinWb (NodeWb _ _ l r) = mergeWb l r

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

{- Red-Black Trees -}

{-

Red-Black trees are BSTs where each node is colored either red or black.

Red-Black trees have the following invariants:
Invariant 1. No red node has a red child.
Invariant 2. Every path from the root to an empty node contains the same
number of black nodes.

Taken together, these two invariants guarantee that the longest possible path in
a red-black tree, one with alternating black and red nodes, is no more than
twice as long as the shortest possible path, one with black nodes only.

-}

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
