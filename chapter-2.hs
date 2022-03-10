module Chapter_2 where

{-
Exercise 2.1

Write a function suffixes of type a list -> a list list that takes a list xs and
returns a list of all the suffixes of xs in decreasing order of length. For
example,

suffixes [1,2,3,4] = [[1,2,3,4], [2,3,4], [3,4], [4], []]

Show that the resulting list of suffixes can be generated in O(n) time and rep-
resented in O(n) space.
-}


suffixes :: [a] -> [[a]]
suffixes [] = [[]]
suffixes xs = xs : suffixes (tail xs)

{-
1. The suffixes are generated in O(n) since it takes only one iteration to
produce the result.

2. The suffixes are generated in O(n) space because there is structural sharing
here. Every iteration will produce a new pointer pointing to the next first
element in the list.
-}

-- Binary Search Trees

data Tree a =
    Empty
  | Node (Tree a) a (Tree a)
  deriving (Show)

-- TODO: Deriving `Eq` is possible here. Figure out how it works.

member :: (Ord a) => a -> Tree a -> Bool
member _ Empty = False
member x (Node left value right)
  | x < value = member x left
  | x > value = member x right
  | otherwise = True

insert :: (Ord a) => a -> Tree a -> Tree a
insert x Empty = Node Empty x Empty
insert x node@(Node left value right)
  | x < value = Node (insert x left) value right
  | x > value = Node left value $ insert x right
  | otherwise = node

{-
Exercise 2.2

In the worst case, member performs ap- proximately 2d comparisons, where d is
the depth of the tree. Rewrite member to take no more than d + 1 comparisons by
keeping track of a candidate element that might be equal to the query
element (say, the last element for which < returned false or <= returned true)
and checking for equality only when you hit the bottom of the tree.
-}

{-
Algorithm:

search: Element to be searched for.
carry: Intermediate element used in the algorithm.
value: Value of the node being checked currently.

1. Check if `search < value`.

1a. If it is, we know surely that `search \= value`. So we do not need to
consider `value`. So go to the left tree with `carry`.

1b. If it is not, it is possible that `search == value`, so go to the right tree
and pass `value` as `carry`.

2. When reach `Empty`, check if `carry == search` and return the result.

-}

member' :: (Ord a) => a -> Tree a -> Bool
member' search node = go search node
  where
    -- go :: (Ord a) => a -> Tree a -> Bool
    -- TODO:  Why does the above type signature not work?
    go carry Empty = carry == search
    go carry (Node left value right)
      | search < value = go carry left
      | otherwise = go value right

{-
Exercise 2.3

Inserting an existing element into a binary search tree copies the entire search --
path even though the copied nodes are indistinguishable from the --
originals. Rewrite insert using exceptions to avoid this copying. Establish only --
one handler per insertion rather than one handler per iteration. --
-}

-- One shortcut implementation would be to just check membership before
-- inserting.
-- This implementation is simple but it will have a higher time complexity.
insertLame :: (Ord a) => a -> Tree a -> Tree a
insertLame x tree
  | member x tree = tree
  | otherwise     = insert x tree

-- Uses the `check` function which returns a Bool and a Tree. The Bool indicates
-- if a copy was made or not.
insertNotLame :: (Ord a) => a -> Tree a -> Tree a
insertNotLame value tree = snd $ check value tree
  where
    check ::  (Ord a) => a -> Tree a -> (Bool, Tree a)
    check v Empty = (True, Node Empty v Empty)
    check v node@(Node left x right)
      | v < x =
        let (isNew, new) = check v left
        in
          useNewIfNeeded isNew node $ Node new x right
      | v > x =
        let (isNew, new) = check v right
        in
          useNewIfNeeded isNew node $ Node left x new
      | otherwise = (False, node)

    useNewIfNeeded isNew old new
      | isNew = (True, new)
      | otherwise = (False, old)

