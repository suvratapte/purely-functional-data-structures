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
member x (Node left value right) =
  if x < value then member x left
  else if value < x then member x right
  else True

insert :: (Ord a) => a -> Tree a -> Tree a
insert x Empty = Node Empty x Empty
insert x node@(Node left value right) =
  if x < value then Node (insert x left) value right
  else if value < x then Node left value (insert x right)
  else node

{-
Exercise 2.2

In the worst case, member performs ap- proximately 2d comparisons, where d is
the depth of the tree. Rewrite member to take no more than d + 1 comparisons by
keeping track of a candidate element that might be equal to the query
element (say, the last element for which < returned false or <= returned true)
and checking for equality only when you hit the bottom of the tree.
-}

member' :: (Ord a) => a -> Tree a -> Bool
member' x node = go x node
  where
    -- go :: (Ord a) => a -> Tree a -> Bool
    -- TODO:  Why does the above type signature not work?
    go t Empty = t == x
    go t (Node left value right) =
      if x < value
      then go t left
      -- When going to the right branch, pass the parennt value as the value to
      -- be searched for.
      else go value right

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
insertLame x tree =
  if member x tree
  then tree
  else insert x tree

-- Uses the `check` function which returns a Bool and a Tree. The Bool indicates
-- if a copy was made or not.
insertNotLame :: (Ord a) => a -> Tree a -> Tree a
insertNotLame value tree = snd $ check value tree
  where
    check v Empty = (True, Node Empty v Empty)
    check v node@(Node left x right) =
      if v < x
      then
        let (isNew, new) = check v left
        in
          useNewIfNeeded isNew node $ Node new x right
      else
        if v > x
        then
          let (isNew, new) = check v right
          in
            useNewIfNeeded isNew node $ Node left x new
        else (False, node)

    useNewIfNeeded isNew old new =
     if isNew then (True, new) else (False, old)
