module Test where

data TreeT a  = Empty_ | Leaf a | Node a (TreeT a) (TreeT a) deriving (Show, Ord, Eq)

preorder :: TreeT a -> [a]
preorder Empty_ = []
preorder (Leaf a) = [a]
preorder (Node a l r) = a : (preorder l ++ preorder r)
  
inorder :: TreeT a -> [a]
inorder Empty_ = []
inorder (Leaf a) = [a]
inorder (Node a l r) = inorder l ++ [a] ++ inorder r
  
postorder :: TreeT a -> [a]
postorder Empty_ = []
postorder (Leaf a) = [a]
postorder (Node a l r) = postorder l ++ postorder r ++ [a]
