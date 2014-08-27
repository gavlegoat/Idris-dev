module Data.RoseTree

%access public
%default total

||| Multiway trees
abstract
data RoseTree : Type -> Type where
  Branch : a -> List (RoseTree a) -> RoseTree a

||| Convert a tree to a list
flatten : RoseTree a -> List a
flatten (Branch v ts) = assert_total $ v :: concatMap flatten ts

||| Gather the elements at each level of the tree
levels : RoseTree a -> List (List a)
levels (Branch v ts) = assert_total $ [v] ::
                       (foldr zipConcat [] $ map levels ts) where
  zipConcat : List (List a) -> List (List a) -> List (List a)
  zipConcat []        ys        = ys
  zipConcat xs        []        = xs
  zipConcat (x :: xs) (y :: ys) = (x ++ y) :: zipConcat xs ys

||| Create a tree from a seed and a function. Partial because the function
||| may never terminate
partial
unfoldTree : (b -> (a, List b)) -> b -> RoseTree a
unfoldTree f x = let (v, ss) = f x in Branch v $ map (unfoldTree f) ss

mapM : Monad m => (a -> m b) -> List a -> m (List b)
mapM _ []        = return []
mapM f (x :: xs) = do
  v <- f x
  vs <- mapM f xs
  return (v :: vs)

||| Create a tree from a monadic building and a seed. Partial because the
||| builder function is arbitrary and may never terminate.
partial
unfoldTreeM : Monad m => (b -> m (a, List b)) -> b -> m (RoseTree a)
unfoldTreeM f x = do
  (v, ss) <- f x
  ts <- mapM (unfoldTreeM f) ss
  return $ Branch v ts
