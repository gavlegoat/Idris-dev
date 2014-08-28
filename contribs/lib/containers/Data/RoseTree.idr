module Data.RoseTree

%access public
%default total

||| Multiway trees
abstract
data RoseTree : Type -> Type where
  Branch : a -> List (RoseTree a) -> RoseTree a

instance Eq a => Eq (RoseTree a) where
  (Branch x xs) == (Branch y ys) = assert_total $ x == y &&
                                   length xs == length ys && equal' xs ys where
    equal' : List (RoseTree a) -> List (RoseTree a) -> Bool
    equal' []        []        = True
    equal' []        _         = False
    equal' _         []        = False
    equal' (x :: xs) (y :: ys) = x == y && equal' xs ys

instance Functor RoseTree where
  map f (Branch v ts) = Branch (f v) $ map (map f) ts

instance Applicative RoseTree where
  pure x = Branch x []
  (Branch f fs) <$> (Branch v vs) = assert_total $ Branch (f v) $
                          map ((pure f) <$>) vs ++ map (<$> (Branch v vs)) fs

instance Monad RoseTree where
  (Branch v vs) >>= f = assert_total $ let Branch v' vs' = f v
                        in Branch v' (vs' ++ map (>>= f) vs)

instance Foldable RoseTree where
  foldr f z (Branch v ts) = assert_total $ foldr (flip $ foldr f) (f v z) ts

instance Traversable RoseTree where
  traverse f (Branch v ts) = assert_total $ pure Branch <$> f v <$>
                                            traverse (traverse f) ts

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

||| Create a tree from a seed and a function. Partial because the function is
||| arbitrary and may never terminate
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
