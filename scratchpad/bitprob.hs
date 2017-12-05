data ProbTree = Up ProbTree | Down ProbTree | Halfway deriving (Eq, Ord, Read, Show)

fn :: Int -> ProbTree
fn 0 = Halfway
fn n | n < 0 = fn (-n)
     | n' == 0 || n' == 3 = Up (fn $ n `div` 2)
     | otherwise = Down (fn $ n `div` 2)
    where
        n' = n `mod` 4

rep :: ProbTree -> Double
rep Halfway = 0.5
rep (Up p) = 0.5 * (1 + rep p)
rep (Down p) = 0.5 * rep p

toEnd :: (ProbTree -> ProbTree) -> ProbTree -> ProbTree
toEnd f Halfway = f Halfway
toEnd f (Up p) = Up (toEnd f p)
toEnd f (Down p) = Down (toEnd f p)

add :: ProbTree -> ProbTree -> ProbTree
add Halfway Halfway = Halfway
add Halfway (Up p) = Up $ Down p
add Halfway (Down p) = Down $ Up p
add (Up p) (Up q) = Up (add p q)
add (Down p) (Down q) = Down (add p q)
add (Up p) (Down q) = case add p q of
                        Halfway -> Halfway
                        Up s -> Up $ Down s
                        Down s -> Down $ Up s
add p q = add q p

prop_dist :: Int -> Int -> Bool
prop_dist a b = rep at + rep bt == 2 * rep (at `add` bt)
    where
        at = fn a
        bt = fn b
