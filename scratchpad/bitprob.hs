data ProbPath = Up ProbPath | Down ProbPath | Halfway deriving (Eq, Ord, Read, Show)

fn :: Int -> ProbPath
fn 0 = Halfway
fn n | n < 0 = fn (-n)
     | n' == 0 || n' == 3 = Up (fn $ n `div` 2)
     | otherwise = Down (fn $ n `div` 2)
    where
        n' = n `mod` 4

rep :: ProbPath -> Double
rep Halfway = 0.5
rep (Up p) = 0.5 * (1 + rep p)
rep (Down p) = 0.5 * rep p

toEnd :: (ProbPath -> ProbPath) -> ProbPath -> ProbPath
toEnd f Halfway = f Halfway
toEnd f (Up p) = Up (toEnd f p)
toEnd f (Down p) = Down (toEnd f p)

avg :: ProbPath -> ProbPath -> ProbPath
avg Halfway Halfway = Halfway
avg Halfway (Up p) = Up $ Down p
avg Halfway (Down p) = Down $ Up p
avg (Up p) (Up q) = Up (avg p q)
avg (Down p) (Down q) = Down (avg p q)
avg (Up p) (Down q) = case avg p q of
                        Halfway -> Halfway
                        Up s -> Up $ Down s
                        Down s -> Down $ Up s
avg p q = avg q p

mul :: ProbPath -> ProbPath -> ProbPath
mul Halfway q         = Down q
mul p Halfway         = Down p
mul (Down p) (Down q) = Down $ Down $ mul p q
mul (Down p) (Up q)   = Down $ p `avg` mul p q
mul (Up p) (Down q)   = Down $ q `avg` mul p q
mul (Up p) (Up q)     = avg p q `avg` Up (mul p q)

neg :: ProbPath -> ProbPath
neg (Down p) = Up (neg p)
neg (Up p) = Down (neg p)
neg Halfway = Halfway

prop_avg_dist :: Int -> Int -> Bool
prop_avg_dist a b = rep at + rep bt == 2 * rep (at `avg` bt)
    where
        at = fn a
        bt = fn b

prop_mul_dist :: Int -> Int -> Bool
prop_mul_dist a b = rep at * rep bt == rep (at `mul` bt)
    where
        at = fn a
        bt = fn b

prop_neg_dist :: Int -> Bool
prop_neg_dist a = rep at + rep (neg at) == 1
    where at = fn a
