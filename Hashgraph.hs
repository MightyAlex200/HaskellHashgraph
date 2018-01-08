-- ｗｈｅｎ   ｉｃｏ？
import Data.Maybe
import Data.List

data Event d t i s = Event { payload :: d, parents :: (Maybe (Event d t i s), Maybe (Event d t i s)), time :: t, creator :: i, sig :: s} deriving (Show, Eq)

data Hashgraph d t i s = Hashgraph { events :: [Event d t i s], population :: Int } deriving (Show)

tupleToList :: (a, a) -> [a]
tupleToList (x, y) = [x, y]

supermajority :: (Fractional f) => Hashgraph d t i s -> f
supermajority hashgraph = 2/3 * (fromIntegral (population hashgraph))

selfParent :: Event d t i s -> Maybe (Event d t i s)
selfParent = fst . parents

otherParent :: Event d t i s -> Maybe (Event d t i s)
otherParent = snd . parents

ancestor :: (Eq d, Eq t, Eq i, Eq s) => Event d t i s -> Event d t i s -> Bool
ancestor x y
    | x == y = True
    | otherwise = any (\z -> maybe False (\z' -> ancestor z' y) z) $ tupleToList (parents x)

selfAncestor :: (Eq d, Eq t, Eq i, Eq s) => Event d t i s -> Event d t i s -> Bool
selfAncestor x y
    | x == y = True
    | otherwise = maybe False (\x' -> selfAncestor x' y) (selfParent x)

manyCreators :: (Eq i) => Hashgraph d t i s -> [Event d t i s] -> Bool
manyCreators hashgraph s =
    let s' = nub $ map (\x -> creator x) s
        n = floor (supermajority hashgraph)
    in length (take (n+1) s') > n

-- Not sure if we need this one lol
see :: (Eq d, Eq t, Eq i, Eq s) => Hashgraph d t i s -> Event d t i s -> Event d t i s -> Bool
-- see hashgraph x y = ancestor x y
see hashgraph x y =
    let e = events hashgraph
    in  ancestor x y &&
        null [() | a <- e, b <- e,
            creator y == creator a,
            creator a == creator b,
            ancestor x a,
            ancestor x b,
            not (selfAncestor a b),
            not (selfAncestor b a)
        ]

stronglySee :: (Eq d, Eq t, Eq i, Eq s) => Hashgraph d t i s -> Event d t i s -> Event d t i s -> Bool
stronglySee hashgraph x y =
    see hashgraph x y &&
    manyCreators hashgraph (filter (\z -> see hashgraph x z && see hashgraph z y) (events hashgraph))

parentRound :: (Integral n, Eq d, Eq t, Eq i, Eq s) => Hashgraph d t i s -> Event d t i s -> n
parentRound hashgraph x = max (maybe 1 (\xp -> eventRound hashgraph (xp)) (selfParent x)) (maybe 1 (\xp -> eventRound hashgraph (xp)) (otherParent x))

eventRound :: (Integral n, Eq d, Eq t, Eq i, Eq s) => Hashgraph d t i s -> Event d t i s -> n
eventRound hashgraph x = parentRound hashgraph x + (if roundInc hashgraph x then 1 else 0)

roundInc :: (Eq d, Eq t, Eq i, Eq s) => Hashgraph d t i s -> Event d t i s -> Bool
roundInc hashgraph x =
    let r = parentRound hashgraph x
        s = [y | y <- events hashgraph, stronglySee hashgraph x y, eventRound hashgraph y == r]
    in manyCreators hashgraph s

witness :: (Eq d, Eq t, Eq i, Eq s) => Hashgraph d t i s -> Event d t i s -> Bool
witness hashgraph x =
    let p = selfParent x
    in  isNothing p ||
        maybe False (\y -> eventRound hashgraph x > eventRound hashgraph y) p

diff :: (Eq d, Eq t, Eq i, Eq s, Integral n) => Hashgraph d t i s -> Event d t i s -> Event d t i s -> n
diff hashgraph x y = eventRound hashgraph x - eventRound hashgraph y

-- All of these are out of date and need to be updated, otherwise it won't compile.
-- votes :: (Integral n) => Hashgraph -> Event d h t i s -> Event d h t i s -> Bool -> n
-- fractTrue :: (Floating f) => Hashgraph -> Event d h t i s -> Event d h t i s -> f
-- decide :: Hashgraph -> Event d h t i s -> Event d h t i s -> Bool
-- copyVote :: Hashgraph -> Event d h t i s -> Event d h t i s -> Bool
-- vote :: Hashgraph -> Event d h t i s -> Event d h t i s -> Bool
-- famous :: Event d h t i s -> Bool
-- uniqueFamous :: Hashgraph -> Event d h t i s -> Bool
-- roundsDecided :: (Integral n) => Hashgraph -> n -> Bool
-- roundRecieved :: (Integral n) => Hashgraph -> Event d h t i s -> n
-- timeRecieved :: (Ord t) => Hashgraph -> Event d h t i s -> t
