-- ｗｈｅｎ   ｉｃｏ？
import Data.Maybe
import Data.List
import Data.Ix

data Event d t i s = Event { payload :: d, parents :: (Maybe (Event d t i s), Maybe (Event d t i s)), time :: t, creator :: i, sig :: s} deriving (Show, Eq)

data Hashgraph d t i s = Hashgraph { events :: [Event d t i s], population :: Int } deriving (Show)

median xs = (sort xs) !! ((length xs) `div` 2)

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
    maybe True (\y -> eventRound hashgraph x > eventRound hashgraph y) (selfParent x)

diff :: (Eq d, Eq t, Eq i, Eq s, Integral n) => Hashgraph d t i s -> Event d t i s -> Event d t i s -> n
diff hashgraph x y = eventRound hashgraph x - eventRound hashgraph y

votes :: (Eq d, Eq t, Eq i, Eq s) => Hashgraph d t i s -> Event d t i s -> Event d t i s -> Bool -> Int
votes hashgraph x y v =
    length [ z | z <- events hashgraph,
        diff hashgraph x z == 1,
        witness hashgraph z,
        stronglySee hashgraph x z,
        vote hashgraph z y == v
    ]

fractTrue :: (Eq d, Eq t, Eq i, Eq s, Floating f) => Hashgraph d t i s -> Event d t i s -> Event d t i s -> f
fractTrue hashgraph x y = (fromIntegral (votes hashgraph x y True))/(fromIntegral (votes hashgraph x y True + votes hashgraph x y False))

decide :: (Eq d, Eq t, Eq i, Eq s) => Hashgraph d t i s -> Event d t i s -> Event d t i s -> Bool
-- (selfParent(x) 6 = ∅ ∧ decide(selfParent(x), y)) ∨(∧ witness(x) ∧ witness(y) ∧ diff(x, y) > 1 ∧ (diff(x, y) mod c > 0) ∧ (∃v ∈ B, votes(x, y, v) > (2n/3) )))
decide hashgraph x y =
    maybe False (\x' ->
        decide hashgraph x' y ||
        (
            witness hashgraph x &&
            witness hashgraph y &&
            diff hashgraph x y > 1 &&
            ((diff hashgraph x y) `mod` 10) > 0 &&
            (
                (fromIntegral (votes hashgraph x y False)) > (supermajority hashgraph) ||
                (fromIntegral (votes hashgraph x y True)) > (supermajority hashgraph)
            )
        )
    ) (selfParent x)

copyVote :: (Eq d, Eq t, Eq i, Eq s) => Hashgraph d t i s -> Event d t i s -> Event d t i s -> Bool
copyVote hashgraph x y =
    maybe (not (witness hashgraph x)) (\x' -> decide hashgraph x' y) (selfParent x)

vote :: (Eq d, Eq t, Eq i, Eq s) => Hashgraph d t i s -> Event d t i s -> Event d t i s -> Bool
vote hashgraph x y
    | not (witness hashgraph x) = vote hashgraph (fromJust (selfParent x)) y
    | witness hashgraph x &&
      (((diff hashgraph x y) `mod` 10) == 0) &&
      fractTrue hashgraph x y >= 1/3 &&
      fractTrue hashgraph x y <= 2/3 = True -- THIS IS SUPPOSED TO BE A COIN ROUND (but hashing is too much work rn lol)
    | otherwise = fractTrue hashgraph x y >= (1/2)

famous :: (Eq d, Eq t, Eq i, Eq s) => Hashgraph d t i s -> Event d t i s -> Bool
famous hashgraph x =
    not (null (filter (\y -> decide hashgraph y x && vote hashgraph y x) (events hashgraph)))

uniqueFamous :: (Eq d, Eq t, Eq i, Eq s) => Hashgraph d t i s -> Event d t i s -> Bool
uniqueFamous hashgraph x =
    famous hashgraph x &&
    null [y | y <- events hashgraph, x /= y, creator x == creator y, eventRound hashgraph x == eventRound hashgraph y, famous hashgraph y]

roundsDecided :: (Eq d, Eq t, Eq i, Eq s, Integral n) => Hashgraph d t i s -> n -> Bool
roundsDecided hashgraph r =
    all (\x -> eventRound hashgraph x <= r && witness hashgraph x) (events hashgraph)

roundReceived :: (Eq d, Eq t, Eq i, Eq s, Integral n) => Hashgraph d t i s -> Event d t i s -> n
roundReceived hashgraph x =
    head [r | r <- [1..], roundsDecided hashgraph r, all (\y -> eventRound hashgraph y == r && uniqueFamous hashgraph y) (events hashgraph)]

timeReceived :: (Eq d, Eq t, Eq i, Eq s, Ord t) => Hashgraph d t i s -> Event d t i s -> t
timeReceived hashgraph x =
    median [time y | y <- events hashgraph, 
        ancestor y x, 
        not (null ([z | z <- events hashgraph, 
            eventRound hashgraph z == roundReceived hashgraph x, 
            uniqueFamous hashgraph z, 
            selfAncestor z y
        ])),
        null ([w | w <- events hashgraph,
            selfAncestor y w,
            ancestor w x
        ])
    ]
