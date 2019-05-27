
{-# LANGUAGE GADTs #-}

-- Vanilla implementation covering
-- 1. Regular equation solver (sans optimizations).
-- 2. DFA based operations intersection and subtraction.
-- 3. Direct methods for intersection and subtraction.
-- 4. Parser for regular equations.


import Data.List
import Data.Maybe

data RE = Let Char
        | Star RE
        | Alt [RE]
        | Seq RE RE
        | Eps
        | Phi
        deriving (Eq, Ord)


-- simplify alternatives
simpA :: RE -> RE
simpA (Alt []) = Phi
simpA (Alt [r]) = r
simpA (Alt rs) = Alt $ map simpA rs
simpA (Star r) = Star $ simpA r
simpA (Seq r s) = Seq (simpA r) (simpA s)
simpA r = r

simpFixA :: RE -> RE
simpFixA r = let r' = simpA r
             in if r == r' then r
                else simpFixA r'

instance Show RE where
   show r = show2 $ simpFixA r

show2 (Let c) = [c]
show2 (Star r) = show r ++ "*"
show2 (Alt rs) = "(" ++ foldl (\b -> \a -> b ++ " + " ++ show a) (show $ head rs) (tail rs) ++ ")"
                -- due to simp, rs is never empty
show2 (Seq r s) = "(" ++ show r ++ " . " ++ show s ++ ")"
show2 Eps = "eps"
show2 Phi = "phi"




------------------------------
-- Solving regular equations

-- Algorithm.
-- 1. Either solve an equation via Arden's Lemma or
--    substitute that equation.
-- 2. Thus, the number of equations is reduced in each step.
-- 3. In a finite number of steps, a solution is found.
--    The solution is (semantically) unique but we may obtain
--    syntatically distinct solutions depending on the order
--    in which equations are solved.

type X = Integer
type RHS = ([(RE, X)], [RE])
data E = E X RHS deriving Show
          -- Xi = ... r . X .. + s
type SOL = (X, RHS)
         -- nothing else than an equation but we choose a different representation

-- By construction:
-- 1.  r is always a plain regular expression
-- 2. X's on the rhs are distinct.
-- 3. We may encounter solutions that (temporarily) contain variables, hence,
--    they are represented as rhs.
--    This is unavoidable, consider
--     1 = x . 1 + 2 . y + eps
--     2 = y . 1 + 2 . x + eps




-- Apply Arden's Lemma on equations of the form
-- X = s . X + r1 . X1 + ... + rn . Xn + r
-- ==>
-- X = s* . r1 . X1 + ... + s* . rn . Xn + s* . r
arden :: E -> SOL
arden (E x (rhs1, rhs2)) =
     let to (re, r) = Seq
         resA = filter (\(_,y) -> x == y) rhs1
         resB = filter (\(_,y) -> x /= y) rhs1
     in case resA of
         [] -> (x, (rhs1, rhs2))
         [(s,x')] -> (x, ([ (Seq (Star s) r, y) | (r,y) <- resB ],
                          [ (Seq (Star s) r) | r <- rhs2 ])) 
         _  -> error "arden: impossible"

-- Combine by transforming  r. X + s . X to (r + s) . X
combine :: [(RE, X)] -> [(RE, X)]
combine es =  map (\xrs -> case xrs of
                                            ((_,x):_) -> (conc xrs, x)) $
              groupBy (\(_,x) -> \(_,y) -> x == y) $
              sortBy (\(_,x) -> \(_,y) ->
                                          if x < y then LT
                                          else if x > y then GT
                                                else EQ)
              es
               where
                conc xrs = Alt $ map fst xrs
                -- conc [(r,_)] = r
                -- conc ((r,_): rs) = Seq r $ conc rs                         


-- Substitution:
-- X = r1 . X1 + ... + rn . Xn + r
-- applied to
-- Y = + ... + s . X + r'
-- 1. Build s . r and add to r'
-- 2. Build s . ri . Xi and immediately normalize
--    by transforming  ... s . X + ... + r . X + ... to (s + r) . X
subst :: SOL -> E -> E
subst (x, (rhs1, rhs2)) (E y (es1, es2)) =
    let res = concat [ map (Seq s) rhs2  | (s,z) <- es1, x == z ]   -- 1.
        res2 = combine $                                            -- 2.
              (concat
               [ [ (Seq r s, y) | (r,y) <- rhs1 ]
               | (s,z) <- es1, x == z ])
              ++
              [ (s,z) | (s,z) <- es1, x /= z ]
    in E y (res2, res ++ es2)


substSol :: SOL -> SOL -> SOL
substSol sol (x,rhs) = let E _ rhs' = subst sol (E x rhs)
                       in (x, rhs')



-- Reduce the set of equations.
-- Either find via arden equation x = r and substitute that equation, or
-- pick any other equation and substitute that equation.
-- We record all (arden) equations x = r.
reduce :: ([E], [SOL]) -> ([E], [SOL])
reduce ([], sols) = ([], sols)
reduce (e:es, sols) =
    let a = arden e
        es' = map (subst a) es
    in reduce (es', a : sols)


reduceStep (e:es, sols) =
    let a = arden e
        es' = map (subst a) es
    in (es', a : sols)



solve :: [E] -> [SOL]
solve es = let ([], sols) = reduce (es, [])
               go [] = []
               go (sol:sols) = sol : (go $ map (substSol sol) sols)
           in go sols



------------------------------------
-- DFA + intersection/subtraction

-- Numbers greater than zero.
type State = Integer
type Transition = (State, Char, State)

data DFA = DFA { states :: [State],
                 start :: State,
                 transitions :: [Transition],
                 finals :: [State] } deriving Show

-- Unique mapping from pairs to number.
-- Use Cantor's pairing function, we only need injective,
-- so maybe something simpler will do, anyway ...
mkState :: State -> State -> State
mkState s1 s2 = ((s1 + s2) * (s1 + s2 + 1) `div` 2) + s2


productDFA
  :: ((State, [State]) -> (State, [State]) -> Bool)
     -> DFA -> DFA -> DFA
productDFA f d1 d2 =
        DFA { states = [ mkState s1 s2 | s1 <- states d1, s2 <- states d2],
              start = mkState (start d1) (start d2),
              transitions = [ (mkState s1 s2, x, mkState e1 e2)
                            | (s1, x, e1) <- transitions d1,
                              (s2, y, e2) <- transitions d2,
                              x == y ],
              finals = [ mkState s1 s2
                       | s1 <- states d1, s2 <- states d2,
                         f (s1, finals d1) (s2, finals d2) ]
            }

-- NOTE:
-- Only works assuming DFAs are complete!
intersectionDFA :: DFA -> DFA -> DFA
intersectionDFA d1 d2 =
    productDFA (\(s1,fs1) -> \(s2,fs2) -> elem s1 fs1 && elem s2 fs2) d1 d2


subtractionDFA :: DFA -> DFA -> DFA
subtractionDFA d1 d2 =
    productDFA (\(s1,fs1) -> \(s2,fs2) -> elem s1 fs1 && (not $ elem s2 fs2)) d1 d2



----------------------------------
-- Derivatives

sigma :: RE -> [Char]
sigma Phi = []
sigma Eps = []
sigma (Let x) = [x]
sigma (Seq r s) = nub $ (sigma r) ++ (sigma s)
sigma (Alt rs) = nub $ concat $ map sigma rs
sigma (Star r) = sigma r

nullable :: RE -> Bool
nullable Phi = False
nullable Eps = True
nullable (Let _) = False
nullable (Seq r1 r2) = (nullable r1) && (nullable r2)
nullable (Alt rs) = or $ map nullable rs
nullable (Star r) = True

isPhi :: RE -> Bool
isPhi Phi = True
isPhi Eps = False
isPhi Let{} = False
isPhi (Seq r s) = isPhi r || isPhi s
isPhi (Alt rs) = and $ map isPhi rs
isPhi Star{} = False

deriv :: RE -> Char -> RE
deriv Phi _ = Phi
deriv Eps _ = Phi
deriv (Let x) y
   | x == y    = Eps
   | otherwise = Phi
deriv (Alt rs) x = Alt $ map (\r -> deriv r x) rs
deriv (Seq r s) x
   | nullable r = Alt [Seq (deriv r x) s, deriv s x]
   | otherwise = Seq (deriv r x) s
deriv (Star r) x = Seq (deriv r x) (Star r)

-- Simplify based on the following laws.
-- Assoc + Comm.
-- r + r = r
-- eps . r = r
-- phi . r = phi
-- phi + r = r
-- SIMP: further agressive simplifications
simp :: RE -> RE
simp (Alt []) = Phi
simp (Alt [r]) = r
simp (Alt rs) = let xs = 
                         filter (not . isPhi) $ map simp $ sort rs -- SIMP
                         -- map simp $ sort rs
                    isAlt Alt{} = True
                    isAlt _     = False
                    rs1 = filter (not . isAlt) xs
                    rs2 = concat $ map (\(Alt rs) -> rs) $ filter isAlt xs
                in Alt $ nub $ rs1 ++ rs2
                -- deal with cases such as (r1 + (r2 + r3) + r4)
simp (Seq Eps r) = simp r  -- SIMP
simp (Seq Phi r) = Phi     -- SIMP
simp (Seq r s) = Seq (simp r) (simp s)
simp r = r
     -- recall deriv not applied under Kleene star

simpFix :: RE -> RE
simpFix r = let r' = simp r
            in if r == r' then r
               else simpFix r'

simpDeriv r x = simpFix $ deriv r x

desc :: [Char] -> RE -> [RE]
desc sig r =
    let go acc [] = acc
        go acc (r:rs) = let new = map (simpDeriv r) sig
                            next = filter (\r -> not $ elem r acc) new
                        in go (acc ++ next) (rs ++ next)
    in go [r] [r]



------------------------
-- RE to DFA

-- Assumption: r is not phi
reToDfa :: RE -> DFA
reToDfa r = let d = filter (not . isPhi) $ desc (sigma r) r
                sig = sigma r
                m = zip d [1..]
                get r = fromJust $ lookup r m
            in DFA { states = map get $ d,
                     start = get r,
                     transitions = [ (get r, x, get $ simpDeriv r x)
                                   | r <- d, x <- sig, not $ isPhi $ simpDeriv r x ],
                     finals = map get $ filter nullable d }

-- Yields complete DFA for any r.
-- Complete in the sense that from any state we consider all possible transitions (symbols). 
reToDfaComplete :: [Char] -> RE -> DFA
reToDfaComplete sig r =
            let d = desc sig r
                m = zip d [1..]
                get r = fromJust $ lookup r m
            in DFA { states = map get $ d,
                     start = get r,
                     transitions = [ (get r, x, get $ simpDeriv r x)
                                   | r <- d, x <- sig ],
                     finals = map get $ filter nullable d }


--------------------------
-- DFA to RE

-- dfaToRe :: DFA -> RE
dfaToRe d = let eqs = [ E s (combine [(Let x, t) | (s',x,t) <- transitions d, s' == s],
                             if elem s (finals d)
                             then [Eps]
                             else [])
                      | s <- states d ]
                sols = solve eqs
            in Alt $ snd $ fromJust $ lookup (start d) sols


----------------------
-- Direct methods

-- Thanks to agressive simplification, see SIMP,
-- can reduce the number of initial equations significantly.

directSub :: RE -> RE -> RE
directSub r s =
   let sig = nub $ sigma r ++ sigma s
       dr = desc sig r
       ds = desc sig s
       m = zip [ (r,s) | r <- dr, s <- ds ] [1..]
       get (r,s) = fromJust $ lookup (r,s) m
       eq = [ if isPhi r
              then E (get (r,s)) ([], [])
              else E (get (r,s))
                     (map (\c-> (Let c, get (simpDeriv r c, simpDeriv s c))) sig,
                      if nullable r && (not . nullable) s
                      then [Eps]
                      else [])              
            | r <- dr, s <- ds ]
       sols = solve eq                         
   in -- error $ show $ length eq -- to count number of equations
      Alt $ snd $ fromJust $ lookup (get (r,s)) sols


directIntersect :: RE -> RE -> RE
directIntersect r s =
   let sig = nub $ sigma r ++ sigma s
       dr = desc sig r
       ds = desc sig s
       m = zip [ (r,s) | r <- dr, s <- ds ] [1..]
       get (r,s) = fromJust $ lookup (r,s) m
       eq = [ if isPhi r || isPhi s
              then E (get (r,s)) ([], [])
              else E (get (r,s))
                     (map (\c-> (Let c, get (simpDeriv r c, simpDeriv s c))) sig,
                      if nullable r && nullable s
                      then [Eps]
                      else [])              
            | r <- dr, s <- ds ]
       sols = solve eq                         
   in Alt $ snd $ fromJust $ lookup (get (r,s)) sols



------------------
-- Parser where parse trees are proof terms

-- We treat r1 + r2 + r3 as r1 + (r2 + r3)

data U where
  Nil :: U
  Empty :: U
  Letter :: Char -> U
  LeftU :: U -> U
  RightU :: U -> U
  Pair :: (U,U) -> U
  List :: [U] -> U
  deriving Show


-- auxiliary functions

flatten :: U -> [Char]
flatten Nil = []
flatten Empty = []
flatten (Letter c) = [c]
flatten (LeftU u) = flatten u
flatten (RightU u) = flatten u
flatten (Pair (u1,u2)) = flatten u1 ++ flatten u2
flatten (List us) = concat $ map flatten us


mkEmptyU :: RE -> U
mkEmptyU Phi            = Nil
mkEmptyU Eps            = Empty
mkEmptyU (Let l)        = error "mkEmptyU, letter impossible"
mkEmptyU (Alt [])       = error "mkEmptyU, must be normalized"
mkEmptyU (Alt [r])      = mkEmptyU r
mkEmptyU (Alt (r:rs))
   | nullable r         = LeftU $ mkEmptyU r
   | otherwise          = RightU $ mkEmptyU $ Alt rs
mkEmptyU (Seq r1 r2)   = Pair (mkEmptyU r1, mkEmptyU r2)
mkEmptyU (Star r)      = List []


-- injD r r\l l yields
-- [[r\l] -> [[r]]
-- r\l derivatives of r wrt l
injD :: RE -> RE -> Char -> U -> U
injD (Star r) (Seq rd _) l (Pair (u, List us)) =  -- _ must be equal to r
    List $ (injD r rd l u) : us

injD (Seq r1 r2) (Alt [Seq rd1 _,  _]) l (LeftU u) = -- first _ = r2, second _ = r2\l
             let Pair (u', u'') = u
             in Pair (injD r1 rd1 l u', u'')
injD (Seq r1 r2) (Alt [_, rd2]) l (RightU u) = 
             Pair (mkEmptyU r1, injD r2 rd2 l u)
injD (Seq r1 r2) (Seq rd1 _) l (Pair (u',u'')) =   -- _ = r2
     Pair (injD r1 rd1 l u', u'')

injD r (Alt [rd]) l u = injD r rd l u
injD (Alt (r1:r2)) (Alt (rd1:rd2)) l (LeftU u) =
      LeftU $ injD r1 rd1 l u 
injD (Alt (r1:r2)) (Alt (rd1:rd2)) l (RightU u) =
      RightU $ injD (Alt r2) (Alt rd2) l u 

injD (Let l') Eps l Empty
  | l == l'   = Letter l
  | otherwise = error "impossible" 
injD r1 r2 l u = 
  error $ show r1 ++ "\n" ++ show r2 ++ "\n" ++ show l ++ "\n" ++ show u


posix2 (r,m) [] 
   | nullable r = m $ mkEmptyU r
   | otherwise = error "no match"
posix2 (r,m) (l:ls) = 
    let r' = deriv r l
    in posix2 (r', m . (injD r r' l)) ls


-- Claim: Yields the POSIX parse tree.
posix :: RE -> [Char] -> U
posix r w = posix2 (r,id) w



-- examples
----------------

x = Let 'x'
y = Let 'y'
z = Let 'z'

r_xy = Seq x y

e1 = E 1 ([], [Eps])

e1b = E 1 ([], [Eps, x, r_xy])

-- R = R . x + xy
e2 = E 1 ([(x,1)], [r_xy])

-- 1 = x . 2 + z
-- 2 = y . 1 + x
e3a = E 1 ([(x,2)], [z])
e3b = E 2 ([(y,1)], [x])

-- 1 = x . 1 + y . 2 + eps
-- 2 = y .1 + x . 2 + eps

e4a = E 1 ([(x,1), (y,2)], [Eps])
e4b = E 2 ([(y,1), (x,2)], [Eps])

r0 = Star x

r1 = Star $ Alt [x,y]

r2 = Seq r1 r1

r3 = Seq r1 (Star x)

r4 = Seq x y

r5 = Seq x (Star x)

r5b = Seq (Star x) x

r6 = Seq (Star x) (Star x)

r6b = Seq (Star x) (Star y)

-- x* . x . x* . x*
r7 = Seq r5b r6
