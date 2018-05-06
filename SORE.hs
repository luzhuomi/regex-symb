module SORE where

import qualified Data.Map as M
import Data.Maybe (isNothing, isJust)
import Data.List (partition, sortBy)

data RE = Phi 
        | Eps          -- ^ an empty exp
        | L Char       -- ^ a literal / a character
        | Choice [RE]  -- ^ a choice exp 'r1 + r2'
        | Seq [RE]     -- ^ a pair exp '(r1,r2)'
        | Star RE      -- ^ a kleene's star exp 'r*'
          deriving ({-Show,-} Eq)

-- ^ Monomial is a term which is either form r.x or a constant r
data Monomial = NonConst RE Var
              | Const RE
          deriving (Show, Eq)
                         
-- ^ variables
type Var = String

-- ^ an equation is a variable (i.e. LHS) and a sum of all monomials (i.e. RHS)
data Eqn = Eqn { lhs::Var
               , rhs::[Monomial]
               }
         deriving (Show,Eq)
                    

instance Show RE where
  show Phi = "{}"
  show Eps = "Eps"
  show (L c) = show c
  show (Choice rs) = "(" ++ concat (interleave (map show rs) "+") ++  ")" 
  show (Seq rs) = "(" ++ concat (interleave (map show rs) ".")  ++ ")"
  show (Star r) = show r ++ "*" 


interleave [] b = []
interleave [a] b = [a]
interleave (a:as) b = a:b:(interleave as b)

-- ^ substitution, substitute the the rhs of an equation into another
type Substitution = M.Map Var [Monomial]

-- this is not needed ? we only allow arden's law to generate substitution.
toSubst :: Eqn -> Maybe Substitution
toSubst (Eqn lhs rhs) | any (\m -> isFree lhs m) rhs = Nothing
                      | otherwise = Just (M.singleton lhs rhs)

-- ^ check whether a var is free in a monomial
isFree :: Var -> Monomial -> Bool
isFree var (Const _) = False
isFree var (NonConst _ var') = var == var'

-- ^ check whether an equation is self-recursive
isSelfRecursive :: Eqn -> Bool
isSelfRecursive e = 
  let var = lhs e
      monos = rhs e
  in any (isFree var) monos

fromSubst :: Substitution -> [Eqn]
fromSubst s = map (\ (v,ms) -> Eqn v ms) $ M.toList s


-- ^ apply s1 to s2's co-domain, then union
compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = 
  let s2' = M.map (\ms -> concatMap (\m -> substM m s1) ms) s2
  in s1 `M.union` s2'


substE :: Eqn -> Substitution -> Eqn
substE e s = case M.lookup (lhs e) s of 
  { Just rhs' -> e{rhs=rhs'}
  ; Nothing -> 
       let rhs' = mergeByVars (concatMap (\m -> substM m s) (rhs e))
       in e{rhs=rhs'}
  }
-- ^ apply subst to a monomial, if the result contains variable, we apply distributivity law r.(x+y) --> r.x + r.y
substM :: Monomial -> Substitution -> [Monomial]
substM (Const r) _ = [Const r]
substM (NonConst r v) s = 
  case M.lookup v s of
    { Nothing -> [NonConst r v]
    ; Just ms -> 
         map (\m -> case m of 
                 { Const t -> Const (Seq [r,t])
                 ; NonConst t u -> NonConst (Seq [r,t]) u
                 }) ms
    }
-- ^ merge non constant monomials based on common vars    e.g. r.x + ... + t.x --> (r+t).x
mergeByVars :: [Monomial] -> [Monomial]
mergeByVars ms = 
  let (consts, nonConsts) = partition (\m -> case m of { Const _ -> True
                                                       ; _ -> False 
                                                       }) ms
      table = foldl (\t m@(NonConst r v) -> 
                      case M.lookup v t of 
                        { Nothing  -> M.insert v [r] t
                        ; Just rs -> M.update (\x -> Just (rs ++ [r])) v t
                        }) M.empty nonConsts
      nonConsts' = map (\(v,rs) -> NonConst (Choice rs) v) (M.toList table)
  in nonConsts' ++ consts

-- ^ apply arden's law                        
-- ^ arden's law is only applicable iff
--   X = c1...cn X + A  -- (1)
--  where no non-terminal appears in ci. and eps \not in ci
--  we check whether the eqn is immediate-recursive. 
--   if so, we turn (1) to an substitution X -> (c1...cn)* A 
--   otherwise, i.e. X = A  -- (2) where X does not appear in A
--      we return X -> A
--     in fact we can unify these two cases, where in the second case we treat X = A as X = \phi X + A
--     however, we don't implement this uniform treatment here.

arden :: Eqn -> Substitution 
arden e = 
  let var = lhs e
      mb_r = findMatched var (rhs e)
  in case mb_r of 
    { Nothing -> M.singleton var (rhs e)
    ; Just (r, monomials) -> 
      let monomials' = map (\m -> case m of 
                              { Const r' -> Const (Seq [Star r,r']) 
                              ; NonConst r' y -> NonConst (Seq [Star r,r']) y 
                              }) monomials
      in M.singleton var monomials'
    }
    where findMatched var monomials =  -- return the matched monomial (the prefix) and the other non matching monomials
            let (matched,others) = partition (\m -> case m of 
                                                 { Const r' -> False
                                                 ; NonConst r' y -> y == var  } ) monomials
            in case matched of 
              { [ NonConst r' y ] -> Just (r', others)
              ; _ -> Nothing
              }


solve :: [Eqn] -> Substitution
solve es = case solve1 es M.empty of 
  { (_, subst) -> subst }
                

-- ^ just solve by variable declaration order
solve1 :: [Eqn] -> Substitution -> ([Eqn], Substitution)
solve1 [] subst = ([],subst)
solve1 (e:es) subst = 
  let s' = arden e
      es' = map (\e -> substE e s') es
      subst' = compose s' subst
  in solve1 es' subst'

solve' :: [Eqn] -> Substitution
solve' es = case solve2 es M.empty of 
  { (_, subst) -> subst }


-- ^ solve by an order of DM weight function
solve2 :: [Eqn] -> Substitution -> ([Eqn], Substitution)
solve2 [] subst = ([],subst)
solve2 [e] subst = solve1 [e] subst
solve2 es subst = 
  let esWeighted       = map (\e -> (e, weight es (lhs e))) es
      esWeightedSorted = sortBy (\(e1,w1) (e2,w2) -> compare w1 w2) esWeighted
      esSorted         = map fst esWeightedSorted
  in case esSorted of 
    { (e:es') -> 
         let s' = arden e
             es'' = map (\e -> substE e s') es'
             subst' = compose s' subst
         in solve2 es'' subst'
    ; _ -> error "not possible"
    }


-- DM heuristic
-- ^ inr(Eqn,var) = { r | var' = A \in Eqn,  A = r . var + A' for some A', var != var' } 

inr :: [Eqn] -> Var -> [RE]
inr es var = concatMap (\e -> 
                         let var' = lhs e
                             monomials = rhs e
                         in if (var' == var) 
                            then [] 
                            else concatMap (\mon -> case mon of
                                               { Const r -> []
                                               ; NonConst r var'' | var'' == var -> [r]
                                                                  | otherwise    -> []
                                               }) monomials
                       ) es


-- ^ outr(Eqn,var) = { r_1 , ... , r_m } where var = r_1 . var_1 + ... + r_{m-1} . var_{m-1} + r_m + r . var \in Eqn
outr :: [Eqn] -> Var -> [RE]
outr es var = concatMap (\e -> 
                          let var' = lhs e 
                              monomials = rhs e
                          in if (var' == var)
                             then concatMap (\m -> case m of 
                                                { NonConst r var'' | var'' == var -> []
                                                                   | otherwise -> [r]
                                                ; Const r -> [r] }) monomials
                             else []
                        ) es


-- ^ loopr(Eqn,var) = r where  var = r_1 . var_1 + ... + r_{m-1} . var_{m-1} + r_m + r . var \in Eqn
loopr :: [Eqn] -> Var -> Maybe RE 
loopr es var = 
  let rs = concatMap (\e -> 
                       let var' = lhs e 
                           monomials = rhs e
                       in if (var' == var)
                          then concatMap (\m -> case m of 
                                             { NonConst r var'' | var'' == var -> [r]
                                                                | otherwise -> []
                                             ; Const r -> [] }) monomials
                          else []
                     ) es
  in case rs of { r:_ -> Just r 
                ; _   -> Nothing }

-- ^ alphabetical width of a given regular expression     
alphaWidth :: RE -> Int
alphaWidth Phi = 0
alphaWidth Eps = 0
alphaWidth (L _) = 1
alphaWidth (Choice rs) = sum (map alphaWidth rs)
alphaWidth (Seq rs) = sum (map alphaWidth rs)
alphaWidth (Star r) = alphaWidth r


-- ^ the weight function of DM heuristic
-- let m = | inr(eqn, var) | 
--     l = | outr(eqn, var) |
--     r0 = | loopr(eqn, var) |  in case there is no loop, we set r0 = phi
--     weight(var) = (m-1) * \Sigma_{r \in outr(Eqn,var)} |r| +
--                   (l-1) * \sigma_{r \in inr(Eqn,var)} |r| + 
--                   (m * l - 1) * |r0|                     
weight :: [Eqn] -> Var -> Int
weight es var = 
  let inrs = inr es var
      outrs = outr es var
      m = length inrs
      l = length outrs
      r0 = case loopr es var of 
        { Just r -> r 
        ; Nothing -> Phi }
  in (m-1)*(sum (map alphaWidth outrs)) + (l-1)*(sum (map alphaWidth inrs)) + (m * l - 1) * (alphaWidth r0)
      


{-
solv :: [Eqn] -> [Eqn]
solv es = case solv1 es M.empty of 
  { ([],s) -> map (\e -> substE e s) es
  ; _      -> es }

solv1 :: [Eqn] -> Substitution -> ([Eqn], Substitution)
solv1 [] s = ([], s)
solv1 (e:es) s = 
  let s' = case arden e of 
        { Nothing -> case toSubst e of
             { Nothing -> error "not possible, otherwise arden e will yield just ... "
             ; Just subs -> subs
             }
        ; Just subs -> subs
        }
      es' = map (\e -> substE e s') es 
      s'' = compose s' s
  in solv1 es' s''
    


solve :: [Eqn] -> [Eqn]
solve es = 
  let es' = solve1 es
  in if es' == es 
     then es
     else solve es'

solve1 :: [Eqn] -> [Eqn]
solve1 [] = []
solve1 [e] = case arden e of 
  { Nothing -> [e]
  ; Just s' -> fromSubst s'
  }
solve1 es = 
  let mb_ardened = map arden es
  in if all isNothing mb_ardened 
     then 
       -- pick one non-self recursive eqn to build a substitution and apply it
       case filter (not . isSelfRecursive) es of 
         (e:_)  -> case toSubst e of 
           { Nothing -> error "this should not happen, unless the self recursive check is wrong."
           ; Just s ->  -- apply the subs to the rest of the euqations.
             let es' = filter (\e' -> not (lhs e' == lhs e)) es
             in map (\e' -> substE e' s) es'
           }
     else 
       -- some has been reduced via arden's law
       -- replace the old one with the new one
       map (\(mb_s', e) -> case mb_s' of 
               Nothing -> e
               Just s' -> head (fromSubst s')
           ) $ zip mb_ardened es
-}

-- ^ some combinators to build equation easily
(.=.) :: Var -> [Monomial] -> Eqn
(.=.) var monos = Eqn var monos


(...) :: RE -> Var -> Monomial 
(...) r var = NonConst r var

co :: RE -> Monomial
co r = Const r




example1 :: [Eqn]
example1 = 
  [ "R2" .=. [ L 'b' ... "R1"
             , L 'c' ... "R3"
             ]
  , "R1" .=. [ L 'a' ... "R2"
             , L 'b' ... "R3"
             , co Eps
             ]
  , "R3" .=. [ L 'a' ... "R1"
             , L 'c' ... "R2"
             ]
  ]


example2 :: [Eqn]
example2 = 
  [ "R1" .=. [ L 'x' ... "R1" 
             , L 'y' ... "R2"
             , L 'z' ... "R3"
             , co Eps
             ]
  , "R2" .=. [ L 'x' ... "R1" 
             , L 'y' ... "R2"
             , L 'z' ... "R3"
             , co Eps
             ]
  , "R3" .=. [ L 'x' ... "R1" 
             , L 'y' ... "R2"
             , L 'z' ... "R3"
             , co Eps
             ]
  ]
  
  
example3 :: [Eqn]
example3 = 
  [ "R" .=. [ L 'x' ... "R", co Eps] 
  ]