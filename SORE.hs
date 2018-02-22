module SORE where

import qualified Data.Map as M
import Data.Maybe (isNothing, isJust)
import Data.List (partition)

data RE = Phi 
        | Eps          -- ^ an empty exp
        | L Char       -- ^ a literal / a character
        | Choice [RE]  -- ^ a choice exp 'r1 + r2'
        | Seq [RE]     -- ^ a pair exp '(r1,r2)'
        | Star RE      -- ^ a kleene's star exp 'r*'
          deriving (Show, Eq)

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
                    


-- ^ substitution, substitute the the rhs of an equation into another
type Substition = M.Map Var [Monomial]

toSubst :: Eqn -> Maybe Substition
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

substE :: Eqn -> Substition -> Eqn
substE e s = if (lhs e) `M.member` s  
             then e
             else 
               let rhs' = mergeByVars (concatMap (\m -> substM m s) (rhs e))
               in e{rhs=rhs'}
-- ^ apply subst to a monomial, if the result contains variable, we apply distributivity law r.(x+y) --> r.x + r.y
substM :: Monomial -> Substition -> [Monomial]
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
--  1. X = c1...cn X + A
--  where no non-terminal appears in ci. and eps \not in ci

arden :: Eqn -> Maybe Eqn 
arden e = 
  let var = lhs e
      mb_r = findMatched var (rhs e)
  in case mb_r of 
    { Nothing -> Nothing
    ; Just (r, monomials) -> 
      let monomials' = map (\m -> case m of 
                              { Const r' -> Const (Seq [Star r,r']) 
                              ; NonConst r' y -> NonConst (Seq [Star r,r']) y 
                              }) monomials
      in Just $ e{rhs=monomials'}
    }
    where findMatched var monomials =  -- return the matched monomial (the prefix) and the other non matching monomials
            let (matched,others) = partition (\m -> case m of 
                                                 { Const r' -> False
                                                 ; NonConst r' y -> y == var  } ) monomials
            in case matched of 
              { [ NonConst r' y ] -> Just (r', others)
              ; _ -> Nothing
              }


solve :: [Eqn] -> [Eqn]
solve es = 
  let es' = go es
  in if es' == es 
     then es
     else go es'
       where 
         go :: [Eqn] -> [Eqn]
         go es = 
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
                map (\(mb_e', e) -> case mb_e' of 
                        Nothing -> e
                        Just e' -> e' 
                    ) $ zip mb_ardened es

-- ^ some combinators to build equation easily
(.=.) :: Var -> [Monomial] -> Eqn
(.=.) var monos = Eqn var monos


(...) :: RE -> Var -> Monomial 
(...) r var = NonConst r var

co :: RE -> Monomial
co r = Const r


example1 :: [Eqn]
example1 = 
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
  
  
  