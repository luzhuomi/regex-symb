module SORE where

import qualified Data.Map as M

data RE = Phi 
        | Eps          -- ^ an empty exp
        | L Char       -- ^ a literal / a character
        | Choice [RE]  -- ^ a choice exp 'r1 + r2'
        | Seq [RE]     -- ^ a pair exp '(r1,r2)'
        | Star RE      -- ^ a kleene's star exp 'r*'
          deriving Show

-- ^ Monomial is a term which is either form r.x or a constant r
data Monomial = NonConst RE Var
              | Const RE
          deriving Show
                         
-- ^ variables
type Var = String

-- ^ an equation is a variable (i.e. LHS) and a sum of all monomials (i.e. RHS)
data Eqn = Eqn { lhs::Var
               , rhs::[Monomial]
               }
         deriving Show
                    


-- ^ substitution, substitute the the rhs of an equation into another
type Substition = M.Map Var [Monomial]

toSubst :: Eqn -> Maybe Substition
toSubst (Eqn lhs rhs) | any (\m -> isFree lhs m) rhs = Nothing
                      | otherwise = Just (M.singleton lhs rhs)

-- ^ check whether a var is free in a monomial
isFree :: Var -> Monomial -> Bool
isFree var (Const _) = False
isFree var (NonConst _ var') = var == var'

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
  let (consts, nonConsts) = span (\m -> case m of { Const _ -> True
                                                  ; _ -> False 
                                                  }) ms
      table = foldl (\t m@(NonConst r v) -> 
                      case M.lookup v t of 
                        { Nothing  -> M.insert v [r] t
                        ; Just rs -> M.update (\x -> Just (rs ++ [r])) v t
                        }) M.empty ms
      nonConsts' = map (\(v,rs) -> NonConst (Choice rs) v) (M.toList table)
  in nonConsts' ++ consts

-- ^ apply arden's law                        
arden :: Eqn -> Maybe Eqn 
arden e = Just e 

