
data RE = Phi 
        | Eps          -- ^ an empty exp
        | L Char       -- ^ a literal / a character
        | Choice [RE]  -- ^ a choice exp 'r1 + r2'
        | Seq [RE]     -- ^ a pair exp '(r1,r2)'
        | Star RE      -- ^ a kleene's star exp 'r*'
          deriving Show

-- ^ a monomial is either a term of form r.x or a constant r
data Monomial = Term RE Var
              | Constant RE
              deriving Show
                         
-- ^ variables
type Var = String

-- ^ equation is a sum of all monomials
data Eqn = Eqn [Monomial]




                       