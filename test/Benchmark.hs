-- cabal install aeson 
import Text.Regex.Symbolic.Solver as S
import System.Environment
import Data.Aeson
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.Map as M
import Control.Monad 
import Control.Applicative hiding (Const)
import qualified Data.Text as T
import Data.Char

instance FromJSON Eqn where
 parseJSON = withObject "eqn" $ \o -> do 
   { lhs <- o .: T.pack "lhs"
   ; rhs <- o .: T.pack "rhs"
   ; return (Eqn lhs rhs)
   }

instance FromJSON Monomial where
  parseJSON = withObject "monomial" $ \o -> do 
    { re <- o .: T.pack "re"
    ; var <- o .: T.pack "var"
    ; return (NonConst re var)
    } <|> do
    { re <- o .: T.pack "re"
    ; return (Const re)
    }
                                        
instance FromJSON RE where                                        
  parseJSON = withText "re" $ \x -> 
    let s = T.unpack x
    in if s == "eps"
       then return Eps
       else let i = read s :: Int
                ch = chr i
            in return (L ch)
               


main :: IO ()
main = do 
  args <- getArgs
  txt <- B.readFile (head args)
  case (eitherDecode txt :: Either String [[Eqn]]) of
    { Left err -> print err
    ; Right test_cases  -> do 
      mapM_ (\test_case -> 
              let normalized = norm test_case
                  subst = solve  normalized
                  subst' = solve' normalized
                  subst'' = solve'' normalized                  
              in case (M.lookup 0 subst, M.lookup 0 subst'') of 
                { (Just ms, Just ms') -> 
                     let width = sum $ map (\(Const r) -> alphaWidth r) ms
                         width' = sum $ map (\(Const r) -> alphaWidth r) ms'
                     in putStrLn $ show width ++ "," ++ show width'
                ; (_,_) -> print "no init state"
                ; 
                }
            ) test_cases
    }