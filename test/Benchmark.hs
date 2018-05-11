
import Text.Regex.Symbolic.Solver as S
import Data.Aeson
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.Map as M


main :: IO ()
main = do 
  txt <- B.readFile "./test_cases.json"
  case (eitherDecode txt :: Either String [[Eqn]]) of
    { Left err -> print err
    ; Right test_cases  -> do 
      mapM_ (\test_case -> 
              let normalized = norm test_case
                  subst = solve  normalized
                  subst' = solve' normalized
              in case (M.lookup 0 subst, M.lookup 0 subst') of 
                { (Just ms, Just ms') -> 
                     let width = sum $ map (\(Const r) -> alphaWidth r) ms
                         width' = sum $ map (\(Const r) -> alphaWidth r) ms'
                     in putStrLn $ show width ++ "," ++ show width'
                ; (_,_) -> print "no init state"
                ; 
                }
            ) test_cases
    }