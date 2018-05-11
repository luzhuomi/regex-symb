module Check where

import SORE
-- import qualified Data.Set as S
import Data.List 
-- ^ check for containment among regular expressions

contain :: RE -> RE -> Bool
contain r1 r2 = containCoInd [] [r1] [r2]


containCoInd :: [([RE],[RE])] -> [RE] -> [RE] -> Bool
containCoInd ctxt rs1 rs2 
  | any posEps rs1 && all (not . posEps) rs2 = False
  | (rs1,rs2) `elem` ctxt = True
  | otherwise = let ls = nub $ concatMap sigma (rs1 ++ rs2)
                    ctxt' = (rs1,rs2):ctxt
                in all (\x -> x) $ map (\l -> 
                                         let rs1' = nub $ concatMap (\r -> pderiv r l) rs1
                                             rs2' = nub $ concatMap (\r -> pderiv r l) rs2
                                         in containCoInd ctxt' rs1' rs2' ) ls


pderiv :: RE -> Char -> [RE]   
pderiv r l = let pds = pdSub r l 
             in nub (map simp pds)
                
pdSub :: RE -> Char -> [RE]
pdSub Phi l = []
pdSub Eps l = []
pdSub (L l') l 
  | l == l' = [Eps]
  | otherwise = []
pdSub (Choice rs) l = concatMap (\r -> pdSub r l) rs                
pdSub (Star r) l = 
  [ Seq [r', Star r] | r' <- pdSub r l ]
pdSub (Seq [r]) l = pdSub r l                
pdSub (Seq []) l = []
pdSub (Seq (r1:rs)) l
  | posEps r1 = 
    let s = pdSub r1 l
        t = pdSub (Seq rs) l
    in [ (Seq (r1':rs)) | r1' <- s ] ++ t
  | otherwise = 
      let s = pdSub r1 l
      in [ (Seq (r1':rs)) | r1' <- s ] 

isEps :: RE -> Bool
isEps Eps = True
isEps _ = False

posEps :: RE -> Bool
posEps Eps = True
posEps Phi = False
posEps (L _) = False
posEps (Star _) = True
posEps (Seq rs) = all posEps rs
posEps (Choice rs) = any posEps rs


simp :: RE -> RE
simp (L l) = L l
simp (Seq rs) = 
  let rs' = filter (not . isEps) $ map simp rs
  in case rs' of
    []  -> Eps
    [r] -> r
    _   -> Seq rs'
simp (Choice rs) = 
  let rs' = map simp rs
      nonEps = filter (not . isEps) rs'
      eps = filter isEps rs'
  in case eps of 
    { _:_ -> case nonEps of 
         { [] -> Eps
         ; [r] -> Choice [Eps,r]
         ; _   -> Choice (Eps:nonEps)
         }
    ; [] -> case nonEps of 
         { [] -> Phi
         ; [r] -> r
         ; _ -> Choice nonEps
         }
    }
simp (Star r) = Star (simp r)     
simp Eps = Eps
simp Phi = Phi


sigma :: RE -> [Char]
sigma r = nub (sigmaSub r)

sigmaSub :: RE -> [Char]
sigmaSub (L l) = [l]
sigmaSub Eps = []
sigmaSub Phi = []
sigmaSub (Seq rs) = concatMap sigmaSub rs
sigmaSub (Choice rs) = concatMap sigmaSub rs
sigmaSub (Star r) = sigmaSub r