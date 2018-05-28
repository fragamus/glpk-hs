import Prelude hiding (Num(..))

import Algebra.Classes
import Control.Monad.LPMonad
import Data.LinearProgram.Common
import Data.LinearProgram
import Data.LinearProgram.GLPK
import qualified Data.Map as M
import Data.LinearProgram.LinExpr

import Control.Monad
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L
import qualified Data.Foldable as F
import qualified Data.Bits as B

listOfSubsetsAsLists s = let {n = S.size s;es=S.toList s} in Prelude.map (\i->( (Prelude.map (es!!)) . (Prelude.filter (B.testBit i))) [0..n-1]) [(0::Int)..((2 Prelude.^ n)-1)]

cost = [[0,  45, 65, 75,  100,  130,  100,  100 ],[85, 0,  19,  30, 27, 140,  120,  120 ],[130,  50,   0,  11,  35, 160,  130,  130],[120,  45, 45, 0,   24, 140,  120,  120 ],[130,  65, 50,   60,    0,  160,  130,  130 ],[85, 160,  150,  160,  190,  0,   26,  90 ],[60,   140,  130,  140,  160,  26,  0,   10 ],[55, 130,  120,  130,  150,  35,  80,   0]]

thirst = [0,70,54,21,4,16,32,18]

thirstForRoute s = Prelude.sum $ Prelude.map (thirst !!) s

entrancesNeeded s = ceiling $ ((thirstForRoute s)::Double) Prelude./ (capacity::Double)

capacity = 200

entrancesLC s = map (\(a,b)->(1,xij a b) )           $   filter (\(a,b)-> (a `S.notMember` s) && (b `S.member` s))      $ setToConnections as 


ws = S.fromList [0]

cs = S.fromList [1,2,3,4,5,6,7]

as = S.union ws cs

dissolve xss = let n = length xss in ((zip3 (map (`Prelude.div` n) [0..]) (map (`Prelude.mod` n) [0..])) . join) xss

nonDiagonals = filter (\(i,j,x)->i/=j)

totalCost = ( (map (\(i,j,v)->(v,xij i j))) . nonDiagonals . dissolve) cost

sumEntries j = let is = S.toList $ as `S.difference` S.singleton j in map (\i->(1,xij i j)) is
   
sumExits i = let js = S.toList $ as `S.difference` S.singleton i in map (\j->(1,xij i j)) js   

xij i j = "x"++(show i)++"c"++(show j) 

setToConnections as = (\zs-> let n = length zs in ((((Prelude.filter (\(i,j)->i/=j)) . (Prelude.map (\i->(zs!!Prelude.div i n, zs!!Prelude.mod i n)))) [0..n Prelude.^ 2-1]))) $ S.toList as

waterDistributionCost :: LinFunc String Int 
waterDistributionCost = linCombination totalCost 

lp :: LP String Int
lp = execLPM $ do
  setDirection Min
  setObjective waterDistributionCost

  mapM_ (\c->equalTo (linCombination $ sumEntries c) 1) $ S.toList cs 
  mapM_ (\c->equalTo (linCombination $ sumExits c) 1) $ S.toList cs 
  mapM_ (\w->equalTo (linCombination $ (-1,"k"++(show w)):(sumEntries w)) 0) $ S.toList ws 
  mapM_ (\w->equalTo (linCombination $ (-1,"k"++(show w)):(sumExits w)) 0) $ S.toList ws 
  mapM_ (\(i,j)->varGeq (xij i j) 0) $ setToConnections as 
  mapM_ (\w->varGeq ("k"++(show w)) 0) $ S.toList ws 
  mapM_ (\(i,j)->setVarKind (xij i j) BinVar) $ setToConnections as 
  mapM_ (\w->setVarKind ("k"++(show w)) IntVar) $ S.toList ws 

  mapM_ (\(e,lincomb)->geqTo (linCombination lincomb) e ) $ map (\l->(entrancesNeeded l, entrancesLC $ S.fromList l))  $ filter (/=[]) $ listOfSubsetsAsLists cs 

main = do
    (ret,ab) <- glpSolveVars mipDefaults lp
    case ab of 
        Nothing -> print "nada"
        Just (a,b) -> do
            print a
            print b
    print "hi" 
    --print $ map (\l->(entrancesNeeded l, entrancesLC $ S.fromList l))  $ filter (/=[]) $ listOfSubsetsAsLists cs 
