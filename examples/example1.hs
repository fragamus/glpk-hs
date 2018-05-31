import Prelude hiding (Num(..))
import Algebra.Classes
import Control.Monad.LPMonad
import Data.LinearProgram.Common
import Data.LinearProgram
import Data.LinearProgram.GLPK
import qualified Data.Map as M
import Data.LinearProgram.LinExpr
import qualified Data.Map as M
import qualified Data.List as L
import qualified Data.Foldable as F
import qualified Data.Bits as B


import Control.Monad
import qualified Data.Set as S
capacity = 200
depots = S.fromList [0]
vPlus = S.fromList [1,2,3,4,5,6,7]
demand = [0,70,54,21,4,16,32,18]
vs = S.union depots vPlus
es = S.fromList $ setToConnections vs
demandForRoute s = Prelude.sum $ Prelude.map (demand !!) s
qRoutesWithoutEndpoints as = do { a <- S.toList vPlus; guard (length as < 1 || a /= head as); guard (length as < 2 || a /= (as!!1)); guard (demandForRoute (a:as) <= capacity); [a:as] ++ qRoutesWithoutEndpoints (a:as)}
depotPairs = [(a,b)|a<-(S.toList depots),b<-(S.toList depots)]
addEndpoints route = map (\(a,b)-> (a:route)++[b]) depotPairs 




listOfSubsetsAsLists s = let {n = S.size s;elements=S.toList s} in Prelude.map (\i->( (Prelude.map (elements!!)) . (Prelude.filter (B.testBit i))) [0..n-1]) [(0::Int)..((2 Prelude.^ n)-1)]

listOfSubsets s = Prelude.map S.fromList $ listOfSubsetsAsLists s

cost = [[0,  45, 65, 75,  100,  130,  100,  100 ],[85, 0,  19,  30, 27, 140,  120,  120 ],[130,  50,   0,  11,  35, 160,  130,  130],[120,  45, 45, 0,   24, 140,  120,  120 ],[130,  65, 50,   60,    0,  160,  130,  130 ],[85, 160,  150,  160,  190,  0,   26,  90 ],[60,   140,  130,  140,  160,  26,  0,   10 ],[55, 130,  120,  130,  150,  35,  80,   0]]

entrancesNeeded s = ceiling $ ((demandForRoute s)::Double) Prelude./ (capacity::Double)
littleK s = ceiling $ ((demandForRoute $ S.toList s)::Double) Prelude./ (capacity::Double)



delta s = S.filter (\(a,b)-> (a `S.member` s) /= (b `S.member` s)) $ es 

xe (i,j) = "x"++(show i)++"c"++(show j) 

ki i = "K"++(show i)

linearCombination = linCombination . S.toList


dissolve xss = let n = length xss in ((zip3 (map (`Prelude.div` n) [0..]) (map (`Prelude.mod` n) [0..])) . join) xss

nonDiagonals = filter (\(i,j,x)->i/=j)

totalCost = ( (map (\(i,j,v)->(v,xij i j))) . nonDiagonals . dissolve) cost

xij i j = "x"++(show i)++"c"++(show j) 

setToConnections as = (\zs-> let n = length zs in ((((Prelude.filter (\(i,j)->i/=j)) . (Prelude.map (\i->(zs!!Prelude.div i n, zs!!Prelude.mod i n)))) [0..n Prelude.^ 2-1]))) $ S.toList as

waterDistributionCost :: LinFunc String Int 
waterDistributionCost = linCombination totalCost 

lp :: LP String Int
lp = execLPM $ do
  setDirection Min
  setObjective waterDistributionCost

  F.mapM_ (\i-> equalTo (linearCombination (S.map (\e->(1,xe e)) (delta (S.singleton i)))) 2) vPlus

  F.mapM_ (\i-> equalTo (linearCombination ((-2,ki i) `S.insert` S.map (\e->(1,xe e)) (delta (S.singleton i)))) 0) depots

  F.mapM_ (\s-> geqTo (linearCombination (S.map (\e->(1,xe e)) (delta s))) (2* littleK s)) 
        (L.filter (not . S.null) $ listOfSubsets vPlus)

  F.mapM_ (\e->leqTo (linearCombination (S.singleton (1,xe e))) 1) (es S.\\ (delta depots))

  F.mapM_ (\e->geqTo (linearCombination (S.singleton (1,xe e))) 0) es

  F.mapM_ (\e->setVarKind (xe e) ContVar) es 

  F.mapM_ (\i->setVarKind (ki i) ContVar) depots 

main = do
    (ret,ab) <- glpSolveVars mipDefaults lp
    case ab of 
        Nothing -> print "nada"
        Just (a,b) -> do
            print a
            print b
    print "hi" 
