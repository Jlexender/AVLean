import avltree.AvlTree

namespace AVL.Test

open AVL
open Operations

def AvlInvariantBool : AvlStructure Int → Bool
| AvlStructure.nil => true
| AvlStructure.node l _ r =>
    let bf := balanceFactor (AvlStructure.node l 0 r)
    bf ≥ -1 && bf ≤ 1 && AvlInvariantBool l && AvlInvariantBool r

def assertInvariant (t : AvlStructure Int) : Bool :=
  if AvlInvariantBool t then
    true
  else
    panic! "AVL invariant violated!"

def insertList (xs : List Int) : AvlStructure Int :=
  xs.foldl (fun t v => insert v t) AvlStructure.nil

#eval assertInvariant (insertList [10,5,15,3,7])
#eval assertInvariant (insertList [10,20,30])
#eval assertInvariant (insertList [30,20,10])
#eval assertInvariant (insertList [30,10,20])
#eval assertInvariant (insertList [10,30,20])
#eval assertInvariant (insertList [10,5,15,12] |> fun t => delete 12 t)

#eval let t := insertList ((List.range 20).map Int.ofNat)
      let t2 := ((List.range 20).map Int.ofNat).foldl (fun acc x => delete x acc) t
      assertInvariant t2

end AVL.Test
