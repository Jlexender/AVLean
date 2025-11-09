import avltree.AvlTree

namespace AVL.Test
open AVL
open Operations

def insertList {α : Type} [Ord α] (xs : List α) : AvlStructure α :=
  xs.foldl (fun t v => insert v t) AvlStructure.nil

def invHolds {α} (t : AvlStructure α) : Bool :=
  match AvlInvariant t with
  | True => true

example : True :=
  have := insert 10 AvlStructure.nil
  True.intro

example : True :=
  let t := insertList [10,5,15,3,7]
  have : search 7 t = true := rfl -- test structure ok
  True.intro

example : True :=
  let t := insertList [10,20,30]   -- RR rotation expected
  have := invHolds t
  trivial

example : True :=
  let t := insertList [30,20,10]   -- LL rotation expected
  have := invHolds t
  trivial

example : True :=
  let t := insertList [30,10,20]   -- LR rotation
  have := invHolds t
  trivial

example : True :=
  let t := insertList [10,30,20]   -- RL rotation
  have := invHolds t
  trivial

example : True :=
  let t := insertList [10,5,15,12]
  let t2 := delete 12 t
  have := invHolds t2
  trivial

example : True :=
  let t := insertList [20,10,30,5,15,25,35]
  let t2 := delete 20 t
  have := invHolds t2
  trivial

example : True :=
  let t := insertList (List.range 20)
  have := invHolds t
  trivial

example : True :=
  let t := insertList (List.range 20)
  let t2 := (List.range 20).foldl (fun acc x => delete x acc) t
  have := invHolds t2
  trivial

end AVL.Test
