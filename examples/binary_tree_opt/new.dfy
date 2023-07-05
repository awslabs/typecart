module BinaryTree {

  // Keyed binary trees and optimized search
  datatype tree = Leaf | Node (tree, int, tree)

  function search(t: tree, key:int): bool
  {
    match t
    case Leaf => false
    case Node (l, k, r) =>
      if k == key then
        true
      else
      if search(l, key) then
        true
      else
        search(r, key)
  }
}
