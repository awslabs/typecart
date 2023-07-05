module BinaryTree {

  // Keyed binary trees and search
  datatype tree = Leaf | Node (tree, int, tree)

  function search(t: tree, key:int): bool
  {
    match t
    case Leaf => false
    case Node (l, k, r) =>
      if k == key then
        true
      else
        var lfound := search(l, key);
        var rfound := search(r, key);
        lfound || rfound
  }
}
