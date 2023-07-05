module BinaryTree {
  // Add the int field
  datatype tree = Leaf | Node (l: tree, int, r: tree)

  function depth(t: tree): int
  {
    match t {
      case Leaf => 0
      case Node (l, k, r) =>
        var dl := depth(l);
        var dr := depth(r);
        if (dl < dr) then
          dl + 1
        else
          dr + 1
    }
  }

  function copy(t: tree): tree
  {
    match t {
      case Leaf => Leaf
      case Node (l, k, r) => Node(copy(l), k, copy(r))
    }
  }
}
