module BinaryTree {

  datatype tree = Leaf | Node (tree, tree)

  function depth(t: tree): int
  {
    match t {
      case Leaf => 0
      case Node (l, r) =>
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
      case Node (l, r) => Node(copy(l), copy(r))
    }
  }
}

