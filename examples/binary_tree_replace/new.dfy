module BinaryTree {
  // Rename "Node" to "Branch"
  datatype tree = Leaf | Branch (tree, tree)

  function depth(t: tree): int
  {
    match t {
      case Leaf => 0
      case Branch (l, r) =>
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
      case Branch (l, r) => Branch(copy(l), copy(r))
    }
  }
}
