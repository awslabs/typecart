module BinaryTree {
  // Add Node3 (tree, tree, tree)
  datatype tree = Leaf | Node (tree, tree) | Node3 (tree, tree, tree)

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
      case Node3 (l, m, r) =>
        var dl := depth(l);
        var dm := depth(m);
        var dr := depth(r);
        if (dl < dr) then
          if dm < dl then
            dm + 1
          else
            dl + 1
        else
        if dm > dr then
          dm + 1
        else
          dr + 1
    }
  }

  function copy(t: tree): tree
  {
    match t {
      case Leaf => Leaf
      case Node (l, r) => Node(copy(l), copy(r))
      case Node3 (l, m, r) => Node3(copy(l), copy(m), copy(r))

    }
  }
}
