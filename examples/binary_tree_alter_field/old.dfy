module BinaryTree {

datatype tree = Leaf | Node (tree, int, int, tree)

function depth(t: tree): int
{ 
  match t {
    case Leaf => 0
    case Node (l, i, j, r) => 
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
    case Node (l, i, j, r) => Node(copy(l), i, j, copy(r))
  }
}

function sum(t: tree): int
{
   match t {
    case Leaf => 0
    case Node (l, i, j, r) => 
      j + sum(l) + sum(r)
   }
}

function reduce (t: tree, id: int, f: (int, int) -> int): int
{
  match t {
    case Leaf => id
    case Node (l, k, v, r) => 
      f(v, f(reduce(l, id, f), reduce(r, id, f)))
   }
}
}
