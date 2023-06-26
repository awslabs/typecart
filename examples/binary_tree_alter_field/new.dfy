module BinaryTree {
// the 3rd field is changed from int to real
datatype tree = Leaf | Node (tree, int, real, tree)

function depth(t: tree): int
{ 
  match t {
    case Leaf => 0
    case Node (l, k, v, r) => 
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
    case Node (l, k, v, r) => Node(copy(l), k, v, copy(r))
  }
}

function sum(t: tree): real
{
   match t {
    case Leaf => 0.0
    case Node (l, k, v, r) => 
      v + sum(l) + sum(r)
   }
}

function reduce (t: tree, id: real, f: (real, real) -> real): real
{
  match t {
    case Leaf => id
    case Node (l, k, v, r) => 
      f(v, f(reduce(l, id, f), reduce(r, id, f)))
   }
}
}