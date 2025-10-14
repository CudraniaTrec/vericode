
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

predicate BinarySearchTree(tree: Tree)
{
  match tree
  case Empty => true
  case Node(_,_,_) =>
    (tree.left == Empty || tree.left.value < tree.value)
    && (tree.right == Empty || tree.right.value > tree.value)
    && BinarySearchTree(tree.left) && BinarySearchTree(tree.right)
    && minValue(tree.right, tree.value) && maxValue(tree.left, tree.value)
}

predicate maxValue(tree: Tree, max: int)
{
  match tree
  case Empty => true
  case Node(left,v,right) => (max > v) && maxValue(left, max) && maxValue(right, max)
}

predicate minValue(tree: Tree, min: int)
{
  match tree
  case Empty => true
  case Node(left,v,right) => (min < v) && minValue(left, min) && minValue(right, min)
}

function Subtrees(t: Tree): set<Tree>
{
  if t == Empty then {} else {t} + Subtrees(t.left) + Subtrees(t.right)
}

method GetMin(tree: Tree) returns (res: int)
  requires tree != Empty
  ensures (forall t :: t in Subtrees(tree) && t != Empty ==> res <= t.value)
  ensures (exists t :: t in Subtrees(tree) && t != Empty && (forall x :: x in Subtrees(tree) && x != Empty ==> t.value <= x.value) && res == t.value)
{
  var t := tree;
  while t.left != Empty
    invariant t != Empty
    invariant t in Subtrees(tree)
    invariant BinarySearchTree(tree)
    invariant BinarySearchTree(t)
    invariant (forall x :: x in Subtrees(tree) && x != Empty ==> t.value <= x.value || x == t || x in Subtrees(t.right))
  {
    t := t.left;
  }
  res := t.value;
}

method GetMax(tree: Tree) returns (res: int)
  requires tree != Empty
  ensures (forall t :: t in Subtrees(tree) && t != Empty ==> res >= t.value)
  ensures (exists t :: t in Subtrees(tree) && t != Empty && (forall x :: x in Subtrees(tree) && x != Empty ==> t.value >= x.value) && res == t.value)
{
  var t := tree;
  while t.right != Empty
    invariant t != Empty
    invariant t in Subtrees(tree)
    invariant BinarySearchTree(tree)
    invariant BinarySearchTree(t)
    invariant (forall x :: x in Subtrees(tree) && x != Empty ==> t.value >= x.value || x == t || x in Subtrees(t.left))
  {
    t := t.right;
  }
  res := t.value;
}

method insert(tree: Tree, value : int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(res)
{
  res := insertRecursion(tree, value);
}

method insertRecursion(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures res != Empty ==> BinarySearchTree(res)
  ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
  ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
{
  match tree {
    case Empty => res := Node(Empty, value, Empty);
    case Node(left, v, right) =>
      if(value == v) {
        res := tree;
      }
      else if(value < v){
        var temp := insertRecursion(left, value);
        res := Node(temp, v, right);
      }else {
        var temp := insertRecursion(right, value);
        res := Node(left, v, temp);
      }
  }
}

method delete(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  //ensures BinarySearchTree(res)
  //ensures res != Empty ==> BinarySearchTree(res)
{
  match tree {
    case Empty => return tree;
    case Node(left, v, right) =>
      if (value < v){
        var temp := delete(left, value);
        res := Node(temp, v, right);
      } else if (value > v){
        var temp := delete(right, value);
        res := Node(left, v, temp);
      } else {
        if (left == Empty){
          res := right;
        } else if (right == Empty) {
          res := left;
        } else {
          var minVal := GetMin(right);
          var temp := delete(right, minVal);
          res := Node(left, minVal, temp);
        }
      }
  }
}

method Inorder(tree: Tree)
{
  match tree {
    case Empty =>
    case Node(left, value, right) =>
      Inorder(tree.left);
      print tree.value, ", ";
      Inorder(tree.right);
  }
}

method Postorder(tree: Tree)
{
  match tree {
    case Empty =>
    case Node(left, value, right) =>
      Postorder(tree.left);
      Postorder(tree.right);
      print tree.value, ", ";
  }
}

method Main() {
  var tree := insert(Empty, 3);
  var u := insert(tree, 2);

  u := insert(u, 7);
  u := insert(u, 6);
  u := insert(u, 9);


  print "This is Inorder: ";
  Inorder(u);
  print "\n";
  //u := delete (u, 1);

  print "This is Postorder: ";
  Postorder(u);
  print "\n";

  print "tree before delete: ", u, "\n";

  u := delete(u, 7);
  print "tree after delete: ", u, "\n";

  print "This is Inorder: ";
  Inorder(u);

  print "\n";
  print "This is Postorder: ";
  Postorder(u);

  // var res := GetMin(u);
  // var max := GetMax(u);
  // print "this is max: ", max;
  //print "this is res: ", res;

  //print u;
}

function abs(a: real) : real {if a>0.0 then a else -a}
