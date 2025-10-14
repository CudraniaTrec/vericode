
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

method GetMin(tree: Tree) returns (res: int)
  requires tree != Empty
  ensures forall t :: BinarySearchTree(tree) && t != Empty ==> res <= t.value
  ensures (exists t :: BinarySearchTree(tree) && t != Empty && t.value == res)
{
  match tree {
    case Empty => 
      // Should never happen due to precondition
      assert false;
      res := 0;
    case Node (Empty, value, Empty) => 
      res := tree.value;
    case Node (Empty, value, right) => 
      res := tree.value;
    case Node (left, value, right) =>
      var minval := tree.value;
      // Strongest invariant: left != Empty
      minval := GetMin(tree.left);
      var tmp := Node(tree.left, minval, tree.right);
      assert minval <= value;
      res := tmp.value;
  }
}

method GetMax(tree: Tree) returns (res: int)
  requires tree != Empty
  ensures forall t :: BinarySearchTree(tree) && t != Empty ==> res >= t.value
  ensures (exists t :: BinarySearchTree(tree) && t != Empty && t.value == res)
{
  match tree {
    case Empty => 
      // Should never happen due to precondition
      assert false;
      res := 0;
    case Node (Empty, value, Empty) => 
      res := tree.value;
    case Node (left, value, Empty) => 
      res := tree.value;
    case Node (left, value, right) =>
      var minval := tree.value;
      // Strongest invariant: right != Empty
      minval := GetMax(tree.right);
      var tmp := Node(tree.left, minval, tree.right);
      assert minval >= value;
      res := tmp.value;
  }
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
    case Empty => 
      res := Node(Empty, value, Empty);
      assert BinarySearchTree(res);
    case Node(_,_,_) =>
      var temp: Tree;
      if(value == tree.value) {
        assert BinarySearchTree(tree);
        return tree;
      }
      if(value < tree.value){
        temp := insertRecursion(tree.left, value);
        assert BinarySearchTree(temp);
        res := Node(temp, tree.value, tree.right);
        assert BinarySearchTree(res);
      }else if (value > tree.value){
        temp := insertRecursion(tree.right, value);
        assert BinarySearchTree(temp);
        res := Node(tree.left, tree.value, temp);
        assert BinarySearchTree(res);
      }
  }
}

method delete(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(res)
  ensures (forall x :: minValue(tree, x) ==> minValue(res, x))
  ensures (forall x :: maxValue(tree, x) ==> maxValue(res, x))
{
  match tree {
    case Empty => 
      assert BinarySearchTree(tree);
      return tree;
    case Node(_,_ ,_) =>
      var temp: Tree;
      if (value < tree.value){
        temp := delete(tree.left, value);
        assert BinarySearchTree(temp);
        res := Node(temp, tree.value, tree.right);
        assert BinarySearchTree(res);
      } else if (value > tree.value){
        temp := delete(tree.right, value);
        assert BinarySearchTree(temp);
        res := Node(tree.left, tree.value, temp);
        assert BinarySearchTree(res);
      } else {
        if (tree.left == Empty){
          assert BinarySearchTree(tree.right);
          return tree.right;
        } else if (tree.right == Empty) {
          assert BinarySearchTree(tree.left);
          return tree.left;
        }
        var minVal := GetMin(tree.right);
        temp := delete(tree.right, minVal);
        assert BinarySearchTree(temp);
        res := Node(tree.left, minVal, temp);
        assert BinarySearchTree(res);
      }
  }
}

method Inorder(tree: Tree)
  ensures BinarySearchTree(tree)
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
  ensures BinarySearchTree(tree)
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
