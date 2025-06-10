class AVLNode<T> {
  var data: T
  var left: AVLNode?<T>
  var right: AVLNode?<T>
  var height: nat

  constructor(value: T)
    ensures data == value
    ensures left == null
    ensures right == null
    ensures height == 1
  {
    data := value;
    left := null;
    right := null;
    height := 1;
  }

  function Height(): nat
    reads this
  {
    height
  }

  function LeftHeight(): nat
    reads this, left
  {
    if left == null then 0 else left.height
  }

  function RightHeight(): nat
    reads this, right
  {
    if right == null then 0 else right.height
  }

  function BalanceFactor(): int
    reads this, left, right
  {
    RightHeight() - LeftHeight()
  }

  predicate IsBalanced()
    reads this, left, right
  {
    var bf := BalanceFactor();
    -1 <= bf <= 1
  }

  predicate HeightValid()
    reads this, left, right
  {
    height == 1 + if LeftHeight() > RightHeight() then LeftHeight() else RightHeight()
  }

  predicate ValidAVLNode()
    reads this, left, right
    decreases height
  {
    HeightValid() &&
    IsBalanced()
  }

  method UpdateHeight()
    requires left == null || left.ValidAVLNode()
    requires right == null || right.ValidAVLNode()
    modifies this
    ensures HeightValid()
    ensures data == old(data)
    ensures left == old(left)
    ensures right == old(right)
  {
    var leftH := LeftHeight();
    var rightH := RightHeight();
    height := 1 + if leftH > rightH then leftH else rightH;
  }

  function IsLeaf(): bool
    reads this
  {
    left == null && right == null
  }

  function HasOneChild(): bool
    reads this
  {
    (left == null && right != null) || (left != null && right == null)
  }

  function HasTwoChildren(): bool
    reads this
  {
    left != null && right != null
  }



}




// AVLTree class to manage the AVL tree structure

// Comparator interface to define the comparison operations for AVLTree
// This interface allows the AVLTree to be generic over any type T that can be compared
// using a custom comparator. The Less method checks if one element is less than another,
// and the Equal method checks if two elements are equal.
trait Comparator<T> {
  method Less(x: T, y: T) returns (b: bool)
    ensures b ==> x != y

  method Equal(x: T, y: T) returns (b: bool)
    ensures b <==> x == y
}

class AVLTree<T> {
  var root: AVLNode?<T>
  var cmp: Comparator<T>

  constructor(c: Comparator<T>)
    ensures root == null
  {
    root := null;
    cmp := c;
  }

  predicate Valid()
    reads this, root, if root != null then {root.left} else {null}, if root != null then {root.right} else {null}
  {
    root == null || root.ValidAVLNode()
  }

  method IsEmpty() returns (empty: bool)
    ensures empty <==> (root == null)
  {
    empty := (root == null);
  }

  method GetHeight() returns (h: nat)
    ensures h == (if root == null then 0 else root.height)
  {
    if root == null {
      h := 0;
    } else {
      h := root.height;
    }
  }

  method Search(value: T) returns (found: bool)
  requires Valid() // Tree is valid at the beginning
  ensures Valid()  // Tree is unchanged, so still valid
  decreases *
{
  var current := root;
  while current != null
    decreases *
  {
    var isEqual := cmp.Equal(current.data, value);
    if isEqual {
      found := true;
      return;
    }

    var isLess := cmp.Less(value, current.data);
    if isLess {
      current := current.left;
    } else {
      current := current.right;
    }
  }
  found := false;
}


}

method TestAVLNode()
{
  var root := new AVLNode(10);
  var leftChild := new AVLNode(5);
  var rightChild := new AVLNode(15);

  root.left := leftChild;
  root.right := rightChild;
  root.UpdateHeight();

  assert root.ValidAVLNode();
  assert root.Height() == 2;
  assert root.BalanceFactor() == 0;
  assert root.IsBalanced();
  assert root.HasTwoChildren();
  assert !root.IsLeaf();
}

method TestBalanceFactors()
{
  var root := new AVLNode(20);
  var left := new AVLNode(10);
  var leftLeft := new AVLNode(5);

  left.left := leftLeft;
  left.UpdateHeight();

  root.left := left;
  root.UpdateHeight();

  var right := new AVLNode(30);
  var rightRight := new AVLNode(35);

  right.right := rightRight;
  right.UpdateHeight();

  root.right := right;
  root.UpdateHeight();
}

method TestSingleNode()
{
  var node := new AVLNode(42);

  assert node.IsLeaf();
  assert node.Height() == 1;
  assert node.BalanceFactor() == 0;
  assert node.IsBalanced();
  assert node.ValidAVLNode();
}


method Main()
{
  TestAVLNode();
  TestBalanceFactors();
  TestSingleNode();
  // TestAVLTree();
}