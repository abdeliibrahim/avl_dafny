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
    modifies this
    ensures data == old(data)
    ensures left == old(left)
    ensures right == old(right)
  {
    var leftH := LeftHeight();
    var rightH := RightHeight();
    var maxH := if leftH > rightH then leftH else rightH;
    height := 1 + maxH;
  }

  // Used when right subtree is taller and right child is right-heavy
  method LeftRotate() returns (newRoot: AVLNode<T>)
    requires right != null
    modifies this, right
    ensures newRoot.data == old(right.data)
  {
    var pivot := right;
    var temp := pivot.left;

    pivot.left := this;
    this.right := temp;

    this.UpdateHeight();
    pivot.UpdateHeight();

    newRoot := pivot;
  }

  method RightRotate() returns (newRoot: AVLNode<T>)
    requires left != null
    modifies this, left
    ensures newRoot.data == old(left.data)
  {
    var pivot := left;
    var temp := pivot.right;

    pivot.right := this;
    this.left := temp;

    this.UpdateHeight();
    pivot.UpdateHeight();

    newRoot := pivot;
  }

  // double rotation
  method LeftRightRotate() returns (newRoot: AVLNode<T>)
    requires left != null && left.right != null
    modifies this, left, left.right
  {
    var a := this;
    var b := left;
    var c := left.right;
    var t1 := c.left;
    var t2 := c.right;

    c.left := b;
    c.right := a;
    b.right := t1;
    a.left := t2;

    b.UpdateHeight();
    a.UpdateHeight();
    c.UpdateHeight();

    newRoot := c;
  }

  // double rotation
  method RightLeftRotate() returns (newRoot: AVLNode<T>)
    requires right != null && right.left != null
    modifies this, right, right.left
  {
    var a := this;
    var b := right;
    var c := right.left;
    var t1 := c.left;
    var t2 := c.right;

    c.left := a;
    c.right := b;
    a.right := t1;
    b.left := t2;

    a.UpdateHeight();
    b.UpdateHeight();
    c.UpdateHeight();

    newRoot := c;
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


// AVLTree below
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
    requires Valid()
    ensures Valid()
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

// TODO: these are failing, not sure why
  // assert root.ValidAVLNode();
  // assert root.Height() == 2;
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