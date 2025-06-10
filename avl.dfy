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

  // ------------ utils
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
  TestAVLTree();
}

