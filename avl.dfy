class AvlNode {
  ghost var Contents: set<int>
  ghost var Repr: set<AvlNode>

  var height: int
  var data: int
  var left: AvlNode?
  var right: AvlNode?

  ghost predicate height_valid()
    reads this, Repr
  {
    this in Repr &&
    (left != null ==> left in Repr && left.Repr <= Repr && this !in left.Repr) &&
    (right != null ==> right in Repr && right.Repr <= Repr && this !in right.Repr) &&
    (left != null && right != null ==> left.Repr !! right.Repr) &&
    (left != null ==> left.height_valid()) &&
    (right != null ==> right.height_valid()) &&
    height == 1 + max(if left == null then -1 else left.height, if right == null then -1 else right.height)
  }

  // difference in subtree heights ≤ 1
  ghost predicate balanced()
    reads this, Repr
  {
    this in Repr &&
    height_valid() &&
    valid() &&
    (left != null ==> left in Repr && left.balanced()) &&
    (right != null ==> right in Repr && right.balanced()) &&
    var leftheight := if left == null then -1 else left.height;
    var rightheight := if right == null then -1 else right.height;
    leftheight - rightheight <= 1 && rightheight - leftheight <= 1
  }

  function max(a: int, b: int) : int
  {
    if a >= b then a else b
  }

  ghost predicate valid()
    reads this, Repr
  {
    this in Repr &&
    (left != null ==> left in Repr && left.Repr <= Repr && this !in left.Repr) &&
    (right != null ==> right in Repr && right.Repr <= Repr && this !in right.Repr) &&
    (left != null && right != null ==> left.Repr !! right.Repr) &&
    (left != null ==> left.valid()) &&
    (right != null ==> right.valid()) &&
    Contents == {data} + (if left == null then {} else left.Contents) + (if right == null then {} else right.Contents) &&
    Repr == {this} + (if left == null then {} else left.Repr) + (if right == null then {} else right.Repr)
  }

  // init leaf node with value x
  constructor Init(x: int)
    ensures valid() && fresh(Repr - {this})
    ensures height_valid()
    ensures balanced()
    ensures Contents == {x}
    ensures Repr == {this}
  {
    data := x;
    height := 0;
    left := null;
    right := null;
    Contents := {x};
    Repr := {this};
  }
}

class AvlTree {
  ghost var Contents: set<int>
  ghost var Repr: set<object>

  var root: AvlNode?;

  ghost predicate valid()
    reads this, root, if root != null then root.Repr else {}
  {
    // empty
    if root == null then
      Contents == {}
    else
      root in Repr && root.Repr <= Repr &&
      root.valid() &&
      Contents == root.Contents
  }

  ghost predicate balanced()
    reads this, root, if root != null then root.Repr else {}
  {
    if root == null then
      true
    else
      root.balanced()
  }

  // init empty AVL tree
  constructor Init()
    ensures valid() && fresh(Repr - {this})
    ensures Contents == {}
    ensures balanced()
  {
    root := null;
    Repr := {this};
    Contents := {};
  }
}