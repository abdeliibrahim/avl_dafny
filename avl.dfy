class AvlNode {
  ghost var Contents: set<int>
  ghost var Repr: set<AvlNode>

  var height: int
  var data: int
  var left: AvlNode?
  var right: AvlNode?

  ghost predicate Height_Valid()
    reads this, Repr
  {
    this in Repr &&
    (left != null ==> left in Repr && left.Repr <= Repr && this !in left.Repr) &&
    (right != null ==> right in Repr && right.Repr <= Repr && this !in right.Repr) &&
    (left != null && right != null ==> left.Repr !! right.Repr) &&
    (left != null ==> left.Height_Valid()) &&
    (right != null ==> right.Height_Valid()) &&
    height == 1 + max(if left == null then -1 else left.height, if right == null then -1 else right.height)
  }

  ghost predicate Balanced()
    reads this, Repr
  {
    this in Repr &&
    (left != null ==> left in Repr && left.Balanced()) &&
    (right != null ==> right in Repr && right.Balanced()) &&
    var leftHeight := if left == null then -1 else left.height;
    var rightHeight := if right == null then -1 else right.height;
    -1 <= leftHeight - rightHeight <= 1
  }

  function max(a: int, b: int) : int
  {
    if a >= b then a else b
  }

  ghost predicate Valid()
    reads this, Repr
  {
    true
  }

  constructor Init(x: int)
    ensures Valid() && fresh(Repr - {this})
    ensures Height_Valid()
    ensures Balanced()
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
    
}