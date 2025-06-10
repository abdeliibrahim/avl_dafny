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
    
    print "AVL Node test passed! Root node has value: ", root.data, "\n";
    print "Root height: ", root.Height(), "\n";
    print "Balance factor: ", root.BalanceFactor(), "\n";
    print "Is balanced: ", root.IsBalanced(), "\n";
}

method TestBalanceFactors()
{
    print "\n=== Testing Balance Factors ===\n";
    
    var root := new AVLNode(20);
    var left := new AVLNode(10);
    var leftLeft := new AVLNode(5);
    
    left.left := leftLeft;
    left.UpdateHeight();
    
    root.left := left;
    root.UpdateHeight();
    
    print "Left-heavy tree:\n";
    print "Root balance factor: ", root.BalanceFactor(), "\n";
    print "Is balanced: ", root.IsBalanced(), "\n";
    
    var right := new AVLNode(30);
    var rightRight := new AVLNode(35);
    
    right.right := rightRight;
    right.UpdateHeight();
    
    root.right := right;
    root.UpdateHeight();
    
    print "After adding right subtree:\n";
    print "Root balance factor: ", root.BalanceFactor(), "\n";
    print "Is balanced: ", root.IsBalanced(), "\n";
    print "Root height: ", root.Height(), "\n";
}

method TestSingleNode()
{
    print "\n=== Testing Single Node ===\n";
    
    var node := new AVLNode(42);
    
    assert node.IsLeaf();
    assert node.Height() == 1;
    assert node.BalanceFactor() == 0;
    assert node.IsBalanced();
    assert node.ValidAVLNode();
    
    print "Single node test passed!\n";
    print "Value: ", node.data, ", Height: ", node.Height(), "\n";
}

method Main()
{
    TestAVLNode();
    TestBalanceFactors();
    TestSingleNode();
    print "\nAll tests completed successfully!\n";
}

