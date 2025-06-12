import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_

# Module: module_

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def TestAVLNode():
        d_0_root_: AVLNode
        nw0_ = AVLNode()
        nw0_.ctor__(10)
        d_0_root_ = nw0_
        d_1_leftChild_: AVLNode
        nw1_ = AVLNode()
        nw1_.ctor__(5)
        d_1_leftChild_ = nw1_
        d_2_rightChild_: AVLNode
        nw2_ = AVLNode()
        nw2_.ctor__(15)
        d_2_rightChild_ = nw2_
        (d_0_root_).left = d_1_leftChild_
        (d_0_root_).right = d_2_rightChild_
        (d_0_root_).UpdateHeight()

    @staticmethod
    def TestBalanceFactors():
        d_0_root_: AVLNode
        nw0_ = AVLNode()
        nw0_.ctor__(20)
        d_0_root_ = nw0_
        d_1_left_: AVLNode
        nw1_ = AVLNode()
        nw1_.ctor__(10)
        d_1_left_ = nw1_
        d_2_leftLeft_: AVLNode
        nw2_ = AVLNode()
        nw2_.ctor__(5)
        d_2_leftLeft_ = nw2_
        (d_1_left_).left = d_2_leftLeft_
        (d_1_left_).UpdateHeight()
        (d_0_root_).left = d_1_left_
        (d_0_root_).UpdateHeight()
        d_3_right_: AVLNode
        nw3_ = AVLNode()
        nw3_.ctor__(30)
        d_3_right_ = nw3_
        d_4_rightRight_: AVLNode
        nw4_ = AVLNode()
        nw4_.ctor__(35)
        d_4_rightRight_ = nw4_
        (d_3_right_).right = d_4_rightRight_
        (d_3_right_).UpdateHeight()
        (d_0_root_).right = d_3_right_
        (d_0_root_).UpdateHeight()

    @staticmethod
    def TestSingleNode():
        d_0_node_: AVLNode
        nw0_ = AVLNode()
        nw0_.ctor__(42)
        d_0_node_ = nw0_

    @staticmethod
    def Main(noArgsParameter__):
        default__.TestAVLNode()
        default__.TestBalanceFactors()
        default__.TestSingleNode()
        d_0_cmp_: IntComparator
        nw0_ = IntComparator()
        nw0_.ctor__()
        d_0_cmp_ = nw0_
        d_1_tree_: AVLTree
        nw1_ = AVLTree()
        nw1_.ctor__(d_0_cmp_)
        d_1_tree_ = nw1_
        d_2_b_: bool
        out0_: bool
        out0_ = (d_1_tree_).IsEmpty()
        d_2_b_ = out0_
        nw2_ = AVLNode()
        nw2_.ctor__(10)
        (d_1_tree_).root = nw2_
        obj0_ = d_1_tree_.root
        nw3_ = AVLNode()
        nw3_.ctor__(5)
        obj0_.left = nw3_
        obj1_ = d_1_tree_.root
        nw4_ = AVLNode()
        nw4_.ctor__(15)
        obj1_.right = nw4_
        (d_1_tree_.root.left).UpdateHeight()
        (d_1_tree_.root.right).UpdateHeight()
        (d_1_tree_.root).UpdateHeight()


class AVLNode:
    def  __init__(self):
        self.data: TypeVar('T') = None
        self.left: AVLNode = None
        self.right: AVLNode = None
        self.height: int = int(0)
        pass

    def __dafnystr__(self) -> str:
        return "_module.AVLNode"
    def ctor__(self, value):
        (self).data = value
        (self).left = None
        (self).right = None
        (self).height = 1

    def Height(self):
        return self.height

    def LeftHeight(self):
        if (self.left) == (None):
            return 0
        elif True:
            return self.left.height

    def RightHeight(self):
        if (self.right) == (None):
            return 0
        elif True:
            return self.right.height

    def BalanceFactor(self):
        return ((self).RightHeight()) - ((self).LeftHeight())

    def IsBalanced(self):
        d_0_bf_ = (self).BalanceFactor()
        return ((-1) <= (d_0_bf_)) and ((d_0_bf_) <= (1))

    def HeightValid(self):
        return (self.height) == ((1) + (((self).LeftHeight() if ((self).LeftHeight()) > ((self).RightHeight()) else (self).RightHeight())))

    def ValidAVLNode(self):
        return ((((self).HeightValid()) and ((self).IsBalanced())) and (((self.left) == (None)) or ((self.left).ValidAVLNode()))) and (((self.right) == (None)) or ((self.right).ValidAVLNode()))

    def UpdateHeight(self):
        d_0_leftH_: int
        d_0_leftH_ = (self).LeftHeight()
        d_1_rightH_: int
        d_1_rightH_ = (self).RightHeight()
        d_2_maxH_: int
        if (d_0_leftH_) > (d_1_rightH_):
            d_2_maxH_ = d_0_leftH_
        elif True:
            d_2_maxH_ = d_1_rightH_
        (self).height = (1) + (d_2_maxH_)

    def LeftRotate(self):
        newRoot: AVLNode = None
        d_0_pivot_: AVLNode
        d_0_pivot_ = self.right
        d_1_temp_: AVLNode
        d_1_temp_ = d_0_pivot_.left
        (d_0_pivot_).left = self
        (self).right = d_1_temp_
        (self).UpdateHeight()
        (d_0_pivot_).UpdateHeight()
        newRoot = d_0_pivot_
        return newRoot

    def RightRotate(self):
        newRoot: AVLNode = None
        d_0_pivot_: AVLNode
        d_0_pivot_ = self.left
        d_1_temp_: AVLNode
        d_1_temp_ = d_0_pivot_.right
        (d_0_pivot_).right = self
        (self).left = d_1_temp_
        (self).UpdateHeight()
        (d_0_pivot_).UpdateHeight()
        newRoot = d_0_pivot_
        return newRoot

    def LeftRightRotate(self):
        newRoot: AVLNode = None
        d_0_a_: AVLNode
        d_0_a_ = self
        d_1_b_: AVLNode
        d_1_b_ = self.left
        d_2_c_: AVLNode
        d_2_c_ = self.left.right
        d_3_t1_: AVLNode
        d_3_t1_ = d_2_c_.left
        d_4_t2_: AVLNode
        d_4_t2_ = d_2_c_.right
        (d_2_c_).left = d_1_b_
        (d_2_c_).right = d_0_a_
        (d_1_b_).right = d_3_t1_
        (d_0_a_).left = d_4_t2_
        (d_1_b_).UpdateHeight()
        (d_0_a_).UpdateHeight()
        (d_2_c_).UpdateHeight()
        newRoot = d_2_c_
        return newRoot

    def RightLeftRotate(self):
        newRoot: AVLNode = None
        d_0_a_: AVLNode
        d_0_a_ = self
        d_1_b_: AVLNode
        d_1_b_ = self.right
        d_2_c_: AVLNode
        d_2_c_ = self.right.left
        d_3_t1_: AVLNode
        d_3_t1_ = d_2_c_.left
        d_4_t2_: AVLNode
        d_4_t2_ = d_2_c_.right
        (d_2_c_).left = d_0_a_
        (d_2_c_).right = d_1_b_
        (d_0_a_).right = d_3_t1_
        (d_1_b_).left = d_4_t2_
        (d_0_a_).UpdateHeight()
        (d_1_b_).UpdateHeight()
        (d_2_c_).UpdateHeight()
        newRoot = d_2_c_
        return newRoot

    def IsLeaf(self):
        return ((self.left) == (None)) and ((self.right) == (None))

    def HasOneChild(self):
        return (((self.left) == (None)) and ((self.right) != (None))) or (((self.left) != (None)) and ((self.right) == (None)))

    def HasTwoChildren(self):
        return ((self.left) != (None)) and ((self.right) != (None))

    def Insert(self, value, cmp):
        newRoot: AVLNode = None
        d_0_isEqual_: bool
        out0_: bool
        out0_ = (cmp).Equal(self.data, value)
        d_0_isEqual_ = out0_
        if d_0_isEqual_:
            newRoot = self
            return newRoot
        d_1_isLess_: bool
        out1_: bool
        out1_ = (cmp).Less(value, self.data)
        d_1_isLess_ = out1_
        if d_1_isLess_:
            if (self.left) == (None):
                nw0_ = AVLNode()
                nw0_.ctor__(value)
                (self).left = nw0_
        elif True:
            if (self.right) == (None):
                nw1_ = AVLNode()
                nw1_.ctor__(value)
                (self).right = nw1_
        (self).UpdateHeight()
        newRoot = self
        return newRoot

    def FindMinNode(self):
        minNode: AVLNode = None
        d_0_current_: AVLNode
        d_0_current_ = self
        while (d_0_current_.left) != (None):
            d_0_current_ = d_0_current_.left
        minNode = d_0_current_
        return minNode

    def Rebalance(self):
        newRoot: AVLNode = None
        newRoot = self
        return newRoot

    def Delete(self, value, cmp):
        newRoot: AVLNode = None
        d_0_isEqual_: bool
        out0_: bool
        out0_ = (cmp).Equal(self.data, value)
        d_0_isEqual_ = out0_
        if d_0_isEqual_:
            if (self).IsLeaf():
                newRoot = None
                return newRoot
            elif (self).HasOneChild():
                if (self.left) == (None):
                    newRoot = self.right
                elif True:
                    newRoot = self.left
                return newRoot
            elif True:
                pass
        elif True:
            newRoot = self
        return newRoot


class Comparator:
    pass
    def Less(self, x, y):
        pass

    def Equal(self, x, y):
        pass


class IntComparator(Comparator):
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "_module.IntComparator"
    def ctor__(self):
        pass
        pass

    def Less(self, x, y):
        b: bool = False
        b = (x) < (y)
        return b

    def Equal(self, x, y):
        b: bool = False
        b = (x) == (y)
        return b


class AVLTree:
    def  __init__(self):
        self.root: AVLNode = None
        self.cmp: Comparator = None
        pass

    def __dafnystr__(self) -> str:
        return "_module.AVLTree"
    def ctor__(self, c):
        (self).root = None
        (self).cmp = c

    def Valid(self):
        return ((self.root) == (None)) or ((self.root).ValidAVLNode())

    def IsEmpty(self):
        empty: bool = False
        empty = (self.root) == (None)
        return empty

    def GetHeight(self):
        h: int = int(0)
        if (self.root) == (None):
            h = 0
        elif True:
            h = self.root.height
        return h

    def Search(self, value):
        found: bool = False
        d_0_current_: AVLNode
        d_0_current_ = self.root
        while (d_0_current_) != (None):
            d_1_isEqual_: bool
            out0_: bool
            out0_ = (self.cmp).Equal(d_0_current_.data, value)
            d_1_isEqual_ = out0_
            if d_1_isEqual_:
                found = True
                return found
            d_2_isLess_: bool
            out1_: bool
            out1_ = (self.cmp).Less(value, d_0_current_.data)
            d_2_isLess_ = out1_
            if d_2_isLess_:
                d_0_current_ = d_0_current_.left
            elif True:
                d_0_current_ = d_0_current_.right
        found = False
        return found

    def Insert(self, value):
        if (self.root) == (None):
            nw0_ = AVLNode()
            nw0_.ctor__(value)
            (self).root = nw0_
        elif True:
            d_0___v0_: AVLNode
            out0_: AVLNode
            out0_ = (self.root).Insert(value, self.cmp)
            d_0___v0_ = out0_

    def Delete(self, value):
        if (self.root) != (None):
            out0_: AVLNode
            out0_ = (self.root).Delete(value, self.cmp)
            (self).root = out0_

