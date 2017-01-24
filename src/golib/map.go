package fscq

import (
    "fmt"
    "testing"
)

type TreeNode struct {
    key Num
    val interface{}

    left *TreeNode
    right *TreeNode
    count Num
}

type AddrMap struct {
    root *TreeNode
}

func (n *TreeNode) insert(newKey Num, newVal interface{}) *TreeNode {
    fmt.Println("inserting %v -> %v", newKey, newVal)
    if (n == nil) {
        newNode := TreeNode {
            key : newKey,
            val : newVal,
        }
        (&newNode.count).Increment()
        return &newNode
    }

    // TODO balance tree
    switch cmp := newKey.Cmp(&n.key); cmp {
    case 0:
        // keys are identical
        n.val = newVal
    case 1:
        // newKey > key
        n.right = n.right.insert(newKey, newVal)
        (&n.count).Increment()
    case -1:
        // newKey < key
        n.left = n.left.insert(newKey, newVal)
        (&n.count).Increment()
    }

    return n
}


func (m *AddrMap) Insert(key Num, val interface{}) {
    m.root = m.root.insert(key, val)
}

func (n *TreeNode) find(findKey Num) (bool, interface{}) {
    if n == nil {
        return false, New_Empty()
    }
    switch cmp := findKey.Cmp(&n.key); cmp {
    case 0:
        // keys are identical
        return true, n.val
    case 1:
        // findKey > key
        return n.right.find(findKey)
    case -1:
        // findKey < key
        return n.left.find(findKey)
    }
    return false, New_Empty()
}

func (m *AddrMap) Find(key Num) (bool, interface{}) {
    return m.root.find(key)
}

func (m *AddrMap) Cardinality() Num {
    if m.root == nil {
        return big_of_i64(0)
    } else {
        return m.root.count
    }
}

func (n *TreeNode) TestCounts(T *testing.T) {
    count := New_Num()
    if (n == nil) {
        return
    }

    n.left.TestCounts(T)
    n.right.TestCounts(T)

    count.Increment()

    if (n.left != nil) {
        count.Add(count, &n.left.count)
        T.Logf("left: %v", n.left.count)
    }

    if (n.right != nil) {
        count.Add(count, &n.right.count)
        T.Logf("right: %v", n.right.count)
    }

    T.Logf("count of %v", count)

    if (&n.count).Cmp(count) != 0 {
        T.Error("expected %v, got %v", n.count, count)
    }
}

func (m *AddrMap) TestInvariants(T *testing.T) {
    m.root.TestCounts(T)
}
