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
}

type AddrMap struct {
    root *TreeNode
    count Num
}

type MapVal interface {
}

type KeyValPair struct {
    key *Num
    val interface{}
}

// Used only for AddrMap_literal
type LiteralKeyValPair struct {
    key Num
    val interface{}
}

func (n *TreeNode) insert(newKey Num, newVal interface{}) (*TreeNode, bool) {
    fmt.Println("inserting %v -> %v", newKey, newVal)
    if (n == nil) {
        newNode := TreeNode {
            key : newKey,
            val : newVal,
        }
        return &newNode, true
    }

    // TODO balance tree
    switch cmp := newKey.Cmp(&n.key); cmp {
    case 0:
        // keys are identical
        n.val = newVal
        return n, false
    case 1:
        // newKey > key
        right, success := n.right.insert(newKey, newVal)
        n.right = right
        return n, success
    case -1:
        // newKey < key
        left, success := n.left.insert(newKey, newVal)
        n.left = left
        return n, success
    }

    return n, false
}


func (m *AddrMap) Insert(key Num, val interface{}) {
    root, success := m.root.insert(key, val)
    m.root = root
    if success {
        (&m.count).Increment()
    }
}

func (n *TreeNode) find(findKey Num) (bool, interface{}) {
    if n == nil {
        return false, nil
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
    return false, nil
}

func (m *AddrMap) Find(key Num) (bool, interface{}) {
    return m.root.find(key)
}

func (m *AddrMap) Cardinality() Num {
    return m.count
}

func (n *TreeNode) getElements(slice []KeyValPair) []KeyValPair {
    if (n == nil) {
        return slice
    }

    slice = n.left.getElements(slice)
    slice = append(slice, KeyValPair {&n.key, n.val})
    slice = n.right.getElements(slice)
    return slice
}

func (m *AddrMap) Elements() []KeyValPair {
    slice := m.root.getElements(nil)
    return slice
}

func interpolate(left *TreeNode, right *TreeNode) *TreeNode {
    if left == nil {
        return right
    } else if right == nil {
        return left
    }

    left.right = interpolate(left.right, right)
    return left
}

func (n *TreeNode) remove(removeKey Num) (*TreeNode, bool) {
    // TODO balance
    if n == nil {
        return nil, false
    }
    var success bool

    switch cmp := removeKey.Cmp(&n.key); cmp {
    case 0:
        // keys are identical
        n = interpolate(n.left, n.right)
        return n, true
    case 1:
        // removeKey > key
        n.right, success = n.right.remove(removeKey)
        return n, success
    case -1:
        // removeKey < key
        n.left, success = n.left.remove(removeKey)
        return n, success
    }
    return nil, false
}

func (m *AddrMap) Remove(key Num) {
    var success bool
    m.root, success = m.root.remove(key)
    if success {
        (&m.count).Decrement()
    }
}

func AddrMap_literal(vals ...LiteralKeyValPair) AddrMap {
    a := new(AddrMap)
    for _, keyVal := range vals {
        a.Insert(keyVal.key, keyVal.val)
    }
    return *a
}

func (m *AddrMap) TestInvariants(T *testing.T) {
}
