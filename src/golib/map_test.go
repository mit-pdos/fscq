package fscq

import (
    "strconv"
    "testing"
)

func TestInsertNoDups(T *testing.T) {
    m := new(AddrMap)
    vals := make(map[int64]string)
    for i := 0; i < 10; i++ {
        vals[int64(i)] = "string " + strconv.Itoa(i)
    }

    for k, v := range vals {
        T.Logf("inserting %v -> %v", k, v)
        m.Insert(big_of_i64(k), v)
        T.Logf("size = %v", m.Cardinality())
    }

    card := m.Cardinality()
    expected := big_of_i64(10)
    if card.Cmp(&expected) != 0 {
        T.Errorf("expected size %#v, got %v", 10, card)
    }

    m.TestInvariants(T)
}