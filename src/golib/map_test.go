package fscq

import (
    "strconv"
    "testing"
)

func TestInsertNoDupsCardinality(T *testing.T) {
    m := new(AddrMap)
    vals := make(map[int64]string)
    for i := 0; i < 10; i++ {
        vals[int64(i)] = "string " + strconv.Itoa(i)
    }

    for k, v := range vals {
        T.Logf("inserting %v -> %v", k, v)
        T.Logf("count %v", m.Cardinality())

        m.Insert(big_of_i64(k), v)
    }

    card := m.Cardinality()
    expected := big_of_i64(10)
    if card.Cmp(&expected) != 0 {
        T.Errorf("expected size %#v, got %v", 10, card)
    }

    m.TestInvariants(T)
}

func TestInsertDupsCardinality(T *testing.T) {
    m := new(AddrMap)
    m.Insert(big_of_i64(1), "one")
    m.Insert(big_of_i64(0), "zero")
    m.Insert(big_of_i64(2), "two")
    m.Insert(big_of_i64(1), "1")

    card := m.Cardinality()
    expected := big_of_i64(3)
    if card.Cmp(&expected) != 0 {
        T.Errorf("expected size %#v, got %v", 3, card)
    }
}

func TestInsertFind(T *testing.T) {
    m := new(AddrMap)
    m.Insert(big_of_i64(1), "one")
    m.Insert(big_of_i64(0), "zero")
    m.Insert(big_of_i64(2), "two")
    m.Insert(big_of_i64(1), "1")

    is_found, val := m.Find(big_of_i64(2))
    if !is_found {
        T.Errorf("couldn't find val inserted into map")
    }

    if val.(string) != "two" {
        T.Errorf("expected %v, got %v", "two", val)
    }

    is_found, val = m.Find(big_of_i64(1))
    if !is_found {
        T.Errorf("couldn't find val inserted into map")
    }

    if val.(string) != "1" {
        T.Errorf("expected %v, got %v", "1", val)
    }
}

func TestRemoveFind(T *testing.T) {
    m := new(AddrMap)
    m.Insert(big_of_i64(1), "one")
    m.Insert(big_of_i64(0), "zero")
    m.Insert(big_of_i64(2), "two")

    m.Remove(big_of_i64(0))
    is_found, _ := m.Find(big_of_i64(0))
    if is_found {
        T.Errorf("found removed value %v", 0)
    }
}

func TestElements(T *testing.T) {
    m := new(AddrMap)
    vals := make(map[int64]Num)
    for i := 0; i < 10; i++ {
        vals[int64(i)] = big_of_i64(int64(i))
    }

    for k, v := range vals {
        T.Logf("inserting %v -> %v", k, v)
        m.Insert(big_of_i64(k), v)
    }

    els := m.Elements()
    for i := 0; i < 10; i++ {
        k, v := els[i].key, els[i].val.(Num)
        i_num := big_of_i64(int64(i))
        T.Logf("at index %v found key %v, val %v", i, k, v)

        if (k.Cmp(&i_num) != 0) {
            T.Errorf("key error")
        }

        if ((&v).Cmp(&i_num) != 0) {
            T.Error("value error")
        }
    }

    if len(els) != len(vals) {
        T.Errorf("len(els) = %v != len(vals) = %v", len(els), len(vals))
    }
}

func TestLiteral(T *testing.T) {
    m := new(AddrMap)
    *m = AddrMap_literal(
        LiteralKeyValPair{big_of_i64(10), "ten"},
        LiteralKeyValPair{big_of_i64(30), "thirty"},
    )

    card := m.Cardinality()
    expected := big_of_i64(2)
    if card.Cmp(&expected) != 0 {
        T.Errorf("expected size %v, got %v", expected, card)
    }

    is_found, _ := m.Find(big_of_i64(0))
    if is_found {
        T.Errorf("shouldn't have been able to find value %v", 0)
    }

    is_found, _ = m.Find(big_of_i64(10))
    if !is_found {
        T.Errorf("couldn't find value %v", 10)
    }
}