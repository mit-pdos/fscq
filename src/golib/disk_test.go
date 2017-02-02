package fscq

import (
	"testing"
)

func TestBufferDeepCopyPreservesData(T *testing.T) {
	b := New_Buffer(240)

	// this is not the way client code is supposed to use buffers
	b.data = make([]byte, 15)
	for i := 0; i < 15; i++ {
		b.data[i] = byte(i)
	}

	c := New_Buffer(240)
	b.DeepCopy(&c)

	for i := 0; i < 15; i++ {
		if c.data[i] != byte(i) {
			T.Errorf("expected %v, got %v at index %v", i, c.data[i], i)
		}
	}

}
