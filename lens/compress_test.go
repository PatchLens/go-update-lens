package lens

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestZstdCompress(t *testing.T) {
	tests := []struct {
		name  string
		input []byte
	}{
		{"nil_input", nil},
		{"empty_input", nil},
		{"ascii_text", []byte("The quick brown fox jumps over the lazy dog")},
		{"binary_data", []byte{0x00, 0xFF, 0x10, 0x20, 0x7F}},
	}

	for _, tt := range tests {
		input := tt.input
		t.Run(tt.name, func(t *testing.T) {
			if testing.Short() {
				t.Skip("skip in short mode")
			}
			t.Parallel()

			compressed := ZstdCompress(nil, input)
			out, err := ZstdDecompress(nil, compressed)
			require.NoError(t, err)
			assert.Equal(t, input, out)
		})
	}
}

func TestZstdDecompressError(t *testing.T) {
	invalid := []byte{0x42, 0x43, 0x44}
	_, err := ZstdDecompress(nil, invalid)
	require.Error(t, err)
}

// TestSnappyCompress exercises SnappyCompress → SnappyDecompress round-trip.
func TestSnappyCompress(t *testing.T) {
	t.Parallel()

	tests := []struct {
		name  string
		input []byte
	}{
		{"nil input", nil},
		{"empty_input", nil},
		{"ascii_text", []byte("Hello, snappy!")},
		{"binary_data", []byte{0xDE, 0xAD, 0xBE, 0xEF}},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if testing.Short() {
				t.Skip("skip in short mode")
			}

			compressed := SnappyCompress(nil, tt.input)
			out, err := SnappyDecompress(nil, compressed)
			require.NoError(t, err)
			assert.Equal(t, tt.input, out)
		})
	}
}

func TestSnappyDecompressError(t *testing.T) {
	invalid := []byte{0x99, 0x88, 0x77}
	_, err := SnappyDecompress(nil, invalid)
	require.Error(t, err)
}
