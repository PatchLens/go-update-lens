package lens

import (
	"runtime"

	"github.com/klauspost/compress/s2"
	"github.com/klauspost/compress/snappy"
	"github.com/klauspost/compress/zstd"
)

// ZstdCompress compresses a byte slice using zstd and returns the compressed data.
func ZstdCompress(dst, data []byte) []byte {
	encOpts := []zstd.EOption{
		zstd.WithEncoderLevel(zstd.SpeedBetterCompression),
	}
	if len(data) > 1024*1024*100 { // update options for large payloads
		encOpts = append(encOpts, zstd.WithEncoderConcurrency(max(1, runtime.NumCPU()/2)))
	}
	encoder, err := zstd.NewWriter(nil, encOpts...)
	if err != nil {
		panic(err) // theoretically not possible
	}
	defer encoder.Close()

	return encoder.EncodeAll(data, dst)
}

// ZstdDecompress decompresses a zstd-compressed byte slice and returns the original data.
func ZstdDecompress(dst, data []byte) ([]byte, error) {
	decoder, err := zstd.NewReader(nil)
	if err != nil {
		return nil, err
	}
	defer decoder.Close()

	return decoder.DecodeAll(data, dst)
}

// SnappyCompress compresses a byte slice using snappy and returns the compressed data.
func SnappyCompress(dst, data []byte) []byte {
	return s2.EncodeSnappyBest(dst, data)
}

// SnappyDecompress decompresses a snappy-compressed byte slice and returns the decompressed data.
// Returns nil if the input is invalid or decompression fails.
func SnappyDecompress(dst, data []byte) ([]byte, error) {
	return snappy.Decode(dst, data)
}
