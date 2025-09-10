package main

import (
	"log"
	"net/http"
	_ "net/http/pprof"

	"github.com/PatchLens/go-update-lens/lens"
	"github.com/PatchLens/go-update-lens/lens/cmd"
)

const pprofDebug = false

func main() {
	log.SetFlags(log.LstdFlags)

	if pprofDebug {
		go func() {
			if err := http.ListenAndServe("localhost:6060", nil); err != nil {
				log.Printf("pprof server failure: %v", err)
			}
		}()
	}

	config, err := cmd.ParseFlags(nil) // No custom flags for standard modlens
	if err != nil {
		log.Fatalf("%s%v", lens.ErrorLogPrefix, err)
	}

	if err := lens.NewAnalysisEngine(config).Run(); err != nil {
		log.Fatalf("%s%v", lens.ErrorLogPrefix, err)
	}
}
