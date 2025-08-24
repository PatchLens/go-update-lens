package main

import (
	"encoding/json"
	"flag"
	"log"
	"os"

	"github.com/PatchLens/go-update-lens/lens"
)

func main() {
	log.SetFlags(log.LstdFlags | log.LUTC)

	reportJsonFile := flag.String("json", "modreport.json", "File to output analysis details")
	reportChartsFile := flag.String("charts", "modreport.png", "File to output analysis overview chart image")
	flag.Parse()

	data, err := os.ReadFile(*reportJsonFile)
	if err != nil {
		log.Fatalf("%sFailed to read modreport: %v", lens.ErrorLogPrefix, err)
	}
	var metrics lens.ReportMetrics
	if err := json.Unmarshal(data, &metrics); err != nil {
		log.Fatalf("%sFailed to unmarshal modreport: %v", lens.ErrorLogPrefix, err)
	}

	charts, err := lens.RenderReportChartsFromJson(metrics)
	if err != nil {
		log.Fatalf("%sFailed to render charts: %v", lens.ErrorLogPrefix, err)
	}
	if err = os.WriteFile(*reportChartsFile, charts, 0644); err != nil {
		log.Fatalf("%sFailed to write chart file: %v", lens.ErrorLogPrefix, err)
	}
	log.Println("Report file wrote: " + *reportChartsFile)
}
