export GO111MODULE = on

.PHONY: default build test test-all test-cover lint setup

build:
	@mkdir -p bin
	for dir in $$(find . -type f -name 'main.go' | xargs -n 1 dirname); do \
	base=$$(basename $$dir); \
	go build -o bin/$$base $$dir; \
	done

clean:
	rm -rf bin/

test:
	go test -short ./...

test-all:
	go test -race -cover ./...

test-cover:
	go test -race -coverprofile=test.out ./... && go tool cover --html=test.out

lint:
	golangci-lint run --timeout=600s --enable=asasalint,asciicheck,bidichk,contextcheck,decorder,durationcheck,errorlint,exptostd,fatcontext,gocheckcompilerdirectives,gochecksumtype,goconst,gofmt,goimports,gosmopolitan,grouper,iface,importas,mirror,misspell,perfsprint,prealloc,reassign,recvcheck,sloglint,testifylint,unconvert,wastedassign,whitespace && go vet ./...

setup:
	go install github.com/avito-tech/go-mutesting/cmd/go-mutesting@v0.0.0-20250418092011-3ce278f4e19f

