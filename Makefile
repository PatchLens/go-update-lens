export GO111MODULE = on

.PHONY: default build build-cross test test-all test-cover lint setup

build:
	@mkdir -p bin
	for dir in $$(find . -type f -name 'main.go' | xargs -n 1 dirname); do \
	base=$$(basename $$dir); \
	go build -ldflags="-w -s" -o bin/$$base $$dir; \
	done

PLATFORMS := linux-amd64 linux-arm64 darwin-amd64 darwin-arm64

build-cross:
	@mkdir -p bin
	@for platform in $(PLATFORMS); do \
		os=$$(echo $$platform | cut -d'-' -f1); \
		arch=$$(echo $$platform | cut -d'-' -f2); \
		for dir in $$(find . -type f -name 'main.go' | xargs -n 1 dirname); do \
			base=$$(basename $$dir); \
			ext=""; \
			if [ "$$os" = "windows" ]; then ext=".exe"; fi; \
			echo "Building $$base for $$os/$$arch..."; \
			GOOS=$$os GOARCH=$$arch go build -ldflags="-w -s" -o bin/$$base-$$platform$$ext $$dir; \
		done; \
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
	golangci-lint run --timeout=600s && go vet ./...

setup:
	go install github.com/avito-tech/go-mutesting/cmd/go-mutesting@v0.0.0-20250418092011-3ce278f4e19f

