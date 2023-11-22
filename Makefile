LEANS = $(shell find Logic -name '*.lean')
TESTS = $(wildcard test/*.lean)

.PHONY: build clean

build: Logic.lean
	lake build

clean:
	-rm -fr .lake/build

Logic.lean: $(LEANS)
	find Logic -name \*.lean | env LC_ALL=C sort | sed 's/.lean//;s/\//./g;s/^/import /' > Logic.lean
