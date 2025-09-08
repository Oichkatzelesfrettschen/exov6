# C17 Test Suite Makefile
CC = clang
CFLAGS = -std=c17 -Wall -Werror -O2 -I../../include -I../../kernel
LDFLAGS = 

# Find all test files
TESTS = $(wildcard test_*.c)
BINARIES = $(TESTS:.c=)

all: $(BINARIES)

%: %.c
	$(CC) $(CFLAGS) $< -o $@ $(LDFLAGS)

run: all
	@for test in $(BINARIES); do \
		echo "Running $$test..."; \
		./$$test || exit 1; \
	done

clean:
	rm -f $(BINARIES) *.o

.PHONY: all run clean
