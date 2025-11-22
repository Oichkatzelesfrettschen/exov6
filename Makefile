# Master Makefile for ExoV6

BUILD_DIR ?= build
GENERATOR ?= Ninja
CMAKE_ARGS ?=

.PHONY: all clean test perf unikernel posix-tests

all: $(BUILD_DIR)/build.ninja
	@cmake --build $(BUILD_DIR)

$(BUILD_DIR)/build.ninja:
	@mkdir -p $(BUILD_DIR)
	@cd $(BUILD_DIR) && cmake -G $(GENERATOR) $(CMAKE_ARGS) ..

clean:
	@rm -rf $(BUILD_DIR)

test: all
	@cd $(BUILD_DIR) && ctest --output-on-failure

perf: all
	@cd $(BUILD_DIR) && ctest -L perf --output-on-failure

unikernel:
	@mkdir -p $(BUILD_DIR)
	@cd $(BUILD_DIR) && cmake -G $(GENERATOR) -DUNIKERNEL=ON ..
	@cmake --build $(BUILD_DIR)

posix-tests: all
	@echo "Running POSIX coverage verification..."
	@cd $(BUILD_DIR) && ctest -R posix --output-on-failure
