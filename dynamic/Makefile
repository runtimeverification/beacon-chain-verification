# Settings
# --------

BUILD_DIR := .build
DEFN_DIR  := $(BUILD_DIR)/defn

DEPS_DIR                := ../deps
PANDOC_TANGLE_SUBMODULE := $(DEPS_DIR)/pandoc-tangle

K_SUBMODULE := $(abspath $(DEPS_DIR)/k)
K_JAR       := $(K_SUBMODULE)/k-distribution/target/release/k/lib/java/kernel-1.0-SNAPSHOT.jar
ifneq (,$(wildcard $(K_SUBMODULE)/k-distribution/target/release/k/bin/*))
    K_RELEASE ?= $(abspath $(K_SUBMODULE)/k-distribution/target/release/k)
else
    K_RELEASE ?= $(dir $(shell which kompile))..
endif
K_BIN := $(K_RELEASE)/bin
K_LIB := $(K_RELEASE)/lib/kframework
export K_RELEASE

K_BUILD_TYPE := FastBuild

PATH := $(K_BIN):$(PATH)
export PATH

PYTHONPATH := $(K_LIB)
export PYTHONPATH

TANGLER  := $(PANDOC_TANGLE_SUBMODULE)/tangle.lua
LUA_PATH := $(PANDOC_TANGLE_SUBMODULE)/?.lua;;
export TANGLER
export LUA_PATH

.SECONDARY:

.PHONY: all clean clean-submodules

all: build

clean:
	rm -rf $(BUILD_DIR)
	rm -f process-justification-finalization-spec.k process-justification-finalization-lemma.k

# Dependencies
# ------------

.PHONY: deps deps-k deps-tangle

deps: deps-k deps-tangle
deps-k: $(K_JAR)
deps-tangle: $(TANGLER)

$(K_JAR):
	cd $(K_SUBMODULE) && mvn package -DskipTests -Dproject.build.type=$(K_BUILD_TYPE)

# Building
# --------

MAIN_MODULE    := DYNAMIC-ABSTRACT-BEACON-CHAIN
SYNTAX_MODULE  := $(MAIN_MODULE)-SYNTAX
MAIN_DEFN_FILE := dynamic-abstract-beacon-chain

KOMPILE_OPTS      :=

k_files := $(MAIN_DEFN_FILE).k \
           $(MAIN_DEFN_FILE)-syntax.k

concrete_dir := $(DEFN_DIR)/concrete
symbolic_dir := $(DEFN_DIR)/symbolic

concrete_files := $(patsubst %,$(concrete_dir)/%,$(k_files))
symbolic_files := $(patsubst %,$(symbolic_dir)/%,$(k_files))

concrete_kompiled := $(concrete_dir)/verification-kompiled/timestamp
symbolic_kompiled := $(symbolic_dir)/verification-kompiled/timestamp

.PHONY: build build-concrete build-symbolic

build: build-concrete build-symbolic
build-concrete: $(concrete_kompiled)
build-symbolic: $(symbolic_kompiled)

# Generate definitions from source files

.PHONY: defn defn-concrete defn-symbolic

defn: defn-concrete defn-symbolic
defn-concrete: $(concrete_files)
defn-symbolic: $(symbolic_files)

concrete_tangle := .k:not(.symbolic),.concrete
symbolic_tangle := .k:not(.concrete),.symbolic

$(concrete_dir)/%.k: %.md
	@mkdir -p $(concrete_dir)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(concrete_tangle)" $< > $@

$(symbolic_dir)/%.k: %.md
	@mkdir -p $(symbolic_dir)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(symbolic_tangle)" $< > $@

$(concrete_kompiled): $(concrete_files) verification.k
	kompile --debug --main-module VERIFICATION --backend java \
	        --syntax-module $(SYNTAX_MODULE) verification.k   \
	        --directory $(concrete_dir) -I $(concrete_dir)    \
	        --emit-json                                       \
	        $(KOMPILE_OPTS)

$(symbolic_kompiled): $(symbolic_files) verification.k
	kompile --debug --main-module VERIFICATION --backend java \
	        --syntax-module $(SYNTAX_MODULE) verification.k   \
	        --directory $(symbolic_dir) -I $(symbolic_dir)    \
	        --emit-json                                       \
	        $(KOMPILE_OPTS)

# Test
# ----

.PHONY: test test-concrete proof proof-lemmas

test: test-concrete proof proof-lemmas

test-concrete: build-concrete
	krun   -d $(concrete_dir) tests/concrete/test1.abc | diff - tests/concrete/test1.abc.out-java
	krun   -d $(concrete_dir) tests/concrete/test2.abc | diff - tests/concrete/test2.abc.out-java
	krun   -d $(concrete_dir) tests/concrete/test3.abc | diff - tests/concrete/test3.abc.out-java

proof: build-symbolic process-justification-finalization-spec.k process-justification-finalization-lemma.k
	kprove -d $(symbolic_dir) -m VERIFICATION -w none process-block-spec.k                            | diff - tests/success.out
	kprove -d $(symbolic_dir) -m VERIFICATION -w none process-epoch-spec.k                            | diff - tests/success.out
	kprove -d $(symbolic_dir) -m VERIFICATION -w none process-justification-finalization-spec.k       | diff - tests/success.out
	kprove -d $(symbolic_dir) -m VERIFICATION -w none process-slots-spec.k                            | diff - tests/success.out

proof-lemmas: build-symbolic
	kprove -d $(symbolic_dir) -m VERIFICATION -w none process-attestation-spec.k                      | diff - tests/success.out
	kprove -d $(symbolic_dir) -m VERIFICATION -w none process-deposit-spec.k                          | diff - tests/success.out
	kprove -d $(symbolic_dir) -m VERIFICATION -w none process-rewards-penalties-spec.k                | diff - tests/success.out
	kprove -d $(symbolic_dir) -m VERIFICATION -w none process-slashing-spec.k                         | diff - tests/success.out
	kprove -d $(symbolic_dir) -m VERIFICATION -w none process-validator-activation-eligibility-spec.k | diff - tests/success.out
	kprove -d $(symbolic_dir) -m VERIFICATION -w none process-validator-activation-spec.k             | diff - tests/success.out
	kprove -d $(symbolic_dir) -m VERIFICATION -w none process-validator-ejection-spec.k               | diff - tests/success.out
	kprove -d $(symbolic_dir) -m VERIFICATION -w none process-validator-exit-spec.k                   | diff - tests/success.out
	kprove -d $(symbolic_dir) -m VERIFICATION -w none process-validator-updates-spec.k                | diff - tests/success.out

process-justification-finalization-spec.k: process-justification-finalization-spec.md
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:".k:not(.lemma),.proof" $< > $@

process-justification-finalization-lemma.k: process-justification-finalization-spec.md
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:".k:not(.proof),.lemma" $< > $@
