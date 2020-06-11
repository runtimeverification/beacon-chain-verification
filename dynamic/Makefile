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

ifneq ($(RELEASE),)
    K_BUILD_TYPE := FastBuild
else
    K_BUILD_TYPE := Debug
endif

$(K_JAR):
	cd $(K_SUBMODULE) && mvn package -DskipTests -Dproject.build.type=$(K_BUILD_TYPE)

# Building
# --------

MAIN_MODULE    := DYNAMIC-ABSTRACT-BEACON-CHAIN
SYNTAX_MODULE  := $(MAIN_MODULE)-SYNTAX
MAIN_DEFN_FILE := dynamic-abstract-beacon-chain

KOMPILE_OPTS :=

k_files := $(MAIN_DEFN_FILE).k \
           $(MAIN_DEFN_FILE)-syntax.k

.PHONY: defn  defn-concrete  defn-symbolic  \
        build build-concrete build-symbolic \
        split-proof

defn:  defn-concrete  defn-symbolic
build: build-concrete build-symbolic split-proof

split-proof: process-justification-finalization-spec.k process-justification-finalization-lemma.k

process-justification-finalization-spec.k: process-justification-finalization-spec.md
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:".k:not(.lemma),.proof" $< > $@

process-justification-finalization-lemma.k: process-justification-finalization-spec.md
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:".k:not(.proof),.lemma" $< > $@

### Concrete Backend

concrete_dir      := $(DEFN_DIR)/concrete
concrete_files    := $(patsubst %,$(concrete_dir)/%,$(k_files))
concrete_kompiled := $(concrete_dir)/verification-kompiled/timestamp
concrete_tangle   := .k:not(.symbolic),.concrete

defn-concrete: $(concrete_files)
build-concrete: $(concrete_kompiled)

$(concrete_dir)/%.k: %.md
	@mkdir -p $(concrete_dir)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(concrete_tangle)" $< > $@

$(concrete_kompiled): $(concrete_files) verification.k
	kompile --debug --main-module VERIFICATION --backend java \
	        --syntax-module $(SYNTAX_MODULE) verification.k   \
	        --directory $(concrete_dir) -I $(concrete_dir)    \
	        --emit-json                                       \
	        $(KOMPILE_OPTS)

### Symbolic Backend

symbolic_dir      := $(DEFN_DIR)/symbolic
symbolic_files    := $(patsubst %,$(symbolic_dir)/%,$(k_files))
symbolic_kompiled := $(symbolic_dir)/verification-kompiled/timestamp
symbolic_tangle   := .k:not(.concrete),.symbolic

defn-symbolic:  $(symbolic_files)
build-symbolic: $(symbolic_kompiled)

$(symbolic_dir)/%.k: %.md
	@mkdir -p $(symbolic_dir)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(symbolic_tangle)" $< > $@

$(symbolic_kompiled): $(symbolic_files) verification.k
	kompile --debug --main-module VERIFICATION --backend java \
	        --syntax-module $(SYNTAX_MODULE) verification.k   \
	        --directory $(symbolic_dir) -I $(symbolic_dir)    \
	        --emit-json                                       \
	        $(KOMPILE_OPTS)

# Test
# ----

CHECK := git --no-pager diff --no-index --ignore-all-space -R

.PHONY: test test-concrete test-prove

test: test-concrete test-prove

concrete_tests := $(wildcard tests/concrete/*.abc)

tests/concrete/%.abc.run: tests/concrete/%.abc $(concrete_kompiled)
	krun -d $(concrete_dir) $< > $<.out
	$(CHECK) $<.out $<.expected
	rm $<.out

prove_tests := $(wildcard *-spec.k)

%-spec.k.prove: %-spec.k $(symbolic_kompiled)
	kprove -d $(symbolic_dir) -m VERIFICATION -w none $< > $<.out
	$(CHECK) $<.out tests/success.out
	rm $<.out

test-concrete: $(concrete_tests:=.run)
test-prove:    $(prove_tests:=.prove)
