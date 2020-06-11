# Settings
# --------

BUILD_DIR := .build
DEFN_DIR  := $(BUILD_DIR)/defn

DEPS_DIR                := ../deps
PANDOC_TANGLE_SUBMODULE := $(DEPS_DIR)/pandoc-tangle

K_SUBMODULE := $(abspath $(DEPS_DIR)/k)

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

K_JAR := $(K_SUBMODULE)/k-distribution/target/release/k/lib/java/kernel-1.0-SNAPSHOT.jar

.PHONY: deps deps-k

deps: deps-k
deps-k: $(K_JAR)

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

SOURCE_MD_FILES    := dynamic-abstract-beacon-chain        \
                      dynamic-abstract-beacon-chain-syntax
SOURCE_K_FILES     := verification
EXTRA_SOURCE_FILES :=

ALL_FILES          := $(patsubst %, %.md, $(SOURCE_MD_FILES)) $(patsubst %, %.k, $(SOURCE_K_FILES)) $(EXTRA_SOURCE_FILES)

tangle_concrete := k & (concrete | ! symbolic)
tangle_symbolic := k & (symbolic | ! concrete)

.PHONY: build build-concrete build-symbolic

build: build-concrete build-symbolic

KOMPILE_OPTS += --emit-json

ifneq (,$(RELEASE))
    KOMPILE_OPTS += -O3
endif

KOMPILE_CONCRETE_OPTS :=

KOMPILE_CONCRETE := kompile --debug --backend java --md-selector "$(tangle_concrete)" \
                    $(KOMPILE_OPTS) $(KOMPILE_CONCRETE_OPTS)

KOMPILE_SYMBOLIC_OPTS :=

KOMPILE_SYMBOLIC := kompile --debug --backend java --md-selector "$(tangle_symbolic)" \
                    $(KOMPILE_OPTS) $(KOMPILE_SYMBOLIC_OPTS)

### Concrete Backend

concrete_dir           := $(DEFN_DIR)/concrete
concrete_files         := $(ALL_FILES)
concrete_main_module   := VERIFICATION
concrete_syntax_module := DYNAMIC-ABSTRACT-BEACON-CHAIN-SYNTAX
concrete_main_file     := verification.k
concrete_kompiled      := $(concrete_dir)/verification-kompiled/timestamp

build-concrete: $(concrete_kompiled)

$(concrete_kompiled): $(concrete_files)
	$(KOMPILE_CONCRETE) $(concrete_main_file)         \
	        --main-module $(concrete_main_module)     \
	        --syntax-module $(concrete_syntax_module) \
	        --directory $(concrete_dir)               \
	        -I $(CURDIR)

### Symbolic Backend


symbolic_dir           := $(DEFN_DIR)/symbolic
symbolic_files         := $(ALL_FILES)
symbolic_main_module   := VERIFICATION
symbolic_syntax_module := DYNAMIC-ABSTRACT-BEACON-CHAIN-SYNTAX
symbolic_main_file     := verification.k
symbolic_kompiled      := $(symbolic_dir)/verification-kompiled/timestamp

build-symbolic: $(symbolic_kompiled)

$(symbolic_kompiled): $(symbolic_files)
	$(KOMPILE_SYMBOLIC) $(symbolic_main_file)         \
	        --main-module $(symbolic_main_module)     \
	        --syntax-module $(symbolic_syntax_module) \
	        --directory $(symbolic_dir)               \
	        -I $(CURDIR)

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

%-spec.k.prove: %-spec.k $(symbolic_kompiled) process-justification-finalization-spec.k process-justification-finalization-lemma.k
	kprove -d $(symbolic_dir) -m VERIFICATION -w none $< > $<.out
	$(CHECK) $<.out tests/success.out
	rm $<.out

test-concrete: $(concrete_tests:=.run)
test-prove:    $(prove_tests:=.prove)

process-justification-finalization-spec.k: process-justification-finalization-spec.md $(TANGLER)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:".k:not(.lemma),.proof" $< > $@

process-justification-finalization-lemma.k: process-justification-finalization-spec.md $(TANGLER)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:".k:not(.proof),.lemma" $< > $@
