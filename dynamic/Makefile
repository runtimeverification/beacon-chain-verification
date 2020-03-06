# Settings
# --------

BUILD_DIR:=.build
DEFN_DIR:=$(BUILD_DIR)/defn

DEPS_DIR:=../deps
K_SUBMODULE:=$(abspath $(DEPS_DIR)/k)
PANDOC_TANGLE_SUBMODULE:=$(DEPS_DIR)/pandoc-tangle

K_RELEASE ?= $(K_SUBMODULE)/k-distribution/target/release/k
K_BIN     := $(K_RELEASE)/bin
K_LIB     := $(K_RELEASE)/lib
export K_RELEASE

K_BUILD_TYPE := FastBuild

PATH:=$(K_BIN):$(PATH)
export PATH

PYTHONPATH:=$(K_LIB)
export PYTHONPATH

TANGLER:=$(PANDOC_TANGLE_SUBMODULE)/tangle.lua
LUA_PATH:=$(PANDOC_TANGLE_SUBMODULE)/?.lua;;
export TANGLER
export LUA_PATH

.SECONDARY:

.PHONY: all clean clean-submodules

all: build

clean:
	rm -rf $(BUILD_DIR)

clean-submodules:
	rm -rf $(DEPS_DIR)/k/submodule.timestamp $(DEPS_DIR)/k/mvn.timestamp $(DEPS_DIR)/pandoc-tangle/submodule.timestamp

# Dependencies
# ------------

.PHONY: deps deps-k deps-tangle

deps: deps-k deps-tangle
deps-k: $(K_SUBMODULE)/mvn.timestamp
deps-tangle: $(PANDOC_TANGLE_SUBMODULE)/submodule.timestamp

%/submodule.timestamp:
	git submodule update --init --recursive -- $*
	touch $@

$(K_SUBMODULE)/mvn.timestamp: $(K_SUBMODULE)/submodule.timestamp
	cd $(K_SUBMODULE) && mvn package -DskipTests -Dproject.build.type=$(K_BUILD_TYPE)
	touch $(K_SUBMODULE)/mvn.timestamp

# Building
# --------

MAIN_MODULE    := DYNAMIC-ABSTRACT-BEACON-CHAIN
SYNTAX_MODULE  := $(MAIN_MODULE)-SYNTAX
MAIN_DEFN_FILE := dynamic-abstract-beacon-chain

KOMPILE_OPTS      :=

k_files := $(MAIN_DEFN_FILE).k          \
           $(MAIN_DEFN_FILE)-syntax.k

static_dir              := $(DEFN_DIR)/static
static_verification_dir := $(DEFN_DIR)/static-verification
static_java_dir         := $(DEFN_DIR)/static-java
dynamic_dir             := $(DEFN_DIR)/dynamic

static_files      := $(patsubst %,$(static_dir)/%,$(k_files))
static_java_files := $(patsubst %,$(static_java_dir)/%,$(k_files))
dynamic_files     := $(patsubst %,$(dynamic_dir)/%,$(k_files))

static_kompiled              := $(static_dir)/$(MAIN_DEFN_FILE)-kompiled/definition.kore
static_verification_kompiled := $(static_verification_dir)/verification-kompiled/definition.kore
static_java_kompiled         := $(static_java_dir)/$(MAIN_DEFN_FILE)-kompiled/timestamp
dynamic_kompiled             := $(dynamic_dir)/$(MAIN_DEFN_FILE)-kompiled/definition.kore

.PHONY: build build-static build-static-verification build-static-java build-dynamic

build: build-static build-static-java build-dynamic
build-static:              $(static_kompiled)
build-static-verification: $(static_verification_kompiled)
build-static-java:         $(static_java_kompiled)
build-dynamic:             $(dynamic_kompiled)

# Generate definitions from source files

.PHONY: defn defn-static defn-static-java defn-dynamic

defn: defn-static defn-static-java defn-dynamic
defn-static:      $(static_files)
defn-static-java: $(static_java_files)
defn-dynamic:     $(dynamic_files)

static_tangle      := .k:not(.dynamic):not(.kast)
static_java_tangle := .k:not(.dynamic):not(.kore)
dynamic_tangle     := .k:not(.kast)

$(static_dir)/%.k: %.md
	@mkdir -p $(static_dir)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(static_tangle)" $< > $@

$(static_java_dir)/%.k: %.md
	@mkdir -p $(static_java_dir)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(static_java_tangle)" $< > $@

$(dynamic_dir)/%.k: %.md
	@mkdir -p $(dynamic_dir)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(dynamic_tangle)" $< > $@

# Static validators model

$(static_kompiled): $(static_files)
	$(K_BIN)/kompile --debug --main-module $(MAIN_MODULE) --backend haskell             \
	                 --syntax-module $(SYNTAX_MODULE) $(static_dir)/$(MAIN_DEFN_FILE).k \
	                 --directory $(static_dir) -I $(static_dir)                         \
	                 --emit-json                                                        \
	                 $(KOMPILE_OPTS)

$(static_verification_kompiled): $(static_files) verification.k
	$(K_BIN)/kompile --debug --main-module VERIFICATION --backend haskell    \
	                 --syntax-module $(SYNTAX_MODULE) verification.k         \
	                 --directory $(static_verification_dir) -I $(static_dir) \
	                 --emit-json                                             \
	                 $(KOMPILE_OPTS)

$(static_java_kompiled): $(static_java_files)
	$(K_BIN)/kompile --debug --main-module $(MAIN_MODULE) --backend java                     \
	                 --syntax-module $(SYNTAX_MODULE) $(static_java_dir)/$(MAIN_DEFN_FILE).k \
	                 --directory $(static_java_dir) -I $(static_java_dir)                    \
	                 --emit-json                                                             \
	                 $(KOMPILE_OPTS)

# Dynamic validators model

$(dynamic_kompiled): $(dynamic_files)
	$(K_BIN)/kompile --debug --main-module $(MAIN_MODULE) --backend haskell              \
	                 --syntax-module $(SYNTAX_MODULE) $(dynamic_dir)/$(MAIN_DEFN_FILE).k \
	                 --directory $(dynamic_dir) -I $(dynamic_dir)                        \
	                 --emit-json                                                         \
	                 $(KOMPILE_OPTS)

# Test
# ----

.PHONY: test test-static test-static-java test-dynamic

test: test-static test-static-java test-dynamic

test-static: build-static
	$(K_BIN)/krun   -d $(static_dir) tests/concrete/test1.abc | diff - tests/concrete/test1.abc.out
	$(K_BIN)/krun   -d $(static_dir) tests/concrete/test2.abc | diff - tests/concrete/test2.abc.out
	$(K_BIN)/krun   -d $(static_dir) tests/concrete/test3.abc | diff - tests/concrete/test3.abc.out
#	$(K_BIN)/kprove -d $(static_dir) -m VERIFICATION tests/symbolic/simple-spec.k | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_dir) -m VERIFICATION tests/symbolic/a-spec.k  | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_dir) -m VERIFICATION tests/symbolic/b-spec.k  | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_dir) -m VERIFICATION tests/symbolic/c-spec.k  | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_dir) -m VERIFICATION tests/symbolic/d-spec.k  | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_dir) -m VERIFICATION tests/symbolic/e-spec.k  | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_dir) -m VERIFICATION tests/symbolic/f-spec.k  | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_dir) -m VERIFICATION tests/symbolic/f2-spec.k | diff - tests/success.out
#	$(K_BIN)/kprove -d $(static_dir) -m VERIFICATION tests/symbolic/g-spec.k  | diff - tests/success.out

test-static-java: build-static-java
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none process-justification-finalization-spec.k   | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none process-slots-base0-spec.k                  | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none process-slots-base1-spec.k                  | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none process-slots-inductive-spec.k              | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/simple-spec.k                | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/process-justification-spec.k | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/process-finalization-spec.k  | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/a-spec.k   | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/b-spec.k   | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/c-spec.k   | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/d-spec.k   | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/e-spec.k   | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/f-spec.k   | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/f2-spec.k  | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/g-spec.k   | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/g2-spec.k  | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/h-spec.k   | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/i-spec.k   | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/j-spec.k   | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/k0-spec.k  | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/k1a-spec.k | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/k1b-spec.k | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/k2a-spec.k | diff - tests/success.out
	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/k2b-spec.k | diff - tests/success.out
#	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/kn1-spec.k | diff - tests/success.out
#	$(K_BIN)/kprove -d $(static_java_dir) -m VERIFICATION -w none tests/symbolic/kn2-spec.k | diff - tests/success.out

test-dynamic: build-dynamic
	$(K_BIN)/krun   -d $(dynamic_dir) tests/concrete/test1.abc | diff - tests/concrete/test1.abc.out
	$(K_BIN)/krun   -d $(dynamic_dir) tests/concrete/test2.abc | diff - tests/concrete/test2.abc.out
	$(K_BIN)/krun   -d $(dynamic_dir) tests/concrete/test3.abc | diff - tests/concrete/test3.abc.out

