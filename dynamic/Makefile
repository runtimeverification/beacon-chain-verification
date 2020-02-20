# Settings
# --------

BUILD_DIR:=.build
DEFN_DIR:=$(BUILD_DIR)/defn

DEPS_DIR:=../deps
K_SUBMODULE:=$(abspath $(DEPS_DIR)/k)
PANDOC_TANGLE_SUBMODULE:=$(DEPS_DIR)/pandoc-tangle

K_RELEASE := $(K_SUBMODULE)/k-distribution/target/release/k
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

.PHONY: all clean                                 \
        deps deps-k deps-tangle deps-media        \
        defn defn-haskell defn-java               \
        build build-haskell build-java            \
        test

.SECONDARY:

all: build

clean:
	rm -rf $(BUILD_DIR)

clean-submodules:
	rm -rf $(DEPS_DIR)/k/submodule.timestamp $(DEPS_DIR)/k/mvn.timestamp $(DEPS_DIR)/pandoc-tangle/submodule.timestamp

# Dependencies
# ------------

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

static_dir  := $(DEFN_DIR)/static
dynamic_dir := $(DEFN_DIR)/dynamic

static_files  := $(patsubst %,$(static_dir)/%,$(k_files))
dynamic_files := $(patsubst %,$(dynamic_dir)/%,$(k_files))

static_kompiled  := $(static_dir)/$(MAIN_DEFN_FILE)-kompiled/definition.kore
dynamic_kompiled := $(dynamic_dir)/$(MAIN_DEFN_FILE)-kompiled/definition.kore

build: build-static build-dynamic
build-static:  $(static_kompiled)
build-dynamic: $(dynamic_kompiled)

# Generate definitions from source files

defn: defn-static defn-dynamic
defn-static:  $(static_files)
defn-dynamic: $(dynamic_files)

static_tangle  := .k:not(.dynamic)
dynamic_tangle := .k

$(static_dir)/%.k: %.md
	@mkdir -p $(static_dir)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(static_tangle)" $< > $@

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

# Dynamic validators model

$(dynamic_kompiled): $(dynamic_files)
	$(K_BIN)/kompile --debug --main-module $(MAIN_MODULE) --backend haskell              \
	                 --syntax-module $(SYNTAX_MODULE) $(dynamic_dir)/$(MAIN_DEFN_FILE).k \
	                 --directory $(dynamic_dir) -I $(dynamic_dir)                        \
	                 --emit-json                                                         \
	                 $(KOMPILE_OPTS)

# Test
# ----

test: test_static test_dynamic

test_static:
	$(K_BIN)/krun -d $(static_dir) test1.abc | diff - test1.abc.out
	$(K_BIN)/krun -d $(static_dir) test2.abc | diff - test2.abc.out
	$(K_BIN)/krun -d $(static_dir) test3.abc | diff - test3.abc.out
	$(K_BIN)/kprove -d $(static_dir) -m VERIFICATION simple-spec.k | diff - simple-spec.k.out

test_dynamic:
	$(K_BIN)/krun -d $(dynamic_dir) test1.abc | diff - test1.abc.out
	$(K_BIN)/krun -d $(dynamic_dir) test2.abc | diff - test2.abc.out
	$(K_BIN)/krun -d $(dynamic_dir) test3.abc | diff - test3.abc.out

