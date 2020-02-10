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

haskell_dir       := $(DEFN_DIR)/haskell
java_dir          := $(DEFN_DIR)/java

haskell_files := $(patsubst %,$(haskell_dir)/%,$(k_files))
java_files    := $(patsubst %,$(java_dir)/%,$(k_files))

haskell_kompiled := $(haskell_dir)/$(MAIN_DEFN_FILE)-kompiled/definition.kore
java_kompiled    := $(java_dir)/$(MAIN_DEFN_FILE)-kompiled/timestamp

build: build-haskell build-java
build-haskell: $(haskell_kompiled)
build-java:    $(java_kompiled)

# Generate definitions from source files

defn: defn-haskell defn-java
defn-haskell: $(haskell_files)
defn-java:    $(java_files)

concrete_tangle := .k:not(.symbolic),.concrete
symbolic_tangle := .k:not(.concrete),.symbolic

$(haskell_dir)/%.k: %.md
	@mkdir -p $(haskell_dir)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(symbolic_tangle)" $< > $@

$(java_dir)/%.k: %.md
	@mkdir -p $(java_dir)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(symbolic_tangle)" $< > $@

# Haskell Backend

$(haskell_kompiled): $(haskell_files)
	$(K_BIN)/kompile --debug --main-module $(MAIN_MODULE) --backend haskell              \
	                 --syntax-module $(SYNTAX_MODULE) $(haskell_dir)/$(MAIN_DEFN_FILE).k \
	                 --directory $(haskell_dir) -I $(haskell_dir)                        \
	                 --emit-json                                                         \
	                 $(KOMPILE_OPTS)

# Java Backend

$(java_kompiled): $(java_files)
	$(K_BIN)/kompile --debug --main-module $(MAIN_MODULE) --backend java              \
	                 --syntax-module $(SYNTAX_MODULE) $(java_dir)/$(MAIN_DEFN_FILE).k \
	                 --directory $(java_dir) -I $(java_dir)							  \
	                 --emit-json                                                      \
	                 $(KOMPILE_OPTS)

# Test
# ----

test:
	$(K_BIN)/krun -d $(haskell_dir) test1.abc | diff - test1.abc.out
	$(K_BIN)/krun -d $(haskell_dir) test2.abc | diff - test2.abc.out
	$(K_BIN)/krun -d $(haskell_dir) test3.abc | diff - test3.abc.out

