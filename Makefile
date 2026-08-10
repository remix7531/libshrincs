# ============================================================================
# libshrincs build system.
#
# User-facing targets:
#   make              build the C library only (build/libwots.a)
#                      for the Clight ASTs use `make extract`
#   make test         C library + self-consistency / tamper tests + SHA-256 KATs
#   make extract      run clightgen (C -> Clight AST) for vst-prove
#   make vst-prove    VST / Rocq proofs (implies extract)
#   make ssprove-prove  SSProve / Rocq native WOTS+C one-time-security proof
#   make fxmss-prove  SSProve / Rocq abstract FXMSS EU-CMA proof (no VST/clightgen)
#   make prove        all proof trees
#   make audit        vst-prove + ssprove-prove + fxmss-prove + the combined
#                      honesty gate (assumptions/check.sh: per-tree gates +
#                      trust-surface report)
#   make check        full CI gate: static + sanitizers + CompCert + ctgrind +
#                      extract + prove + audit
#   make check-ct     ctgrind: constant-time check on shrincs_wots_pubkey_gen + shrincs_wots_sign
#                      under gcc, clang, and CompCert
#   make format       reformat include/ + src/ + test/ in place (clang-format)
#   make check-format CI gate: fails if any file isn't clang-format-clean
#   make clean
#
# Knobs:
#   CC=ccomp        build with CompCert
#   CFLAGS=...      override compiler flags
#
# The Rocq/VST/SSProve proof build lives entirely under proof/ (see
# proof/Makefile); the extract/vst-prove/ssprove-prove/fxmss-prove/prove/
# audit targets below just route `make -C proof <target>` so the targets
# listed above behave identically whether invoked from here or from proof/
# directly.
# ============================================================================

# ----- Configuration --------------------------------------------------------

CC    ?= gcc
AR    ?= ar

ifeq ($(CC),ccomp)
  # ccomp-only knobs:
  #   -Wno-unknown-pragmas    silences gcc-specific #pragma in stdint.h
  #   -Wp,-w                  silences preprocessor warnings.  The big
  #                           one is glibc features.h's #warning about
  #                           _FORTIFY_SOURCE needing GCC >=4.1; the Nix
  #                           hardening wrapper injects -D_FORTIFY_SOURCE
  #                           after our flags so -U_FORTIFY_SOURCE can't
  #                           win the race -- suppress at the cpp level.
  CCOMP_SUPPRESS = -Wno-unknown-pragmas -Wp,-w
  CFLAGS = -std=c99 -Wall -O2 -Isrc -Iinclude $(CCOMP_SUPPRESS)
else
  CCOMP_SUPPRESS =
  CFLAGS = -std=c99 -Wall -Wextra -Wpedantic -Werror -O2 -Isrc -Iinclude
endif

# Sanitizer flags for `make check-asan`.
ASAN_CFLAGS = -std=c99 -Wall -Wextra -Wpedantic -Werror -O1 -g \
              -fsanitize=address,undefined -fno-omit-frame-pointer \
              -fno-sanitize-recover=all -Isrc -Iinclude

# MSan flags for `make check-msan`.  Clang-only; needs all linked code
# instrumented, so we only run it against the pure C test path.
MSAN_CFLAGS = -std=c99 -Wall -Wextra -Wpedantic -Werror -O1 -g \
              -fsanitize=memory -fsanitize-memory-track-origins=2 \
              -fno-omit-frame-pointer -fno-sanitize-recover=all -Isrc -Iinclude

# clang-tidy bypasses the Nix gcc-wrapper that injects glibc's include path,
# so discover the system include dirs from gcc and pass them as -isystem.
# Lazy `=` so the $(CC) probe runs only when check-tidy uses it -- a bare
# `make clean` shouldn't pay for it.
SYS_INCLUDES = $(shell echo | $(CC) -E -Wp,-v -xc - 2>&1 \
                  | sed -n 's|^ \(/.*\)|-isystem \1|p')

# ----- Artifact paths -------------------------------------------------------

BUILD = build

# C library
LIB      = $(BUILD)/libwots.a
LIB_SRCS = src/wots.c src/thash.c src/sha256.c src/util.c
LIB_OBJS = $(patsubst src/%.c,$(BUILD)/src/%.o,$(LIB_SRCS))
LIB_HDRS = include/wots.h include/thash.h include/sha256.h include/util.h

# Test binaries
MAIN    = $(BUILD)/test/main
CTGRIND = $(BUILD)/test/ctgrind

# valgrind ships memcheck.h via pkg-config.  Lazy so `make clean` and bare
# `make` don't pay the pkg-config call when ctgrind isn't being touched.
VALGRIND_CFLAGS = $(shell pkg-config --cflags valgrind 2>/dev/null)

# Compiler for the ctgrind harness itself.  Defaults to $(CC) so the
# harness matches the library; check-ct-ccomp overrides it to gcc since
# CompCert cannot accept valgrind.h's client-request inline asm.
HARNESS_CC ?= $(CC)

# Cyan banner; blue success line.  Disable colors when NO_COLOR is set
# (https://no-color.org/) so CI logs stay readable.
ifeq ($(strip $(NO_COLOR)),)
  BANNER  = printf '\n\033[1;36m══ %s ══\033[0m\n'
  SUCCESS = printf '\033[1;34m✓ %s\033[0m\n'
else
  BANNER  = printf '\n══ %s ══\n'
  SUCCESS = printf '✓ %s\n'
endif

# ----- Top-level targets ----------------------------------------------------

.PHONY: all lib test extract vst-prove ssprove-prove fxmss-prove prove audit clean gen-vectors \
        check-asan check-msan check-ccomp \
        check-ct check-ct-gcc check-ct-clang check-ct-ccomp \
        check check-no-prove check-tidy check-fanalyzer format check-format \
        main-bin ct-bin

all: lib

lib:     $(LIB)

extract:
	@$(MAKE) --no-print-directory -C proof extract

test: $(MAIN)
	./$(MAIN)

# Regenerate the committed WOTS+C KAT vectors from the shrincs-bip
# reference.  A manual developer step -- the .kat is committed, so
# `make test` / CI need neither Python nor a shrincs-bip checkout.
# Override the reference path with SHRINCS=/path/to/shrincs.py.
SHRINCS ?= ../shrincs-bip/impl/shrincs.py
gen-vectors:
	python3 test/wots/gen_vectors.py --shrincs $(SHRINCS) -o test/wots/vectors/wotsc.kat

vst-prove:
	@$(MAKE) --no-print-directory -C proof vst-prove

ssprove-prove:
	@$(MAKE) --no-print-directory -C proof ssprove-prove

fxmss-prove:
	@$(MAKE) --no-print-directory -C proof fxmss-prove

prove:
	@$(MAKE) --no-print-directory -C proof prove

# `make audit` is the combined honesty gate for all proof trees; see
# proof/Makefile's `audit` target for the full recipe and its rationale.
audit:
	@$(MAKE) --no-print-directory -C proof audit

# ----- Quality gates --------------------------------------------------------
# Each sub-target builds in its own BUILD=build/<config> subdir so they
# can run side-by-side without clobbering each other's objects.  No
# sub-target cleans on its own; `make clean` removes everything and
# `make check` does a single clean upfront.

# `check-no-prove` is the full quality gate minus the Rocq/VST proofs, so
# `prove`+`audit` can run as separate steps while still keeping the rest
# of the gate hard-failing.
check-no-prove:
	@$(MAKE) --no-print-directory clean
	@$(MAKE) --no-print-directory check-format
	@$(MAKE) --no-print-directory check-tidy
	@$(MAKE) --no-print-directory check-fanalyzer
	@$(MAKE) --no-print-directory check-asan
	@$(MAKE) --no-print-directory check-msan
	@$(MAKE) --no-print-directory check-ccomp
	@$(MAKE) --no-print-directory check-ct
	@$(BANNER) "extract (clightgen)"
	@$(MAKE) --no-print-directory extract

check: check-no-prove
	@$(BANNER) "prove (Rocq + VST + SSProve)"
	@$(MAKE) --no-print-directory prove
	@$(BANNER) "audit (honesty gate)"
	@$(MAKE) --no-print-directory audit

check-tidy:
	@$(BANNER) "clang-tidy"
	@OUT=$$(clang-tidy --quiet --warnings-as-errors='*' \
	    $(LIB_SRCS) $(TEST_SRCS) -- \
	    -std=c99 -Isrc -Iinclude -Itest -D_DEFAULT_SOURCE=1 $(SYS_INCLUDES) 2>&1) \
	    || { echo "$$OUT"; exit 1; }

# All C sources clang-format governs.  Broader than check-tidy's file list
# (includes headers and ctgrind.c, which check-tidy deliberately excludes).
FMT_SRCS = $(LIB_SRCS) $(LIB_HDRS) $(TEST_SRCS) $(TEST_HDRS) test/ctgrind/ctgrind.c

format:
	@$(BANNER) "clang-format (in place)"
	@clang-format -i --style=file $(FMT_SRCS)

check-format:
	@$(BANNER) "clang-format --dry-run"
	@clang-format --dry-run --Werror --style=file $(FMT_SRCS)

check-fanalyzer:
	@$(BANNER) "gcc -fanalyzer"
	@$(MAKE) --no-print-directory main-bin BUILD=build/fanalyzer \
	    CC=gcc CFLAGS="$(CFLAGS) -fanalyzer"

check-asan:
	@$(BANNER) "C tests (ASan + UBSan)"
	@$(MAKE) --no-print-directory test BUILD=build/asan CFLAGS="$(ASAN_CFLAGS)"

check-msan:
	@$(BANNER) "C tests (MSan)"
	@$(MAKE) --no-print-directory test BUILD=build/msan CC=clang CFLAGS="$(MSAN_CFLAGS)"

check-ccomp:
	@$(BANNER) "C tests (CompCert)"
	@$(MAKE) --no-print-directory test BUILD=build/ccomp CC=ccomp

# ctgrind: run shrincs_wots_pubkey_gen and shrincs_wots_sign under valgrind with
# sk_seed marked uninitialized.  Any branch or memory index dependent
# on a secret byte is reported and --error-exitcode=1 fails the
# build.  Run across gcc / clang / CompCert since each can lower
# constant-time source to branchy code differently.
$(CTGRIND): test/ctgrind/ctgrind.c $(LIB) $(LIB_HDRS)
	@mkdir -p $(@D)
	$(HARNESS_CC) -std=c99 -Wall -Wextra -Wpedantic -Werror -O1 -g -Isrc -Iinclude \
	    $(VALGRIND_CFLAGS) -o $@ test/ctgrind/ctgrind.c $(LIB)

# Phony aliases so check-ct-X can pass a goal that the outer make won't
# pre-expand under the wrong BUILD root.
main-bin: $(MAIN)
ct-bin:   $(CTGRIND)

check-ct: check-ct-gcc check-ct-clang check-ct-ccomp

check-ct-gcc:
	@$(BANNER) "ctgrind on shrincs_wots_pubkey_gen+shrincs_wots_sign (gcc)"
	@$(MAKE) --no-print-directory ct-bin BUILD=build/ct-gcc CC=gcc
	valgrind -q --error-exitcode=1 --track-origins=yes \
	    --leak-check=no --errors-for-leak-kinds=none ./build/ct-gcc/test/ctgrind
	@$(SUCCESS) "shrincs_wots_pubkey_gen/shrincs_wots_sign: no secret-dependent branches (gcc)"

check-ct-clang:
	@$(BANNER) "ctgrind on shrincs_wots_pubkey_gen+shrincs_wots_sign (clang)"
	@$(MAKE) --no-print-directory ct-bin BUILD=build/ct-clang CC=clang
	valgrind -q --error-exitcode=1 --track-origins=yes \
	    --leak-check=no --errors-for-leak-kinds=none ./build/ct-clang/test/ctgrind
	@$(SUCCESS) "shrincs_wots_pubkey_gen/shrincs_wots_sign: no secret-dependent branches (clang)"

check-ct-ccomp:
	@$(BANNER) "ctgrind on shrincs_wots_pubkey_gen+shrincs_wots_sign (CompCert)"
	@$(MAKE) --no-print-directory ct-bin BUILD=build/ct-ccomp CC=ccomp HARNESS_CC=gcc
	valgrind -q --error-exitcode=1 --track-origins=yes \
	    --leak-check=no --errors-for-leak-kinds=none ./build/ct-ccomp/test/ctgrind
	@$(SUCCESS) "shrincs_wots_pubkey_gen/shrincs_wots_sign: no secret-dependent branches (CompCert)"

# ----- C library + tests ----------------------------------------------------

$(BUILD)/src/%.o: src/%.c $(LIB_HDRS)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) -c $< -o $@

$(LIB): $(LIB_OBJS)
	@mkdir -p $(@D)
	$(AR) rcs $@ $^

# Test harness sources.  Split across modules so each TU has one job:
#   common.c   shared helpers (rng, status)
#   sha256.c   SHA-256 KATs + NIST CAVS parser
#   wots.c     WOTS+C self-consistency + tamper checks
#   runner.c   banner + section drivers
TEST_SRCS = test/common.c test/sha256/sha256.c test/wots/wots.c test/runner.c
TEST_HDRS = test/common.h

# _DEFAULT_SOURCE exposes glibc's getrandom(2) / getline(3) to every
# test TU; safer than per-file #define which would race with header
# include order.
TEST_CFLAGS = $(CFLAGS) -Itest -D_DEFAULT_SOURCE=1

$(MAIN): $(TEST_SRCS) $(TEST_HDRS) $(LIB) $(LIB_HDRS)
	@mkdir -p $(@D)
	$(CC) $(TEST_CFLAGS) -o $@ $(TEST_SRCS) $(LIB)

# ----- Clean ----------------------------------------------------------------

clean:
	@rm -rf $(BUILD)
	@$(MAKE) --no-print-directory -C proof clean
