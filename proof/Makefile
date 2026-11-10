# ============================================================================
# libshrincs proof build.
#
# This Makefile owns everything under proof/: clightgen extraction, the
# generated Rocq Makefile.coq, and both proof trees (VST + SSProve) plus
# the honesty gate (assumptions/). It is invoked from the repo root via
# `make -C proof <target>`; the root Makefile's extract/vst-prove/
# ssprove-prove/prove/audit targets simply route here, so `make audit`
# etc. from the repo root behave exactly as before the proof build moved.
# ============================================================================

NPROC := $(shell nproc)

VST_DIR     = internal/vst
CLIGHT_DIR  = clight
SSPROVE_DIR = internal/ssprove
AUDIT_DIR   = assumptions
MODEL_DIR   = internal/common

# Cyan banner; blue success line.  Disable colors when NO_COLOR is set
# (https://no-color.org/) so CI logs stay readable.
ifeq ($(strip $(NO_COLOR)),)
  BANNER  = printf '\n\033[1;36m══ %s ══\033[0m\n'
  SUCCESS = printf '\033[1;34m✓ %s\033[0m\n'
else
  BANNER  = printf '\n══ %s ══\n'
  SUCCESS = printf '✓ %s\n'
endif

# The two trees' .vo targets, derived from _RocqProject so they never drift
# out of sync with the file listing. CLIGHT_VOFILES adds the generated
# clight/ modules to the internal/vst/ proof targets.
CLIGHT_VOFILES  := $(shell grep -E '^$(CLIGHT_DIR)/.*\.v$$' _RocqProject | sed 's/\.v$$/.vo/')
VST_VOFILES     := $(shell grep -E '^$(VST_DIR)/.*\.v$$' _RocqProject | sed 's/\.v$$/.vo/') $(CLIGHT_VOFILES)
SSPROVE_VOFILES := $(shell grep -E '^$(SSPROVE_DIR)/.*\.v$$' _RocqProject | sed 's/\.v$$/.vo/')

.PHONY: extract vst-prove ssprove-prove prove audit spec-test clean

# ----- VST / Rocq -----------------------------------------------------------
# Clight ASTs land in clight/ under the Shrincs root declared by
# _RocqProject. CLIGHT_VOFILES adds them to the VST build targets.
#
# ONE clightgen INVOCATION PER .c FILE, and no -include anywhere: the four
# C sources are four translation units, each verified as its own VSU
# (internal/vst/*/component.v and internal/vst/sha256/vsu.v) and linked
# in internal/vst/link.v. A -include would fold one TU's
# bodies into another's AST, which is exactly what the link step is for.

CLIGHT_ASTS = $(CLIGHT_DIR)/util.v $(CLIGHT_DIR)/sha256.v \
              $(CLIGHT_DIR)/thash.v $(CLIGHT_DIR)/wots.v

extract: $(CLIGHT_ASTS)

# The in-tree libc alternatives, [src/util.c]: memcpy/memset/ct_memcmp/panic.
# The leaf TU -- it calls nothing.
$(CLIGHT_DIR)/util.v: ../src/util.c ../include/util.h Makefile
	@mkdir -p $(@D)
	clightgen -normalize -I../src -I../include -Wp,-w -o $@ ../src/util.c

$(CLIGHT_DIR)/sha256.v: ../src/sha256.c ../include/sha256.h Makefile
	@mkdir -p $(@D)
	clightgen -normalize -I../src -I../include -Wp,-w -o $@ $<

# The shared tweakable-hash TU. shrincs_memcpy/_memset/shrincs_sha256 are
# External here and discharged at the link against the util / sha256 units.
$(CLIGHT_DIR)/thash.v: ../src/thash.c ../include/thash.h ../include/sha256.h ../include/util.h Makefile
	@mkdir -p $(@D)
	clightgen -normalize -I../src -I../include -Wp,-w -o $@ ../src/thash.c

# The WOTS+C TU. Its six callees (the three shims it uses, shrincs_sha256,
# and thash.c's two) are all External; util.h is a prerequisite for the
# declarations only.
$(CLIGHT_DIR)/wots.v: ../src/wots.c ../include/wots.h ../include/thash.h ../include/sha256.h ../include/util.h Makefile
	@mkdir -p $(@D)
	clightgen -normalize -I../src -I../include -Wp,-w -o $@ ../src/wots.c

# rocq makefile reads _RocqProject which lists the clight .v files, so
# they must exist (via extract) before Makefile.coq is regenerated --
# otherwise the generated rules reference missing inputs.
Makefile.coq: _RocqProject $(CLIGHT_ASTS)
	@rocq makefile -f _RocqProject -o Makefile.coq

vst-prove: extract Makefile.coq
	@$(MAKE) -j $(NPROC) --no-print-directory -f Makefile.coq $(VST_VOFILES)
	@$(SUCCESS) "VST Verification Succeeded"

ssprove-prove: Makefile.coq
	@$(MAKE) -j $(NPROC) --no-print-directory -f Makefile.coq $(SSPROVE_VOFILES)
	@$(SUCCESS) "SSProve Verification Succeeded"

prove: Makefile.coq extract
	@$(MAKE) -j $(NPROC) --no-print-directory -f Makefile.coq
	@$(SUCCESS) "All Verifications Succeeded"

# `make audit` is the combined honesty gate for all three proof trees
# (model, ssprove, vst): it forces the vst + ssprove trees to actually
# compile (not just grep their source text; the model tree is built as
# their shared dependency), then runs the single, parameterized combined
# gate (assumptions/check.sh) covering all three trees' build-freshness,
# proof-gap, axiom/parameter/hypothesis, and Print-Assumptions checks --
# see check.sh's header comment for the full gate-by-gate rationale and
# per-tree scoping.
#
# The second recipe line builds internal/common/correct/wots.vo explicitly:
# assumptions/model.v (the MODEL tree's probe) probes
# Shrincs.internal.common.correct.wots.wots_correct, but internal/common/correct/wots.v (the shared pure-model
# correctness theorem) is in neither compiled tree's .vo list and nothing
# in either tree Requires it, so a from-scratch `make audit` would
# otherwise fail check.sh's model-side coqc step (and its model gate 0)
# unless a prior `make prove` (full build) had left the .vo behind.
audit: vst-prove ssprove-prove
	@$(MAKE) -j $(NPROC) --no-print-directory -f Makefile.coq internal/common/correct/wots.vo
	@$(BANNER) "combined honesty gate (model + ssprove + vst)"
	@bash $(AUDIT_DIR)/check.sh
	@$(SUCCESS) "Audit: all proofs green, trust surface unchanged"

# The kernel virtual machine checks the literal specification on each vector.
spec-test: extract Makefile.coq
	@$(MAKE) -j $(NPROC) --no-print-directory -f Makefile.coq spec.vo
	@bash ../test/spec/run.sh

# ----- Clean ----------------------------------------------------------------

clean:
	@if [ -e Makefile.coq ]; then \
	    $(MAKE) --no-print-directory -f Makefile.coq cleanall; \
	fi
	@rm -f Makefile.coq Makefile.coq.conf $(CLIGHT_ASTS)
