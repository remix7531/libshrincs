# ============================================================================
# libshrincs proof build.
#
# This Makefile owns everything under proof/: clightgen extraction, the
# generated Rocq Makefile.coq, the VST, SSProve, and FXMSS proof trees,
# plus the combined honesty gate. It is invoked from the repo root via
# `make -C proof <target>`; the root Makefile's extract/vst-prove/
# ssprove-prove/prove/audit targets simply route here, so `make audit`
# etc. from the repo root behave exactly as before the proof build moved.
# ============================================================================

NPROC := $(shell nproc)

VST_DIR     = vst
SSPROVE_DIR = ssprove
FXMSS_DIR   = fxmss
AUDIT_DIR   = assumptions
MODEL_DIR   = model

# Cyan banner; blue success line.  Disable colors when NO_COLOR is set
# (https://no-color.org/) so CI logs stay readable.
ifeq ($(strip $(NO_COLOR)),)
  BANNER  = printf '\n\033[1;36m══ %s ══\033[0m\n'
  SUCCESS = printf '\033[1;34m✓ %s\033[0m\n'
else
  BANNER  = printf '\n══ %s ══\n'
  SUCCESS = printf '✓ %s\n'
endif

# The proof trees' .vo targets, derived from _RocqProject so they never drift
# out of sync with the file listing.  Each of the three native/abstract
# proof trees gets its own scope -- ssprove-prove builds ONLY ssprove/ (the
# native WOTS+C tree that anchors to the VST-verified C via model_bridge.v),
# fxmss-prove builds ONLY fxmss/ (the abstract, C-unconnected EU-CMA tree).
# `make prove` / `make audit` still build all trees together.
VST_VOFILES     := $(shell grep -E '^$(VST_DIR)/.*\.v$$' _RocqProject | sed 's/\.v$$/.vo/')
SSPROVE_VOFILES := $(shell grep -E '^$(SSPROVE_DIR)/.*\.v$$' _RocqProject | sed 's/\.v$$/.vo/')
FXMSS_VOFILES   := $(shell grep -E '^$(FXMSS_DIR)/.*\.v$$' _RocqProject | sed 's/\.v$$/.vo/')

.PHONY: extract vst-prove ssprove-prove fxmss-prove prove audit clean

# ----- VST / Rocq -----------------------------------------------------------
# Clight ASTs land in vst/clight/ so _RocqProject finds them.

extract: $(VST_DIR)/clight/wots.v $(VST_DIR)/clight/thash.v $(VST_DIR)/clight/sha256.v

$(VST_DIR)/clight/wots.v: ../src/wots.c ../include/wots.h ../include/thash.h ../include/sha256.h ../include/util.h ../src/util.c
	@mkdir -p $(@D)
	clightgen -normalize -I../src -I../include -Wp,-w -include ../src/util.c -o $@ ../src/wots.c

# The shared tweakable-hash TU. Like sha256.v (and unlike wots.v) util.c is
# NOT folded in, so shrincs_memcpy/_memset/shrincs_sha256 stay External and
# resolve through their Gprog funspecs; their bodies are proven in wots.v.
$(VST_DIR)/clight/thash.v: ../src/thash.c ../include/thash.h ../include/sha256.h ../include/util.h
	@mkdir -p $(@D)
	clightgen -normalize -I../src -I../include -Wp,-w -o $@ ../src/thash.c

$(VST_DIR)/clight/sha256.v: ../src/sha256.c ../include/sha256.h ../include/util.h
	@mkdir -p $(@D)
	clightgen -normalize -I../src -I../include -Wp,-w -o $@ $<

# rocq makefile reads _RocqProject which lists the clight .v files, so
# they must exist (via extract) before Makefile.coq is regenerated --
# otherwise the generated rules reference missing inputs.
Makefile.coq: _RocqProject $(VST_DIR)/clight/wots.v $(VST_DIR)/clight/thash.v $(VST_DIR)/clight/sha256.v
	@rocq makefile -f _RocqProject -o Makefile.coq

vst-prove: extract Makefile.coq
	@$(MAKE) -j $(NPROC) --no-print-directory -f Makefile.coq $(VST_VOFILES)
	@$(SUCCESS) "VST Verification Succeeded"

ssprove-prove: Makefile.coq
	@$(MAKE) -j $(NPROC) --no-print-directory -f Makefile.coq $(SSPROVE_VOFILES)
	@$(SUCCESS) "SSProve Verification Succeeded"

# vst-prove / ssprove-prove / fxmss-prove are conveniences over the single
# build: each just asks the one generated Makefile.coq for its tree's .vo
# slice, so `make prove` (no target list) still builds everything together.

fxmss-prove: Makefile.coq
	@$(MAKE) -j $(NPROC) --no-print-directory -f Makefile.coq $(FXMSS_VOFILES)
	@$(SUCCESS) "FXMSS Verification Succeeded"

prove: Makefile.coq extract
	@$(MAKE) -j $(NPROC) --no-print-directory -f Makefile.coq
	@$(SUCCESS) "All Verifications Succeeded"

# `make audit` is the combined honesty gate for all four proof trees
# (model, ssprove, fxmss, vst): it forces vst, ssprove, and fxmss to actually
# compile (not just grep their source text; the model tree is built as
# their shared dependency), then runs the single, parameterized combined
# gate (assumptions/check.sh) covering all four trees' build-freshness,
# proof-gap, axiom/parameter/hypothesis, and Print-Assumptions checks --
# see check.sh's header comment for the full gate-by-gate rationale and
# per-tree scoping.
#
# The second recipe line builds two model .vo files explicitly, because
# neither is in any compiled tree's .vo list and nothing in any tree
# Requires them, so a from-scratch `make audit` would otherwise fail
# check.sh's model gate 0 unless a prior `make prove` had left them
# behind:
#   model/correct/wots.vo  -- assumptions/model.v (the MODEL tree's probe)
#     probes Model.correct.wots.wots_correct, so check.sh's model-side
#     coqc step needs it too.
#   model/shrincs.vo       -- the port of the normative Python spec
#     (model/PORTING.md).  The SSProve bridges now Require the derived
#     views above it (model/theory/shrincs.v), so THAT file is built as
#     part of ssprove-prove; the port itself is still listed here so a
#     from-scratch `make audit` cannot miss it if that ever changes.
audit: vst-prove ssprove-prove fxmss-prove
	@$(MAKE) -j $(NPROC) --no-print-directory -f Makefile.coq model/correct/wots.vo model/shrincs.vo
	@$(BANNER) "combined honesty gate (model + ssprove + fxmss + vst)"
	@bash $(AUDIT_DIR)/check.sh
	@$(SUCCESS) "Audit: all proofs green, trust surface unchanged"

# ----- Clean ----------------------------------------------------------------

clean:
	@if [ -e Makefile.coq ]; then \
	    $(MAKE) --no-print-directory -f Makefile.coq cleanall; \
	fi
	@rm -f Makefile.coq Makefile.coq.conf \
	       $(VST_DIR)/clight/wots.v $(VST_DIR)/clight/thash.v $(VST_DIR)/clight/sha256.v
