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
# out of sync with the file listing. CLIGHT_VOFILES folds into the vst set:
# clight/ is separate from internal/vst/ (single -Q . Shrincs root, see
# _RocqProject), but the generated ASTs are still part of the VST build.
CLIGHT_VOFILES  := $(shell grep -E '^$(CLIGHT_DIR)/.*\.v$$' _RocqProject | sed 's/\.v$$/.vo/')
VST_VOFILES     := $(shell grep -E '^$(VST_DIR)/.*\.v$$' _RocqProject | sed 's/\.v$$/.vo/') $(CLIGHT_VOFILES)
SSPROVE_VOFILES := $(shell grep -E '^$(SSPROVE_DIR)/.*\.v$$' _RocqProject | sed 's/\.v$$/.vo/')

.PHONY: extract vst-prove ssprove-prove prove audit spec-test clean

# ----- VST / Rocq -----------------------------------------------------------
# Clight ASTs land in clight/ (single -Q . Shrincs
# root, see _RocqProject), so _RocqProject finds them; CLIGHT_VOFILES
# below folds them into the vst build set.
#
# ONE clightgen INVOCATION PER .c FILE, and no -include anywhere: the four
# C sources are four translation units, each verified as its own VSU
# (internal/vst/*/component.v and internal/vst/sha256/vsu.v) and linked
# in internal/vst/link.v. A -include would fold one TU's
# bodies into another's AST, which is exactly what the link step is for.

CLIGHT_ASTS = $(CLIGHT_DIR)/util.v $(CLIGHT_DIR)/sha256.v \
              $(CLIGHT_DIR)/thash.v $(CLIGHT_DIR)/wots.v

extract: $(CLIGHT_ASTS)

# The in-tree libc alternatives, [src/util.c]: memcpy/memset/panic.
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

# The WOTS+C TU. Its five callees (the two shims it uses, shrincs_sha256,
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

# The literal specification and both proof stacks are compiled before the gates.
audit: vst-prove ssprove-prove
	@$(MAKE) -j $(NPROC) --no-print-directory -f Makefile.coq spec.vo
	@$(BANNER) "honesty gate"
	@bash $(AUDIT_DIR)/check.sh
	@$(SUCCESS) "Audit: all proofs green, trust surface unchanged"

# spec.v against the reference vectors, evaluated by the kernel's virtual
# machine. Minutes of work per key generation, so it is its own target.
spec-test: extract Makefile.coq
	@$(MAKE) -j $(NPROC) --no-print-directory -f Makefile.coq spec.vo
	@bash ../test/spec/run.sh

# ----- Clean ----------------------------------------------------------------

clean:
	@if [ -e Makefile.coq ]; then \
	    $(MAKE) --no-print-directory -f Makefile.coq cleanall; \
	fi
	@rm -f Makefile.coq Makefile.coq.conf $(CLIGHT_ASTS)
