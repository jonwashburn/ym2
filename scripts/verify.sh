#!/usr/bin/env bash
set -euo pipefail

# Build YM targets (non-interactive)
lake -Kenv=prod build ym | cat

# Create a temporary Lean file to print axioms of key exports
TMP=$(mktemp -t ym_axioms_XXXXXX.lean)
cat > "$TMP" <<'LEAN'
import Mathlib
import ym.Main
import ym.minkowski.Reconstruction
import ym.continuum_limit.Universality

open YM

#print axioms YM.SU_N_YangMills_on_R4_has_mass_gap_via_Wilson_pipeline
#print axioms YM.spectrum_gap_persists_export
#print axioms YM.Minkowski.wightman_export
#print axioms YM.Cont.two_regularizations_universality
LEAN

# Run Lean on the temporary file to emit axioms (use interpreter to print output)
lake -Kenv=prod env lean "$TMP" | cat || true

# Grep for sorry in the ym sources
echo "\nSearching for sorry in ym/ ..."
rg -n "sorry" ym | cat || true

echo "Axiom report generated for:"
echo "  - YM.SU_N_YangMills_on_R4_has_mass_gap_via_Wilson_pipeline"
echo "  - YM.spectrum_gap_persists_export"
echo "  - YM.Minkowski.wightman_export"
echo "  - YM.Cont.two_regularizations_universality"

# Grep exported theorems
echo "\nChecking exported theorems present..."
rg -n "continuum_gap_unconditional_from_cut_and_nrc|unconditional_mass_gap|wilson_pf_gap_select_best_from_pack|NRC_all_nonreal|thermodynamic_limit_exists|gap_persists_in_limit" ym | cat || true

