/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.ProfileConstants
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLocalPayoff

/-!
# SuperposedFluxLocalParameters

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Parameters for the superposed-flux local payoff

This file selects the two auxiliary exponents in the local lower-payoff
producer.  For the manuscript's fixed `b = 2⁻²⁰` and external exponent
`sigma`, set

```text
eps  = b * sigma / 8,
beta = b + b * sigma / 4.
```

These are internal Lean proof parameters: the manuscript does not state these
values, and neither definition is a frozen declaration.  The exponential
branch of the frozen maximum is stronger than the coarse
`gamma = O(b * sigma)` estimate used by `ProfileConstants.lean`.  Applying the
same elementary exponential-decay lemma at the auxiliary scale `b / 16` gives
`gamma ≤ (3 / 32) * b * sigma`.  This bound pays every `eps`- and `beta`-based
scalar gate of
`slstar_descendantGrid_allL_ae_and_isBigOWith_of_gates`, including its explicit
`superposedFluxLocalExponent ≤ b` premise.  It also keeps the resulting local
Orlicz exponent at least `(1 - sigma) / 2` after the source's
`sigma ↦ sigma / 4` substitution.

This file does not select the integers `k₀` and `kp`, and it does not prove the
separate rate-cap inequality `hcap`; those require another producer.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Multiscale

noncomputable section


/-- The exact frozen maximum and fifth-root gates give the sharper smallness
needed by the superposed-flux parameter choice. -/
theorem gamma_le_three_div_thirty_two_mul_bfaProfileB_mul_sigma_of_profileAuxiliaryMaxGate
    {d : ℕ} (M : ABKModel d) {sigma E : ℝ} (hE : 1 ≤ E)
    (hsigma : 0 < sigma)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ))) :
    M.gamma ≤ (3 / 32 : ℝ) * bfaProfileB * sigma := by
  have hfloor : 2 / (15 * (bfaProfileB / 16)) ≤ profileAuxiliaryConst d := by
    have hbad : (32 / 15 : ℝ) ≤ badClustersConst d := by
      linarith [twentyOne_le_badClustersConst d]
    calc
      2 / (15 * (bfaProfileB / 16)) = (32 / 15 : ℝ) / bfaProfileB := by
        field_simp [ne_of_gt bfaProfileB_pos]
        norm_num
      _ ≤ badClustersConst d / bfaProfileB :=
        div_le_div_of_nonneg_right hbad bfaProfileB_pos.le
      _ ≤ profileAuxiliaryConst d :=
        badClustersConst_div_bfaProfileB_le_profileAuxiliaryConst d
  have hexp : Real.exp (profileAuxiliaryConst d / sigma) ≤ E :=
    (le_max_left _ _).trans hmax
  have hgammaE : M.gamma ≤ E ^ (-5 : ℤ) :=
    gamma_le_zpow_neg_five_of_frozenGate hE M.shellPrefix.gamma_pos hEgamma
  have hdecay : E ^ (-5 : ℤ) ≤
      (3 / 2 : ℝ) * (bfaProfileB / 16) * sigma :=
    zpow_neg_five_le_three_halves_mul_of_exp_div_le
      (profileAuxiliaryConst_pos d) (div_pos bfaProfileB_pos (by norm_num))
      hsigma hfloor hexp
  calc
    M.gamma ≤ E ^ (-5 : ℤ) := hgammaE
    _ ≤ (3 / 2 : ℝ) * (bfaProfileB / 16) * sigma := hdecay
    _ = (3 / 32 : ℝ) * bfaProfileB * sigma := by ring


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
