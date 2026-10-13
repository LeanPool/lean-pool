/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Process.Kernel.ResolventTailMoments

/-!
# ResolventTailVariable

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Kolmogorov moments from a shift-dependent resolvent tail

The moment criterion of `Kernel/ResolventTailMoments.lean` asks for one profile and one trivial
cutting radius valid at every shift.  An analytic estimate whose decay rate degrades with the
shift satisfies no such uniform statement, and this file removes the requirement: the profile
`phi lam` and the cutting radius `cut lam` may both depend on the shift, and only two things are
asked uniformly, the cubic layer-cake budget `I` of the profile beyond its cutting radius and
the growth `cut lam ^ 4 ≤ A lam ^ (2 - q)` of the cutting radius.

The price is the time exponent.  At the time `t` the layer cake is applied at the shift `1 / t`,
where the trivial radius contributes `256 cut (1 / t) ^ 4 t ^ 2`; the growth hypothesis converts
that into `256 A t ^ q`, and the budget term `256 · 8 e I · t ^ 2` is absorbed into `t ^ q`
because `t ≤ 1` and `q ≤ 2`.  A cutting radius growing logarithmically in the shift is therefore
free for every `q < 2`, and the library charges nothing for the smaller exponent: the local
criterion, its passage to the global one, and the continuous-path construction are all stated
for a general `q > 1`.

`PositiveC0ContractiveResolvent.OnePointRegular.of_variableResolventTail` is the resulting
regularity data of the compactified process, obtained from the local criterion through the
shared core
`OnePointRegular.of_hasLocalKolmogorovMoments`.  Nothing here asserts an analytic estimate for a
particular generator: the tail decay, the budget and the growth of the cutting radius are the
consumer's hypotheses.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

open MarkovProcess

namespace Algsuperdiff.Process.PositiveC0ContractiveResolvent

open Semigroup SubMarkovKernelSemigroup
open MarkovProcess.PositiveC0ContractiveResolvent

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **The local Kolmogorov criterion from a shift-dependent resolvent tail.**  The profile and the
trivial cutting radius may depend on the shift; a cutting radius growing no faster than
`lam ^ ((2 - q) / 4)` still gives the local moment criterion, with the time exponent `q`. -/
theorem hasLocalKolmogorovMoments_of_variableResolventTail
    (R : PositiveC0ContractiveResolvent X) (hcons : R.kernelSemigroup.IsConservative)
    {phi : ℝ → ℝ → ℝ} (hphi : ∀ lam s, 0 ≤ phi lam s)
    (htail : ∀ mu : PositiveShift, 1 ≤ (mu : ℝ) →
      SubMarkovKernelSemigroup.HasResolventTail R.kernelSemigroup (mu : ℝ) (phi (mu : ℝ)))
    {cut : ℝ → ℝ} (hcut : ∀ lam, 0 ≤ cut lam) {I : ℝ} (hI : 0 ≤ I)
    (hint : ∀ mu : PositiveShift, 1 ≤ (mu : ℝ) →
      ∫⁻ s in Set.Ioi (cut (mu : ℝ)),
        ENNReal.ofReal (phi (mu : ℝ) s * s ^ 3) ≤ ENNReal.ofReal I)
    {q A : ℝ} (hq1 : 1 < q) (hq2 : q ≤ 2) (hA : 0 ≤ A)
    (hgrowth : ∀ mu : PositiveShift, 1 ≤ (mu : ℝ) →
      cut (mu : ℝ) ^ 4 ≤ A * (mu : ℝ) ^ (2 - q))
    {B : ℝ≥0} (hB : ∀ y z : X, edist z y ^ (4 : ℝ) ≤ B) :
    R.kernelSemigroup.HasLocalKolmogorovMoments 4 q
      (Real.toNNReal (256 * (A + 8 * Real.exp 1 * I))) B := by
  refine ⟨by norm_num, hq1, fun h hh1 y ↦ ?_, hB⟩
  rcases eq_or_lt_of_le (zero_le : 0 ≤ h) with hh | hh
  · rw [← hh, lintegral_edist_pow_zero R y]
    exact zero_le
  · have hpos : (0 : ℝ) < (h : ℝ) := hh
    have hcoe : (h : ℝ) ≤ 1 := by exact_mod_cast hh1
    have hinv : (0 : ℝ) < ((h : ℝ))⁻¹ := inv_pos.mpr hpos
    have hone : (1 : ℝ) ≤ ((h : ℝ))⁻¹ := by
      have hmul := mul_le_mul_of_nonneg_left hcoe hinv.le
      rwa [inv_mul_cancel₀ hpos.ne', mul_one] at hmul
    -- the layer cake at the shift `1 / h`, with that shift's profile and cutting radius
    have hkey : ∫⁻ z, edist z y ^ (4 : ℝ) ∂(R.kernelSemigroup h y) ≤
        ENNReal.ofReal (256 * (cut ((h : ℝ)⁻¹) ^ 4 + 8 * Real.exp 1 * I)) *
          ENNReal.ofReal ((h : ℝ) ^ 2) :=
      lintegral_edist_pow_le_of_hasResolventTail R hcons (hphi ((h : ℝ)⁻¹))
        (htail ⟨(h : ℝ)⁻¹, hinv⟩ hone) (inv_mul_cancel₀ hpos.ne') (hcut ((h : ℝ)⁻¹)) hI
        (hint ⟨(h : ℝ)⁻¹, hinv⟩ hone) y
    have hgr : cut ((h : ℝ)⁻¹) ^ 4 ≤ A * ((h : ℝ)⁻¹) ^ (2 - q) :=
      hgrowth ⟨(h : ℝ)⁻¹, hinv⟩ hone
    -- the trivial radius is paid for by the exponent, the budget by `h ≤ 1`
    have hE : (0 : ℝ) ≤ 8 * Real.exp 1 * I := by positivity
    have hr2 : (h : ℝ) ^ (2 : ℕ) = (h : ℝ) ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hr2nonneg : (0 : ℝ) ≤ (h : ℝ) ^ (2 : ℝ) := Real.rpow_nonneg hpos.le 2
    have hexponent : (h : ℝ) ^ (2 : ℝ) ≤ (h : ℝ) ^ q :=
      Real.rpow_le_rpow_of_exponent_ge hpos hcoe hq2
    have hcancel : ((h : ℝ)⁻¹) ^ (2 - q) * (h : ℝ) ^ (2 : ℝ) = (h : ℝ) ^ q := by
      rw [Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le, ← Real.rpow_add hpos]
      congr 1
      ring
    have hterm1 : 256 * cut ((h : ℝ)⁻¹) ^ 4 * (h : ℝ) ^ (2 : ℝ) ≤ 256 * A * (h : ℝ) ^ q := by
      calc 256 * cut ((h : ℝ)⁻¹) ^ 4 * (h : ℝ) ^ (2 : ℝ)
          = 256 * (cut ((h : ℝ)⁻¹) ^ 4 * (h : ℝ) ^ (2 : ℝ)) := by ring
        _ ≤ 256 * (A * ((h : ℝ)⁻¹) ^ (2 - q) * (h : ℝ) ^ (2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hgr hr2nonneg)
              (by norm_num)
        _ = 256 * A * (h : ℝ) ^ q := by rw [mul_assoc A, hcancel]; ring
    have hterm2 : 256 * (8 * Real.exp 1 * I) * (h : ℝ) ^ (2 : ℝ) ≤
        256 * (8 * Real.exp 1 * I) * (h : ℝ) ^ q :=
      mul_le_mul_of_nonneg_left hexponent (by positivity)
    have hreal : 256 * (cut ((h : ℝ)⁻¹) ^ 4 + 8 * Real.exp 1 * I) * (h : ℝ) ^ (2 : ℕ) ≤
        256 * (A + 8 * Real.exp 1 * I) * (h : ℝ) ^ q := by
      calc 256 * (cut ((h : ℝ)⁻¹) ^ 4 + 8 * Real.exp 1 * I) * (h : ℝ) ^ (2 : ℕ)
          = 256 * cut ((h : ℝ)⁻¹) ^ 4 * (h : ℝ) ^ (2 : ℝ) +
              256 * (8 * Real.exp 1 * I) * (h : ℝ) ^ (2 : ℝ) := by rw [hr2]; ring
        _ ≤ 256 * A * (h : ℝ) ^ q + 256 * (8 * Real.exp 1 * I) * (h : ℝ) ^ q :=
            add_le_add hterm1 hterm2
        _ = 256 * (A + 8 * Real.exp 1 * I) * (h : ℝ) ^ q := by ring
    have hcoeff : (0 : ℝ) ≤ 256 * (cut ((h : ℝ)⁻¹) ^ 4 + 8 * Real.exp 1 * I) := by
      have h1 : (0 : ℝ) ≤ cut ((h : ℝ)⁻¹) ^ 4 := by positivity
      linarith only [h1, hE]
    have hM : (0 : ℝ) ≤ 256 * (A + 8 * Real.exp 1 * I) := by linarith only [hA, hE]
    refine hkey.trans ?_
    calc ENNReal.ofReal (256 * (cut ((h : ℝ)⁻¹) ^ 4 + 8 * Real.exp 1 * I)) *
          ENNReal.ofReal ((h : ℝ) ^ 2)
        = ENNReal.ofReal (256 * (cut ((h : ℝ)⁻¹) ^ 4 + 8 * Real.exp 1 * I) * (h : ℝ) ^ 2) :=
          (ENNReal.ofReal_mul hcoeff).symm
      _ ≤ ENNReal.ofReal (256 * (A + 8 * Real.exp 1 * I) * (h : ℝ) ^ q) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (256 * (A + 8 * Real.exp 1 * I)) * ENNReal.ofReal ((h : ℝ) ^ q) :=
          ENNReal.ofReal_mul hM
      _ = (Real.toNNReal (256 * (A + 8 * Real.exp 1 * I)) : ℝ≥0∞) * (h : ℝ≥0∞) ^ q := by
          rw [← ENNReal.ofReal_rpow_of_pos hpos, ENNReal.ofReal_coe_nnreal]
          rfl

/-- **Regularity data of a compactified process from shift-dependent tail decay.**  An exhaustion
function bounded by one, tail decay of the compactified potential measures at every shift at
least one with a profile and a trivial cutting radius that may both depend on the shift, a
uniform cubic budget and a uniform growth bound for the cutting radius together give the data
from which the continuous-path process of the compactified semigroup is formed. -/
def OnePointRegular.of_variableResolventTail (R : PositiveC0ContractiveResolvent X)
    (rho : X → ℝ) (hrho_cont : Continuous rho) (hrho_pos : ∀ x, 0 < rho x)
    (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    (hrho_le : ∀ x, rho x ≤ 1) {phi : ℝ → ℝ → ℝ} (hphi : ∀ lam s, 0 ≤ phi lam s)
    (htail : ∀ mu : PositiveShift, 1 ≤ (mu : ℝ) →
      letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
      SubMarkovKernelSemigroup.HasResolventTail R.onePointKernelSemigroup (mu : ℝ) (phi (mu : ℝ)))
    {cut : ℝ → ℝ} (hcut : ∀ lam, 0 ≤ cut lam) {I : ℝ} (hI : 0 ≤ I)
    (hint : ∀ mu : PositiveShift, 1 ≤ (mu : ℝ) →
      ∫⁻ s in Set.Ioi (cut (mu : ℝ)),
        ENNReal.ofReal (phi (mu : ℝ) s * s ^ 3) ≤ ENNReal.ofReal I)
    {q A : ℝ} (hq1 : 1 < q) (hq2 : q ≤ 2) (hA : 0 ≤ A)
    (hgrowth : ∀ mu : PositiveShift, 1 ≤ (mu : ℝ) →
      cut (mu : ℝ) ^ 4 ≤ A * (mu : ℝ) ^ (2 - q)) :
    R.OnePointRegular :=
  letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  OnePointRegular.of_hasLocalKolmogorovMoments R rho hrho_cont hrho_pos hrho_lipschitz
    hrho_compact
    (hasLocalKolmogorovMoments_of_variableResolventTail R.onePointResolvent
      R.isConservative_onePointKernelSemigroup hphi htail hcut hI hint hq1 hq2 hA hgrowth
      (OnePoint.exhaustionMetricSpace_edist_pow_le rho hrho_cont hrho_pos hrho_lipschitz
        hrho_compact hrho_le))

end Algsuperdiff.Process.PositiveC0ContractiveResolvent
