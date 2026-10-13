/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.Maximum
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Scales.DescendantMassFactor
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.CutoffFrobeniusMassTail

/-!
# CutoffFrobeniusMassMaximum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Descendant maxima of the genuine cutoff Frobenius mass

This module takes the genuine per-cube cutoff mass delivered by
`CutoffFrobeniusMassTail` and forms its literal finite maximum over
`descendantsAtDepth Q n`.  The family is canonically nonempty, so `Finset.sup'`
is used without an empty-family convention.  Every member is bounded by that
maximum, and the maximum remains measurable and nonnegative.

For the tail estimate, depth zero is handled as the singleton `{Q}`, retaining
the exact factor `1`.  At positive depth the model supplies `2 ≤ d`, the family
has cardinality `(3 ^ d) ^ n`, and the finite-maximum `Gamma_1` theorem costs
exactly `3 d log(3) n`, the positive-depth branch of
`descendantMassFactor d n`.

## Source

* ABK26 `e.kmn.bounds`, label and display, supplies the uniform one-cube
  increment tail used by the genuine per-cube provider.
* ABK26 `l.maximums.Gamma.s`, supplies the finite-maximum `Gamma_sigma` step and
  its logarithmic cardinality cost.
* This file provides precisely the genuine finite-depth mass maximum; it does
  not claim the later weighted all-depth aggregation.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Scales

noncomputable section

variable {d : ℕ}

/-- The genuine maximum of the cutoff Frobenius mass over all depth-`n`
descendants of `Q`. -/
noncomputable def cutoffFrobeniusMassMaximum
    (Q : TriadicCube d) (m : ℤ) (n : ℕ) (omega : CutoffSample d) : ℝ :=
  (descendantsAtDepth Q n).sup' (descendantsAtDepth_nonempty Q n)
    (fun R => cutoffFrobeniusMass R m omega)

/-- A descendant cutoff Frobenius-mass maximum is nonnegative. -/
theorem cutoffFrobeniusMassMaximum_nonneg
    (Q : TriadicCube d) (m : ℤ) (n : ℕ) (omega : CutoffSample d) :
    0 ≤ cutoffFrobeniusMassMaximum Q m n omega := by
  unfold cutoffFrobeniusMassMaximum
  obtain ⟨R, hR⟩ := descendantsAtDepth_nonempty Q n
  exact (cutoffFrobeniusMass_nonneg R m omega).trans
    (Finset.le_sup' (f := fun R => cutoffFrobeniusMass R m omega) hR)

/-- The descendant cutoff Frobenius-mass maximum is measurable on the public
cutoff carrier. -/
theorem measurable_cutoffFrobeniusMassMaximum
    (Q : TriadicCube d) (m : ℤ) (n : ℕ) :
    Measurable (cutoffFrobeniusMassMaximum Q m n) := by
  unfold cutoffFrobeniusMassMaximum
  let S : Finset (TriadicCube d) := descendantsAtDepth Q n
  let hS : S.Nonempty := descendantsAtDepth_nonempty Q n
  let X : TriadicCube d → CutoffSample d → ℝ :=
    fun R => cutoffFrobeniusMass R m
  let Y : CutoffSample d → ℝ := S.sup' hS X
  have hY : Measurable Y := by
    apply Finset.measurable_sup' hS
    intro R _
    exact measurable_cutoffFrobeniusMass R m
  have hY_eq : Y = fun omega => S.sup' hS (fun R => X R omega) := by
    funext omega
    exact Finset.sup'_apply hS X omega
  rw [← hY_eq]
  exact hY

/-- Every member of the descendant family is bounded by its genuine maximum. -/
theorem cutoffFrobeniusMass_le_cutoffFrobeniusMassMaximum
    (Q : TriadicCube d) (m : ℤ) (n : ℕ) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth Q n) (omega : CutoffSample d) :
    cutoffFrobeniusMass R m omega ≤ cutoffFrobeniusMassMaximum Q m n omega := by
  unfold cutoffFrobeniusMassMaximum
  exact Finset.le_sup' (f := fun S => cutoffFrobeniusMass S m omega) hR

/-- The genuine depth-`n` descendant maximum has the exact dimension-depth
`Gamma_1` amplitude obtained from the one-cube tail and finite maxima. -/
theorem isBigOWith_gammaSigma_one_cutoffFrobeniusMassMaximum
    (M : ABKModel d) (m : ℤ) (n : ℕ) (Q : TriadicCube d) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 1)
      (cutoffFrobeniusMassMaximum Q m n)
      (cutoffFrobeniusMassFiniteConst d * descendantMassFactor d n *
        M.gamma⁻¹ * (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ)))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [cutoffFrobeniusMassMaximum, descendantMassFactor] using!
      isBigOWith_gammaSigma_one_cutoffFrobeniusMass M m Q
  · let S : Finset (TriadicCube d) := descendantsAtDepth Q n
    let hS : S.Nonempty := descendantsAtDepth_nonempty Q n
    have hcard : S.card = (3 ^ d) ^ n := by
      simpa only [S] using descendantsAtDepth_card Q n
    have hcard_two : 2 ≤ S.card := by
      rw [hcard]
      calc
        2 ≤ 3 ^ d := by
          calc
            2 ≤ 3 ^ 2 := by norm_num
            _ ≤ 3 ^ d := Nat.pow_le_pow_right (by norm_num) M.shellPrefix.dimension
        _ ≤ (3 ^ d) ^ n := by
          calc
            3 ^ d = (3 ^ d) ^ 1 := (pow_one _).symm
            _ ≤ (3 ^ d) ^ n := Nat.pow_le_pow_right (by positivity) hn
    have htail := IndependentSums.isBigOWith_gammaSigma_finset_sup'
      (μ := (cutoffSampleLaw M).toMeasure) S hS
      (X := fun R => cutoffFrobeniusMass R m)
      (A := cutoffFrobeniusMassFiniteConst d * M.gamma⁻¹ *
        (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ))))
      (σ := 1) (by norm_num) hcard_two
      (fun R _ => isBigOWith_gammaSigma_one_cutoffFrobeniusMass M m R)
    have hlogcard :
        Real.log (S.card : ℝ) = (n : ℝ) * ((d : ℝ) * Real.log 3) := by
      rw [hcard]
      push_cast
      rw [Real.log_pow, Real.log_pow]
    have hfactor :
        ((3 : ℝ) * Real.log (S.card : ℝ)) ^ ((1 : ℝ)⁻¹) =
          3 * (n : ℝ) * (d : ℝ) * Real.log 3 := by
      rw [inv_one, Real.rpow_one, hlogcard]
      ring
    rw [hfactor] at htail
    have hbase_nonneg :
        0 ≤ cutoffFrobeniusMassFiniteConst d * M.gamma⁻¹ *
          (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ))) :=
      mul_nonneg
        (mul_nonneg (cutoffFrobeniusMassFiniteConst_pos d).le
          (inv_nonneg.mpr M.shellPrefix.gamma_pos.le))
        (Real.rpow_pos_of_pos (by norm_num) _).le
    have hpenalty :
        3 * (n : ℝ) * (d : ℝ) * Real.log 3 ≤ descendantMassFactor d n := by
      calc
        3 * (n : ℝ) * (d : ℝ) * Real.log 3 =
            3 * (d : ℝ) * Real.log 3 * (n : ℝ) := by ring
        _ ≤ 1 + 3 * (d : ℝ) * Real.log 3 * (n : ℝ) :=
          le_add_of_nonneg_left zero_le_one
        _ = descendantMassFactor d n := by rw [descendantMassFactor]
    have hscaled := htail.mono_scale
      (mul_le_mul_of_nonneg_right hpenalty hbase_nonneg)
    simpa only [cutoffFrobeniusMassMaximum, S, hS, mul_assoc, mul_left_comm,
      mul_comm] using! hscaled

end

end Algsuperdiff.Section3.Provider.Stream
