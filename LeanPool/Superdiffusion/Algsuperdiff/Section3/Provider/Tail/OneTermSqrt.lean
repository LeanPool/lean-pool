/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Tail.TailSqrt
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.ConcentrationAEMeasurable

/-!
# OneTermSqrt

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# A one-term square-root tail conversion

This module supplies the model-free tail conversion used by the corrected
Section 3.2 base-case argument.  If a nonnegative observable satisfies

`X ^ 2 <= D + Y`

almost everywhere and `Y` has a one-sided `Gamma_1` tail, taking square roots
produces a `Gamma_2` random leg.  There are two useful local transformations.
The unshifted form treats `sqrt D` as a second `Gamma_2` leg and pays the
explicit binary addition constant.  The shifted form absorbs `sqrt D` into a deterministic
shift and keeps the random square-root scale unchanged.
-/

namespace Algsuperdiff.Section3.Provider.Tail

open MeasureTheory
open HCPolySupport.Book
open HCPolySupport.IndependentSums
open Algsuperdiff.Section3.Probability

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- The exact binary-addition multiplier at `Gamma_2`. -/
noncomputable def gammaTwoAdditionConst : ℝ :=
  2 * (3 * max 1 (Real.log 2)) ^ (1 / 2 : ℝ)

/-- The `Gamma_2` binary-addition multiplier is positive. -/
theorem gammaTwoAdditionConst_pos : 0 < gammaTwoAdditionConst := by
  rw [gammaTwoAdditionConst]
  exact mul_pos (by norm_num)
    (Real.rpow_pos_of_pos
      (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))) _)

/-- A deterministic constant bounded by a nonnegative scale has a one-sided
`Gamma_sigma` tail at that scale. -/
theorem isBigOWith_gammaSigma_const
    {sigma c A : ℝ} (hA : 0 ≤ A) (hc : c ≤ A) :
    IsBigOWith mu (gammaSigma sigma) (fun _omega : Omega => c) A := by
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hAt : A ≤ A * t := by
    calc
      A = A * 1 := by ring
      _ ≤ A * t := mul_le_mul_of_nonneg_left ht hA
  have htail : upperTailEvent (fun _omega : Omega => c) (A * t) = ∅ := by
    ext omega
    simp only [mem_upperTailEvent, Set.mem_empty_iff_false, iff_false]
    exact not_lt_of_ge (hc.trans hAt)
  rw [htail, measureReal_empty]
  exact (Real.exp_pos _).le

/-- The deterministic square-root inequality for one random summand. -/
private theorem sqrt_le_add_of_sq_le_add {x D Y : ℝ}
    (hx : 0 ≤ x) (hD : 0 ≤ D) (hY : 0 ≤ Y)
    (hsq : x ^ 2 ≤ D + Y) :
    x ≤ Real.sqrt D + Real.sqrt Y := by
  have h := sqrt_le_add_of_sq_le_add_add hx hD hY (le_refl 0)
    (by simpa only [add_zero] using hsq)
  simpa only [Real.sqrt_zero, add_zero] using h

/-- A one-random-leg square bound gives an unshifted one-sided `Gamma_2`
bound.  Both square-root amplitudes are bounded by `B`, so their binary merge
has the exact scale `gammaTwoAdditionConst * B`. -/
theorem isOneSidedOrlicz_gammaSigma_two_of_sq_le_add [IsFiniteMeasure mu]
    {X Y : Omega → ℝ} {D A B : ℝ}
    (hX : Measurable X)
    (hXnn : ∀ omega, 0 ≤ X omega) (hYnn : ∀ omega, 0 ≤ Y omega)
    (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hsq : ∀ᵐ omega ∂mu, X omega ^ 2 ≤ D + Y omega)
    (hYtail : IsBigOWith mu (gammaSigma 1) Y A)
    (hDb : Real.sqrt D ≤ B) (hAb : Real.sqrt A ≤ B)
    (hBpos : 0 < B) :
    IsOneSidedOrlicz mu (gammaSigma 2) X (gammaTwoAdditionConst * B) := by
  have hconst :
      IsBigOWith mu (gammaSigma 2) (fun _omega : Omega => Real.sqrt D) B :=
    isBigOWith_gammaSigma_const hBpos.le hDb
  have hsqrtRaw := isBigOWith_gammaSigma_sqrt hA hYnn hYtail
  have hsqrt : IsBigOWith mu (gammaSigma 2) (fun omega => Real.sqrt (Y omega)) B := by
    norm_num at hsqrtRaw
    exact hsqrtRaw.mono_scale hAb
  have hsumRaw := isBigOWith_gammaSigma_add_of_nonneg
    (μ := mu) (Y := fun _omega : Omega => Real.sqrt D)
    (Z := fun omega => Real.sqrt (Y omega)) (A := B) (B := B) (σ := 2)
    (by norm_num) hBpos.le hBpos.le hconst hsqrt
  have hsum :
      IsBigOWith mu (gammaSigma 2)
        (fun omega => Real.sqrt D + Real.sqrt (Y omega))
        (gammaTwoAdditionConst * B) := by
    convert hsumRaw using 1
    norm_num [gammaTwoAdditionConst, mul_assoc]
  refine ⟨isAdmissibleTail_gammaSigma (by norm_num),
    mul_pos gammaTwoAdditionConst_pos hBpos, hX, ?_⟩
  refine Ch04.isBigOWith_of_ae_le hsum ?_
  filter_upwards [hsq] with omega homega
  exact sqrt_le_add_of_sq_le_add (hXnn omega) hD (hYnn omega) homega

/-- A one-random-leg square bound gives a deterministically shifted
one-sided `Gamma_2` bound.  The deterministic square root is absorbed by `b`,
so the random square-root scale `B` is retained without the binary-merge
multiplier. -/
theorem isDeterministicShiftOneSidedOrlicz_gammaSigma_two_of_sq_le_add
    [IsFiniteMeasure mu] {X Y : Omega → ℝ} {D A b B : ℝ}
    (hX : Measurable X)
    (hXnn : ∀ omega, 0 ≤ X omega) (hYnn : ∀ omega, 0 ≤ Y omega)
    (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hsq : ∀ᵐ omega ∂mu, X omega ^ 2 ≤ D + Y omega)
    (hYtail : IsBigOWith mu (gammaSigma 1) Y A)
    (hDb : Real.sqrt D ≤ b) (hAb : Real.sqrt A ≤ B)
    (hBpos : 0 < B) :
    IsDeterministicShiftOneSidedOrlicz mu (gammaSigma 2) X b B := by
  have hsqrtRaw := isBigOWith_gammaSigma_sqrt hA hYnn hYtail
  have hsqrt : IsBigOWith mu (gammaSigma 2) (fun omega => Real.sqrt (Y omega)) B := by
    norm_num at hsqrtRaw
    exact hsqrtRaw.mono_scale hAb
  refine ⟨isAdmissibleTail_gammaSigma (by norm_num), hBpos, hX, ?_⟩
  refine Ch04.isBigOWith_of_ae_le hsqrt ?_
  filter_upwards [hsq] with omega homega
  have hroot := sqrt_le_add_of_sq_le_add (hXnn omega) hD (hYnn omega) homega
  change X omega - b ≤ Real.sqrt (Y omega)
  linarith only [hroot, hDb]

end

end Algsuperdiff.Section3.Provider.Tail
