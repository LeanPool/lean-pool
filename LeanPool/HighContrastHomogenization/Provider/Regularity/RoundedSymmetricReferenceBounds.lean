/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedAffineFields

/-!
# High-contrast homogenization: Provider.Regularity.RoundedSymmetricReferenceBounds

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Near-identity bounds for the rounded symmetric reference

The canonical alignment `kZero d = d + 5` makes the entrywise rounding error
strictly smaller than the coarse `1 / 101` estimate used for grid positivity.
This sharper slack controls the two inverse-grid factors in the transformed
constant symmetric reference and yields the source's literal one-percent
Loewner sandwich.
-/

namespace HCPolySupport
namespace HighContrast

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem baseRoundedGrid_roundingScale_le :
    (d : ℝ) * (3 : ℝ) ^ (-(kZero d : ℤ)) ≤ 1 / 400 := by
  have hbern : 1 + (d : ℝ) * 2 ≤ (3 : ℝ) ^ d := by
    have h := one_add_mul_le_pow (a := (2 : ℝ)) (by norm_num) d
    rw [show (1 : ℝ) + 2 = 3 by norm_num] at h
    linarith only [h]
  have hd : 2 * (d : ℝ) ≤ (3 : ℝ) ^ d := by
    linarith only [hbern]
  have hpow : 0 ≤ (3 : ℝ) ^ (-(kZero d : ℤ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hd hpow
  have hright :
      (3 : ℝ) ^ d * (3 : ℝ) ^ (-(kZero d : ℤ)) = 1 / 243 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    have hexp : (d : ℤ) + -(kZero d : ℤ) = -5 := by
      simp [kZero]
    rw [hexp]
    norm_num
  have htwice :
      2 * ((d : ℝ) * (3 : ℝ) ^ (-(kZero d : ℤ))) ≤ 1 / 243 := by
    calc
      2 * ((d : ℝ) * (3 : ℝ) ^ (-(kZero d : ℤ))) =
          (2 * (d : ℝ)) * (3 : ℝ) ^ (-(kZero d : ℤ)) := by ring
      _ ≤ (3 : ℝ) ^ d * (3 : ℝ) ^ (-(kZero d : ℤ)) := hmul
      _ = 1 / 243 := hright
  have hnonneg :
      0 ≤ (d : ℝ) * (3 : ℝ) ^ (-(kZero d : ℤ)) := by positivity
  linarith only [htwice, hnonneg]

private theorem norm_baseRoundedGrid_sub_normalizedRoot_raw [NeZero d]
    {m : Mat d} (hm : m.PosDef) :
    ‖baseRoundedGrid m - Selection.normalizedRoot m‖ ≤
      (d : ℝ) * (3 : ℝ) ^ (-(kZero d : ℤ)) := by
  let E : Mat d := baseRoundedGrid m - Selection.normalizedRoot m
  let delta : ℝ := (3 : ℝ) ^ (-(kZero d : ℤ))
  let c : ℝ := (d : ℝ) * delta
  have hentry : ∀ i k, |E i k| ≤ delta := by
    intro i k
    obtain ⟨hlo, hhi⟩ :=
      Recurrence.roundedGrid_sub_normalized_matSqrt_mem (kZero d : ℤ) m i k
    rw [show E = baseRoundedGrid m - Selection.normalizedRoot m from rfl,
      baseRoundedGrid, Selection.normalizedRoot, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, abs_of_nonneg hlo]
    exact hhi
  have hsymm : Eᴴ = E := by
    rw [Matrix.IsHermitian.eq (Matrix.IsHermitian.sub
      (posDef_baseRoundedGrid hm).isHermitian
      (normalizedRoot_posDef_of_posDef hm).isHermitian)]
  have htrans : Eᵀ = E := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hsymm
  have hquadLo : ∀ x : Fin d → ℝ, -c * (x ⬝ᵥ x) ≤ x ⬝ᵥ E *ᵥ x := by
    intro x
    have h := Recurrence.neg_le_dotProduct_mulVec_of_abs_entry_le hentry x
    rw [show c = (d : ℝ) * delta from rfl,
      show delta = (3 : ℝ) ^ (-(kZero d : ℤ)) from rfl]
    simpa only [dotProduct, star_trivial, neg_mul, mul_assoc, mul_left_comm,
      mul_comm] using h
  have hquadHi : ∀ x : Fin d → ℝ, x ⬝ᵥ E *ᵥ x ≤ c * (x ⬝ᵥ x) := by
    intro x
    have h := Recurrence.neg_le_dotProduct_mulVec_of_abs_entry_le
      (E := -E) (fun i k ↦ by simpa using hentry i k) x
    rw [Matrix.neg_mulVec, dotProduct_neg, dotProduct] at h
    have h' := neg_le_neg_iff.mp h
    rw [dotProduct, show c = (d : ℝ) * delta from rfl,
      show delta = (3 : ℝ) ^ (-(kZero d : ℤ)) from rfl]
    simpa only [dotProduct, star_trivial, pow_two, mul_comm] using h'
  have hhi : E ≤ c • (1 : Mat d) := by
    rw [Matrix.le_iff]
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x ↦ ?_
    · simp [Matrix.IsHermitian, htrans]
    · rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
        Matrix.one_mulVec, dotProduct_smul]
      simp only [star_trivial, smul_eq_mul]
      linarith only [hquadHi x]
  have hlo : (-c) • (1 : Mat d) ≤ E := by
    rw [Matrix.le_iff]
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x ↦ ?_
    · simp [Matrix.IsHermitian, htrans]
    · rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
        Matrix.one_mulVec, dotProduct_smul]
      simp only [star_trivial, smul_eq_mul]
      linarith only [hquadLo x]
  exact PortableHistory.norm_le_of_sandwich hsymm
    (mul_nonneg (Nat.cast_nonneg _) (by positivity)) hhi hlo

/-- At the canonical rounded generation, the normalized-root error is below
one four-hundredth in operator norm. -/
theorem norm_baseRoundedGrid_sub_normalizedRoot_le [NeZero d]
    {m : Mat d} (hm : m.PosDef) :
    ‖baseRoundedGrid m - Selection.normalizedRoot m‖ ≤ (1 / 400 : ℝ) := by
  exact (norm_baseRoundedGrid_sub_normalizedRoot_raw hm).trans
    baseRoundedGrid_roundingScale_le

/-- The scalar-normalized symmetric reference, pulled back by the base rounded
grid, differs from the identity by at most one percent in operator norm. -/
theorem norm_baseRoundedReference_sub_one_le [NeZero d]
    {m : Mat d} (hm : m.PosDef) :
    ‖(baseRoundedGrid m)⁻¹ * (specBound m⁻¹ • m) *
          matTranspose (baseRoundedGrid m)⁻¹ - 1‖ ≤ (1 / 100 : ℝ) := by
  let q : Mat d := baseRoundedGrid m
  let L : Mat d := Selection.normalizedRoot m
  let E : Mat d := q - L
  let D : Mat d := q⁻¹ * E
  have hq : q.PosDef := posDef_baseRoundedGrid hm
  have hL : L.PosDef := normalizedRoot_posDef_of_posDef hm
  have hqdet : IsUnit q.det := isUnit_det_of_posDef hq
  have hqherm : qᴴ = q := hq.isHermitian
  have hqInvHerm : (q⁻¹)ᴴ = q⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hqherm]
  have hqInvT : matTranspose q⁻¹ = q⁻¹ := by
    simpa only [matTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hqInvHerm
  have hEherm : Eᴴ = E := by
    exact Matrix.IsHermitian.eq (hq.isHermitian.sub hL.isHermitian)
  have hDstar : Dᴴ = E * q⁻¹ := by
    rw [show D = q⁻¹ * E from rfl, Matrix.conjTranspose_mul,
      hEherm, hqInvHerm]
  have hLsq : L * L = specBound m⁻¹ • m := by
    simpa only [L] using normalizedRoot_mul_self hm
  have hform :
      q⁻¹ * (specBound m⁻¹ • m) * matTranspose q⁻¹ - 1 =
        (-D + -Dᴴ) + D * Dᴴ := by
    rw [← hLsq, hqInvT, show L = q - E by simp [E]]
    rw [hDstar, show D = q⁻¹ * E from rfl]
    have hleft : q⁻¹ * q = 1 := Matrix.nonsing_inv_mul q hqdet
    have hright : q * q⁻¹ = 1 := Matrix.mul_nonsing_inv q hqdet
    have hmiddle : q⁻¹ * (q * (E * q⁻¹)) = E * q⁻¹ := by
      rw [← Matrix.mul_assoc, hleft, Matrix.one_mul]
    noncomm_ring [hleft, hright, hmiddle]
  have hEnorm : ‖E‖ ≤ (1 / 400 : ℝ) := by
    simpa only [E, q, L] using norm_baseRoundedGrid_sub_normalizedRoot_le hm
  have hqInvNorm : ‖q⁻¹‖ ≤ (101 / 100 : ℝ) := by
    simpa only [q] using norm_inv_baseRoundedGrid_le hm
  have hDnorm : ‖D‖ ≤ (101 / 40000 : ℝ) := by
    calc
      ‖D‖ = ‖q⁻¹ * E‖ := rfl
      _ ≤ ‖q⁻¹‖ * ‖E‖ := norm_mul_le _ _
      _ ≤ (101 / 100 : ℝ) * (1 / 400 : ℝ) :=
        mul_le_mul hqInvNorm hEnorm (norm_nonneg E) (by norm_num)
      _ = 101 / 40000 := by ring
  have hnormStar : ‖Dᴴ‖ = ‖D‖ := Matrix.l2_opNorm_conjTranspose D
  have hfirst : ‖-D + -Dᴴ‖ ≤ ‖D‖ + ‖D‖ := by
    simpa only [norm_neg, hnormStar] using norm_add_le (-D) (-Dᴴ)
  have hproduct : ‖D * Dᴴ‖ ≤ ‖D‖ * ‖D‖ := by
    simpa only [hnormStar] using norm_mul_le D Dᴴ
  rw [show baseRoundedGrid m = q from rfl, hform]
  calc
    ‖(-D + -Dᴴ) + D * Dᴴ‖ ≤
        ‖-D + -Dᴴ‖ + ‖D * Dᴴ‖ := norm_add_le _ _
    _ ≤ (‖D‖ + ‖D‖) + ‖D‖ * ‖D‖ :=
      add_le_add hfirst hproduct
    _ ≤ 1 / 100 := by
      nlinarith only [hDnorm, norm_nonneg D,
        sq_nonneg ((101 / 40000 : ℝ) - ‖D‖)]

/-- Pointwise operator-norm form of the rounded reference estimate. -/
theorem norm_roundedSymmetricReferenceCoefficient_sub_one_le [NeZero d]
    (abar : Mat d) (hS : (symmPart abar).PosDef) (y : Vec d) :
    ‖roundedSymmetricReferenceCoefficient abar hS y - 1‖ ≤
      (1 / 100 : ℝ) := by
  simpa only [roundedSymmetricReferenceCoefficient_apply] using
    norm_baseRoundedReference_sub_one_le hS

/-- The source's literal `99/100`--`101/100` matrix-order sandwich for the
constant symmetric reference in rounded coordinates. -/
theorem roundedSymmetricReferenceCoefficient_order_bounds [NeZero d]
    (abar : Mat d) (hS : (symmPart abar).PosDef) (y : Vec d) :
    (99 / 100 : ℝ) • (1 : Mat d) ≤
        roundedSymmetricReferenceCoefficient abar hS y ∧
      roundedSymmetricReferenceCoefficient abar hS y ≤
        (101 / 100 : ℝ) • (1 : Mat d) := by
  let B : Mat d := roundedSymmetricReferenceCoefficient abar hS y
  let q : Mat d := baseRoundedGrid (symmPart abar)
  let L : Mat d := Selection.normalizedRoot (symmPart abar)
  let C : Mat d := q⁻¹ * L
  have hq : q.PosDef := posDef_baseRoundedGrid hS
  have hL : L.PosDef := normalizedRoot_posDef_of_posDef hS
  have hqInvHerm : (q⁻¹)ᴴ = q⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hq.isHermitian]
  have hCstar : Cᴴ = L * q⁻¹ := by
    rw [show C = q⁻¹ * L from rfl, Matrix.conjTranspose_mul,
      hL.isHermitian, hqInvHerm]
  have hqInvT : matTranspose q⁻¹ = q⁻¹ := by
    simpa only [matTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hqInvHerm
  have hLsq : L * L = specBound (symmPart abar)⁻¹ • symmPart abar := by
    simpa only [L] using normalizedRoot_mul_self hS
  have hBform : B = C * Cᴴ := by
    rw [show B = roundedSymmetricReferenceCoefficient abar hS y from rfl,
      roundedSymmetricReferenceCoefficient_apply,
      show baseRoundedGrid (symmPart abar) = q from rfl,
      ← hLsq, hqInvT, hCstar, show C = q⁻¹ * L from rfl]
    noncomm_ring
  have hBpsd : B.PosSemidef := by
    rw [hBform]
    exact Matrix.posSemidef_self_mul_conjTranspose C
  have hdiffHerm : (B - 1)ᴴ = B - 1 :=
    Matrix.IsHermitian.eq (hBpsd.isHermitian.sub Matrix.PosSemidef.one.isHermitian)
  have hnorm : ‖B - 1‖ ≤ (1 / 100 : ℝ) := by
    simpa only [B] using
      norm_roundedSymmetricReferenceCoefficient_sub_one_le abar hS y
  obtain ⟨hupper, hlower⟩ := PortableHistory.sandwich_of_norm_le hdiffHerm hnorm
  constructor
  · calc
      (99 / 100 : ℝ) • (1 : Mat d) =
          (-(1 / 100 : ℝ)) • (1 : Mat d) + 1 := by module
      _ ≤ (B - 1) + 1 := by
        simpa only [add_comm] using add_le_add_right hlower 1
      _ = roundedSymmetricReferenceCoefficient abar hS y := by
        rw [show B = roundedSymmetricReferenceCoefficient abar hS y from rfl]
        abel
  · calc
      roundedSymmetricReferenceCoefficient abar hS y = (B - 1) + 1 := by
        rw [show B = roundedSymmetricReferenceCoefficient abar hS y from rfl]
        abel
      _ ≤ (1 / 100 : ℝ) • (1 : Mat d) + 1 :=
        by simpa only [add_comm] using add_le_add_right hupper 1
      _ = (101 / 100 : ℝ) • (1 : Mat d) := by module

end

end HighContrast
end HCPolySupport
