/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.DeterminantLoss
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.MajorizationSize
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.RoundedGrid
public import LeanPool.HighContrastHomogenization.Provider.ShortHop.Eccentricity

/-!
# High-contrast homogenization: Provider.Selection.RoundedHops

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section
/-!
# Rounded projective hops

This file proves the any-pair form of `l.projective.step`.
The normalized square roots have least singular value one, entrywise rounding
is a uniformly small perturbation, and projective distance controls the two
normalized cross maps.  No absolute eccentricity is assumed.
-/
namespace HCPolySupport.HighContrast.Selection
open scoped MatrixOrder Matrix.Norms.L2Operator Matrix
noncomputable section
variable {d : ℕ} [NeZero d]
/-- The normalized square root `𝒛(m)=|m⁻¹|¹⁄²m¹⁄²`, the matrix the rounding of
`s.scale.selection` rounds. -/
@[expose]
def normalizedRoot (m : Mat d) : Mat d :=
  Real.sqrt (specBound m⁻¹) • matSqrt m
omit [NeZero d] in
/-- The defining equation for the normalized square root. -/
theorem normalizedRoot_eq (m : Mat d) :
    normalizedRoot m = Real.sqrt (specBound m⁻¹) • matSqrt m := rfl
private theorem specBound_pos_of_posDef {m : Mat d} (hm : m.PosDef) :
    0 < specBound m := by
  rw [specBound_eq_norm hm.posSemidef]
  exact norm_pos_iff.mpr hm.isUnit.ne_zero
private theorem normalizedRoot_posDef {m : Mat d} (hm : m.PosDef) :
    (normalizedRoot m).PosDef := by
  refine (posDef_matSqrt hm).smul (Real.sqrt_pos.mpr ?_)
  exact specBound_pos_of_posDef hm.inv
private theorem normalizedRoot_inv_norm_le_one {m : Mat d} (hm : m.PosDef) :
    ‖(normalizedRoot m)⁻¹‖ ≤ 1 := by
  have hL := normalizedRoot_posDef hm
  have horder : (1 : Mat d) ≤ normalizedRoot m := Recurrence.one_le_normalized_matSqrt hm
  have hinv : (normalizedRoot m)⁻¹ ≤ (1 : Mat d) := by
    simpa using inv_le_inv_of_le Matrix.PosDef.one hL horder
  have hnorm := norm_le_norm_of_le hL.inv.posSemidef Matrix.PosSemidef.one hinv
  simpa using hnorm
omit [NeZero d] in
private theorem norm_matSqrt_eq {m : Mat d} (hm : m.PosDef) :
    ‖matSqrt m‖ = Real.sqrt (specBound m) := by
  have hherm : (matSqrt m)ᴴ = matSqrt m := (matSqrt_spec hm.posSemidef).1.isHermitian
  have hsq : ‖matSqrt m‖ ^ 2 = specBound m := by
    rw [pow_two, ← CStarRing.norm_self_mul_star, Matrix.star_eq_conjTranspose, hherm,
      (matSqrt_spec hm.posSemidef).2, specBound_eq_norm hm.posSemidef]
  symm
  exact (Real.sqrt_eq_iff_eq_sq (specBound_nonneg m) (norm_nonneg _)).mpr hsq.symm
omit [NeZero d] in
private theorem norm_normalizedRoot {m : Mat d} (hm : m.PosDef) :
    ‖normalizedRoot m‖ = witnessEccentricity m := by
  rw [normalizedRoot, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    norm_matSqrt_eq hm, witnessEccentricity, ← Real.sqrt_mul (specBound_nonneg m⁻¹),
    mul_comm]
private theorem rounded_error_norm {l : ℤ} {m : Mat d} (hm : m.PosDef) :
    ‖roundedGrid l m - normalizedRoot m‖ ≤ (d : ℝ) * (3 : ℝ) ^ (-l) := by
  set E : Mat d := roundedGrid l m - normalizedRoot m with hE
  set delta : ℝ := (3 : ℝ) ^ (-l) with hdelta
  set t : ℝ := (d : ℝ) * delta with ht
  have hentry : ∀ i k, |E i k| ≤ delta := by
    intro i k
    obtain ⟨h0, h1⟩ := Recurrence.roundedGrid_sub_normalized_matSqrt_mem l m i k
    rw [hE, normalizedRoot, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      abs_of_nonneg h0]
    exact h1
  have hsymm : Eᴴ = E := by
    rw [Matrix.IsHermitian.eq (Matrix.IsHermitian.sub
      (by
        refine Matrix.IsHermitian.ext fun i k => ?_
        simpa using Recurrence.roundedGrid_symm l hm.posSemidef i k)
      (normalizedRoot_posDef hm).isHermitian)]
  have htrans : Eᵀ = E := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hsymm
  have hquadLo : ∀ x : Fin d → ℝ, -t * (x ⬝ᵥ x) ≤ x ⬝ᵥ E *ᵥ x := by
    intro x
    have h := Recurrence.neg_le_dotProduct_mulVec_of_abs_entry_le hentry x
    rw [dotProduct, ht]
    convert h using 1; ring
  have hquadHi : ∀ x : Fin d → ℝ, x ⬝ᵥ E *ᵥ x ≤ t * (x ⬝ᵥ x) := by
    intro x
    have h := Recurrence.neg_le_dotProduct_mulVec_of_abs_entry_le
      (E := -E) (fun i k => by simpa using hentry i k) x
    rw [Matrix.neg_mulVec, dotProduct_neg, dotProduct] at h
    have h' := neg_le_neg_iff.mp h
    rw [dotProduct, ht]
    simpa only [dotProduct, star_trivial, pow_two, mul_comm] using h'
  have hup : E ≤ t • (1 : Mat d) := by
    rw [Matrix.le_iff]
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · simp [Matrix.IsHermitian, htrans]
    · rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_smul]
      simp only [star_trivial, smul_eq_mul]
      linarith only [hquadHi x]
  have hlo : (-t) • (1 : Mat d) ≤ E := by
    rw [Matrix.le_iff]
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · simp [Matrix.IsHermitian, htrans]
    · rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_smul]
      simp only [star_trivial, smul_eq_mul]
      linarith only [hquadLo x]
  have hnorm := PortableHistory.norm_le_of_sandwich hsymm
    (mul_nonneg (Nat.cast_nonneg _) (by positivity)) hup hlo
  exact hnorm
private theorem rounded_error_norm_le {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {m : Mat d} (hm : m.PosDef) :
    ‖roundedGrid l m - normalizedRoot m‖ ≤ 1 / 101 := by
  refine (rounded_error_norm hm).trans ?_
  have hpow : (3 : ℝ) ^ (-l) ≤ (3 : ℝ) ^ (-(kZero d : ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  exact (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)).trans (kZero_spec d)
private theorem normalizedRoot_inv_mul_roundedGrid_le {l : ℤ}
    (hl : (kZero d : ℤ) ≤ l) {m : Mat d} (hm : m.PosDef) :
    ‖(normalizedRoot m)⁻¹ * roundedGrid l m‖ ≤ 102 / 101 := by
  set L := normalizedRoot m
  set E := roundedGrid l m - L
  have hfac : L⁻¹ * roundedGrid l m = 1 + L⁻¹ * E := by
    have hunit : IsUnit L.det := isUnit_det_of_posDef (normalizedRoot_posDef hm)
    have hsplit : roundedGrid l m = L + E := by simp [E]
    rw [hsplit, Matrix.mul_add, Matrix.nonsing_inv_mul _ hunit]
  have hB := (norm_mul_le L⁻¹ E).trans
    (mul_le_mul (normalizedRoot_inv_norm_le_one hm) (rounded_error_norm_le hl hm)
      (norm_nonneg _) zero_le_one)
  rw [hfac]
  calc ‖1 + L⁻¹ * E‖ ≤ 1 + ‖L⁻¹ * E‖ := by simpa using norm_add_le (1 : Mat d) (L⁻¹ * E)
    _ ≤ 102 / 101 := by linarith only [hB]
private theorem roundedGrid_inv_mul_normalizedRoot_le {l : ℤ}
    (hl : (kZero d : ℤ) ≤ l) {m : Mat d} (hm : m.PosDef) :
    ‖(roundedGrid l m)⁻¹ * normalizedRoot m‖ ≤ 101 / 100 := by
  set L := normalizedRoot m
  set E := roundedGrid l m - L
  set B := L⁻¹ * E
  have hB := (norm_mul_le L⁻¹ E).trans
    (mul_le_mul (normalizedRoot_inv_norm_le_one hm) (rounded_error_norm_le hl hm)
      (norm_nonneg _) zero_le_one)
  have hBlt : ‖-B‖ < 1 := by rw [norm_neg]; linarith only [hB]
  have hfac : L⁻¹ * roundedGrid l m = 1 + B := by
    have hunit : IsUnit L.det := isUnit_det_of_posDef (normalizedRoot_posDef hm)
    have hsplit : roundedGrid l m = L + E := by simp [E]
    rw [hsplit, Matrix.mul_add, Matrix.nonsing_inv_mul _ hunit]
  have hinv : (L⁻¹ * roundedGrid l m)⁻¹ = (roundedGrid l m)⁻¹ * L := by
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _
      (isUnit_det_of_posDef (normalizedRoot_posDef hm))]
  have hgeom := tsum_geometric_le_of_norm_lt_one (-B) hBlt
  rw [geom_series_eq_inverse (-B) hBlt, sub_neg_eq_add, norm_neg, norm_one,
    sub_self, zero_add, ← hfac, ← Matrix.nonsing_inv_eq_ringInverse, hinv] at hgeom
  refine hgeom.trans ?_
  have hB' : ‖B‖ ≤ 1 / 101 := by simpa only [B, one_mul] using hB
  rw [inv_le_iff_one_le_mul₀' (by linarith only [hB'])]
  linarith only [hB']
/-- **The absolute inverse bound** in
`e.rounded.grid.bounds`. -/
theorem norm_inv_roundedGrid_le {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {m : Mat d} (hm : m.PosDef) : ‖(roundedGrid l m)⁻¹‖ ≤ 101 / 100 := by
  set L := normalizedRoot m
  have hunit : IsUnit L.det := isUnit_det_of_posDef (normalizedRoot_posDef hm)
  have hfactor : (roundedGrid l m)⁻¹ = (roundedGrid l m)⁻¹ * L * L⁻¹ := by
    symm
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one]
  rw [hfactor]
  calc ‖(roundedGrid l m)⁻¹ * L * L⁻¹‖
      ≤ ‖(roundedGrid l m)⁻¹ * L‖ * ‖L⁻¹‖ := norm_mul_le _ _
    _ ≤ (101 / 100 : ℝ) * 1 := mul_le_mul
      (roundedGrid_inv_mul_normalizedRoot_le hl hm)
      (normalizedRoot_inv_norm_le_one hm) (norm_nonneg _) (by positivity)
    _ = 101 / 100 := by norm_num
/-- **The absolute grid bound** in
`e.rounded.grid.bounds`. -/
theorem norm_roundedGrid_le {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {m : Mat d} (hm : m.PosDef) :
    ‖roundedGrid l m‖ ≤ (100 / 99) * witnessEccentricity m := by
  have hsplit : roundedGrid l m = normalizedRoot m +
      (roundedGrid l m - normalizedRoot m) := by abel
  have hone : 1 ≤ witnessEccentricity m := by
    rw [← norm_normalizedRoot hm]
    have hnorm := norm_le_norm_of_le Matrix.PosSemidef.one
      (normalizedRoot_posDef hm).posSemidef (Recurrence.one_le_normalized_matSqrt hm)
    simpa using hnorm
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_normalizedRoot hm]
  linarith only [rounded_error_norm_le hl hm, hone]

private theorem normalized_cross_le_exp {m₀ m₁ : Mat d}
    (h₀ : m₀.PosDef) (h₁ : m₁.PosDef) :
    ‖(normalizedRoot m₀)⁻¹ * normalizedRoot m₁‖ ≤ Real.exp (projDist m₀ m₁) := by
  set s₀ := Real.sqrt (specBound m₀⁻¹)
  set s₁ := Real.sqrt (specBound m₁⁻¹)
  set A := matSqrt m₀⁻¹ * matSqrt m₁
  have hs₀ : 0 < s₀ := Real.sqrt_pos.mpr (specBound_pos_of_posDef h₀.inv)
  have hs₁ : 0 < s₁ := Real.sqrt_pos.mpr (specBound_pos_of_posDef h₁.inv)
  have hform : (normalizedRoot m₀)⁻¹ * normalizedRoot m₁ = (s₀⁻¹ * s₁) • A := by
    rw [normalizedRoot, normalizedRoot, inv_smul_of_isUnit hs₀.ne'
      ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_matSqrt h₀)),
      ← matSqrt_inv h₀, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hA : ‖A‖ ^ 2 = relSize m₁ m₀ := by
    simp only [A]
    have hroot : matSqrt m₀⁻¹ * matSqrt m₁ * (matSqrt m₁ * matSqrt m₀⁻¹) =
        matSqrt m₀⁻¹ * m₁ * matSqrt m₀⁻¹ := by
      calc
        _ = matSqrt m₀⁻¹ * (matSqrt m₁ * matSqrt m₁) * matSqrt m₀⁻¹ := by
          noncomm_ring
        _ = _ := by rw [(matSqrt_spec h₁.posSemidef).2]
    rw [pow_two, ← CStarRing.norm_self_mul_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_mul, conjTranspose_matSqrt_inv h₀,
      (matSqrt_spec h₁.posSemidef).1.isHermitian, hroot, relSize_def]
  have hr : 0 < relSize m₀ m₁ := relSize_pos h₀ h₁
  have hinv := inv_le_inv_of_le h₀ (posDef_smul h₁ hr)
    (le_relSize_smul h₀.posSemidef h₁)
  rw [inv_smul_of_isUnit hr.ne' (isUnit_det_of_posDef h₁)] at hinv
  have hscaled := smul_le_smul_of_le hr.le hinv
  rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at hscaled
  have hspec := norm_le_norm_of_le h₁.inv.posSemidef
    (posDef_smul h₀.inv hr).posSemidef hscaled
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.le,
    ← specBound_eq_norm h₁.inv.posSemidef,
    ← specBound_eq_norm h₀.inv.posSemidef] at hspec
  have hc : (s₀⁻¹ * s₁) ^ 2 ≤ relSize m₀ m₁ := by
    change ((Real.sqrt (specBound m₀⁻¹))⁻¹ *
      Real.sqrt (specBound m₁⁻¹)) ^ 2 ≤ relSize m₀ m₁
    rw [show (Real.sqrt (specBound m₀⁻¹))⁻¹ *
        Real.sqrt (specBound m₁⁻¹) = Real.sqrt (specBound m₁⁻¹) /
          Real.sqrt (specBound m₀⁻¹) by rw [div_eq_mul_inv, mul_comm],
      div_pow, Real.sq_sqrt (specBound_nonneg _), Real.sq_sqrt (specBound_nonneg _),
      div_le_iff₀ (specBound_pos_of_posDef h₀.inv)]
    simpa [div_eq_mul_inv, mul_comm] using hspec
  have hsq : ‖(normalizedRoot m₀)⁻¹ * normalizedRoot m₁‖ ^ 2 ≤
      relSize m₀ m₁ * relSize m₁ m₀ := by
    rw [hform, norm_smul, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (inv_nonneg.mpr hs₀.le) hs₁.le), mul_pow, hA]
    exact mul_le_mul_of_nonneg_right hc (relSize_nonneg _ _)
  have hexp : Real.exp (projDist m₀ m₁) ^ 2 =
      relSize m₀ m₁ * relSize m₁ m₀ := by
    rw [projDist_def, ← Real.exp_nat_mul]
    have hr₀ := relSize_pos h₀ h₁
    have hr₁ := relSize_pos h₁ h₀
    rw [show ((2 : ℕ) : ℝ) * ((1 / 2) *
      (Real.log (relSize m₁ m₀) + Real.log (relSize m₀ m₁))) =
        Real.log (relSize m₁ m₀) + Real.log (relSize m₀ m₁) by ring,
      Real.exp_add, Real.exp_log hr₁, Real.exp_log hr₀, mul_comm]
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp (hexp.symm ▸ hsq)

private theorem rounded_cross_le {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {m₀ m₁ : Mat d} (h₀ : m₀.PosDef) (h₁ : m₁.PosDef) {chop : ℝ}
    (hdist : projDist m₀ m₁ ≤ chop) :
    ‖(roundedGrid l m₀)⁻¹ * roundedGrid l m₁‖ ≤ (51 / 50) * Real.exp chop := by
  set L₀ := normalizedRoot m₀
  set L₁ := normalizedRoot m₁
  have hu₀ : IsUnit L₀.det := isUnit_det_of_posDef (normalizedRoot_posDef h₀)
  have hu₁ : IsUnit L₁.det := isUnit_det_of_posDef (normalizedRoot_posDef h₁)
  have hfactor : (roundedGrid l m₀)⁻¹ * roundedGrid l m₁ =
      ((roundedGrid l m₀)⁻¹ * L₀) * (L₀⁻¹ * L₁) *
        (L₁⁻¹ * roundedGrid l m₁) := by
    symm
    calc
      ((roundedGrid l m₀)⁻¹ * L₀) * (L₀⁻¹ * L₁) *
          (L₁⁻¹ * roundedGrid l m₁) =
        (roundedGrid l m₀)⁻¹ * (L₀ * L₀⁻¹) *
          (L₁ * L₁⁻¹) * roundedGrid l m₁ := by noncomm_ring
      _ = (roundedGrid l m₀)⁻¹ * roundedGrid l m₁ := by
        simp only [Matrix.mul_nonsing_inv _ hu₀, Matrix.mul_nonsing_inv _ hu₁,
          Matrix.mul_one]
  have hcross := (normalized_cross_le_exp h₀ h₁).trans (Real.exp_le_exp.mpr hdist)
  rw [hfactor]
  calc ‖((roundedGrid l m₀)⁻¹ * L₀) * (L₀⁻¹ * L₁) *
          (L₁⁻¹ * roundedGrid l m₁)‖
      ≤ (‖(roundedGrid l m₀)⁻¹ * L₀‖ * ‖L₀⁻¹ * L₁‖) *
          ‖L₁⁻¹ * roundedGrid l m₁‖ :=
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ((101 / 100) * Real.exp chop) * (102 / 101) :=
      mul_le_mul (mul_le_mul (roundedGrid_inv_mul_normalizedRoot_le hl h₀) hcross
        (norm_nonneg _) (by positivity)) (normalizedRoot_inv_mul_roundedGrid_le hl h₁)
        (norm_nonneg _) (by positivity)
    _ = (51 / 50) * Real.exp chop := by ring

/-- The explicit rounded-hop constant used below. -/
@[expose]
def hopConstant (d : ℕ) (chop : ℝ) : ℝ :=
  (1 + 2 * ((51 / 50) * Real.exp chop)) ^ (2 * d)

omit [NeZero d] in
/-- **The general any-pair rounded-hop bound.** -/
theorem rounded_projective_hop (hd : 2 ≤ d) {chop : ℝ} {l : ℤ}
    (hl : (kZero d : ℤ) ≤ l) {m₀ m₁ : Mat d} (h₀ : m₀.PosDef)
    (h₁ : m₁.PosDef) (hdist : projDist m₀ m₁ ≤ chop) :
    gridRatio (roundedGrid l m₀) (roundedGrid l m₁) ≤ hopConstant d chop := by
  let : NeZero d := ⟨by omega⟩
  have h₁₀ : projDist m₁ m₀ ≤ chop := by rwa [projDist_comm]
  have hleft := rounded_cross_le hl h₀ h₁ hdist
  have hright := rounded_cross_le hl h₁ h₀ h₁₀
  rw [gridRatio, hopConstant]
  exact pow_le_pow_left₀ (by positivity)
    (by linarith only [hleft, hright]) (2 * d)

omit [NeZero d] in
/-- **Existence of a single rounded-hop constant**, in the exact any-pair form
consumed by the frozen short-hop theorem. -/
theorem exists_hopConstant (hd : 2 ≤ d) (chop : ℝ) :
    ∃ Khop : ℝ, 1 ≤ Khop ∧
      ∀ l : ℤ, (kZero d : ℤ) ≤ l → ∀ m₀ m₁ : Mat d,
        m₀.PosDef → m₁.PosDef → projDist m₀ m₁ ≤ chop →
          gridRatio (roundedGrid l m₀) (roundedGrid l m₁) ≤ Khop := by
  let : NeZero d := ⟨by omega⟩
  refine ⟨hopConstant d chop, ?_, ?_⟩
  · rw [hopConstant]
    exact one_le_pow₀ (by linarith only [Real.exp_pos chop])
  · intro l hl m₀ m₁ h₀ h₁ hdist
    exact rounded_projective_hop hd hl h₀ h₁ hdist

/-- The witness identity for the eccentricity of a rounded geometry. -/
theorem rounded_witnessEccentricity_eq_exp {m : Mat d} (hm : m.PosDef) :
    witnessEccentricity m = Real.exp (projDist 1 m) :=
  ShortHop.witnessEccentricity_eq_exp hm

/-- A dimension-only constant for the identity-grid witness bound. -/
@[expose]
def witnessGridConstant (d : ℕ) : ℝ := (2 : ℝ) ^ (2 * d)

/-- The defining equation for the identity-grid constant. -/
theorem witnessGridConstant_eq (d : ℕ) :
    witnessGridConstant d = (2 : ℝ) ^ (2 * d) := rfl

omit [NeZero d] in
/-- The comparison constant between a rounded geometry and the Euclidean
grid. -/
theorem gridRatio_roundedGrid_one_le (hd : 2 ≤ d) {l : ℤ}
    (hl : (kZero d : ℤ) ≤ l) {m : Mat d} (hm : m.PosDef) :
    gridRatio (roundedGrid l m) 1 ≤ witnessGridConstant d *
      (1 + witnessEccentricity m) ^ (2 * d) := by
  let : NeZero d := ⟨by omega⟩
  have hecc : 1 ≤ witnessEccentricity m := by
    have hnorm := norm_mul_le m m⁻¹
    rw [Matrix.mul_nonsing_inv m (isUnit_det_of_posDef hm), norm_one,
      ← specBound_eq_norm hm.posSemidef, ← specBound_eq_norm hm.inv.posSemidef] at hnorm
    simpa [witnessEccentricity] using Real.sqrt_le_sqrt hnorm
  have hbase : 1 + ‖(roundedGrid l m)⁻¹‖ + ‖roundedGrid l m‖ ≤
      2 * (1 + witnessEccentricity m) := by
    linarith only [norm_inv_roundedGrid_le hl hm, norm_roundedGrid_le hl hm, hecc]
  rw [gridRatio, inv_one, Matrix.mul_one, Matrix.one_mul, witnessGridConstant]
  calc (1 + ‖(roundedGrid l m)⁻¹‖ + ‖roundedGrid l m‖) ^ (2 * d)
      ≤ (2 * (1 + witnessEccentricity m)) ^ (2 * d) :=
        pow_le_pow_left₀ (by positivity) hbase _
    _ = 2 ^ (2 * d) * (1 + witnessEccentricity m) ^ (2 * d) := by rw [mul_pow]

end
end HCPolySupport.HighContrast.Selection
