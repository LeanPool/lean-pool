/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineSlopeBijective

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineSlopeTerminalInverse

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Terminal inverse slope-matrix closeness

This module constructs the terminal inverse only from proved bijectivity and
transfers terminal forward-map closeness to operator-norm inverse closeness.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

private theorem euclideanNorm_add_le_local {d : ℕ} (x y : Vec d) :
    euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by
  rw [euclideanNorm_eq_norm_ofVec, euclideanNorm_eq_norm_ofVec,
    euclideanNorm_eq_norm_ofVec]
  exact norm_add_le _ _

private theorem matrixNorm_le_of_euclideanNorm_mulVec_le
    {d : ℕ} (A : Mat d) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ x : Vec d,
      euclideanNorm (matVecMul A x) ≤ K * euclideanNorm x) :
    Book.Ch02.matrixNorm A ≤ K := by
  unfold Book.Ch02.matrixNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hK ?_
  intro x
  let y : Vec d := HilbertVec.toVec x
  have hy : HilbertVec.ofVec y = x := HilbertVec.ofVec_toVec x
  have hx := h y
  rw [euclideanNorm_eq_norm_ofVec, euclideanNorm_eq_norm_ofVec] at hx
  simpa only [hy, Matrix.toEuclideanCLM_toLp, matVecMul] using! hx

/-- On a sufficiently small GoodMax row, the proof-gated terminal inverse
best-fit slope matrix differs from the identity by `O(delta)` in the source
operator norm. -/
theorem exists_scalarIdentityFiniteAffineSlopeTerminalInverseConstants
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C c : ℝ, 1 ≤ C ∧ c ∈ Set.Ioc (0 : ℝ) ((2 * C)⁻¹) ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n m : ℤ),
        n < m → delta ∈ Set.Ioc (0 : ℝ) c →
          ScalarIdentityGoodMaxOnInterval a s delta n m →
          ∃ hbij : Function.Bijective
              (finiteAffineBestFitSlope a m m le_rfl),
            Book.Ch02.matrixNorm
                (finiteAffineBestFitSlopeInverseMatrix a m m le_rfl hbij - 1) ≤
              C * delta := by
  obtain ⟨B, cb, hB, hcb, hbounds⟩ :=
    exists_scalarIdentityFiniteAffineBestFitInductionConstants d s hs hs_lt
  obtain ⟨J, cj, hJ, hcj, hbijective⟩ :=
    exists_scalarIdentityFiniteAffineSlopeBijectiveConstants d s hs hs_lt
  let C : ℝ := 1 + 2 * B + J
  let c : ℝ := min cb (min cj ((2 * C)⁻¹))
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hC : 1 ≤ C := by dsimp [C]; linarith only [hB, hJ]
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have h2BC : 2 * B ≤ C := by dsimp [C]; linarith only [hJ]
  have hcpos : 0 < c := by
    dsimp [c]
    exact lt_min hcb.1 (lt_min hcj.1
      (inv_pos.mpr (mul_pos (by norm_num) hCpos)))
  have hcC : c ≤ (2 * C)⁻¹ := by
    dsimp [c]
    exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨C, c, hC, ⟨hcpos, hcC⟩, ?_⟩
  intro a delta n m hnm hdelta hgood
  have hm : m ∈ Finset.Icc n m := Finset.mem_Icc.mpr ⟨hnm.le, le_rfl⟩
  have hdeltaB : delta ∈ Set.Ioc (0 : ℝ) cb :=
    ⟨hdelta.1, hdelta.2.trans (min_le_left _ _)⟩
  have hdeltaJ : delta ∈ Set.Ioc (0 : ℝ) cj :=
    ⟨hdelta.1, hdelta.2.trans
      ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hsmall : B * delta ≤ 1 / 2 := by
    have hd : delta ≤ (2 * B)⁻¹ := hdeltaB.2.trans hcb.2
    calc
      B * delta ≤ B * (2 * B)⁻¹ :=
        mul_le_mul_of_nonneg_left hd hBpos.le
      _ = 1 / 2 := by field_simp
  obtain ⟨hbij, _hdet⟩ :=
    hbijective a delta n m hnm hdeltaJ hgood m hm
  refine ⟨hbij, ?_⟩
  let Q : Mat d := finiteAffineBestFitSlopeInverseMatrix a m m le_rfl hbij
  have hpoint : ∀ e : Vec d,
      euclideanNorm (matVecMul (Q - 1) e) ≤
        (2 * B * delta) * euclideanNorm e := by
    intro e
    let b : Vec d := matVecMul Q e
    have hPb : finiteAffineBestFitSlope a m m le_rfl b = e := by
      simpa only [Q, b] using
        finiteAffineBestFitSlope_apply_inverseMatrix a m m le_rfl hbij e
    have hterminal :=
      (hbounds a delta n m hnm hdeltaB hgood m hm b).2.2.2 rfl
    rw [hPb] at hterminal
    have hdiff : euclideanNorm (b - e) ≤ B * delta * euclideanNorm b := by
      rw [show b - e = -(e - b) by abel, euclideanNorm_neg]
      exact hterminal
    have hbtri : euclideanNorm b ≤
        euclideanNorm (b - e) + euclideanNorm e := by
      calc
        euclideanNorm b = euclideanNorm ((b - e) + e) := by congr 1; abel
        _ ≤ euclideanNorm (b - e) + euclideanNorm e :=
          euclideanNorm_add_le_local _ _
    have hb : euclideanNorm b ≤ 2 * euclideanNorm e := by
      have hstep : euclideanNorm b ≤
          (1 / 2 : ℝ) * euclideanNorm b + euclideanNorm e := by
        calc
          euclideanNorm b ≤ euclideanNorm (b - e) + euclideanNorm e := hbtri
          _ ≤ (B * delta) * euclideanNorm b + euclideanNorm e :=
            by gcongr
          _ ≤ (1 / 2 : ℝ) * euclideanNorm b + euclideanNorm e := by
            have hmul := mul_le_mul_of_nonneg_right hsmall (euclideanNorm_nonneg b)
            linarith only [hmul]
      linarith only [hstep]
    have hBd_nonneg : 0 ≤ B * delta :=
      mul_nonneg hBpos.le hdelta.1.le
    calc
      euclideanNorm (matVecMul (Q - 1) e) = euclideanNorm (b - e) := by
        rw [sub_matVecMul, matVecMul_one]
      _ ≤ B * delta * euclideanNorm b := hdiff
      _ ≤ B * delta * (2 * euclideanNorm e) :=
        mul_le_mul_of_nonneg_left hb hBd_nonneg
      _ = (2 * B * delta) * euclideanNorm e := by ring
  have hnorm : Book.Ch02.matrixNorm (Q - 1) ≤ 2 * B * delta := by
    exact matrixNorm_le_of_euclideanNorm_mulVec_le (Q - 1) (2 * B * delta)
      (mul_nonneg (mul_nonneg (by norm_num) hBpos.le) hdelta.1.le) hpoint
  calc
    Book.Ch02.matrixNorm
        (finiteAffineBestFitSlopeInverseMatrix a m m le_rfl hbij - 1) =
        Book.Ch02.matrixNorm (Q - 1) := rfl
    _ ≤ 2 * B * delta := hnorm
    _ ≤ C * delta := mul_le_mul_of_nonneg_right h2BC hdelta.1.le

end

end HighContrast
end HCPolySupport
