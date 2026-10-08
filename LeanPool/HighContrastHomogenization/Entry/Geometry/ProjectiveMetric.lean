/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.PositiveSqrtCongruence

/-!
# High-contrast homogenization: Entry.Geometry.ProjectiveMetric

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Metric support for the projective distance

For positive definite matrices `m₀ m₁ : Mat d`, the projective distance
`projectiveDistance m₀ m₁` is half the logarithm of the optimal relative Loewner spread.
The spectral thresholds `specMin` and `specBound` of the normalized relative matrix
`normalizedMat m₀ m₁` are attained at its eigenvalues, and they are exactly the sharp
lower and upper thresholds of the relative comparisons `t • m₀` against `m₁`, so the
distance is `1 / 2 * Real.log (U / L)` for those two thresholds.  The distance is
nonnegative, vanishes exactly on the positive-scalar equivalence classes, is invariant
under positive scaling of its right endpoint, and satisfies the triangle inequality;
from the identity it equals half the logarithm of the eccentricity `‖m‖ * ‖m⁻¹‖`.
These are the metric facts used by `l.projective.step`, and the triangle inequality is
used in the finite run of `p.global.selection`.
-/

open HCPolySupport.HighContrast (matLoewnerLE_smul_one_of_le matLoewnerLE_specBound_smul_one
  matSqrt specBound)
namespace HCPolySupport.HighContrast.Geometry

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The lower and upper Loewner thresholds are attained eigenvalues. -/
theorem spectral_extrema_attained {M : Mat d} [NeZero d] (hM : M.PosDef) :
    ∃ i j : Fin d, specMin M = hM.isHermitian.eigenvalues i ∧
      specBound M = hM.isHermitian.eigenvalues j ∧
      ∀ k : Fin d, hM.isHermitian.eigenvalues i ≤ hM.isHermitian.eigenvalues k ∧
        hM.isHermitian.eigenvalues k ≤ hM.isHermitian.eigenvalues j := by
  classical
  let s : Finset (Fin d) := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  obtain ⟨i, hi, himin⟩ := Finset.exists_mem_eq_inf' hs hM.isHermitian.eigenvalues
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_mem_eq_sup' hs hM.isHermitian.eigenvalues
  refine ⟨i, j, ?_, ?_, ?_⟩
  · rw [specMin_eq_finset_inf_eigenvalues hM]
    exact himin
  · rw [specBound_eq_finset_sup_eigenvalues hM]
    exact hjmax
  · intro k
    constructor
    · rw [← himin]
      exact Finset.inf'_le hM.isHermitian.eigenvalues (Finset.mem_univ k)
    · rw [← hjmax]
      exact Finset.le_sup' hM.isHermitian.eigenvalues (Finset.mem_univ k)

/-- The normalized relative matrix of two positive matrices is positive definite. -/
theorem normalizedMat_posDef {m₀ m₁ : Mat d}
    (h₀ : m₀.PosDef) (h₁ : m₁.PosDef) : (normalizedMat m₀ m₁).PosDef := by
  have hsqrt : (CFC.sqrt m₀⁻¹).PosDef := posDef_sqrt h₀.inv
  have hsqrt_trans : Matrix.transpose (CFC.sqrt m₀⁻¹) = CFC.sqrt m₀⁻¹ :=
    transpose_sqrt h₀.inv
  have hinj : Function.Injective (CFC.sqrt m₀⁻¹).vecMul :=
    Matrix.vecMul_injective_iff_isUnit.mpr hsqrt.isUnit
  have hconj :
      (CFC.sqrt m₀⁻¹ * m₁ * Matrix.conjTranspose (CFC.sqrt m₀⁻¹)).PosDef :=
    h₁.mul_mul_conjTranspose_same (B := CFC.sqrt m₀⁻¹) hinj
  rw [normalizedMat, matSqrt_eq_cfc_sqrt h₀.inv.posSemidef]
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hsqrt_trans] using hconj

private theorem scalar_one_isHermitian (t : ℝ) :
    (t • (1 : Mat d)).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  by_cases hij : i = j
  · subst hij
    simp
  · have hji : j ≠ i := fun h => hij h.symm
    simp [hij, hji]

private theorem matrixOrder_of_matLoewnerLE_of_isHermitian {A B : Mat d}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : MatLoewnerLE A B) :
    A ≤ B := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) ?_
  intro x
  change 0 ≤ dotProduct x (Matrix.mulVec (B - A) x)
  rw [Matrix.sub_mulVec, dotProduct_sub]
  have hAB' :
      (1 / 2 : ℝ) * dotProduct x (Matrix.mulVec A x) ≤
        (1 / 2 : ℝ) * dotProduct x (Matrix.mulVec B x) := by
    simpa [vecDot, matVecMul] using! hAB x
  linarith only [hAB']

private theorem matLoewnerLE_of_matrixOrder {A B : Mat d} (hAB : A ≤ B) :
    MatLoewnerLE A B := by
  have hBA : (B - A).PosSemidef := (Matrix.le_iff).mp hAB
  intro x
  change (1 / 2 : ℝ) * dotProduct x (Matrix.mulVec A x) ≤
      (1 / 2 : ℝ) * dotProduct x (Matrix.mulVec B x)
  have hnonneg : 0 ≤ dotProduct x (Matrix.mulVec (B - A) x) :=
    hBA.dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, dotProduct_sub] at hnonneg
  linarith only [hnonneg]

private theorem matLoewnerLE_refl (A : Mat d) : MatLoewnerLE A A := by
  intro x
  rfl

private theorem matLoewnerLE_trans {A B C : Mat d}
    (hAB : MatLoewnerLE A B) (hBC : MatLoewnerLE B C) : MatLoewnerLE A C := by
  intro x
  exact (hAB x).trans (hBC x)

private theorem smul_isHermitian_of_posDef {A : Mat d} (hA : A.PosDef) (c : ℝ) :
    (c • A).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  have hij := congr_fun (congr_fun (transpose_eq_of_isHermitian hA.isHermitian) i) j
  change A j i = A i j at hij
  simp [hij]

private theorem matLoewnerLE_antisymm_of_isHermitian {A B : Mat d}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : MatLoewnerLE A B) (hBA : MatLoewnerLE B A) : A = B :=
  le_antisymm (matrixOrder_of_matLoewnerLE_of_isHermitian hA hB hAB)
    (matrixOrder_of_matLoewnerLE_of_isHermitian hB hA hBA)

private theorem vecDot_matVecMul_smul (c : ℝ) (A : Mat d) (x : Vec d) :
    vecDot x (matVecMul (c • A) x) = c * vecDot x (matVecMul A x) := by
  simp [vecDot, matVecMul, Finset.mul_sum, mul_comm, mul_left_comm]

private theorem matLoewnerLE_smul_iff_of_pos {A B : Mat d} {c : ℝ} (hc : 0 < c) :
    MatLoewnerLE (c • A) (c • B) ↔ MatLoewnerLE A B := by
  constructor
  · intro h x
    have hx := h x
    rw [vecDot_matVecMul_smul, vecDot_matVecMul_smul] at hx
    nlinarith only [hx, hc]
  · intro h x
    have hx := h x
    rw [vecDot_matVecMul_smul, vecDot_matVecMul_smul]
    nlinarith only [hx, hc]

private theorem eigenvalue_mem_real_spectrum {M : Mat d} (hM : M.IsHermitian) (i : Fin d) :
    hM.eigenvalues i ∈ spectrum ℝ M := by
  rw [hM.spectrum_real_eq_range_eigenvalues]
  exact Set.mem_range_self i

private theorem eigenvalue_le_of_matLoewnerLE_smul_one {M : Mat d} (hM : M.IsHermitian)
    {t : ℝ} (h : MatLoewnerLE M (t • (1 : Mat d))) (i : Fin d) :
    hM.eigenvalues i ≤ t := by
  have horder : M ≤ algebraMap ℝ (Mat d) t := by
    have horder' : M ≤ t • (1 : Mat d) :=
      matrixOrder_of_matLoewnerLE_of_isHermitian hM (scalar_one_isHermitian t) h
    simpa [Algebra.algebraMap_eq_smul_one] using horder'
  exact (le_algebraMap_iff_spectrum_le (a := M) (r := t) (ha := hM)).mp horder
    (hM.eigenvalues i) (eigenvalue_mem_real_spectrum hM i)

private theorem le_eigenvalue_of_smul_one_matLoewnerLE {M : Mat d} (hM : M.IsHermitian)
    {t : ℝ} (h : MatLoewnerLE (t • (1 : Mat d)) M) (i : Fin d) :
    t ≤ hM.eigenvalues i := by
  have horder : algebraMap ℝ (Mat d) t ≤ M := by
    have horder' : t • (1 : Mat d) ≤ M :=
      matrixOrder_of_matLoewnerLE_of_isHermitian (scalar_one_isHermitian t) hM h
    simpa [Algebra.algebraMap_eq_smul_one] using horder'
  exact (algebraMap_le_iff_le_spectrum (a := M) (r := t) (ha := hM)).mp horder
    (hM.eigenvalues i) (eigenvalue_mem_real_spectrum hM i)

private theorem smul_one_matLoewnerLE_iff {M : Mat d} [NeZero d] (hM : M.PosDef) (t : ℝ) :
    MatLoewnerLE (t • (1 : Mat d)) M ↔ t ≤ specMin M := by
  constructor
  · intro h
    rw [specMin_eq_finset_inf_eigenvalues hM]
    exact Finset.le_inf' Finset.univ_nonempty hM.isHermitian.eigenvalues
      fun i _hi => le_eigenvalue_of_smul_one_matLoewnerLE hM.isHermitian h i
  · intro ht
    let lam := (Finset.univ : Finset (Fin d)).inf' Finset.univ_nonempty
      hM.isHermitian.eigenvalues
    have hlam_mem : MatLoewnerLE (lam • (1 : Mat d)) M := by
      have horder : algebraMap ℝ (Mat d) lam ≤ M := by
        refine algebraMap_le_of_le_spectrum (a := M) (r := lam) ?_ (ha := hM.isHermitian)
        intro x hx
        obtain ⟨i, rfl⟩ := hM.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
        exact Finset.inf'_le hM.isHermitian.eigenvalues (Finset.mem_univ i)
      exact matLoewnerLE_of_matrixOrder (by simpa [Algebra.algebraMap_eq_smul_one] using horder)
    have htlam : t ≤ lam := by
      have hspec : specMin M = lam := by
        simpa [lam] using specMin_eq_finset_inf_eigenvalues hM
      rwa [hspec] at ht
    exact (matLoewnerLE_smul_one_of_le htlam).trans hlam_mem

private theorem specBound_le_iff_matLoewnerLE_smul_one {M : Mat d} [NeZero d]
    (hM : M.PosDef) (t : ℝ) :
    specBound M ≤ t ↔ MatLoewnerLE M (t • (1 : Mat d)) := by
  constructor
  · intro ht
    exact (matLoewnerLE_specBound_smul_one M).trans (matLoewnerLE_smul_one_of_le ht)
  · intro h
    rw [specBound_eq_finset_sup_eigenvalues hM]
    exact Finset.sup'_le Finset.univ_nonempty hM.isHermitian.eigenvalues
      fun i _hi => eigenvalue_le_of_matLoewnerLE_smul_one hM.isHermitian h i

private theorem matSqrt_inv_transpose {m : Mat d} (hm : m.PosDef) :
    matTranspose (matSqrt m⁻¹) = matSqrt m⁻¹ := by
  simpa [matTranspose] using
    transpose_eq_of_isHermitian (matSqrt_inv_posDef hm).posSemidef.isHermitian

private theorem matSqrt_inv_congr_smul_self {m : Mat d} (hm : m.PosDef) (t : ℝ) :
    matTranspose (matSqrt m⁻¹) * (t • m) * matSqrt m⁻¹ = t • (1 : Mat d) := by
  rw [matSqrt_inv_transpose hm]
  calc
    matSqrt m⁻¹ * (t • m) * matSqrt m⁻¹ =
        t • (matSqrt m⁻¹ * m * matSqrt m⁻¹) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = t • (1 : Mat d) := by rw [matSqrt_inv_mul_self_mul_matSqrt_inv hm]

private theorem matSqrt_inv_congr_right {m₀ m₁ : Mat d} (h₀ : m₀.PosDef) :
    matTranspose (matSqrt m₀⁻¹) * m₁ * matSqrt m₀⁻¹ = normalizedMat m₀ m₁ := by
  rw [matSqrt_inv_transpose h₀, normalizedMat]

/-- Lower relative Loewner comparisons are exactly the lower spectral threshold of the
normalized relative matrix. -/
theorem matLoewnerLE_smul_left_iff_specMin {m₀ m₁ : Mat d} [NeZero d]
    (h₀ : m₀.PosDef) (h₁ : m₁.PosDef) (t : ℝ) :
    MatLoewnerLE (t • m₀) m₁ ↔ t ≤ specMin (normalizedMat m₀ m₁) := by
  let S : Mat d := matSqrt m₀⁻¹
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp (matSqrt_inv_posDef h₀).isUnit
  calc
    MatLoewnerLE (t • m₀) m₁ ↔
        MatLoewnerLE (matTranspose S * (t • m₀) * S) (matTranspose S * m₁ * S) :=
      matLoewnerLE_congr_iff_of_isUnit_det hSdet
    _ ↔ MatLoewnerLE (t • (1 : Mat d)) (normalizedMat m₀ m₁) := by
      rw [show matTranspose S * (t • m₀) * S = t • (1 : Mat d) by
          simpa [S] using matSqrt_inv_congr_smul_self h₀ t,
        show matTranspose S * m₁ * S = normalizedMat m₀ m₁ by
          simpa [S] using matSqrt_inv_congr_right (m₁ := m₁) h₀]
    _ ↔ t ≤ specMin (normalizedMat m₀ m₁) :=
      smul_one_matLoewnerLE_iff (normalizedMat_posDef h₀ h₁) t

/-- Upper relative Loewner comparisons are exactly the upper spectral threshold of the
normalized relative matrix. -/
theorem matLoewnerLE_right_iff_specBound_le {m₀ m₁ : Mat d} [NeZero d]
    (h₀ : m₀.PosDef) (h₁ : m₁.PosDef) (t : ℝ) :
    MatLoewnerLE m₁ (t • m₀) ↔ specBound (normalizedMat m₀ m₁) ≤ t := by
  let S : Mat d := matSqrt m₀⁻¹
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp (matSqrt_inv_posDef h₀).isUnit
  calc
    MatLoewnerLE m₁ (t • m₀) ↔
        MatLoewnerLE (matTranspose S * m₁ * S) (matTranspose S * (t • m₀) * S) :=
      matLoewnerLE_congr_iff_of_isUnit_det hSdet
    _ ↔ MatLoewnerLE (normalizedMat m₀ m₁) (t • (1 : Mat d)) := by
      rw [show matTranspose S * m₁ * S = normalizedMat m₀ m₁ by
          simpa [S] using matSqrt_inv_congr_right (m₁ := m₁) h₀,
        show matTranspose S * (t • m₀) * S = t • (1 : Mat d) by
          simpa [S] using matSqrt_inv_congr_smul_self h₀ t]
    _ ↔ specBound (normalizedMat m₀ m₁) ≤ t :=
      (specBound_le_iff_matLoewnerLE_smul_one (normalizedMat_posDef h₀ h₁) t).symm

/-- The projective distance is the logarithm of the optimal relative Loewner spread. -/
theorem projectiveDistance_eq_log_relative_spread {m₀ m₁ : Mat d} [NeZero d]
    (h₀ : m₀.PosDef) (h₁ : m₁.PosDef) :
    ∃ L U : ℝ, 0 < L ∧ L ≤ U ∧
      (∀ t : ℝ, MatLoewnerLE (t • m₀) m₁ ↔ t ≤ L) ∧
      (∀ t : ℝ, MatLoewnerLE m₁ (t • m₀) ↔ U ≤ t) ∧
      L = specMin (normalizedMat m₀ m₁) ∧
      U = specBound (normalizedMat m₀ m₁) ∧
      projectiveDistance m₀ m₁ = 1 / 2 * Real.log (U / L) := by
  refine ⟨specMin (normalizedMat m₀ m₁), specBound (normalizedMat m₀ m₁), ?_, ?_, ?_, ?_,
    rfl, rfl, ?_⟩
  · exact specMin_pos (normalizedMat_posDef h₀ h₁)
  · obtain ⟨i, j, hi, hj, hle⟩ := spectral_extrema_attained (normalizedMat_posDef h₀ h₁)
    rw [hi, hj]
    exact (hle j).1
  · intro t
    exact matLoewnerLE_smul_left_iff_specMin h₀ h₁ t
  · intro t
    exact matLoewnerLE_right_iff_specBound_le h₀ h₁ t
  · rfl

/-- The projective distance between positive matrices is nonnegative. -/
theorem projectiveDistance_nonneg {m₀ m₁ : Mat d} [NeZero d]
    (h₀ : m₀.PosDef) (h₁ : m₁.PosDef) : 0 ≤ projectiveDistance m₀ m₁ := by
  obtain ⟨L, U, hL, hLU, _hlow, _hup, _hLdef, _hUdef, hdist⟩ :=
    projectiveDistance_eq_log_relative_spread h₀ h₁
  rw [hdist]
  have hratio : 1 ≤ U / L := by
    rwa [one_le_div hL]
  exact mul_nonneg (by norm_num) (Real.log_nonneg hratio)

/-- The projective distance is invariant under positive scaling in the right endpoint. -/
theorem projectiveDistance_smul_right {m₀ m₁ : Mat d} [NeZero d]
    (h₀ : m₀.PosDef) (h₁ : m₁.PosDef) {c : ℝ} (hc : 0 < c) :
    projectiveDistance m₀ (c • m₁) = projectiveDistance m₀ m₁ := by
  have h₁c : (c • m₁).PosDef := h₁.smul hc
  obtain ⟨L, U, hL, _hLU, hlow, hup, _hLdef, _hUdef, hdist⟩ :=
    projectiveDistance_eq_log_relative_spread h₀ h₁
  obtain ⟨Lc, Uc, _hLc, _hLUc, hlowc, hupc, _hLcdef, _hUcdef, hdistc⟩ :=
    projectiveDistance_eq_log_relative_spread h₀ h₁c
  have hLuniq : Lc = c * L := by
    refine le_antisymm ?_ ?_
    · have hscaled : MatLoewnerLE (Lc • m₀) (c • m₁) := (hlowc Lc).2 le_rfl
      have hcoef : c * (Lc / c) = Lc := by field_simp [hc.ne']
      have hscaled' : MatLoewnerLE (c • ((Lc / c) • m₀)) (c • m₁) := by
        simpa [smul_smul, hcoef] using hscaled
      have hbase : MatLoewnerLE ((Lc / c) • m₀) m₁ :=
        (matLoewnerLE_smul_iff_of_pos hc).1 hscaled'
      have hdiv : Lc / c ≤ L := (hlow (Lc / c)).1 hbase
      simpa [mul_comm] using (div_le_iff₀ hc).1 hdiv
    · have hbase : MatLoewnerLE (L • m₀) m₁ := (hlow L).2 le_rfl
      have hscaled' : MatLoewnerLE (c • (L • m₀)) (c • m₁) :=
        (matLoewnerLE_smul_iff_of_pos hc).2 hbase
      have hscaled : MatLoewnerLE ((c * L) • m₀) (c • m₁) := by
        simpa [smul_smul] using hscaled'
      exact (hlowc (c * L)).1 hscaled
  have hUuniq : Uc = c * U := by
    refine le_antisymm ?_ ?_
    · have hbase : MatLoewnerLE m₁ (U • m₀) := (hup U).2 le_rfl
      have hscaled' : MatLoewnerLE (c • m₁) (c • (U • m₀)) :=
        (matLoewnerLE_smul_iff_of_pos hc).2 hbase
      have hscaled : MatLoewnerLE (c • m₁) ((c * U) • m₀) := by
        simpa [smul_smul] using hscaled'
      exact (hupc (c * U)).1 hscaled
    · have hscaled : MatLoewnerLE (c • m₁) (Uc • m₀) := (hupc Uc).2 le_rfl
      have hcoef : c * (Uc / c) = Uc := by field_simp [hc.ne']
      have hscaled' : MatLoewnerLE (c • m₁) (c • ((Uc / c) • m₀)) := by
        simpa [smul_smul, hcoef] using hscaled
      have hbase : MatLoewnerLE m₁ ((Uc / c) • m₀) :=
        (matLoewnerLE_smul_iff_of_pos hc).1 hscaled'
      have hdiv : U ≤ Uc / c := (hup (Uc / c)).1 hbase
      simpa [mul_comm] using (le_div_iff₀ hc).1 hdiv
  rw [hdistc, hdist, hLuniq, hUuniq]
  have hquot : (c * U) / (c * L) = U / L := by
    field_simp [hc.ne', hL.ne']
  rw [hquot]

private theorem projectiveDistance_self {m : Mat d} [NeZero d] (hm : m.PosDef) :
    projectiveDistance m m = 0 := by
  obtain ⟨L, U, _hL, hLU, hlow, hup, _hLdef, _hUdef, hdist⟩ :=
    projectiveDistance_eq_log_relative_spread hm hm
  have h1L : (1 : ℝ) ≤ L := by
    exact (hlow 1).1 (by simpa using matLoewnerLE_refl m)
  have hU1 : U ≤ (1 : ℝ) := by
    exact (hup 1).1 (by simpa using matLoewnerLE_refl m)
  have hLone : L = 1 := le_antisymm (hLU.trans hU1) h1L
  have hUone : U = 1 := le_antisymm hU1 (h1L.trans hLU)
  rw [hdist, hLone, hUone]
  norm_num

/-- The projective distance vanishes exactly on the positive-scalar equivalence
relation. -/
theorem projectiveDistance_eq_zero_iff {m₀ m₁ : Mat d} [NeZero d]
    (h₀ : m₀.PosDef) (h₁ : m₁.PosDef) :
    projectiveDistance m₀ m₁ = 0 ↔ ProjectiveEq m₀ m₁ := by
  constructor
  · intro hzero
    obtain ⟨L, U, hL, hLU, hlow, hup, _hLdef, _hUdef, hdist⟩ :=
      projectiveDistance_eq_log_relative_spread h₀ h₁
    have hlog : Real.log (U / L) = 0 := by
      linarith only [hzero, hdist]
    have hUpos : 0 < U := lt_of_lt_of_le hL hLU
    have hratio_pos : 0 < U / L := div_pos hUpos hL
    have hratio : U / L = 1 := Real.eq_one_of_pos_of_log_eq_zero hratio_pos hlog
    have hUL : U = L := by
      exact (div_eq_one_iff_eq hL.ne').1 hratio
    have hlowL : MatLoewnerLE (L • m₀) m₁ := (hlow L).2 le_rfl
    have hupL : MatLoewnerLE m₁ (L • m₀) := (hup L).2 (by rw [hUL])
    have heq : m₁ = L • m₀ :=
      matLoewnerLE_antisymm_of_isHermitian h₁.isHermitian
        (smul_isHermitian_of_posDef h₀ L) hupL hlowL
    exact ⟨L, hL, heq⟩
  · rintro ⟨c, hc, rfl⟩
    rw [projectiveDistance_smul_right h₀ h₀ hc]
    exact projectiveDistance_self h₀

/-- The projective distance satisfies the triangle inequality on positive matrices. -/
theorem projectiveDistance_triangle {m₀ m₁ m₂ : Mat d} [NeZero d]
    (h₀ : m₀.PosDef) (h₁ : m₁.PosDef) (h₂ : m₂.PosDef) :
    projectiveDistance m₀ m₂ ≤ projectiveDistance m₀ m₁ + projectiveDistance m₁ m₂ := by
  obtain ⟨L₀₁, U₀₁, hL₀₁, hLU₀₁, hlow₀₁, hup₀₁, _hL₀₁def, _hU₀₁def, hdist₀₁⟩ :=
    projectiveDistance_eq_log_relative_spread h₀ h₁
  obtain ⟨L₁₂, U₁₂, hL₁₂, hLU₁₂, hlow₁₂, hup₁₂, _hL₁₂def, _hU₁₂def, hdist₁₂⟩ :=
    projectiveDistance_eq_log_relative_spread h₁ h₂
  obtain ⟨L₀₂, U₀₂, hL₀₂, hLU₀₂, hlow₀₂, hup₀₂, _hL₀₂def, _hU₀₂def, hdist₀₂⟩ :=
    projectiveDistance_eq_log_relative_spread h₀ h₂
  have hU₀₁pos : 0 < U₀₁ := lt_of_lt_of_le hL₀₁ hLU₀₁
  have hU₁₂pos : 0 < U₁₂ := lt_of_lt_of_le hL₁₂ hLU₁₂
  have hU₀₂pos : 0 < U₀₂ := lt_of_lt_of_le hL₀₂ hLU₀₂
  have hlow_prod : MatLoewnerLE ((L₀₁ * L₁₂) • m₀) m₂ := by
    have hscaled : MatLoewnerLE (L₁₂ • (L₀₁ • m₀)) (L₁₂ • m₁) :=
      (matLoewnerLE_smul_iff_of_pos hL₁₂).2 ((hlow₀₁ L₀₁).2 le_rfl)
    have hscaled' : MatLoewnerLE ((L₀₁ * L₁₂) • m₀) (L₁₂ • m₁) := by
      simpa [smul_smul, mul_comm, mul_left_comm] using hscaled
    exact matLoewnerLE_trans hscaled' ((hlow₁₂ L₁₂).2 le_rfl)
  have hLprod_le : L₀₁ * L₁₂ ≤ L₀₂ := (hlow₀₂ (L₀₁ * L₁₂)).1 hlow_prod
  have hup_prod : MatLoewnerLE m₂ ((U₀₁ * U₁₂) • m₀) := by
    have hscaled : MatLoewnerLE (U₁₂ • m₁) (U₁₂ • (U₀₁ • m₀)) :=
      (matLoewnerLE_smul_iff_of_pos hU₁₂pos).2 ((hup₀₁ U₀₁).2 le_rfl)
    have hscaled' : MatLoewnerLE (U₁₂ • m₁) ((U₀₁ * U₁₂) • m₀) := by
      simpa [smul_smul, mul_comm, mul_left_comm] using hscaled
    exact matLoewnerLE_trans ((hup₁₂ U₁₂).2 le_rfl) hscaled'
  have hU_le_prod : U₀₂ ≤ U₀₁ * U₁₂ := (hup₀₂ (U₀₁ * U₁₂)).1 hup_prod
  have hLprod_pos : 0 < L₀₁ * L₁₂ := mul_pos hL₀₁ hL₁₂
  have hspread_le :
      U₀₂ / L₀₂ ≤ (U₀₁ * U₁₂) / (L₀₁ * L₁₂) := by
    rw [div_le_div_iff₀ hL₀₂ hLprod_pos]
    have hUp_nonneg : 0 ≤ U₀₁ * U₁₂ := le_trans (le_of_lt hU₀₂pos) hU_le_prod
    calc
      U₀₂ * (L₀₁ * L₁₂) ≤ (U₀₁ * U₁₂) * (L₀₁ * L₁₂) :=
        mul_le_mul_of_nonneg_right hU_le_prod (le_of_lt hLprod_pos)
      _ ≤ (U₀₁ * U₁₂) * L₀₂ :=
        mul_le_mul_of_nonneg_left hLprod_le hUp_nonneg
  have hlog_le :
      Real.log (U₀₂ / L₀₂) ≤ Real.log ((U₀₁ * U₁₂) / (L₀₁ * L₁₂)) :=
    Real.log_le_log (div_pos hU₀₂pos hL₀₂) hspread_le
  have hquot :
      (U₀₁ * U₁₂) / (L₀₁ * L₁₂) = (U₀₁ / L₀₁) * (U₁₂ / L₁₂) := by
    field_simp [hL₀₁.ne', hL₁₂.ne']
  have hlog_prod :
      Real.log ((U₀₁ * U₁₂) / (L₀₁ * L₁₂)) =
        Real.log (U₀₁ / L₀₁) + Real.log (U₁₂ / L₁₂) := by
    rw [hquot, Real.log_mul (ne_of_gt (div_pos hU₀₁pos hL₀₁))
      (ne_of_gt (div_pos hU₁₂pos hL₁₂))]
  rw [hdist₀₂, hdist₀₁, hdist₁₂]
  calc
    (1 / 2 : ℝ) * Real.log (U₀₂ / L₀₂) ≤
        1 / 2 * Real.log ((U₀₁ * U₁₂) / (L₀₁ * L₁₂)) :=
      mul_le_mul_of_nonneg_left hlog_le (by norm_num)
    _ = 1 / 2 * Real.log (U₀₁ / L₀₁) + 1 / 2 * Real.log (U₁₂ / L₁₂) := by
      rw [hlog_prod]
      ring

private theorem normalizedMat_one_left (m : Mat d) :
    normalizedMat (1 : Mat d) m = m := by
  rw [normalizedMat]
  have hsqrt : matSqrt ((1 : Mat d)⁻¹) = 1 := by
    rw [inv_one]
    rw [matSqrt_eq_cfc_sqrt Matrix.PosSemidef.one]
    exact CFC.sqrt_one
  rw [hsqrt]
  simp

/-- The projective distance from the identity is the logarithm of the eccentricity expression
using Mathlib's L2 operator norm. -/
theorem projectiveDistance_one_eq_log_eccentricity {m : Mat d} [NeZero d]
    (hm : m.PosDef) :
    projectiveDistance (1 : Mat d) m = 1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) := by
  rw [projectiveDistance, normalizedMat_one_left m, posDef_l2_opNorm_eq_specBound hm,
    posDef_inv_l2_opNorm_eq_specMin_inv hm]
  have harg : specBound m / specMin m = specBound m * (specMin m)⁻¹ :=
    div_eq_mul_inv _ _
  rw [harg]

end

end HCPolySupport.HighContrast.Geometry
