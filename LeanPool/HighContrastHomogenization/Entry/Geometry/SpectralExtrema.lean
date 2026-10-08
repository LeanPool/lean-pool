/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Setup.SchattenNorm
public import LeanPool.HighContrastHomogenization.Entry.Setup.ProjectiveDistance
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.PosDef

/-!
# High-contrast homogenization: Entry.Geometry.SpectralExtrema

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Spectral extrema for the Loewner thresholds

On a positive definite matrix `M`, the scalar Loewner thresholds `specMin M` and
`specBound M` are the attained minimum and maximum Hermitian eigenvalues of `M`, and
they equal the L2 operator norms of `M⁻¹` and `M` respectively; for a positive
continuous-functional-calculus power of `M` the two thresholds are the corresponding
scalar powers of the originals.  These spectral identities provide the
projective-distance and geometry-update comparisons used in `l.projective.step` and in
the finite run of `p.global.selection`.
-/

open HCPolySupport.HighContrast (matLoewnerLE_specBound_smul_one specBound specBound_le)
namespace HCPolySupport.HighContrast.Geometry

open scoped MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem scalar_one_isHermitian (t : ℝ) :
    (t • (1 : Mat d)).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  by_cases hij : i = j
  · subst hij
    simp
  · have hji : j ≠ i := fun h => hij h.symm
    simp [hij, hji]

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

/-- On positive definite matrices, the upper Loewner threshold is the attained maximum
Hermitian eigenvalue. -/
theorem specBound_eq_finset_sup_eigenvalues {M : Mat d} [NeZero d] (hM : M.PosDef) :
    specBound M =
      (Finset.univ : Finset (Fin d)).sup' Finset.univ_nonempty hM.isHermitian.eigenvalues := by
  let μ := (Finset.univ : Finset (Fin d)).sup' Finset.univ_nonempty hM.isHermitian.eigenvalues
  have hμ_nonneg : 0 ≤ μ := by
    obtain ⟨i, hi⟩ := (Finset.univ_nonempty : (Finset.univ : Finset (Fin d)).Nonempty)
    exact (hM.eigenvalues_pos i).le.trans
      (Finset.le_sup' hM.isHermitian.eigenvalues hi)
  have hM_le_μ : MatLoewnerLE M (μ • (1 : Mat d)) := by
    have horder : M ≤ algebraMap ℝ (Mat d) μ := by
      refine le_algebraMap_of_spectrum_le (a := M) (r := μ) ?_ (ha := hM.isHermitian)
      intro x hx
      obtain ⟨i, rfl⟩ := hM.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
      exact Finset.le_sup' hM.isHermitian.eigenvalues (Finset.mem_univ i)
    exact matLoewnerLE_of_matrixOrder (by simpa [Algebra.algebraMap_eq_smul_one] using horder)
  refine le_antisymm (specBound_le hμ_nonneg hM_le_μ) ?_
  refine Finset.sup'_le Finset.univ_nonempty hM.isHermitian.eigenvalues ?_
  intro i _hi
  exact eigenvalue_le_of_matLoewnerLE_smul_one hM.isHermitian
    (matLoewnerLE_specBound_smul_one M) i

/-- On positive definite matrices, the lower Loewner threshold is the attained minimum
Hermitian eigenvalue. -/
theorem specMin_eq_finset_inf_eigenvalues {M : Mat d} [NeZero d] (hM : M.PosDef) :
    specMin M =
      (Finset.univ : Finset (Fin d)).inf' Finset.univ_nonempty hM.isHermitian.eigenvalues := by
  let lam := (Finset.univ : Finset (Fin d)).inf' Finset.univ_nonempty hM.isHermitian.eigenvalues
  let μ := (Finset.univ : Finset (Fin d)).sup' Finset.univ_nonempty hM.isHermitian.eigenvalues
  have hlam_mem : MatLoewnerLE (lam • (1 : Mat d)) M := by
    have horder : algebraMap ℝ (Mat d) lam ≤ M := by
      refine algebraMap_le_of_le_spectrum (a := M) (r := lam) ?_ (ha := hM.isHermitian)
      intro x hx
      obtain ⟨i, rfl⟩ := hM.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
      exact Finset.inf'_le hM.isHermitian.eigenvalues (Finset.mem_univ i)
    exact matLoewnerLE_of_matrixOrder (by simpa [Algebra.algebraMap_eq_smul_one] using horder)
  have hbdd : BddAbove {t : ℝ | MatLoewnerLE (t • (1 : Mat d)) M} := by
    refine ⟨μ, ?_⟩
    intro t ht
    obtain ⟨i, hi⟩ := (Finset.univ_nonempty : (Finset.univ : Finset (Fin d)).Nonempty)
    exact (le_eigenvalue_of_smul_one_matLoewnerLE hM.isHermitian ht i).trans
      (Finset.le_sup' hM.isHermitian.eigenvalues hi)
  refine le_antisymm ?_ (le_csSup hbdd hlam_mem)
  refine csSup_le ⟨lam, hlam_mem⟩ ?_
  intro t ht
  exact Finset.le_inf' Finset.univ_nonempty hM.isHermitian.eigenvalues
    fun i _hi => le_eigenvalue_of_smul_one_matLoewnerLE hM.isHermitian ht i

/-- On positive definite matrices, the lower Loewner threshold is strictly positive. -/
theorem specMin_pos {M : Mat d} [NeZero d] (hM : M.PosDef) : 0 < specMin M := by
  rw [specMin_eq_finset_inf_eigenvalues hM]
  exact (Finset.lt_inf'_iff (H := (Finset.univ_nonempty :
      (Finset.univ : Finset (Fin d)).Nonempty))
      (f := hM.isHermitian.eigenvalues)).mpr fun i _hi => hM.eigenvalues_pos i

private theorem l2_opNorm_conjStarAlgAut {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℝ)) (A : Matrix n n ℝ) :
    ‖(Unitary.conjStarAlgAut ℝ _ U) A‖ = ‖A‖ := by
  rw [Unitary.conjStarAlgAut_apply]
  rw [CStarRing.norm_mul_mem_unitary
    (A := (U : Matrix n n ℝ) * A) (hU := Unitary.star_mem U.prop)]
  exact CStarRing.norm_mem_unitary_mul A U.prop

private theorem hermitian_l2_opNorm_eq_eigenvalue_norm {M : Mat d}
    (hM : M.IsHermitian) :
    ‖M‖ = ‖hM.eigenvalues‖ := by
  conv_lhs => rw [hM.spectral_theorem]
  rw [l2_opNorm_conjStarAlgAut]
  simp

private theorem hermitian_l2_opNorm_cfc_eq_eigenvalue_norm {M : Mat d}
    (hM : M.IsHermitian) (f : ℝ → ℝ) :
    ‖cfc f M‖ = ‖f ∘ hM.eigenvalues‖ := by
  rw [hM.cfc_eq f, Matrix.IsHermitian.cfc]
  rw [l2_opNorm_conjStarAlgAut]
  simp

private theorem pos_eigenvalue_norm_eq_sup {M : Mat d} [NeZero d] (hM : M.PosDef) :
    ‖hM.isHermitian.eigenvalues‖ =
      (Finset.univ : Finset (Fin d)).sup' Finset.univ_nonempty hM.isHermitian.eigenvalues := by
  let μ := (Finset.univ : Finset (Fin d)).sup' Finset.univ_nonempty hM.isHermitian.eigenvalues
  have hμ_nonneg : 0 ≤ μ := by
    obtain ⟨i, hi⟩ := (Finset.univ_nonempty : (Finset.univ : Finset (Fin d)).Nonempty)
    exact (hM.eigenvalues_pos i).le.trans
      (Finset.le_sup' hM.isHermitian.eigenvalues hi)
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg hμ_nonneg).2 ?_
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hM.eigenvalues_pos i).le]
    exact Finset.le_sup' hM.isHermitian.eigenvalues (Finset.mem_univ i)
  · obtain ⟨i, _hi, hsup⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      hM.isHermitian.eigenvalues
    rw [hsup]
    calc
      hM.isHermitian.eigenvalues i = ‖hM.isHermitian.eigenvalues i‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hM.eigenvalues_pos i).le]
      _ ≤ ‖hM.isHermitian.eigenvalues‖ := norm_le_pi_norm _ _

/-- For positive definite matrices, the upper Loewner threshold is Mathlib's L2
operator norm. -/
theorem posDef_l2_opNorm_eq_specBound {M : Mat d} [NeZero d] (hM : M.PosDef) :
    ‖M‖ = specBound M := by
  rw [hermitian_l2_opNorm_eq_eigenvalue_norm hM.isHermitian,
    pos_eigenvalue_norm_eq_sup hM, specBound_eq_finset_sup_eigenvalues hM]

private theorem inv_eigenvalue_norm_eq_inv_inf {M : Mat d} [NeZero d] (hM : M.PosDef) :
    ‖(fun i : Fin d => (hM.isHermitian.eigenvalues i)⁻¹)‖ =
      ((Finset.univ : Finset (Fin d)).inf' Finset.univ_nonempty
        hM.isHermitian.eigenvalues)⁻¹ := by
  let lam := (Finset.univ : Finset (Fin d)).inf' Finset.univ_nonempty
    hM.isHermitian.eigenvalues
  have hlam_pos : 0 < lam := by
    exact (Finset.lt_inf'_iff (H := (Finset.univ_nonempty :
        (Finset.univ : Finset (Fin d)).Nonempty))
        (f := hM.isHermitian.eigenvalues)).mpr fun i _hi => hM.eigenvalues_pos i
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hlam_pos.le)).2 ?_
    intro i
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hM.eigenvalues_pos i))]
    exact (inv_le_inv₀ (hM.eigenvalues_pos i) hlam_pos).2
      (Finset.inf'_le hM.isHermitian.eigenvalues (Finset.mem_univ i))
  · obtain ⟨i, _hi, hinf⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      hM.isHermitian.eigenvalues
    rw [hinf]
    calc
      (hM.isHermitian.eigenvalues i)⁻¹ =
          ‖(hM.isHermitian.eigenvalues i)⁻¹‖ := by
            rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hM.eigenvalues_pos i))]
      _ ≤ ‖(fun i : Fin d => (hM.isHermitian.eigenvalues i)⁻¹)‖ := by
        exact norm_le_pi_norm (fun i : Fin d => (hM.isHermitian.eigenvalues i)⁻¹) i

private theorem posDef_inv_eq_cfc_inv {M : Mat d} (hM : M.PosDef) :
    M⁻¹ = cfc (fun x : ℝ => x⁻¹) M := by
  rw [Matrix.nonsing_inv_eq_ringInverse]
  rw [cfc_inv (R := ℝ) (A := Mat d) (p := IsSelfAdjoint) (fun x : ℝ => x) M ?_
    (ha := hM.isHermitian)]
  · have hid : cfc (fun x : ℝ => x) M = M := by
      simpa using! cfc_id ℝ M hM.isHermitian
    rw [hid]
  · intro x hx
    obtain ⟨i, rfl⟩ := hM.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
    exact ne_of_gt (hM.eigenvalues_pos i)

/-- For positive definite matrices, the L2 operator norm of the inverse is the inverse of
the lower Loewner threshold. -/
theorem posDef_inv_l2_opNorm_eq_specMin_inv {M : Mat d} [NeZero d] (hM : M.PosDef) :
    ‖M⁻¹‖ = (specMin M)⁻¹ := by
  rw [posDef_inv_eq_cfc_inv hM,
    hermitian_l2_opNorm_cfc_eq_eigenvalue_norm hM.isHermitian (fun x : ℝ => x⁻¹),
    Function.comp_def, inv_eigenvalue_norm_eq_inv_inf hM, specMin_eq_finset_inf_eigenvalues hM]

private theorem rpow_eigenvalue_norm_eq_sup_rpow {M : Mat d} [NeZero d] (hM : M.PosDef)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    ‖(fun i : Fin d => hM.isHermitian.eigenvalues i ^ θ)‖ =
      specBound M ^ θ := by
  rw [specBound_eq_finset_sup_eigenvalues hM]
  let μ := (Finset.univ : Finset (Fin d)).sup' Finset.univ_nonempty
    hM.isHermitian.eigenvalues
  have hμ_pos : 0 < μ := by
    obtain ⟨i, hi⟩ := (Finset.univ_nonempty : (Finset.univ : Finset (Fin d)).Nonempty)
    exact (hM.eigenvalues_pos i).trans_le
      (Finset.le_sup' hM.isHermitian.eigenvalues hi)
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (Real.rpow_pos_of_pos hμ_pos θ).le).2 ?_
    intro i
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_pos_of_pos (hM.eigenvalues_pos i) θ).le]
    exact Real.rpow_le_rpow (hM.eigenvalues_pos i).le
      (Finset.le_sup' hM.isHermitian.eigenvalues (Finset.mem_univ i)) hθ
  · obtain ⟨i, _hi, hsup⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      hM.isHermitian.eigenvalues
    rw [hsup]
    calc
      hM.isHermitian.eigenvalues i ^ θ =
          ‖hM.isHermitian.eigenvalues i ^ θ‖ := by
            rw [Real.norm_eq_abs,
              abs_of_nonneg (Real.rpow_pos_of_pos (hM.eigenvalues_pos i) θ).le]
      _ ≤ ‖(fun i : Fin d => hM.isHermitian.eigenvalues i ^ θ)‖ := by
        exact norm_le_pi_norm (fun i : Fin d => hM.isHermitian.eigenvalues i ^ θ) i

/-- The L2 operator norm of a positive CFC power is the corresponding power of the upper
spectral threshold. -/
theorem posDef_l2_opNorm_cfc_rpow_eq_specBound_rpow {M : Mat d} [NeZero d]
    (hM : M.PosDef) {θ : ℝ} (hθ : 0 ≤ θ) :
    ‖cfc (fun x : ℝ => x ^ θ) M‖ = specBound M ^ θ := by
  rw [hermitian_l2_opNorm_cfc_eq_eigenvalue_norm hM.isHermitian (fun x : ℝ => x ^ θ),
    Function.comp_def, rpow_eigenvalue_norm_eq_sup_rpow hM hθ]

private theorem inv_rpow_eigenvalue_norm_eq_inf_rpow_inv {M : Mat d} [NeZero d]
    (hM : M.PosDef) {θ : ℝ} (hθ : 0 ≤ θ) :
    ‖(fun i : Fin d => (hM.isHermitian.eigenvalues i ^ θ)⁻¹)‖ =
      (specMin M ^ θ)⁻¹ := by
  rw [specMin_eq_finset_inf_eigenvalues hM]
  let lam := (Finset.univ : Finset (Fin d)).inf' Finset.univ_nonempty
    hM.isHermitian.eigenvalues
  have hlam_pos : 0 < lam := by
    exact (Finset.lt_inf'_iff (H := (Finset.univ_nonempty :
        (Finset.univ : Finset (Fin d)).Nonempty))
        (f := hM.isHermitian.eigenvalues)).mpr fun i _hi => hM.eigenvalues_pos i
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg
      (inv_nonneg.mpr (Real.rpow_pos_of_pos hlam_pos θ).le)).2 ?_
    intro i
    rw [Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (Real.rpow_pos_of_pos (hM.eigenvalues_pos i) θ))]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos (hM.eigenvalues_pos i) θ)
        (Real.rpow_pos_of_pos hlam_pos θ)).2
      (Real.rpow_le_rpow hlam_pos.le
        (Finset.inf'_le hM.isHermitian.eigenvalues (Finset.mem_univ i)) hθ)
  · obtain ⟨i, _hi, hinf⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      hM.isHermitian.eigenvalues
    rw [hinf]
    calc
      (hM.isHermitian.eigenvalues i ^ θ)⁻¹ =
          ‖(hM.isHermitian.eigenvalues i ^ θ)⁻¹‖ := by
            rw [Real.norm_eq_abs,
              abs_of_pos (inv_pos.mpr (Real.rpow_pos_of_pos (hM.eigenvalues_pos i) θ))]
      _ ≤ ‖(fun i : Fin d => (hM.isHermitian.eigenvalues i ^ θ)⁻¹)‖ := by
        exact norm_le_pi_norm
          (fun i : Fin d => (hM.isHermitian.eigenvalues i ^ θ)⁻¹) i

private theorem posDef_cfc_rpow_inv_eq_cfc_inv_rpow {M : Mat d}
    (hM : M.PosDef) (θ : ℝ) :
    (cfc (fun x : ℝ => x ^ θ) M)⁻¹ =
      cfc (fun x : ℝ => (x ^ θ)⁻¹) M := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ θ) (spectrum ℝ M) := by
    exact continuousOn_id.rpow_const fun x hx => by
      left
      obtain ⟨i, rfl⟩ := hM.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
      exact ne_of_gt (hM.eigenvalues_pos i)
  rw [Matrix.nonsing_inv_eq_ringInverse, eq_comm]
  refine cfc_inv (R := ℝ) (A := Mat d) (p := IsSelfAdjoint)
    (fun x : ℝ => x ^ θ) M ?_ (hf := hcont) (ha := hM.isHermitian)
  intro x hx
  obtain ⟨i, rfl⟩ := hM.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
  exact ne_of_gt (Real.rpow_pos_of_pos (hM.eigenvalues_pos i) θ)

/-- The L2 operator norm of the inverse of a positive CFC power is the inverse corresponding
power of the lower spectral threshold. -/
theorem posDef_inv_l2_opNorm_cfc_rpow_eq_specMin_rpow_inv {M : Mat d} [NeZero d]
    (hM : M.PosDef) {θ : ℝ} (hθ : 0 ≤ θ) :
    ‖(cfc (fun x : ℝ => x ^ θ) M)⁻¹‖ = (specMin M ^ θ)⁻¹ := by
  rw [posDef_cfc_rpow_inv_eq_cfc_inv_rpow hM θ,
    hermitian_l2_opNorm_cfc_eq_eigenvalue_norm hM.isHermitian
      (fun x : ℝ => (x ^ θ)⁻¹),
    Function.comp_def, inv_rpow_eigenvalue_norm_eq_inf_rpow_inv hM hθ]

end

end HCPolySupport.HighContrast.Geometry
