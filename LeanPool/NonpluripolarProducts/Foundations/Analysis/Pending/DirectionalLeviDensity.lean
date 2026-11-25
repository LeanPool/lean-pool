/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedCoefficientCongruence
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedCoordinateDensity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.TopDegreeDensity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.SmoothPshHessian

/-!
# The directional Levi form as the density of `ddᶜ f ∧ (ddᶜ q_a)^{n-1}`

Demailly's [definition of positive currents and proof of order zero](https://www-fourier.univ-grenoble-alpes.fr/~demailly/source_files/analgeom/agbook.pdf#page=132)
(III.1.13 and III.1.14) use strongly positive test forms, including complementary wedges of
coordinate forms. Here the unit direction `a` determines the complementary form
`β_a = ddᶜ q_a`, where `q_a(z) = ‖z‖² - |⟨a, z⟩|²` has complex Hessian the orthogonal
projection onto `a^⊥`. The normalized coefficient identity is the coordinate calculation
in `topDensity_smoothDDC_perpQuadratic`. It yields the factor `(n - 1)! / πⁿ` multiplying
the directional Levi form of a smooth function.

* `mixedCoefficient_cons_perpDiag`: `C(K, D, …, D) = m! K₀₀` for `D = diag(0, 1, …, 1)`.
* `exists_unitary_col_zero`: a unitary matrix with a prescribed unit first column.
* `mixedCoefficient_cons_projection`: `C(H, P, …, P) = m! · y* H y` for `P = 1 - y y*`, `|y| = 1`
  (unitary congruence, `MixedMongeAmpere.mixedCoefficient_mul_mul`).
* `complexHessian_perpQuadratic`: the complex Hessian of `q_a` is `1 - ā āᵀ`.
* `topDensity_smoothDDC_perpQuadratic`: the density identity.
-/

@[expose] public section

open Set Filter Matrix
open scoped Topology ContDiff InnerProductSpace

namespace SGPT.Foundations.Analysis.Pending.DirectionalLeviDensity

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere TopDegreeDensity
  StronglyPositiveForms

noncomputable section

variable {m : ℕ}

/-! ### Linear algebra -/

/-- `D = diag(0, 1, …, 1)`. -/
def perpDiag (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.diagonal fun j => if j = 0 then 0 else 1

/-- **`C(K, D, …, D) = m! K₀₀`** for `D = diag(0, 1, …, 1)`. -/
theorem mixedCoefficient_cons_perpDiag (K : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :
    mixedCoefficient (Fin.cons K (fun _ : Fin m => perpDiag m) :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
      (m.factorial : ℂ) * K 0 0 := by
  classical
  set H : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
    Fin.cons K (fun _ : Fin m => perpDiag m) with hH
  have hrow : ∀ σ : Equiv.Perm (Fin (m + 1)),
      Matrix.det (fun j k => H (σ j) j k) = if σ 0 = 0 then K 0 0 else 0 := by
    intro σ
    by_cases h0 : σ 0 = 0
    · rw [ite_eq_left h0]
      have hM : (Matrix.of fun j k => H (σ j) j k) =
          (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).updateRow 0
            (∑ k, K 0 k • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) k) := by
        ext j k
        by_cases hj : j = 0
        · subst hj
          simp only [Matrix.of_apply, h0, hH, Fin.cons_zero, Matrix.updateRow_self,
            Finset.sum_apply, Pi.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
            mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        · have hne : σ j ≠ 0 := fun h => hj (σ.injective (h.trans h0.symm))
          obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr hne
          simp only [Matrix.of_apply, Matrix.updateRow_ne hj, ← hi, hH, Fin.cons_succ, perpDiag,
            Matrix.diagonal_apply, Matrix.one_apply, ite_eq_right hj]
      have hdet : Matrix.det (fun j k => H (σ j) j k) =
          Matrix.det (Matrix.of fun j k => H (σ j) j k) := rfl
      rw [hdet, hM, Matrix.det_updateRow_sum, Matrix.det_one, smul_eq_mul, mul_one]
    · rw [ite_eq_right h0]
      apply Matrix.det_eq_zero_of_row_eq_zero 0
      intro k
      obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr h0
      simp [hH, ← hi, perpDiag, Matrix.diagonal_apply]
  rw [mixedCoefficient]
  simp_rw [hrow]
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- A unitary matrix with a prescribed unit first column. -/
theorem exists_unitary_col_zero (y : Fin (m + 1) → ℂ) (hy : star y ⬝ᵥ y = 1) :
    ∃ W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ ∀ i, W i 0 = y i := by
  classical
  set v : EuclideanSpace ℂ (Fin (m + 1)) := WithLp.toLp 2 y with hvdef
  have hv : Orthonormal ℂ (({0} : Set (Fin (m + 1))).domRestrict fun _ => v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp only [ite_true]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change y ⬝ᵥ star y = 1
    rw [dotProduct_comm]
    exact hy
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp) (v := fun _ => v) (s := {0})
  set s := EuclideanSpace.basisFun (Fin (m + 1)) ℂ
  refine ⟨s.toBasis.toMatrix b, s.toMatrix_orthonormalBasis_conjTranspose_mul_self b,
    s.toMatrix_orthonormalBasis_self_mul_conjTranspose b, fun i => ?_⟩
  rw [Module.Basis.toMatrix_apply, hb 0 rfl]
  simp [s, hvdef]

/-- **`C(H, P, …, P) = m! · y* H y`** for the orthogonal projection `P = 1 - y y*` onto `y^⊥`. -/
theorem mixedCoefficient_cons_projection (H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (y : Fin (m + 1) → ℂ) (hy : star y ⬝ᵥ y = 1) :
    mixedCoefficient (Fin.cons H (fun _ : Fin m => 1 - vecMulVec y (star y)) :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
      (m.factorial : ℂ) * (star y ⬝ᵥ H *ᵥ y) := by
  obtain ⟨W, hWW, hWW', hW0⟩ := exists_unitary_col_zero y hy
  have hWy : Wᴴ *ᵥ y = Pi.single 0 1 := by
    have hy' : y = W *ᵥ Pi.single 0 1 := by
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, hW0]
    rw [hy', Matrix.mulVec_mulVec, hWW, Matrix.one_mulVec]
  have hyW : star y ᵥ* W = Pi.single 0 1 := by
    have := congrArg star hWy
    rw [Matrix.star_mulVec, conjTranspose_conjTranspose] at this
    rw [this]
    funext i
    simp [Pi.single_apply]
  have hD : Wᴴ * (1 - vecMulVec y (star y)) * W = perpDiag m := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hWW, Matrix.mul_vecMulVec,
      Matrix.vecMulVec_mul, hWy, hyW]
    ext j k
    simp only [perpDiag, Matrix.sub_apply, Matrix.one_apply, vecMulVec_apply, Pi.single_apply,
      Matrix.diagonal_apply]
    by_cases hj : j = k
    · subst hj
      by_cases h0 : j = 0 <;> simp [h0]
    · simp only [hj, ite_false]
      split_ifs with h1 h2 <;> first | (exfalso; exact hj (h1.trans h2.symm)) | simp
  have hHK : H = W * (Wᴴ * H * W) * Wᴴ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hWW', Matrix.one_mul, Matrix.mul_assoc, hWW',
      Matrix.mul_one]
  have hPD : 1 - vecMulVec y (star y) = W * perpDiag m * Wᴴ := by
    rw [← hD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hWW', Matrix.one_mul, Matrix.mul_assoc,
      hWW', Matrix.mul_one]
  have hfun : (Fin.cons H (fun _ : Fin m => 1 - vecMulVec y (star y)) :
      Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
      fun i => W * ((Fin.cons (Wᴴ * H * W) (fun _ : Fin m => perpDiag m) :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) i) * Wᴴ := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      exact hHK
    · simp only [Fin.cons_succ]
      exact hPD
  have hdet : W.det * Wᴴ.det = 1 := by
    rw [← Matrix.det_mul, hWW', Matrix.det_one]
  rw [hfun, MixedMongeAmpere.mixedCoefficient_mul_mul, hdet, one_mul,
    mixedCoefficient_cons_perpDiag]
  congr 1
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, conjTranspose_apply, dotProduct, Matrix.mulVec, hW0,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [Pi.star_apply]

/-! ### The quadratic form `q_a` and its complex Hessian -/

/-- `q_a(z) = ‖z‖² - |⟨a, z⟩|²`; for a unit vector `a` its complex Hessian is the orthogonal
projection onto `a^⊥` (`complexHessian_perpQuadratic`), so `ddᶜ q_a ≥ 0`. -/
def perpQuadratic (a : ComplexModel (m + 1)) (z : ComplexModel (m + 1)) : ℝ :=
  ‖z‖ ^ 2 - ‖⟪a, z⟫_ℂ‖ ^ 2

theorem contDiff_normSq_inner {k : WithTop ℕ∞} (a : ComplexModel (m + 1)) :
    ContDiff ℝ k (fun y : ComplexModel (m + 1) => ‖⟪a, y⟫_ℂ‖ ^ 2) :=
  (contDiff_norm_sq ℝ).comp ((innerSL ℂ a).restrictScalars ℝ).contDiff

theorem contDiff_perpQuadratic {k : WithTop ℕ∞} (a : ComplexModel (m + 1)) :
    ContDiff ℝ k (perpQuadratic a) :=
  (contDiff_norm_sq ℝ).sub (contDiff_normSq_inner a)

theorem realHessian_normSq_inner (a z v w : ComplexModel (m + 1)) :
    realHessian (fun y : ComplexModel (m + 1) => ‖⟪a, y⟫_ℂ‖ ^ 2) z v w =
      2 * (⟪a, w⟫_ℂ * (starRingEnd ℂ) ⟪a, v⟫_ℂ).re := by
  have h := realHessian_comp_affine (u := fun p : ℂ => ‖p‖ ^ 2) (contDiff_norm_sq ℝ)
    ((innerSL ℂ a).restrictScalars ℝ) 0 z v w
  simp only [zero_add, ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply] at h
  rw [h, realHessian_norm_sq, Complex.inner]

theorem complexHessian_normSq_inner (a z : ComplexModel (m + 1)) :
    complexHessian (fun y : ComplexModel (m + 1) => ‖⟪a, y⟫_ℂ‖ ^ 2) z =
      vecMulVec (fun j => star (a j)) (fun k => a k) := by
  ext j k
  have hj : ⟪a, coordinateVector j⟫_ℂ = star (a j) := by
    simp [coordinateVector, EuclideanSpace.inner_single_right]
  have hk : ⟪a, coordinateVector k⟫_ℂ = star (a k) := by
    simp [coordinateVector, EuclideanSpace.inner_single_right]
  simp only [complexHessian, realHessian_normSq_inner, inner_smul_right, hj, hk,
    vecMulVec_apply]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring

theorem complexHessian_perpQuadratic (a z : ComplexModel (m + 1)) :
    complexHessian (perpQuadratic a) z = 1 - vecMulVec (fun j => star (a j)) (fun k => a k) := by
  have hsplit : perpQuadratic a = (fun y : ComplexModel (m + 1) => ‖y‖ ^ 2) +
      (-1 : ℝ) • fun y : ComplexModel (m + 1) => ‖⟪a, y⟫_ℂ‖ ^ 2 := by
    funext y
    simp [perpQuadratic, sub_eq_add_neg]
  have h1 : ContDiffAt ℝ 2 (fun y : ComplexModel (m + 1) => ‖y‖ ^ 2) z :=
    (contDiff_norm_sq ℝ).contDiffAt
  have h2 : ContDiffAt ℝ 2 (fun y : ComplexModel (m + 1) => ‖⟪a, y⟫_ℂ‖ ^ 2) z :=
    (contDiff_normSq_inner a).contDiffAt
  rw [hsplit, complexHessian_add (v := (-1 : ℝ) • fun y : ComplexModel (m + 1) => ‖⟪a, y⟫_ℂ‖ ^ 2)
    h1 (h2.const_smul (-1 : ℝ)), complexHessian_smul h2,
    complexHessian_norm_sq, complexHessian_normSq_inner]
  simp [sub_eq_add_neg]

/-! ### The density identity -/

/-- **The directional Levi form as a top density**: for a unit vector `a`, the density of
`ddᶜ f ∧ (ddᶜ q_a)^m` at `z` is `(m! / π^{m+1}) · L_f(z; a)`. -/
theorem topDensity_smoothDDC_perpQuadratic {f : ComplexModel (m + 1) → ℝ}
    {z : ComplexModel (m + 1)} (hf : ContDiffAt ℝ 2 f z) (a : ComplexModel (m + 1))
    (ha : ‖a‖ = 1) :
    topDensity (wedgeProd (m + 1) (Fin.cons (smoothDDC f z)
        (fun _ : Fin m => smoothDDC (perpQuadratic a) z))) =
      (m.factorial / Real.pi ^ (m + 1)) * leviForm f z a := by
  have hq : ContDiffAt ℝ 2 (perpQuadratic a) z := (contDiff_perpQuadratic a).contDiffAt
  have hslots : ∀ i, IsOneOne ((Fin.cons (smoothDDC f z)
      (fun _ : Fin m => smoothDDC (perpQuadratic a) z) : Fin (m + 1) → RealForm (m + 1) 2) i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      exact fun u v => smoothDDC_isOneOne hf u v
    · simp only [Fin.cons_succ]
      exact fun u v => smoothDDC_isOneOne hq u v
  rw [topDensity_wedgeProd, actualMixedTopDensity_eq_normalizedMixedTopDensity _ hslots,
    normalizedMixedTopDensity]
  set y : Fin (m + 1) → ℂ := fun j => star (a j) with hydef
  have hfun : (fun i => normalizedHermitianMatrix ((Fin.cons (smoothDDC f z)
      (fun _ : Fin m => smoothDDC (perpQuadratic a) z) : Fin (m + 1) → RealForm (m + 1) 2) i)) =
      (Fin.cons (complexHessian f z) (fun _ : Fin m => 1 - vecMulVec y (star y)) :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      exact normalizedHermitianMatrix_smoothDDC hf
    · simp only [Fin.cons_succ]
      rw [normalizedHermitianMatrix_smoothDDC hq, complexHessian_perpQuadratic]
      congr 2
      funext k
      simp [hydef]
  have hy : star y ⬝ᵥ y = 1 := by
    have h2 : ‖a‖ ^ 2 = 1 := by rw [ha]; norm_num
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h2
    simp only [hydef, dotProduct, Pi.star_apply, star_star]
    rw [← Complex.ofReal_one, ← h2, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
  rw [hfun, mixedCoefficient_cons_projection _ y hy,
    complexHessian_dotProduct_mulVec_eq_leviForm hf y, hydef, conjugateCoordinateCombination_star]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.ofReal_re, Complex.natCast_im,
    Complex.ofReal_im, mul_zero, sub_zero]
  ring

end

end SGPT.Foundations.Analysis.Pending.DirectionalLeviDensity
