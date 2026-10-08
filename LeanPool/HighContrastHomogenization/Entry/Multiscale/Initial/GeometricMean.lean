/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Initial.ScalarBounds

/-!
# High-contrast homogenization: Entry.Multiscale.Initial.GeometricMean

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Initialization: the matrix geometric mean and the square-root order toolkit

Operator-order support for the two entry-radius kernels of
`HCPoly/Entry/Multiscale/Initial/CanonicalMetric.lean`: monotonicity of the matrix square root,
Loewner congruence and inversion, and the matrix geometric mean `A #ᵐ B` with its
Riccati characterization, commutativity, monotonicity in both arguments and homogeneity
(`p.global.selection`).

These are helper facts of the initialization route, kept in the `GeometricMean` namespace; they
carry no probability law and no annealed premise.
-/

open HCPolySupport.HighContrast (matSqrt matSqrt_eq matSqrt_spec)
namespace HCPolySupport.HighContrast.Multiscale

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

namespace GeometricMean

/-! ## Public geometric-mean toolkit

These helpers support the entry-radius kernels in
HCPoly/Entry/Multiscale/Initial/CanonicalMetric.lean. -/


open Matrix

/-! ## Part 1. The matrix geometric mean -/


variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! Ported square-root order toolkit. -/


variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Small algebraic helpers ported from `HCPoly.Geometry.OperatorOrder` /
`HCPoly.Geometry.SqrtOrder`. -/

omit [DecidableEq ι] in
/-- Congruence is monotone: conjugating both sides of a Loewner inequality by the same
matrix preserves it. -/
theorem conj_le_conj (C : Matrix ι ι ℝ) {A B : Matrix ι ι ℝ} (h : A ≤ B) :
    Cᴴ * A * C ≤ Cᴴ * B * C := by
  have hPS : (B - A).PosSemidef := Matrix.le_iff.mp h
  have hconj := hPS.conjTranspose_mul_mul_same C
  rw [Matrix.le_iff]
  have hrw : Cᴴ * B * C - Cᴴ * A * C = Cᴴ * (B - A) * C := by noncomm_ring
  rw [hrw]
  exact hconj

theorem isUnit_det_of_posDef {A : Matrix ι ι ℝ} (hA : A.PosDef) : IsUnit A.det :=
  (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit

theorem norm_mul_self_of_symm {X : Matrix ι ι ℝ} (hX : Xᴴ = X) :
    ‖X * X‖ = ‖X‖ ^ 2 := by
  have h := CStarRing.norm_star_mul_self (x := X)
  rw [Matrix.star_eq_conjTranspose, hX] at h
  rw [h, sq]

theorem isHermitian_pow {X : Matrix ι ι ℝ} (hX : Xᴴ = X) (m : ℕ) :
    (X ^ m)ᴴ = X ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Matrix.conjTranspose_mul, hX, ih, ← pow_succ', pow_succ]

omit [DecidableEq ι] in
theorem inner_toLp (x y : ι → ℝ) :
    inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ ι) (WithLp.toLp 2 y) = x ⬝ᵥ y := by
  simp [PiLp.inner_apply, dotProduct, RCLike.inner_apply, mul_comm]

omit [DecidableEq ι] in
theorem norm_toLp_sq_fintype (x : ι → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ^ 2 = x ⬝ᵥ x := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp]

theorem toEuclideanCLM_apply_fintype (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A (WithLp.toLp 2 x)
      = WithLp.toLp 2 (A *ᵥ x) := rfl

omit [DecidableEq ι] in
theorem dotProduct_mulVec_symm {A : Matrix ι ι ℝ} (hA : Aᵀ = A) (x y : ι → ℝ) :
    x ⬝ᵥ A *ᵥ y = (A *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA]

theorem dotProduct_mulVec_le_norm_mul (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ A *ᵥ x ≤ ‖A‖ * (x ⬝ᵥ x) := by
  have hcs : x ⬝ᵥ A *ᵥ x ≤
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ *
        ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℝ ι)‖ := by
    rw [← inner_toLp x (A *ᵥ x)]
    exact real_inner_le_norm _ _
  have hop : ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℝ ι)‖ ≤
      ‖A‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ := by
    rw [← toEuclideanCLM_apply_fintype A x, Matrix.cstar_norm_def]
    exact (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A).le_opNorm _
  have hx : (0 : ℝ) ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ := norm_nonneg _
  calc x ⬝ᵥ A *ᵥ x
      ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ *
          ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℝ ι)‖ := hcs
    _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ *
          (‖A‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖) :=
        mul_le_mul_of_nonneg_left hop hx
    _ = ‖A‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ^ 2 := by ring
    _ = ‖A‖ * (x ⬝ᵥ x) := by rw [norm_toLp_sq_fintype]

theorem norm_le_of_le_smul_one {A : Matrix ι ι ℝ} (hA : A.PosSemidef) {t : ℝ}
    (ht : 0 ≤ t) (h : A ≤ t • (1 : Matrix ι ι ℝ)) : ‖A‖ ≤ t := by
  have hq : ∀ x : ι → ℝ, x ⬝ᵥ A *ᵥ x ≤ t * (x ⬝ᵥ x) := by
    intro x
    have hPS := Matrix.posSemidef_iff_dotProduct_mulVec.mp (Matrix.le_iff.mp h)
    have hx := hPS.2 x
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul] at hx
    simp only [star_trivial, smul_eq_mul] at hx
    linarith only [hx]
  have hsq : ∀ x : ι → ℝ, x ⬝ᵥ (A * A) *ᵥ x ≤ t * (x ⬝ᵥ A *ᵥ x) := by
    intro x
    obtain ⟨hBpsd, hBB⟩ := matSqrt_spec hA
    set B : Matrix ι ι ℝ := matSqrt A with hBdef
    have hBsymm : Bᵀ = B := by
      rw [← conjTranspose_eq_transpose']; exact hBpsd.isHermitian
    have h1 : (B *ᵥ x) ⬝ᵥ A *ᵥ (B *ᵥ x) ≤ t * ((B *ᵥ x) ⬝ᵥ (B *ᵥ x)) := hq (B *ᵥ x)
    have hLHS : (B *ᵥ x) ⬝ᵥ A *ᵥ (B *ᵥ x) = x ⬝ᵥ (A * A) *ᵥ x := by
      have hBAB : B * A * B = A * A := by rw [← hBB]; noncomm_ring
      rw [← dotProduct_mulVec_symm hBsymm x (A *ᵥ (B *ᵥ x)), Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, hBAB]
    have hRHS : (B *ᵥ x) ⬝ᵥ (B *ᵥ x) = x ⬝ᵥ A *ᵥ x := by
      rw [← dotProduct_mulVec_symm hBsymm x (B *ᵥ x), Matrix.mulVec_mulVec, hBB]
    rw [hLHS, hRHS] at h1
    exact h1
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ ht fun y => ?_
  obtain ⟨x, rfl⟩ : ∃ x : ι → ℝ, y = WithLp.toLp 2 x := ⟨WithLp.ofLp y, rfl⟩
  rw [toEuclideanCLM_apply_fintype]
  refine le_of_sq_le_sq ?_ (mul_nonneg ht (norm_nonneg _))
  rw [norm_toLp_sq_fintype, mul_pow, norm_toLp_sq_fintype]
  have hAsymm : Aᵀ = A := by
    rw [← conjTranspose_eq_transpose']; exact hA.isHermitian
  have hexp : (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A * A) *ᵥ x := by
    rw [← dotProduct_mulVec_symm hAsymm x (A *ᵥ x), Matrix.mulVec_mulVec]
  have h2 := hsq x
  have h3 := hq x
  have h4 : t * (x ⬝ᵥ A *ᵥ x) ≤ t * (t * (x ⬝ᵥ x)) := mul_le_mul_of_nonneg_left h3 ht
  rw [hexp]
  calc x ⬝ᵥ (A * A) *ᵥ x ≤ t * (x ⬝ᵥ A *ᵥ x) := h2
    _ ≤ t * (t * (x ⬝ᵥ x)) := h4
    _ = t ^ 2 * (x ⬝ᵥ x) := by ring

theorem le_smul_one_of_norm_le {A : Matrix ι ι ℝ} (hA : A.PosSemidef) {t : ℝ}
    (h : ‖A‖ ≤ t) : A ≤ t • (1 : Matrix ι ι ℝ) := by
  have hherm : (t • (1 : Matrix ι ι ℝ) - A).IsHermitian := by
    refine Matrix.IsHermitian.sub ?_ hA.isHermitian
    simp [Matrix.IsHermitian]
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_)
  have hbound := dotProduct_mulVec_le_norm_mul A x
  have hxx : (0 : ℝ) ≤ x ⬝ᵥ x := by
    rw [← norm_toLp_sq_fintype]; positivity
  have hstep : ‖A‖ * (x ⬝ᵥ x) ≤ t * (x ⬝ᵥ x) := mul_le_mul_of_nonneg_right h hxx
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul]
  simp only [star_trivial, smul_eq_mul]
  linarith only [hbound, hstep]

theorem norm_le_one_of_le_one {X : Matrix ι ι ℝ} (hX : X.PosSemidef)
    (h : X ≤ 1) : ‖X‖ ≤ 1 := by
  refine norm_le_of_le_smul_one hX zero_le_one ?_
  rwa [one_smul]

omit [DecidableEq ι] in
theorem posDef_conj_of_posDef {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (B * A * B).PosDef := by
  classical
  have hBinj : Function.Injective B.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hB.isUnit
  have h := hA.conjTranspose_mul_mul_same (B := B) hBinj
  rwa [hB.isHermitian.eq] at h

theorem inv_smul_of_posDef {A : Matrix ι ι ℝ} (hA : A.PosDef) {a : ℝ} (ha : a ≠ 0) :
    (a • A)⁻¹ = a⁻¹ • A⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ha,
    Matrix.mul_nonsing_inv A (isUnit_det_of_posDef hA), one_smul]

/-- The matrix geometric mean `A # B = A^{1/2}(A^{-1/2} B A^{-1/2})^{1/2} A^{1/2}`. -/
@[expose]
def geoMean (A B : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  matSqrt A * matSqrt (matSqrt A⁻¹ * B * matSqrt A⁻¹) * matSqrt A

theorem geoMeanPosDef {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (geoMean A B).PosDef :=
  posDef_conj_of_posDef (posDef_matSqrt (posDef_normalize hB hA)) (posDef_matSqrt hA)

theorem sqrtCancel {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    matSqrt A * matSqrt A⁻¹ = 1 ∧ matSqrt A⁻¹ * matSqrt A = 1 := by
  have hu : IsUnit (matSqrt A).det := isUnit_det_of_posDef (posDef_matSqrt hA)
  rw [matSqrt_inv hA]
  exact ⟨Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu⟩

theorem riccatiOfRoots {P R S B : Matrix ι ι ℝ}
    (hPR : P * R = 1) (hRP : R * P = 1) (hSS : S * S = R * B * R) :
    P * S * P * (R * R) * (P * S * P) = B := by
  calc P * S * P * (R * R) * (P * S * P)
      = P * S * ((P * R) * (R * P)) * S * P := by noncomm_ring
    _ = P * (S * S) * P := by rw [hPR, hRP]; noncomm_ring
    _ = (P * R) * B * (R * P) := by rw [hSS]; noncomm_ring
    _ = B := by rw [hPR, hRP, Matrix.one_mul, Matrix.mul_one]

theorem geoMean_riccati {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    geoMean A B * A⁻¹ * geoMean A B = B := by
  obtain ⟨hPR, hRP⟩ := sqrtCancel hA
  have hSS := (matSqrt_spec (posDef_normalize hB hA).posSemidef).2
  have key := riccatiOfRoots hPR hRP hSS
  rw [(matSqrt_spec hA.inv.posSemidef).2] at key
  exact key

theorem eq_geoMean_of_riccati {A B X : Matrix ι ι ℝ} (hA : A.PosDef)
    (hX : X.PosDef) (h : X * A⁻¹ * X = B) : X = geoMean A B := by
  have hRR : matSqrt A⁻¹ * matSqrt A⁻¹ = A⁻¹ := (matSqrt_spec hA.inv.posSemidef).2
  have hY : (matSqrt A⁻¹ * X * matSqrt A⁻¹).PosDef := posDef_conj_of_posDef hX (posDef_matSqrt
    hA.inv)
  have hYY : (matSqrt A⁻¹ * X * matSqrt A⁻¹) * (matSqrt A⁻¹ * X * matSqrt A⁻¹)
      = matSqrt A⁻¹ * B * matSqrt A⁻¹ := by
    calc (matSqrt A⁻¹ * X * matSqrt A⁻¹) * (matSqrt A⁻¹ * X * matSqrt A⁻¹)
        = matSqrt A⁻¹ * X * (matSqrt A⁻¹ * matSqrt A⁻¹) * X * matSqrt A⁻¹ := by noncomm_ring
      _ = matSqrt A⁻¹ * (X * A⁻¹ * X) * matSqrt A⁻¹ := by rw [hRR]; noncomm_ring
      _ = matSqrt A⁻¹ * B * matSqrt A⁻¹ := by rw [h]
  have hM : (matSqrt A⁻¹ * B * matSqrt A⁻¹).PosSemidef := by
    rw [← hYY]
    have hq := Matrix.posSemidef_conjTranspose_mul_self (matSqrt A⁻¹ * X * matSqrt A⁻¹)
    rwa [hY.isHermitian.eq] at hq
  have hYsqrt : matSqrt (matSqrt A⁻¹ * B * matSqrt A⁻¹) = matSqrt A⁻¹ * X * matSqrt A⁻¹ :=
    matSqrt_eq hM hY.posSemidef hYY
  obtain ⟨hPR, hRP⟩ := sqrtCancel hA
  calc X = (matSqrt A * matSqrt A⁻¹) * X * (matSqrt A⁻¹ * matSqrt A) := by
        rw [hPR, hRP, Matrix.one_mul, Matrix.mul_one]
    _ = matSqrt A * (matSqrt A⁻¹ * X * matSqrt A⁻¹) * matSqrt A := by noncomm_ring
    _ = matSqrt A * matSqrt (matSqrt A⁻¹ * B * matSqrt A⁻¹) * matSqrt A := by rw [hYsqrt]
    _ = geoMean A B := rfl

theorem invRiccati {A B X : Matrix ι ι ℝ} (h : X * A⁻¹ * X = B) :
    X⁻¹ * (A⁻¹)⁻¹ * X⁻¹ = B⁻¹ := by
  rw [← h, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]

theorem eq_geoMean_comm_of_riccati {A B X : Matrix ι ι ℝ} (hA : A.PosDef)
    (hB : B.PosDef) (hX : X.PosDef) (hric : X * A⁻¹ * X = B) : X = geoMean B A := by
  have hinv : X⁻¹ * A * X⁻¹ = B⁻¹ := by
    have h := invRiccati hric
    rwa [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hA)] at h
  refine eq_geoMean_of_riccati hB hX ?_
  have hstep : X * (X⁻¹ * A * X⁻¹) * X = A := by
    calc X * (X⁻¹ * A * X⁻¹) * X = (X * X⁻¹) * A * (X⁻¹ * X) := by noncomm_ring
      _ = A := by
          rw [Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hX), Matrix.nonsing_inv_mul _
            (isUnit_det_of_posDef hX),
            Matrix.one_mul, Matrix.mul_one]
  rw [← hstep, hinv]

theorem geoMean_comm {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    geoMean A B = geoMean B A :=
  eq_geoMean_comm_of_riccati hA hB (geoMeanPosDef hA hB) (geoMean_riccati hA hB)

theorem geoMean_mono_right {A B₀ B₁ : Matrix ι ι ℝ} (hA : A.PosDef)
    (hB₀ : B₀.PosDef) (hB₁ : B₁.PosDef) (h : B₀ ≤ B₁) :
    geoMean A B₀ ≤ geoMean A B₁ := by
  have hRsymm : (matSqrt A⁻¹)ᴴ = matSqrt A⁻¹ := conjTranspose_matSqrt hA.inv.posSemidef
  have hPsymm : (matSqrt A)ᴴ = matSqrt A := conjTranspose_matSqrt hA.posSemidef
  have hnorm : matSqrt A⁻¹ * B₀ * matSqrt A⁻¹ ≤ matSqrt A⁻¹ * B₁ * matSqrt A⁻¹ :=
    conj_le_conj' hRsymm h
  have hroot := matSqrt_le_matSqrt (posDef_normalize hB₀ hA).posSemidef
    (posDef_normalize hB₁ hA) hnorm
  exact conj_le_conj' hPsymm hroot

theorem geoMean_mono {A₀ A₁ B₀ B₁ : Matrix ι ι ℝ} (hA₀ : A₀.PosDef)
    (hA₁ : A₁.PosDef) (hB₀ : B₀.PosDef) (hB₁ : B₁.PosDef)
    (hA : A₀ ≤ A₁) (hB : B₀ ≤ B₁) :
    geoMean A₀ B₀ ≤ geoMean A₁ B₁ := by
  have h1 : geoMean A₀ B₀ ≤ geoMean A₀ B₁ := geoMean_mono_right hA₀ hB₀ hB₁ hB
  have h2 : geoMean B₁ A₀ ≤ geoMean B₁ A₁ := geoMean_mono_right hB₁ hA₀ hA₁ hA
  rw [← geoMean_comm hA₀ hB₁, geoMean_comm hB₁ hA₁] at h2
  exact h1.trans h2

theorem geoMean_self {A : Matrix ι ι ℝ} (hA : A.PosDef) : geoMean A A = A := by
  refine (eq_geoMean_of_riccati hA hA ?_).symm
  rw [Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hA), Matrix.one_mul]

theorem geoMean_smul {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    geoMean (a • A) (b • B) = Real.sqrt (a * b) • geoMean A B := by
  have hab : 0 < a * b := mul_pos ha hb
  have hs : 0 < Real.sqrt (a * b) := Real.sqrt_pos.mpr hab
  have hss : Real.sqrt (a * b) * Real.sqrt (a * b) = a * b := Real.mul_self_sqrt hab.le
  have hX : (Real.sqrt (a * b) • geoMean A B).PosDef := (geoMeanPosDef hA hB).smul hs
  refine (eq_geoMean_of_riccati (hA.smul ha) hX ?_).symm
  rw [inv_smul_of_posDef hA ha.ne']
  have hscal : Real.sqrt (a * b) • geoMean A B * (a⁻¹ • A⁻¹) *
      (Real.sqrt (a * b) • geoMean A B) =
      (Real.sqrt (a * b) * a⁻¹ * Real.sqrt (a * b)) • (geoMean A B * A⁻¹ * geoMean A B) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_assoc]
  rw [hscal, geoMean_riccati hA hB]
  congr 1
  have hre : Real.sqrt (a * b) * a⁻¹ * Real.sqrt (a * b)
      = Real.sqrt (a * b) * Real.sqrt (a * b) * a⁻¹ := by ring
  rw [hre, hss]
  field_simp

end GeometricMean

end

end HCPolySupport.HighContrast.Multiscale
