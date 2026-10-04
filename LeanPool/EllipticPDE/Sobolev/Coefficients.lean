/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Sobolev.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity


/-!
# Bounded measurable coefficients acting on `L²` (general elliptic operator)

To pass from the Poisson form `∑ᵢ ⟪∂ᵢu, ∂ᵢv⟫` to the general divergence-form operator
`L u = -Dⱼ(aᵢⱼ Dᵢu) + bᵢ Dᵢu + c u` we need to *multiply* an `L²` gradient component by a
bounded measurable coefficient and still land in `L²`. This file provides

* `mulCoeffL` : a bounded measurable scalar `f` (`|f| ≤ M`) acting on `L²(Ω)` as a
  continuous linear map `g ↦ [f · g]`, with operator-norm bound `M`;
* `mulCoeffL_coeFn` : its pointwise a.e. representative `x ↦ f x · g x`;
* `EllipticCoeff` : the bundle of a measurable, bounded, uniformly elliptic coefficient
  matrix `a` (Evans §6.1.1: `∑ aᵢⱼ ξᵢ ξⱼ ≥ λ |ξ|²`).

This mirrors, on the scalar `PiLp` encoding of `Sobolev/Basic.lean`, the coefficient action
`coeffMulLpL` that DeGiorgi (`WeakFormulation/CoefficientOperator.lean`) builds on the
vector-valued `L²(Ω; E)` encoding.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Pointwise multiplication by a bounded measurable coefficient -/

/-- The pointwise product of a bounded measurable scalar function with an `L²` class is `L²`. -/
lemma memLp_mul_of_bdd {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume.restrict Ω), |f x| ≤ M) (g : L2D Ω) :
    MemLp (fun x => f x * (g x : ℝ)) 2 (volume.restrict Ω) := by
  refine (Lp.memLp g).of_le_mul (c := M)
    (hf.aestronglyMeasurable.mul (Lp.aestronglyMeasurable g)) ?_
  filter_upwards [hM] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

/-- The `L²` class of `f · g` for a bounded measurable `f`. -/
def mulCoeffCls {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume.restrict Ω), |f x| ≤ M) (g : L2D Ω) : L2D Ω :=
  (memLp_mul_of_bdd hf hM g).toLp _

/-- The class `mulCoeffCls hf hM g` has pointwise representative `x ↦ f x · g x` a.e. -/
lemma mulCoeffCls_coeFn {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume.restrict Ω), |f x| ≤ M) (g : L2D Ω) :
    mulCoeffCls hf hM g =ᵐ[volume.restrict Ω] fun x => f x * (g x : ℝ) :=
  MemLp.coeFn_toLp _

/-- A bounded measurable scalar `f` acting on `L²(Ω)` by pointwise multiplication,
as a (bare) linear map `g ↦ [f · g]`. -/
def mulCoeffLM {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume.restrict Ω), |f x| ≤ M) : L2D Ω →ₗ[ℝ] L2D Ω where
  toFun := mulCoeffCls hf hM
  map_add' := by
    intro g h
    apply Lp.ext
    filter_upwards [mulCoeffCls_coeFn hf hM (g + h), mulCoeffCls_coeFn hf hM g,
      mulCoeffCls_coeFn hf hM h, Lp.coeFn_add g h,
      Lp.coeFn_add (mulCoeffCls hf hM g) (mulCoeffCls hf hM h)] with x h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply]
    ring
  map_smul' := by
    intro c g
    apply Lp.ext
    filter_upwards [mulCoeffCls_coeFn hf hM (c • g), mulCoeffCls_coeFn hf hM g,
      Lp.coeFn_smul c g, Lp.coeFn_smul c (mulCoeffCls hf hM g)] with x h1 h2 h3 h4
    simp only [h1, h2, h3, h4, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Simp lemma: `mulCoeffLM hf hM g = mulCoeffCls hf hM g`. -/
@[simp] private lemma mulCoeffLM_apply {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume.restrict Ω), |f x| ≤ M) (g : L2D Ω) :
    mulCoeffLM hf hM g = mulCoeffCls hf hM g := rfl

/-- A bounded measurable scalar `f` (`|f| ≤ M`) acting on `L²(Ω)` by pointwise
multiplication, as a continuous linear map with operator norm `≤ M`. -/
def mulCoeffL {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume.restrict Ω), |f x| ≤ M) : L2D Ω →L[ℝ] L2D Ω :=
  (mulCoeffLM hf hM).mkContinuous M (by
    intro g
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [mulCoeffCls_coeFn hf hM g, hM] with x hx hMx
    rw [mulCoeffLM_apply hf hM g, hx,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hMx (abs_nonneg _))

/-- Simp lemma: `mulCoeffL hf hM g = mulCoeffCls hf hM g`. -/
@[simp] lemma mulCoeffL_apply {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume.restrict Ω), |f x| ≤ M) (g : L2D Ω) :
    mulCoeffL hf hM g = mulCoeffCls hf hM g := rfl

/-- The pointwise a.e. representative of the coefficient action. -/
lemma mulCoeffL_coeFn {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume.restrict Ω), |f x| ≤ M) (g : L2D Ω) :
    mulCoeffL hf hM g =ᵐ[volume.restrict Ω] fun x => f x * (g x : ℝ) := by
  rw [mulCoeffL_apply]; exact mulCoeffCls_coeFn hf hM g

/-- Operator-norm bound for the coefficient action: `‖[f · g]‖ ≤ M ‖g‖`. -/
lemma norm_mulCoeffL_le {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume.restrict Ω), |f x| ≤ M) (g : L2D Ω) :
    ‖mulCoeffL hf hM g‖ ≤ M * ‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [mulCoeffL_coeFn hf hM g, hM] with x hx hMx
  rw [hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hMx (abs_nonneg _)

/-- The inner product of the coefficient action against `h` is the integral of the triple
product `∫_Ω f · g · h`. -/
lemma inner_mulCoeffL_eq {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume.restrict Ω), |f x| ≤ M) (g h : L2D Ω) :
    ⟪mulCoeffL hf hM g, h⟫ = ∫ x in Ω, f x * (g x : ℝ) * (h x : ℝ) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulCoeffL_coeFn hf hM g] with a ha
  rw [Real.inner_apply, ha]

/-! ### Uniformly elliptic coefficient matrices (Evans §6.1.1) -/

/-- A measurable, bounded coefficient matrix `a` that is **uniformly elliptic** with
ellipticity constant `lam > 0` and sup bound `Λ`: `∑ᵢⱼ aᵢⱼ(x) ξᵢ ξⱼ ≥ lam · |ξ|²` and
`|aᵢⱼ(x)| ≤ Λ` for almost every `x` (Evans §6.1.1 states ellipticity pointwise for
a.e. `x ∈ U`; the bundle has a measurable representative on `ℝᵈ` with the bounds holding
`volume`-a.e., which restricts to a.e. on every domain `Ω`). This is exactly the data the
divergence-form operator `Lu = -Dⱼ(aᵢⱼ Dᵢu)` needs for the energy estimate.

**No symmetry is assumed**, where Evans §6.1.1 assumes `aᵢⱼ = aⱼᵢ` throughout and
Gilbarg-Trudinger ch. 8 assumes it for the principal part. Neither field above sees the
antisymmetric part of `a x`: `elliptic` constrains the quadratic form `ξ ↦ ∑ᵢⱼ aᵢⱼ ξᵢ ξⱼ`,
which the antisymmetric part annihilates, and `bdd` constrains the entries one at a time.

Symmetry is asked for at one place in the development, as the explicit hypothesis
`hAsymm : ∀ᵐ x ∂(volume.restrict Ω), ∀ i j, a x i j = a x j i` of `bilin_symm` and of the
spectral theorems above it (`symmetric_fullElliptic_spectral` and its bounded-set form).
It enters there because the spectral theorem for compact self-adjoint operators asks the
bilinear form to be symmetric, and `bilin` is symmetric exactly when `a` is (with the drift
vanishing). Every other result of the library is proved for an arbitrary `a`: Gårding,
existence and uniqueness, Fredholm, the resolvent bound, and the whole
interior-regularity chain. With `a` non-symmetric the formal adjoint
`L* v = -Dᵢ(aᵢⱼ Dⱼv) - bⁱ Dᵢv + (c - Dᵢbⁱ)v` has principal part built from the
transpose, which is the transpose problem the Fredholm solvability criterion states. -/
structure EllipticCoeff (d : ℕ) where
  /-- The coefficient matrix entries. -/
  a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ
  /-- Ellipticity constant. -/
  lam : ℝ
  /-- Uniform sup bound on the entries. -/
  Λ : ℝ
  /-- The ellipticity constant is strictly positive. -/
  lam_pos : 0 < lam
  /-- The sup bound is nonnegative. -/
  Λ_nonneg : 0 ≤ Λ
  /-- Every entry of the matrix is measurable. -/
  measurable : ∀ i j, Measurable (fun x => a x i j)
  /-- Every entry is bounded by `Λ` almost everywhere. -/
  bdd : ∀ i j, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a x i j| ≤ Λ
  /-- The quadratic form of `a x` dominates `lam · |ξ|²` for almost every `x`. -/
  elliptic : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
    ∀ ξ : Fin d → ℝ, lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j

namespace EllipticCoeff

variable (A : EllipticCoeff d)

/-- The `(i, j)` coefficient acting on `L²(Ω)`. -/
def actL {Ω : Set (EuclideanSpace ℝ (Fin d))} (i j : Fin d) : L2D Ω →L[ℝ] L2D Ω :=
  mulCoeffL (A.measurable i j) (ae_restrict_of_ae (A.bdd i j))

/-- Simp lemma: `A.actL i j g` has pointwise representative `x ↦ A.a x i j · g x` a.e. -/
@[simp] lemma actL_coeFn {Ω : Set (EuclideanSpace ℝ (Fin d))} (i j : Fin d) (g : L2D Ω) :
    A.actL i j g =ᵐ[volume.restrict Ω] fun x => A.a x i j * (g x : ℝ) :=
  mulCoeffL_coeFn _ _ g

/-- `⟪A.actL i j g, h⟫ = ∫_Ω A.a x i j · g x · h x`. -/
lemma inner_actL_eq {Ω : Set (EuclideanSpace ℝ (Fin d))} (i j : Fin d) (g h : L2D Ω) :
    ⟪A.actL i j g, h⟫ = ∫ x in Ω, A.a x i j * (g x : ℝ) * (h x : ℝ) :=
  inner_mulCoeffL_eq _ _ g h

/-- Operator-norm bound: `‖A.actL i j g‖ ≤ Λ · ‖g‖`. -/
lemma norm_actL_le {Ω : Set (EuclideanSpace ℝ (Fin d))} (i j : Fin d) (g : L2D Ω) :
    ‖A.actL i j g‖ ≤ A.Λ * ‖g‖ :=
  norm_mulCoeffL_le _ _ g

end EllipticCoeff

end EllipticPdes.Sobolev
