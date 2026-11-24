/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ComplexManifold
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.SmoothPlurisubharmonic
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Smooth Monge–Ampère densities and local Bedford–Taylor testing

The complex Hessian below is computed from the actual second real Fréchet
derivative on `ComplexModel n`. We use the standard coordinate orientation
`dx₁ ∧ dy₁ ∧ ... ∧ dxₙ ∧ dyₙ` and the real inner-product Lebesgue measure.
For `ddᶜ = i ∂∂bar / (2π)` the density is `n! / π^n * det (u_{zⱼ zBarₖ})`.
Demailly III.3 uses twice this `ddᶜ`; its degree-n product is rescaled by `2⁻ⁿ`.

The positive measure constructor requires smoothness and positivity of the
actual Hessian. `ENNReal.ofReal` is only an encoding of a nonnegative density
under these hypotheses, not a definition of a positive product for arbitrary
non-PSH functions. No singular product is constructed in this file.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

/-- Standard complex coordinate vectors. The associated real frame is ordered
as `e₀, I e₀, e₁, I e₁, ...`. -/
def coordinateVector (j : Fin n) : ComplexModel n := EuclideanSpace.single j 1

/-- The genuine matrix `(∂²u / ∂zⱼ ∂zBarₖ)`, expressed through the real Hessian.
Its transpose is the convention used for the quadratic form `vᴴ H v`;
both have the same determinant and the same semipositivity condition. -/
def complexHessian (u : ComplexModel n → ℝ) (z : ComplexModel n) :
    Matrix (Fin n) (Fin n) ℂ := fun j k =>
  ((realHessian u z (coordinateVector j) (coordinateVector k) +
      realHessian u z (Complex.I • coordinateVector j) (Complex.I • coordinateVector k) : ℝ) : ℂ)
        / 4 +
    Complex.I * ((realHessian u z (coordinateVector j) (Complex.I • coordinateVector k) -
      realHessian u z (Complex.I • coordinateVector j) (coordinateVector k) : ℝ) : ℂ) / 4

/-- The signed real density. Its interpretation as a smooth top product requires
C² regularity; its nonnegativity requires semipositivity. -/
def smoothDensity (u : ComplexModel n → ℝ) (z : ComplexModel n) : ℝ :=
  (n.factorial : ℝ) / Real.pi ^ n * (complexHessian u z).det.re

/-- Coefficient in the standard real orientation obtained by expanding
`((i/(2π)) ∑ Hⱼₖ dzⱼ ∧ dzBarₖ)^n`: each `dzⱼ ∧ dzBarⱼ` contributes `-2i`.
This is an algebraic coordinate expression, not a new exterior-power API. -/
def complexTopCoefficient (H : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (n.factorial : ℂ) * (Complex.I / (2 * (Real.pi : ℂ))) ^ n * H.det *
    (-2 * Complex.I) ^ n

theorem complexTopCoefficient_eq (H : Matrix (Fin n) (Fin n) ℂ) :
    complexTopCoefficient H = ((n.factorial : ℝ) / Real.pi ^ n : ℝ) * H.det := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hc : Complex.I / (2 * (Real.pi : ℂ)) * (-2 * Complex.I) =
      (Real.pi : ℂ)⁻¹ := by
    field_simp
    simp [Complex.I_sq]
  unfold complexTopCoefficient
  calc
    _ = (n.factorial : ℂ) *
        (Complex.I / (2 * (Real.pi : ℂ)) * (-2 * Complex.I)) ^ n * H.det := by
          rw [mul_pow (Complex.I / (2 * (Real.pi : ℂ))) (-2 * Complex.I)]
          ac_rfl
    _ = _ := by rw [hc]; simp [div_eq_mul_inv]

theorem smoothDensity_eq_re_topCoefficient (u : ComplexModel n → ℝ)
    (z : ComplexModel n) :
    smoothDensity u z = (complexTopCoefficient (complexHessian u z)).re := by
  rw [complexTopCoefficient_eq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, smoothDensity]

@[simp] theorem complexHessian_const (c : ℝ) (z : ComplexModel n) :
    complexHessian (fun _ => c) z = 0 := by
  ext j k
  simp [complexHessian]

theorem complexHessian_diagonal_re (u : ComplexModel n → ℝ)
    (z : ComplexModel n) (j : Fin n) :
    (complexHessian u z j j).re = leviForm u z (coordinateVector j) := by
  simp [complexHessian, leviForm, Complex.add_re, Complex.div_ofNat_re]

theorem complexHessian_add {u v : ComplexModel n → ℝ} {z : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u z) (hv : ContDiffAt ℝ 2 v z) :
    complexHessian (u + v) z = complexHessian u z + complexHessian v z := by
  ext j k
  simp only [complexHessian, realHessian_add hu hv, Matrix.add_apply,
    Complex.ofReal_add, Complex.ofReal_sub]
  ring

theorem complexHessian_smul {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u z) (c : ℝ) :
    complexHessian (c • u) z = (c : ℂ) • complexHessian u z := by
  ext j k
  simp only [complexHessian, realHessian_smul hu, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_mul, Matrix.smul_apply, smul_eq_mul]
  ring

theorem complexHessian_isHermitian {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u z) : (complexHessian u z).IsHermitian := by
  have hs (a b : ComplexModel n) : realHessian u z a b = realHessian u z b a := by
    simpa only [realHessian_eq_fderiv] using hu.isSymmSndFDerivAt (by norm_num) a b
  ext j k
  apply Complex.ext <;>
    simp [Matrix.conjTranspose_apply, complexHessian,
      hs (coordinateVector k) (coordinateVector j),
      hs (Complex.I • coordinateVector k) (Complex.I • coordinateVector j),
      hs (coordinateVector k) (Complex.I • coordinateVector j),
      hs (Complex.I • coordinateVector k) (coordinateVector j)]

@[simp] theorem complexHessian_norm_sq (z : ComplexModel n) :
    complexHessian (fun w : ComplexModel n => ‖w‖ ^ 2) z = 1 := by
  ext j k
  by_cases h : j = k
  · subst k
    norm_num [complexHessian, realHessian_norm_sq, coordinateVector, PiLp.inner_apply,
      apply_ite, norm_smul, Complex.norm_I]
  · simp [complexHessian, realHessian_norm_sq, coordinateVector, PiLp.inner_apply,
      apply_ite, h, Ne.symm h]

@[simp] theorem smoothDensity_norm_sq (z : ComplexModel n) :
    smoothDensity (fun w : ComplexModel n => ‖w‖ ^ 2) z =
      (n.factorial : ℝ) / Real.pi ^ n := by
  simp [smoothDensity]

theorem smoothDensity_nonneg {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (h : (complexHessian u z).PosSemidef) : 0 ≤ smoothDensity u z := by
  apply mul_nonneg (by positivity)
  exact (Complex.nonneg_iff.mp h.det_nonneg).1

@[simp] theorem smoothDensity_const (c : ℝ) (z : ComplexModel (n + 1)) :
    smoothDensity (fun _ => c) z = 0 := by
  simp [smoothDensity]

/-- C∞ and PSH on the actual open domain, together with the explicit
semipositivity certificate for the genuine coordinate Hessian. Equivalence of
the two positivity tests is a separate theorem, not an assumed correspondence. -/
def IsSmoothPshOn (U : Opens (ComplexModel n)) (u : ComplexModel n → ℝ) : Prop :=
  ContDiffOn ℝ ∞ u U ∧ PlurisubharmonicOn (fun z => (u z : EReal)) U ∧
    ∀ z ∈ U, (complexHessian u z).PosSemidef

/-- The smooth positive Monge–Ampère measure on U, extended by zero outside U.
`volume` is fixed standard Lebesgue volume, not an arbitrary Haar normalization. -/
def smoothMeasure (U : Opens (ComplexModel n)) (u : ComplexModel n → ℝ)
    (_hu : IsSmoothPshOn U u) : Measure (ComplexModel n) :=
  (volume.restrict (U : Set (ComplexModel n))).withDensity
    (fun z => ENNReal.ofReal (smoothDensity u z))

/-- A concrete nonconstant potential instantiates all constructor hypotheses. -/
theorem isSmoothPshOn_norm_sq (U : Opens (ComplexModel n)) :
    IsSmoothPshOn U (fun z : ComplexModel n => ‖z‖ ^ 2) := by
  refine ⟨(contDiff_norm_sq ℝ).contDiffOn,
    (discPshOn_norm_sq (U : Set (ComplexModel n))).plurisubharmonicOn U.isOpen, ?_⟩
  intro z _
  rw [complexHessian_norm_sq]
  exact Matrix.PosSemidef.one

/-- The standard quadratic potential has the correctly normalized flat volume. -/
theorem smoothMeasure_norm_sq (U : Opens (ComplexModel n)) :
    smoothMeasure U (fun z : ComplexModel n => ‖z‖ ^ 2) (isSmoothPshOn_norm_sq U) =
      ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n) •
        volume.restrict (U : Set (ComplexModel n)) := by
  simp [smoothMeasure, withDensity_const]

theorem smoothMeasure_weight_toReal (U : Opens (ComplexModel n))
    (u : ComplexModel n → ℝ) (hu : IsSmoothPshOn U u) {z : ComplexModel n}
    (hz : z ∈ U) :
    (ENNReal.ofReal (smoothDensity u z)).toReal = smoothDensity u z :=
  ENNReal.toReal_ofReal (smoothDensity_nonneg (hu.2.2 z hz))

theorem smoothMeasure_restrict {U V : Opens (ComplexModel n)} (hVU : V ≤ U)
    (u : ComplexModel n → ℝ) (hu : IsSmoothPshOn U u) (hv : IsSmoothPshOn V u) :
    (smoothMeasure U u hu).restrict (V : Set (ComplexModel n)) =
      smoothMeasure V u hv := by
  rw [smoothMeasure, restrict_withDensity V.isOpen.measurableSet,
    Measure.restrict_restrict_of_subset hVU]
  rfl

/-- A real-valued PSH function bounded in absolute value on a neighborhood of
each point of the domain. This excludes all poles on the domain. -/
def IsLocallyBoundedPshOn (Ω : Opens (ComplexModel n))
    (u : ComplexModel n → ℝ) : Prop :=
  PlurisubharmonicOn (fun z => (u z : EReal)) Ω ∧
    ∀ z ∈ Ω, ∃ V : Opens (ComplexModel n), z ∈ V ∧ V ≤ Ω ∧
      ∃ C : ℝ, ∀ w ∈ V, |u w| ≤ C

/-- Relative compactness includes the closure-in-domain condition, not just
boundedness or the inclusion of the open sets. -/
def RelativelyCompactIn (U Ω : Opens (ComplexModel n)) : Prop :=
  IsCompact (closure (U : Set (ComplexModel n))) ∧
    closure (U : Set (ComplexModel n)) ⊆ Ω

/-- Actual decreasing pointwise approximation, with smoothness and PSH needed
only on U. Values or differentiability outside U have no significance. -/
def IsDecreasingApproximation (U : Opens (ComplexModel n))
    (u : ComplexModel n → ℝ) (f : ℕ → ComplexModel n → ℝ) : Prop :=
  (∀ j, IsSmoothPshOn U (f j)) ∧
    (∀ z ∈ U, Antitone (fun j => f j z)) ∧
    ∀ z ∈ U, Tendsto (fun j => f j z) atTop (𝓝 (u z))

/-- Vague (compact-test) convergence on U of the constructed smooth measures.
Compact *topological* support inside U rules out boundary mass tests. -/
def WeaklyTendsTo (U : Opens (ComplexModel n)) (f : ℕ → ComplexModel n → ℝ)
    (hf : ∀ j, IsSmoothPshOn U (f j)) (μ : Measure (ComplexModel n)) : Prop :=
  ∀ φ : ComplexModel n → ℝ, Continuous φ → HasCompactSupport φ →
    tsupport φ ⊆ U →
      Tendsto (fun j => ∫ z, φ z ∂(smoothMeasure U (f j) (hf j))) atTop
        (𝓝 (∫ z, φ z ∂μ))

/-- A precise relation, not an assumed or chosen non-pluripolar product.
It includes approximation existence on every relatively compact subdomain,
and quantifies over *all* such approximations. The zero extension need not be
locally finite or regular at boundary points of Ω. -/
def IsLocalBedfordTaylorMeasure (Ω : Opens (ComplexModel n))
    (u : ComplexModel n → ℝ) (μ : Measure (ComplexModel n)) : Prop :=
  IsLocallyBoundedPshOn Ω u ∧
    μ (Ω : Set (ComplexModel n))ᶜ = 0 ∧
    (∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Ω → μ K < ⊤) ∧
    ∀ U : Opens (ComplexModel n), RelativelyCompactIn U Ω →
      (∃ f, IsDecreasingApproximation U u f) ∧
      ∀ f (hf : IsDecreasingApproximation U u f), WeaklyTendsTo U f hf.1 μ

theorem IsLocalBedfordTaylorMeasure.approximations_exist
    {Ω U : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)} (hμ : IsLocalBedfordTaylorMeasure Ω u μ)
    (hU : RelativelyCompactIn U Ω) : ∃ f, IsDecreasingApproximation U u f :=
  (hμ.2.2.2 U hU).1

/-- Any two admissible sequences have the same compact-test limits once the
Bedford–Taylor relation is established. Existence of that measure is not used
or asserted by this elementary consequence. -/
theorem IsLocalBedfordTaylorMeasure.sequence_independent
    {Ω U : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)} (hμ : IsLocalBedfordTaylorMeasure Ω u μ)
    (hU : RelativelyCompactIn U Ω)
    {f g : ℕ → ComplexModel n → ℝ}
    (hf : IsDecreasingApproximation U u f) (hg : IsDecreasingApproximation U u g) :
    WeaklyTendsTo U f hf.1 μ ∧ WeaklyTendsTo U g hg.1 μ :=
  ⟨(hμ.2.2.2 U hU).2 f hf, (hμ.2.2.2 U hU).2 g hg⟩

/-- Nonvacuity for smooth potentials: the constant sequence is admissible. -/
theorem IsSmoothPshOn.constantApproximation {U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsSmoothPshOn U u) :
    IsDecreasingApproximation U u (fun _ => u) :=
  ⟨fun _ => hu, fun _ _ _ _ _ => le_rfl, fun _ _ => tendsto_const_nhds⟩

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere
