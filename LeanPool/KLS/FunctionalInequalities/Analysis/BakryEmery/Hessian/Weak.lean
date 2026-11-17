/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Products

/-!
# Generic weak Hessian coordinates and pointwise identification
-/

@[expose] public section

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff

/-! Weak-route support for Letwin arXiv:2607.24164v1. -/

section WeakThirdDerivativeSymmetry

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

section StructuredSpace

variable {E : Type*}
  [NormedAddCommGroup E]

section InnerProduct

variable [InnerProductSpace ℝ E]

section FiniteDimensional

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private lemma HasWeakDerivAlong.congr_left {f f' g : E → ℝ} {v : E}
    (h : HasWeakDerivAlong f g v) (hff' : f =ᵐ[(volume : Measure E)] f') :
    HasWeakDerivAlong f' g v := by
  refine ⟨h.1.congr hff', h.2.1, ?_⟩
  intro ψ hψ hψc
  have hp :
      (fun x => f' x * fderiv ℝ ψ x v) =ᵐ[(volume : Measure E)]
        (fun x => f x * fderiv ℝ ψ x v) := by
    filter_upwards [hff'] with x hx
    rw [hx]
  rw [integral_congr_ae hp]
  exact h.2.2 ψ hψ hψc

private lemma HasWeakDerivAlong.congr_right {f g g' : E → ℝ} {v : E}
    (h : HasWeakDerivAlong f g v) (hgg' : g =ᵐ[(volume : Measure E)] g') :
    HasWeakDerivAlong f g' v := by
  refine ⟨h.1, h.2.1.congr hgg', ?_⟩
  intro ψ hψ hψc
  have hi := h.2.2 ψ hψ hψc
  have hp :
      (fun x => g x * ψ x) =ᵐ[(volume : Measure E)]
        (fun x => g' x * ψ x) := by
    filter_upwards [hgg'] with x hx
    rw [hx]
  rw [integral_congr_ae hp] at hi
  exact hi

end FiniteDimensional

/-- Differentiability of the gradient gives differentiability of the total Fréchet derivative. -/
theorem differentiableAt_fderiv_of_differentiableAt_gradient [CompleteSpace E]
    {u : E → ℝ} {x : E} (hx : DifferentiableAt ℝ (gradient u) x) :
    DifferentiableAt ℝ (fderiv ℝ u) x := by
  have heq :
      fderiv ℝ u = (InnerProductSpace.toDual ℝ E) ∘ gradient u := by
    funext y
    simp [gradient]
  rw [heq]
  exact
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.differentiableAt.comp x hx

/--
At a differentiability point of the gradient, the differentiated coordinate derivative is the total
Hessian entry. -/
theorem hessian_coord_of_gradient_diff {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {i j : Fin n} (hx : DifferentiableAt ℝ (gradient u) x) :
    fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ j)) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) =
      hessianMatrix u x i j := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hc :
    DifferentiableAt ℝ (fun _ : EuclideanSpace ℝ (Fin n) => EuclideanSpace.basisFun (Fin n) ℝ j)
      x :=
    (differentiable_const (EuclideanSpace.basisFun (Fin n) ℝ j) :
        Differentiable ℝ
          (fun _ : EuclideanSpace ℝ (Fin n) =>
            EuclideanSpace.basisFun (Fin n) ℝ j)).differentiableAt
  have h := fderiv_clm_apply hfd hc
  have h' :=
    congrArg
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L (EuclideanSpace.basisFun (Fin n) ℝ i)) h
  simpa [hessianMatrix, bilinearIteratedFDerivTwo] using h'

private lemma hessian_symm_of_gradient_diff
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {i j : Fin n} (hu : ContDiff ℝ 1 u)
    (hx : DifferentiableAt ℝ (gradient u) x) :
    hessianMatrix u x i j = hessianMatrix u x j i := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hs :=
    second_derivative_symmetric
      (fun y => (hu.differentiable (by simp) y).hasFDerivAt)
      hfd.hasFDerivAt
      (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)
  simpa [hessianMatrix, bilinearIteratedFDerivTwo] using hs

private lemma fderiv_apply_apply_symm
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ φ y v) x w =
      fderiv ℝ (fun y => fderiv ℝ φ y w) x v := by
  have hφ2 : ContDiff ℝ (2 : WithTop ℕ∞) φ :=
    hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hfd' : ContDiff ℝ 1 (fderiv ℝ φ) :=
    hφ2.fderiv_right (by norm_num)
  have hfd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hfd'.differentiable (by simp)).differentiableAt
  have hcv :
      DifferentiableAt ℝ (fun _ : E => v) x :=
    (differentiable_const v : Differentiable ℝ (fun _ : E => v)).differentiableAt
  have hcw :
      DifferentiableAt ℝ (fun _ : E => w) x :=
    (differentiable_const w : Differentiable ℝ (fun _ : E => w)).differentiableAt
  have hv := fderiv_clm_apply hfd hcv
  have hw := fderiv_clm_apply hfd hcw
  have hv' := congrArg (fun L : E →L[ℝ] ℝ => L w) hv
  have hw' := congrArg (fun L : E →L[ℝ] ℝ => L v) hw
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] at hv' hw'
  have hs :=
    second_derivative_symmetric
      (fun y => (hφ2.differentiable (by norm_num) y).hasFDerivAt)
      hfd.hasFDerivAt w v
  calc
    fderiv ℝ (fun y => fderiv ℝ φ y v) x w =
        ((fderiv ℝ (fderiv ℝ φ) x) w) v := hv'
    _ = ((fderiv ℝ (fderiv ℝ φ) x) v) w := hs
    _ = fderiv ℝ (fun y => fderiv ℝ φ y w) x v := hw'.symm

end InnerProduct

private lemma contDiff_fderiv_apply [NormedSpace ℝ E]
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (v : E) :
    ContDiff ℝ 1 (fun x => fderiv ℝ φ x v) := by
  have hφ2 : ContDiff ℝ (2 : WithTop ℕ∞) φ :=
    hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hfd : ContDiff ℝ 1 (fderiv ℝ φ) :=
    hφ2.fderiv_right (by norm_num)
  exact hfd.clm_apply
    (contDiff_const : ContDiff ℝ 1 (fun _ : E => v))

end StructuredSpace

/-- **Symmetry of the weak third derivative**: for `u ∈ C¹` with Lipschitz gradient, if
`T · k i j` is the weak derivative of the Hessian entry `Hᵢⱼ` along `eₖ` for all indices, then a.e.
`Tₖᵢⱼ = Tᵢₖⱼ` and
`Tₖᵢⱼ = Tₖⱼᵢ`. -/
theorem ae_weak_third_derivative_symm {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hT :
      ∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
          (EuclideanSpace.basisFun (Fin n) ℝ k)) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ k i j, T x k i j = T x i k j ∧ T x k i j = T x k j i := by
  let e : Fin n → EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ
  have hcoord (i j : Fin n) :
    (fun x =>
        fderiv ℝ (fun y => fderiv ℝ u y (e j)) x
          (e i)) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => hessianMatrix u x i j) := by
    filter_upwards [hG.ae_differentiableAt] with x hx
    exact hessian_coord_of_gradient_diff hx
  have hHsym (i j : Fin n) :
    (fun x => hessianMatrix u x i j) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => hessianMatrix u x j i) := by
    filter_upwards [hG.ae_differentiableAt] with x hx
    exact hessian_symm_of_gradient_diff hu hx
  have hgi (j : Fin n) :
    LipschitzWith (‖(innerSL ℝ) (e j)‖₊ * G) (fun x => fderiv ℝ u x (e j)) := by
    simpa [Function.comp_def, inner_gradient_left] using (((innerSL ℝ) (e j)).lipschitzWith.comp hG)
  have hweak (i j : Fin n) :
    HasWeakDerivAlong (fun x => fderiv ℝ u x (e j)) (fun x => hessianMatrix u x i j) (e i) := by
    exact
      HasWeakDerivAlong.congr_right (hasWeakDerivAlong_of_lipschitz (hgi j) (e i)) (hcoord i j)
  have hfirst (k i j : Fin n) :
    (fun x => T x k i j) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => T x k j i) := by
    have h' := HasWeakDerivAlong.congr_left (hT k j i) (hHsym j i)
    exact (hT k i j).ae_eq h'
  have hcomm (k i j : Fin n) :
    (fun x => T x k i j) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => T x i k j) := by
    apply ae_eq_of_integral_contDiff_smul_eq (hT k i j).2.1 (hT i k j).2.1
    intro φ hφ hφc
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
    have hφk : ContDiff ℝ 1 (fun x => fderiv ℝ φ x (e k)) := contDiff_fderiv_apply hφ (e k)
    have hφi : ContDiff ℝ 1 (fun x => fderiv ℝ φ x (e i)) := contDiff_fderiv_apply hφ (e i)
    have hφkc : HasCompactSupport (fun x => fderiv ℝ φ x (e k)) := hφc.fderiv_apply ℝ (e k)
    have hφic : HasCompactSupport (fun x => fderiv ℝ φ x (e i)) := hφc.fderiv_apply ℝ (e i)
    have e₁ := (hweak i j).2.2 (fun x => fderiv ℝ φ x (e k)) hφk hφkc
    have e₂ := (hT k i j).2.2 φ hφ1 hφc
    have e₃ := (hweak k j).2.2 (fun x => fderiv ℝ φ x (e i)) hφi hφic
    have e₄ := (hT i k j).2.2 φ hφ1 hφc
    have hleft :
      (∫ x, T x k i j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x,
          fderiv ℝ u x (e j) *
            fderiv ℝ (fun y => fderiv ℝ φ y (e k)) x
              (e i) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      calc
        ∫ x, T x k i j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
            -(∫ x,
                hessianMatrix u x i j *
                  fderiv ℝ φ x (e k) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
          linarith [e₂]
        _ =
            ∫ x,
              fderiv ℝ u x (e j) *
                fderiv ℝ (fun y => fderiv ℝ φ y (e k)) x
                  (e i) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
          linarith [e₁]
    have hright :
      (∫ x, T x i k j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x,
          fderiv ℝ u x (e j) *
            fderiv ℝ (fun y => fderiv ℝ φ y (e i)) x
              (e k) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      calc
        ∫ x, T x i k j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
            -(∫ x,
                hessianMatrix u x k j *
                  fderiv ℝ φ x (e i) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
          linarith [e₄]
        _ =
            ∫ x,
              fderiv ℝ u x (e j) *
                fderiv ℝ (fun y => fderiv ℝ φ y (e i)) x
                  (e k) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
          linarith [e₃]
    have hsecond :
      (fun x => fderiv ℝ u x (e j) * fderiv ℝ (fun y => fderiv ℝ φ y (e k)) x (e i)) =
        (fun x => fderiv ℝ u x (e j) * fderiv ℝ (fun y => fderiv ℝ φ y (e i)) x (e k)) := by
      funext x
      rw [fderiv_apply_apply_symm hφ x (e k) (e i)]
    have hmul :
      (∫ x, T x k i j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, T x i k j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      calc
        ∫ x, T x k i j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
            ∫ x,
              fderiv ℝ u x (e j) *
                fderiv ℝ (fun y => fderiv ℝ φ y (e k)) x
                  (e i) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
          hleft
        _ =
            ∫ x,
              fderiv ℝ u x (e j) *
                fderiv ℝ (fun y => fderiv ℝ φ y (e i)) x
                  (e k) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
          rw [hsecond]
        _ = ∫ x, T x i k j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hright.symm
    simpa only [smul_eq_mul, mul_comm] using hmul
  apply ae_all_iff.2
  intro k
  apply ae_all_iff.2
  intro i
  apply ae_all_iff.2
  intro j
  filter_upwards [hcomm k i j, hfirst k i j] with x hx₁ hx₂
  exact ⟨hx₁, hx₂⟩

end FunctionalInequalities.Analysis

end WeakThirdDerivativeSymmetry

section GradientDerivativeIdentification

open FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Probability.Stein

private lemma hessianMatrix_entry_of_differentiableAt_gradient
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x) (i j : Fin n) :
    hessianMatrix u x i j =
      ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
        fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ := by
  rw [hessian_symm_of_gradient_diff hu hx,
    ← hessian_coord_of_gradient_diff hx]
  have heq :
      (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ i)) =
        fun y => ⟪gradient u y, EuclideanSpace.basisFun (Fin n) ℝ i⟫ := by
    funext y
    exact inner_gradient_left.symm
  rw [heq, fderiv_inner_apply ℝ hx
    (differentiableAt_const (EuclideanSpace.basisFun (Fin n) ℝ i))]
  simp [real_inner_comm]

/-- At a point where the gradient of a `C¹` potential is differentiable, its derivative
is represented by the coordinate Hessian. This pointwise bridge requires no `C²` hypothesis
and supports the weak regular moment-potential package for Letwin's Lemma 2.2. -/
theorem hessianMatrix_toEuclideanLin_of_differentiableAt_gradient
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x) :
    Matrix.toEuclideanLin (hessianMatrix u x) =
      (fderiv ℝ (gradient u) x).toLinearMap := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
  rw [LinearMap.toMatrix_toLin]
  ext i j
  rw [LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]
  exact hessianMatrix_entry_of_differentiableAt_gradient hu hx i j

/-- The coordinate Hessian of a `C¹` potential is symmetric at every differentiability
point of its gradient, including the zero-dimensional case. -/
theorem hessianMatrix_isHermitian_of_differentiableAt_gradient
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x) :
    (hessianMatrix u x).IsHermitian := by
  change (hessianMatrix u x).conjTranspose = hessianMatrix u x
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  exact hessian_symm_of_gradient_diff hu hx

end FunctionalInequalities.Probability.Stein

end GradientDerivativeIdentification

section HessianEntryBounds

open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Probability.Stein

/-- Measurability of the total coordinate Hessian, without smoothness premises. -/
theorem measurable_hessianMatrix_entry {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (i j : Fin n) :
    Measurable (fun x => hessianMatrix u x i j) := by
  have hentry : Continuous
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
        gradientDerivativeMatrix L i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_gradientDerivativeMatrix)
  simpa only [hessianMatrix_eq_gradientDerivativeMatrix, Function.comp_def] using
    hentry.measurable.comp (measurable_fderiv ℝ (gradient u))

/-- The total coordinate Hessian is bounded by the gradient Lipschitz constant;
this does not assert C2 regularity or classical differentiability everywhere. -/
theorem norm_hessianMatrix_entry_le_of_lipschitz_gradient {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u))
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    ‖hessianMatrix u x i j‖ ≤ (G : ℝ) := by
  let L := fderiv ℝ (gradient u) x
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let T := InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))
  rw [hessianMatrix_eq_gradientDerivativeMatrix]
  change ‖T (L (e i)) (e j)‖ ≤ (G : ℝ)
  calc
    ‖T (L (e i)) (e j)‖ ≤ ‖T (L (e i))‖ * ‖e j‖ :=
      (T (L (e i))).le_opNorm (e j)
    _ = ‖L (e i)‖ := by
      rw [T.norm_map, e.norm_eq_one j, mul_one]
    _ ≤ ‖L‖ * ‖e i‖ := L.le_opNorm (e i)
    _ = ‖L‖ := by
      rw [e.norm_eq_one i, mul_one]
    _ ≤ (G : ℝ) := norm_fderiv_le_of_lipschitz ℝ hG

end FunctionalInequalities.Probability.Stein

end HessianEntryBounds


section
open MeasureTheory Set
open scoped Topology ContDiff
namespace FunctionalInequalities.Probability.Stein

/-- Lipschitz-gradient total Hessian entries are essentially bounded on
compact sets, without a differentiability or equation premise. -/
theorem memLp_top_hessianMatrix_entry_of_isCompact {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : NNReal} (hGradLip : LipschitzWith G (gradient u)) (i j : Fin n)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp (fun x => hessianMatrix u x i j) (⊤ : ENNReal)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  exact
    MemLp.of_bound (measurable_hessianMatrix_entry u i j).aestronglyMeasurable (G : ℝ)
      (Filter.Eventually.of_forall fun x =>
        norm_hessianMatrix_entry_le_of_lipschitz_gradient hGradLip x i j)




/-- The total coordinate Hessian entry is L2 on every compact set, from the
actual Lipschitz-gradient bound. No differentiability or PDE premise is added. -/
theorem memLp_hessianMatrix_entry_of_isCompact {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (i j : Fin n)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S) :
    MemLp (fun x => hessianMatrix u x i j) 2
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let : IsFiniteMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  exact (memLp_top_hessianMatrix_entry_of_isCompact hG i j S hS).mono_exponent le_top
/-- Multiplying a total Hessian entry by a continuous compact cutoff produces
an actual global L2 function for the existing difference-quotient criterion. -/
theorem memLp_cutoff_mul_hessianMatrix_entry {n : ℕ}
    {u χ : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (i j : Fin n)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    MemLp (fun x => χ x * hessianMatrix u x i j) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hK : IsCompact (tsupport χ) := hχc
  have hKm : MeasurableSet (tsupport χ) :=
    (isClosed_tsupport χ).measurableSet
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hχ.continuousOn
  let : IsFiniteMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hlocal : MemLp (fun x => χ x * hessianMatrix u x i j) 2
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)) := by
    apply MemLp.of_bound
      (hχ.measurable.mul
        (measurable_hessianMatrix_entry u i j)).aestronglyMeasurable
      (C * (G : ℝ))
    exact (ae_restrict_mem hKm).mono fun x hx => by
      calc
        ‖χ x * hessianMatrix u x i j‖ =
            ‖χ x‖ * ‖hessianMatrix u x i j‖ := norm_mul _ _
        _ ≤ ‖χ x‖ * (G : ℝ) :=
          mul_le_mul_of_nonneg_left
            (norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x i j)
            (norm_nonneg _)
        _ ≤ C * (G : ℝ) :=
          mul_le_mul_of_nonneg_right (hC x hx) (NNReal.coe_nonneg G)
  have heq :
      (tsupport χ).indicator (fun x => χ x * hessianMatrix u x i j) =
        (fun x => χ x * hessianMatrix u x i j) := by
    funext x
    by_cases hx : x ∈ tsupport χ
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx,
        image_eq_zero_of_notMem_tsupport hx, zero_mul]
  rw [← heq]
  exact (memLp_indicator_iff_restrict hKm.nullMeasurableSet).mpr hlocal

end FunctionalInequalities.Probability.Stein

section C1GradientChain

open MeasureTheory Matrix
open scoped ContDiff Topology RealInnerProductSpace

namespace FunctionalInequalities.Probability.Stein

/--
C1 counterpart of `chain_coordinate`: for C1 `u`, `f` and a point where `∇u` is differentiable, the
coordinate derivative of
`f ∘ ∇u` is `∑ⱼ (∇²u)ᵢⱼ (∇f ∘ ∇u)ⱼ`; all finite dimensions. -/
theorem chain_coordinate_of_differentiableAt_gradient {n : ℕ}
    {u f : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u) (hf : ContDiff ℝ 1 f)
    {y : EuclideanSpace ℝ (Fin n)} (hy : DifferentiableAt ℝ (gradient u) y) (i : Fin n) :
    fderiv ℝ (f ∘ gradient u) y (EuclideanSpace.basisFun (Fin n) ℝ i) =
      ∑ j, hessianMatrix u y i j * gradient f (gradient u y) j := by
  rw [fderiv_comp y (hf.differentiable one_ne_zero _) hy]
  change
    fderiv ℝ f (gradient u y) (fderiv ℝ (gradient u) y (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      _
  rw [← inner_gradient_left, PiLp.inner_apply]
  have hlin := hessianMatrix_toEuclideanLin_of_differentiableAt_gradient hu hy
  have hsym := hessianMatrix_isHermitian_of_differentiableAt_gradient hu hy
  apply Finset.sum_congr rfl
  intro j _
  have hcoord :
    fderiv ℝ (gradient u) y (EuclideanSpace.basisFun (Fin n) ℝ i) j = hessianMatrix u y i j := by
    have heq :=
      congrArg
        (fun A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) =>
          A (EuclideanSpace.basisFun (Fin n) ℝ i))
        hlin
    change
      (hessianMatrix u y).toEuclideanLin (EuclideanSpace.basisFun (Fin n) ℝ i) =
        fderiv ℝ (gradient u) y (EuclideanSpace.basisFun (Fin n) ℝ i) at heq
    rw [← heq]
    change (hessianMatrix u y *ᵥ (EuclideanSpace.basisFun (Fin n) ℝ i).ofLp) j = _
    have hb : (EuclideanSpace.basisFun (Fin n) ℝ i).ofLp = Pi.single i (1 : ℝ) := by
      ext k
      simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply, Pi.single_apply]
    rw [hb, Matrix.mulVec_single_one]
    have hs : hessianMatrix u y j i = hessianMatrix u y i j := by
      simpa only [Matrix.IsHermitian, Matrix.conjTranspose_apply, star_trivial] using
        congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hsym
    exact hs
  rw [hcoord]
  simp only [Real.inner_apply, mul_comm]

end FunctionalInequalities.Probability.Stein

end C1GradientChain

section DirectionalCutoffData

open MeasureTheory Set Filter Matrix
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/--
**Cutoff directional Hessian data**: if `∇u` is Lipschitz and `T` is a weak Hessian tensor (`T · k i
j` the weak
derivative of `(∇²u)ᵢⱼ` along `e_k`, L² on compact sets), then for a direction `v` and a compactly
supported C1 cutoff `χ`,
`b = χ · vᵀ∇²u v` is measurable, compactly supported and bounded, with weak derivatives
`χ · Σᵢⱼ vᵢvⱼ T_{kij} + ∂_kχ · vᵀ∇²u v`, compactly supported and globally L². No C1 hypothesis on
`u`, convexity or
smoothness of `vᵀ∇²u v` is used. -/
theorem directional_cutoff_data {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT :
      ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)),
            IsCompact S →
              MemLp (fun x => T x k i j) 2
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (v : Fin n → ℝ) {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχc : HasCompactSupport χ) :
    let b := fun x => χ x * ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
    let ab := fun (k : Fin n) x =>
      χ x * (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j) +
        fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) *
          ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
    Measurable b ∧
      HasCompactSupport b ∧
        (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖b x‖ ≤ B) ∧
          ∀ k : Fin n,
            HasWeakDerivAlong b (ab k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
              HasCompactSupport (ab k) ∧
                MemLp (ab k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  intro b ab
  classical
  set e := fun k : Fin n => EuclideanSpace.basisFun (Fin n) ℝ k
  set hv := fun x => ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
  set tv := fun (k : Fin n) x => ∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j
  have hsum (k : Fin n) :=
    hasWeakDerivAlong_finsetSum_mul (Finset.univ : Finset (Fin n × Fin n))
      (fun p => v p.1 * v p.2) (f := fun p x => hessianMatrix u x p.1 p.2) (df := fun p x =>
      T x k p.1 p.2) (v := e k) (fun p _ => (hT k p.1 p.2).1) (fun p _ => (hT k p.1 p.2).2)
  have hhv :
    hv = fun x =>
      ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)), v p.1 * v p.2 * hessianMatrix u x p.1 p.2 := by
    funext x; simp only [hv, Fintype.sum_prod_type]
  have htv (k : Fin n) :
    tv k = fun x =>
      ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)), v p.1 * v p.2 * T x k p.1 p.2 := by
    funext x; simp only [tv, Fintype.sum_prod_type]
  have hHv (k : Fin n) : HasWeakDerivAlong hv (tv k) (e k) := by
    rw [hhv, htv k];
    exact (hsum k).1
  have hTv2 (k : Fin n) :
    ∀ S : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact S → MemLp (tv k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    rw [htv k]; exact (hsum k).2
  set Hb : ℝ := ∑ i : Fin n, ∑ j : Fin n, ‖v i * v j‖ * (G : ℝ)
  have hvb (x : EuclideanSpace ℝ (Fin n)) : ‖hv x‖ ≤ Hb := by
    refine
      (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
    rw [norm_mul]
    exact
      mul_le_mul_of_nonneg_left (norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x i j)
        (norm_nonneg _)
  have hvm : Measurable hv :=
    Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => (measurable_hessianMatrix_entry u i j).const_mul _
  obtain ⟨Cχ, hCχ⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  have hCχ0 : 0 ≤ Cχ := (norm_nonneg _).trans (hCχ 0)
  have hbb (x : EuclideanSpace ℝ (Fin n)) : ‖b x‖ ≤ Cχ * Hb := by
    simp only [b, norm_mul];
    exact mul_le_mul (hCχ x) (hvb x) (norm_nonneg _) hCχ0
  have hvtop :
    ∀ S : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact S →
        MemLp hv (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    fun S _ => memLp_top_of_bound hvm.aestronglyMeasurable.restrict Hb (ae_of_all _ hvb)
  have hbdata (k : Fin n) := (hHv k).compact_mul_data (hTv2 k) hvtop hχ hχc
  exact
    ⟨hχ.continuous.measurable.mul hvm, hχc.mul_right,
      ⟨Cχ * Hb, (norm_nonneg _).trans (hbb 0), hbb⟩, fun k =>
      ⟨(hbdata k).1, (hbdata k).2.2.1, (hbdata k).2.2.2⟩⟩

end FunctionalInequalities.Analysis

end DirectionalCutoffData
