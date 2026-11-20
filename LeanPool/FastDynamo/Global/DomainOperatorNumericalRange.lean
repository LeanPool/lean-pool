/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.FrequencyRatioDichotomy
public import LeanPool.FastDynamo.Operator.Domain
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The numerical range of a domain operator and the pencil lower bound

For a bundled-domain operator `A` on a Hilbert space, this module defines the numerical range
`DomainOperator.numericalRange A` (values `⟪ι d, A d⟫` on domain vectors with unit ambient norm)
and records the numerical-range criterion as far as the `DomainOperator` API supports it:

* a lower bound `d₀` for the distance from `z` to the numerical range bounds the pencil
  below, `d₀ ‖ι d‖ ≤ ‖(z - A) d‖` (`ambient_norm_pencil_lower_of_numericalRange`);
* a positive lower bound forces injectivity (`pencil_injective_of_ambient_lower`);
* if, in addition, the pencil range is closed and dense, a singleton resolvent exists with the
  matching state-norm bound (`exists_singleton_resolvent_with_stateNorm_le`).  Closedness and
  density are explicit hypotheses; this module does not supply them.

`Global/ReducedInductionHalfPlaneResolvent.lean` applies these to the reduced induction operator.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Complex Set

/-! ## Numerical ranges and domain pencils -/

namespace DomainOperator

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

/-- Numerical range of a bundled-domain operator, evaluated on domain
vectors whose ambient state has unit norm.  The order of the inner-product
arguments is chosen so the second argument is complex-linear, matching the
pencil identity `inner x ((z - A)x) = z - inner x (Ax)`. -/
def numericalRange (A : DomainOperator X D) : Set ℂ :=
  {nu | ∃ d : D, ‖A.embedding d‖ = 1 ∧
    nu = inner ℂ (A.embedding d) (A.op d)}

/-- Every unit-norm domain vector contributes the value `⟪A d, A.op d⟫` to the numerical range. -/
theorem mem_numericalRange (A : DomainOperator X D) (d : D)
    (hd : ‖A.embedding d‖ = 1) :
    inner ℂ (A.embedding d) (A.op d) ∈ A.numericalRange :=
  ⟨d, hd, rfl⟩

/-- Distance from `z` to the numerical range bounds the pencil below in the
ambient norm.  This is the normalized-vector argument in the
numerical-range criterion; it does not assert surjectivity. -/
theorem ambient_norm_pencil_lower_of_numericalRange
    (A : DomainOperator X D) {z : ℂ} {d0 : ℝ}
    (hdist : ∀ nu ∈ A.numericalRange, d0 ≤ dist z nu) (u : D) :
    d0 * ‖A.embedding u‖ ≤ ‖A.pencil z u‖ := by
  by_cases hu : u = 0
  · simp [hu]
  · have hx : A.embedding u ≠ 0 := by
      intro hx0
      apply hu
      apply A.embedding_injective
      simpa using hx0
    have hxnorm : 0 < ‖A.embedding u‖ := norm_pos_iff.mpr hx
    let c : ℂ := ((‖A.embedding u‖ : ℝ) : ℂ)⁻¹
    let v : D := c • u
    have hvnorm : ‖A.embedding v‖ = 1 := by
      simp only [v, map_smul, norm_smul, c, norm_inv,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxnorm]
      exact inv_mul_cancel₀ (ne_of_gt hxnorm)
    let nu : ℂ := inner ℂ (A.embedding v) (A.op v)
    have hnu : nu ∈ A.numericalRange :=
      A.mem_numericalRange v hvnorm
    have hinner : inner ℂ (A.embedding v) (A.pencil z v) = z - nu := by
      simp only [DomainOperator.pencil, sub_apply, smul_apply,
        inner_sub_right, inner_smul_right, nu]
      rw [inner_self_eq_norm_sq_to_K, hvnorm]
      norm_num
    have hdistP : d0 ≤ ‖A.pencil z v‖ := by
      calc
        d0 ≤ dist z nu := hdist nu hnu
        _ = ‖z - nu‖ := by rw [dist_eq_norm]
        _ = ‖inner ℂ (A.embedding v) (A.pencil z v)‖ := by rw [hinner]
        _ ≤ ‖A.embedding v‖ * ‖A.pencil z v‖ :=
          norm_inner_le_norm _ _
        _ = ‖A.pencil z v‖ := by rw [hvnorm, one_mul]
    have hpencilScale :
        ‖A.pencil z v‖ = ‖A.pencil z u‖ / ‖A.embedding u‖ := by
      simp only [v, map_smul, norm_smul, c, norm_inv,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxnorm]
      rw [inv_mul_eq_div]
    rw [hpencilScale] at hdistP
    exact (le_div_iff₀ hxnorm).mp hdistP

/-- A positive ambient lower pencil bound forces injectivity, using the
injectivity of the bundled domain embedding. -/
theorem pencil_injective_of_ambient_lower
    (A : DomainOperator X D) {z : ℂ} {d0 : ℝ} (hd0 : 0 < d0)
    (hlower : ∀ u : D,
      d0 * ‖A.embedding u‖ ≤ ‖A.pencil z u‖) :
    Function.Injective (A.pencil z) := by
  intro u v huv
  have hpencil : A.pencil z (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have hlower' := hlower (u - v)
  rw [hpencil, norm_zero] at hlower'
  have hembNorm : ‖A.embedding (u - v)‖ = 0 := by
    have hnonneg := norm_nonneg (A.embedding (u - v))
    nlinarith
  have hemb : A.embedding (u - v) = 0 := norm_eq_zero.mp hembNorm
  have huv0 : u - v = 0 := by
    apply A.embedding_injective
    simpa using hemb
  exact sub_eq_zero.mp huv0

section Resolvent

variable [CompleteSpace X] [CompleteSpace D]

/-- Construct a singleton resolvent from the quantitative numerical-range
lower bound once the pencil range is known to be both closed and dense.

The resulting estimate is for the ambient state resolvent
`embedding ∘ (z - A)⁻¹`, whose norm is the `L² → L²` resolvent norm used in the paper. -/
theorem exists_singleton_resolvent_with_stateNorm_le
    (A : DomainOperator X D) {z : ℂ} {d0 : ℝ} (hd0 : 0 < d0)
    (hlower : ∀ u : D,
      d0 * ‖A.embedding u‖ ≤ ‖A.pencil z u‖)
    (hclosed : IsClosed (Set.range (A.pencil z)))
    (hdense : DenseRange (A.pencil z)) :
    ∃ h : HasResolventOn A {z},
      ‖h.stateResolvent z‖ ≤ d0⁻¹ := by
  let P : D →L[ℂ] X := A.pencil z
  have hPinj : Function.Injective P :=
    A.pencil_injective_of_ambient_lower hd0 hlower
  have hPsurj : Function.Surjective P := by
    have hclosure : closure (Set.range P) = Set.univ :=
      dense_iff_closure_eq.mp hdense
    rw [hclosed.closure_eq] at hclosure
    exact Set.range_eq_univ.mp hclosure
  have hker : P.ker = ⊥ := LinearMap.ker_eq_bot.mpr hPinj
  have hrange : P.range = ⊤ := LinearMap.range_eq_top.mpr hPsurj
  let e : D ≃L[ℂ] X := ContinuousLinearEquiv.ofBijective P hker hrange
  let R : X →L[ℂ] D := e.symm.toContinuousLinearMap
  have hleft : R.comp P = ContinuousLinearMap.id ℂ D := by
    apply ContinuousLinearMap.ext
    intro u
    exact e.symm_apply_apply u
  have hright : P.comp R = ContinuousLinearMap.id ℂ X := by
    apply ContinuousLinearMap.ext
    intro x
    exact e.apply_symm_apply x
  let h : HasResolventOn A {z} :=
    { inv := fun _ ↦ R
      left_inv := by
        intro w hw
        have hwz : w = z := Set.mem_singleton_iff.mp hw
        subst w
        exact hleft
      right_inv := by
        intro w hw
        have hwz : w = z := Set.mem_singleton_iff.mp hw
        subst w
        exact hright
      continuousOn := continuous_const.continuousOn }
  refine ⟨h, ?_⟩
  change ‖A.embedding.comp R‖ ≤ d0⁻¹
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hd0.le)
  intro x
  have hlowerR := hlower (R x)
  have hrightx := congrArg (fun Q : X →L[ℂ] X ↦ Q x) hright
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hrightx
  change d0 * ‖A.embedding (R x)‖ ≤ ‖P (R x)‖ at hlowerR
  rw [hrightx] at hlowerR
  calc
    ‖A.embedding (R x)‖ ≤ ‖x‖ / d0 :=
      (le_div_iff₀ hd0).2 (by simpa [mul_comm] using hlowerR)
    _ = d0⁻¹ * ‖x‖ := by rw [inv_mul_eq_div]

end Resolvent

end DomainOperator

end

end FastDynamo
