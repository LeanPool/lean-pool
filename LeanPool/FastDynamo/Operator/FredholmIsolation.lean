/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.RieszProjectionCalculus
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# Fredholm and finite-rank spectral bridges

This file records the part of the Fredholm/isolation argument that is
supported by Mathlib without adding a paper-specific certificate.

There are two distinct levels.

* Fredholmness is stable under a **finite-rank** perturbation.  This follows
  from Mathlib's characterization by continuous quasi-inverses modulo
  finite-rank maps.
* For a **compact** factor, the compact Fredholm alternative gives the exact
  invertible-or-eigenvalue dichotomy.  A compact idempotent, in particular a
  compact Riesz projection, has finite-dimensional range.

Mathlib 4.35.0 does not contain stability of `IsFredholm` under arbitrary
compact perturbations or the analytic Fredholm theorem
(discreteness/meromorphy and finite-rank principal parts).  Consequently this
file does **not** infer spectral isolation from compactness.  The
generic input the paper's §2.3 needs beyond this is precisely analytic Fredholm for a
holomorphic family of Fredholm maps which is invertible at one point; its ingredients are
developed in `AnalyticFredholm`, `FiniteDimensionalDeterminant` and `AnalyticFredholmContinuation`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Complex Metric Set
open scoped LinearMap.FiniteRangeSetoid

namespace FredholmIsolation

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A finite-rank perturbation of a Fredholm map is Fredholm.  This is the
strongest perturbation theorem directly supplied by Mathlib's current
quasi-inverse/Fredholm interface. -/
theorem IsFredholm.of_hasFiniteRange_sub {u v : E →L[ℂ] F}
    (hu : ContinuousLinearMap.IsFredholm u)
    (hvu : (v - u).toLinearMap.HasFiniteRange) :
    ContinuousLinearMap.IsFredholm v := by
  obtain ⟨q, hq⟩ := hu.exists_isQuasiInverse
  apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse (v := q)
  apply hq.congr (by rfl)
  exact LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mpr hvu

/-- An invertible map is Fredholm. -/
theorem IsInvertible.isFredholm {u : E →L[ℂ] F} (hu : u.IsInvertible) :
    ContinuousLinearMap.IsFredholm u := by
  apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse (v := u.inverse)
  rcases hu with ⟨e, rfl⟩
  simp only [ContinuousLinearMap.inverse_equiv]
  constructor
  · change e.symm.toLinearMap ∘ₗ e.toLinearMap ≈ LinearMap.id
    have heq : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id := by
      ext x
      simp
    rw [heq]
  · change e.toLinearMap ∘ₗ e.symm.toLinearMap ≈ LinearMap.id
    have heq : e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id := by
      ext x
      simp
    rw [heq]

/-- A finite-rank perturbation of an invertible map is Fredholm. -/
theorem IsInvertible.isFredholm_of_hasFiniteRange_sub {u v : E →L[ℂ] F}
    (hu : u.IsInvertible) (hvu : (v - u).toLinearMap.HasFiniteRange) :
    ContinuousLinearMap.IsFredholm v :=
  IsFredholm.of_hasFiniteRange_sub (IsInvertible.isFredholm hu) hvu

/-- The circle integral of a continuous compact-operator-valued function is
compact.  The proof integrates in the closed subspace of compact operators;
this is the step needed for compactness of Riesz projections. -/
theorem isCompactOperator_circleIntegral
    {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    {f : ℂ → (X →L[ℂ] X)} {c : ℂ} {R : ℝ}
    (hf : ContinuousOn f (sphere c |R|))
    (hcompact : ∀ z ∈ sphere c |R|, IsCompactOperator (f z)) :
    IsCompactOperator
      ((circleIntegral f c R : X →L[ℂ] X) : X → X) := by
  let C : Submodule ℂ (X →L[ℂ] X) :=
    compactOperator (RingHom.id ℂ) X X
  have hCclosed : IsClosed (C : Set (X →L[ℂ] X)) :=
    isClosed_setOfPred_isCompactOperator
  let : CompleteSpace C := hCclosed.completeSpace_coe
  let φ : ℝ → (X →L[ℂ] X) :=
    (fun θ ↦ deriv (circleMap c R) θ) •
      (fun θ ↦ f (circleMap c R θ))
  have hfcircle : Continuous (fun θ : ℝ ↦ f (circleMap c R θ)) := by
    exact continuousOn_univ.mp <|
      hf.comp (continuous_circleMap c R).continuousOn
        (fun θ _ ↦ circleMap_mem_sphere' c R θ)
  have hφcont : Continuous φ := by
    have hderiv : Continuous (fun θ : ℝ ↦ deriv (circleMap c R) θ) := by
      simp_rw [deriv_circleMap]
      fun_prop
    exact hderiv.smul hfcircle
  have hφcompact (θ : ℝ) : IsCompactOperator (φ θ) := by
    simpa [φ] using
      (hcompact _ (circleMap_mem_sphere' c R θ)).smul
        (deriv (circleMap c R) θ)
  let ψ : ℝ → C := fun θ ↦ ⟨φ θ, hφcompact θ⟩
  have hψcont : Continuous ψ := hφcont.subtype_mk hφcompact
  have hψint : IntervalIntegrable ψ MeasureTheory.volume 0 (2 * Real.pi) :=
    hψcont.intervalIntegrable _ _
  have hmap := ContinuousLinearMap.intervalIntegral_comp_comm
    (𝕜 := ℂ) C.subtypeL hψint
  change (∫ θ : ℝ in 0..2 * Real.pi, φ θ) ∈ C
  have heq : (∫ θ : ℝ in 0..2 * Real.pi, φ θ) =
      C.subtypeL (∫ θ : ℝ in 0..2 * Real.pi, ψ θ) := by
    calc
      (∫ θ : ℝ in 0..2 * Real.pi, φ θ) =
          ∫ θ : ℝ in 0..2 * Real.pi, C.subtypeL (ψ θ) := by
        apply intervalIntegral.integral_congr
        intro θ _hθ
        rfl
      _ = C.subtypeL (∫ θ : ℝ in 0..2 * Real.pi, ψ θ) := hmap
  rw [heq]
  exact (∫ θ : ℝ in 0..2 * Real.pi, ψ θ).property

end FredholmIsolation

namespace CompactFactor

universe u

variable {X : Type u}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The normalized compact factor associated with an invertible leading map:
`U - K = U ∘ (1 - U⁻¹K)`. -/
def normalized (U K : X →L[ℂ] X) : X →L[ℂ] X :=
  U.inverse.comp K

omit [CompleteSpace X] in
/-- The normalized compact factor acts by applying `K` and then the inverse of the leading
map `U`. -/
@[simp] theorem normalized_apply (U K : X →L[ℂ] X) (x : X) :
    normalized U K x = U.inverse (K x) :=
  rfl

omit [CompleteSpace X] in
/-- Compactness survives normalization by the inverse of the leading map. -/
theorem isCompact_normalized {U K : X →L[ℂ] X}
    (hK : IsCompactOperator K) :
    IsCompactOperator (normalized U K) :=
  hK.clm_comp U.inverse

omit [CompleteSpace X] in
/-- Exact factorization of an invertible map minus a perturbation. -/
theorem factor_sub {U K : X →L[ℂ] X} (hU : U.IsInvertible) :
    U.comp (ContinuousLinearMap.id ℂ X - normalized U K) = U - K := by
  ext x
  simp [normalized, hU.self_apply_inverse]

/-- For an invertible leading map and a compact perturbation, failure of
invertibility is exactly the occurrence of eigenvalue `1` in the normalized
compact factor.  This is the compact Fredholm alternative in the form needed
for pencil factorizations. -/
theorem hasEigenvalue_one_or_isInvertible_sub {U K : X →L[ℂ] X}
    (hU : U.IsInvertible) (hK : IsCompactOperator K) :
    Module.End.HasEigenvalue
        ((normalized U K : X →L[ℂ] X) : Module.End ℂ X) 1 ∨
      (U - K).IsInvertible := by
  have hcompact : IsCompactOperator (normalized U K) := isCompact_normalized hK
  rcases hcompact.hasEigenvalue_or_mem_resolventSet (one_ne_zero : (1 : ℂ) ≠ 0) with
    heig | hres
  · exact Or.inl heig
  · right
    rw [spectrum.mem_resolventSet_iff, ← IsUnit.neg_iff,
      ContinuousLinearMap.isUnit_iff_bijective] at hres
    have hnormalized :
        (ContinuousLinearMap.id ℂ X - normalized U K).IsInvertible := by
      have hbij : Function.Bijective
          (ContinuousLinearMap.id ℂ X - normalized U K) := by
        have hneg := (Equiv.neg X).bijective.comp hres
        convert hneg using 1
        ext x
        simp
      let e := ContinuousLinearEquiv.ofBijective
        (ContinuousLinearMap.id ℂ X - normalized U K)
        (LinearMap.ker_eq_bot.mpr hbij.injective)
        (LinearMap.range_eq_top.mpr hbij.surjective)
      exact ⟨e, ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
    rw [← factor_sub hU]
    exact hU.comp hnormalized

/-- If the normalized compact factor has no eigenvalue `1`, the perturbed map
is invertible. -/
theorem isInvertible_sub_of_not_hasEigenvalue_one {U K : X →L[ℂ] X}
    (hU : U.IsInvertible) (hK : IsCompactOperator K)
    (hne : ¬ Module.End.HasEigenvalue
      ((normalized U K : X →L[ℂ] X) : Module.End ℂ X) 1) :
    (U - K).IsInvertible :=
  (hasEigenvalue_one_or_isInvertible_sub hU hK).resolve_left hne

end CompactFactor

namespace FredholmIsolation

universe u

variable {X : Type u}
  [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- A compact idempotent has finite-dimensional algebraic range. -/
theorem finiteDimensional_range_of_isCompact_of_isIdempotent
    {P : X →L[ℂ] X} (hPcompact : IsCompactOperator P)
    (hPidempotent : IsIdempotentElem P) :
    FiniteDimensional ℂ P.toLinearMap.range := by
  have hPlinear : IsIdempotentElem P.toLinearMap :=
    _root_.ContinuousLinearMap.IsIdempotentElem.toLinearMap hPidempotent
  have hPrangeClosed : IsClosed (P.toLinearMap.range : Set X) :=
    _root_.ContinuousLinearMap.IsIdempotentElem.isClosed_range hPidempotent
  let pRange : P.toLinearMap.range →ₗ[ℂ] P.toLinearMap.range :=
    P.toLinearMap.restrict (fun x _hx ↦ P.toLinearMap.mem_range_self x)
  have hpRangeCompact : IsCompactOperator pRange :=
    hPcompact.restrict
      (fun x _hx ↦ P.toLinearMap.mem_range_self x)
      hPrangeClosed
  have hpRangeId : pRange = LinearMap.id := by
    ext x
    exact (LinearMap.IsIdempotentElem.mem_range_iff
      hPlinear).mp x.property
  rw [hpRangeId] at hpRangeCompact
  exact FiniteDimensional.of_isCompactOperator_id hpRangeCompact

end FredholmIsolation

namespace HasResolventOn

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  {A : DomainOperator X D} {c : ℂ} {R : ℝ}

/-- If a reference resolvent has vanishing contour integral and its pointwise
difference from the state resolvent is compact, then the Riesz projection is
compact.  This is the useful contour-level consequence of a compact
resolvent difference; isolation of the contour remains a separate analytic
Fredholm input. -/
theorem isCompactOperator_rieszProjection_of_compact_difference
    (h : HasResolventOn A (sphere c R)) (hR : 0 ≤ R)
    (F : ℂ → (X →L[ℂ] X))
    (hFcont : ContinuousOn F (sphere c R))
    (hcompact : ∀ z ∈ sphere c R,
      IsCompactOperator (h.stateResolvent z - F z))
    (hFint : circleIntegral F c R = 0) :
    IsCompactOperator h.rieszProjection := by
  have hstateInt : CircleIntegrable h.stateResolvent c R :=
    h.circleIntegrable_stateResolvent hR
  have hFcircleInt : CircleIntegrable F c R :=
    hFcont.circleIntegrable hR
  have hdiffCont : ContinuousOn
      (fun z ↦ h.stateResolvent z - F z) (sphere c |R|) := by
    rw [abs_of_nonneg hR]
    change ContinuousOn (h.stateResolvent - F) (sphere c R)
    exact h.continuousOn_stateResolvent.sub hFcont
  have hdiffCompact : IsCompactOperator
      ((circleIntegral (fun z ↦ h.stateResolvent z - F z) c R :
        X →L[ℂ] X) : X → X) := by
    apply FredholmIsolation.isCompactOperator_circleIntegral hdiffCont
    intro z hz
    apply hcompact z
    simpa [abs_of_nonneg hR] using hz
  have hintegral :
      circleIntegral (fun z ↦ h.stateResolvent z - F z) c R =
        circleIntegral h.stateResolvent c R := by
    rw [circleIntegral.integral_sub hstateInt hFcircleInt, hFint, sub_zero]
  unfold rieszProjection
  rw [← hintegral]
  exact hdiffCompact.smul (2 * Real.pi * I : ℂ)⁻¹

omit [CompleteSpace X] in
/-- A compact idempotent Riesz projection has finite-dimensional range.  This
is the exact finite-rank bridge needed after compactness of the contour
projection has been established. -/
theorem finiteDimensional_rieszProjection_range_of_isCompact
    (h : HasResolventOn A (sphere c R))
    (hcompact : IsCompactOperator h.rieszProjection)
    (hidempotent : IsIdempotentElem h.rieszProjection) :
    FiniteDimensional ℂ h.rieszProjection.toLinearMap.range :=
  FredholmIsolation.finiteDimensional_range_of_isCompact_of_isIdempotent
    hcompact hidempotent

/-- A Riesz projection has finite-dimensional range once it is obtained from
a compact resolvent difference with a reference family whose contour integral
vanishes, provided the projection is idempotent. -/
theorem finiteDimensional_rieszProjection_range_of_compact_difference
    (h : HasResolventOn A (sphere c R)) (hR : 0 ≤ R)
    (F : ℂ → (X →L[ℂ] X))
    (hFcont : ContinuousOn F (sphere c R))
    (hcompact : ∀ z ∈ sphere c R,
      IsCompactOperator (h.stateResolvent z - F z))
    (hFint : circleIntegral F c R = 0)
    (hidempotent : IsIdempotentElem h.rieszProjection) :
    FiniteDimensional ℂ h.rieszProjection.toLinearMap.range :=
  h.finiteDimensional_rieszProjection_range_of_isCompact
    (h.isCompactOperator_rieszProjection_of_compact_difference
      hR F hFcont hcompact hFint)
    hidempotent

end HasResolventOn

end

end FastDynamo
