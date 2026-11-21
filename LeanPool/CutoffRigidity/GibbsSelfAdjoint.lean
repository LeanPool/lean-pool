/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsSobolev

/-!
# The self-adjoint operator of the actual closed Gibbs energy

The bounded variational resolvent is constructed in `GibbsSobolev`. Its
inverse graph supplies a genuine densely defined nonnegative self-adjoint
operator. This does not assert essential self-adjointness of the initial
compact-test operator, spectral compactness, or spectral-gap attainment.
-/

public section

namespace CutoffRigidity

open MeasureTheory
open scoped LinearPMap

section Resolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual graph of the operator `R⁻¹-I`. -/
@[expose] noncomputable def positiveResolventGraph (R : H →L[ℝ] H) : Submodule ℝ (H × H) :=
  (R.toLinearMap.prod (LinearMap.id - R.toLinearMap)).range

omit [CompleteSpace H] in
theorem mem_positiveResolventGraph (R : H →L[ℝ] H) (x y : H) :
    (x, y) ∈ positiveResolventGraph R ↔ ∃ f : H, R f = x ∧ f - R f = y := by
  change (∃ f, (R f, f - R f) = (x, y)) ↔ _
  simp only [Prod.mk.injEq]

omit [CompleteSpace H] in
theorem positiveResolventGraph_singleValued (R : H →L[ℝ] H) (hR : Function.Injective R) :
    ∀ x : H × H, x ∈ positiveResolventGraph R → x.1 = 0 → x.2 = 0 := by
  rintro ⟨x, y⟩ hxy hx
  obtain ⟨f, hf, hfy⟩ := (mem_positiveResolventGraph R x y).mp hxy
  have hf0 : f = 0 := hR (by simpa only [map_zero] using hf.trans hx)
  simpa only [hf0, map_zero, sub_zero] using hfy.symm

/-- Genuine unbounded operator recovered from its injective resolvent. -/
@[expose] noncomputable def positiveResolventOperator (R : H →L[ℝ] H) : H →ₗ.[ℝ] H :=
  (positiveResolventGraph R).toLinearPMap

omit [CompleteSpace H] in
theorem positiveResolventOperator_graph (R : H →L[ℝ] H) (hR : Function.Injective R) :
    (positiveResolventOperator R).graph = positiveResolventGraph R :=
  Submodule.toLinearPMap_graph_eq _ (positiveResolventGraph_singleValued R hR)

omit [CompleteSpace H] in
theorem positiveResolventOperator_mem_domain (R : H →L[ℝ] H) (hR : Function.Injective R)
    (x : H) : x ∈ (positiveResolventOperator R).domain ↔ ∃ f, R f = x := by
  rw [LinearPMap.mem_domain_iff, positiveResolventOperator_graph R hR]
  constructor
  · rintro ⟨y, hxy⟩
    obtain ⟨f, hf, _⟩ := (mem_positiveResolventGraph R x y).mp hxy
    exact ⟨f, hf⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f - R f, (mem_positiveResolventGraph R _ _).mpr ⟨f, rfl, rfl⟩⟩

omit [CompleteSpace H] in
theorem positiveResolventOperator_apply (R : H →L[ℝ] H) (hR : Function.Injective R)
    (f : H) (hx : R f ∈ (positiveResolventOperator R).domain) :
    positiveResolventOperator R ⟨R f, hx⟩ = f - R f := by
  apply ((positiveResolventOperator R).image_iff hx).mpr ?_ |>.symm
  rw [positiveResolventOperator_graph R hR]
  exact (mem_positiveResolventGraph R _ _).mpr ⟨f, rfl, rfl⟩

/-- Symmetry of an injective resolvent forces its range to be dense. -/
theorem denseRange_of_injective_symmetric (R : H →L[ℝ] H) (hR : Function.Injective R)
    (hsym : ∀ x y, inner ℝ (R x) y = inner ℝ x (R y)) : DenseRange R := by
  change Dense (R.range : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hzero : R x = 0 := by
    apply ext_inner_right ℝ
    intro y
    rw [hsym]
    have hxy := ((R.range.mem_orthogonal x).mp hx) (R y) ⟨y, rfl⟩
    simpa only [inner_zero_left, real_inner_comm] using hxy
  exact hR (by simpa only [map_zero] using hzero)

/-- The constructed operator has actual dense domain. -/
theorem positiveResolventOperator_dense_domain (R : H →L[ℝ] H) (hR : Function.Injective R)
    (hsym : ∀ x y, inner ℝ (R x) y = inner ℝ x (R y)) :
    Dense ((positiveResolventOperator R).domain : Set H) := by
  apply (denseRange_of_injective_symmetric R hR hsym).mono
  rintro x ⟨f, rfl⟩
  exact (positiveResolventOperator_mem_domain R hR _).mpr ⟨f, rfl⟩

omit [CompleteSpace H] in
/-- The inverse-resolvent operator is symmetric on its actual domain. -/
theorem positiveResolventOperator_formalAdjoint (R : H →L[ℝ] H) (hR : Function.Injective R)
    (hsym : ∀ x y, inner ℝ (R x) y = inner ℝ x (R y)) :
    (positiveResolventOperator R).IsFormalAdjoint (positiveResolventOperator R) := by
  intro x y
  obtain ⟨f, hf⟩ := (positiveResolventOperator_mem_domain R hR x).mp x.property
  obtain ⟨g, hg⟩ := (positiveResolventOperator_mem_domain R hR y).mp y.property
  have hAx : positiveResolventOperator R x = f - R f := by
    have hx := positiveResolventOperator_apply R hR f (hf ▸ x.property)
    simpa only [hf] using hx
  have hAy : positiveResolventOperator R y = g - R g := by
    have hy := positiveResolventOperator_apply R hR g (hg ▸ y.property)
    simpa only [hg] using hy
  rw [hAx, hAy, ← hf, ← hg, inner_sub_left, inner_sub_right, hsym]
  rw [hsym f g]

/-- Surjectivity of `I+A` makes the symmetric inverse-resolvent operator
self-adjoint, proved directly from the defining Hilbert-adjoint pairing. -/
theorem positiveResolventOperator_selfAdjoint (R : H →L[ℝ] H) (hR : Function.Injective R)
    (hsym : ∀ x y, inner ℝ (R x) y = inner ℝ x (R y)) :
    IsSelfAdjoint (positiveResolventOperator R) := by
  let A := positiveResolventOperator R
  have hd := positiveResolventOperator_dense_domain R hR hsym
  have hle : A ≤ A.adjoint :=
    (positiveResolventOperator_formalAdjoint R hR hsym).le_adjoint hd
  apply le_antisymm ?_ hle
  constructor
  · intro y hy
    let w := A.adjoint ⟨y, hy⟩
    have hrep : R (w + y) = y := by
      apply ext_inner_right ℝ
      intro f
      have hx := (positiveResolventOperator_mem_domain R hR (R f)).mpr ⟨f, rfl⟩
      have hp := LinearPMap.adjoint_isFormalAdjoint hd ⟨y, hy⟩ ⟨R f, hx⟩
      change inner ℝ w (R f) = inner ℝ y (positiveResolventOperator R ⟨R f, hx⟩) at hp
      rw [positiveResolventOperator_apply R hR f hx] at hp
      rw [hsym, inner_add_left, inner_sub_right] at *
      linarith
    exact (positiveResolventOperator_mem_domain R hR y).mpr ⟨w + y, hrep⟩
  · intro x y hxy
    exact ((LinearPMap.adjoint_apply_eq hd x (x₀ := A y)) (fun v => by
      have hp := positiveResolventOperator_formalAdjoint R hR hsym y v
      simpa only [hxy] using hp))

end Resolvent

section Gibbs

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual variational Gibbs resolvent is injective. -/
theorem gibbsL2Resolvent_injective {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    Function.Injective (gibbsL2Resolvent hV hprob) := by
  let J := gibbsSobolevInclusion hV hprob
  have hDense := gibbsSobolevInclusion_denseRange hV hprob
  have hAd : Function.Injective J.adjoint := by
    intro f g had
    apply hDense.eq_of_inner_left ℝ
    intro u
    calc
      inner ℝ f (J u) = inner ℝ (J.adjoint f) u :=
        (ContinuousLinearMap.adjoint_inner_left J u f).symm
      _ = inner ℝ (J.adjoint g) u := congrArg (fun z => inner ℝ z u) had
      _ = inner ℝ g (J u) := ContinuousLinearMap.adjoint_inner_left J u g
  exact J.self_comp_adjoint_injective_iff.mpr hAd

/-- The variational resolvent has dense range in actual Gibbs L². -/
theorem gibbsL2Resolvent_denseRange {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    DenseRange (gibbsL2Resolvent hV hprob) :=
  denseRange_of_injective_symmetric _ (gibbsL2Resolvent_injective hV hprob)
    (gibbsL2Resolvent_symmetric hV hprob)

/-- The nonnegative self-adjoint L² operator of the genuine closed Gibbs
Dirichlet form. The diffusion generator has the opposite sign. -/
@[expose] noncomputable def gibbsPositiveGenerator {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    (E →₂[gibbsMeasure volume V] ℝ) →ₗ.[ℝ] (E →₂[gibbsMeasure volume V] ℝ) :=
  positiveResolventOperator (gibbsL2Resolvent hV hprob)

/-- Self-adjointness is derived from the actual variational construction. -/
theorem gibbsPositiveGenerator_selfAdjoint {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    IsSelfAdjoint (gibbsPositiveGenerator hV hprob) :=
  positiveResolventOperator_selfAdjoint _ (gibbsL2Resolvent_injective hV hprob)
    (gibbsL2Resolvent_symmetric hV hprob)

theorem gibbsPositiveGenerator_dense_domain {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    Dense ((gibbsPositiveGenerator hV hprob).domain : Set (E →₂[gibbsMeasure volume V] ℝ)) :=
  (gibbsPositiveGenerator_selfAdjoint hV hprob).dense_domain

theorem gibbsPositiveGenerator_isClosed {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    (gibbsPositiveGenerator hV hprob).IsClosed :=
  (gibbsPositiveGenerator_selfAdjoint hV hprob).isClosed

/-- The form operator is nonnegative; this follows from the proved energy
equation, rather than an assumption about its spectrum. -/
theorem gibbsPositiveGenerator_nonneg {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : (gibbsPositiveGenerator hV hprob).domain) :
    0 ≤ inner ℝ (gibbsPositiveGenerator hV hprob u) (u : E →₂[gibbsMeasure volume V] ℝ) := by
  let R := gibbsL2Resolvent hV hprob
  obtain ⟨f, hf⟩ := (positiveResolventOperator_mem_domain R
    (gibbsL2Resolvent_injective hV hprob) u).mp u.property
  have hA : gibbsPositiveGenerator hV hprob u = f - R f := by
    change positiveResolventOperator R u = f - R f
    calc
      positiveResolventOperator R u = positiveResolventOperator R ⟨R f, hf ▸ u.property⟩ :=
        congrArg (positiveResolventOperator R) (Subtype.ext hf.symm)
      _ = f - R f := positiveResolventOperator_apply R
        (gibbsL2Resolvent_injective hV hprob) f (hf ▸ u.property)
  rw [hA, ← hf, inner_sub_left]
  have henergy := gibbsWeakResolvent_equation hV hprob f (gibbsWeakResolvent hV hprob f)
  have hn := gibbsDirichletEnergy_nonneg hV hprob (gibbsWeakResolvent hV hprob f)
  change inner ℝ (R f) (R f) + _ = inner ℝ f (R f) at henergy
  linarith

end Gibbs

end CutoffRigidity
