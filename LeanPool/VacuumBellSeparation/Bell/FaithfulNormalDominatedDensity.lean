/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.FaithfulNormalGNSTransport
public import LeanPool.VacuumBellSeparation.Bell.SeparatingVectorDominatedDensity

/-!
# Full-dual density relative to any faithful normal positive reference

The faithful normal GNS image is an actual VNA. Its actual GNS vector is
separating; all normal positive functionals transport there and back by the
genuine star-algebra equivalence. This closes the reference-domination density
route without assuming a single-vector representation in the original H,
without a support-equality premise, and without normalization by reference mass.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- Carry out the norm-dual argument on an abstract Hilbert representation;
-- only its proved transport data are specialized to the concrete GNS space.
private theorem dominatedApprox_of_transport
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
    (φ ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (Ω : K)
    (hnφ : IsNormalFunctional M φ) (hnψ : IsNormalFunctional M ψ)
    (hsep : IsSeparatingForAlgebra N Ω)
    (href : ∀ b, positiveFunctionalPushforward M N e φ b = vectorFunctional N Ω b)
    (hnormal : ∀ χ : M.toStarSubalgebra →ₚ[ℂ] ℂ,
      IsNormalFunctional N (positiveFunctionalPushforward M N e χ) ↔ IsNormalFunctional M χ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (θ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (C : ℝ),
      0 ≤ C ∧ (∀ X : M.toStarSubalgebra, 0 ≤ X → θ X ≤ C • φ X) ∧
      IsNormalFunctional M θ ∧
      ‖(PositiveContinuousLinearMap.ofClass ψ).toContinuousLinearMap -
        (PositiveContinuousLinearMap.ofClass θ).toContinuousLinearMap‖ < ε := by
  let ψN := positiveFunctionalPushforward M N e ψ
  have hnψN : IsNormalFunctional N ψN := (hnormal ψ).mpr hnψ
  have hcl := normalFunctional_mem_closure_dominated_of_separating N
    Ω hsep ψN hnψN
  change (PositiveContinuousLinearMap.ofClass ψN).toContinuousLinearMap ∈
    closure (dominatedPositiveDualMonoid N (vectorPositiveLinearMap N Ω) :
      Set (StrongDual ℂ N.toStarSubalgebra)) at hcl
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hcl ε hε
  obtain ⟨hgpos, C, hC, hdom⟩ := hg
  let η : N.toStarSubalgebra →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ g.toLinearMap hgpos
  let θ := positiveFunctionalPushforward N M e.symm η
  have hθdom : ∀ X : M.toStarSubalgebra, 0 ≤ X → θ X ≤ C • φ X := by
    intro X hX
    have hepos : 0 ≤ e X := by
      simpa only [map_zero] using (vnaStarEquiv_le_iff M N e).mpr hX
    have h := hdom (e X) hepos
    have hr : vectorPositiveLinearMap N Ω (e X) = φ X := by
      change vectorFunctional N Ω (e X) = φ X
      rw [← href (e X), positiveFunctionalPushforward_apply, StarAlgEquiv.symm_apply_apply]
    change g (e X) ≤ C • φ X
    rwa [hr] at h
  refine ⟨θ, C, hC, hθdom, isNormalFunctional_of_positive_domination M φ θ hnφ C hC hθdom, ?_⟩
  have hnorm := positiveFunctionalPushforward_difference_norm N M e.symm ψN η
  have hback : positiveFunctionalPushforward N M e.symm ψN = ψ :=
    positiveFunctionalPushforward_symm M N e ψ
  change ‖(PositiveContinuousLinearMap.ofClass ψ).toContinuousLinearMap -
    (PositiveContinuousLinearMap.ofClass θ).toContinuousLinearMap‖ < ε
  rw [hback] at hnorm
  rw [hnorm]
  exact (show ‖(PositiveContinuousLinearMap.ofClass ψN).toContinuousLinearMap - g‖ < ε by
    simpa only [dist_eq_norm] using hdist)

/-- Genuine full-dual norm approximation. Both the reference and the target
may have arbitrary positive mass, including the zero-space boundary. -/
theorem exists_normal_dominated_approx_of_faithful_normal
    (M : VonNeumannAlgebra H) (φ ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hnφ : IsNormalFunctional M φ)
    (hf : ∀ a : M.toStarSubalgebra, φ (star a * a) = 0 → a = 0)
    (hnψ : IsNormalFunctional M ψ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (θ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (C : ℝ),
      0 ≤ C ∧ (∀ X : M.toStarSubalgebra, 0 ≤ X → θ X ≤ C • φ X) ∧
      IsNormalFunctional M θ ∧
      ‖(PositiveContinuousLinearMap.ofClass ψ).toContinuousLinearMap -
        (PositiveContinuousLinearMap.ofClass θ).toContinuousLinearMap‖ < ε := by
  obtain ⟨N, e, _, _, hsep, href, hnormal⟩ :=
    exists_faithful_normal_gns_transport M φ hnφ hf
  exact dominatedApprox_of_transport M N e φ ψ (gnsUnitVector φ)
    hnφ hnψ hsep href hnormal hε

theorem normalFunctional_mem_closure_dominated_of_faithful_normal
    (M : VonNeumannAlgebra H) (φ ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hnφ : IsNormalFunctional M φ)
    (hf : ∀ a : M.toStarSubalgebra, φ (star a * a) = 0 → a = 0)
    (hnψ : IsNormalFunctional M ψ) :
    (PositiveContinuousLinearMap.ofClass ψ).toContinuousLinearMap ∈
      (dominatedPositiveDualMonoid M φ).topologicalClosure := by
  change (PositiveContinuousLinearMap.ofClass ψ).toContinuousLinearMap ∈
    closure (dominatedPositiveDualMonoid M φ : Set (StrongDual ℂ M.toStarSubalgebra))
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨θ, C, hC, hdom, _, hdist⟩ :=
    exists_normal_dominated_approx_of_faithful_normal M φ ψ hnφ hf hnψ hε
  refine ⟨(PositiveContinuousLinearMap.ofClass θ).toContinuousLinearMap,
    ⟨fun X hX => θ.map_nonneg hX, C, hC, hdom⟩, ?_⟩
  simpa only [dist_eq_norm] using hdist

/-- Exact equality of literal subsets of the original full continuous dual.
The reverse inclusion uses previously proved positive-normal cone closedness. -/
theorem closure_dominated_eq_positive_normal_of_faithful_normal
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hnφ : IsNormalFunctional M φ)
    (hf : ∀ a : M.toStarSubalgebra, φ (star a * a) = 0 → a = 0) :
    ((dominatedPositiveDualMonoid M φ).topologicalClosure :
      Set (StrongDual ℂ M.toStarSubalgebra)) =
      {f : StrongDual ℂ M.toStarSubalgebra |
        (∀ X : M.toStarSubalgebra, 0 ≤ X → 0 ≤ f X) ∧ IsNormalFunctional M f} := by
  apply Set.ext
  intro f
  constructor
  · exact fun h => closure_dominated_positive_subset_normal M φ hnφ h
  · rintro ⟨hfpos, hfn⟩
    let ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ f.toLinearMap hfpos
    exact normalFunctional_mem_closure_dominated_of_faithful_normal M φ ψ hnφ hf hfn

end VacuumBellSeparation.Bipartite
