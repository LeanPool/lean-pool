/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.FiniteCornerVectorCompression
public import LeanPool.VacuumBellSeparation.Bell.PositiveFunctionalCompressionApproximation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Data.Fintype.EquivFin

/-!
Every positive order-normal functional on the ORIGINAL concrete VNA is in
the full-dual norm closure of finite positive vector sums on original H.
No faithful reference, separability, vector-state field or normalization is
assumed. All finite-subset nets and the empty/zero-H case are retained.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open Filter
open scoped Topology ComplexOrder InnerProductSpace BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Normality of the actual functional, not a representation assumption,
makes complementary projection mass vanish along an arbitrary exhaustion. -/
theorem normalFunctional_projection_lost_mass_tendsto_zero
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hn : IsNormalFunctional M φ) {ι : Type*}
    [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (q : ι → M.toStarSubalgebra) (hq : ∀ i, IsStarProjection (q i))
    (hmono : Monotone q) (hsup : IsLUB (Set.range q) 1) :
    Tendsto (fun i => ‖φ (1 - q i)‖) atTop (𝓝 0) := by
  have ht := normalFunctional_tendsto_monotone_net M φ hn q hmono
    (fun i => (hq i).nonneg) 1 hsup
  have he (i : ι) : ‖φ (1 - q i)‖ = (φ 1).re - (φ (q i)).re := by
    have hr := congrArg Complex.re
      (Complex.eq_coe_norm_of_nonneg (φ.map_nonneg (hq i).one_sub.nonneg))
    rw [map_sub, Complex.sub_re, Complex.ofReal_re] at hr
    simpa only [map_sub] using hr.symm
  have hc : Tendsto (fun _ : ι => (φ 1).re) atTop (𝓝 (φ 1).re) := tendsto_const_nhds
  simpa only [he, sub_self] using hc.sub ht

/-- Full functional-norm convergence of the unnormalized compressions. -/
theorem normalFunctional_projection_compressions_tendsto
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hn : IsNormalFunctional M φ) {ι : Type*}
    [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (q : ι → M.toStarSubalgebra) (hq : ∀ i, IsStarProjection (q i))
    (hmono : Monotone q) (hsup : IsLUB (Set.range q) 1) :
    Tendsto (fun i => compressionDual φ (q i)) atTop
      (𝓝 (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap) :=
  positiveFunctional_compression_tendsto_of_lost_mass_zero φ q hq
    (normalFunctional_projection_lost_mass_tendsto_zero M φ hn q hq hmono hsup)

/-- Finite sums may always be indexed by Fin n, including n=0. -/
theorem finiteVectorFunctional_reindex (M : VonNeumannAlgebra H)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (ξ : ι → H) :
    finiteVectorFunctional M ξ = finiteVectorFunctional M (fun j => ξ (e.symm j)) := by
  apply PositiveLinearMap.ext
  intro a
  simp only [finiteVectorFunctional_apply]
  exact Fintype.sum_equiv e _ _ fun i => by rw [e.symm_apply_apply]

/-- An actual finite positive vector sum approximates every positive normal
functional uniformly on the whole unit ball of the original algebra. -/
theorem exists_finite_vectors_approx_normalFunctional
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hn : IsNormalFunctional M φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (ξ : Fin n → H),
      ‖(PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap -
        (PositiveContinuousLinearMap.ofClass (finiteVectorFunctional M ξ)).toContinuousLinearMap‖
        < ε := by
  classical
  obtain ⟨s, horth, hcorner, hsup, _⟩ := exists_orthogonal_vector_corner_cover M φ hn
  let P : s → M.toStarSubalgebra := fun i => i.1
  let q : Finset s → M.toStarSubalgebra := fun F => ∑ i ∈ F, P i
  have hp (i : s) : IsStarProjection (P i) := (hcorner i.1 i.2).1
  have ho : Pairwise (fun i j : s => P i * P j = 0) := by
    intro i j hij
    exact horth i.2 j.2 (fun he => hij (Subtype.ext he))
  have hq (F : Finset s) : IsStarProjection (q F) :=
    isStarProjection_finite_sum_vna M P hp ho F
  have hm : Monotone q := fun F G hFG =>
    Finset.sum_le_sum_of_subset_of_nonneg hFG (fun i _ _ => (hp i).nonneg)
  have ht := normalFunctional_projection_compressions_tendsto M φ hn q hq hm hsup
  have hevent := (tendsto_iff_norm_sub_tendsto_zero.mp ht).eventually (gt_mem_nhds hε)
  obtain ⟨F, hF⟩ := hevent.exists
  have hrep : ∀ i : F, ∃ ξ : H,
      ∀ a : M.toStarSubalgebra, vectorFunctional M ξ a = φ (P i.1 * a * P i.1) := by
    intro i
    obtain ⟨ξ, _, _, hξ⟩ := (hcorner i.1.1 i.1.2).2.2
    exact ⟨ξ, hξ⟩
  choose ξ hξ using hrep
  obtain ⟨ζ, hζ⟩ := exists_finite_vector_sum_compression M φ
    (fun i : F => P i.1) (fun i => hp i.1) ξ hξ
  have hsum : (∑ i : F, P i.1) = q F := Finset.sum_coe_sort F P
  rw [hsum] at hζ
  let e : F ≃ Fin (Fintype.card F) := Fintype.equivFin F
  refine ⟨Fintype.card F, fun i => ζ (e.symm i), ?_⟩
  rw [← finiteVectorFunctional_reindex M e ζ, ← hζ]
  change ‖(PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap - compressionDual φ
    (q F)‖ < ε
  rw [norm_sub_rev]
  exact hF

/-- The closure is in the actual full continuous dual norm. Its generators
are literal finite positive sums of original-H vector functionals. -/
theorem normalFunctional_mem_closure_finite_vector_sums
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hn : IsNormalFunctional M φ) :
    (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap ∈
      closure {f : StrongDual ℂ M.toStarSubalgebra |
        ∃ (n : ℕ) (ξ : Fin n → H),
          f = (PositiveContinuousLinearMap.ofClass (finiteVectorFunctional M
            ξ)).toContinuousLinearMap} := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨n, ξ, hξ⟩ := exists_finite_vectors_approx_normalFunctional M φ hn hε
  refine ⟨(PositiveContinuousLinearMap.ofClass (finiteVectorFunctional M ξ)).toContinuousLinearMap,
    ⟨n, ξ, rfl⟩, ?_⟩
  simpa only [dist_eq_norm] using hξ

end VacuumBellSeparation.Bipartite
