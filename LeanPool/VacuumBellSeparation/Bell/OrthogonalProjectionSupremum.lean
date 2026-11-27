/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.OrthogonalProjectionStrongZero
public import LeanPool.VacuumBellSeparation.Bell.VectorFunctionalNormal
public import LeanPool.VacuumBellSeparation.Bell.StateExtension
public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
Arbitrary orthogonal projection families in the original concrete VNA.
The net is indexed by all finite subsets, including the empty subset.
There is no separability, countability or nonzero-H assumption.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open Filter
open scoped Topology ComplexOrder BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance projectionSup_vna_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_vonNeumannAlgebra M

/-- The finite sum statement in the actual algebra subtype. -/
theorem isStarProjection_finite_sum_vna (M : VonNeumannAlgebra H) {ι : Type*}
    (P : ι → M.toStarSubalgebra) (hp : ∀ i, IsStarProjection (P i))
    (ho : Pairwise (fun i j => P i * P j = 0)) (F : Finset ι) :
    IsStarProjection (∑ i ∈ F, P i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using IsStarProjection.zero M.toStarSubalgebra
  | @insert i F hi ih =>
    rw [Finset.sum_insert hi]
    apply (hp i).add ih
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun j hj => ho (by intro he; subst j; exact hi hj)

/-- An actual projection supremum, with strong convergence of all finite sums
and a least-upper-bound assertion in the full positive operator order. -/
theorem exists_orthogonal_projection_supremum (M : VonNeumannAlgebra H) {ι : Type*}
    (P : ι → M.toStarSubalgebra) (hp : ∀ i, IsStarProjection (P i))
    (ho : Pairwise (fun i j => P i * P j = 0)) :
    ∃ Q : M.toStarSubalgebra, IsStarProjection Q ∧
      IsLUB (Set.range (fun F : Finset ι => ∑ i ∈ F, P i)) Q ∧
      (∀ i, P i ≤ Q) ∧
      (∀ x : H, Tendsto (fun F : Finset ι =>
        ((∑ i ∈ F, P i : M.toStarSubalgebra) : H →L[ℂ] H) x)
        atTop (𝓝 ((Q : H →L[ℂ] H) x))) := by
  classical
  let A : Finset ι → M.toStarSubalgebra := fun F => ∑ i ∈ F, P i
  have hA (F : Finset ι) : IsStarProjection (A F) :=
    isStarProjection_finite_sum_vna M P hp ho F
  have hmono : Monotone A := by
    intro F G hFG
    exact Finset.sum_le_sum_of_subset_of_nonneg hFG (fun i _ _ => (hp i).nonneg)
  have hbound (F : Finset ι) : A F ≤ 1 := sub_nonneg.mp (hA F).one_sub.nonneg
  obtain ⟨T, hT, hTpos, hsup⟩ :=
    Gaussian.exists_strongLimit_of_monotone_nonneg_bounded
      (fun F => (A F : H →L[ℂ] H)) (fun _ _ h => hmono h)
      (fun F => (hA F).nonneg) 1 hbound
  have hTM : T ∈ M := mem_vonNeumannAlgebra_of_strong_tendsto M
    (Eventually.of_forall fun F => (A F).2) hT
  let Q : M.toStarSubalgebra := ⟨T, hTM⟩
  have hQA (F : Finset ι) : T * (A F : H →L[ℂ] H) = A F := by
    apply ContinuousLinearMap.ext
    intro x
    apply tendsto_nhds_unique (hT ((A F : H →L[ℂ] H) x))
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop F] with G hFG
    have he := (hA F).le_iff_mul_eq_right (hA G) |>.mp (hmono hFG)
    exact congrArg (fun B : M.toStarSubalgebra => (B : H →L[ℂ] H) x) he.symm
  have hTT : T * T = T := by
    apply ContinuousLinearMap.ext
    intro x
    have hleft := T.continuous.tendsto (T x) |>.comp (hT x)
    have he (F : Finset ι) : T ((A F : H →L[ℂ] H) x) = (A F : H →L[ℂ] H) x :=
      congrArg (fun B : H →L[ℂ] H => B x) (hQA F)
    exact tendsto_nhds_unique (hleft.congr (fun F => he F)) (hT x)
  have hQ : IsStarProjection Q := by
    rw [isStarProjection_iff']
    exact ⟨Subtype.ext hTT, Subtype.ext hTpos.isSelfAdjoint.star_eq⟩
  have hQsup : IsLUB (Set.range A) Q := by
    constructor
    · rintro _ ⟨F, rfl⟩
      exact hsup.1 ⟨F, rfl⟩
    · intro B hB
      exact hsup.2 (by rintro _ ⟨F, rfl⟩; exact hB ⟨F, rfl⟩)
  refine ⟨Q, hQ, hQsup, ?_, hT⟩
  intro i
  simpa only [A, Finset.sum_singleton] using hQsup.1 ⟨{i}, rfl⟩

/-- Order normality gives convergence along an arbitrary monotone net,
not merely the net indexed by its image set. -/
theorem normalFunctional_tendsto_monotone_net (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ)
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (A : ι → M.toStarSubalgebra) (hmono : Monotone A) (hp : ∀ i, 0 ≤ A i)
    (Q : M.toStarSubalgebra) (hQ : IsLUB (Set.range A) Q) :
    Tendsto (fun i => (φ (A i)).re) atTop (𝓝 (φ Q).re) := by
  have hd : DirectedOn (· ≤ ·) (Set.range A) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    exact ⟨A k, ⟨k, rfl⟩, hmono hik, hmono hjk⟩
  have he : Set.range (fun i => (φ (A i)).re) =
      (fun X => (φ X).re) '' Set.range A := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨A i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
  apply tendsto_atTop_isLUB
  · intro i j hij
    exact (Complex.le_def.mp (φ.monotone' (hmono hij))).1
  · rw [he]
    exact hn _ (Set.range_nonempty A) hd (by rintro _ ⟨i, rfl⟩; exact hp i) Q hQ

/-- Projectionwise comparison survives the arbitrary orthogonal sum. -/
theorem normalFunctional_comparison_orthogonal_supremum (M : VonNeumannAlgebra H)
    (φ ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hφ : IsNormalFunctional M φ) (hψ : IsNormalFunctional M ψ)
    {ι : Type*} (P : ι → M.toStarSubalgebra)
    (hp : ∀ i, IsStarProjection (P i))
    (hcomp : ∀ i, (ψ (P i)).re ≤ (φ (P i)).re)
    (Q : M.toStarSubalgebra)
    (hQ : IsLUB (Set.range (fun F : Finset ι => ∑ i ∈ F, P i)) Q) :
    (ψ Q).re ≤ (φ Q).re := by
  classical
  let A : Finset ι → M.toStarSubalgebra := fun F => ∑ i ∈ F, P i
  have hmono : Monotone A := fun F G hFG =>
    Finset.sum_le_sum_of_subset_of_nonneg hFG (fun i _ _ => (hp i).nonneg)
  have hpos (F : Finset ι) : 0 ≤ A F := Finset.sum_nonneg fun i _ => (hp i).nonneg
  apply le_of_tendsto_of_tendsto
    (normalFunctional_tendsto_monotone_net M ψ hψ A hmono hpos Q hQ)
    (normalFunctional_tendsto_monotone_net M φ hφ A hmono hpos Q hQ)
  have hsum (θ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (F : Finset ι) :
      (θ (A F)).re = ∑ i ∈ F, (θ (P i)).re := by
    change Complex.reCLM (θ (∑ i ∈ F, P i)) = _
    rw [map_sum]
    exact map_sum Complex.reCLM _ _
  exact Eventually.of_forall fun F => by
    change (ψ (A F)).re ≤ (φ (A F)).re
    rw [hsum ψ F, hsum φ F]
    exact Finset.sum_le_sum fun i _ => hcomp i

end VacuumBellSeparation.Bipartite
