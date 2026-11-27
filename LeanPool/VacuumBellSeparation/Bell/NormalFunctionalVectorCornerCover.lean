/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.NormalFunctionalVectorCorner

/-!
A maximal family of original, mutually orthogonal, vector-realized corners
covers the identity. This includes H=0, where the family may be empty and
the identity is zero. No countability or normal-state representation premise
is added. Cross terms of finite compressions are not discarded.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open Filter
open scoped Topology ComplexOrder InnerProductSpace BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance vectorCornerCover_vna_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_vonNeumannAlgebra M

/-- The nonzero-corner theorem, applied in the remaining complement, forces
the maximal orthogonal family to have actual strong sum equal to one. -/
theorem exists_orthogonal_vector_corner_cover (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ) :
    ∃ s : Set M.toStarSubalgebra,
      s.Pairwise (fun p q => p * q = 0) ∧
      (∀ p ∈ s, IsStarProjection p ∧ p ≠ 0 ∧
        ∃ ξ : H, (p : H →L[ℂ] H) ξ = ξ ∧ ‖ξ‖ = Real.sqrt (φ p).re ∧
          ∀ a : M.toStarSubalgebra, vectorFunctional M ξ a = φ (p * a * p)) ∧
      IsLUB (Set.range (fun F : Finset s => ∑ i ∈ F, i.1)) 1 ∧
      ∀ x : H, Tendsto (fun F : Finset s =>
        ((∑ i ∈ F, i.1 : M.toStarSubalgebra) : H →L[ℂ] H) x) atTop (𝓝 x) := by
  classical
  let good : Set (Set M.toStarSubalgebra) := {s |
    (∀ p ∈ s, IsStarProjection p ∧ p ≠ 0 ∧
      ∃ ξ : H, (p : H →L[ℂ] H) ξ = ξ ∧ ‖ξ‖ = Real.sqrt (φ p).re ∧
        ∀ a : M.toStarSubalgebra, vectorFunctional M ξ a = φ (p * a * p)) ∧
    s.Pairwise (fun p q => p * q = 0)}
  obtain ⟨s, hs⟩ : ∃ s, Maximal (· ∈ good) s := by
    apply zorn_subset
    intro c hc hchain
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun t ht => Set.subset_sUnion_of_mem ht⟩
    · rintro p ⟨t, ht, hpt⟩
      exact (hc ht).1 p hpt
    · rintro p ⟨t, ht, hpt⟩ q ⟨u, hu, hqu⟩ hpq
      by_cases htu : t = u
      · subst u
        exact (hc ht).2 hpt hqu hpq
      · rcases hchain ht hu htu with htu | hut
        · exact (hc hu).2 (htu hpt) hqu hpq
        · exact (hc ht).2 hpt (hut hqu) hpq
  let P : s → M.toStarSubalgebra := fun i => i.1
  have hp (i : s) : IsStarProjection (P i) := (hs.prop.1 i.1 i.2).1
  have ho : Pairwise (fun i j : s => P i * P j = 0) := by
    intro i j hij
    exact hs.prop.2 i.2 j.2 (fun h => hij (Subtype.ext h))
  obtain ⟨Q, hQ, hsup, hPQ, hstrong⟩ := exists_orthogonal_projection_supremum M P hp ho
  have hQone : Q = 1 := by
    by_contra hQne
    have he : 1 - Q ≠ 0 := fun h => hQne (sub_eq_zero.mp h).symm
    obtain ⟨p, ξ, hps, hpne, hple, hpξ, hnξ, hrepr⟩ :=
      exists_nonzero_vector_realized_subcorner M φ hn (1 - Q) hQ.one_sub he
    have hpQ : p * Q = 0 := by
      calc
        p * Q = (p * (1 - Q)) * Q := by
          rw [(hps.le_iff_mul_eq_left hQ.one_sub).mp hple]
        _ = p * ((1 - Q) * Q) := mul_assoc _ _ _
        _ = 0 := by rw [hQ.one_sub_mul_self, mul_zero]
    have hpset (q : M.toStarSubalgebra) (hq : q ∈ s) : p * q = 0 := by
      have hqQ := (hs.prop.1 q hq).1.le_iff_mul_eq_right hQ |>.mp (hPQ ⟨q, hq⟩)
      calc
        p * q = p * (Q * q) := by rw [hqQ]
        _ = (p * Q) * q := (mul_assoc _ _ _).symm
        _ = 0 := by rw [hpQ, zero_mul]
    have hinsert : insert p s ∈ good := by
      constructor
      · intro q hq
        rcases hq with rfl | hq
        · exact ⟨hps, hpne, ξ, hpξ, hnξ, hrepr⟩
        · exact hs.prop.1 q hq
      · apply hs.prop.2.insert
        intro q hq hpq
        refine ⟨hpset q hq, ?_⟩
        simpa only [star_mul, hps.isSelfAdjoint.star_eq,
          (hs.prop.1 q hq).1.isSelfAdjoint.star_eq, star_zero] using congrArg star (hpset q hq)
    have hpin : p ∈ s := hs.mem_of_prop_insert hinsert
    exact hpne (hps.isIdempotentElem.eq.symm.trans (hpset p hpin))
  refine ⟨s, hs.prop.2, hs.prop.1, ?_, ?_⟩
  · simpa only [P, hQone] using hsup
  · intro x
    have hx : (Q : H →L[ℂ] H) x = x := by
      rw [hQone]
      rfl
    simpa only [P, hx] using hstrong x

end VacuumBellSeparation.Bipartite
