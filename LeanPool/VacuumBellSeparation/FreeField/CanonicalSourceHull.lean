/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CanonicalSourceSystemDefs
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroSymplecticNondegenerate
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# A directed cofinal family of finite canonical local source systems

Adjoin the explicit quarter-turns to a finite collection and take its real
span. The resulting finite space is invariant under the quarter-turn, so
the integral of f²+g² proves nondegeneracy of its actual symplectic form.
The construction is monotone and contains every given smooth source.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Canonical source hull obtained from `Submodule.span`. -/
def canonicalSourceHull (s : Set TimeZeroSource) : Submodule ℝ TimeZeroSource :=
  Submodule.span ℝ (s ∪ timeZeroQuarterTurn '' s)

theorem subset_canonicalSourceHull (s : Set TimeZeroSource) : s ⊆ canonicalSourceHull s :=
  fun _ hx => Submodule.subset_span (Or.inl hx)

theorem canonicalSourceHull_mono {s t : Set TimeZeroSource} (h : s ⊆ t) :
    canonicalSourceHull s ≤ canonicalSourceHull t :=
  Submodule.span_mono (Set.union_subset_union h (Set.image_mono h))

theorem quarterTurn_mem_canonicalSourceHull {s : Set TimeZeroSource} {u : TimeZeroSource}
    (hu : u ∈ canonicalSourceHull s) : timeZeroQuarterTurn u ∈ canonicalSourceHull s := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
      rcases hu with hu | ⟨v, hv, rfl⟩
      · exact Submodule.subset_span (Or.inr ⟨u, hu, rfl⟩)
      · rw [timeZeroQuarterTurn_sq]
        exact (canonicalSourceHull s).neg_mem (subset_canonicalSourceHull s hv)
  | zero => simpa only [map_zero] using (canonicalSourceHull s).zero_mem
  | add u v hu hv ihu ihv =>
      simpa only [map_add] using (canonicalSourceHull s).add_mem ihu ihv
  | smul a u hu ih =>
      simpa only [map_smul] using (canonicalSourceHull s).smul_mem a ih

theorem canonicalSourceHull_isCanonical {U : Set (EuclideanSpace ℝ (Fin 3))}
    {s : Set TimeZeroSource} (hs : s.Finite) (hloc : s ⊆ localizedTimeZeroSources U) :
    IsCanonicalSourceSystem U (canonicalSourceHull s) := by
  refine ⟨FiniteDimensional.span_of_finite ℝ (hs.union (hs.image timeZeroQuarterTurn)), ?_, ?_⟩
  · apply Submodule.span_le.mpr
    rintro u (hu | ⟨v, hv, rfl⟩)
    · exact hloc hu
    · exact timeZeroQuarterTurn_local (hloc hv)
  · intro u hu hz
    exact (timeZeroSymplectic_quarterTurn_eq_zero_iff u).mp
      (hz _ (quarterTurn_mem_canonicalSourceHull hu))

/-- Every finite collection of local smooth pairs lies in a finite canonical system. -/
theorem exists_canonicalSourceSystem_containing_finite
    {U : Set (EuclideanSpace ℝ (Fin 3))} {s : Set TimeZeroSource}
    (hs : s.Finite) (hloc : s ⊆ localizedTimeZeroSources U) :
    ∃ S : Submodule ℝ TimeZeroSource, IsCanonicalSourceSystem U S ∧ s ⊆ S :=
  ⟨canonicalSourceHull s, canonicalSourceHull_isCanonical hs hloc, subset_canonicalSourceHull s⟩

/-- Two finite generated canonical hulls have a common canonical upper bound. -/
theorem canonicalSourceHull_directed {U : Set (EuclideanSpace ℝ (Fin 3))}
    {s t : Set TimeZeroSource} (hs : s.Finite) (ht : t.Finite)
    (hsU : s ⊆ localizedTimeZeroSources U) (htU : t ⊆ localizedTimeZeroSources U) :
    ∃ S : Submodule ℝ TimeZeroSource, IsCanonicalSourceSystem U S ∧
      canonicalSourceHull s ≤ S ∧ canonicalSourceHull t ≤ S :=
  ⟨canonicalSourceHull (s ∪ t),
    canonicalSourceHull_isCanonical (hs.union ht) (Set.union_subset hsU htU),
    canonicalSourceHull_mono Set.subset_union_left, canonicalSourceHull_mono Set.subset_union_right⟩

end VacuumBellSeparation
