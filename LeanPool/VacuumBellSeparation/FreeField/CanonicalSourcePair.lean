/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroSymplecticAlgebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The actual joint canonical system of two disjoint source regions

The literal symplectic cross form vanishes by disjoint support. The sum of
the two finite canonical systems is finite and nondegenerate, and their
intersection is zero. Localization is retained in the union of the regions.
-/

@[expose] public section

namespace VacuumBellSeparation

variable {U W : Set (EuclideanSpace ℝ (Fin 3))}
  {S T : Submodule ℝ TimeZeroSource}

theorem canonicalSourcePair_cross (hUW : Disjoint U W)
    (hS : IsCanonicalSourceSystem U S) (hT : IsCanonicalSourceSystem W T)
    {u v : TimeZeroSource} (hu : u ∈ S) (hv : v ∈ T) : timeZeroSymplectic u v = 0 :=
  timeZeroSymplectic_eq_zero_of_disjoint hUW (hS.2.1 hu) (hT.2.1 hv)

theorem canonicalSourcePair_disjoint (hUW : Disjoint U W)
    (hS : IsCanonicalSourceSystem U S) (hT : IsCanonicalSourceSystem W T) : Disjoint S T := by
  apply Submodule.disjoint_def.mpr
  intro u huS huT
  apply hS.2.2 u huS
  intro v hv
  rw [timeZeroSymplectic_skew, canonicalSourcePair_cross hUW hS hT hv huT, neg_zero]

theorem canonicalSourcePair_sup_isCanonical (hUW : Disjoint U W)
    (hS : IsCanonicalSourceSystem U S) (hT : IsCanonicalSourceSystem W T) :
    IsCanonicalSourceSystem (U ∪ W) (S ⊔ T) := by
  let : FiniteDimensional ℝ S := hS.1
  let : FiniteDimensional ℝ T := hT.1
  refine ⟨inferInstance, sup_le
    (hS.2.1.trans (localizedTimeZeroSources_mono Set.subset_union_left))
    (hT.2.1.trans (localizedTimeZeroSources_mono Set.subset_union_right)), ?_⟩
  intro u hu hz
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hu
  have hs0 : s = 0 := by
    apply hS.2.2 s hs
    intro v hv
    have h := hz v (Submodule.mem_sup_left hv)
    have htv : timeZeroSymplectic t v = 0 := by
      rw [timeZeroSymplectic_skew, canonicalSourcePair_cross hUW hS hT hv ht, neg_zero]
    simpa only [timeZeroSymplectic_add_left, htv, add_zero] using h
  have ht0 : t = 0 := by
    apply hT.2.2 t ht
    intro v hv
    have h := hz v (Submodule.mem_sup_right hv)
    simpa only [timeZeroSymplectic_add_left, canonicalSourcePair_cross hUW hS hT hs hv,
      zero_add] using h
  rw [hs0, ht0, add_zero]

end VacuumBellSeparation
