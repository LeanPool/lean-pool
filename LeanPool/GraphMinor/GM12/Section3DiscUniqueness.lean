/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscsInSurface

/-!
# Disc uniqueness when the two discs do not cover the surface

In XII (3.1), page 245, the sphere case is handled by a point outside
the enclosing discs. Two distinct discs with the same boundary would
form a sphere embedded in the original connected surface. Invariance
of domain makes that sphere open and closed, hence onto. The outside
point therefore ensures uniqueness just as nonsphericity does.
-/

public section

namespace GraphMinor.GM12

open Set Topology OnePoint Surface

/-- An injective continuous sphere map fills a connected surface.
Invariance of domain gives openness of its compact image. -/
theorem range_sphere_map_eq_univ
    {S : Type*} [TopologicalSpace S] [T2Space S] [PreconnectedSpace S]
    (hman : ∀ x : S, IsManifoldPoint x) {T : OnePoint EuclideanPlane → S}
    (hT : Continuous T) (hi : Function.Injective T) : range T = univ := by
  exact Surface.isSphereMap_range_eq_univ hman hT hi

/-- Two closed discs with the same boundary coincide if their union
does not fill the connected surface. -/
theorem eq_of_discBd_eq_of_union_ne_univ
    {S : Type*} [TopologicalSpace S] [T2Space S] [PreconnectedSpace S]
    (hman : ∀ x : S, IsManifoldPoint x) {Δ₁ Δ₂ : Set S}
    (h₁ : IsClosedDisc Δ₁) (h₂ : IsClosedDisc Δ₂)
    (hb : discBd Δ₁ = discBd Δ₂) (hnotcover : Δ₁ ∪ Δ₂ ≠ univ) : Δ₁ = Δ₂ := by
  rcases Surface.eq_or_inter_eq_discBd_of_discBd_eq hman h₁ h₂ hb with heq | hinter
  · exact heq
  · obtain ⟨T, hT, hi, hcov⟩ := exists_sphere_map h₁ h₂ hb hinter
    exact (hnotcover (hcov.symm.trans (range_sphere_map_eq_univ hman hT hi))).elim

end GraphMinor.GM12
