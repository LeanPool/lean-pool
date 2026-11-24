/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.Section46ClosedComponents
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.Surface.Cuffs
import LeanPool.GraphMinor.Surface.Classification
import LeanPool.GraphMinor.Surface.AddCrosscap

/-!
# Components of the retained graph together with the cuffs

For the cuff count in VII (4.6), page 226, the components of
`U(L) ∪ bd(Σ)` form a finite closed family. Cover this set by the
vertices and closed edges of `L`, and the finitely many original cuffs.
Each covering set is connected. Finite component families also have
closed remainders, which is needed to lift each part through the cut.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

/-- Finiteness and closedness of the components used for the cuff count
in VII (4.6), page 226. -/
theorem boundary_components_finite_closed {S : Type*} [TopologicalSpace S]
    (hS : IsSurface S) (L : Drawing S) :
    (componentsIn (L.U ∪ bd S)).Finite ∧
      ∀ C ∈ componentsIn (L.U ∪ bd S), IsClosed C ∧ IsClosed ((L.U ∪ bd S) \ C) := by
  have : T2Space S := hS.2.1
  let 𝒜 : Set (Set S) := ((fun x : S => ({x} : Set S)) '' L.V ∪ closure '' L.E) ∪ cuffs S
  have hfin : 𝒜.Finite :=
    ((L.finite_V.image _).union (L.finite_edges.image _)).union (cuff_statement S hS).2.1
  have hne : ∀ A ∈ 𝒜, A.Nonempty := by
    intro A hA
    rcases hA with (⟨x, _, rfl⟩ | ⟨e, he, rfl⟩) | hC
    · exact singleton_nonempty _
    · exact he.1.mono subset_closure
    · exact ((cuff_statement S hS).2.2 A hC).isConnected'.nonempty
  have hconn : ∀ A ∈ 𝒜, IsPreconnected A := by
    intro A hA
    rcases hA with (⟨x, _, rfl⟩ | ⟨e, he, rfl⟩) | hC
    · exact isPreconnected_singleton
    · exact he.2.2.1.isConnected.isPreconnected.closure
    · exact ((cuff_statement S hS).2.2 A hC).isConnected'.isPreconnected
  have hcover : L.U ∪ bd S = ⋃₀ 𝒜 := by
    ext x
    constructor
    · rintro (hx | hx)
      · rw [L.U_eq] at hx
        rcases hx with hxV | hxE
        · exact ⟨{x}, .inl (.inl ⟨x, hxV, rfl⟩), mem_singleton x⟩
        · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxE
          exact ⟨closure e, .inl (.inr ⟨e, he, rfl⟩), hxe⟩
      · obtain ⟨C, hC, hxC⟩ := (congrArg (fun A => x ∈ A) (sUnion_cuffs (S := S))).mpr hx
        exact ⟨C, .inr hC, hxC⟩
    · rintro ⟨A, hA, hxA⟩
      rcases hA with (⟨y, hy, rfl⟩ | ⟨e, he, rfl⟩) | hC
      · exact .inl (L.V_subset_U (hxA ▸ hy))
      · exact .inl (L.closure_subset_U he hxA)
      · exact .inr (sUnion_cuffs (S := S) ▸ ⟨A, hC, hxA⟩)
  have hB : IsClosed (L.U ∪ bd S) := L.isClosed_U.union (isClosed_bd S)
  have hf := finite_componentsIn_of_finite_preconnected_cover hfin hne hconn hcover
  exact ⟨hf, fun C hC => ⟨isClosed_of_mem_componentsIn hB hC,
    isClosed_sdiff_of_mem_finite_componentsIn hB hf hC⟩⟩

end GraphMinor.GM07
