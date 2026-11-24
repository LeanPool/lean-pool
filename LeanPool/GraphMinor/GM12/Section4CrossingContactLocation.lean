/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Locating the residual contacts on their crossing discs

For XII (4.5), claim (1), page 253, the end of a residual
half-edge lies on the boundary of its own crossing disc.
Indeed, it lies in some crossing disc because it is on the
frontier of their closed union. A disc for an unrelated pair
misses the edge. Either incident edge determines that disc's
centre, and the one-crossing equation identifies it as the
edge's own crossing. The two distinct residual ends of the
edge therefore give exactly its two opposite boundary marks.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A residual contact of an edge lies on its own crossing
disc boundary. The protected-disc and one-crossing equations
exclude every other disc. This is used in XII (4.5), claim (1),
page 253. -/
theorem crossing_contact_mem_own_boundary {S T E : Type*}
    [TopologicalSpace S] [T2Space S] [Finite T]
    (hS : IsClosedSurface S) (D : T → Set S) (hD : ∀ i, IsClosedDisc (D i))
    (x : T → S) (hinj : Function.Injective x) (P : E → Set S) (left right : T → E)
    (hpair : ∀ i, x i ∈ P (left i) ∩ P (right i))
    (havoid : ∀ i e, e ≠ left i → e ≠ right i → Disjoint (D i) (P e))
    (e : E) (y : T) (hmeet : P e ∩ range x = {x y})
    {z : S} (hz : z ∈ P e ∩ frontier (⋃ i, D i)) : z ∈ discBd (D y) := by
  classical
  have hZ : IsClosed (⋃ i, D i) := isClosed_iUnion_of_finite (fun i => (hD i).isClosed)
  have hzZ : z ∈ ⋃ i, D i := hZ.closure_eq ▸ hz.2.1
  obtain ⟨i, hzi⟩ := mem_iUnion.mp hzZ
  have hei : e = left i ∨ e = right i := by
    by_cases hl : e = left i
    · exact Or.inl hl
    by_cases hr : e = right i
    · exact Or.inr hr
    exact False.elim (disjoint_left.mp (havoid i e hl hr) hzi hz.1)
  have hxiP : x i ∈ P e := hei.elim (fun h => h.symm ▸ (hpair i).1) (fun h => h.symm ▸ (hpair i).2)
  have hxy : x i = x y := mem_singleton_iff.mp (hmeet.subset ⟨hxiP, mem_range_self i⟩)
  have hiy : i = y := hinj hxy
  have hzDy : z ∈ D y := hiy ▸ hzi
  rw [← GM11.IsClosedDisc.frontier_eq_discBd hS (hD y)]
  refine ⟨subset_closure hzDy, ?_⟩
  intro hint
  exact hz.2.2 (interior_mono (subset_iUnion D y) hint)

/-- Two distinct residual ends of one edge are exactly its
opposite boundary-contact pair. This is the opposite-pair
identification in XII (4.5), claim (1), page 253. -/
theorem crossing_contact_pair_eq {S T E : Type*}
    [TopologicalSpace S] [T2Space S] [Finite T]
    (hS : IsClosedSurface S) (D : T → Set S) (hD : ∀ i, IsClosedDisc (D i))
    (x : T → S) (hinj : Function.Injective x) (P : E → Set S) (left right : T → E)
    (hpair : ∀ i, x i ∈ P (left i) ∩ P (right i))
    (havoid : ∀ i e, e ≠ left i → e ≠ right i → Disjoint (D i) (P e))
    (e : E) (y : T) (hmeet : P e ∩ range x = {x y})
    {a b u v : S} (hbd : P e ∩ discBd (D y) = {a, b}) (huv : u ≠ v)
    (hu : u ∈ P e ∩ frontier (⋃ i, D i)) (hv : v ∈ P e ∩ frontier (⋃ i, D i)) :
    ({u, v} : Set S) = {a, b} := by
  have hu' : u = a ∨ u = b := hbd.subset ⟨hu.1,
    crossing_contact_mem_own_boundary hS D hD x hinj P left right hpair havoid e y hmeet hu⟩
  have hv' : v = a ∨ v = b := hbd.subset ⟨hv.1,
    crossing_contact_mem_own_boundary hS D hD x hinj P left right hpair havoid e y hmeet hv⟩
  rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
  · exact False.elim (huv rfl)
  · rfl
  · exact pair_comm _ _
  · exact False.elim (huv rfl)

end GraphMinor.GM12
