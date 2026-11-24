/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4FiniteMarkedDiscJoin
public import Mathlib.Topology.Separation.Regular
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Disjoint joined vertex stars

For XII (4.5), claim (1), page 253, thicken all vertex stars
without allowing different vertex discs to meet. First separate
the finitely many closed stars by disjoint open neighborhoods.
Join the arms of each star inside its own neighborhood. Each
joined disc has exactly the old star's contacts with the closed
set of crossing discs, and old boundary contacts remain on its
boundary.
-/

public section

namespace GraphMinor.GM12

open Set Surface

private theorem exists_disjoint_open_family {S V : Type*} [TopologicalSpace S]
    [NormalSpace S] [Finite V] (K : V → Set S) (hK : ∀ v, IsClosed (K v))
    (hdisj : ∀ v w, v ≠ w → Disjoint (K v) (K w)) :
    ∃ O : V → Set S, (∀ v, IsOpen (O v)) ∧ (∀ v, K v ⊆ O v) ∧
      ∀ v w, v ≠ w → Disjoint (O v) (O w) := by
  classical
  have hex : ∀ v w, ∃ U W : Set S, IsOpen U ∧ IsOpen W ∧
      K v ⊆ U ∧ K w ⊆ W ∧ (v ≠ w → Disjoint U W) := by
    intro v w
    by_cases hvw : v = w
    · exact ⟨univ, univ, isOpen_univ, isOpen_univ, subset_univ _, subset_univ _,
        fun h => False.elim (h hvw)⟩
    · obtain ⟨U, W, hU, hW, hv, hw, hUW⟩ := normal_separation (hK v) (hK w) (hdisj v w hvw)
      exact ⟨U, W, hU, hW, hv, hw, fun _ => hUW⟩
  choose U W hU hW hKU hKW hUW using hex
  let O := fun v => ⋂ w, U v w ∩ W w v
  refine ⟨O, (fun v => isOpen_iInter_of_finite (fun w => (hU v w).inter (hW w v))), ?_, ?_⟩
  · intro v z hz
    exact mem_iInter.mpr fun w => ⟨hKU v w hz, hKW w v hz⟩
  · intro v w hvw
    exact (hUW v w hvw).mono
      (fun z hz => (mem_iInter.mp hz w).1)
      (fun z hz => (mem_iInter.mp hz v).2)

/-- Disjoint finite stars of discs can be joined to disjoint
closed vertex discs, preserving their exact contacts with a
closed set. This is the vertex-disc assembly in XII (4.5),
claim (1), page 253. -/
theorem exists_disjoint_joined_stars {S V ι : Type} [TopologicalSpace S]
    [NormalSpace S] [Finite V] (hS : IsClosedSurface S)
    (A : V → Set S) (B : ι → Set S) (p : ι → S) (F : V → Finset ι)
    (hA : ∀ v, IsClosedDisc (A v)) (hB : ∀ v i, i ∈ F v → IsClosedDisc (B i))
    (hBB : ∀ v i, i ∈ F v → ∀ j ∈ F v, i ≠ j → Disjoint (B i) (B j))
    (hAB : ∀ v i, i ∈ F v → A v ∩ B i = {p i})
    (hpA : ∀ v i, i ∈ F v → p i ∈ discBd (A v))
    (hpB : ∀ v i, i ∈ F v → p i ∈ discBd (B i))
    (hstars : ∀ v w, v ≠ w → Disjoint
      (A v ∪ ⋃ i ∈ F v, B i) (A w ∪ ⋃ i ∈ F w, B i))
    (Z : Set S) (hZ : IsClosed Z) (hpZ : ∀ v i, i ∈ F v → p i ∉ Z) :
    ∃ D : V → Set S, (∀ v, IsClosedDisc (D v)) ∧
      (∀ v w, v ≠ w → Disjoint (D v) (D w)) ∧
      (∀ v, (A v ∪ ⋃ i ∈ F v, B i) ⊆ D v) ∧
      (∀ v, D v ∩ Z = (A v ∪ ⋃ i ∈ F v, B i) ∩ Z) ∧
      ∀ v, (discBd (A v) ∪ ⋃ i ∈ F v, discBd (B i)) ∩ Z ⊆ discBd (D v) := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hclosed : ∀ v, IsClosed (A v ∪ ⋃ i ∈ F v, B i) := fun v =>
    (hA v).isClosed.union ((F v).finite_toSet.isClosed_biUnion (fun i hi => (hB v i hi).isClosed))
  obtain ⟨O, hO, hKO, hOO⟩ := exists_disjoint_open_family
    (fun v => A v ∪ ⋃ i ∈ F v, B i) hclosed hstars
  have hex : ∀ v, ∃ D : Set S, IsClosedDisc D ∧ (A v ∪ ⋃ i ∈ F v, B i) ⊆ D ∧ D ⊆ O v ∧
      D ∩ Z = (A v ∪ ⋃ i ∈ F v, B i) ∩ Z ∧
      (discBd (A v) ∪ ⋃ i ∈ F v, discBd (B i)) ∩ Z ⊆ discBd D := by
    intro v
    apply exists_finite_join_preserving_contacts hS (A v) (O v) B p (hA v) (hO v)
      (fun z hz => hKO v (Or.inl hz)) (F v) Z hZ (hB v) (hBB v) (hAB v) (hpA v) (hpB v)
    · intro i hi z hz
      exact hKO v (Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hz⟩⟩))
    · exact hpZ v
  choose D hD hsub hDO hcontact hbd using hex
  exact ⟨D, hD, (fun v w hvw => (hOO v w hvw).mono (hDO v) (hDO w)), hsub, hcontact, hbd⟩

end GraphMinor.GM12
