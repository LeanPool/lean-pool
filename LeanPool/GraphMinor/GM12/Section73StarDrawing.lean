/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73ImageArc
public import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM12.Section4FiniteLineDrawing
import LeanPool.GraphMinor.GM11.RadialCorners
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# The drawing obtained by contracting a star

For the radial-star contraction in XII (7.3), page 261, every
surviving edge closure meets the collapsed star in at most one
vertex. Its image is therefore still a line. Assemble these lines
into the image drawing and identify its point, vertex, and edge sets.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Construct the image drawing of a collapsed set when surviving
edge closures meet that set in at most one vertex. This realizes the
radial-star contraction in XII (7.3), page 261. -/
theorem exists_drawing_of_star_collapse
    {S : Type*} [TopologicalSpace S] [T2Space S] {K : Drawing S}
    {A : Set S} {C : Set (Set S)} {v : S} (hv : v ∈ K.V) (hvA : v ∈ A)
    (hremove : ∀ e ∈ C, closure e ⊆ A)
    (hlines : ∀ g ∈ K.E \ C, ∃ u w : S, IsLineWithEnds (closure g) u w ∧
      closure g ∩ K.V = {u, w})
    (hmeet : ∀ g ∈ K.E \ C, (closure g ∩ A).Subsingleton)
    (hvertex : ∀ g ∈ K.E \ C, closure g ∩ A ⊆ K.V)
    (f : C(S, S)) (hcollapse : ∀ x ∈ A, f x = v)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A)) :
    ∃ H : Drawing S, H.U = f '' K.U ∧ H.V = f '' K.V ∧
      H.E = (fun g => f '' g) '' (K.E \ C) := by
  classical
  let ι := {g : K.E // g.val ∉ C}
  let : Finite K.E := K.finite_edges.to_subtype
  have hdata : ∀ i : ι, ∃ u w : S, IsLineWithEnds (closure i.1.1) u w ∧
      closure i.1.1 ∩ K.V = {u, w} := fun i => hlines i.1.1 ⟨i.1.2, i.2⟩
  choose u w hline hcap using hdata
  let L : ι → Set S := fun i => f '' closure i.1.1
  have hinj : ∀ i : ι, InjOn f (closure i.1.1) := by
    intro i x hx y hy heq
    rcases (hfibre x y).mp heq with hxy | hLxy
    · exact hxy
    · exact hmeet i.1.1 ⟨i.1.2, i.2⟩ ⟨hx, hLxy.1⟩ ⟨hy, hLxy.2⟩
  have hnewline : ∀ i : ι, IsLineWithEnds (L i) (f (u i)) (f (w i)) := fun i =>
    lineWithEnds_image_of_injOn (hline i) f.continuous.continuousOn (hinj i)
  have hends : ∀ i : ι, L i ∩ (f '' K.V) = {f (u i), f (w i)} := by
    intro i
    apply Subset.antisymm
    · rintro y ⟨⟨z, hzg, hzy⟩, ⟨a, haV, hay⟩⟩
      have hzV : z ∈ K.V := by
        rcases (hfibre z a).mp (hzy.trans hay.symm) with hza | hzL
        · exact hza ▸ haV
        · exact hvertex i.1.1 ⟨i.1.2, i.2⟩ ⟨hzg, hzL.1⟩
      rcases (hcap i).subset ⟨hzg, hzV⟩ with hzu | hzw
      · exact Or.inl (hzy.symm.trans (congrArg f hzu))
      · exact Or.inr (hzy.symm.trans (congrArg f hzw))
    · rintro y (rfl | rfl)
      · have hu := (hcap i).superset (Or.inl rfl)
        exact ⟨⟨u i, hu.1, rfl⟩, ⟨u i, hu.2, rfl⟩⟩
      · have hw := (hcap i).superset (Or.inr rfl)
        exact ⟨⟨w i, hw.1, rfl⟩, ⟨w i, hw.2, rfl⟩⟩
  have hnewmeet : ∀ i j : ι, i ≠ j → L i ∩ L j ⊆ f '' K.V := by
    intro i j hij y hy
    obtain ⟨z, hzi, hzy⟩ := hy.1
    obtain ⟨a, haj, hay⟩ := hy.2
    have hgedge : i.1.1 ≠ j.1.1 := fun h => hij (Subtype.ext (Subtype.ext h))
    rcases (hfibre z a).mp (hzy.trans hay.symm) with hza | hzL
    · exact ⟨z, closure_inter_subset_V i.1.2 j.1.2 hgedge ⟨hzi, hza ▸ haj⟩, hzy⟩
    · have hyv : y = v := hzy.symm.trans (hcollapse z hzL.1)
      exact ⟨v, hv, (hcollapse v hvA).trans hyv.symm⟩
  obtain ⟨H, hHU, hHV, hHE⟩ := exists_drawing_of_finite_lines
    (K.finite_V.image f) (Set.finite_univ : (univ : Set ι).Finite)
    L (fun i => f (u i)) (fun i => f (w i))
    (fun i _ => hnewline i) (fun i _ => lineWithEnds_ends_ne (hnewline i))
    (fun i _ => hends i) (fun i _ j _ hij => hnewmeet i j hij)
  have hinterior : ∀ i : ι, L i \ {f (u i), f (w i)} = f '' i.1.1 := by
    intro i
    apply Subset.antisymm
    · rintro y ⟨⟨z, hz, hzy⟩, hyn⟩
      have hzV : z ∉ K.V := by
        intro hzV
        rcases (hcap i).subset ⟨hz, hzV⟩ with hzu | hzw
        · exact hyn (Or.inl (hzy.symm.trans (congrArg f hzu)))
        · exact hyn (Or.inr (hzy.symm.trans (congrArg f hzw)))
      exact ⟨z, (K.closure_diff_V i.1.2).subset ⟨hz, hzV⟩, hzy⟩
    · rintro y ⟨z, hz, rfl⟩
      refine ⟨⟨z, subset_closure hz, rfl⟩, ?_⟩
      rintro (hequ | heqw)
      · have hzu : z = u i := hinj i (subset_closure hz)
          ((hcap i).superset (Or.inl rfl)).1 hequ
        exact (i.1.2.2.1 hz).2 (hzu ▸ ((hcap i).superset (Or.inl rfl)).2)
      · have hzw : z = w i := hinj i (subset_closure hz)
          ((hcap i).superset (Or.inr rfl)).1 heqw
        exact (i.1.2.2.1 hz).2 (hzw ▸ ((hcap i).superset (Or.inr rfl)).2)
  refine ⟨H, ?_, hHV, ?_⟩
  · rw [hHU]
    apply Subset.antisymm
    · rintro y (hyV | hyL)
      · obtain ⟨z, hz, rfl⟩ := hyV
        exact ⟨z, K.V_subset_U hz, rfl⟩
      · obtain ⟨i, _, z, hz, rfl⟩ := mem_iUnion₂.mp hyL
        exact ⟨z, K.closure_subset_U i.1.2 hz, rfl⟩
    · rintro y ⟨z, hzK, rfl⟩
      rw [K.U_eq] at hzK
      rcases hzK with hzV | hzE
      · exact Or.inl ⟨z, hzV, rfl⟩
      · obtain ⟨g, hg, hzg⟩ := mem_iUnion₂.mp hzE
        by_cases hge : g ∈ C
        · have hzf : f z = v := hcollapse z (hremove g hge hzg)
          exact Or.inl ⟨v, hv, (hcollapse v hvA).trans hzf.symm⟩
        · let i : ι := ⟨⟨g, hg⟩, hge⟩
          exact Or.inr (mem_iUnion₂.mpr ⟨i, mem_univ _, z, hzg, rfl⟩)
  · rw [hHE]
    apply Subset.antisymm
    · rintro g ⟨i, _, rfl⟩
      exact ⟨i.1.1, ⟨i.1.2, i.2⟩, (hinterior i).symm⟩
    · rintro g ⟨a, ha, rfl⟩
      let i : ι := ⟨⟨a, ha.1⟩, ha.2⟩
      exact ⟨i, mem_univ _, hinterior i⟩

end GraphMinor.GM12
