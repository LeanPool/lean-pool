/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM12.Section2ArcHomotopy
import LeanPool.GraphMinor.Surface.Disc

/-!
# Two planar pair circles determine the third homotopy

For the three-branch shape in VII Section 8, used by XII (3.1), page
245, two pair circles lying in discs make their common branch homotopic
to each other branch. Transitivity makes the other two branches
homotopic. Traversing one and returning along the other therefore
gives a null-homotopic third circle. This spells out the path argument
behind the planarity comparisons for the third schismatic shape.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

private theorem path_of_line
    {S : Type*} [TopologicalSpace S] {L : Set S} {u v : S}
    (hL : IsLineWithEnds L u v) :
    ∃ p : Path u v, Function.Injective p ∧ range p = L := by
  obtain ⟨e, he0, he1⟩ := hL
  let p : Path u v := {
    toFun := fun t => (e t).val
    continuous_toFun := continuous_subtype_val.comp e.continuous
    source' := he0
    target' := he1 }
  exact ⟨p, fun s t he => e.injective (Subtype.ext he),
    (e.surjective.range_comp Subtype.val).trans Subtype.range_val⟩

/-- Two paths whose ranges lie in one closed disc are homotopic with
fixed ends. The disc's relative-endpoint curve homotopy gives the path
homotopy after exchanging its two parameters. -/
theorem paths_homotopic_of_planar_union
    {S : Type*} [TopologicalSpace S] {u v : S} (p q : Path u v)
    (hplan : IsPlanar (range p ∪ range q)) : p.Homotopic q := by
  obtain ⟨D, hD, hsub⟩ := hplan
  have hcurves := hD.curvesHomotopicIn
    (fun _ hx => hsub (Or.inl hx)) (fun _ hx => hsub (Or.inr hx))
    (p.source.trans q.source.symm) (p.target.trans q.target.symm)
  obtain ⟨H, _, h0, h1, hleft, _, hright, _⟩ := hcurves
  refine ⟨{
    toFun := fun z => H (z.2, z.1)
    continuous_toFun := H.continuous.comp (continuous_snd.prodMk continuous_fst)
    map_zero_left := h0
    map_one_left := h1
    prop' := ?_ }⟩
  intro t s hs
  rcases hs with rfl | hs
  · exact hleft t
  · have hs1 : s = 1 := mem_singleton_iff.mp hs
    subst s
    exact hright t

/-- If two pair circles of three branches are planar, the third is
null-homotopic. The homotopies through the common branch are composed
with their ends fixed. -/
theorem third_pair_null_of_two_planar_pairs
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {P Q R : Set S} {u v : S}
    (hP : IsLineWithEnds P u v) (hQ : IsLineWithEnds Q u v) (hR : IsLineWithEnds R u v)
    (hQR : Q ∩ R = {u, v})
    (hplanPQ : IsPlanar (P ∪ Q)) (hplanPR : IsPlanar (P ∪ R)) :
    IsNullHomotopicOArc (Q ∪ R) := by
  obtain ⟨p, _, hp⟩ := path_of_line hP
  obtain ⟨q, hqi, hq⟩ := path_of_line hQ
  obtain ⟨r, hri, hr⟩ := path_of_line hR
  have hpq : p.Homotopic q := paths_homotopic_of_planar_union p q (by rwa [hp, hq])
  have hpr : p.Homotopic r := paths_homotopic_of_planar_union p r (by rwa [hp, hr])
  have hcross : ∀ s t, q s = r t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t he
    have hxQ : q s ∈ Q := hq ▸ mem_range_self s
    have hxR : q s ∈ R := he.symm ▸ (hr ▸ mem_range_self t)
    have hx : q s ∈ ({u, v} : Set S) := hQR ▸ (show q s ∈ Q ∩ R from ⟨hxQ, hxR⟩)
    rcases hx with hxu | hxv
    · exact Or.inl ⟨hqi (hxu.trans q.source.symm), hri (he.symm.trans (hxu.trans r.source.symm))⟩
    · exact Or.inr ⟨hqi (hxv.trans q.target.symm), hri (he.symm.trans (hxv.trans r.target.symm))⟩
  have hnull := nullHomotopic_union_of_homotopic_arcs q r hqi hri hcross (hpq.symm.trans hpr)
  rw [hq, hr] at hnull
  exact hnull

end GraphMinor.GM12
