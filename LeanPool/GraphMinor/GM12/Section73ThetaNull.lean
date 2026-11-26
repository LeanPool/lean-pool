/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2ArcHomotopy
public import LeanPool.GraphMinor.GM12.Section2PathHomotopy
import LeanPool.GraphMinor.GM07.Section11a
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Null-homotopy of the third circle of a theta graph

The representativity argument in XII (7.3), page 261, can simplify
a non-null normal circle by a chord in a region. If both new circles
were null-homotopic, each would bound a disc. In those discs the two
old arcs are each homotopic to the chord. They are therefore homotopic
to each other, which makes the old circle null-homotopic as well.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM07

/-- In a theta graph, null-homotopy of both circles using the chord
implies null-homotopy of the remaining circle. This supplies the
circle simplification used for representativity in XII (7.3). -/
theorem nullHomotopic_third_theta_circle
    {S : Type*} [TopologicalSpace S] [T2Space S] (hS : IsSurface S)
    {A B L : Set S} {a b : S}
    (hA : IsLineWithEnds A a b) (hB : IsLineWithEnds B a b) (hL : IsLineWithEnds L a b)
    (hAB : A ∩ B = {a, b}) (hLA : IsOArc (L ∪ A)) (hLB : IsOArc (L ∪ B))
    (hnullA : IsNullHomotopicOArc (L ∪ A)) (hnullB : IsNullHomotopicOArc (L ∪ B)) :
    IsNullHomotopicOArc (A ∪ B) := by
  obtain ⟨D₁, hD₁, hbd₁⟩ := nullHomotopicOArc_bounds_disc hS hLA hnullA
  obtain ⟨D₂, hD₂, hbd₂⟩ := nullHomotopicOArc_bounds_disc hS hLB hnullB
  obtain ⟨f, hf, hfA, hf0, hf1⟩ := hA.exists_arc
  obtain ⟨g, hg, hgB, hg0, hg1⟩ := hB.exists_arc
  obtain ⟨ℓ, hℓ, hℓL, hℓ0, hℓ1⟩ := hL.exists_arc
  let p : Path a b := ⟨⟨f, hf.1⟩, hf0, hf1⟩
  let q : Path a b := ⟨⟨g, hg.1⟩, hg0, hg1⟩
  let k : Path a b := ⟨⟨ℓ, hℓ.1⟩, hℓ0, hℓ1⟩
  have hpD : ∀ t, p t ∈ D₁ := fun t => Surface.discBd_subset D₁
    (hbd₁.symm ▸ Or.inr (hfA ▸ mem_range_self t))
  have hkD : ∀ t, k t ∈ D₁ := fun t => Surface.discBd_subset D₁
    (hbd₁.symm ▸ Or.inl (hℓL ▸ mem_range_self t))
  have hqD : ∀ t, q t ∈ D₂ := fun t => Surface.discBd_subset D₂
    (hbd₂.symm ▸ Or.inr (hgB ▸ mem_range_self t))
  have hkD' : ∀ t, k t ∈ D₂ := fun t => Surface.discBd_subset D₂
    (hbd₂.symm ▸ Or.inl (hℓL ▸ mem_range_self t))
  have hpk := paths_homotopic_of_range_in_simplyConnected hD₁.isSimplyConnectedSet p k hpD hkD
  have hqk := paths_homotopic_of_range_in_simplyConnected hD₂.isSimplyConnectedSet q k hqD hkD'
  have hcross : ∀ s t, p s = q t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t heq
    have hends : p s ∈ ({a, b} : Set S) := hAB.subset
      ⟨hfA ▸ mem_range_self s, heq ▸ (hgB ▸ mem_range_self t)⟩
    rcases hends with ha | hb
    · exact Or.inl ⟨hf.2 (ha.trans hf0.symm), hg.2 (heq.symm.trans (ha.trans hg0.symm))⟩
    · exact Or.inr ⟨hf.2 (hb.trans hf1.symm), hg.2 (heq.symm.trans (hb.trans hg1.symm))⟩
  have hnull := nullHomotopic_union_of_homotopic_arcs p q hf.2 hg.2 hcross (hpk.trans hqk.symm)
  change IsNullHomotopicOArcIn univ (range f ∪ range g) at hnull
  rwa [hfA, hgB] at hnull

end GraphMinor.GM12
