/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73SplicedCircuit

/-!
# The part of the spliced circuit in the collapsed star

For XII (7.3), Claim (1), page 262, the retained path misses
the star. Each surviving spoke meets it only at its old hub.
When the hubs agree, the old circuit therefore meets the star
only at that hub. When they differ, its intersection is exactly
the union of the two star spokes used by the splice.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

open Classical in
/-- Compute the collapsed part of a spliced circuit from its
vertex and edge sets. This gives the two fibre alternatives in
XII (7.3), Claim (1), page 262. -/
theorem spliced_circuit_inter_collapse_set
    {S : Type*} [TopologicalSpace S] [T2Space S] {K C : Drawing S}
    {x y v p q : S} {a b c d : Set S} {A : Set S}
    (ha : K.toGraph.IsLink a v p) (hd : K.toGraph.IsLink d q v)
    (P : GraphWalk K.toGraph x y)
    (hCV : C.V = ({z | z ∈ P.support} ∪ {p, q}) ∪ (if p = q then ∅ else {v}))
    (hCE : C.E = if p = q then insert b (insert c {e | e ∈ P.edges})
      else insert a (insert b (insert c (insert d {e | e ∈ P.edges}))))
    (hPA : Disjoint (walkDrawing K P).U A)
    (haA : closure a ⊆ A) (hdA : closure d ⊆ A)
    (hbA : closure b ∩ A ⊆ {p}) (hcA : closure c ∩ A ⊆ {q}) :
    C.U ∩ A = if p = q then {p} else closure a ∪ closure d := by
  classical
  have hpcl : p ∈ closure a := (ha.2.2.2.superset (Or.inr rfl)).1
  have hqcl : q ∈ closure d := (hd.2.2.2.superset (Or.inl rfl)).1
  have hvcl : v ∈ closure a := (ha.2.2.2.superset (Or.inl rfl)).1
  have hPV : ∀ z ∈ P.support, z ∉ A := by
    intro z hz
    have hzV : z ∈ (walkDrawing K P).V := by rw [walkDrawing_V]; exact hz
    exact disjoint_left.mp hPA ((walkDrawing K P).V_subset_U hzV)
  have hPE : ∀ e ∈ P.edges, Disjoint (closure e) A := by
    intro e he
    have heP : e ∈ (walkDrawing K P).E := by rw [walkDrawing_E]; exact he
    exact hPA.mono_left ((walkDrawing K P).closure_subset_U heP)
  by_cases hpq : p = q
  · subst q
    rw [ite_eq_left rfl]
    have hCV' : C.V = {z | z ∈ P.support} ∪ {p} := by rw [hCV]; simp
    have hCE' : C.E = insert b (insert c {e | e ∈ P.edges}) := by
      rw [hCE, ite_eq_left rfl]
    apply Subset.antisymm
    · rintro z ⟨hzC, hzA⟩
      rw [C.U_eq] at hzC
      rcases hzC with hzV | hzE
      · rw [hCV'] at hzV
        exact hzV.resolve_left (fun hzP => hPV z hzP hzA)
      · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hzE
        rw [hCE'] at he
        rcases he with heq | heq | he
        · subst e
          exact hbA ⟨hze, hzA⟩
        · subst e
          exact hcA ⟨hze, hzA⟩
        · exact (disjoint_left.mp (hPE e he) hze hzA).elim
    · rintro z rfl
      exact ⟨C.V_subset_U (hCV'.symm ▸ Or.inr rfl), haA hpcl⟩
  · rw [ite_eq_right hpq]
    have hCV' : C.V = ({z | z ∈ P.support} ∪ {p, q}) ∪ {v} := by
      rw [hCV, ite_eq_right hpq]
    have hCE' : C.E = insert a (insert b (insert c (insert d {e | e ∈ P.edges}))) := by
      rw [hCE, ite_eq_right hpq]
    apply Subset.antisymm
    · rintro z ⟨hzC, hzA⟩
      rw [C.U_eq] at hzC
      rcases hzC with hzV | hzE
      · rw [hCV'] at hzV
        rcases hzV with (hzP | hzp | hzq) | hzv
        · exact (hPV z hzP hzA).elim
        · exact Or.inl (hzp.symm ▸ hpcl)
        · exact Or.inr (hzq.symm ▸ hqcl)
        · exact Or.inl (hzv.symm ▸ hvcl)
      · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hzE
        rw [hCE'] at he
        rcases he with heq | heq | heq | heq | he
        · subst e
          exact Or.inl hze
        · subst e
          have hzp : z = p := hbA ⟨hze, hzA⟩
          exact Or.inl (hzp.symm ▸ hpcl)
        · subst e
          have hzq : z = q := hcA ⟨hze, hzA⟩
          exact Or.inr (hzq.symm ▸ hqcl)
        · subst e
          exact Or.inr hze
        · exact (disjoint_left.mp (hPE e he) hze hzA).elim
    · intro z hz
      rcases hz with hz | hz
      · have haC : a ∈ C.E := hCE'.symm ▸ Or.inl rfl
        exact ⟨C.closure_subset_U haC hz, haA hz⟩
      · have hdC : d ∈ C.E := hCE'.symm ▸ Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        exact ⟨C.closure_subset_U hdC hz, hdA hz⟩

end GraphMinor.GM12
