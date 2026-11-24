/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM11.Walks

/-!
# The sum along the path in VII (2.6)

The text bounds `|U(P) ∩ V(G)|` by adding a bound for each edge. A vertex of `P` off `bd(Σ)` lies
only on
edges with the inequality of `Net.edge_contacts_le`. An inner one is on two such edges and an end of
`P`
on one, and `walk_contacts_le` counts this along the walk.
-/

public section
namespace GraphMinor.GM07
open Set Surface
universe u

variable {S : Type u} [TopologicalSpace S]

/-- The ends of a line are determined by the line. -/
theorem seam_line_end_mem {F : Set S} {s t u v : S} (h₁ : IsLineWithEnds F s t)
    (h₂ : IsLineWithEnds F u v) : s = u ∨ s = v := by
  obtain ⟨g, g0, g1⟩ := h₁
  obtain ⟨f, f0, f1⟩ := h₂
  by_contra hn
  push Not at hn
  let c : unitInterval → unitInterval := fun q => f.symm (g q)
  have hc : Continuous c := f.symm.continuous.comp g.continuous
  have hA : IsPreconnected (c '' Ioc 0 1) := isPreconnected_Ioc.image c hc.continuousOn
  have hord := hA.ordConnected
  have hin : ∀ r : unitInterval, (f r).1 ≠ s → r ∈ c '' Ioc 0 1 := by
    intro r hr
    refine ⟨g.symm (f r), ?_, by simp [c]⟩
    refine ⟨lt_of_le_of_ne unitInterval.nonneg' fun h => hr ?_, unitInterval.le_one'⟩
    have : g (g.symm (f r)) = g 0 := by rw [← h]
    rw [g.apply_symm_apply] at this
    rw [this, g0]
  have h0 : (0 : unitInterval) ∈ c '' Ioc 0 1 := hin 0 (by rw [f0]; exact hn.1.symm)
  have h1 : (1 : unitInterval) ∈ c '' Ioc 0 1 := hin 1 (by rw [f1]; exact hn.2.symm)
  obtain ⟨q, hq, hqc⟩ := hord.out h0 h1 (⟨unitInterval.nonneg', unitInterval.le_one'⟩ :
    c 0 ∈ Icc (0 : unitInterval) 1)
  have : g q = g 0 := f.symm.injective hqc
  exact hq.1.ne' (g.injective this)

/-- The vertices of a walk, with its edges. -/
@[expose] def walkPoints {Γ : Drawing S} {x y : S} (W : GraphWalk Γ.toGraph x y) : Set S :=
  {z | z ∈ W.support} ∪ ⋃ e ∈ {e | e ∈ W.edges}, e

/-- See the module docstring. An edge either has no contacts off `Bd`, or it satisfies the
inequality
with total `c`. -/
theorem walk_contacts_le {Γ : Drawing S} {V Bd : Set S} (hV : V.Finite) (c : ℕ) {x y : S}
    (W : GraphWalk Γ.toGraph x y) (hW : W.IsSimple)
    (hedge : ∀ e a b, e ∈ W.edges → Γ.toGraph.IsLink e a b → a ≠ b →
      (e ∩ V ⊆ Bd ∧ a ∉ V \ Bd ∧ b ∉ V \ Bd) ∨
        2 * (e ∩ V).ncard + ({a} ∩ V).ncard + ({b} ∩ V).ncard ≤ c) :
    2 * (walkPoints W ∩ (V \ Bd)).ncard ≤
      W.edges.length * c + ({x} ∩ (V \ Bd)).ncard + ({y} ∩ (V \ Bd)).ncard := by
  have hle : ∀ z : S, ({z} ∩ (V \ Bd)).ncard ≤ ({z} ∩ V).ncard := fun z =>
    ncard_le_ncard (fun w hw => ⟨hw.1, hw.2.1⟩) (hV.subset inter_subset_right)
  have hzero : ∀ z : S, z ∉ V \ Bd → ({z} ∩ (V \ Bd)).ncard = 0 := by
    intro z hz
    rw [show {z} ∩ (V \ Bd) = ∅ from eq_empty_of_forall_notMem fun w hw =>
      hz ((mem_singleton_iff.mp hw.1) ▸ hw.2), ncard_empty]
  have hfin : (V \ Bd).Finite := hV.subset sdiff_subset
  induction W with
  | @nil z hv =>
    have : walkPoints (GraphWalk.nil hv : GraphWalk Γ.toGraph z z) ∩ (V \ Bd) =
        {z} ∩ (V \ Bd) := by
      ext w
      simp [walkPoints]
    rw [this]
    simp only [GraphWalk.edges, List.length_nil, zero_mul]
    omega
  | @cons u v w e hlink rest ih =>
    have hnd : (u :: rest.support).Nodup := hW
    have huv : u ≠ v := by
      have hmem : v ∈ rest.support := by cases rest <;> simp [GraphWalk.support]
      rintro rfl
      exact (List.nodup_cons.mp hnd).1 hmem
    have ih' := ih (List.nodup_cons.mp hnd).2 (fun e' a b he' => hedge e' a b (by
      simp only [GraphWalk.edges]
      exact List.mem_cons_of_mem _ he'))
    have hsub : walkPoints (GraphWalk.cons hlink rest) ∩ (V \ Bd) ⊆
        (({u} ∩ (V \ Bd)) ∪ (e ∩ (V \ Bd))) ∪ (walkPoints rest ∩ (V \ Bd)) := by
      rintro z ⟨hz | hz, hzV⟩
      · have : z = u ∨ z ∈ rest.support := by simpa [GraphWalk.support] using hz
        rcases this with rfl | h
        · exact Or.inl (Or.inl ⟨rfl, hzV⟩)
        · exact Or.inr ⟨Or.inl h, hzV⟩
      · obtain ⟨g, hg, hzg⟩ := mem_iUnion₂.mp hz
        have : g = e ∨ g ∈ rest.edges := by simpa [GraphWalk.edges] using hg
        rcases this with rfl | h
        · exact Or.inl (Or.inr ⟨hzg, hzV⟩)
        · exact Or.inr ⟨Or.inr (mem_biUnion h hzg), hzV⟩
    have hle₁ : (walkPoints (GraphWalk.cons hlink rest) ∩ (V \ Bd)).ncard ≤
        ({u} ∩ (V \ Bd)).ncard + (e ∩ (V \ Bd)).ncard + (walkPoints rest ∩ (V \ Bd)).ncard := by
      have h₁ := ncard_le_ncard hsub (((hfin.subset inter_subset_right).union
        (hfin.subset inter_subset_right)).union (hfin.subset inter_subset_right))
      have h₂ := ncard_union_le (({u} ∩ (V \ Bd)) ∪ (e ∩ (V \ Bd))) (walkPoints rest ∩ (V \ Bd))
      have h₃ := ncard_union_le ({u} ∩ (V \ Bd)) (e ∩ (V \ Bd))
      omega
    have hlen : (GraphWalk.cons hlink rest).edges.length * c = rest.edges.length * c + c := by
      simp only [GraphWalk.edges, List.length_cons, Nat.succ_mul]
    rw [hlen]
    rcases hedge e u v (by simp [GraphWalk.edges]) hlink huv with ⟨h₁, h₂, h₃⟩ | h₁
    · have he0 : (e ∩ (V \ Bd)).ncard = 0 := by
        rw [show e ∩ (V \ Bd) = ∅ from eq_empty_of_forall_notMem fun z hz =>
          hz.2.2 (h₁ ⟨hz.1, hz.2.1⟩), ncard_empty]
      have := hzero u h₂
      have := hzero v h₃
      omega
    · have he : (e ∩ (V \ Bd)).ncard ≤ (e ∩ V).ncard :=
        ncard_le_ncard (fun z hz => ⟨hz.1, hz.2.1⟩) (hV.subset inter_subset_right)
      have := hle u
      have := hle v
      omega

end GraphMinor.GM07
