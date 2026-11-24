/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Seven
public import LeanPool.GraphMinor.Surface.CutLoop

/-!
# Graph Minors XIX, proof of (6.2): the enlargement `τ`

An inflation `σ` of `Γ₁` in `Γ₂` gives an enlargement `τ` of `sk(Γ₁)` in `sk(Γ₂)`, in `Σ̂`, as in
the
proof of (6.2), page 342. If `e` is an edge of `Γ₁` of size 2 then `τ(e) = σ(e)`. If `e` is a part
of the
boundary of the disc of an edge `c` of size 3, with ends `u, v`, then `τ(e)` is the part of the
boundary of the disc of `σ(c)` with ends in `σ(u), σ(v)`. For a vertex `v`, `τ(v)` is the subdrawing
of
`sk(Γ₂)` induced on `σ(v)`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]

/-- A set of vertices connected in a graph is closed under nothing smaller. -/
theorem preconnected_closed {α : Type} {G : SimpleGraph α} {X : Set α} (h :
  (G.induce X).Preconnected)
    {Y : Set α} (hY : Y ⊆ X) (hne : Y.Nonempty) (hc : ∀ a ∈ Y, ∀ b ∈ X, G.Adj a b → b ∈ Y) : Y = X
      := by
  obtain ⟨a, ha⟩ := hne
  refine Subset.antisymm hY fun b hb => ?_
  obtain ⟨p⟩ := h ⟨a, hY ha⟩ ⟨b, hb⟩
  have key : ∀ {x y : X}, (G.induce X).Walk x y → x.1 ∈ Y → y.1 ∈ Y := by
    intro x y p
    induction p with
    | nil => exact id
    | cons hadj _ ih => exact fun hx => ih (hc _ hx _ (Subtype.property _) hadj)
  exact key p ha

section Ends

variable {Γ Γ' : Painting S} {σv : S → Set S} {σe : Set S → Set S}


omit [T2Space S] in
/-- The ends of `σ(e)` are matched with the ends of `e`. -/
theorem infl_ends (h : IsInflation Γ Γ' σv σe) {e : Set S} (he : e ∈ Γ.E) :
    (∀ a ∈ tilde (σe e), ∃ y ∈ tilde e, a ∈ σv y) ∧ (∀ y ∈ tilde e, ∃ a ∈ tilde (σe e), a ∈ σv y)
      := by
  have hE' := h.edge_mem e he
  have hlen : (Γ.γ e).length = (Γ'.γ (σe e)).length := by
    rw [Γ.length_γ he, Γ'.length_γ hE', h.edge_size e he]
  have hs₁ : ∀ y, y ∈ Γ.γ e ↔ y ∈ tilde e := fun y => by
    rw [← Γ.γ_set e he]
    rfl
  have hs₂ : ∀ y, y ∈ Γ'.γ (σe e) ↔ y ∈ tilde (σe e) := fun y => by
    rw [← Γ'.γ_set _ hE']
    rfl
  constructor
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ((hs₂ a).mpr ha)
    have hi' : i < (Γ.γ e).length := hlen ▸ hi
    exact ⟨_, (hs₁ _).mp (List.getElem_mem hi'), h.ends e he i hi' hi⟩
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ((hs₁ y).mpr hy)
    have hi' : i < (Γ'.γ (σe e)).length := hlen ▸ hi
    exact ⟨_, (hs₂ _).mp (List.getElem_mem hi'), h.ends e he i hi hi'⟩

end Ends

section Boundary

variable (Γ : Painting S)

/-- **The parts of the boundary of the disc of an edge of size 3.** Two of the three ends are the
ends of
an edge of `sk(Γ)` in the boundary. -/
theorem exists_sk_boundary {c₀ : Set S} (hc₀ : c₀ ∈ Γ.E) (h3c : (tilde c₀).ncard = 3) {u₀ v₀ : S}
    (hut : u₀ ∈ tilde c₀) (hvt : v₀ ∈ tilde c₀) (huv₀ : u₀ ≠ v₀) :
    ∃ f ∈ arcComponentsIn (Γ.skU \ Γ.V), f ⊆ discBd (closure c₀) ∧ f ⊆ c₀ ∧ tilde f = {u₀, v₀} := by
  classical
  obtain ⟨hdisc, hT', -⟩ := Γ.isDisc_of_three hc₀ h3c
  have htil : ∀ {x₀ : S}, x₀ ∈ closure c₀ → x₀ ∈ Γ.V → x₀ ∈ tilde c₀ := fun hx hxV =>
    ⟨hx, fun h => Γ.disjoint_V hc₀ h hxV⟩
  have hu₀ : u₀ ∈ Γ.V := Γ.tilde_subset_V hc₀ hut
  have hv₀ : v₀ ∈ Γ.V := Γ.tilde_subset_V hc₀ hvt
  obtain ⟨w₀, hw₀, hwu, hwv⟩ : ∃ w₀ ∈ tilde c₀, w₀ ≠ u₀ ∧ w₀ ≠ v₀ := by
    by_contra hn
    push Not at hn
    have hsub : tilde c₀ ⊆ {u₀, v₀} := fun x hx => by
      by_cases hxu : x = u₀
      · exact .inl hxu
      · exact .inr (hn x hx hxu)
    have := ncard_le_ncard hsub (toFinite _)
    have h2 := ncard_pair huv₀
    omega
  have htri : tilde c₀ = {u₀, v₀, w₀} := by
    refine (eq_of_subset_of_ncard_le (s := {u₀, v₀, w₀}) ?_ ?_ (Γ.isDisc_of_three hc₀ h3c).2.2).symm
    · rintro x (rfl | rfl | rfl)
      · exact hut
      · exact hvt
      · exact hw₀
    · rw [h3c, ncard_eq_toFinset_card', Set.toFinset_insert, Set.toFinset_insert]
      simp [Finset.card_insert_of_notMem, huv₀, hwu.symm, hwv.symm]
  obtain ⟨A₁, A₂, hA₁, hA₂, hAU, hAI⟩ := hdisc.isOArc_discBd.lines (hT' hut) (hT' hvt) huv₀
  obtain ⟨A₀, hA₀, hAw, hAB⟩ : ∃ A₀, IsLineWithEnds A₀ u₀ v₀ ∧ w₀ ∉ A₀ ∧ A₀ ⊆ discBd (closure c₀)
    := by
    by_cases hw₁ : w₀ ∈ A₁
    · refine ⟨A₂, hA₂, fun hw₂ => ?_, hAU ▸ subset_union_right⟩
      have : w₀ ∈ A₁ ∩ A₂ := ⟨hw₁, hw₂⟩
      rw [hAI] at this
      rcases this with h | h
      · exact hwu h
      · exact hwv h
    · exact ⟨A₁, hA₁, hw₁, hAU ▸ subset_union_left⟩
  have hint₀ : ∀ {x}, x ∈ A₀ \ {u₀, v₀} → x ∈ c₀ ∧ x ∈ Γ.skU \ Γ.V := by
    intro x hx
    have hxB := hAB hx.1
    have hxcl : x ∈ closure c₀ := Surface.discBd_subset _ hxB
    have hxV : x ∉ Γ.V := fun h => by
      have h₁ := htil hxcl h
      rw [htri] at h₁
      rcases h₁ with h₁ | h₁ | h₁
      · exact hx.2 (.inl h₁)
      · exact hx.2 (.inr h₁)
      · exact hAw (h₁ ▸ hx.1)
    refine ⟨by_contra fun h => hxV (Γ.tilde_subset_V hc₀ ⟨hxcl, h⟩), ?_, hxV⟩
    exact Or.inr (mem_iUnion₂.2 ⟨c₀, ⟨hc₀, h3c⟩, hxB⟩)
  have hpc := isPathConnected_sdiff_pair hA₀
  obtain ⟨f, hf, hsubf⟩ := exists_arcComp_superset hpc fun x hx => (hint₀ hx).2
  obtain ⟨x₀, hx₀⟩ := hpc.nonempty
  have hx₀f := hsubf hx₀
  obtain ⟨p, q, hpq, ht, htV, hline⟩ := Γ.sk_line hf
  have hclf : A₀ ⊆ closure f := hA₀.subset_closure_diff.trans (closure_mono hsubf)
  have htf : ∀ {y}, y ∈ A₀ → y ∈ Γ.V → y ∈ tilde f := fun hy hyV =>
    ⟨hclf hy, fun h => (hf.2.1 h).2 hyV⟩
  have ht' : tilde f = {u₀, v₀} := by
    refine (eq_of_subset_of_ncard_le (s := {u₀, v₀}) ?_ ?_ (by rw [ht]; exact toFinite _)).symm
    · rintro y (rfl | rfl)
      · exact htf hA₀.left_mem hu₀
      · exact htf hA₀.right_mem hv₀
    · rw [ht, ncard_pair hpq, ncard_pair huv₀]
  rcases Γ.sk_cases hf with ⟨hfE, h2⟩ | ⟨c, hc, -, hfc, hfB⟩
  · have := arcComp_eq_of_mem hfE hc₀ hx₀f (hint₀ hx₀).1
    rw [this, h3c] at h2
    omega
  · obtain rfl := arcComp_eq_of_mem hc hc₀ (hfc hx₀f) (hint₀ hx₀).1
    exact ⟨f, hf, hfB, hfc, ht'⟩

/-- Two edges of `sk(Γ)` in the boundary of the disc of an edge of size 3, with the same ends, are
equal,
since otherwise they would form all of the boundary, which holds a third vertex. -/
theorem sk_boundary_unique {c₀ f f' : Set S} (hc₀ : c₀ ∈ Γ.E) (h3c : (tilde c₀).ncard = 3)
    (hf : f ∈ arcComponentsIn (Γ.skU \ Γ.V)) (hf' : f' ∈ arcComponentsIn (Γ.skU \ Γ.V))
    (hB : f ⊆ discBd (closure c₀)) (hB' : f' ⊆ discBd (closure c₀)) (ht : tilde f = tilde f') :
    f = f' := by
  classical
  by_contra hne
  obtain ⟨hdisc, hT', -⟩ := Γ.isDisc_of_three hc₀ h3c
  obtain ⟨u, v, huv, htu, htV, hL⟩ := Γ.sk_line hf
  obtain ⟨u', v', huv', htu', -, hL'⟩ := Γ.sk_line hf'
  have hL₂ : IsLineWithEnds (closure f') u v := by
    have hset : ({u', v'} : Set S) = {u, v} := by rw [← htu', ← ht, htu]
    have hu : u ∈ ({u', v'} : Set S) := hset ▸ .inl rfl
    have hv : v ∈ ({u', v'} : Set S) := hset ▸ .inr rfl
    rcases hu with rfl | hu
    · rcases hv with rfl | hv
      · exact absurd rfl huv
      · rw [mem_singleton_iff.mp hv]
        exact hL'
    · have hu' : u = v' := hu
      subst hu'
      rcases hv with rfl | hv
      · exact GraphMinor.GM11.IsLineWithEnds.symm hL'
      · exact absurd (mem_singleton_iff.mp hv).symm huv
  have hcap : closure f ∩ closure f' ⊆ {u, v} := by
    rintro x ⟨hx, hx'⟩
    by_cases hxf : x ∈ f
    · by_cases hxf' : x ∈ f'
      · exact absurd (arcComp_eq_of_mem hf hf' hxf hxf') hne
      · have hxt : x ∈ tilde f' := ⟨hx', hxf'⟩
        rw [← ht] at hxt
        rw [← htu]
        exact hxt
    · rw [← htu]
      exact ⟨hx, hxf⟩
  have hO := isOArc_union hL hL₂ hcap
  have hBc : IsClosed (discBd (closure c₀)) := (isCompact_of_isOArc hdisc.isOArc_discBd).isClosed
  obtain ⟨φ⟩ := id hdisc.isOArc_discBd
  have heq := oarc_eq φ hO (union_subset (closure_minimal hB hBc) (closure_minimal hB' hBc))
  obtain ⟨w₀, hw₀, hwu, hwv⟩ : ∃ w₀ ∈ tilde c₀, w₀ ≠ u ∧ w₀ ≠ v := by
    by_contra hn
    push Not at hn
    have hsub : tilde c₀ ⊆ {u, v} := fun x hx => by
      by_cases hxu : x = u
      · exact .inl hxu
      · exact .inr (hn x hx hxu)
    have := ncard_le_ncard hsub (toFinite _)
    have h2 := ncard_pair huv
    omega
  have hwV : w₀ ∈ Γ.V := Γ.tilde_subset_V hc₀ hw₀
  have hwt : ∀ {g}, g ∈ arcComponentsIn (Γ.skU \ Γ.V) → tilde g = {u, v} → w₀ ∉ closure g := by
    intro g hg htg hw
    have : w₀ ∈ tilde g := ⟨hw, fun h => (hg.2.1 h).2 hwV⟩
    rw [htg] at this
    rcases this with h | h
    · exact hwu h
    · exact hwv h
  have hwF : w₀ ∈ closure f ∪ closure f' := heq ▸ hT' hw₀
  rcases hwF with h | h
  · exact hwt hf htu h
  · exact hwt hf' (ht ▸ htu) h

end Boundary

end GraphMinor.GM19
