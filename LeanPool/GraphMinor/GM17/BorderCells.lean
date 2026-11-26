/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.BorderArc

/-!
# Curves around border cells

Here we prove the parts of `RegionBoundaryOArcCriterionStatement` on border cells, which are used in
(8.4), (8.6) and (8.7) of Graph Minors XVII (pages 182 and 183). Two border
cells with the same nodes are pushed off along their outer sides to a normal `O`-arc (`two_border`).
A node with only border cells at it has exactly two cells. We paste a disc on the
cuff, add these two cells to it, and take a thin disc along the two outer sides, which gives a
normal `I`-arc past the node (`border_node`). In both cases a disc that bounds the curve
and misses the other nodes would fill up the surface, so there would be too few nodes.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

namespace Painting

variable {Γ : Painting S} [T2Space S]

/-- The outer side of a border cell. -/
theorem border_side (hS : IsSurface S) {c : Set S} (hc : c ∈ Γ.C) (hbd : (c ∩ bd S).Nonempty) :
    ∃ u v O, tilde c = {u, v} ∧ IsLineWithEnds (closure c ∩ bd S) u v ∧ Γ.IsSide c O u v ∧ discBd
      (closure c) = (closure c ∩ bd S) ∪ O ∧ (closure c ∩ bd S) ∩ O = {u, v} ∧ u ∈ bd S ∧ v ∈ bd S
      ∧ c ∩ bd S = (closure c ∩ bd S) \ {u, v} := by
  obtain ⟨u, v, -, ht, hB, he, hu, hv⟩ := Γ.border_cell_exists_ends hc hbd
  have hdisc := Γ.isClosedDisc_closure_cell hc
  have hBs : closure c ∩ bd S ⊆ discBd (closure c) := fun x hx => by
    by_contra hn
    exact hx.2 (isInteriorPoint_of_mem_discInt hS.2.2 hdisc ⟨hx.1, hn⟩)
  obtain ⟨B', hB', hun, hin⟩ := oarc_split hdisc.isOArc_discBd hB hBs
  have hB'c : B' ⊆ closure c := (hun ▸ subset_union_right : B' ⊆ _).trans (discBd_subset _)
  refine ⟨u, v, B', ht, hB, ⟨⟨hc, hB', hun ▸ subset_union_right, ?_⟩, ?_⟩, hun.symm, hin, hu.2,
    hv.2, he⟩
  · rw [← ht, ← Γ.closure_cell_inter_N hc]
    apply subset_antisymm
    · exact fun z hz => ⟨hB'c hz.1, hz.2⟩
    · intro z hz
      have h1 : z ∈ tilde c := by
        rw [← Γ.closure_cell_inter_N hc]
        exact hz
      rw [ht] at h1
      rcases h1 with rfl | rfl
      · exact ⟨hB'.left_mem, hz.2⟩
      · exact ⟨hB'.right_mem, hz.2⟩
  · refine disjoint_left.mpr fun x hx hxb => hx.2 ?_
    have h1 : x ∈ (closure c ∩ bd S) ∩ B' := ⟨⟨hB'c hx.1, hxb⟩, hx.1⟩
    rwa [hin] at h1

omit [T2Space S] in
/-- The closure of a border cell with a strip along its outer side is a neighbourhood of its points
off the nodes. -/
theorem border_nhds (hS : IsSurface S) {c O St : Set S} {u v x : S} (hc : c ∈ Γ.C) (ht : tilde c
  = {u, v}) (hB : IsLineWithEnds (closure c ∩ bd S) u v)
    (hb : discBd (closure c) = (closure c ∩ bd S) ∪ O)
    (hnb : ∀ x ∈ O, x ≠ u → x ≠ v → closure c ∪ St ∈ 𝓝 x) (hx : x ∈ closure c)
      (hxt : x ∉ tilde c) : closure c ∪ St ∈ 𝓝 x := by
  have hdisc := Γ.isClosedDisc_closure_cell hc
  have hxu : x ≠ u := fun e => hxt (ht ▸ .inl e)
  have hxv : x ≠ v := fun e => hxt (ht ▸ .inr e)
  by_cases hxb : x ∈ discBd (closure c)
  · rcases (hb ▸ hxb : x ∈ (closure c ∩ bd S) ∪ O) with h | h
    · exact Filter.mem_of_superset (disc_nhds hS hdisc hB (hb ▸ subset_union_left) rfl h hxu hxv)
        subset_union_left
    · exact hnb x h hxu hxv
  · exact Filter.mem_of_superset ((hdisc.isOpen_discInt hS.2.2).mem_nhds ⟨hx,
      hxb⟩) fun y hy => .inl hy.1

/-- Two border cells with the same nodes are pushed off along their outer sides to a normal `O`-arc
that bounds no disc without other nodes. -/
theorem two_border [ConnectedSpace S] (hS : IsSurface S) (hΓ : Γ.Tame) {c₁ c₂ : Set S}
  (h₁ : c₁ ∈ Γ.C) (h₂ : c₂ ∈ Γ.C) (hne : c₁ ≠ c₂) (hb₁ : (c₁ ∩ bd S).Nonempty)
    (hb₂ : (c₂ ∩ bd S).Nonempty) (he : tilde c₁ = tilde c₂) :
    ∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧ (F ∩ Γ.N).ncard = 2 ∧ ∀ Δ : Set S, IsClosedDisc Δ
      → discBd Δ = F → ¬ (Δ ∩ Γ.N ⊆ F) := by
  classical
  have hcS : CompactSpace S := hS.1
  have hman := hS.2.2
  obtain ⟨u, v, O₁, ht₁, hB₁, hs₁, hd₁, hi₁, hu, hv, hc₁⟩ := border_side hS h₁ hb₁
  obtain ⟨u', v', O₂', ht₂, hB₂', hs₂', hd₂', hi₂', -, -, hc₂'⟩ := border_side hS h₂ hb₂
  have hpair : ({u', v'} : Set S) = {u, v} := by rw [← ht₂, ← he, ht₁]
  obtain ⟨O₂, hs₂, hB₂, hd₂, hi₂, hc₂⟩ : ∃ O₂, Γ.IsSide c₂ O₂ u v ∧ IsLineWithEnds
    (closure c₂ ∩ bd S) u v ∧ discBd (closure c₂) = (closure c₂ ∩ bd S) ∪ O₂ ∧
      (closure c₂ ∩ bd S) ∩ O₂ = {u, v} ∧ c₂ ∩ bd S = (closure c₂ ∩ bd S) \ {u, v} := by
    have huv' := hB₂'.ne'
    rcases (Set.ext_iff.mp hpair u').mp (.inl rfl) with rfl | rfl
    · have : v' = v := by
        rcases (Set.ext_iff.mp hpair v').mp (.inr rfl) with h | h
        · exact absurd h.symm huv'
        · exact h
      subst this
      exact ⟨O₂', hs₂', hB₂', hd₂', hi₂', hc₂'⟩
    · have : v' = u := by
        rcases (Set.ext_iff.mp hpair v').mp (.inr rfl) with h | h
        · exact h
        · exact absurd h.symm huv'
      subst this
      refine ⟨O₂', hs₂'.symm, hB₂'.symm, hd₂', ?_, ?_⟩
      · rw [pair_comm]
        exact hi₂'
      · rw [pair_comm]
        exact hc₂'
  have huv := hB₁.ne'
  obtain ⟨St₁, γ₁, r₁, hSt₁, hγ₁, hbS₁, hiS₁, -, -, hU₁, -, -, -, hnb₁⟩
    := side_strip hS hΓ.isOpen hs₁ isClosed_empty (by simp)
  have hA : St₁ ∩ O₂ ⊆ {u, v} := by
    rintro z ⟨hz, hz'⟩
    have hzO₁ := hU₁ ⟨hz, hs₂.1.subset_U hz'⟩
    by_cases hzN : z ∈ Γ.N
    · exact hs₂.1.2.2.2.le ⟨hz', hzN⟩
    · exact absurd (hs₁.1.unique hs₂.1 hzO₁ hz' hzN).1 hne
  obtain ⟨St₂, γ₂, r₂, hSt₂, hγ₂, hbS₂, hiS₂, -, hSA, hU₂, -, -, -, hnb₂⟩
    := side_strip hS hΓ.isOpen hs₂ hSt₁.isClosed hA
  have hγS₁ : γ₁ ⊆ St₁ := (hbS₁ ▸ subset_union_right).trans (discBd_subset St₁)
  have hγS₂ : γ₂ ⊆ St₂ := (hbS₂ ▸ subset_union_right).trans (discBd_subset St₂)
  have hii : γ₁ ∩ γ₂ = {u, v} := by
    apply subset_antisymm
    · exact fun z hz => hSA ⟨hγS₂ hz.2, hγS₁ hz.1⟩
    · rintro z (rfl | rfl)
      · exact ⟨hγ₁.left_mem, hγ₂.left_mem⟩
      · exact ⟨hγ₁.right_mem, hγ₂.right_mem⟩
  have hUF : ∀ {z}, z ∈ γ₁ ∪ γ₂ → z ∈ Γ.U → z = u ∨ z = v := by
    rintro z (h | h) hzU
    · exact hiS₁.le ⟨hU₁ ⟨hγS₁ h, hzU⟩, h⟩
    · exact hiS₂.le ⟨hU₂ ⟨hγS₂ h, hzU⟩, h⟩
  have huN := hs₁.1.left_mem_N
  have hvN := hs₁.1.right_mem_N
  have hFN : (γ₁ ∪ γ₂) ∩ Γ.N = {u, v} := by
    apply subset_antisymm
    · exact fun z hz => hUF hz.1 (Γ.N_subset hz.2)
    · rintro z (rfl | rfl)
      · exact ⟨.inl hγ₁.left_mem, huN⟩
      · exact ⟨.inl hγ₁.right_mem, hvN⟩
  have hnorm : Γ.IsNormal (γ₁ ∪ γ₂) := fun z hz => by
    rcases hUF hz.1 hz.2 with rfl | rfl
    · exact huN
    · exact hvN
  refine ⟨γ₁ ∪ γ₂, oArc_of_lines hγ₁ hγ₂ hii, hnorm, by rw [hFN, Set.ncard_pair huv],
    fun Δ hΔ hbΔ hN => ?_⟩
  have hnbΔ : ∀ x ∈ Δ, x ∉ γ₁ ∪ γ₂ → Δ ∈ 𝓝 x := fun x hx hxF =>
    Filter.mem_of_superset ((hΔ.isOpen_discInt hman).mem_nhds ⟨hx, fun h => hxF
      (hbΔ ▸ h)⟩) fun y hy => hy.1
  have hoff : ∀ {c}, c ∈ Γ.C → (c ∩ bd S).Nonempty → c ⊆ Δᶜ := fun {c} hc hb => by
    rcases cell_side hc hnorm hΔ (fun y hy => hnbΔ y hy.1 hy.2) with h | h
    · exfalso
      obtain ⟨x, hx, hxb⟩ := hb
      have hxF : x ∉ γ₁ ∪ γ₂ := fun hF => disjoint_left.mp (Γ.cell_disjoint_N hc) hx
        (hnorm ⟨hF, Γ.cell_subset_U hc hx⟩)
      exact hxb (isInteriorPoint_of_mem_discInt hman hΔ ⟨h hx, fun h' => hxF (hbΔ ▸ h')⟩)
    · exact h
  have hStΔ : ∀ {St O γ c γ' : Set S}, IsClosedDisc St → discBd St = O ∪ γ → γ' ∩ St ⊆ γ
    → IsLineWithEnds O u v → O ∩ γ = {u, v} → (∀ x ∈ O, x ≠ u → x ≠ v → x ∈ c) →
      c ⊆ Δᶜ → γ ∪ γ' = γ₁ ∪ γ₂ → St ∩ Δ = γ := by
    intro St O γ c γ' hSt hbS hγ' hO hiO hmem hcoff hun
    apply subset_antisymm
    · have hY := isPreconnected_disc_diff hSt (L := γ) (hbS ▸ subset_union_right)
      have hd : Disjoint (St \ γ) (discBd Δ) := by
        rw [hbΔ, ← hun]
        refine disjoint_left.mpr fun y hy hy' => hy'.elim hy.2 fun h => hy.2 (hγ' ⟨h, hy.1⟩)
      rcases hΔ.side hman hY hd with h | h
      · exfalso
        obtain ⟨z, hz, h3, h4, -⟩ := exists_inner hO (finite_empty (α := S))
        have hzF : z ∉ γ := fun h5 => by
          rcases (hiO ▸ ⟨hz, h5⟩ : z ∈ ({u, v} : Set S)) with e | e
          · exact h3 e
          · exact h4 e
        exact hcoff (hmem z hz h3 h4) (h ⟨discBd_subset St (hbS ▸ .inl hz), hzF⟩).1
      · rintro y ⟨hy, hy'⟩
        by_contra hn
        exact disjoint_left.mp h ⟨hy, hn⟩ hy'
    · intro x hx
      have hxS : x ∈ St := discBd_subset St (hbS ▸ .inr hx)
      exact ⟨hxS, discBd_subset Δ (hbΔ ▸ hun ▸ .inl hx)⟩
  have hS₁Δ : St₁ ∩ Δ = γ₁ := hStΔ hSt₁ hbS₁ (γ' := γ₂) (fun z hz => by
    rcases hSA ⟨hγS₂ hz.1, hz.2⟩ with rfl | rfl
    · exact hγ₁.left_mem
    · exact hγ₁.right_mem) hs₁.1.2.1 hiS₁ (fun x hx h3 h4 => hs₁.1.mem_cell hx h3 h4)
        (hoff h₁ hb₁) rfl
  have hS₂Δ : St₂ ∩ Δ = γ₂ := hStΔ hSt₂ hbS₂ (γ' := γ₁) (fun z hz => by
    rcases hSA ⟨hz.2, hγS₁ hz.1⟩ with rfl | rfl
    · exact hγ₂.left_mem
    · exact hγ₂.right_mem) hs₂.1.2.1 hiS₂ (fun x hx h3 h4 => hs₂.1.mem_cell hx h3 h4) (hoff h₂ hb₂)
        (union_comm _ _)
  let W : Set S := Δ ∪ (closure c₁ ∪ St₁) ∪ (closure c₂ ∪ St₂)
  have hWc : IsClosed W := (hΔ.isClosed.union (isClosed_closure.union hSt₁.isClosed)).union
    (isClosed_closure.union hSt₂.isClosed)
  have hA' : ({u, v} : Set S).Finite := toFinite _
  have hl₁ : closure c₁ ∪ St₁ ⊆ W := fun z hz => .inl (.inr hz)
  have hl₂ : closure c₂ ∪ St₂ ⊆ W := fun z hz => .inr hz
  have hlΔ : Δ ⊆ W := fun z hz => .inl (.inl hz)
  have hγnb : ∀ {x}, x ∈ γ₁ ∪ γ₂ → x ∉ ({u, v} : Set S) → W ∈ 𝓝 x := by
    rintro x (h | h) hxA
    · have hF : γ₁ ⊆ discBd Δ := hbΔ ▸ subset_union_left
      refine Filter.mem_of_superset (union_nhds hman hSt₁ hΔ hγ₁ hS₁Δ
        (hbS₁ ▸ subset_union_right) hF h (fun e => hxA (.inl e)) (fun e => hxA (.inr e))) ?_
      exact union_subset (subset_union_right.trans hl₁) hlΔ
    · have hF : γ₂ ⊆ discBd Δ := hbΔ ▸ subset_union_right
      refine Filter.mem_of_superset (union_nhds hman hSt₂ hΔ hγ₂ hS₂Δ
        (hbS₂ ▸ subset_union_right) hF h (fun e => hxA (.inl e)) (fun e => hxA (.inr e))) ?_
      exact union_subset (subset_union_right.trans hl₂) hlΔ
  have hStnb : ∀ {St O γ c : Set S}, IsClosedDisc St → discBd St = O ∪ γ → γ ⊆ γ₁ ∪ γ₂
    → closure c ∪ St ⊆ W → tilde c = {u, v} → (∀ x ∈ O, x ≠ u → x ≠ v → closure c ∪ St ∈ 𝓝 x) →
      ∀ x ∈ St, x ∉ ({u, v} : Set S) → W ∈ 𝓝 x := by
    intro St O γ c hSt hbS hγ hsub ht hnb x hx hxA
    by_cases hxO : x ∈ O
    · exact Filter.mem_of_superset (hnb x hxO (fun e => hxA (.inl e)) (fun e => hxA (.inr e))) hsub
    · by_cases hxγ : x ∈ γ
      · exact hγnb (hγ hxγ) hxA
      · refine Filter.mem_of_superset ((hSt.isOpen_discInt hman).mem_nhds ⟨hx,
          fun h => (hbS ▸ h : x ∈ O ∪ γ).elim hxO hxγ⟩) fun y hy => hsub (.inr hy.1)
  have hnbW : ∀ x ∈ W, x ∉ ({u, v} : Set S) → W ∈ 𝓝 x := by
    rintro x ((h | (h | h)) | (h | h)) hxA
    · by_cases hxF : x ∈ γ₁ ∪ γ₂
      · exact hγnb hxF hxA
      · exact Filter.mem_of_superset (hnbΔ x h hxF) hlΔ
    · have hx' : x ∉ tilde c₁ := ht₁.symm ▸ hxA
      exact Filter.mem_of_superset (border_nhds hS h₁ ht₁ hB₁ hd₁ hnb₁ h hx') hl₁
    · exact hStnb hSt₁ hbS₁ subset_union_left hl₁ ht₁ hnb₁ x h hxA
    · have ht₂ := he ▸ ht₁
      have hx' : x ∉ tilde c₂ := ht₂.symm ▸ hxA
      exact Filter.mem_of_superset (border_nhds hS h₂ ht₂ hB₂ hd₂ hnb₂ h hx') hl₂
    · exact hStnb hSt₂ hbS₂ subset_union_right hl₂ (he ▸ ht₁) hnb₂ x h hxA
  obtain ⟨z, hz⟩ := arcComponentsIn_nonempty h₁
  have hWne : (W \ {u, v}).Nonempty := ⟨z, hl₁ (.inl (subset_closure hz)), fun h
    => disjoint_left.mp (Γ.cell_disjoint_N h₁) hz (h.elim (fun e => e ▸ huN) (fun e => e ▸ hvN))⟩
  refine hΓ.not_covered hA' ((Set.ncard_pair huv).le.trans (by norm_num)) fun n hn => ?_
  by_contra hnt
  rcases cover_off hman hWc hA' hWne hnbW hnt with (h | (h | h)) | (h | h)
  · exact hnt (hFN ▸ ⟨hN ⟨h, hn⟩, hn⟩)
  · exact hnt (ht₁ ▸ Γ.closure_cell_inter_N h₁ ▸ ⟨h, hn⟩)
  · exact hnt (hs₁.1.2.2.2 ▸ ⟨hU₁ ⟨h, Γ.N_subset hn⟩, hn⟩)
  · exact hnt (ht₁ ▸ he ▸ Γ.closure_cell_inter_N h₂ ▸ ⟨h, hn⟩)
  · exact hnt (hs₂.1.2.2.2 ▸ ⟨hU₂ ⟨h, Γ.N_subset hn⟩, hn⟩)

end Painting

end GraphMinor.GM17
