/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.CliqueChord
public import LeanPool.GraphMinor.GM17.CellPartitionSystem

/-!
# One chord for each pair of a clique of nodes

This file builds the graph used in Claim (1) of the proof of (12.2) of Graph Minors XVII (page 198).
Let `M` be a set of nodes in which every two nodes lie on a common cell. The paper joins each pair
by an arc of `bd(cBar)`. Such an arc lies in `U(Γ)`, so a cycle of them is not `Γ`-normal. We push
each arc into the region beside it (`exists_chords`), which gives lines with the same ends that are
`Γ`-normal, and that are still disjoint off their ends.

Each chord has two sides near each of its inner points (`IsChordSide`). This is what we use in place
of "`H` is drawn in `Σ`".
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface Painting

variable {S : Type} [TopologicalSpace S] [T2Space S] {Γ : Painting S}

/-- Two nodes of a cell are the ends of a side of it. A cell has at most three nodes, so the two
nodes are consecutive on one of the two lines between them. A border cell has two nodes, and only
one of its two lines lies on the cuff. -/
theorem exists_side_pair [ConnectedSpace S] (hS : IsSurface S) (h : CellHyps Γ) {c : Set S} {a b :
  S} (hc : c ∈ Γ.C) (ha : a ∈ tilde c) (hb : b ∈ tilde c) (hab : a ≠ b) :
    ∃ L r, Γ.IsSide c L a b ∧ r ∈ Γ.regions ∧ L ⊆ closure r := by
  have hcS : CompactSpace S := hS.1
  have hfin := Γ.finite_tilde_cell hc
  have hO := (Γ.isClosedDisc_closure_cell hc).isOArc_discBd
  obtain ⟨A, B, hA, hB, hu, hi⟩ := hO.lines (Γ.tilde_subset_discBd hc ha)
    (Γ.tilde_subset_discBd hc hb) hab
  have hAs : A ⊆ discBd (closure c) := hu ▸ subset_union_left
  have hBs : B ⊆ discBd (closure c) := hu ▸ subset_union_right
  have hgap : ∀ X, IsLineWithEnds X a b → X ⊆ discBd (closure c) → (∀ x ∈ tilde c, x ∈ X → x = a
    ∨ x = b) → Γ.IsGap c X a b := fun X hX hs ht => by
    refine ⟨hc, hX, hs, ?_⟩
    ext x
    constructor
    · rintro ⟨hx, hxN⟩
      have : x ∈ tilde c := by
        rw [← Γ.closure_cell_inter_N hc]
        exact ⟨discBd_subset _ (hs hx), hxN⟩
      exact ht x this hx
    · rintro (rfl | rfl)
      · exact ⟨hX.left_mem, Γ.tilde_subset_N hc ha⟩
      · exact ⟨hX.right_mem, Γ.tilde_subset_N hc hb⟩
  have hside : ∃ L, Γ.IsSide c L a b := by
    by_cases hbd : (c ∩ bd S).Nonempty
    · have h2 : tilde c = {a, b} := by
        have hsub : ({a, b} : Set S) ⊆ tilde c := by
          rintro x (rfl | rfl) <;> assumption
        exact (eq_of_subset_of_ncard_le hsub (by rw [ncard_pair hab,
          (Γ.border_cell c hc hbd).1]) hfin).symm
      have ht : ∀ X : Set S, ∀ x ∈ tilde c, x ∈ X → x = a ∨ x = b := fun X x hx _ => by
        rw [h2] at hx
        exact hx
      have gA := hgap A hA hAs (ht A)
      have gB := hgap B hB hBs (ht B)
      rcases gap_or_border hS gA with h1 | h1
      · exact ⟨A, h1⟩
      rcases gap_or_border hS gB with h3 | h3
      · exact ⟨B, h3⟩
      exfalso
      have hAB : A = B := h1.trans h3.symm
      obtain ⟨z, hz, hza, hzb, -⟩ := exists_inner hA (finite_empty (α := S))
      have : z ∈ A ∩ B := ⟨hz, hAB ▸ hz⟩
      rw [hi] at this
      exact this.elim hza hzb
    · have hgapX : ∃ X, Γ.IsGap c X a b := by
        by_cases hx : ∃ x ∈ tilde c, x ∈ A ∧ x ≠ a ∧ x ≠ b
        · obtain ⟨x, hxt, hxA, hxa, hxb⟩ := hx
          refine ⟨B, hgap B hB hBs fun y hy hyB => ?_⟩
          by_contra hn
          push Not at hn
          have hyA : y ∉ A := fun hyA => by
            have : y ∈ A ∩ B := ⟨hyA, hyB⟩
            rw [hi] at this
            exact this.elim hn.1 hn.2
          have hxy : x ≠ y := fun e => hyA (e ▸ hxA)
          have h3 : ({a, b, x, y} : Set S) ⊆ tilde c := by
            rintro z (rfl | rfl | rfl | rfl) <;> assumption
          have hcard : ({a, b, x, y} : Set S).ncard = 4 := by
            rw [ncard_insert_of_notMem (by simp [hab, hxa.symm, hn.1.symm]) (by simp),
              ncard_insert_of_notMem (by simp [hxb.symm, hn.2.symm]) (by simp), ncard_pair hxy]
          have := ncard_le_ncard h3 hfin
          have := Γ.ncard_tilde_cell_le hc
          omega
        · push Not at hx
          exact ⟨A, hgap A hA hAs fun y hy hyA => by
            by_contra hn
            push Not at hn
            exact hn.2 (hx y hy hyA hn.1)⟩
      obtain ⟨X, hX⟩ := hgapX
      rcases gap_or_border hS hX with h1 | h1
      · exact ⟨X, h1⟩
      · exfalso
        obtain ⟨z, hz, hza, hzb, -⟩ := exists_inner hX.2.1 (finite_empty (α := S))
        exact hbd ⟨z, hX.mem_cell hz hza hzb, (h1 ▸ hz : z ∈ closure c ∩ bd S).2⟩
  obtain ⟨L, hL⟩ := hside
  obtain ⟨-, -, r, -, -, -, -, -, -, -, hr, -, hLr, -⟩ := side_strip hS h.hopen hL isClosed_empty
    (by simp)
  exact ⟨L, r, hL, hr, hLr⟩

/-- Near the inner point `x` of the chord `E`, the surface is cut by `E` into two sides `A`, `B`,
which are off all the chords in `𝓔`. -/
def IsChordSide (E : Set S) (𝓔 : Set (Set S)) (x : S) : Prop :=
  ∃ V A B, IsOpen V ∧ x ∈ V ∧ V ⊆ A ∪ B ∪ E ∧ IsPreconnected A ∧ IsPreconnected B ∧ x ∈ closure A
    ∧ ∀ E' ∈ 𝓔, Disjoint A E' ∧ Disjoint B E'

omit [T2Space S] in
theorem region_inter_N {r : Set S} (hr : r ∈ Γ.regions) : Disjoint r Γ.N :=
  disjoint_left.mpr fun _ hx hx' => (arcComponentsIn_subset hr hx).2 (Γ.N_subset hx')

omit [TopologicalSpace S] [T2Space S] in
private theorem finite_node_pairs {M : Set S} (hfin : M.Finite) :
    {p | ∃ a ∈ M, ∃ b ∈ M, a ≠ b ∧ p = ({a, b} : Set S)}.Finite := by
  refine ((hfin.prod hfin).image fun t : S × S => ({t.1, t.2} : Set S)).subset ?_
  rintro p ⟨a, ha, b, hb, -, rfl⟩
  exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

/-- One chord for each pair of a clique of nodes. Each is a line with the ends of the pair, its
inner points lie in a region, chords are disjoint off their ends, and each has two sides at each
inner point. -/
theorem exists_chords [ConnectedSpace S] (hS : IsSurface S) (h : CellHyps Γ) {M : Set S}
  (hM : M ⊆ Γ.N) (hne : M.Nonempty)
    (hadj : ∀ a ∈ M, ∀ b ∈ M, a ≠ b → ∃ c ∈ Γ.C, a ∈ tilde c ∧ b ∈ tilde c) :
    ∃ L : Set S → Set S, ∀ 𝓟 : Set (Set S), 𝓟 = {p | ∃ a ∈ M, ∃ b ∈ M, a ≠ b ∧ p = {a, b}} →
      (∀ a ∈ M, ∀ b ∈ M, a ≠ b → IsLineWithEnds (L {a, b}) a b) ∧
      (∀ p ∈ 𝓟, ∃ r ∈ Γ.regions, L p \ p ⊆ r ∧ ∀ x ∈ L p \ p, IsChordSide (L p) (L '' 𝓟) x) ∧
      (∀ p ∈ 𝓟, ∀ q ∈ 𝓟, p ≠ q → Disjoint (L p \ p) (L q)) := by
  classical
  have hcS : CompactSpace S := hS.1
  have hman := hS.2.2
  obtain ⟨m, hm⟩ := hne
  have : Nonempty S := ⟨m⟩
  have hfinM : M.Finite := Γ.finite_N.subset hM
  let P : Set (Set S) := {p | ∃ a ∈ M, ∃ b ∈ M, a ≠ b ∧ p = {a, b}}
  have hPfin : P.Finite := finite_node_pairs hfinM
  have hdata : ∀ p ∈ P, ∃ (a b : S) (G r c : Set S), p = {a, b} ∧ a ≠ b ∧ a ∈ M ∧ b ∈ M
    ∧ Γ.IsSide c G a b ∧ r ∈ Γ.regions ∧ G ⊆ closure r := by
    rintro p ⟨a, ha, b, hb, hab, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hadj a ha b hb hab
    obtain ⟨G, r, hG, hr, hGr⟩ := exists_side_pair hS h hc hac hbc hab
    exact ⟨a, b, G, r, c, rfl, hab, ha, hb, hG, hr, hGr⟩
  choose! A B G rg cl hpe hab haM hbM hside hrg hGr using hdata
  have hdisc : ∀ r ∈ Γ.regions, IsClosedDisc (closure r) ∧ discBd (closure r) = closure r \ r
    := fun r hr =>
    region_disc hS (fun r hr => (h.hreg r hr).1) hr (h.hreg r hr).2
  have hGD : ∀ p ∈ P, G p ⊆ discBd (closure (rg p)) := fun p hp x hx => by
    rw [(hdisc _ (hrg p hp)).2]
    exact ⟨hGr p hp hx, fun hxr => (arcComponentsIn_subset (hrg p hp) hxr).2
      ((hside p hp).1.subset_U hx)⟩
  have hsys : ∀ r ∈ Γ.regions, ∃ R Ch Cap, ChordSys (closure r) (hPfin.toFinset.filter fun p
    => rg p = r) G A B R Ch Cap := fun r hr => by
    refine chords_in_disc hman (hdisc r hr).1 _ (fun p hp => ?_) (fun p hp => ?_) (fun p hp
      => ?_) fun p hp q hq hpq => ?_
    · have := Finset.mem_filter.1 hp
      exact (hside p (by simpa using this.1)).1.2.1
    · have h1 := Finset.mem_filter.1 hp
      have := hGD p (by simpa using h1.1)
      rwa [h1.2] at this
    · exact hab p (by simpa using (Finset.mem_filter.1 hp).1)
    · have hpP : p ∈ P := by simpa using (Finset.mem_filter.1 hp).1
      have hqP : q ∈ P := by simpa using (Finset.mem_filter.1 hq).1
      rintro x ⟨hxp, hxq⟩
      by_cases hxN : x ∈ Γ.N
      · have h1 : x ∈ G p ∩ Γ.N := ⟨hxp, hxN⟩
        have h2 : x ∈ G q ∩ Γ.N := ⟨hxq, hxN⟩
        rw [(hside p hpP).1.2.2.2] at h1
        rw [(hside q hqP).1.2.2.2] at h2
        exact ⟨h1, h2⟩
      · exfalso
        obtain ⟨-, hGpq⟩ := (hside p hpP).1.unique (hside q hqP).1 hxp hxq hxN
        apply hpq
        have e1 := (hside p hpP).1.2.2.2
        have e2 := (hside q hqP).1.2.2.2
        rw [hpe p hpP, hpe q hqP, ← e1, ← e2, hGpq]
  choose! Rr Ch Cap hs using hsys
  let s : Set S → Finset (Set S) := fun r => hPfin.toFinset.filter fun p => rg p = r
  have hmem : ∀ p ∈ P, p ∈ s (rg p) := fun p hp => Finset.mem_filter.2 ⟨by simpa using hp, rfl⟩
  have hmem' : ∀ {p r}, p ∈ s r → p ∈ P ∧ rg p = r := fun {p r} hp => by
    have := Finset.mem_filter.1 hp
    exact ⟨by simpa using this.1, this.2⟩
  let L : Set S → Set S := fun p => Ch (rg p) p
  let C : Set S → Set S := fun p => Cap (rg p) p
  have hsp : ∀ p ∈ P, ChordSys (closure (rg p)) (s (rg p)) G A B (Rr (rg p)) (Ch (rg p)) (Cap
    (rg p)) := fun p hp => hs _ (hrg p hp)
  have hLC : ∀ p ∈ P, L p ⊆ C p := fun p hp x hx => by
    have : x ∈ Cap (rg p) p ∩ Rr (rg p) := by
      rw [(hsp p hp).capR p (hmem p hp)]
      exact hx
    exact this.1
  have hRD : ∀ r ∈ Γ.regions, Rr r ⊆ closure r := fun r hr => by
    have := (hs r hr).cover
    intro x hx
    rw [this]
    exact .inl hx
  have hCD : ∀ p ∈ P, C p ⊆ closure (rg p) := fun p hp x hx => by
    rw [(hsp p hp).cover]
    exact .inr (mem_biUnion (hmem p hp) hx)
  have hLe : ∀ p ∈ P, p = {A p, B p} := hpe
  have hLl : ∀ p ∈ P, IsLineWithEnds (L p) (A p) (B p) := fun p hp => (hsp p hp).line p (hmem p hp)
  have hinner : ∀ p ∈ P, L p \ p ⊆ rg p := fun p hp x hx => by
    have hxD : x ∈ closure (rg p) := hCD p hp (hLC p hp hx.1)
    by_contra hn
    have hb : x ∈ discBd (closure (rg p)) := by
      rw [(hdisc _ (hrg p hp)).2]
      exact ⟨hxD, hn⟩
    have h1 := (hsp p hp).capD p (hmem p hp) ⟨hLC p hp hx.1, hb⟩
    have h2 : x ∈ G p ∩ Ch (rg p) p := ⟨h1, hx.1⟩
    rw [(hsp p hp).inter p (hmem p hp)] at h2
    exact hx.2 (by rw [hpe p hp]; exact h2)
  have hNp : ∀ p ∈ P, p ⊆ Γ.N := fun p hp x hx => by
    rw [hpe p hp] at hx
    rcases hx with rfl | rfl
    · exact hM (haM p hp)
    · exact hM (hbM p hp)
  have hoff : ∀ p ∈ P, ∀ q ∈ P, rg p ≠ rg q → Disjoint (rg p) (L q) := fun p hp q hq hr
    => disjoint_left.mpr fun x hx hxq => by
    by_cases hxp : x ∈ q
    · exact disjoint_left.mp (region_inter_N (hrg p hp)) hx (hNp q hq hxp)
    · exact hr (region_eq (hrg p hp) (hrg q hq) hx (hinner q hq ⟨hxq, hxp⟩))
  have hsame : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → rg p = rg q → C p ∩ C q ⊆ p := fun p hp q hq hpq hr => by
    have hq' : q ∈ s (rg p) := by rw [hr]; exact hmem q hq
    have := (hsp p hp).pair p (hmem p hp) q hq' hpq
    intro x hx
    have hx' : x ∈ Cap (rg p) p ∩ Cap (rg p) q := ⟨hx.1, by have := hx.2; simpa only [C, hr] using
      this⟩
    rw [hpe p hp]
    exact (this hx').1
  have hdj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint (L p \ p) (L q) := fun p hp q hq hpq
    => disjoint_left.mpr fun x hx hxq => by
    by_cases hr : rg p = rg q
    · exact hx.2 (hsame p hp q hq hpq hr ⟨hLC p hp hx.1, hLC q hq hxq⟩)
    · exact disjoint_left.mp (hoff p hp q hq hr) (hinner p hp hx) hxq
  refine ⟨L, fun 𝓟 h𝓟 => ?_⟩
  obtain rfl : 𝓟 = P := h𝓟
  refine ⟨fun a ha b hb hne' => ?_, fun p hp => ⟨rg p, hrg p hp, hinner p hp, fun x hx => ?_⟩, hdj⟩
  · have hp : ({a, b} : Set S) ∈ P := ⟨a, ha, b, hb, hne', rfl⟩
    have h1 := hLl _ hp
    have h2 := hpe _ hp
    have hA : A {a, b} = a ∨ A {a, b} = b := (Set.ext_iff.1 h2 _).2 (Or.inl rfl)
    have hB : B {a, b} = a ∨ B {a, b} = b := (Set.ext_iff.1 h2 _).2 (Or.inr rfl)
    have hne2 := hab _ hp
    rcases hA with e1 | e1 <;> rcases hB with e2 | e2
    · exact absurd (e1.trans e2.symm) hne2
    · rwa [e1, e2] at h1
    · rw [e1, e2] at h1
      exact h1.symm
    · exact absurd (e1.trans e2.symm) hne2
  · have hsysp := hsp p hp
    have hmp := hmem p hp
    have hr := hrg p hp
    have hDb := (hdisc _ hr).2
    let r := rg p
    have hdiscInt : ∀ Y, IsClosedDisc Y → Y ⊆ closure r → discInt Y ⊆ r := fun Y hY hYs x hx => by
      have := discInt_mono hman hY hYs hx
      by_contra hn
      exact this.2 (by rw [hDb]; exact ⟨this.1, hn⟩)
    have hAoff : ∀ q ∈ P, Disjoint (discInt (C p)) (L q) := fun q hq => disjoint_left.mpr fun y hy
      hyq => by
      by_cases he : q = p
      · subst he
        exact hy.2 (by rw [hsysp.capb q hmp]; exact .inr hyq)
      by_cases hre : rg p = rg q
      · have h3 := hsame p hp q hq (Ne.symm he) hre ⟨hy.1, hLC q hq hyq⟩
        have h4 : y ∈ L p := by
          rw [hpe p hp] at h3
          rcases h3 with rfl | rfl
          · exact (hLl p hp).left_mem
          · exact (hLl p hp).right_mem
        exact hy.2 (by rw [hsysp.capb p hmp]; exact .inr h4)
      · exact disjoint_left.mp (hoff p hp q hq hre) (hdiscInt _ (hsysp.cap p hmp) (hCD p hp) hy) hyq
    have hBoff : ∀ q ∈ P, Disjoint (discInt (Rr r)) (L q) := fun q hq
      => disjoint_left.mpr fun y hy hyq => by
      by_cases hre : rg p = rg q
      · have h2 : L q ⊆ discBd (Rr r) := by
          have := (hs (rg q) (hrg q hq)).chR q (hmem q hq)
          simpa only [r, hre] using this
        exact hy.2 (h2 hyq)
      · exact disjoint_left.mp (hoff p hp q hq hre) (hdiscInt _ hsysp.hR (hRD r hr) hy) hyq
    let W : Set S := ⋃ q ∈ (s r).erase p, Cap r q
    have hWc : IsClosed W := isClosed_biUnion_finset fun q hq => (hsysp.cap q
      (Finset.mem_of_mem_erase hq)).isClosed
    refine ⟨r \ W, discInt (C p), discInt (Rr r), (h.hreg r hr).1.1.sdiff hWc, ⟨hinner p hp hx,
      ?_⟩, ?_, (hsysp.cap p hmp).isPreconnected_discInt, hsysp.hR.isPreconnected_discInt,
        (hsysp.cap p hmp).subset_closure_discInt (hLC p hp hx.1), ?_⟩
    · intro hxW
      obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.1 hxW
      obtain ⟨hqs, hqr⟩ := hmem' (Finset.mem_of_mem_erase hq)
      have hxq' : x ∈ C q := by
        change x ∈ Cap (rg q) q
        rw [hqr]
        exact hxq
      exact hx.2 (hsame p hp q hqs (Finset.ne_of_mem_erase hq).symm hqr.symm ⟨hLC p hp hx.1, hxq'⟩)
    · rintro y ⟨hyr, hyW⟩
      have hyD : y ∈ closure r := subset_closure hyr
      have hnb : y ∉ discBd (closure r) := fun hb => (by rw [hDb] at hb; exact hb.2 hyr)
      have hoffW : ∀ i ∈ s r, i ≠ p → y ∉ Cap r i := fun i hi hip hy' => hyW (mem_biUnion
        (Finset.mem_erase.2 ⟨hip, hi⟩) hy')
      rw [hsysp.cover] at hyD
      rcases hyD with hyR | hyU
      · by_cases hyb : y ∈ discBd (Rr r)
        · rcases hsysp.bdR hyb with h1 | h1
          · obtain ⟨i, hi, h2⟩ := mem_iUnion₂.1 h1
            by_cases hip : i = p
            · subst hip
              exact .inr h2
            · exfalso
              refine hoffW i hi hip ?_
              have h3 : y ∈ Cap r i ∩ Rr r := by
                rw [hsysp.capR i hi]
                exact h2
              exact h3.1
          · exact absurd h1 hnb
        · exact .inl (.inr ⟨hyR, hyb⟩)
      · obtain ⟨i, hi, h2⟩ := mem_iUnion₂.1 hyU
        by_cases hip : i = p
        · subst hip
          by_cases hyb : y ∈ discBd (Cap r i)
          · rw [hsysp.capb i hi] at hyb
            rcases hyb with h3 | h3
            · exact absurd (hGD i hp h3) hnb
            · exact .inr h3
          · exact .inl (.inl ⟨h2, hyb⟩)
        · exact absurd h2 (hoffW i hi hip)
    · rintro _ ⟨q, hq, rfl⟩
      exact ⟨hAoff q hq, hBoff q hq⟩

end GraphMinor.GM17
