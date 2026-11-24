/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.ThreeNodeReplace
public import LeanPool.GraphMinor.GM17.ArcDisc
public import LeanPool.GraphMinor.GM17.ReplaceDisc

/-!
# Disjoint chords in a closed disc

This file holds the two surface facts behind Claim (1) of the proof of (12.2) of Graph Minors XVII
(page 198). The paper draws a graph `H` on the boundaries of the cells. A cycle of `H` is not
`Γ`-normal, so (8.5) does not apply to it directly. We push each edge of `H` we need off its cell,
into the region beside it.

If several boundary lines of one closed disc are given, meeting only at common ends, then there are
chords with the same ends that are disjoint except at common ends (`chords_in_disc`). Each chord
cuts off a cap, and one disc `R` is left over.

A closed disc lies on exactly one side of a line of its boundary (`disc_flip`).
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S] [T2Space S] {ι : Type}

/-- The result of cutting caps off a disc `D`: for each `i ∈ s`, the chord `Ch i` cuts the cap `Cap
i` off `D` along the line `G i` of its boundary, and `R` is what is left. -/
structure ChordSys (D : Set S) (s : Finset ι) (G : ι → Set S) (a b : ι → S) (R : Set S) (Ch Cap : ι
  → Set S) : Prop where
  hR : IsClosedDisc R
  line : ∀ i ∈ s, IsLineWithEnds (Ch i) (a i) (b i)
  cap : ∀ i ∈ s, IsClosedDisc (Cap i)
  capb : ∀ i ∈ s, discBd (Cap i) = G i ∪ Ch i
  inter : ∀ i ∈ s, G i ∩ Ch i = {a i, b i}
  chR : ∀ i ∈ s, Ch i ⊆ discBd R
  capR : ∀ i ∈ s, Cap i ∩ R = Ch i
  cover : D = R ∪ ⋃ i ∈ s, Cap i
  pair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Cap i ∩ Cap j ⊆ {a i, b i} ∩ {a j, b j}
  bdR : discBd R ⊆ (⋃ i ∈ s, Ch i) ∪ discBd D
  capD : ∀ i ∈ s, Cap i ∩ discBd D ⊆ G i

theorem chords_in_disc (hman : ∀ x : S, IsManifoldPoint x) {D : Set S} (hD : IsClosedDisc D)
  (s : Finset ι) {G : ι → Set S} {a b : ι → S}
    (hG : ∀ i ∈ s, IsLineWithEnds (G i) (a i) (b i)) (hsub : ∀ i ∈ s, G i ⊆ discBd D)
      (hne : ∀ i ∈ s, a i ≠ b i)
    (hp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → G i ∩ G j ⊆ {a i, b i} ∩ {a j, b j}) :
    ∃ R Ch Cap, ChordSys D s G a b R Ch Cap := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨D, fun _ => ∅, fun _ => ∅, ⟨hD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> simp
  | insert k s hk ih =>
    obtain ⟨R, Ch, Cap, h⟩ := ih (fun i hi => hG i (Finset.mem_insert_of_mem hi)) (fun i hi
      => hsub i (Finset.mem_insert_of_mem hi))
      (fun i hi => hne i (Finset.mem_insert_of_mem hi)) (fun i hi j hj => hp i
        (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
    have hkk := Finset.mem_insert_self k s
    have hik : ∀ i ∈ s, i ≠ k := fun i hi e => hk (e ▸ hi)
    have hmem : ∀ i ∈ s, i ∈ insert k s := fun i hi => Finset.mem_insert_of_mem hi
    have hRD : R ⊆ D := by rw [h.cover]; exact subset_union_left
    have hCapD : ∀ i ∈ s, Cap i ⊆ D := fun i hi x hx => by
      rw [h.cover]
      exact .inr (mem_biUnion hi hx)
    have hChCap : ∀ i ∈ s, Ch i ⊆ Cap i := fun i hi x hx => by
      rw [← h.capR i hi] at hx
      exact hx.1
    have hGb' : ∀ x ∈ G k, x ∈ discBd D := fun x hx => hsub k hkk hx
    have hGcap : ∀ i ∈ s, ∀ x ∈ Cap i, x ∈ G k → x ∈ ({a i, b i} : Set S) ∩ {a k, b k}
      := fun i hi x hx hxk =>
      hp i (hmem i hi) k hkk (hik i hi) ⟨h.capD i hi ⟨hx, hGb' x hxk⟩, hxk⟩
    have hends : ∀ i ∈ s, ∀ x ∈ ({a i, b i} : Set S), x ∈ Ch i := fun i hi x hx => by
      rcases hx with rfl | rfl
      · exact (h.line i hi).left_mem
      · exact (h.line i hi).right_mem
    have hGR : G k ⊆ R := fun x hx => by
      have hxD : x ∈ D := discBd_subset _ (hGb' x hx)
      rw [h.cover] at hxD
      rcases hxD with h1 | h1
      · exact h1
      · obtain ⟨i, hi, h2⟩ := mem_iUnion₂.1 h1
        exact discBd_subset _ (h.chR i hi (hends i hi x (hGcap i hi x h2 hx).1))
    have hGb : G k ⊆ discBd R := fun x hx => by
      by_contra hn
      exact (discInt_mono hman h.hR hRD ⟨hGR hx, hn⟩).2 (hGb' x hx)
    obtain ⟨Q, hQ, hu, hi⟩ := oarc_split h.hR.isOArc_discBd (hG k hkk) hGb
    obtain ⟨L, Δ₁, Δ₂, hL, hLb, hLR, hd₁, hd₂, hu', hi', hb₁, hb₂⟩ := split_disc h.hR (hG k hkk) hQ
      (hne k hkk) hu hi
    have hΔ₁R : Δ₁ ⊆ R := hu' ▸ subset_union_left
    have hΔ₂R : Δ₂ ⊆ R := hu' ▸ subset_union_right
    have hChΔ : ∀ i ∈ s, Ch i ⊆ discBd Δ₂ := fun i hi' x hx => by
      have hxb : x ∈ discBd R := h.chR i hi' hx
      rw [← hu] at hxb
      rcases hxb with h1 | h1
      · have h3 : x ∈ G k ∩ Q := by
          rw [hi]
          exact (hGcap i hi' x (hChCap i hi' hx) h1).2
        rw [hb₂]
        exact .inl h3.2
      · rw [hb₂]
        exact .inl h1
    have hupC : ∀ i ∈ s, Function.update Ch k L i = Ch i := fun i hi => Function.update_of_ne
      (hik i hi) _ _
    have hupK : ∀ i ∈ s, Function.update Cap k Δ₁ i = Cap i := fun i hi => Function.update_of_ne
      (hik i hi) _ _
    have hupC' : Function.update Ch k L k = L := Function.update_self _ _ _
    have hupK' : Function.update Cap k Δ₁ k = Δ₁ := Function.update_self _ _ _
    have hLG : G k ∩ L = {a k, b k} := by
      ext x
      constructor
      · rintro ⟨h1, h2⟩
        rw [← hLb]
        exact ⟨h2, hGb h1⟩
      · intro h1
        have h2 : x ∈ L ∩ discBd R := by rw [hLb]; exact h1
        rcases h1 with rfl | rfl
        · exact ⟨(hG k hkk).left_mem, h2.1⟩
        · exact ⟨(hG k hkk).right_mem, h2.1⟩
    have hLbD : ∀ x ∈ L, x ∈ discBd D → x ∈ ({a k, b k} : Set S) := fun x hx hxD => by
      rw [← hLb]
      refine ⟨hx, ?_⟩
      by_contra hn
      exact (discInt_mono hman h.hR hRD ⟨hLR hx, hn⟩).2 hxD
    refine ⟨Δ₂, Function.update Ch k L, Function.update Cap k Δ₁, ⟨hd₂, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩⟩
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [hupC']; exact hL
      · rw [hupC i hi]; exact h.line i hi
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [hupK']; exact hd₁
      · rw [hupK i hi]; exact h.cap i hi
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [hupK', hupC']; exact hb₁
      · rw [hupK i hi, hupC i hi]; exact h.capb i hi
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [hupC']; exact hLG
      · rw [hupC i hi]; exact h.inter i hi
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [hupC', hb₂]; exact subset_union_right
      · rw [hupC i hi]; exact hChΔ i hi
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [hupK', hupC']; exact hi'
      · rw [hupK i hi, hupC i hi]
        refine Subset.antisymm (fun x hx => ?_) fun x hx => ⟨hChCap i hi hx,
          discBd_subset _ (hChΔ i hi hx)⟩
        rw [← h.capR i hi]
        exact ⟨hx.1, hΔ₂R hx.2⟩
    · ext x
      constructor
      · intro hx
        rw [h.cover] at hx
        rcases hx with hx | hx
        · rw [← hu'] at hx
          rcases hx with hx | hx
          · exact .inr (mem_biUnion hkk (by rw [hupK']; exact hx))
          · exact .inl hx
        · obtain ⟨i, hi, h2⟩ := mem_iUnion₂.1 hx
          exact .inr (mem_biUnion (hmem i hi) (by rw [hupK i hi]; exact h2))
      · intro hx
        rcases hx with hx | hx
        · exact hRD (hΔ₂R hx)
        · obtain ⟨i, hi, h2⟩ := mem_iUnion₂.1 hx
          rcases Finset.mem_insert.1 hi with rfl | hi
          · rw [hupK'] at h2
            exact hRD (hΔ₁R h2)
          · rw [hupK i hi] at h2
            exact hCapD i hi h2
    · have hcross : ∀ i ∈ s, Cap i ∩ Δ₁ ⊆ {a i, b i} ∩ {a k, b k} := fun i hi x hx => by
        have hxCh : x ∈ Ch i := by
          rw [← h.capR i hi]
          exact ⟨hx.1, hΔ₁R hx.2⟩
        have hxL : x ∈ L := by
          rw [← hi']
          exact ⟨hx.2, discBd_subset _ (hChΔ i hi hxCh)⟩
        have hxe : x ∈ ({a k, b k} : Set S) := by
          rw [← hLb]
          exact ⟨hxL, h.chR i hi hxCh⟩
        have hxG : x ∈ G k := by
          rcases hxe with rfl | rfl
          · exact (hG k hkk).left_mem
          · exact (hG k hkk).right_mem
        exact hGcap i hi x hx.1 hxG
      intro i hi j hj hij
      rcases Finset.mem_insert.1 hi with e | hi' <;> rcases Finset.mem_insert.1 hj with e' | hj'
      · exact absurd (e.trans e'.symm) hij
      · rw [e, hupK', hupK j hj', inter_comm, inter_comm {a k, b k}]
        exact hcross j hj'
      · rw [e', hupK i hi', hupK']
        exact hcross i hi'
      · rw [hupK i hi', hupK j hj']
        exact h.pair i hi' j hj' hij
    · intro x hx
      rw [hb₂] at hx
      rcases hx with hx | hx
      · have hxb : x ∈ discBd R := hu ▸ .inr hx
        rcases h.bdR hxb with h1 | h1
        · obtain ⟨i, hi, h2⟩ := mem_iUnion₂.1 h1
          exact .inl (mem_biUnion (hmem i hi) (by rw [hupC i hi]; exact h2))
        · exact .inr h1
      · exact .inl (mem_biUnion hkk (by rw [hupC']; exact hx))
    · intro i hi x hx
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [hupK'] at hx
        rw [Function.update_self] at *
        by_cases hxb : x ∈ discBd Δ₁
        · rw [hb₁] at hxb
          rcases hxb with h1 | h1
          · exact h1
          · have := hLbD x h1 hx.2
            rcases this with rfl | rfl
            · exact (hG i hkk).left_mem
            · exact (hG i hkk).right_mem
        · exact absurd hx.2 (discInt_mono hman hd₁ (hΔ₁R.trans hRD) ⟨hx.1, hxb⟩).2
      · rw [hupK i hi] at hx
        exact h.capD i hi hx

variable (hman : ∀ x : S, IsManifoldPoint x)
include hman

/-- A preconnected set off the boundary of a disc lies in the disc or misses it. -/
theorem disc_dichotomy {Δ A : Set S} (hΔ : IsClosedDisc Δ) (hA : IsPreconnected A) (hd : Disjoint A
  (discBd Δ)) : A ⊆ Δ ∨ Disjoint A Δ := by
  have hsub : A ⊆ discInt Δ ∪ Δᶜ := fun x hx => by
    by_cases h : x ∈ Δ
    · exact .inl ⟨h, disjoint_left.mp hd hx⟩
    · exact .inr h
  have hdj : Disjoint (discInt Δ) Δᶜ := disjoint_left.mpr fun x hx hx' => hx' hx.1
  rcases hA.subset_or_subset (hΔ.isOpen_discInt hman) hΔ.isClosed.isOpen_compl hdj hsub with h | h
  · exact .inl (h.trans sdiff_subset)
  · exact .inr (disjoint_left.mpr fun x hx hx' => h hx hx')

/-- Near a point of its boundary inside the surface, a closed disc lies on exactly one of two sides.
-/
theorem disc_flip {Δ A B V : Set S} {x : S} (hΔ : IsClosedDisc Δ) (hx : x ∈ discBd Δ)
  (hi : IsInteriorPoint x) (hV : IsOpen V) (hxV : x ∈ V) (hsub : V ⊆ A ∪ B ∪ discBd Δ)
    (hA : IsPreconnected A) (hB : IsPreconnected B) (hAd : Disjoint A (discBd Δ)) (hBd : Disjoint B
      (discBd Δ)) : (A ⊆ Δ ∧ Disjoint B Δ) ∨ (B ⊆ Δ ∧ Disjoint A Δ) := by
  rcases disc_dichotomy hman hΔ hA hAd with h1 | h1 <;> rcases disc_dichotomy hman hΔ hB hBd with
    h2 | h2
  · exfalso
    obtain ⟨y, hy, hyc⟩ := mem_closure_iff.mp (mem_closure_compl hx hi) V hV hxV
    rcases hsub hy with (h3 | h3) | h3
    · exact hyc (h1 h3)
    · exact hyc (h2 h3)
    · exact hyc (discBd_subset _ h3)
  · exact .inl ⟨h1, h2⟩
  · exact .inr ⟨h2, h1⟩
  · exfalso
    obtain ⟨y, hy, hyc⟩ := mem_closure_iff.mp (hΔ.subset_closure_discInt
      (discBd_subset _ hx)) V hV hxV
    rcases hsub hy with (h3 | h3) | h3
    · exact disjoint_left.mp h1 h3 hyc.1
    · exact disjoint_left.mp h2 h3 hyc.1
    · exact hyc.2 h3

end GraphMinor.GM17
