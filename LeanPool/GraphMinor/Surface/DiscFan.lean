/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Fans of closed discs

A fan at a point `y` is a finite family of closed discs through `y`, each with two rays from `y` on
its boundary. Two
discs of the family meet only in common rays, a ray lies in at most two discs, and the family is
connected through
common rays. Then the union is a closed disc (`IsFan.exists_disc`). We merge two discs along a
common ray with
`disc_union` until at most two discs are left. No cyclic order around `y` is needed.

If each ray lies in two discs then `y` is not on the boundary of the union. If some ray lies in only
one disc, then `y`
is on this boundary.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The hypotheses on a fan at `y`. A member is a disc with the set of its two rays. -/
structure IsFan (y : X) (𝓟 : Set (Set X × Set (Set X))) : Prop where
  fin : 𝓟.Finite
  disc : ∀ P ∈ 𝓟, IsClosedDisc P.1
  rays : ∀ P ∈ 𝓟, ∃ r r' u u', P.2 = {r, r'} ∧ r ≠ r' ∧ IsLineWithEnds r y u
    ∧ IsLineWithEnds r' y u' ∧
    r ⊆ discBd P.1 ∧ r' ⊆ discBd P.1 ∧ r ∩ r' = {y}
  meet : ∀ P ∈ 𝓟, ∀ P' ∈ 𝓟, P ≠ P' → P.1 ∩ P'.1 = {y} ∪ ⋃₀ (P.2 ∩ P'.2)
  two : ∀ r, {P ∈ 𝓟 | r ∈ P.2}.encard ≤ 2
  conn : ∀ 𝓠 ⊆ 𝓟, 𝓠.Nonempty → (∀ P ∈ 𝓠, ∀ P' ∈ 𝓟, (P.2 ∩ P'.2).Nonempty → P' ∈ 𝓠) → 𝓠 = 𝓟

theorem IsLineWithEnds.ne' {L : Set X} {u v : X} (h : IsLineWithEnds L u v) : u ≠ v := by
  obtain ⟨f, h0, h1⟩ := h
  intro he
  have : f 0 = f 1 := Subtype.ext (by rw [h0, h1, he])
  exact zero_ne_one (f.injective this)

omit [TopologicalSpace X] in
theorem not_third {𝓟 : Set (Set X × Set (Set X))} {r : Set X} (h : {P ∈ 𝓟 | r ∈ P.2}.encard ≤ 2)
    {P P' Q : Set X × Set (Set X)} (hP : P ∈ 𝓟) (hP' : P' ∈ 𝓟) (hQ : Q ∈ 𝓟) (h1 : r ∈ P.2)
      (h2 : r ∈ P'.2)
    (h3 : r ∈ Q.2) (hne : P ≠ P') (hQ1 : Q ≠ P) (hQ2 : Q ≠ P') : False := by
  classical
  have hs : ({Q, P, P'} : Set (Set X × Set (Set X))) ⊆ {P ∈ 𝓟 | r ∈ P.2} := by
    rintro x (rfl | rfl | rfl)
    · exact ⟨hQ, h3⟩
    · exact ⟨hP, h1⟩
    · exact ⟨hP', h2⟩
  have h4 := (encard_le_encard hs).trans h
  rw [encard_insert_of_notMem (by simp [hQ1, hQ2]), encard_pair hne] at h4
  norm_num at h4

variable [T2Space X]

omit [T2Space X] in
theorem IsFan.rays_of {y : X} {𝓟 : Set (Set X × Set (Set X))} (h : IsFan y 𝓟) {P : Set X × Set
  (Set X)} (hP : P ∈ 𝓟)
    {c : Set X} (hc : c ∈ P.2) : ∃ o u v, P.2 = {c, o} ∧ c ≠ o ∧ IsLineWithEnds c y u
      ∧ IsLineWithEnds o y v ∧
      c ⊆ discBd P.1 ∧ o ⊆ discBd P.1 ∧ c ∩ o = {y} := by
  obtain ⟨r, r', u, u', hR, hrr, hl, hl', hb, hb', hi⟩ := h.rays P hP
  rw [hR] at hc
  rcases hc with rfl | hc
  · exact ⟨r', u, u', hR, hrr, hl, hl', hb, hb', hi⟩
  · have hc' : c = r' := hc
    subst hc'
    exact ⟨r, u', u, by rw [hR, pair_comm], hrr.symm, hl', hl, hb', hb, by rw [inter_comm, hi]⟩

omit [T2Space X] in
private theorem IsFan.merge_conn {y : X} {𝓟 : Set (Set X × Set (Set X))}
    (h : IsFan y 𝓟) {P P' : Set X × Set (Set X)}
    (hP : P ∈ 𝓟) (hP' : P' ∈ 𝓟) {c o o' : Set X}
    (hR : P.2 = {c, o}) (hR' : P'.2 = {c, o'})
    (hNc : ∀ Q ∈ 𝓟, Q ≠ P → Q ≠ P' → c ∉ Q.2) :
    let N : Set X × Set (Set X) := (P.1 ∪ P'.1, ({o, o'} : Set (Set X)))
    N ∉ 𝓟 →
    ∀ 𝓠 ⊆ insert N (𝓟 \ {P, P'}), 𝓠.Nonempty →
      (∀ Q ∈ 𝓠, ∀ Q' ∈ insert N (𝓟 \ {P, P'}),
        (Q.2 ∩ Q'.2).Nonempty → Q' ∈ 𝓠) →
      𝓠 = insert N (𝓟 \ {P, P'}) := by
  classical
  intro N hNnot 𝓠 hsub hne𝓠 hcl
  have hshare : ∀ Q ∈ 𝓠, ∀ t, t ∈ Q.2 → t ∈ N.2 → N ∈ 𝓠 := fun Q hQ t h1 h2 =>
    hcl Q hQ N (.inl rfl) ⟨t, h1, h2⟩
  have hPray : ∀ Q ∈ 𝓟, Q ≠ P → Q ≠ P' → ∀ t ∈ Q.2, t ∈ P.2 ∪ P'.2 → t ∈ N.2 := by
    rintro Q hQ h1 h2 t ht (h3 | h3)
    · rw [hR] at h3
      rcases h3 with rfl | h3
      · exact absurd ht (hNc Q hQ h1 h2)
      · exact .inl h3
    · rw [hR'] at h3
      rcases h3 with rfl | h3
      · exact absurd ht (hNc Q hQ h1 h2)
      · exact .inr h3
  have hQ𝓟 : ∀ Q ∈ 𝓠, Q ≠ N → Q ∈ 𝓟 ∧ Q ≠ P ∧ Q ≠ P' := fun Q hQ hne' => by
    rcases hsub hQ with rfl | h1
    · exact absurd rfl hne'
    · exact ⟨h1.1, fun he => h1.2 (.inl he), fun he => h1.2 (.inr he)⟩
  let 𝓠' : Set (Set X × Set (Set X)) := (𝓠 \ {N}) ∪ (if N ∈ 𝓠 then {P, P'} else ∅)
  have hsub' : 𝓠' ⊆ 𝓟 := by
    rintro Q (hQ | hQ)
    · exact (hQ𝓟 Q hQ.1 hQ.2).1
    · split_ifs at hQ with h1
      · rcases hQ with rfl | rfl
        · exact hP
        · exact hP'
      · exact absurd hQ (notMem_empty _)
  have hne' : 𝓠'.Nonempty := by
    obtain ⟨Q, hQ⟩ := hne𝓠
    by_cases hQN : Q = N
    · subst hQN
      exact ⟨P, .inr (by rw [ite_eq_left hQ]; exact .inl rfl)⟩
    · exact ⟨Q, .inl ⟨hQ, hQN⟩⟩
  have hcl' : ∀ Q ∈ 𝓠', ∀ Q' ∈ 𝓟, (Q.2 ∩ Q'.2).Nonempty → Q' ∈ 𝓠' := by
    intro Q hQ Q' hQ' ⟨t, ht1, ht2⟩
    have hNin : ∀ Q'' ∈ 𝓠, Q'' ≠ N → (Q' = P ∨ Q' = P') → t ∈ Q''.2 → N ∈ 𝓠 := by
      intro Q'' hQ'' hn h1 h2
      obtain ⟨h3, h4, h5⟩ := hQ𝓟 Q'' hQ'' hn
      refine hshare Q'' hQ'' t h2 (hPray Q'' h3 h4 h5 t h2 ?_)
      rcases h1 with rfl | rfl
      · exact .inl ht2
      · exact .inr ht2
    by_cases hQ'P : Q' = P ∨ Q' = P'
    · have hNm : N ∈ 𝓠 := by
        rcases hQ with hQ | hQ
        · exact hNin Q hQ.1 hQ.2 hQ'P ht1
        · split_ifs at hQ with h1
          · exact h1
          · exact absurd hQ (notMem_empty _)
      refine .inr ?_
      rw [ite_eq_left hNm]
      rcases hQ'P with rfl | rfl
      · exact .inl rfl
      · exact .inr rfl
    · push Not at hQ'P
      have hQ'N : Q' ≠ N := fun he => hNnot (he ▸ hQ')
      have hm' : Q' ∈ insert N (𝓟 \ {P, P'}) := .inr ⟨hQ', fun h1 => by
        rcases h1 with h1 | h1
        · exact hQ'P.1 h1
        · exact hQ'P.2 h1⟩
      refine .inl ⟨?_, hQ'N⟩
      rcases hQ with hQ | hQ
      · exact hcl Q hQ.1 Q' hm' ⟨t, ht1, ht2⟩
      · split_ifs at hQ with h1
        · have ht3 : t ∈ N.2 := by
            refine hPray Q' hQ' hQ'P.1 hQ'P.2 t ht2 ?_
            rcases hQ with rfl | rfl
            · exact .inl ht1
            · exact .inr ht1
          exact hcl N h1 Q' hm' ⟨t, ht3, ht2⟩
        · exact absurd hQ (notMem_empty _)
  have hall := h.conn 𝓠' hsub' hne' hcl'
  have hNm : N ∈ 𝓠 := by
    have h1 : P ∈ 𝓠' := hall ▸ hP
    rcases h1 with h1 | h1
    · have h2 := hsub h1.1
      rcases h2 with h2 | h2
      · exact absurd h2 h1.2
      · exact absurd (.inl rfl) h2.2
    · split_ifs at h1 with h2
      · exact h2
      · exact absurd h1 (notMem_empty _)
  refine subset_antisymm hsub ?_
  rintro Q (rfl | hQ)
  · exact hNm
  · have h1 : Q ∈ 𝓠' := hall ▸ hQ.1
    rcases h1 with h1 | h1
    · exact h1.1
    · rw [ite_eq_left hNm] at h1
      exact absurd h1 hQ.2

/-- Merging two members of a fan along a common ray gives a fan. -/
theorem IsFan.merge {y : X} {𝓟 : Set (Set X × Set (Set X))} (h : IsFan y 𝓟) {P P' : Set X × Set
  (Set X)}
    (hP : P ∈ 𝓟) (hP' : P' ∈ 𝓟) (hne : P ≠ P') {c o o' : Set X} {u : X} (hR : P.2 = {c, o})
      (hR' : P'.2 = {c, o'})
    (hoo : o ≠ o') (hco : c ≠ o) (hco' : c ≠ o') (hlc : IsLineWithEnds c y u) (hco1 : c ∩ o = {y})
      (hco2 : c ∩ o' = {y})
    (hbc : c ⊆ discBd P.1) (hbc' : c ⊆ discBd P'.1) (hbo : o ⊆ discBd P.1) (hbo' : o' ⊆ discBd P'.1)
    (hlo : ∃ v, IsLineWithEnds o y v) (hlo' : ∃ v, IsLineWithEnds o' y v) :
    (P.1 ∪ P'.1, ({o, o'} : Set (Set X))) ∉ 𝓟 ∧ IsFan y (insert (P.1 ∪ P'.1, ({o, o'} : Set
      (Set X))) (𝓟 \ {P, P'})) ∧
      IsClosedDisc (P.1 ∪ P'.1) ∧ o ⊆ discBd (P.1 ∪ P'.1) ∧ o' ⊆ discBd (P.1 ∪ P'.1) := by
  classical
  set N : Set X × Set (Set X) := (P.1 ∪ P'.1, ({o, o'} : Set (Set X))) with hN
  have hyc : y ∈ c := hlc.left_mem
  have hinter : P.2 ∩ P'.2 = {c} := by
    rw [hR, hR']
    ext t
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact h1
      · exact h1
      · exact h2
      · exact absurd (h1.symm.trans h2) hoo
    · rintro rfl
      exact ⟨.inl rfl, .inl rfl⟩
  have hmeet : P.1 ∩ P'.1 = c := by
    rw [h.meet P hP P' hP' hne, hinter, sUnion_singleton]
    exact union_eq_right.mpr (singleton_subset_iff.mpr hyc)
  obtain ⟨hdisc, hbd⟩ := disc_union.{u} P.1 P'.1 c y u (h.disc P hP) (h.disc P' hP') hlc hmeet hbc
    hbc'
  have hoi : o ⊆ discBd (P.1 ∪ P'.1) := fun z hz => by
    rw [hbd]
    refine ⟨.inl (hbo hz), fun hzc => hzc.2 (.inl ?_)⟩
    have : z ∈ c ∩ o := ⟨hzc.1, hz⟩
    rwa [hco1] at this
  have hoi' : o' ⊆ discBd (P.1 ∪ P'.1) := fun z hz => by
    rw [hbd]
    refine ⟨.inr (hbo' hz), fun hzc => hzc.2 (.inl ?_)⟩
    have : z ∈ c ∩ o' := ⟨hzc.1, hz⟩
    rwa [hco2] at this
  have hNnot : N ∉ 𝓟 := by
    intro hNm
    have hPN : P ≠ N := by
      intro he
      apply hoo
      have h1 : c ∈ P.2 := by rw [hR]; exact .inl rfl
      rw [he] at h1
      rcases h1 with h1 | h1
      · exact absurd h1 hco
      · exact absurd h1 hco'
    have h1 := h.meet P hP N hNm hPN
    have h2 : P.1 ∩ N.1 = P.1 := inter_eq_left.mpr subset_union_left
    rw [h2] at h1
    obtain ⟨z, hz⟩ := (h.disc P hP).nonempty_discInt
    have h3 : z ∈ {y} ∪ ⋃₀ (P.2 ∩ N.2) := h1 ▸ hz.1
    rcases h3 with h3 | ⟨t, ht, hzt⟩
    · exact hz.2 (hbc (by rw [show z = y from h3]; exact hyc))
    · rw [hR] at ht
      rcases ht.1 with rfl | ht1
      · exact hz.2 (hbc hzt)
      · have ht2 : t = o := ht1
        exact hz.2 (hbo (ht2 ▸ hzt))
  have hNc : ∀ Q ∈ 𝓟, Q ≠ P → Q ≠ P' → c ∉ Q.2 := fun Q hQ h1 h2 hc =>
    not_third (h.two c) hP hP' hQ (by rw [hR]; exact .inl rfl) (by rw [hR']; exact .inl rfl) hc hne
      h1 h2
  have hs1 : ∀ Q ∈ 𝓟, Q ≠ P → Q ≠ P' → P.1 ∩ Q.1 = {y} ∪ ⋃₀ (({o} : Set (Set X)) ∩ Q.2)
    := fun Q hQ h1 h2 => by
    rw [h.meet P hP Q hQ h1.symm]
    congr 2
    ext t
    rw [hR]
    constructor
    · rintro ⟨rfl | ht, h4⟩
      · exact absurd h4 (hNc Q hQ h1 h2)
      · exact ⟨ht, h4⟩
    · rintro ⟨ht, h4⟩
      exact ⟨.inr ht, h4⟩
  have hs2 : ∀ Q ∈ 𝓟, Q ≠ P → Q ≠ P' → P'.1 ∩ Q.1 = {y} ∪ ⋃₀ (({o'} : Set (Set X)) ∩ Q.2)
    := fun Q hQ h1 h2 => by
    rw [h.meet P' hP' Q hQ h2.symm]
    congr 2
    ext t
    rw [hR']
    constructor
    · rintro ⟨rfl | ht, h4⟩
      · exact absurd h4 (hNc Q hQ h1 h2)
      · exact ⟨ht, h4⟩
    · rintro ⟨ht, h4⟩
      exact ⟨.inr ht, h4⟩
  have hNQ : ∀ Q ∈ 𝓟, Q ≠ P → Q ≠ P' → N.1 ∩ Q.1 = {y} ∪ ⋃₀ (N.2 ∩ Q.2) := fun Q hQ h1 h2 => by
    change (P.1 ∪ P'.1) ∩ Q.1 = {y} ∪ ⋃₀ (({o, o'} : Set (Set X)) ∩ Q.2)
    rw [union_inter_distrib_right, hs1 Q hQ h1 h2, hs2 Q hQ h1 h2, insert_eq,
      union_inter_distrib_right, sUnion_union]
    ext z
    simp only [mem_union, mem_singleton_iff]
    tauto
  refine ⟨hNnot, ⟨(h.fin.sdiff).insert _, ?_, ?_, ?_, ?_, ?_⟩, hdisc, hoi, hoi'⟩
  · rintro Q (rfl | hQ)
    · exact hdisc
    · exact h.disc Q hQ.1
  · rintro Q (rfl | hQ)
    · obtain ⟨v, hv⟩ := hlo
      obtain ⟨v', hv'⟩ := hlo'
      refine ⟨o, o', v, v', rfl, hoo, hv, hv', hoi, hoi', ?_⟩
      have hy1 : y ∈ o := hv.left_mem
      have hy2 : y ∈ o' := hv'.left_mem
      refine subset_antisymm (fun z hz => ?_) (singleton_subset_iff.mpr ⟨hy1, hy2⟩)
      have h1 : z ∈ P.1 ∩ P'.1 := ⟨discBd_subset _ (hbo hz.1), discBd_subset _ (hbo' hz.2)⟩
      rw [hmeet] at h1
      have h2 : z ∈ c ∩ o := ⟨h1, hz.1⟩
      rwa [hco1] at h2
    · exact h.rays Q hQ.1
  · have hQn : ∀ Q ∈ 𝓟 \ {P, P'}, Q ≠ N ∧ Q ≠ P ∧ Q ≠ P' := fun Q hQ =>
      ⟨fun he => hNnot (he ▸ hQ.1), fun he => hQ.2 (.inl he), fun he => hQ.2 (.inr he)⟩
    rintro Q (rfl | hQ) Q' (rfl | hQ') hne'
    · exact absurd rfl hne'
    · exact hNQ Q' hQ'.1 (hQn Q' hQ').2.1 (hQn Q' hQ').2.2
    · have := hNQ Q hQ.1 (hQn Q hQ).2.1 (hQn Q hQ).2.2
      rw [inter_comm, this, inter_comm Q.2]
    · exact h.meet Q hQ.1 Q' hQ'.1 hne'
  · intro t
    by_cases ht : t ∈ N.2
    · let φ : Set X × Set (Set X) → Set X × Set (Set X) := fun Q => if Q = N then (if t
      = o then P else P') else Q
      have hsub : φ '' {Q ∈ insert N (𝓟 \ {P, P'}) | t ∈ Q.2} ⊆ {Q ∈ 𝓟 | t ∈ Q.2} := by
        rintro _ ⟨Q, ⟨rfl | hQ, htQ⟩, rfl⟩
        · simp only [φ, ite_true]
          split_ifs with h3
          · exact ⟨hP, by rw [hR, h3]; exact .inr rfl⟩
          · have : t = o' := by
              rcases ht with h4 | h4
              · exact absurd h4 h3
              · exact h4
            exact ⟨hP', by rw [hR', this]; exact .inr rfl⟩
        · have hQN : Q ≠ N := fun he => hNnot (he ▸ hQ.1)
          simp only [φ, ite_eq_right hQN]
          exact ⟨hQ.1, htQ⟩
      have hinj : InjOn φ {Q ∈ insert N (𝓟 \ {P, P'}) | t ∈ Q.2} := by
        have hval : ∀ Q ∈ 𝓟 \ {P, P'}, φ Q = Q := fun Q hQ => by
          have hQN : Q ≠ N := fun he => hNnot (he ▸ hQ.1)
          simp only [φ, ite_eq_right hQN]
        have hvalN : φ N = P ∨ φ N = P' := by
          simp only [φ, ite_true]
          split_ifs
          · exact .inl rfl
          · exact .inr rfl
        rintro Q ⟨rfl | hQ, -⟩ Q' ⟨rfl | hQ', -⟩ he
        · rfl
        · rw [hval Q' hQ'] at he
          rcases hvalN with h4 | h4
          · exact absurd (h4.symm.trans he).symm (fun h5 => hQ'.2 (.inl h5))
          · exact absurd (h4.symm.trans he).symm (fun h5 => hQ'.2 (.inr h5))
        · rw [hval Q hQ] at he
          rcases hvalN with h4 | h4
          · exact absurd (he.trans h4) (fun h5 => hQ.2 (.inl h5))
          · exact absurd (he.trans h4) (fun h5 => hQ.2 (.inr h5))
        · rw [hval Q hQ, hval Q' hQ'] at he
          exact he
      rw [← hinj.encard_image]
      exact (encard_le_encard hsub).trans (h.two t)
    · refine (encard_le_encard ?_).trans (h.two t)
      rintro Q ⟨rfl | hQ, htQ⟩
      · exact absurd htQ ht
      · exact ⟨hQ.1, htQ⟩
  · exact h.merge_conn hP hP' hR hR' hNc hNnot

theorem IsFan.exists_disc (n : ℕ) : ∀ (y : X) (𝓟 : Set (Set X × Set (Set X))), 𝓟.ncard = n
  → IsFan y 𝓟 → 𝓟.Nonempty →
    ∃ E, IsClosedDisc E ∧ E = (⋃ P ∈ 𝓟, P.1) ∧
      ((∀ P ∈ 𝓟, ∀ r ∈ P.2, ∃ P' ∈ 𝓟, P' ≠ P ∧ r ∈ P'.2) → y ∉ discBd E) ∧
      ((∃ P ∈ 𝓟, ∃ r ∈ P.2, ∀ P' ∈ 𝓟, r ∈ P'.2 → P' = P) → y ∈ discBd E) := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y 𝓟 hn h hne
  obtain ⟨P, hP⟩ := hne
  obtain ⟨r, r', u, u', hR, hrr, hl, hl', hb, hb', hi⟩ := h.rays P hP
  by_cases hsing : 𝓟 = {P}
  · subst hsing
    refine ⟨P.1, h.disc P hP, by simp, fun hall => ?_, fun _ => hb hl.left_mem⟩
    obtain ⟨P', hP', hne, -⟩ := hall P hP r (by rw [hR]; exact .inl rfl)
    exact absurd hP' hne
  obtain ⟨P', hP', hPP', c, hcP, hcP'⟩ : ∃ P' ∈ 𝓟, P' ≠ P ∧ ∃ c, c ∈ P.2 ∧ c ∈ P'.2 := by
    by_contra hcon
    push Not at hcon
    refine hsing (h.conn {P} (by simpa using hP) ⟨P, rfl⟩ ?_).symm
    rintro _ rfl Q hQ ⟨c, hc1, hc2⟩
    by_contra hQne
    exact hcon Q hQ hQne c hc1 hc2
  obtain ⟨o, u₁, v₁, hR1, hco, hlc, hlo, hbc, hbo, hio⟩ := h.rays_of hP hcP
  obtain ⟨o', u₂, v₂, hR2, hco', hlc', hlo', hbc', hbo', hio'⟩ := h.rays_of hP' hcP'
  have hPne : P ≠ P' := hPP'.symm
  by_cases hoo : o = o'
  · subst hoo
    have hall : ({P, P'} : Set _) = 𝓟 := by
      refine h.conn {P, P'} (by
        rintro Q (rfl | rfl)
        · exact hP
        · exact hP') ⟨P, .inl rfl⟩ ?_
      rintro Q hQ Q' hQ' ⟨t, ht1, ht2⟩
      by_contra hn'
      have hq1 : Q' ≠ P := fun he => hn' (.inl he)
      have hq2 : Q' ≠ P' := fun he => hn' (.inr he)
      have htP : t ∈ P.2 ∧ t ∈ P'.2 := by
        have h1 : t ∈ ({c, o} : Set (Set X)) := by
          rcases hQ with rfl | rfl
          · rw [← hR1]
            exact ht1
          · rw [← hR2]
            exact ht1
        exact ⟨hR1 ▸ h1, hR2 ▸ h1⟩
      exact not_third (h.two t) hP hP' hQ' htP.1 htP.2 ht2 hPne hq1 hq2
    have hinter : P.2 ∩ P'.2 = {c, o} := by
      rw [hR1, hR2, inter_self]
    have hmeet : P.1 ∩ P'.1 = c ∪ o := by
      rw [h.meet P hP P' hP' hPne, hinter, sUnion_pair]
      exact union_eq_right.mpr (singleton_subset_iff.mpr (.inl hlc.left_mem))
    have hline : IsLineWithEnds (c ∪ o) u₁ v₁ := hlc.symm.union hlo hio
    obtain ⟨hdisc, hbd⟩ := disc_union.{u} P.1 P'.1 (c ∪ o) u₁ v₁ (h.disc P hP)
      (h.disc P' hP') hline hmeet
      (union_subset hbc hbo) (union_subset hbc' hbo')
    refine ⟨P.1 ∪ P'.1, hdisc, ?_, fun _ => ?_, ?_⟩
    · rw [← hall]
      simp
    · rw [hbd]
      rintro ⟨-, h2⟩
      refine h2 ⟨.inl hlc.left_mem, ?_⟩
      rintro (h3 | h3)
      · exact hlc.ne' h3
      · exact hlo.ne' h3
    · rintro ⟨Q, hQ, t, ht, hfree⟩
      have ht' : t ∈ ({c, o} : Set (Set X)) := by
        rw [← hall] at hQ
        rcases hQ with rfl | rfl
        · rw [← hR1]
          exact ht
        · rw [← hR2]
          exact ht
      exact absurd ((hfree P hP (hR1 ▸ ht')).trans (hfree P' hP' (hR2 ▸ ht')).symm) hPne
  · obtain ⟨hNnot, hfan, hdisc, hoi, hoi'⟩ :=
      h.merge hP hP' hPne hR1 hR2 hoo hco hco' hlc hio hio' hbc hbc' hbo hbo' ⟨_, hlo⟩ ⟨_, hlo'⟩
    set N : Set X × Set (Set X) := (P.1 ∪ P'.1, ({o, o'} : Set (Set X))) with hN
    have hlt : (insert N (𝓟 \ {P, P'})).ncard < n := by
      have hnN : N ∉ 𝓟 \ {P, P'} := fun h1 => hNnot h1.1
      rw [← hn, ncard_insert_of_notMem hnN h.fin.sdiff]
      have hs : ({P, P'} : Set _) ⊆ 𝓟 := by
        rintro Q (rfl | rfl)
        · exact hP
        · exact hP'
      have h1 := ncard_sdiff_add_ncard_of_subset hs h.fin
      rw [ncard_pair hPne] at h1
      omega
    obtain ⟨E, hE, hEu, hc1, hc2⟩ := ih _ hlt y _ rfl hfan ⟨N, .inl rfl⟩
    have hcN : ∀ Q ∈ 𝓟, Q ≠ P → Q ≠ P' → c ∉ Q.2 := fun Q hQ h1 h2 hc =>
      not_third (h.two c) hP hP' hQ (hR1 ▸ .inl rfl) (hR2 ▸ .inl rfl) hc hPne h1 h2
    refine ⟨E, hE, ?_, fun hall => hc1 ?_, fun hfree => hc2 ?_⟩
    · rw [hEu]
      ext z
      simp only [mem_iUnion, exists_prop, mem_insert_iff]
      constructor
      · rintro ⟨Q, rfl | hQ, hz⟩
        · rcases hz with hz | hz
          · exact ⟨P, hP, hz⟩
          · exact ⟨P', hP', hz⟩
        · exact ⟨Q, hQ.1, hz⟩
      · rintro ⟨Q, hQ, hz⟩
        by_cases h1 : Q = P
        · exact ⟨N, .inl rfl, .inl (h1 ▸ hz)⟩
        · by_cases h2 : Q = P'
          · exact ⟨N, .inl rfl, .inr (h2 ▸ hz)⟩
          · exact ⟨Q, .inr ⟨hQ, by
              rintro (h3 | h3)
              · exact h1 h3
              · exact h2 h3⟩, hz⟩
    · have hkeep : ∀ Q ∈ 𝓟, Q ≠ P → Q ≠ P' → Q ∈ insert N (𝓟 \ {P, P'}) := fun Q hQ h1 h2 =>
        .inr ⟨hQ, by
          rintro (h3 | h3)
          · exact h1 h3
          · exact h2 h3⟩
      have hother : ∀ t, (t = o ∨ t = o') → ∃ Q ∈ 𝓟, Q ≠ P ∧ Q ≠ P' ∧ t ∈ Q.2 := by
        rintro t (rfl | rfl)
        · obtain ⟨Q, hQ, hne1, ht'⟩ := hall P hP t (hR1 ▸ .inr rfl)
          refine ⟨Q, hQ, hne1, fun he => ?_, ht'⟩
          rw [he, hR2] at ht'
          rcases ht' with h3 | h3
          · exact hco h3.symm
          · exact hoo h3
        · obtain ⟨Q, hQ, hne1, ht'⟩ := hall P' hP' t (hR2 ▸ .inr rfl)
          refine ⟨Q, hQ, fun he => ?_, hne1, ht'⟩
          rw [he, hR1] at ht'
          rcases ht' with h3 | h3
          · exact hco' h3.symm
          · exact hoo h3.symm
      rintro Q (rfl | hQ) t ht
      · obtain ⟨Q, hQ, h1, h2, h3⟩ := hother t (by
          rcases ht with h4 | h4
          · exact .inl h4
          · exact .inr h4)
        exact ⟨Q, hkeep Q hQ h1 h2, fun he => hNnot (he ▸ hQ), h3⟩
      · have hQ1 : Q ≠ P := fun he => hQ.2 (.inl he)
        have hQ2 : Q ≠ P' := fun he => hQ.2 (.inr he)
        have hQN : Q ≠ N := fun he => hNnot (he ▸ hQ.1)
        obtain ⟨Q', hQ', hne1, ht'⟩ := hall Q hQ.1 t ht
        by_cases h1 : Q' = P
        · rw [h1, hR1] at ht'
          rcases ht' with h3 | h3
          · exact absurd (h3 ▸ ht) (hcN Q hQ.1 hQ1 hQ2)
          · exact ⟨N, .inl rfl, hQN.symm, .inl h3⟩
        · by_cases h2 : Q' = P'
          · rw [h2, hR2] at ht'
            rcases ht' with h3 | h3
            · exact absurd (h3 ▸ ht) (hcN Q hQ.1 hQ1 hQ2)
            · exact ⟨N, .inl rfl, hQN.symm, .inr h3⟩
          · exact ⟨Q', hkeep Q' hQ' h1 h2, hne1, ht'⟩
    · obtain ⟨Q, hQ, t, ht, hfr⟩ := hfree
      have hold : ∀ R ∈ insert N (𝓟 \ {P, P'}), R ≠ N → R ∈ 𝓟 ∧ R ≠ P ∧ R ≠ P' := by
        rintro R (rfl | h1) h2
        · exact absurd rfl h2
        · exact ⟨h1.1, fun he => h1.2 (.inl he), fun he => h1.2 (.inr he)⟩
      by_cases h1 : Q = P
      · subst h1
        rw [hR1] at ht
        rcases ht with h3 | h3
        · exact absurd (hfr P' hP' (by rw [h3]; exact hR2 ▸ .inl rfl)) hPP'
        · have h3' : t = o := h3
          refine ⟨N, .inl rfl, t, .inl h3', fun R hRm htR => ?_⟩
          by_contra hRN
          obtain ⟨h4, h5, -⟩ := hold R hRm hRN
          exact h5 (hfr R h4 htR)
      · by_cases h2 : Q = P'
        · subst h2
          rw [hR2] at ht
          rcases ht with h3 | h3
          · exact absurd (hfr P hP (by rw [h3]; exact hR1 ▸ .inl rfl)) hPne
          · have h3' : t = o' := h3
            refine ⟨N, .inl rfl, t, .inr h3', fun R hRm htR => ?_⟩
            by_contra hRN
            obtain ⟨h4, -, h5⟩ := hold R hRm hRN
            exact h5 (hfr R h4 htR)
        · refine ⟨Q, .inr ⟨hQ, by
            rintro (h3 | h3)
            · exact h1 h3
            · exact h2 h3⟩, t, ht, fun R hRm htR => ?_⟩
          by_cases hRN : R = N
          · rw [hRN] at htR
            rcases htR with h3 | h3
            · exact absurd (hfr P hP (by rw [h3]; exact hR1 ▸ .inr rfl)).symm h1
            · exact absurd (hfr P' hP' (by rw [show t = o' from h3]; exact hR2 ▸ .inr rfl)).symm h2
          · exact hfr R (hold R hRm hRN).1 htR

end GraphMinor.Surface
