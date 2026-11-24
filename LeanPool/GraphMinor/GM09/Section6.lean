/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section2a
import LeanPool.GraphMinor.GM09.Section2b
import LeanPool.GraphMinor.GM09.Section2d
import LeanPool.GraphMinor.GM09.Section3a
import LeanPool.GraphMinor.GM09.Section3b
import LeanPool.GraphMinor.GM09.Section3c
import LeanPool.GraphMinor.GM09.Section4a
import LeanPool.GraphMinor.GM09.Section4b
import LeanPool.GraphMinor.GM09.Section4c
import LeanPool.GraphMinor.GM09.Section5a
import LeanPool.GraphMinor.GM09.Section5b
import Mathlib.Data.Set.Card

/-!
# Graph Minors IX, Section 6: The Main Theorem (6.1)

This file formalizes Section 6 (pages 55–58) of
N. Robertson and P. D. Seymour, *Graph Minors. IX. Disjoint crossed paths*,
J. Combin. Theory Ser. B **49** (1990) 40–77:
- Properties of `peripheralIntervalSet` (`U(P)`), `transactionPeripheralUnion` (`U(P_set)`), and
  `coveredComponentUnion` (`C(P_set)`), and existence of a transaction `P_set` satisfying `(a)`,
  `(b)`, and `(c)` (maximal `C(P_set)`).
- Claims `(1)`–`(9)` (`lemma_6_1_claim_5`, `lemma_6_1_claim_6`, `lemma_6_1_claim_7`,
  `lemma_6_1_claim_8`, `lemma_6_1_claim_9`, pages 55–57).
- Statement `S_t` (`StatementSt`, page 58), `statementSt_zero`, `statementSt_succ`,
  `statementSt_two`, `exists_crooked_of_statementSt_two`, and the main theorem `(6.1)`
  (`theorem_6_1`, pages 55–58).
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM06

universe u v

variable {α : Type u} {β : Type v}

/-- Every graph path `P` with ends `a, b` is a connected graph. -/
theorem IsGraphPathWithEnds.isGraphConnected {G P : Graph α β} {a b : α}
    (h : IsGraphPathWithEnds G P a b) : IsGraphConnected P := by
  refine ⟨⟨a, h.left_mem⟩, fun u hu v hv => ?_⟩
  obtain ⟨_, hQP, ⟨_, W, _, _, _⟩, _⟩ := h.exists_subpath hu hv
  obtain ⟨W_P, _, _⟩ := exists_walk_up_of_le hQP W
  exact ⟨W_P⟩

namespace Society

variable (S : Society α β)

/-! ## Properties of `U(P)`, `U(P_set)`, and `C(P_set)` (page 55) -/

/-- If `P` is an `Ω`-path with ends `a, b` and no internal vertex of `P` is in `ΩBar`, then
`V(P) ∩ ΩBar = {a, b}`. -/
theorem IsOmegaPathWithEnds.vertexSet_inter_bar_eq {P : Graph α β} {a b : α}
    (hP : S.IsOmegaPathWithEnds P a b)
    (hno_int : Disjoint (pathInternalVerts S.G P) S.Ω.bar) :
    V(P) ∩ S.Ω.bar = {a, b} := by
  ext x
  simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hxP, hx_bar⟩
    by_contra hne
    have hx_int : x ∈ pathInternalVerts S.G P := by
      rw [pathInternalVerts, hP.1.pathEnds_eq]
      exact ⟨hxP, hne⟩
    exact disjoint_left.mp hno_int hx_int hx_bar
  · rintro (rfl | rfl)
    · exact ⟨hP.1.left_mem, hP.2.2.1⟩
    · exact ⟨hP.1.right_mem, hP.2.2.2⟩

/-- When `P_set` is a transaction with `|P_set| ≥ 2` and `P ∈ P_set` has ends `a, b` such that
`Ω(a, b) ∩ V(P_set) = ∅`, the opposite interval `Ω(b, a)` meets `V(P_set)` and hence
`U(P) = peripheralIntervalSet P_set P = Ω(b, a)` uniquely (Graph Minors IX, Section 6, page 55:
"(This defines `U(P)` uniquely.)"). -/
theorem peripheralIntervalSet_eq_interval {P_set : Set (Graph α β)} {P : Graph α β} {a b : α}
    (htrans : S.IsTransaction P_set)
    (hcard : 2 ≤ P_set.ncard)
    (hP_in : P ∈ P_set)
    (hP_ends : S.IsOmegaPathWithEnds P a b)
    (hd_ab : Disjoint (S.Ω.interval a b) (S.transactionEnds P_set)) :
    ¬ Disjoint (S.Ω.interval b a) (S.transactionEnds P_set) ∧
      S.peripheralIntervalSet P_set P = S.Ω.interval b a := by
  obtain ⟨A, B, hfence⟩ := htrans
  have hex_other : ∃ P₁ ∈ P_set, P₁ ≠ P := by
    by_contra! hall
    have hsub : P_set ⊆ {P} := fun Q hQ => mem_singleton_iff.mpr (hall Q hQ)
    have hle : P_set.ncard ≤ ({P} : Set (Graph α β)).ncard :=
      ncard_le_ncard hsub (finite_singleton P)
    rw [ncard_singleton] at hle
    omega
  obtain ⟨P₁, hP₁_in, hP₁_ne⟩ := hex_other
  obtain ⟨a₁, _, b₁, _, hP₁_ends⟩ := hfence.2.2 P₁ hP₁_in
  have hdisj_P₁P : Disjoint V(P₁) V(P) := hfence.1.2 hP₁_in hP_in hP₁_ne
  have ha₁_ne_a : a₁ ≠ a := fun h =>
    disjoint_left.mp hdisj_P₁P hP₁_ends.1.left_mem (h ▸ hP_ends.1.left_mem)
  have ha₁_ne_b : a₁ ≠ b := fun h =>
    disjoint_left.mp hdisj_P₁P hP₁_ends.1.left_mem (h ▸ hP_ends.1.right_mem)
  have ha₁_W : a₁ ∈ S.transactionEnds P_set := hP₁_ends.mem_transactionEnds_left S hP₁_in
  have ha₁_ba : a₁ ∈ S.Ω.interval b a := by
    rcases S.Ω.mem_interval_or_interval_swap hP_ends.2.2.1 hP_ends.2.2.2 hP₁_ends.2.2.1
      hP_ends.2.1 ha₁_ne_a ha₁_ne_b with ha₁_ab | ha₁_ba
    · exact (disjoint_left.mp hd_ab ha₁_ab ha₁_W).elim
    · exact ha₁_ba
  have hnot_disj_ba : ¬ Disjoint (S.Ω.interval b a) (S.transactionEnds P_set) :=
    fun hd => disjoint_left.mp hd ha₁_ba ha₁_W
  refine ⟨hnot_disj_ba, ?_⟩
  ext x
  simp only [peripheralIntervalSet, mem_iUnion]
  constructor
  · rintro ⟨s, t, ⟨hP_st, hd_st⟩, hx⟩
    rcases hP_ends.ends_eq S hP_st with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hx
    · exact (hnot_disj_ba hd_st).elim
  · intro hx
    exact ⟨a, b, ⟨hP_ends, hd_ab⟩, hx⟩

/-- For every peripheral member `P` of `P_set`, `C(P_set) ∩ V(P) = ∅`. -/
theorem disjoint_coveredComponentUnion_of_isPeripheralIn {P_set : Set (Graph α β)} {P : Graph α β}
    (hP_in : P ∈ P_set) (hper : S.IsPeripheralIn P_set P) :
    Disjoint (S.coveredComponentUnion P_set) V(P) := by
  rw [disjoint_left]
  rintro v ⟨_, _, _, Q, hQ, hav⟩ hvP
  exact disjoint_left.mp (hav P hP_in hper) hvP hQ.left_mem

/-- When `P_set` is a transaction with `|P_set| ≥ 2` and no member of `P_set` has an internal vertex
in `ΩBar`, `U(P_set) ⊆ C(P_set)` and `U(P_set)` is disjoint from `V(P)` for every peripheral member
`P`
of `P_set`. -/
theorem transactionPeripheralUnion_subset_coveredComponentUnion {P_set : Set (Graph α β)}
    (htrans : S.IsTransaction P_set)
    (hcard : 2 ≤ P_set.ncard)
    (hno_int : ∀ P ∈ P_set, Disjoint (pathInternalVerts S.G P) S.Ω.bar) :
    S.transactionPeripheralUnion P_set ⊆ S.coveredComponentUnion P_set := by
  intro u hu
  have hu_bar : u ∈ S.Ω.bar := hu.1
  have huG : u ∈ V(S.G) := S.bar_subset hu_bar
  let Q := walkSubgraph (GraphWalk.nil huG)
  have hQ_path : IsGraphPathWithEnds S.G Q u u :=
    isGraphPathWithEnds_walkSubgraph (List.nodup_singleton u)
  have hVQ : V(Q) = {u} := by
    ext z
    simp [Q, vertexSet_walkSubgraph]
  refine ⟨huG, u, hu, Q, hQ_path, fun P hP_in hper => ?_⟩
  rw [Avoids, hVQ, disjoint_singleton_right]
  intro huP
  have hu_ends : u ∈ pathEnds S.G P := by
    by_contra hu_not_ends
    exact disjoint_left.mp (hno_int P hP_in) ⟨huP, hu_not_ends⟩ hu_bar
  rcases hper with ⟨_, a, b, hP_ab, hd_ab | hd_ba⟩
  · obtain ⟨_, hU_eq⟩ := S.peripheralIntervalSet_eq_interval htrans hcard hP_in hP_ab hd_ab
    have hu_ba : u ∈ S.Ω.interval b a := by
      rw [← hU_eq]
      exact mem_iInter₂.mp hu.2 P ⟨hP_in, hP_in, a, b, hP_ab, Or.inl hd_ab⟩
    rw [hP_ab.1.pathEnds_eq, mem_insert_iff, mem_singleton_iff] at hu_ends
    rcases hu_ends with h_eq | h_eq
    · rw [h_eq] at hu_ba
      exact S.Ω.not_mem_interval_right b a hu_ba
    · rw [h_eq] at hu_ba
      exact S.Ω.not_mem_interval_left b a hu_ba
  · obtain ⟨_, hU_eq⟩ := S.peripheralIntervalSet_eq_interval htrans hcard hP_in (hP_ab.symm S) hd_ba
    have hu_ab : u ∈ S.Ω.interval a b := by
      rw [← hU_eq]
      exact mem_iInter₂.mp hu.2 P ⟨hP_in, hP_in, a, b, hP_ab, Or.inr hd_ba⟩
    rw [hP_ab.1.pathEnds_eq, mem_insert_iff, mem_singleton_iff] at hu_ends
    rcases hu_ends with h_eq | h_eq
    · rw [h_eq] at hu_ab
      exact S.Ω.not_mem_interval_left a b hu_ab
    · rw [h_eq] at hu_ab
      exact S.Ω.not_mem_interval_right a b hu_ab

/-- Every transaction `P_set` in `(G, Ω)` can be refined to a transaction `P_set'` of the same
cardinality such that no member of `P_set'` has an internal vertex in `ΩBar` (Graph Minors IX,
Section 6, page 56:
"Let $(A, B)$ be a fence for $\mathcal{P}$, for each $P \in \mathcal{P}$ choose an $A \to B$
subpath of $P$, and let $\mathcal{P}'$ be the collection of these subpaths. Then
$\mathcal{P}'$ satisfies (a) and (b)"). -/
theorem exists_transaction_no_internal_in_bar {P_set : Set (Graph α β)}
    (htrans : S.IsTransaction P_set) :
    ∃ P_set' : Set (Graph α β),
      S.IsTransaction P_set' ∧
      P_set'.ncard = P_set.ncard ∧
      ∀ P' ∈ P_set', Disjoint (pathInternalVerts S.G P') S.Ω.bar := by
  classical
  rcases htrans with ⟨A, B, hdisj, hfence, hends⟩
  have hex_sub : ∀ P : P_set, ∃ Q : Graph α β,
      Q ≤ P.1 ∧ ∃ a ∈ A, ∃ b ∈ B,
        S.IsOmegaPathWithEnds Q a b ∧
        Disjoint (pathInternalVerts S.G Q) S.Ω.bar := by
    intro P
    obtain ⟨a₀, ha₀, b₀, hb₀, hP₀⟩ := hends P.1 P.2
    obtain ⟨a, haA, b, hbB, Q, hQP, hQ_ft⟩ :=
      hP₀.1.exists_isFromToPathWithEnds ha₀ hb₀
    have hab_ne : a ≠ b := fun h => disjoint_left.mp hfence.2.2.1 haA (h ▸ hbB)
    have hQ_omega : S.IsOmegaPathWithEnds Q a b :=
      ⟨hQ_ft.1, hab_ne, hfence.1 haA, hfence.2.1 hbB⟩
    have hno_int : Disjoint (pathInternalVerts S.G Q) S.Ω.bar := by
      rw [disjoint_left]
      rintro z ⟨hzQ, hz_not_ends⟩ hz_bar
      rw [hQ_ft.1.pathEnds_eq, mem_insert_iff, mem_singleton_iff, not_or] at hz_not_ends
      rcases (hfence.2.2.2.1.symm ▸ hz_bar : z ∈ A ∪ B) with hzA | hzB
      · have : z ∈ V(Q) ∩ A := ⟨hzQ, hzA⟩
        rw [hQ_ft.2.1, mem_singleton_iff] at this
        exact hz_not_ends.1 this
      · have : z ∈ V(Q) ∩ B := ⟨hzQ, hzB⟩
        rw [hQ_ft.2.2, mem_singleton_iff] at this
        exact hz_not_ends.2 this
    exact ⟨Q, hQP, a, haA, b, hbB, hQ_omega, hno_int⟩
  choose f hf_le hf_ends using hex_sub
  let P_set' : Set (Graph α β) := range f
  have hf_inj : Function.Injective f := by
    intro P₁ P₂ heq
    by_contra hne
    obtain ⟨a₁, _, _, _, hQ₁, _⟩ := hf_ends P₁
    have ha₁_Q₂ : a₁ ∈ V(f P₂) := heq ▸ hQ₁.1.left_mem
    exact disjoint_left.mp (hdisj.2 P₁.2 P₂.2 (Subtype.ext_iff.not.mp hne))
      ((hf_le P₁).vertexSet_mono hQ₁.1.left_mem)
      ((hf_le P₂).vertexSet_mono ha₁_Q₂)
  have hcard_eq : P_set'.ncard = P_set.ncard := by
    have h_img : P_set' = (fun P : Graph α β => if h : P ∈ P_set then f ⟨P, h⟩ else P) '' P_set
      := by
      ext Q
      simp only [P_set', mem_range, mem_image]
      exact ⟨by rintro ⟨⟨P, hP⟩, rfl⟩; exact ⟨P, hP, by simp [hP]⟩,
        by rintro ⟨P, hP, rfl⟩; exact ⟨⟨P, hP⟩, by simp [hP]⟩⟩
    rw [h_img]
    refine Set.InjOn.ncard_image fun P₁ h₁ P₂ h₂ heq => ?_
    simp only [h₁, h₂, ↓reduceDIte] at heq
    exact Subtype.ext_iff.mp (hf_inj heq)
  refine ⟨P_set', ⟨A, B, ⟨?_, ?_⟩, hfence, ?_⟩, hcard_eq, ?_⟩
  · rintro Q ⟨P, rfl⟩
    obtain ⟨a, _, b, _, hQ, _⟩ := hf_ends P
    exact ⟨a, b, hQ⟩
  · rintro Q₁ ⟨P₁, rfl⟩ Q₂ ⟨P₂, rfl⟩ hne
    exact (hdisj.2 P₁.2 P₂.2 (fun h => hne (congrArg f (Subtype.ext h)))).mono
      (hf_le P₁).vertexSet_mono (hf_le P₂).vertexSet_mono
  · rintro Q ⟨P, rfl⟩
    obtain ⟨a, haA, b, hbB, hQ, _⟩ := hf_ends P
    exact ⟨a, haA, b, hbB, hQ⟩
  · rintro Q ⟨P, rfl⟩
    obtain ⟨_, _, _, _, _, hno_int⟩ := hf_ends P
    exact hno_int

/-- If `(G, Ω)` has a transaction of cardinality `3p + 8`, then we may choose a transaction `P_set`
in `(G, Ω)` satisfying `(a)`, `(b)`, and `(c)` (Graph Minors IX, Section 6, page 56:
"We claim that we may choose a transaction $\mathcal{P}$ in $(G, \Omega)$ such that (a)
$|\mathcal{P}| = 3p + 8$ (b) for each $P \in \mathcal{P}$, no internal vertex of $P$ is in
$\bar{\Omega}$, and (c) subject to (a) and (b), $C(\mathcal{P})$ is maximal."). -/
theorem exists_transaction_with_max_coveredComponentUnion {p : ℕ}
    (hex : ∃ P_set₀ : Set (Graph α β), S.IsTransaction P_set₀ ∧ P_set₀.ncard = 3 * p + 8) :
    ∃ P_set : Set (Graph α β),
      S.IsTransaction P_set ∧
      P_set.ncard = 3 * p + 8 ∧
      (∀ P ∈ P_set, Disjoint (pathInternalVerts S.G P) S.Ω.bar) ∧
      (∀ P_set' : Set (Graph α β),
        S.IsTransaction P_set' →
        P_set'.ncard = 3 * p + 8 →
        (∀ P' ∈ P_set', Disjoint (pathInternalVerts S.G P') S.Ω.bar) →
        S.coveredComponentUnion P_set ⊆ S.coveredComponentUnion P_set' →
        S.coveredComponentUnion P_set = S.coveredComponentUnion P_set') := by
  classical
  obtain ⟨P_set₀, htrans₀, hcard₀⟩ := hex
  obtain ⟨P_set₁, htrans₁, hcard₁, hno_int₁⟩ := S.exists_transaction_no_internal_in_bar htrans₀
  have hcard₁' : P_set₁.ncard = 3 * p + 8 := hcard₁.trans hcard₀
  let Cand (P_set : Set (Graph α β)) : Prop :=
    S.IsTransaction P_set ∧
      P_set.ncard = 3 * p + 8 ∧
      ∀ P ∈ P_set, Disjoint (pathInternalVerts S.G P) S.Ω.bar
  have hCand₁ : Cand P_set₁ := ⟨htrans₁, hcard₁', hno_int₁⟩
  have hC_sub_V : ∀ P_set, S.coveredComponentUnion P_set ⊆ V(S.G) := fun _ _ hv => hv.1
  have hex_gap : ∃ k : ℕ, ∃ P_set : Set (Graph α β),
      Cand P_set ∧ V(S.G).ncard - (S.coveredComponentUnion P_set).ncard = k :=
    ⟨_, P_set₁, hCand₁, rfl⟩
  let k₀ := Nat.find hex_gap
  obtain ⟨P_set, ⟨htrans, hcard, hno_int⟩, hk₀⟩ := Nat.find_spec hex_gap
  refine ⟨P_set, htrans, hcard, hno_int, fun P_set' htrans' hcard' hno_int' hsub => ?_⟩
  have hmin : k₀ ≤ V(S.G).ncard - (S.coveredComponentUnion P_set').ncard :=
    Nat.find_min' hex_gap ⟨P_set', ⟨htrans', hcard', hno_int'⟩, rfl⟩
  have hle_V : (S.coveredComponentUnion P_set').ncard ≤ V(S.G).ncard :=
    ncard_le_ncard (hC_sub_V P_set') S.finite_V
  have hle_C : (S.coveredComponentUnion P_set').ncard ≤ (S.coveredComponentUnion P_set).ncard := by
    omega
  exact Set.eq_of_subset_of_ncard_le hsub hle_C (S.finite_V.subset (hC_sub_V P_set'))

/-! ## Connected subgraphs avoiding the separator of a graph separation -/

/-- If `(G₁, G₂)` is a separation of `G` and `C ≤ G` is a connected subgraph avoiding `V(G₁) ∩
V(G₂)`
that meets `V(G₂)`, then `V(C) ⊆ V(G₂) \ V(G₁)` (and in particular `Disjoint V(C) V(G₁)`). -/
theorem connected_subset_right_of_avoids_inter {G G₁ G₂ C : Graph α β}
    (hsep : IsGraphSeparation G G₁ G₂)
    (hCG : C ≤ G)
    (hconn : IsGraphConnected C)
    (hav : Disjoint V(C) (V(G₁) ∩ V(G₂)))
    (hne : (V(C) ∩ V(G₂)).Nonempty) :
    V(C) ⊆ V(G₂) \ V(G₁) := by
  obtain ⟨y₀, hy₀C, hy₀G₂⟩ := hne
  have hwalk_in_G₂ : ∀ {u v : α} (W : GraphWalk G u v),
      (∀ z ∈ W.support, z ∈ V(C)) → u ∈ V(G₂) → v ∈ V(G₂) := by
    intro u v W
    induction W with
    | nil _ => intro _ hu; exact hu
    | @cons x w z e hlink W_tail ih =>
      intro hsupp hxG₂
      have hxC : x ∈ V(C) := hsupp x List.mem_cons_self
      have hx_not_G₁ : x ∉ V(G₁) :=
        fun hxG₁ => disjoint_left.mp hav hxC ⟨hxG₁, hxG₂⟩
      have he_G₂ : e ∈ E(G₂) := by
        rcases hsep.2.2.2.1 ▸ hlink.edge_mem with he₁ | he₂
        · exact (hx_not_G₁ ((hsep.1.isLink_iff he₁).mpr hlink).left_mem).elim
        · exact he₂
      have hwG₂ : w ∈ V(G₂) := ((hsep.2.1.isLink_iff he_G₂).mpr hlink).right_mem
      exact ih (fun q hq => hsupp q (List.mem_cons_of_mem x hq)) hwG₂
  intro v hvC
  obtain ⟨W_C⟩ := hconn.2 y₀ hy₀C v hvC
  obtain ⟨W_G, hs_G, _⟩ := exists_walk_up_of_le hCG W_C
  have hvG₂ : v ∈ V(G₂) := hwalk_in_G₂ W_G
    (fun z hz => W_C.mem_vertexSet_of_mem_support (hs_G ▸ hz)) hy₀G₂
  exact ⟨hvG₂, fun hvG₁ => disjoint_left.mp hav hvC ⟨hvG₁, hvG₂⟩⟩

/-- For a separating `Ω`-path `P` with ends `a, b` and no internal vertex in `ΩBar`, there is a
canonical separation `(G₁, G₂)` of `G` with `G₂` minimal such that `V(G₁) ∩ V(G₂) = V(P)`,
`P ≤ G₁`, `Ω(a, b) ⊆ V(G₁)`, `Ω(b, a) ⊆ V(G₂)`, `G₁ = G \ V(H)` is induced, and `Ω(b, a)` catches
`H = G₂ \ V(G₁)` (Graph Minors IX, Section 6, pages 56–57:
"Let $(G_1, G_2)$ be a separation of $G$ with $V(P) = V(G_1 \cap G_2)$,
$\Omega(a, b) \subseteq V(G_1)$ and $\Omega(b, a) \subseteq V(G_2)$, chosen so that $G_2$ is
minimal... Let $H = G_2 \setminus V(G_1)$. By the minimality of $G_2$, $\Omega(b, a)$ catches $H$,
and $G_1$ is an induced subgraph of $G$."). -/
theorem exists_minimal_separation_of_separating {P : Graph α β} {a b : α}
    (hP_ends : S.IsOmegaPathWithEnds P a b)
    (hP_sep : S.IsSeparatingOmegaPath P)
    (hno_intP : Disjoint (pathInternalVerts S.G P) S.Ω.bar) :
    ∃ G₁ G₂ H : Graph α β,
      IsGraphSeparation S.G G₁ G₂ ∧
      V(G₁) ∩ V(G₂) = V(P) ∧
      P ≤ G₁ ∧
      S.Ω.interval a b ⊆ V(G₁) ∧
      S.Ω.interval b a ⊆ V(G₂) ∧
      H ≤ S.G ∧
      H = deleteVertices G₂ V(G₁) ∧
      H = deleteVertices S.G V(G₁) ∧
      V(H) = V(S.G) \ V(G₁) ∧
      G₁ = deleteVertices S.G V(H) ∧
      Catches (S.Ω.interval b a) H := by
  let K := deleteVertices S.G V(P)
  have hKG : K ≤ S.G := deleteVertices_le S.G V(P)
  let V_H : Set α := {v ∈ V(K) | ∃ u ∈ S.Ω.interval b a, Nonempty (GraphWalk K v u)}
  have hVH_sub_K : V_H ⊆ V(K) := fun _ hv => hv.1
  have hVH_sub_G : V_H ⊆ V(S.G) := fun _ hv => hv.1.1
  have hVP_bar : V(P) ∩ S.Ω.bar = {a, b} := hP_ends.vertexSet_inter_bar_eq S hno_intP
  have hab_in_K : S.Ω.interval a b ⊆ V(K) := by
    intro s hs
    refine ⟨S.bar_subset hs.1.1, fun hsP => ?_⟩
    have hs_ab : s ∈ ({a, b} : Set α) := hVP_bar ▸ ⟨hsP, hs.1.1⟩
    exact hs.1.2 hs_ab
  have hba_in_K : S.Ω.interval b a ⊆ V(K) := by
    intro t ht
    refine ⟨S.bar_subset ht.1.1, fun htP => ?_⟩
    have ht_ab : t ∈ ({a, b} : Set α) := hVP_bar ▸ ⟨htP, ht.1.1⟩
    rw [pair_comm] at ht_ab
    exact ht.1.2 ht_ab
  have hba_in_VH : S.Ω.interval b a ⊆ V_H :=
    fun t ht => ⟨hba_in_K ht, t, ht, ⟨.nil (hba_in_K ht)⟩⟩
  -- Show `Disjoint V_H (S.Ω.interval a b)` using `S.IsSeparatingOmegaPath P`.
  have hdisj_VH_ab : Disjoint V_H (S.Ω.interval a b) := by
    rw [disjoint_left]
    rintro s ⟨_, t, ht_ba, ⟨W_K⟩⟩ hs_ab
    obtain ⟨W_G, _, _⟩ := exists_walk_up_of_le hKG W_K
    obtain ⟨P', hP'_K, _, _⟩ := exists_isGraphPathWithEnds_of_walk W_K
    have hP'_G : IsGraphPathWithEnds S.G P' s t := hP'_K.mono hKG
    have hst_ne : s ≠ t :=
      fun h => disjoint_left.mp (S.Ω.disjoint_interval_swap a b) hs_ab (h ▸ ht_ba)
    have hP'_omega : S.IsOmegaPathWithEnds P' s t := ⟨hP'_G, hst_ne, hs_ab.1.1, ht_ba.1.1⟩
    have hdisj_P'P : Disjoint V(P') V(P) := by
      rw [disjoint_left]
      intro z hzP' hzP
      exact (hP'_K.le.vertexSet_mono hzP').2 hzP
    have hcr : S.Ω.Crosses s t a b :=
      (S.Ω.crosses_iff_interval.mpr (Or.inl ⟨hs_ab, ht_ba⟩)).symm
    exact hP_sep.2 ⟨P', hdisj_P'P, s, t, a, b, hP'_omega, hP_ends, hcr⟩
  -- No edge of `K` joins `V_H` to `V(K) \ V_H`.
  have hVH_closed_K : ∀ {e : β} {x y : α}, K.IsLink e x y → x ∈ V_H → y ∈ V_H := by
    rintro e x y hxy ⟨_, u, hu_ba, ⟨W_xu⟩⟩
    exact ⟨hxy.right_mem, u, hu_ba, ⟨.cons hxy.symm W_xu⟩⟩
  let H := S.G.induce V_H
  let G₁ := deleteVertices S.G V_H
  let G₂ := (S.G.induce (V_H ∪ V(P))).restrict (E(S.G) \ E(G₁))
  have hHG : H ≤ S.G := S.G.induce_le hVH_sub_G
  have hG₁G : G₁ ≤ S.G := deleteVertices_le S.G V_H
  have hG₂G : G₂ ≤ S.G :=
    restrict_le.trans (S.G.induce_le (union_subset hVH_sub_G hP_ends.1.le.vertexSet_mono))
  have hVG₁ : V(G₁) = V(S.G) \ V_H := rfl
  have hVG₂ : V(G₂) = V_H ∪ V(P) := rfl
  have hdisj_VH_P : Disjoint V_H V(P) := by
    rw [disjoint_left]
    exact fun _ hz hzP => hz.1.2 hzP
  have hVP_sub_G₁ : V(P) ⊆ V(G₁) :=
    subset_sdiff.mpr ⟨hP_ends.1.le.vertexSet_mono, hdisj_VH_P.symm⟩
  have hP_G₁ : P ≤ G₁ := le_deleteVertices hP_ends.1.le hdisj_VH_P.symm
  have hEG₂ : E(G₂) = E(S.G) \ E(G₁) := by
    change E(S.G.induce (V_H ∪ V(P))) ∩ (E(S.G) \ E(G₁)) = E(S.G) \ E(G₁)
    rw [inter_eq_right]
    rintro e ⟨heG, he_not_G₁⟩
    obtain ⟨x, y, hxy⟩ := S.G.exists_isLink_of_mem_edgeSet heG
    have hxy_VH : x ∈ V_H ∨ y ∈ V_H := by
      by_contra hnot
      push Not at hnot
      exact he_not_G₁ ((deleteVertices_isLink S.G V_H).mpr ⟨hxy, hnot.1, hnot.2⟩).edge_mem
    refine ⟨x, y, hxy, ?_, ?_⟩
    · rcases hxy_VH with hxVH | hyVH
      · exact Or.inl hxVH
      · by_cases hxP : x ∈ V(P)
        · exact Or.inr hxP
        · have hxyK : K.IsLink e y x :=
            (deleteVertices_isLink S.G V(P)).mpr ⟨hxy.symm, hyVH.1.2, hxP⟩
          exact Or.inl (hVH_closed_K hxyK hyVH)
    · rcases hxy_VH with hxVH | hyVH
      · by_cases hyP : y ∈ V(P)
        · exact Or.inr hyP
        · have hxyK : K.IsLink e x y :=
            (deleteVertices_isLink S.G V(P)).mpr ⟨hxy, hxVH.1.2, hyP⟩
          exact Or.inl (hVH_closed_K hxyK hxVH)
      · exact Or.inl hyVH
  have hsep : IsGraphSeparation S.G G₁ G₂ := by
    refine ⟨hG₁G, hG₂G, ?_, ?_, hEG₂ ▸ disjoint_sdiff_self_right⟩
    · rw [hVG₁, hVG₂]
      ext z
      simp only [mem_union, mem_sdiff]
      constructor
      · rintro (⟨hzG, _⟩ | hzVH | hzP)
        · exact hzG
        · exact hVH_sub_G hzVH
        · exact hP_ends.1.le.vertexSet_mono hzP
      · intro hzG
        by_cases hz : z ∈ V_H
        · exact Or.inr (Or.inl hz)
        · exact Or.inl ⟨hzG, hz⟩
    · rw [hEG₂]
      exact union_sdiff_cancel hG₁G.edgeSet_mono
  have hinter : V(G₁) ∩ V(G₂) = V(P) := by
    rw [hVG₁, hVG₂]
    ext z
    simp only [mem_inter_iff, mem_sdiff, mem_union]
    constructor
    · rintro ⟨⟨_, hz_not⟩, hzVH | hzP⟩
      · exact (hz_not hzVH).elim
      · exact hzP
    · intro hzP
      exact ⟨hVP_sub_G₁ hzP, Or.inr hzP⟩
  have hab_G₁ : S.Ω.interval a b ⊆ V(G₁) :=
    subset_sdiff.mpr ⟨(S.Ω.interval_subset_bar a b).trans S.bar_subset, hdisj_VH_ab.symm⟩
  have hba_G₂ : S.Ω.interval b a ⊆ V(G₂) := hba_in_VH.trans subset_union_left
  have hVH_eq_diff : V_H = V(S.G) \ V(G₁) := by
    rw [hVG₁, Set.sdiff_sdiff_right_self, inter_eq_right.mpr hVH_sub_G]
  have hH_del_G : H = deleteVertices S.G V(G₁) := by
    change S.G.induce V_H = S.G.induce (V(S.G) \ V(G₁))
    rw [hVH_eq_diff]
  have hH_del_G₂ : H = deleteVertices G₂ V(G₁) := by
    refine (Compatible.of_le_le hHG ((deleteVertices_le G₂ V(G₁)).trans hG₂G)).ext ?_ ?_
    · change V_H = (V_H ∪ V(P)) \ V(G₁)
      ext z
      simp only [mem_sdiff, mem_union]
      constructor
      · intro hz
        exact ⟨Or.inl hz, fun hzG₁ => hzG₁.2 hz⟩
      · rintro ⟨hzVH | hzP, hz_not_G₁⟩
        · exact hzVH
        · exact (hz_not_G₁ (hVP_sub_G₁ hzP)).elim
    · apply Subset.antisymm
      · intro e heH
        obtain ⟨x, y, hxy, hxVH, hyVH⟩ := heH
        have he_not_G₁ : e ∉ E(G₁) := by
          rintro ⟨x', y', hxy', hx'G₁, hy'G₁⟩
          rcases hxy.left_eq_or_eq hxy' with rfl | rfl
          · exact hx'G₁.2 hxVH
          · exact hy'G₁.2 hxVH
        have hxyG₂ : G₂.IsLink e x y :=
          (hG₂G.isLink_iff (by rw [hEG₂]; exact ⟨hxy.edge_mem, he_not_G₁⟩)).mpr hxy
        exact ((deleteVertices_isLink G₂ V(G₁)).mpr
          ⟨hxyG₂, fun h => h.2 hxVH, fun h => h.2 hyVH⟩).edge_mem
      · intro e he_del
        obtain ⟨x, y, hxy⟩ := (deleteVertices G₂ V(G₁)).exists_isLink_of_mem_edgeSet he_del
        rw [deleteVertices_isLink] at hxy
        have hxyG : S.G.IsLink e x y := hxy.1.mono hG₂G
        have hxVH : x ∈ V_H := by
          rcases hxy.1.left_mem with hx | hxP
          · exact hx
          · exact (hxy.2.1 (hVP_sub_G₁ hxP)).elim
        have hyVH : y ∈ V_H := by
          rcases hxy.1.right_mem with hy | hyP
          · exact hy
          · exact (hxy.2.2 (hVP_sub_G₁ hyP)).elim
        exact ⟨x, y, hxyG, hxVH, hyVH⟩
  -- Prove `Catches (S.Ω.interval b a) H`.
  have hcatch_H : Catches (S.Ω.interval b a) H := by
    refine ⟨hba_in_VH, fun D hD => ?_⟩
    obtain ⟨v₀, hv₀D⟩ := hD.2.1.1
    have hv₀_VH : v₀ ∈ V_H := hD.1.vertexSet_mono hv₀D
    rcases hv₀_VH with ⟨_, u₀, hu₀_ba, ⟨W_K⟩⟩
    -- Every vertex of `W_K.support` is in `V_H = V(H)` and every edge of `W_K.edges` is in `E(H)`.
    have hsupp_VH : ∀ z ∈ W_K.support, z ∈ V_H := by
      have hwalk : ∀ {p q : α} (W : GraphWalk K p q), q ∈ V_H → ∀ z ∈ W.support, z ∈ V_H := by
        intro p q W
        induction W with
        | nil _ =>
          intro hq z hz
          simp only [GraphWalk.support_nil, List.mem_singleton] at hz
          exact hz ▸ hq
        | @cons x y w e hlink W_tail ih =>
          intro hw z hz
          have hy_VH : y ∈ V_H := ih hw y W_tail.start_mem_support
          have hx_VH : x ∈ V_H := hVH_closed_K hlink.symm hy_VH
          rcases List.mem_cons.mp hz with rfl | hz_tail
          · exact hx_VH
          · exact ih hw z hz_tail
      exact hwalk W_K (hba_in_VH hu₀_ba)
    obtain ⟨W_G, hs_G, he_G⟩ := exists_walk_up_of_le hKG W_K
    have hedges_H : ∀ e ∈ W_G.edges, e ∈ E(H) := by
      intro e he
      have heK : e ∈ E(K) := walk_edges_subset_edgeSet W_K e (he_G ▸ he)
      obtain ⟨x, y, hxyK⟩ := K.exists_isLink_of_mem_edgeSet heK
      have hhm := walk_isLink_mem_support W_K (he_G ▸ he) hxyK
      exact ⟨x, y, hxyK.mono hKG, hsupp_VH x hhm.1, hsupp_VH y hhm.2⟩
    obtain ⟨W_H, _, _⟩ := exists_walk_down_of_le hHG W_G
      (fun z hz => hsupp_VH z (hs_G ▸ hz)) hedges_H
    -- Since `W_H` is a walk in `H` from `v₀ ∈ V(D)` to `u₀`, `u₀ ∈ V(D)`.
    have hwalk_D : ∀ {p q : α} (W : GraphWalk H p q), p ∈ V(D) → q ∈ V(D) := by
      intro p q W
      induction W with
      | nil _ => intro hp; exact hp
      | @cons x y w e hlink W_tail ih =>
        intro hxD
        exact ih ((mem_graphComponent_iff_of_isLink hD hlink).mp hxD)
    exact ⟨u₀, hu₀_ba, hwalk_D W_H hv₀D⟩
  exact ⟨G₁, G₂, H, hsep, hinter, hP_G₁, hab_G₁, hba_G₂, hHG, hH_del_G₂, hH_del_G,
    hVH_eq_diff, rfl, hcatch_H⟩

/-! ## Counterexample properties (1)–(4) and Claims (5)–(9) (pages 55–57) -/

/-- Properties `(1)–(4)` of a minimal counterexample `(G, Ω)` in the proof of (6.1)
(Graph Minors IX, Section 6, pages 55–56):
- `(1)` "`G` is simple."
- `(2)` "No vertex `v ∈ ΩBar` is isolated."
- `(3)` "If $v \in \bar{\Omega}$ has valency 1, then its neighbor is in $\bar{\Omega}$."
- `(4)` "If $u, v \in \bar{\Omega}$ are distinct and $\Omega(u, v) = \emptyset$, then $u$ and $v$
  are
not adjacent in $G$." -/
structure CounterexampleProperties : Prop where
  /-- (1) "`G` is simple." -/
  isSimple : IsSimpleGraph S.G
  /-- (2) "No vertex `v ∈ ΩBar` is isolated." -/
  no_isolated_in_bar : ∀ v ∈ S.Ω.bar, ∃ u : α, S.G.Adj v u
  /-- (3) "If $v \in \bar{\Omega}$ has valency 1, then its neighbor is in $\bar{\Omega}$." -/
  neighbor_in_bar_of_degree_one : ∀ v ∈ S.Ω.bar, ∀ u : α,
    S.G.Adj v u → (∀ w : α, S.G.Adj v w → w = u) → u ∈ S.Ω.bar
  /-- (4) "If $u, v \in \bar{\Omega}$ are distinct and $\Omega(u, v) = \emptyset$, then $u$ and $v$
  are
not adjacent in $G$." -/
  not_adj_of_interval_empty : ∀ u ∈ S.Ω.bar, ∀ v ∈ S.Ω.bar,
    u ≠ v → S.Ω.interval u v = ∅ → ¬ S.G.Adj u v

/-- **Graph Minors IX, (6.1), Claim (5)** (page 56):
"If $P'$ is an $\Omega$-path with $P' \subseteq G_1$, then $C(\mathcal{P}) \subseteq
C((\mathcal{P} - \{P\}) \cup \{P'\})$." -/
theorem lemma_6_1_claim_5 {P_set : Set (Graph α β)} {P P' G₁ G₂ : Graph α β} {a b : α}
    (htrans : S.IsTransaction P_set)
    (hcard : 2 ≤ P_set.ncard)
    (_hno_int : ∀ R ∈ P_set, Disjoint (pathInternalVerts S.G R) S.Ω.bar)
    (hP_in : P ∈ P_set)
    (hP_ends : S.IsOmegaPathWithEnds P a b)
    (hd_ab : Disjoint (S.Ω.interval a b) (S.transactionEnds P_set))
    (hsep : IsGraphSeparation S.G G₁ G₂)
    (hinter : V(G₁) ∩ V(G₂) = V(P))
    (_hab_G₁ : S.Ω.interval a b ⊆ V(G₁))
    (hba_G₂ : S.Ω.interval b a ⊆ V(G₂))
    (_hP'_omega : S.IsOmegaPath P')
    (hP'_le : P' ≤ G₁)
    (hU_sub : S.transactionPeripheralUnion P_set ⊆
      S.transactionPeripheralUnion ((P_set \ {P}) ∪ {P'}))
    (hper_sub : ∀ R ∈ (P_set \ {P}) ∪ {P'},
      S.IsPeripheralIn ((P_set \ {P}) ∪ {P'}) R → R = P' ∨ S.IsPeripheralIn P_set R) :
    S.coveredComponentUnion P_set ⊆ S.coveredComponentUnion ((P_set \ {P}) ∪ {P'}) := by
  have hperP : S.IsPeripheralIn P_set P := ⟨hP_in, a, b, hP_ends, Or.inl hd_ab⟩
  obtain ⟨_, hU_P⟩ := S.peripheralIntervalSet_eq_interval htrans hcard hP_in hP_ends hd_ab
  have hU_sub_ba : S.transactionPeripheralUnion P_set ⊆ S.Ω.interval b a := by
    intro u hu
    rw [← hU_P]
    exact mem_iInter₂.mp hu.2 P ⟨hP_in, hperP⟩
  intro v ⟨hvG, u, huU, Q, hQ, hav⟩
  have hu_G₂ : u ∈ V(G₂) := hba_G₂ (hU_sub_ba huU)
  have hav_P : Disjoint V(Q) (V(G₁) ∩ V(G₂)) := by
    rw [hinter]
    exact (hav P hP_in hperP).symm
  have hVQ_sub : V(Q) ⊆ V(G₂) \ V(G₁) :=
    connected_subset_right_of_avoids_inter hsep hQ.le hQ.isGraphConnected hav_P
      ⟨u, hQ.right_mem, hu_G₂⟩
  have hav_P' : Avoids Q V(P') := by
    rw [Avoids, disjoint_left]
    intro z hzP' hzQ
    exact (hVQ_sub hzQ).2 (hP'_le.vertexSet_mono hzP')
  refine ⟨hvG, u, hU_sub huU, Q, hQ, fun R hR_in hperR => ?_⟩
  rcases hper_sub R hR_in hperR with rfl | hperR_old
  · exact hav_P'
  · exact hav R hperR_old.1 hperR_old

/-- Under the separation `(G₁, G₂)` of `S.G` with `V(G₁) ∩ V(G₂) = V(P)` and
`Disjoint (S.Ω.interval a b) (S.transactionEnds P_set)`, every member `R ∈ P_set \ {P}` has both
ends in `S.Ω.interval b a` and satisfies `V(R) ⊆ V(G₂) \ V(G₁)`. -/
theorem sdiff_singleton_subset_right_of_separation {P_set : Set (Graph α β)}
    {P G₁ G₂ R : Graph α β} {a b a_R b_R : α}
    (htrans : S.IsTransaction P_set)
    (hP_in : P ∈ P_set)
    (hP_ends : S.IsOmegaPathWithEnds P a b)
    (hd_ab : Disjoint (S.Ω.interval a b) (S.transactionEnds P_set))
    (hsep : IsGraphSeparation S.G G₁ G₂)
    (hinter : V(G₁) ∩ V(G₂) = V(P))
    (hba_G₂ : S.Ω.interval b a ⊆ V(G₂))
    (hR : R ∈ P_set \ {P})
    (hR_ends : S.IsOmegaPathWithEnds R a_R b_R) :
    a_R ∈ S.Ω.interval b a ∧ b_R ∈ S.Ω.interval b a ∧ V(R) ⊆ V(G₂) \ V(G₁) := by
  obtain ⟨_, _, hfence⟩ := htrans
  have hdisj_RP : Disjoint V(R) V(P) := hfence.1.2 hR.1 hP_in hR.2
  have ha_ne_a : a_R ≠ a :=
    fun h => disjoint_left.mp hdisj_RP hR_ends.1.left_mem (h ▸ hP_ends.1.left_mem)
  have ha_ne_b : a_R ≠ b :=
    fun h => disjoint_left.mp hdisj_RP hR_ends.1.left_mem (h ▸ hP_ends.1.right_mem)
  have hb_ne_a : b_R ≠ a :=
    fun h => disjoint_left.mp hdisj_RP hR_ends.1.right_mem (h ▸ hP_ends.1.left_mem)
  have hb_ne_b : b_R ≠ b :=
    fun h => disjoint_left.mp hdisj_RP hR_ends.1.right_mem (h ▸ hP_ends.1.right_mem)
  have ha_W : a_R ∈ S.transactionEnds P_set := hR_ends.mem_transactionEnds_left S hR.1
  have hb_W : b_R ∈ S.transactionEnds P_set := hR_ends.mem_transactionEnds_right S hR.1
  have ha_ba : a_R ∈ S.Ω.interval b a :=
    (S.Ω.mem_interval_or_interval_swap hP_ends.2.2.1 hP_ends.2.2.2 hR_ends.2.2.1
      hP_ends.2.1 ha_ne_a ha_ne_b).resolve_left (fun h => disjoint_left.mp hd_ab h ha_W)
  have hb_ba : b_R ∈ S.Ω.interval b a :=
    (S.Ω.mem_interval_or_interval_swap hP_ends.2.2.1 hP_ends.2.2.2 hR_ends.2.2.2
      hP_ends.2.1 hb_ne_a hb_ne_b).resolve_left (fun h => disjoint_left.mp hd_ab h hb_W)
  have hav_inter : Disjoint V(R) (V(G₁) ∩ V(G₂)) := hinter ▸ hdisj_RP
  have hVR : V(R) ⊆ V(G₂) \ V(G₁) :=
    connected_subset_right_of_avoids_inter hsep hR_ends.1.le hR_ends.1.isGraphConnected hav_inter
      ⟨a_R, hR_ends.1.left_mem, hba_G₂ ha_ba⟩
  exact ⟨ha_ba, hb_ba, hVR⟩

private theorem preservePeripheralIntervals
    {S : Society α β} {P_set : Set (Graph α β)} {P : Graph α β} {a b : α} (hP_in : P ∈ P_set)
    (hP_ends : S.IsOmegaPathWithEnds P a b) (htrans_orig : S.IsTransaction P_set) {A B : Set α}
    (hfence : S.IsFenceFor P_set A B) {P'' : Graph α β} {u₀ v₀ : α}
    (hW'_bar : (S.transactionEnds (P_set \ {P})) ⊆ S.Ω.bar) {a'_0 : α}
    (ha'_0 : a'_0 ∈ A ∩ (S.transactionEnds (P_set \ {P}))) {b_0 : α}
    (hb_0 : b_0 ∈ B ∩ (S.transactionEnds (P_set \ {P})))
    (hd'_ab : Disjoint (S.Ω.interval a'_0 b_0) (S.transactionEnds (P_set \ {P}))) {b'_0 : α}
    (hb'_0 : b'_0 ∈ B ∩ (S.transactionEnds (P_set \ {P}))) {a_0 : α}
    (ha_0 : a_0 ∈ A ∩ (S.transactionEnds (P_set \ {P})))
    (hd'_ba : Disjoint (S.Ω.interval b'_0 a_0) (S.transactionEnds (P_set \ {P})))
    (hI_sub_G₁ : {a, b} ∪ S.Ω.interval a b ⊆ S.Ω.interval a'_0 b_0)
    (hu₀_G₁ : u₀ ∈ S.Ω.interval a'_0 b_0)
    (hG₂_sub_b'a' : S.Ω.interval b'_0 a_0 ⊆ S.Ω.interval b'_0 a'_0)
    (hG₁_sub_a'b' : S.Ω.interval a'_0 b_0 ⊆ S.Ω.interval a'_0 b'_0)
    (hdisj_P_arcs : Disjoint ({a'_0} ∪ S.Ω.interval b'_0 a'_0) ({b'_0} ∪ S.Ω.interval a'_0 b'_0))
    (hfence_f : S.Ω.IsFence (S.Ω.interval b'_0 v₀) ({b'_0, v₀} ∪ S.Ω.interval v₀ b'_0))
    (hA_W'_Af : A ∩ (S.transactionEnds (P_set \ {P})) ⊆ (S.Ω.interval b'_0 v₀))
    (hB_W'_Bf : B ∩ (S.transactionEnds (P_set \ {P})) ⊆ ({b'_0, v₀} ∪ S.Ω.interval v₀ b'_0))
    (hu₀_Af : u₀ ∈ (S.Ω.interval b'_0 v₀)) (hv₀_Bf : v₀ ∈ ({b'_0, v₀} ∪ S.Ω.interval v₀ b'_0))
    (htrans' : S.IsTransaction (P_set \ {P} ∪ {P''})) (hcard_ge2 : 2 ≤ P_set.ncard)
    (hcard'_ge2 : 2 ≤ (P_set \ {P} ∪ {P''}).ncard)
    (hW_new_bar : (S.transactionEnds (P_set \ {P} ∪ {P''})) ⊆ S.Ω.bar)
    (hW_new_eq : (S.transactionEnds (P_set \ {P} ∪ {P''})) = (S.transactionEnds (P_set \ {P})) ∪
      {u₀, v₀})
    (hd_uv_new : Disjoint (S.Ω.interval u₀ v₀) (S.transactionEnds (P_set \ {P} ∪ {P''})))
    {R : Graph α β} (hR : R ∈ P_set \ {P}) (hperR' : S.IsPeripheralIn (P_set \ {P} ∪ {P''}) R) :
    S.IsPeripheralIn P_set R ∧ S.peripheralIntervalSet (P_set \ {P} ∪ {P''}) R =
      S.peripheralIntervalSet P_set R ∧ S.Ω.interval a'_0 b_0 ⊆ S.peripheralIntervalSet (P_set \
      {P} ∪ {P''}) R := by
  classical
  let W := S.transactionEnds P_set
  let W' := S.transactionEnds (P_set \ {P})
  let A_f := S.Ω.interval b'_0 v₀
  let B_f := {b'_0, v₀} ∪ S.Ω.interval v₀ b'_0
  let P_set' := P_set \ {P} ∪ {P''}
  let W_new := S.transactionEnds P_set'
  have hW_eq : W_new = W' ∪ {u₀, v₀} := hW_new_eq
  obtain ⟨a_R, ha_R_A, b_R, hb_R_B, hR_ends⟩ := hfence.2.2 R hR.1
  have ha_R_W' : a_R ∈ A ∩ W' := ⟨ha_R_A, hR_ends.mem_transactionEnds_left S hR⟩
  have hb_R_W' : b_R ∈ B ∩ W' := ⟨hb_R_B, hR_ends.mem_transactionEnds_right S hR⟩
  have ha_R_Af : a_R ∈ A_f ∩ W_new := ⟨hA_W'_Af ha_R_W', hW_eq ▸ Or.inl ha_R_W'.2⟩
  have hb_R_Bf : b_R ∈ B_f ∩ W_new := ⟨hB_W'_Bf hb_R_W', hW_eq ▸ Or.inl hb_R_W'.2⟩
  have hu₀_Af_W : u₀ ∈ A_f ∩ W_new := ⟨hu₀_Af, hW_eq ▸ Or.inr (Or.inl rfl)⟩
  have hv₀_Bf_W : v₀ ∈ B_f ∩ W_new := ⟨hv₀_Bf, hW_eq ▸ Or.inr (Or.inr rfl)⟩
  have hd_ba_R_new : Disjoint (S.Ω.interval b_R a_R) W_new := by
    rcases (hR_ends.isPeripheralIn_iff S (Or.inl hR)).mp hperR' with hd_ab_R | hd_ba_R
    · exfalso
      have hu₀_eq : u₀ = a_R :=
        (S.Ω.unique_empty_interval_AB_of_isFence hfence_f hW_new_bar
          hu₀_Af_W hv₀_Bf_W ha_R_Af hb_R_Bf hd_uv_new hd_ab_R).1
      exact disjoint_left.mp hd'_ab hu₀_G₁ (hu₀_eq ▸ ha_R_W'.2)
    · exact hd_ba_R
  have hd_ba_R_W' : Disjoint (S.Ω.interval b_R a_R) W' :=
    hd_ba_R_new.mono_right (hW_eq ▸ subset_union_left)
  obtain ⟨rfl, rfl⟩ :=
    S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1.symm hW'_bar
      hb'_0 ha_0 hb_R_W' ha_R_W' hd'_ba hd_ba_R_W'
  have hdisj_G₂_G₁ : Disjoint (S.Ω.interval b'_0 a_0) (S.Ω.interval a'_0 b_0) :=
    (disjoint_union_left.mp (disjoint_union_right.mp hdisj_P_arcs).2).2.mono
      hG₂_sub_b'a' hG₁_sub_a'b'
  have hd_ba_W : Disjoint (S.Ω.interval b'_0 a_0) W := by
    have hW_union : W = W' ∪ {a, b} := hfence.transactionEnds_eq_union S hP_in hP_ends
    rw [hW_union, disjoint_union_right]
    refine ⟨hd'_ba, disjoint_left.mpr fun z hz hab => ?_⟩
    exact disjoint_left.mp hdisj_G₂_G₁ hz (hI_sub_G₁ (Or.inl hab))
  have hperR_old : S.IsPeripheralIn P_set R :=
    ⟨hR.1, a_0, b'_0, hR_ends, Or.inr hd_ba_W⟩
  have hU'_R : S.peripheralIntervalSet P_set' R = S.Ω.interval a_0 b'_0 :=
    (S.peripheralIntervalSet_eq_interval htrans' hcard'_ge2 (Or.inl hR)
      (hR_ends.symm S) hd_ba_R_new).2
  have hU_R : S.peripheralIntervalSet P_set R = S.Ω.interval a_0 b'_0 :=
    (S.peripheralIntervalSet_eq_interval htrans_orig hcard_ge2 hR.1
      (hR_ends.symm S) hd_ba_W).2
  have hG₁_sub_U' : S.Ω.interval a'_0 b_0 ⊆ S.peripheralIntervalSet P_set' R := by
    rw [hU'_R]
    exact S.Ω.interval_subset_of_disjoint_AB hfence.2.1 hW'_bar ha'_0 hb_0 hd'_ab ha_0 hb'_0
  exact ⟨hperR_old, hU'_R.trans hU_R.symm, hG₁_sub_U'⟩

private theorem replacePathWithOrderedEnds
    {S : Society α β} (p : ℕ) {P_set : Set (Graph α β)} {P P' G₁ G₂ : Graph α β} {a b : α}
    (hcard : P_set.ncard = 3 * p + 8)
    (hno_int : ∀ R ∈ P_set, Disjoint (pathInternalVerts S.G R) S.Ω.bar) (hP_in : P ∈ P_set)
    (hP_ends : S.IsOmegaPathWithEnds P a b)
    (hd_ab : Disjoint (S.Ω.interval a b) (S.transactionEnds P_set))
    (hsep : IsGraphSeparation S.G G₁ G₂) (hinter : V(G₁) ∩ V(G₂) = V(P))
    (hab_G₁ : S.Ω.interval a b ⊆ V(G₁)) (hba_G₂ : S.Ω.interval b a ⊆ V(G₂))
    (htrans_orig : S.IsTransaction P_set) {A B : Set α} (hfence : S.IsFenceFor P_set A B)
    (haA : a ∈ A) (hbB : b ∈ B) {P'' : Graph α β} (hP''_le_P' : P'' ≤ P') (hP''_le_G₁ : P'' ≤ G₁)
    (hno_int_P'' : Disjoint (pathInternalVerts S.G P'') S.Ω.bar) {u₀ v₀ x₀ : α}
    (hP''_uv : S.IsOmegaPathWithEnds P'' u₀ v₀) (hu₀_av₀ : u₀ ∈ {a} ∪ S.Ω.interval a v₀)
    (hu₀_ab : u₀ ∈ {a, b} ∪ S.Ω.interval a b) (hv₀_ab : v₀ ∈ {a, b} ∪ S.Ω.interval a b)
    (hx₀_ab : x₀ ∈ ({a, b} : Set α)) (hx₀_vu : x₀ ∈ S.Ω.interval v₀ u₀)
    (huv_sub_ab : S.Ω.interval u₀ v₀ ⊆ S.Ω.interval a b)
    (hba_sub_vu : S.Ω.interval b a ⊆ S.Ω.interval v₀ u₀) :
    ∃ P'' : Graph α β, P'' ≤ P' ∧ S.IsTransaction (P_set \ {P} ∪ {P''}) ∧
      (P_set \ {P} ∪ {P''}).ncard = 3 * p + 8 ∧
      (∀ R ∈ P_set \ {P} ∪ {P''}, Disjoint (pathInternalVerts S.G R) S.Ω.bar) ∧
      S.coveredComponentUnion P_set ⊆ S.coveredComponentUnion (P_set \ {P} ∪ {P''}) ∧ ({a, b} ∩
      S.transactionPeripheralUnion (P_set \ {P} ∪ {P''})).Nonempty := by
  classical
  let W := S.transactionEnds P_set
  let W' := S.transactionEnds (P_set \ {P})
  have hW_bar : W ⊆ S.Ω.bar := S.transactionEnds_subset_bar P_set
  have hW'_bar : W' ⊆ S.Ω.bar := S.transactionEnds_subset_bar (P_set \ {P})
  have hW'_eq : W' = W \ {a, b} := S.transactionEnds_diff_singleton hfence.1 hP_in hP_ends
  have hW'_sub : W' ⊆ W := hW'_eq ▸ sdiff_subset
  have haW : a ∈ A ∩ W := ⟨haA, hP_ends.mem_transactionEnds_left S hP_in⟩
  have hbW : b ∈ B ∩ W := ⟨hbB, hP_ends.mem_transactionEnds_right S hP_in⟩
  have hfin_P : P_set.Finite := hfence.1.finite S
  have hne_diff : (P_set \ {P}).Nonempty := by
    rw [← ncard_pos hfin_P.sdiff, ncard_sdiff_singleton_of_mem hP_in]
    omega
  obtain ⟨R₀, hR₀_diff⟩ := hne_diff
  obtain ⟨a_R₀, ha_R₀_A, b_R₀, hb_R₀_B, hR₀_ends⟩ := hfence.2.2 R₀ hR₀_diff.1
  have ha_R₀_W' : a_R₀ ∈ A ∩ W' := ⟨ha_R₀_A, hR₀_ends.mem_transactionEnds_left S hR₀_diff⟩
  have hb_R₀_W' : b_R₀ ∈ B ∩ W' := ⟨hb_R₀_B, hR₀_ends.mem_transactionEnds_right S hR₀_diff⟩
  have hW'_AB : W' ⊆ A ∪ B := hfence.2.1.2.2.2.1 ▸ hW'_bar
  have hW'_BA : W' ⊆ B ∪ A := union_comm A B ▸ hW'_AB
  obtain ⟨a'_0, ha'_0, b_0, hb_0, hd'_ab⟩ :=
    S.Ω.exists_empty_interval_AB_of_subset_union hW'_bar hW'_AB ⟨a_R₀, ha_R₀_W'⟩ ⟨b_R₀, hb_R₀_W'⟩
  obtain ⟨b'_0, hb'_0, a_0, ha_0, hd'_ba⟩ :=
    S.Ω.exists_empty_interval_AB_of_subset_union hW'_bar hW'_BA ⟨b_R₀, hb_R₀_W'⟩ ⟨a_R₀, ha_R₀_W'⟩
  -- Show `{a, b} ∪ S.Ω.interval a b ⊆ S.Ω.interval a'_0 b_0`.
  have ha'_0_W : a'_0 ∈ A ∩ W := ⟨ha'_0.1, hW'_sub ha'_0.2⟩
  have hb_0_W : b_0 ∈ B ∩ W := ⟨hb_0.1, hW'_sub hb_0.2⟩
  have ha'_0_ne_a : a'_0 ≠ a := fun h => (hW'_eq ▸ ha'_0.2).2 (Or.inl h)
  have hb_0_ne_b : b_0 ≠ b := fun h => (hW'_eq ▸ hb_0.2).2 (Or.inr h)
  have hb_in_G₁ : b ∈ S.Ω.interval a'_0 b_0 :=
    (S.Ω.mem_interval_of_mem_B_of_disjoint_AB hfence.2.1 hW_bar haW hbW hd_ab
      ha'_0_W hb_0_W hb_0_ne_b).1
  have ha_b_a' : a ∈ S.Ω.interval a'_0 b ∧ b ∈ S.Ω.interval a a'_0 :=
    S.Ω.mem_interval_of_mem_A_of_disjoint_AB hfence.2.1 hW_bar haW hbW hd_ab
      ha'_0_W ha'_0_ne_a hbW
  have ha_in_G₁ : a ∈ S.Ω.interval a'_0 b_0 :=
    S.Ω.interval_subset_interval_left hb_in_G₁ ha_b_a'.1
  have hab_sub_G₁ : S.Ω.interval a b ⊆ S.Ω.interval a'_0 b_0 :=
    S.Ω.interval_subset_of_disjoint_AB hfence.2.1 hW_bar haW hbW hd_ab ha'_0_W hb_0_W
  have hI_sub_G₁ : ({a, b} : Set α) ∪ S.Ω.interval a b ⊆ S.Ω.interval a'_0 b_0 := by
    rintro z ((rfl | rfl) | hz)
    · exact ha_in_G₁
    · exact hb_in_G₁
    · exact hab_sub_G₁ hz
  have hu₀_G₁ : u₀ ∈ S.Ω.interval a'_0 b_0 := hI_sub_G₁ hu₀_ab
  have hv₀_G₁ : v₀ ∈ S.Ω.interval a'_0 b_0 := hI_sub_G₁ hv₀_ab
  have ha_in_a'v₀ : a ∈ S.Ω.interval a'_0 v₀ := by
    rcases hv₀_ab with (rfl | rfl) | hv₀_in
    · exfalso
      rcases hu₀_av₀ with rfl | hu₀_in
      · exact hP''_uv.2.1 rfl
      · exact (S.Ω.isClockwise3_iff.mp hu₀_in.2).2.1 rfl
    · exact ha_b_a'.1
    · exact S.Ω.mem_interval_rotate_right
        (S.Ω.interval_subset_interval_left ha_b_a'.2 hv₀_in)
  have hu₀_a'v₀ : u₀ ∈ S.Ω.interval a'_0 v₀ := by
    rcases hu₀_av₀ with rfl | hu₀_in
    · exact ha_in_a'v₀
    · exact S.Ω.interval_subset_interval_right ha_in_a'v₀ hu₀_in
  -- Apply `four_arc_partition` and construct the fence `(A_f, B_f)` cutting `G₁` at `v₀`.
  obtain ⟨hA_sub_arc, hB_sub_arc, hG₂_sub_b'a', hG₁_sub_a'b', hdisj_P_arcs, _⟩ :=
    four_arc_partition hfence.2.1 hW'_bar ha_0 ha'_0 hb_0 hb'_0 hd'_ab hd'_ba
  let A_f : Set α := S.Ω.interval b'_0 v₀
  let B_f : Set α := {b'_0, v₀} ∪ S.Ω.interval v₀ b'_0
  have hb'_0_bar : b'_0 ∈ S.Ω.bar := hW'_bar hb'_0.2
  have hv₀_a'b' : v₀ ∈ S.Ω.interval a'_0 b'_0 := hG₁_sub_a'b' hv₀_G₁
  have hv₀_ne_b' : v₀ ≠ b'_0 := fun h => S.Ω.not_mem_interval_right a'_0 b'_0 (h ▸ hv₀_a'b')
  have ha'_in_b'v₀ : a'_0 ∈ S.Ω.interval b'_0 v₀ := S.Ω.mem_interval_rotate_right hv₀_a'b'
  have hfence_f : S.Ω.IsFence A_f B_f := by
    unfold A_f B_f
    exact pair_comm v₀ b'_0 ▸ (S.Ω.isFence_interval_compl hP''_uv.2.2.2 hb'_0_bar hv₀_ne_b').symm
  have hA_W'_Af : A ∩ W' ⊆ A_f := by
    intro z hz
    rcases (hA_sub_arc hz).1 with rfl | hz_in
    · exact ha'_in_b'v₀
    · exact S.Ω.interval_subset_interval_left ha'_in_b'v₀ hz_in
  have hB_W'_Bf : B ∩ W' ⊆ B_f := by
    intro y hy
    rcases hB_sub_arc hy with ⟨rfl | hy_in, hy_not_G₁⟩
    · exact Or.inl (Or.inl rfl)
    · rw [S.Ω.interval_eq_union_of_mem hv₀_a'b'] at hy_in
      rcases hy_in with (hy_a'v₀ | rfl) | hy_v₀b'
      · exact (hy_not_G₁ (S.Ω.interval_subset_interval_left hv₀_G₁ hy_a'v₀)).elim
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr hy_v₀b'
  have hu₀_Af : u₀ ∈ A_f := S.Ω.interval_subset_interval_right ha'_in_b'v₀ hu₀_a'v₀
  have hv₀_Bf : v₀ ∈ B_f := Or.inl (Or.inr rfl)
  -- Vertex-disjointness of `P''` from `P_set \ {P}` and fence for `P_set' := (P_set \ {P}) ∪
  -- {P''}`.
  let P_set' := (P_set \ {P}) ∪ {P''}
  have hdisj_RP'' : ∀ R ∈ P_set \ {P}, Disjoint V(R) V(P'') := by
    intro R hR
    obtain ⟨a_R, _, b_R, _, hR_ends⟩ := hfence.2.2 R hR.1
    obtain ⟨_, _, hVR⟩ := S.sdiff_singleton_subset_right_of_separation htrans_orig hP_in hP_ends
      hd_ab hsep hinter hba_G₂ hR hR_ends
    rw [disjoint_left]
    intro z hzR hzP''
    exact (hVR hzR).2 (hP''_le_G₁.vertexSet_mono hzP'')
  have hP''_not_in : P'' ∉ P_set \ {P} :=
    fun h_in => disjoint_left.mp (hdisj_RP'' P'' h_in) hP''_uv.1.left_mem hP''_uv.1.left_mem
  have hfence' : S.IsFenceFor P_set' A_f B_f := by
    refine ⟨⟨?_, ?_⟩, hfence_f, ?_⟩
    · rintro R (hR | rfl)
      · exact hfence.1.1 R hR.1
      · exact ⟨u₀, v₀, hP''_uv⟩
    · rintro R₁ (hR₁ | rfl) R₂ (hR₂ | rfl) hne
      · exact hfence.1.2 hR₁.1 hR₂.1 hne
      · exact hdisj_RP'' R₁ hR₁
      · exact (hdisj_RP'' R₂ hR₂).symm
      · exact (hne rfl).elim
    · rintro R (hR | rfl)
      · obtain ⟨a_R, ha_R_A, b_R, hb_R_B, hR_ends⟩ := hfence.2.2 R hR.1
        exact ⟨a_R, hA_W'_Af ⟨ha_R_A, hR_ends.mem_transactionEnds_left S hR⟩,
          b_R, hB_W'_Bf ⟨hb_R_B, hR_ends.mem_transactionEnds_right S hR⟩, hR_ends⟩
      · exact ⟨u₀, hu₀_Af, v₀, hv₀_Bf, hP''_uv⟩
  have htrans' : S.IsTransaction P_set' := ⟨A_f, B_f, hfence'⟩
  have hcard' : P_set'.ncard = 3 * p + 8 := by
    change ((P_set \ {P}) ∪ {P''}).ncard = 3 * p + 8
    rw [union_singleton, ncard_insert_of_notMem hP''_not_in hfin_P.sdiff,
      ncard_sdiff_singleton_of_mem hP_in]
    omega
  have hcard_ge2 : 2 ≤ P_set.ncard := by omega
  have hcard'_ge2 : 2 ≤ P_set'.ncard := by omega
  have hno_int' : ∀ R ∈ P_set', Disjoint (pathInternalVerts S.G R) S.Ω.bar := by
    rintro R (hR | rfl)
    · exact hno_int R hR.1
    · exact hno_int_P''
  -- Analyze `W_new := S.transactionEnds P_set'` and the peripheral members of `P_set'`.
  let W_new := S.transactionEnds P_set'
  have hW_new_bar : W_new ⊆ S.Ω.bar := S.transactionEnds_subset_bar P_set'
  have hW_new_eq : W_new = W' ∪ {u₀, v₀} := S.transactionEnds_insert (P_set \ {P}) hP''_uv
  have hd_uv_new : Disjoint (S.Ω.interval u₀ v₀) W_new := by
    rw [hW_new_eq, disjoint_union_right]
    refine ⟨hd'_ab.mono_left (huv_sub_ab.trans hab_sub_G₁), disjoint_left.mpr ?_⟩
    rintro z hz (rfl | rfl)
    · exact S.Ω.not_mem_interval_left z v₀ hz
    · exact S.Ω.not_mem_interval_right u₀ z hz
  have hU_P'' : S.peripheralIntervalSet P_set' P'' = S.Ω.interval v₀ u₀ :=
    (S.peripheralIntervalSet_eq_interval htrans' hcard'_ge2 (Or.inr rfl) hP''_uv hd_uv_new).2
  have hU_P : S.peripheralIntervalSet P_set P = S.Ω.interval b a :=
    (S.peripheralIntervalSet_eq_interval htrans_orig hcard_ge2 hP_in hP_ends hd_ab).2
  have hper_other : ∀ R ∈ P_set \ {P}, S.IsPeripheralIn P_set' R →
      S.IsPeripheralIn P_set R ∧
      S.peripheralIntervalSet P_set' R = S.peripheralIntervalSet P_set R ∧
      S.Ω.interval a'_0 b_0 ⊆ S.peripheralIntervalSet P_set' R := by
    intro R hR hperR'
    exact preservePeripheralIntervals hP_in hP_ends htrans_orig hfence hW'_bar ha'_0 hb_0 hd'_ab
      hb'_0 ha_0 hd'_ba hI_sub_G₁ hu₀_G₁ hG₂_sub_b'a' hG₁_sub_a'b' hdisj_P_arcs hfence_f hA_W'_Af
      hB_W'_Bf hu₀_Af hv₀_Bf htrans' hcard_ge2 hcard'_ge2 hW_new_bar hW_new_eq hd_uv_new hR hperR'
  have hper_sub : ∀ R ∈ P_set', S.IsPeripheralIn P_set' R → R = P'' ∨ S.IsPeripheralIn P_set R := by
    rintro R (hR | rfl) hperR'
    · exact Or.inr (hper_other R hR hperR').1
    · exact Or.inl rfl
  have hper_P : S.IsPeripheralIn P_set P := ⟨hP_in, a, b, hP_ends, Or.inl hd_ab⟩
  have hU_sub : S.transactionPeripheralUnion P_set ⊆ S.transactionPeripheralUnion P_set' := by
    rintro z ⟨hz_bar, hz_inter⟩
    refine ⟨hz_bar, mem_iInter₂.mpr fun R ⟨hR_in, hperR'⟩ => ?_⟩
    rcases hR_in with hR | rfl
    · obtain ⟨hperR_old, hU_eq, _⟩ := hper_other R hR hperR'
      rw [hU_eq]
      exact mem_iInter₂.mp hz_inter R ⟨hR.1, hperR_old⟩
    · rw [hU_P'']
      apply hba_sub_vu
      rw [← hU_P]
      exact mem_iInter₂.mp hz_inter P ⟨hP_in, hper_P⟩
  have hC_sub : S.coveredComponentUnion P_set ⊆ S.coveredComponentUnion P_set' :=
    S.lemma_6_1_claim_5 htrans_orig hcard_ge2 hno_int hP_in hP_ends hd_ab hsep hinter hab_G₁ hba_G₂
      ⟨u₀, v₀, hP''_uv⟩ hP''_le_G₁ hU_sub hper_sub
  have hx₀_U' : x₀ ∈ S.transactionPeripheralUnion P_set' := by
    have hx₀_bar : x₀ ∈ S.Ω.bar := by
      rcases hx₀_ab with rfl | rfl
      · exact hP_ends.2.2.1
      · exact hP_ends.2.2.2
    refine ⟨hx₀_bar, mem_iInter₂.mpr fun R ⟨hR_in, hperR'⟩ => ?_⟩
    rcases hR_in with hR | rfl
    · exact (hper_other R hR hperR').2.2 (hI_sub_G₁ (Or.inl hx₀_ab))
    · rw [hU_P'']
      exact hx₀_vu
  exact ⟨P'', hP''_le_P', htrans', hcard', hno_int', hC_sub, ⟨x₀, hx₀_ab, hx₀_U'⟩⟩

/-- In the setup of Claim (6), if `P' ≤ G₁` is an `Ω`-path with ends `c, d` where `c ∉ {a, b}`, then
a minimal `{c} → (ΩBar \ {c})` subpath `P'' ≤ P'` replaces `P` in `P_set` to form a transaction
`(P_set \ {P}) ∪ {P''}` of size `3p + 8` satisfying (a), (b),
`C(P_set) ⊆ C((P_set \ {P}) ∪ {P''})`, and `{a, b} ∩ U((P_set \ {P}) ∪ {P''}) ≠ ∅`. -/
theorem exists_replacement_of_end_notMem {p : ℕ} {P_set : Set (Graph α β)}
    {P P' G₁ G₂ : Graph α β} {a b c d : α}
    (htrans : S.IsTransaction P_set)
    (hcard : P_set.ncard = 3 * p + 8)
    (hno_int : ∀ R ∈ P_set, Disjoint (pathInternalVerts S.G R) S.Ω.bar)
    (hP_in : P ∈ P_set)
    (hP_ends : S.IsOmegaPathWithEnds P a b)
    (hd_ab : Disjoint (S.Ω.interval a b) (S.transactionEnds P_set))
    (hsep : IsGraphSeparation S.G G₁ G₂)
    (hinter : V(G₁) ∩ V(G₂) = V(P))
    (hab_G₁ : S.Ω.interval a b ⊆ V(G₁))
    (hba_G₂ : S.Ω.interval b a ⊆ V(G₂))
    (hP'_le : P' ≤ G₁)
    (hP'_cd : S.IsOmegaPathWithEnds P' c d)
    (hc_not : c ∉ ({a, b} : Set α)) :
    ∃ P'' : Graph α β,
      P'' ≤ P' ∧
      S.IsTransaction ((P_set \ {P}) ∪ {P''}) ∧
      ((P_set \ {P}) ∪ {P''}).ncard = 3 * p + 8 ∧
      (∀ R ∈ (P_set \ {P}) ∪ {P''}, Disjoint (pathInternalVerts S.G R) S.Ω.bar) ∧
      S.coveredComponentUnion P_set ⊆ S.coveredComponentUnion ((P_set \ {P}) ∪ {P''}) ∧
      ({a, b} ∩ S.transactionPeripheralUnion ((P_set \ {P}) ∪ {P''})).Nonempty := by
  classical
  have htrans_orig : S.IsTransaction P_set := htrans
  obtain ⟨A₀, B₀, hfence₀⟩ := htrans
  have hex_AB : ∃ A B : Set α, S.IsFenceFor P_set A B ∧ a ∈ A ∧ b ∈ B := by
    obtain ⟨a₀, ha₀A₀, b₀, hb₀B₀, hP₀⟩ := hfence₀.2.2 P hP_in
    rcases hP_ends.ends_eq S hP₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨A₀, B₀, hfence₀, ha₀A₀, hb₀B₀⟩
    · refine ⟨B₀, A₀, ⟨hfence₀.1, hfence₀.2.1.symm, fun R hR => ?_⟩, hb₀B₀, ha₀A₀⟩
      obtain ⟨x, hxA₀, y, hyB₀, hR_xy⟩ := hfence₀.2.2 R hR
      exact ⟨y, hyB₀, x, hxA₀, hR_xy.symm S⟩
  obtain ⟨A, B, hfence, haA, hbB⟩ := hex_AB
  -- Every vertex of `V(P') ∩ S.Ω.bar` lies in `{a, b} ∪ S.Ω.interval a b`.
  have hVP'_bar : ∀ z ∈ V(P'), z ∈ S.Ω.bar → z ∈ ({a, b} : Set α) ∪ S.Ω.interval a b := by
    intro z hzP' hz_bar
    by_cases hz_ab : z ∈ ({a, b} : Set α)
    · exact Or.inl hz_ab
    · simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz_ab
      rcases S.Ω.mem_interval_or_interval_swap hP_ends.2.2.1 hP_ends.2.2.2 hz_bar
          hP_ends.2.1 hz_ab.1 hz_ab.2 with hz_in | hz_ba
      · exact Or.inr hz_in
      · exfalso
        have hzP : z ∈ V(P) := hinter ▸ ⟨hP'_le.vertexSet_mono hzP', hba_G₂ hz_ba⟩
        have hz_pair : z ∈ ({a, b} : Set α) := by
          rw [← hP_ends.vertexSet_inter_bar_eq S (hno_int P hP_in)]
          exact ⟨hzP, hz_bar⟩
        exact hz_ab.1 (hz_pair.resolve_right hz_ab.2)
  have hc_ab : c ∈ S.Ω.interval a b :=
    (hVP'_bar c hP'_cd.1.left_mem hP'_cd.2.2.1).resolve_left hc_not
  -- Choose a minimal `{c} → (S.Ω.bar \ {c})` subpath `P'' ≤ P'`.
  obtain ⟨c', hc'_eq, d', hd'_mem, P'', hP''_le_P', hP''_ft⟩ :=
    hP'_cd.1.exists_isFromToPathWithEnds (X := {c}) (Y := S.Ω.bar \ {c})
      rfl ⟨hP'_cd.2.2.2, Ne.symm hP'_cd.2.1⟩
  rw [mem_singleton_iff] at hc'_eq
  subst c'
  have hd'_bar : d' ∈ S.Ω.bar := hd'_mem.1
  have hc_ne_d' : c ≠ d' := Ne.symm hd'_mem.2
  have hP''_le_G₁ : P'' ≤ G₁ := hP''_le_P'.trans hP'_le
  have hP''_cd' : S.IsOmegaPathWithEnds P'' c d' :=
    ⟨hP''_ft.1, hc_ne_d', hP'_cd.2.2.1, hd'_bar⟩
  have hno_int_P'' : Disjoint (pathInternalVerts S.G P'') S.Ω.bar := by
    rw [hP''_ft.1.pathInternalVerts_eq, disjoint_left]
    intro z ⟨hzP'', hz_not_cd'⟩ hz_bar
    have hz_ne_c : z ≠ c := fun h => hz_not_cd' (Or.inl h)
    have hz_in : z ∈ V(P'') ∩ (S.Ω.bar \ {c}) := ⟨hzP'', hz_bar, hz_ne_c⟩
    rw [hP''_ft.2.2, mem_singleton_iff] at hz_in
    exact hz_not_cd' (Or.inr hz_in)
  have hd'_ab_or : d' ∈ ({a, b} : Set α) ∪ S.Ω.interval a b :=
    hVP'_bar d' (hP''_le_P'.vertexSet_mono hP''_ft.1.right_mem) hd'_bar
  -- Order the ends `{c, d'}` of `P''` along `{a, b} ∪ S.Ω.interval a b`.
  have hex_uv : ∃ u₀ v₀ x₀ : α,
      S.IsOmegaPathWithEnds P'' u₀ v₀ ∧
      u₀ ∈ ({a} : Set α) ∪ S.Ω.interval a v₀ ∧
      v₀ ∈ ({b} : Set α) ∪ S.Ω.interval u₀ b ∧
      u₀ ∈ ({a, b} : Set α) ∪ S.Ω.interval a b ∧
      v₀ ∈ ({a, b} : Set α) ∪ S.Ω.interval a b ∧
      x₀ ∈ ({a, b} : Set α) ∧
      x₀ ∈ S.Ω.interval v₀ u₀ := by
    have hd'_split : d' ∈ ({a} : Set α) ∪ S.Ω.interval a c ∨
        d' ∈ ({b} : Set α) ∪ S.Ω.interval c b := by
      rcases hd'_ab_or with (rfl | rfl) | hd'_in
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr (Or.inl rfl)
      · rw [S.Ω.interval_eq_union_of_mem hc_ab] at hd'_in
        rcases hd'_in with (hd'_ac | rfl) | hd'_cb
        · exact Or.inl (Or.inr hd'_ac)
        · exact (hc_ne_d' rfl).elim
        · exact Or.inr (Or.inr hd'_cb)
    rcases hd'_split with hd'_ac | hd'_cb
    · have hc_d'b : c ∈ S.Ω.interval d' b := by
        rcases hd'_ac with rfl | hd'_in
        · exact hc_ab
        · exact S.Ω.mem_interval_right_of_mem_interval_left hc_ab hd'_in
      refine ⟨d', c, b, hP''_cd'.symm S, hd'_ac, Or.inr hc_d'b, hd'_ab_or, Or.inr hc_ab,
        Or.inr rfl, S.Ω.mem_interval_rotate_left hc_d'b⟩
    · have hc_ad' : c ∈ S.Ω.interval a d' := by
        rcases hd'_cb with rfl | hd'_in
        · exact hc_ab
        · exact S.Ω.mem_interval_left_of_mem_interval_right hc_ab hd'_in
      refine ⟨c, d', a, hP''_cd', Or.inr hc_ad', hd'_cb, Or.inr hc_ab, hd'_ab_or,
        Or.inl rfl, S.Ω.mem_interval_rotate_right hc_ad'⟩
  obtain ⟨u₀, v₀, x₀, hP''_uv, hu₀_av₀, hv₀_u₀b, hu₀_ab, hv₀_ab, hx₀_ab, hx₀_vu⟩ := hex_uv
  have huv_sub_ab : S.Ω.interval u₀ v₀ ⊆ S.Ω.interval a b := by
    have h1 : S.Ω.interval u₀ v₀ ⊆ S.Ω.interval a v₀ := by
      rcases hu₀_av₀ with rfl | hu₀_in
      · exact Subset.rfl
      · exact S.Ω.interval_subset_interval_right hu₀_in
    have h2 : S.Ω.interval a v₀ ⊆ S.Ω.interval a b := by
      rcases hv₀_ab with (rfl | rfl) | hv₀_in
      · exfalso
        rcases hu₀_av₀ with rfl | hu₀_in
        · exact hP''_uv.2.1 rfl
        · exact (S.Ω.isClockwise3_iff.mp hu₀_in.2).2.1 rfl
      · exact Subset.rfl
      · exact S.Ω.interval_subset_interval_left hv₀_in
    exact h1.trans h2
  have hba_sub_vu : S.Ω.interval b a ⊆ S.Ω.interval v₀ u₀ := by
    intro z hz_ba
    have hz_not_I : z ∉ ({a, b} : Set α) ∪ S.Ω.interval a b := by
      rintro ((rfl | rfl) | hz_ab)
      · exact S.Ω.not_mem_interval_right b z hz_ba
      · exact S.Ω.not_mem_interval_left z a hz_ba
      · exact disjoint_left.mp (S.Ω.disjoint_interval_swap a b) hz_ab hz_ba
    have hz_ne_u₀ : z ≠ u₀ := fun h => hz_not_I (h ▸ hu₀_ab)
    have hz_ne_v₀ : z ≠ v₀ := fun h => hz_not_I (h ▸ hv₀_ab)
    exact (S.Ω.mem_interval_or_interval_swap hP''_uv.2.2.1 hP''_uv.2.2.2 hz_ba.1.1
      hP''_uv.2.1 hz_ne_u₀ hz_ne_v₀).resolve_left (fun h => hz_not_I (Or.inr (huv_sub_ab h)))
  -- Set up `W := S.transactionEnds P_set` and `W' := S.transactionEnds (P_set \ {P})`.
  exact replacePathWithOrderedEnds p hcard hno_int hP_in hP_ends hd_ab hsep hinter hab_G₁ hba_G₂
    htrans_orig hfence haA hbB hP''_le_P' hP''_le_G₁ hno_int_P'' hP''_uv hu₀_av₀ hu₀_ab hv₀_ab
    hx₀_ab hx₀_vu huv_sub_ab hba_sub_vu

/-- **Graph Minors IX, (6.1), Claim (6)** (page 56):
"If $P'$ is an $\Omega$-path with $P' \subseteq G_1$, then $P'$ has ends $a, b$." -/
theorem lemma_6_1_claim_6 {p : ℕ} {P_set : Set (Graph α β)} {P P' G₁ G₂ : Graph α β} {a b : α}
    (htrans : S.IsTransaction P_set)
    (hcard : P_set.ncard = 3 * p + 8)
    (hno_int : ∀ R ∈ P_set, Disjoint (pathInternalVerts S.G R) S.Ω.bar)
    (hmax : ∀ P_set' : Set (Graph α β),
      S.IsTransaction P_set' →
      P_set'.ncard = 3 * p + 8 →
      (∀ R ∈ P_set', Disjoint (pathInternalVerts S.G R) S.Ω.bar) →
      S.coveredComponentUnion P_set ⊆ S.coveredComponentUnion P_set' →
      S.coveredComponentUnion P_set = S.coveredComponentUnion P_set')
    (hP_in : P ∈ P_set)
    (hP_ends : S.IsOmegaPathWithEnds P a b)
    (hd_ab : Disjoint (S.Ω.interval a b) (S.transactionEnds P_set))
    (hsep : IsGraphSeparation S.G G₁ G₂)
    (hinter : V(G₁) ∩ V(G₂) = V(P))
    (hab_G₁ : S.Ω.interval a b ⊆ V(G₁))
    (hba_G₂ : S.Ω.interval b a ⊆ V(G₂))
    (hP'_omega : S.IsOmegaPath P')
    (hP'_le : P' ≤ G₁) :
    S.IsOmegaPathWithEnds P' a b := by
  obtain ⟨c, d, hP'_cd⟩ := hP'_omega
  have hc_ab : c ∈ ({a, b} : Set α) := by
    by_contra hc_not
    obtain ⟨P'', _, htrans', hcard', hno_int', hC_sub, ⟨x, hx_ab, hx_U'⟩⟩ :=
      S.exists_replacement_of_end_notMem htrans hcard hno_int hP_in hP_ends hd_ab hsep hinter
        hab_G₁ hba_G₂ hP'_le hP'_cd hc_not
    have hC_eq : S.coveredComponentUnion P_set =
        S.coveredComponentUnion ((P_set \ {P}) ∪ {P''}) :=
      hmax _ htrans' hcard' hno_int' hC_sub
    have hcard_ge2 : 2 ≤ ((P_set \ {P}) ∪ {P''}).ncard := by omega
    have hx_C : x ∈ S.coveredComponentUnion P_set := by
      rw [hC_eq]
      exact S.transactionPeripheralUnion_subset_coveredComponentUnion htrans' hcard_ge2
        hno_int' hx_U'
    have hperP : S.IsPeripheralIn P_set P := ⟨hP_in, a, b, hP_ends, Or.inl hd_ab⟩
    have hdisj_CP := S.disjoint_coveredComponentUnion_of_isPeripheralIn hP_in hperP
    have hx_P : x ∈ V(P) := by
      rcases hx_ab with rfl | rfl
      · exact hP_ends.1.left_mem
      · exact hP_ends.1.right_mem
    exact disjoint_left.mp hdisj_CP hx_C hx_P
  have hd_ab_mem : d ∈ ({a, b} : Set α) := by
    by_contra hd_not
    obtain ⟨P'', _, htrans', hcard', hno_int', hC_sub, ⟨x, hx_ab, hx_U'⟩⟩ :=
      S.exists_replacement_of_end_notMem htrans hcard hno_int hP_in hP_ends hd_ab hsep hinter
        hab_G₁ hba_G₂ hP'_le (hP'_cd.symm S) hd_not
    have hC_eq : S.coveredComponentUnion P_set =
        S.coveredComponentUnion ((P_set \ {P}) ∪ {P''}) :=
      hmax _ htrans' hcard' hno_int' hC_sub
    have hcard_ge2 : 2 ≤ ((P_set \ {P}) ∪ {P''}).ncard := by omega
    have hx_C : x ∈ S.coveredComponentUnion P_set := by
      rw [hC_eq]
      exact S.transactionPeripheralUnion_subset_coveredComponentUnion htrans' hcard_ge2
        hno_int' hx_U'
    have hperP : S.IsPeripheralIn P_set P := ⟨hP_in, a, b, hP_ends, Or.inl hd_ab⟩
    have hdisj_CP := S.disjoint_coveredComponentUnion_of_isPeripheralIn hP_in hperP
    have hx_P : x ∈ V(P) := by
      rcases hx_ab with rfl | rfl
      · exact hP_ends.1.left_mem
      · exact hP_ends.1.right_mem
    exact disjoint_left.mp hdisj_CP hx_C hx_P
  rcases hc_ab with rfl | rfl <;> rcases hd_ab_mem with rfl | rfl
  · exact (hP'_cd.2.1 rfl).elim
  · exact hP'_cd
  · exact hP'_cd.symm S
  · exact (hP'_cd.2.1 rfl).elim

/-- **Graph Minors IX, (6.1), Claim (7)** (page 57):
"`Ω(a, b) = ∅`." -/
theorem lemma_6_1_claim_7 {P G₁ G₂ : Graph α β} {a b : α}
    (hconn3 : S.IsKConnected 3)
    (hloopless : ∀ x : α, ¬ S.G.Adj x x)
    (hno_iso : ∀ v ∈ S.Ω.bar, ∃ u : α, S.G.Adj v u)
    (hP_ends : S.IsOmegaPathWithEnds P a b)
    (hno_intP : Disjoint (pathInternalVerts S.G P) S.Ω.bar)
    (hsep : IsGraphSeparation S.G G₁ G₂)
    (hinter : V(G₁) ∩ V(G₂) = V(P))
    (hP_G₁ : P ≤ G₁)
    (hab_G₁ : S.Ω.interval a b ⊆ V(G₁))
    (_hba_G₂ : S.Ω.interval b a ⊆ V(G₂))
    (hclaim6 : ∀ P' : Graph α β, S.IsOmegaPath P' → P' ≤ G₁ → S.IsOmegaPathWithEnds P' a b) :
    S.Ω.interval a b = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro c hc_ab
  have hc_bar : c ∈ S.Ω.bar := hc_ab.1.1
  have hcG : c ∈ V(S.G) := S.bar_subset hc_bar
  have hc_not_P : c ∉ V(P) := by
    intro hcP
    have hc_ab_pair : c ∈ ({a, b} : Set α) := by
      rw [← hP_ends.vertexSet_inter_bar_eq S hno_intP]
      exact ⟨hcP, hc_bar⟩
    rcases hc_ab_pair with h_eq | h_eq
    · rw [h_eq] at hc_ab
      exact S.Ω.not_mem_interval_left a b hc_ab
    · rw [h_eq] at hc_ab
      exact S.Ω.not_mem_interval_right a b hc_ab
  let G' := reachableComponent S.G c
  have hG'_comp : IsGraphComponent G' S.G := isGraphComponent_reachableComponent hcG
  have hcG' : c ∈ V(G') := self_mem_reachableComponent hcG
  by_cases hmeet : (V(G') ∩ V(P)).Nonempty
  · -- Case 1: `G' ∩ P` is non-null; construct an `Ω`-path `P' ≤ G₁` with end `c ∉ {a, b}`.
    obtain ⟨w, hwG', hwP⟩ := hmeet
    obtain ⟨W_G'⟩ := hG'_comp.2.1.2 c hcG' w hwG'
    obtain ⟨W_G, _, _⟩ := exists_walk_up_of_le hG'_comp.1 W_G'
    obtain ⟨Q₀, hQ₀_G, _, _⟩ := exists_isGraphPathWithEnds_of_walk W_G
    obtain ⟨c', hc'_eq, x, hxP, P₁, _, hP₁_ft⟩ :=
      hQ₀_G.exists_isFromToPathWithEnds (X := {c}) (Y := V(P)) rfl hwP
    rw [mem_singleton_iff] at hc'_eq
    subst c'
    obtain ⟨P_xa, hP_xa_le, _, hP_xa_G⟩ := hP_ends.1.exists_subpath hxP hP_ends.1.left_mem
    have hinter_P₁_xa : V(P₁) ∩ V(P_xa) = {x} := by
      ext z
      simp only [mem_inter_iff, mem_singleton_iff]
      refine ⟨fun ⟨hz₁, hz₂⟩ => ?_, fun h => h ▸ ⟨hP₁_ft.1.right_mem, hP_xa_G.left_mem⟩⟩
      have : z ∈ V(P₁) ∩ V(P) := ⟨hz₁, hP_xa_le.vertexSet_mono hz₂⟩
      rwa [hP₁_ft.2.2, mem_singleton_iff] at this
    let P' := subgraphUnion S.G P₁ P_xa
    have hP'_G : IsGraphPathWithEnds S.G P' c a := hP₁_ft.1.subgraphUnion hP_xa_G hinter_P₁_xa
    have hc_ne_a : c ≠ a := fun h => S.Ω.not_mem_interval_left a b (h ▸ hc_ab)
    have hP'_omega : S.IsOmegaPath P' := ⟨c, a, hP'_G, hc_ne_a, hc_bar, hP_ends.2.2.1⟩
    have hVP₁_G₁ : V(P₁) ⊆ V(G₁) := by
      intro z hz
      by_cases hz_G₁ : z ∈ V(G₁)
      · exact hz_G₁
      · exfalso
        have hz_G₂ : z ∈ V(G₂) := (hsep.2.2.1 ▸ hP₁_ft.1.le.vertexSet_mono hz).resolve_left hz_G₁
        obtain ⟨R₁, hR₁_P₁, hR₁_path, hR₁_G⟩ := hP₁_ft.1.exists_subpath hP₁_ft.1.left_mem hz
        have hx_not_R₁ : x ∉ V(R₁) := by
          intro hxR₁
          obtain ⟨S₁, S₂, _, _, hpath_S₁, hpath_S₂, _, hinter_S, _⟩ :=
            hP₁_ft.1.exists_split_at hz
          have hx_S₂ : x = z := by
            have hR₁_eq : R₁ = S₁ := hP₁_ft.1.subpath_unique_of_left hR₁_path hpath_S₁
            rw [hR₁_eq] at hxR₁
            have : x ∈ V(S₁) ∩ V(S₂) := ⟨hxR₁, hpath_S₂.right_mem⟩
            rwa [hinter_S, mem_singleton_iff] at this
          subst hx_S₂
          exact hz_G₁ (hP_G₁.vertexSet_mono hxP)
        have hav_R₁ : Disjoint V(R₁) (V(G₁) ∩ V(G₂)) := by
          rw [hinter, disjoint_left]
          intro q hqR₁ hqP
          have hq_x : q = x := by
            have : q ∈ V(P₁) ∩ V(P) := ⟨hR₁_P₁.vertexSet_mono hqR₁, hqP⟩
            rwa [hP₁_ft.2.2, mem_singleton_iff] at this
          exact hx_not_R₁ (hq_x ▸ hqR₁)
        have hVR₁_sub := connected_subset_right_of_avoids_inter hsep hR₁_G.le
          hR₁_G.isGraphConnected hav_R₁ ⟨z, hR₁_G.right_mem, hz_G₂⟩
        exact (hVR₁_sub hR₁_G.left_mem).2 (hab_G₁ hc_ab)
    have hP₁_le_G₁ : P₁ ≤ G₁ := by
      rw [(Compatible.of_le_le hP₁_ft.1.le hsep.1).le_iff]
      refine ⟨hVP₁_G₁, fun e he => ?_⟩
      obtain ⟨u, v, huv⟩ := P₁.exists_isLink_of_mem_edgeSet he
      have huvG : S.G.IsLink e u v := huv.mono hP₁_ft.1.le
      rcases hsep.2.2.2.1 ▸ huvG.edge_mem with he₁ | he₂
      · exact he₁
      · exfalso
        have huG₂ : u ∈ V(G₂) := ((hsep.2.1.isLink_iff he₂).mpr huvG).left_mem
        have hvG₂ : v ∈ V(G₂) := ((hsep.2.1.isLink_iff he₂).mpr huvG).right_mem
        have huP : u ∈ V(P) := hinter ▸ ⟨hVP₁_G₁ huv.left_mem, huG₂⟩
        have hvP : v ∈ V(P) := hinter ▸ ⟨hVP₁_G₁ huv.right_mem, hvG₂⟩
        have hux : u = x := by
          have : u ∈ V(P₁) ∩ V(P) := ⟨huv.left_mem, huP⟩
          rwa [hP₁_ft.2.2, mem_singleton_iff] at this
        have hvx : v = x := by
          have : v ∈ V(P₁) ∩ V(P) := ⟨huv.right_mem, hvP⟩
          rwa [hP₁_ft.2.2, mem_singleton_iff] at this
        rw [hux, hvx] at huvG
        exact hloopless x huvG.adj
    have hP'_le_G₁ : P' ≤ G₁ :=
      (subgraphUnion_le_iff hP₁_ft.1.le hP_xa_G.le hsep.1).mpr
        ⟨hP₁_le_G₁, hP_xa_le.trans hP_G₁⟩
    have hP'_ab := hclaim6 P' hP'_omega hP'_le_G₁
    have hc_ne_b : c ≠ b := fun h => S.Ω.not_mem_interval_right a b (h ▸ hc_ab)
    rcases hP'_ab.ends_eq S ⟨hP'_G, hc_ne_a, hc_bar, hP_ends.2.2.1⟩ with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hc_ne_a h1
    · exact hc_ne_b h1
  · -- Case 2: `G' ∩ P` is null, so `G' ≤ G₁`.
    have hdisj_G'P : Disjoint V(G') (V(G₁) ∩ V(G₂)) := by
      rw [hinter]
      exact not_nonempty_iff_eq_empty.mp hmeet |> disjoint_iff_inter_eq_empty.mpr
    have hVG'_sub : V(G') ⊆ V(G₁) \ V(G₂) :=
      connected_subset_right_of_avoids_inter (IsGraphSeparation.symm hsep) hG'_comp.1 hG'_comp.2.1
        (inter_comm V(G₂) V(G₁) ▸ hdisj_G'P) ⟨c, hcG', hab_G₁ hc_ab⟩
    have hG'_le_G₁ : G' ≤ G₁ := by
      rw [(Compatible.of_le_le hG'_comp.1 hsep.1).le_iff]
      refine ⟨fun z hz => (hVG'_sub hz).1, fun e he => ?_⟩
      obtain ⟨u, v, huv⟩ := G'.exists_isLink_of_mem_edgeSet he
      have huvG : S.G.IsLink e u v := huv.mono hG'_comp.1
      rcases hsep.2.2.2.1 ▸ huvG.edge_mem with he₁ | he₂
      · exact he₁
      · exact ((hVG'_sub huv.left_mem).2 ((hsep.2.1.isLink_iff he₂).mpr huvG).left_mem).elim
    -- Show `V(G') ∩ S.Ω.bar ⊆ {c}` using Claim (6).
    have hG'_bar : V(G') ∩ S.Ω.bar ⊆ {c} := by
      rintro d ⟨hdG', hd_bar⟩
      rw [mem_singleton_iff]
      by_contra hdc
      obtain ⟨W_cd⟩ := hG'_comp.2.1.2 c hcG' d hdG'
      obtain ⟨W_G, hs_G, _⟩ := exists_walk_up_of_le hG'_comp.1 W_cd
      obtain ⟨P', hP'_G, hVP', _⟩ := exists_isGraphPathWithEnds_of_walk W_G
      have hVP'_G' : V(P') ⊆ V(G') :=
        fun z hz => W_cd.mem_vertexSet_of_mem_support (hs_G ▸ hVP' hz)
      have hP'_le_G' : P' ≤ G' := by
        rw [(Compatible.of_le_le hP'_G.le hG'_comp.1).le_iff]
        refine ⟨hVP'_G', fun e he => ?_⟩
        obtain ⟨u, v, huv⟩ := P'.exists_isLink_of_mem_edgeSet he
        have huvG : S.G.IsLink e u v := huv.mono hP'_G.le
        exact (isClosedSubgraph_of_isGraphComponent hG'_comp).closed ⟨v, huvG⟩
          (hVP'_G' huv.left_mem)
      have hP'_ab := hclaim6 P' ⟨c, d, hP'_G, Ne.symm hdc, hc_bar, hd_bar⟩
        (hP'_le_G'.trans hG'_le_G₁)
      have ha_G₂ : a ∈ V(G₂) := (hinter ▸ hP_ends.1.left_mem : a ∈ V(G₁) ∩ V(G₂)).2
      exact (hVG'_sub (hP'_le_G'.vertexSet_mono hP'_ab.1.left_mem)).2 ha_G₂
    -- Construct the society separation `(G', B')` of `S` with `V(G') ∩ V(B') = {c}`.
    let B' := (S.G.induce ((V(S.G) \ V(G')) ∪ {c})).restrict (E(S.G) \ E(G'))
    have hB'_le : B' ≤ S.G :=
      restrict_le.trans (S.G.induce_le (union_subset sdiff_subset (singleton_subset_iff.mpr hcG)))
    have hVB' : V(B') = (V(S.G) \ V(G')) ∪ {c} := rfl
    have hEB' : E(B') = E(S.G) \ E(G') := by
      change E(S.G.induce ((V(S.G) \ V(G')) ∪ {c})) ∩ (E(S.G) \ E(G')) = E(S.G) \ E(G')
      rw [inter_eq_right]
      rintro e ⟨heG, he_not_G'⟩
      obtain ⟨u, v, huv⟩ := S.G.exists_isLink_of_mem_edgeSet heG
      have hu_not_G' : u ∉ V(G') := fun huG' =>
        he_not_G' ((isClosedSubgraph_of_isGraphComponent hG'_comp).closed ⟨v, huv⟩ huG')
      have hv_not_G' : v ∉ V(G') := fun hvG' =>
        hu_not_G' ((mem_graphComponent_iff_of_isLink hG'_comp huv).mpr hvG')
      exact ⟨u, v, huv, Or.inl ⟨huv.left_mem, hu_not_G'⟩, Or.inl ⟨huv.right_mem, hv_not_G'⟩⟩
    have hsep_G'B' : S.IsSocietySeparation G' B' := by
      refine ⟨⟨hG'_comp.1, hB'_le, ?_, ?_, hEB' ▸ disjoint_sdiff_self_right⟩, ?_⟩
      · rw [hVB']
        ext z
        simp only [mem_union, mem_sdiff, mem_singleton_iff]
        exact ⟨by rintro (hzG' | ⟨hzG, _⟩ | rfl); exacts [hG'_comp.1.vertexSet_mono hzG', hzG, hcG],
          fun hzG => by_cases Or.inl (fun hz => Or.inr (Or.inl ⟨hzG, hz⟩))⟩
      · rw [hEB']
        exact union_sdiff_cancel hG'_comp.1.edgeSet_mono
      · intro z hz_bar
        rw [hVB']
        by_cases hzG' : z ∈ V(G')
        · exact Or.inr (hG'_bar ⟨hzG', hz_bar⟩)
        · exact Or.inl ⟨S.bar_subset hz_bar, hzG'⟩
    have hinter_G'B' : V(G') ∩ V(B') = {c} := by
      rw [hVB']
      ext z
      simp only [mem_inter_iff, mem_union, mem_sdiff, mem_singleton_iff]
      exact ⟨by rintro ⟨hzG', ⟨_, hz_not⟩ | rfl⟩; exacts [(hz_not hzG').elim, rfl],
        by rintro rfl; exact ⟨hcG', Or.inr rfl⟩⟩
    -- By `(2)`, `c` has a neighbor `u` in `S.G`, with `u ≠ c` by `hloopless`.
    obtain ⟨u, hcu⟩ := hno_iso c hc_bar
    have huc_ne : u ≠ c := fun h => hloopless c (h ▸ hcu)
    obtain ⟨e, he_cu⟩ := hcu
    have huG' : u ∈ V(G') := (mem_graphComponent_iff_of_isLink hG'_comp he_cu).mp hcG'
    have hVB'_ne : V(B') ≠ V(S.G) := by
      intro heq
      have huB' : u ∈ V(B') := heq ▸ hG'_comp.1.vertexSet_mono huG'
      rw [hVB', mem_union, mem_sdiff, mem_singleton_iff] at huB'
      rcases huB' with ⟨_, hu_not⟩ | h_eq
      · exact hu_not huG'
      · exact huc_ne h_eq
    have hcard_inter : (V(G') ∩ V(B')).ncard ≤ 1 := by
      rw [hinter_G'B', ncard_singleton]
    exact hconn3 1 (by decide) G' B' ⟨hsep_G'B', hcard_inter, hVB'_ne⟩

/-- Concatenating two paths `P₁` (from `u` to `z`) and `P₂` (from `z` to `w`) in `G` yields a path
`M` in `G` from `u` to `w` with `V(M) ⊆ V(P₁) ∪ V(P₂)`. -/
theorem exists_path_subset_union_of_paths {G P₁ P₂ : Graph α β} {u z w : α}
    (h₁ : IsGraphPathWithEnds G P₁ u z) (h₂ : IsGraphPathWithEnds G P₂ z w) :
    ∃ M : Graph α β, IsGraphPathWithEnds G M u w ∧ V(M) ⊆ V(P₁) ∪ V(P₂) := by
  rcases h₁ with ⟨h₁G, W₁, _, hV₁, _⟩
  rcases h₂ with ⟨h₂G, W₂, _, hV₂, _⟩
  obtain ⟨W₁', hs₁, _⟩ := exists_walk_up_of_le h₁G W₁
  obtain ⟨W₂', hs₂, _⟩ := exists_walk_up_of_le h₂G W₂
  obtain ⟨M, hM, hVM, _⟩ := exists_isGraphPathWithEnds_of_walk (W₁'.append W₂')
  refine ⟨M, hM, fun x hx => ?_⟩
  rcases (GraphWalk.mem_support_append W₁' W₂').mp (hVM hx) with hx₁ | hx₂
  · exact Or.inl (hV₁ ▸ hs₁ ▸ hx₁)
  · exact Or.inr (hV₂ ▸ hs₂ ▸ hx₂)

/-- Replacing `P ∈ P_set` (with ends `a, b`) by `P' ≤ G₁` (also with ends `a, b` and no internal
vertex in `ΩBar`) preserves the fence `(A, B)`, cardinality, `transactionEnds`,
`peripheralIntervalSet`, `transactionPeripheralUnion`, and (under `hmax`) `coveredComponentUnion`.
-/
theorem replacement_same_ends_properties {p : ℕ} {P_set : Set (Graph α β)}
    {P P' G₁ G₂ : Graph α β} {a b : α}
    (htrans : S.IsTransaction P_set)
    (hcard : P_set.ncard = 3 * p + 8)
    (hno_int : ∀ R ∈ P_set, Disjoint (pathInternalVerts S.G R) S.Ω.bar)
    (hmax : ∀ P_set' : Set (Graph α β),
      S.IsTransaction P_set' →
      P_set'.ncard = 3 * p + 8 →
      (∀ R ∈ P_set', Disjoint (pathInternalVerts S.G R) S.Ω.bar) →
      S.coveredComponentUnion P_set ⊆ S.coveredComponentUnion P_set' →
      S.coveredComponentUnion P_set = S.coveredComponentUnion P_set')
    (hP_in : P ∈ P_set)
    (hP_ends : S.IsOmegaPathWithEnds P a b)
    (hd_ab : Disjoint (S.Ω.interval a b) (S.transactionEnds P_set))
    (hsep : IsGraphSeparation S.G G₁ G₂)
    (hinter : V(G₁) ∩ V(G₂) = V(P))
    (hab_G₁ : S.Ω.interval a b ⊆ V(G₁))
    (hba_G₂ : S.Ω.interval b a ⊆ V(G₂))
    (hP'_ends : S.IsOmegaPathWithEnds P' a b)
    (hP'_le : P' ≤ G₁)
    (hno_int_P' : Disjoint (pathInternalVerts S.G P') S.Ω.bar) :
    let P_set' := (P_set \ {P}) ∪ {P'}
    P' ∉ P_set \ {P} ∧
    S.IsTransaction P_set' ∧
    P_set'.ncard = 3 * p + 8 ∧
    (∀ R ∈ P_set', Disjoint (pathInternalVerts S.G R) S.Ω.bar) ∧
    S.transactionEnds P_set' = S.transactionEnds P_set ∧
    S.IsPeripheralIn P_set' P' ∧
    (∀ R ∈ P_set \ {P}, S.IsPeripheralIn P_set' R ↔ S.IsPeripheralIn P_set R) ∧
    S.transactionPeripheralUnion P_set' = S.transactionPeripheralUnion P_set ∧
    S.coveredComponentUnion P_set = S.coveredComponentUnion P_set' := by
  intro P_set'
  have htrans_orig : S.IsTransaction P_set := htrans
  obtain ⟨A, B, hfence⟩ := htrans
  have hdisj_RP' : ∀ R ∈ P_set \ {P}, Disjoint V(R) V(P') := by
    intro R hR
    obtain ⟨a_R, _, b_R, _, hR_ends⟩ := hfence.2.2 R hR.1
    obtain ⟨_, _, hVR⟩ := S.sdiff_singleton_subset_right_of_separation htrans_orig hP_in hP_ends
      hd_ab hsep hinter hba_G₂ hR hR_ends
    rw [disjoint_left]
    intro z hzR hzP'
    exact (hVR hzR).2 (hP'_le.vertexSet_mono hzP')
  have hP'_not_in : P' ∉ P_set \ {P} := by
    intro hP'_in
    exact disjoint_left.mp (hdisj_RP' P' hP'_in) hP'_ends.1.left_mem hP'_ends.1.left_mem
  have hfence' : S.IsFenceFor P_set' A B := by
    refine ⟨⟨?_, ?_⟩, hfence.2.1, ?_⟩
    · rintro R (hR | rfl)
      · exact hfence.1.1 R hR.1
      · exact ⟨a, b, hP'_ends⟩
    · rintro R₁ (hR₁ | rfl) R₂ (hR₂ | rfl) hne
      · exact hfence.1.2 hR₁.1 hR₂.1 hne
      · exact hdisj_RP' R₁ hR₁
      · exact (hdisj_RP' R₂ hR₂).symm
      · exact (hne rfl).elim
    · rintro R (hR | rfl)
      · exact hfence.2.2 R hR.1
      · obtain ⟨a₀, ha₀A, b₀, hb₀B, hP₀⟩ := hfence.2.2 P hP_in
        rcases hP_ends.ends_eq S hP₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨a₀, ha₀A, b₀, hb₀B, hP'_ends⟩
        · exact ⟨a₀, ha₀A, b₀, hb₀B, hP'_ends.symm S⟩
  have htrans' : S.IsTransaction P_set' := ⟨A, B, hfence'⟩
  have hfin_P : P_set.Finite := hfence.1.finite S
  have hcard' : P_set'.ncard = 3 * p + 8 := by
    change ((P_set \ {P}) ∪ {P'}).ncard = 3 * p + 8
    rw [union_singleton, ncard_insert_of_notMem hP'_not_in hfin_P.sdiff,
      ncard_sdiff_singleton_of_mem hP_in]
    omega
  have hno_int' : ∀ R ∈ P_set', Disjoint (pathInternalVerts S.G R) S.Ω.bar := by
    rintro R (hR | rfl)
    · exact hno_int R hR.1
    · exact hno_int_P'
  have hP'_ends_iff : ∀ s t : α, S.IsOmegaPathWithEnds P' s t ↔ S.IsOmegaPathWithEnds P s t := by
    intro s t
    constructor
    · intro h
      rcases hP'_ends.ends_eq S h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hP_ends
      · exact hP_ends.symm S
    · intro h
      rcases hP_ends.ends_eq S h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hP'_ends
      · exact hP'_ends.symm S
  have hW_eq : S.transactionEnds P_set' = S.transactionEnds P_set := by
    ext x
    simp only [transactionEnds, mem_ofPred_eq]
    constructor
    · rintro ⟨R, hR | rfl, y, hRy⟩
      · exact ⟨R, hR.1, y, hRy⟩
      · exact ⟨P, hP_in, y, (hP'_ends_iff x y).mp hRy⟩
    · rintro ⟨R, hR_in, y, hRy⟩
      by_cases hRP : R = P
      · subst hRP
        exact ⟨P', Or.inr rfl, y, (hP'_ends_iff x y).mpr hRy⟩
      · exact ⟨R, Or.inl ⟨hR_in, hRP⟩, y, hRy⟩
  have hU_R_eq : ∀ R : Graph α β,
      S.peripheralIntervalSet P_set' R = S.peripheralIntervalSet P_set R := by
    intro R
    simp only [peripheralIntervalSet, hW_eq]
  have hU_P'_eq : S.peripheralIntervalSet P_set' P' = S.peripheralIntervalSet P_set P := by
    ext x
    simp only [peripheralIntervalSet, hW_eq, mem_iUnion, hP'_ends_iff]
  have hper_P' : S.IsPeripheralIn P_set' P' :=
    ⟨Or.inr rfl, a, b, hP'_ends, Or.inl (hW_eq ▸ hd_ab)⟩
  have hper_P : S.IsPeripheralIn P_set P :=
    ⟨hP_in, a, b, hP_ends, Or.inl hd_ab⟩
  have hper_iff : ∀ R ∈ P_set \ {P}, S.IsPeripheralIn P_set' R ↔ S.IsPeripheralIn P_set R := by
    intro R hR
    simp only [IsPeripheralIn, hW_eq]
    exact ⟨fun ⟨_, h⟩ => ⟨hR.1, h⟩, fun ⟨_, h⟩ => ⟨Or.inl hR, h⟩⟩
  have hper_sub : ∀ R ∈ P_set', S.IsPeripheralIn P_set' R → R = P' ∨ S.IsPeripheralIn P_set R := by
    rintro R (hR | rfl) hperR
    · exact Or.inr ((hper_iff R hR).mp hperR)
    · exact Or.inl rfl
  have hU_eq : S.transactionPeripheralUnion P_set' = S.transactionPeripheralUnion P_set := by
    ext x
    simp only [transactionPeripheralUnion, mem_inter_iff, mem_iInter, mem_ofPred_eq,
      and_congr_right_iff]
    intro _
    constructor
    · intro hx R ⟨hR_in, hperR⟩
      by_cases hRP : R = P
      · subst hRP
        rw [← hU_P'_eq]
        exact hx P' ⟨Or.inr rfl, hper_P'⟩
      · rw [← hU_R_eq R]
        exact hx R ⟨Or.inl ⟨hR_in, hRP⟩, (hper_iff R ⟨hR_in, hRP⟩).mpr hperR⟩
    · intro hx R ⟨hR_in, hperR⟩
      rcases hR_in with hR_diff | rfl
      · rw [hU_R_eq R]
        exact hx R ⟨hR_diff.1, (hper_iff R hR_diff).mp hperR⟩
      · rw [hU_P'_eq]
        exact hx P ⟨hP_in, hper_P⟩
  have hcard_ge2 : 2 ≤ P_set.ncard := by omega
  have hC_sub : S.coveredComponentUnion P_set ⊆ S.coveredComponentUnion P_set' :=
    S.lemma_6_1_claim_5 htrans_orig hcard_ge2 hno_int hP_in hP_ends hd_ab hsep hinter hab_G₁ hba_G₂
      ⟨a, b, hP'_ends⟩ hP'_le hU_eq.symm.subset hper_sub
  have hC_eq : S.coveredComponentUnion P_set = S.coveredComponentUnion P_set' :=
    hmax P_set' htrans' hcard' hno_int' hC_sub
  exact ⟨hP'_not_in, htrans', hcard', hno_int', hW_eq, hper_P', hper_iff, hU_eq, hC_eq⟩

/-- In the setup of Claim (8), if `H' ≠ H` while `H = deleteVertices S.G V(G₁)`, `H ≤ H' ≤ S.G`, and
`Catches (S.Ω.interval b a) H'`, there exist `v ∈ V(P)`, `u₀ ∈ S.Ω.interval b a`, and a path
`Q ≤ H'` in `S.G` with `IsFromToPathWithEnds S.G Q V(P) (S.Ω.interval b a) v u₀`. -/
theorem exists_fromToPath_from_P_to_ba_of_ne {P G₁ G₂ H H' : Graph α β} {a b : α}
    (hsep : IsGraphSeparation S.G G₁ G₂)
    (hinter : V(G₁) ∩ V(G₂) = V(P))
    (hba_G₂ : S.Ω.interval b a ⊆ V(G₂))
    (hHG : H ≤ S.G)
    (hH_del_G : H = deleteVertices S.G V(G₁))
    (hVH : V(H) = V(S.G) \ V(G₁))
    (hH_le_H' : H ≤ H')
    (hH'_le_G : H' ≤ S.G)
    (hcatch_H' : Catches (S.Ω.interval b a) H')
    (hne : H' ≠ H) :
    ∃ v ∈ V(P), ∃ u₀ ∈ S.Ω.interval b a, ∃ Q : Graph α β,
      Q ≤ H' ∧ IsFromToPathWithEnds S.G Q V(P) (S.Ω.interval b a) v u₀ := by
  have hex_v₀ : ∃ v₀ ∈ V(H'), v₀ ∉ V(H) := by
    by_contra! hall
    have hV_eq : V(H') = V(H) := Subset.antisymm hall hH_le_H'.vertexSet_mono
    have hE_eq : E(H') = E(H) := by
      refine Subset.antisymm (fun e he => ?_) hH_le_H'.edgeSet_mono
      obtain ⟨x, y, hxy⟩ := H'.exists_isLink_of_mem_edgeSet he
      have hxyG : S.G.IsLink e x y := hxy.mono hH'_le_G
      have hxH : x ∈ V(S.G) \ V(G₁) := hVH ▸ hV_eq ▸ hxy.left_mem
      have hyH : y ∈ V(S.G) \ V(G₁) := hVH ▸ hV_eq ▸ hxy.right_mem
      rw [hH_del_G]
      exact ((deleteVertices_isLink S.G V(G₁)).mpr ⟨hxyG, hxH.2, hyH.2⟩).edge_mem
    exact hne ((Compatible.of_le_le hH'_le_G hHG).ext hV_eq hE_eq)
  obtain ⟨v₀, hv₀H', hv₀_not_H⟩ := hex_v₀
  have hv₀G : v₀ ∈ V(S.G) := hH'_le_G.vertexSet_mono hv₀H'
  have hv₀G₁ : v₀ ∈ V(G₁) := by
    by_contra hv₀_not_G₁
    exact hv₀_not_H (hVH.symm ▸ ⟨hv₀G, hv₀_not_G₁⟩)
  let D := reachableComponent H' v₀
  have hD_comp : IsGraphComponent D H' := isGraphComponent_reachableComponent hv₀H'
  have hv₀D : v₀ ∈ V(D) := self_mem_reachableComponent hv₀H'
  obtain ⟨w₀, hw₀_ba, hw₀D⟩ := hcatch_H'.2 D hD_comp
  obtain ⟨W_D⟩ := hD_comp.2.1.2 v₀ hv₀D w₀ hw₀D
  obtain ⟨W_H', _, _⟩ := exists_walk_up_of_le hD_comp.1 W_D
  obtain ⟨Q₀, hQ₀_H', _, _⟩ := exists_isGraphPathWithEnds_of_walk W_H'
  have hQ₀_G : IsGraphPathWithEnds S.G Q₀ v₀ w₀ := hQ₀_H'.mono hH'_le_G
  have hmeet_P : (V(Q₀) ∩ V(P)).Nonempty := by
    by_contra hnot
    have hdisj : Disjoint V(Q₀) (V(G₁) ∩ V(G₂)) :=
      hinter ▸ (not_nonempty_iff_eq_empty.mp hnot |> disjoint_iff_inter_eq_empty.mpr)
    have hVQ₀_sub := connected_subset_right_of_avoids_inter hsep hQ₀_G.le hQ₀_G.isGraphConnected
      hdisj ⟨w₀, hQ₀_G.right_mem, hba_G₂ hw₀_ba⟩
    exact (hVQ₀_sub hQ₀_G.left_mem).2 hv₀G₁
  obtain ⟨x₀, hx₀Q₀, hx₀P⟩ := hmeet_P
  obtain ⟨Q₁, hQ₁_Q₀, _, hQ₁_G⟩ := hQ₀_G.exists_subpath hx₀Q₀ hQ₀_G.right_mem
  obtain ⟨v, hvP, u₀, hu₀_ba, Q, hQ_Q₁, hQ_ft⟩ :=
    hQ₁_G.exists_isFromToPathWithEnds hx₀P hw₀_ba
  exact ⟨v, hvP, u₀, hu₀_ba, Q, (hQ_Q₁.trans hQ₁_Q₀).trans hQ₀_H'.le, hQ_ft⟩

/-- In the setup of Claim (8), if `R` is an `Ω`-path with ends `a, w` (where
`w ∈ {b''} ∪ S.Ω.interval b'' a''`) that is vertex-disjoint from every member of `P_set \ {P, P''}`,
then `R` together with `p - 1` members of `P_set \ {P, P''}` forms a crooked transaction of
cardinality `p`. -/
theorem exists_crooked_of_leap_path {p : ℕ} {P_set : Set (Graph α β)} {A B : Set α}
    {P P'' R : Graph α β} {a b a'' b'' w : α}
    (hp2 : 2 ≤ p)
    (hfence : S.IsFenceFor P_set A B)
    (hcard : P_set.ncard = 3 * p + 8)
    (hP_in : P ∈ P_set)
    (hP''_diff : P'' ∈ P_set \ {P})
    (haA : a ∈ A) (hbB : b ∈ B) (hP_ends : S.IsOmegaPathWithEnds P a b)
    (ha''A : a'' ∈ A) (hb''B : b'' ∈ B) (hP''_ends : S.IsOmegaPathWithEnds P'' a'' b'')
    (hd_ab : Disjoint (S.Ω.interval a b) (S.transactionEnds P_set))
    (hd_b''a'' : Disjoint (S.Ω.interval b'' a'') (S.transactionEnds P_set))
    (hw_in : w ∈ ({b''} : Set α) ∪ S.Ω.interval b'' a'')
    (hR_ends : S.IsOmegaPathWithEnds R a w)
    (hdisj_R : ∀ R₀ ∈ P_set \ {P, P''}, Disjoint V(R) V(R₀)) :
    ∃ P_set_c : Set (Graph α β), S.IsCrookedTransaction P_set_c ∧ P_set_c.ncard = p := by
  classical
  let W := S.transactionEnds P_set
  have hW_bar : W ⊆ S.Ω.bar := S.transactionEnds_subset_bar P_set
  have haW : a ∈ A ∩ W := ⟨haA, hP_ends.mem_transactionEnds_left S hP_in⟩
  have hbW : b ∈ B ∩ W := ⟨hbB, hP_ends.mem_transactionEnds_right S hP_in⟩
  have ha''W : a'' ∈ A ∩ W := ⟨ha''A, hP''_ends.mem_transactionEnds_left S hP''_diff.1⟩
  have hb''W : b'' ∈ B ∩ W := ⟨hb''B, hP''_ends.mem_transactionEnds_right S hP''_diff.1⟩
  have hdisj_PP'' : Disjoint V(P) V(P'') := hfence.1.2 hP_in hP''_diff.1 (Ne.symm hP''_diff.2)
  have ha''_ne_a : a'' ≠ a :=
    fun h => disjoint_left.mp hdisj_PP'' hP_ends.1.left_mem (h ▸ hP''_ends.1.left_mem)
  have hb''_ne_b : b'' ≠ b :=
    fun h => disjoint_left.mp hdisj_PP'' hP_ends.1.right_mem (h ▸ hP''_ends.1.right_mem)
  have hb''_aa'' : b'' ∈ S.Ω.interval a a'' :=
    (S.Ω.mem_interval_of_mem_A_of_disjoint_AB hfence.2.1 hW_bar haW hbW hd_ab ha''W ha''_ne_a
      hb''W).2
  have ha''_b''a : a'' ∈ S.Ω.interval b'' a := S.Ω.mem_interval_rotate_left hb''_aa''
  -- Interval fence `(A_f, B_f) = ({a'', a} ∪ S.Ω.interval a'' a, S.Ω.interval a a'')`.
  let A_f : Set α := {a'', a} ∪ S.Ω.interval a'' a
  let B_f : Set α := S.Ω.interval a a''
  have hfence_f : S.Ω.IsFence A_f B_f :=
    S.Ω.isFence_interval_compl hP''_ends.2.2.1 hP_ends.2.2.1 ha''_ne_a
  have ha_Af : a ∈ A_f := Or.inl (Or.inr rfl)
  have hw_Bf : w ∈ B_f := by
    rcases hw_in with rfl | hw_int
    · exact hb''_aa''
    · exact S.Ω.interval_subset_interval_right hb''_aa'' hw_int
  -- Every `R₀ ∈ P_set \ {P, P''}` has ends `a₀ ∈ A_f`, `b₀ ∈ B_f`, and crosses `R`.
  have hR₀_props : ∀ R₀ ∈ P_set \ {P, P''},
      (∃ a₀ ∈ A_f, ∃ b₀ ∈ B_f, S.IsOmegaPathWithEnds R₀ a₀ b₀) ∧
      S.OmegaPathsCross R R₀ := by
    intro R₀ ⟨hR₀_in, hR₀_not⟩
    rw [mem_insert_iff, mem_singleton_iff, not_or] at hR₀_not
    obtain ⟨a₀, ha₀A, b₀, hb₀B, hR₀_ends⟩ := hfence.2.2 R₀ hR₀_in
    have ha₀W : a₀ ∈ A ∩ W := ⟨ha₀A, hR₀_ends.mem_transactionEnds_left S hR₀_in⟩
    have hb₀W : b₀ ∈ B ∩ W := ⟨hb₀B, hR₀_ends.mem_transactionEnds_right S hR₀_in⟩
    have hdisj_R₀P : Disjoint V(R₀) V(P) := hfence.1.2 hR₀_in hP_in hR₀_not.1
    have hdisj_R₀P'' : Disjoint V(R₀) V(P'') := hfence.1.2 hR₀_in hP''_diff.1 hR₀_not.2
    have ha₀_ne_a : a₀ ≠ a :=
      fun h => disjoint_left.mp hdisj_R₀P hR₀_ends.1.left_mem (h ▸ hP_ends.1.left_mem)
    have ha₀_ne_a'' : a₀ ≠ a'' :=
      fun h => disjoint_left.mp hdisj_R₀P'' hR₀_ends.1.left_mem (h ▸ hP''_ends.1.left_mem)
    have hb₀_ne_b'' : b₀ ≠ b'' :=
      fun h => disjoint_left.mp hdisj_R₀P'' hR₀_ends.1.right_mem (h ▸ hP''_ends.1.right_mem)
    have hb_aa₀ : b ∈ S.Ω.interval a a₀ :=
      (S.Ω.mem_interval_of_mem_A_of_disjoint_AB hfence.2.1 hW_bar haW hbW hd_ab ha₀W ha₀_ne_a hbW).2
    have ha₀_ba : a₀ ∈ S.Ω.interval b a := S.Ω.mem_interval_rotate_left hb_aa₀
    have ha''_ba₀ : a'' ∈ S.Ω.interval b a₀ :=
      (S.Ω.mem_interval_of_mem_B_of_disjoint_AB hfence.2.1.symm hW_bar hb''W ha''W hd_b''a''
        hbW ha₀W ha₀_ne_a'').1
    have ha₀_a''a : a₀ ∈ S.Ω.interval a'' a :=
      S.Ω.mem_interval_right_of_mem_interval_left ha₀_ba ha''_ba₀
    have ha_b''b₀ : a ∈ S.Ω.interval b'' b₀ :=
      (S.Ω.mem_interval_of_mem_A_of_disjoint_AB hfence.2.1.symm hW_bar hb''W ha''W hd_b''a''
        hb₀W hb₀_ne_b'' haW).2
    have hb₀_ab'' : b₀ ∈ S.Ω.interval a b'' := S.Ω.mem_interval_rotate_left ha_b''b₀
    have ha₀_Af : a₀ ∈ A_f := Or.inr ha₀_a''a
    have hb₀_Bf : b₀ ∈ B_f := S.Ω.interval_subset_interval_left hb''_aa'' hb₀_ab''
    have hb₀_aw : b₀ ∈ S.Ω.interval a w := by
      rcases hw_in with rfl | hw_int
      · exact hb₀_ab''
      · have hb''_aw : b'' ∈ S.Ω.interval a w :=
          S.Ω.mem_interval_left_of_mem_interval_right hb''_aa'' hw_int
        exact S.Ω.interval_subset_interval_left hb''_aw hb₀_ab''
    have ha₀_wa : a₀ ∈ S.Ω.interval w a := by
      rcases hw_in with rfl | hw_int
      · exact S.Ω.interval_subset_interval_right ha''_b''a ha₀_a''a
      · have ha''_wa : a'' ∈ S.Ω.interval w a :=
          S.Ω.mem_interval_right_of_mem_interval_left ha''_b''a hw_int
        exact S.Ω.interval_subset_interval_right ha''_wa ha₀_a''a
    have hcr : S.Ω.Crosses a w a₀ b₀ :=
      S.Ω.crosses_iff_interval.mpr (Or.inr ⟨hb₀_aw, ha₀_wa⟩)
    have hdisj_RR₀ : Disjoint V(R) V(R₀) :=
      hdisj_R R₀ ⟨hR₀_in, by simp [hR₀_not.1, hR₀_not.2]⟩
    exact ⟨⟨a₀, ha₀_Af, b₀, hb₀_Bf, hR₀_ends⟩,
      ⟨hdisj_RR₀, a, w, a₀, b₀, hR_ends, hR₀_ends, hcr⟩⟩
  -- Choose a subset `M ⊆ P_set \ {P, P''}` of cardinality `p - 1`.
  have hfin_P : P_set.Finite := hfence.1.finite S
  have hfin_diff : (P_set \ {P, P''}).Finite := hfin_P.sdiff
  have hcard_diff : p - 1 ≤ (P_set \ {P, P''}).ncard := by
    have h_eq : P_set \ {P, P''} = (P_set \ {P}) \ {P''} := by
      ext Q
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or]
      tauto
    rw [h_eq, ncard_sdiff_singleton_of_mem hP''_diff, ncard_sdiff_singleton_of_mem hP_in]
    omega
  have hex_sub : ∀ k ≤ (P_set \ {P, P''}).ncard, ∃ M ⊆ P_set \ {P, P''}, M.ncard = k := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨∅, empty_subset _, ncard_empty _⟩
    | succ k ih =>
      intro hk
      obtain ⟨M, hM_sub, hM_card⟩ := ih (Nat.le_of_succ_le hk)
      have hM_fin : M.Finite := hfin_diff.subset hM_sub
      have h_diff_pos : 0 < ((P_set \ {P, P''}) \ M).ncard := by
        rw [ncard_sdiff hM_sub hM_fin]
        omega
      obtain ⟨Q₀, hQ₀_in, hQ₀_not_M⟩ := (ncard_pos hfin_diff.sdiff).mp h_diff_pos
      refine ⟨insert Q₀ M, insert_subset hQ₀_in hM_sub, ?_⟩
      rw [ncard_insert_of_notMem hQ₀_not_M hM_fin, hM_card]
  obtain ⟨M, hM_sub, hM_card⟩ := hex_sub (p - 1) hcard_diff
  have hfin_M : M.Finite := hfin_diff.subset hM_sub
  have hR_not_M : R ∉ M := by
    intro hRM
    exact disjoint_left.mp (hdisj_R R (hM_sub hRM)) hR_ends.1.left_mem hR_ends.1.left_mem
  let P_set_c := insert R M
  have hcard_c : P_set_c.ncard = p := by
    rw [ncard_insert_of_notMem hR_not_M hfin_M, hM_card]
    omega
  have htrans_c : S.IsTransaction P_set_c := by
    refine ⟨A_f, B_f, ⟨?_, ?_⟩, hfence_f, ?_⟩
    · rintro Q (rfl | hQM)
      · exact ⟨a, w, hR_ends⟩
      · exact hfence.1.1 Q (hM_sub hQM).1
    · rintro Q₁ (rfl | hQ₁M) Q₂ (rfl | hQ₂M) hne
      · exact (hne rfl).elim
      · exact hdisj_R Q₂ (hM_sub hQ₂M)
      · exact (hdisj_R Q₁ (hM_sub hQ₁M)).symm
      · exact hfence.1.2 (hM_sub hQ₁M).1 (hM_sub hQ₂M).1 hne
    · rintro Q (rfl | hQM)
      · exact ⟨a, ha_Af, w, hw_Bf, hR_ends⟩
      · exact (hR₀_props Q (hM_sub hQM)).1
  have hM_ne : M.Nonempty := (ncard_pos hfin_M).mp (by omega)
  obtain ⟨R₀_wit, hR₀_wit⟩ := hM_ne
  refine ⟨P_set_c, ⟨htrans_c, ?_⟩, hcard_c⟩
  rintro Q (rfl | hQM) hperQ
  · rcases (hR₀_props R₀_wit (hM_sub hR₀_wit)).2 with ⟨hd, s₁, t₁, s₂, t₂, h1, h2, hcr⟩
    exact S.not_omegaPathsCross_of_isPeripheralIn hperQ (Or.inr hR₀_wit)
      ⟨hd.symm, s₂, t₂, s₁, t₁, h2, h1, hcr.symm⟩
  · exact S.not_omegaPathsCross_of_isPeripheralIn hperQ (Or.inl rfl)
      (hR₀_props Q (hM_sub hQM)).2

private theorem connectorDisjointOfPeripheral
    {S : Society α β} {P_set : Set (Graph α β)} {P : Graph α β} {a b : α} (hP_in : P ∈ P_set)
    (hP_ends : S.IsOmegaPathWithEnds P a b)
    (hd_ab : Disjoint (S.Ω.interval a b) (S.transactionEnds P_set)) {P' : Graph α β}
    (hP'_not_in : P' ∉ P_set \ {P}) {v : α} {P'' : Graph α β} (hP''_diff : P'' ∈ P_set \ {P})
    {A' B' A B : Set α} (hfence' : S.IsFenceFor (P_set \ {P} ∪ {P'}) A' B')
    (hfence : S.IsFenceFor P_set A B) {a'' b'' : α} (hP''_ends : S.IsOmegaPathWithEnds P'' a'' b'')
    (hW_bar : (S.transactionEnds P_set) ⊆ S.Ω.bar) (haW : a ∈ A ∩ (S.transactionEnds P_set))
    (hbW : b ∈ B ∩ (S.transactionEnds P_set)) (ha''W : a'' ∈ A ∩ (S.transactionEnds P_set))
    (hb''W : b'' ∈ B ∩ (S.transactionEnds P_set))
    (hd_b''a'' : Disjoint (S.Ω.interval b'' a'') (S.transactionEnds P_set))
    (hU'_eq_inter : S.transactionPeripheralUnion (P_set \ {P} ∪ {P'}) = S.Ω.interval b a ∩
      S.Ω.interval a'' b'')
    {u : α} {Q' : Graph α β}
    (hQ'_ft : IsFromToPathWithEnds S.G Q' {v} (V(P'') ∪ S.Ω.interval b a) v u)
    (hdisj_Q'_P' : Disjoint V(Q') V(P'))
    (hno_path_to_U' : ∀ {w : α} {M : Graph α β}, w ∈ S.transactionPeripheralUnion (P_set \ {P} ∪
      {P'}) → IsGraphPathWithEnds S.G M v w → Disjoint V(M) V(P') → Disjoint V(M) V(P'') →
      False)
    {R₀ : Graph α β} (hR₀_in : R₀ ∈ P_set) (hR₀_not : R₀ ∉ ({P, P''} : Set (Graph α β))) :
    Disjoint V(Q') V(R₀) := by
  classical
  let P_set' := P_set \ {P} ∪ {P'}
  let W := S.transactionEnds P_set
  rw [mem_insert_iff, mem_singleton_iff, not_or] at hR₀_not
  rw [disjoint_left]
  intro z hzQ' hzR₀
  obtain ⟨a₀, ha₀A, b₀, hb₀B, hR₀_ends⟩ := hfence.2.2 R₀ hR₀_in
  have ha₀W : a₀ ∈ A ∩ W := ⟨ha₀A, hR₀_ends.mem_transactionEnds_left S hR₀_in⟩
  have hdisj_R₀P : Disjoint V(R₀) V(P) := hfence.1.2 hR₀_in hP_in hR₀_not.1
  have hdisj_R₀P'' : Disjoint V(R₀) V(P'') := hfence.1.2 hR₀_in hP''_diff.1 hR₀_not.2
  have hdisj_R₀P' : Disjoint V(R₀) V(P') := hfence'.1.2 (Or.inl ⟨hR₀_in, hR₀_not.1⟩) (Or.inr rfl)
    (fun h => hP'_not_in (h ▸ ⟨hR₀_in, hR₀_not.1⟩))
  have ha₀_ne_a : a₀ ≠ a :=
    fun h => disjoint_left.mp hdisj_R₀P hR₀_ends.1.left_mem (h ▸ hP_ends.1.left_mem)
  have ha₀_ne_a'' : a₀ ≠ a'' :=
    fun h => disjoint_left.mp hdisj_R₀P'' hR₀_ends.1.left_mem (h ▸ hP''_ends.1.left_mem)
  have hb_aa₀ : b ∈ S.Ω.interval a a₀ :=
    (S.Ω.mem_interval_of_mem_A_of_disjoint_AB hfence.2.1 hW_bar haW hbW hd_ab ha₀W ha₀_ne_a hbW).2
  have ha₀_ba : a₀ ∈ S.Ω.interval b a := S.Ω.mem_interval_rotate_left hb_aa₀
  have hb''_a₀a'' : b'' ∈ S.Ω.interval a₀ a'' :=
    (S.Ω.mem_interval_of_mem_B_of_disjoint_AB hfence.2.1.symm hW_bar hb''W ha''W hd_b''a''
      hb''W ha₀W ha₀_ne_a'').2
  have ha₀_a''b'' : a₀ ∈ S.Ω.interval a'' b'' := S.Ω.mem_interval_rotate_right hb''_a₀a''
  have ha₀_U' : a₀ ∈ S.transactionPeripheralUnion P_set' :=
    hU'_eq_inter.symm ▸ ⟨ha₀_ba, ha₀_a''b''⟩
  obtain ⟨Q'_vz, Q'_zu, hQ'_vz_le, _, _, hQ'_zu_path, _, hinter_Q', _⟩ :=
    hQ'_ft.1.exists_split_at hzQ'
  obtain ⟨Q'_vz_G, _, _, hQ'_vz_path_G⟩ :=
    hQ'_ft.1.exists_subpath hQ'_ft.1.left_mem hzQ'
  obtain ⟨R₀_za, hR₀_za_le, _, hR₀_za_path_G⟩ :=
    hR₀_ends.1.exists_subpath hzR₀ hR₀_ends.1.left_mem
  have hQ'_vz_eq : Q'_vz_G = Q'_vz :=
    hQ'_ft.1.subpath_unique_of_left (hQ'_vz_path_G.of_le ‹Q'_vz_G ≤ Q'›) ‹IsGraphPathWithEnds Q'
      Q'_vz v z›
  have hdisj_vz_P'' : Disjoint V(Q'_vz_G) V(P'') := by
    rw [hQ'_vz_eq, disjoint_left]
    intro y hy_vz hyP''
    have hyu : y = u := by
      have : y ∈ V(Q') ∩ (V(P'') ∪ S.Ω.interval b a) :=
        ⟨hQ'_vz_le.vertexSet_mono hy_vz, Or.inl hyP''⟩
      rwa [hQ'_ft.2.2, mem_singleton_iff] at this
    subst hyu
    have hyz : y = z := by
      have : y ∈ V(Q'_vz) ∩ V(Q'_zu) := ⟨hy_vz, hQ'_zu_path.right_mem⟩
      rwa [hinter_Q', mem_singleton_iff] at this
    exact disjoint_left.mp hdisj_R₀P'' (hyz ▸ hzR₀) hyP''
  obtain ⟨M, hM_path, hVM_sub⟩ :=
    exists_path_subset_union_of_paths hQ'_vz_path_G hR₀_za_path_G
  have hdisj_M_P' : Disjoint V(M) V(P') :=
    (disjoint_union_left.mpr ⟨hdisj_Q'_P'.mono_left ‹Q'_vz_G ≤ Q'›.vertexSet_mono,
      hdisj_R₀P'.mono_left hR₀_za_le.vertexSet_mono⟩).mono_left hVM_sub
  have hdisj_M_P'' : Disjoint V(M) V(P'') :=
    (disjoint_union_left.mpr ⟨hdisj_vz_P'',
      hdisj_R₀P''.mono_left hR₀_za_le.vertexSet_mono⟩).mono_left hVM_sub
  exact hno_path_to_U' ha₀_U' hM_path hdisj_M_P' hdisj_M_P''

/-- **Graph Minors IX, (6.1), Claim (8)** (page 57):
"If $H'$ is a subgraph of $G$ such that $H \subseteq H'$, $\Omega(b, a)$ catches $H'$, and
there is a path of $G$ between $a$ and $b$ avoiding $V(H')$, then $H' = H$." -/
theorem lemma_6_1_claim_8 {p : ℕ} {P_set : Set (Graph α β)} {P G₁ G₂ H H' : Graph α β} {a b : α}
    (hp2 : 2 ≤ p)
    (_hp3 : p ≠ 3)
    (_hconn3 : S.IsKConnected 3)
    (_hconn4 : S.IsInternallyKConnected 4)
    (_hsimple : IsSimpleGraph S.G)
    (htrans : S.IsTransaction P_set)
    (hcard : P_set.ncard = 3 * p + 8)
    (hno_int : ∀ R ∈ P_set, Disjoint (pathInternalVerts S.G R) S.Ω.bar)
    (hmax : ∀ P_set' : Set (Graph α β),
      S.IsTransaction P_set' →
      P_set'.ncard = 3 * p + 8 →
      (∀ R ∈ P_set', Disjoint (pathInternalVerts S.G R) S.Ω.bar) →
      S.coveredComponentUnion P_set ⊆ S.coveredComponentUnion P_set' →
      S.coveredComponentUnion P_set = S.coveredComponentUnion P_set')
    (hno_crooked : ∀ P_set_c : Set (Graph α β), S.IsCrookedTransaction P_set_c → P_set_c.ncard ≠ p)
    (hP_in : P ∈ P_set)
    (hP_ends : S.IsOmegaPathWithEnds P a b)
    (hd_ab : Disjoint (S.Ω.interval a b) (S.transactionEnds P_set))
    (hsep : IsGraphSeparation S.G G₁ G₂)
    (hinter : V(G₁) ∩ V(G₂) = V(P))
    (_hP_G₁ : P ≤ G₁)
    (hab_empty : S.Ω.interval a b = ∅)
    (hba_G₂ : S.Ω.interval b a ⊆ V(G₂))
    (hHG : H ≤ S.G)
    (_hH_del_G₂ : H = deleteVertices G₂ V(G₁))
    (hH_del_G : H = deleteVertices S.G V(G₁))
    (hVH : V(H) = V(S.G) \ V(G₁))
    (hG₁_eq : G₁ = deleteVertices S.G V(H))
    (hcatch_H : Catches (S.Ω.interval b a) H)
    (hH_le_H' : H ≤ H')
    (hH'_le_G : H' ≤ S.G)
    (hcatch_H' : Catches (S.Ω.interval b a) H')
    (hex_path : ∃ P' : Graph α β, IsGraphPathWithEnds S.G P' a b ∧ Avoids P' V(H')) :
    H' = H := by
  by_contra hne
  obtain ⟨P', hP', hav'⟩ := hex_path
  have hdisj_P'_H : Disjoint V(P') V(H) := Disjoint.mono_right hH_le_H'.vertexSet_mono hav'.symm
  have hP'_le : P' ≤ G₁ := hG₁_eq ▸ le_deleteVertices hP'.le hdisj_P'_H
  have hP'_ends : S.IsOmegaPathWithEnds P' a b :=
    ⟨hP', hP_ends.2.1, hP_ends.2.2.1, hP_ends.2.2.2⟩
  have hno_int_P' : Disjoint (pathInternalVerts S.G P') S.Ω.bar := by
    rw [disjoint_left]
    rintro z ⟨hzP', hz_not_ends⟩ hz_bar
    rw [hP'.pathEnds_eq, mem_insert_iff, mem_singleton_iff, not_or] at hz_not_ends
    rcases S.Ω.mem_interval_or_interval_swap hP_ends.2.2.1 hP_ends.2.2.2 hz_bar
      hP_ends.2.1 hz_not_ends.1 hz_not_ends.2 with hz_ab | hz_ba
    · exact (hab_empty ▸ hz_ab).elim
    · exact disjoint_left.mp hav' (hH_le_H'.vertexSet_mono (hcatch_H.1 hz_ba)) hzP'
  have hab_G₁ : S.Ω.interval a b ⊆ V(G₁) := hab_empty ▸ empty_subset _
  let P_set' := (P_set \ {P}) ∪ {P'}
  obtain ⟨hP'_not_in, htrans', hcard', hno_int', hW_eq, hper_P', hper_iff, hU_eq, hC_eq⟩ :=
    S.replacement_same_ends_properties htrans hcard hno_int hmax hP_in hP_ends hd_ab hsep hinter
      hab_G₁ hba_G₂ hP'_ends hP'_le hno_int_P'
  -- By `H' ≠ H`, obtain `v ∈ V(P)`, `u₀ ∈ S.Ω.interval b a`, and `Q ≤ H'` from `v` to `u₀`.
  obtain ⟨v, hvP, u₀, hu₀_ba, Q, hQ_H', hQ_ft⟩ :=
    S.exists_fromToPath_from_P_to_ba_of_ne hsep hinter hba_G₂ hHG hH_del_G hVH hH_le_H'
      hH'_le_G hcatch_H' hne
  have hper_P : S.IsPeripheralIn P_set P := ⟨hP_in, a, b, hP_ends, Or.inl hd_ab⟩
  have hv_not_C' : v ∉ S.coveredComponentUnion P_set' := by
    rw [← hC_eq]
    exact fun hvC => disjoint_left.mp (S.disjoint_coveredComponentUnion_of_isPeripheralIn hP_in
      hper_P)
      hvC hvP
  have hdisj_Q_P' : Disjoint V(Q) V(P') := Disjoint.mono_left hQ_H'.vertexSet_mono hav'
  have hcard_ge2 : 2 ≤ P_set.ncard := by omega
  have hcard'_ge2 : 2 ≤ P_set'.ncard := by
    change 2 ≤ (P_set \ {P} ∪ {P'}).ncard
    omega
  obtain ⟨_, hU_P'⟩ :=
    S.peripheralIntervalSet_eq_interval htrans' hcard'_ge2 (Or.inr rfl) hP'_ends (hW_eq ▸ hd_ab)
  -- `P_set'` must have a second peripheral member `P'' ∈ P_set \ {P}`.
  have hex_P'' : ∃ P'' ∈ P_set \ {P}, S.IsPeripheralIn P_set' P'' := by
    by_contra! hno_P''
    have hper_only_P' : ∀ R ∈ P_set', S.IsPeripheralIn P_set' R → R = P' := by
      rintro R (hR | rfl) hperR
      · exact (hno_P'' R hR hperR).elim
      · rfl
    have hu₀_U' : u₀ ∈ S.transactionPeripheralUnion P_set' := by
      refine ⟨hu₀_ba.1.1, mem_iInter₂.mpr fun R ⟨hR_in, hperR⟩ => ?_⟩
      rcases hper_only_P' R hR_in hperR with rfl
      exact hU_P' ▸ hu₀_ba
    have hv_in_C' : v ∈ S.coveredComponentUnion P_set' := by
      refine ⟨hP_ends.1.le.vertexSet_mono hvP, u₀, hu₀_U', Q, hQ_ft.1, fun R hR_in hperR => ?_⟩
      rcases hper_only_P' R hR_in hperR with rfl
      exact hdisj_Q_P'.symm
    exact hv_not_C' hv_in_C'
  obtain ⟨P'', hP''_diff, hper_P''_in'⟩ := hex_P''
  have hper_P'' : S.IsPeripheralIn P_set P'' := (hper_iff P'' hP''_diff).mp hper_P''_in'
  -- Every peripheral member of `P_set'` is either `P'` or `P''`.
  obtain ⟨_, _, hfence'⟩ := htrans'
  have hper'_eq : ∀ R ∈ P_set', S.IsPeripheralIn P_set' R → R = P' ∨ R = P'' := by
    intro R hR_in hperR
    by_contra! hne_both
    exact hfence'.not_three_peripheral S hper_P' hper_P''_in' hperR
      (Ne.symm ( fun h => hP'_not_in (h ▸ hP''_diff) ))
      hne_both.1.symm hne_both.2.symm
  -- Orient the fence `(A, B)` of `P_set` so `a ∈ A` and `b ∈ B`.
  obtain ⟨A₀, B₀, hfence₀⟩ := htrans
  have hex_fence_AB : ∃ A B : Set α, S.IsFenceFor P_set A B ∧ a ∈ A ∧ b ∈ B := by
    obtain ⟨a₀, ha₀A, b₀, hb₀B, hP₀⟩ := hfence₀.2.2 P hP_in
    rcases hP_ends.ends_eq S hP₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨A₀, B₀, hfence₀, ha₀A, hb₀B⟩
    · refine ⟨B₀, A₀, ⟨hfence₀.1, hfence₀.2.1.symm, fun R hR => ?_⟩, hb₀B, ha₀A⟩
      obtain ⟨x, hx, y, hy, hR_xy⟩ := hfence₀.2.2 R hR
      exact ⟨y, hy, x, hx, hR_xy.symm S⟩
  obtain ⟨A, B, hfence, haA, hbB⟩ := hex_fence_AB
  obtain ⟨a'', ha''A, b'', hb''B, hP''_ends⟩ := hfence.2.2 P'' hP''_diff.1
  let W := S.transactionEnds P_set
  have hW_bar : W ⊆ S.Ω.bar := S.transactionEnds_subset_bar P_set
  have haW : a ∈ A ∩ W := ⟨haA, hP_ends.mem_transactionEnds_left S hP_in⟩
  have hbW : b ∈ B ∩ W := ⟨hbB, hP_ends.mem_transactionEnds_right S hP_in⟩
  have ha''W : a'' ∈ A ∩ W := ⟨ha''A, hP''_ends.mem_transactionEnds_left S hP''_diff.1⟩
  have hb''W : b'' ∈ B ∩ W := ⟨hb''B, hP''_ends.mem_transactionEnds_right S hP''_diff.1⟩
  have hdisj_PP'' : Disjoint V(P) V(P'') := hfence.1.2 hP_in hP''_diff.1 (Ne.symm hP''_diff.2)
  have ha''_ne_a : a'' ≠ a :=
    fun h => disjoint_left.mp hdisj_PP'' hP_ends.1.left_mem (h ▸ hP''_ends.1.left_mem)
  have ha_in_a''b'' : a ∈ S.Ω.interval a'' b'' :=
    (S.Ω.mem_interval_of_mem_A_of_disjoint_AB hfence.2.1 hW_bar haW hbW hd_ab ha''W ha''_ne_a
      hb''W).1
  have hd_b''a'' : Disjoint (S.Ω.interval b'' a'') W := by
    rcases (hP''_ends.isPeripheralIn_iff S hP''_diff.1).mp hper_P'' with hd₁ | hd₂
    · exact (disjoint_left.mp hd₁ ha_in_a''b'' haW.2).elim
    · exact hd₂
  obtain ⟨_, hU_P''⟩ := S.peripheralIntervalSet_eq_interval ⟨A, B, hfence⟩ hcard_ge2
    hP''_diff.1 (hP''_ends.symm S) hd_b''a''
  have hU_P''_in' : S.peripheralIntervalSet P_set' P'' = S.Ω.interval a'' b'' := by
    unfold P_set' peripheralIntervalSet
    rw [hW_eq]
    exact hU_P''
  have hU'_eq_inter : S.transactionPeripheralUnion P_set' =
      S.Ω.interval b a ∩ S.Ω.interval a'' b'' := by
    ext x
    simp only [transactionPeripheralUnion, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    constructor
    · intro ⟨_, hx⟩
      exact ⟨hU_P' ▸ hx P' ⟨Or.inr rfl, hper_P'⟩, hU_P''_in' ▸ hx P'' ⟨Or.inl hP''_diff,
        hper_P''_in'⟩⟩
    · rintro ⟨hx_ba, hx_a''b''⟩
      refine ⟨hx_ba.1.1, fun R ⟨hR_in, hperR⟩ => ?_⟩
      rcases hper'_eq R hR_in hperR with rfl | rfl
      · exact hU_P'.symm ▸ hx_ba
      · exact hU_P''_in'.symm ▸ hx_a''b''
  -- Take the minimal subpath `Q' ≤ Q` from `{v}` to `V(P'') ∪ S.Ω.interval b a`.
  obtain ⟨v', hv'_eq, u, hu_in, Q', hQ'_Q, hQ'_ft_raw⟩ :=
    hQ_ft.1.exists_isFromToPathWithEnds (X := {v}) (Y := V(P'') ∪ S.Ω.interval b a)
      (mem_singleton v) (Or.inr hu₀_ba)
  have hQ'_ft : IsFromToPathWithEnds S.G Q' {v} (V(P'') ∪ S.Ω.interval b a) v u :=
    mem_singleton_iff.mp hv'_eq ▸ hQ'_ft_raw
  have hdisj_Q'_P' : Disjoint V(Q') V(P') := hdisj_Q_P'.mono_left hQ'_Q.vertexSet_mono
  have hVQ'_inter_P : V(Q') ∩ V(P) = {v} := by
    refine Subset.antisymm (fun z ⟨hzQ', hzP⟩ => ?_)
      (singleton_subset_iff.mpr ⟨hQ'_ft.1.left_mem, hvP⟩)
    have : z ∈ V(Q) ∩ V(P) := ⟨hQ'_Q.vertexSet_mono hzQ', hzP⟩
    rwa [hQ_ft.2.1] at this
  -- Any path in `S.G` from `v` to `U(P_set')` avoiding `V(P')` and `V(P'')` contradicts `v ∉
  -- C(P_set')`.
  have hno_path_to_U' : ∀ {w : α} {M : Graph α β},
      w ∈ S.transactionPeripheralUnion P_set' →
      IsGraphPathWithEnds S.G M v w →
      Disjoint V(M) V(P') → Disjoint V(M) V(P'') → False := by
    intro w M hw_U' hM hd_P' hd_P''
    refine hv_not_C' ⟨hP_ends.1.le.vertexSet_mono hvP, w, hw_U', M, hM, fun R hR_in hperR => ?_⟩
    rcases hper'_eq R hR_in hperR with rfl | rfl
    · exact hd_P'.symm
    · exact hd_P''.symm
  -- Deduce `u ∈ V(P'') ∨ u ∈ S.Ω.interval b'' a''`.
  have hu_P''_or_b''a'' : u ∈ V(P'') ∨ u ∈ S.Ω.interval b'' a'' := by
    by_cases huP'' : u ∈ V(P'')
    · exact Or.inl huP''
    · have hu_ba : u ∈ S.Ω.interval b a := hu_in.resolve_left huP''
      have hdisj_Q'_P'' : Disjoint V(Q') V(P'') := by
        rw [disjoint_left]
        intro z hzQ' hzP''
        have hzu : z = u := by
          have : z ∈ V(Q') ∩ (V(P'') ∪ S.Ω.interval b a) := ⟨hzQ', Or.inl hzP''⟩
          rwa [hQ'_ft.2.2, mem_singleton_iff] at this
        exact huP'' (hzu ▸ hzP'')
      have hu_not_U' : u ∉ S.transactionPeripheralUnion P_set' :=
        fun hu_U' => hno_path_to_U' hu_U' hQ'_ft.1 hdisj_Q'_P' hdisj_Q'_P''
      have hu_not_a''b'' : u ∉ S.Ω.interval a'' b'' :=
        fun hu_a''b'' => hu_not_U' (hU'_eq_inter.symm ▸ ⟨hu_ba, hu_a''b''⟩)
      have hu_ne_a'' : u ≠ a'' := fun h => huP'' (h ▸ hP''_ends.1.left_mem)
      have hu_ne_b'' : u ≠ b'' := fun h => huP'' (h ▸ hP''_ends.1.right_mem)
      exact Or.inr ((S.Ω.mem_interval_or_interval_swap hP''_ends.2.2.1 hP''_ends.2.2.2 hu_ba.1.1
        hP''_ends.2.1 hu_ne_a'' hu_ne_b'').resolve_left hu_not_a''b'')
  -- Deduce `Disjoint V(Q') V(R₀)` for every `R₀ ∈ P_set \ {P, P''}`.
  have hdisj_Q'_R₀ : ∀ R₀ ∈ P_set \ {P, P''}, Disjoint V(Q') V(R₀) := by
    intro R₀ ⟨hR₀_in, hR₀_not⟩
    exact connectorDisjointOfPeripheral hP_in hP_ends hd_ab hP'_not_in hP''_diff hfence' hfence
      hP''_ends hW_bar haW hbW ha''W hb''W hd_b''a'' hU'_eq_inter hQ'_ft hdisj_Q'_P'
      hno_path_to_U' hR₀_in hR₀_not
  -- Construct `(R, w)` with `w ∈ {b''} ∪ S.Ω.interval b'' a''` and `S.IsOmegaPathWithEnds R a w`.
  obtain ⟨P_av, hP_av_le, _, hP_av_G⟩ := hP_ends.1.exists_subpath hP_ends.1.left_mem hvP
  have hinter_av_Q' : V(P_av) ∩ V(Q') = {v} := by
    refine Subset.antisymm (fun z ⟨hz_av, hzQ'⟩ => ?_)
      (singleton_subset_iff.mpr ⟨hP_av_G.right_mem, hQ'_ft.1.left_mem⟩)
    have : z ∈ V(Q') ∩ V(P) := ⟨hzQ', hP_av_le.vertexSet_mono hz_av⟩
    rwa [hVQ'_inter_P] at this
  let R₁ := subgraphUnion S.G P_av Q'
  have hR₁_G : IsGraphPathWithEnds S.G R₁ a u := hP_av_G.subgraphUnion hQ'_ft.1 hinter_av_Q'
  have hex_R : ∃ R : Graph α β, ∃ w ∈ ({b''} : Set α) ∪ S.Ω.interval b'' a'',
      S.IsOmegaPathWithEnds R a w ∧
      ∀ R₀ ∈ P_set \ {P, P''}, Disjoint V(R) V(R₀) := by
    rcases hu_P''_or_b''a'' with huP'' | hu_b''a''
    · obtain ⟨P''_ub'', hP''_ub''_le, _, hP''_ub''_G⟩ :=
        hP''_ends.1.exists_subpath huP'' hP''_ends.1.right_mem
      have hinter_R₁_ub'' : V(R₁) ∩ V(P''_ub'') = {u} := by
        refine Subset.antisymm (fun z ⟨hzR₁, hz_ub''⟩ => ?_)
          (singleton_subset_iff.mpr ⟨hR₁_G.right_mem, hP''_ub''_G.left_mem⟩)
        have hzP'' : z ∈ V(P'') := hP''_ub''_le.vertexSet_mono hz_ub''
        rcases (vertexSet_subgraphUnion S.G P_av Q' ▸ hzR₁ : z ∈ V(P_av) ∪ V(Q')) with hz_av | hzQ'
        · exact (disjoint_left.mp hdisj_PP'' (hP_av_le.vertexSet_mono hz_av) hzP'').elim
        · have : z ∈ V(Q') ∩ (V(P'') ∪ S.Ω.interval b a) := ⟨hzQ', Or.inl hzP''⟩
          rwa [hQ'_ft.2.2] at this
      let R := subgraphUnion S.G R₁ P''_ub''
      have hR_G : IsGraphPathWithEnds S.G R a b'' := hR₁_G.subgraphUnion hP''_ub''_G hinter_R₁_ub''
      have ha_ne_b'' : a ≠ b'' :=
        fun h => disjoint_left.mp hdisj_PP'' hP_ends.1.left_mem (h ▸ hP''_ends.1.right_mem)
      refine ⟨R, b'', Or.inl rfl, ⟨hR_G, ha_ne_b'', hP_ends.2.2.1, hP''_ends.2.2.2⟩,
        fun R₀ hR₀ => ?_⟩
      have hR₀_not := hR₀.2
      rw [mem_insert_iff, mem_singleton_iff, not_or] at hR₀_not
      rw [vertexSet_subgraphUnion, vertexSet_subgraphUnion, disjoint_union_left,
        disjoint_union_left]
      exact ⟨⟨(hfence.1.2 hP_in hR₀.1 (Ne.symm hR₀_not.1)).mono_left hP_av_le.vertexSet_mono,
        hdisj_Q'_R₀ R₀ hR₀⟩,
        (hfence.1.2 hP''_diff.1 hR₀.1 (Ne.symm hR₀_not.2)).mono_left hP''_ub''_le.vertexSet_mono⟩
    · have ha_ne_u : a ≠ u :=
        fun h => disjoint_left.mp hd_b''a'' (h ▸ hu_b''a'') haW.2
      refine ⟨R₁, u, Or.inr hu_b''a'', ⟨hR₁_G, ha_ne_u, hP_ends.2.2.1, hu_b''a''.1.1⟩,
        fun R₀ hR₀ => ?_⟩
      have hR₀_not := hR₀.2
      rw [mem_insert_iff, mem_singleton_iff, not_or] at hR₀_not
      rw [vertexSet_subgraphUnion, disjoint_union_left]
      exact ⟨(hfence.1.2 hP_in hR₀.1 (Ne.symm hR₀_not.1)).mono_left hP_av_le.vertexSet_mono,
        hdisj_Q'_R₀ R₀ hR₀⟩
  obtain ⟨R, w, hw_in, hR_ends, hdisj_R⟩ := hex_R
  obtain ⟨P_set_c, hcr_c, hcard_c⟩ :=
    S.exists_crooked_of_leap_path hp2 hfence hcard hP_in hP''_diff haA hbB hP_ends ha''A hb''B
      hP''_ends hd_ab hd_b''a'' hw_in hR_ends hdisj_R
  exact hno_crooked P_set_c hcr_c hcard_c

/-- Deduction of `G₁ = P` from `(7)`, `(8)`, and `(2.1)` (`theorem_2_1_proof`, Graph Minors IX,
Section 6,
page 57:
"As $H = G_2 \setminus V(G_1)$ and $G_1$ is induced, it follows that $G_1 = G \setminus
V(H)$. Hence, if $G_1 \ne P$, then by (2.1) there would be a separation $(J_1, J_2)$ of $G$
with $\{a, b\} \subseteq V(J_1)$, $|V(J_1 \cap J_2)| = 2$, $H \subseteq J_1$ and $V(J_1) \ne
V(G)$. But then $(J_2, J_1)$ would by (7) be a separation of $(G, \Omega)$, contradicting
the 3-connectedness of $(G, \Omega)$. It follows that $G_1 = P$."). -/
theorem eq_path_of_claim_7_and_8 {P G₁ H : Graph α β} {a b : α}
    (hconn3 : S.IsKConnected 3)
    (hsimple : IsSimpleGraph S.G)
    (hP_ends : S.IsOmegaPathWithEnds P a b)
    (hHG : H ≤ S.G)
    (hG₁_eq : G₁ = deleteVertices S.G V(H))
    (hPG₁ : IsGraphPathWithEnds G₁ P a b)
    (hab_empty : S.Ω.interval a b = ∅)
    (hcatch_H : Catches (S.Ω.interval b a) H)
    (hclaim8 : ∀ H' : Graph α β, H ≤ H' → H' ≤ S.G → Catches (S.Ω.interval b a) H' →
      (∃ Q : Graph α β, IsGraphPathWithEnds S.G Q a b ∧ Avoids Q V(H')) → H' = H) :
    P = G₁ := by
  have hPG_del : IsGraphPathWithEnds (deleteVertices S.G V(H)) P a b := hG₁_eq ▸ hPG₁
  have hloopless : ∀ x : α, ¬ S.G.Adj x x := fun x ⟨e, he⟩ => hsimple.1 e he.edge_mem x he
  have hsimple' : ∀ e₁ e₂ x y, S.G.IsLink e₁ x y → S.G.IsLink e₂ x y → e₁ = e₂ :=
    fun e₁ e₂ x y h1 h2 => hsimple.2 e₁ h1.edge_mem e₂ h2.edge_mem x y h1 h2
  rcases theorem_2_1_proof hloopless hsimple' hP_ends.2.1 hHG hcatch_H hclaim8 hPG_del with
    h_eq | ⟨J₁, J₂, hsep_J, hab_J₁, hcard_J, _, _, hH_J₁, hVJ₁_ne⟩
  · exact hG₁_eq ▸ h_eq
  · exfalso
    have hbar_J₁ : S.Ω.bar ⊆ V(J₁) := by
      intro z hz_bar
      by_cases hza : z = a
      · exact hab_J₁ (Or.inl hza)
      · by_cases hzb : z = b
        · exact hab_J₁ (Or.inr hzb)
        · rcases S.Ω.mem_interval_or_interval_swap hP_ends.2.2.1 hP_ends.2.2.2 hz_bar
            hP_ends.2.1 hza hzb with hz_ab | hz_ba
          · rw [hab_empty] at hz_ab
            exact hz_ab.elim
          · exact hH_J₁.vertexSet_mono (hcatch_H.1 hz_ba)
    have hsep_soc : S.IsSocietySeparation J₂ J₁ := ⟨IsGraphSeparation.symm hsep_J, hbar_J₁⟩
    have hcard_J' : (V(J₂) ∩ V(J₁)).ncard ≤ 2 := by
      rw [inter_comm, hcard_J]
    exact hconn3 2 (by decide) J₂ J₁ ⟨hsep_soc, hcard_J', hVJ₁_ne⟩

/-- **Graph Minors IX, (6.1), Claim (9)** (page 57):
"If $P \in \mathcal{P}$ is peripheral and separating, with ends $a, b$ where $\Omega(a, b)
\cap V(\mathcal{P}) = \emptyset$, then $\Omega(a, b) = \emptyset$, $P$ is induced, and
$\Omega(b, a)$ catches $G \setminus V(P)$." -/
theorem lemma_6_1_claim_9 {p : ℕ} {P_set : Set (Graph α β)} {P : Graph α β} {a b : α}
    (hp2 : 2 ≤ p) (hp3 : p ≠ 3)
    (hconn3 : S.IsKConnected 3)
    (hconn4 : S.IsInternallyKConnected 4)
    (hno_crooked : ∀ P_set_c : Set (Graph α β), S.IsCrookedTransaction P_set_c → P_set_c.ncard ≠ p)
    (hsimple : IsSimpleGraph S.G)
    (hno_iso : ∀ v ∈ S.Ω.bar, ∃ u : α, S.G.Adj v u)
    (htrans : S.IsTransaction P_set)
    (hcard : P_set.ncard = 3 * p + 8)
    (hno_int : ∀ R ∈ P_set, Disjoint (pathInternalVerts S.G R) S.Ω.bar)
    (hmax : ∀ P_set' : Set (Graph α β),
      S.IsTransaction P_set' →
      P_set'.ncard = 3 * p + 8 →
      (∀ R ∈ P_set', Disjoint (pathInternalVerts S.G R) S.Ω.bar) →
      S.coveredComponentUnion P_set ⊆ S.coveredComponentUnion P_set' →
      S.coveredComponentUnion P_set = S.coveredComponentUnion P_set')
    (hP_in : P ∈ P_set)
    (hP_sep : S.IsSeparatingOmegaPath P)
    (hP_ends : S.IsOmegaPathWithEnds P a b)
    (hd_ab : Disjoint (S.Ω.interval a b) (S.transactionEnds P_set)) :
    S.Ω.interval a b = ∅ ∧
      P = S.G.induce V(P) ∧
      Catches (S.Ω.interval b a) (deleteVertices S.G V(P)) := by
  have hno_intP : Disjoint (pathInternalVerts S.G P) S.Ω.bar := hno_int P hP_in
  obtain ⟨G₁, G₂, H, hsep, hinter, hP_G₁, hab_G₁, hba_G₂, hHG, hH_del_G₂, hH_del_G,
    hVH, hG₁_eq, hcatch_H⟩ :=
    S.exists_minimal_separation_of_separating hP_ends hP_sep hno_intP
  have hloopless : ∀ x : α, ¬ S.G.Adj x x := fun x ⟨e, he⟩ => hsimple.1 e he.edge_mem x he
  have hclaim6 : ∀ P' : Graph α β, S.IsOmegaPath P' → P' ≤ G₁ → S.IsOmegaPathWithEnds P' a b :=
    fun P' hP'_omega hP'_le =>
      S.lemma_6_1_claim_6 htrans hcard hno_int hmax hP_in hP_ends hd_ab hsep hinter
        hab_G₁ hba_G₂ hP'_omega hP'_le
  have hab_empty : S.Ω.interval a b = ∅ :=
    S.lemma_6_1_claim_7 hconn3 hloopless hno_iso hP_ends hno_intP hsep hinter hP_G₁
      hab_G₁ hba_G₂ hclaim6
  have hclaim8 : ∀ H' : Graph α β, H ≤ H' → H' ≤ S.G → Catches (S.Ω.interval b a) H' →
      (∃ Q : Graph α β, IsGraphPathWithEnds S.G Q a b ∧ Avoids Q V(H')) → H' = H :=
    fun H' hH_le_H' hH'_le_G hcatch_H' hex_path =>
      S.lemma_6_1_claim_8 hp2 hp3 hconn3 hconn4 hsimple htrans hcard hno_int hmax hno_crooked
        hP_in hP_ends hd_ab hsep hinter hP_G₁ hab_empty hba_G₂ hHG hH_del_G₂ hH_del_G hVH
        hG₁_eq hcatch_H hH_le_H' hH'_le_G hcatch_H' hex_path
  have hPG₁ : IsGraphPathWithEnds G₁ P a b := hP_ends.1.of_le hP_G₁
  have hP_eq_G₁ : P = G₁ :=
    S.eq_path_of_claim_7_and_8 hconn3 hsimple hP_ends hHG hG₁_eq hPG₁ hab_empty hcatch_H hclaim8
  have hVP_eq : V(P) = V(G₁) := congrArg vertexSet hP_eq_G₁
  have hP_ind : P = S.G.induce V(P) := by
    have hV_diff : V(S.G) \ V(H) = V(P) := by
      rw [hVH, hVP_eq, sdiff_sdiff_right_self,
        inter_eq_right.mpr (hG₁_eq ▸ deleteVertices_le S.G V(H)).vertexSet_mono]
    calc
      P = G₁ := hP_eq_G₁
      _ = S.G.induce (V(S.G) \ V(H)) := hG₁_eq
      _ = S.G.induce V(P) := by rw [hV_diff]
  have hH_eq_delP : deleteVertices S.G V(P) = H := by
    rw [hH_del_G, hVP_eq]
  exact ⟨hab_empty, hP_ind, hH_eq_delP ▸ hcatch_H⟩

/-! ## Statement `S_t` and the inductive proof of (6.1) (page 58) -/

/-- **Graph Minors IX, Section 6, Statement `S_t`** (page 58):
"For an integer $t$ with $0 \le t \le 2$, let $\mathbf{S}_t$ be the following statement.
*Statement* $\mathbf{S}_t$. *The society $(G, \Omega)$ has a transaction $\mathcal{P}_t$
with $|\mathcal{P}_t| \ge 3p + 8 - t(p + 4)$ and with at most $2 - t$ peripheral separating
members. Moreover, every separating member of $\mathcal{P}_t$ is in $\mathcal{P}$, and every
peripheral separating member of $\mathcal{P}_t$ is peripheral in $\mathcal{P}$." -/
def StatementSt (p : ℕ) (P_set : Set (Graph α β)) (t : ℕ) : Prop :=
  ∃ P_set_t : Set (Graph α β),
    S.IsTransaction P_set_t ∧
    3 * p + 8 - t * (p + 4) ≤ P_set_t.ncard ∧
    {P ∈ P_set_t | S.IsPeripheralIn P_set_t P ∧ S.IsSeparatingOmegaPath P}.ncard ≤ 2 - t ∧
    (∀ P ∈ P_set_t, S.IsSeparatingOmegaPath P → P ∈ P_set) ∧
    (∀ P ∈ P_set_t, S.IsPeripheralIn P_set_t P → S.IsSeparatingOmegaPath P →
      S.IsPeripheralIn P_set P)

/-- Any transaction `P_set` in `S` has at most 2 peripheral members. -/
theorem ncard_peripheral_le_two {P_set : Set (Graph α β)} (htrans : S.IsTransaction P_set) :
    {P ∈ P_set | S.IsPeripheralIn P_set P}.ncard ≤ 2 := by
  classical
  obtain ⟨A, B, hfence⟩ := htrans
  have hfin : {P ∈ P_set | S.IsPeripheralIn P_set P}.Finite :=
    (hfence.1.finite S).subset fun _ h => h.1
  by_contra hgt
  have hge3 : 3 ≤ {P ∈ P_set | S.IsPeripheralIn P_set P}.ncard := by omega
  obtain ⟨P₁, hP₁⟩ : {P ∈ P_set | S.IsPeripheralIn P_set P}.Nonempty :=
    (ncard_pos hfin).mp (by omega)
  have hfin₁ : ({P ∈ P_set | S.IsPeripheralIn P_set P} \ {P₁}).Finite := hfin.sdiff
  have hcard₁ : 2 ≤ ({P ∈ P_set | S.IsPeripheralIn P_set P} \ {P₁}).ncard := by
    have := ncard_sdiff_singleton_of_mem hP₁
    omega
  obtain ⟨P₂, hP₂_mem⟩ : ({P ∈ P_set | S.IsPeripheralIn P_set P} \ {P₁}).Nonempty :=
    (ncard_pos hfin₁).mp (by omega)
  rcases hP₂_mem with ⟨hP₂, hP₂_ne₁⟩
  have hfin₂ : (({P ∈ P_set | S.IsPeripheralIn P_set P} \ {P₁}) \ {P₂}).Finite := hfin₁.sdiff
  have hcard₂ : 1 ≤ (({P ∈ P_set | S.IsPeripheralIn P_set P} \ {P₁}) \ {P₂}).ncard := by
    have := ncard_sdiff_singleton_of_mem (s := {P ∈ P_set | S.IsPeripheralIn P_set P} \ {P₁})
      ⟨hP₂, hP₂_ne₁⟩
    omega
  obtain ⟨P₃, hP₃_mem⟩ :
      (({P ∈ P_set | S.IsPeripheralIn P_set P} \ {P₁}) \ {P₂}).Nonempty :=
    (ncard_pos hfin₂).mp (by omega)
  rcases hP₃_mem with ⟨⟨hP₃, hP₃_ne₁⟩, hP₃_ne₂⟩
  exact hfence.not_three_peripheral S hP₁.2 hP₂.2 hP₃.2
    (Ne.symm (mem_singleton_iff.not.mp hP₂_ne₁))
    (Ne.symm (mem_singleton_iff.not.mp hP₃_ne₁))
    (Ne.symm (mem_singleton_iff.not.mp hP₃_ne₂))

/-- Base case `t = 0` of Statement `S_t` (Graph Minors IX, Section 6, page 58:
"Now $\mathbf{S}_0$ is true, with $\mathcal{P}_0 = \mathcal{P}$."). -/
theorem statementSt_zero {p : ℕ} {P_set : Set (Graph α β)}
    (htrans : S.IsTransaction P_set)
    (hcard : P_set.ncard = 3 * p + 8) :
    S.StatementSt p P_set 0 := by
  have htrans' : S.IsTransaction P_set := htrans
  obtain ⟨A, B, hfence⟩ := htrans
  have hfin_per : {P ∈ P_set | S.IsPeripheralIn P_set P}.Finite :=
    (hfence.1.finite S).subset fun _ h => h.1
  have hsub_per :
      {P ∈ P_set | S.IsPeripheralIn P_set P ∧ S.IsSeparatingOmegaPath P} ⊆
        {P ∈ P_set | S.IsPeripheralIn P_set P} :=
    fun _ hP => ⟨hP.1, hP.2.1⟩
  have hle2 : {P ∈ P_set | S.IsPeripheralIn P_set P ∧ S.IsSeparatingOmegaPath P}.ncard ≤ 2 :=
    (ncard_le_ncard hsub_per hfin_per).trans (S.ncard_peripheral_le_two htrans')
  refine ⟨P_set, htrans', by omega, hle2, fun _ hP _ => hP, fun _ _ hper _ => hper⟩

/-- Inductive step `S_t → S_{t+1}` for `t < 2` (Graph Minors IX, Section 6, page 58:
"We shall show that for $t = 0$ or $t = 1$, if $\mathbf{S}_t$ is true then $\mathbf{S}_{t+1}$
is true."). -/
theorem statementSt_succ {p t : ℕ} {P_set : Set (Graph α β)}
    (_ht : t < 2)
    (hSt : S.StatementSt p P_set t)
    (hstep_of_peripheral_sep : ∀ P_set_t : Set (Graph α β),
      S.IsTransaction P_set_t →
      3 * p + 8 - t * (p + 4) ≤ P_set_t.ncard →
      {P ∈ P_set_t | S.IsPeripheralIn P_set_t P ∧ S.IsSeparatingOmegaPath P}.ncard ≤ 2 - t →
      (∀ P ∈ P_set_t, S.IsSeparatingOmegaPath P → P ∈ P_set) →
      (∀ P ∈ P_set_t, S.IsPeripheralIn P_set_t P → S.IsSeparatingOmegaPath P →
        S.IsPeripheralIn P_set P) →
      (∃ P₁ ∈ P_set_t, S.IsPeripheralIn P_set_t P₁ ∧ S.IsSeparatingOmegaPath P₁) →
      S.StatementSt p P_set (t + 1)) :
    S.StatementSt p P_set (t + 1) := by
  obtain ⟨P_set_t, htrans_t, hcard_t, hper_card_t, hsep_mem_t, hper_sep_t⟩ := hSt
  by_cases hex_per_sep : ∃ P₁ ∈ P_set_t, S.IsPeripheralIn P_set_t P₁ ∧ S.IsSeparatingOmegaPath P₁
  · -- `P_set_t` has a peripheral separating member `P₁`.
    exact hstep_of_peripheral_sep P_set_t htrans_t hcard_t hper_card_t hsep_mem_t hper_sep_t
      hex_per_sep
  · -- `P_set_t` has no peripheral separating members; set `P_set_{t+1} = P_set_t`.
    push Not at hex_per_sep
    have hempty : {P ∈ P_set_t | S.IsPeripheralIn P_set_t P ∧ S.IsSeparatingOmegaPath P} = ∅ := by
      ext P
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun hP hper => hex_per_sep P hP hper
    have hcard_next : 3 * p + 8 - (t + 1) * (p + 4) ≤ P_set_t.ncard :=
      (Nat.sub_le_sub_left (Nat.mul_le_mul_right (p + 4) (Nat.le_succ t)) (3 * p + 8)).trans hcard_t
    refine ⟨P_set_t, htrans_t, hcard_next, ?_, hsep_mem_t, hper_sep_t⟩
    rw [hempty, ncard_empty]
    omega

/-- In the inductive step `S_t → S_{t+1}`, if `P_set_t = {P₁, …, P_n}` is enumerated in order with
`P₁` peripheral and separating, and some `P_j` (`2 ≤ j ≤ p + 5`) is non-separating, then
`P_set_{t+1} = {P_j, P_{p+6}, …, P_n}` satisfies `S_{t+1}` (Graph Minors IX, Section 6, page 58:
"If one of $P_2, \dots, P_{p+5}$ is non-separating (say $P_j$), then we may set
$\mathcal{P}_{t+1}$ to be $\{P_j, P_{p+6}, P_{p+7}, \dots, P_n\}$."). -/
theorem statementSt_succ_of_nonSeparating_member {p t : ℕ} {P_set P_set_t P_set_next : Set
  (Graph α β)}
    {P₁ P_j : Graph α β}
    (ht : t < 2)
    (htrans_t : S.IsTransaction P_set_t)
    (hP₁_in : P₁ ∈ P_set_t)
    (hP₁_per : S.IsPeripheralIn P_set_t P₁)
    (hP₁_sep : S.IsSeparatingOmegaPath P₁)
    (hper_card_t :
      {P ∈ P_set_t | S.IsPeripheralIn P_set_t P ∧ S.IsSeparatingOmegaPath P}.ncard ≤ 2 - t)
    (hsep_mem_t : ∀ P ∈ P_set_t, S.IsSeparatingOmegaPath P → P ∈ P_set)
    (hper_sep_t : ∀ P ∈ P_set_t, S.IsPeripheralIn P_set_t P → S.IsSeparatingOmegaPath P →
      S.IsPeripheralIn P_set P)
    (hsub_next : P_set_next ⊆ P_set_t)
    (hP₁_not_next : P₁ ∉ P_set_next)
    (_hPj_in_next : P_j ∈ P_set_next)
    (hPj_nonsep : S.IsNonSeparatingOmegaPath P_j)
    (htrans_next : S.IsTransaction P_set_next)
    (hcard_next : 3 * p + 8 - (t + 1) * (p + 4) ≤ P_set_next.ncard)
    (hper_next_sub : ∀ R ∈ P_set_next, S.IsPeripheralIn P_set_next R →
      S.IsSeparatingOmegaPath R → R = P_j ∨ S.IsPeripheralIn P_set_t R) :
    S.StatementSt p P_set (t + 1) := by
  have _ := ht
  obtain ⟨_, _, hfence_t⟩ := htrans_t
  have hfin_t : P_set_t.Finite := hfence_t.1.finite S
  have hfin_per_t : {P ∈ P_set_t | S.IsPeripheralIn P_set_t P ∧ S.IsSeparatingOmegaPath P}.Finite :=
    hfin_t.subset fun _ h => h.1
  have hsub_per_sep :
      {P ∈ P_set_next | S.IsPeripheralIn P_set_next P ∧ S.IsSeparatingOmegaPath P} ⊆
        {P ∈ P_set_t | S.IsPeripheralIn P_set_t P ∧ S.IsSeparatingOmegaPath P} \ {P₁} := by
    rintro R ⟨hR_next, hR_per_next, hR_sep⟩
    refine ⟨⟨hsub_next hR_next, ?_, hR_sep⟩, fun h_eq => hP₁_not_next
      (mem_singleton_iff.mp h_eq ▸ hR_next)⟩
    rcases hper_next_sub R hR_next hR_per_next hR_sep with rfl | hR_per_t
    · exact (hR_sep.2 hPj_nonsep.2).elim
    · exact hR_per_t
  have hP₁_mem_per_t :
      P₁ ∈ {P ∈ P_set_t | S.IsPeripheralIn P_set_t P ∧ S.IsSeparatingOmegaPath P} :=
    ⟨hP₁_in, hP₁_per, hP₁_sep⟩
  have hcard_per_next :
      {P ∈ P_set_next | S.IsPeripheralIn P_set_next P ∧ S.IsSeparatingOmegaPath P}.ncard ≤
        2 - (t + 1) := by
    have hle := ncard_le_ncard hsub_per_sep hfin_per_t.sdiff
    have hdiff := ncard_sdiff_singleton_of_mem hP₁_mem_per_t
    omega
  refine ⟨P_set_next, htrans_next, hcard_next, hcard_per_next,
    fun R hR hsep => hsep_mem_t R (hsub_next hR) hsep,
    fun R hR hperR hsepR => ?_⟩
  rcases hper_next_sub R hR hperR hsepR with rfl | hperR_t
  · exact (hsepR.2 hPj_nonsep.2).elim
  · exact hper_sep_t R (hsub_next hR) hperR_t hsepR

/-- In the inductive step `S_t → S_{t+1}`, when `P₁, …, P_{p+5}` are all separating, applying `(9)`
and `(5.5)` produces a non-separating `Ω`-path `P' ≤ G₁` disjoint from `P_{p+6}, …, P_n` such that
`P_set_{t+1} = {P', P_{p+6}, …, P_n}` satisfies `S_{t+1}` (Graph Minors IX, Section 6, page 58:
"By applying (5.5) to the transaction $\{P_1, \dots, P_{p+5}\}$ in $(G, \Omega)$ (which is
possible by (9)) we deduce that there is a non-separating path $P'$ of $(G, \Omega)$ with
$P' \subseteq G_1$. Thus we may set $\mathcal{P}_{t+1} = \{P', P_{p+6}, \dots, P_n\}$ and
$\mathbf{S}_{t+1}$ is true."). -/
theorem statementSt_succ_of_replacement_nonSeparating {p t : ℕ}
    {P_set P_set_t P_rest : Set (Graph α β)} {P₁ P' : Graph α β}
    (_ht : t < 2)
    (htrans_t : S.IsTransaction P_set_t)
    (hP₁_in : P₁ ∈ P_set_t)
    (hP₁_per : S.IsPeripheralIn P_set_t P₁)
    (hP₁_sep : S.IsSeparatingOmegaPath P₁)
    (hper_card_t :
      {P ∈ P_set_t | S.IsPeripheralIn P_set_t P ∧ S.IsSeparatingOmegaPath P}.ncard ≤ 2 - t)
    (hsep_mem_t : ∀ P ∈ P_set_t, S.IsSeparatingOmegaPath P → P ∈ P_set)
    (hper_sep_t : ∀ P ∈ P_set_t, S.IsPeripheralIn P_set_t P → S.IsSeparatingOmegaPath P →
      S.IsPeripheralIn P_set P)
    (hrest_sub : P_rest ⊆ P_set_t \ {P₁})
    (hP'_nonsep : S.IsNonSeparatingOmegaPath P')
    (htrans_next : S.IsTransaction (insert P' P_rest))
    (hcard_next : 3 * p + 8 - (t + 1) * (p + 4) ≤ (insert P' P_rest).ncard)
    (hper_next_sub : ∀ R ∈ insert P' P_rest, S.IsPeripheralIn (insert P' P_rest) R →
      S.IsSeparatingOmegaPath R → R = P' ∨ S.IsPeripheralIn P_set_t R) :
    S.StatementSt p P_set (t + 1) := by
  obtain ⟨_, _, hfence_t⟩ := htrans_t
  have hfin_t : P_set_t.Finite := hfence_t.1.finite S
  have hfin_per_t : {P ∈ P_set_t | S.IsPeripheralIn P_set_t P ∧ S.IsSeparatingOmegaPath P}.Finite :=
    hfin_t.subset fun _ h => h.1
  have hsub_per_sep :
      {P ∈ insert P' P_rest | S.IsPeripheralIn (insert P' P_rest) P ∧ S.IsSeparatingOmegaPath P} ⊆
        {P ∈ P_set_t | S.IsPeripheralIn P_set_t P ∧ S.IsSeparatingOmegaPath P} \ {P₁} := by
    rintro R ⟨hR_in, hR_per_next, hR_sep⟩
    rcases mem_insert_iff.mp hR_in with rfl | hR_rest
    · exact (hR_sep.2 hP'_nonsep.2).elim
    · have hR_diff := hrest_sub hR_rest
      refine ⟨⟨hR_diff.1, ?_, hR_sep⟩, hR_diff.2⟩
      rcases hper_next_sub R hR_in hR_per_next hR_sep with rfl | hR_per_t
      · exact (hR_sep.2 hP'_nonsep.2).elim
      · exact hR_per_t
  have hP₁_mem_per_t :
      P₁ ∈ {P ∈ P_set_t | S.IsPeripheralIn P_set_t P ∧ S.IsSeparatingOmegaPath P} :=
    ⟨hP₁_in, hP₁_per, hP₁_sep⟩
  have hcard_per_next :
      {P ∈ insert P' P_rest |
        S.IsPeripheralIn (insert P' P_rest) P ∧ S.IsSeparatingOmegaPath P}.ncard ≤
        2 - (t + 1) := by
    have hle := ncard_le_ncard hsub_per_sep hfin_per_t.sdiff
    have hdiff := ncard_sdiff_singleton_of_mem hP₁_mem_per_t
    omega
  refine ⟨insert P' P_rest, htrans_next, hcard_next, hcard_per_next,
    fun R hR hsepR => ?_, fun R hR hperR hsepR => ?_⟩
  · rcases mem_insert_iff.mp hR with rfl | hR_rest
    · exact (hsepR.2 hP'_nonsep.2).elim
    · exact hsep_mem_t R (hrest_sub hR_rest).1 hsepR
  · rcases hper_next_sub R hR hperR hsepR with rfl | hperR_t
    · exact (hsepR.2 hP'_nonsep.2).elim
    · rcases mem_insert_iff.mp hR with rfl | hR_rest
      · exact (hsepR.2 hP'_nonsep.2).elim
      · exact hper_sep_t R (hrest_sub hR_rest).1 hperR_t hsepR

/-- Applying `statementSt_succ` twice from `statementSt_zero` yields `S₂`
(Graph Minors IX, Section 6, page 58: "We deduce that `S₂` is true."). -/
theorem statementSt_two {p : ℕ} {P_set : Set (Graph α β)}
    (htrans : S.IsTransaction P_set)
    (hcard : P_set.ncard = 3 * p + 8)
    (hstep : ∀ t < 2, S.StatementSt p P_set t → S.StatementSt p P_set (t + 1)) :
    S.StatementSt p P_set 2 := by
  have h0 : S.StatementSt p P_set 0 := S.statementSt_zero htrans hcard
  have h1 : S.StatementSt p P_set 1 := hstep 0 (by decide) h0
  exact hstep 1 (by decide) h1

/-- From `S₂`, `(4.1)` (`theorem_4_1_proof`), and `(3.4)` (`theorem_3_4_proof`), `(G, Ω)` has a
crooked
transaction of cardinality `p` (Graph Minors IX, Section 6, page 58:
"We deduce that $\mathbf{S}_2$ is true. But every peripheral member of $\mathcal{P}_2$ is
non-separating and $|\mathcal{P}_2| \ge p$, and so $(G, \Omega)$ has a crooked transaction
with cardinality $p$, by (4.1) and (3.4)."). -/
theorem exists_crooked_of_statementSt_two {p : ℕ} {P_set : Set (Graph α β)}
    (hp2 : 2 ≤ p) (hp3 : p ≠ 3)
    (hS₂ : S.StatementSt p P_set 2) :
    ∃ P_set' : Set (Graph α β), S.IsCrookedTransaction P_set' ∧ P_set'.ncard = p := by
  obtain ⟨P_set₂, htrans₂, hcard₂, hper_card₂, _, _⟩ := hS₂
  have hcard₂_ge_p : p ≤ P_set₂.ncard := by omega
  obtain ⟨A, B, hfence₂⟩ := htrans₂
  have hfin₂ : P_set₂.Finite := hfence₂.1.finite S
  have hfin_per_sep :
      {P ∈ P_set₂ | S.IsPeripheralIn P_set₂ P ∧ S.IsSeparatingOmegaPath P}.Finite :=
    hfin₂.subset fun _ h => h.1
  have hper_nonsep : ∀ P ∈ P_set₂, S.IsPeripheralIn P_set₂ P → S.IsNonSeparatingOmegaPath P := by
    intro P hP_in hperP
    have hP_omega : S.IsOmegaPath P := hfence₂.1.1 P hP_in
    by_cases hcross : ∃ P' : Graph α β, S.OmegaPathsCross P' P
    · exact ⟨hP_omega, hcross⟩
    · exfalso
      have hsepP : S.IsSeparatingOmegaPath P := ⟨hP_omega, hcross⟩
      have hpos : 0 < {Q ∈ P_set₂ | S.IsPeripheralIn P_set₂ Q ∧ S.IsSeparatingOmegaPath Q}.ncard :=
        (ncard_pos hfin_per_sep).mpr ⟨P, hP_in, hperP, hsepP⟩
      omega
  obtain ⟨P_set_cr, hcr, hcard_cr⟩ := S.theorem_4_1_proof ⟨A, B, hfence₂⟩ hper_nonsep
  obtain ⟨P_set', _, hcard', hcr'⟩ := S.theorem_3_4_proof hp2 hp3 hcr (hcard₂_ge_p.trans hcard_cr)
  exact ⟨P_set', hcr', hcard'⟩

end Society

end GraphMinor.GM09
