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
import LeanPool.GraphMinor.GM09.Section2d
import LeanPool.GraphMinor.GM09.Section3a
import LeanPool.GraphMinor.GM09.Section3c
import LeanPool.GraphMinor.GM09.Section4a
import LeanPool.GraphMinor.GM09.Section4b
import LeanPool.GraphMinor.GM09.Section4c
import Mathlib.Data.Set.Card

/-!
# Graph Minors IX, Section 5 (Part A): Separations and Crosses (5.1)–(5.2)

This file formalizes (5.1) and (5.2) from Section 5 of
N. Robertson and P. D. Seymour, *Graph Minors. IX. Disjoint crossed paths*,
J. Combin. Theory Ser. B **49** (1990) 40–77 (pages 52–53):
- `(5.1)` (`theorem_5_1`, page 52): if `Q` is a separating `Ω`-path with ends `a, b` and `P_set`
  is a crooked transaction disjoint from `Q` with `V(P_set) ∩ Ω(a, b) ≠ ∅`, then there is a cross
  in `P_set` with all four ends in `Ω(a, b)`.
- `(5.2)` (`theorem_5_2`, pages 52–53): given `{Q₁, …, Q_{p+4}}` separating and in order and a
  separation `(G₁, G₂)` along `Q_{p+4}`, either `(G, Ω)` has a cross disjoint from `G₂` or a
  crooked transaction of cardinality `p` with no end in `Ω(a₁, b₁)`.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM06

universe u v

variable {α : Type u} {β : Type v}

/-! ## Clockwise sequences of indexed endpoint pairs -/

namespace CyclicPerm

variable (Ω : CyclicPerm α)

/-- If `u, v ∈ Ω.interval a b` and `u ≠ v`, then either `Ω.interval u v ⊆ Ω.interval a b` or
`Ω.interval v u ⊆ Ω.interval a b`. -/
theorem interval_subset_interval_or_swap {a b u v : α}
    (hu : u ∈ Ω.interval a b) (hv : v ∈ Ω.interval a b) (huv : u ≠ v) :
    Ω.interval u v ⊆ Ω.interval a b ∨ Ω.interval v u ⊆ Ω.interval a b := by
  have hv' : v ∈ Ω.interval a u ∪ {u} ∪ Ω.interval u b := by
    rw [← Ω.interval_eq_union_of_mem hu]
    exact hv
  rcases hv' with (hv_au | rfl) | hv_ub
  · exact Or.inr ((Ω.interval_subset_interval_right hv_au).trans
      (Ω.interval_subset_interval_left hu))
  · exact (huv rfl).elim
  · exact Or.inl ((Ω.interval_subset_interval_left hv_ub).trans
      (Ω.interval_subset_interval_right hu))

/-- If `(a_m, …, a₁, b₁, …, b_m)` is `Ω`-clockwise (`(List.ofFn a).reverse ++ List.ofFn b`) and
`i < j` in `Fin m`, then `a i, b i ∈ Ω.interval (a j) (b j)`,
`Ω.interval (a i) (b i) ⊆ Ω.interval (a j) (b j)`, and `a j, b j ∈ Ω.interval (b i) (a i)`. -/
theorem mem_intervals_of_isClockwiseSeq_ofFn {m : ℕ} {a b : Fin m → α}
    (hcw : Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b))
    {i j : Fin m} (hij : i < j) :
    a i ∈ Ω.interval (a j) (b j) ∧
      b i ∈ Ω.interval (a j) (b j) ∧
      Ω.interval (a i) (b i) ⊆ Ω.interval (a j) (b j) ∧
      a j ∈ Ω.interval (b i) (a i) ∧
      b j ∈ Ω.interval (b i) (a i) := by
  have hi_lt : i.1 < m := i.2
  have hj_lt : j.1 < m := j.2
  have hij_val : i.1 < j.1 := hij
  let L := (List.ofFn a).reverse ++ List.ofFn b
  have hlen_rev : (List.ofFn a).reverse.length = m := by simp
  have hlen_b : (List.ofFn b).length = m := by simp
  have hlen : L.length = m + m := by
    simp [L, List.length_append]
  have idx_aj_lt : m - 1 - j.1 < L.length := by omega
  have idx_ai_lt : m - 1 - i.1 < L.length := by omega
  have idx_bi_lt : m + i.1 < L.length := by omega
  have idx_bj_lt : m + j.1 < L.length := by omega
  have hL_aj : L[m - 1 - j.1]'idx_aj_lt = a j := by
    rw [List.getElem_append_left (by omega)]
    rw [List.getElem_reverse]
    simp only [List.length_ofFn, List.getElem_ofFn]
    congr 1; ext; dsimp; omega
  have hL_ai : L[m - 1 - i.1]'idx_ai_lt = a i := by
    rw [List.getElem_append_left (by omega)]
    rw [List.getElem_reverse]
    simp only [List.length_ofFn, List.getElem_ofFn]
    congr 1; ext; dsimp; omega
  have hL_bi : L[m + i.1]'idx_bi_lt = b i := by
    rw [List.getElem_append_right (by omega)]
    simp only [hlen_rev, List.getElem_ofFn]
    congr 1; ext; dsimp; omega
  have hL_bj : L[m + j.1]'idx_bj_lt = b j := by
    rw [List.getElem_append_right (by omega)]
    simp only [hlen_rev, List.getElem_ofFn]
    congr 1; ext; dsimp; omega
  have hai_ajbi : a i ∈ Ω.interval (a j) (b i) := by
    have h := Ω.mem_interval_of_lt hcw (i₁ := m - 1 - j.1) (i₂ := m - 1 - i.1) (i₃ := m + i.1)
      (by omega) (by omega) idx_bi_lt
    rwa [hL_aj, hL_ai, hL_bi] at h
  have hbi_ajbj : b i ∈ Ω.interval (a j) (b j) := by
    have h := Ω.mem_interval_of_lt hcw (i₁ := m - 1 - j.1) (i₂ := m + i.1) (i₃ := m + j.1)
      (by omega) (by omega) idx_bj_lt
    rwa [hL_aj, hL_bi, hL_bj] at h
  have hai_ajbj : a i ∈ Ω.interval (a j) (b j) := by
    have h := Ω.mem_interval_of_lt hcw (i₁ := m - 1 - j.1) (i₂ := m - 1 - i.1) (i₃ := m + j.1)
      (by omega) (by omega) idx_bj_lt
    rwa [hL_aj, hL_ai, hL_bj] at h
  have hbi_aibj : b i ∈ Ω.interval (a i) (b j) := by
    have h := Ω.mem_interval_of_lt hcw (i₁ := m - 1 - i.1) (i₂ := m + i.1) (i₃ := m + j.1)
      (by omega) (by omega) idx_bj_lt
    rwa [hL_ai, hL_bi, hL_bj] at h
  have hsub : Ω.interval (a i) (b i) ⊆ Ω.interval (a j) (b j) :=
    (Ω.interval_subset_interval_left hbi_aibj).trans
      (Ω.interval_subset_interval_right hai_ajbj)
  have haj_biai : a j ∈ Ω.interval (b i) (a i) :=
    Ω.mem_interval_rotate_right hai_ajbi
  have hbj_biai : b j ∈ Ω.interval (b i) (a i) :=
    Ω.mem_interval_rotate_left hbi_aibj
  exact ⟨hai_ajbj, hbi_ajbj, hsub, haj_biai, hbj_biai⟩

end CyclicPerm

/-! ## Proof of (5.1) (page 52) -/

namespace Society

variable (S : Society α β)

/-- If `Q` is a separating `Ω`-path with ends `a, b` and `P` is an `Ω`-path disjoint from `Q` with
an end `s ∈ Ω(a, b)`, then both ends of `P` lie in `Ω(a, b)`. -/
theorem both_ends_mem_interval_of_separating {Q P : Graph α β} {a b s t : α}
    (hQ_ends : S.IsOmegaPathWithEnds Q a b)
    (hQ_sep : S.IsSeparatingOmegaPath Q)
    (hP_ends : S.IsOmegaPathWithEnds P s t)
    (hdisj : Disjoint V(P) V(Q))
    (hs_in : s ∈ S.Ω.interval a b) :
    t ∈ S.Ω.interval a b := by
  have hab : a ≠ b := (S.Ω.isClockwise3_iff.mp hs_in.2).2.1
  have ht_ne_a : t ≠ a := fun h =>
    disjoint_left.mp hdisj hP_ends.1.right_mem (h ▸ hQ_ends.1.left_mem)
  have ht_ne_b : t ≠ b := fun h =>
    disjoint_left.mp hdisj hP_ends.1.right_mem (h ▸ hQ_ends.1.right_mem)
  rcases S.Ω.mem_interval_or_interval_swap hQ_ends.2.2.1 hQ_ends.2.2.2
    hP_ends.2.2.2 hab ht_ne_a ht_ne_b with ht_ab | ht_ba
  · exact ht_ab
  · exfalso
    have hcr_ends : S.Ω.Crosses a b s t :=
      S.Ω.crosses_iff_interval.mpr (Or.inl ⟨hs_in, ht_ba⟩)
    exact hQ_sep.2 ⟨P, hdisj, s, t, a, b, hP_ends, hQ_ends, hcr_ends.symm⟩

/-- **Graph Minors IX, (5.1)** (page 52):
"Let $Q$ be a separating $\Omega$-path in $(G, \Omega)$ with ends $a, b$. If $\mathcal{P}$ is
a crooked transaction in $(G, \Omega)$ with $Q \cap \bigcup \mathcal{P}$ null and with
$V(\mathcal{P}) \cap \Omega(a, b) \ne \emptyset$ then there is a cross $\mathcal{P}'
\subseteq \mathcal{P}$ with all four ends in $\Omega(a, b)$." -/
theorem theorem_5_1_proof {Q : Graph α β} {a b : α} {P_set : Set (Graph α β)}
    (hQ_ends : S.IsOmegaPathWithEnds Q a b)
    (hQ_sep : S.IsSeparatingOmegaPath Q)
    (hcrooked : S.IsCrookedTransaction P_set)
    (hdisj : Disjoint V(Q) V(S.transactionUnion P_set))
    (hne : (S.transactionEnds P_set ∩ S.Ω.interval a b).Nonempty) :
    ∃ P₁ ∈ P_set, ∃ P₂ ∈ P_set,
      S.OmegaPathsCross P₁ P₂ ∧
      pathEnds S.G P₁ ⊆ S.Ω.interval a b ∧
      pathEnds S.G P₂ ⊆ S.Ω.interval a b := by
  obtain ⟨A, B, hfence⟩ := hcrooked.1
  -- Every `R ∈ P_set` with an end in `Ω(a, b)` has ends `s, t ∈ Ω(a, b)` with `Ω(s, t) ⊆ Ω(a, b)`.
  have hex_good : ∀ R ∈ P_set, (pathEnds S.G R ∩ S.Ω.interval a b).Nonempty →
      ∃ s t : α, S.IsOmegaPathWithEnds R s t ∧
        s ∈ S.Ω.interval a b ∧ t ∈ S.Ω.interval a b ∧
        S.Ω.interval s t ⊆ S.Ω.interval a b := by
    intro R hR ⟨x, hx_end, hx_ab⟩
    obtain ⟨u, huA, v, hvB, hR_uv⟩ := hfence.2.2 R hR
    have huv_ne : u ≠ v := fun h => disjoint_left.mp hfence.2.1.2.2.1 huA (h ▸ hvB)
    have hdisj_RQ : Disjoint V(R) V(Q) := by
      rw [disjoint_left]
      intro z hzR hzQ
      exact disjoint_left.mp hdisj hzQ (mem_iUnion₂.mpr ⟨R, hR, hzR⟩)
    rw [hR_uv.1.pathEnds_eq, mem_insert_iff, mem_singleton_iff] at hx_end
    have hu_ab : u ∈ S.Ω.interval a b := by
      rcases hx_end with rfl | rfl
      · exact hx_ab
      · exact S.both_ends_mem_interval_of_separating hQ_ends hQ_sep (hR_uv.symm S) hdisj_RQ hx_ab
    have hv_ab : v ∈ S.Ω.interval a b :=
      S.both_ends_mem_interval_of_separating hQ_ends hQ_sep hR_uv hdisj_RQ hu_ab
    rcases S.Ω.interval_subset_interval_or_swap hu_ab hv_ab huv_ne with hsub_uv | hsub_vu
    · exact ⟨u, v, hR_uv, hu_ab, hv_ab, hsub_uv⟩
    · exact ⟨v, u, hR_uv.symm S, hv_ab, hu_ab, hsub_vu⟩
  -- Existence of a candidate `P ∈ P_set` with `Ω(s, t) ⊆ Ω(a, b)`.
  have hex_cand : ∃ n : ℕ, ∃ P ∈ P_set, ∃ s t : α,
      S.IsOmegaPathWithEnds P s t ∧
      s ∈ S.Ω.interval a b ∧ t ∈ S.Ω.interval a b ∧
      S.Ω.interval s t ⊆ S.Ω.interval a b ∧
      (S.Ω.interval s t).ncard = n := by
    rcases hne with ⟨x, ⟨P₀, hP₀, y₀, hP₀_xy⟩, hx_ab⟩
    have hx_end : x ∈ pathEnds S.G P₀ := by
      rw [hP₀_xy.1.pathEnds_eq]
      exact Or.inl rfl
    obtain ⟨s₀, t₀, hP₀_st, hs₀, ht₀, hsub₀⟩ := hex_good P₀ hP₀ ⟨x, hx_end, hx_ab⟩
    exact ⟨(S.Ω.interval s₀ t₀).ncard, P₀, hP₀, s₀, t₀, hP₀_st, hs₀, ht₀, hsub₀, rfl⟩
  classical
  let n_min := Nat.find hex_cand
  obtain ⟨P, hP_in, s, t, hP_ends, hs_ab, ht_ab, hsub_st, hcard_st⟩ := Nat.find_spec hex_cand
  have hmin_st : ∀ P' ∈ P_set, ∀ s' t' : α,
      S.IsOmegaPathWithEnds P' s' t' →
      s' ∈ S.Ω.interval a b → t' ∈ S.Ω.interval a b →
      S.Ω.interval s' t' ⊆ S.Ω.interval a b →
      n_min ≤ (S.Ω.interval s' t').ncard := by
    intro P' hP' s' t' hP'_st hs' ht' hsub'
    exact Nat.find_min' hex_cand ⟨P', hP', s', t', hP'_st, hs', ht', hsub', rfl⟩
  -- Since `P_set` is crooked, `P` is not peripheral in `P_set`.
  have hnot_periph : ¬ S.IsPeripheralIn P_set P := hcrooked.2 P hP_in
  have hhit_st : (S.Ω.interval s t ∩ S.transactionEnds P_set).Nonempty := by
    by_contra h_empty
    rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at h_empty
    exact hnot_periph ⟨hP_in, s, t, hP_ends, Or.inl h_empty⟩
  rcases hhit_st with ⟨x', hx'_st, P', hP'_in, y', hP'_ends⟩
  have hP'_ne_P : P' ≠ P := by
    rintro rfl
    rcases hP_ends.ends_eq S hP'_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hx'_st.1.2 (Or.inl rfl)
    · exact hx'_st.1.2 (Or.inr rfl)
  have hdisj_PP' : Disjoint V(P) V(P') := hfence.1.2 hP_in hP'_in hP'_ne_P.symm
  -- Find the other end `y'` of `P'`.
  have hdisj_P'Q : Disjoint V(P') V(Q) := by
    rw [disjoint_left]
    intro z hzP' hzQ
    exact disjoint_left.mp hdisj hzQ (mem_iUnion₂.mpr ⟨P', hP'_in, hzP'⟩)
  have hx'_ab : x' ∈ S.Ω.interval a b := hsub_st hx'_st
  have hy'_ab : y' ∈ S.Ω.interval a b :=
    S.both_ends_mem_interval_of_separating hQ_ends hQ_sep hP'_ends hdisj_P'Q hx'_ab
  have hx'y'_ne : x' ≠ y' := hP'_ends.2.1
  -- `y' ∉ Ω(s, t)` by minimality of `(Ω(s, t)).ncard`.
  have hy'_not_st : y' ∉ S.Ω.interval s t := by
    intro hy'_st
    have hfin_st : (S.Ω.interval s t).Finite := S.Ω.finite_bar.subset (S.Ω.interval_subset_bar s t)
    rcases S.Ω.interval_subset_interval_or_swap hx'_st hy'_st hx'y'_ne with hsub' | hsub'
    · have hlt : (S.Ω.interval x' y').ncard < (S.Ω.interval s t).ncard :=
        ncard_lt_ncard ⟨hsub', fun h_all => (h_all hy'_st).1.2 (Or.inr rfl)⟩ hfin_st
      have hge := hmin_st P' hP'_in x' y' hP'_ends hx'_ab hy'_ab (hsub'.trans hsub_st)
      omega
    · have hlt : (S.Ω.interval y' x').ncard < (S.Ω.interval s t).ncard :=
        ncard_lt_ncard ⟨hsub', fun h_all => (h_all hx'_st).1.2 (Or.inr rfl)⟩ hfin_st
      have hge := hmin_st P' hP'_in y' x' (hP'_ends.symm S) hy'_ab hx'_ab (hsub'.trans hsub_st)
      omega
  have hst_ne : s ≠ t := by
    obtain ⟨u₀, hu₀A, v₀, hv₀B, hP_uv₀⟩ := hfence.2.2 P hP_in
    have huv₀_ne : u₀ ≠ v₀ := fun h => disjoint_left.mp hfence.2.1.2.2.1 hu₀A (h ▸ hv₀B)
    rcases hP_ends.ends_eq S hP_uv₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact huv₀_ne
    · exact huv₀_ne.symm
  have hy'_ne_s : y' ≠ s := fun h =>
    disjoint_left.mp hdisj_PP' (h ▸ hP_ends.1.left_mem) hP'_ends.1.right_mem
  have hy'_ne_t : y' ≠ t := fun h =>
    disjoint_left.mp hdisj_PP' (h ▸ hP_ends.1.right_mem) hP'_ends.1.right_mem
  have hy'_ts : y' ∈ S.Ω.interval t s := by
    rcases S.Ω.mem_interval_or_interval_swap hP_ends.2.2.1 hP_ends.2.2.2
      hP'_ends.2.2.2 hst_ne hy'_ne_s hy'_ne_t with h_st | h_ts
    · exact (hy'_not_st h_st).elim
    · exact h_ts
  have hcr_PP' : S.OmegaPathsCross P P' := by
    refine ⟨hdisj_PP', s, t, x', y', hP_ends, hP'_ends, ?_⟩
    exact S.Ω.crosses_iff_interval.mpr (Or.inl ⟨hx'_st, hy'_ts⟩)
  refine ⟨P, hP_in, P', hP'_in, hcr_PP', ?_, ?_⟩
  · rw [hP_ends.1.pathEnds_eq]
    rintro z (rfl | rfl)
    · exact hs_ab
    · exact ht_ab
  · rw [hP'_ends.1.pathEnds_eq]
    rintro z (rfl | rfl)
    · exact hx'_ab
    · exact hy'_ab

/-! ## Proof of (5.2) (pages 52–53) -/

/-- For a finite graph `S.G`, if `Q_set` is a transaction in `S` with no internal vertex in `ΩBar`
and `S` has a crooked transaction `P₀` with `p ≤ P₀.ncard` (`2 ≤ p`), then there exist a crooked
transaction `P_set` and a fence `(A, B)` satisfying `S.StatementS p P_set Q_set A B`. -/
theorem exists_statementS [Finite V(S.G)] [Finite E(S.G)] {p : ℕ} (hp2 : 2 ≤ p)
    {Q_set : Set (Graph α β)} (htr_Q : S.IsTransaction Q_set)
    (hno_int : ∀ Q ∈ Q_set, Disjoint (pathInternalVerts S.G Q) S.Ω.bar)
    (hex_cr : ∃ P₀ : Set (Graph α β), S.IsCrookedTransaction P₀ ∧ p ≤ P₀.ncard) :
    ∃ (P_set : Set (Graph α β)) (A B : Set α), S.StatementS p P_set Q_set A B := by
  let unionGraph (P_set : Set (Graph α β)) : Graph α β :=
    subgraphUnion S.G (S.transactionUnion P_set) (S.transactionUnion Q_set)
  let unionSize (P_set : Set (Graph α β)) : ℕ :=
    (V(unionGraph P_set)).ncard + (E(unionGraph P_set)).ncard
  have hex_u : ∃ u : ℕ, ∃ P_set : Set (Graph α β),
      S.IsCrookedTransaction P_set ∧ p ≤ P_set.ncard ∧ unionSize P_set = u := by
    rcases hex_cr with ⟨P₀, hcr₀, hp₀⟩
    exact ⟨unionSize P₀, P₀, hcr₀, hp₀, rfl⟩
  classical
  let u_min := Nat.find hex_u
  have hex_c : ∃ c : ℕ, ∃ P_set : Set (Graph α β),
      S.IsCrookedTransaction P_set ∧ p ≤ P_set.ncard ∧
      unionSize P_set = u_min ∧ P_set.ncard = c := by
    obtain ⟨P₁, hcr₁, hp₁, hu₁⟩ := Nat.find_spec hex_u
    exact ⟨P₁.ncard, P₁, hcr₁, hp₁, hu₁, rfl⟩
  let c_min := Nat.find hex_c
  obtain ⟨P_set, hcr_P, hp_P, hu_P, hc_P⟩ := Nat.find_spec hex_c
  obtain ⟨A, B, hfence_P⟩ := hcr_P.1
  have hQ_le : ∀ M ∈ Q_set, M ≤ S.G := by
    obtain ⟨_, _, hfQ⟩ := htr_Q
    exact fun M hM => let ⟨_, _, h⟩ := hfQ.1.1 M hM; h.1.1
  have hUQ_le : S.transactionUnion Q_set ≤ S.G := subgraphSUnion_le hQ_le
  have hVG_fin : V(S.G).Finite := toFinite V(S.G)
  have hEG_fin : E(S.G).Finite := toFinite E(S.G)
  refine ⟨P_set, A, B, hp2, htr_Q, hno_int, hcr_P, hp_P, ?_, ?_, hfence_P⟩
  · intro P_set' hcr' hp' hle
    have hP_le : ∀ M ∈ P_set, M ≤ S.G :=
      fun M hM => let ⟨_, _, h⟩ := hfence_P.1.1 M hM; h.1.1
    have hP'_le : ∀ M ∈ P_set', M ≤ S.G := by
      obtain ⟨_, _, hfP'⟩ := hcr'.1
      exact fun M hM => let ⟨_, _, h⟩ := hfP'.1.1 M hM; h.1.1
    have hU_le : unionGraph P_set ≤ S.G := subgraphUnion_le (subgraphSUnion_le hP_le) hUQ_le
    have hU'_le : unionGraph P_set' ≤ S.G := subgraphUnion_le (subgraphSUnion_le hP'_le) hUQ_le
    have hV_sub : V(unionGraph P_set') ⊆ V(unionGraph P_set) := hle.vertexSet_mono
    have hE_sub : E(unionGraph P_set') ⊆ E(unionGraph P_set) := hle.edgeSet_mono
    have hV_fin : (V(unionGraph P_set)).Finite := hVG_fin.subset hU_le.vertexSet_mono
    have hE_fin : (E(unionGraph P_set)).Finite := hEG_fin.subset hU_le.edgeSet_mono
    have hV_le : (V(unionGraph P_set')).ncard ≤ (V(unionGraph P_set)).ncard :=
      ncard_le_ncard hV_sub hV_fin
    have hE_le : (E(unionGraph P_set')).ncard ≤ (E(unionGraph P_set)).ncard :=
      ncard_le_ncard hE_sub hE_fin
    have hu_ge : u_min ≤ unionSize P_set' :=
      Nat.find_min' hex_u ⟨P_set', hcr', hp', rfl⟩
    have hV_eq : V(unionGraph P_set') = V(unionGraph P_set) :=
      eq_of_subset_of_ncard_le hV_sub (by dsimp [unionSize] at hu_P hu_ge; omega) hV_fin
    have hE_eq : E(unionGraph P_set') = E(unionGraph P_set) :=
      eq_of_subset_of_ncard_le hE_sub (by dsimp [unionSize] at hu_P hu_ge; omega) hE_fin
    exact (Compatible.of_le_le hU'_le hU_le).ext hV_eq hE_eq
  · intro P_set' hcr' hp' heq
    have hu' : unionSize P_set' = u_min := by
      have h_eq_graph : unionGraph P_set' = unionGraph P_set := heq
      dsimp [unionSize] at hu_P ⊢
      rw [h_eq_graph]
      exact hu_P
    have hc_ge : c_min ≤ P_set'.ncard :=
      Nat.find_min' hex_c ⟨P_set', hcr', hp', hu', rfl⟩
    omega

/-- In a separation `(G₁, G₂)` of `S.G` with `V(G₁) ∩ V(G₂) = V(Q_m)` and
`Ω(a_m, b_m) ⊆ V(G₁)`, if `Q_j` is a separating `Ω`-path with `Ω(a_j, b_j) ⊆ Ω(a_m, b_m)` and
`a_m, b_m ∈ Ω(b_j, a_j)` (or `Q_j = Q_m`), then any `Ω`-path `P` disjoint from `Q_j` with
`pathEnds S.G P ⊆ Ω(a_j, b_j)` satisfies `Disjoint V(P) V(G₂)`. -/
theorem disjoint_right_of_ends_in_interval_of_separating
    {Q_j Q_m P G₁ G₂ : Graph α β} {a_j b_j a_m b_m : α}
    (hQj_ends : S.IsOmegaPathWithEnds Q_j a_j b_j)
    (hQj_sep : S.IsSeparatingOmegaPath Q_j)
    (hQm_ends : S.IsOmegaPathWithEnds Q_m a_m b_m)
    (hQm_no_int : Disjoint (pathInternalVerts S.G Q_m) S.Ω.bar)
    (hsub_jm : S.Ω.interval a_j b_j ⊆ S.Ω.interval a_m b_m)
    (hjm : Q_j = Q_m ∨
      (Disjoint V(Q_j) V(Q_m) ∧ a_m ∈ S.Ω.interval b_j a_j ∧ b_m ∈ S.Ω.interval b_j a_j))
    (hsep_G : IsGraphSeparation S.G G₁ G₂)
    (hinter_G : V(G₁) ∩ V(G₂) = V(Q_m))
    (hint_G₁ : S.Ω.interval a_m b_m ⊆ V(G₁))
    {s t : α} (hP_ends : S.IsOmegaPathWithEnds P s t)
    (hdisj_PQj : Disjoint V(P) V(Q_j))
    (hs_ajbj : s ∈ S.Ω.interval a_j b_j)
    (ht_ajbj : t ∈ S.Ω.interval a_j b_j) :
    Disjoint V(P) V(G₂) := by
  by_contra hnot_disj
  rw [not_disjoint_iff_nonempty_inter] at hnot_disj
  -- First show `(V(P) ∩ V(Q_m)).Nonempty` because `s ∈ V(G₁)` and `P` is a path meeting `V(G₂)`.
  have hs_G₁ : s ∈ V(G₁) := hint_G₁ (hsub_jm hs_ajbj)
  have hmeet_P_Qm : (V(P) ∩ V(Q_m)).Nonempty := by
    rw [← hinter_G]
    rcases hnot_disj with ⟨z, hzP, hzG₂⟩
    obtain ⟨R_sz, hRsz_le, _, hRsz_G⟩ := hP_ends.1.exists_subpath hP_ends.1.left_mem hzP
    obtain ⟨w, hw_Rsz, hw_inter⟩ := exists_mem_inter_of_isGraphPathWithEnds hsep_G hRsz_G hs_G₁ hzG₂
    exact ⟨w, hRsz_le.vertexSet_mono hw_Rsz, hw_inter⟩
  -- Now `Q_j ≠ Q_m` since `Disjoint V(P) V(Q_j)`.
  rcases hjm with rfl | ⟨hdisj_QjQm, ham_bjaj, hbm_bjaj⟩
  · exact disjoint_left.mp hdisj_PQj hmeet_P_Qm.some_mem.1 hmeet_P_Qm.some_mem.2
  · rcases hmeet_P_Qm with ⟨w₀, hw₀_P, hw₀_Qm⟩
    -- Take subpath of `P` from `s` to `w₀`, then extract `{s, t} → V(Q_m)` path `R₁ ≤ P`.
    obtain ⟨R_sw, hRsw_le, _, hRsw_G⟩ := hP_ends.1.exists_subpath hP_ends.1.left_mem hw₀_P
    obtain ⟨x_s, hx_s_in, x, hx_Qm, R₁, hR₁_Rsw, hR₁_ft⟩ :=
      hRsw_G.exists_isFromToPathWithEnds (X := {s, t}) (Y := V(Q_m)) (Or.inl rfl) hw₀_Qm
    have hR₁_le : R₁ ≤ P := hR₁_Rsw.trans hRsw_le
    -- Take subpath of `Q_m` from `x` to `a_m`.
    obtain ⟨R₂, hR₂_le, _, hR₂_G⟩ := hQm_ends.1.exists_subpath hx_Qm hQm_ends.1.left_mem
    have hinter_R₁R₂ : V(R₁) ∩ V(R₂) = {x} := by
      apply Subset.antisymm
      · intro z ⟨hz₁, hz₂⟩
        have hz_in : z ∈ V(R₁) ∩ V(Q_m) := ⟨hz₁, hR₂_le.vertexSet_mono hz₂⟩
        rwa [hR₁_ft.2.2] at hz_in
      · rintro z rfl
        exact ⟨hR₁_ft.1.right_mem, hR₂_G.left_mem⟩
    let P' := subgraphUnion S.G R₁ R₂
    have hP'_G : IsGraphPathWithEnds S.G P' x_s a_m :=
      hR₁_ft.1.subgraphUnion hR₂_G hinter_R₁R₂
    have hx_s_ajbj : x_s ∈ S.Ω.interval a_j b_j := by
      rcases hx_s_in with rfl | rfl
      · exact hs_ajbj
      · exact ht_ajbj
    have hx_s_ne_am : x_s ≠ a_m := fun h =>
      disjoint_left.mp (S.Ω.disjoint_interval_swap a_j b_j) hx_s_ajbj (h ▸ ham_bjaj)
    have hP'_omega : S.IsOmegaPathWithEnds P' x_s a_m :=
      ⟨hP'_G, hx_s_ne_am, S.Ω.interval_subset_bar a_j b_j hx_s_ajbj,
        S.Ω.interval_subset_bar b_j a_j ham_bjaj⟩
    have hdisj_P'Qj : Disjoint V(P') V(Q_j) := by
      rw [disjoint_left]
      intro z hzP' hzQj
      rw [vertexSet_subgraphUnion] at hzP'
      rcases hzP' with hzR₁ | hzR₂
      · exact disjoint_left.mp hdisj_PQj (hR₁_le.vertexSet_mono hzR₁) hzQj
      · exact disjoint_left.mp hdisj_QjQm.symm (hR₂_le.vertexSet_mono hzR₂) hzQj
    have hcr_P'Qj : S.OmegaPathsCross P' Q_j :=
      ⟨hdisj_P'Qj, x_s, a_m, a_j, b_j, hP'_omega, hQj_ends,
        (S.Ω.crosses_iff_interval.mpr (Or.inl ⟨hx_s_ajbj, ham_bjaj⟩)).symm⟩
    exact hQj_sep.2 ⟨P', hcr_P'Qj⟩

/-- **Graph Minors IX, (5.2)** (pages 52–53):
"Let $(G, \Omega)$ have a crooked transaction with cardinality $p \ge 2$ and $p \ne 3$. Let
$\{Q_1, \dots, Q_{p+4}\}$ be a transaction in $(G, \Omega)$ such that for $1 \le i \le p+4$,
$Q_i$ is separating, and has no internal vertex in $\bar{\Omega}$, and has ends $a_i, b_i$,
where $(a_{p+4}, a_{p+3}, \dots, a_1, b_1, b_2, \dots, b_{p+4})$ is clockwise. Let $(G_1,
G_2)$ be a separation of $G$ with $V(G_1 \cap G_2) = V(Q_{p+4})$, $\Omega(a_{p+4}, b_{p+4})
\subseteq V(G_1)$ and $\Omega(b_{p+4}, a_{p+4}) \subseteq V(G_2)$. Then either* (i) *there
is a cross $\{P_1, P_2\}$ of $(G, \Omega)$ with $P_1 \cap G_2$ and $P_2 \cap G_2$ both null,
or* (ii) *there is a crooked transaction $\mathcal{P}$ in $(G, \Omega)$ with cardinality $p$
and with $\Omega(a_1, b_1) \cap V(\mathcal{P}) = \emptyset$." -/
theorem theorem_5_2_proof [Finite V(S.G)] [Finite E(S.G)] {p : ℕ} (hp2 : 2 ≤ p) (hp3 : p ≠ 3)
    (hex_cr : ∃ P₀ : Set (Graph α β), S.IsCrookedTransaction P₀ ∧ p ≤ P₀.ncard)
    {Q : Fin (p + 4) → Graph α β} {a b : Fin (p + 4) → α}
    (hinj_Q : Function.Injective Q)
    (htr_Q : S.IsTransaction (range Q))
    (hsep_Q : ∀ i : Fin (p + 4), S.IsSeparatingOmegaPath (Q i))
    (hno_int : ∀ i : Fin (p + 4), Disjoint (pathInternalVerts S.G (Q i)) S.Ω.bar)
    (hends_Q : ∀ i : Fin (p + 4), S.IsOmegaPathWithEnds (Q i) (a i) (b i))
    (hcw : S.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b))
    {G₁ G₂ : Graph α β} (hsep_G : IsGraphSeparation S.G G₁ G₂)
    (hinter_G : V(G₁) ∩ V(G₂) = V(Q ⟨p + 3, by omega⟩))
    (hint_G₁ : S.Ω.interval (a ⟨p + 3, by omega⟩) (b ⟨p + 3, by omega⟩) ⊆ V(G₁))
    (_hint_G₂ : S.Ω.interval (b ⟨p + 3, by omega⟩) (a ⟨p + 3, by omega⟩) ⊆ V(G₂)) :
    (∃ P₁ P₂ : Graph α β, S.OmegaPathsCross P₁ P₂ ∧
      Disjoint V(P₁) V(G₂) ∧ Disjoint V(P₂) V(G₂)) ∨
    (∃ P_set : Set (Graph α β), S.IsCrookedTransaction P_set ∧ P_set.ncard = p ∧
      Disjoint (S.Ω.interval (a ⟨0, by omega⟩) (b ⟨0, by omega⟩)) (S.transactionEnds P_set)) := by
  let Q_set : Set (Graph α β) := range Q
  have hno_int_Q : ∀ R ∈ Q_set, Disjoint (pathInternalVerts S.G R) S.Ω.bar := by
    rintro _ ⟨i, rfl⟩
    exact hno_int i
  have hsep_Q_set : ∀ R ∈ Q_set, S.IsSeparatingOmegaPath R := by
    rintro _ ⟨i, rfl⟩
    exact hsep_Q i
  have hcard_Q : Q_set.ncard = p + 4 := by
    dsimp [Q_set]
    rw [ncard_range_of_injective hinj_Q, Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨P_set, A, B, hS⟩ := S.exists_statementS hp2 htr_Q hno_int_Q hex_cr
  have hcard_P : P_set.ncard = p := hS.card_P_eq S hp3
  by_cases hdisj_0 :
      Disjoint (S.Ω.interval (a ⟨0, by omega⟩) (b ⟨0, by omega⟩)) (S.transactionEnds P_set)
  · exact Or.inr ⟨P_set, hS.isCrooked_P, hcard_P, hdisj_0⟩
  · left
    -- By (4.6), some `Q j ∈ Q_set` is vertex-disjoint from `⋃ P_set`.
    obtain ⟨_, ⟨j, rfl⟩, hdisj_Qj⟩ := S.theorem_4_6_proof hS hp3 hcard_Q hsep_Q_set
    let i₀ : Fin (p + 4) := ⟨0, by omega⟩
    let i_last : Fin (p + 4) := ⟨p + 3, by omega⟩
    have hj_le_last : j ≤ i_last := by
      change j.1 ≤ p + 3
      have := j.2
      omega
    have hsub_0j : S.Ω.interval (a i₀) (b i₀) ⊆ S.Ω.interval (a j) (b j) := by
      rcases eq_or_lt_of_le (Fin.zero_le j) with rfl | hlt
      · exact Subset.rfl
      · exact (S.Ω.mem_intervals_of_isClockwiseSeq_ofFn hcw hlt).2.2.1
    have hne_j : (S.transactionEnds P_set ∩ S.Ω.interval (a j) (b j)).Nonempty := by
      rw [not_disjoint_iff_nonempty_inter] at hdisj_0
      rcases hdisj_0 with ⟨x, hx0, hxP⟩
      exact ⟨x, hxP, hsub_0j hx0⟩
    -- By (5.1), there is a cross `P₁, P₂ ∈ P_set` with all four ends in `Ω(a_j, b_j)`.
    obtain ⟨P₁, hP₁_in, P₂, hP₂_in, hcr_12, hends₁_j, hends₂_j⟩ :=
      S.theorem_5_1_proof (hends_Q j) (hsep_Q j) hS.isCrooked_P hdisj_Qj hne_j
    -- Both `P₁` and `P₂` are disjoint from `V(G₂)`.
    have hsub_j_last : S.Ω.interval (a j) (b j) ⊆ S.Ω.interval (a i_last) (b i_last) := by
      rcases eq_or_lt_of_le hj_le_last with rfl | hlt
      · exact Subset.rfl
      · exact (S.Ω.mem_intervals_of_isClockwiseSeq_ofFn hcw hlt).2.2.1
    have hj_last : Q j = Q i_last ∨
        (Disjoint V(Q j) V(Q i_last) ∧
          a i_last ∈ S.Ω.interval (b j) (a j) ∧ b i_last ∈ S.Ω.interval (b j) (a j)) := by
      rcases eq_or_lt_of_le hj_le_last with rfl | hlt
      · exact Or.inl rfl
      · right
        obtain ⟨_, _, hfence_Q⟩ := htr_Q
        have hne_Q : Q j ≠ Q i_last := fun h => (ne_of_lt hlt) (hinj_Q h)
        have hdisj_jm : Disjoint V(Q j) V(Q i_last) :=
          hfence_Q.1.2 (mem_range_self j) (mem_range_self i_last) hne_Q
        have hint_jm := S.Ω.mem_intervals_of_isClockwiseSeq_ofFn hcw hlt
        exact ⟨hdisj_jm, hint_jm.2.2.2.1, hint_jm.2.2.2.2⟩
    have hdisj_P_G₂ : ∀ P ∈ P_set, pathEnds S.G P ⊆ S.Ω.interval (a j) (b j) →
        Disjoint V(P) V(G₂) := by
      intro P hP_in hends_P
      obtain ⟨s, t, hP_ends⟩ := hS.isFenceFor_P.1.1 P hP_in
      have hs_j : s ∈ S.Ω.interval (a j) (b j) := by
        apply hends_P
        rw [hP_ends.1.pathEnds_eq]
        exact Or.inl rfl
      have ht_j : t ∈ S.Ω.interval (a j) (b j) := by
        apply hends_P
        rw [hP_ends.1.pathEnds_eq]
        exact Or.inr rfl
      have hdisj_PQj : Disjoint V(P) V(Q j) := by
        rw [disjoint_left]
        intro z hzP hzQj
        exact disjoint_left.mp hdisj_Qj hzQj (mem_iUnion₂.mpr ⟨P, hP_in, hzP⟩)
      exact S.disjoint_right_of_ends_in_interval_of_separating
        (hends_Q j) (hsep_Q j) (hends_Q i_last) (hno_int i_last)
        hsub_j_last hj_last hsep_G hinter_G hint_G₁ hP_ends hdisj_PQj hs_j ht_j
    exact ⟨P₁, P₂, hcr_12, hdisj_P_G₂ P₁ hP₁_in hends₁_j, hdisj_P_G₂ P₂ hP₂_in hends₂_j⟩

end Society

export Society (theorem_5_1_proof theorem_5_2_proof)

end GraphMinor.GM09
