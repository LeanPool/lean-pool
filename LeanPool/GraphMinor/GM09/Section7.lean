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
import LeanPool.GraphMinor.GM09.Section3a
import LeanPool.GraphMinor.GM09.Section3c
import LeanPool.GraphMinor.GM09.Section4a
import LeanPool.GraphMinor.GM09.Section4b
import Mathlib.Data.Set.Card

/-!
# Graph Minors IX, Section 7: Some Special Transactions and (7.1)

This file formalizes Section 7 of N. Robertson and P. D. Seymour,
*Graph Minors. IX. Disjoint crossed paths*, J. Combin. Theory Ser. B **49** (1990) 40–77
(pages 58–60), proving (7.1) (`theorem_7_1`): every sufficiently large crooked transaction contains
a crosscap of size `r`, a leap of size `s`, or a doublecross of size `t`.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Graph GraphMinor

universe u v

variable {α : Type u} {β : Type v}

/-! ## Clockwise Subsequences and Cyclic Rotations -/

namespace CyclicPerm

variable {Ω : CyclicPerm α}

/-- `M` is a subsequence of `L` realized by strictly increasing indices in `[lo, hi)`. -/
def IsBoundedSubseq (L M : List α) (lo hi : ℕ) : Prop :=
  lo ≤ hi ∧ ∃ pos : ℕ → ℕ,
    (∀ (i : ℕ) (hi_M : i < M.length),
      ∃ hlt : pos i < L.length, lo ≤ pos i ∧ pos i < hi ∧ M[i]'hi_M = L[pos i]'hlt) ∧
    (∀ i j, i < j → j < M.length → pos i < pos j)

theorem IsBoundedSubseq.singleton (L : List α) {p lo hi : ℕ} (hp : p < L.length)
    (hlo : lo ≤ p) (hhi : p < hi) :
    IsBoundedSubseq L [L[p]'hp] lo hi := by
  refine ⟨by omega, fun _ => p, fun i hi_M => ?_, fun i j hij hj => by simp at hj; omega⟩
  simp only [List.length_singleton] at hi_M
  have hi0 : i = 0 := by omega
  subst hi0
  exact ⟨hp, hlo, hhi, rfl⟩

theorem IsBoundedSubseq.append {L M₁ M₂ : List α} {lo mid hi : ℕ}
    (h₁ : IsBoundedSubseq L M₁ lo mid) (h₂ : IsBoundedSubseq L M₂ mid hi) :
    IsBoundedSubseq L (M₁ ++ M₂) lo hi := by
  rcases h₁ with ⟨hle₁, pos₁, hspec₁, hmono₁⟩
  rcases h₂ with ⟨hle₂, pos₂, hspec₂, hmono₂⟩
  let pos (i : ℕ) : ℕ := if i < M₁.length then pos₁ i else pos₂ (i - M₁.length)
  refine ⟨le_trans hle₁ hle₂, pos, fun i hi_M => ?_, fun i j hij hj => ?_⟩
  · simp only [List.length_append] at hi_M
    by_cases hi₁ : i < M₁.length
    · obtain ⟨hlt, hlo, hmid, heq⟩ := hspec₁ i hi₁
      refine ⟨by simpa [pos, hi₁] using hlt, by simpa [pos, hi₁] using hlo, ?_, ?_⟩
      · simp only [pos, hi₁, ↓reduceIte]
        omega
      · rw [List.getElem_append_left hi₁]
        simpa [pos, hi₁] using heq
    · have hi₂ : i - M₁.length < M₂.length := by omega
      obtain ⟨hlt, hmid, hhi, heq⟩ := hspec₂ (i - M₁.length) hi₂
      refine ⟨by simpa [pos, hi₁] using hlt, ?_, by simpa [pos, hi₁] using hhi, ?_⟩
      · simp only [pos, hi₁, ↓reduceIte]
        omega
      · rw [List.getElem_append_right (Nat.le_of_not_lt hi₁)]
        simpa [pos, hi₁] using heq
  · simp only [List.length_append] at hj
    by_cases hj₁ : j < M₁.length
    · have hi₁ : i < M₁.length := Nat.lt_trans hij hj₁
      simp only [pos, hi₁, hj₁, ↓reduceIte]
      exact hmono₁ i j hij hj₁
    · by_cases hi₁ : i < M₁.length
      · obtain ⟨_, _, hmid₁, _⟩ := hspec₁ i hi₁
        obtain ⟨_, hmid₂, _, _⟩ := hspec₂ (j - M₁.length) (by omega)
        simp only [pos, hi₁, hj₁, ↓reduceIte]
        omega
      · simp only [pos, hi₁, hj₁, ↓reduceIte]
        exact hmono₂ (i - M₁.length) (j - M₁.length) (by omega) (by omega)

theorem IsBoundedSubseq.pair (L : List α) {p₁ p₂ lo hi : ℕ}
    (hp₁ : p₁ < L.length) (hp₂ : p₂ < L.length)
    (hlo : lo ≤ p₁) (h12 : p₁ < p₂) (hhi : p₂ < hi) :
    IsBoundedSubseq L [L[p₁]'hp₁, L[p₂]'hp₂] lo hi :=
  (IsBoundedSubseq.singleton L hp₁ hlo h12).append (IsBoundedSubseq.singleton L hp₂ le_rfl hhi)

theorem IsBoundedSubseq.ofFn_strictMono (L : List α) {m lo hi : ℕ} (hle : lo ≤ hi)
    (f : Fin m → ℕ) (hf_lt : ∀ i : Fin m, f i < L.length)
    (hf_lo : ∀ i : Fin m, lo ≤ f i) (hf_hi : ∀ i : Fin m, f i < hi)
    (hmono : StrictMono f) :
    IsBoundedSubseq L (List.ofFn (fun i : Fin m => L[f i]'(hf_lt i))) lo hi := by
  let pos (i : ℕ) : ℕ := if hi_m : i < m then f ⟨i, hi_m⟩ else 0
  refine ⟨hle, pos, fun i hi_M => ?_, fun i j hij hj => ?_⟩
  · simp only [List.length_ofFn] at hi_M
    refine ⟨by simpa [pos, hi_M] using hf_lt ⟨i, hi_M⟩,
      by simpa [pos, hi_M] using hf_lo ⟨i, hi_M⟩,
      by simpa [pos, hi_M] using hf_hi ⟨i, hi_M⟩, ?_⟩
    simp [pos, hi_M]
  · simp only [List.length_ofFn] at hj
    have hi : i < m := Nat.lt_trans hij hj
    simp only [pos, hi, hj, ↓reduceDIte]
    exact hmono hij

theorem IsBoundedSubseq.ofFn_reverse_strictAnti (L : List α) {m lo hi : ℕ} (hle : lo ≤ hi)
    (f : Fin m → ℕ) (hf_lt : ∀ i : Fin m, f i < L.length)
    (hf_lo : ∀ i : Fin m, lo ≤ f i) (hf_hi : ∀ i : Fin m, f i < hi)
    (hanti : StrictAnti f) :
    IsBoundedSubseq L ((List.ofFn (fun i : Fin m => L[f i]'(hf_lt i))).reverse) lo hi := by
  let pos (i : ℕ) : ℕ := if hi_m : i < m then f ⟨m - 1 - i, by omega⟩ else 0
  refine ⟨hle, pos, fun i hi_M => ?_, fun i j hij hj => ?_⟩
  · simp only [List.length_reverse, List.length_ofFn] at hi_M
    have hidx : m - 1 - i < m := by omega
    refine ⟨by simpa [pos, hi_M] using hf_lt ⟨m - 1 - i, hidx⟩,
      by simpa [pos, hi_M] using hf_lo ⟨m - 1 - i, hidx⟩,
      by simpa [pos, hi_M] using hf_hi ⟨m - 1 - i, hidx⟩, ?_⟩
    rw [List.getElem_reverse]
    simp [pos, hi_M]
  · simp only [List.length_reverse, List.length_ofFn] at hj
    have hi : i < m := Nat.lt_trans hij hj
    simp only [pos, hi, hj, ↓reduceDIte]
    have hlt_rev : (⟨m - 1 - j, by omega⟩ : Fin m) < ⟨m - 1 - i, by omega⟩ := by
      simp only [Fin.mk_lt_mk]; omega
    exact hanti hlt_rev

/-- Any subsequence of a clockwise sequence realized by strictly increasing indices is clockwise. -/
theorem IsClockwiseSeq.of_isBoundedSubseq {L M : List α} {lo hi : ℕ}
    (hcw : Ω.IsClockwiseSeq L) (hsub : IsBoundedSubseq L M lo hi) :
    Ω.IsClockwiseSeq M := by
  rcases hsub with ⟨_, pos, hspec, hmono⟩
  have hpos_lt : ∀ i, i < M.length → pos i < L.length := fun i hi => (hspec i hi).choose
  have hpos_eq : ∀ (i : ℕ) (hi : i < M.length), M[i]'hi = L[pos i]'(hpos_lt i hi) :=
    fun i hi => (hspec i hi).choose_spec.2.2
  have hpos_inj : ∀ i j, i < M.length → j < M.length → pos i = pos j → i = j := by
    intro i j hi hj heq
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · have := hmono i j hlt hj; omega
    · rfl
    · have := hmono j i hgt hi; omega
  have hM_nodup : M.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [Fin.mk.injEq]
    dsimp only at hij
    rw [hpos_eq i hi, hpos_eq j hj] at hij
    have hpos_eq_ij : pos i = pos j := (List.Nodup.getElem_inj_iff hcw.1).mp hij
    exact hpos_inj i j hi hj hpos_eq_ij
  have hM_sub_L : ∀ v ∈ M, v ∈ L := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    rw [hpos_eq i hi]
    exact List.getElem_mem (hpos_lt i hi)
  refine ⟨hM_nodup, fun v hv => hcw.2.1 v (hM_sub_L v hv), fun i hi => ?_⟩
  have hlt_i : pos i < L.length := hpos_lt i hi
  have hlen_L : 0 < L.length := Nat.zero_lt_of_lt hlt_i
  by_cases hi_next : i + 1 < M.length
  · have hlt_next : pos (i + 1) < L.length := hpos_lt (i + 1) hi_next
    have hmod_M : (i + 1) % M.length = i + 1 := Nat.mod_eq_of_lt hi_next
    have hlt_pos : pos i < pos (i + 1) := hmono i (i + 1) (Nat.lt_succ_self i) hi_next
    obtain ⟨k, hk1, hk_eq, hk_min⟩ :=
      Ω.exists_iterate_step hcw (pos i) (pos (i + 1) - pos i) hlt_i (by omega)
    have hmod_L : (pos i + (pos (i + 1) - pos i)) % L.length = pos (i + 1) := by
      rw [Nat.add_sub_of_le (le_of_lt hlt_pos), Nat.mod_eq_of_lt hlt_next]
    have hk_target : (Ω.toFun^[k]) (M[i]) = M[(i + 1) % M.length]'(Nat.mod_lt _ (by omega)) := by
      rw [hpos_eq i hi, hk_eq, hpos_eq ((i + 1) % M.length)]
      congr 1
      rw [hmod_L, hmod_M]
    refine ⟨k, hk1, hk_target, List.getElem_mem _, fun j hj1 hjlt hj_in => ?_⟩
    have hj_L : (Ω.toFun^[j]) (L[pos i]'hlt_i) ∈ {v | v ∈ L} := by
      rw [← hpos_eq i hi]
      exact hM_sub_L _ hj_in
    obtain ⟨d, hd1, hdd, hd_eq⟩ := hk_min j hj1 hjlt hj_L
    obtain ⟨r, hr, hr_eq⟩ := List.getElem_of_mem hj_in
    rw [hpos_eq i hi, hd_eq, hpos_eq r hr] at hr_eq
    have hpos_r : (pos i + d) % L.length = pos r :=
      (List.Nodup.getElem_inj_iff hcw.1).mp hr_eq.symm
    rw [Nat.mod_eq_of_lt (by omega)] at hpos_r
    rcases lt_trichotomy r i with hri | rfl | hir
    · have := hmono r i hri hi; omega
    · omega
    · rcases eq_or_lt_of_le (by omega : i + 1 ≤ r) with rfl | h_gt
      · omega
      · have := hmono (i + 1) r h_gt hr; omega
  · have hi_last : i + 1 = M.length := by omega
    have hmod_M : (i + 1) % M.length = 0 := by rw [hi_last, Nat.mod_self]
    rcases Nat.eq_zero_or_pos i with rfl | hi_pos
    · -- `M.length = 1`
      obtain ⟨k, hk1, hk_eq, hk_min⟩ :=
        Ω.exists_iterate_step hcw (pos 0) L.length hlt_i hlen_L
      have hmod_L : (pos 0 + L.length) % L.length = pos 0 := by
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt_i]
      have hk_target : (Ω.toFun^[k]) (M[0]) = M[(0 + 1) % M.length]'(Nat.mod_lt _ (by omega)) := by
        rw [hpos_eq 0 hi, hk_eq, hpos_eq ((0 + 1) % M.length)]
        congr 1
        rw [hmod_L, hmod_M]
      refine ⟨k, hk1, hk_target, List.getElem_mem _, fun j hj1 hjlt hj_in => ?_⟩
      have hj_L : (Ω.toFun^[j]) (L[pos 0]'hlt_i) ∈ {v | v ∈ L} := by
        rw [← hpos_eq 0 hi]
        exact hM_sub_L _ hj_in
      obtain ⟨d, hd1, hdd, hd_eq⟩ := hk_min j hj1 hjlt hj_L
      obtain ⟨r, hr, hr_eq⟩ := List.getElem_of_mem hj_in
      have hr0 : r = 0 := by omega
      subst hr0
      rw [hpos_eq 0 hi, hd_eq] at hr_eq
      have hpos_0 : (pos 0 + d) % L.length = pos 0 :=
        (List.Nodup.getElem_inj_iff hcw.1).mp hr_eq.symm
      by_cases hlt_len : pos 0 + d < L.length
      · rw [Nat.mod_eq_of_lt hlt_len] at hpos_0; omega
      · have h_sub : (pos 0 + d) % L.length = pos 0 + d - L.length := by
          have h_eq : pos 0 + d = L.length + (pos 0 + d - L.length) := by omega
          conv_lhs => rw [h_eq]
          rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        rw [h_sub] at hpos_0; omega
    · -- `M.length ≥ 2`
      have h0_lt : 0 < M.length := by omega
      have hlt_0 : pos 0 < L.length := hpos_lt 0 h0_lt
      have hlt_0i : pos 0 < pos i := hmono 0 i hi_pos hi
      obtain ⟨k, hk1, hk_eq, hk_min⟩ :=
        Ω.exists_iterate_step hcw (pos i) (L.length + pos 0 - pos i) hlt_i (by omega)
      have hmod_L : (pos i + (L.length + pos 0 - pos i)) % L.length = pos 0 := by
        have h_add : pos i + (L.length + pos 0 - pos i) = L.length + pos 0 := by omega
        rw [h_add, Nat.add_mod_left, Nat.mod_eq_of_lt hlt_0]
      have hk_target : (Ω.toFun^[k]) (M[i]) = M[(i + 1) % M.length]'(Nat.mod_lt _ (by omega)) := by
        rw [hpos_eq i hi, hk_eq, hpos_eq ((i + 1) % M.length)]
        congr 1
        rw [hmod_L, hmod_M]
      refine ⟨k, hk1, hk_target, List.getElem_mem _, fun j hj1 hjlt hj_in => ?_⟩
      have hj_L : (Ω.toFun^[j]) (L[pos i]'hlt_i) ∈ {v | v ∈ L} := by
        rw [← hpos_eq i hi]
        exact hM_sub_L _ hj_in
      obtain ⟨d, hd1, hdd, hd_eq⟩ := hk_min j hj1 hjlt hj_L
      obtain ⟨r, hr, hr_eq⟩ := List.getElem_of_mem hj_in
      have hlt_r : pos r < L.length := hpos_lt r hr
      rw [hpos_eq i hi, hd_eq, hpos_eq r hr] at hr_eq
      have hpos_r : (pos i + d) % L.length = pos r :=
        (List.Nodup.getElem_inj_iff hcw.1).mp hr_eq.symm
      have hpos_ge_0 : pos 0 ≤ pos r := by
        rcases Nat.eq_zero_or_pos r with rfl | hr_pos
        · exact le_rfl
        · exact le_of_lt (hmono 0 r hr_pos hr)
      have hpos_le_i : pos r ≤ pos i := by
        rcases eq_or_lt_of_le (by omega : r ≤ i) with rfl | hri
        · exact le_rfl
        · exact le_of_lt (hmono r i hri hi)
      by_cases hlt_len : pos i + d < L.length
      · rw [Nat.mod_eq_of_lt hlt_len] at hpos_r; omega
      · have h_sub : (pos i + d) % L.length = pos i + d - L.length := by
          have h_eq : pos i + d = L.length + (pos i + d - L.length) := by omega
          conv_lhs => rw [h_eq]
          rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        rw [h_sub] at hpos_r; omega

/-- Cyclic rotation of a clockwise sequence is clockwise. -/
theorem IsClockwiseSeq.append_comm {L₁ L₂ : List α}
    (hcw : Ω.IsClockwiseSeq (L₁ ++ L₂)) :
    Ω.IsClockwiseSeq (L₂ ++ L₁) := by
  have hnodup : (L₂ ++ L₁).Nodup := List.nodup_append_comm.mp hcw.1
  have hbar : ∀ v ∈ L₂ ++ L₁, v ∈ Ω.bar := by
    intro v hv
    rw [List.mem_append] at hv
    exact hcw.2.1 v (List.mem_append.mpr hv.symm)
  have hset : {v | v ∈ L₂ ++ L₁} = {v | v ∈ L₁ ++ L₂} := by
    ext v; simp [or_comm]
  have hget : ∀ (m : ℕ) (hm : m < (L₂ ++ L₁).length),
      (L₂ ++ L₁)[m]'hm =
        (L₁ ++ L₂)[(m + L₁.length) % (L₁ ++ L₂).length]'(Nat.mod_lt _ (by simp at hm ⊢; omega))
          := by
    intro m hm
    have hlen_eq : (L₁ ++ L₂).length = L₁.length + L₂.length := List.length_append
    have hm_len : m < L₂.length + L₁.length := by simpa using hm
    by_cases hm₂ : m < L₂.length
    · rw [List.getElem_append_left hm₂]
      have hmod : (m + L₁.length) % (L₁ ++ L₂).length = L₁.length + m := by
        rw [hlen_eq, add_comm m L₁.length]
        exact Nat.mod_eq_of_lt (by omega)
      have hrhs : (L₁ ++ L₂)[(m + L₁.length) % (L₁ ++ L₂).length]'(Nat.mod_lt _
        (by simp at hm ⊢; omega)) =
          (L₁ ++ L₂)[L₁.length + m]'(by rw [hlen_eq]; omega) := by
        congr 1
      rw [hrhs, List.getElem_append_right (Nat.le_add_right L₁.length m)]
      simp
    · rw [List.getElem_append_right (Nat.le_of_not_lt hm₂)]
      have hmod : (m + L₁.length) % (L₁ ++ L₂).length = m - L₂.length := by
        have h_add : m + L₁.length = (L₁ ++ L₂).length + (m - L₂.length) := by
          rw [hlen_eq]; omega
        rw [h_add, Nat.add_mod_left, Nat.mod_eq_of_lt (by rw [hlen_eq]; omega)]
      have hrhs : (L₁ ++ L₂)[(m + L₁.length) % (L₁ ++ L₂).length]'(Nat.mod_lt _
        (by simp at hm ⊢; omega)) =
          (L₁ ++ L₂)[m - L₂.length]'(by rw [hlen_eq]; omega) := by
        congr 1
      rw [hrhs, List.getElem_append_left (by omega)]
  refine ⟨hnodup, hbar, fun i hi => ?_⟩
  rw [hset]
  have hn_pos : 0 < (L₁ ++ L₂).length := by simp at hi ⊢; omega
  have hlen_same : (L₂ ++ L₁).length = (L₁ ++ L₂).length := by simp [add_comm]
  let i' := (i + L₁.length) % (L₁ ++ L₂).length
  have hi' : i' < (L₁ ++ L₂).length := Nat.mod_lt _ hn_pos
  have hhit := hcw.2.2 i' hi'
  have h1 : (L₂ ++ L₁)[i]'hi = (L₁ ++ L₂)[i']'hi' := hget i hi
  have h2 : (L₂ ++ L₁)[(i + 1) % (L₂ ++ L₁).length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)) =
      (L₁ ++ L₂)[(i' + 1) % (L₁ ++ L₂).length]'(Nat.mod_lt _ hn_pos) := by
    rw [hget ((i + 1) % (L₂ ++ L₁).length)]
    congr 1
    simp only [i', hlen_same]
    calc ((i + 1) % (L₁ ++ L₂).length + L₁.length) % (L₁ ++ L₂).length
      _ = (i + 1 + L₁.length) % (L₁ ++ L₂).length := Nat.mod_add_mod _ _ _
      _ = (i + L₁.length + 1) % (L₁ ++ L₂).length := by ring_nf
      _ = ((i + L₁.length) % (L₁ ++ L₂).length + 1) % (L₁ ++ L₂).length :=
        (Nat.mod_add_mod _ _ _).symm
  rwa [h1, h2]

end CyclicPerm

/-! ## Fence Construction from Clockwise Endpoint Sequences and Transaction Enumeration -/

namespace Society

variable (S : Society α β)

/-- Given `p ≥ 2` mutually disjoint `Ω`-paths `P : Fin p → Graph α β` in `P_set` with ends
`a i, b i` such that `(List.ofFn a).reverse ++ b_perm` is `Ω`-clockwise (where every `b i` belongs
to `b_perm`), the complementary intervals determined by `a ⟨p - 1, _⟩` and `a ⟨0, _⟩` form a fence
`(A', B')` for `range P` with `a i ∈ A'` and `b i ∈ B'` for all `i`. -/
theorem exists_isFenceFor_of_isClockwiseSeq_reverse_append
    {P_set : Set (Graph α β)} (hdisj : S.IsDisjointOmegaPathSet P_set)
    {p : ℕ} (hp : 2 ≤ p)
    (P : Fin p → Graph α β) (a b : Fin p → α) (b_perm : List α)
    (hP_inj : Function.Injective P)
    (hP_sub : range P ⊆ P_set)
    (hends : ∀ i : Fin p, S.IsOmegaPathWithEnds (P i) (a i) (b i))
    (hb_mem : ∀ i : Fin p, b i ∈ b_perm)
    (hcw : S.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ b_perm)) :
    (range P).ncard = p ∧
      ∃ A' B' : Set α, S.IsFenceFor (range P) A' B' ∧
        ∀ i : Fin p, a i ∈ A' ∧ b i ∈ B' ∧ S.IsOmegaPathWithEnds (P i) (a i) (b i) := by
  have hcard : (range P).ncard = p := by
    rw [← image_univ, Set.ncard_image_of_injective _ hP_inj, Set.ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  let L := (List.ofFn a).reverse ++ b_perm
  have hlen_a : ((List.ofFn a).reverse).length = p := by simp
  have h0_lt : 0 < L.length := by simp [L]; omega
  have hp1_lt : p - 1 < L.length := by simp [L]; omega
  let u := a ⟨p - 1, by omega⟩
  let v := a ⟨0, by omega⟩
  have hL0 : L[0]'h0_lt = u := by
    rw [List.getElem_append_left (by simp; omega), List.getElem_reverse]
    simp [u]
  have hLp1 : L[p - 1]'hp1_lt = v := by
    rw [List.getElem_append_left (by simp; omega), List.getElem_reverse]
    simp [v]
  have hu_bar : u ∈ S.Ω.bar := (hends ⟨p - 1, by omega⟩).2.2.1
  have hv_bar : v ∈ S.Ω.bar := (hends ⟨0, by omega⟩).2.2.1
  have huv : u ≠ v := by
    intro heq
    have h0_eq : L[0]'h0_lt = L[p - 1]'hp1_lt := by rw [hL0, hLp1, heq]
    have hidx := (List.Nodup.getElem_inj_iff hcw.1).mp h0_eq
    omega
  let A' : Set α := {u, v} ∪ S.Ω.interval u v
  let B' : Set α := S.Ω.interval v u
  have hfence_AB : S.Ω.IsFence A' B' := S.Ω.isFence_interval_compl hu_bar hv_bar huv
  have ha_in_A' : ∀ i : Fin p, a i ∈ A' := by
    intro i
    let m := p - 1 - i.1
    have hm_lt : m < L.length := by simp [L, m]; omega
    have hLm : L[m]'hm_lt = a i := by
      rw [List.getElem_append_left (by simp [m]; omega), List.getElem_reverse]
      simp only [List.length_ofFn, List.getElem_ofFn, m]
      congr 1
      ext
      dsimp
      omega
    rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
    · have : a i = u := by rw [← hLm, ← hL0]; congr 1
      exact Or.inl (Or.inl this)
    · rcases eq_or_lt_of_le (by omega : m ≤ p - 1) with hmp | hm_lt_p1
      · have : a i = v := by rw [← hLm, ← hLp1]; congr 1
        exact Or.inl (Or.inr this)
      · right
        have hint := S.Ω.mem_interval_of_lt hcw hm_pos hm_lt_p1 hp1_lt
        rwa [hL0, hLp1, hLm] at hint
  have hb_in_B' : ∀ i : Fin p, b i ∈ B' := by
    intro i
    obtain ⟨j, hj, hj_eq⟩ := List.getElem_of_mem (hb_mem i)
    have h_idx_lt : p + j < L.length := by simp [L]; omega
    have hLpj : L[p + j]'h_idx_lt = b i := by
      rw [List.getElem_append_right (by simp)]
      simpa using hj_eq
    have hint := S.Ω.mem_interval_of_lt hcw (i₁ := 0) (i₂ := p - 1) (i₃ := p + j)
      (by omega) (by omega) h_idx_lt
    rw [hL0, hLp1, hLpj] at hint
    exact S.Ω.mem_interval_rotate_left hint
  have hdisj_range : S.IsDisjointOmegaPathSet (range P) :=
    ⟨fun Q hQ => hdisj.1 Q (hP_sub hQ), hdisj.2.mono hP_sub⟩
  refine ⟨hcard, A', B', ⟨hdisj_range, hfence_AB, ?_⟩,
    fun i => ⟨ha_in_A' i, hb_in_B' i, hends i⟩⟩
  rintro Q ⟨i, rfl⟩
  exact ⟨a i, ha_in_A' i, b i, hb_in_B' i, hends i⟩

theorem exists_crosscap_of_isClockwiseSeq
    {P_set : Set (Graph α β)} (hdisj : S.IsDisjointOmegaPathSet P_set)
    {r : ℕ} (hr : 2 ≤ r)
    (P : Fin r → Graph α β) (a b : Fin r → α)
    (hP_inj : Function.Injective P)
    (hP_sub : range P ⊆ P_set)
    (hends : ∀ i : Fin r, S.IsOmegaPathWithEnds (P i) (a i) (b i))
    (hcw : S.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ (List.ofFn b).reverse)) :
    range P ⊆ P_set ∧ (range P).ncard = r ∧ S.IsCrosscapTransaction (range P) := by
  obtain ⟨hcard, A', B', hfence, h_ab⟩ :=
    S.exists_isFenceFor_of_isClockwiseSeq_reverse_append hdisj hr P a b
      ((List.ofFn b).reverse) hP_inj hP_sub hends
      (fun i => List.mem_reverse.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)) hcw
  exact ⟨hP_sub, hcard, A', B', hfence, r, hr, P, a, b, hP_inj, rfl, h_ab, hcw⟩

theorem exists_leap_of_isClockwiseSeq
    {P_set : Set (Graph α β)} (hdisj : S.IsDisjointOmegaPathSet P_set)
    {s : ℕ} (hs : 3 ≤ s)
    (P : Fin s → Graph α β) (a b : Fin s → α)
    (hP_inj : Function.Injective P)
    (hP_sub : range P ⊆ P_set)
    (hends : ∀ i : Fin s, S.IsOmegaPathWithEnds (P i) (a i) (b i))
    (hcw : S.Ω.IsClockwiseSeq
      ((List.ofFn a).reverse ++
        List.ofFn (fun i : Fin (s - 1) => b ⟨i.1 + 1, by omega⟩) ++
        [b ⟨0, by omega⟩])) :
    range P ⊆ P_set ∧ (range P).ncard = s ∧ S.IsLeapTransaction (range P) := by
  let b_perm := List.ofFn (fun i : Fin (s - 1) => b ⟨i.1 + 1, by omega⟩) ++ [b ⟨0, by omega⟩]
  have hcw' : S.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ b_perm) := by
    simpa [b_perm, List.append_assoc] using hcw
  have hb_mem : ∀ i : Fin s, b i ∈ b_perm := by
    intro ⟨i, hi⟩
    simp only [b_perm, List.mem_append, List.mem_ofFn, List.mem_singleton]
    rcases Nat.eq_zero_or_pos i with rfl | hi_pos
    · exact Or.inr rfl
    · left
      refine ⟨⟨i - 1, by omega⟩, ?_⟩
      congr 1
      ext
      dsimp
      omega
  obtain ⟨hcard, A', B', hfence, h_ab⟩ :=
    S.exists_isFenceFor_of_isClockwiseSeq_reverse_append hdisj (by omega) P a b
      b_perm hP_inj hP_sub hends hb_mem hcw'
  exact ⟨hP_sub, hcard, A', B', hfence, s, hs, P, a, b, hP_inj, rfl, h_ab, hcw⟩

theorem exists_doublecross_of_isClockwiseSeq
    {P_set : Set (Graph α β)} (hdisj : S.IsDisjointOmegaPathSet P_set)
    {t : ℕ} (ht : 4 ≤ t)
    (P : Fin t → Graph α β) (a b : Fin t → α)
    (hP_inj : Function.Injective P)
    (hP_sub : range P ⊆ P_set)
    (hends : ∀ i : Fin t, S.IsOmegaPathWithEnds (P i) (a i) (b i))
    (hcw : S.Ω.IsClockwiseSeq
      ((List.ofFn a).reverse ++
        [b ⟨1, by omega⟩, b ⟨0, by omega⟩] ++
        List.ofFn (fun i : Fin (t - 4) => b ⟨i.1 + 2, by omega⟩) ++
        [b ⟨t - 1, by omega⟩, b ⟨t - 2, by omega⟩])) :
    range P ⊆ P_set ∧ (range P).ncard = t ∧ S.IsDoublecrossTransaction (range P) := by
  let b_perm := [b ⟨1, by omega⟩, b ⟨0, by omega⟩] ++
    List.ofFn (fun i : Fin (t - 4) => b ⟨i.1 + 2, by omega⟩) ++
    [b ⟨t - 1, by omega⟩, b ⟨t - 2, by omega⟩]
  have hcw' : S.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ b_perm) := by
    simpa [b_perm, List.append_assoc] using hcw
  have hb_mem : ∀ i : Fin t, b i ∈ b_perm := by
    intro ⟨i, hi⟩
    simp only [b_perm, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_ofFn]
    by_cases hi0 : i = 0
    · subst hi0; exact Or.inl (Or.inl (Or.inr rfl))
    · by_cases hi1 : i = 1
      · subst hi1; exact Or.inl (Or.inl (Or.inl rfl))
      · by_cases hit2 : i = t - 2
        · subst hit2; exact Or.inr (Or.inr rfl)
        · by_cases hit1 : i = t - 1
          · subst hit1; exact Or.inr (Or.inl rfl)
          · left; right
            refine ⟨⟨i - 2, by omega⟩, ?_⟩
            congr 1; ext; dsimp; omega
  obtain ⟨hcard, A', B', hfence, h_ab⟩ :=
    S.exists_isFenceFor_of_isClockwiseSeq_reverse_append hdisj (by omega) P a b
      b_perm hP_inj hP_sub hends hb_mem hcw'
  exact ⟨hP_sub, hcard, A', B', hfence, t, ht, P, a, b, hP_inj, rfl, h_ab, hcw⟩

/-- For any transaction `P_set` of cardinality `k ≥ 1` with fence `(A, B)`, there is a clockwise
enumeration `L` of `S.transactionEnds P_set` of length `2 * k` with the ends in `A` first, an
injective map `R : Fin k → Graph α β` into `P_set`, and a bijection `φ : Fin k → Fin k` such that
each `R i` has ends `L[k - 1 - i.1]` and `L[k + (φ i).1]`. -/
theorem exists_clockwise_enumeration {P_set : Set (Graph α β)} {A B : Set α}
    (hfence : S.IsFenceFor P_set A B) {k : ℕ} (hk_eq : P_set.ncard = k) (hk_pos : 1 ≤ k) :
    ∃ (L : List α) (hL_len : L.length = 2 * k)
      (R : Fin k → Graph α β) (φ : Fin k → Fin k),
      S.Ω.IsClockwiseSeq L ∧ {v | v ∈ L} = S.transactionEnds P_set ∧
      Function.Injective R ∧ range R ⊆ P_set ∧
      Function.Injective φ ∧ Function.Surjective φ ∧
      (∀ i : Fin k, S.IsOmegaPathWithEnds (R i)
        (L[k - 1 - i.1]'(by omega)) (L[k + (φ i).1]'(by omega))) ∧
      (∀ (i : ℕ) (hi : i < L.length), i < k → L[i]'hi ∈ A) ∧
      (∀ (i : ℕ) (hi : i < L.length), k ≤ i → L[i]'hi ∈ B) ∧
      Disjoint (S.Ω.interval (L[2 * k - 1]'(by omega)) (L[0]'(by omega)))
        (S.transactionEnds P_set) := by
  classical
  let W := S.transactionEnds P_set
  have hW_bar : W ⊆ S.Ω.bar := S.transactionEnds_subset_bar P_set
  obtain ⟨hncard_A, hncard_B, hncard_W⟩ := hfence.ncard_transactionEnds S
  rw [hk_eq] at hncard_A hncard_B hncard_W
  have hfin_P : P_set.Finite := hfence.1.finite S
  have hP_ne : P_set.Nonempty := (Set.ncard_pos hfin_P).mp (by omega)
  obtain ⟨P₀, hP₀_in⟩ := hP_ne
  obtain ⟨a₀, ha₀A, b₀, hb₀B, hP₀_ends⟩ := hfence.2.2 P₀ hP₀_in
  have ha₀W : a₀ ∈ A ∩ W := ⟨ha₀A, hP₀_ends.mem_transactionEnds_left S hP₀_in⟩
  have hb₀W : b₀ ∈ B ∩ W := ⟨hb₀B, hP₀_ends.mem_transactionEnds_right S hP₀_in⟩
  have hW_sub_BA : W ⊆ B ∪ A := by
    rw [union_comm, hfence.2.1.2.2.2.1]; exact hW_bar
  obtain ⟨b_k, hb_k, a_k, ha_k, hd_bk_ak⟩ :=
    S.Ω.exists_empty_interval_AB_of_subset_union hW_bar hW_sub_BA ⟨b₀, hb₀W⟩ ⟨a₀, ha₀W⟩
  obtain ⟨L, hL_len_W, hL_set, hL_0, hL_cw⟩ :=
    S.Ω.exists_isClockwiseSeq_of_subset_bar hW_bar ha_k.2
  have hL_len : L.length = 2 * k := hL_len_W.trans hncard_W
  have h2k_pos : 0 < L.length := by omega
  have hL_last : L[2 * k - 1]'(by omega) = b_k := by
    have hhit_last : S.Ω.FirstHitIn W (L[2 * k - 1]'(by omega)) a_k := by
      have h := hL_cw.2.2 (2 * k - 1) (by omega)
      have hmod : (2 * k - 1 + 1) % L.length = 0 := by
        rw [hL_len, Nat.sub_add_cancel (by omega), Nat.mod_self]
      rw [hL_set] at h
      simpa [hmod, hL_0 h2k_pos] using h
    have hbk_ne_ak : b_k ≠ a_k :=
      fun h => disjoint_left.mp hfence.2.1.2.2.1 ha_k.1 (h ▸ hb_k.1)
    have hhit_bk : S.Ω.FirstHitIn W b_k a_k :=
      (S.Ω.firstHitIn_iff_disjoint_interval hW_bar hb_k.2 ha_k.2 hbk_ne_ak).mpr hd_bk_ak
    have hlast_W : L[2 * k - 1]'(by omega) ∈ W := by
      rw [← hL_set]; exact List.getElem_mem (by omega)
    exact hhit_last.inj_left (hW_bar hlast_W) (hW_bar hb_k.2) hlast_W hb_k.2 hhit_bk
  have hno_BA : ∀ (i j : ℕ) (hi : i < L.length) (hj : j < L.length),
      i < j → L[i]'hi ∈ B → L[j]'hj ∈ A → False := by
    intro i j hi hj hij hLiB hLjA
    have hi_gt : 0 < i := by
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [hL_0 h2k_pos] at hLiB
        exact (disjoint_left.mp hfence.2.1.2.2.1 ha_k.1 hLiB).elim
      · exact hpos
    have hj_lt : j < 2 * k - 1 := by
      by_contra hge
      have hj_eq : j = 2 * k - 1 := by omega
      subst hj_eq
      rw [hL_last] at hLjA
      exact disjoint_left.mp hfence.2.1.2.2.1 hLjA hb_k.1
    have hLi_in : L[i]'hi ∈ S.Ω.interval a_k (L[j]'hj) := by
      have h := S.Ω.mem_interval_of_lt hL_cw hi_gt hij hj
      simpa [hL_0 h2k_pos] using h
    have hLj_in : L[j]'hj ∈ S.Ω.interval a_k b_k := by
      have h := S.Ω.mem_interval_of_lt hL_cw (Nat.lt_trans hi_gt hij) hj_lt (by omega)
      simpa [hL_0 h2k_pos, hL_last] using h
    have hbk_in : b_k ∈ S.Ω.interval (L[j]'hj) a_k := S.Ω.mem_interval_rotate_left hLj_in
    have hcr : S.Ω.Crosses a_k (L[j]'hj) (L[i]'hi) b_k :=
      S.Ω.crosses_iff_interval.mpr (Or.inl ⟨hLi_in, hbk_in⟩)
    exact hfence.2.1.2.2.2.2 a_k ha_k.1 (L[j]'hj) hLjA
      (fun h => by
        have h0j : L[0]'h2k_pos = L[j]'hj := (hL_0 h2k_pos).trans h
        have := (List.Nodup.getElem_inj_iff hL_cw.1).mp h0j
        omega)
      (L[i]'hi) hLiB b_k hb_k.1
      (fun h => by
        have hij' : L[i]'hi = L[2 * k - 1]'(by omega) := h.trans hL_last.symm
        have := (List.Nodup.getElem_inj_iff hL_cw.1).mp hij'
        omega)
      hcr
  have hL_A : ∀ (i : ℕ) (hi : i < L.length), i < k → L[i]'hi ∈ A := by
    intro i hi hik
    have hLi_W : L[i]'hi ∈ W := by rw [← hL_set]; exact List.getElem_mem hi
    have hLi_AB : L[i]'hi ∈ A ∪ B := by rw [hfence.2.1.2.2.2.1]; exact hW_bar hLi_W
    rcases hLi_AB with hA | hB
    · exact hA
    · exfalso
      have hsub : A ∩ W ⊆ {v | v ∈ L.take i} := by
        intro x ⟨hxA, hxW⟩
        rw [← hL_set] at hxW
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hxW
        have hji : j < i := by
          by_contra hge
          rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with rfl | hgt
          · exact disjoint_left.mp hfence.2.1.2.2.1 hxA hB
          · exact hno_BA i j hi hj hgt hB hxA
        rw [mem_ofPred_eq, List.mem_take_iff_getElem]
        exact ⟨j, by omega, rfl⟩
      have hfin_take : {v | v ∈ L.take i}.Finite :=
        (L.take i).toFinset.finite_toSet.subset (fun _ hx => List.mem_toFinset.mpr hx)
      have hle1 : k ≤ {v | v ∈ L.take i}.ncard := by
        rw [← hncard_A]
        exact Set.ncard_le_ncard hsub hfin_take
      have h_eq : {v | v ∈ L.take i} = ((L.take i).toFinset : Set α) := by ext x; simp
      have hle2 : {v | v ∈ L.take i}.ncard ≤ i := by
        rw [h_eq, Set.ncard_coe_finset]
        exact (List.toFinset_card_le (L.take i)).trans (by simp [Nat.le_of_lt hi])
      omega
  have hex_Q : ∀ i : Fin k,
      ∃ P ∈ P_set, ∃ j : Fin k,
        S.IsOmegaPathWithEnds P (L[k - 1 - i.1]'(by omega)) (L[k + j.1]'(by omega)) := by
    intro i
    have h_in_W : L[k - 1 - i.1]'(by omega) ∈ W := by
      rw [← hL_set]; exact List.getElem_mem (by omega)
    have h_in_A : L[k - 1 - i.1]'(by omega) ∈ A := hL_A (k - 1 - i.1) (by omega) (by omega)
    obtain ⟨P, hP_in, y, hPy⟩ := h_in_W
    obtain ⟨aP, haPA, bP, hbPB, hP_ends⟩ := hfence.2.2 P hP_in
    have haP_eq : aP = L[k - 1 - i.1]'(by omega) := by
      rcases hP_ends.ends_eq S hPy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact (disjoint_left.mp hfence.2.1.2.2.1 h_in_A hbPB).elim
    subst haP_eq
    have hbP_W : bP ∈ W := hP_ends.mem_transactionEnds_right S hP_in
    rw [← hL_set] at hbP_W
    obtain ⟨m, hm, hm_eq⟩ := List.getElem_of_mem hbP_W
    have hmk : k ≤ m := by
      by_contra hlt
      exact disjoint_left.mp hfence.2.1.2.2.1 (hL_A m hm (by omega)) (hm_eq ▸ hbPB)
    refine ⟨P, hP_in, ⟨m - k, by omega⟩, ?_⟩
    have hm_add : k + (m - k) = m := Nat.add_sub_of_le hmk
    simpa [hm_add, hm_eq] using hP_ends
  let R (i : Fin k) : Graph α β := (hex_Q i).choose
  let φ (i : Fin k) : Fin k := (hex_Q i).choose_spec.2.choose
  have hR_in : ∀ i : Fin k, R i ∈ P_set := fun i => (hex_Q i).choose_spec.1
  have hR_ends : ∀ i : Fin k,
      S.IsOmegaPathWithEnds (R i) (L[k - 1 - i.1]'(by omega)) (L[k + (φ i).1]'(by omega)) :=
    fun i => (hex_Q i).choose_spec.2.choose_spec
  have hL_B : ∀ (i : ℕ) (hi : i < L.length), k ≤ i → L[i]'hi ∈ B := by
    intro i hi hki
    have hLi_W : L[i]'hi ∈ W := by rw [← hL_set]; exact List.getElem_mem hi
    have hLi_AB : L[i]'hi ∈ A ∪ B := by rw [hfence.2.1.2.2.2.1]; exact hW_bar hLi_W
    rcases hLi_AB with hA | hB
    · exfalso
      have hsub : B ∩ W ⊆ {v | v ∈ L.drop (i + 1)} := by
        intro x ⟨hxB, hxW⟩
        rw [← hL_set] at hxW
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hxW
        have hij : i < j := by
          by_contra hle
          rcases eq_or_lt_of_le (Nat.le_of_not_lt hle) with rfl | hlt
          · exact disjoint_left.mp hfence.2.1.2.2.1 hA hxB
          · exact hno_BA j i hj hi hlt hxB hA
        rw [mem_ofPred_eq, List.mem_iff_getElem]
        refine ⟨j - (i + 1), by simp; omega, ?_⟩
        simp [Nat.add_sub_of_le (by omega : i + 1 ≤ j)]
      have hfin_drop : {v | v ∈ L.drop (i + 1)}.Finite :=
        (L.drop (i + 1)).toFinset.finite_toSet.subset (fun _ hx => List.mem_toFinset.mpr hx)
      have hle1 : k ≤ {v | v ∈ L.drop (i + 1)}.ncard := by
        rw [← hncard_B]
        exact Set.ncard_le_ncard hsub hfin_drop
      have h_eq : {v | v ∈ L.drop (i + 1)} = ((L.drop (i + 1)).toFinset : Set α) := by ext x; simp
      have hle2 : {v | v ∈ L.drop (i + 1)}.ncard ≤ L.length - (i + 1) := by
        rw [h_eq, Set.ncard_coe_finset]
        exact (List.toFinset_card_le (L.drop (i + 1))).trans (by simp)
      omega
    · exact hB
  have hR_inj : Function.Injective R := by
    intro i j heq
    have h₁ := hR_ends i
    have h₂ := hR_ends j
    rw [heq] at h₁
    rcases h₁.ends_eq S h₂ with ⟨h_eq, _⟩ | ⟨h_eq, _⟩
    · have := (List.Nodup.getElem_inj_iff hL_cw.1).mp h_eq
      ext; omega
    · exfalso
      have hA_j : L[k - 1 - j.1]'(by omega) ∈ A := hL_A (k - 1 - j.1) (by omega) (by omega)
      have hB_i : L[k + (φ i).1]'(by omega) ∈ B := hL_B (k + (φ i).1) (by omega) (by omega)
      exact disjoint_left.mp hfence.2.1.2.2.1 hA_j (h_eq ▸ hB_i)
  have hφ_inj : Function.Injective φ := by
    intro i j heq
    by_contra hne
    have hne_R : R i ≠ R j := fun h => hne (hR_inj h)
    have hdisj_R : Disjoint V(R i) V(R j) := hfence.1.2 (hR_in i) (hR_in j) hne_R
    have h_same_b : L[k + (φ i).1]'(by omega) = L[k + (φ j).1]'(by omega) := by
      congr 1; rw [heq]
    exact disjoint_left.mp hdisj_R (hR_ends i).1.right_mem (h_same_b ▸ (hR_ends j).1.right_mem)
  have hφ_surj : Function.Surjective φ := Finite.surjective_of_injective hφ_inj
  refine ⟨L, hL_len, R, φ, hL_cw, hL_set, hR_inj, by rintro _ ⟨i, rfl⟩; exact hR_in i,
    hφ_inj, hφ_surj, hR_ends, hL_A, hL_B, ?_⟩
  rw [hL_last, hL_0 h2k_pos]
  exact hd_bk_ak

/-- For any crooked transaction `P_set` of cardinality `k ≥ 1`, there is a clockwise enumeration `L`
of `S.transactionEnds P_set` of length `2 * k`, an injective map `R : Fin k → Graph α β` into
`P_set`, and a bijection `φ : Fin k → Fin k` such that each `R i` has ends
`L[k - 1 - i.1]` and `L[k + (φ i).1]`, with `φ ⟨0, _⟩ ≠ ⟨0, _⟩` and `φ ⟨k - 1, _⟩ ≠ ⟨k - 1, _⟩`. -/
theorem exists_clockwise_enumeration_of_crooked
    {P_set : Set (Graph α β)} (hcrooked : S.IsCrookedTransaction P_set)
    {k : ℕ} (hk_eq : P_set.ncard = k) (hk_pos : 1 ≤ k) :
    ∃ (L : List α) (hL_len : L.length = 2 * k)
      (R : Fin k → Graph α β) (φ : Fin k → Fin k),
      S.Ω.IsClockwiseSeq L ∧
      Function.Injective R ∧ range R ⊆ P_set ∧
      Function.Injective φ ∧ Function.Surjective φ ∧
      (∀ i : Fin k, S.IsOmegaPathWithEnds (R i)
        (L[k - 1 - i.1]'(by omega)) (L[k + (φ i).1]'(by omega))) ∧
      φ ⟨0, by omega⟩ ≠ ⟨0, by omega⟩ ∧
      φ ⟨k - 1, by omega⟩ ≠ ⟨k - 1, by omega⟩ := by
  obtain ⟨A, B, hfence⟩ := hcrooked.1
  obtain ⟨L, hL_len, R, φ, hL_cw, hL_set, hR_inj, hR_sub, hφ_inj, hφ_surj, hR_ends, -, -, hgap⟩ :=
    S.exists_clockwise_enumeration hfence hk_eq hk_pos
  have hR_in : ∀ i : Fin k, R i ∈ P_set := fun i => hR_sub ⟨i, rfl⟩
  have hW_bar := S.transactionEnds_subset_bar P_set
  refine ⟨L, hL_len, R, φ, hL_cw, hR_inj, hR_sub, hφ_inj, hφ_surj, hR_ends, ?_, ?_⟩
  · intro heq0
    have h₀_ends := hR_ends ⟨0, by omega⟩
    have hhit_0 : S.Ω.FirstHitIn (S.transactionEnds P_set) (L[k - 1]'(by omega)) (L[k]'(by omega))
      := by
      have h := hL_cw.2.2 (k - 1) (by omega)
      have hmod : (k - 1 + 1) % L.length = k := by
        rw [Nat.sub_add_cancel hk_pos, Nat.mod_eq_of_lt (by omega)]
      rw [hL_set] at h
      simpa [hmod] using h
    have h_u_W : L[k - 1]'(by omega) ∈ S.transactionEnds P_set := by
      rw [← hL_set]; exact List.getElem_mem (by omega)
    have h_v_W : L[k]'(by omega) ∈ S.transactionEnds P_set := by
      rw [← hL_set]; exact List.getElem_mem (by omega)
    have h_uv_ne : L[k - 1]'(by omega) ≠ L[k]'(by omega) := by
      intro h
      have := (List.Nodup.getElem_inj_iff hL_cw.1).mp h
      omega
    have hd_0 := (S.Ω.firstHitIn_iff_disjoint_interval hW_bar h_u_W h_v_W h_uv_ne).mp hhit_0
    have h₀_ends' : S.IsOmegaPathWithEnds (R ⟨0, by omega⟩) (L[k - 1]'(by omega)) (L[k]'(by omega))
      := by
      simpa [heq0] using h₀_ends
    exact hcrooked.2 _ (hR_in _) ⟨hR_in _, _, _, h₀_ends', Or.inl hd_0⟩
  · intro heqk
    have hk_ends := hR_ends ⟨k - 1, by omega⟩
    have hk_ends' : S.IsOmegaPathWithEnds (R ⟨k - 1, by omega⟩)
        (L[0]'(by omega)) (L[2 * k - 1]'(by omega)) := by
      have h_idx : k + (k - 1) = 2 * k - 1 := by omega
      simpa [heqk, h_idx] using hk_ends
    exact hcrooked.2 _ (hR_in _) ⟨hR_in _, _, _, hk_ends', Or.inr hgap⟩

/-! ## Erdős–Szekeres and Longest Increasing Subsequence on `Fin k` -/

private theorem strictMono_fin_ge {m k : ℕ} {x : Fin m → Fin k} (hx : StrictMono x) :
    ∀ (d : ℕ) (hd : d < m), d ≤ (x ⟨d, hd⟩).1 := by
  intro d
  induction d with
  | zero => intro _; exact Nat.zero_le _
  | succ d ih =>
    intro hd
    have hprev := ih (Nat.lt_of_succ_lt hd)
    have hstep : (x ⟨d, Nat.lt_of_succ_lt hd⟩).1 < (x ⟨d + 1, hd⟩).1 :=
      hx (by simp [Fin.mk_lt_mk])
    omega

private def IsIncSubseq {k : ℕ} (φ : Fin k → Fin k) (m : ℕ) : Prop :=
  ∃ x : Fin m → Fin k, StrictMono x ∧ StrictMono (φ ∘ x)

private def IsIncEndingAt {k : ℕ} (φ : Fin k → Fin k) (i : Fin k) (m : ℕ) : Prop :=
  ∃ x : Fin m → Fin k, StrictMono x ∧ StrictMono (φ ∘ x) ∧
    ∀ hm : 0 < m, x ⟨m - 1, by omega⟩ = i

private theorem not_isIncSubseq_succ {k : ℕ} (φ : Fin k → Fin k) :
    ¬ IsIncSubseq φ (k + 1) := by
  rintro ⟨x, hx, _⟩
  have hge := strictMono_fin_ge hx k (Nat.lt_succ_self k)
  have hlt := (x ⟨k, Nat.lt_succ_self k⟩).2
  omega

private theorem not_isIncEndingAt_succ {k : ℕ} (φ : Fin k → Fin k) (i : Fin k) :
    ¬ IsIncEndingAt φ i (k + 1) := by
  rintro ⟨x, hx, hφx, _⟩
  exact not_isIncSubseq_succ φ ⟨x, hx, hφx⟩

private theorem exists_fiber_ncard_ge {α₀ : Type*} [Finite α₀]
    (f : α₀ → ℕ) (r : ℕ) :
    ∀ (n : ℕ) (U : Set α₀), (∀ x ∈ U, f x < n) → n * (r - 1) < U.ncard →
      ∃ c < n, r ≤ {x ∈ U | f x = c}.ncard := by
  intro n
  induction n with
  | zero =>
    intro U hU hcard
    have hne : U.Nonempty := (Set.ncard_pos (Set.toFinite U)).mp (by omega)
    rcases hne with ⟨x, hx⟩
    exact (Nat.not_lt_zero (f x) (hU x hx)).elim
  | succ n ih =>
    intro U hU hcard
    let T : Set α₀ := {x ∈ U | f x = n}
    let U' : Set α₀ := {x ∈ U | f x < n}
    have h_union : U' ∪ T = U := by
      ext x
      simp only [U', T, mem_union, mem_sep_iff]
      exact ⟨fun h => h.elim (fun h1 => h1.1) (fun h2 => h2.1),
        fun hx => (lt_or_eq_of_le (Nat.le_of_lt_succ (hU x hx))).imp
          (fun hlt => ⟨hx, hlt⟩) (fun heq => ⟨hx, heq⟩)⟩
    have h_disj : Disjoint U' T := by
      rw [disjoint_left]
      intro x hx₁ hx₂
      exact Nat.ne_of_lt hx₁.2 hx₂.2
    have hcard_eq : U.ncard = U'.ncard + T.ncard := by
      rw [← h_union]
      exact Set.ncard_union_eq h_disj (Set.toFinite U') (Set.toFinite T)
    by_cases hT : r ≤ T.ncard
    · exact ⟨n, Nat.lt_succ_self n, hT⟩
    · have hU'_card : n * (r - 1) < U'.ncard := by
        rw [Nat.succ_mul] at hcard
        omega
      obtain ⟨c, hc_lt, hc_card⟩ := ih U' (fun _ hx => hx.2) hU'_card
      refine ⟨c, Nat.lt_succ_of_lt hc_lt, hc_card.trans ?_⟩
      refine Set.ncard_le_ncard (fun x hx => ⟨hx.1.1, hx.2⟩) (Set.toFinite _)

private theorem exists_strictMono_mem_of_ncard_ge {k : ℕ} :
    ∀ (r : ℕ) (T : Set (Fin k)), r ≤ T.ncard →
      ∃ idx : Fin r → Fin k, StrictMono idx ∧ ∀ j : Fin r, idx j ∈ T := by
  classical
  intro r
  induction r with
  | zero =>
    intro T _
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ r ih =>
    intro T hcard
    have hne : T.Nonempty := (Set.ncard_pos (Set.toFinite T)).mp (by omega)
    have hex : ∃ m : ℕ, ∃ hm : m < k, (⟨m, hm⟩ : Fin k) ∈ T := by
      rcases hne with ⟨⟨m, hm⟩, hmT⟩
      exact ⟨m, hm, hmT⟩
    let m₀ := Nat.find hex
    have hm₀_spec := Nat.find_spec hex
    let x₀ : Fin k := ⟨m₀, hm₀_spec.choose⟩
    have hx₀_in : x₀ ∈ T := hm₀_spec.choose_spec
    have hx₀_min : ∀ y ∈ T, x₀ ≤ y := by
      intro ⟨y, hy⟩ hyT
      change m₀ ≤ y
      by_contra hlt
      exact Nat.find_min hex (by omega) ⟨hy, hyT⟩
    let T' : Set (Fin k) := T \ {x₀}
    have hcard_T' : r ≤ T'.ncard := by
      rw [Set.ncard_sdiff_singleton_of_mem hx₀_in]
      omega
    obtain ⟨idx', hmono', hmem'⟩ := ih T' hcard_T'
    let idx (j : Fin (r + 1)) : Fin k :=
      if hj : j.1 = 0 then x₀ else idx' ⟨j.1 - 1, by omega⟩
    refine ⟨idx, fun i j hij => ?_, fun j => ?_⟩
    · by_cases hi0 : i.1 = 0
      · have hj0 : j.1 ≠ 0 := by omega
        simp only [idx, hi0, hj0, ↓reduceDIte]
        have hmem_j := hmem' ⟨j.1 - 1, by omega⟩
        exact lt_of_le_of_ne (hx₀_min _ hmem_j.1) (Ne.symm hmem_j.2)
      · have hj0 : j.1 ≠ 0 := by omega
        simp only [idx, hi0, hj0, ↓reduceDIte]
        exact hmono' (by simp only [Fin.mk_lt_mk]; omega)
    · by_cases hj0 : j.1 = 0
      · simp only [idx, hj0, ↓reduceDIte]
        exact hx₀_in
      · simp only [idx, hj0, ↓reduceDIte]
        exact (hmem' ⟨j.1 - 1, by omega⟩).1

/-- Erdős–Szekeres theorem for an injective map `φ : Fin k → Fin k`: if `(r - 1) * M ≤ k` with
`2 ≤ r` and `1 ≤ M`, then either there is a decreasing subsequence of length `r`, or there is a
maximum-length increasing subsequence `x : Fin n → Fin k` with `M ≤ n`. -/
theorem exists_decreasing_or_max_increasing {k r M : ℕ}
    (hr : 2 ≤ r) (hM : 1 ≤ M) (hk_pos : 1 ≤ k)
    (φ : Fin k → Fin k) (hφ_inj : Function.Injective φ)
    (hcard : (r - 1) * M ≤ k) :
    (∃ idx : Fin r → Fin k, StrictMono idx ∧ StrictAnti (φ ∘ idx)) ∨
    (∃ (n : ℕ) (hn : M ≤ n) (x : Fin n → Fin k),
      StrictMono x ∧ StrictMono (φ ∘ x) ∧
      (∀ p : Fin k, p < x ⟨0, by omega⟩ → φ (x ⟨0, by omega⟩) < φ p) ∧
      (∀ p : Fin k, φ p < φ (x ⟨0, by omega⟩) → x ⟨0, by omega⟩ < p) ∧
      (∀ p : Fin k, x ⟨n - 1, by omega⟩ < p → φ p < φ (x ⟨n - 1, by omega⟩)) ∧
      (∀ p : Fin k, φ (x ⟨n - 1, by omega⟩) < φ p → p < x ⟨n - 1, by omega⟩)) := by
  classical
  have hex_not : ∃ N : ℕ, ¬ IsIncSubseq φ (N + 1) := ⟨k, not_isIncSubseq_succ φ⟩
  let n := Nat.find hex_not
  have hnot_succ : ¬ IsIncSubseq φ (n + 1) := Nat.find_spec hex_not
  have hn_pos : 1 ≤ n := by
    by_contra hlt
    have hn0 : n = 0 := by omega
    rw [hn0] at hnot_succ
    refine hnot_succ ⟨fun _ => ⟨0, hk_pos⟩, ?_, ?_⟩
    · intro i j hij; omega
    · intro i j hij; omega
  have hinc_n : IsIncSubseq φ n := by
    by_contra hnot
    exact Nat.find_min hex_not (by omega : n - 1 < n) (by simpa [Nat.sub_add_cancel hn_pos] using
      hnot)
  by_cases hMn : M ≤ n
  · right
    obtain ⟨x, hx, hφx⟩ := hinc_n
    have hnot_prepend : ∀ p : Fin k, ¬ (p < x ⟨0, by omega⟩ ∧ φ p < φ (x ⟨0, by omega⟩)) := by
      rintro p ⟨hp_x, hp_φ⟩
      refine hnot_succ ⟨fun j : Fin (n + 1) => if hj : j.1 = 0 then p else x ⟨j.1 - 1, by omega⟩,
        ?_, ?_⟩
      · intro i j hij
        by_cases hi0 : i.1 = 0
        · have hj0 : j.1 ≠ 0 := by omega
          simp only [hi0, hj0, ↓reduceDIte]
          rcases eq_or_lt_of_le (Nat.zero_le (j.1 - 1)) with h0 | hpos
          · have h_eq : (⟨j.1 - 1, by omega⟩ : Fin n) = ⟨0, by omega⟩ := by ext; dsimp; omega
            rw [h_eq]; exact hp_x
          · exact lt_trans hp_x (hx (by simp only [Fin.mk_lt_mk]; omega))
        · have hj0 : j.1 ≠ 0 := by omega
          simp only [hi0, hj0, ↓reduceDIte]
          exact hx (by simp only [Fin.mk_lt_mk]; omega)
      · intro i j hij
        change φ _ < φ _
        by_cases hi0 : i.1 = 0
        · have hj0 : j.1 ≠ 0 := by omega
          simp only [hi0, hj0, ↓reduceDIte]
          rcases eq_or_lt_of_le (Nat.zero_le (j.1 - 1)) with h0 | hpos
          · have h_eq : (⟨j.1 - 1, by omega⟩ : Fin n) = ⟨0, by omega⟩ := by ext; dsimp; omega
            rw [h_eq]; exact hp_φ
          · exact lt_trans hp_φ (hφx (by simp only [Fin.mk_lt_mk]; omega))
        · have hj0 : j.1 ≠ 0 := by omega
          simp only [hi0, hj0, ↓reduceDIte]
          exact hφx (by simp only [Fin.mk_lt_mk]; omega)
    have hnot_append : ∀ p : Fin k,
        ¬ (x ⟨n - 1, by omega⟩ < p ∧ φ (x ⟨n - 1, by omega⟩) < φ p) := by
      rintro p ⟨hp_x, hp_φ⟩
      refine hnot_succ ⟨fun j : Fin (n + 1) => if hj : j.1 < n then x ⟨j.1, hj⟩ else p, ?_, ?_⟩
      · intro i j hij
        by_cases hj_n : j.1 < n
        · have hi_n : i.1 < n := Nat.lt_trans hij hj_n
          simp only [hi_n, hj_n, ↓reduceDIte]
          exact hx hij
        · have hi_n : i.1 < n := by omega
          simp only [hi_n, hj_n, ↓reduceDIte]
          rcases eq_or_lt_of_le (by omega : i.1 ≤ n - 1) with heq | hlt
          · have h_eq : (⟨i.1, hi_n⟩ : Fin n) = ⟨n - 1, by omega⟩ := by ext; dsimp; omega
            rw [h_eq]; exact hp_x
          · exact lt_trans (hx (by simp only [Fin.mk_lt_mk]; exact hlt)) hp_x
      · intro i j hij
        change φ _ < φ _
        by_cases hj_n : j.1 < n
        · have hi_n : i.1 < n := Nat.lt_trans hij hj_n
          simp only [hi_n, hj_n, ↓reduceDIte]
          exact hφx hij
        · have hi_n : i.1 < n := by omega
          simp only [hi_n, hj_n, ↓reduceDIte]
          rcases eq_or_lt_of_le (by omega : i.1 ≤ n - 1) with heq | hlt
          · have h_eq : (⟨i.1, hi_n⟩ : Fin n) = ⟨n - 1, by omega⟩ := by ext; dsimp; omega
            rw [h_eq]; exact hp_φ
          · exact lt_trans (hφx (by simp only [Fin.mk_lt_mk]; exact hlt)) hp_φ
    refine ⟨n, hMn, x, hx, hφx, ?_, ?_, ?_, ?_⟩
    · intro p hp
      rcases lt_trichotomy (φ p) (φ (x ⟨0, by omega⟩)) with hlt | heq | hgt
      · exact (hnot_prepend p ⟨hp, hlt⟩).elim
      · exact (ne_of_lt hp (hφ_inj heq)).elim
      · exact hgt
    · intro p hp
      rcases lt_trichotomy p (x ⟨0, by omega⟩) with hlt | heq | hgt
      · exact (hnot_prepend p ⟨hlt, hp⟩).elim
      · rw [heq] at hp; exact (lt_irrefl _ hp).elim
      · exact hgt
    · intro p hp
      rcases lt_trichotomy (φ p) (φ (x ⟨n - 1, by omega⟩)) with hlt | heq | hgt
      · exact hlt
      · exact (ne_of_gt hp (hφ_inj heq)).elim
      · exact (hnot_append p ⟨hp, hgt⟩).elim
    · intro p hp
      rcases lt_trichotomy p (x ⟨n - 1, by omega⟩) with hlt | heq | hgt
      · exact hlt
      · rw [heq] at hp; exact (lt_irrefl _ hp).elim
      · exact (hnot_append p ⟨hgt, hp⟩).elim
  · left
    have h_mul_lt : n * (r - 1) < k := by
      have hn_le : n + 1 ≤ M := by omega
      have h1 : (n + 1) * (r - 1) ≤ M * (r - 1) := Nat.mul_le_mul_right (r - 1) hn_le
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm M (r - 1)] at h1
      omega
    have hex_end : ∀ i : Fin k, ∃ N : ℕ, ¬ IsIncEndingAt φ i (N + 1) :=
      fun i => ⟨k, not_isIncEndingAt_succ φ i⟩
    let len (i : Fin k) : ℕ := Nat.find (hex_end i)
    have hlen_not_succ : ∀ i : Fin k, ¬ IsIncEndingAt φ i (len i + 1) :=
      fun i => Nat.find_spec (hex_end i)
    have hlen_pos : ∀ i : Fin k, 1 ≤ len i := by
      intro i
      by_contra hlt
      have h0 : len i = 0 := by omega
      have hnot := hlen_not_succ i
      rw [h0] at hnot
      refine hnot ⟨fun _ => i, fun a b hab => by omega, fun a b hab => by omega, fun _ => rfl⟩
    have hlen_spec : ∀ i : Fin k, IsIncEndingAt φ i (len i) := by
      intro i
      by_contra hnot
      have hp := hlen_pos i
      exact Nat.find_min (hex_end i) (by omega : len i - 1 < len i)
        (by simpa [Nat.sub_add_cancel hp] using hnot)
    have hlen_le_n : ∀ i : Fin k, len i ≤ n := by
      intro i
      by_contra hgt
      obtain ⟨x, hx, hφx, _⟩ := hlen_spec i
      refine hnot_succ ⟨fun j : Fin (n + 1) => x ⟨j.1, by omega⟩,
        fun a b hab => hx (by simp only [Fin.mk_lt_mk]; exact hab),
        fun a b hab => hφx (by simp only [Fin.mk_lt_mk]; exact hab)⟩
    let f (i : Fin k) : ℕ := len i - 1
    have hf_lt_n : ∀ i : Fin k, f i < n := by
      intro i; have := hlen_pos i; have := hlen_le_n i; dsimp [f]; omega
    have huniv_card : (Set.univ : Set (Fin k)).ncard = k := by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    obtain ⟨c, _, hc_card⟩ :=
      exists_fiber_ncard_ge f r n Set.univ (fun i _ => hf_lt_n i) (by rw [huniv_card]; exact
        h_mul_lt)
    obtain ⟨idx, hidx_mono, hidx_mem⟩ :=
      exists_strictMono_mem_of_ncard_ge r {i ∈ (Set.univ : Set (Fin k)) | f i = c} hc_card
    refine ⟨idx, hidx_mono, fun a b hab => ?_⟩
    have hij : idx a < idx b := hidx_mono hab
    have hfa : f (idx a) = c := (hidx_mem a).2
    have hfb : f (idx b) = c := (hidx_mem b).2
    have hlen_eq : len (idx a) = len (idx b) := by
      have := hlen_pos (idx a); have := hlen_pos (idx b)
      dsimp [f] at hfa hfb; omega
    change φ (idx b) < φ (idx a)
    rcases lt_trichotomy (φ (idx a)) (φ (idx b)) with hlt | heq | hgt
    · exfalso
      obtain ⟨x, hx, hφx, hx_end⟩ := hlen_spec (idx a)
      have hp_a := hlen_pos (idx a)
      have hend_a := hx_end hp_a
      refine hlen_not_succ (idx b) ⟨fun j : Fin (len (idx b) + 1) =>
        if hj : j.1 < len (idx a) then x ⟨j.1, hj⟩ else idx b, ?_, ?_, ?_⟩
      · intro u v huv
        by_cases hv_lt : v.1 < len (idx a)
        · have hu_lt : u.1 < len (idx a) := Nat.lt_trans huv hv_lt
          simp only [hu_lt, hv_lt, ↓reduceDIte]
          exact hx huv
        · have hu_lt : u.1 < len (idx a) := by omega
          simp only [hu_lt, hv_lt, ↓reduceDIte]
          rcases eq_or_lt_of_le (by omega : u.1 ≤ len (idx a) - 1) with heq_u | hlt_u
          · have h_eq : (⟨u.1, hu_lt⟩ : Fin (len (idx a))) = ⟨len (idx a) - 1, by omega⟩ := by
              ext; dsimp; omega
            rw [h_eq, hend_a]; exact hij
          · have h_step : x ⟨u.1, hu_lt⟩ < x ⟨len (idx a) - 1, by omega⟩ :=
              hx (by simp only [Fin.mk_lt_mk]; exact hlt_u)
            rw [hend_a] at h_step
            exact lt_trans h_step hij
      · intro u v huv
        change φ _ < φ _
        by_cases hv_lt : v.1 < len (idx a)
        · have hu_lt : u.1 < len (idx a) := Nat.lt_trans huv hv_lt
          simp only [hu_lt, hv_lt, ↓reduceDIte]
          exact hφx huv
        · have hu_lt : u.1 < len (idx a) := by omega
          simp only [hu_lt, hv_lt, ↓reduceDIte]
          rcases eq_or_lt_of_le (by omega : u.1 ≤ len (idx a) - 1) with heq_u | hlt_u
          · have h_eq : (⟨u.1, hu_lt⟩ : Fin (len (idx a))) = ⟨len (idx a) - 1, by omega⟩ := by
              ext; dsimp; omega
            rw [h_eq, hend_a]; exact hlt
          · have h_step : φ (x ⟨u.1, hu_lt⟩) < φ (x ⟨len (idx a) - 1, by omega⟩) :=
              hφx (by simp only [Fin.mk_lt_mk]; exact hlt_u)
            rw [hend_a] at h_step
            exact lt_trans h_step hlt
      · intro _
        have hnot_lt : ¬ (len (idx b) < len (idx a)) := by omega
        simp [hnot_lt]
    · exact (ne_of_lt hij (hφ_inj heq)).elim
    · exact hgt

/-! ## Construction of Crosscaps, Leaps, and Doublecrosses from Index Configurations -/

/-- A decreasing subsequence `idx : Fin r → Fin k` of `φ` yields a crosscap transaction of size `r`.
-/
theorem exists_crosscap_of_decreasing
    {P_set : Set (Graph α β)} (hdisj : S.IsDisjointOmegaPathSet P_set)
    {k r : ℕ} (hr : 2 ≤ r)
    {L : List α} (hL_len : L.length = 2 * k) (hL_cw : S.Ω.IsClockwiseSeq L)
    {R : Fin k → Graph α β} (hR_inj : Function.Injective R) (hR_sub : range R ⊆ P_set)
    {φ : Fin k → Fin k}
    (hR_ends : ∀ i : Fin k, S.IsOmegaPathWithEnds (R i)
      (L[k - 1 - i.1]'(by omega)) (L[k + (φ i).1]'(by omega)))
    (idx : Fin r → Fin k) (hidx_mono : StrictMono idx) (hφ_anti : StrictAnti (φ ∘ idx)) :
    ∃ P_set' ⊆ P_set, P_set'.ncard = r ∧ S.IsCrosscapTransaction P_set' := by
  let P' (j : Fin r) : Graph α β := R (idx j)
  let fa (j : Fin r) : ℕ := k - 1 - (idx j).1
  let fb (j : Fin r) : ℕ := k + (φ (idx j)).1
  have hfa_lt : ∀ j : Fin r, fa j < L.length := fun j => by dsimp [fa]; omega
  have hfb_lt : ∀ j : Fin r, fb j < L.length := fun j => by dsimp [fb]; omega
  let a' (j : Fin r) : α := L[fa j]'(hfa_lt j)
  let b' (j : Fin r) : α := L[fb j]'(hfb_lt j)
  have hfa_anti : StrictAnti fa := by
    intro i j hij
    have hlt : (idx i).1 < (idx j).1 := hidx_mono hij
    have := (idx j).2
    dsimp [fa]; omega
  have hfb_anti : StrictAnti fb := by
    intro i j hij
    have hlt : (φ (idx j)).1 < (φ (idx i)).1 := hφ_anti hij
    dsimp [fb]; omega
  have hsub_a : CyclicPerm.IsBoundedSubseq L ((List.ofFn a').reverse) 0 k :=
    CyclicPerm.IsBoundedSubseq.ofFn_reverse_strictAnti L (by omega) fa hfa_lt
      (fun j => Nat.zero_le _) (fun j => by dsimp [fa]; omega) hfa_anti
  have hsub_b : CyclicPerm.IsBoundedSubseq L ((List.ofFn b').reverse) k (2 * k) :=
    CyclicPerm.IsBoundedSubseq.ofFn_reverse_strictAnti L (by omega) fb hfb_lt
      (fun j => by dsimp [fb]; omega) (fun j => by have := (φ (idx j)).2; dsimp [fb]; omega)
        hfb_anti
  have hcw : S.Ω.IsClockwiseSeq ((List.ofFn a').reverse ++ (List.ofFn b').reverse) :=
    hL_cw.of_isBoundedSubseq (hsub_a.append hsub_b)
  have hP'_inj : Function.Injective P' := hR_inj.comp hidx_mono.injective
  have hP'_sub : range P' ⊆ P_set := by
    rintro _ ⟨j, rfl⟩; exact hR_sub ⟨idx j, rfl⟩
  obtain ⟨hsub, hcard, hcross⟩ :=
    S.exists_crosscap_of_isClockwiseSeq hdisj hr P' a' b' hP'_inj hP'_sub
      (fun j => hR_ends (idx j)) hcw
  exact ⟨range P', hsub, hcard, hcross⟩

/-- Leap construction (Type A): `p < q 0` and `φ (q (s - 2)) < φ p`. -/
theorem exists_leap_typeA
    {P_set : Set (Graph α β)} (hdisj : S.IsDisjointOmegaPathSet P_set)
    {k s : ℕ} (hs : 3 ≤ s)
    {L : List α} (hL_len : L.length = 2 * k) (hL_cw : S.Ω.IsClockwiseSeq L)
    {R : Fin k → Graph α β} (hR_inj : Function.Injective R) (hR_sub : range R ⊆ P_set)
    {φ : Fin k → Fin k}
    (hR_ends : ∀ i : Fin k, S.IsOmegaPathWithEnds (R i)
      (L[k - 1 - i.1]'(by omega)) (L[k + (φ i).1]'(by omega)))
    (q : Fin (s - 1) → Fin k) (hq_mono : StrictMono q) (hφq_mono : StrictMono (φ ∘ q))
    (p : Fin k) (hp_lt : p < q ⟨0, by omega⟩) (hφp_gt : φ (q ⟨s - 2, by omega⟩) < φ p) :
    ∃ P_set' ⊆ P_set, P_set'.ncard = s ∧ S.IsLeapTransaction P_set' := by
  let idx (i : Fin s) : Fin k := if hi0 : i.1 = 0 then p else q ⟨i.1 - 1, by omega⟩
  have hidx_mono : StrictMono idx := by
    intro i j hij
    by_cases hi0 : i.1 = 0
    · have hj0 : j.1 ≠ 0 := by omega
      simp only [idx, hi0, hj0, ↓reduceDIte]
      rcases eq_or_lt_of_le (Nat.zero_le (j.1 - 1)) with h0 | hpos
      · have h_eq : (⟨j.1 - 1, by omega⟩ : Fin (s - 1)) = ⟨0, by omega⟩ := by ext; dsimp; omega
        rw [h_eq]; exact hp_lt
      · exact lt_trans hp_lt (hq_mono (by simp only [Fin.mk_lt_mk]; omega))
    · have hj0 : j.1 ≠ 0 := by omega
      simp only [idx, hi0, hj0, ↓reduceDIte]
      exact hq_mono (by simp only [Fin.mk_lt_mk]; omega)
  let P' (i : Fin s) : Graph α β := R (idx i)
  let fa (i : Fin s) : ℕ := k - 1 - (idx i).1
  have hfa_lt : ∀ i : Fin s, fa i < L.length := fun i => by dsimp [fa]; omega
  let a' (i : Fin s) : α := L[fa i]'(hfa_lt i)
  let b' (i : Fin s) : α := L[k + (φ (idx i)).1]'(by omega)
  have hfa_anti : StrictAnti fa := by
    intro i j hij
    have hlt : (idx i).1 < (idx j).1 := hidx_mono hij
    have := (idx j).2
    dsimp [fa]; omega
  have hsub_a : CyclicPerm.IsBoundedSubseq L ((List.ofFn a').reverse) 0 k :=
    CyclicPerm.IsBoundedSubseq.ofFn_reverse_strictAnti L (by omega) fa hfa_lt
      (fun i => Nat.zero_le _) (fun i => by dsimp [fa]; omega) hfa_anti
  let fb_mid (i : Fin (s - 1)) : ℕ := k + (φ (q i)).1
  have hfb_mid_lt : ∀ i : Fin (s - 1), fb_mid i < L.length := fun i => by dsimp [fb_mid]; omega
  have hfb_mid_hi : ∀ i : Fin (s - 1), fb_mid i < k + (φ p).1 := by
    intro i
    have hi_le : i ≤ ⟨s - 2, by omega⟩ := by change i.1 ≤ s - 2; omega
    have hle : (φ (q i)).1 ≤ (φ (q ⟨s - 2, by omega⟩)).1 := hφq_mono.monotone hi_le
    have hlt : (φ (q ⟨s - 2, by omega⟩)).1 < (φ p).1 := hφp_gt
    dsimp [fb_mid]; omega
  have hfb_mid_mono : StrictMono fb_mid := by
    intro i j hij
    have hlt : (φ (q i)).1 < (φ (q j)).1 := hφq_mono hij
    dsimp [fb_mid]; omega
  have h_mid_eq : List.ofFn (fun i : Fin (s - 1) => b' ⟨i.1 + 1, by omega⟩) =
      List.ofFn (fun i : Fin (s - 1) => L[fb_mid i]'(hfb_mid_lt i)) := by
    simp [b', idx, fb_mid]
  have hsub_b_mid : CyclicPerm.IsBoundedSubseq L
      (List.ofFn (fun i : Fin (s - 1) => b' ⟨i.1 + 1, by omega⟩)) k (k + (φ p).1) := by
    rw [h_mid_eq]
    exact CyclicPerm.IsBoundedSubseq.ofFn_strictMono L (by omega) fb_mid hfb_mid_lt
      (fun i => by dsimp [fb_mid]; omega) hfb_mid_hi hfb_mid_mono
  have h_b0_eq : b' ⟨0, by omega⟩ = L[k + (φ p).1]'(by omega) := by
    simp [b', idx]
  have hsub_b0 : CyclicPerm.IsBoundedSubseq L [b' ⟨0, by omega⟩] (k + (φ p).1) (2 * k) := by
    rw [h_b0_eq]
    exact CyclicPerm.IsBoundedSubseq.singleton L (by omega) le_rfl
      (by have := (φ p).2; omega)
  have hcw : S.Ω.IsClockwiseSeq
      ((List.ofFn a').reverse ++
        List.ofFn (fun i : Fin (s - 1) => b' ⟨i.1 + 1, by omega⟩) ++
        [b' ⟨0, by omega⟩]) :=
    hL_cw.of_isBoundedSubseq ((hsub_a.append hsub_b_mid).append hsub_b0)
  have hP'_inj : Function.Injective P' := hR_inj.comp hidx_mono.injective
  have hP'_sub : range P' ⊆ P_set := by
    rintro _ ⟨i, rfl⟩; exact hR_sub ⟨idx i, rfl⟩
  obtain ⟨hsub, hcard, hleap⟩ :=
    S.exists_leap_of_isClockwiseSeq hdisj hs P' a' b' hP'_inj hP'_sub
      (fun i => hR_ends (idx i)) hcw
  exact ⟨range P', hsub, hcard, hleap⟩

/-- Leap construction (Type B): `q (s - 2) < p` and `φ p < φ (q 0)`. -/
theorem exists_leap_typeB
    {P_set : Set (Graph α β)} (hdisj : S.IsDisjointOmegaPathSet P_set)
    {k s : ℕ} (hs : 3 ≤ s)
    {L : List α} (hL_len : L.length = 2 * k) (hL_cw : S.Ω.IsClockwiseSeq L)
    {R : Fin k → Graph α β} (hR_inj : Function.Injective R) (hR_sub : range R ⊆ P_set)
    {φ : Fin k → Fin k}
    (hR_ends : ∀ i : Fin k, S.IsOmegaPathWithEnds (R i)
      (L[k - 1 - i.1]'(by omega)) (L[k + (φ i).1]'(by omega)))
    (q : Fin (s - 1) → Fin k) (hq_mono : StrictMono q) (hφq_mono : StrictMono (φ ∘ q))
    (p : Fin k) (hp_gt : q ⟨s - 2, by omega⟩ < p) (hφp_lt : φ p < φ (q ⟨0, by omega⟩)) :
    ∃ P_set' ⊆ P_set, P_set'.ncard = s ∧ S.IsLeapTransaction P_set' := by
  let idx (i : Fin s) : Fin k := if hi0 : i.1 = 0 then p else q ⟨i.1 - 1, by omega⟩
  have hq_lt_p : ∀ j : Fin (s - 1), q j < p := by
    intro j
    have hj_le : j ≤ ⟨s - 2, by omega⟩ := by change j.1 ≤ s - 2; omega
    exact lt_of_le_of_lt (hq_mono.monotone hj_le) hp_gt
  have hidx_inj : Function.Injective idx := by
    intro i j hij
    by_cases hi0 : i.1 = 0
    · by_cases hj0 : j.1 = 0
      · ext; omega
      · simp only [idx, hi0, hj0, ↓reduceDIte] at hij
        exact (ne_of_gt (hq_lt_p ⟨j.1 - 1, by omega⟩) hij).elim
    · by_cases hj0 : j.1 = 0
      · simp only [idx, hi0, hj0, ↓reduceDIte] at hij
        exact (ne_of_lt (hq_lt_p ⟨i.1 - 1, by omega⟩) hij).elim
      · simp only [idx, hi0, hj0, ↓reduceDIte] at hij
        have heq := hq_mono.injective hij
        ext; have := congrArg Fin.val heq; dsimp at this; omega
  let P' (i : Fin s) : Graph α β := R (idx i)
  let a' (i : Fin s) : α :=
    if hi0 : i.1 = 0 then L[k + (φ p).1]'(by omega)
    else L[k - 1 - (q ⟨i.1 - 1, by omega⟩).1]'(by omega)
  let b' (i : Fin s) : α :=
    if hi0 : i.1 = 0 then L[k - 1 - p.1]'(by omega)
    else L[k + (φ (q ⟨i.1 - 1, by omega⟩)).1]'(by omega)
  have hends' : ∀ i : Fin s, S.IsOmegaPathWithEnds (P' i) (a' i) (b' i) := by
    intro i
    by_cases hi0 : i.1 = 0
    · simp only [P', idx, a', b', hi0, ↓reduceDIte]
      exact (hR_ends p).symm S
    · simp only [P', idx, a', b', hi0, ↓reduceDIte]
      exact hR_ends (q ⟨i.1 - 1, by omega⟩)
  let fa_q (j : Fin (s - 1)) : ℕ := k - 1 - (q j).1
  have hfa_q_lt : ∀ j : Fin (s - 1), fa_q j < L.length := fun j => by dsimp [fa_q]; omega
  let fb_q (j : Fin (s - 1)) : ℕ := k + (φ (q j)).1
  have hfb_q_lt : ∀ j : Fin (s - 1), fb_q j < L.length := fun j => by dsimp [fb_q]; omega
  have h_a_rev_eq : (List.ofFn a').reverse =
      (List.ofFn (fun j : Fin (s - 1) => L[fa_q j]'(hfa_q_lt j))).reverse ++
        [L[k + (φ p).1]'(by omega)] := by
    have h_a_eq : List.ofFn a' =
        [L[k + (φ p).1]'(by omega)] ++
          List.ofFn (fun j : Fin (s - 1) => L[fa_q j]'(hfa_q_lt j)) := by
      apply List.ext_getElem
      · simp; omega
      · intro i hi₁ hi₂
        rcases Nat.eq_zero_or_pos i with rfl | hi_pos
        · simp [a']
        · rw [List.getElem_ofFn, List.getElem_append_right (by simp; omega)]
          simp [a', Nat.ne_of_gt hi_pos, fa_q]
    rw [h_a_eq, List.reverse_append, List.reverse_singleton]
  have h_b_mid_eq : List.ofFn (fun j : Fin (s - 1) => b' ⟨j.1 + 1, by omega⟩) =
      List.ofFn (fun j : Fin (s - 1) => L[fb_q j]'(hfb_q_lt j)) := by
    simp [b', fb_q]
  have h_b0_eq : b' ⟨0, by omega⟩ = L[k - 1 - p.1]'(by omega) := by
    simp [b']
  let mid₁ := k - 1 - (q ⟨s - 2, by omega⟩).1
  let mid₂ := k + (φ (q ⟨0, by omega⟩)).1
  have hsub_1 : CyclicPerm.IsBoundedSubseq L [L[k - 1 - p.1]'(by omega)] 0 mid₁ :=
    CyclicPerm.IsBoundedSubseq.singleton L (by omega) (Nat.zero_le _)
      (by have : (q ⟨s - 2, by omega⟩).1 < p.1 := hp_gt; have := p.2; dsimp [mid₁]; omega)
  have hsub_2 : CyclicPerm.IsBoundedSubseq L
      ((List.ofFn (fun j : Fin (s - 1) => L[fa_q j]'(hfa_q_lt j))).reverse) mid₁ k := by
    refine CyclicPerm.IsBoundedSubseq.ofFn_reverse_strictAnti L (by dsimp [mid₁]; omega)
      fa_q hfa_q_lt (fun j => ?_) (fun j => by dsimp [fa_q]; omega) (fun i j hij => ?_)
    · have hj_le : j ≤ ⟨s - 2, by omega⟩ := by change j.1 ≤ s - 2; omega
      have : (q j).1 ≤ (q ⟨s - 2, by omega⟩).1 := hq_mono.monotone hj_le
      have := (q ⟨s - 2, by omega⟩).2
      dsimp [mid₁, fa_q]; omega
    · have : (q i).1 < (q j).1 := hq_mono hij
      have := (q j).2
      dsimp [fa_q]; omega
  have hsub_3 : CyclicPerm.IsBoundedSubseq L [L[k + (φ p).1]'(by omega)] k mid₂ :=
    CyclicPerm.IsBoundedSubseq.singleton L (by omega) (by omega)
      (by have : (φ p).1 < (φ (q ⟨0, by omega⟩)).1 := hφp_lt; dsimp [mid₂]; omega)
  have hsub_4 : CyclicPerm.IsBoundedSubseq L
      (List.ofFn (fun j : Fin (s - 1) => L[fb_q j]'(hfb_q_lt j))) mid₂ (2 * k) := by
    refine CyclicPerm.IsBoundedSubseq.ofFn_strictMono L
      (by have := (φ (q ⟨0, by omega⟩)).2; dsimp [mid₂]; omega)
      fb_q hfb_q_lt (fun j => ?_) (fun j => by have := (φ (q j)).2; dsimp [fb_q]; omega)
      (fun i j hij => ?_)
    · have hj_ge : (⟨0, by omega⟩ : Fin (s - 1)) ≤ j := by change 0 ≤ j.1; omega
      have : (φ (q ⟨0, by omega⟩)).1 ≤ (φ (q j)).1 := hφq_mono.monotone hj_ge
      dsimp [mid₂, fb_q]; omega
    · have : (φ (q i)).1 < (φ (q j)).1 := hφq_mono hij
      dsimp [fb_q]; omega
  have hcw_rot : S.Ω.IsClockwiseSeq
      ([b' ⟨0, by omega⟩] ++
        ((List.ofFn a').reverse ++
          List.ofFn (fun j : Fin (s - 1) => b' ⟨j.1 + 1, by omega⟩))) := by
    rw [h_b0_eq, h_a_rev_eq, h_b_mid_eq, ← List.append_assoc, ← List.append_assoc]
    exact hL_cw.of_isBoundedSubseq (((hsub_1.append hsub_2).append hsub_3).append hsub_4)
  have hcw : S.Ω.IsClockwiseSeq
      ((List.ofFn a').reverse ++
        List.ofFn (fun j : Fin (s - 1) => b' ⟨j.1 + 1, by omega⟩) ++
        [b' ⟨0, by omega⟩]) :=
    hcw_rot.append_comm
  have hP'_inj : Function.Injective P' := hR_inj.comp hidx_inj
  have hP'_sub : range P' ⊆ P_set := by
    rintro _ ⟨i, rfl⟩; exact hR_sub ⟨idx i, rfl⟩
  obtain ⟨hsub, hcard, hleap⟩ :=
    S.exists_leap_of_isClockwiseSeq hdisj hs P' a' b' hP'_inj hP'_sub hends' hcw
  exact ⟨range P', hsub, hcard, hleap⟩

/-- Doublecross construction from crossed end pairs `(u₀, u₁)` and `(v₀, v₁)` around the middle
increasing subsequence `x ⟨s - 2, _⟩, …, x ⟨s + t - 7, _⟩`. -/
theorem exists_doublecross_of_ends
    {P_set : Set (Graph α β)} (hdisj : S.IsDisjointOmegaPathSet P_set)
    {k s t n : ℕ} (hs : 3 ≤ s) (ht : 4 ≤ t) (hn : 2 * s + t - 7 ≤ n)
    {L : List α} (hL_len : L.length = 2 * k) (hL_cw : S.Ω.IsClockwiseSeq L)
    {R : Fin k → Graph α β} (hR_inj : Function.Injective R) (hR_sub : range R ⊆ P_set)
    {φ : Fin k → Fin k}
    (hR_ends : ∀ i : Fin k, S.IsOmegaPathWithEnds (R i)
      (L[k - 1 - i.1]'(by omega)) (L[k + (φ i).1]'(by omega)))
    (x : Fin n → Fin k) (hx_mono : StrictMono x) (hφx_mono : StrictMono (φ ∘ x))
    (u₀ u₁ : Fin k) (hu_lt : u₀ < u₁) (hu₁_lt : u₁ < x ⟨s - 2, by omega⟩)
    (hφu_lt : φ u₁ < φ u₀) (hφu₀_lt : φ u₀ < φ (x ⟨s - 2, by omega⟩))
    (v₀ v₁ : Fin k) (hv₀_gt : x ⟨n - s + 1, by omega⟩ < v₀) (hv_lt : v₀ < v₁)
    (hφv₁_gt : φ (x ⟨n - s + 1, by omega⟩) < φ v₁) (hφv_lt : φ v₁ < φ v₀) :
    ∃ P_set' ⊆ P_set, P_set'.ncard = t ∧ S.IsDoublecrossTransaction P_set' := by
  let idx (i : Fin t) : Fin k :=
    if i.1 = 0 then u₀
    else if i.1 = 1 then u₁
    else if hlt : i.1 < t - 2 then x ⟨s - 2 + (i.1 - 2), by omega⟩
    else if i.1 = t - 2 then v₀
    else v₁
  have hidx_0 : ∀ i : Fin t, i.1 = 0 → idx i = u₀ := fun i h => by
    dsimp [idx]; split_ifs; rfl
  have hidx_1 : ∀ i : Fin t, i.1 = 1 → idx i = u₁ := fun i h => by
    dsimp [idx]; split_ifs <;> first | rfl | omega
  have hidx_mid : ∀ (i : Fin t) (h2 : 2 ≤ i.1) (hlt : i.1 < t - 2),
      idx i = x ⟨s - 2 + (i.1 - 2), by omega⟩ := fun i h2 hlt => by
    dsimp [idx]; split_ifs <;> first | rfl | omega
  have hidx_t2 : ∀ i : Fin t, i.1 = t - 2 → idx i = v₀ := fun i h => by
    dsimp [idx]; split_ifs <;> first | rfl | omega
  have hidx_t1 : ∀ i : Fin t, i.1 = t - 1 → idx i = v₁ := fun i h => by
    dsimp [idx]; split_ifs <;> first | rfl | omega
  have hx_bot_lt_v₀ : x ⟨s - 2, by omega⟩ < v₀ := by
    have hle : (⟨s - 2, by omega⟩ : Fin n) ≤ ⟨n - s + 1, by omega⟩ := by
      change s - 2 ≤ n - s + 1; omega
    exact lt_of_le_of_lt (hx_mono.monotone hle) hv₀_gt
  have hu₁_lt_v₀ : u₁ < v₀ := lt_trans hu₁_lt hx_bot_lt_v₀
  have hu₁_lt_v₁ : u₁ < v₁ := lt_trans hu₁_lt_v₀ hv_lt
  have hu₀_lt_v₀ : u₀ < v₀ := lt_trans hu_lt hu₁_lt_v₀
  have hu₀_lt_v₁ : u₀ < v₁ := lt_trans hu_lt hu₁_lt_v₁
  have hx_mid_lt_v₀ : ∀ m : ℕ, (hm : 2 ≤ m) → (hmt : m < t - 2) →
      x ⟨s - 2 + (m - 2), by omega⟩ < v₀ := by
    intro m hm hmt
    have hle : (⟨s - 2 + (m - 2), by omega⟩ : Fin n) ≤ ⟨n - s + 1, by omega⟩ := by
      change s - 2 + (m - 2) ≤ n - s + 1; omega
    exact lt_of_le_of_lt (hx_mono.monotone hle) hv₀_gt
  have hu₁_lt_x_mid : ∀ m : ℕ, (hm : 2 ≤ m) → (hmt : m < t - 2) →
      u₁ < x ⟨s - 2 + (m - 2), by omega⟩ := by
    intro m hm hmt
    have hle : (⟨s - 2, by omega⟩ : Fin n) ≤ ⟨s - 2 + (m - 2), by omega⟩ := by
      change s - 2 ≤ s - 2 + (m - 2); omega
    exact lt_of_lt_of_le hu₁_lt (hx_mono.monotone hle)
  have hφx_mid_lt_v₁ : ∀ m : ℕ, (hm : m < t - 4) → φ (x ⟨s - 2 + m, by omega⟩) < φ v₁ := by
    intro m hm
    have hle : (⟨s - 2 + m, by omega⟩ : Fin n) ≤ ⟨n - s + 1, by omega⟩ := by
      change s - 2 + m ≤ n - s + 1; omega
    exact lt_of_le_of_lt (hφx_mono.monotone hle) hφv₁_gt
  have hidx_mono : StrictMono idx := by
    intro i j hij
    have hij_val : i.1 < j.1 := hij
    have hi_t : i.1 < t := i.2
    have hj_t : j.1 < t := j.2
    by_cases hi0 : i.1 = 0
    · rw [hidx_0 i hi0]
      by_cases hj1 : j.1 = 1
      · rw [hidx_1 j hj1]; exact hu_lt
      · by_cases hjlt : j.1 < t - 2
        · rw [hidx_mid j (by omega) hjlt]
          exact lt_trans hu_lt (hu₁_lt_x_mid j.1 (by omega) hjlt)
        · by_cases hj2 : j.1 = t - 2
          · rw [hidx_t2 j hj2]; exact hu₀_lt_v₀
          · rw [hidx_t1 j (by omega)]; exact hu₀_lt_v₁
    · by_cases hi1 : i.1 = 1
      · rw [hidx_1 i hi1]
        by_cases hjlt : j.1 < t - 2
        · rw [hidx_mid j (by omega) hjlt]
          exact hu₁_lt_x_mid j.1 (by omega) hjlt
        · by_cases hj2 : j.1 = t - 2
          · rw [hidx_t2 j hj2]; exact hu₁_lt_v₀
          · rw [hidx_t1 j (by omega)]; exact hu₁_lt_v₁
      · by_cases hilt : i.1 < t - 2
        · rw [hidx_mid i (by omega) hilt]
          by_cases hjlt : j.1 < t - 2
          · rw [hidx_mid j (by omega) hjlt]
            exact hx_mono (by change s - 2 + (i.1 - 2) < s - 2 + (j.1 - 2); omega)
          · by_cases hj2 : j.1 = t - 2
            · rw [hidx_t2 j hj2]
              exact hx_mid_lt_v₀ i.1 (by omega) hilt
            · rw [hidx_t1 j (by omega)]
              exact lt_trans (hx_mid_lt_v₀ i.1 (by omega) hilt) hv_lt
        · rw [hidx_t2 i (by omega), hidx_t1 j (by omega)]
          exact hv_lt
  let P' (i : Fin t) : Graph α β := R (idx i)
  let fa (i : Fin t) : ℕ := k - 1 - (idx i).1
  have hfa_lt : ∀ i : Fin t, fa i < L.length := fun i => by dsimp [fa]; omega
  let a' (i : Fin t) : α := L[fa i]'(hfa_lt i)
  let b' (i : Fin t) : α := L[k + (φ (idx i)).1]'(by omega)
  have hfa_anti : StrictAnti fa := by
    intro i j hij
    have hlt : (idx i).1 < (idx j).1 := hidx_mono hij
    have := (idx j).2
    dsimp [fa]; omega
  have hsub_a : CyclicPerm.IsBoundedSubseq L ((List.ofFn a').reverse) 0 k :=
    CyclicPerm.IsBoundedSubseq.ofFn_reverse_strictAnti L (by omega) fa hfa_lt
      (fun i => Nat.zero_le _) (fun i => by dsimp [fa]; omega) hfa_anti
  let m1 : ℕ := k + (φ (x ⟨s - 2, by omega⟩)).1
  let m2 : ℕ := k + (φ v₁).1
  have h_b10_eq : [b' ⟨1, by omega⟩, b' ⟨0, by omega⟩] =
      [L[k + (φ u₁).1]'(by omega), L[k + (φ u₀).1]'(by omega)] := by
    have h1 : idx ⟨1, by omega⟩ = u₁ := hidx_1 ⟨1, by omega⟩ rfl
    have h0 : idx ⟨0, by omega⟩ = u₀ := hidx_0 ⟨0, by omega⟩ rfl
    simp [b', h1, h0]
  have hsub_b10 : CyclicPerm.IsBoundedSubseq L [b' ⟨1, by omega⟩, b' ⟨0, by omega⟩] k m1 := by
    rw [h_b10_eq]
    refine CyclicPerm.IsBoundedSubseq.pair L (by omega) (by omega)
      (by omega) (by have : (φ u₁).1 < (φ u₀).1 := hφu_lt; omega)
      (by have : (φ u₀).1 < (φ (x ⟨s - 2, by omega⟩)).1 := hφu₀_lt; dsimp [m1]; omega)
  let fb_mid (j : Fin (t - 4)) : ℕ := k + (φ (x ⟨s - 2 + j.1, by omega⟩)).1
  have hfb_mid_lt : ∀ j : Fin (t - 4), fb_mid j < L.length := fun j => by dsimp [fb_mid]; omega
  have h_mid_eq : List.ofFn (fun j : Fin (t - 4) => b' ⟨j.1 + 2, by omega⟩) =
      List.ofFn (fun j : Fin (t - 4) => L[fb_mid j]'(hfb_mid_lt j)) := by
    congr 1; funext j
    have hj_lt : j.1 + 2 < t - 2 := by have := j.2; omega
    have hj_idx : idx ⟨j.1 + 2, by omega⟩ = x ⟨s - 2 + j.1, by omega⟩ :=
      hidx_mid ⟨j.1 + 2, by omega⟩ (by dsimp; omega) hj_lt
    simp [b', hj_idx, fb_mid]
  have hsub_b_mid : CyclicPerm.IsBoundedSubseq L
      (List.ofFn (fun j : Fin (t - 4) => b' ⟨j.1 + 2, by omega⟩)) m1 m2 := by
    rw [h_mid_eq]
    refine CyclicPerm.IsBoundedSubseq.ofFn_strictMono L
      (by have hle : (⟨s - 2, by omega⟩ : Fin n) ≤ ⟨n - s + 1, by omega⟩ := by
            change s - 2 ≤ n - s + 1; omega
          have : (φ (x ⟨s - 2, by omega⟩)).1 ≤ (φ (x ⟨n - s + 1, by omega⟩)).1 :=
            hφx_mono.monotone hle
          have : (φ (x ⟨n - s + 1, by omega⟩)).1 < (φ v₁).1 := hφv₁_gt
          dsimp [m1, m2]; omega)
      fb_mid hfb_mid_lt (fun j => ?_) (fun j => ?_) (fun i j hij => ?_)
    · have hle : (⟨s - 2, by omega⟩ : Fin n) ≤ ⟨s - 2 + j.1, by omega⟩ := by
        change s - 2 ≤ s - 2 + j.1; omega
      have : (φ (x ⟨s - 2, by omega⟩)).1 ≤ (φ (x ⟨s - 2 + j.1, by omega⟩)).1 :=
        hφx_mono.monotone hle
      dsimp [m1, fb_mid]; omega
    · have : (φ (x ⟨s - 2 + j.1, by omega⟩)).1 < (φ v₁).1 := hφx_mid_lt_v₁ j.1 j.2
      dsimp [m2, fb_mid]; omega
    · have hlt : (⟨s - 2 + i.1, by omega⟩ : Fin n) < ⟨s - 2 + j.1, by omega⟩ := by
        change s - 2 + i.1 < s - 2 + j.1; exact Nat.add_lt_add_left hij _
      have : (φ (x ⟨s - 2 + i.1, by omega⟩)).1 < (φ (x ⟨s - 2 + j.1, by omega⟩)).1 :=
        hφx_mono hlt
      dsimp [fb_mid]; omega
  have h_bt_eq : [b' ⟨t - 1, by omega⟩, b' ⟨t - 2, by omega⟩] =
      [L[k + (φ v₁).1]'(by omega), L[k + (φ v₀).1]'(by omega)] := by
    have ht1 : idx ⟨t - 1, by omega⟩ = v₁ := hidx_t1 ⟨t - 1, by omega⟩ rfl
    have ht2 : idx ⟨t - 2, by omega⟩ = v₀ := hidx_t2 ⟨t - 2, by omega⟩ rfl
    simp [b', ht1, ht2]
  have hsub_bt : CyclicPerm.IsBoundedSubseq L [b' ⟨t - 1, by omega⟩, b' ⟨t - 2, by omega⟩] m2
    (2 * k) := by
    rw [h_bt_eq]
    refine CyclicPerm.IsBoundedSubseq.pair L (by omega) (by omega)
      (by dsimp [m2]; omega) (by have : (φ v₁).1 < (φ v₀).1 := hφv_lt; omega)
      (by have := (φ v₀).2; omega)
  have hcw : S.Ω.IsClockwiseSeq
      ((List.ofFn a').reverse ++
        [b' ⟨1, by omega⟩, b' ⟨0, by omega⟩] ++
        List.ofFn (fun j : Fin (t - 4) => b' ⟨j.1 + 2, by omega⟩) ++
        [b' ⟨t - 1, by omega⟩, b' ⟨t - 2, by omega⟩]) :=
    hL_cw.of_isBoundedSubseq (((hsub_a.append hsub_b10).append hsub_b_mid).append hsub_bt)
  have hP'_inj : Function.Injective P' := hR_inj.comp hidx_mono.injective
  have hP'_sub : range P' ⊆ P_set := by
    rintro _ ⟨i, rfl⟩; exact hR_sub ⟨idx i, rfl⟩
  obtain ⟨hsub, hcard, hdc⟩ :=
    S.exists_doublecross_of_isClockwiseSeq hdisj ht P' a' b' hP'_inj hP'_sub
      (fun i => hR_ends (idx i)) hcw
  exact ⟨range P', hsub, hcard, hdc⟩

/-! ## Proof of Theorem (7.1) -/

/-- **Graph Minors IX, (7.1)** (page 59):
"Let $r \ge 2$, $s \ge 3$, $t \ge 4$ be integers. Let $\mathcal{P}$ be a crooked transaction
in $(G, \Omega)$ such that $|\mathcal{P}| \ge (r - 1)(2s + t - 7)$. Then there exists
$\mathcal{P}' \subseteq \mathcal{P}$ such that either* (i) *|\mathcal{P}'| = r and
\mathcal{P}' is a crosscap, or* (ii) *|\mathcal{P}'| = s and \mathcal{P}' is a leap, or*
(iii) *|\mathcal{P}'| = t and \mathcal{P}' is a doublecross." -/
theorem theorem_7_1_proof
    {P_set : Set (Graph α β)}
    {r s t : ℕ} (hr : 2 ≤ r) (hs : 3 ≤ s) (ht : 4 ≤ t)
    (hcrooked : S.IsCrookedTransaction P_set)
    (hcard : (r - 1) * (2 * s + t - 7) ≤ P_set.ncard) :
    ∃ P_set' ⊆ P_set,
      (P_set'.ncard = r ∧ S.IsCrosscapTransaction P_set') ∨
      (P_set'.ncard = s ∧ S.IsLeapTransaction P_set') ∨
      (P_set'.ncard = t ∧ S.IsDoublecrossTransaction P_set') := by
  obtain ⟨A_orig, B_orig, hfence_orig⟩ := hcrooked.1
  have hdisj : S.IsDisjointOmegaPathSet P_set := hfence_orig.1
  let k := P_set.ncard
  have hk_ge : (r - 1) * (2 * s + t - 7) ≤ k := hcard
  have hk_ge2 : 2 ≤ k := by
    have : 1 * 3 ≤ (r - 1) * (2 * s + t - 7) := Nat.mul_le_mul (by omega) (by omega)
    omega
  obtain ⟨L, hL_len, R, φ, hL_cw, hR_inj, hR_sub, hφ_inj, hφ_surj, hR_ends, hφ_0, hφ_last⟩ :=
    S.exists_clockwise_enumeration_of_crooked hcrooked rfl (by omega)
  rcases exists_decreasing_or_max_increasing hr (by omega : 1 ≤ 2 * s + t - 7) (by omega : 1 ≤ k)
      φ hφ_inj hk_ge with
    ⟨idx, hidx_mono, hφ_anti⟩ |
    ⟨n, hn, x, hx_mono, hφx_mono, hno_before_lt, hno_before_φ, hno_after_gt, hno_after_φ⟩
  · obtain ⟨P_set', hsub, hncard, hcross⟩ :=
      S.exists_crosscap_of_decreasing hdisj hr hL_len hL_cw hR_inj hR_sub hR_ends
        idx hidx_mono hφ_anti
    exact ⟨P_set', hsub, Or.inl ⟨hncard, hcross⟩⟩
  · -- First analyze the bottom end (`x 0` and `x (s - 2)`)
    have hbottom :
        (∃ P_set' ⊆ P_set, P_set'.ncard = s ∧ S.IsLeapTransaction P_set') ∨
        ∃ u₀ u₁ : Fin k, u₀ < u₁ ∧ u₁ < x ⟨s - 2, by omega⟩ ∧
          φ u₁ < φ u₀ ∧ φ u₀ < φ (x ⟨s - 2, by omega⟩) := by
      let q_bot (j : Fin (s - 1)) : Fin k := x ⟨j.1, by omega⟩
      have hq_bot_mono : StrictMono q_bot := fun a b hab =>
        hx_mono (by change a.1 < b.1; exact hab)
      have hφq_bot_mono : StrictMono (φ ∘ q_bot) := fun a b hab =>
        hφx_mono (by change a.1 < b.1; exact hab)
      rcases eq_or_lt_of_le (Nat.zero_le (x ⟨0, by omega⟩).1) with hx0_eq | hx0_pos
      · -- Case B1: `x 0 = 0`
        have hx0 : x ⟨0, by omega⟩ = ⟨0, by omega⟩ := by ext; dsimp; omega
        have hφx0_pos : 0 < (φ (x ⟨0, by omega⟩)).1 := by
          rw [hx0]
          exact Nat.pos_of_ne_zero fun h => hφ_0 (by ext; exact h)
        obtain ⟨p, hp_φ⟩ := hφ_surj ⟨0, by omega⟩
        have hφp_lt : φ p < φ (x ⟨0, by omega⟩) := by
          change (φ p).1 < (φ (x ⟨0, by omega⟩)).1
          rw [hp_φ]; exact hφx0_pos
        have hp_gt_x0 : x ⟨0, by omega⟩ < p := hno_before_φ p hφp_lt
        rcases lt_or_ge p (x ⟨s - 2, by omega⟩) with hp_lt_xs | hp_ge_xs
        · refine Or.inr ⟨x ⟨0, by omega⟩, p, hp_gt_x0, hp_lt_xs, hφp_lt, ?_⟩
          exact hφx_mono (by change 0 < s - 2; omega)
        · have hp_gt_xs : x ⟨s - 2, by omega⟩ < p := by
            rcases eq_or_lt_of_le hp_ge_xs with heq | hgt
            · exfalso
              have hle : φ (x ⟨0, by omega⟩) ≤ φ (x ⟨s - 2, by omega⟩) :=
                hφx_mono.monotone (by change 0 ≤ s - 2; omega)
              exact not_lt_of_ge (heq ▸ hle) hφp_lt
            · exact hgt
          exact Or.inl (S.exists_leap_typeB hdisj hs hL_len hL_cw hR_inj hR_sub hR_ends
            q_bot hq_bot_mono hφq_bot_mono p hp_gt_xs hφp_lt)
      · -- Case B2: `0 < x 0`
        let p : Fin k := ⟨0, by omega⟩
        have hp_lt_x0 : p < x ⟨0, by omega⟩ := hx0_pos
        have hφp_gt_x0 : φ (x ⟨0, by omega⟩) < φ p := hno_before_lt p hp_lt_x0
        rcases lt_or_ge (φ p) (φ (x ⟨s - 2, by omega⟩)) with hφp_lt_xs | hφp_ge_xs
        · refine Or.inr ⟨p, x ⟨0, by omega⟩, hp_lt_x0, ?_, hφp_gt_x0, hφp_lt_xs⟩
          exact hx_mono (by change 0 < s - 2; omega)
        · have hφp_gt_xs : φ (x ⟨s - 2, by omega⟩) < φ p := by
            rcases eq_or_lt_of_le hφp_ge_xs with heq | hgt
            · exfalso
              have hle : x ⟨0, by omega⟩ ≤ x ⟨s - 2, by omega⟩ :=
                hx_mono.monotone (by change 0 ≤ s - 2; omega)
              have heq_idx : x ⟨s - 2, by omega⟩ = p := hφ_inj heq
              exact not_lt_of_ge (heq_idx ▸ hle) hp_lt_x0
            · exact hgt
          exact Or.inl (S.exists_leap_typeA hdisj hs hL_len hL_cw hR_inj hR_sub hR_ends
            q_bot hq_bot_mono hφq_bot_mono p hp_lt_x0 hφp_gt_xs)
    rcases hbottom with ⟨P_set', hsub, hncard, hleap⟩ | ⟨u₀, u₁, hu_lt, hu₁_lt, hφu_lt, hφu₀_lt⟩
    · exact ⟨P_set', hsub, Or.inr (Or.inl ⟨hncard, hleap⟩)⟩
    · -- Next analyze the top end (`x (n - s + 1)` and `x (n - 1)`)
      have htop :
          (∃ P_set' ⊆ P_set, P_set'.ncard = s ∧ S.IsLeapTransaction P_set') ∨
          ∃ v₀ v₁ : Fin k, x ⟨n - s + 1, by omega⟩ < v₀ ∧ v₀ < v₁ ∧
            φ (x ⟨n - s + 1, by omega⟩) < φ v₁ ∧ φ v₁ < φ v₀ := by
        let q_top (j : Fin (s - 1)) : Fin k := x ⟨n - s + 1 + j.1, by omega⟩
        have hq_top_mono : StrictMono q_top := fun a b hab =>
          hx_mono (by change n - s + 1 + a.1 < n - s + 1 + b.1; exact Nat.add_lt_add_left hab _)
        have hφq_top_mono : StrictMono (φ ∘ q_top) := fun a b hab =>
          hφx_mono (by change n - s + 1 + a.1 < n - s + 1 + b.1; exact Nat.add_lt_add_left hab _)
        have hq_top_last : q_top ⟨s - 2, by omega⟩ = x ⟨n - 1, by omega⟩ := by
          dsimp [q_top]; congr 1; ext; dsimp; omega
        have hxn_le : (x ⟨n - 1, by omega⟩).1 ≤ k - 1 := by
          have := (x ⟨n - 1, by omega⟩).2; omega
        rcases eq_or_lt_of_le hxn_le with hxn_eq | hxn_lt
        · -- Case T1: `x (n - 1) = k - 1`
          have hxn : x ⟨n - 1, by omega⟩ = ⟨k - 1, by omega⟩ := by ext; dsimp; omega
          have hφxn_lt : (φ (x ⟨n - 1, by omega⟩)).1 < k - 1 := by
            have hlt_k := (φ (x ⟨n - 1, by omega⟩)).2
            have hne : φ (x ⟨n - 1, by omega⟩) ≠ ⟨k - 1, by omega⟩ := by
              rw [hxn]; exact hφ_last
            have hne_val : (φ (x ⟨n - 1, by omega⟩)).1 ≠ k - 1 := fun h => hne (by ext; exact h)
            omega
          obtain ⟨p, hp_φ⟩ := hφ_surj ⟨k - 1, by omega⟩
          have hφp_gt : φ (x ⟨n - 1, by omega⟩) < φ p := by
            change (φ (x ⟨n - 1, by omega⟩)).1 < (φ p).1
            rw [hp_φ]; exact hφxn_lt
          have hp_lt_xn : p < x ⟨n - 1, by omega⟩ := hno_after_φ p hφp_gt
          rcases lt_or_ge (x ⟨n - s + 1, by omega⟩) p with hp_gt_xns | hp_le_xns
          · refine Or.inr ⟨p, x ⟨n - 1, by omega⟩, hp_gt_xns, hp_lt_xn, ?_, hφp_gt⟩
            exact hφx_mono (by change n - s + 1 < n - 1; omega)
          · have hp_lt_xns : p < x ⟨n - s + 1, by omega⟩ := by
              rcases eq_or_lt_of_le hp_le_xns with heq | hlt
              · exfalso
                have hle : φ (x ⟨n - s + 1, by omega⟩) ≤ φ (x ⟨n - 1, by omega⟩) :=
                  hφx_mono.monotone (by change n - s + 1 ≤ n - 1; omega)
                exact not_lt_of_ge (heq ▸ hle) hφp_gt
              · exact hlt
            have hp_lt_q0 : p < q_top ⟨0, by omega⟩ := by
              simpa [q_top] using hp_lt_xns
            have hφp_gt_qlast : φ (q_top ⟨s - 2, by omega⟩) < φ p := by
              rw [hq_top_last]; exact hφp_gt
            exact Or.inl (S.exists_leap_typeA hdisj hs hL_len hL_cw hR_inj hR_sub hR_ends
              q_top hq_top_mono hφq_top_mono p hp_lt_q0 hφp_gt_qlast)
        · -- Case T2: `x (n - 1) < k - 1`
          let p : Fin k := ⟨k - 1, by omega⟩
          have hp_gt_xn : x ⟨n - 1, by omega⟩ < p := hxn_lt
          have hφp_lt_xn : φ p < φ (x ⟨n - 1, by omega⟩) := hno_after_gt p hp_gt_xn
          rcases lt_or_ge (φ (x ⟨n - s + 1, by omega⟩)) (φ p) with hφp_gt_xns | hφp_le_xns
          · refine Or.inr ⟨x ⟨n - 1, by omega⟩, p, ?_, hp_gt_xn, hφp_gt_xns, hφp_lt_xn⟩
            exact hx_mono (by change n - s + 1 < n - 1; omega)
          · have hφp_lt_xns : φ p < φ (x ⟨n - s + 1, by omega⟩) := by
              rcases eq_or_lt_of_le hφp_le_xns with heq | hlt
              · exfalso
                have hle : x ⟨n - s + 1, by omega⟩ ≤ x ⟨n - 1, by omega⟩ :=
                  hx_mono.monotone (by change n - s + 1 ≤ n - 1; omega)
                have heq_idx : p = x ⟨n - s + 1, by omega⟩ := hφ_inj heq
                exact not_lt_of_ge (heq_idx.symm ▸ hle) hp_gt_xn
              · exact hlt
            have hp_gt_qlast : q_top ⟨s - 2, by omega⟩ < p := by
              rw [hq_top_last]; exact hp_gt_xn
            have hφp_lt_q0 : φ p < φ (q_top ⟨0, by omega⟩) := by
              simpa [q_top] using hφp_lt_xns
            exact Or.inl (S.exists_leap_typeB hdisj hs hL_len hL_cw hR_inj hR_sub hR_ends
              q_top hq_top_mono hφq_top_mono p hp_gt_qlast hφp_lt_q0)
      rcases htop with ⟨P_set', hsub, hncard, hleap⟩ | ⟨v₀, v₁, hv₀_gt, hv_lt, hφv₁_gt, hφv_lt⟩
      · exact ⟨P_set', hsub, Or.inr (Or.inl ⟨hncard, hleap⟩)⟩
      · obtain ⟨P_set', hsub, hncard, hdc⟩ :=
          S.exists_doublecross_of_ends hdisj hs ht hn hL_len hL_cw hR_inj hR_sub hR_ends
            x hx_mono hφx_mono u₀ u₁ hu_lt hu₁_lt hφu_lt hφu₀_lt v₀ v₁ hv₀_gt hv_lt hφv₁_gt hφv_lt
        exact ⟨P_set', hsub, Or.inr (Or.inr ⟨hncard, hdc⟩)⟩

end Society

export Society (theorem_7_1_proof)

end GraphMinor.GM09
