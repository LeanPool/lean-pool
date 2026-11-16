/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Readers.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Order.Interval.Finset.Nat

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Suffix chains

For a word `t` and a length `b`, let `v_b` be the suffix of `t` of length `b`. The distance
`suffixReturnGap t b` is the least `h ≥ 1` such that `v_b` also occurs in `t` ending `h` letters
before the end; then `v_b` is a prefix of `v_{b+h}`, so `v_{b+h}` has period `h`. A suffix
chain is a sequence `b₀ < b₁ < ⋯` in which each step adds this distance. Along a chain the
suffixes `v_{b_i}` form a prefix chain, and the cuts `|t| - b_i` start comparable suffixes.

On an eligible coordinate of a structural reader with a mortal endpoint, comparable suffix
starts carry distinct live states, so every chain has fewer than `|S|` members
(`chain_length_le_mortal`). The rejected-tail bound uses chains of bounded length through
`chain_stop_from`: if the chains that start at a length at least `b₀` have at most `S` steps,
following a chain from `bs ≥ b₀` while the distance stays below a threshold `g` stops within the
`S`-fold iterate of `b ↦ b + g b`.

## Main declarations

- `suffixOfLength`, `occurrences`: suffixes of a given length and their occurrences in a word.
- `suffixReturnGap`: the distance from the suffix of length `b` to its previous occurrence.
- `SuffixChain`, `ChainBound`, `ChainBoundFrom`: suffix chains and bounds on their length, for
  all chains or for the chains that start at a given length or later.
- `chainBound_mortal`: on a mortal eligible coordinate, chains have at most `|S| - 1` members.
- `chain_stop_from`, `chain_stop`: a chain of bounded length stops at a controlled scale.
-/

@[expose] public section


namespace DeciSigma1.Words

open DeciSigma1.Readers

variable {α : Type}

/-! ## Suffixes and occurrences -/

/-- The suffix `v_b` of `t` of length `b` (all of `t` if `b ≥ |t|`). -/
def suffixOfLength (t : List α) (b : ℕ) : List α := t.drop (t.length - b)

@[simp] theorem length_suffixOfLength (t : List α) (b : ℕ) :
    (suffixOfLength t b).length = min b t.length := by
  simp only [suffixOfLength, List.length_drop]; omega

theorem suffixOfLength_suffix_suffixOfLength (t : List α) {b b' : ℕ} (h : b ≤ b') :
    suffixOfLength t b <:+ suffixOfLength t b' := by
  unfold suffixOfLength
  by_cases hb : b' ≤ t.length
  · have : t.drop (t.length - b) = (t.drop (t.length - b')).drop (b' - b) := by
      rw [List.drop_drop]; congr 1; omega
    rw [this]; exact List.drop_suffix _ _
  · rw [show t.length - b' = 0 by omega, List.drop_zero]; exact List.drop_suffix _ _

variable [DecidableEq α]

/-- The cuts `e` of the word `x` at which an occurrence of the suffix `v_b` of `t` ends; empty
if `b > |t|`. -/
def occurrences (x t : List α) (b : ℕ) : Finset ℕ :=
  (Finset.range (x.length + 1)).filter (fun e => b ≤ t.length ∧ suffixOfLength t b <:+ x.take e)

theorem mem_occurrences {x t : List α} {b e : ℕ} :
    e ∈ occurrences x t b ↔ e ≤ x.length ∧ b ≤ t.length ∧ suffixOfLength t b <:+ x.take e := by
  simp only [occurrences, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

theorem occurrences_antitone {x t : List α} {b b' : ℕ} (h : b ≤ b') :
    occurrences x t b' ⊆ occurrences x t b := by
  intro e he
  rw [mem_occurrences] at he ⊢
  exact ⟨he.1, h.trans he.2.1, (suffixOfLength_suffix_suffixOfLength t h).trans he.2.2⟩

/-! ## The distance to the previous occurrence -/

/-- The least `h ≥ 1` such that the suffix `v_b` of `t` also occurs in `t` ending at cut
`|t| - h`, or `none` if there is no such occurrence or `b > |t|`. -/
def suffixReturnGap (t : List α) (b : ℕ) : Option ℕ :=
  if b ≤ t.length then
    ((List.range t.length).find? (fun h => suffixOfLength t b <:+ t.take (t.length - (h + 1)))).map
        (· + 1)
  else none

theorem suffixReturnGap_spec {t : List α} {b h : ℕ} (hD : suffixReturnGap t b = some h) :
    b ≤ t.length ∧ 1 ≤ h ∧ b + h ≤ t.length ∧ suffixOfLength t b <:+ t.take (t.length - h) := by
  unfold suffixReturnGap at hD
  split_ifs at hD with hb
  obtain ⟨h0, hf, rfl⟩ := Option.map_eq_some_iff.mp hD
  rw [List.find?_range_eq_some] at hf
  obtain ⟨h1, h2, _⟩ := hf
  simp only [List.mem_range, decide_eq_true_eq] at h1 h2
  refine ⟨hb, by omega, ?_, h1⟩
  have := h1.length_le
  simp only [length_suffixOfLength, List.length_take] at this
  omega

/-- An occurrence of `v_b` ending `h` letters before the end bounds `suffixReturnGap t b` by
`h`. -/
theorem suffixReturnGap_le_of_occ {t : List α} {b h : ℕ} (hb : b ≤ t.length) (h1 : 1 ≤ h)
    (h2 : h ≤ t.length)
    (hocc : suffixOfLength t b <:+ t.take (t.length - h)) : ∃ h₀, suffixReturnGap t b = some h₀ ∧
        h₀ ≤
        h := by
  unfold suffixReturnGap
  rw [ite_eq_left hb]
  cases hf : (List.range t.length).find?
      (fun h => suffixOfLength t b <:+ t.take (t.length - (h + 1))) with
  | none =>
    rw [List.find?_eq_none] at hf
    have := hf (h - 1) (List.mem_range.mpr (by omega))
    rw [show h - 1 + 1 = h by omega] at this
    exact absurd (decide_eq_true hocc) this
  | some h0 =>
    refine ⟨h0 + 1, rfl, ?_⟩
    rw [List.find?_range_eq_some] at hf
    by_contra hlt
    have := hf.2.2 (h - 1) (by omega)
    rw [show h - 1 + 1 = h by omega] at this
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
    exact this hocc

/-- `suffixReturnGap t` is monotone: an occurrence of a longer suffix contains an occurrence of the
shorter suffix at the same distance from the end. -/
theorem suffixReturnGap_mono {t : List α} {b b' h' : ℕ} (hbb : b ≤ b')
    (hD : suffixReturnGap t b' = some h') :
    ∃ h, suffixReturnGap t b = some h ∧ h ≤ h' := by
  obtain ⟨hb', h1, h2, hocc⟩ := suffixReturnGap_spec hD
  exact suffixReturnGap_le_of_occ (hbb.trans hb') h1 (by omega)
      ((suffixOfLength_suffix_suffixOfLength t hbb).trans hocc)

/-- One chain step makes `v_b` a prefix of `v_{b+h}`. -/
theorem suffixOfLength_prefix_of_suffixReturnGap {t : List α} {b h : ℕ}
    (hD : suffixReturnGap t b = some h) :
    suffixOfLength t b <+: suffixOfLength t (b + h) := by
  obtain ⟨hb, h1, h2, hocc⟩ := suffixReturnGap_spec hD
  obtain ⟨u, hu⟩ := hocc
  have hlen : u.length = t.length - h - b := by
    have := congrArg List.length hu
    simp only [List.length_append, length_suffixOfLength, List.length_take] at this
    omega
  have e : suffixOfLength t b = (t.take (t.length - h)).drop (t.length - h - b) := by
    rw [← hu, ← hlen, List.drop_left]
  rw [e, List.drop_take]
  unfold suffixOfLength
  rw [show t.length - h - b = t.length - (b + h) by omega]
  exact List.take_prefix _ _

/-! ## Suffix chains -/

/-- One chain step: `b' = b + suffixReturnGap t b`. -/
def SuffixStep (t : List α) (b b' : ℕ) : Prop := suffixReturnGap t b = some (b' - b) ∧ b < b'

/-- A suffix chain `b₀, b₁, …` of `t`: `b_{i+1} = b_i + suffixReturnGap t b_i` for every `i`. -/
def SuffixChain (t : List α) (bs : List ℕ) : Prop := bs.IsChain (SuffixStep t)

/-- Every suffix chain of `t` has at most `Sb + 1` members, that is, at most `Sb` steps. -/
def ChainBound (t : List α) (Sb : ℕ) : Prop := ∀ bs, SuffixChain t bs → bs.length ≤ Sb + 1

theorem SuffixStep.spec {t : List α} {b b' : ℕ} (h : SuffixStep t b b') :
    b < b' ∧ b' ≤ t.length ∧ suffixOfLength t b <+: suffixOfLength t b' := by
  obtain ⟨hD, hlt⟩ := h
  have := suffixReturnGap_spec hD
  refine ⟨hlt, by omega, ?_⟩
  have h' := suffixOfLength_prefix_of_suffixReturnGap hD
  rwa [show b + (b' - b) = b' by omega] at h'

/-- The members of a chain increase, all but the first are at most `|t|`, and their suffixes
form a prefix chain. -/
theorem SuffixChain.pairwise {t : List α} {bs : List ℕ} (h : SuffixChain t bs) :
    bs.Pairwise
        (fun b b' => b < b' ∧ b' ≤ t.length ∧ suffixOfLength t b <+: suffixOfLength t b') := by
  unfold SuffixChain at h
  have htrans : ∀ a b c : ℕ, (a < b ∧ b ≤ t.length ∧ suffixOfLength t a <+: suffixOfLength t b) →
      (b < c ∧ c ≤ t.length ∧ suffixOfLength t b <+: suffixOfLength t c) →
      (a < c ∧ c ≤ t.length ∧ suffixOfLength t a <+: suffixOfLength t c) :=
    fun a b c h1 h2 => ⟨h1.1.trans h2.1, h2.2.1, h1.2.2.trans h2.2.2⟩
  have hc : bs.IsChain
      (fun b b' => b < b' ∧ b' ≤ t.length ∧ suffixOfLength t b <+: suffixOfLength t b') :=
    h.imp fun b b' hs => hs.spec
  have : Trans (fun b b' : ℕ => b < b' ∧ b' ≤ t.length ∧ suffixOfLength t b <+: suffixOfLength t b')
      (fun b b' : ℕ => b < b' ∧ b' ≤ t.length ∧ suffixOfLength t b <+: suffixOfLength t b')
      (fun b b' : ℕ => b < b' ∧ b' ≤ t.length ∧ suffixOfLength t b <+: suffixOfLength t b') :=
    ⟨fun h1 h2 => htrans _ _ _ h1 h2⟩
  exact List.isChain_iff_pairwise.mp hc

theorem SuffixChain.nodup {t : List α} {bs : List ℕ} (h : SuffixChain t bs) : bs.Nodup :=
  h.pairwise.imp fun h => Nat.ne_of_lt h.1

/-- In a chain with at least two members every member is `≤ |t|`. -/
theorem SuffixChain.le_length {t : List α} {bs : List ℕ} (h : SuffixChain t bs)
    (h2 : 2 ≤ bs.length) :
    ∀ b ∈ bs, b ≤ t.length := by
  match bs, h, h2 with
  | b0 :: b1 :: rest, h, _ =>
    have hp := (List.pairwise_cons.mp h.pairwise).1
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · have := hp b1 List.mem_cons_self; omega
    · exact (hp b hb).2.1

/-- Every chain has at most `|t| + 1` members. -/
theorem chainBound_len (t : List α) : ChainBound t t.length := by
  intro bs h
  match bs, h with
  | [], _ => simp
  | b0 :: rest, h =>
    have hp := (List.pairwise_cons.mp h.pairwise)
    have hsub : rest.toFinset ⊆ Finset.Icc 1 t.length := by
      intro b hb
      have := hp.1 b (List.mem_toFinset.mp hb)
      simp only [Finset.mem_Icc]; omega
    have hnd : rest.Nodup := hp.2.imp fun h => Nat.ne_of_lt h.1
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, Nat.card_Icc] at this
    simp only [List.length_cons]
    omega

theorem ChainBound.mono {t : List α} {Sb Sb' : ℕ}
    (h : ChainBound t Sb)
    (hS : Sb ≤ Sb') : ChainBound t Sb' :=
  fun bs hbs => (h bs hbs).trans (by omega)

/-- Every suffix chain of `t` whose first member is at least `b₀` has at most `Sb` steps. -/
def ChainBoundFrom (t : List α) (b₀ Sb : ℕ) : Prop :=
  ∀ b bs, b₀ ≤ b → SuffixChain t (b :: bs) → bs.length ≤ Sb

theorem ChainBound.chainBoundFrom {t : List α} {Sb : ℕ} (h : ChainBound t Sb) (b₀ : ℕ) :
    ChainBoundFrom t b₀ Sb := fun _ _ _ hbs => by
  have := h _ hbs
  simp only [List.length_cons] at this
  omega

theorem ChainBoundFrom.mono {t : List α} {b₀ b₁ Sb Sb' : ℕ} (h : ChainBoundFrom t b₀ Sb)
    (hb : b₀ ≤ b₁) (hS : Sb ≤ Sb') : ChainBoundFrom t b₁ Sb' :=
  fun b bs hb₁ hbs => (h b bs (hb.trans hb₁) hbs).trans hS

/-- Two members `b < b'` of a suffix chain have `v_b` a prefix of `v_{b'}`. -/
theorem SuffixChain.prefix_of_lt {t : List α} {bs : List ℕ}
    (h : SuffixChain t bs)
    {b b' : ℕ} (hb : b ∈ bs) (hb' : b' ∈ bs) (hlt : b < b') : suffixOfLength t b <+:
        suffixOfLength t b' := by
  have hp := List.pairwise_iff_getElem.mp h.pairwise
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hb'
  rcases lt_trichotomy j j' with h1 | rfl | h1
  · exact (hp j j' hj hj' h1).2.2
  · omega
  · exact absurd (hp j' j hj' hj h1).1 (by omega)

/-- Counting chain members by an injective labeling that avoids one value. -/
theorem SuffixChain.length_le_card {S : Type} [Fintype S] {t : List α}
    {bs : List ℕ} (h : SuffixChain t bs) (f : ℕ → S) (d : S)
    (hinj : ∀ b ∈ bs, ∀ b' ∈ bs, b < b' → f b ≠ f b') (hd : ∀ b ∈ bs, f b ≠ d) :
    bs.length ≤ Fintype.card S - 1 := by
  classical
  have hnd := h.nodup
  have hsub : bs.toFinset.image f ⊆ Finset.univ.erase d := by
    intro s hs
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_erase.mpr ⟨hd b (List.mem_toFinset.mp hb), Finset.mem_univ _⟩
  have hinj' : Set.InjOn f bs.toFinset := by
    intro b hb b' hb' he
    rw [Finset.mem_coe, List.mem_toFinset] at hb hb'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact hinj b hb b' hb' hlt he
    · exact hinj b' hb' b hb hlt he.symm
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj', List.toFinset_card_of_nodup hnd,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at this
  exact this

/-! ## Chains on mortal coordinates -/

section Mortal

variable {S : Type} [Fintype S] {k : ℕ} (M : StructuralReader α S k)
  {W : Fin k → List α} {j : Fin k}

omit [DecidableEq α] in
theorem two_le_card_of_eligible (h : M.Eligible W j) : 2 ≤ Fintype.card S := by
  classical
  have hne : M.endState W j ≠ M.dead := by
    intro he; have := h.2; rw [he, M.rejected_dead] at this; exact Bool.false_ne_true this
  have := Finset.card_le_univ ({M.endState W j, M.dead} : Finset S)
  rw [Finset.card_pair hne] at this
  exact this

variable {M}

/-- A suffix chain of an eligible coordinate with a mortal endpoint has at most `|S| - 1`
members: its suffix starts carry distinct live states. -/
theorem chain_length_le_mortal (h : M.Eligible W j) (hm : ¬ M.Immortal (M.endState W j))
    {bs : List ℕ} (hbs : SuffixChain (W j) bs) : bs.length ≤ Fintype.card S - 1 := by
  classical
  by_cases h2 : 2 ≤ bs.length
  · have hle := hbs.le_length h2
    have hp := hbs.pairwise
    refine hbs.length_le_card (fun b => M.runPrefix W j ((W j).length - b)) M.dead ?_
      (fun b _ => h.runPrefix_ne _)
    intro b hb b' hb' hlt
    have hpre : (W j).drop ((W j).length - b) <+: (W j).drop ((W j).length - b') := by
      have := (List.pairwise_iff_getElem.mp hp)
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem hb'
      have hii : i < i' := by
        rcases lt_trichotomy i i' with hlt' | rfl | hlt'
        · exact hlt'
        · omega
        · exact absurd (this i' i hi' hi hlt').1 (by omega)
      exact (this i i' hi hi' hii).2.2
    have := StructuralReader.runPrefix_ne_of_mortal h hm (a := (W j).length - b')
      (b := (W j).length - b)
      (by have := hle b hb; have := hle b' hb'; omega) (Nat.sub_le _ _) hpre
    exact fun he => this he.symm
  · have := two_le_card_of_eligible M h
    omega

/-- On an eligible coordinate with a mortal endpoint, chains have at most `|S| - 1` members. -/
theorem chainBound_mortal (h : M.Eligible W j) (hm : ¬ M.Immortal (M.endState W j)) :
    ChainBound (W j) (Fintype.card S - 1) :=
  fun _ hbs => (chain_length_le_mortal h hm hbs).trans (Nat.le_succ _)

end Mortal

/-! ## The stopping scale -/

/-- If every chain of `t` that starts at a length at least `b₀` has at most `S` steps, the chain
from `bs ≥ b₀` that continues while `suffixReturnGap t b ≤ g b` stops at some `b ≥ bs` where
`suffixReturnGap t b` is undefined or exceeds `g b`, and `b` is at most the `S`-fold iterate of
`b ↦ b + g b` at `bs`. -/
theorem chain_stop_from {t : List α} {b₀ S : ℕ} (hS : ChainBoundFrom t b₀ S) (g : ℕ → ℕ)
    (hg : Monotone g) {bs : ℕ} (hbs : b₀ ≤ bs) :
    ∃ b, bs ≤ b ∧ b ≤ (fun b => b + g b)^[S] bs ∧
      ∀ h, suffixReturnGap t b = some h → g b < h := by
  set G : ℕ → ℕ := fun b => b + g b with hG
  have hGm : Monotone G := fun a b hab => Nat.add_le_add hab (hg hab)
  have hGi : ∀ n b, b ≤ G^[n] b := by
    intro n
    induction n with
    | zero => intro b; simp
    | succ n ih =>
        intro b; rw [Function.iterate_succ_apply]; exact (Nat.le_add_right b _).trans (ih _)
  have claim : ∀ n b0, (∃ b, b0 ≤ b ∧ b ≤ G^[n] b0 ∧ ∀ h, suffixReturnGap t b = some h → g b < h) ∨
      ∃ l : List ℕ, SuffixChain t (b0 :: l) ∧ l.length = n + 1 := by
    intro n
    induction n with
    | zero =>
      intro b0
      by_cases hstop : ∀ h, suffixReturnGap t b0 = some h → g b0 < h
      · exact Or.inl ⟨b0, le_rfl, by simp, hstop⟩
      · push Not at hstop
        obtain ⟨h, hD, _⟩ := hstop
        have h1 := (suffixReturnGap_spec hD).2.1
        refine Or.inr ⟨[b0 + h], ?_, rfl⟩
        exact List.isChain_pair.mpr ⟨by rw [Nat.add_sub_cancel_left]; exact hD, by omega⟩
    | succ n ih =>
      intro b0
      by_cases hstop : ∀ h, suffixReturnGap t b0 = some h → g b0 < h
      · exact Or.inl ⟨b0, le_rfl, hGi _ _, hstop⟩
      · push Not at hstop
        obtain ⟨h, hD, hhg⟩ := hstop
        have h1 := (suffixReturnGap_spec hD).2.1
        rcases ih (b0 + h) with ⟨b, hb1, hb2, hb3⟩ | ⟨l, hl, hlen⟩
        · refine Or.inl ⟨b, by omega, hb2.trans ?_, hb3⟩
          rw [Function.iterate_succ_apply]
          exact Monotone.iterate hGm n (by simp only [G]; omega)
        · refine Or.inr ⟨(b0 + h) :: l, ?_, by simp [hlen]⟩
          exact List.isChain_cons_cons.mpr
            ⟨⟨by rw [Nat.add_sub_cancel_left]; exact hD, by omega⟩, hl⟩
  rcases claim S bs with hl | ⟨l, hl, hlen⟩
  · exact hl
  · have := hS bs l hbs hl
    omega

/-- If every chain of `t` has at most `S` steps, the chain from `bs` that continues while
`suffixReturnGap t b ≤ g b` stops at some `b ≥ bs` where `suffixReturnGap t b` is undefined or
exceeds `g b`, and `b` is at most the `S`-fold iterate of `b ↦ b + g b` at `bs`. -/
theorem chain_stop {t : List α} {S : ℕ} (hS : ChainBound t S) (g : ℕ → ℕ) (hg : Monotone g)
    (bs : ℕ) : ∃ b, bs ≤ b ∧ b ≤ (fun b => b + g b)^[S] bs ∧
      ∀ h, suffixReturnGap t b = some h → g b < h :=
  chain_stop_from (hS.chainBoundFrom bs) g hg le_rfl

end DeciSigma1.Words
