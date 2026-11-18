/-
Copyright (c) 2026 Marcel Blattner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Blattner
-/
module

public import Mathlib.Data.List.GetD
public import Mathlib.Data.Set.Card
public import LeanPool.CorlessNilpotent.Matrix

/-!
# Corless's vectors and their number

Corless states Conjecture 5.1 for vectors `u = (u₁, …, u_{m-1})` with entries in `{1, i}`, the
superdiagonal of `T_m(u)`, built by the rule of his Theorem 4.2: start from the empty vector (the
`1 × 1` zero matrix) and pass from `u` to `(u, 1, i, rev u)` or to `(u, i, 1, rev u)`.
`CorlessVec k u` is this rule, written literally; Corless's `k` is our `k + 1`, so `u` has length
`2^(k+1) - 2` and `T` has dimension `2^(k+1) - 1`.

We prove that these vectors are exactly the vectors with nilpotent `T` (`corless_conjecture`) and
that there are `2^k` of them in dimension `2^(k+1) - 1` (`card_nilpotent`).
-/

@[expose] public section

open Polynomial

namespace Corless

/-- Insert two entries between a list and its reflection. -/
def foldVector {α : Type*} (u : List α) (a b : α) : List α := u ++ [a, b] ++ u.reverse

lemma length_foldVector {α : Type*} (u : List α) (a b : α) :
    (foldVector u a b).length = 2 * u.length + 2 := by
  simp [foldVector]
  omega

lemma eq_of_foldVector_eq {α : Type*} {u v : List α} {a b c d : α}
    (h : foldVector u a b = foldVector v c d) : u = v := by
  have lengths := congrArg List.length h
  simp only [length_foldVector] at lengths
  simp only [foldVector, List.append_assoc] at h
  exact (List.append_inj h (by omega)).1

/-- Corless's recursively constructed vectors (Theorem 4.2 of Corless 2021). -/
inductive CorlessVec : ℕ → List ℂ → Prop
  | base : CorlessVec 0 []
  | step₁ {k : ℕ} {u : List ℂ} :
      CorlessVec k u → CorlessVec (k + 1) (foldVector u 1 Complex.I)
  | step₂ {k : ℕ} {u : List ℂ} :
      CorlessVec k u → CorlessVec (k + 1) (foldVector u Complex.I 1)

/-- The signs `u i ^ 2` of a vector with entries in `{1, i}`, as in `T_nilpotent_iff`. -/
noncomputable def sgns (u : List ℂ) : ℕ → ℤ := fun i => entrySign (u.getD i 1)

/-- `Fam k s` only depends on the first `2^(k+1) - 2` signs. -/
lemma Fam_congr : ∀ (k : ℕ) {s t : ℕ → ℤ}, (∀ i < 2 ^ (k + 1) - 2, s i = t i) →
    (Fam k s ↔ Fam k t)
  | 0, _, _, _ => by simp [Fam]
  | k + 1, s, t, h => by
      have hp := two_le_pow k
      have h2 : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; ring
      simp only [Fam, IsFolded]
      rw [h (2 ^ (k + 1) - 2 + 1) (by omega), h (2 ^ (k + 1) - 2) (by omega),
        Fam_congr k (fun i hi => h i (by omega))]
      constructor
      · rintro ⟨⟨h1, h2'⟩, h3⟩
        refine ⟨⟨h1, fun i hi => ?_⟩, h3⟩
        rw [← h _ (by omega), ← h i (by omega)]
        exact h2' i hi
      · rintro ⟨⟨h1, h2'⟩, h3⟩
        refine ⟨⟨h1, fun i hi => ?_⟩, h3⟩
        rw [h _ (by omega), h i (by omega)]
        exact h2' i hi

/-! ### Entries of `u ++ [a, b] ++ rev u` -/

lemma getD_step_left (u : List ℂ) (a b : ℂ) {i : ℕ} (hi : i < u.length) :
    (foldVector u a b).getD i 1 = u.getD i 1 := by
  rw [foldVector, List.append_assoc, List.getD_append _ _ _ _ hi]

lemma getD_step_a (u : List ℂ) (a b : ℂ) : (foldVector u a b).getD u.length 1 = a := by
  rw [foldVector, List.append_assoc, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  simp

lemma getD_step_b (u : List ℂ) (a b : ℂ) :
    (foldVector u a b).getD (u.length + 1) 1 = b := by
  rw [foldVector, List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
    show u.length + 1 - u.length = 1 by omega]
  simp

lemma getD_step_right (u : List ℂ) (a b : ℂ) {i : ℕ} (hi : i < u.length) :
    (foldVector u a b).getD (2 * u.length + 1 - i) 1 = u.getD i 1 := by
  rw [foldVector, List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
    List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_cons, List.length_nil]
  rw [show 2 * u.length + 1 - i - u.length - (0 + 1 + 1) = u.length - 1 - i by omega,
    List.getD_reverse _ (by omega), show u.length - 1 - (u.length - 1 - i) = i by omega]

/-! ### Corless's vectors satisfy `Fam` -/

lemma CorlessVec.length_eq {k : ℕ} {u : List ℂ} (h : CorlessVec k u) :
    u.length = 2 ^ (k + 1) - 2 := by
  induction h with
  | base => simp
  | @step₁ k u _ ih | @step₂ k u _ ih =>
      have hp := two_le_pow k
      rw [length_foldVector, ih, pow_succ 2 (k + 1)]
      omega

lemma CorlessVec.mem {k : ℕ} {u : List ℂ} (h : CorlessVec k u) :
    ∀ x ∈ u, x = 1 ∨ x = Complex.I := by
  induction h with
  | base => simp
  | step₁ _ ih | step₂ _ ih =>
      intro x hx
      simp only [foldVector, List.mem_append, List.mem_reverse, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rcases hx with (hx | hx) | hx
      · exact ih x hx
      · first | exact hx | exact hx.symm
      · exact ih x hx

lemma fam_step {k : ℕ} {u : List ℂ} {a b : ℂ} (hlen : u.length = 2 ^ (k + 1) - 2)
    (hfam : Fam k (sgns u)) (hab : (a = 1 ∧ b = Complex.I) ∨ (a = Complex.I ∧ b = 1)) :
    Fam (k + 1) (sgns (foldVector u a b)) := by
  simp only [Fam, IsFolded, ← hlen]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold sgns
    rw [getD_step_a, getD_step_b]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · intro i hi
    unfold sgns
    rw [getD_step_right _ _ _ hi, getD_step_left _ _ _ hi]
  · rw [Fam_congr k (t := sgns u) (fun i hi => by
      unfold sgns
      rw [getD_step_left _ _ _ (by omega)])]
    exact hfam

lemma CorlessVec.fam {k : ℕ} {u : List ℂ} (h : CorlessVec k u) : Fam k (sgns u) := by
  induction h with
  | base => simp [Fam]
  | step₁ h ih => exact fam_step h.length_eq ih (Or.inl ⟨rfl, rfl⟩)
  | step₂ h ih => exact fam_step h.length_eq ih (Or.inr ⟨rfl, rfl⟩)

/-! ### Every vector satisfying `Fam` is one of Corless's vectors -/

lemma getD_mem {u : List ℂ} (hu : ∀ x ∈ u, x = 1 ∨ x = Complex.I) (i : ℕ) :
    u.getD i 1 = 1 ∨ u.getD i 1 = Complex.I := by
  by_cases hi : i < u.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hu _ (List.getElem_mem hi)
  · left
    rw [List.getD_eq_default _ _ (by omega)]

/-- An entry in `{1, i}` is determined by its sign. -/
lemma eq_of_sgn {x y : ℂ} (hx : x = 1 ∨ x = Complex.I) (hy : y = 1 ∨ y = Complex.I)
    (h : entrySign x = entrySign y) : x = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · simp at h
  · simp at h
  · rfl

lemma ext_getD {l l' : List ℂ} (hl : l.length = l'.length)
    (h : ∀ i < l.length, l.getD i 1 = l'.getD i 1) : l = l' := by
  apply List.ext_getElem hl
  intro i h1 h2
  rw [← List.getD_eq_getElem _ 1 h1, ← List.getD_eq_getElem _ 1 h2]
  exact h i h1

lemma CorlessVec.of_fam : ∀ (k : ℕ) {u : List ℂ}, u.length = 2 ^ (k + 1) - 2 →
    (∀ x ∈ u, x = 1 ∨ x = Complex.I) → Fam k (sgns u) → CorlessVec k u
  | 0, u, hlen, _, _ => by
      obtain rfl : u = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      exact .base
  | k + 1, u, hlen, hu, hfam => by
      have hp := two_le_pow k
      obtain ⟨n, hn⟩ : ∃ n, n = 2 ^ (k + 1) - 2 := ⟨_, rfl⟩
      have hlen' : u.length = 2 * n + 2 := by rw [hlen, pow_succ]; omega
      simp only [Fam, IsFolded, ← hn] at hfam
      obtain ⟨⟨hmid, hmir⟩, hfam'⟩ := hfam
      obtain ⟨v, hv⟩ : ∃ v, v = u.take n := ⟨_, rfl⟩
      have hvlen : v.length = n := by rw [hv, List.length_take]; omega
      have hvget : ∀ i < n, v.getD i 1 = u.getD i 1 := by
        intro i hi
        rw [hv, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take]
        simp [hi]
      have hvmem : ∀ x ∈ v, x = 1 ∨ x = Complex.I := fun x hx =>
        hu x (List.mem_of_mem_take (hv ▸ hx))
      have hvfam : Fam k (sgns v) := by
        rw [Fam_congr k (t := sgns u) (fun i hi => by
          unfold sgns
          rw [hvget i (by omega)])]
        exact hfam'
      have ih := CorlessVec.of_fam k (by omega) hvmem hvfam
      -- `u` is `v ++ [a, b] ++ rev v` with `a, b` its two middle entries
      have hu_eq : u = foldVector v (u.getD n 1) (u.getD (n + 1) 1) := by
        apply ext_getD (by rw [length_foldVector, hvlen, hlen'])
        intro i hi
        rcases Nat.lt_or_ge i n with h1 | h1
        · rw [getD_step_left _ _ _ (by omega), hvget i h1]
        rcases Nat.lt_or_ge i (n + 2) with h2 | h2
        · rcases Nat.lt_or_ge i (n + 1) with h3 | h3
          · rw [show i = v.length by omega, getD_step_a, hvlen]
          · rw [show i = v.length + 1 by omega, getD_step_b, hvlen]
        · -- the right half mirrors the left half
          have hj := hmir (2 * n + 1 - i) (by omega)
          rw [show 2 * n + 1 - (2 * n + 1 - i) = i by omega] at hj
          rw [show i = 2 * v.length + 1 - (2 * n + 1 - i) by omega,
            getD_step_right _ _ _ (by omega), hvget _ (by omega)]
          rw [show 2 * v.length + 1 - (2 * n + 1 - i) = i by omega]
          exact eq_of_sgn (getD_mem hu _) (getD_mem hu _) hj
      -- the two middle entries are `1, i` or `i, 1`
      rw [hu_eq]
      unfold sgns at hmid
      rcases getD_mem hu n with ha | ha <;> rcases getD_mem hu (n + 1) with hb | hb <;>
        rw [ha, hb] at hmid ⊢ <;> simp at hmid
      · exact .step₁ ih
      · exact .step₂ ih

/-! ### Corless's conjecture and the count -/

/-- **Corless's Conjecture 5.1.** For a vector `u` with entries in `{1, i}`, the
skew-symmetric tridiagonal matrix `T_{|u|+1}(u)` is nilpotent iff `u` is one of Corless's
recursively constructed vectors. -/
theorem corless_conjecture {u : List ℂ} (hu : ∀ x ∈ u, x = 1 ∨ x = Complex.I) :
    IsNilpotent (T (u.length + 1) (fun i => u.getD i 1)) ↔ ∃ k, CorlessVec k u := by
  rw [T_nilpotent_iff (getD_mem hu) (by omega)]
  constructor
  · rintro ⟨k, hk, hfam⟩
    exact ⟨k, CorlessVec.of_fam k (by omega) hu hfam⟩
  · rintro ⟨k, hk⟩
    have hp := two_le_pow k
    exact ⟨k, by rw [hk.length_eq]; omega, hk.fam⟩

open Classical in
/-- Corless's vectors with parameter `k`, as a finite set. -/
noncomputable def vecs : ℕ → Finset (List ℂ)
  | 0 => {[]}
  | k + 1 => (vecs k).biUnion fun u =>
      {foldVector u 1 Complex.I, foldVector u Complex.I 1}

lemma mem_vecs (k : ℕ) : ∀ {u : List ℂ}, u ∈ vecs k ↔ CorlessVec k u := by
  induction k with
  | zero =>
      intro u
      simp only [vecs, Finset.mem_singleton]
      constructor
      · rintro rfl
        exact .base
      · intro h
        cases h
        rfl
  | succ k ih =>
      intro u
      simp only [vecs, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, ih]
      constructor
      · rintro ⟨v, hv, rfl | rfl⟩
        · exact .step₁ hv
        · exact .step₂ hv
      · intro h
        cases h with
        | step₁ hv => exact ⟨_, hv, Or.inl rfl⟩
        | step₂ hv => exact ⟨_, hv, Or.inr rfl⟩

lemma card_vecs : ∀ k, (vecs k).card = 2 ^ k
  | 0 => by simp [vecs]
  | k + 1 => by
      classical
      rw [vecs, Finset.card_biUnion]
      · rw [Finset.sum_congr rfl (g := fun _ => 2), Finset.sum_const, card_vecs k, smul_eq_mul,
          pow_succ, mul_comm]
        intro u _
        convert Finset.card_pair _
        intro h
        have middle := congrArg (fun w : List ℂ => w.getD u.length 1) h
        rw [getD_step_a, getD_step_a] at middle
        exact I_ne_one middle.symm
      · intro u _ v _ huv
        rw [Function.onFun, Finset.disjoint_left]
        intro w hw hw'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw hw'
        apply huv
        rcases hw with rfl | rfl <;> rcases hw' with h | h <;> exact eq_of_foldVector_eq h

/-- **The count.** Exactly `2^k` vectors `u` of length `2^(k+1) - 2` with entries in `{1, i}` give
a nilpotent `T(u)`. Since `u` is the superdiagonal of `T(u)`, these are `2^k` distinct matrices of
dimension `2^(k+1) - 1` (Corless's `2^(K-1)` in dimension `2^K - 1`). In every other dimension
there are none, by `T_nilpotent_iff`. -/
theorem card_nilpotent (k : ℕ) :
    {u : List ℂ | u.length = 2 ^ (k + 1) - 2 ∧ (∀ x ∈ u, x = 1 ∨ x = Complex.I) ∧
      IsNilpotent (T (u.length + 1) (fun i => u.getD i 1))}.ncard = 2 ^ k := by
  have hset : {u : List ℂ | u.length = 2 ^ (k + 1) - 2 ∧ (∀ x ∈ u, x = 1 ∨ x = Complex.I) ∧
      IsNilpotent (T (u.length + 1) (fun i => u.getD i 1))} = ↑(vecs k) := by
    ext u
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, mem_vecs]
    constructor
    · rintro ⟨hlen, hu, hnil⟩
      obtain ⟨k', hk'⟩ := (corless_conjecture hu).mp hnil
      have hkk : k' = k := by
        have h1 := hk'.length_eq
        have := two_le_pow k
        have := two_le_pow k'
        have h2 : 2 ^ (k' + 1) = 2 ^ (k + 1) := by omega
        have := Nat.pow_right_injective le_rfl h2
        omega
      exact hkk ▸ hk'
    · intro h
      exact ⟨h.length_eq, h.mem, (corless_conjecture h.mem).mpr ⟨k, h⟩⟩
  rw [hset, Set.ncard_coe_finset, card_vecs]

end Corless
