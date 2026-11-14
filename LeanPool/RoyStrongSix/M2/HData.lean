/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.M2.HilbertPoly

/-!
# Dimension and degree via forward differences

For an integer-valued `f : ℕ → ℤ`, say `f` **has data `(a, c)`** if `c ≠ 0` and `Δᵃ f` is
eventually the constant `c`. For a Hilbert function this means
`f(k) = c kᵃ/a! + O(k^{a−1})`: `a` is the (projective) dimension and `c` the degree. All proofs are
elementary manipulations of forward differences.

* `HasData.unique`: the data is unique.
* `HasData.exists`: an eventually polynomial `f` that is not eventually zero has data.
* `HasData.pos`: if `f ≥ 0` eventually, then `c > 0`.
* `HasData.compare`: if `0 ≤ f ≤ g` eventually, then `(a, c) ≤ (b, d)` lexicographically.
* `HasData.of_shift_sum`: if `g(k+e) = f(k+e) − f(k)` and `f` has data `(a+1, c)`, then `g` has data
  `(a, e c)`. This is the hyperplane section.
-/

@[expose] public section

namespace LeanPool

namespace StrongSix.M2

/-- `f` has dimension `a` and degree `c`. -/
def HasData (f : ℕ → ℤ) (a : ℕ) (c : ℤ) : Prop := c ≠ 0 ∧ ∀ᶠ k in Filter.atTop, (Δ^[a] f) k = c

theorem iter_Δ_const {f : ℕ → ℤ} {a : ℕ} {c : ℤ} (h : ∀ᶠ k in Filter.atTop, (Δ^[a] f) k = c) :
    ∀ j, 1 ≤ j → ∀ᶠ k in Filter.atTop, (Δ^[a + j] f) k = 0 := by
  intro j hj
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp h
  have h1 : ∀ k ≥ k0, (Δ^[a + 1] f) k = 0 := fun k hk => by
    rw [Function.iterate_succ_apply']
    change (Δ^[a] f) (k + 1) - (Δ^[a] f) k = 0
    rw [hk0 k hk, hk0 (k + 1) (by omega), sub_self]
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
  have := iter_Δ_zero_from h1 i
  exact Filter.eventually_atTop.mpr ⟨k0, fun k hk => by
    rw [show a + (1 + i) = a + 1 + i by ring]; exact this k hk⟩

/-- **Uniqueness of the data.** -/
theorem HasData.unique {f : ℕ → ℤ} {a b : ℕ} {c d : ℤ} (h1 : HasData f a c) (h2 : HasData f b d) :
    a = b ∧ c = d := by
  have hab : a = b := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h
      have := iter_Δ_const h1.2 (j + 1) (by omega)
      obtain ⟨k, hk1, hk2⟩ := (this.and h2.2).exists
      rw [show a + (j + 1) = a + j + 1 by ring] at hk1
      exact h2.1 (hk2 ▸ hk1)
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h
      have := iter_Δ_const h2.2 (j + 1) (by omega)
      obtain ⟨k, hk1, hk2⟩ := (this.and h1.2).exists
      rw [show b + (j + 1) = b + j + 1 by ring] at hk1
      exact h1.1 (hk2 ▸ hk1)
  subst hab
  obtain ⟨k, hk1, hk2⟩ := (h1.2.and h2.2).exists
  exact ⟨rfl, hk1 ▸ hk2⟩

/-- **Existence of the data.** -/
theorem HasData.exists {f : ℕ → ℤ} (hf : EvPoly f) (hnz : ¬ ∀ᶠ k in Filter.atTop, f k = 0) :
    ∃ a c, HasData f a c := by
  classical
  let n := Nat.find hf
  have hn : ∀ᶠ k in Filter.atTop, (Δ^[n] f) k = 0 := Nat.find_spec hf
  have hn0 : n ≠ 0 := fun h => hnz (by have := hn; rw [h] at this; exact this)
  obtain ⟨a, ha⟩ : ∃ a, n = a + 1 := ⟨n - 1, by omega⟩
  -- `Δᵃ f` is eventually constant
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp hn
  have hconst : ∀ k ≥ k0, (Δ^[a] f) k = (Δ^[a] f) k0 := by
    intro k hk
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
    induction i with
    | zero => rfl
    | succ i ih =>
      have := hk0 (k0 + i) (by omega)
      rw [ha, Function.iterate_succ_apply'] at this
      have e : (Δ^[a] f) (k0 + i + 1) - (Δ^[a] f) (k0 + i) = 0 := this
      rw [← add_assoc]; linarith [ih (by omega)]
  refine ⟨a, (Δ^[a] f) k0, fun h0 => ?_, Filter.eventually_atTop.mpr ⟨k0, hconst⟩⟩
  -- otherwise `n` was not minimal
  have hmin := Nat.find_min hf (show a < n by omega)
  exact hmin (Filter.eventually_atTop.mpr ⟨k0, fun k hk => (hconst k hk).trans h0⟩)

/-- An integer function with eventually positive differences is eventually positive. -/
theorem eventually_pos_of_Δ_pos {f : ℕ → ℤ} (h : ∀ᶠ k in Filter.atTop, 0 < Δ f k) :
    ∀ᶠ k in Filter.atTop, 0 < f k := by
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp h
  have hgrow : ∀ i, f k0 + i ≤ f (k0 + i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have := hk0 (k0 + i) (by omega)
      have e : Δ f (k0 + i) = f (k0 + i + 1) - f (k0 + i) := rfl
      have e2 : f (k0 + (i + 1)) = f (k0 + i + 1) := rfl
      push_cast; linarith
  refine Filter.eventually_atTop.mpr ⟨k0 + (|f k0| + 1).toNat, fun k hk => ?_⟩
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (show k0 ≤ k by omega)
  have := hgrow i
  have hi : ((|f k0| + 1).toNat : ℤ) ≤ i := by
    have : (|f k0| + 1).toNat ≤ i := by omega
    exact_mod_cast this
  rw [Int.toNat_of_nonneg (by positivity)] at hi
  linarith [neg_abs_le (f k0)]

/-- **Positive degree ⇒ eventually positive.** -/
theorem HasData.eventually_pos {f : ℕ → ℤ} {a : ℕ} {c : ℤ} (h : HasData f a c) (hc : 0 < c) :
    ∀ᶠ k in Filter.atTop, 0 < f k := by
  induction a generalizing f with
  | zero =>
    filter_upwards [h.2] with k hk
    simp only [Function.iterate_zero, id_eq] at hk
    rw [hk]; exact hc
  | succ a ih =>
    refine eventually_pos_of_Δ_pos (ih (f := Δ f) ⟨h.1, ?_⟩)
    have := h.2
    simpa [Function.iterate_succ_apply] using this

/-- **The degree of an eventually non-negative function is positive.** -/
theorem HasData.pos {f : ℕ → ℤ} {a : ℕ} {c : ℤ} (h : HasData f a c)
    (hnn : ∀ᶠ k in Filter.atTop, 0 ≤ f k) : 0 < c := by
  rcases lt_or_gt_of_ne h.1 with hc | hc
  · exfalso
    have h' : HasData (-f) a (-c) := ⟨neg_ne_zero.mpr h.1, by
      have hl : ∀ n (g : ℕ → ℤ), Δ^[n] (-g) = -(Δ^[n] g) := by
        intro n
        induction n with
        | zero => intro g; rfl
        | succ n ih => intro g; rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
            show Δ (-g) = -Δ g from by funext k; simp [fwdDiff]; ring, ih]
      filter_upwards [h.2] with k hk
      rw [hl, Pi.neg_apply, hk]⟩
    obtain ⟨k, hk1, hk2⟩ := ((h'.eventually_pos (by linarith)).and hnn).exists
    simp at hk1; linarith
  · exact hc

theorem iter_Δ_sub (n : ℕ) (f g : ℕ → ℤ) : Δ^[n] (g - f) = Δ^[n] g - Δ^[n] f := by
  have hneg : ∀ n (h : ℕ → ℤ), Δ^[n] (-h) = -(Δ^[n] h) := by
    intro n
    induction n with
    | zero => intro h; rfl
    | succ n ih => intro h; rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        show Δ (-h) = -Δ h from by funext k; simp [fwdDiff]; ring, ih]
  rw [sub_eq_add_neg, iter_Δ_add, hneg, ← sub_eq_add_neg]

/-- **Comparison.** If `0 ≤ f ≤ g` eventually, the data of `f` is lexicographically at most that
  of `g`. -/
theorem HasData.compare {f g : ℕ → ℤ} {a b : ℕ} {c d : ℤ} (hf : HasData f a c) (hg : HasData g b d)
    (hfg : ∀ᶠ k in Filter.atTop, f k ≤ g k) (hnn : ∀ᶠ k in Filter.atTop, 0 ≤ f k) :
    a < b ∨ (a = b ∧ c ≤ d) := by
  have hc := hf.pos hnn
  have hdiff_nn : ∀ᶠ k in Filter.atTop, 0 ≤ (g - f) k := by
    filter_upwards [hfg] with k hk; simp; linarith
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact Or.inl h
  · subst h
    refine Or.inr ⟨rfl, ?_⟩
    by_contra hlt
    push Not at hlt
    have hD : HasData (g - f) a (d - c) := ⟨by omega, by
      filter_upwards [hf.2, hg.2] with k h1 h2
      rw [iter_Δ_sub, Pi.sub_apply, h1, h2]⟩
    have := hD.pos hdiff_nn
    omega
  · exfalso
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h
    have hD : HasData (g - f) (b + j + 1) (-c) := ⟨by omega, by
      have hz := iter_Δ_const hg.2 (j + 1) (by omega)
      filter_upwards [hf.2, hz] with k h1 h2
      rw [show b + (j + 1) = b + j + 1 by ring] at h2
      rw [iter_Δ_sub, Pi.sub_apply, h1, h2, zero_sub]⟩
    have := hD.pos hdiff_nn
    omega

/-- Shifting does not change the data. -/
theorem HasData.of_shift {f : ℕ → ℤ} {a : ℕ} {c : ℤ} (h : HasData (shift f) a c) : HasData f a c
  := by
  refine ⟨h.1, ?_⟩
  have := h.2
  rw [iter_Δ_shift] at this
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp this
  exact Filter.eventually_atTop.mpr ⟨k0 + 1, fun k hk => by
    have := hk0 (k - 1) (by omega)
    simpa [shift, show k - 1 + 1 = k by omega] using this⟩

theorem HasData.of_shiftN {f : ℕ → ℤ} {a e : ℕ} {c : ℤ} (h : HasData (fun k => f (k + e)) a c) :
    HasData f a c := by
  induction e generalizing f with
  | zero => simpa using h
  | succ e ih =>
    apply HasData.of_shift
    apply ih
    simpa [shift, add_assoc, add_comm 1 e] using h

/-- **Hyperplane section.** If `g (k + e) = f (k + e) − f k` for all `k` and `f` has data
`(a+1, c)`, then `g` has data `(a, e c)` (for `e ≥ 1`). -/
theorem HasData.of_sub_shift {f g : ℕ → ℤ} {a e : ℕ} {c : ℤ} (he : 1 ≤ e) (hf : HasData f (a + 1) c)
    (hg : ∀ k, g (k + e) = f (k + e) - f k) : HasData g a (e * c) := by
  apply HasData.of_shiftN (e := e)
  -- `g(k+e) = Σ_{i<e} Δ f (k+i)`
  have hsum : (fun k => g (k + e)) = ∑ i ∈ Finset.range e, fun k => Δ f (k + i) := by
    funext k
    rw [hg k, Finset.sum_apply]
    have : ∀ n, f (k + n) - f k = ∑ i ∈ Finset.range n, Δ f (k + i) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ← ih]
        change f (k + (n + 1)) - f k = f (k + n) - f k + (f (k + n + 1) - f (k + n))
        rw [← add_assoc]; ring
    exact this e
  have hshiftN : ∀ (n i : ℕ) (h : ℕ → ℤ), Δ^[n] (fun k => h (k + i)) = fun k => (Δ^[n] h) (k +
    i) := by
    intro n i
    induction n with
    | zero => intro h; rfl
    | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        show Δ (fun k => h (k + i)) = fun k => Δ h (k + i) from by
          funext k; change h (k + 1 + i) - h (k + i) = h (k + i + 1) - h (k + i); ring_nf, ih]
  have hsumΔ : ∀ (n : ℕ) (s : Finset ℕ) (F : ℕ → ℕ → ℤ),
      Δ^[n] (∑ i ∈ s, F i) = ∑ i ∈ s, Δ^[n] (F i) := by
    intro n s F
    classical
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply, show Δ (0 : ℕ → ℤ) = 0 from by
          funext k; simp [fwdDiff], ih]
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, iter_Δ_add, ih]
  refine ⟨mul_ne_zero (by exact_mod_cast (show e ≠ 0 by omega)) hf.1, ?_⟩
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp hf.2
  refine Filter.eventually_atTop.mpr ⟨k0, fun k hk => ?_⟩
  rw [hsum, hsumΔ, Finset.sum_apply]
  have : ∀ i ∈ Finset.range e, (Δ^[a] fun k => Δ f (k + i)) k = c := by
    intro i _
    rw [hshiftN]
    have := hk0 (k + i) (by omega)
    rwa [Function.iterate_succ_apply] at this
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end StrongSix.M2

end LeanPool
