/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/
module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import LeanPool.RunsOfMultiples.Defs

/-!
# Counting entropy along the prime factorisation

For a finite set `R` and a function `f`, `ent R f = ∑_{m ∈ R} log (|R| / |fibre of m|)`; this is
`|R|` times the Shannon entropy of `f(X)` for `X` uniform on `R`.

`key t m` records the exponents of the primes `< t` in `m` (the `t`-smooth part of `m`).
`D T t` is `|T|` times the conditional entropy of `v_t(X)` given `key t X`; the chain rule
`∑_{t < B} D T t = |T| log |T|` is `sum_D`.
-/

open Finset Real

@[expose] public section

namespace RunsOfMultiples

section ent

variable {β : Type*} [DecidableEq β]

/-- Counting entropy: `|R|` times the entropy of `f(X)`, `X` uniform on `R`. -/
noncomputable def ent (R : Finset ℕ) (f : ℕ → β) : ℝ :=
  ∑ m ∈ R, Real.log ((R.card : ℝ) / ((R.filter (fun x => f x = f m)).card : ℝ))

lemma fibre_card_pos {R : Finset ℕ} {f : ℕ → β} {m : ℕ} (hm : m ∈ R) :
    0 < (R.filter (fun x => f x = f m)).card :=
  card_pos.2 ⟨m, mem_filter.2 ⟨hm, rfl⟩⟩

lemma fibre_card_le (R : Finset ℕ) (f : ℕ → β) (m : ℕ) :
    (R.filter (fun x => f x = f m)).card ≤ R.card :=
  card_le_card (filter_subset _ _)

lemma log_card_div_fibre_nonneg {R : Finset ℕ} {f : ℕ → β} {m : ℕ} (hm : m ∈ R) :
    0 ≤ Real.log ((R.card : ℝ) / ((R.filter (fun x => f x = f m)).card : ℝ)) := by
  have h1 : (0 : ℝ) < (R.filter (fun x => f x = f m)).card := by
    exact_mod_cast fibre_card_pos hm
  have h2 : ((R.filter (fun x => f x = f m)).card : ℝ) ≤ R.card := by
    exact_mod_cast fibre_card_le R f m
  exact Real.log_nonneg ((one_le_div h1).2 h2)

lemma ent_nonneg (R : Finset ℕ) (f : ℕ → β) : 0 ≤ ent R f :=
  sum_nonneg fun _ hm => log_card_div_fibre_nonneg hm

end ent

/-- The exponents of the primes `< t` in `m`. -/
noncomputable def key (t m : ℕ) : ℕ →₀ ℕ := m.factorization.filter (· < t)

lemma key_apply (t m p : ℕ) : key t m p = if p < t then m.factorization p else 0 := by
  simp [key, Finsupp.filter_apply]

lemma key_zero (m : ℕ) : key 0 m = 0 := by
  ext p
  simp [key_apply]

lemma key_succ_eq_iff (t m m' : ℕ) :
    key (t + 1) m = key (t + 1) m' ↔
      key t m = key t m' ∧ m.factorization t = m'.factorization t := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · ext p
      have := DFunLike.congr_fun h p
      simp only [key_apply] at this ⊢
      split_ifs with hp
      · simpa [show p < t + 1 by omega] using this
      · rfl
    · have := DFunLike.congr_fun h t
      simpa [key_apply] using this
  · rintro ⟨h1, h2⟩
    ext p
    have := DFunLike.congr_fun h1 p
    simp only [key_apply] at this ⊢
    split_ifs at this ⊢ with hp hp'
    · exact this
    · have : p = t := by omega
      subst this
      exact h2
    · omega
    · rfl

lemma key_eq_factorization {t m : ℕ} (hm : ∀ p ∈ m.primeFactors, p < t) :
    key t m = m.factorization := by
  ext p
  rw [key_apply]
  split_ifs with hp
  · rfl
  · rw [Finsupp.notMem_support_iff.1]
    rw [Nat.support_factorization]
    intro hp'
    exact hp (hm p hp')

/-- Multiplying by a prime `p ≥ t` does not change the `t`-smooth part. -/
lemma key_prime_mul {t p m : ℕ} (hp : p.Prime) (htp : t ≤ p) (hm : m ≠ 0) :
    key t (p * m) = key t m := by
  ext x
  rw [key_apply, key_apply, Nat.factorization_mul hp.ne_zero hm, hp.factorization]
  split_ifs with hx
  · simp [show p ≠ x by omega]
  · rfl

lemma factorization_prime_mul_self {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    (p * m).factorization p = m.factorization p + 1 := by
  rw [Nat.factorization_mul hp.ne_zero hm, hp.factorization]
  simp [add_comm]

/-- `D T t`: `|T|` times the conditional entropy of `v_t(X)` given the `t`-smooth part of `X`. -/
noncomputable def D (T : Finset ℕ) (t : ℕ) : ℝ :=
  ∑ c ∈ T.image (key t), ent (T.filter (fun m => key t m = c)) (fun m => m.factorization t)

lemma D_nonneg (T : Finset ℕ) (t : ℕ) : 0 ≤ D T t :=
  sum_nonneg fun _ _ => ent_nonneg _ _

/-- Regrouping: `D T t` is the increase of `ent T (key ·)` from `t` to `t + 1`. -/
lemma D_eq (T : Finset ℕ) (t : ℕ) : D T t = ent T (key (t + 1)) - ent T (key t) := by
  unfold D ent
  rw [← sum_sub_distrib]
  rw [← sum_fiberwise_of_maps_to (s := T) (t := T.image (key t)) (g := key t)
    (fun m hm => mem_image_of_mem _ hm)]
  refine sum_congr rfl fun c _ => sum_congr rfl fun m hm => ?_
  rw [mem_filter] at hm
  obtain ⟨hmT, rfl⟩ := hm
  -- the fibre of `m` for `key t` and its refinement
  have hF : (T.filter (fun x => key t x = key t m)).filter
      (fun x => x.factorization t = m.factorization t) =
      T.filter (fun x => key (t + 1) x = key (t + 1) m) := by
    ext x
    simp only [mem_filter, key_succ_eq_iff]
    tauto
  rw [hF]
  have hT : (0 : ℝ) < T.card := by exact_mod_cast card_pos.2 ⟨m, hmT⟩
  have h1 : (0 : ℝ) < (T.filter (fun x => key (t + 1) x = key (t + 1) m)).card := by
    exact_mod_cast fibre_card_pos hmT
  have h2 : (0 : ℝ) < (T.filter (fun x => key t x = key t m)).card := by
    exact_mod_cast fibre_card_pos hmT
  rw [Real.log_div h2.ne' h1.ne', Real.log_div hT.ne' h1.ne', Real.log_div hT.ne' h2.ne']
  ring

lemma ent_key_zero (T : Finset ℕ) : ent T (key 0) = 0 := by
  unfold ent
  refine sum_eq_zero fun m hm => ?_
  have : T.filter (fun x => key 0 x = key 0 m) = T := by
    ext x
    simp [key_zero]
  rw [this, div_self]
  · simp
  · exact_mod_cast (card_pos.2 ⟨m, hm⟩).ne'

lemma ent_key_large (T : Finset ℕ) (hT : ∀ m ∈ T, 0 < m) {B : ℕ} (hB : ∀ m ∈ T, m < B) :
    ent T (key B) = T.card * Real.log T.card := by
  unfold ent
  have hsing : ∀ m ∈ T, T.filter (fun x => key B x = key B m) = {m} := by
    intro m hm
    ext x
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hx, hkey⟩
      have hkx : ∀ p ∈ x.primeFactors, p < B := fun p hp =>
        lt_of_le_of_lt (Nat.le_of_dvd (hT x hx) (Nat.dvd_of_mem_primeFactors hp)) (hB x hx)
      have hkm : ∀ p ∈ m.primeFactors, p < B := fun p hp =>
        lt_of_le_of_lt (Nat.le_of_dvd (hT m hm) (Nat.dvd_of_mem_primeFactors hp)) (hB m hm)
      rw [key_eq_factorization hkx, key_eq_factorization hkm] at hkey
      exact Nat.factorization_inj (Nat.pos_iff_ne_zero.1 (hT x hx))
        (Nat.pos_iff_ne_zero.1 (hT m hm)) hkey
    · rintro rfl
      exact ⟨hm, rfl⟩
  rw [sum_congr rfl fun m hm => by rw [hsing m hm]]
  simp

/-- Chain rule: the conditional entropies along all primes add up to `|T| log |T|`. -/
theorem sum_D (T : Finset ℕ) (hT : ∀ m ∈ T, 0 < m) {B : ℕ} (hB : ∀ m ∈ T, m < B) :
    ∑ t ∈ range B, D T t = T.card * Real.log T.card := by
  simp_rw [D_eq]
  rw [sum_range_sub (fun t => ent T (key t)), ent_key_large T hT hB, ent_key_zero, sub_zero]

/-- Restricting the chain-rule sum to a sub-family of indices. -/
lemma sum_D_le (T : Finset ℕ) (hT : ∀ m ∈ T, 0 < m) {B : ℕ} (hB : ∀ m ∈ T, m < B)
    (P : Finset ℕ) (hP : P ⊆ range B) :
    ∑ t ∈ P, D T t ≤ T.card * Real.log T.card := by
  rw [← sum_D T hT hB]
  exact sum_le_sum_of_subset_of_nonneg hP fun t _ _ => D_nonneg T t

end RunsOfMultiples
