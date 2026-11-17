/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.DensityHalesJewett.Insensitive
public import Mathlib.Computability.Ackermann
import LeanPool.DensityHalesJewett.DensityHalesJewett.Induction
import LeanPool.ShelahHalesJewett.Ackermann

/-!
# Density Hales--Jewett with the Ackermann function as the bound

Density Hales--Jewett holds for `k ≥ 2` letters in every dimension at least
`ack (4 * k) (k + ⌈1 / δ⌉₊)`: this is `DensityHalesJewett.isDHJBound_ack`. The proof is the
induction on `k`, with `isDHJBound_two` as the base case and `IsDHJBound.step` as the step,
together with a bound for the dimensions that the step produces.

Shelah's bound for the Hales--Jewett numbers is below `ack 5`, by
`Combinatorics.Line.shelahBound_lt_ack`. Sums, products and powers are also below `ack 5`, so for
`M ≥ 5` an expression built from them is a fixed number of applications of `ack M` above its
arguments: `AckBounded M s c x` says that `x ≤ (ack M)^[c] s`. Iterating such an expression `t`
times is below `ack (M + 1)` at a multiple of `t`, by `iterate_le_ack`.

The Graham--Rothschild bound iterates Shelah's bound, so it is a fixed number of applications of
`ack 6` above its parameters. Passing from `k` to `k + 1` letters iterates the bound `F` for `k`
letters three times, one inside the other: in `Subspace.densityBound`, in
`IsInsensitive.intersectionTilingBound` and in `stepBound`. A fourth level turns the result into a
single application of `ack`, so the bound for `k + 2` letters is below `ack (4 * k + 5)`. The
levels are not optimized.

## Main results

* `DensityHalesJewett.isDHJBound_ack`: density Hales--Jewett for `k ≥ 2` letters in every
  dimension at least `ack (4 * k) (k + ⌈1 / δ⌉₊)`.
* `DensityHalesJewett.exists_isDHJDimension_ackBounded`: for `k + 2` letters, a dimension one
  application of `ack (4 * k + 5)` above a bound for `1 / δ`. The thresholds of Szemerédi's and
  Varnavides' theorems are bounded from this form.
-/

@[expose] public section

open Combinatorics Finset

namespace DensityHalesJewett

/-! ### Elementary functions and the Ackermann function -/

private lemma add_le_ack (a b : ℕ) : a + b ≤ ack 2 (max a b) := by
  rw [ack_two]
  omega

private lemma sq_add_three_le (m : ℕ) : m * m + 3 ≤ 2 ^ (m + 3) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ]
    nlinarith

private lemma mul_le_ack (a b : ℕ) : a * b ≤ ack 3 (max a b) := by
  rw [ack_three]
  have h := sq_add_three_le (max a b)
  have h' : a * b ≤ max a b * max a b := Nat.mul_le_mul (le_max_left _ _) (le_max_right _ _)
  omega

private lemma two_pow_le_ack (x : ℕ) : 2 ^ x ≤ ack 3 x := by
  rw [ack_three, pow_add]
  have : 1 ≤ 2 ^ x := Nat.one_le_two_pow
  omega

private lemma pow_le_ack (a b : ℕ) : a ^ b ≤ ack 5 (max a b) :=
  calc a ^ b ≤ (2 ^ a) ^ b := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le b
    _ = 2 ^ (a * b) := (pow_mul 2 a b).symm
    _ ≤ ack 3 (a * b) := two_pow_le_ack _
    _ ≤ ack 3 (ack 3 (max a b)) := ack_mono_right _ (mul_le_ack a b)
    _ ≤ ack 5 (max a b) := (ack_ack_lt_ack_max_add_two 3 3 _).le

private lemma ack_four_one : ack 4 1 = 65533 := by
  have h1 : ack 4 1 = ack 3 (ack 4 0) := ack_succ_succ 3 0
  have h2 : ack 4 0 = ack 3 1 := ack_succ_zero 3
  rw [h1, h2, ack_three, ack_three]
  norm_num

private lemma add_le_ack_four {c s : ℕ} (hc : c ≤ 65532) (hs : 1 ≤ s) : c + s ≤ ack 4 s := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' hs
  have h := (ack_strictMono_right 4).add_le_nat t 1
  rw [ack_four_one] at h
  omega

private lemma ack_add_le {M c s : ℕ} (hM : 2 ≤ M) (hc : c ≤ 65532) (hs : 1 ≤ s) :
    ack (M + 1) (c + s) ≤ ack (M + 3) s :=
  calc ack (M + 1) (c + s) ≤ ack (M + 1) (ack (M + 2) s) :=
        ack_mono_right _ ((add_le_ack_four hc hs).trans (ack_mono_left s (by omega)))
    _ = ack (M + 2) (s + 1) := (ack_succ_succ (M + 1) s).symm
    _ ≤ ack (M + 3) s := ack_succ_right_le_ack_succ_left (M + 2) s

private lemma ack_ack_add_le {M c s : ℕ} (hM : 2 ≤ M) (hc : c ≤ 65532) (hs : 1 ≤ s) :
    ack (M + 3) (ack (M + 1) (c + s)) ≤ ack (M + 4) s := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' hs
  calc ack (M + 3) (ack (M + 1) (c + (t + 1))) ≤ ack (M + 3) (ack (M + 3) (t + 1)) :=
        ack_mono_right _ (ack_add_le hM hc hs)
    _ ≤ ack (M + 3) (ack (M + 4) t) :=
        ack_mono_right _ (ack_succ_right_le_ack_succ_left (M + 3) t)
    _ = ack (M + 4) (t + 1) := (ack_succ_succ (M + 3) t).symm

private lemma le_iterate_ack (M c s : ℕ) : s ≤ (ack M)^[c] s := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (lt_ack_right _ _).le

private lemma iterate_ack_le (M t x : ℕ) : (ack M)^[t] x ≤ ack (M + 1) (t + x) := by
  induction t with
  | zero => simpa using (lt_ack_right _ _).le
  | succ t ih =>
    rw [Function.iterate_succ_apply', (by omega : t + 1 + x = t + x + 1), ack_succ_succ]
    exact ack_mono_right _ ih

private lemma iterate_add_le {f : ℕ → ℕ} (hf : StrictMono f) (t y q : ℕ) :
    f^[t] y + q ≤ f^[t] (y + q) := by
  induction t generalizing y with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    refine (ih (f y)).trans ((hf.iterate t).monotone ?_)
    simpa [add_comm] using hf.add_le_nat q y

/-- `x` is at most `c` applications of `ack M` above `s`. -/
def AckBounded (M s c x : ℕ) : Prop := x ≤ (ack M)^[c] s

namespace AckBounded

variable {M M' s s' c c' x y g : ℕ}

lemma of_le (h : x ≤ s) : AckBounded M s 0 x := h

lemma num (hM : 5 ≤ M) (x : ℕ) (h : x ≤ 65533 := by norm_num) : AckBounded M s 1 x := by
  change x ≤ ack M s
  exact (h.trans_eq ack_four_one.symm).trans
    ((ack_succ_zero 4).symm.le.trans (ack_le_ack hM (Nat.zero_le s)))

lemma mono (h : AckBounded M s c x) (hc : c ≤ c') : AckBounded M s c' x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
  rw [AckBounded, add_comm, Function.iterate_add_apply]
  exact h.trans (le_iterate_ack M d _)

lemma le (h : AckBounded M s c y) (hxy : x ≤ y) : AckBounded M s c x := hxy.trans h

lemma size (h : AckBounded M s c x) (hs : s ≤ s') : AckBounded M s' c x :=
  h.trans ((ack_mono_right M).iterate c hs)

lemma lift (h : AckBounded M s c x) (hM : M ≤ M') : AckBounded M' s c x :=
  h.trans (Monotone.iterate_le_of_le (ack_mono_right M) (fun y ↦ ack_mono_left y hM) c s)

lemma join (hx : AckBounded M s c x) (hy : AckBounded M s c' y) :
    AckBounded M s (max c c') (max x y) :=
  max_le (hx.mono (le_max_left _ _)) (hy.mono (le_max_right _ _))

lemma comp (hx : AckBounded M s c x) (hg : g ≤ M) (hy : y ≤ ack g x) :
    AckBounded M s (c + 1) y := by
  rw [AckBounded, Function.iterate_succ_apply']
  exact hy.trans (ack_le_ack hg hx)

lemma trans (hx : AckBounded M s c x) (hy : AckBounded M x c' y) :
    AckBounded M s (c' + c) y := by
  rw [AckBounded, Function.iterate_add_apply]
  exact le_trans hy ((ack_mono_right M).iterate c' hx)

lemma add (hx : AckBounded M s c x) (hM : 5 ≤ M) (hy : AckBounded M s c' y) :
    AckBounded M s (max c c' + 1) (x + y) :=
  (hx.join hy).comp (by omega) (add_le_ack x y)

lemma mul (hx : AckBounded M s c x) (hM : 5 ≤ M) (hy : AckBounded M s c' y) :
    AckBounded M s (max c c' + 1) (x * y) :=
  (hx.join hy).comp (by omega) (mul_le_ack x y)

lemma pow (hx : AckBounded M s c x) (hM : 5 ≤ M) (hy : AckBounded M s c' y) :
    AckBounded M s (max c c' + 1) (x ^ y) :=
  (hx.join hy).comp hM (pow_le_ack x y)

/-- A bounded number of applications of `ack M` is below `ack (M + 3)`. -/
lemma le_ack (h : AckBounded M s c x) (hM : 2 ≤ M) (hc : c ≤ 65532) (hs : 1 ≤ s) :
    x ≤ ack (M + 3) s :=
  (le_trans h (iterate_ack_le M c s)).trans (ack_add_le hM hc hs)

end AckBounded

open AckBounded

/-- Iterating a function that is `c` applications of `ack M` above its argument. -/
private lemma iterate_le_ack {f : ℕ → ℕ} {M σ c : ℕ} (hf : ∀ x, AckBounded M (max σ x) c (f x))
    (t x₀ : ℕ) : f^[t] x₀ ≤ ack (M + 1) (c * t + max σ x₀) := by
  refine le_trans ?_ (iterate_ack_le M _ _)
  induction t with
  | zero => exact le_max_right σ x₀
  | succ t ih =>
    rw [Function.iterate_succ_apply', Nat.mul_succ, add_comm (c * t) c,
      Function.iterate_add_apply]
    exact le_trans (hf _) ((ack_mono_right M).iterate c
      (max_le ((le_max_left σ x₀).trans (le_iterate_ack M _ _)) ih))

/-! ### The Graham--Rothschild bound -/

private lemma ackBounded_translatedCubeBound {s c n : ℕ} (hc : c ≤ s) (hn : n ≤ s) :
    AckBounded 5 s 7 (FiniteUnions.translatedCubeBound c n) := by
  have h1 : AckBounded 5 s _ (n + 1) := (of_le hn).add le_rfl (num le_rfl 1)
  have h2 : AckBounded 5 s _ (2 * 2 ^ (n + 1) + c) :=
    ((num le_rfl 2).mul le_rfl ((num le_rfl 2).pow le_rfl h1)).add le_rfl (of_le hc)
  exact ((h2.comp le_rfl (Line.shelahBound_lt_ack _ _).le).mul le_rfl h1).mono (by grind)

private lemma minCanonicalBound_eq (c t : ℕ) :
    FiniteUnions.minCanonicalBound c t = (FiniteUnions.translatedCubeBound c)^[t] 0 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [FiniteUnions.minCanonicalBound, ih, Function.iterate_succ_apply']

private lemma minCanonicalBound_le {s c : ℕ} (hc : c ≤ s) (t : ℕ) :
    FiniteUnions.minCanonicalBound c t ≤ ack 6 (7 * t + s) := by
  rw [minCanonicalBound_eq]
  simpa using iterate_le_ack (f := FiniteUnions.translatedCubeBound c) (σ := s)
    (fun x ↦ ackBounded_translatedCubeBound (hc.trans (le_max_left _ _)) (le_max_right _ _)) t 0

private lemma ackBounded_monochromaticUnionsBound {s c m : ℕ} (hc : c ≤ s) (hm : m ≤ s) :
    AckBounded 6 s 5 (FiniteUnions.monochromaticUnionsBound c m) := by
  obtain _ | m := m
  · exact of_le (Nat.zero_le s) |>.mono (Nat.zero_le 5)
  have h6 : 5 ≤ 6 := by norm_num
  have ht : AckBounded 6 s _ (7 * (m * c + 1) + s) :=
    ((num h6 7).mul h6 (((of_le ((Nat.le_succ m).trans hm)).mul h6 (of_le hc)).add h6
      (num h6 1))).add h6 (of_le le_rfl)
  exact (ht.comp le_rfl (minCanonicalBound_le hc _)).mono (by grind)

/-- One step of the recursion `Canonization.bound`. -/
private lemma ackBounded_canonizationStep {σ k c p : ℕ} (hk : k + 1 ≤ σ) (hc : c ≤ σ)
    (hp : p ≤ σ) (B s : ℕ) :
    AckBounded 5 (max σ (max B s)) 7 (B + Line.shelahBound k (c ^ (k + 1) ^ (p + B + s))) := by
  have hσ : σ ≤ max σ (max B s) := le_max_left _ _
  have hB : AckBounded 5 (max σ (max B s)) 0 B := of_le ((le_max_left _ _).trans (le_max_right _ _))
  have harg : AckBounded 5 (max σ (max B s)) _ (2 * k + c ^ (k + 1) ^ (p + B + s)) :=
    ((num le_rfl 2).mul le_rfl (of_le ((Nat.le_succ k).trans (hk.trans hσ)))).add le_rfl
      ((of_le (hc.trans hσ)).pow le_rfl ((of_le (hk.trans hσ)).pow le_rfl
        (((of_le (hp.trans hσ)).add le_rfl hB).add le_rfl
          (of_le ((le_max_right _ _).trans (le_max_right _ _))))))
  exact (hB.add le_rfl (harg.comp le_rfl (Line.shelahBound_lt_ack _ _).le)).mono (by grind)

private lemma canonizationBound_le_iterate {σ k c p : ℕ} (hk : k + 1 ≤ σ) (hc : c ≤ σ)
    (hp : p ≤ σ) (ℓ s : ℕ) : Canonization.bound k c ℓ p s ≤ (ack 5)^[7 * ℓ] (σ + s + ℓ) := by
  induction ℓ generalizing s with
  | zero => simp [Canonization.bound]
  | succ ℓ ih =>
    rw [Canonization.bound, Nat.mul_succ, add_comm (7 * ℓ) 7, Function.iterate_add_apply,
      (by omega : σ + s + (ℓ + 1) = σ + (s + 1) + ℓ)]
    refine le_trans (ackBounded_canonizationStep hk hc hp _ s)
      ((ack_mono_right 5).iterate 7 (max_le ?_ (max_le (ih _) ?_)))
    · exact (by omega : σ ≤ σ + (s + 1) + ℓ).trans (le_iterate_ack _ _ _)
    · exact (by omega : s ≤ σ + (s + 1) + ℓ).trans (le_iterate_ack _ _ _)

private lemma canonizationBound_le {σ k c p : ℕ} (hk : k + 1 ≤ σ) (hc : c ≤ σ) (hp : p ≤ σ)
    (ℓ s : ℕ) : Canonization.bound k c ℓ p s ≤ ack 6 (8 * ℓ + σ + s) :=
  (canonizationBound_le_iterate hk hc hp ℓ s).trans
    ((iterate_ack_le 5 _ _).trans (ack_mono_right 6 (by omega)))

/-- The Graham--Rothschild bound is eight applications of `ack 6` above its parameters. -/
private lemma ackBounded_grahamRothschildBound {s k r m : ℕ} (hk : k + 1 ≤ s) (hr : r ≤ s)
    (hm : m ≤ s) : AckBounded 6 s 8 (GrahamRothschild.bound k r m) := by
  have h6 : 5 ≤ 6 := by norm_num
  have harg : AckBounded 6 s _ (8 * FiniteUnions.monochromaticUnionsBound r m + s) :=
    ((num h6 8).mul h6 (ackBounded_monochromaticUnionsBound hr hm)).add h6 (of_le le_rfl)
  exact (harg.comp le_rfl (canonizationBound_le hk hr (Nat.zero_le _) _ 0)).mono (by grind)

/-! ### Natural bounds for the reciprocals of the real parameters -/

section Reciprocals

variable {k N n : ℕ} {δ : ℝ}

private lemma one_div_mul_le {a b A B : ℝ} (ha : 0 < a) (hb : 0 < b) (hA : 1 / a ≤ A)
    (hB : 1 / b ≤ B) : 1 / (a * b) ≤ A * B := by
  rw [← one_div_mul_one_div]
  exact mul_le_mul hA hB (by positivity) ((by positivity : (0 : ℝ) ≤ 1 / a).trans hA)

private lemma one_div_div_le {a c A : ℝ} (hc : 0 ≤ c) (hA : 1 / a ≤ A) :
    1 / (a / c) ≤ c * A := by
  rw [one_div_div, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left hA hc

private lemma one_div_sq_le {a A : ℝ} (ha : 0 < a) (hA : 1 / a ≤ A) : 1 / a ^ 2 ≤ A ^ 2 := by
  rw [← one_div_pow]
  exact pow_le_pow_left₀ (by positivity) hA 2

private lemma one_div_min_le {a b E : ℝ} (ha : 1 / a ≤ E) (hb : 1 / b ≤ E) : 1 / min a b ≤ E := by
  rcases min_choice a b with h | h <;> rw [h] <;> assumption

private lemma floor_div_le {a E : ℕ} {ε : ℝ} (hE : 1 / ε ≤ E) : ⌊(a : ℝ) / ε⌋₊ ≤ a * E := by
  refine Nat.floor_le_of_le ?_
  rw [div_eq_mul_one_div, Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)

lemma one_div_half_le (hn : 1 / δ ≤ n) : 1 / (δ / 2) ≤ ((2 * n : ℕ) : ℝ) := by
  exact_mod_cast one_div_div_le zero_le_two hn

private lemma one_div_quarter_le (hn : 1 / δ ≤ n) : 1 / (δ / 4) ≤ ((4 * n : ℕ) : ℝ) := by
  exact_mod_cast one_div_div_le zero_le_four hn

/-- `variableCutFibersBound` in terms of a natural bound for `1 / ε`. -/
private lemma variableCutFibersBound_le {a d E : ℕ} {ε : ℝ} (hE : 1 / ε ≤ E) :
    Subspace.variableCutFibersBound a d ε ≤ d * (a ^ d * E + 1 + 1) + 1 := by
  have h : ⌊(a : ℝ) ^ d / ε⌋₊ ≤ a ^ d * E := by exact_mod_cast floor_div_le (a := a ^ d) hE
  unfold Subspace.variableCutFibersBound
  gcongr

/-- A natural bound for `1 / θ`. -/
private def invθBound (k N n : ℕ) : ℕ := 4 * n * (k + 1) ^ (N + 1)

/-- A natural bound for `1 / η`. -/
private def invηBound (k N n : ℕ) : ℕ := 48 * n * invθBound k N n + 4 * invθBound k N n + 6 * n

/-- A natural bound for `1 / γ`. -/
private def invγBound (k N n : ℕ) : ℕ :=
  k * n * invηBound k N n ^ 2 + 2 * invηBound k N n ^ 2 + invηBound k N n

private lemma one_div_θ_le (hδ : 0 < δ) (hn : 1 / δ ≤ n) :
    1 / Parameters.θ k N δ ≤ invθBound k N n := by
  have hden : (((k + 1) ^ (N + 1) - k ^ (N + 1) : ℕ) : ℝ) ≤ (k + 1) ^ (N + 1) := by
    exact_mod_cast Nat.sub_le _ _
  have hnδ : 1 ≤ n * δ := by rwa [div_le_iff₀ hδ] at hn
  rw [Parameters.θ, one_div_div, invθBound, div_div_eq_mul_div, div_le_iff₀ hδ]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hnδ (by positivity : (0 : ℝ) ≤ 4 * (k + 1) ^ (N + 1))]

private lemma max_max_le_add_add {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    max x (max y z) ≤ x + y + z := by
  refine max_le ?_ (max_le ?_ ?_) <;> linarith

private lemma one_div_η_le (hδ : 0 < δ) (hn : 1 / δ ≤ n) :
    1 / Parameters.η k N δ ≤ invηBound k N n := by
  have hθ := one_div_θ_le (k := k) (N := N) hδ hn
  calc 1 / Parameters.η k N δ
      ≤ max (48 * ((n : ℝ) * invθBound k N n)) (max (4 * (invθBound k N n : ℝ)) (6 * n)) :=
        one_div_min_le (le_max_of_le_left (one_div_div_le (by norm_num)
          (one_div_mul_le hδ (Parameters.θ_pos k N hδ) hn hθ)))
          (one_div_min_le (le_max_of_le_right (le_max_of_le_left (one_div_div_le (by norm_num) hθ)))
            (le_max_of_le_right (le_max_of_le_right (one_div_div_le (by norm_num) hn))))
    _ ≤ 48 * ((n : ℝ) * invθBound k N n) + 4 * (invθBound k N n : ℝ) + 6 * n :=
        max_max_le_add_add (by positivity) (by positivity) (by positivity)
    _ = invηBound k N n := by
        unfold invηBound
        push_cast
        ring

private lemma one_div_γ_le (hδ : 0 < δ) (hn : 1 / δ ≤ n) :
    1 / Parameters.γ k N δ ≤ invγBound k N n := by
  have hη := one_div_η_le (k := k) (N := N) hδ hn
  have hη₀ := Parameters.η_pos k N hδ
  calc 1 / Parameters.γ k N δ
      ≤ max ((k : ℝ) * (n * (invηBound k N n : ℝ) ^ 2))
          (max (2 * (invηBound k N n : ℝ) ^ 2) (1 / 3 * invηBound k N n)) :=
        one_div_min_le (le_max_of_le_left (one_div_div_le k.cast_nonneg
          (one_div_mul_le hδ (by positivity) hn (one_div_sq_le hη₀ hη))))
          (one_div_min_le (le_max_of_le_right (le_max_of_le_left
            (one_div_div_le zero_le_two (one_div_sq_le hη₀ hη))))
            (le_max_of_le_right (le_max_of_le_right
              (one_div_mul_le (by norm_num) hη₀ (le_refl (1 / 3 : ℝ)) hη))))
    _ ≤ (k : ℝ) * (n * (invηBound k N n : ℝ) ^ 2) + 2 * (invηBound k N n : ℝ) ^ 2 +
          1 / 3 * invηBound k N n :=
        max_max_le_add_add (by positivity) (by positivity) (by positivity)
    _ ≤ invγBound k N n := by
        unfold invγBound
        push_cast
        linarith [(by positivity : (0 : ℝ) ≤ invηBound k N n)]

/-- The nested density of the recursion `Subspace.densityBound`. -/
private lemma one_div_nested_le {q : ℕ} (hδ : 0 < δ) (hn : 1 / δ ≤ n) (hq : 1 ≤ q) :
    0 < δ / (2 * (((k + 1) ^ q - k ^ q : ℕ) : ℝ)) ∧
      1 / (δ / (2 * (((k + 1) ^ q - k ^ q : ℕ) : ℝ))) ≤ ((2 * (k + 1) ^ q * n : ℕ) : ℝ) := by
  have hD : 0 < (k + 1) ^ q - k ^ q :=
    Nat.sub_pos_of_lt (Nat.pow_lt_pow_left k.lt_succ_self (by omega))
  refine ⟨div_pos hδ (mul_pos two_pos (Nat.cast_pos.2 hD)),
    (one_div_div_le (by positivity) hn).trans ?_⟩
  push_cast
  gcongr
  exact_mod_cast Nat.sub_le _ _

end Reciprocals

/-! ### The density increment -/

/-- `F` is below level `L` of the Ackermann function at `max (k + 2) n`, for every natural `n`
that bounds the reciprocal of the density. -/
private def AtLevel (k L : ℕ) (F : ℝ → ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ n : ℕ, 1 / δ ≤ n → F δ ≤ ack L (max (k + 2) n)

section Density

variable {k L M s σ n : ℕ} {F : ℝ → ℕ} {δ : ℝ}

private lemma AtLevel.ackBounded_half (hF : AtLevel k L F) (hM : 5 ≤ M) (hLM : L ≤ M)
    (hk : k + 2 ≤ s) (hn : n ≤ s) (hδ : 0 < δ) (hnδ : 1 / δ ≤ n) :
    AckBounded M s 3 (F (δ / 2)) :=
  (((of_le hk).join ((num hM 2).mul hM (of_le hn))).comp hLM
    (hF _ (by positivity) _ (one_div_half_le hnδ))).mono (by grind)

private lemma AtLevel.ackBounded_quarter (hF : AtLevel k L F) (hM : 5 ≤ M) (hLM : L ≤ M)
    (hk : k + 2 ≤ s) (hn : n ≤ s) (hδ : 0 < δ) (hnδ : 1 / δ ≤ n) :
    AckBounded M s 3 (F (δ / 4)) :=
  (((of_le hk).join ((num hM 4).mul hM (of_le hn))).comp hLM
    (hF _ (by positivity) _ (one_div_quarter_le hnδ))).mono (by grind)

/-- One step of the recursion `Subspace.densityBound`. -/
private lemma ackBounded_densityBound_step (hF : AtLevel k L F) (hL : 5 ≤ L) (hk : k + 2 ≤ σ)
    (hδ : 0 < δ) (hnδ : 1 / δ ≤ n) : AckBounded L (max σ n) 7
      (max σ (2 * (k + 1) ^ max 1 (F (δ / 2)) * n) + max 1 (F (δ / 2))) := by
  have hσ : σ ≤ max σ n := le_max_left _ _
  have hq : AckBounded L (max σ n) _ (max 1 (F (δ / 2))) :=
    (num hL 1).join (hF.ackBounded_half hL le_rfl (hk.trans hσ) (le_max_right _ _) hδ hnδ)
  exact (((of_le hσ).join (((num hL 2).mul hL
    ((of_le ((by omega : k + 1 ≤ σ).trans hσ)).pow hL hq)).mul hL
      (of_le (le_max_right _ _)))).add hL hq).mono (by grind)

private lemma densityBound_succ_le (hF : AtLevel k L F) (hL : 5 ≤ L) (hk : k + 2 ≤ σ) (m : ℕ)
    (hδ : 0 < δ) (hnδ : 1 / δ ≤ n) :
    Subspace.densityBound k F (m + 1) δ ≤ (ack L)^[7 * m + 1] (max σ n) := by
  induction m generalizing δ n with
  | zero => exact (hF δ hδ n hnδ).trans (ack_mono_right L (max_le_max_right n hk))
  | succ m ih =>
    rw [Subspace.densityBound_succ k F (by omega : 1 ≤ m + 1)]
    obtain ⟨hδ', hnδ'⟩ := one_div_nested_le (k := k) hδ hnδ (le_max_left 1 (F (δ / 2)))
    calc _ ≤ (ack L)^[7 * m + 1] (max σ (2 * (k + 1) ^ max 1 (F (δ / 2)) * n)) +
            max 1 (F (δ / 2)) :=
          Nat.add_le_add_right (ih hδ' hnδ') _
      _ ≤ (ack L)^[7 * m + 1]
            (max σ (2 * (k + 1) ^ max 1 (F (δ / 2)) * n) + max 1 (F (δ / 2))) :=
          iterate_add_le (ack_strictMono_right L) _ _ _
      _ ≤ (ack L)^[7 * m + 1] ((ack L)^[7] (max σ n)) :=
          (ack_mono_right L).iterate _ (ackBounded_densityBound_step hF hL hk hδ hnδ)
      _ = (ack L)^[7 * (m + 1) + 1] (max σ n) := by
          rw [← Function.iterate_add_apply]
          congr 1

private lemma densityBound_le (hF : AtLevel k L F) (hL : 5 ≤ L) (hk : k + 2 ≤ σ) (m : ℕ)
    (hδ : 0 < δ) (hnδ : 1 / δ ≤ n) :
    Subspace.densityBound k F m δ ≤ ack (L + 1) (7 * m + max σ n) := by
  cases m with
  | zero => exact Nat.zero_le _
  | succ m =>
    exact (densityBound_succ_le hF hL hk m hδ hnδ).trans
      ((iterate_ack_le L _ _).trans (ack_mono_right _ (by omega)))

private lemma ackBounded_restrictAlphabetBound (hF : AtLevel k L F) (hL : 5 ≤ L) (hk : k + 2 ≤ σ)
    (m : ℕ) (hδ : 0 < δ) (hnδ : 1 / δ ≤ n) :
    AckBounded (L + 1) (max σ (max m n)) 10 (Subspace.restrictAlphabetBound k F m δ) := by
  have hL' : 5 ≤ L + 1 := by omega
  have hσ : σ ≤ max σ (max m n) := le_max_left _ _
  have h2n : AckBounded (L + 1) (max σ (max m n)) _ (2 * n) :=
    (num hL' 2).mul hL' (of_le ((le_max_right _ _).trans (le_max_right _ _)))
  have hd : AckBounded (L + 1) (max σ (max m n)) _
      (max 1 (Subspace.densityBound k F m (δ / 2))) :=
    (num hL' 1).join ((((num hL' 7).mul hL'
      (of_le ((le_max_left _ _).trans (le_max_right _ _)))).add hL' ((of_le hσ).join h2n)).comp
        le_rfl
        (densityBound_le hF hL hk m (by positivity) (one_div_half_le hnδ)))
  exact ((((hd.mul hL' (((((of_le ((by omega : k + 1 ≤ σ).trans hσ)).pow hL' hd).mul hL'
    h2n).add hL' (num hL' 1)).add hL' (num hL' 1))).add hL' (num hL' 1))).le
      (variableCutFibersBound_le (one_div_half_le hnδ))).mono (by grind)

private lemma ackBounded_tilingBound (hF : AtLevel k L F) (hL : 5 ≤ L) (hk : k + 2 ≤ σ) (m : ℕ)
    {β : ℝ} {E : ℕ} (hβ : 0 < β) (hE : 1 / β ≤ E) :
    AckBounded (L + 1) (max σ (max m E)) 14 (IsInsensitive.tilingBound k F m β) := by
  have hL' : 5 ≤ L + 1 := by omega
  have hσ : σ ≤ max σ (max m E) := le_max_left _ _
  have hb : AckBounded (L + 1) (max σ (max m E)) _
      (max m (Subspace.restrictAlphabetBound k F m β)) :=
    (of_le ((le_max_left _ _).trans (le_max_right _ _))).join
      (ackBounded_restrictAlphabetBound hF hL hk m hβ hE)
  have hfloor : ⌊((k : ℝ) + 1) ^ max m (Subspace.restrictAlphabetBound k F m β) / β⌋₊ ≤
      (k + 1) ^ max m (Subspace.restrictAlphabetBound k F m β) * E := by
    exact_mod_cast floor_div_le (a := (k + 1) ^ max m (Subspace.restrictAlphabetBound k F m β)) hE
  exact ((((((of_le ((by omega : k + 1 ≤ σ).trans hσ)).pow hL' hb).mul hL'
    (of_le ((le_max_right _ _).trans (le_max_right _ _)))).add hL' (num hL' 1)).mul hL' hb).le
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right hfloor 1))).mono (by grind)

private lemma intersectionTilingBound_succ_le (r m : ℕ) (β : ℝ) :
    IsInsensitive.intersectionTilingBound k F (r + 1) m β ≤
      (fun x ↦ max 1 (IsInsensitive.tilingBound k F x β))^[r + 1] m := by
  induction r generalizing m with
  | zero => exact le_max_right _ _
  | succ r ih =>
    rw [IsInsensitive.intersectionTilingBound, Function.iterate_succ_apply]
    exact ih _

private lemma intersectionTilingBound_le (hF : AtLevel k L F) (hL : 5 ≤ L) (hk : k + 2 ≤ σ)
    (r m : ℕ) {β : ℝ} {E : ℕ} (hβ : 0 < β) (hE : 1 / β ≤ E) :
    IsInsensitive.intersectionTilingBound k F r m β ≤
      ack (L + 2) (14 * r + max (max σ E) m) := by
  cases r with
  | zero => exact Nat.zero_le _
  | succ r =>
    exact (intersectionTilingBound_succ_le r m β).trans (iterate_le_ack (fun x ↦
      (((num (by omega) 1).join (ackBounded_tilingBound hF hL hk x hβ hE)).mono
        (by grind)).size (by omega)) (r + 1) m)

private lemma ackBounded_invηBound (hF : AtLevel k L F) (hM : 5 ≤ M) (hLM : L ≤ M) (hk : k + 2 ≤ s)
    (hn : n ≤ s) (hδ : 0 < δ) (hnδ : 1 / δ ≤ n) :
    AckBounded M s 9 (invηBound k (F (δ / 4)) n) := by
  have hθ : AckBounded M s _ (invθBound k (F (δ / 4)) n) :=
    ((num hM 4).mul hM (of_le hn)).mul hM ((of_le (by omega : k + 1 ≤ s)).pow hM
      ((hF.ackBounded_quarter hM hLM hk hn hδ hnδ).add hM (num hM 1)))
  exact (((((num hM 48).mul hM (of_le hn)).mul hM hθ).add hM ((num hM 4).mul hM hθ)).add hM
    ((num hM 6).mul hM (of_le hn))).mono (by grind)

private lemma ackBounded_invγBound (hF : AtLevel k L F) (hM : 5 ≤ M) (hLM : L ≤ M) (hk : k + 2 ≤ s)
    (hn : n ≤ s) (hδ : 0 < δ) (hnδ : 1 / δ ≤ n) :
    AckBounded M s 13 (invγBound k (F (δ / 4)) n) := by
  have hη := ackBounded_invηBound hF hM hLM hk hn hδ hnδ
  have hsq : AckBounded M s _ (invηBound k (F (δ / 4)) n ^ 2) := hη.pow hM (num hM 2)
  exact (((((of_le (by omega : k ≤ s)).mul hM (of_le hn)).mul hM hsq).add hM
    ((num hM 2).mul hM hsq)).add hM hη).mono (by grind)

private lemma ackBounded_workingDimension (hF : AtLevel k L F) (hL : 5 ≤ L) (hk2 : 2 ≤ k)
    (hk : k + 2 ≤ s) (d : ℕ) (hn : n ≤ s) (hδ : 0 < δ) (hnδ : 1 / δ ≤ n) :
    AckBounded (L + 2) (max s d) 17 (workingDimension k F d δ) := by
  have hM : 5 ≤ L + 2 := by omega
  have hs : s ≤ max s d := le_max_left _ _
  have hkS : AckBounded (L + 2) (max s d) 0 k := of_le (by omega)
  have hγ := Parameters.γ_pos hk2 (F (δ / 4)) hδ
  have hceil : ⌈(k : ℝ) / Parameters.η k (F (δ / 4)) δ⌉₊ ≤ k * invηBound k (F (δ / 4)) n := by
    rw [Nat.ceil_le, ← one_div_div]
    exact_mod_cast one_div_div_le k.cast_nonneg (one_div_η_le hδ hnδ)
  have hβ : 1 / (Parameters.γ k (F (δ / 4)) δ ^ 2 / (4 * (k : ℝ))) ≤
      ((4 * k * invγBound k (F (δ / 4)) n ^ 2 : ℕ) : ℝ) := by
    push_cast
    exact one_div_div_le (by positivity) (one_div_sq_le hγ (one_div_γ_le hδ hnδ))
  have harg : AckBounded (L + 2) (max s d) _
      (14 * k + max (max (max s d) (4 * k * invγBound k (F (δ / 4)) n ^ 2)) d) :=
    ((num hM 14).mul hM hkS).add hM (((of_le le_rfl).join (((num hM 4).mul hM hkS).mul hM
      ((ackBounded_invγBound hF hM (by omega) (hk.trans hs) (hn.trans hs) hδ hnδ).pow hM
        (num hM 2)))).join (of_le (le_max_right s d)))
  exact (((num hM 1).join ((hkS.mul hM (ackBounded_invηBound hF hM (by omega) (hk.trans hs)
    (hn.trans hs) hδ hnδ)).le hceil)).join (harg.comp le_rfl
      (intersectionTilingBound_le hF hL (hk.trans hs) k d (by positivity) hβ))).mono (by grind)

private lemma ackBounded_incrementBound (hF : AtLevel k L F) (hL : 5 ≤ L) (hk2 : 2 ≤ k)
    (hk : k + 2 ≤ s) (d : ℕ) (hn : n ≤ s) (hδ : 0 < δ) (hnδ : 1 / δ ≤ n) :
    AckBounded (L + 2) (max s d) 31 (incrementBound k F d δ) := by
  have hM : 5 ≤ L + 2 := by omega
  have hs : s ≤ max s d := le_max_left _ _
  have harg : AckBounded (L + 2) (max s d) _
      (max (k + 2) (max (workingDimension k F d δ) (F (δ / 4) + 1))) :=
    (of_le (hk.trans hs)).join ((ackBounded_workingDimension hF hL hk2 hk d hn hδ hnδ).join
      ((hF.ackBounded_quarter hM (by omega) (hk.trans hs) (hn.trans hs) hδ hnδ).add hM
        (num hM 1)))
  have hgr : AckBounded (L + 2) (max s d) _ (max 1 (GrahamRothschild.bound (k + 1) 2
      (max (workingDimension k F d δ) (F (δ / 4) + 1)))) :=
    (num hM 1).join (harg.trans ((ackBounded_grahamRothschildBound (le_max_left _ _)
      ((by omega : 2 ≤ k + 2).trans (le_max_left _ _)) (le_max_right _ _)).lift (by omega)))
  have hε : 1 / (Parameters.η k (F (δ / 4)) δ ^ 2 / 2) ≤
      ((2 * invηBound k (F (δ / 4)) n ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast one_div_div_le zero_le_two
      (one_div_sq_le (Parameters.η_pos k (F (δ / 4)) hδ) (one_div_η_le hδ hnδ))
  have hE : AckBounded (L + 2) (max s d) _ (2 * invηBound k (F (δ / 4)) n ^ 2) :=
    (num hM 2).mul hM ((ackBounded_invηBound hF hM (by omega) (hk.trans hs) (hn.trans hs) hδ
      hnδ).pow hM (num hM 2))
  exact ((((hgr.mul hM (((((of_le (by omega : k + 1 ≤ max s d)).pow hM hgr).mul hM hE).add hM
    (num hM 1)).add hM (num hM 1))).add hM (num hM 1))).le
      (variableCutFibersBound_le hε)).mono (by grind)

/-- If the bound for `k` letters is at level `L`, the bound for `k + 1` letters is at level
`L + 4`. -/
private lemma AtLevel.step (hF : AtLevel k L F) (hL : 5 ≤ L) (hk2 : 2 ≤ k) :
    AtLevel (k + 1) (L + 4) (stepBound k F) := by
  intro δ hδ n hnδ
  have hk : k + 2 ≤ max (k + 1 + 2) n := by omega
  have hn : n ≤ max (k + 1 + 2) n := le_max_right _ _
  have ht : ⌈2 / Parameters.γ k (F (δ / 4)) δ⌉₊ ≤ 2 * invγBound k (F (δ / 4)) n := by
    rw [Nat.ceil_le, ← one_div_div]
    exact_mod_cast one_div_div_le zero_le_two (one_div_γ_le hδ hnδ)
  have hX : AckBounded L (max (k + 1 + 2) n) 17
      (31 * (⌈2 / Parameters.γ k (F (δ / 4)) δ⌉₊ + 1) + max (max (k + 1 + 2) n) 1) :=
    (((num hL 31).mul hL ((((num hL 2).mul hL (ackBounded_invγBound hF hL le_rfl hk hn hδ hnδ)).le
      ht).add hL (num hL 1))).add hL ((of_le le_rfl).join (num hL 1))).mono (by grind)
  calc stepBound k F δ
      ≤ ack (L + 3) (31 * (⌈2 / Parameters.γ k (F (δ / 4)) δ⌉₊ + 1) + max (max (k + 1 + 2) n) 1) :=
        iterate_le_ack (fun x ↦ ((num (by omega) 1).join
          (ackBounded_incrementBound hF hL hk2 hk x hn hδ hnδ)).mono (by grind)) _ 1
    _ ≤ ack (L + 3) (ack (L + 1) (17 + max (k + 1 + 2) n)) :=
        ack_mono_right _ (le_trans hX (iterate_ack_le L 17 _))
    _ ≤ ack (L + 4) (max (k + 1 + 2) n) := ack_ack_add_le (by omega) (by norm_num) (by omega)

end Density

private lemma atLevel_two : AtLevel 2 5 fun δ ↦ 2 * ⌈1 / δ ^ 2⌉₊ := by
  intro δ hδ n hnδ
  have hceil : ⌈1 / δ ^ 2⌉₊ ≤ n * n := by
    rw [Nat.ceil_le]
    exact_mod_cast (one_div_sq_le hδ hnδ).trans_eq (sq _)
  calc 2 * ⌈1 / δ ^ 2⌉₊ ≤ ack 2 (n * n) := by
        rw [ack_two]
        omega
    _ ≤ ack 2 (ack 3 n) := ack_mono_right 2 (by simpa using mul_le_ack n n)
    _ ≤ ack 5 n := (ack_ack_lt_ack_max_add_two 2 3 n).le
    _ ≤ ack 5 (max (2 + 2) n) := ack_mono_right 5 (le_max_right _ _)

/-- The induction on the alphabet: density Hales--Jewett for `k + 2` letters has a bound at level
`4 * k + 5`. -/
private lemma exists_isDHJBound_atLevel (k : ℕ) :
    ∃ F, IsDHJBound (k + 2) F ∧ AtLevel (k + 2) (4 * k + 5) F := by
  induction k with
  | zero => exact ⟨_, isDHJBound_two, atLevel_two⟩
  | succ k ih =>
    obtain ⟨F, hF, hL⟩ := ih
    refine ⟨stepBound (k + 2) F, hF.step (by omega), ?_⟩
    rw [(by omega : 4 * (k + 1) + 5 = 4 * k + 5 + 4)]
    exact hL.step (by omega) (by omega)

lemma ack_max_le {M k n : ℕ} (hn : 0 < n) : ack M (max (k + 4) n) ≤ ack (M + 1) (k + 2 + n) :=
  (ack_mono_right M (by omega : max (k + 4) n ≤ k + 2 + n + 1)).trans
    (ack_succ_right_le_ack_succ_left M _)

/-- A dimension in which density Hales--Jewett holds for `k + 2` letters and density `δ`, one
application of `ack M` above a bound `N` for `1 / δ`. -/
lemma exists_isDHJDimension_ackBounded (k : ℕ) {δ : ℝ} (hδ : 0 < δ) {M s c N : ℕ}
    (hM : 4 * k + 5 ≤ M) (hs : k + 4 ≤ s) (hN : AckBounded M s c N) (hδN : 1 / δ ≤ N) :
    ∃ d, IsDHJDimension (k + 2) δ d ∧ AckBounded M s (c + 1) d := by
  obtain ⟨F, hF, hL⟩ := exists_isDHJBound_atLevel k
  exact ⟨F δ, hF δ hδ _ le_rfl,
    (((of_le hs).join hN).comp hM (hL δ hδ N hδN)).mono (by omega)⟩

/-- **Density Hales--Jewett** for `k ≥ 2` letters holds in every dimension
`n ≥ ack (4 * k) (k + ⌈1 / δ⌉₊)`. -/
theorem isDHJBound_ack {k : ℕ} (hk : 2 ≤ k) :
    IsDHJBound k fun δ ↦ ack (4 * k) (k + ⌈1 / δ⌉₊) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  obtain ⟨F, hF, hL⟩ := exists_isDHJBound_atLevel k
  intro δ hδ n hn
  refine hF δ hδ n (le_trans ?_ hn)
  calc F δ ≤ ack (4 * k + 5) (max (k + 4) ⌈1 / δ⌉₊) := hL δ hδ _ (Nat.le_ceil _)
    _ ≤ ack (4 * k + 5 + 1) (k + 2 + ⌈1 / δ⌉₊) := ack_max_le (Nat.ceil_pos.2 (by positivity))
    _ ≤ ack (4 * (k + 2)) (k + 2 + ⌈1 / δ⌉₊) := ack_mono_left _ (by omega)

end DensityHalesJewett
