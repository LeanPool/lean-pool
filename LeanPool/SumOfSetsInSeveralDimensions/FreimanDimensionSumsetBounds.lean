/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import LeanPool.SumOfSetsInSeveralDimensions.FreimanDimension
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import LeanPool.SumOfSetsInSeveralDimensions.AffineDimSumset
import LeanPool.SumOfSetsInSeveralDimensions.ClosedForm
import LeanPool.SumOfSetsInSeveralDimensions.LowerBound

/-!
# Sumset bounds from the Freiman dimension

Let `A` and `B` be finite subsets of a commutative monoid with `B` nonempty and `|B| ≤ |A|`, and
let `f` be a Freiman isomorphism of order `2` from `A ∪ B` onto a subset of `ℝ^r` of affine
dimension `r`. Then `f` sends `A` and `B` to sets `A'` and `B'` with `|A'| = |A|`, `|B'| = |B|` and
`|A' + B'| = |A + B|`, and `A' + B'` has affine dimension at least `r - 1`. Ruzsa's theorem then
gives `|A| + ∑ t ∈ {1, …, |B| - 1}, min (r - 1) (|A| - t) ≤ |A + B|`. A Freiman model in `ℚ^r` is
one in `ℝ^r`, so this holds when `r ≥ 1` is the Freiman dimension of `A ∪ B`.

For `A = B = X` the model `f(X) + f(X)` has affine dimension `r`, and the asymmetric form of
Freiman's lemma gives `(r + 1) * |X| - r * (r + 1) / 2 ≤ |X + X|`. If `|X + X| ≤ κ * |X|`, then
`r ≤ 2 * κ - 1`, so `r * (r + 1) / 2 ≤ κ * (2 * κ - 1)` and `r ≤ κ - 1 + κ * (2 * κ - 1) / |X|`.

## Main statements

* `card_add_sum_min_le_card_add_of_isAddFreimanIso`: the bound above.
* `card_add_sum_min_le_of_freimanDim_union`: the bound for `r` the Freiman dimension of `A ∪ B`.
* `two_mul_card_add_mul_card_le_of_isAddFreimanIso`: Freiman's lemma for a Freiman model `f` of
  `X` in `ℝ^r` of affine dimension `r`, `2 * (|X| + r * |X|) ≤ 2 * |X + X| + r * (r + 1)`.
* `card_add_mul_card_sub_choose_le_card_add_of_freimanDim_union`: the weaker bound
  `|A| + (r - 1) * |B| - (r + 1).choose 2 ≤ |A + B|`.
* `card_add_mul_card_sub_le_card_add_of_freimanDim`: if `X` is nonempty with Freiman dimension
  `r ≥ 1`, then `|X| + r * |X| - r * (r + 1) / 2 ≤ |X + X|`.
* `le_two_mul_sub_one_of_isAddFreimanIso`: if `|X + X| ≤ κ * |X|` for a real `κ`, then a Freiman
  model of `X` in `ℝ^r` of affine dimension `r` has `r ≤ 2 * κ - 1`.
* `freimanDim_le_two_mul_sub_one_of_card_add_le`: if `|X + X| ≤ κ * |X|`, then
  `freimanDim X ≤ 2 * κ - 1`.
* `le_sub_one_add_mul_div_card_of_isAddFreimanIso`: under the same hypotheses,
  `r ≤ κ - 1 + κ * (2 * κ - 1) / |X|`.
* `freimanDim_le_sub_one_add_mul_div_card_of_card_add_le`: if `|X + X| ≤ κ * |X|`, then
  `freimanDim X ≤ κ - 1 + κ * (2 * κ - 1) / |X|`.
-/

@[expose] public section

namespace SumOfSetsInSeveralDimensions

open Finset
open scoped Pointwise

noncomputable section

lemma rationalVectorToReal_injective {d : ℕ} :
    Function.Injective (rationalVectorToReal (d := d)) :=
  Rat.cast_injective.comp_left

lemma rationalVectorToReal_add {d : ℕ} (x y : Fin d → ℚ) :
    rationalVectorToReal (x + y) = rationalVectorToReal x + rationalVectorToReal y := by
  ext i
  simp [rationalVectorToReal]

/-- A Freiman isomorphism into `ℚ^d` followed by the inclusion of `ℚ^d` into `ℝ^d` is a Freiman
isomorphism into `ℝ^d`. -/
lemma isAddFreimanIso_rationalVectorToReal_comp {G : Type*} [AddCommMonoid G] {d : ℕ}
    {X : Finset G} {f : G → (Fin d → ℚ)}
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin d → ℚ)) f) :
    IsAddFreimanIso 2 (X : Set G) (X.image (rationalVectorToReal ∘ f) : Set (Fin d → ℝ))
      (rationalVectorToReal ∘ f) := by
  rw [isAddFreimanIso_two] at hf ⊢
  constructor
  · rw [coe_image]
    exact (rationalVectorToReal_injective.comp_injOn hf.1.injOn).bijOn_image
  · intro a ha b hb c hc e he
    simp only [Function.comp, ← rationalVectorToReal_add, rationalVectorToReal_injective.eq_iff]
    exact hf.2 a ha b hb c hc e he

/-- A set of Freiman dimension `r ≥ 1` has a Freiman model in `ℝ^r` of affine dimension `r`. -/
lemma exists_isAddFreimanIso_of_freimanDim_eq {G : Type*} [AddCommMonoid G]
    {r : ℕ} {X : Finset G} (hdim : freimanDim X = r) (hr : r ≠ 0) :
    ∃ f : G → Fin r → ℝ, IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin r → ℝ)) f ∧
      (X.image f).affineDim = r := by
  classical
  obtain ⟨f, hf, haff⟩ := Nat.findGreatest_of_ne_zero hdim hr
  exact ⟨_, isAddFreimanIso_rationalVectorToReal_comp hf, by rwa [← image_image]⟩

/-- Two maps with the same fibres on `s` have images of `s` of the same size. -/
lemma card_image_eq_of_kernel_iff {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    {s : Finset α} {f : α → β} {g : α → γ}
    (h : ∀ x ∈ s, ∀ y ∈ s, (f x = f y ↔ g x = g y)) :
    #(s.image f) = #(s.image g) := by
  apply card_bij (fun b hb ↦ g (mem_image.mp hb).choose)
  · intro b hb
    exact mem_image_of_mem g (mem_image.mp hb).choose_spec.1
  · intro b₁ hb₁ b₂ hb₂ hgb
    obtain ⟨hx₁, hfb₁⟩ := (mem_image.mp hb₁).choose_spec
    obtain ⟨hx₂, hfb₂⟩ := (mem_image.mp hb₂).choose_spec
    exact hfb₁ ▸ hfb₂ ▸ (h _ hx₁ _ hx₂).2 hgb
  · intro c hc
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hc
    obtain ⟨hy, hfy⟩ := (mem_image.mp (mem_image_of_mem f hx)).choose_spec
    exact ⟨f x, mem_image_of_mem f hx, (h _ hy _ hx).1 hfy⟩

/-- A Freiman isomorphism of order `2` on `X` preserves the size of `A + B` for `A, B ⊆ X`. -/
lemma card_add_image_of_isAddFreimanIso {G H : Type*} [DecidableEq G] [DecidableEq H]
    [AddCommMonoid G] [AddCommMonoid H] {X A B : Finset G} {f : G → H}
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set H) f) (hAX : A ⊆ X) (hBX : B ⊆ X) :
    #(A.image f + B.image f) = #(A + B) := by
  rw [add_def, add_def, ← prodMap_image_product, image_image]
  apply card_image_eq_of_kernel_iff
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab'
  obtain ⟨ha, hb⟩ := mem_product.1 hab
  obtain ⟨ha', hb'⟩ := mem_product.1 hab'
  exact hf.add_eq_add (hAX ha) (hBX hb) (hAX ha') (hBX hb')

/-- **Ruzsa's theorem for a Freiman model.** Let `A` and `B` be finite subsets of a commutative
monoid with `B` nonempty and `|B| ≤ |A|`, and let `f` be a Freiman isomorphism of order `2` from
`A ∪ B` onto a subset of `ℝ^r` of affine dimension `r`. Then
`|A| + ∑ t ∈ {1, …, |B| - 1}, min (r - 1) (|A| - t) ≤ |A + B|`. -/
theorem card_add_sum_min_le_card_add_of_isAddFreimanIso {G : Type*} [DecidableEq G]
    [AddCommMonoid G] {r : ℕ} {A B : Finset G} {f : G → Fin r → ℝ} (hB : B.Nonempty)
    (hBA : #B ≤ #A)
    (hf : IsAddFreimanIso 2 ((A ∪ B : Finset G) : Set G) ((A ∪ B).image f : Set (Fin r → ℝ)) f)
    (hdim : ((A ∪ B).image f).affineDim = r) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min (r - 1) (#A - t) ≤ #(A + B) := by
  have hcard {S : Finset G} (hS : S ⊆ A ∪ B) : #(S.image f) = #S :=
    card_image_of_injOn (hf.bijOn.injOn.mono (coe_subset.2 hS))
  have hA : A.Nonempty := card_pos.1 (hB.card_pos.trans_le hBA)
  have h := card_add_sum_min_le_card_add_of_le (d := r - 1) (hB.image f)
    (by rwa [hcard subset_union_left, hcard subset_union_right])
    (by grind [image_union, affineDim_union_le_sum_add_one (hA.image f) (hB.image f)])
  rwa [hcard subset_union_left, hcard subset_union_right,
    card_add_image_of_isAddFreimanIso hf subset_union_left subset_union_right] at h

/-- Ruzsa's theorem for a Freiman model, with the affine dimension of the model written as the
dimension of the span of its differences. -/
theorem card_add_sum_min_le_card_add_of_isAddFreimanIso_of_finrank_span_sub_eq {G : Type*}
    [DecidableEq G] [AddCommMonoid G] {r : ℕ} {A B : Finset G} {f : G → Fin r → ℝ}
    (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hf : IsAddFreimanIso 2 ((A ∪ B : Finset G) : Set G) ((A ∪ B).image f : Set (Fin r → ℝ)) f)
    (hdim : Module.finrank ℝ (Submodule.span ℝ
      (↑((A ∪ B).image f) - ↑((A ∪ B).image f) : Set (Fin r → ℝ))) = r) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min (r - 1) (#A - t) ≤ #(A + B) :=
  card_add_sum_min_le_card_add_of_isAddFreimanIso hB hBA hf
    ((affineDim_eq_finrank_span_sub _).trans hdim)

/-- **Freiman's lemma for a Freiman model.** If `f` is a Freiman isomorphism of order `2` from a
nonempty `X` onto a subset of `ℝ^r` of affine dimension `r`, then
`2 * (|X| + r * |X|) ≤ 2 * |X + X| + r * (r + 1)`. -/
lemma two_mul_card_add_mul_card_le_of_isAddFreimanIso {G : Type*} [DecidableEq G]
    [AddCommMonoid G] {r : ℕ} {X : Finset G} {f : G → Fin r → ℝ} (hX : X.Nonempty)
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin r → ℝ)) f)
    (hdim : (X.image f).affineDim = r) :
    2 * (#X + r * #X) ≤ 2 * #(X + X) + r * (r + 1) := by
  have h := two_mul_card_add_mul_card_le (hX.image f) le_rfl
    (hdim.symm.trans_le (affineDim_le_affineDim_add_right _ (hX.image f)))
  rwa [card_image_of_injOn hf.bijOn.injOn,
    card_add_image_of_isAddFreimanIso hf subset_rfl subset_rfl] at h

private lemma sub_one_mul_le_choose_add_choose (b r : ℕ) :
    (r - 1) * b ≤ b.choose 2 + (r + 1).choose 2 := by
  obtain _ | r := r
  · simp
  · rw [← Nat.cast_le (α := ℚ), Nat.cast_add, Nat.cast_choose_two, Nat.cast_choose_two]
    push_cast
    nlinarith [sq_nonneg ((r : ℚ) + 1 - b), (Nat.cast_nonneg r : (0 : ℚ) ≤ r),
      (Nat.cast_nonneg b : (0 : ℚ) ≤ b)]

private lemma sum_Ico_one_min_eq_choose {r : ℕ} (hr : 1 ≤ r) :
    ∑ s ∈ Ico 1 r, min (r - 1) s = r.choose 2 := by
  rw [sum_congr rfl (g := id) (by grind), ← Nat.sub_add_cancel hr, Ico_add_one_right_eq_Icc]
  simpa using Nat.sum_Icc_choose (r - 1) 1

private lemma sum_Ico_min_eq_mul {b r : ℕ} :
    ∑ s ∈ Ico r b, min (r - 1) s = (b - r) * (r - 1) := by
  rw [sum_congr rfl (g := fun _ ↦ r - 1) (by grind)]
  simp

private lemma sum_Icc_min_sub {b r : ℕ} (hr : 1 ≤ r) (hrb : r ≤ b) :
    ∑ t ∈ Icc 1 (b - 1), min (r - 1) (b - t) = r.choose 2 + (b - r) * (r - 1) := by
  rw [← sum_Ico_one_min_eq_choose hr, ← sum_Ico_min_eq_mul, sum_Ico_consecutive _ hr hrb,
    ← Ico_add_one_right_eq_Icc, Nat.sub_add_cancel (hr.trans hrb)]
  convert sum_Ico_reflect (fun s ↦ min (r - 1) s) 1 (Nat.le_succ b) using 3 <;> grind

/-- In a cancellative monoid, `|X + X| ≤ κ * |X|` for a nonempty `X` forces `1 ≤ κ`. -/
private lemma one_le_of_card_add_le {G : Type*} [DecidableEq G] [AddCancelCommMonoid G] {κ : ℝ}
    {X : Finset G} (hX : X.Nonempty) (hXX : (#(X + X) : ℝ) ≤ κ * #X) : 1 ≤ κ := by
  have h : (#X : ℝ) ≤ κ * #X := (Nat.cast_le.2 (card_le_card_add_left hX)).trans hXX
  nlinarith [(mod_cast hX.card_pos : (0 : ℝ) < #X)]

/-- If `|X + X| ≤ κ * |X|` for a nonempty `X` and `f` is a Freiman isomorphism of order `2` from
`X` onto a subset of `ℝ^r` of affine dimension `r`, then `r ≤ 2 * κ - 1`. -/
theorem le_two_mul_sub_one_of_isAddFreimanIso {G : Type*} [DecidableEq G]
    [AddCancelCommMonoid G] {r : ℕ} {κ : ℝ} {X : Finset G} {f : G → Fin r → ℝ}
    (hX : X.Nonempty) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin r → ℝ)) f)
    (hdim : (X.image f).affineDim = r) : (r : ℝ) ≤ 2 * κ - 1 := by
  have hrX : r + 1 ≤ #X := by
    grind [affineDim_add_one_le_card (hX.image f), card_image_of_injOn hf.bijOn.injOn]
  have h : (2 * (#X + r * #X) : ℝ) ≤ 2 * #(X + X) + r * (r + 1) :=
    mod_cast two_mul_card_add_mul_card_le_of_isAddFreimanIso hX hf hdim
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ r + 1)
    (sub_nonneg.2 (mod_cast hrX.trans' r.le_succ : (r : ℝ) ≤ #X)),
    (mod_cast hX.card_pos : (0 : ℝ) < #X)]

/-- The bound `r ≤ 2 * κ - 1` for a Freiman model, with the affine dimension of the model written
as the dimension of the span of its differences. -/
theorem le_two_mul_sub_one_of_isAddFreimanIso_of_finrank_span_sub_eq {G : Type*} [DecidableEq G]
    [AddCancelCommMonoid G] {r : ℕ} {κ : ℝ} {X : Finset G} {f : G → Fin r → ℝ}
    (hX : X.Nonempty) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin r → ℝ)) f)
    (hdim : Module.finrank ℝ (Submodule.span ℝ (↑(X.image f) - ↑(X.image f) : Set (Fin r → ℝ))) =
      r) :
    (r : ℝ) ≤ 2 * κ - 1 :=
  le_two_mul_sub_one_of_isAddFreimanIso hX hXX hf
    ((affineDim_eq_finrank_span_sub _).trans hdim)

lemma sub_mul_sub_choose_le_sum_min (b r : ℕ) :
    (r - 1) * b - (r + 1).choose 2 ≤ ∑ t ∈ Icc 1 (b - 1), min (r - 1) (b - t) := by
  rw [Nat.sub_le_iff_le_add]
  obtain hrb | hbr := le_total r b
  · obtain rfl | hr := r.eq_zero_or_pos
    · simp
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hrb
      rw [sum_Icc_min_sub hr hrb, Nat.add_sub_cancel_left, mul_add]
      linarith [sub_one_mul_le_choose_add_choose r r, mul_comm c (r - 1)]
  · obtain rfl | hb := b.eq_zero_or_pos
    · simp
    · refine (sub_one_mul_le_choose_add_choose b r).trans ?_
      rw [← add_zero (b.choose 2), ← zero_mul (b - 1), ← Nat.sub_self b,
        ← sum_Icc_min_sub hb le_rfl]
      gcongr

lemma sub_mul_sub_choose_le_sum_min_of_le {a b r d : ℕ} (hba : b ≤ a) (hrd : r ≤ d + 1) :
    (r - 1) * b - (r + 1).choose 2 ≤ ∑ t ∈ Icc 1 (b - 1), min d (a - t) := by
  refine (sub_mul_sub_choose_le_sum_min b r).trans ?_
  apply sum_le_sum
  grind

/-- Let `A` and `B` be finite with `B` nonempty and `|B| ≤ |A|`, and let `r ≥ 1` be the Freiman
dimension of `A ∪ B`. Then `|A| + ∑ t ∈ {1, …, |B| - 1}, min (r - 1) (|A| - t) ≤ |A + B|`. -/
theorem card_add_sum_min_le_of_freimanDim_union {G : Type*} [DecidableEq G] [AddCommMonoid G]
    {r : ℕ} {A B : Finset G} (hr : 1 ≤ r) (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hdim : freimanDim (A ∪ B) = r) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min (r - 1) (#A - t) ≤ #(A + B) := by
  obtain ⟨f, hf, haff⟩ := exists_isAddFreimanIso_of_freimanDim_eq hdim (Nat.ne_of_gt hr)
  exact card_add_sum_min_le_card_add_of_isAddFreimanIso hB hBA hf haff

/-- Let `A` and `B` be finite with `B` nonempty and `|B| ≤ |A|`, and let `r ≥ 1` be the Freiman
dimension of `A ∪ B`. Then `|A| + (r - 1) * |B| - (r + 1).choose 2 ≤ |A + B|`. -/
lemma card_add_mul_card_sub_choose_le_card_add_of_freimanDim_union
    {G : Type*} [DecidableEq G] [AddCommMonoid G] {r : ℕ} {A B : Finset G} (hr : 1 ≤ r)
    (hB : B.Nonempty) (hBA : #B ≤ #A) (hdim : freimanDim (A ∪ B) = r) :
    #A + (r - 1) * #B - (r + 1).choose 2 ≤ #(A + B) := by
  grind [card_add_sum_min_le_of_freimanDim_union hr hB hBA hdim,
    sub_mul_sub_choose_le_sum_min_of_le (r := r) (d := r - 1) hBA (by grind)]

/-- Freiman's lemma for `X + X` in terms of the Freiman dimension: if `X` is nonempty with Freiman
dimension `r ≥ 1`, then `(r + 1) * |X| - r * (r + 1) / 2 ≤ |X + X|`. -/
lemma card_add_mul_card_sub_le_card_add_of_freimanDim {G : Type*} [DecidableEq G]
    [AddCommMonoid G] {X : Finset G} (hX : X.Nonempty) (hr : freimanDim X ≠ 0) :
    (freimanDim X + 1) * #X - freimanDim X * (freimanDim X + 1) / 2 ≤ #(X + X) := by
  obtain ⟨f, hf, hdim⟩ := exists_isAddFreimanIso_of_freimanDim_eq rfl hr
  grind [two_mul_card_add_mul_card_le_of_isAddFreimanIso hX hf hdim]

/-- If `|X + X| ≤ κ * |X|` for a nonempty `X`, then `X` has Freiman dimension at most
`2 * κ - 1`. -/
theorem freimanDim_le_two_mul_sub_one_of_card_add_le {G : Type*} [DecidableEq G]
    [AddCancelCommMonoid G] {κ : ℝ} {X : Finset G} (hX : X.Nonempty)
    (hXX : (#(X + X) : ℝ) ≤ κ * #X) : (freimanDim X : ℝ) ≤ 2 * κ - 1 := by
  obtain hr | hr := (freimanDim X).eq_zero_or_pos
  · rw [hr, Nat.cast_zero]
    linarith [one_le_of_card_add_le hX hXX]
  obtain ⟨f, hf, haff⟩ := exists_isAddFreimanIso_of_freimanDim_eq rfl hr.ne'
  exact le_two_mul_sub_one_of_isAddFreimanIso hX hXX hf haff

/-- If `|X + X| ≤ κ * |X|` for a nonempty `X` and `f` is a Freiman isomorphism of order `2` from
`X` onto a subset of `ℝ^r` of affine dimension `r`, then `r ≤ κ - 1 + κ * (2 * κ - 1) / |X|`. -/
theorem le_sub_one_add_mul_div_card_of_isAddFreimanIso {G : Type*} [DecidableEq G]
    [AddCancelCommMonoid G] {r : ℕ} {κ : ℝ} {X : Finset G} {f : G → Fin r → ℝ}
    (hX : X.Nonempty) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin r → ℝ)) f)
    (hdim : (X.image f).affineDim = r) : r ≤ κ - 1 + κ * (2 * κ - 1) / #X := by
  have h : (2 * (#X + r * #X) : ℝ) ≤ 2 * #(X + X) + r * (r + 1) :=
    mod_cast two_mul_card_add_mul_card_le_of_isAddFreimanIso hX hf hdim
  have hr := le_two_mul_sub_one_of_isAddFreimanIso hX hXX hf hdim
  rw [← sub_le_iff_le_add', le_div_iff₀ (mod_cast hX.card_pos)]
  nlinarith [mul_nonneg (sub_nonneg.2 hr) (by linarith : (0 : ℝ) ≤ 2 * κ + r)]

/-- The bound `r ≤ κ - 1 + κ * (2 * κ - 1) / |X|` for a Freiman model, with the affine dimension
of the model written as the dimension of the span of its differences. -/
theorem le_sub_one_add_mul_div_card_of_isAddFreimanIso_of_finrank_span_sub_eq {G : Type*}
    [DecidableEq G] [AddCancelCommMonoid G] {r : ℕ} {κ : ℝ} {X : Finset G} {f : G → Fin r → ℝ}
    (hX : X.Nonempty) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin r → ℝ)) f)
    (hdim : Module.finrank ℝ (Submodule.span ℝ (↑(X.image f) - ↑(X.image f) : Set (Fin r → ℝ))) =
      r) :
    r ≤ κ - 1 + κ * (2 * κ - 1) / #X :=
  le_sub_one_add_mul_div_card_of_isAddFreimanIso hX hXX hf
    ((affineDim_eq_finrank_span_sub _).trans hdim)

/-- If `|X + X| ≤ κ * |X|` for a nonempty `X`, then `X` has Freiman dimension at most
`κ - 1 + κ * (2 * κ - 1) / |X|`. -/
theorem freimanDim_le_sub_one_add_mul_div_card_of_card_add_le {G : Type*} [DecidableEq G]
    [AddCancelCommMonoid G] {κ : ℝ} {X : Finset G} (hX : X.Nonempty)
    (hXX : (#(X + X) : ℝ) ≤ κ * #X) : freimanDim X ≤ κ - 1 + κ * (2 * κ - 1) / #X := by
  obtain hr | hr := (freimanDim X).eq_zero_or_pos
  · rw [hr, Nat.cast_zero]
    have hκ := one_le_of_card_add_le hX hXX
    have : 0 ≤ κ * (2 * κ - 1) / #X := div_nonneg (by nlinarith) (Nat.cast_nonneg _)
    linarith
  obtain ⟨f, hf, haff⟩ := exists_isAddFreimanIso_of_freimanDim_eq rfl hr.ne'
  exact le_sub_one_add_mul_div_card_of_isAddFreimanIso hX hXX hf haff

end

end SumOfSetsInSeveralDimensions
