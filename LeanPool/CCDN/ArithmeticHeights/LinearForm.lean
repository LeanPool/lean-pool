/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ArithmeticHeights.Affine
public import LeanPool.CCDN.ArithmeticHeights.Arakelov
public import Mathlib.NumberTheory.Height.MvPolynomial
import all Mathlib.NumberTheory.Height.Basic

/-!
# Linear forms, sums of coordinates, and the Segre relation

Mathlib bounds the height of a sum of *field elements*, `Height.mulHeight₁_sum_le`, with the
constant `#s ^ totalWeight K`, and the height of the image of a tuple under a *linear map*,
`Height.mulHeight_linearMap_apply_le`, with the constant `Nat.card ι ^ totalWeight K`. It also has
the Segre relation `Height.mulHeight_fun_mul_eq`, that the height of the multiplication table
`fun (i, j) ↦ x i * y j` is the product of the heights. This file adds the two statements about
linear forms that those leave open, and the Arakelov form of the second.

The first is the **tuple sum bound**: if every term of a sum is an entry of one and the same tuple
`w`, read off along index maps, then the height of the tuple of sums exceeds `mulHeight w` by at
most `#s ^ totalWeight K` — a *single* height on the right, not a product of heights of the terms.
This is what `Height.mulHeight₁_sum_le` cannot say, and it is the form an iteration needs, since
it costs one additive `totalWeight K * log #s` per step rather than a multiplicative factor.

The second is the **value of a linear form**, `∑ i, a i * x i`. Its projective height is not
bounded by the projective heights of `a` and `x` in any way: scaling `a` by `c` multiplies the
value by `c` and leaves `mulHeight a` fixed. The bound that is true replaces both by the *affine*
height `Height.mulHeightAff` of Layer 0.5, and then the constant is again
`Nat.card ι ^ totalWeight K`. Both are deduced here from the tuple sum bound and the Segre
relation, applied to the multiplication table of the two affine tuples.

Finally, in the Arakelov normalization of `ArithmeticHeights.Arakelov` — the ℓ² norm at the
archimedean places — **the constant disappears**: Cauchy–Schwarz at each infinite place gives
`NumberField.arakelovMulHeight_linearMap_apply_le` with constant `1`, against
`Nat.card ι ^ totalWeight K` for the sup norm. This is the first place in the development where
the Arakelov normalization is strictly better and not merely different.

## Main results

* `Height.mulHeight_sum_comp_le` and `Height.logHeight_sum_comp_le`: the tuple sum bound, with the
  constant `#s ^ totalWeight K`; `Height.mulHeight_sum_comp_le'` is the version whose index set of
  summation may depend on the coordinate.
* `Height.mulHeight₁_sum_mul_le` and `Height.logHeight₁_sum_mul_le`: the value of a linear form
  against the affine heights of its coefficients and of the point, with the constant
  `Nat.card ι ^ totalWeight K`.
* `Height.exists_not_mulHeight_add_le`: the naive tuple analogue of `Height.mulHeight₁_sum_le`
  is false over `ℚ`, for every constant.
* `NumberField.arakelovMulHeight_linearMap_apply_le` and
  `NumberField.arakelovLogHeight_linearMap_apply_le`: the Arakelov height of the image of a tuple
  under a linear map, with constant `1`.

## Implementation notes

The local halves are separated out as `AbsoluteValue.iSup_abv_sum_comp_le'` and
`IsNonarchimedean.iSup_abv_sum_comp_le'`, following Mathlib's
`AbsoluteValue.iSup_abv_linearMap_apply_le`, so that the archimedean cost `#s` and its
disappearance at the nonarchimedean places are visible before any global product is formed.

The global step needs `Height.hasFiniteMulSupport_iSup_nonarchAbsVal`, which is `private` in
`Mathlib/NumberTheory/Height/Basic.lean`; it is reached by `import all`, the way Mathlib's own
`Mathlib/NumberTheory/Height/MvPolynomial.lean` reaches it. It should be public upstream.

The affine height is a normalization and not a theorem about linear forms, so it lives in Layer
0.5, `ArithmeticHeights.Affine`, and not here. What this file uses of it is that it is not
invariant under scaling — `Height.exists_mulHeightAff_smul_ne` — which is why it and not
`Height.mulHeight` can appear on the right of a bound on a linear form's value.

The Arakelov bound is stated for a number field because `Height.AdmissibleAbsValues` records no
archimedean structure — no inner product at an archimedean place, hence no Cauchy–Schwarz.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Proposition 1.5.15 and 1.5.14 for the sum bound and the Segre relation, and Definition 2.8.1 for
the Arakelov normalization used here.

This is Layer 2.4 of the `ArithmeticHeights` roadmap.
-/

public section

open Finset Function Height AdmissibleAbsValues Real

namespace AbsoluteValue

variable {K : Type*} [Field K] {α ι κ : Type*}

/-- The local form of the tuple sum bound at an arbitrary absolute value, with the index set of
the sum allowed to depend on the coordinate: if every sum has at most `n` terms, then the supremum
of `v` over the entries of `fun i ↦ ∑ a ∈ s i, w (f a i)` is at most `n` times the supremum of `v`
over the entries of `w`. -/
theorem iSup_abv_sum_comp_le' [Nonempty ι] [Finite κ] (v : AbsoluteValue K ℝ) {n : ℕ}
    {s : ι → Finset α} (hs : ∀ i, #(s i) ≤ n) (f : α → ι → κ) (w : κ → K) :
    ⨆ i, v (∑ a ∈ s i, w (f a i)) ≤ n * ⨆ k, v (w k) := by
  have hw : (0 : ℝ) ≤ ⨆ k, v (w k) := Real.iSup_nonneg_of_nonnegHomClass v _
  refine ciSup_le fun i ↦ ?_
  calc v (∑ a ∈ s i, w (f a i))
      ≤ ∑ a ∈ s i, v (w (f a i)) := v.sum_le _ _
    _ ≤ ∑ _a ∈ s i, ⨆ k, v (w k) :=
        Finset.sum_le_sum fun a _ ↦ Finite.le_ciSup_of_le (f a i) le_rfl
    _ = #(s i) * ⨆ k, v (w k) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ n * ⨆ k, v (w k) := by gcongr; exact_mod_cast hs i

/-- The local form of the tuple sum bound at an arbitrary absolute value. -/
theorem iSup_abv_sum_comp_le [Nonempty ι] [Finite κ] (v : AbsoluteValue K ℝ) (s : Finset α)
    (f : α → ι → κ) (w : κ → K) :
    ⨆ i, v (∑ a ∈ s, w (f a i)) ≤ #s * ⨆ k, v (w k) :=
  v.iSup_abv_sum_comp_le' (s := fun _ ↦ s) (fun _ ↦ le_rfl) f w

end AbsoluteValue

namespace IsNonarchimedean

variable {K : Type*} [Field K] {α ι κ : Type*}

/-- The local form of the tuple sum bound at a nonarchimedean absolute value: there the factor
`#s` disappears, because the absolute value of a sum is bounded by the maximum of the absolute
values of its terms. -/
theorem iSup_abv_sum_comp_le' [Nonempty ι] [Finite κ] {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) (s : ι → Finset α) (f : α → ι → κ) (w : κ → K) :
    ⨆ i, v (∑ a ∈ s i, w (f a i)) ≤ ⨆ k, v (w k) := by
  have hw : (0 : ℝ) ≤ ⨆ k, v (w k) := Real.iSup_nonneg_of_nonnegHomClass v _
  refine ciSup_le fun i ↦ (hv.apply_sum_le).trans ?_
  rcases isEmpty_or_nonempty (s i : Type _) with h | h
  · simpa using hw
  exact ciSup_le fun a ↦ Finite.le_ciSup_of_le (f a.val i) le_rfl

/-- The local form of the tuple sum bound at a nonarchimedean absolute value. -/
theorem iSup_abv_sum_comp_le [Nonempty ι] [Finite κ] {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) (s : Finset α) (f : α → ι → κ) (w : κ → K) :
    ⨆ i, v (∑ a ∈ s, w (f a i)) ≤ ⨆ k, v (w k) :=
  hv.iSup_abv_sum_comp_le' (fun _ ↦ s) f w

end IsNonarchimedean

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {α ι κ : Type*}

/-!
### The height of a tuple of sums of entries of a single tuple
-/

/-- **The tuple sum bound**, with the index set of summation allowed to depend on the coordinate.
If every term of the sum is an entry of one and the same tuple `w : κ → K`, read off along index
maps `f a : ι → κ`, and every sum has at most `n` terms, then the height of the resulting tuple
exceeds that of `w` by at most `n ^ totalWeight K`.

Contrast `Height.mulHeight₁_sum_le`, whose right-hand side is a *product* of the heights of the
terms; here a single `mulHeight w` suffices, which is what makes an iteration cost an additive
rather than a multiplicative constant per step. -/
theorem mulHeight_sum_comp_le' [Finite ι] [Finite κ] {n : ℕ} (hn : 0 < n) {s : ι → Finset α}
    (hs : ∀ i, #(s i) ≤ n) (f : α → ι → κ) (w : κ → K) :
    mulHeight (fun i ↦ ∑ a ∈ s i, w (f a i)) ≤ (n : ℝ) ^ totalWeight K * mulHeight w := by
  have hcard : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs1 : (1 : ℝ) ≤ (n : ℝ) ^ totalWeight K := one_le_pow₀ hcard
  rcases eq_or_ne (fun i ↦ ∑ a ∈ s i, w (f a i)) (0 : ι → K) with h0 | h0
  · rw [h0, mulHeight_zero]
    exact hs1.trans <| le_mul_of_one_le_right (by positivity) (one_le_mulHeight w)
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp h0
  have hι : Nonempty ι := ⟨i₀⟩
  have hw : w ≠ 0 := by
    rintro rfl
    exact hi₀ (by simp)
  rw [mulHeight_eq h0, mulHeight_eq hw]
  have hconst : ((n : ℝ)) ^ totalWeight K
      = (Multiset.map (fun _ : AbsoluteValue K ℝ ↦ (n : ℝ)) archAbsVal).prod := by
    rw [Multiset.map_const', Multiset.prod_replicate]
    rfl
  rw [hconst, ← mul_assoc, ← Multiset.prod_map_mul]
  refine mul_le_mul ?_ ?_ ?_ ?_
  · exact Multiset.prod_map_le_prod_map₀ _ _
      (fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _) fun v _ ↦ v.iSup_abv_sum_comp_le' hs f w
  · exact finprod_le_finprod₀ (hasFiniteMulSupport_iSup_nonarchAbsVal h0)
      (fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _)
      (hasFiniteMulSupport_iSup_nonarchAbsVal hw) fun v ↦
        (isNonarchimedean _ v.prop).iSup_abv_sum_comp_le' s f w
  · exact finprod_nonneg fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _
  · exact Multiset.prod_map_nonneg fun v _ ↦
      mul_nonneg (by positivity) (Real.iSup_nonneg_of_nonnegHomClass v _)

/-- **The tuple sum bound**, all the sums over the same index set. -/
theorem mulHeight_sum_comp_le [Finite ι] [Finite κ] {s : Finset α} (hs : s.Nonempty)
    (f : α → ι → κ) (w : κ → K) :
    mulHeight (fun i ↦ ∑ a ∈ s, w (f a i)) ≤ (#s : ℝ) ^ totalWeight K * mulHeight w :=
  mulHeight_sum_comp_le' hs.card_pos (s := fun _ ↦ s) (fun _ ↦ le_rfl) f w

/-- The logarithmic form of `Height.mulHeight_sum_comp_le`. -/
theorem logHeight_sum_comp_le [Finite ι] [Finite κ] {s : Finset α} (hs : s.Nonempty)
    (f : α → ι → κ) (w : κ → K) :
    logHeight (fun i ↦ ∑ a ∈ s, w (f a i)) ≤ totalWeight K * log #s + logHeight w := by
  have hcard : (0 : ℝ) < (#s : ℝ) := by exact_mod_cast hs.card_pos
  simp only [logHeight_eq_log_mulHeight]
  refine (log_le_log (mulHeight_pos _) (mulHeight_sum_comp_le hs f w)).trans_eq ?_
  rw [log_mul (by positivity) (mulHeight_ne_zero w), log_pow]

/-!
### The value of a linear form
-/

/-- **The height of the value of a linear form.** The affine height of `∑ i, a i * x i` is at
most `Nat.card ι ^ totalWeight K` times the product of the affine heights of the coefficient
tuple `a` and of the point `x`.

Both heights on the right have to be affine: scaling `a` by `c` multiplies the value by `c` and
leaves `mulHeight a` unchanged, so with projective heights the statement is false for every
constant.

The proof is the Segre relation `Height.mulHeight_fun_mul_eq` applied to the multiplication table
of the two affine tuples, followed by `Height.mulHeight_sum_comp_le'`: the pair
`![∑ i, a i * x i, 1]` reads off `Nat.card ι` entries of that table in its first coordinate and a
single entry in its second. -/
theorem mulHeight₁_sum_mul_le [Fintype ι] [Nonempty ι] (a x : ι → K) :
    mulHeight₁ (∑ i, a i * x i)
      ≤ (Nat.card ι : ℝ) ^ totalWeight K * (mulHeightAff a * mulHeightAff x) := by
  classical
  have hpos : 0 < Nat.card ι := Nat.card_pos
  set A : Option ι → K := fun o ↦ o.elim 1 a with hA
  set X : Option ι → K := fun o ↦ o.elim 1 x with hX
  set w : Option ι × Option ι → K := fun p ↦ A p.1 * X p.2 with hw
  set s : Fin 2 → Finset (Option ι) :=
    ![(Finset.univ : Finset ι).image some, {none}] with hs
  have hcard : ∀ j, #(s j) ≤ Nat.card ι := by
    intro j
    fin_cases j
    · simp [hs, Finset.card_image_of_injective _ (Option.some_injective ι),
        Nat.card_eq_fintype_card]
    · simpa [hs] using hpos.nat_succ_le
  have key : (fun j : Fin 2 ↦ ∑ o ∈ s j, w (o, o)) = ![∑ i, a i * x i, 1] := by
    ext j
    fin_cases j
    · simp [hs, hw, hA, hX, Finset.sum_image, Option.some_injective ι]
    · simp [hs, hw, hA, hX]
  have hbound := mulHeight_sum_comp_le' (K := K) hpos hcard (fun o (_ : Fin 2) ↦ (o, o)) w
  rw [key] at hbound
  rw [mulHeight₁_eq_mulHeight]
  refine hbound.trans ?_
  gcongr
  exact le_of_eq (mulHeight_fun_mul_eq (optionElim_one_ne_zero a) (optionElim_one_ne_zero x))

/-- The logarithmic form of `Height.mulHeight₁_sum_mul_le`. -/
theorem logHeight₁_sum_mul_le [Fintype ι] [Nonempty ι] (a x : ι → K) :
    logHeight₁ (∑ i, a i * x i)
      ≤ totalWeight K * log (Nat.card ι) + (logHeightAff a + logHeightAff x) := by
  have hpos : (0 : ℝ) < Nat.card ι := by exact_mod_cast Nat.card_pos (α := ι)
  simp only [logHeight₁_eq_log_mulHeight₁, logHeightAff_eq_log_mulHeightAff]
  refine (log_le_log (mulHeight₁_pos _) (mulHeight₁_sum_mul_le a x)).trans_eq ?_
  rw [log_mul (pow_ne_zero _ hpos.ne') (mul_ne_zero (mulHeightAff_ne_zero a)
      (mulHeightAff_ne_zero x)),
    log_mul (mulHeightAff_ne_zero a) (mulHeightAff_ne_zero x), log_pow]

/-!
### The naive tuple analogue of the sum bound is false
-/

/-- Any field element whose height exceeds `2 ^ totalWeight K` refutes the tuple analogue of
`Height.mulHeight₁_sum_le`: the two tuples `![x, 0]` and `![0, 1]` both have height `1`, while
their sum `![x, 1]` has height `mulHeight₁ x`. The mechanism is scaling invariance
(`Height.mulHeight_smul_eq_mulHeight`), which the left-hand side of such a bound does not enjoy,
so no choice of constant can repair the statement. -/
theorem not_mulHeight_add_le_of_lt_mulHeight₁ {x : K}
    (hx : (2 : ℝ) ^ totalWeight K < mulHeight₁ x) :
    ¬ mulHeight ((![x, 0] : Fin 2 → K) + (![0, 1] : Fin 2 → K))
        ≤ (2 : ℝ) ^ totalWeight K
            * (mulHeight (![x, 0] : Fin 2 → K) * mulHeight (![0, 1] : Fin 2 → K)) := by
  have h1 : (![x, 0] : Fin 2 → K) + (![0, 1] : Fin 2 → K) = ![x, 1] := by
    ext i
    fin_cases i <;> simp
  rw [h1, ← mulHeight₁_eq_mulHeight]
  simpa using not_le.2 hx

/-- The tuple analogue of `Height.mulHeight₁_sum_le` fails already over `ℚ`. This is why the
right-hand side of `Height.mulHeight₁_sum_mul_le` is stated with affine heights, and why
`Height.mulHeight_sum_comp_le` reads off all its summands from *one* tuple. -/
theorem exists_not_mulHeight_add_le :
    ∃ x : ℚ, ¬ mulHeight ((![x, 0] : Fin 2 → ℚ) + (![0, 1] : Fin 2 → ℚ))
      ≤ (2 : ℝ) ^ totalWeight ℚ
          * (mulHeight (![x, 0] : Fin 2 → ℚ) * mulHeight (![0, 1] : Fin 2 → ℚ)) := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((2 : ℝ) ^ totalWeight ℚ)
  have hpos : (0 : ℝ) ≤ 2 ^ totalWeight ℚ := by positivity
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero] at hn
    exact hpos.not_gt hn
  have : NeZero n := ⟨hn0⟩
  exact ⟨(n : ℚ), not_mulHeight_add_le_of_lt_mulHeight₁ (by rwa [Rat.mulHeight₁_natCast])⟩

end Height

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-!
### Linear maps in the Arakelov normalization

At an infinite place the local factor of the Arakelov height is an ℓ² norm, so Cauchy–Schwarz
bounds the local factor of `A x` by the product of those of `A` and `x` with no constant at all;
at a finite place the sup norm does the same, by the ultrametric inequality. The constant
`Nat.card ι ^ totalWeight K` of `Height.mulHeight_linearMap_apply_le` therefore disappears.
-/

omit [NumberField K] in
/-- Cauchy–Schwarz at an infinite place: the squared ℓ² norm of `A x` is at most the product of
those of `A` and `x`. This is where the cardinality of the index set is not paid. -/
private lemma sum_sq_apply_linearMap_le (v : InfinitePlace K) (A : ι' × ι → K) (x : ι → K) :
    ∑ j, v (∑ i, A (j, i) * x i) ^ 2 ≤ (∑ p, v (A p) ^ 2) * ∑ i, v (x i) ^ 2 := by
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  calc v (∑ i, A (j, i) * x i) ^ 2
      ≤ (∑ i, v (A (j, i)) * v (x i)) ^ 2 := by
        gcongr ?_ ^ 2
        refine (v.1.sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ ↦ ?_)
        exact map_mul ..
    _ ≤ (∑ i, v (A (j, i)) ^ 2) * ∑ i, v (x i) ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- **The Arakelov height of the image of a tuple under a linear map**, with constant `1`. Let
`A : ι' × ι → K`, read as a linear map from `ι → K` to `ι' → K`. Then

`arakelovMulHeight (A x) ≤ arakelovMulHeight A * arakelovMulHeight x`.

Mathlib's sup-norm statement `Height.mulHeight_linearMap_apply_le` carries the constant
`Nat.card ι ^ totalWeight K`, which cannot be removed there — the affine form of that is the
second example at the end of this file; here Cauchy–Schwarz at each infinite place removes it.
No hypothesis on `A` or `x` is needed: the junk value `arakelovMulHeight 0 = 1` is at most the
right-hand side, which is at least `1`. -/
theorem arakelovMulHeight_linearMap_apply_le (A : ι' × ι → K) (x : ι → K) :
    arakelovMulHeight (fun j ↦ ∑ i, A (j, i) * x i)
      ≤ arakelovMulHeight A * arakelovMulHeight x := by
  rcases eq_or_ne (fun j ↦ ∑ i, A (j, i) * x i) (0 : ι' → K) with h0 | h0
  · rw [h0, arakelovMulHeight_zero]
    exact one_le_mul_of_one_le_of_one_le (one_le_arakelovMulHeight A) (one_le_arakelovMulHeight x)
  have hA : A ≠ 0 := by
    rintro rfl
    exact h0 (by ext j; simp)
  have hx : x ≠ 0 := by
    rintro rfl
    exact h0 (by ext j; simp)
  have hfinA : (fun v : FinitePlace K ↦ ⨆ p, v (A p)).HasFiniteMulSupport :=
    Height.hasFiniteMulSupport_iSup_nonarchAbsVal hA
  have hfinx : (fun v : FinitePlace K ↦ ⨆ i, v (x i)).HasFiniteMulSupport :=
    Height.hasFiniteMulSupport_iSup_nonarchAbsVal hx
  have hfin0 : (fun v : FinitePlace K ↦ ⨆ j, v (∑ i, A (j, i) * x i)).HasFiniteMulSupport :=
    Height.hasFiniteMulSupport_iSup_nonarchAbsVal h0
  have hnonarch (v : FinitePlace K) :
      ⨆ j, v (∑ i, A (j, i) * x i) ≤ (⨆ p, v (A p)) * ⨆ i, v (x i) :=
    IsNonarchimedean.iSup_abv_linearMap_apply_le (v := v.1) (FinitePlace.add_le v) A x
  rw [arakelovMulHeight_eq h0, arakelovMulHeight_eq hA, arakelovMulHeight_eq hx, mul_mul_mul_comm]
  refine mul_le_mul ?_ ?_ ?_ ?_
  · rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ ↦ by positivity) fun v _ ↦ ?_
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (sum_sq_apply_linearMap_le v A x) (by positivity)
  · rw [← _root_.finprod_mul_distrib hfinA hfinx]
    exact finprod_le_finprod₀ hfin0 (fun v ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)
      (hfinA.mul hfinx) hnonarch
  · exact _root_.finprod_nonneg fun v ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _
  · positivity

/-- The logarithmic form of `NumberField.arakelovMulHeight_linearMap_apply_le`: in the Arakelov
normalization a linear map costs nothing beyond the heights of the matrix and of the point. -/
theorem arakelovLogHeight_linearMap_apply_le (A : ι' × ι → K) (x : ι → K) :
    arakelovLogHeight (fun j ↦ ∑ i, A (j, i) * x i)
      ≤ arakelovLogHeight A + arakelovLogHeight x := by
  simp only [arakelovLogHeight_eq_log_arakelovMulHeight]
  refine (log_le_log (arakelovMulHeight_pos _)
    (arakelovMulHeight_linearMap_apply_le A x)).trans_eq ?_
  rw [log_mul (arakelovMulHeight_ne_zero A) (arakelovMulHeight_ne_zero x)]

end NumberField

/-!
### Examples

The tests that fix the constants: that `#s ^ totalWeight K` in the tuple sum bound and
`Nat.card ι ^ totalWeight K` in the linear-form bound are attained over `ℚ`, and that the
Arakelov constant `1` is attained too.
-/

section Examples

open Height NumberField

/-- **Sharpness of the tuple sum bound.** Over `ℚ`, reading two entries of `w = ![1, 0]` off in
each of two coordinates produces the tuple `![2, 1]` of height `2`, while `w` has height `1` and
`#s ^ totalWeight ℚ = 2`. The constant of `Height.mulHeight_sum_comp_le` is therefore attained. -/
example :
    mulHeight (fun i : Fin 2 ↦ ∑ a ∈ (Finset.univ : Finset (Fin 2)),
        (![1, 0] : Fin 2 → ℚ) (![![0, 0], ![0, 1]] a i)) = 2
      ∧ mulHeight (![1, 0] : Fin 2 → ℚ) = 1
      ∧ ((#(Finset.univ : Finset (Fin 2)) : ℝ)) ^ totalWeight ℚ = 2 := by
  have hw : totalWeight ℚ = 1 := by
    rw [NumberField.totalWeight_eq_finrank, Module.finrank_self]
  have h1 : (fun i : Fin 2 ↦ ∑ a ∈ (Finset.univ : Finset (Fin 2)),
      (![1, 0] : Fin 2 → ℚ) (![![0, 0], ![0, 1]] a i))
      = ((↑) : ℤ → ℚ) ∘ (![2, 1] : Fin 2 → ℤ) := by
    ext i
    fin_cases i <;> norm_num [Fin.sum_univ_two]
  have h2 : (![1, 0] : Fin 2 → ℚ) = ((↑) : ℤ → ℚ) ∘ (![1, 0] : Fin 2 → ℤ) := by
    ext i
    fin_cases i <;> simp
  refine ⟨?_, ?_, by rw [hw]; norm_num⟩
  · rw [h1, Rat.mulHeight_eq_max_abs_of_gcd_eq_one (by decide)]
    norm_num [show (⨆ i : Fin 2, |(![2, 1] : Fin 2 → ℤ) i|) = 2 from
      le_antisymm (ciSup_le fun i ↦ by fin_cases i <;> decide)
        (Finite.le_ciSup_of_le 0 (by decide))]
  · rw [h2, Rat.mulHeight_eq_max_abs_of_gcd_eq_one (by decide)]
    norm_num [show (⨆ i : Fin 2, |(![1, 0] : Fin 2 → ℤ) i|) = 1 from
      le_antisymm (ciSup_le fun i ↦ by fin_cases i <;> decide)
        (Finite.le_ciSup_of_le 0 (by decide))]

/-- **Sharpness of the linear-form bound.** Over `ℚ` with `a = x = ![1, 1]` the value is `2`, of
affine height `2`, while both affine heights on the right are `1` and
`Nat.card (Fin 2) ^ totalWeight ℚ = 2`. So the cardinality in `Height.mulHeight₁_sum_mul_le`
cannot be removed — which is exactly what Cauchy–Schwarz achieves in the Arakelov normalization,
`NumberField.arakelovMulHeight_linearMap_apply_le`. -/
example :
    mulHeight₁ (∑ i, (![1, 1] : Fin 2 → ℚ) i * (![1, 1] : Fin 2 → ℚ) i) = 2
      ∧ mulHeightAff (![1, 1] : Fin 2 → ℚ) = 1
      ∧ (Nat.card (Fin 2) : ℝ) ^ totalWeight ℚ = 2 := by
  have hw : totalWeight ℚ = 1 := by
    rw [NumberField.totalWeight_eq_finrank, Module.finrank_self]
  have haff : (fun o : Option (Fin 2) ↦ o.elim 1 (![1, 1] : Fin 2 → ℚ)) = 1 := by
    ext o
    rcases o with _ | i
    · rfl
    · fin_cases i <;> rfl
  refine ⟨?_, by rw [mulHeightAff, haff, mulHeight_one],
    by rw [hw, Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num⟩
  rw [show (∑ i, (![1, 1] : Fin 2 → ℚ) i * (![1, 1] : Fin 2 → ℚ) i) = ((2 : ℕ) : ℚ) by
    norm_num [Fin.sum_univ_two]]
  rw [Rat.mulHeight₁_natCast]
  norm_num

/-- **Sharpness of the Arakelov constant.** For a one-element source the linear map is a
reindexing, so `NumberField.arakelovMulHeight_linearMap_apply_le` is an equality and the
constant `1` cannot be lowered. -/
example {K : Type*} [Field K] [NumberField K] {ι' : Type*} [Fintype ι'] (A : ι' × Fin 1 → K) :
    arakelovMulHeight (fun j ↦ ∑ i, A (j, i) * (1 : Fin 1 → K) i)
      = arakelovMulHeight A * arakelovMulHeight (1 : Fin 1 → K) := by
  have he : (fun j ↦ ∑ i, A (j, i) * (1 : Fin 1 → K) i)
      = A ∘ (Equiv.prodUnique ι' (Fin 1)).symm := by
    ext j
    simp
  rw [he, arakelovMulHeight_comp_equiv (Equiv.prodUnique ι' (Fin 1)).symm,
    arakelovMulHeight_eq_one_of_subsingleton (1 : Fin 1 → K), mul_one]

end Examples
