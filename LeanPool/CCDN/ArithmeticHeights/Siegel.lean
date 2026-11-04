/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ArithmeticHeights.Absolute
public import Mathlib.NumberTheory.NumberField.House
public import Mathlib.NumberTheory.SiegelsLemma

/-!
# Siegel's lemma, in height form

Mathlib proves the classical Siegel lemma as a statement about the **sup norm**: a nonzero
`M × N` integer matrix with `M < N` kills a nonzero integer vector of norm at most
`(N ‖A‖) ^ (M / (N - M))`. This file restates it in the vocabulary of heights, which is what the
rest of the roadmap consumes; the translation between the two normalizations is isolated as a
lemma of its own, the exponent is shown to be sharp, and the number-field corollary is read off
Mathlib's `house`-normalized version the same way.

## Main results

* `Rat.gcd_mul_mulHeight_intCast`: the translation. For a nonzero integer tuple,
  `gcd x * H(x) = max i, |x i|`; `Rat.mulHeight_intCast_le` is the inequality it is used through.
* `Int.Matrix.exists_ne_zero_mulVec_eq_zero_iSup_abs_le` and
  `Int.Matrix.exists_ne_zero_mulVec_eq_zero_mulHeight_le`: Siegel's lemma with an explicit bound
  `B` on the entries, in the sup norm and in the height, both at `(N B) ^ (M / (N - M))`.
* `Int.Matrix.exists_forall_pow_le_iSup_abs`: the exponent `M / (N - M)` is sharp.
* `NumberField.absMulHeight_le_iSup_house`: the absolute height of a tuple of algebraic integers
  is at most the largest house of its entries.
* `NumberField.exists_forall_exists_ne_zero_mulVec_eq_zero_absMulHeight_le`: Siegel's lemma over a
  number field in height form, Bombieri–Gubler's Corollary 2.9.2.

## Implementation notes

⚠ **The height form is not a strengthening, because the content can always be divided out.** The
height of an integer tuple is its sup norm divided by the greatest common divisor of its entries,
so `H(x) ≤ max i, |x i|` with equality exactly on primitive tuples. That makes the height bound
formally weaker-looking hypotheses and formally stronger conclusions, but nothing is gained: the
primitive multiple of a kernel vector is again a kernel vector, and it is the one on which the two
statements coincide. What the translation buys is the *vocabulary*: everything downstream of
Layer 1 is stated for `Height.mulHeight`, and a sup norm cannot be fed to it.

⚠ **The exponent is sharp already at `N = M + 1`, and only the factor `N ^ (M / (N - M))` is
slack.** The equations `B xᵢ = xᵢ₊₁` have kernel the line through `(1, B, B², …, B ^ M)`, whose
nonzero integer points all have sup norm at least `B ^ M`, against the bound `((M + 1) B) ^ M`.
Taking `k` such blocks side by side realizes every exponent `M = k M / (k (M + 1) - k M)`, so the
sharpness is not an artifact of `N - M = 1`. The bound is nevertheless not *invariant*: it changes
under `A ↦ U A` for `U ∈ GL_M(ℤ)`, which leaves the kernel alone, and removing that defect is the
whole content of Layer 5.2.

⚠ **Passing from the house to the height costs no constant at all.** For a tuple of algebraic
integers every finite local factor is at most `1` — the finite part of the height is the inverse
norm of the ideal the entries generate, and that norm is a positive integer — while each infinite
place is the modulus of a conjugate and so is dominated by the house. The infinite factors carry
the weights `mult v`, which sum to `[K : ℚ]`, and that is exactly the root the absolute
normalization takes. So `H_abs(x) ≤ max l, house (x l)` with no degree factor, and Mathlib's
number-field Siegel bound transfers verbatim.

⚠ **Mathlib's number-field constant is `private`.** `c₁ K` of
`Mathlib/NumberTheory/NumberField/House.lean` cannot be named from outside that file, so the
restatement has to quantify over it existentially — which is also the shape Bombieri–Gubler state
the corollary in — and the witness is supplied by unification against the theorem it is proved
from.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 2.9.1 and Corollary 2.9.2.

M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction*, Springer (2000),
Lemma D.4.1, which is the statement Mathlib's file is proved against.

This is Layer 5.1 of the `ArithmeticHeights` roadmap.
-/

public section

open Finset Height Matrix

/-! ### The sup norm of an integer tuple -/

/-- The sup norm of an integer tuple is the maximum of the absolute values of its entries. The
left-hand side is the shape Mathlib's Siegel lemma is stated in, the right-hand side the shape
every height statement is stated in. -/
theorem Int.pi_norm_eq_iSup_abs {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℤ) :
    ‖x‖ = ((⨆ i, |x i| : ℤ) : ℝ) := by
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ |x i|)
  have hb : ∀ i, |x i| ≤ ⨆ j, |x j| := fun i ↦
    le_ciSup (f := fun j ↦ |x j|) (Finite.bddAbove_range _) i
  refine le_antisymm (pi_norm_le_iff_of_nonneg ?_ |>.2 fun i ↦ ?_) ?_
  · exact_mod_cast (abs_nonneg (x i₀)).trans (hb i₀)
  · rw [Int.norm_eq_abs, ← Int.cast_abs, Int.cast_le]
    exact hb i
  · rw [← hi₀, Int.cast_abs, ← Int.norm_eq_abs]
    exact norm_le_pi_norm x i₀

namespace Rat

variable {ι : Type*} [Nonempty ι] {x : ι → ℤ}

/-- Multiplication by a nonnegative integer commutes with a finite supremum. -/
private lemma iSup_const_mul [Finite ι] {g : ℤ} (hg : 0 ≤ g) (f : ι → ℤ) :
    ⨆ i, g * f i = g * ⨆ i, f i := by
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ g * f i)
  obtain ⟨j₀, hj₀⟩ := exists_eq_ciSup_of_finite (f := f)
  have h1 : f i₀ ≤ f j₀ := (le_ciSup (Finite.bddAbove_range f) i₀).trans_eq hj₀.symm
  have h2 : g * f j₀ ≤ g * f i₀ :=
    (le_ciSup (Finite.bddAbove_range fun i ↦ g * f i) j₀).trans_eq hi₀.symm
  rw [← hi₀, ← hj₀]
  exact le_antisymm (mul_le_mul_of_nonneg_left h1 hg) h2

/-- **The sup-norm-to-height translation.** The multiplicative height of a nonzero tuple of
integers, read as a tuple of rationals, is the maximum of the absolute values of its entries
divided by their greatest common divisor. Mathlib's `Rat.mulHeight_eq_max_abs_of_gcd_eq_one` is
the primitive case; the content is what the projective height divides out. -/
theorem gcd_mul_mulHeight_intCast [Fintype ι] (hx : x ≠ 0) :
    ((univ.gcd x : ℤ) : ℝ) * mulHeight (((↑) : ℤ → ℚ) ∘ x) = ((⨆ i, |x i| : ℤ) : ℝ) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  have hg0 : univ.gcd x ≠ 0 := fun h ↦ hi₀ (Finset.gcd_eq_zero_iff.1 h i₀ (mem_univ i₀))
  have hgnn : 0 ≤ univ.gcd x := by
    rw [← Finset.normalize_gcd, ← Int.abs_eq_normalize]
    exact abs_nonneg _
  have hdvd : ∀ i, univ.gcd x ∣ x i := fun i ↦ Finset.gcd_dvd (mem_univ i)
  set y : ι → ℤ := fun i ↦ x i / univ.gcd x
  have hxy : ∀ i, x i = univ.gcd x * y i := fun i ↦ (Int.mul_ediv_cancel' (hdvd i)).symm
  have hy1 : univ.gcd y = 1 := Finset.gcd_div_eq_one (mem_univ i₀) hi₀
  have hsmul : (((↑) : ℤ → ℚ) ∘ x) = ((univ.gcd x : ℤ) : ℚ) • (((↑) : ℤ → ℚ) ∘ y) := by
    funext i
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    exact_mod_cast congrArg (Int.cast : ℤ → ℚ) (hxy i)
  rw [hsmul, mulHeight_smul_eq_mulHeight _ (by exact_mod_cast hg0),
    mulHeight_eq_max_abs_of_gcd_eq_one hy1, ← Int.cast_mul, ← iSup_const_mul hgnn]
  congr 1
  exact congrArg _ (funext fun i ↦ by rw [hxy i, abs_mul, abs_of_nonneg hgnn])

/-- The height of an integer tuple is at most its sup norm, with equality exactly when the tuple
is primitive. This is the direction Siegel's lemma is read in. -/
theorem mulHeight_intCast_le [Finite ι] (hx : x ≠ 0) :
    mulHeight (((↑) : ℤ → ℚ) ∘ x) ≤ ((⨆ i, |x i| : ℤ) : ℝ) := by
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  have hg0 : univ.gcd x ≠ 0 := fun h ↦ hi₀ (Finset.gcd_eq_zero_iff.1 h i₀ (mem_univ i₀))
  have hgnn : 0 ≤ univ.gcd x := by
    rw [← Finset.normalize_gcd, ← Int.abs_eq_normalize]
    exact abs_nonneg _
  have hg1 : (1 : ℝ) ≤ ((univ.gcd x : ℤ) : ℝ) := by
    rw [← Int.cast_one, Int.cast_le]
    omega
  rw [← gcd_mul_mulHeight_intCast hx]
  exact le_mul_of_one_le_left (mulHeight_pos _).le hg1

end Rat

/-! ### Siegel's lemma in height form -/

attribute [local instance] Matrix.seminormedAddCommGroup

namespace Int.Matrix

variable {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℤ)

/-- **Siegel's lemma, with an explicit bound on the entries.** A system of `M` linear equations in
`N > M` unknowns with integer coefficients of absolute value at most `B` has a nonzero integer
solution of sup norm at most `(N B) ^ (M / (N - M))`.

This is Mathlib's `Int.Matrix.exists_ne_zero_int_vec_norm_le` with the matrix norm traded for a
bound on the entries; the hypothesis `1 ≤ B` is what removes the `max 1 ‖A‖` there, and costs
nothing, since a nonzero integer matrix has an entry of absolute value at least `1`. -/
theorem exists_ne_zero_mulVec_eq_zero_iSup_abs_le {B : ℤ} (hB : 1 ≤ B) (hA : ∀ i j, |A i j| ≤ B)
    (hn : Fintype.card α < Fintype.card β) (hm : 0 < Fintype.card α) :
    ∃ x : β → ℤ, x ≠ 0 ∧ A *ᵥ x = 0 ∧
      ((⨆ j, |x j| : ℤ) : ℝ) ≤ ((Fintype.card β : ℝ) * B) ^
        ((Fintype.card α : ℝ) / ((Fintype.card β : ℝ) - Fintype.card α)) := by
  have _ : Nonempty β := Fintype.card_pos_iff.1 (hm.trans hn)
  have hB' : (0 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB.trans' zero_le_one
  have hAB : ‖A‖ ≤ (B : ℝ) := by
    rw [Matrix.norm_le_iff hB']
    intro i j
    rw [Int.norm_eq_abs, ← Int.cast_abs, Int.cast_le]
    exact hA i j
  obtain ⟨x, hx0, hxA, hxb⟩ := exists_ne_zero_int_vec_norm_le A hn hm
  refine ⟨x, hx0, hxA, ?_⟩
  rw [← Int.pi_norm_eq_iSup_abs]
  refine hxb.trans (Real.rpow_le_rpow ?_ ?_ ?_)
  · exact mul_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one (le_max_left _ _))
  · exact mul_le_mul_of_nonneg_left (max_le (by exact_mod_cast hB) hAB) (Nat.cast_nonneg _)
  · exact div_nonneg (Nat.cast_nonneg _) (by simpa using (Nat.cast_le (α := ℝ)).2 hn.le)

/-- **Siegel's lemma in height form** (Bombieri–Gubler, Lemma 2.9.1; Hindry–Silverman, Lemma
D.4.1). The solution the previous statement produces has multiplicative height at most
`(N B) ^ (M / (N - M))` as well: by `Rat.gcd_mul_mulHeight_intCast` the height of an integer tuple
is at most its sup norm, and the two agree when the tuple is primitive — which the minimal
solution is, but which the statement does not need. -/
theorem exists_ne_zero_mulVec_eq_zero_mulHeight_le {B : ℤ} (hB : 1 ≤ B) (hA : ∀ i j, |A i j| ≤ B)
    (hn : Fintype.card α < Fintype.card β) (hm : 0 < Fintype.card α) :
    ∃ x : β → ℤ, x ≠ 0 ∧ A *ᵥ x = 0 ∧
      mulHeight (((↑) : ℤ → ℚ) ∘ x) ≤ ((Fintype.card β : ℝ) * B) ^
        ((Fintype.card α : ℝ) / ((Fintype.card β : ℝ) - Fintype.card α)) := by
  have _ : Nonempty β := Fintype.card_pos_iff.1 (hm.trans hn)
  obtain ⟨x, hx0, hxA, hxb⟩ := exists_ne_zero_mulVec_eq_zero_iSup_abs_le A hB hA hn hm
  exact ⟨x, hx0, hxA, (Rat.mulHeight_intCast_le hx0).trans hxb⟩

/-- **The exponent `M / (N - M)` is sharp**, already for `N = M + 1`, where it is `M`. The
`M × (M + 1)` matrix of the equations `B xᵢ = xᵢ₊₁` has entries of absolute value at most `B` and
kernel the line spanned by `(1, B, B², …, B ^ M)`, so every nonzero solution has sup norm at least
`B ^ M`, against a bound of `((M + 1) B) ^ M`: only the factor `(M + 1) ^ M` is slack.

Taking `k` copies of this system side by side gives, for every `k`, an `k M × k (M + 1)` system
with the same conclusion and exponent `k M / k = M`, so no exponent below `M / (N - M)` can be
substituted in the statement above. -/
theorem exists_forall_pow_le_iSup_abs (M : ℕ) {B : ℤ} (hB : 1 ≤ B) :
    ∃ A : Matrix (Fin M) (Fin (M + 1)) ℤ, (∀ i j, |A i j| ≤ B) ∧
      ∀ x : Fin (M + 1) → ℤ, x ≠ 0 → A *ᵥ x = 0 → B ^ M ≤ ⨆ j, |x j| := by
  classical
  set A : Matrix (Fin M) (Fin (M + 1)) ℤ := Matrix.of fun i j ↦
    B * (if j = i.castSucc then 1 else 0) - (if j = i.succ then 1 else 0) with hAdef
  have hne : ∀ i : Fin M, i.castSucc ≠ i.succ := fun i ↦
    ne_of_lt (Fin.castSucc_lt_succ : i.castSucc < i.succ)
  have hmul : ∀ (x : Fin (M + 1) → ℤ) (i : Fin M),
      (A *ᵥ x) i = B * x i.castSucc - x i.succ := by
    intro x i
    simp [hAdef, Matrix.mulVec, dotProduct, sub_mul, ite_mul, Finset.sum_sub_distrib,
      Finset.sum_ite_eq']
  refine ⟨A, ?_, ?_⟩
  · intro i j
    rcases eq_or_ne j i.castSucc with rfl | hj
    · simp [hAdef, hne i, abs_of_nonneg (hB.trans' zero_le_one)]
    · rcases eq_or_ne j i.succ with rfl | hj'
      · simpa [hAdef, hj] using hB
      · simpa [hAdef, hj, hj'] using hB.trans' zero_le_one
  · intro x hx0 hxA
    have hstep : ∀ i : Fin M, B * x i.castSucc = x i.succ := by
      intro i
      have h : B * x i.castSucc - x i.succ = 0 := by
        rw [← hmul x i]; exact congrFun hxA i
      exact eq_of_sub_eq_zero h
    have hpow : ∀ j : Fin (M + 1), x j = B ^ (j : ℕ) * x 0 := by
      intro j
      induction j using Fin.induction with
      | zero => simp
      | succ i ih =>
        rw [← hstep i, ih, Fin.val_castSucc, Fin.val_succ, pow_succ]
        ring
    have hx00 : x 0 ≠ 0 := fun h ↦ hx0 (funext fun j ↦ by simp [hpow j, h])
    have hlast : B ^ M ≤ |x (Fin.last M)| := by
      rw [hpow (Fin.last M), Fin.val_last, abs_mul, abs_pow,
        abs_of_nonneg (hB.trans' zero_le_one)]
      exact le_mul_of_one_le_right (pow_nonneg (hB.trans' zero_le_one) M)
        (Int.one_le_abs hx00)
    exact hlast.trans (le_ciSup (f := fun j ↦ |x j|) (Finite.bddAbove_range _) (Fin.last M))

end Int.Matrix

/-! ### Siegel's lemma over a number field -/

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]

/-- **The house bounds the height.** For a nonzero tuple of algebraic integers the absolute
multiplicative height is at most the largest house of its entries: the finite local factors are at
most `1` because the entries are integral, and each infinite one is bounded by the house because an
infinite place is the modulus of a conjugate.

This is the whole of the passage from Mathlib's `NumberField.house`-normalized Siegel lemma to a
height statement. -/
theorem absMulHeight_le_iSup_house {x : ι → 𝓞 K} (hx : x ≠ 0) :
    absMulHeight (fun i ↦ ((x i : K))) ≤ ⨆ i, house ((x i : K)) := by
  obtain ⟨i₁, hi₁⟩ := Function.ne_iff.mp hx
  have hx0 : (fun i ↦ ((x i : K))) ≠ 0 := Function.ne_iff.mpr ⟨i₁, by simpa using hi₁⟩
  have hHb : ∀ i, house ((x i : K)) ≤ ⨆ j, house ((x j : K)) := fun i ↦
    le_ciSup (f := fun j ↦ house ((x j : K))) (Finite.bddAbove_range _) i
  have hH0 : 0 ≤ ⨆ j, house ((x j : K)) := (house_nonneg _).trans (hHb i₁)
  have hple : ∀ (v : InfinitePlace K) (i : ι), v ((x i : K)) ≤ house ((x i : K)) := by
    intro v i
    have h := norm_le_pi_norm (canonicalEmbedding K ((x i : K))) v.embedding
    rwa [canonicalEmbedding.apply_at, InfinitePlace.norm_embedding_eq] at h
  have hfin : ∏ᶠ v : FinitePlace K, (⨆ i, v ((x i : K))) ≤ 1 := by
    have hone := absNorm_mul_finprod_finitePlace_eq_one hx
    have hn1 : (1 : ℝ) ≤ ((Ideal.span (Set.range x)).absNorm : ℝ) := by
      rw [← Nat.cast_one, Nat.cast_le, Nat.one_le_iff_ne_zero]
      intro h
      rw [h, Nat.cast_zero, zero_mul] at hone
      exact absurd hone (by norm_num)
    refine le_of_mul_le_mul_left ?_ (lt_of_lt_of_le zero_lt_one hn1)
    rw [hone, mul_one]
    exact hn1
  have hmulH : Height.mulHeight (fun i ↦ ((x i : K))) ≤
      (⨆ j, house ((x j : K))) ^ Module.finrank ℚ K := by
    rw [NumberField.mulHeight_eq hx0]
    have hprod : ∏ v : InfinitePlace K, (⨆ i, v ((x i : K))) ^ v.mult ≤
        (⨆ j, house ((x j : K))) ^ Module.finrank ℚ K := by
      calc ∏ v : InfinitePlace K, (⨆ i, v ((x i : K))) ^ v.mult
          ≤ ∏ v : InfinitePlace K, (⨆ j, house ((x j : K))) ^ v.mult := by
            gcongr <;> intros <;>
              first
                | exact pow_nonneg (Real.iSup_nonneg fun i ↦ apply_nonneg _ _) _
                | exact Real.iSup_nonneg fun i ↦ apply_nonneg _ _
                | exact Finite.bddAbove_range fun j ↦ house ((x j : K))
                | exact hple _ _
        _ = (⨆ j, house ((x j : K))) ^ ∑ v : InfinitePlace K, v.mult :=
            Finset.prod_pow_eq_pow_sum _ _ _
        _ = (⨆ j, house ((x j : K))) ^ Module.finrank ℚ K := by rw [InfinitePlace.sum_mult_eq]
    refine le_trans (mul_le_mul hprod hfin ?_ (pow_nonneg hH0 _)) (le_of_eq (mul_one _))
    exact finprod_nonneg fun v ↦ Real.iSup_nonneg fun i ↦ apply_nonneg v _
  rw [absMulHeight_eq]
  calc Height.mulHeight (fun i ↦ ((x i : K))) ^ ((Module.finrank ℚ K : ℝ))⁻¹
      ≤ ((⨆ j, house ((x j : K))) ^ Module.finrank ℚ K) ^ ((Module.finrank ℚ K : ℝ))⁻¹ :=
        Real.rpow_le_rpow (Height.mulHeight_pos _).le hmulH (by positivity)
    _ = ⨆ j, house ((x j : K)) := Real.pow_rpow_inv_natCast hH0 Module.finrank_pos.ne'

open scoped Classical in
/-- **Siegel's lemma over a number field, in height form** (Bombieri–Gubler, Corollary 2.9.2).
There is a constant `C`, depending only on `K`, such that a system of `p` linear equations in
`q > p` unknowns whose coefficients are algebraic integers of house at most `A` has a nonzero
solution in `𝓞 K ^ q` of absolute multiplicative height at most `C (C q A) ^ (p / (q - p))`.

The constant is Mathlib's, and is `private` in `Mathlib/NumberTheory/NumberField/House.lean`;
quantifying over it existentially is therefore the only way to restate the theorem, and it is also
the shape the literature states it in. What is proved here is the left-hand side: Mathlib bounds
the *house* of each coordinate, and `absMulHeight_le_iSup_house` turns that into a bound on the
height of the tuple. -/
theorem exists_forall_exists_ne_zero_mulVec_eq_zero_absMulHeight_le (K : Type*) [Field K]
    [NumberField K] :
    ∃ C : ℝ, ∀ (p q : ℕ) (a : Matrix (Fin p) (Fin q) (𝓞 K)) (A : ℝ), a ≠ 0 → 0 < p → p < q →
      (∀ k l, house ((a k l : K)) ≤ A) →
      ∃ ξ : Fin q → 𝓞 K, ξ ≠ 0 ∧ a *ᵥ ξ = 0 ∧
        absMulHeight (fun l ↦ ((ξ l : K))) ≤ C * ((C * q * A) ^ ((p : ℝ) / (q - p))) :=
  ⟨_, fun p q a A ha h0p hpq habs ↦ by
    have : Nonempty (Fin q) := Fin.pos_iff_nonempty.1 (h0p.trans hpq)
    obtain ⟨ξ, hξ0, hξa, hξb⟩ :=
      NumberField.house.exists_ne_zero_int_vec_house_le (K := K) (a := a) (ha := ha)
        (h0p := h0p) (hpq := hpq) (cardβ := Fintype.card_fin q) (habs := habs)
        (cardα := Fintype.card_fin p)
    exact ⟨ξ, hξ0, hξa, (absMulHeight_le_iSup_house hξ0).trans (ciSup_le hξb)⟩⟩

end NumberField
