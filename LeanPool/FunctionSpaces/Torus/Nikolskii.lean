/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.TrigPolynomials
public import LeanPool.FunctionSpaces.MeasureSpaces.Besov.Nikolskii
public import Mathlib.Algebra.Order.Chebyshev

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Nikolskii inequality for trigonometric polynomials

For a trigonometric polynomial `T` of degree `< n` on `𝕋^d`, `n ≥ 1`, and `1 ≤ p < ∞`,

`‖T‖_∞ ≤ (2m)^(d/p) n^(d/p) ‖T‖_p`,   `m = ⌈p/2⌉`

(`Torus.norm_le_rpow_mul_eLpNorm`), so the scheme of trigonometric polynomials has the
Nikolskii property of dimension `d` (`Torus.trigScheme_hasNikolskii`).

**Proof without kernels.**
1. *`p = 2`*: write `T = ∑ c_k e_k` over the at most `(2n)^d` frequencies of degree `< n`.
   Then `|T(x)| ≤ ∑ |c_k| ≤ ((2n)^d)^(1/2) (∑ |c_k|²)^(1/2) = ((2n)^d)^(1/2) ‖T‖_2` by the
   Cauchy–Schwarz inequality and Parseval's identity (orthonormality of the `e_k` in `L_2`,
   Mathlib's `UnitAddTorus.orthonormal_mFourier`).
2. *The power trick*: `T^m` is a trigonometric polynomial of degree `< m n`, so by step 1
   `‖T‖_∞^(2m) = ‖T^m‖_∞² ≤ (2mn)^d ‖T^m‖_2² = (2mn)^d ∫ |T|^(2m) ≤ (2mn)^d ‖T‖_∞^(2m-p) ‖T‖_p^p`
   for `2m ≥ p`; dividing by `‖T‖_∞^(2m-p)` gives `‖T‖_∞^p ≤ (2mn)^d ‖T‖_p^p`.

The usual proof uses the de la Vallée Poussin kernel and gives a constant independent of `p`;
the power trick avoids all kernels at the price of the factor `(2m)^(d/p)`, which is bounded
by `3^d` for `p ≥ 1`.  Only the order `n^(d/p)` matters for the embedding theorems.
-/

@[expose] public section

open MeasureTheory UnitAddTorus
open scoped ENNReal BoundedContinuousFunction TorusHaar InnerProductSpace

namespace Torus

variable {d : Type*} [Fintype d]

/-- The `L_p` class of a trigonometric monomial is Mathlib's `L_p` Fourier monomial. -/
theorem toLp_trigMonomial (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : d → ℤ) :
    BoundedContinuousFunction.toLp (E := ℂ) p volume ℂ (trigMonomial k) = mFourierLp p k :=
  rfl

/-- A trigonometric polynomial of degree `< n` is a combination of the monomials of degree
`< n`. -/
theorem exists_sum_of_mem_trigPoly {n : ℕ} {T : UnitAddTorus d →ᵇ ℂ} (hT : T ∈ trigPoly d n) :
    ∃ t : Finset (d → ℤ), t ⊆ boxLt d n ∧ ∃ c : (d → ℤ) → ℂ,
      T = ∑ k ∈ t, c k • trigMonomial k := by
  classical
  obtain ⟨t, ht, c, hc⟩ := (Submodule.mem_span_image_iff_exists_fun ℂ).1 hT
  refine ⟨t, by exact_mod_cast ht, fun k => if hk : k ∈ t then c ⟨k, hk⟩ else 0, ?_⟩
  rw [← hc, ← Finset.sum_coe_sort t]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

/-- **Parseval for trigonometric polynomials**: `‖∑ c_k e_k‖_2² = ∑ |c_k|²` (Mathlib's
`OrthogonalFamily.norm_sum` for the orthonormal characters). -/
theorem norm_toLp_sum_sq (t : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) :
    ‖BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℂ (∑ k ∈ t, c k • trigMonomial k)‖ ^ 2 =
      ∑ k ∈ t, ‖c k‖ ^ 2 := by
  have hsum : BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℂ (∑ k ∈ t, c k • trigMonomial k)
      = ∑ k ∈ t, c k • mFourierLp 2 k := by
    rw [map_sum]; simp_rw [map_smul, toLp_trigMonomial]
  rw [hsum]
  exact orthonormal_mFourier.orthogonalFamily.norm_sum c t

/-- **The Nikolskii inequality from `L_2` to `L_∞`**: for a trigonometric polynomial of degree
`< n`, `‖T‖_∞² ≤ (2n)^d ‖T‖_2²`. -/
theorem norm_sq_le_card_mul_norm_toLp_sq {n : ℕ} {T : UnitAddTorus d →ᵇ ℂ}
    (hT : T ∈ trigPoly d n) :
    ‖T‖ ^ 2 ≤ ((2 * n) ^ Fintype.card d : ℕ) *
      ‖BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℂ T‖ ^ 2 := by
  obtain ⟨t, ht, c, rfl⟩ := exists_sum_of_mem_trigPoly hT
  rw [norm_toLp_sum_sq]
  have hcard : (t.card : ℝ) ≤ ((2 * n) ^ Fintype.card d : ℕ) := by
    exact_mod_cast (Finset.card_le_card ht).trans (card_boxLt_le n)
  have hsup : ‖∑ k ∈ t, c k • trigMonomial k‖ ≤ ∑ k ∈ t, ‖c k‖ := by
    refine (BoundedContinuousFunction.norm_le (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2
      fun x => ?_
    calc ‖(∑ k ∈ t, c k • trigMonomial k) x‖ = ‖∑ k ∈ t, c k * trigMonomial k x‖ := by
          simp
      _ ≤ ∑ k ∈ t, ‖c k * trigMonomial k x‖ := norm_sum_le _ _
      _ = ∑ k ∈ t, ‖c k‖ := Finset.sum_congr rfl fun k _ => by
          rw [norm_mul, norm_trigMonomial_apply, mul_one]
  calc ‖∑ k ∈ t, c k • trigMonomial k‖ ^ 2 ≤ (∑ k ∈ t, ‖c k‖) ^ 2 := by
        gcongr
    _ ≤ t.card * ∑ k ∈ t, ‖c k‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ _ := by gcongr

/-- For a bounded continuous function, `‖T‖^m ≤ ‖T^m‖` (in fact equality holds). -/
theorem norm_pow_le_norm_pow {α : Type*} [TopologicalSpace α] (T : α →ᵇ ℂ) {m : ℕ}
    (hm : m ≠ 0) : ‖T‖ ^ m ≤ ‖T ^ m‖ := by
  have hA := norm_nonneg (T ^ m)
  have hT : ‖T‖ ≤ ‖T ^ m‖ ^ ((m : ℝ)⁻¹) :=
    (BoundedContinuousFunction.norm_le (Real.rpow_nonneg hA _)).2 fun x => by
      have h1 : ‖T x‖ ^ m ≤ ‖T ^ m‖ := by
        rw [← norm_pow]
        simpa [FunLike.coe_pow] using (T ^ m).norm_coe_le_norm x
      calc ‖T x‖ = (‖T x‖ ^ m) ^ ((m : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast (norm_nonneg _) hm).symm
        _ ≤ ‖T ^ m‖ ^ ((m : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
  calc ‖T‖ ^ m ≤ (‖T ^ m‖ ^ ((m : ℝ)⁻¹)) ^ m := pow_le_pow_left₀ (norm_nonneg _) hT m
    _ = ‖T ^ m‖ := Real.rpow_inv_natCast_pow hA hm

/-- The `L_2` norm of `T^m` is the `m`-th power of the `L_{2m}` norm of `T`. -/
theorem norm_toLp_two_pow (T : UnitAddTorus d →ᵇ ℂ) {m : ℕ} (hm : m ≠ 0) :
    ‖BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℂ (T ^ m)‖ =
      (eLpNorm T (2 * m) volume).toReal ^ m := by
  rw [BoundedContinuousFunction.norm_toLp_eq_toReal_eLpNorm]
  have hT := T.continuous.aestronglyMeasurable (μ := volume)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have h1 : eLpNorm (⇑(T ^ m)) 2 volume = eLpNorm (fun x => ‖T x‖ ^ (m : ℝ)) 2 volume :=
    eLpNorm_congr_norm_ae (T ^ m).continuous.aestronglyMeasurable
      (T.continuous.norm.measurable.pow_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simp [Real.rpow_natCast])
  rw [h1, eLpNorm_norm_rpow _ hT hm0, ENNReal.ofReal_natCast, ENNReal.rpow_natCast,
    ENNReal.toReal_pow]

/-- **The Nikolskii inequality from `L_p` to `L_∞`** for trigonometric polynomials: for
`T` of degree `< n`, `1 ≤ p < ∞` and `m = ⌈p/2⌉`,
`‖T‖_∞^p ≤ (2mn)^d ‖T‖_p^p`. -/
theorem norm_rpow_le_card_mul_eLpNorm_rpow {n : ℕ} {T : UnitAddTorus d →ᵇ ℂ}
    (hT : T ∈ trigPoly d n) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    ‖T‖ ^ p.toReal ≤ ((2 * (⌈p.toReal / 2⌉₊ * n)) ^ Fintype.card d : ℕ) *
      (eLpNorm T p volume).toReal ^ p.toReal := by
  set P := p.toReal
  have hP1 : 1 ≤ P := ENNReal.one_le_toReal_of_one_le hp hp'
  have hP0 : 0 < P := zero_lt_one.trans_le hP1
  set m := ⌈P / 2⌉₊
  have hm0 : m ≠ 0 := by
    have : 0 < P / 2 := by positivity
    exact (Nat.ceil_pos.2 this).ne'
  have hmP : P ≤ 2 * m := by
    have := Nat.le_ceil (P / 2); linarith
  set K : ℝ := (((2 * (m * n)) ^ Fintype.card d : ℕ) : ℝ)
  have hK : 0 ≤ K := Nat.cast_nonneg _
  set N := (eLpNorm T p volume).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  set X := (eLpNorm T (2 * m) volume).toReal
  -- `T^m` is a trigonometric polynomial of degree `< m n`
  have hS : T ^ m ∈ trigPoly d (m * n) := by
    obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    rw [hm']
    exact pow_mem_trigPoly hT m'
  -- interpolation between `L_p` and `L_∞` at the exponent `2m`
  have h2m : p ≤ (2 * m : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_toReal hp']
    calc ENNReal.ofReal P ≤ ENNReal.ofReal (2 * m) := ENNReal.ofReal_le_ofReal hmP
      _ = (2 * m : ℝ≥0∞) := by rw [ENNReal.ofReal_mul (by norm_num)]; simp
  have h2mtop : (2 * m : ℝ≥0∞) ≠ ∞ := ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top m)
  have h2mR : ((2 * m : ℝ≥0∞)).toReal = 2 * m := by simp
  have hint := toReal_eLpNorm_le_rpow_mul (μ := volume) T.continuous.aestronglyMeasurable
    (norm_nonneg T) (Filter.Eventually.of_forall T.norm_coe_le_norm)
    (zero_lt_one.trans_le hp).ne' h2m h2mtop
  rw [h2mR] at hint
  have hX : X ^ (2 * m : ℝ) ≤ ‖T‖ ^ (2 * m - P) * N ^ P := by
    have hθ : 0 ≤ 1 - P / (2 * m) := by
      rw [sub_nonneg, div_le_one (by positivity)]; exact hmP
    calc X ^ (2 * m : ℝ) ≤ (‖T‖ ^ (1 - P / (2 * m)) * N ^ (P / (2 * m))) ^ (2 * m : ℝ) :=
          Real.rpow_le_rpow ENNReal.toReal_nonneg hint (by positivity)
      _ = ‖T‖ ^ (2 * m - P) * N ^ P := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (norm_nonneg _),
            ← Real.rpow_mul hN]
          congr 2 <;> field_simp
  -- the chain of inequalities
  have hchain : ‖T‖ ^ (2 * m : ℝ) ≤ K * (‖T‖ ^ (2 * m - P) * N ^ P) := by
    have h1 : ‖T‖ ^ (2 * m : ℝ) ≤ ‖T ^ m‖ ^ 2 := by
      rw [show (2 * m : ℝ) = ((2 * m : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, mul_comm,
        pow_mul]
      exact pow_le_pow_left₀ (by positivity) (norm_pow_le_norm_pow T hm0) 2
    have h2 := norm_sq_le_card_mul_norm_toLp_sq hS
    rw [norm_toLp_two_pow T hm0] at h2
    have h3 : (X ^ m) ^ 2 = X ^ (2 * m : ℝ) := by
      rw [← pow_mul, show (2 * m : ℝ) = ((m * 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    calc ‖T‖ ^ (2 * m : ℝ) ≤ ‖T ^ m‖ ^ 2 := h1
      _ ≤ K * (X ^ m) ^ 2 := h2
      _ = K * X ^ (2 * m : ℝ) := by rw [h3]
      _ ≤ K * (‖T‖ ^ (2 * m - P) * N ^ P) := by gcongr
  -- cancel `‖T‖^(2m - P)`
  rcases (norm_nonneg T).eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow hP0.ne']; positivity
  have hsplit : ‖T‖ ^ (2 * m : ℝ) = ‖T‖ ^ (2 * m - P) * ‖T‖ ^ P := by
    rw [← Real.rpow_add hpos, sub_add_cancel]
  rw [hsplit, mul_left_comm] at hchain
  exact le_of_mul_le_mul_left hchain (Real.rpow_pos_of_pos hpos _)

/-- **The Nikolskii inequality** for trigonometric polynomials: for `T` of degree `< n` and
`1 ≤ p < ∞`, `‖T‖_∞ ≤ (2⌈p/2⌉)^(d/p) n^(d/p) ‖T‖_p`. -/
theorem norm_le_rpow_mul_eLpNorm {n : ℕ} {T : UnitAddTorus d →ᵇ ℂ} (hT : T ∈ trigPoly d n)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    ‖T‖ ≤ (2 * ⌈p.toReal / 2⌉₊ : ℝ) ^ ((Fintype.card d : ℝ) * p.toReal⁻¹) *
      (n : ℝ) ^ ((Fintype.card d : ℝ) * p.toReal⁻¹) * (eLpNorm T p volume).toReal := by
  set P := p.toReal
  have hP0 : 0 < P := zero_lt_one.trans_le (ENNReal.one_le_toReal_of_one_le hp hp')
  set m := ⌈P / 2⌉₊
  set N := (eLpNorm T p volume).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have h := norm_rpow_le_card_mul_eLpNorm_rpow hT hp hp'
  have hK : (((2 * (m * n)) ^ Fintype.card d : ℕ) : ℝ) ^ P⁻¹ =
      (2 * m : ℝ) ^ ((Fintype.card d : ℝ) * P⁻¹) * (n : ℝ) ^ ((Fintype.card d : ℝ) * P⁻¹) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.mul_rpow
      (by positivity) (by positivity)]
    push_cast; ring_nf
  calc ‖T‖ = (‖T‖ ^ P) ^ P⁻¹ := (Real.rpow_rpow_inv (norm_nonneg T) hP0.ne').symm
    _ ≤ ((((2 * (m * n)) ^ Fintype.card d : ℕ) : ℝ) * N ^ P) ^ P⁻¹ :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = (((2 * (m * n)) ^ Fintype.card d : ℕ) : ℝ) ^ P⁻¹ * N := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.rpow_rpow_inv hN hP0.ne']
    _ = _ := by rw [hK]

/-- **The trigonometric polynomials have the Nikolskii property of dimension `d`**. -/
theorem trigScheme_hasNikolskii :
    (trigScheme d).HasNikolskii volume (Fintype.card d) := by
  refine ⟨fun p hp => ?_⟩
  rcases eq_or_ne p ∞ with rfl | hp'
  · refine ⟨1, zero_le_one, fun n _ a _ => ?_⟩
    have := BoundedContinuousFunction.norm_toLp_top (μ := (volume : Measure (UnitAddTorus d)))
      (𝕜 := ℂ) a
    rw [BoundedContinuousFunction.norm_toLp_eq_toReal_eLpNorm] at this
    simp [this]
  · refine ⟨(2 * ⌈p.toReal / 2⌉₊ : ℝ) ^ ((Fintype.card d : ℝ) * p.toReal⁻¹), by positivity,
      fun n _ a ha => ?_⟩
    exact norm_le_rpow_mul_eLpNorm ha hp hp'

end Torus
