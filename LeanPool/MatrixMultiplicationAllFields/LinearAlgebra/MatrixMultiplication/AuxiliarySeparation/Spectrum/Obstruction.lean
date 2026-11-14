/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Spectrum/Obstruction.lean`, by
Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K` algebraically
closed; docstrings updated from ℂ to `K`.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankExponent
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.PolynomialOverhead
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.SpectralLimit
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Scalar
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# The rank obstruction behind the preliminary spectral state

The finite catalyst is kept fixed while first tensor powers, then exponent
slack, then the number of copies are varied.  The hypotheses below isolate the
rank inequalities supplied by the catalytic comparison; they do not assert
the existence of a tensor spectrum or the separation argument producing that
comparison.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

/-- Tensor powers of a fixed exact matrix algorithm retain their exact rank
bound after identifying the product coordinates with one matrix dimension. -/
theorem exactMatrixRank_pow_le (u j : ℕ) :
    exactMatrixRank K (u ^ j) ≤ exactMatrixRank K u ^ j := by
  classical
  let e : Fin (u ^ j) ≃ (Fin j → Fin u) := Fintype.equivOfCardEq (by simp)
  let f : Fin (u ^ j) × Fin (u ^ j) → Fin j → Fin u × Fin u :=
    fun x i => (e x.1 i, e x.2 i)
  have h := ((exactMatrixRank_spec (K := K) u).power j).pullback f f f
  have heq : Tensor.pullback f f f (Tensor.power (Tensor.matMul K u u u) j) =
      Tensor.matMul K (u ^ j) (u ^ j) (u ^ j) := by
    funext x y z
    simp only [Tensor.pullback, Tensor.power, Tensor.matMul, f,
      Fintype.prod_boole, forall_and, ← funext_iff, e.injective.eq_iff]
  rw [heq] at h
  exact exactRank_le h

/-- A floor approximation uses at most `n^j` copies of a fixed matrix
algorithm and loses at most one factor of its fixed matrix dimension. -/
theorem floor_rank_power_bounds {u n R : ℕ} (hu : 2 ≤ u) (hn : 1 ≤ n)
    {τ : ℝ} (hτ : 0 < τ) (hR : (R : ℝ) ≤ (u : ℝ) ^ τ) (j : ℕ) :
    let l := ⌊(j : ℝ) * Real.logb (u : ℝ) (n : ℝ) / τ⌋₊
    (R : ℝ) ^ l ≤ (n : ℝ) ^ j ∧
      (n : ℝ) ^ ((j : ℝ) / τ) ≤ (u : ℝ) * (u : ℝ) ^ l := by
  have hu1 : (1 : ℝ) < u := by exact_mod_cast (show 1 < u by omega)
  have hu0 : (0 : ℝ) < u := zero_lt_one.trans hu1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  let x := (j : ℝ) * Real.logb (u : ℝ) (n : ℝ) / τ
  let l := ⌊x⌋₊
  have hx : 0 ≤ x := div_nonneg
    (mul_nonneg (Nat.cast_nonneg j) (Real.logb_nonneg hu1 hn1)) hτ.le
  have hl : (l : ℝ) ≤ x := Nat.floor_le hx
  have hxl : x ≤ (l : ℝ) + 1 := (Nat.lt_floor_add_one x).le
  have hlog : (u : ℝ) ^ Real.logb (u : ℝ) (n : ℝ) = n :=
    Real.rpow_logb hu0 (ne_of_gt hu1) hn0
  change (R : ℝ) ^ l ≤ (n : ℝ) ^ j ∧
    (n : ℝ) ^ ((j : ℝ) / τ) ≤ (u : ℝ) * (u : ℝ) ^ l
  constructor
  · calc
      (R : ℝ) ^ l ≤ ((u : ℝ) ^ τ) ^ l :=
        pow_le_pow_left₀ (Nat.cast_nonneg R) hR l
      _ = (u : ℝ) ^ (τ * (l : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
      _ ≤ (u : ℝ) ^ (τ * x) :=
        Real.rpow_le_rpow_of_exponent_le hu1.le (mul_le_mul_of_nonneg_left hl hτ.le)
      _ = (n : ℝ) ^ j := by
        rw [show τ * x = Real.logb (u : ℝ) (n : ℝ) * (j : ℝ) by
          dsimp [x]; field_simp]
        rw [Real.rpow_mul hu0.le, hlog, Real.rpow_natCast]
  · calc
      (n : ℝ) ^ ((j : ℝ) / τ) = (u : ℝ) ^ x := by
        rw [← hlog, ← Real.rpow_mul hu0.le]
        congr 1
        dsimp [x]
        ring
      _ ≤ (u : ℝ) ^ ((l : ℝ) + 1) :=
        Real.rpow_le_rpow_of_exponent_le hu1.le hxl
      _ = (u : ℝ) * (u : ℝ) ^ l := by
        rw [Real.rpow_add hu0, Real.rpow_natCast, Real.rpow_one, mul_comm]

/-- At fixed `n` and exponent slack, every admissible matrix rank budget
forces the exponential growth rate of the catalytic comparison.  The constant
`R` is fixed before the tensor-power parameter varies. -/
theorem catalytic_rank_bound_at_slack {d n Kc R : ℕ}
    (hd : 0 < d) (hn : 1 ≤ n)
    (hbound : ∀ j : ℕ, 1 ≤ j → ∀ g : ℕ, exactMatrixRank K g ≤ n ^ j →
      exactMatrixRank K (d ^ j * g) ≤ R * Kc ^ j)
    {δ : ℝ} (hδ : 0 < δ) :
    (d : ℝ) ^ exactRankExponent K *
      (n : ℝ) ^ (exactRankExponent K / (exactRankExponent K + δ)) ≤ Kc := by
  let ν := exactRankExponent K
  let τ := ν + δ
  have hν : 0 ≤ ν := (by norm_num : (0 : ℝ) ≤ 2).trans exactRankExponent_lower
  have hτ : 0 < τ := add_pos_of_nonneg_of_pos hν hδ
  obtain ⟨u, hu, huR⟩ := exists_exactMatrixRank_lt_rpow
    (show exactRankExponent K < τ from lt_add_of_pos_right _ hδ)
  apply le_of_eventually_pow_le_const_mul_pow (C := (u : ℝ) ^ ν * R)
    (Nat.cast_nonneg Kc)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with j hj
  let l := ⌊(j : ℝ) * Real.logb (u : ℝ) (n : ℝ) / τ⌋₊
  let g := u ^ l
  have hg : 0 < g := pow_pos (by omega) l
  have hf := floor_rank_power_bounds hu hn hτ huR.le j
  change (exactMatrixRank K u : ℝ) ^ l ≤ (n : ℝ) ^ j ∧
    (n : ℝ) ^ ((j : ℝ) / τ) ≤ (u : ℝ) * (u : ℝ) ^ l at hf
  have hbudget : exactMatrixRank K g ≤ n ^ j := by
    have hpow : (exactMatrixRank K g : ℝ) ≤ (exactMatrixRank K u : ℝ) ^ l := by
      exact_mod_cast exactMatrixRank_pow_le u l
    have hb := hpow.trans hf.1
    exact_mod_cast hb
  have hrank := hbound j hj g hbudget
  have hsize : (n : ℝ) ^ ((j : ℝ) / τ) ≤ (u : ℝ) * g := by
    simpa only [g, Nat.cast_pow] using hf.2
  have hlow := exactMatrixRank_rpow_lower_of_pos (K := K) (mul_pos (pow_pos hd j) hg)
  have hpow_n : ((n : ℝ) ^ (ν / τ)) ^ j =
      ((n : ℝ) ^ ((j : ℝ) / τ)) ^ ν := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n),
      ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  calc
    ((d : ℝ) ^ ν * (n : ℝ) ^ (ν / τ)) ^ j =
        (((d ^ j : ℕ) : ℝ) ^ ν) * ((n : ℝ) ^ ((j : ℝ) / τ)) ^ ν := by
      rw [mul_pow, Real.rpow_pow_comm (Nat.cast_nonneg d), hpow_n, Nat.cast_pow]
    _ ≤ (((d ^ j : ℕ) : ℝ) ^ ν) * ((u : ℝ) * g) ^ ν := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) _) hsize hν)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (u : ℝ) ^ ν * (((d ^ j * g : ℕ) : ℝ) ^ ν) := by
      rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg u) (Nat.cast_nonneg g),
        Real.mul_rpow (Nat.cast_nonneg (d ^ j)) (Nat.cast_nonneg g)]
      ring
    _ ≤ (u : ℝ) ^ ν * (exactMatrixRank K (d ^ j * g) : ℝ) :=
      mul_le_mul_of_nonneg_left hlow (Real.rpow_nonneg (Nat.cast_nonneg u) _)
    _ ≤ (u : ℝ) ^ ν * ((R : ℝ) * (Kc : ℝ) ^ j) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg u) _)
      exact_mod_cast hrank
    _ = ((u : ℝ) ^ ν * R) * (Kc : ℝ) ^ j := by ring

/-- The numerical rank consequence of a single fixed finite catalyst is
incompatible with `k < d^ν`.  The same `D` and `R` occur for every `n` and
every tensor power.  No uniform bound on the approximation block selected
after an exponent slack is assumed. -/
theorem catalytic_rank_obstruction {d k D R : ℕ} (hd : 0 < d)
    (hbound : ∀ n : ℕ, 1 ≤ n → ∀ j : ℕ, 1 ≤ j → ∀ g : ℕ,
      exactMatrixRank K g ≤ n ^ j →
      exactMatrixRank K (d ^ j * g) ≤ R * (n * k + D) ^ j) :
    (d : ℝ) ^ exactRankExponent K ≤ k := by
  apply spectral_coefficient_le_of_all_nat
    (hν := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) exactRankExponent_lower)
    (D := (D : ℝ))
  intro n hn δ hδ
  have h := catalytic_rank_bound_at_slack hd hn (hbound n hn) hδ
  simpa only [Nat.cast_add, Nat.cast_mul] using h

/-- Contradiction form for the finite-obstruction argument. -/
theorem not_catalytic_rank_bounds_of_lt {d k D R : ℕ} (hd : 0 < d)
    (hk : (k : ℝ) < (d : ℝ) ^ exactRankExponent K) :
    ¬ (∀ n : ℕ, 1 ≤ n → ∀ j : ℕ, 1 ≤ j → ∀ g : ℕ,
      exactMatrixRank K g ≤ n ^ j →
      exactMatrixRank K (d ^ j * g) ≤ R * (n * k + D) ^ j) := by
  intro hbound
  exact (not_lt_of_ge (catalytic_rank_obstruction hd hbound)) hk

/-- Iteration and absorption of a fixed catalyst require no cancellation of
the tensor factor `s`.  Monotonicity is explicit so the lemma applies to the
restriction order on a tensor semiring, where additive cancellation fails. -/
theorem catalytic_power_comparison {S : Type*} [CommSemiring S] [Preorder S]
    (hadd : ∀ {a b c e : S}, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hmul : ∀ {a b c e : S}, a ≤ b → c ≤ e → a * c ≤ b * e)
    (hzero : ∀ a : S, 0 ≤ a)
    (D t s : S) (k C : ℕ)
    (hcat : D + t * s ≤ D + (k : S) * s)
    (hD : D ≤ (C : S) * s) (n j : ℕ) :
    (n : S) ^ j * t ^ j * s ≤ ((n * k + C : ℕ) : S) ^ j * s := by
  have hiter : ∀ m : ℕ,
      D + (m : S) * (t * s) ≤ D + (m : S) * ((k : S) * s) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc
        D + ((m + 1 : ℕ) : S) * (t * s) =
            (D + t * s) + (m : S) * (t * s) := by push_cast; ring
        _ ≤ (D + (k : S) * s) + (m : S) * (t * s) := hadd hcat le_rfl
        _ = (D + (m : S) * (t * s)) + (k : S) * s := by ring
        _ ≤ (D + (m : S) * ((k : S) * s)) + (k : S) * s := hadd ih le_rfl
        _ = D + ((m + 1 : ℕ) : S) * ((k : S) * s) := by push_cast; ring
  have habsorb : (n : S) * t * s ≤ ((n * k + C : ℕ) : S) * s := by
    calc
      (n : S) * t * s = 0 + (n : S) * (t * s) := by ring
      _ ≤ D + (n : S) * (t * s) := hadd (hzero D) le_rfl
      _ ≤ D + (n : S) * ((k : S) * s) := hiter n
      _ ≤ (C : S) * s + (n : S) * ((k : S) * s) := hadd hD le_rfl
      _ = ((n * k + C : ℕ) : S) * s := by push_cast; ring
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      (n : S) ^ (j + 1) * t ^ (j + 1) * s =
          ((n : S) ^ j * t ^ j) * ((n : S) * t * s) := by ring
      _ ≤ ((n : S) ^ j * t ^ j) * (((n * k + C : ℕ) : S) * s) :=
        hmul le_rfl habsorb
      _ = ((n * k + C : ℕ) : S) * ((n : S) ^ j * t ^ j * s) := by ring
      _ ≤ ((n * k + C : ℕ) : S) * (((n * k + C : ℕ) : S) ^ j * s) :=
        hmul le_rfl ih
      _ = ((n * k + C : ℕ) : S) ^ (j + 1) * s := by ring

/-- A rank-compatible ordered tensor semiring converts a single finite
catalytic inequality into the actual exact-rank obstruction.  The hypotheses
name the required tensor interpretation and scalar rank domination explicitly;
no additive rank formula or cancellation property is assumed. -/
theorem catalytic_semiring_obstruction {S : Type*} [CommSemiring S] [Preorder S]
    (hadd : ∀ {a b c e : S}, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hmul : ∀ {a b c e : S}, a ≤ b → c ≤ e → a * c ≤ b * e)
    (hzero : ∀ a : S, 0 ≤ a)
    (ρ : S → ℕ) (hρmono : Monotone ρ)
    (hρcopies : ∀ (m : ℕ) (s : S), ρ ((m : S) * s) ≤ m * ρ s)
    (M : ℕ → S)
    (hMmul : ∀ a b : ℕ, M (a * b) = M a * M b)
    (hMpow : ∀ a j : ℕ, M (a ^ j) = M a ^ j)
    (hρM : ∀ a : ℕ, ρ (M a) = exactMatrixRank K a)
    (hbudget : ∀ n j g : ℕ, exactMatrixRank K g ≤ n ^ j → M g ≤ (n : S) ^ j)
    (D s : S) (d k C : ℕ) (hd : 0 < d) (hs : 1 ≤ s)
    (hcat : D + M d * s ≤ D + (k : S) * s)
    (hD : D ≤ (C : S) * s) :
    (d : ℝ) ^ exactRankExponent K ≤ k := by
  apply catalytic_rank_obstruction (D := C) (R := ρ s) hd
  intro n _hn j _hj g hg
  have hcompare : M (d ^ j * g) ≤ ((n * k + C : ℕ) : S) ^ j * s := by
    calc
      M (d ^ j * g) = M d ^ j * M g := by rw [hMmul, hMpow]
      _ ≤ M d ^ j * (n : S) ^ j := hmul le_rfl (hbudget n j g hg)
      _ = ((n : S) ^ j * M d ^ j) * 1 := by ring
      _ ≤ ((n : S) ^ j * M d ^ j) * s := hmul le_rfl hs
      _ ≤ ((n * k + C : ℕ) : S) ^ j * s :=
        catalytic_power_comparison hadd hmul hzero D (M d) s k C hcat hD n j
  calc
    exactMatrixRank K (d ^ j * g) = ρ (M (d ^ j * g)) := (hρM _).symm
    _ ≤ ρ (((n * k + C : ℕ) : S) ^ j * s) := hρmono hcompare
    _ = ρ ((((n * k + C) ^ j : ℕ) : S) * s) := by rw [Nat.cast_pow]
    _ ≤ (n * k + C) ^ j * ρ s := hρcopies _ s
    _ = ρ s * (n * k + C) ^ j := Nat.mul_comm _ _

/-- In the semiring of actual finite tensors over `K` modulo mutual
restriction, a fixed catalyst cannot make `k` copies dominate multiplication
by `T_d` unless `k ≥ d^ν`.  The nonzero hypothesis is exactly what supplies
the scalar restriction `s ≥ 1`; the catalyst remains fixed throughout. -/
theorem tensor_catalytic_obstruction
    {D s : (TensorSemiring.TensorClass K)} {d k : ℕ}
    (hd : 0 < d) (hs : s ≠ 0)
    (hcat : D + TensorSemiring.matrixClass K d * s ≤ D + (k : (TensorSemiring.TensorClass K)) * s) :
    (d : ℝ) ^ exactRankExponent K ≤ k := by
  have hs1 : 1 ≤ s := TensorSemiring.one_le_of_ne_zero hs
  have hcopies : ∀ (m : ℕ) (x : (TensorSemiring.TensorClass K)),
      TensorSemiring.rank ((m : (TensorSemiring.TensorClass K)) * x) ≤
        m * TensorSemiring.rank x := by
    intro m x
    simpa only [TensorSemiring.rank_natCast] using
      TensorSemiring.rank_mul_le (m : (TensorSemiring.TensorClass K)) x
  have hbudget : ∀ n j g : ℕ, exactMatrixRank K g ≤ n ^ j →
      TensorSemiring.matrixClass K g ≤ (n : (TensorSemiring.TensorClass K)) ^ j := by
    intro n j g hg
    have hleft : TensorSemiring.matrixClass K g ≤
        (exactMatrixRank K g : (TensorSemiring.TensorClass K)) := by
      simpa only [TensorSemiring.rank_matrixClass] using
        TensorSemiring.le_rank (TensorSemiring.matrixClass K g)
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hg
    have hright : (exactMatrixRank K g : (TensorSemiring.TensorClass K)) ≤
        (n : (TensorSemiring.TensorClass K)) ^ j := by
      rw [← Nat.cast_pow, hq, Nat.cast_add]
      simpa only [add_zero] using TensorSemiring.add_mono
        (le_refl (exactMatrixRank K g : (TensorSemiring.TensorClass K)))
        (TensorSemiring.zero_le (q : (TensorSemiring.TensorClass K)))
    exact hleft.trans hright
  have hD : D ≤ (TensorSemiring.rank D : (TensorSemiring.TensorClass K)) * s := by
    calc
      D ≤ (TensorSemiring.rank D : (TensorSemiring.TensorClass K)) := TensorSemiring.le_rank D
      _ = (TensorSemiring.rank D : (TensorSemiring.TensorClass K)) * 1 := (mul_one _).symm
      _ ≤ (TensorSemiring.rank D : (TensorSemiring.TensorClass K)) * s :=
        TensorSemiring.mul_mono le_rfl hs1
  exact catalytic_semiring_obstruction
    TensorSemiring.add_mono TensorSemiring.mul_mono TensorSemiring.zero_le
    TensorSemiring.rank (fun _ _ h => TensorSemiring.rank_mono h) hcopies
    (TensorSemiring.matrixClass K) TensorSemiring.matrixClass_mul TensorSemiring.matrixClass_pow
    TensorSemiring.rank_matrixClass hbudget D s d k (TensorSemiring.rank D) hd hs1 hcat hD

/-- The stronger comparison produced by a finite separation certificate
has the same consequence.  Its positive scalar summand is only needed
earlier to rule out `s = 0`; that nonzero fact is explicit here. -/
theorem tensor_catalytic_obstruction_of_scalar_gain
    {D s : (TensorSemiring.TensorClass K)} {d k m : ℕ}
    (hd : 0 < d) (hs : s ≠ 0)
    (hcat : D + (m : (TensorSemiring.TensorClass K)) + TensorSemiring.matrixClass K d * s ≤
      D + (k : (TensorSemiring.TensorClass K)) * s) :
    (d : ℝ) ^ exactRankExponent K ≤ k := by
  apply tensor_catalytic_obstruction hd hs
  refine le_trans ?_ hcat
  simpa only [add_zero] using TensorSemiring.add_mono
    (TensorSemiring.add_mono (le_refl D)
      (TensorSemiring.zero_le (m : (TensorSemiring.TensorClass K))))
    (le_refl (TensorSemiring.matrixClass K d * s))

/-- A finite tensor cannot absorb a positive scalar direct summand.  Iterating
such an absorption would place arbitrarily large scalar tensors below one
fixed finite-rank tensor.  This uses rank monotonicity, not rank additivity. -/
theorem not_tensor_add_positive_nat_le_self (D : (TensorSemiring.TensorClass K))
    {m : ℕ} (hm : 0 < m) : ¬ D + (m : (TensorSemiring.TensorClass K)) ≤ D := by
  intro h
  have hiter : ∀ n : ℕ, D + ((n * m : ℕ) : (TensorSemiring.TensorClass K)) ≤ D := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        D + (((n + 1) * m : ℕ) : (TensorSemiring.TensorClass K)) =
            (D + ((n * m : ℕ) : (TensorSemiring.TensorClass K))) + m := by push_cast; ring
        _ ≤ D + (m : (TensorSemiring.TensorClass K)) := TensorSemiring.add_mono ih le_rfl
        _ ≤ D := h
  let n := TensorSemiring.rank D + 1
  have hscalar : ((n * m : ℕ) : (TensorSemiring.TensorClass K)) ≤ D := by
    have hleft := TensorSemiring.add_mono (TensorSemiring.zero_le D)
      (le_refl ((n * m : ℕ) : (TensorSemiring.TensorClass K)))
    have hsmall : ((n * m : ℕ) : (TensorSemiring.TensorClass K)) ≤
        D + ((n * m : ℕ) : (TensorSemiring.TensorClass K)) := by
      simpa only [zero_add] using hleft
    exact hsmall.trans (hiter n)
  have hrank : n * m ≤ TensorSemiring.rank D := by
    simpa only [TensorSemiring.rank_natCast] using TensorSemiring.rank_mono hscalar
  have hnm : n ≤ n * m := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left n (Nat.succ_le_of_lt hm)
  have hlarge : TensorSemiring.rank D + 1 ≤ TensorSemiring.rank D := hnm.trans hrank
  omega

/-- The exact finite-obstruction comparison from Appendix A.1 forces
`k ≥ d^ν`.  Both tensors are fixed, `m` is a positive scalar gain, and the
ordinary tensor rank and restriction order are the actual ones. -/
theorem tensor_catalytic_obstruction_of_positive_scalar_gain
    {D s : (TensorSemiring.TensorClass K)} {d k m : ℕ}
    (hd : 0 < d) (hm : 0 < m)
    (hcat : D + (m : (TensorSemiring.TensorClass K)) + TensorSemiring.matrixClass K d * s ≤
      D + (k : (TensorSemiring.TensorClass K)) * s) :
    (d : ℝ) ^ exactRankExponent K ≤ k := by
  apply tensor_catalytic_obstruction_of_scalar_gain hd (m := m) ?_ hcat
  intro hs
  subst s
  have hbad : D + (m : (TensorSemiring.TensorClass K)) ≤ D := by
    simpa only [mul_zero, add_zero] using hcat
  exact not_tensor_add_positive_nat_le_self D hm hbad

/-- Contradiction interface for the finite inconsistency certificate in
the construction of an additive monotone state. -/
theorem no_tensor_catalytic_gain {d k : ℕ} (hd : 0 < d)
    (hk : (k : ℝ) < (d : ℝ) ^ exactRankExponent K) :
    ¬ ∃ (D s : (TensorSemiring.TensorClass K)) (m : ℕ), 0 < m ∧
      D + (m : (TensorSemiring.TensorClass K)) + TensorSemiring.matrixClass K d * s ≤
        D + (k : (TensorSemiring.TensorClass K)) * s := by
  rintro ⟨D, s, m, hm, hcat⟩
  exact (not_lt_of_ge (tensor_catalytic_obstruction_of_positive_scalar_gain hd hm hcat)) hk

end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
