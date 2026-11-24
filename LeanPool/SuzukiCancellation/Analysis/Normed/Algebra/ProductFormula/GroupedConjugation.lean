/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.CommutatorExpansion

/-!
# Finite conjugation expansions with additive kicks

Conjugations are applied in increasing index order, with an additive kick after each layer.
The Taylor coefficients are combined before taking norms, preserving cancellation between kicks.

## Main definitions

* `groupedConj`: a finite sequence of conjugations with kicks.
* `groupedConjCoeff`: its factorial-normalized coefficient recursion.
* `groupedConjBound`: the sum of single-layer remainders on the combined coefficients.

## Main results

* `norm_groupedConj_sub_sum_le`: a finite Taylor bound for every real parameter.
* `norm_groupedConj_sub_sum_le_of_skewAdjoint`: the C*-algebra specialization.
-/

@[expose] public noncomputable section

open scoped RealScalar algebraMap
open Finset NormedSpace MeasureTheory

namespace TrotterError

/-- Conjugations in increasing index order, with the kick `K i` added after layer `i`. -/
def groupedConj {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A K : Fin s → 𝔸) (B : 𝔸) (x : ℝ) : 𝔸 :=
  match s with
  | 0 => B
  | s + 1 => expSMulConj (A (Fin.last s))
      (groupedConj (fun i ↦ A i.castSucc) (fun i ↦ K i.castSucc) B x) x + K (Fin.last s)

/-- Factorial-normalized Taylor coefficients; the initial series is constant. -/
def groupedConjCoeff {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸]
    {s : ℕ} (A K : Fin s → 𝔸) (B : 𝔸) (n : ℕ) : 𝔸 :=
  match s with
  | 0 => if n = 0 then B else 0
  | s + 1 =>
      (∑ q ∈ range (n + 1), (Nat.factorial q : ℝ)⁻¹ •
        adPow (A (Fin.last s)) q
          (groupedConjCoeff (fun i ↦ A i.castSucc) (fun i ↦ K i.castSucc) B (n - q))) +
        if n = 0 then K (Fin.last s) else 0

/-- Sum of the layerwise remainder constants, retaining each combined coefficient in one norm. -/
def groupedConjBound {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸]
    {s : ℕ} (A K : Fin s → 𝔸) (B : 𝔸) (p : ℕ) : ℝ :=
  match s with
  | 0 => 0
  | s + 1 => groupedConjBound (fun i ↦ A i.castSucc) (fun i ↦ K i.castSucc) B p +
      ∑ k ∈ range p, ‖adPow (A (Fin.last s)) (p - k)
        (groupedConjCoeff (fun i ↦ A i.castSucc) (fun i ↦ K i.castSucc) B k)‖ /
          (Nat.factorial (p - k) : ℝ)

/-- A one-layer finite Taylor remainder under explicit two-sided exponential control. -/
theorem norm_expSMulConj_sub_sum_le_of_le_one {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (A B : 𝔸)
    (hA : ∀ t : ℝ, ‖exp (t • A)‖ ≤ 1) (p : ℕ) (hp : 1 ≤ p) (x : ℝ) :
    ‖expSMulConj A B x -
      ∑ q ∈ range p, (x ^ q / (Nat.factorial q : ℝ)) • adPow A q B‖ ≤
        |x| ^ p * (‖adPow A p B‖ / (Nat.factorial p : ℝ)) := by
  have hpoly : (∑ q ∈ range p,
      (Nat.factorial q : ℝ)⁻¹ • adPow A q B * (x ^ q : 𝔸)) =
      ∑ q ∈ range p, (x ^ q / (Nat.factorial q : ℝ)) • adPow A q B := by
    apply sum_congr rfl
    intro q _
    rw [← pow_smul_eq_smul_mul]
    congr 1
    ring
  rw [expSMulConj_taylor A B p x hp, hpoly, add_sub_cancel_left]
  have h := norm_conj_smul_integral_le_of_norm_conj_le A (adPow A p B) p 0
    (Nat.factorial (p - 1)) hp (by positivity) x ‖adPow A p B‖ (norm_nonneg _)
    (fun u _ ↦ (norm_expSMulConj_eq_of_le_one A _ hA u).le)
  have heq : (∫ u in 0..x,
      expSMulConj A (adPow A p B) (x - u) *
        ((u ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸)) =
      ∫ u in 0..x, (((x - u) ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : ℝ) •
        expSMulConj A (adPow A p B) u := by
    rw [← integral_smul_eq_integral_mul_sub]
  rw [heq]
  have hf : p.factorial = p * (p - 1).factorial := by
    simpa only [Nat.sub_add_cancel hp] using Nat.factorial_succ (p - 1)
  simpa only [pow_zero, mul_one, Nat.add_zero, hf,
    ← Nat.cast_mul, mul_comm,
    mul_div_assoc] using h

/-- Reindexing the triangular Taylor sum by total degree. -/
lemma sum_conj_taylor_eq {𝔸 : Type*} [AddCommGroup 𝔸] [Module ℝ 𝔸]
    (f : ℕ → ℕ → 𝔸) (p : ℕ) (x : ℝ) :
    (∑ k ∈ range p, x ^ k • ∑ q ∈ range (p - k), x ^ q • f q k) =
      ∑ n ∈ range p, x ^ n • ∑ q ∈ range (n + 1), f q (n - q) := by
  simp only [Finset.smul_sum, smul_smul, ← pow_add]
  rw [sum_range_add_antidiagonal p (fun q k ↦ x ^ (k + q) • f q k)]
  apply sum_congr rfl
  intro n _
  apply sum_congr rfl
  intro q hq
  rw [Nat.sub_add_cancel (by simpa using mem_range.mp hq : q ≤ n)]

/-- The coefficient recursion reassembles the finite single-layer Taylor polynomials. -/
lemma groupedConjCoeff_sum_succ {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸]
    {s : ℕ} (A K : Fin (s + 1) → 𝔸) (B : 𝔸) (p : ℕ) (hp : 1 ≤ p) (x : ℝ) :
    (∑ n ∈ range p, x ^ n • groupedConjCoeff A K B n) =
      (∑ k ∈ range p, x ^ k • ∑ q ∈ range (p - k),
        (x ^ q / (Nat.factorial q : ℝ)) •
          adPow (A (Fin.last s)) q
            (groupedConjCoeff (fun i ↦ A i.castSucc) (fun i ↦ K i.castSucc) B k)) +
      K (Fin.last s) := by
  simp only [groupedConjCoeff, smul_add, sum_add_distrib]
  congr 1
  · rw [← sum_conj_taylor_eq
      (fun q k ↦ (Nat.factorial q : ℝ)⁻¹ • adPow (A (Fin.last s)) q
        (groupedConjCoeff (fun i ↦ A i.castSucc) (fun i ↦ K i.castSucc) B k)) p x]
    apply sum_congr rfl
    intro k _
    congr 1
    apply sum_congr rfl
    intro q _
    rw [smul_smul, div_eq_mul_inv]
  · simp [Finset.sum_ite_eq', show 0 ∈ range p from mem_range.mpr (by lia)]

/-- A finite polynomial can be expanded one layer at a time without splitting its coefficients. -/
lemma norm_expSMulConj_sum_sub_sum_le {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (A : 𝔸) (c : ℕ → 𝔸)
    (hA : ∀ t : ℝ, ‖exp (t • A)‖ ≤ 1) (p : ℕ) (x : ℝ) :
    ‖expSMulConj A (∑ k ∈ range p, x ^ k • c k) x -
      ∑ k ∈ range p, x ^ k • ∑ q ∈ range (p - k),
        (x ^ q / (Nat.factorial q : ℝ)) • adPow A q (c k)‖ ≤
      |x| ^ p * ∑ k ∈ range p, ‖adPow A (p - k) (c k)‖ /
        (Nat.factorial (p - k) : ℝ) := by
  change ‖expSMulConjLin A x (∑ k ∈ range p, x ^ k • c k) - _‖ ≤ _
  rw [map_sum]
  simp only [LinearMap.map_smul]
  rw [← sum_sub_distrib]
  simp only [← smul_sub]
  calc
    _ ≤ ∑ k ∈ range p, ‖x ^ k •
        (expSMulConj A (c k) x - ∑ q ∈ range (p - k),
          (x ^ q / (Nat.factorial q : ℝ)) • adPow A q (c k))‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range p, |x| ^ p *
        (‖adPow A (p - k) (c k)‖ / (Nat.factorial (p - k) : ℝ)) := by
      apply sum_le_sum
      intro k hk
      rw [norm_smul, Real.norm_eq_abs, abs_pow]
      calc
        _ ≤ |x| ^ k * (|x| ^ (p - k) *
            (‖adPow A (p - k) (c k)‖ / (Nat.factorial (p - k) : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (norm_expSMulConj_sub_sum_le_of_le_one A (c k) hA (p - k) (by
              have := mem_range.mp hk
              lia) x) (by positivity)
        _ = _ := by rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (by
          have := mem_range.mp hk
          lia)]
    _ = _ := (Finset.mul_sum ..).symm

/-- **Grouped finite conjugation remainder** for all real times and all positive orders.
Every layer is assumed to have a contractive exponential for both signs of time. -/
theorem norm_groupedConj_sub_sum_le {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] {s : ℕ} (A K : Fin s → 𝔸) (B : 𝔸)
    (hA : ∀ (i : Fin s) (t : ℝ), ‖exp (t • A i)‖ ≤ 1)
    (p : ℕ) (hp : 1 ≤ p) (x : ℝ) :
    ‖groupedConj A K B x - ∑ k ∈ range p, x ^ k • groupedConjCoeff A K B k‖ ≤
      |x| ^ p * groupedConjBound A K B p := by
  induction s with
  | zero =>
      simp [groupedConj, groupedConjCoeff, groupedConjBound,
        show 0 ∈ range p from mem_range.mpr (by lia)]
  | succ s ih =>
      let A' : Fin s → 𝔸 := fun i ↦ A i.castSucc
      let K' : Fin s → 𝔸 := fun i ↦ K i.castSucc
      let P := ∑ k ∈ range p, x ^ k • groupedConjCoeff A' K' B k
      let Q := ∑ k ∈ range p, x ^ k • ∑ q ∈ range (p - k),
        (x ^ q / (Nat.factorial q : ℝ)) •
          adPow (A (Fin.last s)) q (groupedConjCoeff A' K' B k)
      rw [groupedConjCoeff_sum_succ A K B p hp x]
      change ‖(expSMulConj (A (Fin.last s)) (groupedConj A' K' B x) x + _) -
        (Q + _)‖ ≤ |x| ^ p * (groupedConjBound A' K' B p + _)
      rw [add_sub_add_right_eq_sub]
      refine (norm_sub_le_norm_sub_add_norm_sub _ (expSMulConj (A (Fin.last s)) P x) Q).trans ?_
      rw [← dist_eq_norm, (isometry_expSMulConj_of_le_one _ (hA (Fin.last s)) x).dist_eq,
        dist_eq_norm, mul_add]
      exact add_le_add (ih A' K' (fun i ↦ hA i.castSucc))
        (norm_expSMulConj_sum_sub_sum_le _ _ (hA (Fin.last s)) p x)

/-- The remainder bound for skew-adjoint generators in any complete real C*-algebra. -/
theorem norm_groupedConj_sub_sum_le_of_skewAdjoint {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸]
    [StarModule ℝ 𝔸] {s : ℕ} (A K : Fin s → 𝔸) (B : 𝔸)
    (hA : ∀ i, star (A i) = -A i) (p : ℕ) (hp : 1 ≤ p) (x : ℝ) :
    ‖groupedConj A K B x - ∑ k ∈ range p, x ^ k • groupedConjCoeff A K B k‖ ≤
      |x| ^ p * groupedConjBound A K B p := by
  rcases subsingleton_or_nontrivial 𝔸 with h | h
  · have := h
    exact norm_groupedConj_sub_sum_le A K B
      (fun i t ↦ by simp [Subsingleton.elim (exp (t • A i)) 0]) p hp x
  · have := h
    exact norm_groupedConj_sub_sum_le A K B
      (fun i t ↦ (norm_exp_smul_of_skewAdjoint (hA i) t).le) p hp x

/-- The recursive constant is the explicit sum over layers and lower Taylor coefficients. -/
lemma groupedConjBound_eq_sum {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸]
    {s : ℕ} (A K : Fin s → 𝔸) (B : 𝔸) (p : ℕ) :
    groupedConjBound A K B p =
      ∑ j : Fin s, ∑ k ∈ range p, ‖adPow (A j) (p - k)
        (groupedConjCoeff (A ∘ Fin.castLE (Nat.le_of_lt j.isLt))
          (K ∘ Fin.castLE (Nat.le_of_lt j.isLt)) B k)‖ /
            (Nat.factorial (p - k) : ℝ) := by
  induction s with
  | zero => simp [groupedConjBound]
  | succ s ih =>
      rw [groupedConjBound, ih, Fin.sum_univ_castSucc]
      rfl

/-- The constant in the grouped remainder estimate is nonnegative. -/
lemma groupedConjBound_nonneg {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸]
    {s : ℕ} (A K : Fin s → 𝔸) (B : 𝔸) (p : ℕ) :
    0 ≤ groupedConjBound A K B p := by
  rw [groupedConjBound_eq_sum]
  positivity

/-- The finite recursion equals the list fold in the same increasing index order. -/
lemma groupedConj_eq_foldl {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A K : Fin s → 𝔸) (B : 𝔸) (x : ℝ) :
    groupedConj A K B x = (List.ofFn (fun i ↦ (A i, K i))).foldl
      (fun acc a ↦ expSMulConj a.1 acc x + a.2) B := by
  induction s with
  | zero => rfl
  | succ s ih =>
      rw [List.ofFn_succ', List.concat_eq_append, List.foldl_concat, ← ih]
      rfl

/-- At zero time, only the seed and the kicks remain. -/
lemma groupedConj_zero {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A K : Fin s → 𝔸) (B : 𝔸) :
    groupedConj A K B 0 = B + ∑ i, K i := by
  induction s with
  | zero => simp [groupedConj]
  | succ s ih => simp [groupedConj, expSMulConj, ih, Fin.sum_univ_castSucc, add_assoc]

/-- The constant coefficient is the seed plus all kicks. -/
lemma groupedConjCoeff_zero {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸]
    {s : ℕ} (A K : Fin s → 𝔸) (B : 𝔸) :
    groupedConjCoeff A K B 0 = B + ∑ i, K i := by
  induction s with
  | zero => simp [groupedConjCoeff]
  | succ s ih => simp [groupedConjCoeff, adPow, ih, Fin.sum_univ_castSucc, add_assoc]

/-- Zero kicks recover the ordinary multilayer conjugation. -/
lemma groupedConj_zero_kicks_eq_multiConj {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] {s : ℕ} (Z : Fin s → 𝔸) (B : 𝔸) (x : ℝ) :
    groupedConj Z (fun _ ↦ 0) B x = multiConj Z B x := by
  induction s with
  | zero => simp [groupedConj, multiConj]
  | succ s ih => simp only [groupedConj, multiConj_succ, ih, add_zero]

/-- Zero kicks recover the ordinary conjugation coefficients. -/
lemma groupedConjCoeff_zero_kicks_eq_conjCoeff {𝔸 : Type*} [Ring 𝔸]
    [Algebra ℝ 𝔸] {s : ℕ} (Z : Fin s → 𝔸) (B : 𝔸) (n : ℕ) :
    groupedConjCoeff Z (fun _ ↦ 0) B n = conjCoeff Z B n := by
  induction s generalizing n with
  | zero =>
      by_cases hn : n = 0
      · simp [groupedConjCoeff, conjCoeff, hn, adSequence, finAntidiagonal_zero]
      · simp [groupedConjCoeff, conjCoeff, hn, finAntidiagonal_zero]
  | succ s ih => simp only [groupedConjCoeff, conjCoeff_succ, ih, ite_self, add_zero]

/-- A single layer is exactly one conjugation followed by its kick. -/
@[simp]
lemma groupedConj_single {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A K B : 𝔸) (x : ℝ) :
    groupedConj (fun _ : Fin 1 ↦ A) (fun _ ↦ K) B x = expSMulConj A B x + K := rfl

/-- In one layer the kick changes only the constant coefficient. -/
lemma groupedConjCoeff_single {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸]
    (A K B : 𝔸) (n : ℕ) :
    groupedConjCoeff (fun _ : Fin 1 ↦ A) (fun _ ↦ K) B n =
      (Nat.factorial n : ℝ)⁻¹ • adPow A n B + if n = 0 then K else 0 := by
  rw [groupedConjCoeff]
  congr 1
  rw [sum_eq_single n]
  · simp [groupedConjCoeff]
  · intro q hq hqn
    have hnq : n - q ≠ 0 := by
      have := mem_range.mp hq
      lia
    simp [groupedConjCoeff, hnq]
  · simp

end TrotterError
