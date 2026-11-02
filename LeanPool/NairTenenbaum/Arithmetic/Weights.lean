/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import LeanPool.NairTenenbaum.Polynomials.RootCount
public import Mathlib.Data.PNat.Interval
import Mathlib.Tactic.Positivity

/-! # Exponent substitution and the dagger weight

The substitutions `n'`, `n''` and the lifted weight in §2, and the weight in equation (16).
The exponent matrix and the discriminant are explicit arguments, allowing the
combinatorial identities to be used independently of the polynomial factorization.
-/

@[expose] public section

namespace NairTenenbaum

open Finset

/-- The exponent of the `h`th irreducible factor in the total product. -/
def totalExponent {k r : ℕ} (γ : Fin k → Fin r → ℕ) (h : Fin r) : ℕ := ∑ j, γ j h

/-- The tuple `n'` in §2. -/
def substitute {k r : ℕ} (γ : Fin k → Fin r → ℕ) (n : Tuple r) : Tuple k :=
  fun j => ∏ h, n h ^ γ j h

/-- The integer `n''` in §2. -/
def weightedMass {k r : ℕ} (γ : Fin k → Fin r → ℕ) (n : Tuple r) : ℕ :=
  ∏ h, (n h : ℕ) ^ totalExponent γ h

/-- Equation (15). -/
def pullback {k r : ℕ} (γ : Fin k → Fin r → ℕ) (H : ArithmeticMap k) : ArithmeticMap r :=
  fun n => H (substitute γ n)

@[simp] theorem substitute_one {k r : ℕ} (γ : Fin k → Fin r → ℕ) :
    substitute γ 1 = 1 := by ext j; simp [substitute]

@[simp] theorem substitute_mul {k r : ℕ} (γ : Fin k → Fin r → ℕ) (a b : Tuple r) :
    substitute γ (a * b) = substitute γ a * substitute γ b := by
  ext j
  simp [substitute, mul_pow, Finset.prod_mul_distrib]

theorem mass_substitute {k r : ℕ} (γ : Fin k → Fin r → ℕ) (n : Tuple r) :
    mass (substitute γ n) = weightedMass γ n := by
  simp only [mass, substitute, PNat.coe_prod, PNat.pow_coe, weightedMass, totalExponent]
  rw [Finset.prod_comm]
  congr 1
  ext h
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem weightedMass_pos {k r : ℕ} (γ : Fin k → Fin r → ℕ) (n : Tuple r) :
    0 < weightedMass γ n := by rw [← mass_substitute]; exact mass_pos _

@[simp] theorem weightedMass_one {k r : ℕ} (γ : Fin k → Fin r → ℕ) :
    weightedMass γ 1 = 1 := by simp [weightedMass]

@[simp] theorem weightedMass_mul {k r : ℕ} (γ : Fin k → Fin r → ℕ) (a b : Tuple r) :
    weightedMass γ (a * b) = weightedMass γ a * weightedMass γ b := by
  simp only [← mass_substitute, substitute_mul, mass_mul]

/-- Distinct tuples need cross-coordinate coprimality before substitution. -/
theorem substitute_coprime {k r : ℕ} (γ : Fin k → Fin r → ℕ) {a b : Tuple r}
    (h : ∀ i j, Nat.Coprime (a i) (b j)) : Coprime (substitute γ a) (substitute γ b) := by
  intro j
  simp only [substitute, PNat.coe_prod, PNat.pow_coe, Nat.coprime_prod_left_iff,
    Nat.coprime_prod_right_iff]
  intro i _ l _
  exact ((h l i).pow_left _).pow_right _

/-- Identity exponent matrix, the irreducible pairwise coprime case. -/
def identityExponents (k : ℕ) (j h : Fin k) : ℕ := if j = h then 1 else 0

@[simp] theorem substitute_identity {k : ℕ} (n : Tuple k) :
    substitute (identityExponents k) n = n := by
  ext j
  simp [substitute, identityExponents]

@[simp] theorem totalExponent_identity {k : ℕ} (h : Fin k) :
    totalExponent (identityExponents k) h = 1 := by simp [totalExponent, identityExponents]

@[simp] theorem weightedMass_identity {k : ℕ} (n : Tuple k) :
    weightedMass (identityExponents k) n = mass n := by simp [weightedMass, mass]

/-- The dagger in (16): pairwise coprimality and coprimality with `|D*|`. -/
def Dagger {r : ℕ} (D : ℕ) (n : Tuple r) : Prop :=
  (∀ i j, i ≠ j → Nat.Coprime (n i) (n j)) ∧ ∀ i, Nat.Coprime (n i) D

/-- All positive tuples with each coordinate at most `N`. -/
def tupleBox (r : ℕ) (N : ℕ+) : Finset (Tuple r) :=
  Fintype.piFinset fun _ => Finset.Icc 1 N

@[simp] theorem mem_tupleBox {r : ℕ} {N : ℕ+} {n : Tuple r} :
    n ∈ tupleBox r N ↔ ∀ h, n h ≤ N := by
  simp [tupleBox]

/-- Tuples in the fiber of `n''`, subject to the dagger conditions. -/
noncomputable def weightFiber {k r : ℕ} (γ : Fin k → Fin r → ℕ) (D : ℕ) (N : ℕ+) :
    Finset (Tuple r) := by
  classical
  exact (tupleBox r N).filter fun n => weightedMass γ n = N ∧ Dagger D n

/-- Equation (16), for a positive integer argument. -/
noncomputable def weight {k r : ℕ} (γ : Fin k → Fin r → ℕ) (D : ℕ)
    (F : ArithmeticMap k) (θ : Fin r → ℕ → ℝ) (N : ℕ+) : ℝ :=
  ∑ n ∈ weightFiber γ D N, pullback γ F n * ∏ h, θ h (n h) / (n h : ℝ)

theorem coordinate_le_weightedMass {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ h, 0 < totalExponent γ h) (n : Tuple r) (i : Fin r) :
    (n i : ℕ) ≤ weightedMass γ n := by
  have hp : (n i : ℕ) ≤ (n i : ℕ) ^ totalExponent γ i :=
    Nat.le_pow (hγ i)
  exact hp.trans (Finset.single_le_prod (fun h _ => Nat.one_le_pow _ _ (n h).pos) (mem_univ i))

/-- No tuples are lost by the finite box in the definition of the weight. -/
theorem mem_weightFiber {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ h, 0 < totalExponent γ h) (D : ℕ) (N : ℕ+) (n : Tuple r) :
    n ∈ weightFiber γ D N ↔ weightedMass γ n = N ∧ Dagger D n := by
  classical
  simp only [weightFiber, mem_filter]
  constructor
  · exact And.right
  · intro hn
    refine ⟨mem_tupleBox.mpr (fun i => ?_), hn⟩
    exact_mod_cast hn.1 ▸ coordinate_le_weightedMass γ hγ n i

theorem weight_nonneg {k r : ℕ} (γ : Fin k → Fin r → ℕ) (D : ℕ)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) {θ : Fin r → ℕ → ℝ}
    (hθ : ∀ h n, 0 ≤ θ h n) (N : ℕ+) : 0 ≤ weight γ D F θ N := by
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (hF _) (Finset.prod_nonneg fun h _ => div_nonneg (hθ h _) (by positivity))

/-- In one variable the fiber has exactly one element when it is coprime to `D`. -/
theorem weightFiber_one_variable (D : ℕ) (N : ℕ+) :
    weightFiber (identityExponents 1) D N =
      if Nat.Coprime N D then {fun _ => N} else ∅ := by
  classical
  split_ifs with h
  · ext n
    rw [mem_weightFiber _ (by intro h; simp)]
    simp only [mem_singleton, weightedMass_identity, mass, Fin.prod_univ_one,
      Dagger, Fin.forall_fin_one]
    constructor
    · rintro ⟨heq, _⟩
      funext j
      exact (congrArg n (Subsingleton.elim j 0)).trans (PNat.coe_injective heq)
    · intro heq
      rw [heq]
      simp only [Fin.isValue, ne_eq, not_true_eq_false, Nat.coprime_self, PNat.coe_eq_one_iff,
        IsEmpty.forall_iff, true_and]
      exact h
  · ext n
    rw [mem_weightFiber _ (by intro h; simp)]
    simp only [notMem_empty, iff_false, weightedMass_identity, mass,
      Fin.prod_univ_one, Dagger, Fin.forall_fin_one]
    rintro ⟨heq, _, hcop⟩
    exact h (by simpa only [heq] using hcop)

/-- The exact one-variable specialization of (16), including the dagger restriction. -/
theorem weight_one_variable (D : ℕ) (F : ArithmeticMap 1) (θ : Fin 1 → ℕ → ℝ) (N : ℕ+) :
    weight (identityExponents 1) D F θ N =
      if Nat.Coprime N D then F (fun _ => N) * θ 0 N / (N : ℝ) else 0 := by
  classical
  rw [weight, weightFiber_one_variable]
  split_ifs <;> simp [pullback, mul_div_assoc]

end NairTenenbaum
