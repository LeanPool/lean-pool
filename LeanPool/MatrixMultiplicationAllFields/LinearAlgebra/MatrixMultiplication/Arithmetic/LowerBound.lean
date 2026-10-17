/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Arithmetic.Complexity
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Division-free arithmetic programs over a field and their operation counts. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

namespace Program

variable {F Input : Type*}

def registerCost : {r : ℕ} → Program F Input r → Fin r → ℕ
  | 0, .nil => Fin.elim0
  | _ + 1, .step p g => Fin.cases g.cost p.registerCost

theorem sum_registerCost {r : ℕ} (p : Program F Input r) :
    ∑ i, p.registerCost i = p.cost := by
  induction p with
  | nil => simp [registerCost, cost]
  | step p g ih => simp [registerCost, Fin.sum_univ_succ, ih, Nat.add_comm]

theorem eval_eq_constant_or_input_of_registerCost_eq_zero [Field F]
    {r : ℕ} (p : Program F Input r) (i : Fin r) (hi : p.registerCost i = 0) :
    (∃ z : F, ∀ inputs, p.eval inputs i = z) ∨
      (∃ a : Input, ∀ inputs, p.eval inputs i = inputs a) := by
  revert i
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i hi
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi
      change g.cost = 0 at hi
      cases g with
      | literal z => exact Or.inl ⟨z, fun _ => rfl⟩
      | input a => exact Or.inr ⟨a, fun _ => rfl⟩
      | add a b => simp [Gate.cost] at hi
      | sub a b => simp [Gate.cost] at hi
      | mul a b => simp [Gate.cost] at hi
    · intro hi
      simpa only [eval_step_succ] using ih j hi

end Program

section ElementaryMatrices

variable {F : Type*} [Field F] {a b c : ℕ}

def elementaryLeft (i : Fin a) (j : Fin b) : Matrix (Fin a) (Fin b) F :=
  fun x y => if x = i then if y = j then 1 else 0 else 0

def elementaryRight (j : Fin b) (k : Fin c) : Matrix (Fin b) (Fin c) F :=
  fun y z => if z = k then if y = j then 1 else 0 else 0

theorem elementaryProduct (i x : Fin a) (j : Fin b) (k z : Fin c) :
    (elementaryLeft (F := F) i j * elementaryRight (F := F) j k) x z =
      if (x, z) = (i, k) then 1 else 0 := by
  by_cases hi : x = i <;> by_cases hk : z = k <;>
    simp [Matrix.mul_apply, elementaryLeft, elementaryRight, hi, hk]

end ElementaryMatrices

namespace MatrixAlgorithm

variable {F : Type*} [Field F] {a b c : ℕ}

theorem output_injective (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) : Function.Injective (fun o : Fin a × Fin c => P.output o.1 o.2) := by
  classical
  intro x y hxy
  change P.output x.1 x.2 = P.output y.1 y.2 at hxy
  let j : Fin b := ⟨0, by omega⟩
  let A := elementaryLeft (F := F) x.1 j
  let B := elementaryRight (F := F) j x.2
  have hx := congrFun (congrFun (hP A B) x.1) x.2
  have hy := congrFun (congrFun (hP A B) y.1) y.2
  have heq : (A * B) x.1 x.2 = (A * B) y.1 y.2 := by
    rw [← hx, ← hy]
    change P.program.eval (matrixInputs A B) (P.output x.1 x.2) =
      P.program.eval (matrixInputs A B) (P.output y.1 y.2)
    rw [hxy]
  simp only [A, B, elementaryProduct, Prod.eta, ite_true] at heq
  by_contra hne
  have hyx : y ≠ x := Ne.symm hne
  simp [hyx] at heq

theorem one_le_output_registerCost (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) (i : Fin a) (k : Fin c) :
    1 ≤ P.program.registerCost (P.output i k) := by
  by_contra hn
  have hzero : P.program.registerCost (P.output i k) = 0 := by omega
  let j : Fin b := ⟨0, by omega⟩
  have hentry (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
      P.program.eval (matrixInputs A B) (P.output i k) = (A * B) i k :=
    congrFun (congrFun (hP A B) i) k
  rcases P.program.eval_eq_constant_or_input_of_registerCost_eq_zero
      (P.output i k) hzero with ⟨z, hz⟩ | ⟨u, hu⟩
  · have hz0 : z = 0 := by
      have h := hentry 0 0
      rw [hz] at h
      simpa using h
    have hz1 : z = 1 := by
      have h := hentry (elementaryLeft i j) (elementaryRight j k)
      rw [hz] at h
      simpa only [elementaryProduct, ite_true] using h
    exact (zero_ne_one : (0 : F) ≠ 1) (hz0.symm.trans hz1)
  · rcases u with ⟨x, y⟩ | ⟨y, z⟩
    · have h := hentry (Matrix.of fun _ _ => 1) 0
      rw [hu] at h
      simp [matrixInputs, Matrix.mul_apply] at h
    · have h := hentry 0 (Matrix.of fun _ _ => 1)
      rw [hu] at h
      simp [matrixInputs, Matrix.mul_apply] at h

theorem output_size_le_cost (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) : a * c ≤ P.cost := by
  classical
  let f : Fin a × Fin c → Fin P.registers := fun o => P.output o.1 o.2
  have hf : Function.Injective f := P.output_injective hb hP
  calc
    a * c = ∑ _o : Fin a × Fin c, (1 : ℕ) := by simp
    _ ≤ ∑ o : Fin a × Fin c, P.program.registerCost (f o) := by
      apply Finset.sum_le_sum
      intro o ho
      exact P.one_le_output_registerCost hb hP o.1 o.2
    _ = ∑ r ∈ Finset.univ.image f, P.program.registerCost r := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => hf h
    _ ≤ ∑ r, P.program.registerCost r :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = P.cost := P.program.sum_registerCost

end MatrixAlgorithm

theorem rectangularAdmissibleExponent_two_le {F : Type*} [Field F] {k τ : ℝ}
    (hτ : RectangularAdmissibleExponent F k τ) : 2 ≤ τ := by
  by_contra hneg
  have hτlt : τ < 2 := lt_of_not_ge hneg
  let ε : ℝ := (2 - τ) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C ^ ε⁻¹) 1)
  have hnreal : 1 < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : 0 < (n : ℝ) := lt_trans zero_lt_one hnreal
  have hn1 : 1 ≤ n := (Nat.one_le_cast (α := ℝ)).mp hnreal.le
  have hpow : C < (n : ℝ) ^ ε :=
    (Real.rpow_inv_lt_iff_of_pos hC.le (Nat.cast_nonneg n) hε).mp
      (lt_of_le_of_lt (le_max_left _ _) hn)
  obtain ⟨P, hP, hcost⟩ := hbound n hn1
  have hlower : (n : ℝ) ^ (2 : ℕ) ≤ P.cost := by
    have h : n ^ 2 ≤ P.cost := by
      simpa [pow_two] using P.output_size_le_cost (one_le_innerSize hn1 k) hP
    exact_mod_cast h
  have hstrict : (n : ℝ) ^ (2 : ℕ) < (n : ℝ) ^ (2 : ℕ) := calc
    (n : ℝ) ^ (2 : ℕ) ≤ C * (n : ℝ) ^ (τ + ε) := hlower.trans hcost
    _ < (n : ℝ) ^ ε * (n : ℝ) ^ (τ + ε) :=
      mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos hnpos _)
    _ = (n : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_add hnpos]
      have he : ε + (τ + ε) = 2 := by dsimp [ε]; ring
      rw [he]
      norm_num
  exact (lt_irrefl _ hstrict)

theorem rectangularAdmissibleExponent_bddBelow (F : Type*) [Field F] (k : ℝ) :
    BddBelow {τ : ℝ | RectangularAdmissibleExponent F k τ} :=
  ⟨2, fun _ h => rectangularAdmissibleExponent_two_le h⟩

theorem rectangularOmega_le_of_admissibleExponent {F : Type*} [Field F] {k τ : ℝ}
    (hτ : RectangularAdmissibleExponent F k τ) : rectangularOmega F k ≤ τ :=
  csInf_le (rectangularAdmissibleExponent_bddBelow F k) hτ

theorem admissibleExponent_iff_rectangular_one (F : Type*) [Field F] (τ : ℝ) :
    AdmissibleExponent F τ ↔ RectangularAdmissibleExponent F 1 τ := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    rw [innerSize_one]
    exact hbound n hn
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    have hnBound := hbound n hn
    rw [innerSize_one] at hnBound
    exact hnBound

theorem admissibleExponent_two_le {F : Type*} [Field F] {τ : ℝ}
    (hτ : AdmissibleExponent F τ) : 2 ≤ τ :=
  rectangularAdmissibleExponent_two_le ((admissibleExponent_iff_rectangular_one F τ).mp hτ)

theorem admissibleExponent_bddBelow (F : Type*) [Field F] :
    BddBelow {τ : ℝ | AdmissibleExponent F τ} :=
  ⟨2, fun _ h => admissibleExponent_two_le h⟩

theorem omega_le_of_admissibleExponent {F : Type*} [Field F] {τ : ℝ}
    (hτ : AdmissibleExponent F τ) : omega F ≤ τ :=
  csInf_le (admissibleExponent_bddBelow F) hτ

@[simp] theorem rectangularOmega_one (F : Type*) [Field F] :
    rectangularOmega F 1 = omega F := by
  unfold rectangularOmega omega
  congr 1
  ext τ
  exact (admissibleExponent_iff_rectangular_one F τ).symm

end MatrixMultiplication.Arithmetic

end

end MatrixMultiplicationAllFields
