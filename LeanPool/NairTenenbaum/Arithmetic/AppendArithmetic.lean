/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.FloorRootArithmetic

/-! # Products on disjoint blocks of arithmetic coordinates -/

@[expose] public section

namespace NairTenenbaum

/-- The arithmetic map obtained by adjoining the extra coordinate. -/
noncomputable def appendArithmeticMap {k r : ℕ} (F : ArithmeticMap k)
    (H : ArithmeticMap r) : ArithmeticMap (k + r) :=
  fun n => F (fun j => n (Fin.castAdd r j)) * H (fun i => n (Fin.natAdd k i))

theorem mass_append_blocks {k r : ℕ} (n : Tuple (k + r)) :
    mass n = mass (fun j : Fin k => n (Fin.castAdd r j)) *
      mass (fun i : Fin r => n (Fin.natAdd k i)) := Fin.prod_univ_add _

/-- Independent coordinate blocks multiply the polynomial growth constants,
while keeping a common exponent and prime-factor constant. -/
theorem admissible_appendArithmeticMap {k r : ℕ} {A B C ε : ℝ}
    {F : ArithmeticMap k} {H : ArithmeticMap r}
    (hF : Admissible A B ε F) (hH : Admissible A C ε H)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    Admissible A (B * C) ε (appendArithmeticMap F H) := by
  refine ⟨fun n => mul_nonneg (hF.nonneg _) (hH.nonneg _), ?_⟩
  intro m n hmn
  let m₁ : Tuple k := fun j => m (Fin.castAdd r j)
  let m₂ : Tuple r := fun i => m (Fin.natAdd k i)
  let n₁ : Tuple k := fun j => n (Fin.castAdd r j)
  let n₂ : Tuple r := fun i => n (Fin.natAdd k i)
  have HF := hF.growth m₁ n₁ (fun j => hmn (Fin.castAdd r j))
  have HH := hH.growth m₂ n₂ (fun i => hmn (Fin.natAdd k i))
  have Hbound : growthBound A B ε m₁ * growthBound A C ε m₂ ≤
      growthBound A (B * C) ε m := by
    apply le_min
    · calc
        _ ≤ A ^ bigOmega (mass m₁) * A ^ bigOmega (mass m₂) :=
          mul_le_mul (min_le_left _ _) (min_le_left _ _)
            (growthBound_nonneg hA hC _) (pow_nonneg hA _)
        _ = A ^ bigOmega (mass m) := by
          rw [← pow_add, mass_append_blocks m,
            bigOmega_mul (mass_pos m₁).ne' (mass_pos m₂).ne']
    · calc
        _ ≤ (B * (mass m₁ : ℝ) ^ ε) * (C * (mass m₂ : ℝ) ^ ε) :=
          mul_le_mul (min_le_right _ _) (min_le_right _ _)
            (growthBound_nonneg hA hC _) (by positivity)
        _ = (B * C) * (mass m : ℝ) ^ ε := by
          rw [mass_append_blocks m, Nat.cast_mul,
            Real.mul_rpow (by positivity) (by positivity)]
          ring
  calc
    appendArithmeticMap F H (m * n) = F (m₁ * n₁) * H (m₂ * n₂) := rfl
    _ ≤ (growthBound A B ε m₁ * F n₁) * (growthBound A C ε m₂ * H n₂) :=
      mul_le_mul HF HH (hH.nonneg _) (mul_nonneg (growthBound_nonneg hA hB _) (hF.nonneg _))
    _ = (growthBound A B ε m₁ * growthBound A C ε m₂) * appendArithmeticMap F H n := by
      change _ = _ * (F n₁ * H n₂)
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right Hbound (mul_nonneg (hF.nonneg _) (hH.nonneg _))

/-- The paper's scalar class `M`: one prime-factor constant works for every
positive polynomial-growth exponent, with the latter's constant allowed to vary. -/
def ScalarClassM (θ : ℕ → ℝ) : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧ ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 1 ≤ B ∧
    Admissible A B ε (fun n : Tuple 1 => θ (n 0))

/-- A finite family in `M` has common admissibility constants at any fixed
positive exponent. -/
theorem scalarClassM_common {r : ℕ} {θ : Fin r → ℕ → ℝ}
    (hθ : ∀ i, ScalarClassM (θ i)) {ε : ℝ} (hε : 0 < ε) :
    ∃ A B : ℝ, 1 ≤ A ∧ 1 ≤ B ∧
      ∀ i, Admissible A B ε (fun n : Tuple 1 => θ i (n 0)) := by
  classical
  choose A hA H using hθ
  choose B hB hF using fun i => H i ε hε
  let A' := 1 + ∑ i, A i
  let B' := 1 + ∑ i, B i
  have hA₀ (i) : 0 ≤ A i := zero_le_one.trans (hA i)
  have hB₀ (i) : 0 ≤ B i := zero_le_one.trans (hB i)
  have hAA (i) : A i ≤ A' := by
    have := Finset.single_le_sum (fun j _ => hA₀ j) (Finset.mem_univ i)
    dsimp [A']; linarith
  have hBB (i) : B i ≤ B' := by
    have := Finset.single_le_sum (fun j _ => hB₀ j) (Finset.mem_univ i)
    dsimp [B']; linarith
  refine ⟨A', B', ?_, ?_, fun i => (hF i).mono (hA₀ i) (hB₀ i) (hAA i) (hBB i) le_rfl⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hA₀ i))
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hB₀ i))

end NairTenenbaum
