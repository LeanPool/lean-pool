/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Model

/-! # Weighted products and the size of their support -/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle
variable {F : Type*} {i j k : ℕ}

/-- The weighted rank le of type `Prop` for the given inputs. -/
def WeightedRankLE [CommSemiring F] (w : Fin i → Fin j → Fin k → F) (r : ℕ) : Prop :=
  ∃ (a : Fin r → Pos i k → F) (b : Fin r → Pos k j → F) (c : Fin r → Pos i j → F),
    ∀ x y z, ∑ l : Fin r, a l x * b l y * c l z =
      if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then w x.1 y.2 x.2 else 0

theorem WeightedRankLE.map {K : Type*} [CommSemiring F] [CommSemiring K]
    {w : Fin i → Fin j → Fin k → F} {r : ℕ} (h : WeightedRankLE w r) (φ : F →+* K) :
    WeightedRankLE (fun x y z => φ (w x y z)) r := by
  obtain ⟨a, b, c, h⟩ := h
  refine ⟨fun l x => φ (a l x), fun l y => φ (b l y), fun l z => φ (c l z), ?_⟩
  intro x y z
  simpa only [map_sum, map_mul, apply_ite φ, map_zero] using congrArg φ (h x y z)

open Classical in
/-- The value specified by `∑ c, ∑ a, ∑ b, if w a c b = 0 then 0 else 1`. -/
noncomputable def supportSize [Zero F] (w : Fin i → Fin j → Fin k → F) : ℕ :=
  ∑ c, ∑ a, ∑ b, if w a c b = 0 then 0 else 1

/-- Density times the ordinary asymptotic rank bounds the cost of
any exact decomposition, including a sparsely supported one. -/
def DensityBound (F : Type*) [Field F] : Prop :=
  ∀ i j k r : ℕ, 0 < i → 0 < j → 0 < k → ∀ w : Fin i → Fin j → Fin k → F,
    WeightedRankLE w r →
    supportSize w * Real.exp (exponent F (Real.log i) (Real.log j) (Real.log k)) ≤
      (i : ℝ) * j * k * r

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle
