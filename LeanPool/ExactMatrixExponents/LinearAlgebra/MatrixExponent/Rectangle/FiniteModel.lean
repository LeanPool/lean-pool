/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Weights
public import Mathlib.Data.Fintype.BigOperators

/-!
# Exact ranks of powers and their asymptotic rate

Each side of a power has one independent digit per copy. Convergence
to the stated limit is proved for positive support density.
-/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle
open Filter

variable {F : Type*} [Field F] {i j k : ℕ}

/-- The indexed operation `fun a b c => ∏ l : Fin n, w (finFunctionFinEquiv.symm a l)
(finFunctionFinEquiv.symm b l) (finFunctionFinEquiv.symm c l)`. -/
def WPower (w : Fin i → Fin j → Fin k → F) (n : ℕ) :
    Fin (i ^ n) → Fin (j ^ n) → Fin (k ^ n) → F := fun a b c =>
  ∏ l : Fin n, w (finFunctionFinEquiv.symm a l)
    (finFunctionFinEquiv.symm b l) (finFunctionFinEquiv.symm c l)

/-- The infimum of `{r : ℕ | WeightedRankLE w r}`. -/
def rankW (w : Fin i → Fin j → Fin k → F) : ℕ := sInf {r : ℕ | WeightedRankLE w r}

/-- The quantity computed by `limUnder atTop fun n : ℕ => (rankW (WPower w n) : ℝ) ^ (n : ℝ)⁻¹`. -/
def asymptoticRank (w : Fin i → Fin j → Fin k → F) : ℝ :=
  limUnder atTop fun n : ℕ => (rankW (WPower w n) : ℝ) ^ (n : ℝ)⁻¹

/-- Evaluates `1` at the input `_ _ _`. -/
def ordinary (F : Type*) [Field F] (i j k : ℕ) : Fin i → Fin j → Fin k → F :=
  fun _ _ _ => 1

/-- The quantity computed by `supportSize w / ((i : ℝ) * j * k)`. -/
def density (w : Fin i → Fin j → Fin k → F) : ℝ := supportSize w / ((i : ℝ) * j * k)

/-- Normalize the surplus by the output area divided by its natural logarithm. -/
noncomputable def normalized (x y : ℝ) (r : ℕ → ℕ) (n : ℕ) : ℝ :=
  let A := (side n x : ℝ) * side n y
  ((r n : ℝ) - A) * Real.log A / A

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle
