/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-
Ported from RegularityStructures-dev, commit 852e51c64f977a7cdd3eacab66e0188bc0ed75a2.
Modified for EhrhardGaussian, 2026.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-! Prepending a scalar coordinate to a finite real vector. -/

@[expose] public noncomputable section

namespace EhrhardGaussian.Gaussian

/-- Prepend one scalar coordinate to a finite real vector. -/
def finCons {n : ℕ} (x : ℝ) (y : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  @Fin.cons n (fun _ : Fin (n + 1) => ℝ) x y

end EhrhardGaussian.Gaussian

end
