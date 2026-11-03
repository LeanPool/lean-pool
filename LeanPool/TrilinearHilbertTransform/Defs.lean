/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!

# Definition of the trilinear Hilbert transform

-/

@[expose] public noncomputable section

namespace TrilinearHT

open Topology Filter

/-- Truncated trilinear Hilbert transform of a triple of functions `f` at `x`. -/
def T_trunc (f : Fin 3 → ℝ → ℂ) (x : ℝ) (ε : ℝ) : ℂ :=
  ∫ t in {t : ℝ | ε < |t|}, (∏ i : Fin 3, f i (x + (i.val + 1) * t)) / t

/-- Trilinear Hilbert transform.

**Note:** The (trivial) fact that the principal value limit exists when `f` are Schwartz functions
is proved as the automatically generated lemma `Auto.tendsto_T_trunc`.
-/
def T (f : Fin 3 → ℝ → ℂ) (x : ℝ) : ℂ := limUnder (𝓝[>] 0) (T_trunc f x)

end TrilinearHT

end
