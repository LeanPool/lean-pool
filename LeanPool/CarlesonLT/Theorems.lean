/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import LeanPool.CarlesonLT.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import LeanPool.CarlesonLT.Auto.ClassicalCarleson

/-!
This file contains the statements of the main theorems:
`anisotropic_carleson` and `classical_carleson`
-/

@[expose] public section

namespace CarlesonLT

open CarlesonLT
open MeasureTheory Filter Topology Function Real Set SchwartzMap

variable {n : ℕ}

/-- Theorem 1.1 of `arXiv:1710.10962` proving a weak (2,2) a priori bound for
Carleson operators associated with anisotropic multipliers on `ℝ^n`. -/
theorem anisotropic_carleson (α : Fin n → ℕ) (hα : ∀ i, 1 ≤ α i) (hn : 0 < n) (ν₀ : ℕ)
    (hν₀ : 3 * (∑ i, α i) + 2 ≤ ν₀) :
      ∃ C : ℝ, 0 < C ∧ ∀ (m : ℝ^n → ℂ), MultiplierClass α ν₀ m → ∀ f : 𝓢(ℝ^n, ℂ),
        weakL2Norm volume (carlesonOperator m f) ≤
          ENNReal.ofReal C * (multiplierNorm α ν₀ m) * eLpNorm f 2 volume :=
  Auto.anisotropic_carleson α hα hn ν₀ hν₀

/-- **Carleson's theorem.** The Fourier series of a `2π`-periodic `L²` function
on `ℝ` converges pointwise almost everywhere. -/
theorem classical_carleson (f : ℝ → ℂ) (hper : Periodic f (2 * π))
    (hf : MemLp f 2 (volume.restrict (Ico 0 (2 * π)))) :
    ∀ᵐ x, Tendsto (fun N ↦ fourierPartialSum f N x) atTop (𝓝 (f x)) :=
  Auto.classical_carleson f hper hf

end CarlesonLT
