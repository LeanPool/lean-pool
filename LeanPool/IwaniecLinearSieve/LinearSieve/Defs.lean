/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.SieveMajorants.Majorants
import Mathlib.NumberTheory.Chebyshev

/-!
# Notation for [I71, §4]

`L = log y`, `ξ(y) = log y / (log log 3y)^{11/5}`, `δ(s, y) = (1 + s² log⁵ s / log² y)^{5s}`.
The main-term majorants are `f` (lower sieve) and `F + (3 - s)⁺` (upper sieve, which also
contains the depth-one deficit); the error majorants are `𝔣` and `𝔉`.
-/

@[expose] public section

open Real

namespace IwaniecLinearSieve

/-- Iwaniec's `ξ = log y / (log log 3y)^{11/5}`. -/
noncomputable def xi (y : ℝ) : ℝ := log y / log (log (3 * y)) ^ (11 / 5 : ℝ)

/-- Iwaniec's compensation factor `(1 + s² log⁵ s / log² y)^{5s}`. -/
noncomputable def delta (s y : ℝ) : ℝ := (1 + s ^ 2 * log s ^ 5 / log y ^ 2) ^ (5 * s)

/-- Main-term majorants: `f` for the lower sieve, `F + (3 - s)⁺` for the upper sieve. -/
noncomputable def mainMaj : Bool → ℝ → ℝ
  | true, s => fSieve s
  | false, s => FSieve s + max (3 - s) 0

/-- Error majorants `G`: `𝔣` for the lower sieve, `𝔉` for the upper sieve. -/
noncomputable def errMaj : Bool → ℝ → ℝ
  | true => majf
  | false => majF

/-- The smallest sifting parameter `s`: `2` for the lower sieve, `1` for the upper sieve. -/
def sMin : Bool → ℝ
  | true => 2
  | false => 1

end IwaniecLinearSieve
