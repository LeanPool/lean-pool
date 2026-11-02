/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.ConvolutionMean
public import LeanPool.NairTenenbaum.NumberFields.IdealNormMultiplicative

/-! # Ideal norm counts as a multiplicative arithmetic function with positive mean -/

@[expose] public section

namespace NairTenenbaum

open Finset Filter NumberField
open scoped Topology

variable (K : Type*) [Field K] [NumberField K]

/-- Zero at zero, since arithmetic functions encode only positive integers. -/
noncomputable def idealNormArithmetic : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (idealNormCount K n : ℝ), by simp⟩

theorem idealNormArithmetic_apply_pos {n : ℕ} (hn : 0 < n) :
    idealNormArithmetic K n = (idealNormCount K n : ℝ) := by
  simp [idealNormArithmetic, hn.ne']

theorem idealNormArithmetic_isMultiplicative : (idealNormArithmetic K).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · simp [idealNormArithmetic]
  · intro m n hm hn hcop
    simp only [idealNormArithmetic, ArithmeticFunction.coe_mk, hm, hn, mul_ne_zero hm hn,
      ↓reduceIte, idealNormCount_mul_of_coprime hcop, Nat.cast_mul]

theorem idealNormArithmetic_mean :
    Tendsto (fun n : ℕ => (∑ k ∈ Icc 1 n, idealNormArithmetic K k) / n) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  convert idealNormCount_partialSum_limit K using 1
  ext n
  congr 1
  apply sum_congr rfl
  intro k hk
  exact idealNormArithmetic_apply_pos K (mem_Icc.mp hk).1

theorem idealNormArithmetic_convolution_mean {g : ArithmeticFunction ℝ}
    (hg : Summable (fun d : ℕ => |g d| / d)) :
    Tendsto (fun x : ℝ => arithmeticSummatory (g * idealNormArithmetic K : ArithmeticFunction ℝ) x
        / x)
      atTop (𝓝 (dedekindZeta_residue K * ∑' d : ℕ, g d / d)) :=
  arithmeticFunction_convolution_mean (idealNormArithmetic_mean K) hg

end NairTenenbaum
