/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.Actual214LowGrid
public import LeanPool.ShellsortMean.RoughGapDenominatorAverage

/-! Write the preceding estimate with exactly the negative-sign Fourier
energy used by the large-denominator sieve, on the real physical slots. -/
@[expose] public noncomputable section
namespace Shellsort.Actual214
open Finset RoughGapEndpoint RoughGapDenominatorAverage

/-- The root of unity with negative orientation used to evaluate Fourier sums. -/
def negGridRoot (h : ℕ) : ℂ := Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I / h))

theorem negGridRoot_primitive {h : ℕ} (hh : 0 < h) : IsPrimitiveRoot (negGridRoot h) h := by
  let z := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / h)
  have hp : IsPrimitiveRoot z h := Complex.isPrimitiveRoot_exp h hh.ne'
  change IsPrimitiveRoot (Complex.exp (-_)) h
  rw [Complex.exp_neg]
  constructor
  · change (z⁻¹) ^ h = 1
    rw [inv_pow, hp.pow_eq_one, inv_one]
  · intro m hm
    apply hp.dvd_of_pow_eq_one m
    simpa only [inv_pow, inv_eq_one] using hm

theorem physical_energy_eq_grid {n : ℕ} (p : RankPlacement n) (T a h : ℕ) :
    energy 0 (fun i : Fin n ↦ (slotError p T i : ℂ)) (a, h) =
    ‖amplitude p T ((negGridRoot h) ^ a)‖ ^ 2 := by
  unfold energy amplitude negGridRoot
  congr 2
  apply sum_congr rfl
  intro i _
  congr 1
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 1
  simp only [Int.cast_zero, zero_add]
  ring

theorem physical_low_grid_after_retained {n c h g₁ g₂ D : ℕ}
    (p : RankPlacement n) (T : ℕ) (hT : T ≤ n) (h₂ : 0 < g₂) (hle : g₂ ≤ g₁)
    (hp : 0 < h) (hh : h ∈ window c (Nat.gcd g₁ g₂)) :
    (∑ a ∈ lowGrid h D, energy 0 (fun i : Fin n ↦
        (slotError (gapSort (gapSort p g₁) g₂) T i : ℂ)) (a, h)) ≤
      (2 * (g₁ : ℝ) * D ^ 3) * (∑ i, |(slotError p T i : ℝ)|) := by
  simp_rw [physical_energy_eq_grid]
  exact menu_lowGrid_total p T hT h₂ hle hh _ (negGridRoot_primitive hp)

end Shellsort.Actual214
