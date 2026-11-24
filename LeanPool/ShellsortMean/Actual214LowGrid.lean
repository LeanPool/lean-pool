/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.Actual214RetainedMode
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-! The total low-frequency contribution of an actual candidate h after the
two retained passes. Count grid indices, not union-of-grids multiplicities. -/
@[expose] public noncomputable section
namespace Shellsort.Actual214
open Finset RoughGapEndpoint

def lowGrid (h D : ℕ) : Finset ℕ :=
  (range h).filter (fun a => 0 < a ∧ h / Nat.gcd h a ≤ D)

private theorem low_facts {h D a : ℕ} (ha : a ∈ lowGrid h D) :
    0 < a ∧ a < h ∧ 0 < Nat.gcd h a ∧ 0 < a / Nat.gcd h a ∧
    a / Nat.gcd h a < h / Nat.gcd h a ∧ h / Nat.gcd h a ≤ D := by
  obtain ⟨hr, apos, hd⟩ := mem_filter.mp ha
  have lt := mem_range.mp hr
  have g := Nat.gcd_pos_of_pos_left a (by omega : 0 < h)
  exact ⟨apos, lt, g, Nat.div_pos (Nat.gcd_le_right h apos) g,
    (Nat.div_lt_div_right g.ne' (Nat.gcd_dvd_left h a)).mpr lt, hd⟩

/-- The map to (reduced numerator, reduced denominator minus 1) lands in a
D by D box and is one-to-one on a fixed grid. Includes D = 0 and h = 0. -/
theorem lowGrid_card_le (h D : ℕ) : (lowGrid h D).card ≤ D ^ 2 := by
  let f (a : ℕ) := (a / Nat.gcd h a, h / Nat.gcd h a - 1)
  have hb : (lowGrid h D).card ≤ ((range D) ×ˢ (range D)).card := by
    apply card_le_card_of_injOn f
    · intro a ha
      obtain ⟨_, _, _, _, hl, hu⟩ := low_facts ha
      apply mem_product.mpr
      exact ⟨mem_range.mpr (by dsimp [f]; omega), mem_range.mpr (by dsimp [f]; omega)⟩
    · intro a ha b hb eq
      obtain ⟨_, _, _, _, hla, _⟩ := low_facts ha
      obtain ⟨_, _, _, _, hlb, _⟩ := low_facts hb
      have ea : a / Nat.gcd h a = b / Nat.gcd h b := congrArg Prod.fst eq
      have e0 : h / Nat.gcd h a - 1 = h / Nat.gcd h b - 1 := congrArg Prod.snd eq
      have ed : h / Nat.gcd h a = h / Nat.gcd h b := by omega
      have va := Nat.div_mul_cancel (Nat.gcd_dvd_left h a)
      have vb := Nat.div_mul_cancel (Nat.gcd_dvd_left h b)
      rw [← ed] at vb
      have eg := Nat.eq_of_mul_eq_mul_left (by omega : 0 < h / Nat.gcd h a) (va.trans vb.symm)
      calc
        a = (a / Nat.gcd h a) * Nat.gcd h a := (Nat.div_mul_cancel (Nat.gcd_dvd_right h a)).symm
        _ = (b / Nat.gcd h b) * Nat.gcd h b := by rw [ea, eg]
        _ = b := Nat.div_mul_cancel (Nat.gcd_dvd_right h b)
  simpa [pow_two] using hb

/-- Any primitive h-th root enumerates this physical grid, in either
orientation; the bound uses the original (pre-retained-pass) error mass. -/
theorem menu_lowGrid_total {n c h g₁ g₂ D : ℕ}
    (p : RankPlacement n) (T : ℕ) (hT : T ≤ n) (h₂ : 0 < g₂) (hle : g₂ ≤ g₁)
    (hh : h ∈ window c (Nat.gcd g₁ g₂)) (z : ℂ) (hz : IsPrimitiveRoot z h) :
    (∑ a ∈ lowGrid h D, ‖amplitude (gapSort (gapSort p g₁) g₂) T (z ^ a)‖ ^ 2) ≤
      (2 * (g₁ : ℝ) * D ^ 3) * (∑ i, |(slotError p T i : ℝ)|) := by
  let mass : ℝ := ∑ i, |(slotError p T i : ℝ)|
  have mp : 0 ≤ mass := by dsimp [mass]; positivity
  calc
    _ ≤ ∑ _a ∈ lowGrid h D, (2 * (g₁ : ℝ) * D) * mass := by
      apply sum_le_sum
      intro a ha
      obtain ⟨ap, lt, g, na, nd, du⟩ := low_facts ha
      have pd := hz.pow_div_gcd a g.ne'
      have pos : 1 < h / Nat.gcd h a := by omega
      have bound := menu_mode_after_retained p T hT h₂ hle hh
        (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left h a)) pos (z ^ a) (pd.norm'_eq_one (by omega)) pd
      apply bound.trans
      change (2 * (g₁ : ℝ) * (h / Nat.gcd h a : ℕ)) * mass ≤ _
      gcongr
    _ = ((lowGrid h D).card : ℝ) * ((2 * (g₁ : ℝ) * D) * mass) := by simp [nsmul_eq_mul]
    _ ≤ ((D : ℝ) ^ 2) * ((2 * (g₁ : ℝ) * D) * mass) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast lowGrid_card_le h D
    _ = _ := by dsimp [mass]; ring

end Shellsort.Actual214
