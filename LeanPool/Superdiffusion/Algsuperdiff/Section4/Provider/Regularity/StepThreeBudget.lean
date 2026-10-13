/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepThreeBadSet

/-!
# StepThreeBudget

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 3: the bad-scale budget, centre-uniformly, and the
# separation `|𝓑_z| + 7 ≤ m - n`

## The target

ABK26 `e.bad.scale.proportion.bound`:

```
|𝓑_z| ≤ max_{z' ∈ 3^n ℤ^d ∩ □_m} Σ_{j=n}^{m} (1 - 1_{𝒢(j,z'; ⅛s, ⅛ s δ^{1/2})})
      ≤ δ (m - n + 1) = C₁^{-1}(1-α)(m-n+1) .
```

The producer is the `Algsuperdiff.Frozen.Section4.minimal_scale_separation`
whose conclusion body exported as `GoodScaleWindows`: its S clause is literally
the centre-uniform Cesàro density

```
sup_{z' ∈ 3^{n-1} ℤ^d ∩ □_m} ( (m-n+1)^{-1} Σ_{k=n}^{m} 1_{𝒢(k,z')ᶜ} ) ≤ δ ,
```

Multiplying the Cesàro form by `(m-n+1)` and dropping the scale `m` (which
`𝓑_z` does not contain) is the whole conversion.

## The producer's lattice is finer than the printed one

The producer's supremum runs over `3^{n-1} ℤ^d ∩ □_m`, the printed maximum over
`3^{n} ℤ^d ∩ □_m`.  Since `3^n ℤ^d ⊆ 3^{n-1} ℤ^d` (`triadicLatticePoint_shift`),
the delivered bound is at least as strong as the printed one at every printed
centre; `stepThreeBadSet_card_le_of_goodScaleWindows` is the printed statement,
`..._fine` the stronger one actually available.

## The separation `|𝓑_z| + 7 ≤ m - n`, resolved

The honest resolution, with the exact arithmetic:

* the budget is `|𝓑| ≤ δ(t+1)` with `t := m - n`, and `δ ≤ 1/2`
  (`stepOneDelta_mem`), so `2|𝓑| ≤ t + 1`;
* `|𝓑|` is an integer, so this is `|𝓑| ≤ ⌊(t+1)/2⌋`, and `⌊(t+1)/2⌋ + 7 ≤ t` holds
  **iff `t ≥ 14`** — for even `t` at `t ≥ 14` (`t/2 + 7 ≤ t`), for odd `t` at
  `t ≥ 15` (`(t+1)/2 + 7 ≤ t`), and `t = 15` is the first odd value.  The naive
  real-valued reading `(t+1)/2 + 7 ≤ t ↔ t ≥ 15` is one unit pessimistic;
  integrality buys the missing unit at `t = 14`;
* `t = 13` genuinely fails (`|𝓑| ≤ 7` and `7 + 7 = 14 > 13`), so a window length
  of 13 does not suffice;
* the fix costs nothing: `X_m(α) = Z_m + k + 3 ≥ 14` needs only `k ≥ 11`, and
  `k = ⌈4 log₃(16 C_edos)⌉ ≥ 11` follows from the same explicit floor
  `1 ≤ C_edos` that gives `k ≥ 10` — because `⌈x⌉ ≥ 11 ↔ x > 10` and
  `3^5 = 243 < 256 = 16²` is a strict inequality.  So no
  `C_edos` floor moves, no `k`-formula moves, and no statement anywhere changes;
  only the pin sharpens from `k ≥ 10, X ≥ 13` to `k ≥ 11, X ≥ 14`.

The exact `C_edos` floor for `k ≥ 11` is `C_edos > 3^{5/2}/16 = 0.97427…`, so
the standing floor `C_edos ≥ 1` has room; the floor for `k ≥ 12` would be
`C_edos > 3^{11/4}/16 = 1.28…`, which is not free, and is not needed.

## Contents

* `triadicLatticePoint_shift`, `mem_latticeCubeSet_shift`,
  `mem_openCubeSet_of_mem_latticeCubeSet` — the lattice bookkeeping.
* `stepThreeBadSet_card_le_of_goodScaleWindows(_fine)` — the budget.
* `fourteen_le_minimalScaleX`, `fourteen_le_window` — the
  sharpened window-length pin.
* `stepOneBadSetSeparation_of_card_le`,
  `stepOneBadSetSeparation_of_goodScaleWindows` — the separation.

## References

* ABK26, `t.regularity` Steps 1--3.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-! ## 1. The lattice bookkeeping -/

/-- `3^n v = 3^{n-1}(3v)`: the printed centre lattice `3^n ℤ^d` sits inside the
producer's finer lattice `3^{n-1} ℤ^d`. -/
theorem triadicLatticePoint_shift (n : ℤ) (v : Fin d → ℤ) :
    Support.triadicLatticePoint (n - 1) (fun i => 3 * v i) =
      Support.triadicLatticePoint n v := by
  funext i
  simp only [Support.triadicLatticePoint]
  push_cast
  rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
  ring

/-- The embedding on index sets. -/
theorem mem_latticeCubeSet_shift {n m : ℤ} {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeCubeSet d n m) :
    (fun i => 3 * v i) ∈ Support.latticeCubeSet d (n - 1) m := by
  rw [Support.latticeCubeSet, Set.mem_ofPred_eq, triadicLatticePoint_shift]
  exact hv

/-- A lattice centre of `3^n ℤ^d ∩ □_m` lies in `□_m` — the hypothesis the window
family's sandwich needs. -/
theorem mem_openCubeSet_of_mem_latticeCubeSet {n m : ℤ} {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeCubeSet d n m) :
    Support.triadicLatticePoint n v ∈ openCubeSet (originCube d m) := hv

/-! ## 2. The budget -/

theorem stepThreeBadSet_card_le_of_goodScaleWindows_fine {M : ABKModel d} {delta : ℝ}
    {n m : ℤ} {omega : Cutoff.CutoffSample d} (hdelta : 0 ≤ delta)
    (hgood : GoodScaleWindows M stepOneSEighth delta stepOneSEighth_pos n m omega)
    {w : Fin d → ℤ} (hw : w ∈ Support.latticeCubeSet d (n - 1) m) :
    ((stepThreeBadSet M delta n m (Support.triadicLatticePoint (n - 1) w) omega).card :
        ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1) := by
  have hsup := le_trans (le_iSup (fun z : ↥(Support.latticeCubeSet d (n - 1) m) =>
      ((((m - n).toNat : ℝ≥0∞) + 1)⁻¹ *
        ∑ k ∈ Finset.Icc n m,
          Set.indicator
            ((Algsuperdiff.Frozen.Section4.goodEventAt M
                (Support.cgEllipLowerConstant d) k
                (Support.triadicLatticePoint (n - 1) z)
                ⟨stepOneSEighth, stepOneSEighth_pos⟩
                (stepOneSEighth * Real.sqrt delta))ᶜ)
            (fun _ => (1 : ℝ≥0∞)) omega)) ⟨w, hw⟩) hgood.2
  simp only [← stepThreeGoodEvent_eq_goodEventAt] at hsup
  set a : ℝ≥0∞ := ((m - n).toNat : ℝ≥0∞) with ha
  set z : Vec d := Support.triadicLatticePoint (n - 1) w with _hz
  have hne0 : a + 1 ≠ 0 := by positivity
  have hnetop : a + 1 ≠ ⊤ := by
    rw [ha]
    simp
  have hS : (∑ k ∈ Finset.Icc n m,
      Set.indicator ((stepThreeGoodEvent M delta k z)ᶜ) (fun _ => (1 : ℝ≥0∞)) omega) ≤
      ENNReal.ofReal delta * (a + 1) := by
    calc (∑ k ∈ Finset.Icc n m,
            Set.indicator ((stepThreeGoodEvent M delta k z)ᶜ) (fun _ => (1 : ℝ≥0∞)) omega)
        = ((a + 1) * (a + 1)⁻¹) * ∑ k ∈ Finset.Icc n m,
            Set.indicator ((stepThreeGoodEvent M delta k z)ᶜ)
              (fun _ => (1 : ℝ≥0∞)) omega := by
          rw [ENNReal.mul_inv_cancel hne0 hnetop, one_mul]
      _ = (a + 1) * ((a + 1)⁻¹ * ∑ k ∈ Finset.Icc n m,
            Set.indicator ((stepThreeGoodEvent M delta k z)ᶜ)
              (fun _ => (1 : ℝ≥0∞)) omega) := by rw [mul_assoc]
      _ ≤ (a + 1) * ENNReal.ofReal delta := by gcongr
      _ = ENNReal.ofReal delta * (a + 1) := mul_comm _ _
  have hcard : ((stepThreeBadSet M delta n m z omega).card : ℝ≥0∞) ≤
      ENNReal.ofReal (delta * (((m - n).toNat : ℝ) + 1)) := by
    refine le_trans (stepThreeBadSet_card_le_sum_Icc M delta n m z omega) (le_trans hS ?_)
    rw [ENNReal.ofReal_mul hdelta, ENNReal.ofReal_add (by positivity) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one, ha]
  rw [← ENNReal.ofReal_natCast] at hcard
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcard

/-- **`e.bad.scale.proportion.bound`**, at the printed centres `z ∈ 3^n ℤ^d ∩
□_m` and uniformly in them:

```
|𝓑_z| ≤ δ (m - n + 1) .
``` -/
theorem stepThreeBadSet_card_le_of_goodScaleWindows {M : ABKModel d} {delta : ℝ}
    {n m : ℤ} {omega : Cutoff.CutoffSample d} (hdelta : 0 ≤ delta)
    (hgood : GoodScaleWindows M stepOneSEighth delta stepOneSEighth_pos n m omega)
    {v : Fin d → ℤ} (hv : v ∈ Support.latticeCubeSet d n m) :
    ((stepThreeBadSet M delta n m (Support.triadicLatticePoint n v) omega).card : ℝ) ≤
      delta * (((m - n).toNat : ℝ) + 1) := by
  have h := stepThreeBadSet_card_le_of_goodScaleWindows_fine hdelta hgood
    (mem_latticeCubeSet_shift hv)
  rwa [triadicLatticePoint_shift] at h

/-! ## 3. The sharpened window-length pin -/

/-- **`X_m(α) ≥ 14`** at `k ≥ 11` (the sharpened pin). -/
theorem fourteen_le_minimalScaleX {Omega : Type*} (Z : Omega → ℕ∞) {k : ℕ}
    (hk : 11 ≤ k) (omega : Omega) : (14 : ℕ∞) ≤ minimalScaleX Z k omega := by
  rw [minimalScaleX_eq_add_cast]
  have h : ((14 : ℕ) : ℕ∞) ≤ ((k + 3 : ℕ) : ℕ∞) := Nat.cast_le.mpr (by omega)
  calc (14 : ℕ∞) = ((14 : ℕ) : ℕ∞) := by norm_num
    _ ≤ ((k + 3 : ℕ) : ℕ∞) := h
    _ ≤ Z omega + ((k + 3 : ℕ) : ℕ∞) := le_add_self

/-- **The window-length demand of Step 3**: at `k ≥ 11`, the gate `X_m(α) ≤ m - n`
is available only on windows of length at least 14 — the length the separation
needs. -/
theorem fourteen_le_window {Omega : Type*} (Z : Omega → ℕ∞) {k : ℕ} (hk : 11 ≤ k)
    (omega : Omega) {n m : ℤ}
    (hgate : minimalScaleX Z k omega ≤ (((m - n).toNat : ℕ) : ℕ∞)) :
    (14 : ℤ) ≤ m - n := by
  have h14 : ((14 : ℕ) : ℕ∞) ≤ (((m - n).toNat : ℕ) : ℕ∞) := by
    refine le_trans ?_ (le_trans (fourteen_le_minimalScaleX Z hk omega) hgate)
    norm_num
  have hnat : 14 ≤ (m - n).toNat := Nat.cast_le.mp h14
  omega

/-! ## 4. The separation -/

/-- **The separation, from the budget**: at `δ ≤ 1/2` and window length
at least 14, `|𝓑| + 7 ≤ m - n`.  The integrality of `|𝓑|` is what makes 14
(rather than 15) the threshold. -/
theorem stepOneBadSetSeparation_of_card_le {c : ℕ} {delta : ℝ} {n m : ℤ}
    (hdelta : delta ≤ 1 / 2) (hwin : (14 : ℤ) ≤ m - n)
    (hcard : (c : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1)) :
    StepOneBadSetSeparation c n m := by
  refine stepOneBadSetSeparation_of_le ?_
  have ht : (0 : ℝ) ≤ ((m - n).toNat : ℝ) := Nat.cast_nonneg _
  have h2 : (c : ℝ) ≤ 1 / 2 * (((m - n).toNat : ℝ) + 1) :=
    le_trans hcard (mul_le_mul_of_nonneg_right hdelta (by linarith only [ht]))
  have h3 : ((2 * c : ℕ) : ℝ) ≤ (((m - n).toNat + 1 : ℕ) : ℝ) := by
    push_cast
    linarith only [h2]
  have h4 : 2 * c ≤ (m - n).toNat + 1 := by exact_mod_cast h3
  have h5 : 14 ≤ (m - n).toNat := by omega
  omega

theorem stepOneBadSetSeparation_of_goodScaleWindows {M : ABKModel d} {delta : ℝ}
    {n m : ℤ} {omega : Cutoff.CutoffSample d} (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ 1 / 2) (hwin : (14 : ℤ) ≤ m - n)
    (hgood : GoodScaleWindows M stepOneSEighth delta stepOneSEighth_pos n m omega)
    {v : Fin d → ℤ} (hv : v ∈ Support.latticeCubeSet d n m) :
    StepOneBadSetSeparation
      (stepThreeBadSet M delta n m (Support.triadicLatticePoint n v) omega).card n m :=
  stepOneBadSetSeparation_of_card_le hdelta hwin
    (stepThreeBadSet_card_le_of_goodScaleWindows hdelta0 hgood hv)

end Algsuperdiff.Section4.Provider.Regularity
