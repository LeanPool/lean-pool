/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EdAssemblyOneStep
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SlopeStabilityEndpoints

/-!
# EdBridgeFolds

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The three folds between the anchored one-step and the Step-4 slot

The anchored interior one-step delivers the one-step contraction
with the anchor's four printed legs on the right.  The iteration anchor's own
per-scale hypothesis (`e.Ej.decay.assumption`, named `IterationDecay` by the
Step-5 provider) asks instead for

```text
   E(u, U_{j-h}) ≤ θ^h E(u, U_j) + ε_j |∇ℓ_j| + δ_j ,        θ = 3^{-1/4} .
```

This module is the scalar/geometric part of that conversion — residues 1, 2
and 4, each as a standalone atom, with the window bookkeeping of residue 3 left
to `EdBridgeStepFour`.

## The three atoms

* **The good-event cap fold** (residue 1).  `rpow_neg_four_mul_le_of_cap` is
  the multiplication `C s^{-4} · 𝓔 · X ≤ C · C_cap · s^{-3} · δ^{1/2} · X`,
  valid at any `X ≥ 0` once the proved
  `OneStepGoodScales.ae_errorRepresentative_le_goodEventDeltaSlot` supplies `𝓔
  ≤ C_cap s δ^{1/2}` on the supply event.  It is the printed `s^{-1/2} δ^{1/2}`
  of `e.excess.decay.one.step` read at the re-pin `s^{-4}`.
* **The oscillation-to-excess fold** (residue 2).
  `normalizedL2On_sub_average_truncatedWindow_le` turns the anchor's leg-1
  carrier `‖u − (u)_{W}‖_{L²(W)}` on a truncated window `W = (z+□_j) ∩ □_m`
  into `3^j · C_i(d) · (E(u,W) + |∇ℓ(u,W)|)`, by the proved endpoint comparison
  at the window's own aspect-`1/9` sandwich
  (`SlopeStabilityEndpoints.endpoint_comparisons_of_axisCubeSandwich`) and the
  proved normalizer comparison (`AffineExcess.rpow_normalizer_bounds`).  The
  `eLpNorm`-shaped version is the one the anchor's display literally carries.
* **The contraction absorption** (residue 4).  `exists_edBridgeStep` produces
  the step size `k₀(d)`: for every `k ≥ k₀`,
  ```text
     C_t(d) · C_sch(d) · κ(d,2) · κ(d,1) · (3^{-k})^{1/2} ≤ ½ · 3^{-(k+1)/4} ,
  ```
  `κ(d,1) = windowRatioConst d 1` being the price of the excess
  quasi-monotonicity `E(u,U_{j-1}) ≤ κ(d,1) E(u,U_j)` that residue 3 pays for
  the one-scale re-index.

## References

* ABK26, `l.excess.decay.good.scales`, the printed one-step, the
  oscillation-to-excess comparison and the good-event cap; `t.regularity` Step
  4.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ## 1. The good-event cap fold -/

/-- `s^{-4} · s = s^{-3}` for `s > 0`, the only exponent arithmetic the cap fold needs. -/
theorem rpow_neg_four_mul_self {s : ℝ} (hs : 0 < s) :
    Real.rpow s (-(4 : ℝ)) * s = Real.rpow s (-(3 : ℝ)) := by
  change s ^ (-(4 : ℝ)) * s = s ^ (-(3 : ℝ))
  rw [show (-(3 : ℝ)) = -(4 : ℝ) + 1 by norm_num, Real.rpow_add hs, Real.rpow_one]

/-- ** residue 1: the good-event cap fold.**

On the supply event the proved good-event cap
`OneStepGoodScales.ae_errorRepresentative_le_goodEventDeltaSlot` gives `𝓔 ≤
C_cap · s · δ^{1/2}`.  Substituting it into the anchor's leg prefactor `C
s^{-4} 𝓔` turns the whole leg into `C · C_cap · s^{-3} · δ^{1/2}` times its
(nonnegative) carrier — the printed `3^{(1+d/2)k} s^{-1/2} δ^{1/2}` slot, at
the `ε`-re-pin's `s^{-4}`. -/
theorem rpow_neg_four_mul_le_of_cap {s : ℝ} (hs : 0 < s) {Ecal Ccap dlt X Cc : ℝ}
    (hcap : Ecal ≤ Ccap * s * Real.sqrt dlt) (hX : 0 ≤ X) (hCc : 0 ≤ Cc) :
    Cc * Real.rpow s (-(4 : ℝ)) * Ecal * X
      ≤ Cc * Ccap * Real.rpow s (-(3 : ℝ)) * Real.sqrt dlt * X := by
  have h4 : (0 : ℝ) ≤ Real.rpow s (-(4 : ℝ)) := Real.rpow_nonneg hs.le _
  have hstep : Cc * Real.rpow s (-(4 : ℝ)) * Ecal * X
      ≤ Cc * Real.rpow s (-(4 : ℝ)) * (Ccap * s * Real.sqrt dlt) * X :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcap (mul_nonneg hCc h4)) hX
  have heq : Cc * Real.rpow s (-(4 : ℝ)) * (Ccap * s * Real.sqrt dlt) * X
      = Cc * Ccap * Real.rpow s (-(3 : ℝ)) * Real.sqrt dlt * X := by
    rw [← rpow_neg_four_mul_self hs]
    ring
  linarith only [hstep, heq]

/-! ## 2. The oscillation-to-excess fold on a truncated window -/

/-- The aspect ratio of the proved truncated-window sandwich: `(1/9) · 3^j =
3^{j-2}`. -/
theorem truncatedWindow_aspect (j : ℤ) :
    (1 / 9 : ℝ) * (3 : ℝ) ^ j ≤ (3 : ℝ) ^ (j - 2) := by
  have h : (3 : ℝ) ^ (j - 2) = (3 : ℝ) ^ j / (3 : ℝ) ^ (2 : ℤ) :=
    zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0) j 2
  have h9 : ((3 : ℝ) ^ (2 : ℤ)) = 9 := by norm_num
  rw [h, h9]
  linarith only []

/-- ** residue 2, on the window carrier.**  The volume-normalized oscillation of
`u` on a truncated window is controlled by the excess and the slope of any
affine minimizer there, at the proved endpoint constant `C_i(d) = endpointConst
d (1/9)` of the aspect-`1/9` sandwich. -/
theorem oscillationOn_truncatedWindow_le (hd : d ≠ 0) {m j : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (hjm : j - 1 ≤ m) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow z m j))) {c : ℝ} {g : Vec d}
    (hmin : IsAffineMinimizer (truncatedWindow z m j) u c g) :
    oscillationOn (truncatedWindow z m j) u
      ≤ endpointConst d (1 / 9 : ℝ)
          * (affineExcess (truncatedWindow z m j) u + slopeMagnitude g) := by
  obtain ⟨zin, zout, hin, hout⟩ := exists_axisCube_sandwich_truncatedWindow z hz hjm
  exact (endpoint_comparisons_of_axisCubeSandwich (Nat.pos_of_ne_zero hd)
    (zpow_pos (by norm_num) (j - 2)) (zpow_pos (by norm_num) j) (by norm_num)
    (truncatedWindow_aspect j) (measurableSet_truncatedWindow z m j) hin hout hu hmin).1

/-- ** residue 2, on the anchor's own carrier.**  The un-normalized mean-subtracted
`L²` norm — the anchor's leg-1 object — in terms of the excess and the slope:

```text
   ‖u − (u)_{(z+□_j)∩□_m}‖_{L²((z+□_j)∩□_m)}
     ≤ 3^j · C_i(d) · ( E(u,(z+□_j)∩□_m) + |∇ℓ| ) .
```

The factor `3^j` is the proved normalizer comparison `|W|^{-1/d} ≥ 3^{-j}` on
the window's own volume sandwich; no sharper aspect ratio than the printed
`3^{-2}` is used. -/
theorem normalizedL2On_sub_average_truncatedWindow_le (hd : d ≠ 0) {m j : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (hjm : j - 1 ≤ m) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow z m j))) {c : ℝ} {g : Vec d}
    (hmin : IsAffineMinimizer (truncatedWindow z m j) u c g) :
    normalizedL2On (truncatedWindow z m j)
        (fun y => u y - volumeAverage (truncatedWindow z m j) u)
      ≤ (3 : ℝ) ^ j * (endpointConst d (1 / 9 : ℝ)
          * (affineExcess (truncatedWindow z m j) u + slopeMagnitude g)) := by
  obtain ⟨hlo, _⟩ := rpow_normalizer_bounds (d := d) hd
    (volume_toReal_truncatedWindow_bounds z hz hjm).1
    (volume_toReal_truncatedWindow_bounds z hz hjm).2
  have hstep : (3 : ℝ) ^ (-j) * normalizedL2On (truncatedWindow z m j)
      (fun y => u y - volumeAverage (truncatedWindow z m j) u)
      ≤ oscillationOn (truncatedWindow z m j) u :=
    mul_le_mul_of_nonneg_right hlo (normalizedL2On_nonneg _ _)
  have hfold := oscillationOn_truncatedWindow_le hd hz hjm hu hmin
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hid : (3 : ℝ) ^ j * ((3 : ℝ) ^ (-j)) = 1 := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have hmul := mul_le_mul_of_nonneg_left (hstep.trans hfold) h3.le
  have hcancel : (3 : ℝ) ^ j * ((3 : ℝ) ^ (-j) * normalizedL2On (truncatedWindow z m j)
      (fun y => u y - volumeAverage (truncatedWindow z m j) u))
      = normalizedL2On (truncatedWindow z m j)
        (fun y => u y - volumeAverage (truncatedWindow z m j) u) := by
    rw [← mul_assoc, hid, one_mul]
  linarith only [hmul, hcancel]

/-- ** residue 2, in the anchor's printed shape.**  The same fold with the
left-hand side written as the `toReal` of an `eLpNorm` against the normalized
volume measure — the literal carrier of the anchor's leg 1. -/
theorem eLpNorm_sub_average_truncatedWindow_le (hd : d ≠ 0) {m j : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (hjm : j - 1 ≤ m) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow z m j))) {c : ℝ} {g : Vec d}
    (hmin : IsAffineMinimizer (truncatedWindow z m j) u c g) :
    (eLpNorm (fun y => u y - volumeAverage (truncatedWindow z m j) u) 2
        (normalizedVolumeMeasureOn (truncatedWindow z m j))).toReal
      ≤ (3 : ℝ) ^ j * (endpointConst d (1 / 9 : ℝ)
          * (affineExcess (truncatedWindow z m j) u + slopeMagnitude g)) := by
  have htop : volume (truncatedWindow z m j) ≠ ⊤ :=
    ne_of_lt (volume_truncatedWindow_lt_top z m j)
  have hreal : (0 : ℝ) < (volume (truncatedWindow z m j)).toReal :=
    volume_toReal_truncatedWindow_pos z hz hjm
  have hpos : 0 < volume (truncatedWindow z m j) :=
    (ENNReal.toReal_pos_iff.1 hreal).1
  have : IsFiniteMeasure (volume.restrict (truncatedWindow z m j)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 htop
  have hf : MemLp (fun y => u y - volumeAverage (truncatedWindow z m j) u) 2
      (volume.restrict (truncatedWindow z m j)) := hu.sub (memLp_const _)
  have hEq := normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn hpos htop hf
  rw [← hEq]
  exact normalizedL2On_sub_average_truncatedWindow_le hd hz hjm hu hmin

/-! ## 3. The contraction absorption -/

/-- `(3^{-k})^{1/2} = (3^{-1/2})^k`: the one-step's contraction factor as a natural power. -/
theorem zpow_neg_rpow_half_eq (k : ℕ) :
    ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) = ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ k := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have hcast : ((3 : ℝ) ^ (-(k : ℤ))) = (3 : ℝ) ^ (-(k : ℝ)) := by
    rw [← Real.rpow_intCast (3 : ℝ) (-(k : ℤ))]
    norm_num
  rw [hcast, ← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 2 : ℝ))) k, ← Real.rpow_mul h3,
    ← Real.rpow_mul h3]
  congr 1
  ring

/-- `3^{-(k+1)/4} = 3^{-1/4} · (3^{-1/4})^k`: the target contraction ratio as a natural power. -/
theorem rpow_quarter_succ_eq (k : ℕ) :
    (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1))
      = (3 : ℝ) ^ (-(1 / 4 : ℝ)) * ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 4 : ℝ))) k, ← Real.rpow_mul h3.le,
    ← Real.rpow_add h3]
  congr 1
  ring

/-- `3^{-1/2} = (3^{-1/4})²`, the identity that makes the absorption a single division. -/
theorem rpow_half_eq_quarter_sq :
    (3 : ℝ) ^ (-(1 / 2 : ℝ))
      = (3 : ℝ) ^ (-(1 / 4 : ℝ)) * (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  norm_num

/-- `0 < 3^{-1/4} < 1`. -/
theorem rpow_quarter_mem : (3 : ℝ) ^ (-(1 / 4 : ℝ)) ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨Real.rpow_pos_of_pos (by norm_num) _,
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)⟩

/-- ** residue 4: the contraction absorption.**

There is a step size `k₀(d) ≥ 3` beyond which the one-step's contraction prefactor — including
the quasi-monotonicity price `κ(d,1)` that the one-scale re-index of residue 3 pays — is
absorbed into *half* of the iteration anchor's ratio `θ^{k+1} = 3^{-(k+1)/4}`.  The remaining
half is what the good-event cap fold of residue 1 is gated against. -/
theorem exists_edBridgeStep (d : ℕ) [NeZero d] :
    ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2
            * windowRatioConst d 1 * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
        ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) := by
  classical
  obtain ⟨hq0, hq1⟩ := rpow_quarter_mem
  set q : ℝ := (3 : ℝ) ^ (-(1 / 4 : ℝ)) with hqdef
  set A : ℝ := max (taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2
    * windowRatioConst d 1) 1 with hAdef
  have hA1 : (1 : ℝ) ≤ A := le_max_right _ _
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA1
  have hAle : taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2
      * windowRatioConst d 1 ≤ A := le_max_left _ _
  obtain ⟨k₁, hk₁⟩ := exists_pow_lt_of_lt_one (x := 1 / 2 * q / A) (y := q)
    (div_pos (by linarith only [hq0] : (0 : ℝ) < 1 / 2 * q) hApos) hq1
  refine ⟨max k₁ 3, le_max_right _ _, ?_⟩
  intro k hk
  have hk1 : k₁ ≤ k := le_trans (le_max_left _ _) hk
  have hqk : q ^ k ≤ q ^ k₁ := pow_le_pow_of_le_one hq0.le hq1.le hk1
  have hqklt : q ^ k < 1 / 2 * q / A := lt_of_le_of_lt hqk hk₁
  have hqkpos : (0 : ℝ) < q ^ k := pow_pos hq0 k
  -- the absorption at the level of the two natural powers
  have hkey : A * q ^ k ≤ 1 / 2 * q := by
    have h := (le_div_iff₀ hApos).1 (le_of_lt hqklt)
    linarith only [h]
  have hmul : A * q ^ k * q ^ k ≤ 1 / 2 * q * q ^ k :=
    mul_le_mul_of_nonneg_right hkey hqkpos.le
  -- rewrite both sides of the goal into the `q`-power shape
  have hL : ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) = q ^ k * q ^ k := by
    rw [zpow_neg_rpow_half_eq k, rpow_half_eq_quarter_sq, ← hqdef, mul_pow]
  have hR : (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) = q * q ^ k := by
    rw [rpow_quarter_succ_eq k, ← hqdef]
  rw [hL, hR]
  have hqq : (0 : ℝ) ≤ q ^ k * q ^ k := mul_nonneg hqkpos.le hqkpos.le
  have hleft : taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2
        * windowRatioConst d 1 * (q ^ k * q ^ k) ≤ A * (q ^ k * q ^ k) :=
    mul_le_mul_of_nonneg_right hAle hqq
  linarith only [hleft, hmul]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
