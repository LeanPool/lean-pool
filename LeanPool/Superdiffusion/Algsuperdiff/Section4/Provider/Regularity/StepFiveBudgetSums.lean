/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFiveGeometricTail
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepThreeBudget

/-!
# StepFiveBudgetSums

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 5: the two budget sums

## The target

ABK26 `t.regularity` Step 5, the displays

```text
  e.sum.eps.j.bound
      ∑_{j=n}^{m-1} ε_j  ≤  C δ (m-n)  =  C C₁^{-1}(1-α)(m-n)

  e.sum.delta.j.bound
      ∑_{j=n}^{m-1} δ_j  ≤  C 3^{m/2} σ_m^{-1} [g]_{W^{1/2,∞}(□_m)}
        + C ( 3^{m/2} [∇h]_{W^{1/2,∞}(□_m)}
              + C₁^{-1}(1-α)(m-n) ‖∇h‖_{L^∞(□_m)} ) 1_{z ∉ □_{m-1}} .
```



The first display is unconditional here: it is the Cesàro clause of
`GoodScaleWindows` — the very same clause that supplies the bad-scale budget —
read on the `ε` leg instead of the indicator leg.  The manuscript attributes it to
"`e.scale.sep.for.mathcal.E` and the definition of `X_m(α)`"; in the proved
formalization the `X_m(α)` gate is what delivers `GoodScaleWindows`, so the
implication is exactly the one transcribed here.

The second display is proved in abstract-real form: its three legs are the two
geometric tails of
`StepFiveGeometricTail` plus one `ε`-sum leg, which is the first display again.

## Deviations from print

* **D1 (window).** The anchor `l.iteration.lemma` sums `ε` and `δ` over
  `Finset.Icc n m`; the manuscript's displays sum over `[n, m-1]`.  The `ε`
  bound below is proved on the larger window `Icc n m` (which is what
  `GoodScaleWindows` gives and what the anchor consumes), hence dominates the
  printed sum.
* **D2 (constant).** `GoodScaleWindows` yields `δ((m-n)+1)`, not `δ(m-n)`.  With
  the Step-3 window gate `14 ≤ m-n` this is `≤ 2δ(m-n)`, i.e. the printed
  `C δ (m-n)` at the explicit `C = 2`.  Recorded, not hidden.
* ** (binding).** The boundary leg `ε_j ‖∇h‖_{L^∞} 1_{z∉□_{m-1}}` is carried
  explicitly through the three-leg budget; it is NOT discarded.

## References

* ABK26, `t.regularity` Step 5.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal
open scoped Classical

variable {d : ℕ}

/-! ## 1. The real-valued `ε_j(z)` family -/

/-- **`ε_j(z)` as a real number.**'s `stepOneEpsJ` is `ℝ≥0∞`-valued, while
`l.iteration.lemma` demands `ε : ℤ → ℝ`; this is the `toReal` layer. -/
noncomputable def stepFiveEps (M : ABKModel d) (j : ℤ) (z : Vec d) (delta : ℝ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  (stepOneEpsJ M j z delta omega).toReal

/-- `ε_j(z) ≥ 0` — the sign hypothesis of `l.iteration.lemma`. -/
theorem stepFiveEps_nonneg (M : ABKModel d) (j : ℤ) (z : Vec d) (delta : ℝ)
    (omega : Cutoff.CutoffSample d) : 0 ≤ stepFiveEps M j z delta omega :=
  ENNReal.toReal_nonneg

/-! ## 2. `e.sum.eps.j.bound` -/

/-- **The `ε`-Cesàro clause read as a sum**, at the producer's own (finer) lattice:
`∑_{k=n}^{m} ε_k(z) ≤ δ ((m-n)+1)` in `ℝ≥0∞`. -/
theorem sum_stepOneEpsJ_le_of_goodScaleWindows_fine {M : ABKModel d} {delta : ℝ}
    {n m : ℤ} {omega : Cutoff.CutoffSample d}
    (hgood : GoodScaleWindows M stepOneSEighth delta stepOneSEighth_pos n m omega)
    {w : Fin d → ℤ} (hw : w ∈ Support.latticeCubeSet d (n - 1) m) :
    ∑ k ∈ Finset.Icc n m,
        stepOneEpsJ M k (Support.triadicLatticePoint (n - 1) w) delta omega ≤
      ENNReal.ofReal delta * (((m - n).toNat : ℝ≥0∞) + 1) := by
  have hraw :=
    le_trans (le_iSup _ (⟨w, hw⟩ : ↥(Support.latticeCubeSet d (n - 1) m))) hgood.1
  have hsup : (((m - n).toNat : ℝ≥0∞) + 1)⁻¹ *
      ∑ k ∈ Finset.Icc n m,
        stepOneEpsJ M k (Support.triadicLatticePoint (n - 1) w) delta omega ≤
      ENNReal.ofReal delta := hraw
  have hne0 : (((m - n).toNat : ℝ≥0∞) + 1) ≠ 0 := by positivity
  have hnetop : (((m - n).toNat : ℝ≥0∞) + 1) ≠ ⊤ := by simp
  calc ∑ k ∈ Finset.Icc n m,
        stepOneEpsJ M k (Support.triadicLatticePoint (n - 1) w) delta omega
      = ((((m - n).toNat : ℝ≥0∞) + 1) * (((m - n).toNat : ℝ≥0∞) + 1)⁻¹) *
          ∑ k ∈ Finset.Icc n m,
            stepOneEpsJ M k (Support.triadicLatticePoint (n - 1) w) delta omega := by
        rw [ENNReal.mul_inv_cancel hne0 hnetop, one_mul]
    _ = (((m - n).toNat : ℝ≥0∞) + 1) *
          ((((m - n).toNat : ℝ≥0∞) + 1)⁻¹ *
            ∑ k ∈ Finset.Icc n m,
              stepOneEpsJ M k (Support.triadicLatticePoint (n - 1) w) delta omega) := by
        rw [mul_assoc]
    _ ≤ (((m - n).toNat : ℝ≥0∞) + 1) * ENNReal.ofReal delta := by gcongr
    _ = ENNReal.ofReal delta * (((m - n).toNat : ℝ≥0∞) + 1) := mul_comm _ _

/-- The same at the printed lattice `3^n ℤ^d ∩ □_m`, and in `ℝ`. -/
theorem sum_stepFiveEps_le_of_goodScaleWindows_fine {M : ABKModel d} {delta : ℝ}
    {n m : ℤ} {omega : Cutoff.CutoffSample d} (hdelta : 0 ≤ delta)
    (hgood : GoodScaleWindows M stepOneSEighth delta stepOneSEighth_pos n m omega)
    {w : Fin d → ℤ} (hw : w ∈ Support.latticeCubeSet d (n - 1) m) :
    ∑ k ∈ Finset.Icc n m,
        stepFiveEps M k (Support.triadicLatticePoint (n - 1) w) delta omega ≤
      delta * (((m - n).toNat : ℝ) + 1) := by
  have hE := sum_stepOneEpsJ_le_of_goodScaleWindows_fine hgood hw
  have hrhs : ENNReal.ofReal delta * (((m - n).toNat : ℝ≥0∞) + 1)
      = ENNReal.ofReal (delta * (((m - n).toNat : ℝ) + 1)) := by
    rw [ENNReal.ofReal_mul hdelta,
      ENNReal.ofReal_add (by positivity) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  rw [hrhs] at hE
  have hne : ∀ k ∈ Finset.Icc n m,
      stepOneEpsJ M k (Support.triadicLatticePoint (n - 1) w) delta omega ≠ ⊤ := by
    intro k hk
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans ?_ hE)
    exact Finset.single_le_sum (f := fun k =>
      stepOneEpsJ M k (Support.triadicLatticePoint (n - 1) w) delta omega)
      (fun i _ => zero_le) hk
  have hrnn : 0 ≤ delta * (((m - n).toNat : ℝ) + 1) :=
    mul_nonneg hdelta (by positivity)
  calc ∑ k ∈ Finset.Icc n m,
        stepFiveEps M k (Support.triadicLatticePoint (n - 1) w) delta omega
      = (∑ k ∈ Finset.Icc n m,
          stepOneEpsJ M k (Support.triadicLatticePoint (n - 1) w) delta omega).toReal :=
        (ENNReal.toReal_sum hne).symm
    _ ≤ (ENNReal.ofReal (delta * (((m - n).toNat : ℝ) + 1))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hE
    _ = delta * (((m - n).toNat : ℝ) + 1) := ENNReal.toReal_ofReal hrnn

/-- **`e.sum.eps.j.bound`, at the printed centres** `z ∈ 3^n ℤ^d ∩ □_m`:

```text
   ∑_{k=n}^{m} ε_k(z)  ≤  δ ((m-n) + 1) .
```

Note the window is the anchor's `Icc n m` (deviation D1) and the length is
`(m-n)+1` (deviation D2). -/
theorem sum_stepFiveEps_le_of_goodScaleWindows {M : ABKModel d} {delta : ℝ}
    {n m : ℤ} {omega : Cutoff.CutoffSample d} (hdelta : 0 ≤ delta)
    (hgood : GoodScaleWindows M stepOneSEighth delta stepOneSEighth_pos n m omega)
    {v : Fin d → ℤ} (hv : v ∈ Support.latticeCubeSet d n m) :
    ∑ k ∈ Finset.Icc n m,
        stepFiveEps M k (Support.triadicLatticePoint n v) delta omega ≤
      delta * (((m - n).toNat : ℝ) + 1) := by
  have h := sum_stepFiveEps_le_of_goodScaleWindows_fine hdelta hgood
    (mem_latticeCubeSet_shift hv)
  rwa [triadicLatticePoint_shift] at h

/-- `(m-n).toNat + 1 ≤ 2 (m-n)` at the Step-3 window gate `14 ≤ m-n` — the
arithmetic that turns deviation D2's `δ((m-n)+1)` into the printed `C δ (m-n)`
at `C = 2`. -/
theorem toNat_window_add_one_le_two_mul {n m : ℤ} (hwin : (14 : ℤ) ≤ m - n) :
    (((m - n).toNat : ℝ) + 1) ≤ 2 * ((m : ℝ) - (n : ℝ)) := by
  have hz : ((m - n).toNat : ℤ) = m - n := Int.toNat_of_nonneg (by omega)
  have hr : (((m - n).toNat : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
    have hc := congrArg (fun t : ℤ => (t : ℝ)) hz
    push_cast at hc
    linarith only [hc]
  have hw : (14 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have := congrArg (fun t : ℤ => (t : ℝ)) (le_antisymm (le_refl (m - n)) (le_refl (m - n)))
    have hcast : ((14 : ℤ) : ℝ) ≤ ((m - n : ℤ) : ℝ) := Int.cast_le.mpr hwin
    push_cast at hcast
    linarith only [hcast]
  rw [hr]
  linarith only [hw]

/-- **`e.sum.eps.j.bound` in the printed shape**:

```text
   ∑_{k=n}^{m} ε_k(z)  ≤  2 δ (m-n) .
```

The explicit `C = 2` is deviation D2; the window is the anchor's (D1), which
dominates the printed `[n, m-1]`. -/
theorem sum_stepFiveEps_le_two_mul_delta_mul_window {M : ABKModel d} {delta : ℝ}
    {n m : ℤ} {omega : Cutoff.CutoffSample d} (hdelta : 0 ≤ delta)
    (hwin : (14 : ℤ) ≤ m - n)
    (hgood : GoodScaleWindows M stepOneSEighth delta stepOneSEighth_pos n m omega)
    {v : Fin d → ℤ} (hv : v ∈ Support.latticeCubeSet d n m) :
    ∑ k ∈ Finset.Icc n m,
        stepFiveEps M k (Support.triadicLatticePoint n v) delta omega ≤
      2 * delta * ((m : ℝ) - (n : ℝ)) := by
  have h1 := sum_stepFiveEps_le_of_goodScaleWindows hdelta hgood hv
  have h2 := mul_le_mul_of_nonneg_left (toNat_window_add_one_le_two_mul hwin) hdelta
  linarith only [h1, h2]

end Algsuperdiff.Section4.Provider.Regularity
