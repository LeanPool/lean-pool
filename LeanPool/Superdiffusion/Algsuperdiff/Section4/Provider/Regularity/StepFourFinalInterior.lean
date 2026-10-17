/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EdFinalInputs
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourCollapseInterface

/-!
# StepFourFinalInterior

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `hstep4`'s body at one scale, on the interior branch

## What this module is

`excessDecay_oneStep_interior_anchored_twoLeg` is the one-step contraction
off the harmonic-approximation anchor's frontier-empty clause: two legs, no
`∇h`, the oscillation on the contraction's own window.
`stepFourDecay_of_edOneStep` is the Step-4 collapse into `hstep4`'s body.  This
module composes them at `x := z`, with the carried items discharged from
`EdFinalInputs`, and produces

```text
   E(u, U_{n-k}) ≤ 3^{-k/4} E(u, U_n) + C_ε ε_n |∇ℓ_n| + δ_n ,
   U_j = stepThreeWindow z m j = (z + □_j) ∩ □_m ,
   δ_n = C_δ 3^{n/2} σ_n^{-1} K_g .
```

`δ_n` is the `g`-leg shape of the Step-5 family, at the
root's own Hölder datum `K_g` in place of the `W^{1/2,∞}` seminorm (which it
dominates).  The ungated, non-decaying flat `∇h` leg
is gone: the interior clause carries no `∇h` leg at all.

## The three conversions, per leg

* the `𝓔`-leg: the oscillation-to-excess fold is
  `oscLeg_normalized_le_interior` — a theorem at this window, not a binder;
* the Gagliardo exponent: `StepFourCollapseInterface.stepFourGsemLeg_le` is
  read at the interior clause's OWN window index `n` and re-pinned to the
  collapse's `n+1` by `Real.rpow_le_rpow_of_exponent_le` — the one-scale re-pin
  is free because `1/2 - s > 0`.

## References

* ABK26, `l.excess.decay.good.scales`; `l.harmonic.approximation.good.scales`,
  (interior clause); `t.regularity` Step 4.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ## 1. The interior branch's `ε` coefficient and `δ` family -/

/-- The `ε`-slot coefficient the interior collapse produces: `C_rem √((3²)^d) C
s^{-4} C_i(d)` (`stepFourEpsCoeff` at the interior constants). -/
def edFinalEpsCoeff (d : ℕ) [NeZero d] (C : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  stepFourEpsCoeff (triangleRemainderConst d (schauderWindowConst d) k)
    (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d)) C s (endpointConst d (1 / 9 : ℝ))

theorem edFinalEpsCoeff_nonneg (d : ℕ) [NeZero d] {C : ℝ} (hC : 0 ≤ C) (k : ℕ)
    {s : ℝ} (hs : 0 ≤ s) : 0 ≤ edFinalEpsCoeff d C k s := by
  have hCi : (1 : ℝ) ≤ endpointConst d (1 / 9 : ℝ) := one_le_endpointConst (by norm_num)
  rw [edFinalEpsCoeff, stepFourEpsCoeff]
  refine mul_nonneg (mul_nonneg (mul_nonneg
    (triangleRemainderConst_nonneg d (schauderWindowConst_nonneg d) k)
    (Real.sqrt_nonneg _)) (mul_nonneg hC (Real.rpow_nonneg hs _))) ?_
  linarith only [hCi]

/-- The `δ`-slot constant the interior collapse produces: `8 C_rem √((3²)^d) C
s^{-19/2}`. -/
def edFinalDeltaConst (d : ℕ) [NeZero d] (C : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  8 * (triangleRemainderConst d (schauderWindowConst d) k *
    Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * (C * s ^ (-(19 / 2 : ℝ))))

/-- **The interior branch's `δ_n`**: `C_δ 3^{n/2} σ_n^{-1} K_g`, the `g`-leg of
the Step-5 family at the root's own Hölder datum.  There is
no `∇h` leg and no boundary indicator. -/
def edFinalDelta (M : ABKModel d) (Cdel Kg : ℝ) (n : ℤ) : ℝ :=
  Cdel * (3 : ℝ) ^ ((n : ℝ) / 2) * ((Annealed.sigmaBar M n : ℝ))⁻¹ * Kg

theorem edFinalDelta_nonneg {M : ABKModel d} {Cdel Kg : ℝ} (hC : 0 ≤ Cdel)
    (hK : 0 ≤ Kg) (n : ℤ) : 0 ≤ edFinalDelta M Cdel Kg n := by
  have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ ((n : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have h2 : (0 : ℝ) ≤ ((Annealed.sigmaBar M n : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M n).2.le
  exact mul_nonneg (mul_nonneg (mul_nonneg hC h1) h2) hK

/-- The produced `δ` at the interior instantiation (no `∇h` legs) is
`edFinalDelta`.  The identity is `s^{-7} · s^{-5/2} = s^{-19/2}`. -/
theorem stepFourDeltaOut_interior_eq {M : ABKModel d} {C s epsj Kg : ℝ}
    [NeZero d] (hs : 0 < s) (k : ℕ) (n : ℤ) :
    stepFourDeltaOut (triangleRemainderConst d (schauderWindowConst d) k)
        (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d)) C s epsj 0
        (s ^ (-(5 / 2 : ℝ)) * ((Annealed.sigmaBar M n : ℝ))⁻¹) Kg 0 n =
      edFinalDelta M (edFinalDeltaConst d C k s) Kg n := by
  have hpow : s ^ (-(7 : ℝ)) * s ^ (-(5 / 2 : ℝ)) = s ^ (-(19 / 2 : ℝ)) := by
    rw [← Real.rpow_add hs]
    norm_num
  rw [stepFourDeltaOut, edFinalDelta, edFinalDeltaConst, ← hpow]
  ring

/-- **The interior two-leg display IS's `hed` slot** at `Gav = Hsem = Hl2 = 0` and
`SigInv = s^{-5/2} σ_{n-2}^{-1}`: the single `s`-power carries the interior
clause's `-19/2` force exponent into the collapse's `s^{-7}` shom slot.  One
`rpow_add` identity, no inequality. -/
theorem twoLeg_is_hed {s : ℝ} (hs : 0 < s) (C Efl Osc Gsem SigInv2 Crem Vd : ℝ)
    (n : ℤ) :
    Crem * ((3 : ℝ) ^ (-n) * (Vd *
        (C * Real.rpow s (-(4 : ℝ)) * Efl * Osc +
          C * Real.rpow s (-(19 / 2 : ℝ)) * SigInv2 *
            Real.rpow (3 : ℝ) ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Gsem)))
      = Crem * ((3 : ℝ) ^ (-n) * (Vd *
        (C * s ^ (-(4 : ℝ)) * Efl *
              (Osc + s ^ (-(3 / 2 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * 0) +
            C * s ^ (-(7 : ℝ)) * (s ^ (-(5 / 2 : ℝ)) * SigInv2) *
              (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Gsem +
          C * s ^ (-(6 : ℝ)) * (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * 0 +
        C * s ^ (-(6 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * 0))) := by
  have hpow : s ^ (-(7 : ℝ)) * s ^ (-(5 / 2 : ℝ)) = s ^ (-(19 / 2 : ℝ)) := by
    rw [← Real.rpow_add hs]
    norm_num
  change Crem * ((3 : ℝ) ^ (-n) * (Vd *
      (C * s ^ (-(4 : ℝ)) * Efl * Osc +
        C * s ^ (-(19 / 2 : ℝ)) * SigInv2 *
          (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Gsem))) = _
  rw [← hpow]
  ring

/-- **The Step-4 collapse on the interior branch**, over abstract reals: the
two-leg display becomes `hstep4`'s body at the unshifted ratio `θ^k`. -/
theorem stepFourDecay_of_twoLegDisplay [NeZero d] {Exc Slp : ℤ → ℝ} {n : ℤ}
    {k : ℕ} {Crem Vd C s Efl Osc Gsem SigInv2 SigInvN2 epsj Kg thetaK : ℝ}
    (hCV : 0 ≤ Crem * Vd) (hs : 0 < s)
    (hcoef4 : 0 ≤ C * s ^ (-(4 : ℝ))) (hcoef6 : 0 ≤ C * s ^ (-(6 : ℝ)))
    (hcoef7 : 0 ≤ C * s ^ (-(7 : ℝ))) (hw : 0 ≤ s ^ (-(3 / 2 : ℝ)))
    (hExc0 : 0 ≤ Exc n) (hEfl : Efl ≤ epsj) (heps0 : 0 ≤ epsj)
    (hOsc0 : 0 ≤ (3 : ℝ) ^ (-n) * Osc)
    (hOsc : (3 : ℝ) ^ (-n) * Osc ≤ endpointConst d (1 / 9 : ℝ) * (Exc n + Slp n))
    (hSig : s ^ (-(5 / 2 : ℝ)) * SigInv2 ≤ 8 * (s ^ (-(5 / 2 : ℝ)) * SigInvN2))
    (hSigN0 : 0 ≤ s ^ (-(5 / 2 : ℝ)) * SigInvN2)
    (hGsem0 : 0 ≤ Gsem) (hKg0 : 0 ≤ Kg)
    (hGsem : Gsem ≤ Kg * (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s)))
    (hCcon : taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2
        * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) ≤ thetaK / 2)
    (hTC34B : stepFourEpsCoeff Crem Vd C s (endpointConst d (1 / 9 : ℝ)) * epsj
      ≤ thetaK / 2)
    (hed : Exc (n - (k : ℤ)) ≤
      taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2
          * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) * Exc n +
        Crem * ((3 : ℝ) ^ (-n) * (Vd *
          (C * Real.rpow s (-(4 : ℝ)) * Efl * Osc +
            C * Real.rpow s (-(19 / 2 : ℝ)) * SigInv2 *
              Real.rpow (3 : ℝ) ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Gsem)))) :
    Exc (n - (k : ℤ)) ≤ thetaK * Exc n +
      (stepFourEpsCoeff Crem Vd C s (endpointConst d (1 / 9 : ℝ)) * epsj) * Slp n +
      stepFourDeltaOut Crem Vd C s epsj 0 (s ^ (-(5 / 2 : ℝ)) * SigInvN2) Kg 0 n := by
  refine stepFourDecay_of_edOneStep (Exc := Exc) (Slp := Slp) hCV hs.le hcoef4 hcoef6
    hcoef7 hw hExc0 hEfl heps0 hOsc0 hOsc le_rfl (le_refl (0 : ℝ)) hSig hSigN0 hGsem0
    hKg0 hGsem (le_refl (0 : ℝ)) (le_of_eq (zero_mul _).symm) (le_refl (0 : ℝ)) hCcon
    hTC34B ?_
  rw [twoLeg_is_hed hs C Efl Osc Gsem SigInv2 Crem Vd n] at hed
  exact hed

/-! ## 3. The two per-leg re-pins -/

/-- **The one-scale re-pin of the Gagliardo exponent.**'s comparison is read at the
interior clause's OWN window index `n`, and moved to the collapse's `n+1` for
free, because `1/2 - s > 0`. -/
theorem stepFourGsemLeg_shift_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {z : Vec d} {m n : ℤ} {g : Vec d → E} {K s : ℝ}
    (hd : 1 ≤ d) (hz : z ∈ openCubeSet (originCube d m)) (hs0 : 0 < s)
    (hs : s < 1 / 2) (hK : 0 ≤ K)
    (hg : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K g) :
    (Support.normalizedGagliardoESeminormOn (stepThreeWindow z m n) s g).toReal ≤
      (K * stepFourGagliardoConst d s) *
        (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s)) := by
  have hbase := stepFourGsemLeg_le (z := z) (m := m) (j := n) (g := g) (K := K)
    (s := s) hd hz hs0 hs hK hg
  have hexp : ((n : ℝ)) * (1 / 2 - s) ≤ ((n + 1 : ℤ) : ℝ) * (1 / 2 - s) := by
    have hpos : (0 : ℝ) < 1 / 2 - s := by linarith only [hs]
    have hcast : ((n : ℝ)) ≤ ((n + 1 : ℤ) : ℝ) := by push_cast; linarith only []
    exact mul_le_mul_of_nonneg_right hcast hpos.le
  have hmono : (3 : ℝ) ^ (((n : ℝ)) * (1 / 2 - s)) ≤
      (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hKnn : (0 : ℝ) ≤ K * stepFourGagliardoConst d s :=
    mul_nonneg hK (stepFourGagliardoConst_nonneg d s)
  exact hbase.trans (mul_le_mul_of_nonneg_left hmono hKnn)

theorem sigmaBar_shift_weighted {M : ABKModel d} {m0 : ℤ}
    {Ecap : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap)
    (hgamma : M.gamma ≤ 1 / 4) {n : ℤ} (hn : n ≤ m0) {s : ℝ} (hs : 0 < s) :
    s ^ (-(5 / 2 : ℝ)) * ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ ≤
      8 * (s ^ (-(5 / 2 : ℝ)) * ((Annealed.sigmaBar M n : ℝ))⁻¹) := by
  have hbase := inv_sigmaBar_sub_two_le_eight_mul_inv_sigmaBar hS hgamma hn
  have hw : (0 : ℝ) ≤ s ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
  have h := mul_le_mul_of_nonneg_left hbase hw
  linarith only [h]

end

end Algsuperdiff.Section4.Provider.Regularity
