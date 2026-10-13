/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.SecondTermSlots

/-!
# SecondTermMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 5's second summand: its `q`-th moment, by the four-factor Hölder

## What this module does

The second summand of `PerCubeFirstThird.step3SecondTerm` is

```
C σ_m^{-1} σ_{j−2}²  ·  λ_{2γ,2}^{-1}  ·  (1 + ∇k λ^{-1})^{4γ/(1−4γ)}
      ·  ( σ_{j−2}^{-2} ‖h‖² + (σ_m σ_{j−2}^{-1} − 1)² ) ,
```

the one Step 5 handles "with additional inputs".  This module supplies its
`q`-th moment in the development normal form.

The route is a S followed by two Hölder products.  Because `σ_{j−2}²
σ_{j−2}^{-2} = 1`, the summand is

```
  C σ_m^{-1} · ( λ^{-1} · ( bracket · ‖h‖² ) )                       (the value leg)
+ C σ_m^{-1} σ_{j−2}² (σ_m σ_{j−2}^{-1} − 1)² · ( λ^{-1} · bracket ) (the (B2) leg)
```

-- no inequality is spent on the split.  The (B2) leg is a TWO-factor product
with a deterministic scalar in front, so it reads (B5) and the bracket at `2q`
only; its scalar is bullet (B2), which is deterministic and therefore costs no
moment at all.

Every Step-4 bullet is available at every moment `q ∈ [1,∞)` -- that is exactly
what Step 4's "hence, for every `q`" sentences deliver -- so the exponent boost
is free, and NO constant beyond the product of the caller's own majorants
appears.

## References

* ABK26, `l.bounds.mathcal.E.aL`, `e.apply.sensitivity.J.aL`, Step 4 bullets
  (B2)/(B5)/(B6a)/(B6b), Step 5.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section4.Provider.Annular
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The two named majorants -/

/-- The bracket majorant of `PerCubeBracket.exists_lintegral_rpow_step3Bracket_le`
at moment `r`, named: `1 + R_{B6a}(2r) R_{B5}(2r)`. -/
def bracketMajorant (d : ℕ) (M : ABKModel d) (EB : ℝ) (j : ℤ) (r : ℝ) : ℝ :=
  1 + gradSlotMajorant M j (2 * r) * lambdaSlotMajorant d M EB j (2 * r)

theorem bracketMajorant_nonneg (d : ℕ) (M : ABKModel d) (EB : ℝ) (j : ℤ) {r : ℝ}
    (hr : 0 ≤ r) : 0 ≤ bracketMajorant d M EB j r := by
  have hG : (0 : ℝ) ≤ gradSlotMajorant M j (2 * r) := gradSlotMajorant_nonneg M j (2 * r)
  have hL : (0 : ℝ) ≤ lambdaSlotMajorant d M EB j (2 * r) :=
    lambdaSlotMajorant_nonneg d M EB j (by linarith only [hr])
  have h := mul_nonneg hG hL
  rw [bracketMajorant]
  linarith only [h]

/-- **The second summand's majorant at moment `q`**, at the two proved budgets `E`
(the `λ`-slot bullet) and `E_B` (the bracket). -/
def secondTermMajorant (d : ℕ) (M : ABKModel d) (E EB Cd : ℝ) (m j : ℤ) (q : ℝ) : ℝ :=
  Cd * ((Annealed.sigmaBar M m : ℝ))⁻¹ *
      (lambdaSlotMajorant d M E j (2 * q) *
        (bracketMajorant d M EB j (4 * q) * valueSlotMajorant M m j (8 * q) ^ 2)) +
    Cd * (((Annealed.sigmaBar M m : ℝ))⁻¹ * (Annealed.sigmaBar M (j - 2) : ℝ) ^ 2 *
        ((Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M (j - 2) : ℝ))⁻¹ - 1) ^ 2) *
      (lambdaSlotMajorant d M E j (2 * q) * bracketMajorant d M EB j (2 * q))

/-! ## 2. The abstract four-factor Hölder core -/

/-- **The four-factor Hölder at the second summand's shape, over an abstract
measure space.**

`smi` stands for `σ_m^{-1}`, `sA` for `σ_{j−2}` and `sAi` for its inverse (the
only fact used about the pair is `sA² sAi² = 1`); `Delta` is the deterministic
(B2) scalar.  The three random slots enter at the exponents the Hölder doubling
produces: `λ^{-1}` at `2q`, the bracket at `4q` (value leg) and at `2q` ((B2)
leg), the value slot at `8q`. -/
private theorem secondTermMomentCore {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {lam br val : Omega → ℝ}
    {Cd smi sA sAi Delta RL RB4 RB2 RV q : ℝ}
    (hq : 1 ≤ q) (hCd : 0 ≤ Cd) (hsmi : 0 ≤ smi) (hsAi : sA ^ 2 * sAi ^ 2 = 1)
    (hlam0 : ∀ w, 0 ≤ lam w) (hbr0 : ∀ w, 0 ≤ br w) (hval0 : ∀ w, 0 ≤ val w)
    (hlamm : AEMeasurable lam mu) (hbrm : AEMeasurable br mu) (hvalm : AEMeasurable val mu)
    (hRL : 0 ≤ RL) (hRB4 : 0 ≤ RB4) (hRB2 : 0 ≤ RB2) (hRV : 0 ≤ RV)
    (hlamMom : (∫⁻ w, ENNReal.ofReal (lam w) ^ (2 * q) ∂mu) ≤ ENNReal.ofReal RL ^ (2 * q))
    (hbrMom4 : (∫⁻ w, ENNReal.ofReal (br w) ^ (4 * q) ∂mu) ≤ ENNReal.ofReal RB4 ^ (4 * q))
    (hbrMom2 : (∫⁻ w, ENNReal.ofReal (br w) ^ (2 * q) ∂mu) ≤ ENNReal.ofReal RB2 ^ (2 * q))
    (hvalMom : (∫⁻ w, ENNReal.ofReal (val w) ^ (8 * q) ∂mu) ≤ ENNReal.ofReal RV ^ (8 * q)) :
    (∫⁻ w, ENNReal.ofReal (Cd * (smi * sA ^ 2) * lam w * br w *
        (sAi ^ 2 * val w ^ 2 + Delta ^ 2)) ^ q ∂mu) ≤
      ENNReal.ofReal (Cd * smi * (RL * (RB4 * RV ^ 2)) +
        Cd * (smi * sA ^ 2 * Delta ^ 2) * (RL * RB2)) ^ q := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have h2q0 : (0 : ℝ) < 2 * q := by linarith only [hq0]
  have hbnnA : (0 : ℝ) ≤ Cd * smi := mul_nonneg hCd hsmi
  have hbnnB : (0 : ℝ) ≤ Cd * (smi * sA ^ 2 * Delta ^ 2) :=
    mul_nonneg hCd (mul_nonneg (mul_nonneg hsmi (sq_nonneg _)) (sq_nonneg _))
  -- the squared value slot, at `4q`
  have hvalsq : (∫⁻ w, ENNReal.ofReal (val w ^ 2) ^ (4 * q) ∂mu) ≤
      ENNReal.ofReal (RV ^ 2) ^ (4 * q) := by
    refine lintegral_rpow_sq_le_of_moments (mu := mu) (X := val) (r := 4 * q)
      (Filter.Eventually.of_forall hval0) hRV ?_
    rw [show (2 : ℝ) * (4 * q) = 8 * q from by ring]
    exact hvalMom
  -- (b) the bracket times the squared value slot, at `2q`
  have hBmom : (∫⁻ w, ENNReal.ofReal (br w * val w ^ 2) ^ (2 * q) ∂mu) ≤
      ENNReal.ofReal (RB4 * RV ^ 2) ^ (2 * q) := by
    have h := lintegral_rpow_const_mul_mul_le_of_moments (mu := mu)
      (F := fun w => br w * val w ^ 2) (A := br) (B := fun w => val w ^ 2)
      (b := 1) (RA := RB4) (RB := RV ^ 2) h2q0 zero_le_one
      (Filter.Eventually.of_forall hbr0) hbrm (hvalm.pow_const 2) hRB4
      (Filter.Eventually.of_forall fun w => by rw [one_mul])
      (by rw [show (2 : ℝ) * (2 * q) = 4 * q from by ring]; exact hbrMom4)
      (by rw [show (2 : ℝ) * (2 * q) = 4 * q from by ring]; exact hvalsq)
    rwa [one_mul] at h
  -- (c) the value leg, at `q`
  have hlegA : (∫⁻ w, ENNReal.ofReal (Cd * smi * (lam w * (br w * val w ^ 2))) ^ q ∂mu) ≤
      ENNReal.ofReal (Cd * smi * (RL * (RB4 * RV ^ 2))) ^ q :=
    lintegral_rpow_const_mul_mul_le_of_moments (mu := mu)
      (F := fun w => Cd * smi * (lam w * (br w * val w ^ 2))) (A := lam)
      (B := fun w => br w * val w ^ 2) (b := Cd * smi) hq0 hbnnA
      (Filter.Eventually.of_forall hlam0) hlamm (hbrm.mul (hvalm.pow_const 2)) hRL
      (Filter.Eventually.of_forall fun _ => le_rfl) hlamMom hBmom
  -- (d) the (B2) leg, at `q`
  have hlegB : (∫⁻ w, ENNReal.ofReal (Cd * (smi * sA ^ 2 * Delta ^ 2) *
      (lam w * br w)) ^ q ∂mu) ≤
      ENNReal.ofReal (Cd * (smi * sA ^ 2 * Delta ^ 2) * (RL * RB2)) ^ q :=
    lintegral_rpow_const_mul_mul_le_of_moments (mu := mu)
      (F := fun w => Cd * (smi * sA ^ 2 * Delta ^ 2) * (lam w * br w)) (A := lam) (B := br)
      (b := Cd * (smi * sA ^ 2 * Delta ^ 2)) hq0 hbnnB
      (Filter.Eventually.of_forall hlam0) hlamm hbrm hRL
      (Filter.Eventually.of_forall fun _ => le_rfl) hlamMom hbrMom2
  -- (e) the split (an identity) and the two-term Minkowski
  have hsplit : ∀ w : Omega, Cd * (smi * sA ^ 2) * lam w * br w *
      (sAi ^ 2 * val w ^ 2 + Delta ^ 2) =
      Cd * smi * (lam w * (br w * val w ^ 2)) +
        Cd * (smi * sA ^ 2 * Delta ^ 2) * (lam w * br w) := by
    intro w
    have hid : Cd * (smi * sA ^ 2) * lam w * br w * (sAi ^ 2 * val w ^ 2 + Delta ^ 2) =
        Cd * smi * (sA ^ 2 * sAi ^ 2) * (lam w * (br w * val w ^ 2)) +
          Cd * (smi * sA ^ 2 * Delta ^ 2) * (lam w * br w) := by ring
    rw [hid, hsAi, mul_one]
  have hcong : (∫⁻ w, ENNReal.ofReal (Cd * (smi * sA ^ 2) * lam w * br w *
        (sAi ^ 2 * val w ^ 2 + Delta ^ 2)) ^ q ∂mu) =
      ∫⁻ w, ENNReal.ofReal (Cd * smi * (lam w * (br w * val w ^ 2)) +
        Cd * (smi * sA ^ 2 * Delta ^ 2) * (lam w * br w)) ^ q ∂mu :=
    lintegral_congr fun w => by rw [hsplit w]
  rw [hcong]
  refine lintegral_rpow_real_add_le_of_moments hq
    ((hlamm.mul (hbrm.mul (hvalm.pow_const 2))).const_mul _)
    ((hlamm.mul hbrm).const_mul _) ?_ ?_ hlegA hlegB
  · exact mul_nonneg hbnnA (mul_nonneg hRL (mul_nonneg hRB4 (sq_nonneg _)))
  · exact mul_nonneg hbnnB (mul_nonneg hRL hRB2)

/-! ## 3. The second summand's moment at the Step-3 slots -/

/-- **The second summand's `q`-th moment.**

```
∫⁻ ( step3SecondTerm )^q ≤ ( ofReal ( secondTermMajorant ) )^q ,
```

the four-factor Hölder of the module docstring at the proved Step-4 bullets.
Both budgets are of the printed shape `C c⋆^{-1}`; the standing regime is taken
at the maximum of the two proved constants. -/
theorem exists_lintegral_rpow_step3SecondTerm_le (d : ℕ) : ∃ CL CB : ℝ, 6 ≤ CL ∧ 6 ≤ CB ∧
      ∀ M : ABKModel d,
        M.gamma ≤ ((max CL CB)⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        M.gamma ≤ 1 / 8 → ∀ Cd : ℝ, 0 ≤ Cd →
          ∀ (m : ℤ) (R : TriadicCube d), R.scale ≤ m → ∀ q : ℝ, 1 ≤ q →
            (∫⁻ omega : Cutoff.CutoffSample d,
                ENNReal.ofReal (step3SecondTerm Cd M m R omega
                  (lFreeGradSlot m (tailSeriesGauge m) R omega)
                  (lFreeValueSlot m (tailSeriesGauge m) R omega)) ^ q
                ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
              ENNReal.ofReal (secondTermMajorant d M (CL * (Disorder.cstar M)⁻¹)
                (CB * (Disorder.cstar M)⁻¹) Cd m R.scale q) ^ q  := by
  obtain ⟨CL, hCL6, hlamAll⟩ := exists_lintegral_rpow_inv_unitCubeLambda_twoGamma_le d
  obtain ⟨CB, hCB6, hbrAll⟩ := exists_lintegral_rpow_step3Bracket_le d
  refine ⟨CL, CB, hCL6, hCB6, ?_⟩
  intro M hreg hgam Cd hCd m R hkm q hq
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hCL0 : (0 : ℝ) < CL := by linarith only [hCL6]
  have hCB0 : (0 : ℝ) < CB := by linarith only [hCB6]
  have hregL := gamma_regime_mono hCL0 (le_max_left CL CB) hcs0.le hreg
  have hregB := gamma_regime_mono hCB0 (le_max_right CL CB) hcs0.le hreg
  obtain ⟨E, hEval, hlam⟩ := hlamAll M hregL
  rw [hEval] at hlam
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have h2q : (1 : ℝ) ≤ 2 * q := by linarith only [hq]
  have h4q : (1 : ℝ) ≤ 4 * q := by linarith only [hq]
  have h8q : (1 : ℝ) ≤ 8 * q := by linarith only [hq]
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hden : (0 : ℝ) < 1 - 4 * M.gamma := by linarith only [hgam]
  have hth0 : (0 : ℝ) ≤ 4 * M.gamma / (1 - 4 * M.gamma) :=
    div_nonneg (by linarith only [hgam0]) hden.le
  have hth1 : 4 * M.gamma / (1 - 4 * M.gamma) ≤ 1 := step3_gamma_exponent_le_one hgam
  have hsA0 : (0 : ℝ) < (Annealed.sigmaBar M (R.scale - 2) : ℝ) :=
    (Annealed.sigmaBar M (R.scale - 2)).2
  have hsmi : (0 : ℝ) ≤ ((Annealed.sigmaBar M m : ℝ))⁻¹ :=
    (inv_pos.mpr (Annealed.sigmaBar M m).2).le
  have hsAi : (Annealed.sigmaBar M (R.scale - 2) : ℝ) ^ 2 *
      ((Annealed.sigmaBar M (R.scale - 2) : ℝ))⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hsA0), one_pow]
  obtain ⟨hlamm, hgradm, hvalm⟩ := slotMeasurableTriple M m R
  exact secondTermMomentCore (mu := (Cutoff.cutoffSampleLaw M).toMeasure) hq hCd hsmi hsAi
    (fun omega => inv_unitCubeLambda_twoGamma_nonneg M R omega)
    (fun omega => Real.rpow_nonneg (by
      have h := mul_nonneg (lFreeGradSlot_tailSeriesGauge_nonneg m R omega)
        (inv_unitCubeLambda_twoGamma_nonneg M R omega)
      linarith only [h]) _)
    (fun omega => lFreeValueSlot_tailSeriesGauge_nonneg m R omega)
    hlamm (aemeasurable_step3Bracket M m R hth0) hvalm
    (lambdaSlotMajorant_nonneg d M (CL * (Disorder.cstar M)⁻¹) R.scale
      (by linarith only [h2q]))
    (bracketMajorant_nonneg d M (CB * (Disorder.cstar M)⁻¹) R.scale
      (by linarith only [h4q]))
    (bracketMajorant_nonneg d M (CB * (Disorder.cstar M)⁻¹) R.scale
      (by linarith only [h2q]))
    (valueSlotMajorant_nonneg M m R.scale (8 * q))
    (hlam R (2 * q) h2q)
    (hbrAll M hregB m R hkm (4 * q) h4q _ hth1)
    (hbrAll M hregB m R hkm (2 * q) h2q _ hth1)
    (lintegral_rpow_lFreeValueSlot_le M R hkm h8q)

end

end Algsuperdiff.Section4.Provider.BoundsEaL
