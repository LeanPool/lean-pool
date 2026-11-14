/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepFourIdentity

/-!
# HomStepFourEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 4: the introduction's energy display

## The assembly

```text
  |⨍ ν|∇u|² - ⨍ σ_m|∇v|²|
      = |⨍ (a_L∇u - σ_m∇v)·∇v  +  σ_m ⨍ (∇u-∇v)·∇v|            (§3)
      ≤ (W_flux + σ_m W_grad) · ‖∇v‖_{W^{s,∞}}                   (§4)
      ≤ (3^{ms}σ_m C E D + σ_m 3^{ms} C E D) · C_sch 3^{-ms} D
      = 2 C C_sch E · σ_m D²  =  2 C C_sch E · bracket²,          (§5)
```

the last step being the EXACT identity `σ D² = bracket²`
(`sigma_mul_sq_dataBracket`), where `D` is the un-square-rooted data bracket of
the introduction's homogenization estimate and `bracket` the square-rooted one
of the introduction's energy display.  No inequality is spent there: the two
printed brackets differ by exactly one factor `√σ_m`.

## The three inputs, and which of them is a hypothesis

* the **flux** weak bound and the **gradient** weak bound.  The
  manuscript's own justification reads BOTH
  off ONE application of the general coarse-graining proposition, whose printed conclusion carries
  the two halves in a single sum on the left.  They
  are therefore ONE transcribed source hypothesis, not two, and they arrive at
  the duality carrier of `HomStepFourPairing`.
* the **Schauder** bound on `‖∇v‖_{W^{s,∞}(□_m)}`.  This is
  The manuscript's Schauder step: "By Schauder estimates for the Poisson equation in a cube
  (by odd reflection)" is asserted with no citation and no labelled in-paper
  result, and bullet 2 records it as deferred to reflection
  folklore.  Nothing in the manuscript, in this repository, or in `CoarseGraining` proves it
  (surveyed: the `Provider/ExcessDecay/OneStepSchauder*` chain is the
  ZERO-forcing interior/odd-reflection estimate for the harmonic competitor on
  the §4.3 replacement window; there is no `-σΔv = ∇·g` gradient-Hölder
  estimate anywhere, and an earlier rebuild carried the same bound as an
  ASSUMED field).  It therefore enters here as a NAMED TRANSCRIBED hypothesis
  `hSch`, in exactly the printed shape, and is disclosed as a THIRD conditional
  of clause (C4) beyond `{hC, hCG}`.
-/

open HCPolySupport MeasureTheory

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. Linearity of the volume average -/

private theorem volumeAverage_sub_of_integrableOn {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IntegrableOn f U volume) (hg : IntegrableOn g U volume) :
    volumeAverage U (fun x => f x - g x) = volumeAverage U f - volumeAverage U g := by
  unfold volumeAverage
  rw [MeasureTheory.integral_sub hf hg]
  ring

private theorem volumeAverage_congr {U : Set (Vec d)} {f g : Vec d → ℝ}
    (h : ∀ x, f x = g x) : volumeAverage U f = volumeAverage U g := by
  congr 1
  funext x
  exact h x

private theorem volumeAverage_of_integral_eq_const_mul {U : Set (Vec d)}
    {f g : Vec d → ℝ} {c : ℝ}
    (h : (∫ x in U, f x ∂volume) = c * ∫ x in U, g x ∂volume) :
    volumeAverage U f = c * volumeAverage U g := by
  unfold volumeAverage
  rw [h]
  ring

/-! ## 2. The `ν`-drop at the volume average -/

/-- **`⨍ ν|∇u|² = ⨍ ∇u·a∇u`** (a correction to the printed statement), pointwise and hence at
the average.  `ν` is not divided by anything and no ellipticity is used. -/
theorem volumeAverage_nu_vecNormSq_eq {A : CoeffField d} {U : Set (Vec d)} {nu : ℝ}
    (u : H1Function U) {F : Vec d → Vec d} (hF : ∀ x, F x = matVecMul (A x) (u.grad x))
    (hsym : ∀ x, symmPart (A x) = nu • (1 : Mat d)) :
    volumeAverage U (fun y => nu * vecNormSq (u.grad y)) =
      volumeAverage U fun x => vecDot (u.grad x) (F x) :=
  volumeAverage_congr fun x => by
    rw [hF x]
    exact (vecDot_matVecMul_self_of_symmPart_smul_one (hsym x) (u.grad x)).symm

/-- The comparator's energy density at the scalar field `σ Id`. -/
theorem volumeAverage_sigma_vecNormSq_eq {U : Set (Vec d)} (sigma : ℝ)
    (v : H1Function U) :
    volumeAverage U (fun y => sigma * vecNormSq (v.grad y)) =
      volumeAverage U fun x => vecDot (v.grad x) (sigma • v.grad x) :=
  volumeAverage_congr fun x => by
    rw [vecDot_smul_right]
    rfl

/-! ## 3. The energy split -/

/-- **The Step-4 energy split.**

The pointwise identity of `HomStepFourIdentity` averaged, with the testing
identity substituted into the second summand:

```text
  ⨍ ν|∇u|² - ⨍ σ|∇v|²
      = ⨍ (a_L∇u - σ∇v)·∇v  +  σ ⨍ (∇u - ∇v)·∇v.
```

Both summands are `cubePairing`s against the SAME test field `∇v`, which is
what the two duality bounds consume.  The three integrability hypotheses are
the manuscript's own `u, v ∈ H¹(□_m)` in force; they are stated rather than
smuggled. -/
theorem energy_split {A : CoeffField d} {Qc : TriadicCube d} {sigma nu : ℝ}
    {u v h : H1Function (openCubeSet Qc)} {g F : Vec d → Vec d}
    (hF : ∀ x, F x = matVecMul (A x) (u.grad x))
    (hsym : ∀ x, symmPart (A x) = nu • (1 : Mat d))
    (hu : IsDivFormWeakSolutionOn A (openCubeSet Qc) u g)
    (hv : IsDivFormWeakSolutionOn (fun _ => sigma • (1 : Mat d)) (openCubeSet Qc) v g)
    (hbu : HasZeroTraceDifferenceOn (openCubeSet Qc) u h)
    (hbv : HasZeroTraceDifferenceOn (openCubeSet Qc) v h)
    (hiU : IntegrableOn (fun x => vecDot (u.grad x) (F x)) (openCubeSet Qc) volume)
    (hiV : IntegrableOn (fun x => vecDot (v.grad x) (sigma • v.grad x))
      (openCubeSet Qc) volume)
    (hiC : IntegrableOn (fun x => vecDot (F x) (v.grad x)) (openCubeSet Qc) volume) :
    volumeAverage (openCubeSet Qc) (fun y => nu * vecNormSq (u.grad y)) -
        volumeAverage (openCubeSet Qc) (fun y => sigma * vecNormSq (v.grad y)) =
      cubePairing Qc (fun x => F x - sigma • v.grad x) v.grad +
        sigma * cubePairing Qc (fun x => u.grad x - v.grad x) v.grad := by
  have hP := volumeAverage_nu_vecNormSq_eq (A := A) (nu := nu) u hF hsym
  have hR := volumeAverage_sigma_vecNormSq_eq (U := openCubeSet Qc) sigma v
  /- the flux-difference pairi -/
  have h1 : cubePairing Qc (fun x => F x - sigma • v.grad x) v.grad =
      volumeAverage (openCubeSet Qc) (fun x => vecDot (F x) (v.grad x)) -
        volumeAverage (openCubeSet Qc) (fun x => vecDot (v.grad x) (sigma • v.grad x)) := by
    rw [cubePairing_def, ← volumeAverage_sub_of_integrableOn hiC hiV]
    refine volumeAverage_congr fun x => ?_
    rw [vecDot_sub_left, vecDot_smul_left, vecDot_smul_right]
  /- the cross term, rewritten by the testing identi -/
  have hTint : (∫ x in openCubeSet Qc, vecDot (F x) (u.grad x - v.grad x) ∂volume) =
      sigma * ∫ x in openCubeSet Qc, vecDot (v.grad x) (u.grad x - v.grad x) ∂volume := by
    have hT := testing_identity_gradDiff (h := h) hu hv hbu hbv
    rw [← hT]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hF]
  have h2a : volumeAverage (openCubeSet Qc) (fun x => vecDot (F x) (u.grad x - v.grad x)) =
      sigma * volumeAverage (openCubeSet Qc)
        (fun x => vecDot (v.grad x) (u.grad x - v.grad x)) :=
    volumeAverage_of_integral_eq_const_mul hTint
  have h2b : volumeAverage (openCubeSet Qc)
      (fun x => vecDot (v.grad x) (u.grad x - v.grad x)) =
      cubePairing Qc (fun x => u.grad x - v.grad x) v.grad := by
    rw [cubePairing_def]
    exact volumeAverage_congr fun x => vecDot_comm _ _
  have h2c : volumeAverage (openCubeSet Qc) (fun x => vecDot (F x) (u.grad x - v.grad x)) =
      volumeAverage (openCubeSet Qc) (fun x => vecDot (u.grad x) (F x)) -
        volumeAverage (openCubeSet Qc) (fun x => vecDot (F x) (v.grad x)) := by
    rw [← volumeAverage_sub_of_integrableOn hiU hiC]
    refine volumeAverage_congr fun x => ?_
    rw [vecDot_sub_right, vecDot_comm (F x) (u.grad x)]
  rw [hP, hR, h1, ← h2b, ← h2a, h2c]
  ring

/-! ## 4. The duality step -/

/-- **The two pairings, applied.**  From the split and the two duality levels,
the energy difference is bounded by `(W_flux + σ W_grad)` times the test gauge
of `∇v`. -/
theorem abs_energy_le_of_weakNegDual {Qc : TriadicCube d} {s sigma Wf Wg Ksup KHol : ℝ}
    {Fflux Fgrad gradv : Vec d → Vec d} {E : ℝ}
    (hsplit : E = cubePairing Qc Fflux gradv + sigma * cubePairing Qc Fgrad gradv)
    (hsigma : 0 ≤ sigma) (hsup : 0 ≤ Ksup) (hhol : 0 ≤ KHol)
    (hb : ∀ x ∈ openCubeSet Qc, ‖gradv x‖ ≤ Ksup)
    (hH : HolderSeminormBoundOn (openCubeSet Qc) s KHol gradv)
    (hWf : WeakNegDualBoundOn Qc s Wf Fflux)
    (hWg : WeakNegDualBoundOn Qc s Wg Fgrad) :
    |E| ≤ (Wf + sigma * Wg) * wsInftyGauge Qc s Ksup KHol := by
  have h1 := hWf.pairing hsup hhol hb hH
  have h2 := hWg.pairing hsup hhol hb hH
  have h2' : |sigma * cubePairing Qc Fgrad gradv| ≤
      sigma * Wg * wsInftyGauge Qc s Ksup KHol := by
    rw [abs_mul, abs_of_nonneg hsigma, mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 hsigma
  calc |E| = |cubePairing Qc Fflux gradv + sigma * cubePairing Qc Fgrad gradv| := by
        rw [hsplit]
    _ ≤ |cubePairing Qc Fflux gradv| + |sigma * cubePairing Qc Fgrad gradv| :=
        abs_add_le _ _
    _ ≤ Wf * wsInftyGauge Qc s Ksup KHol + sigma * Wg * wsInftyGauge Qc s Ksup KHol :=
        add_le_add h1 h2'
    _ = (Wf + sigma * Wg) * wsInftyGauge Qc s Ksup KHol := by ring

/-! ## 5. The bracket arithmetic `σ D² = bracket²` -/

/-- The un-square-rooted data bracket of the introduction's homogenization estimate. -/
def dataBracket (sigma pow Kg KhInf Kh : ℝ) : ℝ :=
  sigma⁻¹ * pow * Kg + (KhInf + pow * Kh)

/-- The square-rooted data bracket of the introduction's energy display. -/
def energyBracket (sigma pow Kg KhInf Kh : ℝ) : ℝ :=
  Real.sqrt sigma⁻¹ * pow * Kg + Real.sqrt sigma * (KhInf + pow * Kh)

/-- **The exact relation between the two printed brackets**: `√σ · D = bracket`.

No inequality is spent: the introduction's energy display bracket is the
the introduction's homogenization estimate bracket multiplied by `√σ_m`. -/
theorem sqrt_mul_dataBracket (sigma pow Kg KhInf Kh : ℝ) (hsig : 0 < sigma) :
    Real.sqrt sigma * dataBracket sigma pow Kg KhInf Kh =
      energyBracket sigma pow Kg KhInf Kh := by
  have hsq : Real.sqrt sigma * Real.sqrt sigma = sigma := Real.mul_self_sqrt (le_of_lt hsig)
  have hinv : (Real.sqrt sigma)⁻¹ = Real.sqrt sigma * sigma⁻¹ :=
    inv_eq_of_mul_eq_one_right (by
      calc Real.sqrt sigma * (Real.sqrt sigma * sigma⁻¹)
          = Real.sqrt sigma * Real.sqrt sigma * sigma⁻¹ := by ring
        _ = sigma * sigma⁻¹ := by rw [hsq]
        _ = 1 := mul_inv_cancel₀ (ne_of_gt hsig))
  have hsqrt : Real.sqrt sigma * sigma⁻¹ = Real.sqrt sigma⁻¹ := by
    rw [Real.sqrt_inv, hinv]
  rw [dataBracket, energyBracket, ← hsqrt]
  ring

/-- `σ D² = bracket²`, the form the assembly consumes. -/
theorem sigma_mul_sq_dataBracket (sigma pow Kg KhInf Kh : ℝ) (hsig : 0 < sigma) :
    sigma * dataBracket sigma pow Kg KhInf Kh ^ (2 : ℕ) =
      energyBracket sigma pow Kg KhInf Kh ^ (2 : ℕ) := by
  rw [← sqrt_mul_dataBracket sigma pow Kg KhInf Kh hsig, mul_pow,
    Real.sq_sqrt (le_of_lt hsig)]

/-! ## 6. The §4.5 display -/

/-- **the introduction's energy display from the three §4.5 inputs.**

The weak flux bound at level `3^{ms} σ (C E D)`, the weak gradient bound at
level `3^{ms} (C E D)` — the two halves of the ONE coarse-graining application
— and the Schauder gauge `C_sch 3^{-ms} D` (the Schauder gap) compose to

```text
  |⨍ ν|∇u|² - ⨍ σ|∇v|²| ≤ 2 C C_sch E · σ D²  =  2 C C_sch E · bracket².
```

Every constant is explicit; nothing is absorbed silently.  The residual `2 C
C_sch` is exactly what's witness rescaling (`ethmB_const_smul_moment`)
transports through the moment bound. -/
theorem stepFourEnergyDisplay {Qc : TriadicCube d} {s sigma pow Kg KhInf Kh : ℝ}
    {Cw Csch EB Ksup KHol : ℝ} {Fflux Fgrad gradv : Vec d → Vec d} {E : ℝ}
    (hsig : 0 < sigma) (hCw : 0 ≤ Cw) (hEB : 0 ≤ EB)
    (hD : 0 ≤ dataBracket sigma pow Kg KhInf Kh)
    (hsup : 0 ≤ Ksup) (hhol : 0 ≤ KHol)
    (hsplit : E = cubePairing Qc Fflux gradv + sigma * cubePairing Qc Fgrad gradv)
    (hb : ∀ x ∈ openCubeSet Qc, ‖gradv x‖ ≤ Ksup)
    (hH : HolderSeminormBoundOn (openCubeSet Qc) s KHol gradv)
    (hSch : wsInftyGauge Qc s Ksup KHol ≤
      Csch * (Real.rpow 3 (s * ((Qc.scale : ℤ) : ℝ)))⁻¹ *
        dataBracket sigma pow Kg KhInf Kh)
    (hWf : WeakNegDualBoundOn Qc s (Real.rpow 3 (s * ((Qc.scale : ℤ) : ℝ)) * sigma *
      (Cw * EB * dataBracket sigma pow Kg KhInf Kh)) Fflux)
    (hWg : WeakNegDualBoundOn Qc s (Real.rpow 3 (s * ((Qc.scale : ℤ) : ℝ)) *
      (Cw * EB * dataBracket sigma pow Kg KhInf Kh)) Fgrad) :
    |E| ≤ 2 * Cw * Csch * EB * energyBracket sigma pow Kg KhInf Kh ^ (2 : ℕ) := by
  have hwpos : 0 < Real.rpow 3 (s * ((Qc.scale : ℤ) : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  set w : ℝ := Real.rpow 3 (s * ((Qc.scale : ℤ) : ℝ)) with hwdef
  set D : ℝ := dataBracket sigma pow Kg KhInf Kh with hDdef
  clear_value w
  have hCED : (0 : ℝ) ≤ Cw * EB * D := mul_nonneg (mul_nonneg hCw hEB) hD
  have hstep := abs_energy_le_of_weakNegDual hsplit (le_of_lt hsig) hsup hhol hb hH hWf hWg
  have hWsum : (0 : ℝ) ≤ w * sigma * (Cw * EB * D) + sigma * (w * (Cw * EB * D)) := by
    have ha : (0 : ℝ) ≤ w * sigma * (Cw * EB * D) :=
      mul_nonneg (mul_nonneg (le_of_lt hwpos) (le_of_lt hsig)) hCED
    have hb2 : (0 : ℝ) ≤ sigma * (w * (Cw * EB * D)) :=
      mul_nonneg (le_of_lt hsig) (mul_nonneg (le_of_lt hwpos) hCED)
    linarith only [ha, hb2]
  have hchain := hstep.trans (mul_le_mul_of_nonneg_left hSch hWsum)
  refine hchain.trans (le_of_eq ?_)
  have hww : w * w⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hwpos)
  have hbr : energyBracket sigma pow Kg KhInf Kh ^ (2 : ℕ) = sigma * D ^ (2 : ℕ) := by
    rw [hDdef, sigma_mul_sq_dataBracket sigma pow Kg KhInf Kh hsig]
  rw [hbr]
  calc (w * sigma * (Cw * EB * D) + sigma * (w * (Cw * EB * D))) * (Csch * w⁻¹ * D)
      = (w * w⁻¹) * (2 * Cw * Csch * EB * (sigma * D ^ (2 : ℕ))) := by ring
    _ = 2 * Cw * Csch * EB * (sigma * D ^ (2 : ℕ)) := by rw [hww, one_mul]

end

end Algsuperdiff.Section4.Provider.Homogenization
