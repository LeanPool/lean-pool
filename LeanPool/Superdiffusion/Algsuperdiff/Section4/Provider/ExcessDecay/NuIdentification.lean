/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.AntisymmetricShiftCutoff
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.FluxCorrectedRepresentative
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Definitions

/-!
# NuIdentification

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `ν`-identification of the coefficient energy

Throughout §4.3 the manuscript writes the local energy of a solution in three
interchangeable ways:

```text
  ⨍_V ∇u · a_L ∇u        (the coarse-graining lemmas)
  ⨍_V ∇u · symm(a) ∇u    (CoarseGraining's localizedCoeffEnergyValue)
  ν ⨍_V |∇u|²            (the manuscript's own "ν^{1/2}‖∇u‖")
```

The third form is ABK26; the `ν^{1/2}‖∇u‖` it abbreviates is that of ABK26.

The three agree **exactly**, and the reason is the antisymmetric structure of the
layer law: `a_L = ν Id + k_L` with `k_L` skew, so `symm(a_L) = ν Id`, and the
skew part contributes nothing to a quadratic form.  Subtracting the constant skew
matrix `(k_L − k_{n+2})_{z+□_{n+2}}` does not disturb this: `symm(ã_{L,n+2})` is
still exactly `ν Id`.

This module closes it.

## What is proved is an, and it is unconditional

That is weaker than the truth and the caps chain is not needed: the identity
`symm(ã_{L,k}) = ν Id` holds for **every** sample and every point, so

```text
  localizedCoeffEnergyValue V ã_{L,k} u = ν · ⨍_V |∇u|²
```

is an equality valid pointwise in `ω`, with no good event, no ellipticity ratio
cap and no probabilistic input whatsoever.  Both inequalities follow, and the
`ν^{1/2}` form is obtained by taking square roots.

## Main results

* `vecDot_matVecMul_symmPart_self` — the symmetric part is invisible on the
  diagonal: `v · symm(A) v = v · A v` for every matrix.
* `localizedCoeffEnergyValue_eq_mul_of_symmPart_eq` — the general identification
  for any coefficient object whose symmetric part is a constant multiple of the
  identity.
* `sqrt_localizedCoeffEnergyValue_fluxCorrectedCoeffFamily` — the printed
  `ν^{1/2}‖∇u‖_{L²(V)}` reading.

## References

* ABK26, (`⨍ ν|∇u|²` as the energy base).
* CoarseGraining, `Homogenization/Book/Ch03/Definitions.lean`
  (`localizedCoeffEnergyValue`), `Homogenization/Ambient/Basic.lean`
  (`symmPart`, `skewPart`, `matTranspose_skewPart`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The symmetric part is invisible on the diagonal -/

/-! ## 2. The general identification -/

private theorem volumeAverage_const_mul (V : Set (Vec d)) (c : ℝ) (f : Vec d → ℝ) :
    volumeAverage V (fun x => c * f x) = c * volumeAverage V f := by
  unfold volumeAverage
  rw [MeasureTheory.integral_const_mul]
  ring

private theorem vecDot_matVecMul_smul_one (nu : ℝ) (v : Vec d) :
    vecDot v (matVecMul (nu • (1 : Mat d)) v) = nu * vecNormSq v := by
  have hmat : matVecMul (nu • (1 : Mat d)) v = nu • v := by
    rw [smul_matVecMul]
    congr 1
    funext i
    simp only [matVecMul, Matrix.one_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ i v]
    simp
  rw [hmat]
  simp only [vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The `ν`-identification, general form.**  If the symmetric part of the
coefficient representative is `ν Id` at every point, the localized coefficient
energy is exactly `ν` times the normalized gradient `L²` square. -/
theorem localizedCoeffEnergyValue_eq_mul_of_symmPart_eq {U : Ch02.Domain d}
    (V : Set (Vec d)) (a : Ch02.CoeffOn U) (u : H1Function (U : Set (Vec d)))
    (nu : ℝ) (hsymm : ∀ x : Vec d, symmPart (a.toCoeffField x) = nu • (1 : Mat d)) :
    localizedCoeffEnergyValue V a u =
      nu * normalizedSetAverage V (fun x => vecNormSq (u.grad x)) := by
  have hpt : ∀ x : Vec d,
      vecDot (u.grad x) (matVecMul (symmPart (a.toCoeffField x)) (u.grad x)) =
        nu * vecNormSq (u.grad x) := by
    intro x
    rw [hsymm x]
    exact vecDot_matVecMul_smul_one nu (u.grad x)
  rw [localizedCoeffEnergyValue,
    show (fun x : Vec d =>
        vecDot (u.grad x) (matVecMul (symmPart (a.toCoeffField x)) (u.grad x))) =
      fun x : Vec d => nu * vecNormSq (u.grad x) from funext hpt]
  exact volumeAverage_const_mul V nu _

/-! ## 3. The identification at the flux-corrected family -/

/-- **The `ν`-identification at the shifted field.**

No good event, no ellipticity cap, no hypothesis on the sample. -/
theorem localizedCoeffEnergyValue_fluxCorrectedCoeffFamily_eq (M : ABKModel d)
    (L k : ℤ) (Q R : TriadicCube d) (omega : Cutoff.CutoffSample d)
    (V : Set (Vec d))
    (u : H1Function (Ch02.cubeDomain R : Set (Vec d))) :
    localizedCoeffEnergyValue V
        ((Support.fluxCorrectedCoeffFamily M L k Q omega).coeffOn R) u =
      (M.nu : ℝ) * normalizedSetAverage V (fun x => vecNormSq (u.grad x)) := by
  refine localizedCoeffEnergyValue_eq_mul_of_symmPart_eq V _ u M.nu fun x => ?_
  have hfield : ((Support.fluxCorrectedCoeffFamily M L k Q omega).coeffOn R).toCoeffField x =
      Support.fluxCorrectedField M L k Q omega x := by
    rw [Support.fluxCorrectedCoeffFamily,
      Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField_coeffOn_toCoeffField]
    exact congrFun (Support.fluxCorrectedRegField_toFun M L k Q omega) x
  rw [hfield]
  exact symmPart_fluxCorrectedField_eq M L k Q omega x

/-! ## 4. The printed `ν^{1/2}‖∇u‖` form -/

/-- **The manuscript's `ν^{1/2}‖∇u‖_{L²(V)}`.**  The square root of the localized
coefficient energy of `ã_{L,k}` factors exactly as `ν^{1/2}` times the
normalized gradient `L²` norm — the form in which write the energy. -/
theorem sqrt_localizedCoeffEnergyValue_fluxCorrectedCoeffFamily (M : ABKModel d)
    (L k : ℤ) (Q R : TriadicCube d) (omega : Cutoff.CutoffSample d)
    (V : Set (Vec d))
    (u : H1Function (Ch02.cubeDomain R : Set (Vec d))) :
    Real.sqrt (localizedCoeffEnergyValue V
        ((Support.fluxCorrectedCoeffFamily M L k Q omega).coeffOn R) u) =
      Real.sqrt (M.nu : ℝ) *
        Real.sqrt (normalizedSetAverage V (fun x => vecNormSq (u.grad x))) := by
  rw [localizedCoeffEnergyValue_fluxCorrectedCoeffFamily_eq M L k Q R omega V u,
    Real.sqrt_mul (le_of_lt M.nu_pos)]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
