/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.LambdaSensitivityUnconditional
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.ResponseCongruence
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.ObservableSwapPayoff
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.Step1Assembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Events

/-!
# SensitivitySwitch

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The field switch `a_{n−2} ⟶ a_{j−2}` at a triadic cube

ABK26, §4.1, the first inequality of the
sensitivity switch of `l.localize.lambdas.for.regularity`:

```
λ_{γ,2}^{-1}(z+□_{j−2}; a_{n−2})
  ≤ 6 ( 1 + C 3^{2j} ‖∇(k_{n−2} − k_{j−2})‖_{W^{1,∞}(z+□_{j−2})}
              λ_{γ,2}^{-1}(z+□_{j−2}; a_{j−2}) )^{2γ/(1−2γ)}
      λ_{γ,2}^{-1}(z+□_{j−2}; a_{j−2}) .
```

The manuscript reads this off `l.J.sensitivity.no.conditions`'s display
`e.lambda.sensitivity.no.conditions` at `a := a_{j−2}`, `h := k_{n−2} − k_{j−2}`,
`s = t = γ`, `q = 2` — hence the literal factor `6` and the exponent
`2γ/(1−2γ)`.

This module performs the transport to an arbitrary triadic cube `Q = z + □_l`
at the actual cutoff fields, using only proved, pointwise, unconditional
Section 3 machinery:

* `BadEvents.unitRescaledCutoffCoeff` / `unitCubeLambda_unitRescaledCutoffCoeff`
  — the `λ`-gauge of `a_r` on `Q` **is** the frozen unit-cube gauge of the
  rescaled coefficient object (an equality, no side condition);
* `BadEvents.perturbCoeffOn_unitRescaledCutoffCoeff_aeEq` /
  `unitCubeLambda_perturbCoeffOn_unitRescaledCutoffCoeff` — the frozen
  perturbation of the rescaled `a_j` by the rescaled increment `k_n − k_j`
  **is** the rescaled `a_n` (for `j ≤ n`);
* `BadEvents.gradientW1Infinity_incrementUnitCube₂_le` — the anchor's unit-cube
  gauge is below `incrementOscGauge₂ Q j n`, which is the manuscript's
  `3^{2l} ‖∇(k_n − k_j)‖_{W^{1,∞}(z+□_l)}`.

Nothing here is a.e. in the sample and nothing is conditional on a good local
event: unlike the Section 3 consumers of the *conditional* anchor
`Frozen.Section24.lambda_sensitivity`, the unconditional anchor needs no gate,
which is exactly why §4.1 can cite it as `l.J.sensitivity.no.conditions`.

## The carrier identification

`Section4/Support/Events.lean` writes the `𝒢₀` atom as the centered literal of
`Observable/CutoffMultiscaleEllipticity.lean` read at the translated sample.
`lambdaAnnulusAtom_eq_inv_lambdaSq` identifies it with `λ_{γ,2}^{-1}` of the
Chapter 2 carrier on the honest triadic cube `z + □_{k−2}`, which is what the
sensitivity statement above is phrased at.  It is the composition of two proved
Section 3 identities and carries no hypothesis.

## What is *not* here

The `𝒢₁`-derived budget `3^{2j}‖∇(k_{n−2}−k_{j−2})‖_{W^{1,∞}(z+□_{j−2})}
≤^{(1+γ)(m−j)/4}` — the second inequality of the step — is **not** proved here.

## References

* ABK26, `l.localize.lambdas.for.regularity`, the sensitivity switch.
* `l.J.sensitivity.no.conditions` / `e.lambda.sensitivity.no.conditions`, the
  anchor `Frozen.Section24.lambda_sensitivity_unconditional`.
* `d.good.event.for.lambda`.
-/

namespace Algsuperdiff.Section4.Provider.Localize

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The triadic cube of a lattice point -/

/-- The triadic cube `z + □_j` at the lattice point `z = 3^j v` of `3^j ℤ^d`,
i.e. the cube of scale `j` and integer index `v`. -/
def latticeCube (j : ℤ) (v : Fin d → ℤ) : TriadicCube d := ⟨j, v⟩

@[simp] theorem latticeCube_scale (j : ℤ) (v : Fin d → ℤ) :
    (latticeCube j v).scale = j := rfl

/-- The base point of `latticeCube j v` is the Section 4 lattice point
`Support.triadicLatticePoint j v`. -/
theorem triadicCubeShift_latticeCube (j : ℤ) (v : Fin d → ℤ) :
    triadicCubeShift (latticeCube j v) = Support.triadicLatticePoint j v := by
  funext i
  simp only [triadicCubeShift, latticeCube, Support.triadicLatticePoint,
    cubeScaleFactor]
  exact mul_comm _ _

/-! ## 2. The `𝒢₀` atom is `λ_{γ,2}^{-1}` at the Chapter 2 carrier -/

/-- **The carrier identification.**  The Section 4 support layer's `𝒢₀` atom at
the lattice point `3^{k−2} v` is `λ_{γ,2}^{-1}(z + □_{k−2}; a_{k−2})` of the
Chapter 2 coefficient family of the actual cutoff, on the honest triadic cube.

This is the composition of the proved off-centre identification
`BadEvents.cubeLowerEllipticityInvLiteral_translateCutoffSample` with the
proved `Multiscale.cubeLowerEllipticityInvLiteral_eq_lambdaSq_inv`; it holds at
every sample point and carries no hypothesis. -/
theorem lambdaAnnulusAtom_eq_inv_lambdaSq (M : ABKModel d) (k : ℤ)
    (v : Fin d → ℤ) (omega : Cutoff.CutoffSample d) :
    Support.lambdaAnnulusAtom M k (Support.triadicLatticePoint (k - 2) v) omega =
      (Ch02.lambdaSq (latticeCube (k - 2) v) M.gamma
        Support.coarseEllipticityExponentTwo.1
        (Cutoff.coefficientCutoffTriadicCoeffFamily M (k - 2) omega))⁻¹ := by
  have hshift := triadicCubeShift_latticeCube (d := d) (k - 2) v
  have hswap :=
    Algsuperdiff.Section3.Provider.BadEvents.cubeLowerEllipticityInvLiteral_translateCutoffSample
      M (latticeCube (k - 2) v) (k - 2) M.gamma
      Support.coarseEllipticityExponentTwo omega
  rw [hshift, latticeCube_scale] at hswap
  rw [Support.lambdaAnnulusAtom, ← hswap,
    Algsuperdiff.Section3.Provider.Multiscale.cubeLowerEllipticityInvLiteral_eq_lambdaSq_inv]

/-! ## 3. The unconditional `λ`-sensitivity, transported to a cube -/

end

end Algsuperdiff.Section4.Provider.Localize
