/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FoldAbsorption
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.ConstantAbsorptionIntoLength

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.RootCertificateAndFoldAbsorption

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# (iii) the certificate surface, and the `Lg`/`pEcc` double absorptions

**(iii).**  `RootInterface.RootGoodScale.provider_surface` hands the Dirichlet
provider everything the certificate side of the module asks for.  Two of its
eight conclusions are the ones no other module supplies: the positive-definiteness
of `symmPart abar`, and the retained row's amplitude window
`delta ∈ Ioo 0 1` — from which `√δ ≤ 1`, the hypothesis the module needs to
drop the certificate amplitude out of the flux constant.
The Dirichlet-surface packaging supplies exactly those.

**The double absorptions.**  The module proves the frozen conclusion at the capstone's
own length `x * eccentricityFoldFactor abar p₀` and at whatever constant the
caller passes.  The clause wants it at `x * (Lg * eccentricityFoldFactor abar pEcc)`
with `C₀` **law-free**.  The two moves that get there are already separately — that module
absorptions a law-free residual `Krest` into the length factor at
the rate `κ`, and that module absorptions an eccentricity power into the fold exponent — and
`constant_and_eccentricity_absorbed` performs them in one step, with

```
Lg   := perGLengthFactor Krest κ ,      pEcc := p₀ + p / κ .
```

That is the dispatch's "`pEcc` := the sum of the rate-leg and energy-leg
exponents": `p₀` is the rate leg (`foldedFrameEccentricityExponent g κ`), and
`p / κ` is the energy leg together with the output factor's `(d+1)/2`, divided
by `κ` because the rate factor takes the `κ`-th power.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## (iii) The certificate surface -/

/-! ## The double absorptions -/

/-- **The `Lg`/`pEcc` double absorptions.**  A law-free residual constant and an
eccentricity power standing beside the law-free head are absorbed, the first
into the per-`g` length factor and the second into the fold exponent, leaving
the head alone in front of the clause's rate factor. -/
theorem constant_and_eccentricity_absorbed (abar : Mat d)
    {Claw Krest p p0 kappa epsilon x : ℝ}
    (hClaw : 0 ≤ Claw) (hkappa : 0 < kappa) (hp : 0 ≤ p) (hp0 : 0 ≤ p0)
    (heps : 0 ≤ epsilon) (hx : 0 ≤ x) :
    (Claw * (max 1 (witnessEccentricity (symmPart abar))) ^ p * Krest) *
        (epsilon * (x * eccentricityFoldFactor abar p0)) ^ kappa ≤
      Claw *
        (epsilon * (x * (perGLengthFactor Krest kappa *
          eccentricityFoldFactor abar (p0 + p / kappa)))) ^ kappa := by
  have hE0 : (0 : ℝ) ≤ max 1 (witnessEccentricity (symmPart abar)) :=
    le_trans zero_le_one (le_max_left _ _)
  have hEp0 : (0 : ℝ) ≤ (max 1 (witnessEccentricity (symmPart abar))) ^ p :=
    Real.rpow_nonneg hE0 _
  have hC0 : (0 : ℝ) ≤
      Claw * (max 1 (witnessEccentricity (symmPart abar))) ^ p :=
    mul_nonneg hClaw hEp0
  have hfold0 : (0 : ℝ) ≤ eccentricityFoldFactor abar p0 :=
    (eccentricityFoldFactor_pos abar p0).le
  have hLg0 : (0 : ℝ) ≤ perGLengthFactor Krest kappa := by
    rw [perGLengthFactor]
    exact Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
  have hstep1 := constant_absorbed_into_length
    (C0 := Claw * (max 1 (witnessEccentricity (symmPart abar))) ^ p)
    (Krest := Krest) (epsilon := epsilon) (x := x)
    (fold := eccentricityFoldFactor abar p0) (kappa := kappa)
    hC0 hkappa heps hx hfold0
  have hassoc : ∀ y : ℝ,
      epsilon * (x * perGLengthFactor Krest kappa * y) =
        epsilon * (x * (perGLengthFactor Krest kappa * y)) := by
    intro y
    ring
  rw [hassoc] at hstep1
  exact hstep1.trans
    (eccentricity_absorbed_into_fold abar hClaw hkappa hp hp0 heps hx hLg0)

end

end RowSupply
end HighContrast
end HCPolySupport
