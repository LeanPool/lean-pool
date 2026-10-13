/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Path.Densities
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.DoubledMu

/-!
# MuExpansion

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Two-sided expansion of the doubled `mu` functional along the path

The doubled `mu` functional is an infimum over a class of doubled fields that
does **not** depend on the coefficient, while the energy of every fixed field
expands exactly quadratically along `t ↦ perturbCoeffOn U a h t`.  Testing the
infimum with the base minimizer yields the upper second-difference expansion
of `l.sensitivity.coarse.grained.general`.

The printed suggestion to obtain the lower estimate by "applying the same
argument with `-h` in place of `h`" at the same base field proves an estimate
about `a - h`, not the required lower bound at `a + h`.  The faithful route
applies the upper estimate at the shifted base field: testing the base infimum
with the *shifted* minimizer yields
`doubledMu_perturbCoeffOn_expansion_lower`, whose linear term is the one
attached to the shifted base.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Path

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The exact value-level expansion along the path -/

/-- **Exact expansion of the doubled energy value along the canonical path.**
For every doubled field with vector-`L²` components,
`E_t(X) = E_0(X) + t ℓ(X) + t² q(X)` with no remainder. -/
theorem doubledMuValue_perturbCoeffOn {U : Domain d} (a : CoeffOn U)
    (h : LInfSkewMatrixFieldOn U) (t : ℝ) {X : DoubledField d}
    (hpot : MemVectorL2 (U : Set (Vec d)) X.potential)
    (hflux : MemVectorL2 (U : Set (Vec d)) X.flux) :
    doubledMuValue U (perturbCoeffOn U a h t) X =
      doubledMuValue U a X + t * pathLinearTerm a h.1.1 X
        + t ^ 2 * pathQuadraticTerm a h.1.1 X := by
  have hL := integrableOn_pathLinearDensity a h.1 hpot hflux
  have hQ := integrableOn_pathQuadraticDensity a h.1 hpot
  have hE := integrableOn_blockEnergyDensity a hpot hflux
  show volumeAverage (U : Set (Vec d))
      (fun x => blockEnergyDensityAt (perturbCoeffOn U a h t) (X.eval x) x) = _
  rw [volumeAverage_congr_ae (blockEnergyDensity_expansion_ae a h t X)]
  rw [show (fun x => blockEnergyDensityAt a (X.eval x) x
        + t * pathLinearDensity a h.1.1 X x
        + t ^ 2 * pathQuadraticDensity a h.1.1 X x)
      = ((fun x => blockEnergyDensityAt a (X.eval x) x)
          + t • pathLinearDensity a h.1.1 X)
        + t ^ 2 • pathQuadraticDensity a h.1.1 X from rfl]
  rw [volumeAverage_add (hE.add (hL.smul t)) (hQ.smul (t ^ 2)),
    volumeAverage_add hE (hL.smul t),
    volumeAverage_smul, volumeAverage_smul]
  rfl

/-! ## Competitor bounds -/

/-- The doubled `mu` infimum is bounded by the value of any admissible
doubled field. -/
theorem doubledMu_le_doubledMuValue {U : Domain d} (a : CoeffOn U)
    (P : BlockVec d) {X : DoubledField d}
    (hX : IsDoubledMuAdmissible U P X) :
    doubledMu U a P ≤ doubledMuValue U a X := by
  obtain ⟨Y, hY⟩ := (doubledMuTheory U a).minimizer_exists P
  have hbdd : BddBelow (doubledMuValueSet U a P) := by
    refine ⟨doubledMuValue U a Y, ?_⟩
    rintro m ⟨Z, hZ, rfl⟩
    exact hY.2 Z hZ
  exact csInf_le hbdd ⟨X, hX, rfl⟩

/-! ## The two-sided second-difference expansion -/

/-- **Upper second-difference expansion at the base field** (source: the chain of
displays from `e.variational.mu.U.P` to the final display of the proof of
`l.sensitivity.coarse.grained.general`, upper half).  Testing the perturbed
infimum with a base minimizer `X` gives `mu_t - mu_0 - t ℓ(X) ≤ t² q(X)`. -/
theorem doubledMu_perturbCoeffOn_expansion_upper {U : Domain d}
    (a : CoeffOn U) (h : LInfSkewMatrixFieldOn U) (t : ℝ) (P : BlockVec d)
    {X : DoubledField d} (hX : IsDoubledMuMinimizer U a P X) :
    doubledMu U (perturbCoeffOn U a h t) P - doubledMu U a P
        - t * pathLinearTerm a h.1.1 X
      ≤ t ^ 2 * pathQuadraticTerm a h.1.1 X := by
  have hpot := memVectorL2_potential_of_isDoubledMuAdmissible hX.1
  have hflux := memVectorL2_flux_of_isDoubledMuAdmissible hX.1
  have h1 : doubledMu U (perturbCoeffOn U a h t) P ≤
      doubledMuValue U (perturbCoeffOn U a h t) X :=
    doubledMu_le_doubledMuValue (perturbCoeffOn U a h t) P hX.1
  rw [doubledMuValue_perturbCoeffOn a h t hpot hflux,
    hX.doubledMuValue_eq_doubledMu] at h1
  linarith

/-- Testing the *base* infimum with a minimizer `X` of the *shifted* problem gives
`t ℓ(X) + t² q(X) ≤ mu_t - mu_0`, where `ℓ(X), q(X)` are still the base
response terms. -/
theorem doubledMu_perturbCoeffOn_expansion_lower {U : Domain d}
    (a : CoeffOn U) (h : LInfSkewMatrixFieldOn U) (t : ℝ) (P : BlockVec d)
    {X : DoubledField d}
    (hX : IsDoubledMuMinimizer U (perturbCoeffOn U a h t) P X) :
    t * pathLinearTerm a h.1.1 X + t ^ 2 * pathQuadraticTerm a h.1.1 X
      ≤ doubledMu U (perturbCoeffOn U a h t) P - doubledMu U a P := by
  have hpot := memVectorL2_potential_of_isDoubledMuAdmissible hX.1
  have hflux := memVectorL2_flux_of_isDoubledMuAdmissible hX.1
  have h1 : doubledMu U a P ≤ doubledMuValue U a X :=
    doubledMu_le_doubledMuValue a P hX.1
  have h2 := doubledMuValue_perturbCoeffOn a h t hpot hflux (X := X)
  rw [hX.doubledMuValue_eq_doubledMu] at h2
  linarith

end

end Algsuperdiff.Section24.Sensitivity.Provider.Path
