/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.JunctionDischargeStepFiveDisplay
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationSplitFoldArithmetic

/-!
# GammaTenGridFold

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The **grid** annealed Hoelder fold of Step 2

ABK26, Step 2 of `l.approximate.recurrence.formula`, at the carrier of
`e.lower.bound.localization.terms`.

## The gap this module fills

`LocalizationFluctuationSplitFoldArithmetic.integral_mul_mul_le_gamma_pow_twelve_of_regime`
performs the annealed Hoelder fold **at one mesoscopic cell**: it asks for the
oscillation leg in the per-cell form `E[h^2] <= (Cosc cgamma^{14})^2`.  No such
per-cell moment is available.  The proved oscillation producers --- the
full-mesh endpoints
`LocalizationOscillationFullMesh.exists_gamma0_freshShellDirichlet_step5MeshOscillation_le_gamma_pow_fifteen`
and its Neumann mirror --- control only the **grid** functional

```
  gridFourthMomentRoot mu (descendantsAtDepth cu_K j) osc
    =  ( avsum_{R} E[ osc_R^4 ] )^{1/4}   <=  cgamma^{15} ,
```

and the target of Step 2 is itself a grid average,

```
  fluctuationEnergyAverage  =  avsum_{R in descendantsAtDepth cu_K j} E[ cell_R ] .
```

So the fold has to be run **jointly** in the sample and on the grid: Hoelder in
the sample per cell at the exponents `1/4 + 1/4 + 1/2 = 1`, with the two
*uniform* legs (ellipticity, load) released to constants, and then Jensen on the
grid to collect the remaining oscillation legs into the single grid functional
the producers bound.  That joint step is what this module supplies.

## What is proved

* `integral_rpow_two_rpow_half_le_rpowFourRoot` --- the `L^2` leg of the Hoelder
  triple, released to the fourth-moment root that the grid functional is built
  from (Cauchy--Schwarz in the sample on a probability space).
* `integral_mul_mul_le_mul_mul_rpowFourRoot` --- the per-cell fold with its two
  uniform legs released: `E[f g h] <= a b (E[h^4])^{1/4}`.
* `cubeFamilyAverage_integral_mul_sq_le_sq_gridFourthMomentRoot` --- **the
  quadratic term on the grid**:
  ```
    avsum_R E[ F_R H_R H_R ]  <=  a * (gridFourthMomentRoot mu I H)^2 .
  ```
* The matching cross term `avsum_R E[F_R G_R H_R]`, and the two legs added at
  the shape the per-cube bound of
  `LocalizationFluctuationPerCube.perCube_localizationFluctuation_le` delivers
  once its ellipticity factor has been replaced by
  `LocalizationFluctuationEllipticity.gaugedEllipticitySum` (both summands of
  the per-cube bound are then **linear** in that sum), are assembled from these
  pieces in `Closure.GammaTenLoadFold`.
* `exists_gamma_threshold_gridFold` --- the numerical obligation, at the
  exponents this route produces.  With the ellipticity leg at `cgamma^{-2}`
  (`LocalizationFluctuationSplitFoldArithmetic.gammaRegime_ellipticityLeg_le`,
  the `cstar^{-1}` absorption) and the oscillation grid root at `cgamma^{15}`,
  the cross term is `c1 cgamma^{13}` and the quadratic term `c2 cgamma^{28}`;
  both exponents are strictly above `10`, so
  `exists_gamma_threshold_regime_holder_fold` closes the fold.  The threshold is
  **produced**, not assumed.

## The exponent bookkeeping

| leg | per cell | on the grid |
| --- | --- | --- |
| ellipticity | `(E[G^4])^{1/4} <= cgamma^{-2}` | uniform in `R` |
| load | `(E[L^4])^{1/4} <= Cload` | uniform in `R` |
| oscillation | none | `( avsum_[B_R^4] )^{1/4} <= cgamma^{15}` |

cross: `cgamma^{-2} * Cload * cgamma^{15} = Cload cgamma^{13}`;
quadratic: `cgamma^{-2} * (cgamma^{15})^2 = cgamma^{28}`.

## Binders

Everything below is measure theory and real arithmetic at a probability
measure.  The binders are the pointwise nonnegativity of the three families,
the `L^p` memberships that the two Cauchy--Schwarz steps of
`LocalizationFluctuationGammaFold.integral_mul_mul_le_L4_L4_L2` require ---
these are conditional A obligations, discharged by the caller at its carrier
--- and the two *uniform* moment bounds.  No smallness gate is assumed: the
`cgamma`-threshold of `exists_gamma_threshold_gridFold` is produced.  Nothing
about the corrector, the coefficient field or the cube geometry occurs.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2,
  `e.lower.bound.localization.terms`, `e.lower.bound.oscillations`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem gridFold_ofReal_two : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
  simp [ENNReal.ofReal_ofNat]

section Sample

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## The `L^2` leg of the Hoelder triple, released to the fourth-moment root -/

/-- **Cauchy--Schwarz in the sample, at the exponent the grid functional uses.**

The oscillation leg of the annealed Hoelder fold enters as `(E[h^2])^{1/2}`,
while `gridFourthMomentRoot` is built from `E[h^4]`.  On a probability space the
two are ordered:

```
  ( E[h^2] )^{1/2}  <=  ( E[h^4] )^{1/4} .
```

on the nonnegativity of `h` and on `h in L^4`, the standing integrability of
the moment being formed. -/
theorem integral_rpow_two_rpow_half_le_rpowFourRoot (mu : Measure Omega)
    [IsProbabilityMeasure mu] {X : Omega → ℝ} (hX : ∀ w, 0 ≤ X w)
    (hXm : MemLp X 4 mu) :
    (∫ w, X w ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) ≤
      (∫ w, X w ^ (4 : ℝ) ∂mu) ^ ((4 : ℝ)⁻¹) := by
  have hbase := integral_rpow_two_le_rpow_integral_rpow_four mu hX hXm
  have hnn : (0 : ℝ) ≤ ∫ w, X w ^ (2 : ℝ) ∂mu :=
    integral_nonneg fun w => Real.rpow_nonneg (hX w) _
  have h4nn : (0 : ℝ) ≤ ∫ w, X w ^ (4 : ℝ) ∂mu :=
    integral_nonneg fun w => Real.rpow_nonneg (hX w) _
  have hmono := Real.rpow_le_rpow hnn hbase (by norm_num : (0 : ℝ) ≤ 1 / (2 : ℝ))
  refine hmono.trans (le_of_eq ?_)
  rw [← Real.rpow_mul h4nn]
  norm_num

/-- **The fourth-moment bounds of the two uniform legs, in the fourth-root
spelling the fold consumes.**  Unconditional apart from the sign of the
majorant. -/
theorem rpowFourRoot_le_of_integral_rpow_four_le (mu : Measure Omega)
    {X : Omega → ℝ} (hX : ∀ w, 0 ≤ X w) {A : ℝ} (hA : 0 ≤ A)
    (h4 : ∫ w, X w ^ (4 : ℝ) ∂mu ≤ A ^ (4 : ℕ)) :
    (∫ w, X w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) ≤ A := by
  have hnn : (0 : ℝ) ≤ ∫ w, X w ^ (4 : ℝ) ∂mu :=
    integral_nonneg fun w => Real.rpow_nonneg (hX w) _
  have hmono := Real.rpow_le_rpow hnn h4 (by norm_num : (0 : ℝ) ≤ 1 / (4 : ℝ))
  have heq : (A ^ (4 : ℕ)) ^ (1 / (4 : ℝ)) = A := by
    rw [← Real.rpow_natCast A 4, ← Real.rpow_mul hA]
    norm_num
  rwa [heq] at hmono

/-- **The ellipticity leg at the regime amplitude.**  The proved producer
`LocalizationFluctuationSplitFoldArithmetic.exists_regime_gaugedEllipticitySum_pow_four_le`
delivers `E[F^4] <= (cgamma^8)^{-1}`; the fold consumes `(E[F^4])^{1/4} <=
(cgamma^2)^{-1}`.  The two are the same statement. -/
theorem rpowFourRoot_le_inv_sq_of_integral_rpow_four_le (mu : Measure Omega)
    {X : Omega → ℝ} (hX : ∀ w, 0 ≤ X w) {gamma : ℝ} (hgamma : 0 < gamma)
    (h4 : ∫ w, X w ^ (4 : ℝ) ∂mu ≤ (gamma ^ (8 : ℕ))⁻¹) :
    (∫ w, X w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) ≤ (gamma ^ (2 : ℕ))⁻¹ := by
  have hpow : ((gamma ^ (2 : ℕ))⁻¹) ^ (4 : ℕ) = (gamma ^ (8 : ℕ))⁻¹ := by
    rw [← inv_pow, ← pow_mul, inv_pow]
  refine rpowFourRoot_le_of_integral_rpow_four_le mu hX (by positivity) ?_
  rw [hpow]
  exact h4

/-! ## The per-cell fold with the two uniform legs released -/

/-- **The three-factor Hoelder fold at one cell, with the ellipticity and load legs
released to constants.**

```
  E[ f g h ]  <=  a * b * ( E[h^4] )^{1/4}
```

whenever `(E[f^4])^{1/4} <= a` and `(E[g^4])^{1/4} <= b`.  The point of the
shape is that the *third* leg is left in the fourth-moment spelling, which is
the one the grid functional `gridFourthMomentRoot` collects.

on the pointwise nonnegativity of the three factors and on the four `L^p`
memberships of the two Cauchy--Schwarz steps; these are analytic side
conditions of the pairing, not premises of the pinned source statement. -/
theorem integral_mul_mul_le_mul_mul_rpowFourRoot (mu : Measure Omega)
    [IsProbabilityMeasure mu] (f g h : Omega → ℝ)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w) (hh : ∀ w, 0 ≤ h w)
    (hfm : MemLp (fun w => f w ^ (2 : ℝ)) (ENNReal.ofReal 2) mu)
    (hgm : MemLp (fun w => g w ^ (2 : ℝ)) (ENNReal.ofReal 2) mu)
    (hhm : MemLp h 4 mu)
    (hfgm : MemLp (fun w => f w * g w) (ENNReal.ofReal 2) mu)
    {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : (∫ w, f w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) ≤ a)
    (hb : (∫ w, g w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) ≤ b) :
    ∫ w, f w * g w * h w ∂mu ≤ a * b * (∫ w, h w ^ (4 : ℝ) ∂mu) ^ ((4 : ℝ)⁻¹) := by
  have hh2 : MemLp h (ENNReal.ofReal 2) mu := by
    rw [gridFold_ofReal_two]
    exact hhm.mono_exponent (by norm_num)
  have hholder := integral_mul_mul_le_L4_L4_L2 mu f g h hf hg hh hfm hgm hh2 hfgm
  have hI4f : (0 : ℝ) ≤ ∫ w, f w ^ (4 : ℝ) ∂mu :=
    integral_nonneg fun w => Real.rpow_nonneg (hf w) _
  have hI4g : (0 : ℝ) ≤ ∫ w, g w ^ (4 : ℝ) ∂mu :=
    integral_nonneg fun w => Real.rpow_nonneg (hg w) _
  have hI4h : (0 : ℝ) ≤ ∫ w, h w ^ (4 : ℝ) ∂mu :=
    integral_nonneg fun w => Real.rpow_nonneg (hh w) _
  have hI2h : (0 : ℝ) ≤ ∫ w, h w ^ (2 : ℝ) ∂mu :=
    integral_nonneg fun w => Real.rpow_nonneg (hh w) _
  have hq1 : (0 : ℝ) ≤ (∫ w, f w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) :=
    Real.rpow_nonneg hI4f _
  have hq2 : (0 : ℝ) ≤ (∫ w, g w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) :=
    Real.rpow_nonneg hI4g _
  have hq3 : (0 : ℝ) ≤ (∫ w, h w ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) :=
    Real.rpow_nonneg hI2h _
  have hlast : (∫ w, h w ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) ≤
      (∫ w, h w ^ (4 : ℝ) ∂mu) ^ ((4 : ℝ)⁻¹) :=
    integral_rpow_two_rpow_half_le_rpowFourRoot mu hh hhm
  have hstep1 : (∫ w, f w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) *
      (∫ w, g w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) ≤ a * b :=
    mul_le_mul ha hb hq2 ha0
  have hstep2 : (∫ w, f w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) *
      (∫ w, g w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) *
      (∫ w, h w ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) ≤
      a * b * (∫ w, h w ^ (4 : ℝ) ∂mu) ^ ((4 : ℝ)⁻¹) :=
    mul_le_mul hstep1 hlast hq3 (mul_nonneg ha0 hb0)
  linarith [hholder, hstep2]

/-- **The quadratic per-cell fold**: the case `g = h` of the previous statement,
with the *second* fourth-moment root also released against the third leg.

```
  E[ f h h ]  <=  a * ( E[h^4] )^{1/2} .
```

exactly as the cross term. -/
theorem integral_mul_sq_le_mul_rpow_half (mu : Measure Omega)
    [IsProbabilityMeasure mu] (f h : Omega → ℝ)
    (hf : ∀ w, 0 ≤ f w) (hh : ∀ w, 0 ≤ h w)
    (hfm : MemLp (fun w => f w ^ (2 : ℝ)) (ENNReal.ofReal 2) mu)
    (hhsqm : MemLp (fun w => h w ^ (2 : ℝ)) (ENNReal.ofReal 2) mu)
    (hhm : MemLp h 4 mu)
    (hfhm : MemLp (fun w => f w * h w) (ENNReal.ofReal 2) mu)
    {a : ℝ} (ha0 : 0 ≤ a)
    (ha : (∫ w, f w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) ≤ a) :
    ∫ w, f w * h w * h w ∂mu ≤ a * (∫ w, h w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹) := by
  have hI4h : (0 : ℝ) ≤ ∫ w, h w ^ (4 : ℝ) ∂mu :=
    integral_nonneg fun w => Real.rpow_nonneg (hh w) _
  have hb0 : (0 : ℝ) ≤ (∫ w, h w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) :=
    Real.rpow_nonneg hI4h _
  have hbase := integral_mul_mul_le_mul_mul_rpowFourRoot mu f h h hf hh hh hfm hhsqm
    hhm hfhm ha0 hb0 ha (le_refl _)
  refine hbase.trans (le_of_eq ?_)
  have hsplit : (∫ w, h w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) *
      (∫ w, h w ^ (4 : ℝ) ∂mu) ^ ((4 : ℝ)⁻¹) =
      (∫ w, h w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹) := by
    rw [one_div, ← Real.rpow_add_of_nonneg hI4h (by norm_num) (by norm_num)]
    norm_num
  calc a * (∫ w, h w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) *
        (∫ w, h w ^ (4 : ℝ) ∂mu) ^ ((4 : ℝ)⁻¹)
      = a * ((∫ w, h w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) *
          (∫ w, h w ^ (4 : ℝ) ∂mu) ^ ((4 : ℝ)⁻¹)) := by ring
    _ = a * (∫ w, h w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹) := by rw [hsplit]

end Sample

/-! ## The two legs on the grid -/

section Grid

variable {Omega : Type*} [MeasurableSpace Omega]

/-- **The quadratic term, folded on the grid.**

```
  avsum_{R in I} E[ F_R H_R H_R ]  <=  a * ( gridFourthMomentRoot mu I H )^2 .
```

The grid step is Jensen for the concave square root
(`Closure.JunctionDischargeStepFiveDisplay.cubeFamilyAverage_sqrt_le`).

exactly as the cross term. -/
theorem cubeFamilyAverage_integral_mul_sq_le_sq_gridFourthMomentRoot
    (mu : Measure Omega) [IsProbabilityMeasure mu] (I : Finset (TriadicCube d))
    (F H : TriadicCube d → Omega → ℝ)
    (hF : ∀ R w, 0 ≤ F R w) (hH : ∀ R w, 0 ≤ H R w)
    (hFm : ∀ R ∈ I, MemLp (fun w => F R w ^ (2 : ℝ)) (ENNReal.ofReal 2) mu)
    (hHsqm : ∀ R ∈ I, MemLp (fun w => H R w ^ (2 : ℝ)) (ENNReal.ofReal 2) mu)
    (hHm : ∀ R ∈ I, MemLp (H R) 4 mu)
    (hFHm : ∀ R ∈ I, MemLp (fun w => F R w * H R w) (ENNReal.ofReal 2) mu)
    {a : ℝ} (ha0 : 0 ≤ a)
    (ha : ∀ R ∈ I, (∫ w, F R w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) ≤ a) :
    cubeFamilyAverage I (fun R => ∫ w, F R w * H R w * H R w ∂mu) ≤
      a * (gridFourthMomentRoot mu I H) ^ (2 : ℕ) := by
  have hper : ∀ R ∈ I, (∫ w, F R w * H R w * H R w ∂mu) ≤
      a * (∫ w, H R w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹) := fun R hR =>
    integral_mul_sq_le_mul_rpow_half mu (F R) (H R) (hF R) (hH R) (hFm R hR)
      (hHsqm R hR) (hHm R hR) (hFHm R hR) ha0 (ha R hR)
  have hgmnn : (0 : ℝ) ≤ gridFourthMoment mu I H :=
    gridFourthMoment_nonneg mu I H
  have hjensen : cubeFamilyAverage I
      (fun R => (∫ w, H R w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹)) ≤
      (gridFourthMoment mu I H) ^ ((2 : ℝ)⁻¹) :=
    cubeFamilyAverage_sqrt_le I (fun R => ∫ w, H R w ^ (4 : ℝ) ∂mu)
      (fun R _ => integral_nonneg fun w => Real.rpow_nonneg (hH R w) _)
  have hsq : (gridFourthMomentRoot mu I H) ^ (2 : ℕ) =
      (gridFourthMoment mu I H) ^ ((2 : ℝ)⁻¹) := by
    unfold gridFourthMomentRoot
    rw [← Real.rpow_natCast ((gridFourthMoment mu I H) ^ ((4 : ℝ)⁻¹)) 2,
      ← Real.rpow_mul hgmnn]
    norm_num
  calc cubeFamilyAverage I (fun R => ∫ w, F R w * H R w * H R w ∂mu)
      ≤ cubeFamilyAverage I
          (fun R => a * (∫ w, H R w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹)) :=
        cubeFamilyAverage_mono hper
    _ = a * cubeFamilyAverage I
          (fun R => (∫ w, H R w ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹)) :=
        cubeFamilyAverage_const_mul I a _
    _ ≤ a * (gridFourthMoment mu I H) ^ ((2 : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left hjensen ha0
    _ = a * (gridFourthMomentRoot mu I H) ^ (2 : ℕ) := by rw [hsq]

end Grid

/-! ## The numerical obligation of the grid fold -/

/-- **The grid fold closes at `cgamma^{10}`.**

With the ellipticity leg at `a = cgamma^{-2}` --- the `cstar^{-1}` absorption of
`LocalizationFluctuationSplitFoldArithmetic.gammaRegime_ellipticityLeg_le` --- and
the oscillation grid root at `Bosc <= cgamma^{15}` --- the full-mesh endpoints of
`e.lower.bound.oscillations` --- the cross term is `c1 cgamma^{13}` and the
quadratic term `c2 cgamma^{28}`.  Both exponents are strictly above `10`, so the
sum is below `cgamma^{10}` once `cgamma` is small, for every pair of nonnegative
**absolute** constants.

This is `LocalizationFluctuationSplitFoldArithmetic.exists_gamma_threshold_regime_holder_fold`
read at the grid route's own numerals; the threshold is **produced**, not
assumed. -/
theorem exists_gamma_threshold_gridFold (c1 c2 : ℝ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ gamma : ℝ, 0 < gamma → gamma ≤ gamma0 →
        ∀ Bosc : ℝ, 0 ≤ Bosc → Bosc ≤ gamma ^ (15 : ℕ) →
          c1 * ((gamma ^ (2 : ℕ))⁻¹ * Bosc) +
              c2 * ((gamma ^ (2 : ℕ))⁻¹ * Bosc ^ (2 : ℕ)) ≤
            gamma ^ (10 : ℕ) := by
  obtain ⟨g0, hg0pos, hg0q, hfold⟩ := exists_gamma_threshold_regime_holder_fold c1 c2 hc1 hc2
  refine ⟨g0, hg0pos, hg0q, ?_⟩
  intro gamma hgamma hle Bosc hB0 hB
  have hq : gamma ≤ 1 / 4 := hle.trans hg0q
  have hone : gamma ≤ 1 := by linarith
  have hg2 : (0 : ℝ) < gamma ^ (2 : ℕ) := by positivity
  have hg2inv : (0 : ℝ) < (gamma ^ (2 : ℕ))⁻¹ := inv_pos.2 hg2
  -- the cross leg
  have hcross : (gamma ^ (2 : ℕ))⁻¹ * Bosc ≤ gamma ^ (13 : ℕ) := by
    have hstep : (gamma ^ (2 : ℕ))⁻¹ * Bosc ≤ (gamma ^ (2 : ℕ))⁻¹ * gamma ^ (15 : ℕ) :=
      mul_le_mul_of_nonneg_left hB hg2inv.le
    have hval : (gamma ^ (2 : ℕ))⁻¹ * gamma ^ (15 : ℕ) = gamma ^ (13 : ℕ) := by
      field_simp
    rwa [hval] at hstep
  -- the quadratic leg
  have hBsq : Bosc ^ (2 : ℕ) ≤ (gamma ^ (15 : ℕ)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hB0 hB 2
  have hquad : (gamma ^ (2 : ℕ))⁻¹ * Bosc ^ (2 : ℕ) ≤ gamma ^ (28 : ℕ) := by
    have hstep : (gamma ^ (2 : ℕ))⁻¹ * Bosc ^ (2 : ℕ) ≤
        (gamma ^ (2 : ℕ))⁻¹ * (gamma ^ (15 : ℕ)) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hBsq hg2inv.le
    have hval : (gamma ^ (2 : ℕ))⁻¹ * (gamma ^ (15 : ℕ)) ^ (2 : ℕ) = gamma ^ (28 : ℕ) := by
      field_simp
    rwa [hval] at hstep
  -- the two exponents are above the fold's own numerals
  have h13 : gamma ^ (13 : ℕ) ≤ gamma ^ (12 : ℕ) :=
    pow_le_pow_of_le_one hgamma.le hone (by norm_num)
  have h28 : gamma ^ (28 : ℕ) ≤ gamma ^ (24 : ℕ) :=
    pow_le_pow_of_le_one hgamma.le hone (by norm_num)
  have hbase := hfold gamma hgamma hle
  have hc1step : c1 * ((gamma ^ (2 : ℕ))⁻¹ * Bosc) ≤ c1 * gamma ^ (12 : ℕ) :=
    mul_le_mul_of_nonneg_left (hcross.trans h13) hc1
  have hc2step : c2 * ((gamma ^ (2 : ℕ))⁻¹ * Bosc ^ (2 : ℕ)) ≤ c2 * gamma ^ (24 : ℕ) :=
    mul_le_mul_of_nonneg_left (hquad.trans h28) hc2
  linarith [hbase, hc1step, hc2step]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
