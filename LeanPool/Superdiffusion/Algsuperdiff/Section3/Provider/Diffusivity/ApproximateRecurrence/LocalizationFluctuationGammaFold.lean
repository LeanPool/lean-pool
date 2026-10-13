/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationMeshTransfer
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfacesPositiveQTwo

/-!
# LocalizationFluctuationGammaFold

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The three quantitative folds of Step 2 of `l.approximate.recurrence.formula`

ABK26, Step 2 of `l.approximate.recurrence.formula`.  After the per-cube bound
(`LocalizationFluctuationPerCube.perCube_localizationFluctuation_le`), the
ellipticity transfer
(`doubledPoincareEllipticityFactor_sq_le_descendant_gaugedEllipticitySum`)
and the oscillation/Besov bridge
(`cubeBesovPositiveVectorDepthAverage_le_descendantsAverage_sq`)
have been applied, three purely quantitative folds remain between the proved
inputs and the display `e.lower.bound.localization.terms`.  This module proves
all three, each as a standalone, unconditional statement.

## 1.  The eighth-moment envelope

```
  sqrt(d 3^{g - p}) * sqrt( avsum_{R in mesh} ( E[ (F R)^4 ] )^2 ) ,
```

and leaves the *squared* fourth-moment grid average to the consumer.  Here that
average is closed by Cauchy--Schwarz in the sample,

```
  ( E[ X^4 ] )^2  <=  E[ X^8 ]      (any probability measure) ,
```

so the remainder is controlled by the **eighth**-moment grid average -- the
quantity that `e.nablaw.in.L.eight` supplies after the per-cube Jensen step and
the mesh tiling identity.
`gridFourthMoment_mesoCubeGrid_le_interior_add_of_eighthMoment` is the composed
form.

`exists_gamma_threshold_mesh_boundary` then absorbs the geometric factor: under
the recurrence's own large-cube gate `10^10 gamma^{-1} <= K - m` the boundary
remainder is below `gamma^100`, for every prefactor, once `gamma` is small --
the machine-checked form of the manuscript's "increasing `M` in
`e.cgamma.constraints`, if necessary".

## 2.  The multi-depth geometric fold

The finite-depth positive `q = 2` Besov seminorm that the duality leg consumes is
`(sum_{j <= N} 3^{2 s j} A_j)^{1/2}` in the depth averages `A_j`.  Instantiating
the free-buffer oscillation display at buffer `Q.scale - j` bounds each `A_j` by
`(A 3^{-(B + j)})^2` with a *`j`-independent* amplitude `A` -- the display's
second and third terms carry `3^{-N} 3^{gamma (n + N)}` whose exponent
`n + N = m - h` does not move with the depth.  For `s <= 1/2` the ratio
`3^{2s - 2}` is at most `1/2`, so the depth sum is geometric and

```
  [ u ]_{B^s_{2,2}, <= N}  <=  sqrt 2 * A * 3^{-B}
```

uniformly in `N`.  That is `cubeBesovPositiveVectorPartialSeminormTwo_le_of_depthAverage_le`,
whose conclusion is exactly the envelope `Bg` of the per-cube bound.

## 3.  The annealed Hoelder fold

 ABK26 combines an ellipticity moment `C gamma^{-1}`, a load moment `C` and an
oscillation moment `C gamma^{14}` by Hoelder into `gamma^{10}`.
`integral_mul_mul_le_L4_L4_L2` is the pairing itself, at the exponents `1/4 +
1/4 + 1/2 = 1` (the quadratic summand is the case `g = h`); the resulting
numerical obligation is `c1 gamma^13 + c2 gamma^27 <= gamma^10`, which
`exists_gamma_threshold_holder_fold` discharges for every pair of nonnegative
constants once `gamma` is small -- again the manuscript's "increasing `M`".

## Auxiliary

The `descendantsAverage` form of the grid
Cauchy--Schwarz `(avsum F)^2 <= avsum F^2` is the step that passes from the grid
average of squared oscillation cells (the majorant of the Besov depth average)
to the grid average of their fourth powers, which is what
`e.lower.bound.oscillations` controls.

## Binders

Every statement below is either finite combinatorics, real arithmetic, or a
single application of Cauchy--Schwarz on a probability space.  No smallness
gate is assumed: the three `gamma`-thresholds are **produced**, not required.
Nothing about the corrector, the coefficient field or the sample space is
assumed.

## Scope

There is no `sorry`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2,
  `e.lower.bound.localization.terms`, `e.lower.bound.oscillations`,
  `e.nablaw.in.L.eight`, `e.recurrence.params`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Elementary `rpow` bookkeeping -/

private theorem gammaFold_one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  exact le_of_lt (lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num))

private theorem gammaFold_holderConjugate_two_two : (2 : ℝ).HolderConjugate 2 := by
  rw [Real.holderConjugate_iff]
  constructor <;> norm_num

/-! ## Fold 1: the eighth-moment envelope of the mesh boundary remainder -/

/-- **Cauchy--Schwarz in the sample.**  On a probability space the square of a
fourth moment is below the eighth moment.  This is the step that turns the
remainder of `gridFourthMoment_mesoCubeGrid_le_interior_add` into a consumer of
`e.nablaw.in.L.eight`.

on the nonnegativity of `f` and on the `L^2` membership of `f^4`, which is the
standing integrability of the moment being formed. -/
theorem sq_integral_rpow_four_le_integral_rpow_eight {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (f : Omega → ℝ) (hf : ∀ omega, 0 ≤ f omega)
    (hmem : MemLp (fun omega => f omega ^ (4 : ℝ)) 2 mu) :
    (∫ omega, f omega ^ (4 : ℝ) ∂mu) ^ (2 : ℕ) ≤ ∫ omega, f omega ^ (8 : ℝ) ∂mu := by
  have hofReal : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
    simp [ENNReal.ofReal_ofNat]
  have hfmem : MemLp (fun omega => f omega ^ (4 : ℝ)) (ENNReal.ofReal (2 : ℝ)) mu := by
    rwa [hofReal]
  have hgmem : MemLp (fun _ : Omega => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) mu :=
    memLp_const 1
  have hf4 : 0 ≤ᵐ[mu] fun omega => f omega ^ (4 : ℝ) :=
    Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (hf omega) _
  have hg1 : 0 ≤ᵐ[mu] fun _ : Omega => (1 : ℝ) :=
    Filter.Eventually.of_forall fun _ => zero_le_one
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg gammaFold_holderConjugate_two_two
    hf4 hg1 hfmem hgmem
  have hleft : ∫ omega, f omega ^ (4 : ℝ) * (1 : ℝ) ∂mu =
      ∫ omega, f omega ^ (4 : ℝ) ∂mu := by simp
  have hmid : ∀ omega, (f omega ^ (4 : ℝ)) ^ (2 : ℝ) = f omega ^ (8 : ℝ) := by
    intro omega
    rw [← Real.rpow_mul (hf omega)]
    norm_num
  have hright : ∫ _omega : Omega, ((1 : ℝ)) ^ (2 : ℝ) ∂mu = 1 := by simp
  rw [hleft] at hholder
  simp only [hmid] at hholder
  rw [hright] at hholder
  have h8nn : (0 : ℝ) ≤ ∫ omega, f omega ^ (8 : ℝ) ∂mu :=
    integral_nonneg fun omega => Real.rpow_nonneg (hf omega) _
  have hstep : ∫ omega, f omega ^ (4 : ℝ) ∂mu ≤
      (∫ omega, f omega ^ (8 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) := by simpa using hholder
  have hsq : ((∫ omega, f omega ^ (8 : ℝ) ∂mu) ^ (1 / (2 : ℝ))) ^ (2 : ℕ) =
      ∫ omega, f omega ^ (8 : ℝ) ∂mu := by
    rw [← Real.rpow_natCast ((∫ omega, f omega ^ (8 : ℝ) ∂mu) ^ (1 / (2 : ℝ))) 2,
      ← Real.rpow_mul h8nn]
    norm_num
  have h4nn : (0 : ℝ) ≤ ∫ omega, f omega ^ (4 : ℝ) ∂mu :=
    integral_nonneg fun omega => Real.rpow_nonneg (hf omega) _
  calc (∫ omega, f omega ^ (4 : ℝ) ∂mu) ^ (2 : ℕ)
      ≤ ((∫ omega, f omega ^ (8 : ℝ) ∂mu) ^ (1 / (2 : ℝ))) ^ (2 : ℕ) :=
        pow_le_pow_left₀ h4nn hstep 2
    _ = ∫ omega, f omega ^ (8 : ℝ) ∂mu := hsq

/-- The grid form of the previous statement: the squared fourth-moment grid
average that the mesh transfer leaves open is below the eighth-moment grid
average. -/
theorem cubeFamilyAverage_sq_integral_rpow_four_le_eighth {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (I : Finset (TriadicCube d)) (F : TriadicCube d → Omega → ℝ)
    (hF : ∀ R omega, 0 ≤ F R omega)
    (hmem : ∀ R ∈ I, MemLp (fun omega => F R omega ^ (4 : ℝ)) 2 mu) :
    cubeFamilyAverage I (fun R => (∫ omega, F R omega ^ (4 : ℝ) ∂mu) ^ (2 : ℕ)) ≤
      cubeFamilyAverage I (fun R => ∫ omega, F R omega ^ (8 : ℝ) ∂mu) := by
  unfold cubeFamilyAverage
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun R hR => ?_) (by positivity)
  exact sq_integral_rpow_four_le_integral_rpow_eight mu (F R) (fun omega => hF R omega)
    (hmem R hR)

/-- **The mesh transfer, closed against an eighth-moment envelope.**  The
full-mesh fourth-moment average of `e.lower.bound.oscillations` is the interior
one plus a geometric boundary remainder carrying the square root of any
envelope `E` of the *eighth*-moment grid average -- which is exactly what
`e.nablaw.in.L.eight` supplies after the per-cube Jensen step and the mesh
tiling identity.

on the scale bookkeeping, the nonnegativity of `F`, the standing `L^2`
membership of the fourth powers, and the envelope `hE`. -/
theorem gridFourthMoment_mesoCubeGrid_le_interior_add_of_eighthMoment {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu] (d : ℕ)
    {K n outer : ℤ} {p g : ℕ} (hK : K = n + (p : ℤ)) (houter : outer + 1 = n + (g : ℤ))
    (hgp : g ≤ p) (F : TriadicCube d → Omega → ℝ) (hF : ∀ R omega, 0 ≤ F R omega)
    (hmem : ∀ R ∈ mesoCubeGrid d K n, MemLp (fun omega => F R omega ^ (4 : ℝ)) 2 mu)
    {E : ℝ} (hE : cubeFamilyAverage (mesoCubeGrid d K n)
      (fun R => ∫ omega, F R omega ^ (8 : ℝ) ∂mu) ≤ E) :
    gridFourthMoment mu (mesoCubeGrid d K n) F ≤
      gridFourthMoment mu (interiorMesoCubeGrid d K n outer) F +
        Real.sqrt ((d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p)) * Real.sqrt E := by
  have hmain := gridFourthMoment_mesoCubeGrid_le_interior_add mu d hK houter hgp F
  have hCS := cubeFamilyAverage_sq_integral_rpow_four_le_eighth mu (mesoCubeGrid d K n) F
    hF hmem
  have hroot : Real.sqrt (cubeFamilyAverage (mesoCubeGrid d K n)
      (fun R => (∫ omega, F R omega ^ (4 : ℝ) ∂mu) ^ 2)) ≤ Real.sqrt E :=
    Real.sqrt_le_sqrt (hCS.trans hE)
  have hfrac : (0 : ℝ) ≤ Real.sqrt ((d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p)) :=
    Real.sqrt_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hroot hfrac
  linarith [hmain, hmul]

/-! ## Fold 1, continued: absorbing the boundary factor into a power of `gamma` -/

/-- The boundary geometric factor of the mesh transfer, in `rpow` form. -/
private theorem gammaFold_sqrt_ratio_eq (d p g : ℕ) :
    Real.sqrt ((d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p)) =
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(((p : ℝ) - (g : ℝ)) / 2)) := by
  rw [Real.sqrt_mul (Nat.cast_nonneg d)]
  congr 1
  have hratio : (3 : ℝ) ^ g / (3 : ℝ) ^ p = (3 : ℝ) ^ ((g : ℝ) - (p : ℝ)) := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 3), Real.rpow_natCast, Real.rpow_natCast]
  rw [hratio, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- Polynomial beats exponential at the recurrence gate, half-power form. -/
private theorem gammaFold_half_gap_le_gammaPow_mul_spare {gamma G : ℝ} (hgamma : 0 < gamma)
    (hquarter : gamma ≤ 1 / 4) (hG : (10 : ℝ) ^ (10 : ℕ) * gamma⁻¹ ≤ G) :
    (3 : ℝ) ^ (-(G / 2)) ≤
      gamma ^ (100 : ℕ) * (3 : ℝ) ^ (-((10 : ℝ) ^ (9 : ℕ)) * gamma⁻¹) := by
  set t : ℝ := gamma⁻¹ with htdef
  have ht4 : (4 : ℝ) ≤ t := by
    rw [htdef, le_inv_comm₀ (by norm_num) hgamma]
    linarith
  have htpos : (0 : ℝ) < t := by linarith
  have hexp : -(G / 2) ≤ -((5 : ℝ) * 10 ^ (9 : ℕ)) * t := by
    have h1 : (10 : ℝ) ^ (10 : ℕ) * t ≤ G := hG
    nlinarith [h1, htpos]
  have hstep1 : (3 : ℝ) ^ (-(G / 2)) ≤ (3 : ℝ) ^ (-((5 : ℝ) * 10 ^ (9 : ℕ)) * t) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hsplit : (3 : ℝ) ^ (-((5 : ℝ) * 10 ^ (9 : ℕ)) * t) =
      (3 : ℝ) ^ (-((4 : ℝ) * 10 ^ (9 : ℕ)) * t) *
        (3 : ℝ) ^ (-((10 : ℝ) ^ (9 : ℕ)) * t) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  have hpoly : (3 : ℝ) ^ (-((4 : ℝ) * 10 ^ (9 : ℕ)) * t) ≤ gamma ^ (100 : ℕ) := by
    have hgpow : (0 : ℝ) < gamma ^ (100 : ℕ) := by positivity
    have hlhs : (0 : ℝ) < (3 : ℝ) ^ (-((4 : ℝ) * 10 ^ (9 : ℕ)) * t) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rw [← Real.exp_log hlhs, ← Real.exp_log hgpow]
    refine Real.exp_le_exp.mpr ?_
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 3), Real.log_pow]
    have hloggamma : Real.log gamma = -Real.log t := by
      rw [htdef, Real.log_inv, neg_neg]
    rw [hloggamma]
    have hlogt : Real.log t ≤ t := by
      have := Real.log_le_sub_one_of_pos htpos
      linarith
    have hlogtnn : (0 : ℝ) ≤ Real.log t := Real.log_nonneg (by linarith)
    have hmul : t * 1 ≤ t * Real.log 3 :=
      mul_le_mul_of_nonneg_left gammaFold_one_le_log_three htpos.le
    push_cast
    nlinarith [hlogt, hlogtnn, htpos, hmul]
  calc (3 : ℝ) ^ (-(G / 2))
      ≤ (3 : ℝ) ^ (-((5 : ℝ) * 10 ^ (9 : ℕ)) * t) := hstep1
    _ = (3 : ℝ) ^ (-((4 : ℝ) * 10 ^ (9 : ℕ)) * t) *
          (3 : ℝ) ^ (-((10 : ℝ) ^ (9 : ℕ)) * t) := hsplit
    _ ≤ gamma ^ (100 : ℕ) * (3 : ℝ) ^ (-((10 : ℝ) ^ (9 : ℕ)) * t) :=
        mul_le_mul_of_nonneg_right hpoly (Real.rpow_pos_of_pos (by norm_num) _).le

/-- Every constant is below the spare factor `3^{10^9 / gamma}` once `gamma` is
small.  The quantitative form of "increasing `M` in `e.cgamma.constraints`". -/
private theorem gammaFold_exists_threshold_spare (C : ℝ) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ gamma : ℝ, 0 < gamma → gamma ≤ gamma0 →
        C ≤ (3 : ℝ) ^ ((10 : ℝ) ^ (9 : ℕ) * gamma⁻¹) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, C < (3 : ℝ) ^ N :=
    ((tendsto_pow_atTop_atTop_of_one_lt (r := (3 : ℝ)) (by norm_num)).eventually_gt_atTop
      C).exists
  refine ⟨min (1 / 4) ((10 : ℝ) ^ (9 : ℕ) / ((N : ℝ) + 1)), ?_, min_le_left _ _, ?_⟩
  · have hpos : (0 : ℝ) < (10 : ℝ) ^ (9 : ℕ) / ((N : ℝ) + 1) := by positivity
    exact lt_min (by norm_num) hpos
  · intro gamma hgamma hle
    have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hbound : gamma ≤ (10 : ℝ) ^ (9 : ℕ) / ((N : ℝ) + 1) := hle.trans (min_le_right _ _)
    have hmul : gamma * ((N : ℝ) + 1) ≤ (10 : ℝ) ^ (9 : ℕ) := (le_div_iff₀ hNpos).mp hbound
    have hexp : ((N : ℕ) : ℝ) ≤ (10 : ℝ) ^ (9 : ℕ) * gamma⁻¹ := by
      have hinvpos : (0 : ℝ) < gamma⁻¹ := inv_pos.2 hgamma
      have hstep : gamma⁻¹ * (gamma * ((N : ℝ) + 1)) ≤ gamma⁻¹ * (10 : ℝ) ^ (9 : ℕ) :=
        mul_le_mul_of_nonneg_left hmul hinvpos.le
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hgamma), one_mul] at hstep
      nlinarith [hstep]
    have hmono : ((3 : ℝ) ^ N : ℝ) ≤ (3 : ℝ) ^ ((10 : ℝ) ^ (9 : ℕ) * gamma⁻¹) := by
      rw [← Real.rpow_natCast (3 : ℝ) N]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    linarith [hN, hmono]

/-- **The boundary remainder is below every power of `gamma`.**  Under the
recurrence's own large-cube gate, read on the mesh as `10^10 gamma^{-1} <= p -
g` with `p = K - n` the mesh depth and `g = (m-h) - n` the window gap, the
geometric boundary factor of the mesh transfer, times any prefactor `C >= 0`,
is at most `gamma^100` once `gamma` is small.

The threshold is **produced**, not assumed: this is the machine-checked form of
the manuscript's "for a sufficiently large choice of `M` in
`e.cgamma.constraints`". -/
theorem exists_gamma_threshold_mesh_boundary (d : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ gamma : ℝ, 0 < gamma → gamma ≤ gamma0 →
        ∀ p g : ℕ, (10 : ℝ) ^ (10 : ℕ) * gamma⁻¹ ≤ (p : ℝ) - (g : ℝ) →
          C * Real.sqrt ((d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p)) ≤ gamma ^ (100 : ℕ) := by
  have hCd : (0 : ℝ) ≤ C * Real.sqrt (d : ℝ) := mul_nonneg hC (Real.sqrt_nonneg _)
  obtain ⟨gamma0, hpos, hquarter, hthr⟩ :=
    gammaFold_exists_threshold_spare (C * Real.sqrt (d : ℝ))
  refine ⟨gamma0, hpos, hquarter, ?_⟩
  intro gamma hgamma hle p g hgap
  have hq : gamma ≤ 1 / 4 := hle.trans hquarter
  have hgapfac := gammaFold_half_gap_le_gammaPow_mul_spare (G := (p : ℝ) - (g : ℝ))
    hgamma hq hgap
  have hsparepos : (0 : ℝ) < (3 : ℝ) ^ ((10 : ℝ) ^ (9 : ℕ) * gamma⁻¹) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hinv : (3 : ℝ) ^ (-((10 : ℝ) ^ (9 : ℕ)) * gamma⁻¹) =
      ((3 : ℝ) ^ ((10 : ℝ) ^ (9 : ℕ) * gamma⁻¹))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    ring_nf
  have habsorb : (C * Real.sqrt (d : ℝ)) *
      (3 : ℝ) ^ (-((10 : ℝ) ^ (9 : ℕ)) * gamma⁻¹) ≤ 1 := by
    rw [hinv, mul_inv_le_iff₀ hsparepos, one_mul]
    exact hthr gamma hgamma hle
  rw [gammaFold_sqrt_ratio_eq d p g]
  calc C * (Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(((p : ℝ) - (g : ℝ)) / 2)))
      = (C * Real.sqrt (d : ℝ)) * (3 : ℝ) ^ (-(((p : ℝ) - (g : ℝ)) / 2)) := by ring
    _ ≤ (C * Real.sqrt (d : ℝ)) *
          (gamma ^ (100 : ℕ) * (3 : ℝ) ^ (-((10 : ℝ) ^ (9 : ℕ)) * gamma⁻¹)) :=
        mul_le_mul_of_nonneg_left hgapfac hCd
    _ = ((C * Real.sqrt (d : ℝ)) * (3 : ℝ) ^ (-((10 : ℝ) ^ (9 : ℕ)) * gamma⁻¹)) *
          gamma ^ (100 : ℕ) := by ring
    _ ≤ 1 * gamma ^ (100 : ℕ) := mul_le_mul_of_nonneg_right habsorb (by positivity)
    _ = gamma ^ (100 : ℕ) := one_mul _

/-! ## Fold 3: the annealed Hoelder fold -/

/-- **The three-factor Hoelder inequality in `L^4 x L^4 x L^2`.**  This is the
pairing the manuscript uses: the ellipticity moment, the load moment and the
oscillation moment enter at the exponents `1/4 + 1/4 + 1/2 = 1`.  Taking `g =
h` gives the quadratic term of `e.lower.bound.localization.terms`.

: the four `L^2` memberships are the analytic side conditions of the two
Cauchy--Schwarz steps and are caller obligations; they are not premises of the
pinned source statement. -/
theorem integral_mul_mul_le_L4_L4_L2 {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (f g h : Omega → ℝ)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w) (hh : ∀ w, 0 ≤ h w)
    (hfm : MemLp (fun w => f w ^ (2 : ℝ)) (ENNReal.ofReal 2) mu)
    (hgm : MemLp (fun w => g w ^ (2 : ℝ)) (ENNReal.ofReal 2) mu)
    (hhm : MemLp h (ENNReal.ofReal 2) mu)
    (hfgm : MemLp (fun w => f w * g w) (ENNReal.ofReal 2) mu) :
    ∫ w, f w * g w * h w ∂mu ≤
      (∫ w, f w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) *
        (∫ w, g w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) *
        (∫ w, h w ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) := by
  have hfg0 : 0 ≤ᵐ[mu] fun w => f w * g w :=
    Filter.Eventually.of_forall fun w => mul_nonneg (hf w) (hg w)
  have hh0 : 0 ≤ᵐ[mu] h := Filter.Eventually.of_forall hh
  have hf20 : 0 ≤ᵐ[mu] fun w => f w ^ (2 : ℝ) :=
    Filter.Eventually.of_forall fun w => Real.rpow_nonneg (hf w) _
  have hg20 : 0 ≤ᵐ[mu] fun w => g w ^ (2 : ℝ) :=
    Filter.Eventually.of_forall fun w => Real.rpow_nonneg (hg w) _
  have H1 := integral_mul_le_Lp_mul_Lq_of_nonneg gammaFold_holderConjugate_two_two hfg0
    hh0 hfgm hhm
  have H2 := integral_mul_le_Lp_mul_Lq_of_nonneg gammaFold_holderConjugate_two_two hf20
    hg20 hfm hgm
  have hsplit : ∀ w, (f w * g w) ^ (2 : ℝ) = f w ^ (2 : ℝ) * g w ^ (2 : ℝ) := fun w =>
    Real.mul_rpow (hf w) (hg w)
  have hf4 : ∀ w, (f w ^ (2 : ℝ)) ^ (2 : ℝ) = f w ^ (4 : ℝ) := by
    intro w; rw [← Real.rpow_mul (hf w)]; norm_num
  have hg4 : ∀ w, (g w ^ (2 : ℝ)) ^ (2 : ℝ) = g w ^ (4 : ℝ) := by
    intro w; rw [← Real.rpow_mul (hg w)]; norm_num
  simp only [hsplit] at H1
  simp only [hf4, hg4] at H2
  have hI4f : (0 : ℝ) ≤ ∫ w, f w ^ (4 : ℝ) ∂mu :=
    integral_nonneg fun w => Real.rpow_nonneg (hf w) _
  have hI4g : (0 : ℝ) ≤ ∫ w, g w ^ (4 : ℝ) ∂mu :=
    integral_nonneg fun w => Real.rpow_nonneg (hg w) _
  have hI2h : (0 : ℝ) ≤ ∫ w, h w ^ (2 : ℝ) ∂mu :=
    integral_nonneg fun w => Real.rpow_nonneg (hh w) _
  have hInner : (0 : ℝ) ≤ ∫ w, f w ^ (2 : ℝ) * g w ^ (2 : ℝ) ∂mu :=
    integral_nonneg fun w =>
      mul_nonneg (Real.rpow_nonneg (hf w) _) (Real.rpow_nonneg (hg w) _)
  have hhalf : (∫ w, f w ^ (2 : ℝ) * g w ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) ≤
      (∫ w, f w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) *
        (∫ w, g w ^ (4 : ℝ) ∂mu) ^ (1 / (4 : ℝ)) := by
    have hmono := Real.rpow_le_rpow hInner H2 (by norm_num : (0 : ℝ) ≤ 1 / (2 : ℝ))
    refine hmono.trans (le_of_eq ?_)
    rw [Real.mul_rpow (Real.rpow_nonneg hI4f _) (Real.rpow_nonneg hI4g _),
      ← Real.rpow_mul hI4f, ← Real.rpow_mul hI4g]
    norm_num
  have hmul := mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg hI2h (1 / (2 : ℝ)))
  refine H1.trans ?_
  simpa using hmul

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
