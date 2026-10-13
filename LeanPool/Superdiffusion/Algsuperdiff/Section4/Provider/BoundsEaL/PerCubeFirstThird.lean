/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.PerCubeBracket

/-!
# PerCubeFirstThird

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 5's per-cube moments: the first and third summands

## What this module does

Step 5 of `l.bounds.mathcal.E.aL` says that "the `p`-th root of the sum over `j
≤ n` of the `p/2`-th moment of the first and third terms appearing on the right side of
`e.apply.sensitivity.J.aL` is indeed bounded by the right side of
`e.bounds.mathcal.E.aL`", and treats the second and fourth terms separately,
"with additional inputs".

```
first  :  R = 4C · ( 1 + R_{B6a}(4q) R_{B5}(4q) ) · R_{B4}(4q)²
third  :  R = C  · ( σ_m^{-1} + R_{B5}(4q) )²   · R_{B6a}(4q)²
```

Both are exactly the anchor's scalar shape once the proved bullets are read:
`R_{B4}(4q)²` is `O(q s^{-2} γ)` (the printed `C s^{-1}q^{1/2}γ^{1/2}` squared,
which is the `s^{-1}√p√γ` of the anchor), and in the third term `(σ_m^{-1} +
R_{B5}) · R_{B6a}` is `O(√q √γ)` by (B3) at both indices
(`SigmaBarLandmark.exists_rpow_gamma_mul_inv_sigmaBar_sub_one_le`), so its
square is `O(q γ)`.  N summand carries a `3^{γ(m−j)}` factor: they are uniform
in the descendant scale, which is why Step 5 calls them straightforward.

The engines are the proved ones:
`MomentHolder.lintegral_rpow_mul_le_of_moments` for the two-factor Hölder,
`PerCubeBracket` for the `(1+∇k·λ^{-1})^θ` bracket, and `ℝ≥0∞` Minkowski
against a constant for the `σ_m^{-1} + λ^{-1}` slot.

## What is NOT here

The S summand.  It is the one the manuscript handles with the additional
`j`-geometric sum, and it is NOT uniform in the descendant scale.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section4.Provider.Annular
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The three summands of Step 3's display, named -/

/-- The summand of `MajorantSlots.step3DisplayAt`: the `(2,2)` homogenization error
leg. -/
def step3FirstTerm [NeZero d] (C : ℝ) (M : ABKModel d) (m : ℤ) (R : TriadicCube d)
    (omega : Cutoff.CutoffSample d) (s grad : ℝ) : ℝ :=
  C * ((Annealed.sigmaBar M m : ℝ)⁻¹ * (Annealed.sigmaBar M (R.scale - 2) : ℝ)) *
      Real.rpow (1 + grad *
          (unitCubeLambda (2 * M.gamma) (.finite 2)
            (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹)
        (2 * s / (1 - 4 * M.gamma)) *
      unitCubeHomogenizationError s (.finite 2) (.finite 2)
        (unitRescaledCutoffCoeff M R (R.scale - 2) omega)
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M (R.scale - 2))) ^ 2

/-- The S summand of `MajorantSlots.step3DisplayAt`: the `λ^{-1}`-weighted
value/ratio leg.  Named here for the decomposition only; NO moment bound for it
is asserted on this tree. -/
def step3SecondTerm (C : ℝ) (M : ABKModel d) (m : ℤ) (R : TriadicCube d)
    (omega : Cutoff.CutoffSample d) (grad val : ℝ) : ℝ :=
  C * ((Annealed.sigmaBar M m : ℝ)⁻¹ * (Annealed.sigmaBar M (R.scale - 2) : ℝ) ^ 2) *
    (unitCubeLambda (2 * M.gamma) (.finite 2)
      (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹ *
    Real.rpow (1 + grad *
        (unitCubeLambda (2 * M.gamma) (.finite 2)
          (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹)
      (4 * M.gamma / (1 - 4 * M.gamma)) *
    ((Annealed.sigmaBar M (R.scale - 2) : ℝ)⁻¹ ^ 2 * val ^ 2 +
      ((Annealed.sigmaBar M m : ℝ) * (Annealed.sigmaBar M (R.scale - 2) : ℝ)⁻¹ - 1) ^ 2)

/-- The third summand of `MajorantSlots.step3DisplayAt`: the pure gradient leg. -/
def step3ThirdTerm (C : ℝ) (M : ABKModel d) (m : ℤ) (R : TriadicCube d)
    (omega : Cutoff.CutoffSample d) (grad : ℝ) : ℝ :=
  C * (((Annealed.sigmaBar M m : ℝ)⁻¹ +
      (unitCubeLambda (2 * M.gamma) (.finite 2)
        (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹) * grad) ^ 2

/-! ## 2. Two abstract moment steps -/

/-- **The square of an observable, in the normal form.**  If `X` obeys the
development normal form at `2r`, then `X²` obeys it at `r` with the majorant
`R_X²`.  This is the step that converts the printed `(2,2)`-error and gradient
bullets (stated for the object itself) into the display's squared slots. -/
theorem lintegral_rpow_sq_le_of_moments {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {X : Omega → ℝ} {RX r : ℝ}
    (hX0 : ∀ᵐ omega ∂mu, 0 ≤ X omega) (hRX : 0 ≤ RX)
    (hX : (∫⁻ omega, ENNReal.ofReal (X omega) ^ (2 * r) ∂mu) ≤ ENNReal.ofReal RX ^ (2 * r)) :
    (∫⁻ omega, ENNReal.ofReal (X omega ^ 2) ^ r ∂mu) ≤ ENNReal.ofReal (RX ^ 2) ^ r := by
  have key : ∀ y : ℝ, 0 ≤ y →
      ENNReal.ofReal (y ^ 2) ^ r = ENNReal.ofReal y ^ (2 * r) := by
    intro y hy
    have h1 : ENNReal.ofReal (y ^ 2) = ENNReal.ofReal y ^ (2 : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hy (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]
    rw [h1, ← ENNReal.rpow_mul]
  have hae : ∀ᵐ omega ∂mu,
      ENNReal.ofReal (X omega ^ 2) ^ r = ENNReal.ofReal (X omega) ^ (2 * r) := by
    filter_upwards [hX0] with omega homega
    exact key (X omega) homega
  rw [lintegral_congr_ae hae, key RX hRX]
  exact hX

/-- **Minkowski against a deterministic shift, in the normal form.**  If `Y` obeys
the development normal form at `r ≥ 1`, so does `b + Y` for every constant `b ≥
0`, with the majorant `b + R_Y`.  This is the `σ_m^{-1} + λ^{-1}` slot of the
display's third summand. -/
theorem lintegral_rpow_const_add_le_of_moments {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {Y : Omega → ℝ} {b RY r : ℝ}
    (hr : 1 ≤ r) (hb : 0 ≤ b) (hY0 : ∀ omega, 0 ≤ Y omega) (hYm : AEMeasurable Y mu)
    (hRY : 0 ≤ RY)
    (hY : (∫⁻ omega, ENNReal.ofReal (Y omega) ^ r ∂mu) ≤ ENNReal.ofReal RY ^ r) :
    (∫⁻ omega, ENNReal.ofReal (b + Y omega) ^ r ∂mu) ≤ ENNReal.ofReal (b + RY) ^ r := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  set f : Omega → ℝ≥0∞ := fun _ => ENNReal.ofReal b with hf
  set g : Omega → ℝ≥0∞ := fun omega => ENNReal.ofReal (Y omega) with hg
  have hgm : AEMeasurable g mu := hYm.ennreal_ofReal
  have hpt : ∀ omega : Omega, ENNReal.ofReal (b + Y omega) = (f + g) omega := by
    intro omega
    rw [hf, hg]
    exact ENNReal.ofReal_add hb (hY0 omega)
  have hmink : (∫⁻ omega, (f + g) omega ^ r ∂mu) ^ (1 / r) ≤
      (∫⁻ omega, f omega ^ r ∂mu) ^ (1 / r) + (∫⁻ omega, g omega ^ r ∂mu) ^ (1 / r) :=
    ENNReal.lintegral_Lp_add_le (μ := mu) (f := f) (g := g)
      measurable_const.aemeasurable hgm hr
  have hconst : (∫⁻ omega, f omega ^ r ∂mu) ^ (1 / r) = ENNReal.ofReal b := by
    rw [hf, lintegral_const, measure_univ, mul_one, ← ENNReal.rpow_mul,
      mul_one_div_cancel (ne_of_gt hr0), ENNReal.rpow_one]
  have hgroot : (∫⁻ omega, g omega ^ r ∂mu) ^ (1 / r) ≤ ENNReal.ofReal RY := by
    refine le_trans (ENNReal.rpow_le_rpow hY (by positivity)) (le_of_eq ?_)
    rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hr0), ENNReal.rpow_one]
  have hsum : (∫⁻ omega, (f + g) omega ^ r ∂mu) ^ (1 / r) ≤ ENNReal.ofReal (b + RY) := by
    refine le_trans hmink (le_trans (add_le_add (le_of_eq hconst) hgroot) (le_of_eq ?_))
    rw [ENNReal.ofReal_add hb hRY]
  have hraise := ENNReal.rpow_le_rpow hsum hr0.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt hr0), ENNReal.rpow_one] at hraise
  refine le_trans (le_of_eq (lintegral_congr fun omega => ?_)) hraise
  rw [hpt omega]

/-- **A deterministically scaled two-factor product, in the normal form.**

The shape both of Step 3's first summand (`4C · bracket · 𝓔²`) and of its third
(`C · (σ_m^{-1}+λ^{-1})² · ∇k²`): a nonnegative observable dominated pointwise
by `b · (A · B)` with `A, B` in the normal form at the doubled exponent. -/
theorem lintegral_rpow_const_mul_mul_le_of_moments {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {F A B : Omega → ℝ} {b RA RB q : ℝ} (hq : 0 < q) (hb : 0 ≤ b)
    (hA0 : ∀ᵐ omega ∂mu, 0 ≤ A omega)
    (hAm : AEMeasurable A mu) (hBm : AEMeasurable B mu) (hRA : 0 ≤ RA)
    (hF : ∀ᵐ omega ∂mu, F omega ≤ b * (A omega * B omega))
    (hA : (∫⁻ omega, ENNReal.ofReal (A omega) ^ (2 * q) ∂mu) ≤ ENNReal.ofReal RA ^ (2 * q))
    (hB : (∫⁻ omega, ENNReal.ofReal (B omega) ^ (2 * q) ∂mu) ≤ ENNReal.ofReal RB ^ (2 * q)) :
    (∫⁻ omega, ENNReal.ofReal (F omega) ^ q ∂mu) ≤ ENNReal.ofReal (b * (RA * RB)) ^ q := by
  have hprod := lintegral_rpow_mul_le_of_moments (mu := mu)
    (X := fun omega => ENNReal.ofReal (A omega)) (Y := fun omega => ENNReal.ofReal (B omega))
    hq hAm.ennreal_ofReal hBm.ennreal_ofReal hRA hA hB
  have hpt : ∀ᵐ omega ∂mu, ENNReal.ofReal (F omega) ^ q ≤
      ENNReal.ofReal b ^ q *
        (ENNReal.ofReal (A omega) * ENNReal.ofReal (B omega)) ^ q := by
    filter_upwards [hA0, hF] with omega hA0omega hFomega
    have hstep : ENNReal.ofReal (F omega) ≤
        ENNReal.ofReal b * (ENNReal.ofReal (A omega) * ENNReal.ofReal (B omega)) := by
      refine le_trans (ENNReal.ofReal_le_ofReal hFomega) (le_of_eq ?_)
      rw [ENNReal.ofReal_mul hb, ENNReal.ofReal_mul hA0omega]
    refine le_trans (ENNReal.rpow_le_rpow hstep hq.le) (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le]
  calc (∫⁻ omega, ENNReal.ofReal (F omega) ^ q ∂mu)
      ≤ ∫⁻ omega, ENNReal.ofReal b ^ q *
          (ENNReal.ofReal (A omega) * ENNReal.ofReal (B omega)) ^ q ∂mu :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal b ^ q *
          ∫⁻ omega, (ENNReal.ofReal (A omega) * ENNReal.ofReal (B omega)) ^ q ∂mu :=
        lintegral_const_mul' _ _ (by
          exact ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal b ^ q * ENNReal.ofReal (RA * RB) ^ q := mul_le_mul' le_rfl hprod
    _ = ENNReal.ofReal (b * (RA * RB)) ^ q := by
        rw [ENNReal.ofReal_mul hb, ENNReal.mul_rpow_of_nonneg _ _ hq.le]

/-! ## 3. The three Step-4 majorants, named -/

/-- The (B5) majorant at exponent `p`, at the `λ`-slot Step 3 reads
(`LambdaSlotConsumer`). -/
def lambdaSlotMajorant (d : ℕ) (M : ABKModel d) (E : ℝ) (j : ℤ) (p : ℝ) : ℝ :=
  lambdaUpscaleConst d *
      (((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ * Support.cgEllipLowerConstant d) +
    gammaMomentBound (1 / 3) p
      (lambdaUpscaleConst d * lambdaMaxOrliczConst d *
        (((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ * Proportion.cgTailScale M E))

/-- The (B6a) majorant at exponent `p` (`StepFourMoments`). -/
def gradSlotMajorant (M : ABKModel d) (j : ℤ) (p : ℝ) : ℝ :=
  gammaTwoMomentBound p (fullGradConst M * Real.rpow 3 (M.gamma * (j : ℝ)))

/-- The (B4) majorant at exponent `p` (`StepFourMoments`), the two-lane
`(Γ₂, Γ_{1/2})` bound of the `(2,2)` homogenization error. -/
def errSlotMajorant (d : ℕ) (M : ABKModel d) (C s p : ℝ) : ℝ :=
  gammaTwoHalfMomentBound p
    (Real.sqrt 3 * (Proportion.annulusPenalty d 2 1 *
      (C * (Disorder.cstar M)⁻¹ * s⁻¹ * Real.sqrt M.gamma)))
    (Real.sqrt 3 * (Proportion.annulusPenalty d (1 / 2) 1 *
      Real.exp (-(C⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹))))

theorem lambdaSlotMajorant_nonneg (d : ℕ) (M : ABKModel d) (E : ℝ) (j : ℤ) {p : ℝ}
    (hp : 0 ≤ p) : 0 ≤ lambdaSlotMajorant d M E j p := by
  have hsig : (0 : ℝ) ≤ ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ :=
    (inv_pos.mpr (Annealed.sigmaBar M (j - 1)).2).le
  refine add_nonneg (mul_nonneg (lambdaUpscaleConst_pos d).le
    (mul_nonneg hsig (Support.cgEllipLowerConstant_pos d).le)) ?_
  refine gammaMomentBound_nonneg (by norm_num) hp ?_
  exact mul_nonneg (mul_nonneg (lambdaUpscaleConst_pos d).le (lambdaMaxOrliczConst_pos d).le)
    (mul_nonneg hsig (Proportion.cgTailScale_pos M E).le)

theorem gradSlotMajorant_nonneg (M : ABKModel d) (j : ℤ) (p : ℝ) :
    0 ≤ gradSlotMajorant M j p :=
  gammaTwoMomentBound_nonneg
    (mul_nonneg (fullGradConst_pos M).le (Real.rpow_nonneg (by norm_num) _))

/-! ## 4. The third summand -/

/-- **The third summand's `q`-th moment.**

```
∫⁻ ( C ((σ_m^{-1} + λ^{-1}) · 3^{2j}‖∇(k_L−k_{j−2})‖)² )^q
    ≤ ( ofReal ( C (σ_m^{-1} + R_{B5}(4q))² R_{B6a}(4q)² ) )^q .
```

Both factors enter at the exponent `4q` — the two-factor Hölder doubling
applied to two squares — and the majorant is uniform in the descendant scale `j =
R.scale` once (B3) is applied at both `σ` indices: `σ_m^{-1}·R_{B6a}` and
`R_{B5}·R_{B6a}` are both `O(√q √γ)`, so the whole term is `O(q γ)`, which the
anchor's `(√p (s^{-1}+√(m−n)) √γ)²` dominates.  This is one of the two summands
Step 5 calls straightforward. -/
theorem exists_lintegral_rpow_step3ThirdTerm_le (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 6 ≤ C ∧
      ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∀ Cd : ℝ, 0 ≤ Cd → ∀ (m : ℤ) (R : TriadicCube d), R.scale ≤ m →
          ∀ q : ℝ, 1 ≤ q →
            ∫⁻ omega : Cutoff.CutoffSample d,
                ENNReal.ofReal (step3ThirdTerm Cd M m R omega
                  (lFreeGradSlot m (tailSeriesGauge m) R omega)) ^ q
                ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
              ENNReal.ofReal (Cd *
                ((((Annealed.sigmaBar M m : ℝ))⁻¹ +
                    lambdaSlotMajorant d M (C * (Disorder.cstar M)⁻¹) R.scale (4 * q)) ^ 2 *
                  gradSlotMajorant M R.scale (4 * q) ^ 2)) ^ q := by
  obtain ⟨C, hC6, hall⟩ := exists_lintegral_rpow_inv_unitCubeLambda_twoGamma_le d
  refine ⟨C, hC6, ?_⟩
  intro M hreg Cd hCd m R hkm q hq
  obtain ⟨E, hEval, hlam⟩ := hall M hreg
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have h4q : (1 : ℝ) ≤ 4 * q := by linarith only [hq]
  have hsplit : (2 : ℝ) * (2 * q) = 4 * q := by ring
  have hsigm : (0 : ℝ) ≤ ((Annealed.sigmaBar M m : ℝ))⁻¹ :=
    (inv_pos.mpr (Annealed.sigmaBar M m).2).le
  have hRL : (0 : ℝ) ≤ lambdaSlotMajorant d M (E : ℝ) R.scale (4 * q) :=
    lambdaSlotMajorant_nonneg d M (E : ℝ) R.scale (by linarith only [h4q])
  have hRG : (0 : ℝ) ≤ gradSlotMajorant M R.scale (4 * q) :=
    gradSlotMajorant_nonneg M R.scale (4 * q)
  -- the two slot moments at the doubled-doubled exponent
  have hlam4 := hlam R (4 * q) h4q
  have hgrad4 := lintegral_rpow_lFreeGradSlot_le M m R hkm h4q
  have hshift : (∫⁻ omega : Cutoff.CutoffSample d,
      ENNReal.ofReal (((Annealed.sigmaBar M m : ℝ))⁻¹ +
        (unitCubeLambda (2 * M.gamma) (.finite 2)
          (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹) ^ (2 * (2 * q))
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (((Annealed.sigmaBar M m : ℝ))⁻¹ +
        lambdaSlotMajorant d M (E : ℝ) R.scale (4 * q)) ^ (2 * (2 * q)) := by
    rw [hsplit]
    exact lintegral_rpow_const_add_le_of_moments h4q hsigm
      (fun omega => inv_unitCubeLambda_twoGamma_nonneg M R omega)
      (measurable_inv_unitCubeLambda_twoGamma M R).aemeasurable hRL hlam4
  have hgradShift : (∫⁻ omega : Cutoff.CutoffSample d,
      ENNReal.ofReal (lFreeGradSlot m (tailSeriesGauge m) R omega) ^ (2 * (2 * q))
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (gradSlotMajorant M R.scale (4 * q)) ^ (2 * (2 * q)) := by
    rw [hsplit]
    exact hgrad4
  -- the two squared factors
  have hA := lintegral_rpow_sq_le_of_moments (mu := (Cutoff.cutoffSampleLaw M).toMeasure)
    (X := fun omega => ((Annealed.sigmaBar M m : ℝ))⁻¹ +
      (unitCubeLambda (2 * M.gamma) (.finite 2)
        (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹)
    (Filter.Eventually.of_forall fun omega => by
      have := inv_unitCubeLambda_twoGamma_nonneg M R omega
      linarith only [hsigm, this])
    (by linarith only [hsigm, hRL]) hshift
  have hB := lintegral_rpow_sq_le_of_moments (mu := (Cutoff.cutoffSampleLaw M).toMeasure)
    (X := fun omega => lFreeGradSlot m (tailSeriesGauge m) R omega)
    (Filter.Eventually.of_forall fun omega => lFreeGradSlot_tailSeriesGauge_nonneg m R omega)
    hRG hgradShift
  -- the product
  have hmain := lintegral_rpow_const_mul_mul_le_of_moments
    (mu := (Cutoff.cutoffSampleLaw M).toMeasure)
    (F := fun omega => step3ThirdTerm Cd M m R omega
      (lFreeGradSlot m (tailSeriesGauge m) R omega))
    (A := fun omega => (((Annealed.sigmaBar M m : ℝ))⁻¹ +
      (unitCubeLambda (2 * M.gamma) (.finite 2)
        (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹) ^ 2)
    (B := fun omega => lFreeGradSlot m (tailSeriesGauge m) R omega ^ 2)
    hq0 hCd (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    (((measurable_const.add (measurable_inv_unitCubeLambda_twoGamma M R)).pow_const 2)).aemeasurable
    (((measurable_lFreeGradSlot m (tailSeriesGauge m)
      (fun k v => measurable_tailSeriesGauge m k v) R).pow_const 2)).aemeasurable
    (by positivity)
    (Filter.Eventually.of_forall fun omega =>
      le_of_eq (by unfold step3ThirdTerm; ring))
    hA hB
  rw [hEval] at hmain
  exact hmain

/-! ## 5. The first summand -/

/-- **The first summand's `q`-th moment.**

```
∫⁻ ( C σ_m^{-1}σ_{j−2} (1 + ∇k·λ^{-1})^{2s/(1−4γ)} 𝓔_{s,2,2}² )^q
    ≤ ( ofReal ( 4C · R_bracket · R_{B4}² ) )^q .
```

The three inputs are the three proved Step-4 items, and they enter at the
exponents the two-factor Hölder doubling produces: the deterministic ratio
bullet (B1) at `4` (`StepFourSigmaBar`), the bracket at `2q`
(`PerCubeBracket.exists_lintegral_rpow_step3Bracket_le`, which itself reads
(B6a) and (B5) at `4q`), and the `(2,2)` error at `4q`
(`StepFourMoments.exists_lintegral_rpow_unitCubeHomogenizationError22_le`).

The three moment inputs are conditional API obligations, carried as
hypotheses rather than instantiated, so that each proved bullet keeps its own
constant: no constant is enlarged and no regime is merged here.

Because `R_{B4}(4q)` is the printed `C s^{-1}q^{1/2}γ^{1/2} + Cq²
e^{-C^{-1}γ^{-1}}` and `R_bracket = 1 + O(√q√γ)`
(`PerCubeBracket.step3Bracket_majorant_le`), this majorant is `O(q s^{-2} γ)`
uniformly in the descendant scale — the anchor's own `(√p s^{-1} √γ)²`. -/
theorem lintegral_rpow_step3FirstTerm_le [NeZero d] (M : ABKModel d) (m : ℤ)
    (R : TriadicCube d) {s Cd q RB RE : ℝ} (hs : 0 < s)
    (hgam : M.gamma ≤ 1 / 8) (hCd : 0 ≤ Cd) (hq : 1 ≤ q) (hRB : 0 ≤ RB) (hRE : 0 ≤ RE)
    (hratio : ((Annealed.sigmaBar M m : ℝ))⁻¹ * (Annealed.sigmaBar M (R.scale - 2) : ℝ) ≤ 4)
    (hbracket : (∫⁻ omega : Cutoff.CutoffSample d,
        ENNReal.ofReal (Real.rpow (1 +
            lFreeGradSlot m (tailSeriesGauge m) R omega *
              (unitCubeLambda (2 * M.gamma) (.finite 2)
                (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹)
          (2 * s / (1 - 4 * M.gamma))) ^ (2 * q)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal RB ^ (2 * q))
    (herr : (∫⁻ omega : Cutoff.CutoffSample d,
        ENNReal.ofReal (unitCubeHomogenizationError s (.finite 2) (.finite 2)
            (unitRescaledCutoffCoeff M R (R.scale - 2) omega)
            (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M (R.scale - 2)))) ^
          (2 * (2 * q)) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal RE ^ (2 * (2 * q))) :
    (∫⁻ omega : Cutoff.CutoffSample d,
        ENNReal.ofReal (step3FirstTerm Cd M m R omega s
          (lFreeGradSlot m (tailSeriesGauge m) R omega)) ^ q
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (4 * Cd * (RB * RE ^ 2)) ^ q := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hth0 : (0 : ℝ) ≤ 2 * s / (1 - 4 * M.gamma) := by
    have hden : (0 : ℝ) < 1 - 4 * M.gamma := by linarith only [hgam]
    exact div_nonneg (by linarith only [hs]) hden.le
  -- the a.e. nonnegativity of the literal `(2,2)` error, through the representative
  have hErr0 : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      0 ≤ unitCubeHomogenizationError s (.finite 2) (.finite 2)
        (unitRescaledCutoffCoeff M R (R.scale - 2) omega)
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M (R.scale - 2))) := by
    filter_upwards [ae_eq_annularErrorObservable_translate M R ⟨s, hs⟩] with omega homega
    rw [homega]
    exact Support.annularErrorObservable_nonneg M R.scale ⟨s, hs⟩ _
  -- the bracket base is nonnegative
  have hbase0 : ∀ omega : Cutoff.CutoffSample d, (0 : ℝ) ≤ 1 +
      lFreeGradSlot m (tailSeriesGauge m) R omega *
        (unitCubeLambda (2 * M.gamma) (.finite 2)
          (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹ := by
    intro omega
    have hmul := mul_nonneg (lFreeGradSlot_tailSeriesGauge_nonneg m R omega)
      (inv_unitCubeLambda_twoGamma_nonneg M R omega)
    linarith only [hmul]
  -- the squared error slot
  have hB := lintegral_rpow_sq_le_of_moments (mu := (Cutoff.cutoffSampleLaw M).toMeasure)
    (X := fun omega => unitCubeHomogenizationError s (.finite 2) (.finite 2)
      (unitRescaledCutoffCoeff M R (R.scale - 2) omega)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M (R.scale - 2))))
    hErr0 hRE herr
  -- the two measurabilities
  have hAm : AEMeasurable (fun omega : Cutoff.CutoffSample d =>
      Real.rpow (1 + lFreeGradSlot m (tailSeriesGauge m) R omega *
        (unitCubeLambda (2 * M.gamma) (.finite 2)
          (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹)
        (2 * s / (1 - 4 * M.gamma))) (Cutoff.cutoffSampleLaw M).toMeasure :=
    ((Real.continuous_rpow_const hth0).measurable.comp
      (measurable_const.add
        ((measurable_lFreeGradSlot m (tailSeriesGauge m)
          (fun k v => measurable_tailSeriesGauge m k v) R).mul
          (measurable_inv_unitCubeLambda_twoGamma M R)))).aemeasurable
  have hBm : AEMeasurable (fun omega : Cutoff.CutoffSample d =>
      unitCubeHomogenizationError s (.finite 2) (.finite 2)
        (unitRescaledCutoffCoeff M R (R.scale - 2) omega)
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M (R.scale - 2))) ^ 2)
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (aemeasurable_unitCubeHomogenizationError22_unitRescaledCutoffCoeff M R ⟨s, hs⟩).pow_const 2
  -- the pointwise domination: the (B1) ratio, paid deterministically
  have hF : ∀ omega : Cutoff.CutoffSample d,
      step3FirstTerm Cd M m R omega s (lFreeGradSlot m (tailSeriesGauge m) R omega) ≤
        4 * Cd * (Real.rpow (1 + lFreeGradSlot m (tailSeriesGauge m) R omega *
            (unitCubeLambda (2 * M.gamma) (.finite 2)
              (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹)
            (2 * s / (1 - 4 * M.gamma)) *
          unitCubeHomogenizationError s (.finite 2) (.finite 2)
            (unitRescaledCutoffCoeff M R (R.scale - 2) omega)
            (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M (R.scale - 2))) ^ 2) := by
    intro omega
    have hAB : (0 : ℝ) ≤ Real.rpow (1 + lFreeGradSlot m (tailSeriesGauge m) R omega *
          (unitCubeLambda (2 * M.gamma) (.finite 2)
            (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹)
          (2 * s / (1 - 4 * M.gamma)) *
        unitCubeHomogenizationError s (.finite 2) (.finite 2)
          (unitRescaledCutoffCoeff M R (R.scale - 2) omega)
          (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M (R.scale - 2))) ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (hbase0 omega) _) (sq_nonneg _)
    have hc : Cd * (((Annealed.sigmaBar M m : ℝ))⁻¹ *
        (Annealed.sigmaBar M (R.scale - 2) : ℝ)) ≤ Cd * 4 :=
      mul_le_mul_of_nonneg_left hratio hCd
    have hstep := mul_le_mul_of_nonneg_right hc hAB
    unfold step3FirstTerm
    linarith only [hstep]
  exact lintegral_rpow_const_mul_mul_le_of_moments hq0 (by linarith only [hCd])
    (Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (hbase0 omega) _)
    hAm hBm hRB (Filter.Eventually.of_forall hF) hbracket hB

end

end Algsuperdiff.Section4.Provider.BoundsEaL
