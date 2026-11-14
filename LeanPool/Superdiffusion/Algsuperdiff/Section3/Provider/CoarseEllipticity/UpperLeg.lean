/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffMultiscaleEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.OneSidedOrlicz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.CutoffBaseTailArithmetic
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.PlateauLandmarks
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.GridDominationEndpoint
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxUpperPerDescendant
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperFiniteQGeTwoInfinityAggregation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperFiniteQLtTwoAggregation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.WaveBandMean
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.DiscountBounds

/-!
# UpperLeg

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Upper coarse-ellipticity leg

This module provides the direct upper leg consumed by
`coarse_ellipticity_bounds_of_legs`.  Its public result
`superposedFlux_coarse_ellipticity_upper_leg` chooses one dimension-only
constant before the model, scale, exponent, and window data and returns the
literal upper Orlicz carrier of the frozen theorem.

The proof has two branches.  For `m ≤ mStarStar M`,
`coarse_ellipticity_upper_of_le_mStarStar` uses the base-case cutoff-mass
estimate.  For `mStarStar M < m`, the twelve analytic lanes are constructed
per descendant and then aggregated separately for finite exponents below two
and for finite exponents at least two together with infinity.  The deep-band
mean enters the deterministic shift; it is not hidden in the ordinary Orlicz
lane.

No caller supplies an upper estimate, summability assertion, measurability
assertion, or packaged fraction of the conclusion to the final theorem.

## References

* ABK26, `p.cg.ellipticity.bounds`, statement and proof.
* ABK26, `e.basecase.homogenization`.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Scales

/-- The dimension-dependent budget for the rare coarse-ellipticity contribution. -/
noncomputable def coarseEllipticityRareBudgetConst (d : ℕ) : ℝ := 4 *
  upperAfterBandRareTriangleConst ^ 2 * (1658880 : ℝ) ^ 2 *
    upperAfterBandRareGridNetConst d

/-- A common constant joining the upper coarse-ellipticity estimates. -/
noncomputable def coarseEllipticityUpperMergeConst (d : ℕ) : ℝ :=
  max 4 (max
    (147456 * HCPolySupport.IndependentSums.gammaTriangleConst 1 *
      gridNetConst d 1)
    (max
      (1152 * triadicJointDepthEntropyConst d)
      ((12 * upperAfterBandRareTriangleConst) *
        coarseEllipticityRareBudgetConst d + 15)))

private theorem coarseEllipticityRareBudgetConst_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < coarseEllipticityRareBudgetConst d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd)
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [coarseEllipticityRareBudgetConst, upperAfterBandRareTriangleConst,
    upperAfterBandRareGridNetConst]
  positivity

private theorem coarseEllipticity_rawRareScale_le_normalized {d : ℕ} (hd : 2 ≤ d)
    {Clane Cup X gamma : ℝ} (hClane : 0 < Clane) (hCup : 0 < Cup)
    (hX : Cup ≤ X)
    (hchoice :
      (12 * upperAfterBandRareTriangleConst) *
          coarseEllipticityRareBudgetConst d + 15 ≤ Clane⁻¹ * Cup)
    (k : ℕ) :
    (12 * upperAfterBandRareTriangleConst) *
        ((3 : ℝ) ^ (gamma * ((k : ℝ) + 1)) *
          Real.exp (-(Clane⁻¹ * X)) ^ 8) ≤
      (coarseEllipticityRareBudgetConst d)⁻¹ *
        ((3 : ℝ) ^ (gamma * ((k : ℝ) + 1)) *
          Real.exp (-(Cup⁻¹ * X)) ^ 15) := by
  let K : ℝ := 12 * upperAfterBandRareTriangleConst
  let lane : ℝ := Real.exp (-(Clane⁻¹ * X))
  let frozen : ℝ := Real.exp (-(Cup⁻¹ * X))
  have hR : 0 < coarseEllipticityRareBudgetConst d :=
    coarseEllipticityRareBudgetConst_pos hd
  have hK : 0 ≤ K := by
    dsimp only [K]
    rw [upperAfterBandRareTriangleConst]
    positivity
  have hX0 : 0 ≤ X := hCup.le.trans hX
  have hlane1 : lane ≤ 1 := by
    dsimp only [lane]
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg (inv_nonneg.mpr hClane.le) hX0)
  have hlanePow : lane ^ 8 ≤ lane := by
    simpa only [pow_one] using pow_le_pow_of_le_one (Real.exp_pos _).le hlane1
      (by norm_num : 1 ≤ 8)
  have htotal : (K * coarseEllipticityRareBudgetConst d) * lane ≤ frozen ^ 15 := by
    simpa only [K, lane, frozen] using
      prefactor_mul_exp_le_frozenRare_pow
        (K := K * coarseEllipticityRareBudgetConst d) (c := Clane⁻¹)
        (C := Cup) (X := X) (p := 15) (mul_nonneg hK hR.le) hCup hX hchoice
  have hnormalized : K * lane ^ 8 ≤
      (coarseEllipticityRareBudgetConst d)⁻¹ * frozen ^ 15 := by
    calc
      K * lane ^ 8 ≤ K * lane := mul_le_mul_of_nonneg_left hlanePow hK
      _ = (coarseEllipticityRareBudgetConst d)⁻¹ *
          ((K * coarseEllipticityRareBudgetConst d) * lane) := by field_simp [hR.ne']
      _ ≤ (coarseEllipticityRareBudgetConst d)⁻¹ * frozen ^ 15 :=
        mul_le_mul_of_nonneg_left htotal (inv_nonneg.mpr hR.le)
  calc
    K * ((3 : ℝ) ^ (gamma * ((k : ℝ) + 1)) * lane ^ 8) =
        (3 : ℝ) ^ (gamma * ((k : ℝ) + 1)) * (K * lane ^ 8) := by ring
    _ ≤ (3 : ℝ) ^ (gamma * ((k : ℝ) + 1)) *
        ((coarseEllipticityRareBudgetConst d)⁻¹ * frozen ^ 15) :=
      mul_le_mul_of_nonneg_left hnormalized (Real.rpow_nonneg (by norm_num) _)
    _ = (coarseEllipticityRareBudgetConst d)⁻¹ *
        ((3 : ℝ) ^ (gamma * ((k : ℝ) + 1)) * frozen ^ 15) := by ring

/-! ## 1. The model-free split constructor -/

private theorem finiteEllipticity_weightedTerm_le_infinityBound :
    ∀ {d : ℕ} (Q : TriadicCube d)
      (a : Ch02.TriadicCoeffFamily d) {s q : ℝ},
      let H : ℕ → ℝ := fun (n : ℕ) => Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (↑n : ℤ)) a;
      let V : ℝ := Ch02.LambdaSq Q (s / (2 : ℝ)) Ch02.MultiscaleExponent.infinity a;
      (0 : ℝ) < q →
        (0 : ℝ) < s / (2 : ℝ) →
          (∀ (n : ℕ), (0 : ℝ) ≤ H n) →
            (∀ (n : ℕ), Real.rpow (3 : ℝ) (-s * (↑n : ℝ)) * H n ≤ V) →
              Ch02.geometricDiscount s q ≤ (2 : ℝ) * Ch02.geometricDiscount (s / (2 : ℝ)) q →
                ∀ (n : ℕ),
                  Ch02.geometricWeight s q n * (H n).rpow (q / (2 : ℝ)) ≤
                    (2 : ℝ) * Ch02.geometricWeight (s / (2 : ℝ)) q n * V.rpow (q / (2 : ℝ)) := by
  intro _ _ a s q H V hqpos hhalf hHnonneg hendpoint hdiscount n
  have hbase0 : 0 ≤ Real.rpow (3 : ℝ) (-s * (n : ℝ)) * H n :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hHnonneg n)
  have hpow :
      Real.rpow (Real.rpow (3 : ℝ) (-s * (n : ℝ)) * H n) (q / 2) ≤
        Real.rpow V (q / 2) :=
    Real.rpow_le_rpow hbase0 (hendpoint n)
      (div_nonneg hqpos.le (by norm_num))
  have hdepth :
      Real.rpow (3 : ℝ) (-s * q * (n : ℝ)) * Real.rpow (H n) (q / 2) =
        Real.rpow (3 : ℝ) (-(s / 2) * q * (n : ℝ)) *
          Real.rpow
            (Real.rpow (3 : ℝ) (-s * (n : ℝ)) * H n) (q / 2) := by
    symm
    calc
      Real.rpow (3 : ℝ) (-(s / 2) * q * (n : ℝ)) *
          Real.rpow
            (Real.rpow (3 : ℝ) (-s * (n : ℝ)) * H n) (q / 2) =
        Real.rpow (3 : ℝ) (-(s / 2) * q * (n : ℝ)) *
          (Real.rpow (Real.rpow (3 : ℝ) (-s * (n : ℝ))) (q / 2) *
            Real.rpow (H n) (q / 2)) := by
              have hraw0 : 0 ≤ Real.rpow (3 : ℝ) (-s * (n : ℝ)) :=
                Real.rpow_nonneg (by norm_num) _
              have hmulpow :
                  Real.rpow
                      (Real.rpow (3 : ℝ) (-s * (n : ℝ)) * H n) (q / 2) =
                    Real.rpow (Real.rpow (3 : ℝ) (-s * (n : ℝ))) (q / 2) *
                      Real.rpow (H n) (q / 2) :=
                Real.mul_rpow hraw0 (hHnonneg n)
              exact congrArg
                (fun z : ℝ => Real.rpow (3 : ℝ) (-(s / 2) * q * (n : ℝ)) * z)
                hmulpow
      _ = Real.rpow (3 : ℝ) (-(s / 2) * q * (n : ℝ)) *
          (Real.rpow (3 : ℝ) ((-s * (n : ℝ)) * (q / 2)) *
            Real.rpow (H n) (q / 2)) := by
              have hrpowmul :=
                (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)
                  (-s * (n : ℝ)) (q / 2)).symm
              exact congrArg
                (fun z : ℝ => Real.rpow (3 : ℝ) (-(s / 2) * q * (n : ℝ)) *
                  (z * Real.rpow (H n) (q / 2))) hrpowmul
      _ = (Real.rpow (3 : ℝ) (-(s / 2) * q * (n : ℝ)) *
            Real.rpow (3 : ℝ) ((-s * (n : ℝ)) * (q / 2))) *
          Real.rpow (H n) (q / 2) := by ring
      _ = Real.rpow (3 : ℝ)
            (-(s / 2) * q * (n : ℝ) + (-s * (n : ℝ)) * (q / 2)) *
          Real.rpow (H n) (q / 2) := by
              have hadd :=
                (Real.rpow_add (by norm_num : (0 : ℝ) < 3)
                  (-(s / 2) * q * (n : ℝ))
                  ((-s * (n : ℝ)) * (q / 2))).symm
              exact congrArg (fun z : ℝ => z * Real.rpow (H n) (q / 2)) hadd
      _ = Real.rpow (3 : ℝ) (-s * q * (n : ℝ)) *
          Real.rpow (H n) (q / 2) := by
              congr 2
              ring
  rw [Ch02.geometricWeight, Ch02.geometricWeight]
  have hweight0 : 0 ≤ Real.rpow (3 : ℝ) (-(s / 2) * q * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hhalfdisc0 : 0 ≤ Ch02.geometricDiscount (s / 2) q := by
    simpa [Ch02.geometricDiscount_eq_old] using
      HCPolySupport.geometricDiscount_nonneg (mul_nonneg hhalf.le hqpos.le)
  calc
    Ch02.geometricDiscount s q *
        Real.rpow (3 : ℝ) (-s * q * (n : ℝ)) * Real.rpow (H n) (q / 2) =
      Ch02.geometricDiscount s q *
        (Real.rpow (3 : ℝ) (-s * q * (n : ℝ)) *
          Real.rpow (H n) (q / 2)) := by ring
    _ = Ch02.geometricDiscount s q *
        (Real.rpow (3 : ℝ) (-(s / 2) * q * (n : ℝ)) *
          Real.rpow
            (Real.rpow (3 : ℝ) (-s * (n : ℝ)) * H n) (q / 2)) := by
        rw [hdepth]
    _ ≤ (2 * Ch02.geometricDiscount (s / 2) q) *
        (Real.rpow (3 : ℝ) (-(s / 2) * q * (n : ℝ)) *
          Real.rpow
            (Real.rpow (3 : ℝ) (-s * (n : ℝ)) * H n) (q / 2)) := by
        exact mul_le_mul_of_nonneg_right hdiscount
          (mul_nonneg hweight0 (Real.rpow_nonneg hbase0 _))
    _ ≤ (2 * Ch02.geometricDiscount (s / 2) q) *
        (Real.rpow (3 : ℝ) (-(s / 2) * q * (n : ℝ)) *
          Real.rpow V (q / 2)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow hweight0)
          (mul_nonneg (by norm_num) hhalfdisc0)
    _ = 2 *
        (Ch02.geometricDiscount (s / 2) q *
          Real.rpow (3 : ℝ) (-(s / 2) * q * (n : ℝ))) *
        Real.rpow V (q / 2) := by ring

/-- A pointwise three-term split with a deterministic first summand is the
source's `X ≤ b + O_{Gamma_{sigma1}}(A1) + O_{Gamma_{sigma2}}(A2)`.

This is the only probabilistic step of the leg's reduction: the mean-split route
produces its output as `Udet + U1 + Uexp` with `Udet` deterministic, and this
lemma is what turns that into the frozen carrier. -/
theorem isDeterministicShiftTwoTermOneSidedOrlicz_of_split {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {sigma1 sigma2 : ℝ}
    {X Udet U1 Uexp : Ω → ℝ} {b A1 A2 : ℝ}
    (hsigma1 : 0 < sigma1) (hsigma2 : 0 < sigma2) (hA1 : 0 < A1) (hA2 : 0 < A2)
    (hXmeas : Measurable X) (h1m : Measurable U1) (hexpm : Measurable Uexp)
    (hdom : ∀ omega, X omega ≤ Udet omega + U1 omega + Uexp omega)
    (hdet : ∀ omega, Udet omega ≤ b)
    (h1 : HCPolySupport.IndependentSums.IsBigOWith μ
      (HCPolySupport.IndependentSums.gammaSigma sigma1) U1 A1)
    (hexp : HCPolySupport.IndependentSums.IsBigOWith μ
      (HCPolySupport.IndependentSums.gammaSigma sigma2) Uexp A2) :
    Probability.IsDeterministicShiftTwoTermOneSidedOrlicz μ
      (HCPolySupport.IndependentSums.gammaSigma sigma1)
      (HCPolySupport.IndependentSums.gammaSigma sigma2) X b A1 A2 := by
  rw [Probability.deterministicShiftTwoTermOneSidedOrlicz_iff_exists]
  refine ⟨U1, Uexp, Probability.isAdmissibleTail_gammaSigma hsigma1,
    Probability.isAdmissibleTail_gammaSigma hsigma2, hA1, hA2, hXmeas, h1m, hexpm,
    ?_, h1, hexp⟩
  intro omega
  have hd := hdom omega
  have hb := hdet omega
  linarith

/-! ## 2. Direct small-scale branch -/

private theorem LambdaSq_finite_le_four_mul_infinity_half {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : Ch02.TriadicCoeffFamily d) {s q : ℝ}
    (hs : 0 < s) (hq : 1 ≤ q) :
    Ch02.LambdaSq Q s (.finite q) a ≤
      4 * Ch02.LambdaSq Q (s / 2) .infinity a := by
  let H : ℕ → ℝ := fun n =>
    Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a
  let V : ℝ := Ch02.LambdaSq Q (s / 2) .infinity a
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hhalf : 0 < s / 2 := by positivity
  have hVpos : 0 < V := Ch02.LambdaSq_infinity_pos Q a hhalf
  have hHnonneg : ∀ n, 0 ≤ H n := by
    intro n
    exact Ch02.maxDescendantBMatrixNormAtScale_nonneg Q
      (sub_le_self Q.scale (by exact_mod_cast Nat.zero_le n)) a
  have hendpoint : ∀ n : ℕ,
      Real.rpow (3 : ℝ) (-s * (n : ℝ)) * H n ≤ V := by
    intro n
    have hmem : Real.rpow (3 : ℝ) (-s * (n : ℝ)) * H n ∈
        {x : ℝ | ∃ k : ℕ,
          x = Real.rpow (3 : ℝ) (-2 * (s / 2) * (k : ℝ)) * H k} := by
      refine ⟨n, ?_⟩
      congr 2
      ring
    simpa only [V, Ch02.LambdaSq, Ch02.LambdaSqInfinity] using
      le_csSup (Ch02.LambdaSqInfinity_valueSet_bddAbove Q a hhalf.le) hmem
  have hdiscount : Ch02.geometricDiscount s q ≤
      2 * Ch02.geometricDiscount (s / 2) q := by
    let x : ℝ := Real.rpow (3 : ℝ) (-(s * q / 2))
    have hx0 : 0 ≤ x := Real.rpow_nonneg (by norm_num) _
    have hx1 : x ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
      nlinarith [mul_pos hs hqpos]
    have hxpow : Real.rpow (3 : ℝ) (-s * q) = x ^ 2 := by
      dsimp only [x]
      rw [pow_two]
      calc
        Real.rpow (3 : ℝ) (-s * q) =
            Real.rpow (3 : ℝ) (-(s * q / 2) + -(s * q / 2)) := by
              congr 1
              ring
        _ = Real.rpow (3 : ℝ) (-(s * q / 2)) *
            Real.rpow (3 : ℝ) (-(s * q / 2)) :=
          Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _
    have hxhalf : Real.rpow (3 : ℝ) (-(s / 2) * q) = x := by
      dsimp only [x]
      congr 1
      ring
    simp only [Ch02.geometricDiscount]
    rw [hxpow, hxhalf]
    nlinarith
  have hleftSummable : Summable (fun n : ℕ =>
      Ch02.geometricWeight s q n * Real.rpow (H n) (q / 2)) := by
    simpa only [H] using Ch02.summable_B_series_pointwiseCoeffField Q a hs hqpos
  have hrightSummable : Summable (fun n : ℕ =>
      2 * Ch02.geometricWeight (s / 2) q n * Real.rpow V (q / 2)) := by
    exact ((HCPolySupport.summable_geometricWeight
      (mul_pos hhalf hqpos)).mul_left 2).mul_right _
  have hterm := @finiteEllipticity_weightedTerm_le_infinityBound (d) (Q) (a) (s) (q) (hqpos)
    (hhalf) (hHnonneg) (hendpoint) (hdiscount)
  have hseries :
      (∑' n : ℕ,
        Ch02.geometricWeight s q n * Real.rpow (H n) (q / 2)) ≤
        2 * Real.rpow V (q / 2) := by
    calc
      (∑' n : ℕ,
          Ch02.geometricWeight s q n * Real.rpow (H n) (q / 2)) ≤
          ∑' n : ℕ,
            2 * Ch02.geometricWeight (s / 2) q n * Real.rpow V (q / 2) :=
        Summable.tsum_le_tsum hterm hleftSummable hrightSummable
      _ = 2 * Real.rpow V (q / 2) := by
        have hfun : (fun n : ℕ =>
            2 * Ch02.geometricWeight (s / 2) q n * Real.rpow V (q / 2)) =
            (fun n : ℕ =>
              2 * (Ch02.geometricWeight (s / 2) q n * Real.rpow V (q / 2))) := by
          funext n
          ring
        have hweights :
            (∑' n : ℕ, Ch02.geometricWeight (s / 2) q n) = 1 := by
          simpa only [Ch02.geometricWeight_eq_old] using
            HCPolySupport.tsum_geometricWeight_eq_one (mul_pos hhalf hqpos)
        rw [hfun, tsum_mul_left, tsum_mul_right, hweights]
        ring
  have hseries0 : 0 ≤ ∑' n : ℕ,
      Ch02.geometricWeight s q n * Real.rpow (H n) (q / 2) :=
    Ch02.LambdaSqFinite_series_nonneg Q s q a hqpos.le
      (mul_nonneg hs.le hqpos.le)
  have hpowBound :
      Real.rpow
          (∑' n : ℕ,
            Ch02.geometricWeight s q n * Real.rpow (H n) (q / 2)) (2 / q) ≤
        Real.rpow (2 * Real.rpow V (q / 2)) (2 / q) :=
    Real.rpow_le_rpow hseries0 hseries
      (div_nonneg (by norm_num) hqpos.le)
  have htwo : Real.rpow (2 : ℝ) (2 / q) ≤ 4 := by
    calc
      Real.rpow (2 : ℝ) (2 / q) ≤ Real.rpow (2 : ℝ) 2 := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        rw [div_le_iff₀ hqpos]
        nlinarith
      _ = 4 := by norm_num [Real.rpow_two]
  rw [Ch02.LambdaSq_finite]
  change Real.rpow
      (∑' n : ℕ,
        Ch02.geometricWeight s q n * Real.rpow (H n) (q / 2)) (2 / q) ≤
      4 * V
  calc
    Real.rpow
        (∑' n : ℕ,
          Ch02.geometricWeight s q n * Real.rpow (H n) (q / 2)) (2 / q) ≤
        Real.rpow (2 * Real.rpow V (q / 2)) (2 / q) := hpowBound
    _ = Real.rpow (2 : ℝ) (2 / q) * V := by
      have hcancel : (q / 2) * (2 / q) = 1 := by field_simp [hqpos.ne']
      calc
        Real.rpow (2 * Real.rpow V (q / 2)) (2 / q) =
            Real.rpow (2 : ℝ) (2 / q) *
              Real.rpow (Real.rpow V (q / 2)) (2 / q) :=
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
            (Real.rpow_nonneg hVpos.le _)
        _ = Real.rpow (2 : ℝ) (2 / q) *
            Real.rpow V ((q / 2) * (2 / q)) := by
              have hrpowmul :=
                (Real.rpow_mul hVpos.le (q / 2) (2 / q)).symm
              exact congrArg (fun z : ℝ => Real.rpow (2 : ℝ) (2 / q) * z)
                hrpowmul
        _ = Real.rpow (2 : ℝ) (2 / q) * V := by
              rw [hcancel]
              exact congrArg (fun z : ℝ => Real.rpow (2 : ℝ) (2 / q) * z)
                (Real.rpow_one V)
    _ ≤ 4 * V := mul_le_mul_of_nonneg_right htwo hVpos.le
    _ = 4 * Ch02.LambdaSq Q (s / 2) .infinity a := rfl

private theorem LambdaSqCoeffField_finite_le_four_mul_infinity_half
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : RegCoeffField d)
    {s q : ℝ} (hs : 0 < s) (hq : 1 ≤ q) :
    Ch04.LambdaSqCoeffField Q s (.finite q) a ≤
      4 * Ch04.LambdaSqCoeffField Q (s / 2) .infinity a := by
  classical
  by_cases ha : Ch04.AELocallyUniformlyEllipticField a
  · simp only [Ch04.LambdaSqCoeffField, ha, dite_eq_left]
    exact LambdaSq_finite_le_four_mul_infinity_half Q
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) hs hq
  · simp [Ch04.LambdaSqCoeffField, ha]

private theorem neZero_of_model {d : ℕ} (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-- The dimension-dependent mass constant in the direct small-scale upper estimate. -/
noncomputable def directSmallUpperMassConst (d : ℕ) : ℝ :=
  320 * Provider.Base.cutoffMassSqrtConst d ^ 2 *
    (1 + 12 * (d : ℝ) * Real.log 3)


private theorem baseLoss_half_le_const_mul_inv (d : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) :
    baseLoss d ⟨s / 2, by constructor <;> linarith⟩ ≤
      (1 + 12 * (d : ℝ) * Real.log 3) * s⁻¹ := by
  rw [Provider.Scales.baseLoss_eq]
  have hA : 0 ≤ 12 * (d : ℝ) * Real.log 3 := by positivity
  have hinv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hinv_one : (1 : ℝ) ≤ s⁻¹ := by
    have hcancel : s * s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
    have hprod : 0 ≤ (1 - s) * s⁻¹ :=
      mul_nonneg (by linarith) hinv_nonneg
    nlinarith
  have hrewrite :
      6 * (d : ℝ) * Real.log 3 / (s / 2) =
        (12 * (d : ℝ) * Real.log 3) * s⁻¹ := by
    field_simp [hs.ne']
    ring
  rw [hrewrite]
  calc
    1 + (12 * (d : ℝ) * Real.log 3) * s⁻¹ ≤
        s⁻¹ + (12 * (d : ℝ) * Real.log 3) * s⁻¹ :=
      by simpa [add_comm] using
        (add_le_add_left hinv_one ((12 * (d : ℝ) * Real.log 3) * s⁻¹))
    _ = (1 + 12 * (d : ℝ) * Real.log 3) * s⁻¹ := by ring

private theorem inv_geometricDiscount_half_two_le_ten_mul_inv {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) :
    (Book.Ch02.geometricDiscount (s / 2) 2)⁻¹ ≤ 10 * s⁻¹ := by
  have hraw := Book.Ch02.inv_geometricDiscount_le_five_inv
    (s := s / 2) (p := 2) (by linarith) (by linarith) (by norm_num)
  calc
    (Book.Ch02.geometricDiscount (s / 2) 2)⁻¹ ≤ 5 * (s / 2)⁻¹ := hraw
    _ = 10 * s⁻¹ := by
      rw [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring

private theorem cstarPlus_inv_le_cstar_inv {d : ℕ} (M : ABKModel d) :
    (Disorder.cstarPlus M)⁻¹ ≤ (Disorder.cstar M)⁻¹ := by
  have hdNat : 1 ≤ d :=
    le_trans (by norm_num) M.shellPrefix.dimension
  have hd : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdNat
  have hcpos : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcle : Disorder.cstar M ≤ Disorder.cstarPlus M := by
    calc
      Disorder.cstar M = 1 * Disorder.cstar M := by ring
      _ ≤ (d : ℝ) * Disorder.cstar M :=
        mul_le_mul_of_nonneg_right hd hcpos.le
      _ ≤ Disorder.cstarPlus M := Disorder.dim_mul_cstar_le_cstarPlus M
  exact (inv_le_inv₀ (Disorder.cstarPlus_pos M) hcpos).2 hcle

private theorem cutoffMassTailScale_le_mStarStar {d : ℕ}
    (M : ABKModel d) (m : ℤ) (hm : m ≤ mStarStar M)
    (u : {u : ℝ // u ∈ Set.Ioo 0 1}) :
    IndependentSums.gammaTriangleConst 1 *
        Provider.Base.cutoffMassLinearWeightedScale M m u ≤
      Provider.Base.cutoffMassSqrtConst d ^ 2 *
        (Disorder.cstarPlus M)⁻¹ * M.gamma * baseLoss d u := by
  have hroot := Provider.Base.sqrt_cutoffMassTailScale_le_mStarStar M m u hm
  have hleft : 0 ≤ Real.sqrt
      (IndependentSums.gammaTriangleConst 1 *
        Provider.Base.cutoffMassLinearWeightedScale M m u) := Real.sqrt_nonneg _
  have hright : 0 ≤
      Provider.Base.cutoffMassSqrtConst d *
        (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma *
          Real.sqrt (baseLoss d u) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Provider.Base.cutoffMassSqrtConst_pos d).le
          (inv_nonneg.mpr (Real.sqrt_nonneg _)))
        (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have hsq := (sq_le_sq₀ hleft hright).2 hroot
  rw [Real.sq_sqrt (mul_nonneg
      IndependentSums.gammaTriangleConst_pos.le
      (Provider.Base.cutoffMassLinearWeightedScale_pos M m u).le)] at hsq
  have hcplus : 0 ≤ Disorder.cstarPlus M :=
    (Disorder.cstarPlus_pos M).le
  have hgamma : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hloss : 0 ≤ baseLoss d u := (baseLoss_pos d u).le
  calc
    IndependentSums.gammaTriangleConst 1 *
          Provider.Base.cutoffMassLinearWeightedScale M m u ≤
        (Provider.Base.cutoffMassSqrtConst d *
          (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma *
            Real.sqrt (baseLoss d u)) ^ 2 := hsq
    _ = Provider.Base.cutoffMassSqrtConst d ^ 2 *
          (Disorder.cstarPlus M)⁻¹ * M.gamma * baseLoss d u := by
      rw [show
        (Provider.Base.cutoffMassSqrtConst d *
          (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma *
            Real.sqrt (baseLoss d u)) ^ 2 =
          Provider.Base.cutoffMassSqrtConst d ^ 2 *
            ((Real.sqrt (Disorder.cstarPlus M))⁻¹) ^ 2 *
              (Real.sqrt M.gamma) ^ 2 * (Real.sqrt (baseLoss d u)) ^ 2 by ring,
        inv_pow, Real.sq_sqrt hcplus, Real.sq_sqrt hgamma, Real.sq_sqrt hloss]

private theorem inv_sq_le_eight_mul_mul_gap_inv_cube {gamma s : ℝ}
    (hgamma : 0 < gamma) (hs : 0 < s) (hgap : 0 < 2 * s - gamma) :
    s⁻¹ ^ 2 ≤ 8 * s * (2 * s - gamma)⁻¹ ^ 3 := by
  have hgap_le : 2 * s - gamma ≤ 2 * s := by linarith
  have hinv : (2 * s)⁻¹ ≤ (2 * s - gamma)⁻¹ :=
    (inv_le_inv₀ (by positivity) hgap).2 hgap_le
  have hinv_nonneg : 0 ≤ (2 * s)⁻¹ := inv_nonneg.mpr (by positivity)
  have hcube : (2 * s)⁻¹ ^ 3 ≤ (2 * s - gamma)⁻¹ ^ 3 := by
    exact pow_le_pow_left₀ hinv_nonneg hinv 3
  calc
    s⁻¹ ^ 2 = 8 * s * (2 * s)⁻¹ ^ 3 := by field_simp [hs.ne']; ring
    _ ≤ 8 * s * (2 * s - gamma)⁻¹ ^ 3 :=
      mul_le_mul_of_nonneg_left hcube (by positivity)

theorem directSmallUpper_mass_scale_le {d : ℕ}
    (M : ABKModel d) (m : ℤ) (hm : m ≤ mStarStar M)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hhalf : M.gamma / 2 < s) :
    4 * (Book.Ch02.geometricDiscount (s / 2) 2)⁻¹ *
        (IndependentSums.gammaTriangleConst 1 *
          Provider.Base.cutoffMassLinearWeightedScale M m
            ⟨s / 2, by constructor <;> linarith⟩) ≤
      directSmallUpperMassConst d * (Disorder.cstar M)⁻¹ * s * M.gamma *
        (2 * s - M.gamma)⁻¹ ^ 3 := by
  let u : {u : ℝ // u ∈ Set.Ioo 0 1} :=
    ⟨s / 2, by constructor <;> linarith⟩
  let K : ℝ := Provider.Base.cutoffMassSqrtConst d
  let D : ℝ := 1 + 12 * (d : ℝ) * Real.log 3
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hgap : 0 < 2 * s - M.gamma := by linarith
  have hdisc := inv_geometricDiscount_half_two_le_ten_mul_inv hs hs1
  have htail := cutoffMassTailScale_le_mStarStar M m hm u
  have hloss := baseLoss_half_le_const_mul_inv d hs hs1
  have hcstar := cstarPlus_inv_le_cstar_inv M
  have hK : 0 ≤ K := (Provider.Base.cutoffMassSqrtConst_pos d).le
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hcinv : 0 ≤ (Disorder.cstar M)⁻¹ :=
    inv_nonneg.mpr (Disorder.cstar_characterization M).1.le
  have hcplusinv : 0 ≤ (Disorder.cstarPlus M)⁻¹ :=
    inv_nonneg.mpr (Disorder.cstarPlus_pos M).le
  have hginv : 0 ≤ M.gamma := hgamma.le
  have hsinv : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have htail_nonneg : 0 ≤
      IndependentSums.gammaTriangleConst 1 *
        Provider.Base.cutoffMassLinearWeightedScale M m u :=
    mul_nonneg IndependentSums.gammaTriangleConst_pos.le
      (Provider.Base.cutoffMassLinearWeightedScale_pos M m u).le
  have hloss_nonneg : 0 ≤ baseLoss d u := (baseLoss_pos d u).le
  have hgapfactor := inv_sq_le_eight_mul_mul_gap_inv_cube hgamma hs hgap
  have hcoef : (0 : ℝ) ≤ 4 * (10 * s⁻¹) :=
    mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hsinv)
  calc
    4 * (Book.Ch02.geometricDiscount (s / 2) 2)⁻¹ *
          (IndependentSums.gammaTriangleConst 1 *
            Provider.Base.cutoffMassLinearWeightedScale M m u) ≤
        4 * (10 * s⁻¹) *
          (IndependentSums.gammaTriangleConst 1 *
            Provider.Base.cutoffMassLinearWeightedScale M m u) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdisc (by norm_num : (0 : ℝ) ≤ 4))
        htail_nonneg
    _ ≤ 4 * (10 * s⁻¹) *
          (K ^ 2 * (Disorder.cstarPlus M)⁻¹ * M.gamma * baseLoss d u) := by
      exact mul_le_mul_of_nonneg_left htail hcoef
    _ ≤ 4 * (10 * s⁻¹) *
          (K ^ 2 * (Disorder.cstar M)⁻¹ * M.gamma * baseLoss d u) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcstar (sq_nonneg K)) hginv)
          hloss_nonneg)
        hcoef
    _ ≤ 40 * K ^ 2 * D * (Disorder.cstar M)⁻¹ * M.gamma * s⁻¹ ^ 2 := by
      change baseLoss d u ≤ D * s⁻¹ at hloss
      calc
        4 * (10 * s⁻¹) *
            (K ^ 2 * (Disorder.cstar M)⁻¹ * M.gamma * baseLoss d u) ≤
          4 * (10 * s⁻¹) *
            (K ^ 2 * (Disorder.cstar M)⁻¹ * M.gamma * (D * s⁻¹)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hloss
                (mul_nonneg (mul_nonneg (sq_nonneg K) hcinv) hginv))
              hcoef
        _ = 40 * K ^ 2 * D * (Disorder.cstar M)⁻¹ * M.gamma * s⁻¹ ^ 2 := by
          ring
    _ ≤ 320 * K ^ 2 * D * (Disorder.cstar M)⁻¹ * M.gamma *
          (s * (2 * s - M.gamma)⁻¹ ^ 3) := by
      have hmul := mul_le_mul_of_nonneg_left hgapfactor
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by positivity : 0 ≤ 40 * K ^ 2 * D) hcinv)
            hginv)
          (by norm_num : 0 ≤ (1 : ℝ)))
      nlinarith
    _ = directSmallUpperMassConst d * (Disorder.cstar M)⁻¹ * s * M.gamma *
          (2 * s - M.gamma)⁻¹ ^ 3 := by
      simp only [directSmallUpperMassConst, K, D]
      ring

private theorem cutoffFrobeniusMass_le_root_control {d : ℕ}
    (Q R : TriadicCube d) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (m : ℤ) (omega : CutoffSample d) :
    Provider.Stream.cutoffFrobeniusMass R m omega ≤
      (d : ℝ) ^ 2 * cutoffLocalControl (cubeOriginCoverScale Q) m omega ^ 2 := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) := by
    simpa only [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet R).isFiniteMeasure_restrict_volume
  have hintegrable : IntegrableOn
      (fun x : Vec d => Ch02.matrixFrobeniusNormSq (cutoff m omega x))
      (openCubeSet R) volume := by
    exact
      ((Provider.Stream.continuous_frobeniusMass_cutoff m omega).continuousOn.integrableOn_compact
        (isBounded_openCubeSet R).isCompact_closure).mono_set subset_closure
  rw [Provider.Stream.cutoffFrobeniusMass, Ch02.average, Ch02.cubeDomain_coe]
  refine volumeAverage_le_of_le_on (measurableSet_openCubeSet R) hintegrable ?_ ?_
  · rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos R).ne'
  · intro x hx
    exact Provider.Stream.matrixFrobeniusNormSq_le_of_abs_entry_le fun i j =>
      abs_cutoff_entry_le_cutoffLocalControl (cubeOriginCoverScale Q) m omega
        (openCubeSet_subset_originCover Q (hRQ hx)) i j

private theorem cutoffFrobeniusMassMaximum_le_root_control {d : ℕ}
    (Q : TriadicCube d) (m : ℤ) (n : ℕ) (omega : CutoffSample d) :
    Provider.Stream.cutoffFrobeniusMassMaximum Q m n omega ≤
      (d : ℝ) ^ 2 * cutoffLocalControl (cubeOriginCoverScale Q) m omega ^ 2 := by
  unfold Provider.Stream.cutoffFrobeniusMassMaximum
  refine Finset.sup'_le (descendantsAtDepth_nonempty Q n) _ ?_
  intro R hR
  exact cutoffFrobeniusMass_le_root_control Q R
    (openCubeSet_subset_of_mem_descendantsAtDepth hR) m omega

private theorem summable_cutoffMassLinearWeightedSum_terms {d : ℕ}
    (M : ABKModel d) (Q : TriadicCube d) (m : ℤ)
    (u : {u : ℝ // u ∈ Set.Ioo 0 1}) (omega : CutoffSample d) :
    Summable (fun n : ℕ => Ch02.geometricWeight (u : ℝ) 2 n *
      (M.nu⁻¹ ^ 2 * Provider.Stream.cutoffFrobeniusMassMaximum Q m n omega)) := by
  have hu : 0 < (u : ℝ) := (Set.mem_Ioo.mp u.2).1
  have hsum := HCPolySupport.summable_geometricWeight_mul_of_nonneg_of_le
    (s := (u : ℝ)) (q := 2)
    (C := M.nu⁻¹ ^ 2 *
      ((d : ℝ) ^ 2 * cutoffLocalControl (cubeOriginCoverScale Q) m omega ^ 2))
    (mul_pos hu (by norm_num))
    (fun n => mul_nonneg (sq_nonneg _)
      (Provider.Stream.cutoffFrobeniusMassMaximum_nonneg Q m n omega))
    (fun n => mul_le_mul_of_nonneg_left
      (cutoffFrobeniusMassMaximum_le_root_control Q m n omega) (sq_nonneg _))
  simpa only [Ch02.geometricWeight_eq_old] using hsum

private theorem measurable_cutoffMassLinearWeightedSum {d : ℕ}
    (M : ABKModel d) (Q : TriadicCube d) (m : ℤ)
    (u : {u : ℝ // u ∈ Set.Ioo 0 1}) :
    Measurable (Provider.Base.cutoffMassLinearWeightedSum M Q m u) := by
  change Measurable (fun omega : CutoffSample d => ∑' n : ℕ,
    Ch02.geometricWeight (u : ℝ) 2 n *
      (M.nu⁻¹ ^ 2 * Provider.Stream.cutoffFrobeniusMassMaximum Q m n omega))
  exact Measurable.tsum (L := SummationFilter.unconditional ℕ)
    (fun n =>
      ((Provider.Stream.measurable_cutoffFrobeniusMassMaximum Q m n).const_mul
        (M.nu⁻¹ ^ 2)).const_mul (Ch02.geometricWeight (u : ℝ) 2 n))

/-- Every admissible cutoff upper coefficient at `s` is bounded by four times
the true infinity endpoint at `s / 2`, uniformly in the exponent. -/
theorem cutoffUpperEllipticity_le_four_mul_infinity_half {d : ℕ}
    (M : ABKModel d) (m L : ℤ) {s : ℝ} (hs : 0 < s)
    (q : CoarseEllipticityExponent) (omega : Cutoff.CutoffSample d) :
    Observable.cutoffUpperEllipticity M m L s hs q omega ≤
      4 * Observable.cutoffUpperEllipticity M m L (s / 2) (by positivity)
        CoarseEllipticityExponent.infinity omega := by
  let : NeZero d := neZero_of_model M
  rw [congrFun (Observable.cutoffUpperEllipticity_eq_literal M m L s hs q) omega,
    congrFun (Observable.cutoffUpperEllipticity_eq_literal M m L (s / 2)
      (by positivity) CoarseEllipticityExponent.infinity) omega]
  unfold Observable.cutoffUpperEllipticityLiteral
  rcases q with ⟨q, hq⟩
  cases q with
  | finite r =>
      change 1 ≤ r at hq
      exact LambdaSqCoeffField_finite_le_four_mul_infinity_half
        (originCube d m) (Cutoff.coefficientCutoff M.nu L omega) hs hq
  | infinity =>
      have hmono := Ch02.LambdaSq_infinity_antitone
        (originCube d m)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
        (t := s / 2) (s := s) (by positivity) (by linarith)
      simpa only [Ch04.LambdaSqCoeffField,
        Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField, dite_eq_left] using!
        hmono.trans (le_mul_of_one_le_left
          (Ch02.LambdaSq_infinity_nonneg
            (originCube d m)
            (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) (by positivity))
          (by norm_num : (1 : ℝ) ≤ 4))

private theorem cutoffUpperEllipticity_infinity_half_mul_sigmaBarInv_le
    {d : ℕ} (M : ABKModel d) (m : ℤ) (hm : m ≤ mStarStar M)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (omega : CutoffSample d) :
    Observable.cutoffUpperEllipticity M m m (s / 2) (by positivity)
          CoarseEllipticityExponent.infinity omega *
        (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ ≤
      1 + (Ch02.geometricDiscount (s / 2) 2)⁻¹ *
        Provider.Base.cutoffMassLinearWeightedSum M (originCube d m) m
          ⟨s / 2, by constructor <;> linarith⟩ omega := by
  let : NeZero d := neZero_of_model M
  let u : {u : ℝ // u ∈ Set.Ioo 0 1} :=
    ⟨s / 2, by constructor <;> linarith⟩
  let D : ℝ := Ch02.geometricDiscount (s / 2) 2
  let scaling : ℝ := (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹
  let mass : CutoffSample d → ℝ :=
    Provider.Base.cutoffMassLinearWeightedSum M (originCube d m) m u
  have hmPred : m - 1 ≤ mStarStar M := by linarith
  have hnu : M.nu ≤ (Annealed.sigmaBar M (m - 1) : ℝ) :=
    (Provider.Base.annealedPlateau_le_mStarStar M (m - 1) hmPred).1
  have hsigma : 0 < (Annealed.sigmaBar M (m - 1) : ℝ) :=
    (Annealed.sigmaBar M (m - 1)).2
  have hscaling : 0 ≤ scaling := inv_nonneg.mpr hsigma.le
  have hscnu : scaling * M.nu ≤ 1 := by
    exact (inv_mul_le_one₀ hsigma).2 hnu
  have hsc_le_nuinv : scaling ≤ M.nu⁻¹ := by
    exact (inv_le_inv₀ hsigma M.nu_pos).2 hnu
  have hDpos : 0 < D := by
    dsimp only [D]
    exact Ch02.book_geometricDiscount_pos (by positivity)
  have hDinv : 0 ≤ D⁻¹ := inv_nonneg.mpr hDpos.le
  refine Provider.CoarseEllipticity.cutoffUpperEllipticity_infinity_mul_le
    M m m (s := s / 2) (by positivity)
      (q := CoarseEllipticityExponent.infinity) rfl
      (scaling := scaling) (V := fun omega' => 1 + D⁻¹ * mass omega')
      hscaling ?_ omega
  intro n omega'
  let F : ℝ :=
    Provider.Stream.cutoffFrobeniusMassMaximum (originCube d m) m n omega'
  let raw : ℝ := Real.rpow (3 : ℝ) (-2 * (s / 2) * (n : ℝ))
  have hF : 0 ≤ F :=
    Provider.Stream.cutoffFrobeniusMassMaximum_nonneg (originCube d m) m n omega'
  have hraw : 0 ≤ raw := Real.rpow_nonneg (by norm_num) _
  have hraw_one : raw ≤ 1 := by
    dsimp only [raw]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have hn : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hb :
      Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
          (originCube d m) (m - (n : ℤ))
          (coefficientCutoff M.nu m omega') ≤
        M.nu + M.nu⁻¹ * F := by
    simpa only [Ch04.maxDescendantBMatrixNormCoeffFieldAtScale,
      coefficientCutoff_aeLocallyUniformlyEllipticField, dite_eq_left, F] using!
      (Provider.Base.maxDescendantBMatrixNormAtScale_coefficientCutoff_le
        M (originCube d m) m n omega')
  have hterm :
      Ch02.geometricWeight (u : ℝ) 2 n * (M.nu⁻¹ ^ 2 * F) ≤ mass omega' := by
    have hsum := summable_cutoffMassLinearWeightedSum_terms
      M (originCube d m) m u omega'
    have hfinite := hsum.sum_le_tsum {n} fun j _ =>
      mul_nonneg
        (HCPolySupport.geometricWeight_nonneg j
          (mul_nonneg (Set.mem_Ioo.mp u.2).1.le (by norm_num)))
        (mul_nonneg (sq_nonneg _)
          (Provider.Stream.cutoffFrobeniusMassMaximum_nonneg
            (originCube d m) m j omega'))
    simpa only [Finset.sum_singleton, mass,
      Provider.Base.cutoffMassLinearWeightedSum, F] using! hfinite
  have hweight : D⁻¹ * Ch02.geometricWeight (u : ℝ) 2 n = raw := by
    dsimp only [D, u, raw]
    rw [Ch02.geometricWeight]
    have hDne : Ch02.geometricDiscount (s / 2) 2 ≠ 0 := by
      exact (Ch02.book_geometricDiscount_pos (by positivity)).ne'
    field_simp [hDne]
  have hmasspart :
      raw * (scaling * (M.nu⁻¹ * F)) ≤ D⁻¹ * mass omega' := by
    calc
      raw * (scaling * (M.nu⁻¹ * F)) ≤
          raw * (M.nu⁻¹ * (M.nu⁻¹ * F)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsc_le_nuinv
            (mul_nonneg (inv_nonneg.mpr M.nu_pos.le) hF)) hraw
      _ = D⁻¹ * (Ch02.geometricWeight (u : ℝ) 2 n *
          (M.nu⁻¹ ^ 2 * F)) := by rw [← hweight]; ring
      _ ≤ D⁻¹ * mass omega' := mul_le_mul_of_nonneg_left hterm hDinv
  calc
    scaling * (Real.rpow (3 : ℝ) (-2 * (s / 2) * (n : ℝ)) *
        Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
          (originCube d m) (m - (n : ℤ))
          (coefficientCutoff M.nu m omega')) =
        raw * (scaling *
          Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
            (originCube d m) (m - (n : ℤ))
            (coefficientCutoff M.nu m omega')) := by dsimp only [raw]; ring
    _ ≤ raw * (scaling * (M.nu + M.nu⁻¹ * F)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hb hscaling) hraw
    _ = raw * (scaling * M.nu) + raw * (scaling * (M.nu⁻¹ * F)) := by ring
    _ ≤ 1 + D⁻¹ * mass omega' := by
      have hscnu0 : 0 ≤ scaling * M.nu := mul_nonneg hscaling M.nu_pos.le
      exact add_le_add
        ((mul_le_mul hraw_one hscnu hscnu0 zero_le_one).trans (by norm_num))
        hmasspart
    _ = 1 + (Ch02.geometricDiscount (s / 2) 2)⁻¹ *
        Provider.Base.cutoffMassLinearWeightedSum M (originCube d m) m
          ⟨s / 2, by constructor <;> linarith⟩ omega' := rfl

theorem cutoffUpperEllipticity_mul_sigmaBarInv_le_four_add_mass {d : ℕ}
    (M : ABKModel d) (m : ℤ) (hm : m ≤ mStarStar M)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (q : CoarseEllipticityExponent) (omega : CutoffSample d) :
    Observable.cutoffUpperEllipticity M m m s hs q omega *
        (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ ≤
      4 + 4 * (Ch02.geometricDiscount (s / 2) 2)⁻¹ *
        Provider.Base.cutoffMassLinearWeightedSum M (originCube d m) m
          ⟨s / 2, by constructor <;> linarith⟩ omega := by
  have hscaling : 0 ≤ (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M (m - 1)).2.le
  have hq := cutoffUpperEllipticity_le_four_mul_infinity_half
    M m m hs q omega
  have hinf := cutoffUpperEllipticity_infinity_half_mul_sigmaBarInv_le
    M m hm hs hs1 omega
  calc
    Observable.cutoffUpperEllipticity M m m s hs q omega *
          (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ ≤
        (4 * Observable.cutoffUpperEllipticity M m m (s / 2) (by positivity)
          CoarseEllipticityExponent.infinity omega) *
            (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hq hscaling
    _ = 4 * (Observable.cutoffUpperEllipticity M m m (s / 2) (by positivity)
          CoarseEllipticityExponent.infinity omega *
            (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹) := by ring
    _ ≤ 4 * (1 + (Ch02.geometricDiscount (s / 2) 2)⁻¹ *
        Provider.Base.cutoffMassLinearWeightedSum M (originCube d m) m
          ⟨s / 2, by constructor <;> linarith⟩ omega) :=
      mul_le_mul_of_nonneg_left hinf (by norm_num)
    _ = 4 + 4 * (Ch02.geometricDiscount (s / 2) 2)⁻¹ *
        Provider.Base.cutoffMassLinearWeightedSum M (originCube d m) m
          ⟨s / 2, by constructor <;> linarith⟩ omega := by ring

private theorem isBigOWith_gammaSigma_zero {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} {sigma A : ℝ} (hA : 0 ≤ A) :
    IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma)
      (fun _ : Omega => 0) A :=
  Algsuperdiff.Section3.Probability.isBigOWith_gammaSigma_of_eq_zero hA (fun _ => rfl)

/-- The upper-family carrier in the direct branch `m ≤ mStarStar M`.
The branch uses no induction-state or large-scale gate premise. -/
theorem coarse_ellipticity_upper_of_le_mStarStar
    {d : ℕ} (M : ABKModel d) (m : ℤ) (hm : m ≤ mStarStar M)
    {Cup : ℝ} (hfour : 4 ≤ Cup)
    (hmassConst : directSmallUpperMassConst d ≤ Cup)
    (E : {E : ℝ // 1 ≤ E}) (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioc 0 (1 / 2))
    (q : CoarseEllipticityExponent) (s : ℝ)
    (hsWindow : s ∈ Set.Icc
      (M.gamma / 2 + Real.exp (-(Cup⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1) :
    Probability.IsDeterministicShiftTwoTermOneSidedOrlicz
      (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 1)
      (IndependentSums.gammaSigma ((1 - sigma) / 3))
      (fun omega =>
        Observable.cutoffUpperEllipticity M m m s
          (by
            exact (add_pos
              (div_pos M.shellPrefix.gamma_pos (by norm_num))
              (Real.exp_pos
                (-(Cup⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)))).trans_le hsWindow.1)
          q omega * (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹)
      Cup
      (Cup * (Disorder.cstar M)⁻¹ * s * M.gamma *
        (2 * s - M.gamma)⁻¹ ^ 3)
      (Real.exp (-(Cup⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) := by
  let u : {u : ℝ // u ∈ Set.Ioo 0 1} :=
    ⟨s / 2, by
      constructor
      · have hhalf : M.gamma / 2 < s := by
          linarith [hsWindow.1, Real.exp_pos
            (-(Cup⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))]
        linarith [M.shellPrefix.gamma_pos]
      · linarith [hsWindow.2]⟩
  let D : ℝ := Ch02.geometricDiscount (s / 2) 2
  let mass : CutoffSample d → ℝ :=
    Provider.Base.cutoffMassLinearWeightedSum M (originCube d m) m u
  let Udet : CutoffSample d → ℝ := fun _ => 4
  let U1 : CutoffSample d → ℝ := fun omega => 4 * D⁻¹ * mass omega
  let Uexp : CutoffSample d → ℝ := fun _ => 0
  have hrare : 0 < Real.exp (-(Cup⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) :=
    Real.exp_pos _
  have hhalf : M.gamma / 2 < s := by linarith [hsWindow.1, hrare]
  have hs : 0 < s := by linarith [M.shellPrefix.gamma_pos]
  have hs1 : s ≤ 1 := hsWindow.2
  have hgap : 0 < 2 * s - M.gamma := by linarith
  have hCupPos : 0 < Cup := by linarith [hfour]
  have hDpos : 0 < D := by
    dsimp only [D]
    exact Ch02.book_geometricDiscount_pos (by positivity)
  have hDinv : 0 ≤ D⁻¹ := inv_nonneg.mpr hDpos.le
  have hA1pos : 0 < Cup * (Disorder.cstar M)⁻¹ * s * M.gamma *
      (2 * s - M.gamma)⁻¹ ^ 3 := by
    positivity [hCupPos, (Disorder.cstar_characterization M).1,
      M.shellPrefix.gamma_pos, hgap]
  have hsigmaExp : 0 < (1 - sigma) / 3 := by linarith [hsigma.2]
  have hXmeas : Measurable (fun omega =>
      Observable.cutoffUpperEllipticity M m m s hs q omega *
        (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹) :=
    (Observable.measurable_cutoffUpperEllipticity M m m s hs q).mul_const _
  have hU1meas : Measurable U1 := by
    exact (measurable_cutoffMassLinearWeightedSum
      M (originCube d m) m u).const_mul (4 * D⁻¹)
  have hdom : ∀ omega,
      Observable.cutoffUpperEllipticity M m m s hs q omega *
          (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ ≤
        Udet omega + U1 omega + Uexp omega := by
    intro omega
    have hpoint := cutoffUpperEllipticity_mul_sigmaBarInv_le_four_add_mass
      M m hm hs hs1 q omega
    simpa only [Udet, U1, Uexp, mass, D, add_zero] using hpoint
  have hU1tail : IndependentSums.IsBigOWith
      (cutoffSampleLaw M).toMeasure (IndependentSums.gammaSigma 1) U1
      (Cup * (Disorder.cstar M)⁻¹ * s * M.gamma *
        (2 * s - M.gamma)⁻¹ ^ 3) := by
    have hraw :=
      (Provider.Base.isBigOWith_gammaSigma_one_cutoffMassLinearWeightedSum
        M (originCube d m) m u).const_mul (c := 4 * D⁻¹)
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hDinv)
    have hscale0 := directSmallUpper_mass_scale_le M m hm hs hs1 hhalf
    have hprofile0 : 0 ≤ (Disorder.cstar M)⁻¹ * s * M.gamma *
        (2 * s - M.gamma)⁻¹ ^ 3 := by
      positivity [(Disorder.cstar_characterization M).1, hs,
        M.shellPrefix.gamma_pos, hgap]
    have hscaleC :
        directSmallUpperMassConst d * (Disorder.cstar M)⁻¹ * s * M.gamma *
            (2 * s - M.gamma)⁻¹ ^ 3 ≤
          Cup * (Disorder.cstar M)⁻¹ * s * M.gamma *
            (2 * s - M.gamma)⁻¹ ^ 3 := by
      have hmul := mul_le_mul_of_nonneg_right hmassConst hprofile0
      simpa only [mul_assoc] using hmul
    have hscale := hscale0.trans hscaleC
    exact hraw.mono_scale (by
      simpa only [U1, mass, D, u, mul_assoc] using hscale)
  refine Provider.CoarseEllipticity.isDeterministicShiftTwoTermOneSidedOrlicz_of_split
    (Udet := Udet) (U1 := U1) (Uexp := Uexp)
    one_pos hsigmaExp hA1pos hrare ?_ hU1meas measurable_const hdom
      (fun _ => hfour) hU1tail ?_
  · simpa only using hXmeas
  · exact isBigOWith_gammaSigma_zero hrare.le

/-! ## 3. The complete upper leg -/

private theorem upperLeg_comparisonBounds1 :
    ∀ (d : ℕ),
      let previousLaneOutput : ℝ :=
        max (goodHeadTunedOutputConst d)
          (max (probeSharpBandMeanTunedOutputConst d)
            (max (probeSharpDeepBandTailTunedOutputConst d)
              (max (probeSharpCollarBaseTunedOutputConst d)
                (max (collarHeadTunedPerDescendantOutputConst d)
                  (max (collarAfterBandTunedOutputConst d)
                    (max (probeSharpWaveTailTunedOutputConst d)
                      (max (Multiscale.probeSharpGoodBaseConst d)
                        (max (collarBandMeanTunedOutputConst d) (collarDeepTailTunedOutputConst
                          d)))))))));
      let laneOutput : ℝ :=
        max previousLaneOutput (max (probeSharpAfterBandTunedOutputConst d)
          (probeSharpCollarWaveTailTunedOutputConst d));
      let Clane : ℝ :=
        max (4 : ℝ)
          (max (directSmallUpperMassConst d)
            (max (profileAuxiliaryConst d) (max (collarBandMeanDepthThreshold d) laneOutput)));
      let Cblock : ℝ := ((12 : ℝ) + (12 : ℝ) * IndependentSums.gammaTriangleConst (1 : ℝ)) * Clane;
      let Cmerge : ℝ := coarseEllipticityUpperMergeConst d;
      let Cup : ℝ := Cblock * Cmerge;
      (0 : ℝ) < Clane ∧
        Clane ≤ Cblock ∧
          (0 : ℝ) < Cblock ∧
            (1 : ℝ) ≤ Cmerge ∧
              Cblock ≤ Cup ∧
                (4 : ℝ) ≤ Cup ∧
                  goodHeadTunedOutputConst d ≤ Clane ∧
                    probeSharpBandMeanTunedOutputConst d ≤ Clane ∧
                      probeSharpDeepBandTailTunedOutputConst d ≤ Clane ∧
                        probeSharpCollarBaseTunedOutputConst d ≤ Clane ∧
                          collarHeadTunedPerDescendantOutputConst d ≤ Clane ∧
                            collarAfterBandTunedOutputConst d ≤ Clane ∧
                              probeSharpWaveTailTunedOutputConst d ≤ Clane ∧
                                Multiscale.probeSharpGoodBaseConst d ≤ Clane ∧
                                  collarBandMeanTunedOutputConst d ≤ Clane ∧
                                    collarDeepTailTunedOutputConst d ≤ Clane ∧
                                      probeSharpAfterBandTunedOutputConst d ≤ Clane ∧
                                        probeSharpCollarWaveTailTunedOutputConst d ≤ Clane ∧
                                          profileAuxiliaryConst d ≤ Clane ∧
                                            collarBandMeanDepthThreshold d ≤ Clane ∧
                                              directSmallUpperMassConst d ≤ Cup ∧
                                                collarBandMeanDepthThreshold d ≤ Cup ∧ (0 : ℝ) <
                                                  Cup := by
  intro d previousLaneOutput laneOutput Clane Cblock Cmerge Cup
  have hfourLane : 4 ≤ Clane := by
    exact le_max_left _ _
  have hlanePos : 0 < Clane := lt_of_lt_of_le (by norm_num) hfourLane
  have hlaneBlock : Clane ≤ Cblock := by
    dsimp only [Cblock]
    have htriangle : 0 < HCPolySupport.IndependentSums.gammaTriangleConst 1 :=
      HCPolySupport.IndependentSums.gammaTriangleConst_pos
    nlinarith
  have hblockPos : 0 < Cblock := hlanePos.trans_le hlaneBlock
  have hmergeOne : 1 ≤ Cmerge := by
    exact (by norm_num : (1 : ℝ) ≤ 4).trans (by
      dsimp only [Cmerge, coarseEllipticityUpperMergeConst]
      exact le_max_left _ _)
  have hblockCup : Cblock ≤ Cup := by
    dsimp only [Cup]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hmergeOne hblockPos.le
  have hfour : 4 ≤ Cup := hfourLane.trans (hlaneBlock.trans hblockCup)
  have hlaneOutput : laneOutput ≤ Clane := by
    exact (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hpreviousLaneOutput : previousLaneOutput ≤ Clane :=
    (le_max_left _ _).trans hlaneOutput
  have hgoodHeadOutput : goodHeadTunedOutputConst d ≤ Clane := by
    exact (le_max_left _ _).trans hpreviousLaneOutput
  have hgoodBandOutput : probeSharpBandMeanTunedOutputConst d ≤ Clane := by
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans hpreviousLaneOutput
  have hgoodDeepOutput : probeSharpDeepBandTailTunedOutputConst d ≤ Clane := by
    exact (((le_max_left _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans hpreviousLaneOutput
  have hcollarBaseOutput : probeSharpCollarBaseTunedOutputConst d ≤ Clane := by
    exact ((((le_max_left _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)).trans hpreviousLaneOutput
  have hcollarHeadOutput : collarHeadTunedPerDescendantOutputConst d ≤ Clane := by
    exact (((((le_max_left _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans hpreviousLaneOutput
  have hcollarAfterOutput : collarAfterBandTunedOutputConst d ≤ Clane := by
    exact ((((((le_max_left _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans hpreviousLaneOutput
  have hgoodWaveOutput : probeSharpWaveTailTunedOutputConst d ≤ Clane := by
    exact (((((((le_max_left _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
          (le_max_right _ _)).trans hpreviousLaneOutput
  have hgoodBaseOutput : Provider.Multiscale.probeSharpGoodBaseConst d ≤ Clane := by
    exact ((((((((le_max_left _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
          (le_max_right _ _)).trans (le_max_right _ _)).trans hpreviousLaneOutput
  have hcollarBandOutput : collarBandMeanTunedOutputConst d ≤ Clane := by
    exact (((((((((le_max_left _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
          (le_max_right _ _)).trans (le_max_right _ _)).trans
            (le_max_right _ _)).trans hpreviousLaneOutput
  have hcollarDeepOutput : collarDeepTailTunedOutputConst d ≤ Clane := by
    exact (((((((((le_max_right _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
          (le_max_right _ _)).trans (le_max_right _ _)).trans
            (le_max_right _ _)).trans hpreviousLaneOutput
  have hgoodAfterOutput : probeSharpAfterBandTunedOutputConst d ≤ Clane := by
    exact (le_max_left _ _).trans ((le_max_right _ _).trans hlaneOutput)
  have hcollarWaveOutput : probeSharpCollarWaveTailTunedOutputConst d ≤ Clane := by
    exact (le_max_right _ _).trans ((le_max_right _ _).trans hlaneOutput)
  have hprofileAuxLane : profileAuxiliaryConst d ≤ Clane := by
    exact (le_max_left _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have hdepthThresholdLane : collarBandMeanDepthThreshold d ≤ Clane := by
    exact (le_max_left _ _).trans
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))
  have hmassConst : directSmallUpperMassConst d ≤ Cup := by
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans
      (hlaneBlock.trans hblockCup)
  have hdepthThreshold : collarBandMeanDepthThreshold d ≤ Cup := by
    exact hdepthThresholdLane.trans (hlaneBlock.trans hblockCup)
  have hCup : 0 < Cup := lt_of_lt_of_le (by norm_num) hfour
  exact ⟨hlanePos, hlaneBlock, hblockPos, hmergeOne, hblockCup, hfour, hgoodHeadOutput,
    hgoodBandOutput, hgoodDeepOutput, hcollarBaseOutput, hcollarHeadOutput, hcollarAfterOutput,
      hgoodWaveOutput, hgoodBaseOutput, hcollarBandOutput, hcollarDeepOutput, hgoodAfterOutput,
        hcollarWaveOutput, hprofileAuxLane, hdepthThresholdLane, hmassConst, hdepthThreshold, hCup⟩

private theorem upperLeg_estimate1 :
    ∀ (d : ℕ),
      let previousLaneOutput : ℝ :=
        max (goodHeadTunedOutputConst d)
          (max (probeSharpBandMeanTunedOutputConst d)
            (max (probeSharpDeepBandTailTunedOutputConst d)
              (max (probeSharpCollarBaseTunedOutputConst d)
                (max (collarHeadTunedPerDescendantOutputConst d)
                  (max (collarAfterBandTunedOutputConst d)
                    (max (probeSharpWaveTailTunedOutputConst d)
                      (max (Multiscale.probeSharpGoodBaseConst d)
                        (max (collarBandMeanTunedOutputConst d) (collarDeepTailTunedOutputConst
                          d)))))))));
      let laneOutput : ℝ :=
        max previousLaneOutput (max (probeSharpAfterBandTunedOutputConst d)
          (probeSharpCollarWaveTailTunedOutputConst d));
      let Clane : ℝ :=
        max (4 : ℝ)
          (max (directSmallUpperMassConst d)
            (max (profileAuxiliaryConst d) (max (collarBandMeanDepthThreshold d) laneOutput)));
      let Cblock : ℝ := ((12 : ℝ) + (12 : ℝ) * IndependentSums.gammaTriangleConst (1 : ℝ)) * Clane;
      let Cmerge : ℝ := coarseEllipticityUpperMergeConst d;
      let Cup : ℝ := Cblock * Cmerge;
      ∀ (_ : (0 : ℝ) < Clane) (_ : goodHeadTunedOutputConst d ≤ Clane)
        (_ : probeSharpBandMeanTunedOutputConst d ≤ Clane)
        (_ : probeSharpDeepBandTailTunedOutputConst d ≤ Clane)
        (_ : probeSharpCollarBaseTunedOutputConst d ≤ Clane)
        (_ : collarHeadTunedPerDescendantOutputConst d ≤ Clane)
        (_ : collarAfterBandTunedOutputConst d ≤ Clane)
        (_ : probeSharpWaveTailTunedOutputConst d ≤ Clane)
        (_ : Multiscale.probeSharpGoodBaseConst d ≤ Clane)
        (_ : collarBandMeanTunedOutputConst d ≤ Clane)
        (_ : collarDeepTailTunedOutputConst d ≤ Clane)
        (_ : probeSharpAfterBandTunedOutputConst d ≤ Clane)
        (_ : probeSharpCollarWaveTailTunedOutputConst d ≤ Clane)
        (_ : profileAuxiliaryConst d ≤ Clane) (_ : collarBandMeanDepthThreshold d ≤ Clane)
        (_ : (0 : ℝ) < Cup) (M : ABKModel d) (m : ℤ) (E : { E : ℝ // (1 : ℝ) ≤ E })
        (_ : Frozen.Section3.inductionState M (m - (1 : ℤ)) E) (sigma : ℝ) (_ : (↑E : ℝ) ≤ M.gamma
          ^ (-(1 / 5 : ℝ)))
        (_ : (2 : ℕ) ≤ d) (_ : (0 : ℝ) < sigma) (_ : sigma ≤ (1 / 2 : ℝ))
        (_ : Cup ≤ (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹) (_ : (3 : ℕ) ≤ collarBandMeanDepth M (↑E : ℝ))
        (_ : max (Real.exp (Clane / sigma)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ))
        (_ :
          (12 : ℝ) * upperAfterBandRareTriangleConst * coarseEllipticityRareBudgetConst d + (15 :
            ℝ) ≤ Clane⁻¹ * Cup)
        (k : ℕ),
        ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
          ∃ (Uone : CutoffSample d → ℝ) (Uexp : CutoffSample d → ℝ),
            (∀ (omega : CutoffSample d), (0 : ℝ) ≤ Uone omega) ∧
              Measurable Uone ∧
                (∀ (omega : CutoffSample d), (0 : ℝ) ≤ Uexp omega) ∧
                  Measurable Uexp ∧
                    (∀ (omega : CutoffSample d),
                        cutoffBBlockFamily M m (↑(Annealed.sigmaBar M (m - (1 : ℤ))) : ℝ)⁻¹ R
                          omega ≤
                          Cblock + Uone omega + Uexp omega) ∧
                      IndependentSums.IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d))
                          (IndependentSums.gammaSigma (1 : ℝ)) Uone
                          (upperSaturatedPerCubeAmplitude Cblock (Disorder.cstar M) M.gamma k) ∧
                        IndependentSums.IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d))
                          (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) Uexp
                          ((coarseEllipticityRareBudgetConst d)⁻¹ *
                            ((3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) *
                              Real.exp (-(Cup⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (15 :
                                ℕ))) := by
  intro _ _ _ Clane _ _ _ hlanePos hgoodHeadOutput hgoodBandOutput hgoodDeepOutput
    hcollarBaseOutput hcollarHeadOutput hcollarAfterOutput hgoodWaveOutput hgoodBaseOutput
      hcollarBandOutput hcollarDeepOutput hgoodAfterOutput hcollarWaveOutput hprofileAuxLane
        hdepthThresholdLane hCup M m E hstate sigma hE2 hd hsigma0 hsigmaHalf hX hk0 hmaxLane
          hrareChoice k R hR
  obtain ⟨Uone, Uexp, hUone0, hUoneM, hUexp0, hUexpM,
      hdom, hOone, hOexp⟩ :=
    superposedFlux_upper_per_descendant_split M m E hstate sigma Clane
      hsigma0 hsigmaHalf hmaxLane hE2 hlanePos
      hgoodBaseOutput hgoodHeadOutput hgoodBandOutput hgoodDeepOutput
      hgoodAfterOutput hgoodWaveOutput hcollarBaseOutput hcollarHeadOutput
      hcollarBandOutput hcollarDeepOutput hcollarAfterOutput hcollarWaveOutput
      hprofileAuxLane hdepthThresholdLane hk0 k R hR
  refine ⟨Uone, Uexp, hUone0, hUoneM, hUexp0, hUexpM, hdom, hOone, ?_⟩
  exact hOexp.mono_scale
    (coarseEllipticity_rawRareScale_le_normalized
      hd hlanePos hCup hX hrareChoice k)

/-- The direct upper half of the exact coarse-ellipticity theorem. One
dimension-only constant is selected before the model and every scale; the
small-scale branch is handled above, while the large-scale branch constructs
the twelve-lane per-descendant split and aggregates all finite and infinite
exponents. -/
theorem superposedFlux_coarse_ellipticity_upper_leg (d : ℕ) :
    ∃ Cup : ℝ, 0 < Cup ∧
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
          max (Real.exp (Cup / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          ∀ q : CoarseEllipticityExponent,
            ∀ s : ℝ,
              ∀ hsWindow : s ∈ Set.Icc
                (M.gamma / 2 +
                  Real.exp
                    (-(Cup⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1,
              Probability.IsDeterministicShiftTwoTermOneSidedOrlicz
                (Cutoff.cutoffSampleLaw M).toMeasure
                (HCPolySupport.IndependentSums.gammaSigma 1)
                (HCPolySupport.IndependentSums.gammaSigma
                  ((1 - sigma) / 3))
                (fun omega =>
                  Observable.cutoffUpperEllipticity
                      M m m s
                      (by
                        exact
                          (add_pos
                            (div_pos M.shellPrefix.gamma_pos (by norm_num))
                          (Real.exp_pos
                            (-(Cup⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                                M.gamma⁻¹)))).trans_le hsWindow.1)
                      q omega *
                    (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹)
                Cup
                (Cup * (Disorder.cstar M)⁻¹ * s * M.gamma *
                  (2 * s - M.gamma)⁻¹ ^ 3)
                (Real.exp
                  (-(Cup⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) := by
  let previousLaneOutput : ℝ := max
    (goodHeadTunedOutputConst d)
    (max
      (probeSharpBandMeanTunedOutputConst d)
      (max
        (probeSharpDeepBandTailTunedOutputConst d)
        (max
          (probeSharpCollarBaseTunedOutputConst d)
          (max
            (collarHeadTunedPerDescendantOutputConst d)
            (max
              (collarAfterBandTunedOutputConst d)
              (max
                (probeSharpWaveTailTunedOutputConst d)
                (max
                  (Provider.Multiscale.probeSharpGoodBaseConst d)
                  (max
                    (collarBandMeanTunedOutputConst d)
                    (collarDeepTailTunedOutputConst d)))))))))
  let laneOutput : ℝ := max previousLaneOutput (max
    (probeSharpAfterBandTunedOutputConst d)
    (probeSharpCollarWaveTailTunedOutputConst d))
  let Clane : ℝ :=
    max 4 (max
      (directSmallUpperMassConst d)
      (max
        (profileAuxiliaryConst d)
        (max
          (collarBandMeanDepthThreshold d)
          laneOutput)))
  let Cblock : ℝ :=
    (12 + 12 * HCPolySupport.IndependentSums.gammaTriangleConst 1) * Clane
  let Cmerge : ℝ := coarseEllipticityUpperMergeConst d
  let Cup : ℝ := Cblock * Cmerge
  obtain ⟨hlanePos, hlaneBlock, hblockPos, hmergeOne, hblockCup, hfour, hgoodHeadOutput,
    hgoodBandOutput, hgoodDeepOutput, hcollarBaseOutput, hcollarHeadOutput, hcollarAfterOutput,
      hgoodWaveOutput, hgoodBaseOutput, hcollarBandOutput, hcollarDeepOutput, hgoodAfterOutput,
        hcollarWaveOutput, hprofileAuxLane, hdepthThresholdLane, hmassConst, hdepthThreshold,
          hCup⟩ :=
    (show (0 < Clane) ∧ (Clane ≤ Cblock) ∧ (0 < Cblock) ∧ (1 ≤ Cmerge) ∧ (Cblock ≤ Cup) ∧ (4 ≤
      Cup) ∧ (goodHeadTunedOutputConst d ≤ Clane) ∧ (probeSharpBandMeanTunedOutputConst d ≤ Clane)
        ∧ (probeSharpDeepBandTailTunedOutputConst d ≤ Clane) ∧
          (probeSharpCollarBaseTunedOutputConst d ≤ Clane) ∧
            (collarHeadTunedPerDescendantOutputConst d ≤ Clane) ∧ (collarAfterBandTunedOutputConst
              d ≤ Clane) ∧ (probeSharpWaveTailTunedOutputConst d ≤ Clane) ∧
                (Provider.Multiscale.probeSharpGoodBaseConst d ≤ Clane) ∧
                  (collarBandMeanTunedOutputConst d ≤ Clane) ∧ (collarDeepTailTunedOutputConst d ≤
                    Clane) ∧ (probeSharpAfterBandTunedOutputConst d ≤ Clane) ∧
                      (probeSharpCollarWaveTailTunedOutputConst d ≤ Clane) ∧
                        (profileAuxiliaryConst d ≤ Clane) ∧ (collarBandMeanDepthThreshold d ≤
                          Clane) ∧ (directSmallUpperMassConst d ≤ Cup) ∧
                            (collarBandMeanDepthThreshold d ≤ Cup) ∧ (0 < Cup) from
      @upperLeg_comparisonBounds1 (d))
  refine ⟨Cup, hCup, ?_⟩
  intro M m E hstate sigma hsigma hE1 hE2 q s hsWindow
  by_cases hm : m ≤ mStarStar M
  · exact coarse_ellipticity_upper_of_le_mStarStar
      M m hm hfour hmassConst E sigma hsigma q s hsWindow
  · have hd : 2 ≤ d := M.shellPrefix.dimension
    let : NeZero d := ⟨by omega⟩
    have hsigma0 : 0 < sigma := hsigma.1
    have hsigmaHalf : sigma ≤ 1 / 2 := hsigma.2
    have hgamma : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) :=
      gamma_le_zpow_neg_five_of_frozenGate
        E.property M.shellPrefix.gamma_pos hE2
    have hX : Cup ≤ (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹ := by
      exact outputConst_le_invSq_mul_gammaInv_of_gate
        M hCup.le hsigma0 hsigmaHalf E.property
          ((le_max_left _ _).trans hE1) hgamma
    have hlarge : collarBandMeanDepthThreshold d ≤
        (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹ :=
      hdepthThreshold.trans hX
    have hk0 : 3 ≤ collarBandMeanDepth M (E : ℝ) := by
      exact three_le_waveBandDepth_collarBandMeanDepthCoeff
        (lt_of_lt_of_le zero_lt_one E.property) M.shellPrefix.gamma_pos rfl hlarge
    have hmaxLane : max (Real.exp (Clane / sigma))
        (Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
      refine max_le ?_ ((le_max_right _ _).trans hE1)
      exact (Real.exp_le_exp.mpr
        ((div_le_div_iff_of_pos_right hsigma0).2
          (hlaneBlock.trans hblockCup))).trans
          ((le_max_left _ _).trans hE1)
    have hmergeRare :
        (12 * upperAfterBandRareTriangleConst) *
          coarseEllipticityRareBudgetConst d + 15 ≤ Cmerge := by
      dsimp only [Cmerge, coarseEllipticityUpperMergeConst]
      exact (le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))
    have hblockCoeffOne : (1 : ℝ) ≤
        12 + 12 * HCPolySupport.IndependentSums.gammaTriangleConst 1 :=
      (by norm_num : (1 : ℝ) ≤ 12).trans
        (le_add_of_nonneg_right (mul_nonneg (by norm_num)
          HCPolySupport.IndependentSums.gammaTriangleConst_pos.le))
    have hmergeLeRatio : Cmerge ≤ Clane⁻¹ * Cup := by
      calc
        Cmerge = 1 * Cmerge := by ring
        _ ≤ (12 + 12 * HCPolySupport.IndependentSums.gammaTriangleConst 1) *
              Cmerge := mul_le_mul_of_nonneg_right hblockCoeffOne
                (zero_le_one.trans hmergeOne)
        _ = Clane⁻¹ * Cup := by
          dsimp only [Cup, Cblock]
          field_simp [hlanePos.ne']
    have hrareChoice :
        (12 * upperAfterBandRareTriangleConst) *
          coarseEllipticityRareBudgetConst d + 15 ≤ Clane⁻¹ * Cup :=
      hmergeRare.trans hmergeLeRatio
    have hperDescendant :
      ∀ (k : ℕ) (R : TriadicCube d),
        R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)) →
          ∃ Uone Uexp : Cutoff.CutoffSample d → ℝ,
            (∀ omega, 0 ≤ Uone omega) ∧
            Measurable Uone ∧
            (∀ omega, 0 ≤ Uexp omega) ∧
            Measurable Uexp ∧
            (∀ omega,
              cutoffBBlockFamily
                  M m (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ R omega ≤
                Cblock + Uone omega + Uexp omega) ∧
            HCPolySupport.IndependentSums.IsBigOWith
              (Cutoff.cutoffSampleLaw M).toMeasure
              (HCPolySupport.IndependentSums.gammaSigma 1) Uone
              (upperSaturatedPerCubeAmplitude
                Cblock (Disorder.cstar M) M.gamma k) ∧
            HCPolySupport.IndependentSums.IsBigOWith
              (Cutoff.cutoffSampleLaw M).toMeasure
              (HCPolySupport.IndependentSums.gammaSigma ((1 - sigma) / 3)) Uexp
              ((coarseEllipticityRareBudgetConst d)⁻¹ *
                ((3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) *
                  (Real.exp
                    (-(Cup⁻¹ * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))) ^ 15))  := @upperLeg_estimate1 (d)
                      (hlanePos) (hgoodHeadOutput) (hgoodBandOutput) (hgoodDeepOutput)
                        (hcollarBaseOutput) (hcollarHeadOutput) (hcollarAfterOutput)
                          (hgoodWaveOutput) (hgoodBaseOutput) (hcollarBandOutput)
                            (hcollarDeepOutput) (hgoodAfterOutput) (hcollarWaveOutput)
                              (hprofileAuxLane) (hdepthThresholdLane) (hCup) (M) (m) (E) (hstate)
                                (sigma) (hE2) (hd) (hsigma0) (hsigmaHalf) (hX) (hk0) (hmaxLane)
                                  (hrareChoice)
    let eps : ℝ := Real.exp
      (-(Cup⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))
    have heps : 0 < eps := by
      dsimp only [eps]
      exact Real.exp_pos _
    have heps1 : eps ≤ 1 := by
      dsimp only [eps]
      exact exp_neg_frozen_le_one hCup M.shellPrefix.gamma_pos
    have hhalf : M.gamma / 2 < s :=
      (lt_add_of_pos_right _ heps).trans_le hsWindow.1
    have hs : 0 < s := (div_pos M.shellPrefix.gamma_pos (by norm_num)).trans hhalf
    have hgap : 0 < 2 * s - M.gamma := by linarith
    have hscaling : 0 ≤ (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ :=
      inv_nonneg.mpr (Annealed.sigmaBar M (m - 1)).2.le
    have hgamma1 : M.gamma ≤ 1 :=
      M.shellPrefix.gamma_le_quarter.trans (by norm_num)
    have hdetHead : 4 * Cblock ≤ Cup := by
      calc
        4 * Cblock = Cblock * 4 := by ring
        _ ≤ Cblock * Cmerge := mul_le_mul_of_nonneg_left (by
          dsimp only [Cmerge, coarseEllipticityUpperMergeConst]
          exact le_max_left _ _) hblockPos.le
        _ = Cup := by rfl
    have hltHead :
        147456 * HCPolySupport.IndependentSums.gammaTriangleConst 1 *
            gridNetConst d 1 * Cblock ≤ Cup := by
      calc
        _ = Cblock * (147456 * HCPolySupport.IndependentSums.gammaTriangleConst 1 *
            gridNetConst d 1) := by ring
        _ ≤ Cblock * Cmerge := mul_le_mul_of_nonneg_left (by
          dsimp only [Cmerge, coarseEllipticityUpperMergeConst]
          exact (le_max_left _ _).trans (le_max_right _ _)) hblockPos.le
        _ = Cup := by rfl
    have hgeHead : 1152 * triadicJointDepthEntropyConst d * Cblock ≤ Cup := by
      calc
        _ = Cblock * (1152 * triadicJointDepthEntropyConst d) := by ring
        _ ≤ Cblock * Cmerge := mul_le_mul_of_nonneg_left (by
          dsimp only [Cmerge, coarseEllipticityUpperMergeConst]
          exact (le_max_left _ _).trans
            ((le_max_right _ _).trans (le_max_right _ _))) hblockPos.le
        _ = Cup := by rfl
    have hlt := fun (r : {r : ℝ // 1 ≤ r}) (hr : (r : ℝ) < 2) =>
      upper_finite_lt_two_of_per_descendant
        hd M m r hr hsigma0 hsigmaHalf hs hsWindow.2 hscaling hblockPos heps heps1
          hsWindow.1 hCup hdetHead hltHead (by
            simpa only [coarseEllipticityRareBudgetConst,
              upperFiniteQLtTwoRareBudgetConst, eps, mul_assoc] using hperDescendant)
    have hgeinf :=
      upper_finite_two_le_and_infinity_of_per_descendant
        hd M m hsigma0 hsigmaHalf hs hsWindow.2 hscaling hblockPos heps heps1
          hgamma1 hgap hsWindow.1 hCup hblockCup hgeHead (by
            simpa only [coarseEllipticityRareBudgetConst, eps, mul_assoc] using
              hperDescendant)
    rcases coarseEllipticityExponent_trichotomy q with
      ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | rfl
    · simpa only [eps] using hlt r hr
    · simpa only [eps] using hgeinf.1 r hr
    · simpa only [eps] using hgeinf.2 _ rfl

end Algsuperdiff.Section3.Provider.CoarseEllipticity
