/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.ZerothOrderOneStep
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.DyadicRadii

/-!
# ZerothOrderIteration

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Dyadic iteration with a geometrically decaying scalar source
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

private theorem affineContraction_with_halfGeometricSource
    {A : ℕ → ℝ} {q B C : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hA : ∀ n, 0 ≤ A n)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hrec : ∀ n, A (n + 1) ≤ q * A n + B + C * (1 / 2 : ℝ) ^ n) :
    ∀ n, A n ≤ A 0 + (1 - q)⁻¹ * B + 2 * C := by
  have hqle : q ≤ 1 := hq1.le
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hgeom : ∀ n : ℕ,
      A n ≤ A 0 + (1 - q)⁻¹ * B +
        C * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := by
    intro n
    induction n with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
        exact le_add_of_nonneg_right <|
          mul_nonneg (inv_nonneg.mpr hden.le) hB
    | succ n ih =>
        have hqA : q * A 0 ≤ A 0 := by
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hqle (hA 0))
        have hqB : q * ((1 - q)⁻¹ * B) + B = (1 - q)⁻¹ * B := by
          have hne : 1 - q ≠ 0 := hden.ne'
          field_simp [hne]
          ring
        have hsum0 : 0 ≤ ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i :=
          Finset.sum_nonneg fun i _ => pow_nonneg (by norm_num) i
        have hqC : q * (C * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i) ≤
            C * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hqle
            (mul_nonneg hC hsum0)
        calc
          A (n + 1) ≤ q * A n + B + C * (1 / 2 : ℝ) ^ n := hrec n
          _ ≤ q * (A 0 + (1 - q)⁻¹ * B +
                C * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i) + B +
              C * (1 / 2 : ℝ) ^ n := by
            exact add_le_add
              (add_le_add (mul_le_mul_of_nonneg_left ih hq0) le_rfl) le_rfl
          _ ≤ A 0 + (1 - q)⁻¹ * B +
              C * ∑ i ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ i := by
            rw [Finset.sum_range_succ]
            calc
              q * (A 0 + (1 - q)⁻¹ * B +
                    C * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i) + B +
                  C * (1 / 2 : ℝ) ^ n
                  = q * A 0 + (q * ((1 - q)⁻¹ * B) + B) +
                      q * (C * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i) +
                      C * (1 / 2 : ℝ) ^ n := by ring
              _ ≤ A 0 + (1 - q)⁻¹ * B +
                    C * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i +
                    C * (1 / 2 : ℝ) ^ n := by
                rw [hqB]
                exact add_le_add (add_le_add (add_le_add hqA le_rfl) hqC) le_rfl
              _ = A 0 + (1 - q)⁻¹ * B +
                    C * (∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i +
                      (1 / 2 : ℝ) ^ n) := by ring
  intro n
  have hn := hgeom n
  have hsum := sum_geometric_two_le n
  have hCsum := mul_le_mul_of_nonneg_left hsum hC
  calc
    A n ≤ A 0 + (1 - q)⁻¹ * B +
        C * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := hn
    _ ≤ A 0 + (1 - q)⁻¹ * B + C * 2 := add_le_add le_rfl hCsum
    _ = A 0 + (1 - q)⁻¹ * B + 2 * C := by ring

/-- A scalar source whose dyadic contribution decays by one half adds only
the literal factor `2`, while the divergence source retains the printed
`8(1-alpha)⁻¹` factor. -/
theorem dyadicSmallContrastIteration_zerothOrder
    {A : ℕ → ℝ} {alpha B C : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hA : ∀ n, 0 ≤ A n) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hrec : ∀ n, A (n + 1) ≤
      smallContrastContraction alpha * A n + B + C * (1 / 2 : ℝ) ^ n) :
    ∀ n, A n ≤ A 0 + 8 * (1 - alpha)⁻¹ * B + 2 * C := by
  have hq := smallContrastContraction_mem_Ioo halpha0 halpha1
  have hraw := affineContraction_with_halfGeometricSource
    hq.1.le hq.2 hA hB hC hrec
  have hinv := inv_one_sub_smallContrastContraction_le halpha1
  intro n
  have hn := hraw n
  have hmul : (1 - smallContrastContraction alpha)⁻¹ * B ≤
      8 * (1 - alpha)⁻¹ * B :=
    mul_le_mul_of_nonneg_right hinv hB
  calc
    A n ≤ A 0 + (1 - smallContrastContraction alpha)⁻¹ * B + 2 * C := hn
    _ ≤ A 0 + 8 * (1 - alpha)⁻¹ * B + 2 * C :=
      add_le_add (add_le_add le_rfl hmul) le_rfl

private theorem weighted_half_step_zerothOrder
    {e e' f g c kf kg r theta w w' P rinv D G : ℝ}
    (hkf : 0 ≤ kf) (hkg : 0 ≤ kg) (hr : 0 ≤ r)
    (htheta : 0 ≤ theta) (hw : 0 ≤ w)
    (hstep : e' ≤ c * e + kf * f + kg * r * g)
    (hf : f ≤ P * rinv * D) (hg0 : 0 ≤ g) (hg : g ≤ G)
    (hw' : w' = theta * w) (hcancel : w * rinv = 1) (hw'le : w' ≤ 1) :
    w' * e' ≤ (c * theta) * (w * e) + theta * kf * P * D + kg * r * G := by
  have hw'0 : 0 ≤ w' := by rw [hw']; positivity
  have hstep' := mul_le_mul_of_nonneg_left hstep hw'0
  have hf' := mul_le_mul_of_nonneg_left hf
    (mul_nonneg (mul_nonneg htheta hkf) hw)
  have hg' : w' * g ≤ G := by
    simpa only [one_mul] using mul_le_mul hw'le hg hg0 zero_le_one
  have hscalar := mul_le_mul_of_nonneg_left hg' (mul_nonneg hkg hr)
  calc
    w' * e' ≤ w' * (c * e + kf * f + kg * r * g) := hstep'
    _ = (c * theta) * (w * e) + theta * kf * w * f + kg * r * (w' * g) := by
      rw [hw']
      ring
    _ ≤ (c * theta) * (w * e) + theta * kf * w * (P * rinv * D) +
        kg * r * (w' * g) := add_le_add (add_le_add le_rfl hf') le_rfl
    _ ≤ (c * theta) * (w * e) + theta * kf * w * (P * rinv * D) +
        kg * r * G := add_le_add le_rfl hscalar
    _ = (c * theta) * (w * e) + theta * kf * P * D + kg * r * G := by
      have hmiddle : theta * kf * w * (P * rinv * D) = theta * kf * P * D := by
        calc
          theta * kf * w * (P * rinv * D) =
              theta * kf * P * (w * rinv) * D := by ring
          _ = theta * kf * P * D := by rw [hcancel, mul_one]
      rw [hmiddle]

/-- The concrete dyadic estimate on an interior ball for an equation with both
a divergence source and a bounded scalar source.  The scalar price is uniform
in `alpha`. -/
theorem dyadicGradientScaleBound_zerothOrder_on_interiorBall [NeZero d]
    {U : Set (Vec d)} (z : Vec d) {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (houter : euclideanBall z R ⊆ U)
    {a : CoeffField d} {u : H1Function U} {g : Vec d → ℝ} {f : Vec d → Vec d}
    {delta alpha : ℝ}
    (hd : 2 ≤ d) (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hUopen : IsOpen U) (hmeas : Measurable a)
    (ha : CoefficientIdentityDistanceLE U a delta)
    (hu : IsMatrixDivFormWeakSolutionZerothOrderOn a U u g f)
    (hg : MemScalarLInfOn U g)
    (hf : MemVectorLpOn U (schauderSourceExponent d alpha) f) :
    ∀ n : ℕ,
      smallContrastDyadicRadius R n ^ (1 - alpha) *
          vectorNormalizedL2On
            (euclideanBall z (smallContrastDyadicRadius R n)) u.grad ≤
        R ^ (1 - alpha) * vectorNormalizedL2On (euclideanBall z R) u.grad +
          16 * (1 - alpha)⁻¹ *
            ((1 / 2 : ℝ) ^ (-(d : ℝ) / 2) * smallContrastUnitBallVolumePrice d) *
            vectorLpSizeOn U (schauderSourceExponent d alpha) f +
          8 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
            unitCubeDirichletPoincareExplicit d * (d : ℝ) * scalarLInfSizeOn U g := by
  let p : ℝ := schauderSourceExponent d alpha
  let A : ℕ → ℝ := fun n =>
    smallContrastDyadicRadius R n ^ (1 - alpha) *
      vectorNormalizedL2On (euclideanBall z (smallContrastDyadicRadius R n)) u.grad
  let B : ℝ := 2 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
    smallContrastUnitBallVolumePrice d * vectorLpSizeOn U p f
  let C : ℝ := 4 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
    unitCubeDirichletPoincareExplicit d * (d : ℝ) * scalarLInfSizeOn U g
  have hp2 : 2 ≤ p := two_le_schauderSourceExponent hd halpha0.le halpha1
  have hA0 : ∀ n, 0 ≤ A n := fun n => mul_nonneg
    (Real.rpow_nonneg (smallContrastDyadicRadius_pos hR n).le _)
    (Real.sqrt_nonneg _)
  have hB0 : 0 ≤ B := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
        (smallContrastUnitBallVolumePrice_nonneg d)) ENNReal.toReal_nonneg
  have hC0 : 0 ≤ C := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
          (unitCubeDirichletPoincareExplicit_nonneg d)) (Nat.cast_nonneg d))
      ENNReal.toReal_nonneg
  have hrecRaw : ∀ n,
      A (n + 1) ≤
        ((1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)) *
          (1 / 2 : ℝ) ^ (1 - alpha)) * A n + B + C * (1 / 2 : ℝ) ^ n := by
    intro n
    let r : ℝ := smallContrastDyadicRadius R n
    let V : Set (Vec d) := euclideanBall z r
    have hr : 0 < r := smallContrastDyadicRadius_pos hR n
    have hrR : r ≤ R := smallContrastDyadicRadius_le hR.le n
    have hVU : V ⊆ U := by
      rcases eq_or_lt_of_le hrR with heq | hlt
      · simpa only [V, r, heq] using houter
      · exact (euclideanBall_subset_euclideanBall hr.le hlt).trans houter
    let uV : H1Function V := u.restrict (isOpen_euclideanBall z r) hVU
    let finiteVolumeV : IsFiniteMeasure (volumeMeasureOn V) :=
      HCPolySupport.Book.Ch01.isFiniteMeasure_volumeMeasureOn_euclideanBall z r
    have haV : CoefficientIdentityDistanceLE V a delta :=
      ha.filter_mono (ae_mono (Measure.restrict_mono hVU le_rfl))
    have huV := isMatrixDivFormWeakSolutionZerothOrderOn_restrict
      hUopen (isOpen_euclideanBall z r) hVU hu
    have hg2V := memScalarL2_of_memScalarLInfOn_of_subset hVU hg
    have hf2V := memVectorL2_of_memVectorLpOn_of_subset hp2 hVU hf
    have hstep0 := oneStep_normalizedGradient_half_zerothOrder z hr hmeas haV
      halpha0 halpha1 hdelta0 hdelta huV hg2V hf2V
    have hstep :
        vectorNormalizedL2On (euclideanBall z (r / 2)) u.grad ≤
          (1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)) *
              vectorNormalizedL2On V u.grad +
            2 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) * vectorNormalizedL2On V f +
            4 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) * unitCubeDirichletPoincareExplicit d *
              (d : ℝ) * r * normalizedL2On V g := by
      simpa only [uV, H1Function.restrict] using hstep0
    have hfV := vectorNormalizedL2On_euclideanBall_le_price_mul_rpow_mul_globalLp
      (d := d) z hr hp2 hVU hf
    have hgV := normalizedL2On_le_scalarLInfSizeOn hVU
      (lt_of_le_of_ne ENNReal.toReal_nonneg
        (Ne.symm (HCPolySupport.Book.Ch01.volume_euclideanBall_toReal_ne_zero z hr))) hg
    have hweight := smallContrastDyadicRadius_succ_rpow
      (alpha := alpha) hR.le n
    have hcancel := smallContrast_source_scale_cancel
      (alpha := alpha) (r := r) (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)) halpha1 hr
    have hr1 : r ≤ 1 := hrR.trans hR1
    have hrnext1 : smallContrastDyadicRadius R (n + 1) ≤ 1 :=
      (smallContrastDyadicRadius_le hR.le (n + 1)).trans hR1
    have hw'le : smallContrastDyadicRadius R (n + 1) ^ (1 - alpha) ≤ 1 :=
      Real.rpow_le_one (smallContrastDyadicRadius_pos hR (n + 1)).le hrnext1
        (sub_nonneg.mpr halpha1.le)
    have hraw := weighted_half_step_zerothOrder
      (e := vectorNormalizedL2On V u.grad)
      (e' := vectorNormalizedL2On (euclideanBall z (r / 2)) u.grad)
      (f := vectorNormalizedL2On V f) (g := normalizedL2On V g)
      (c := 1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2))
      (kf := 2 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2))
      (kg := 4 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
        unitCubeDirichletPoincareExplicit d * (d : ℝ))
      (r := r) (theta := (1 / 2 : ℝ) ^ (1 - alpha))
      (w := r ^ (1 - alpha))
      (w' := smallContrastDyadicRadius R (n + 1) ^ (1 - alpha))
      (P := smallContrastUnitBallVolumePrice d)
      (rinv := r ^ (-(d : ℝ) / p))
      (D := vectorLpSizeOn U p f) (G := scalarLInfSizeOn U g)
      (by positivity)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
          (unitCubeDirichletPoincareExplicit_nonneg d)) (Nat.cast_nonneg d))
      hr.le (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hr.le _)
      hstep hfV (normalizedL2On_nonneg _ _) hgV hweight hcancel hw'le
    have hsource := half_source_coefficient_le_dimension_only
      (d := d) (alpha := alpha) halpha1
    have hsourcePrice := mul_le_mul_of_nonneg_right hsource
      (smallContrastUnitBallVolumePrice_nonneg d)
    have hsourceMul := mul_le_mul_of_nonneg_right hsourcePrice
      (show 0 ≤ vectorLpSizeOn U p f from ENNReal.toReal_nonneg)
    have hrhalf : r ≤ (1 / 2 : ℝ) ^ n := by
      dsimp only [r, smallContrastDyadicRadius]
      rw [Real.rpow_natCast]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hR1 (pow_nonneg (by norm_num) n)
    have hscalar := mul_le_mul_of_nonneg_left hrhalf hC0
    change A (n + 1) ≤ _
    rw [show r / 2 = smallContrastDyadicRadius R (n + 1) by
      exact (smallContrastDyadicRadius_succ R n).symm] at hraw
    calc
      A (n + 1) ≤
          ((1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)) *
            (1 / 2 : ℝ) ^ (1 - alpha)) * A n +
            ((2 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
              (1 / 2 : ℝ) ^ (1 - alpha)) * smallContrastUnitBallVolumePrice d) *
              vectorLpSizeOn U p f + C * r := by
        convert hraw using 1
        all_goals dsimp only [C]
        all_goals ring
      _ ≤ ((1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)) *
            (1 / 2 : ℝ) ^ (1 - alpha)) * A n + B + C * r := by
        exact add_le_add (add_le_add le_rfl hsourceMul) le_rfl
      _ ≤ ((1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)) *
            (1 / 2 : ℝ) ^ (1 - alpha)) * A n + B + C * (1 / 2 : ℝ) ^ n :=
        add_le_add le_rfl hscalar
  have hcoef := dyadic_smallContrast_contraction halpha0 halpha1 hdelta
  have hrec : ∀ n, A (n + 1) ≤
      smallContrastContraction alpha * A n + B + C * (1 / 2 : ℝ) ^ n := by
    intro n
    have hAn := hA0 n
    exact (hrecRaw n).trans <| by
      gcongr
  have hiter := dyadicSmallContrastIteration_zerothOrder
    halpha0 halpha1 hA0 hB0 hC0 hrec
  intro n
  have hn := hiter n
  dsimp only [A, B, C, p] at hn
  rw [smallContrastDyadicRadius_zero] at hn
  convert hn using 1
  all_goals ring

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
