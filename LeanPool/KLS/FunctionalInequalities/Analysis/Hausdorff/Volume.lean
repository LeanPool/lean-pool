/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Hausdorff.Isodiametric
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
# Hausdorff normalization and volume

Covering and the isodiametric inequality identify Mathlib’s diameter-gauge Hausdorff measure
with a scalar multiple of volume. The normalized top-dimensional measure equals volume,
including dimension zero. Existing Analysis and KLS namespaces are preserved.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Pointwise

namespace FunctionalInequalities

universe u

namespace Analysis

section Isodiametric

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- One half of the normalization identity, by covering: `volume ≤ (ω_n / 2^n) • μH[n]`. -/
theorem volume_le_ofReal_mul_hausdorffMeasure (S : Set V) :
    volume S ≤
      ENNReal.ofReal (KLS.unitBallVolume (Module.finrank ℝ V) / 2 ^ Module.finrank ℝ V) *
        μH[(Module.finrank ℝ V : ℝ)] S := by
  have hωpos : 0 < KLS.unitBallVolume (Module.finrank ℝ V) := by
    unfold KLS.unitBallVolume
    positivity
  have hkey : (ENNReal.ofReal (2 ^ Module.finrank ℝ V / KLS.unitBallVolume (Module.finrank ℝ V))
      • (volume : Measure V)) ≤ μH[(Module.finrank ℝ V : ℝ)] := by
    refine Measure.le_hausdorffMeasure (Module.finrank ℝ V : ℝ) _ 1 one_pos ?_
    intro s hs
    have hb : Bornology.IsBounded s :=
      Metric.isBounded_iff_ediam_ne_top.mpr (ne_top_of_le_ne_top ENNReal.one_ne_top hs)
    have hd0 : (0:ℝ) ≤ Metric.diam s := Metric.diam_nonneg
    rw [Measure.smul_apply, smul_eq_mul]
    calc ENNReal.ofReal (2 ^ Module.finrank ℝ V / KLS.unitBallVolume (Module.finrank ℝ V))
          * volume s
        ≤ ENNReal.ofReal (2 ^ Module.finrank ℝ V / KLS.unitBallVolume (Module.finrank ℝ V))
          * ENNReal.ofReal (KLS.unitBallVolume (Module.finrank ℝ V)
            * (Metric.diam s / 2) ^ Module.finrank ℝ V) := by
          gcongr
          exact isodiametric s hb
      _ = ENNReal.ofReal (Metric.diam s ^ Module.finrank ℝ V) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [div_pow]
          field_simp
      _ = Metric.ediam s ^ (Module.finrank ℝ V : ℝ) := by
          have hdiam : ENNReal.ofReal (Metric.diam s) = Metric.ediam s := by
            unfold Metric.diam
            rw [ENNReal.ofReal_toReal hb.ediam_ne_top]
          rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow hd0, hdiam]
  have := (Measure.le_iff'.mp hkey) S
  rw [Measure.smul_apply, smul_eq_mul] at this
  calc volume S
      = ENNReal.ofReal (KLS.unitBallVolume (Module.finrank ℝ V) / 2 ^ Module.finrank ℝ V)
        * (ENNReal.ofReal (2 ^ Module.finrank ℝ V / KLS.unitBallVolume (Module.finrank ℝ V))
          * volume S) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        rw [show KLS.unitBallVolume (Module.finrank ℝ V) / 2 ^ Module.finrank ℝ V
            * (2 ^ Module.finrank ℝ V / KLS.unitBallVolume (Module.finrank ℝ V)) = 1 by
          field_simp]
        simp
    _ ≤ _ := by gcongr

/-- The unit ball has `μH[n]`-measure at most `2^n / ω_n` times its Lebesgue measure: a
Besicovitch covering by disjoint balls of vanishing radius, at each scale of the `mkMetric`
premeasure.  The leftover set is Lebesgue-null, hence `μH[n]`-null by Haar uniqueness. -/
private theorem hausdorffMeasure_ball_le [Nontrivial V] :
    (μH[(Module.finrank ℝ V : ℝ)] : Measure V) (Metric.ball 0 1)
      ≤ ENNReal.ofReal (2 ^ Module.finrank ℝ V / KLS.unitBallVolume (Module.finrank ℝ V))
        * volume (Metric.ball (0:V) 1) := by
  set n := Module.finrank ℝ V with hn
  have hωpos : 0 < KLS.unitBallVolume n := by unfold KLS.unitBallVolume; positivity
  have hsmul : (μH[(n : ℝ)] : Measure V)
      = (((μH[(n : ℝ)] : Measure V).addHaarScalarFactor (volume : Measure V) : ℝ≥0) : ℝ≥0∞)
        • (volume : Measure V) :=
    Measure.isAddLeftInvariant_eq_smul _ _
  set P : ℕ → OuterMeasure V := fun k =>
    OuterMeasure.mkMetric'.pre (fun s : Set V => (Metric.ediam s) ^ (n : ℝ)) (k : ℝ≥0∞)⁻¹ with hP
  have hcoe : ∀ s : Set V, (μH[(n : ℝ)] : Measure V) s = ⨆ k : ℕ, P k s := by
    intro s
    have h1 : (μH[(n : ℝ)] : Measure V) s
        = (OuterMeasure.mkMetric (fun r : ℝ≥0∞ => r ^ (n : ℝ)) : OuterMeasure V) s := by
      rw [OuterMeasure.coe_mkMetric]; rfl
    rw [h1, show (OuterMeasure.mkMetric (fun r : ℝ≥0∞ => r ^ (n : ℝ)) : OuterMeasure V)
      = OuterMeasure.mkMetric' (fun s : Set V => (Metric.ediam s) ^ (n : ℝ)) from rfl,
      OuterMeasure.mkMetric'.eq_iSup_nat, OuterMeasure.iSup_apply]
  have hPle : ∀ (k : ℕ) (s : Set V), P k s ≤ (μH[(n : ℝ)] : Measure V) s := by
    intro k s
    rw [hcoe s]
    exact le_iSup (fun j : ℕ => P j s) k
  rw [hcoe]
  refine iSup_le fun k => ?_
  set δ : ℝ := 1 / (4 * ((k : ℝ) + 1)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨t, r, htc, hts, hr, hnull, hdisj⟩ :=
    Besicovitch.exists_disjoint_closedBall_covering_ae (volume : Measure V)
      (fun _ => Set.Ioo 0 δ) (Metric.ball (0 : V) 1)
      (fun x _ δ' hδ' => ⟨min δ δ' / 2, ⟨by positivity, by
          have := min_le_left δ δ'; linarith⟩, ⟨by positivity, by
          have := min_le_right δ δ'; linarith⟩⟩)
      (fun x => min δ (1 - ‖x‖))
      (fun x hx => lt_min hδpos (by
        have : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx
        linarith))
  have hsub : ∀ x ∈ t, Metric.closedBall x (r x) ⊆ Metric.ball (0 : V) 1 := by
    intro x hx y hy
    have hrx := (hr x hx).2
    have hx1 : ‖x‖ < 1 := by
      have := hts hx; simpa [Metric.mem_ball, dist_zero_right] using this
    have h1 : ‖y - x‖ ≤ r x := by
      rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hy
    have h2 : r x < 1 - ‖x‖ := lt_of_lt_of_le hrx.2 (min_le_right _ _)
    have : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa using norm_add_le (y - x) x
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  have hediam : ∀ x ∈ t, Metric.ediam (Metric.closedBall x (r x))
      ≤ ENNReal.ofReal (2 * r x) := by
    intro x hx
    have hbd : Bornology.IsBounded (Metric.closedBall x (r x)) := Metric.isBounded_closedBall
    have h0 : (0:ℝ) ≤ r x := (hr x hx).2.1.le
    have : Metric.ediam (Metric.closedBall x (r x))
        = ENNReal.ofReal (Metric.diam (Metric.closedBall x (r x))) := by
      unfold Metric.diam
      rw [ENNReal.ofReal_toReal hbd.ediam_ne_top]
    rw [this]
    exact ENNReal.ofReal_le_ofReal (Metric.diam_closedBall h0)
  have hsmall : ∀ x ∈ t, Metric.ediam (Metric.closedBall x (r x)) ≤ (k : ℝ≥0∞)⁻¹ := by
    intro x hx
    refine (hediam x hx).trans ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hk1 : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hkpos : (0:ℝ) < (k : ℝ) := by linarith
      have hcast : ((k : ℕ) : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / (k : ℝ)) := by
        rw [one_div, ENNReal.ofReal_inv_of_pos hkpos, ENNReal.ofReal_natCast]
      rw [hcast]
      refine ENNReal.ofReal_le_ofReal ?_
      have hrx : r x < δ := (hr x hx).1.2
      rw [hδdef] at hrx
      have hpos4 : (0:ℝ) < 4 * ((k:ℝ) + 1) := by positivity
      have hrx' : r x * (4 * ((k:ℝ) + 1)) < 1 := (lt_div_iff₀ hpos4).mp hrx
      have hr0 : 0 < r x := (hr x hx).1.1
      rw [le_div_iff₀ hkpos]
      nlinarith
  have hcover : Metric.ball (0:V) 1 ⊆ (⋃ x ∈ t, Metric.closedBall x (r x))
      ∪ (Metric.ball (0:V) 1 \ ⋃ x ∈ t, Metric.closedBall x (r x)) := by
    intro y hy
    by_cases hmem : y ∈ ⋃ x ∈ t, Metric.closedBall x (r x)
    · exact Or.inl hmem
    · exact Or.inr ⟨hy, hmem⟩
  have hdiff0 : P k (Metric.ball (0:V) 1 \ ⋃ x ∈ t, Metric.closedBall x (r x)) = 0 := by
    refine le_antisymm ((hPle k _).trans ?_) (by simp)
    rw [hsmul, Measure.smul_apply, smul_eq_mul, hnull, mul_zero]
  have hterm : ∀ x ∈ t, P k (Metric.closedBall x (r x))
      ≤ ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n) * volume (Metric.closedBall x (r x)) := by
    intro x hx
    have hr0 : 0 < r x := (hr x hx).1.1
    have h1 : P k (Metric.closedBall x (r x))
        ≤ (Metric.ediam (Metric.closedBall x (r x))) ^ (n : ℝ) :=
      OuterMeasure.mkMetric'.pre_le (hsmall x hx)
    have h2 : (Metric.ediam (Metric.closedBall x (r x))) ^ (n : ℝ)
        ≤ (ENNReal.ofReal (2 * r x)) ^ (n : ℝ) :=
      ENNReal.rpow_le_rpow (hediam x hx) (Nat.cast_nonneg _)
    have h3 : (ENNReal.ofReal (2 * r x)) ^ (n : ℝ)
        = ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n) * volume (Metric.closedBall x (r x)) := by
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (by positivity),
        InnerProductSpace.volume_closedBall, ← ENNReal.ofReal_pow hr0.le,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      unfold KLS.unitBallVolume
      field_simp
      ring
    exact (h1.trans h2).trans_eq h3
  calc P k (Metric.ball (0:V) 1)
      ≤ P k (⋃ x ∈ t, Metric.closedBall x (r x))
        + P k (Metric.ball (0:V) 1 \ ⋃ x ∈ t, Metric.closedBall x (r x)) :=
        le_trans (measure_mono hcover) (measure_union_le _ _)
    _ = P k (⋃ x ∈ t, Metric.closedBall x (r x)) := by rw [hdiff0, add_zero]
    _ ≤ ∑' x : t, P k (Metric.closedBall (x : V) (r x)) := measure_biUnion_le _ htc _
    _ ≤ ∑' x : t, ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n)
          * volume (Metric.closedBall (x : V) (r x)) :=
        ENNReal.tsum_le_tsum fun x => hterm (x : V) x.2
    _ = ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n)
          * ∑' x : t, volume (Metric.closedBall (x : V) (r x)) := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n)
          * volume (⋃ x ∈ t, Metric.closedBall x (r x)) := by
        rw [measure_biUnion htc hdisj fun b _ => measurableSet_closedBall]
    _ ≤ ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n) * volume (Metric.ball (0:V) 1) := by
        gcongr
        exact Set.iUnion₂_subset hsub

variable (V) in
/-- Mathlib's top-dimensional Hausdorff measure of a finite-dimensional inner-product space is
`2^n / ω_n` times Lebesgue measure.  General form of `KLS.hausdorffNormalized_finrank_eq_volume`:
multiplying by `ENNReal.ofReal (ω_n / 2^n)` recovers `hausdorffNormalized V n = volume`. -/
theorem hausdorffMeasure_finrank_eq_smul_volume :
    (μH[(Module.finrank ℝ V : ℝ)] : Measure V) =
      ENNReal.ofReal (2 ^ Module.finrank ℝ V / KLS.unitBallVolume (Module.finrank ℝ V)) •
        (volume : Measure V) := by
  rcases subsingleton_or_nontrivial V with hsub | hnt
  · have hn0 : Module.finrank ℝ V = 0 := Module.finrank_zero_of_subsingleton
    have hval : (2 : ℝ) ^ (0 : ℕ) / KLS.unitBallVolume 0 = 1 := by simp [KLS.unitBallVolume]
    rw [hn0, hval, ENNReal.ofReal_one, one_smul, Nat.cast_zero]
    have hvolU : (volume : Measure V) Set.univ = 1 := by
      have hb := (stdOrthonormalBasis ℝ V).toBasis.addHaar_self
      have hne : (parallelepiped ((stdOrthonormalBasis ℝ V).toBasis)).Nonempty :=
        ⟨0, 0, by simp, by simp⟩
      rw [Subsingleton.eq_univ_of_nonempty hne] at hb
      exact hb
    have hHU : (μH[(0 : ℝ)] : Measure V) Set.univ = 1 := by
      rw [show (Set.univ : Set V) = {(0 : V)} from
        (Subsingleton.eq_univ_of_nonempty (Set.singleton_nonempty (0 : V))).symm]
      exact Measure.hausdorffMeasure_zero_singleton 0
    refine Measure.ext fun s _ => ?_
    rcases Set.eq_empty_or_nonempty s with rfl | hne
    · simp
    · rw [Subsingleton.eq_univ_of_nonempty hne, hHU, hvolU]
  · set n := Module.finrank ℝ V with hn
    have hωpos : 0 < KLS.unitBallVolume n := by unfold KLS.unitBallVolume; positivity
    have hsmul : (μH[(n : ℝ)] : Measure V)
        = (((μH[(n : ℝ)] : Measure V).addHaarScalarFactor (volume : Measure V) : ℝ≥0) : ℝ≥0∞)
          • (volume : Measure V) :=
      Measure.isAddLeftInvariant_eq_smul _ _
    set c : ℝ≥0 := (μH[(n : ℝ)] : Measure V).addHaarScalarFactor (volume : Measure V) with hcdef
    have hball : volume (Metric.ball (0 : V) 1) = ENNReal.ofReal (KLS.unitBallVolume n) := by
      rw [InnerProductSpace.volume_ball, hn]
      simp [KLS.unitBallVolume]
    have hV0 : volume (Metric.ball (0 : V) 1) ≠ 0 := by
      rw [hball]
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hωpos
    have hVtop : volume (Metric.ball (0 : V) 1) ≠ ⊤ := by rw [hball]; exact ENNReal.ofReal_ne_top
    have hcancel : ∀ a b : ℝ≥0∞, a * volume (Metric.ball (0 : V) 1)
        ≤ b * volume (Metric.ball (0 : V) 1) → a ≤ b := by
      intro a b hab
      calc a = a * volume (Metric.ball (0 : V) 1) * (volume (Metric.ball (0 : V) 1))⁻¹ := by
            rw [mul_assoc, ENNReal.mul_inv_cancel hV0 hVtop, mul_one]
        _ ≤ b * volume (Metric.ball (0 : V) 1) * (volume (Metric.ball (0 : V) 1))⁻¹ := by gcongr
        _ = b := by rw [mul_assoc, ENNReal.mul_inv_cancel hV0 hVtop, mul_one]
    have hle : (c : ℝ≥0∞) ≤ ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n) := by
      refine hcancel _ _ ?_
      have := hausdorffMeasure_ball_le (V := V)
      rwa [hsmul, Measure.smul_apply, smul_eq_mul] at this
    have hge : ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n) ≤ (c : ℝ≥0∞) := by
      have hlow := volume_le_ofReal_mul_hausdorffMeasure (Metric.ball (0 : V) 1)
      rw [hsmul, Measure.smul_apply, smul_eq_mul] at hlow
      have h1 : (1 : ℝ≥0∞) * volume (Metric.ball (0 : V) 1)
          ≤ (ENNReal.ofReal (KLS.unitBallVolume n / 2 ^ n) * c)
            * volume (Metric.ball (0 : V) 1) := by
        rw [one_mul, mul_assoc]
        exact hlow
      have h2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (KLS.unitBallVolume n / 2 ^ n) * c := hcancel _ _ h1
      calc ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n)
          = ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n) * 1 := (mul_one _).symm
        _ ≤ ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n)
              * (ENNReal.ofReal (KLS.unitBallVolume n / 2 ^ n) * c) := by gcongr
        _ = c := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
              show 2 ^ n / KLS.unitBallVolume n * (KLS.unitBallVolume n / 2 ^ n) = 1 by
                field_simp, ENNReal.ofReal_one, one_mul]
    rw [hsmul, le_antisymm hle hge]

end Isodiametric

end Analysis

end FunctionalInequalities

namespace FunctionalInequalities.KLS

universe u

section Normalization

variable (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V]

/-- Convention check: the normalized top-dimensional Hausdorff measure is Lebesgue measure on the
inner-product space (the isodiametric inequality).  Recorded so that the normalization of
`surfaceMeasure` is pinned by a statement rather than by a comment.

Proved from `Analysis.hausdorffMeasure_finrank_eq_smul_volume`, which pins Mathlib's diameter-gauge
`μH[n]` as `(2^n / ω_n) • volume`; the normalizing factor `ω_n / 2^n` of `hausdorffNormalized` is
its exact inverse, and `ω_n > 0` in every dimension.  In dimension zero the general input already
covers the subsingleton case and `ω_0 = 1`, so both sides are the unit mass at the single point. -/
theorem hausdorffNormalized_finrank_eq_volume :
    hausdorffNormalized V (Module.finrank ℝ V) = (volume : Measure V) := by
  have hωpos : 0 < unitBallVolume (Module.finrank ℝ V) := by
    unfold unitBallVolume; positivity
  rw [hausdorffNormalized, Analysis.hausdorffMeasure_finrank_eq_smul_volume V, smul_smul,
    ← ENNReal.ofReal_mul (by positivity),
    show unitBallVolume (Module.finrank ℝ V) / 2 ^ Module.finrank ℝ V
        * (2 ^ Module.finrank ℝ V / unitBallVolume (Module.finrank ℝ V)) = 1 by
      field_simp,
    ENNReal.ofReal_one, one_smul]

end Normalization

end FunctionalInequalities.KLS
