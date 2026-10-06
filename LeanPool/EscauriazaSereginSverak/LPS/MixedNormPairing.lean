/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.MixedNormProducts
public import LeanPool.EscauriazaSereginSverak.LPS.MixedNormMollification
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.SerrinPairingLimit
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCutoff
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Cutoff pairings for finite mixed norms

Spatial mollification converges in conjugate finite mixed norms. The cutoff
pairing then converges by mixed Hölder and dominated convergence.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private lemma lps_pairing_limit_of_L1_product_errors
    {T : ℝ} {f g : ParabolicPoint → ℝ} {a b : ℕ → ParabolicPoint → ℝ}
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hg : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (ha : ∀ n, AEStronglyMeasurable (a n)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hb : ∀ n, AEStronglyMeasurable (b n)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hBase : Integrable (fun z => f z * g z)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hProductPairs : ∀ᶠ n in atTop,
      Integrable (fun z => a n z * g z) (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) ∧
      Integrable (fun z => f z * b n z) (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) ∧
      Integrable (fun z => a n z * b n z) (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))))
    (hPairError1 : Tendsto (fun n => ∫⁻ z in spaceTimeSet Set.univ (Ioo 0 T), ‖a n z * g z‖ₑ)
      atTop (𝓝 0))
    (hPairError2 : Tendsto (fun n => ∫⁻ z in spaceTimeSet Set.univ (Ioo 0 T), ‖f z * b n z‖ₑ)
      atTop (𝓝 0))
    (hPairError3 : Tendsto (fun n => ∫⁻ z in spaceTimeSet Set.univ (Ioo 0 T), ‖a n z * b n z‖ₑ)
      atTop (𝓝 0)) :
    (∀ᶠ n in atTop, Integrable (fun z : ParabolicPoint =>
      serrinCutoff n (parabolicHomeomorph z).1 * (a n z + f z) * (b n z + g z))
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T)))) ∧
    Tendsto (fun n => ∫ z in spaceTimeSet Set.univ (Ioo 0 T),
      serrinCutoff n (parabolicHomeomorph z).1 * (a n z + f z) * (b n z + g z)) atTop
      (𝓝 (∫ z in spaceTimeSet Set.univ (Ioo 0 T), f z * g z)) := by
  let μ : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
  have hCutMeas (n : ℕ) : AEStronglyMeasurable
      (fun z : ParabolicPoint => serrinCutoff n (parabolicHomeomorph z).1) μ :=
    (((serrinCutoff_contDiff n).continuous.measurable).comp
      (measurable_fst.comp parabolicHomeomorph.continuous.measurable)).aestronglyMeasurable
  have hFGMeas : AEStronglyMeasurable (fun z : ParabolicPoint => f z * g z) μ :=
    by
      change AEStronglyMeasurable (f * g) μ
      exact hf.mul hg
  have hCutoffError : Tendsto (fun n => ∫⁻ z in spaceTimeSet
      (Set.univ : Set Vec3) (Ioo 0 T),
        ‖(serrinCutoff n (parabolicHomeomorph z).1 - 1) * (f z * g z)‖ₑ) atTop (𝓝 0) := by
    have hDCT : Tendsto (fun n => ∫⁻ z : ParabolicPoint,
        ‖(serrinCutoff n (parabolicHomeomorph z).1 - 1) * (f z * g z)‖ₑ ∂μ) atTop
        (𝓝 (∫⁻ z : ParabolicPoint, (0 : ℝ≥0∞) ∂μ)) := by
      refine tendsto_lintegral_of_dominated_convergence'
        (bound := fun z : ParabolicPoint => 2 * ‖f z * g z‖ₑ)
        (hF_meas := fun n => (((hCutMeas n).sub aestronglyMeasurable_const).mul
          hFGMeas).enorm)
        ?_ ?_ ?_
      · intro n
        filter_upwards [] with z
        rw [enorm_mul]
        gcongr
        rw [Real.enorm_eq_ofReal_abs]
        calc
          ENNReal.ofReal |serrinCutoff n (parabolicHomeomorph z).1 - 1| ≤ ENNReal.ofReal 2 := by
            apply ENNReal.ofReal_le_ofReal
            calc
              |serrinCutoff n (parabolicHomeomorph z).1 - 1| ≤
                  |serrinCutoff n (parabolicHomeomorph z).1| + |(1 : ℝ)| :=
                abs_sub _ _
              _ ≤ 1 + 1 := add_le_add
                (serrinCutoff_abs_le_one n (parabolicHomeomorph z).1) (by norm_num)
              _ = 2 := by norm_num
          _ = 2 := by simp
      · rw [lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
        exact ENNReal.mul_ne_top (by norm_num) hBase.hasFiniteIntegral.ne
      · filter_upwards [] with z
        have hz := serrinCutoff_tendsto_one (parabolicHomeomorph z).1
        have hsub : Tendsto (fun n : ℕ => serrinCutoff n (parabolicHomeomorph z).1 - 1) atTop (𝓝
          0) := by
          simpa using hz.sub_const 1
        have hmul := (hsub.mul_const (f z * g z)).enorm
        simpa using hmul
    simpa [μ] using hDCT
  have hErrBound : ∀ᶠ n in atTop,
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        ‖serrinCutoff n (parabolicHomeomorph z).1 * (a n z + f z) * (b n z + g z) -
            f z * g z‖ₑ) ≤
        (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), ‖a n z * g z‖ₑ) +
        (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), ‖f z * b n z‖ₑ) +
        (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), ‖a n z * b n z‖ₑ) +
        (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          ‖(serrinCutoff n (parabolicHomeomorph z).1 - 1) * (f z * g z)‖ₑ) := by
    filter_upwards [hProductPairs] with n _hPairs
    have hpoint (z : ParabolicPoint) :
        ‖serrinCutoff n (parabolicHomeomorph z).1 * (a n z + f z) * (b n z + g z) -
            f z * g z‖ₑ ≤
          ‖a n z * g z‖ₑ + ‖f z * b n z‖ₑ +
            ‖a n z * b n z‖ₑ +
            ‖(serrinCutoff n (parabolicHomeomorph z).1 - 1) * (f z * g z)‖ₑ := by
      have hid :
          serrinCutoff n (parabolicHomeomorph z).1 * (a n z + f z) * (b n z + g z) - f z * g z =
            serrinCutoff n (parabolicHomeomorph z).1 *
              (a n z * g z + f z * b n z + a n z * b n z) +
                (serrinCutoff n (parabolicHomeomorph z).1 - 1) * (f z * g z) := by ring
      have hcut : ‖serrinCutoff n (parabolicHomeomorph z).1‖ₑ ≤ 1 := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_one.mpr (serrinCutoff_abs_le_one n (parabolicHomeomorph z).1)
      rw [hid]
      calc
        _ ≤ ‖serrinCutoff n (parabolicHomeomorph z).1 *
              (a n z * g z + f z * b n z + a n z * b n z)‖ₑ +
              ‖(serrinCutoff n (parabolicHomeomorph z).1 - 1) * (f z * g z)‖ₑ := enorm_add_le _ _
        _ ≤ ‖a n z * g z + f z * b n z + a n z * b n z‖ₑ +
              ‖(serrinCutoff n (parabolicHomeomorph z).1 - 1) * (f z * g z)‖ₑ := by
          rw [enorm_mul]
          exact add_le_add (mul_le_of_le_one_left bot_le hcut) le_rfl
        _ ≤ _ := add_le_add
          ((enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) le_rfl)) le_rfl
    have htermsMeas :
        AEMeasurable (fun z : ParabolicPoint => ‖a n z * g z‖ₑ) μ ∧
        AEMeasurable (fun z : ParabolicPoint => ‖f z * b n z‖ₑ) μ ∧
        AEMeasurable (fun z : ParabolicPoint => ‖a n z * b n z‖ₑ) μ ∧
        AEMeasurable (fun z : ParabolicPoint =>
          ‖(serrinCutoff n (parabolicHomeomorph z).1 - 1) * (f z * g z)‖ₑ) μ := by
      exact ⟨((ha n).mul hg).enorm,
        (hf.mul (hb n)).enorm,
        ((ha n).mul (hb n)).enorm,
        ((((hCutMeas n).sub aestronglyMeasurable_const).mul (hf.mul hg)).enorm)⟩
    have hsumInt :
        (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          ‖a n z * g z‖ₑ + ‖f z * b n z‖ₑ +
            ‖a n z * b n z‖ₑ +
            ‖(serrinCutoff n (parabolicHomeomorph z).1 - 1) * (f z * g z)‖ₑ) =
          (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), ‖a n z * g z‖ₑ) +
            (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), ‖f z * b n z‖ₑ) +
            (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
              ‖a n z * b n z‖ₑ) +
            (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
              ‖(serrinCutoff n (parabolicHomeomorph z).1 - 1) * (f z * g z)‖ₑ) := by
      change (∫⁻ z : ParabolicPoint,
          ‖a n z * g z‖ₑ + ‖f z * b n z‖ₑ +
            ‖a n z * b n z‖ₑ +
              ‖(serrinCutoff n (parabolicHomeomorph z).1 - 1) * (f z * g z)‖ₑ ∂μ) =
        (∫⁻ z : ParabolicPoint, ‖a n z * g z‖ₑ ∂μ) +
          (∫⁻ z : ParabolicPoint, ‖f z * b n z‖ₑ ∂μ) +
            (∫⁻ z : ParabolicPoint, ‖a n z * b n z‖ₑ ∂μ) +
              (∫⁻ z : ParabolicPoint,
                ‖(serrinCutoff n (parabolicHomeomorph z).1 - 1) * (f z * g z)‖ₑ ∂μ)
      rw [lintegral_add_right' (fun z : ParabolicPoint =>
          ‖a n z * g z‖ₑ + ‖f z * b n z‖ₑ + ‖a n z * b n z‖ₑ)
          htermsMeas.2.2.2,
        lintegral_add_right' (fun z : ParabolicPoint =>
          ‖a n z * g z‖ₑ + ‖f z * b n z‖ₑ)
          htermsMeas.2.2.1,
        lintegral_add_right' (fun z : ParabolicPoint => ‖a n z * g z‖ₑ)
          htermsMeas.2.1]
    calc
      _ ≤ ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          ‖a n z * g z‖ₑ + ‖f z * b n z‖ₑ +
            ‖a n z * b n z‖ₑ +
            ‖(serrinCutoff n (parabolicHomeomorph z).1 - 1) * (f z * g z)‖ₑ :=
        lintegral_mono (fun z => hpoint z)
      _ = _ := hsumInt
  have hErr : Tendsto (fun n => ∫⁻ z in spaceTimeSet
      (Set.univ : Set Vec3) (Ioo 0 T),
        ‖serrinCutoff n (parabolicHomeomorph z).1 * (a n z + f z) * (b n z + g z) -
            f z * g z‖ₑ) atTop (𝓝 0) := by
    have hsum := (((hPairError1.add hPairError2).add hPairError3).add hCutoffError)
    simp only [zero_add] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hErrBound] with n hn
    exact hn
  have hApproxIntegrable : ∀ᶠ n in atTop,
      Integrable (fun z : ParabolicPoint =>
        serrinCutoff n (parabolicHomeomorph z).1 * (a n z + f z) * (b n z + g z)) μ := by
    filter_upwards [hProductPairs] with n hPairs
    have hsumInt :
        Integrable (fun z : ParabolicPoint =>
          f z * g z + a n z * g z + f z * b n z + a n z * b n z) μ :=
      ((hBase.add hPairs.1).add hPairs.2.1).add hPairs.2.2
    have hUncut : Integrable (fun z : ParabolicPoint =>
        (a n z + f z) * (b n z + g z)) μ :=
      hsumInt.congr (Eventually.of_forall fun z => by
        change f z * g z + a n z * g z + f z * b n z +
          a n z * b n z = (a n z + f z) * (b n z + g z)
        ring)
    have hWeight := hUncut.bdd_mul (c := 1) (hCutMeas n)
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]
        exact serrinCutoff_abs_le_one n (parabolicHomeomorph z).1)
    exact hWeight.congr (Eventually.of_forall fun z => by
      simp only [mul_assoc])
  refine ⟨hApproxIntegrable, ?_⟩
  exact tendsto_integral_of_L1 _ hFGMeas hApproxIntegrable hErr

/-- The cutoff-weighted pairing of two spatial mollifications converges when
the factors have conjugate finite mixed norms. -/
theorem lps_mixed_cutoff_pairing_limit
    {T px qx pt qt : ℝ}
    (hpx1 : 1 ≤ px) (hqx1 : 1 ≤ qx)
    (hpt1 : 1 ≤ pt) (hqt1 : 1 ≤ qt)
    (hSpace : px.HolderConjugate qx)
    (hTime : pt.HolderConjugate qt)
    {f g : ParabolicPoint → ℝ}
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hg : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hfSlice : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => f (x,t)) (ENNReal.ofReal px) volume)
    (hgSlice : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => g (x,t)) (ENNReal.ofReal qx) volume)
    (hfMoment : (∫⁻ t in Ioo 0 T,
      eLpNorm (fun x : Vec3 => f (x,t)) (ENNReal.ofReal px) volume ^ pt) < ⊤)
    (hgMoment : (∫⁻ t in Ioo 0 T,
      eLpNorm (fun x : Vec3 => g (x,t)) (ENNReal.ofReal qx) volume ^ qt) < ⊤) :
    (∀ᶠ n in atTop, Integrable
      (fun z : ParabolicPoint =>
        serrinCutoff n (parabolicHomeomorph z).1 * serrinSM f n z * serrinSM g n z)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) ∧
    Tendsto (fun n => ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      serrinCutoff n (parabolicHomeomorph z).1 * serrinSM f n z * serrinSM g n z) atTop
      (𝓝 (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z * g z)) := by
  let μ : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
  let μt : Measure ℝ := volume.restrict (Ioo 0 T)
  let MF : ℕ → ℝ≥0∞ := fun n => ∫⁻ t in Ioo 0 T,
    eLpNorm (fun x : Vec3 => serrinSM f n (x,t) - f (x,t))
      (ENNReal.ofReal px) volume ^ pt
  let MG : ℕ → ℝ≥0∞ := fun n => ∫⁻ t in Ioo 0 T,
    eLpNorm (fun x : Vec3 => serrinSM g n (x,t) - g (x,t))
      (ENNReal.ofReal qx) volume ^ qt
  have hpx0 : 0 < px := lt_of_lt_of_le (by norm_num) hpx1
  have hqx0 : 0 < qx := lt_of_lt_of_le (by norm_num) hqx1
  have hpt0 : 0 < pt := lt_of_lt_of_le (by norm_num) hpt1
  have hqt0 : 0 < qt := lt_of_lt_of_le (by norm_num) hqt1
  have hFlim : Tendsto MF atTop (𝓝 0) := by
    simpa [MF, μt] using
      (lps_mollify_mixed_norm_tendsto hpt1 hpx1 hf hfSlice hfMoment)
  have hGlim : Tendsto MG atTop (𝓝 0) := by
    simpa [MG, μt] using
      (lps_mollify_mixed_norm_tendsto hqt1 hqx1 hg hgSlice hgMoment)
  have hMFfinite : ∀ᶠ n in atTop, MF n < ⊤ :=
    ((tendsto_order.1 hFlim).2 1 one_pos).mono fun _ h => h.trans ENNReal.one_lt_top
  have hMGfinite : ∀ᶠ n in atTop, MG n < ⊤ :=
    ((tendsto_order.1 hGlim).2 1 one_pos).mono fun _ h => h.trans ENNReal.one_lt_top
  have hRootF : Tendsto (fun n => MF n ^ (1 / pt)) atTop (𝓝 0) := by
    let r : ℝ := 1 / pt
    have hr : 0 < r := by dsimp [r]; positivity
    have hc : Continuous (fun x : ℝ≥0∞ => x ^ r) := ENNReal.continuous_rpow_const
    have h := (hc.tendsto 0).comp hFlim
    have hz : (0 : ℝ≥0∞) ^ r = 0 := ENNReal.zero_rpow_of_pos hr
    rw [hz] at h
    exact h
  have hRootG : Tendsto (fun n => MG n ^ (1 / qt)) atTop (𝓝 0) := by
    let r : ℝ := 1 / qt
    have hr : 0 < r := by dsimp [r]; positivity
    have hc : Continuous (fun x : ℝ≥0∞ => x ^ r) := ENNReal.continuous_rpow_const
    have h := (hc.tendsto 0).comp hGlim
    have hz : (0 : ℝ≥0∞) ^ r = 0 := ENNReal.zero_rpow_of_pos hr
    rw [hz] at h
    exact h
  have hBaseF : (∫⁻ t : ℝ,
      eLpNorm (fun x : Vec3 => f (x,t)) (ENNReal.ofReal px) volume ^ pt ∂μt) < ⊤ := by
    simpa [μt] using hfMoment
  have hBaseG : (∫⁻ t : ℝ,
      eLpNorm (fun x : Vec3 => g (x,t)) (ENNReal.ofReal qx) volume ^ qt ∂μt) < ⊤ := by
    simpa [μt] using hgMoment
  have hBaseGroot :
      (∫⁻ t : ℝ,
        eLpNorm (fun x : Vec3 => g (x,t)) (ENNReal.ofReal qx) volume ^ qt ∂μt) ^
          (1 / qt) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by positivity) hBaseG.ne
  have hBaseFroot :
      (∫⁻ t : ℝ,
        eLpNorm (fun x : Vec3 => f (x,t)) (ENNReal.ofReal px) volume ^ pt ∂μt) ^
          (1 / pt) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by positivity) hBaseF.ne
  have hErr1Bound : Tendsto (fun n => MF n ^ (1 / pt) *
      (∫⁻ t : ℝ,
        eLpNorm (fun x : Vec3 => g (x,t)) (ENNReal.ofReal qx) volume ^ qt ∂μt) ^
          (1 / qt)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hRootF (Or.inr hBaseGroot.ne)
  have hErr2Bound : Tendsto (fun n =>
      (∫⁻ t : ℝ,
        eLpNorm (fun x : Vec3 => f (x,t)) (ENNReal.ofReal px) volume ^ pt ∂μt) ^
          (1 / pt) * MG n ^ (1 / qt)) atTop (𝓝 0) := by
    simpa [mul_comm] using
      (ENNReal.Tendsto.mul_const hRootG (Or.inr hBaseFroot.ne))
  have hErr3Bound : Tendsto (fun n => MF n ^ (1 / pt) * MG n ^ (1 / qt))
      atTop (𝓝 0) := by
    have hGsmall : ∀ᶠ n in atTop, MG n ^ (1 / qt) ≤ 1 := by
      filter_upwards [((tendsto_order.1 hRootG).2 1 one_pos).mono fun _ h => h.le]
        with n hn
      exact hn
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hRootF
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hGsmall] with n hn
    calc
      MF n ^ (1 / pt) * MG n ^ (1 / qt) ≤ MF n ^ (1 / pt) * 1 := by
        gcongr
      _ = MF n ^ (1 / pt) := mul_one _
  let hDf (n : ℕ) : ParabolicPoint → ℝ := fun z => serrinSM f n z - f z
  let hDg (n : ℕ) : ParabolicPoint → ℝ := fun z => serrinSM g n z - g z
  have hDfMeas (n : ℕ) : AEStronglyMeasurable (hDf n) μ :=
    by
      change AEStronglyMeasurable (serrinSM f n - f) μ
      exact (serrinSM_aestronglyMeasurable hf n).sub hf
  have hDgMeas (n : ℕ) : AEStronglyMeasurable (hDg n) μ :=
    by
      change AEStronglyMeasurable (serrinSM g n - g) μ
      exact (serrinSM_aestronglyMeasurable hg n).sub hg
  have hDfmix : ∀ᶠ n in atTop, ∀ᵐ t ∂μt,
      MemLp (fun x : Vec3 => hDf n (x,t)) (ENNReal.ofReal px) volume := by
    filter_upwards [hMFfinite] with n hn
    exact lps_mixed_slice_memLp_ae hpt0 hpx0 (hDfMeas n)
      (by simpa [MF, hDf, μt] using hn)
  have hDgmix : ∀ᶠ n in atTop, ∀ᵐ t ∂μt,
      MemLp (fun x : Vec3 => hDg n (x,t)) (ENNReal.ofReal qx) volume := by
    filter_upwards [hMGfinite] with n hn
    exact lps_mixed_slice_memLp_ae hqt0 hqx0 (hDgMeas n)
      (by simpa [MG, hDg, μt] using hn)
  have hBasePair := lps_mixed_product_integrable hpx0 hqx0 hpt0 hqt0
    hSpace hTime hf hg hfSlice hgSlice hfMoment hgMoment
  have hProductPairs : ∀ᶠ n in atTop,
      Integrable (fun z : ParabolicPoint => hDf n z * g z) μ ∧
      Integrable (fun z : ParabolicPoint => f z * hDg n z) μ ∧
      Integrable (fun z : ParabolicPoint => hDf n z * hDg n z) μ := by
    filter_upwards [hMFfinite, hMGfinite, hDfmix, hDgmix] with n hFn hGn hDfn hDgn
    exact ⟨(lps_mixed_product_integrable hpx0 hqx0 hpt0 hqt0 hSpace hTime
        (hDfMeas n) hg hDfn hgSlice
        (by simpa [MF, hDf, μt] using hFn) hgMoment).1,
      (lps_mixed_product_integrable hpx0 hqx0 hpt0 hqt0 hSpace hTime
        hf (hDgMeas n) hfSlice hDgn hfMoment
        (by simpa [MG, hDg, μt] using hGn)).1,
      (lps_mixed_product_integrable hpx0 hqx0 hpt0 hqt0 hSpace hTime
        (hDfMeas n) (hDgMeas n) hDfn hDgn
        (by simpa [MF, hDf, μt] using hFn)
        (by simpa [MG, hDg, μt] using hGn)).1⟩
  have hDfid (n : ℕ) (z : ParabolicPoint) :
      serrinSM f n z = hDf n z + f z := by
    dsimp only [hDf]
    ring
  have hDgid (n : ℕ) (z : ParabolicPoint) :
      serrinSM g n z = hDg n z + g z := by
    dsimp only [hDg]
    ring
  have hPairError1 : Tendsto (fun n => ∫⁻ z in spaceTimeSet
      (Set.univ : Set Vec3) (Ioo 0 T), ‖hDf n z * g z‖ₑ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hErr1Bound
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hMFfinite, hDfmix] with n hFn hDfn
    exact (lps_mixed_product_integrable hpx0 hqx0 hpt0 hqt0 hSpace hTime
      (hDfMeas n) hg hDfn hgSlice
      (by simpa [MF, hDf, μt] using hFn) hgMoment).2
  have hPairError2 : Tendsto (fun n => ∫⁻ z in spaceTimeSet
      (Set.univ : Set Vec3) (Ioo 0 T), ‖f z * hDg n z‖ₑ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hErr2Bound
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hMGfinite, hDgmix] with n hGn hDgn
    exact (lps_mixed_product_integrable hpx0 hqx0 hpt0 hqt0 hSpace hTime
      hf (hDgMeas n) hfSlice hDgn hfMoment
      (by simpa [MG, hDg, μt] using hGn)).2
  have hPairError3 : Tendsto (fun n => ∫⁻ z in spaceTimeSet
      (Set.univ : Set Vec3) (Ioo 0 T), ‖hDf n z * hDg n z‖ₑ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hErr3Bound
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hMFfinite, hMGfinite, hDfmix, hDgmix] with n hFn hGn hDfn hDgn
    exact (lps_mixed_product_integrable hpx0 hqx0 hpt0 hqt0 hSpace hTime
      (hDfMeas n) (hDgMeas n) hDfn hDgn
      (by simpa [MF, hDf, μt] using hFn)
      (by simpa [MG, hDg, μt] using hGn)).2
  have hlimit := lps_pairing_limit_of_L1_product_errors hf hg hDfMeas hDgMeas
    hBasePair.1 hProductPairs hPairError1 hPairError2 hPairError3
  simpa only [hDfid, hDgid] using hlimit

end ESS

end
