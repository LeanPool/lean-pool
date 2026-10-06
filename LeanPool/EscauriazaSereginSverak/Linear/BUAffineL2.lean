/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineWeak
public import LeanPool.EscauriazaSereginSverak.Linear.BUGrowthL2

/-!
# Quadratic data in affine parabolic coordinates

The finite local quadratic derivative data in `thm:bu` remains finite after
the affine parabolic changes of variables used for time iteration.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Affine parabolic coordinates take bounded subsets of space-time to bounded
subsets. -/
theorem buAffinePoint_bounded_image
    (τ scale : ℝ) (hscale : 0 < scale)
    {K : Set ParabolicPoint} (hK : Bornology.IsBounded K) :
    Bornology.IsBounded (buAffinePoint τ scale '' K) := by
  obtain ⟨R, hRpos, hR⟩ := hK.subset_ball_lt 0
    (show ParabolicPoint from ((0 : Vec3), (0 : ℝ)))
  let T := scale * R + Real.sqrt (|τ| + scale ^ 2 * R ^ 2) + 1
  have hTpos : 0 < T := by
    dsimp [T]
    have hsr : 0 ≤ scale * R := mul_nonneg hscale.le hRpos.le
    have hroot : 0 ≤ Real.sqrt (|τ| + scale ^ 2 * R ^ 2) := Real.sqrt_nonneg _
    linarith only [hsr, hroot]
  apply Bornology.IsBounded.subset (Metric.isBounded_ball (x :=
    (show ParabolicPoint from ((0 : Vec3), (0 : ℝ)))) (r := T))
  rintro q ⟨z, hz, rfl⟩
  have hzball := hR hz
  have hdist : parabolicDist z ((0 : Vec3), (0 : ℝ)) < R := by
    have h := Metric.mem_ball.mp hzball
    rwa [dist_eq_parabolicDist] at h
  have hmax : max (vec3EuclideanNorm z.1) (Real.sqrt |z.2|) < R := by
    simpa [parabolicDist] using hdist
  have hx : vec3EuclideanNorm z.1 < R := (le_max_left _ _).trans_lt hmax
  have ht : Real.sqrt |z.2| < R := (le_max_right _ _).trans_lt hmax
  have htAbs : |z.2| < R ^ 2 := by
    have hsq := (sq_lt_sq₀ (Real.sqrt_nonneg |z.2|) hRpos.le).2 ht
    simpa only [Real.sq_sqrt (abs_nonneg _)] using hsq
  have htime : |τ + scale ^ 2 * z.2| ≤ |τ| + scale ^ 2 * R ^ 2 := by
    calc
      |τ + scale ^ 2 * z.2| ≤ |τ| + |scale ^ 2 * z.2| := abs_add_le _ _
      _ = |τ| + scale ^ 2 * |z.2| := by
        congr 1
        rw [abs_mul, abs_of_nonneg (sq_nonneg scale)]
      _ ≤ |τ| + scale ^ 2 * R ^ 2 := by
        gcongr
  have hroot : Real.sqrt |τ + scale ^ 2 * z.2| ≤
      Real.sqrt (|τ| + scale ^ 2 * R ^ 2) := Real.sqrt_le_sqrt htime
  have hspace : vec3EuclideanNorm (scale • z.1) < scale * R := by
    rw [vec3EuclideanNorm_smul, abs_of_pos hscale]
    exact mul_lt_mul_of_pos_left hx hscale
  have hpar : parabolicDist (buAffinePoint τ scale z)
      ((0 : Vec3), (0 : ℝ)) < T := by
    simp only [parabolicDist, buAffinePoint, sub_zero]
    apply max_lt
    · dsimp [T]
      linarith only [hspace, Real.sqrt_nonneg (|τ| + scale ^ 2 * R ^ 2)]
    · dsimp [T]
      have hsr : 0 ≤ scale * R := mul_nonneg hscale.le hRpos.le
      linarith only [hroot, hsr]
  apply Metric.mem_ball.mpr
  rwa [dist_eq_parabolicDist]

/-- A finite quadratic integral on every bounded source subset transfers to
every bounded subset of the normalized half-space cylinder. -/
theorem bu_affine_l2_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (τ scale : ℝ) (hscale : 0 < scale)
    (f : ParabolicPoint → E)
    (hfloc : LocallyIntegrableOn f
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2))) volume)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2)) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖f z‖ₑ ^ (2 : ℝ)) < ⊤)
    (K : Set ParabolicPoint)
    (hKsub : K ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))
    (hKbounded : Bornology.IsBounded K) :
    (∫⁻ z in K, ‖f (buAffinePoint τ scale z)‖ₑ ^ (2 : ℝ)) < ⊤ := by
  let e := buAffineParabolicHomeomorph τ scale hscale
  let S := e '' K
  have heq : ⇑e = buAffinePoint τ scale :=
    buAffineParabolicHomeomorph_eq τ scale hscale
  have hSsub : S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
      (Ioo τ (τ + scale ^ 2)) := by
    rintro q ⟨z, hz, rfl⟩
    rw [heq]
    have hp := buAffinePoint_preimage_halfSlab τ scale hscale
    exact hp.symm.subset (hKsub hz)
  have hSbounded : Bornology.IsBounded S := by
    change Bornology.IsBounded (e '' K)
    rw [heq]
    exact buAffinePoint_bounded_image τ scale hscale hKbounded
  have hSfin := hL2 S hSsub hSbounded
  let F := fun z : ParabolicPoint => ‖f z‖ₑ ^ (2 : ℝ)
  have hfm : AEStronglyMeasurable f (volume.restrict S) :=
    (hfloc.mono_set hSsub).aestronglyMeasurable
  have hFm : AEMeasurable F (volume.restrict S) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hfm.enorm
  have hmap : Measure.map e volume =
      ENNReal.ofReal (scale⁻¹ ^ 5) • (volume : Measure ParabolicPoint) := by
    rw [heq, buAffinePoint_eq_scalingParabolic]
    exact CKN.map_scalingParabolic scale hscale ((0 : Vec3), τ)
  have hpres : MeasurePreserving e volume
      (ENNReal.ofReal (scale⁻¹ ^ 5) • volume) := ⟨e.measurable, hmap⟩
  have hmapS := (hpres.restrict_image_emb e.measurableEmbedding K).map_eq
  have hFmap : AEMeasurable F (Measure.map e (volume.restrict K)) := by
    rw [hmapS, Measure.restrict_smul]
    exact hFm.smul_measure (ENNReal.ofReal (scale⁻¹ ^ 5))
  have hcomp := lintegral_map' hFmap e.measurable.aemeasurable
  rw [hmapS, Measure.restrict_smul, lintegral_smul_measure] at hcomp
  have hfinite : (∫⁻ z in K, F (e z)) < ⊤ := by
    rw [← hcomp]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSfin
  simpa only [F, heq] using hfinite

/-- Finite local quadratic energy remains finite after affine composition
and multiplication by a subunit scalar. -/
theorem bu_affine_l2_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (τ scale c : ℝ) (hscale : 0 < scale)
    (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (f : ParabolicPoint → E)
    (hfloc : LocallyIntegrableOn f
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2))) volume)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2)) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖f z‖ₑ ^ (2 : ℝ)) < ⊤)
    (K : Set ParabolicPoint)
    (hKsub : K ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))
    (hKbounded : Bornology.IsBounded K) :
    (∫⁻ z in K, ‖c • f (buAffinePoint τ scale z)‖ₑ ^ (2 : ℝ)) < ⊤ := by
  have hbase := bu_affine_l2_comp τ scale hscale f hfloc hL2
    K hKsub hKbounded
  have hpoint (z : ParabolicPoint) :
      ‖c • f (buAffinePoint τ scale z)‖ₑ ^ (2 : ℝ) ≤
        ‖f (buAffinePoint τ scale z)‖ₑ ^ (2 : ℝ) := by
    rw [enorm_smul, ← ofReal_norm c, Real.norm_eq_abs, abs_of_nonneg hc]
    rw [ENNReal.rpow_ofNat, mul_pow]
    have hcoef : ENNReal.ofReal c ^ (2 : ℕ) ≤ 1 := by
      exact pow_le_one₀ bot_le (ENNReal.ofReal_le_one.mpr hc1)
    simpa only [ENNReal.rpow_ofNat] using
      (mul_le_of_le_one_left
        (b := ‖f (buAffinePoint τ scale z)‖ₑ ^ 2) bot_le hcoef)
  exact (lintegral_mono hpoint).trans_lt hbase

/-- The three quadratic derivative terms required by `thm:bu` remain finite
on bounded subsets after an affine parabolic change of variables. -/
theorem bu_affine_derivative_l2
    (τ scale : ℝ) (hτ : 0 ≤ τ) (hscale : 0 < scale)
    (hupper : τ + scale ^ 2 ≤ 1)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
      w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    ∀ K : Set ParabolicPoint,
      K ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded K →
      (∫⁻ z in K,
        ‖(buAffineDw τ scale Dw) z‖ₑ ^ (2 : ℝ) +
        ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ) +
        ‖(buAffineDtw τ scale Dtw) z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  have hI : Ioo τ (τ + scale ^ 2) ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    exact ⟨lt_of_le_of_lt hτ ht.1, ht.2.trans_le hupper⟩
  have hweakS := bu_weak_restrict_time hI w Dw D2w Dtw hweak
  have hscale2le : scale ^ 2 ≤ 1 := by linarith only [hτ, hupper]
  have hscale1 : scale ≤ 1 := by nlinarith only [hscale, hscale2le]
  have hSsub (S : Set ParabolicPoint)
      (hS : S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo τ (τ + scale ^ 2))) :
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) := by
    intro z hz
    exact ⟨(hS hz).1, hI (hS hz).2⟩
  have hDwL2 (S : Set ParabolicPoint)
      (hS : S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo τ (τ + scale ^ 2))) (hSb : Bornology.IsBounded S) :
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    refine (lintegral_mono (fun z => ?_)).trans_lt
      (hL2 S (hSsub S hS) hSb)
    exact le_add_of_nonneg_right (by positivity) |>.trans
      (le_add_of_nonneg_right (by positivity))
  have hD2L2 (S : Set ParabolicPoint)
      (hS : S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo τ (τ + scale ^ 2))) (hSb : Bornology.IsBounded S) :
      (∫⁻ z in S, ‖D2w z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    refine (lintegral_mono (fun z => ?_)).trans_lt
      (hL2 S (hSsub S hS) hSb)
    exact le_add_of_nonneg_left (by positivity) |>.trans
      (le_add_of_nonneg_right (by positivity))
  have hDtL2 (S : Set ParabolicPoint)
      (hS : S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo τ (τ + scale ^ 2))) (hSb : Bornology.IsBounded S) :
      (∫⁻ z in S, ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    refine (lintegral_mono (fun z => ?_)).trans_lt
      (hL2 S (hSsub S hS) hSb)
    exact le_add_of_nonneg_left (by positivity)
  intro K hKsub hKb
  have hDwK := bu_affine_l2_smul τ scale scale hscale hscale.le hscale1
    Dw hweakS.2.1 hDwL2 K hKsub hKb
  have hD2K := bu_affine_l2_smul τ scale (scale ^ 2) hscale
    (sq_nonneg scale) hscale2le D2w hweakS.2.2.1 hD2L2 K hKsub hKb
  have hDtK := bu_affine_l2_smul τ scale (scale ^ 2) hscale
    (sq_nonneg scale) hscale2le Dtw hweakS.2.2.2.1 hDtL2 K hKsub hKb
  have hscaled := bu_affine_weak_derivatives τ scale hτ hscale hupper
    w Dw D2w Dtw hweak
  have hmDw : AEMeasurable
      (fun z => ‖(buAffineDw τ scale Dw) z‖ₑ ^ (2 : ℝ))
      (volume.restrict K) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      ((hscaled.2.1.mono_set hKsub).aestronglyMeasurable.enorm)
  have hmD2 : AEMeasurable
      (fun z => ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ))
      (volume.restrict K) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      ((hscaled.2.2.1.mono_set hKsub).aestronglyMeasurable.enorm)
  have hsum :
      (∫⁻ z in K,
        ‖(buAffineDw τ scale Dw) z‖ₑ ^ (2 : ℝ) +
        ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ) +
        ‖(buAffineDtw τ scale Dtw) z‖ₑ ^ (2 : ℝ)) =
      (∫⁻ z in K, ‖(buAffineDw τ scale Dw) z‖ₑ ^ (2 : ℝ)) +
      (∫⁻ z in K, ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ)) +
      (∫⁻ z in K, ‖(buAffineDtw τ scale Dtw) z‖ₑ ^ (2 : ℝ)) := by
    have h12 :
        (∫⁻ z in K,
          ‖(buAffineDw τ scale Dw) z‖ₑ ^ (2 : ℝ) +
          ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ)) =
        (∫⁻ z in K, ‖(buAffineDw τ scale Dw) z‖ₑ ^ (2 : ℝ)) +
        (∫⁻ z in K, ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ)) := by
      simpa only [Pi.add_apply] using
        (lintegral_add_left' hmDw
          (fun z => ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ)))
    have h123 :
        (∫⁻ z in K,
          (‖(buAffineDw τ scale Dw) z‖ₑ ^ (2 : ℝ) +
            ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ)) +
          ‖(buAffineDtw τ scale Dtw) z‖ₑ ^ (2 : ℝ)) =
        (∫⁻ z in K,
          ‖(buAffineDw τ scale Dw) z‖ₑ ^ (2 : ℝ) +
          ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ)) +
        (∫⁻ z in K, ‖(buAffineDtw τ scale Dtw) z‖ₑ ^ (2 : ℝ)) := by
      simpa only [Pi.add_apply] using
        (lintegral_add_left' (hmDw.add hmD2)
          (fun z => ‖(buAffineDtw τ scale Dtw) z‖ₑ ^ (2 : ℝ)))
    exact h123.trans (congrArg (· + _ ) h12)
  rw [hsum]
  have hDwEq : buAffineDw τ scale Dw =
      fun z => scale • Dw (buAffinePoint τ scale z) := by
    funext z i j
    rfl
  have hD2Eq : buAffineD2w τ scale D2w =
      fun z => scale ^ 2 • D2w (buAffinePoint τ scale z) := by
    funext z i j k
    rfl
  have hDtEq : buAffineDtw τ scale Dtw =
      fun z => scale ^ 2 • Dtw (buAffinePoint τ scale z) := by
    funext z i
    rfl
  apply ENNReal.add_lt_top.mpr
  constructor
  · apply ENNReal.add_lt_top.mpr
    constructor
    · rw [hDwEq]
      exact hDwK
    · rw [hD2Eq]
      exact hD2K
  · rw [hDtEq]
    exact hDtK

end ESS
