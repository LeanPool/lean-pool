/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.PressureSplitMass
public import LeanPool.EscauriazaSereginSverak.Endpoint.PressureSplitConclusion

/-!
# Space-time bound for the harmonic pressure supremum

The local pressure and the fixed whole-space Riesz pressure control the
space-time norm of their harmonic difference.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

private theorem pressureSplit_productLp_transport
    {p : ParabolicPoint → ℝ} {P : Vec3 × ℝ → ℝ}
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict pressureSplitDomain))
    (hPglobal : MemLp P (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ))) :
    let μ : Measure (Vec3 × ℝ) :=
      (volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))
    (μ = (volume : Measure (Vec3 × ℝ)).restrict pressureSplitProductDomain) ∧
      MeasurableSet pressureSplitProductDomain ∧
      MemLp (fun z : Vec3 × ℝ => p (z.1, z.2)) (3 / 2 : ℝ≥0∞) μ ∧
      MemLp P (3 / 2 : ℝ≥0∞) μ := by
  dsimp only
  let μ : Measure (Vec3 × ℝ) :=
    (volume.restrict (CKN.euclideanBall 0 1)).prod
      (volume.restrict (Ioo (-1 : ℝ) 0))
  let D : Set (Vec3 × ℝ) := pressureSplitProductDomain
  have hball : CKN.euclideanBall (0 : Vec3) 1 = pressureSplitBall := by
    rw [pressureSplitBall, CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball
      (by norm_num : (0 : ℝ) < 1)]
  have hmeasure : μ = (volume : Measure (Vec3 × ℝ)).restrict D := by
    dsimp [μ, D]
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
    simp only [pressureSplitProductDomain, pressureSplitTime, hball]
  have hD : MeasurableSet D := by
    exact (isOpen_vec3Ball (0 : Vec3) 1).measurableSet.prod measurableSet_Ioo
  have hpara : MeasurableSet pressureSplitDomain := by
    exact (isOpen_spaceTimeSet pressureSplitBall pressureSplitTime
      (isOpen_vec3Ball 0 1) isOpen_Ioo).measurableSet
  have hpre : parabolicHomeomorph.symm ⁻¹' pressureSplitDomain = D := by
    ext z
    rfl
  have hmp : MeasurePreserving parabolicHomeomorph.symm μ
      (volume.restrict pressureSplitDomain) := by
    have h := parabolicHomeomorphSymm_measurePreserving.restrict_preimage hpara
    rw [hpre] at h
    rw [hmeasure]
    exact h
  have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hpProduct0 := hp.comp_measurePreserving hmp
  have hpeq : (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z)) =ᵐ[μ]
      (fun z => p (z.1, z.2)) := by
    filter_upwards [] with z
    simp only [parabolicHomeomorph_symm_apply]
  have hpProduct : MemLp (fun z : Vec3 × ℝ => p (z.1, z.2))
      (3 / 2 : ℝ≥0∞) μ := by
    rw [← hcoeff]
    exact (memLp_congr_ae hpeq).2 hpProduct0
  have hPμ₀ : MemLp P (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    rw [hmeasure]
    exact hPglobal.restrict D
  have hPμ : MemLp P (3 / 2 : ℝ≥0∞) μ := by
    rw [← hcoeff]
    exact hPμ₀
  exact ⟨hmeasure, hD, hpProduct, hPμ⟩

private theorem pressureSplit_remainder_productLp_and_difference
    {p p₂ : ParabolicPoint → ℝ} {P : Vec3 × ℝ → ℝ}
    {μ : Measure (Vec3 × ℝ)} {D : Set (Vec3 × ℝ)}
    (hD : MeasurableSet D)
    (hmeasure : μ = (volume : Measure (Vec3 × ℝ)).restrict D)
    (hp₂global : MemLp p₂ (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure ParabolicPoint))
    (hPcoord : ∀ z ∈ D, p₂ (parabolicHomeomorph.symm z) =
      p (z.1, z.2) - P z) :
    MemLp (fun z : Vec3 × ℝ => p₂ (z.1, z.2)) (3 / 2 : ℝ≥0∞) μ ∧
      (fun z : Vec3 × ℝ => p₂ (z.1, z.2)) =ᵐ[μ]
        (fun z => p (z.1, z.2) - P z) := by
  have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hp₂μ : MemLp (fun z : Vec3 × ℝ => p₂ (z.1, z.2))
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    have hrestrict := hp₂global.restrict D
    rw [hmeasure]
    apply (memLp_congr_ae ?_).2 hrestrict
    filter_upwards [ae_restrict_mem hD] with z hz
    rfl
  have hdiff : (fun z : Vec3 × ℝ => p₂ (z.1, z.2)) =ᵐ[μ]
      (fun z => p (z.1, z.2) - P z) := by
    have hAE := ae_restrict_mem (μ := volume) hD
    rw [← hmeasure] at hAE
    filter_upwards [hAE] with z hz
    simpa [parabolicHomeomorph_symm_apply] using hPcoord z hz
  have hp₂μ' : MemLp (fun z : Vec3 × ℝ => p₂ (z.1, z.2))
      (3 / 2 : ℝ≥0∞) μ := by
    rw [← hcoeff]
    exact hp₂μ
  exact ⟨hp₂μ', hdiff⟩

private theorem pressureSplit_remainder_coordinate_eq
    {p p₁ p₂ : ParabolicPoint → ℝ} {P : Vec3 × ℝ → ℝ}
    (hp₂ : p₂ = pressureSplitRemainder p p₁)
    (hP₁ : ∀ z, p₁ (parabolicHomeomorph.symm z) = P z)
    (z : Vec3 × ℝ) (hz : z ∈ pressureSplitProductDomain) :
    p₂ (parabolicHomeomorph.symm z) = p (z.1, z.2) - P z := by
  rw [hp₂]
  change goodPointDomain.indicator (fun y => p y - p₁ y)
    (parabolicHomeomorph.symm z) = p (z.1, z.2) - P z
  have hmem : parabolicHomeomorph.symm z ∈ goodPointDomain := by
    change z ∈ pressureSplitProductDomain at hz
    change z.1 ∈ vec3Ball 0 1 ∧ z.2 ∈ Ioo (-1 : ℝ) 0 at hz
    rcases hz with ⟨hx, ht⟩
    change ((z.1, z.2) : ParabolicPoint).1 ∈ vec3Ball 0 1 ∧
      ((z.1, z.2) : ParabolicPoint).2 ∈ Ioo (-1 : ℝ) 0
    exact ⟨hx, ht⟩
  rw [Set.indicator_of_mem hmem, hP₁ z, parabolicHomeomorph_symm_apply]

private theorem pressureSplit_lp_power_eq_mass
    {P : Vec3 × ℝ → ℝ} {μ : Measure (Vec3 × ℝ)}
    (hP : MemLp P (3 / 2 : ℝ≥0∞) μ) :
    eLpNorm P (3 / 2 : ℝ≥0∞) μ ^ (3 / 2 : ℝ) =
      ∫⁻ z, ENNReal.ofReal |P z| ^ (3 / 2 : ℝ) ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral
    (p := (3 / 2 : NNReal)) (f := P) (by norm_num) hP.aestronglyMeasurable
  norm_num at h ⊢
  simpa only [Real.enorm_eq_ofReal_abs] using h

/-- The time-integrated interior supremum of the harmonic remainder is
controlled by the local pressure norm and the critical velocity bound. -/
theorem pressureSplit_remainder_supLp_bound
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict pressureSplitDomain))
    (hDu : AEStronglyMeasurable Du (volume.restrict pressureSplitDomain))
    (hpmeas : AEStronglyMeasurable p (volume.restrict pressureSplitDomain))
    (hL2 : essSup (fun t : ℝ => ∫⁻ x in pressureSplitBall,
      ‖u (x, t)‖ₑ ^ (2 : ℝ)) (volume.restrict pressureSplitTime) < ⊤)
    (henergy : (∫⁻ z in pressureSplitDomain,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict pressureSplitDomain))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in pressureSplitBall,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict pressureSplitTime) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict pressureSplitTime), ∀ i : Fin 3,
      HasWeakGradientOn pressureSplitBall (fun x => u (x, t) i)
        (fun x => Du (x, t) i))
    (hdiv : ∀ χ : Vec3 × ℝ → ℝ,
      χ ∈ spaceTimeTestFunction (V := ℝ) pressureSplitBall pressureSplitTime →
      ∫ z in pressureSplitDomain,
        ∑ i : Fin 3, u z i * spatialPartial χ i z = 0)
    (hMomentum : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) pressureSplitBall pressureSplitTime →
      ∫ z in pressureSplitDomain,
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0) :
    let F := pressureSplitTensor u
    let hF := pressureSplitTensor_memLp hu hDu henergy hL3 hgrad
    let p₁ := pressureSplitRieszPressure F hF
    let p₂ := pressureSplitRemainder p p₁
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      (∫⁻ t : ℝ, blowupHarmonicSupExtended p₂ t ^ (3 / 2 : ℝ)) ≤
        C * ((eLpNorm (fun z : Vec3 × ℝ => p (z.1, z.2))
          (3 / 2 : ℝ≥0∞)
          ((volume.restrict (CKN.euclideanBall 0 1)).prod
            (volume.restrict (Ioo (-1 : ℝ) 0))) ^ (3 / 2 : ℝ)) +
          ENNReal.ofReal (pressureSplitVelocityLpBound u ^ 3)) := by
  dsimp only
  let F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := pressureSplitTensor u
  let hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) :=
    pressureSplitTensor_memLp hu hDu henergy hL3 hgrad
  let P : Vec3 × ℝ → ℝ := CKN.Leray.rieszPressureSpaceTime
    (3 / 2 : ℝ) (by norm_num) F hF
  let p₁ : ParabolicPoint → ℝ := pressureSplitRieszPressure F hF
  let p₂ : ParabolicPoint → ℝ := pressureSplitRemainder p p₁
  let μ : Measure (Vec3 × ℝ) :=
    (volume.restrict (CKN.euclideanBall 0 1)).prod
      (volume.restrict (Ioo (-1 : ℝ) 0))
  let D : Set (Vec3 × ℝ) := pressureSplitProductDomain
  have hPglobal : MemLp P (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := by
    exact CKN.Leray.rieszPressureSpaceTime_memLp (3 / 2 : ℝ)
      (by norm_num) F hF
  obtain ⟨hmeasure, hD, hpProduct, hPμ⟩ :=
    pressureSplit_productLp_transport hp hPglobal
  have hsplit := pressureSplit_remainder_harmonic_interior_bound
    hu hDu hpmeas hL2 henergy hp hL3 hgrad hdiv hMomentum
  rcases hsplit with ⟨hp₂global, hharm, ⟨Cₕ, hCₕ, hsup⟩⟩
  have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hP₁ (z : Vec3 × ℝ) : p₁ (parabolicHomeomorph.symm z) = P z := by
    simp only [p₁, P, pressureSplitRieszPressure,
      parabolicHomeomorph.apply_symm_apply]
  have hPcoord (z : Vec3 × ℝ) (hz : z ∈ D) :
      p₂ (parabolicHomeomorph.symm z) = p (z.1, z.2) - P z :=
    pressureSplit_remainder_coordinate_eq rfl hP₁ z hz
  have ⟨hp₂μ, hdiff⟩ := pressureSplit_remainder_productLp_and_difference
    hD hmeasure hp₂global hPcoord
  have htri : eLpNorm (fun z : Vec3 × ℝ => p₂ (z.1, z.2))
      (3 / 2 : ℝ≥0∞) μ ≤
      eLpNorm (fun z : Vec3 × ℝ => p (z.1, z.2)) (3 / 2 : ℝ≥0∞) μ +
        eLpNorm P (3 / 2 : ℝ≥0∞) μ := by
    calc
      _ = eLpNorm (fun z : Vec3 × ℝ => p (z.1, z.2) - P z)
          (3 / 2 : ℝ≥0∞) μ := eLpNorm_congr_ae hdiff
      _ ≤ _ := eLpNorm_sub_le (by
        rw [← ENNReal.ofReal_one, ← hcoeff]
        exact ENNReal.ofReal_le_ofReal (by norm_num))
  have hPpow := pressureSplit_lp_power_eq_mass hPμ
  have hmass := pressureSplitRieszPressure_source_mass_bound
    hu hDu henergy hL3 hgrad
  let A : ℝ := CKN.Leray.rieszPressureOperatorBound
    (3 / 2 : ℝ) (by norm_num)
  let M : ℝ := pressureSplitVelocityLpBound u
  have hA : 0 ≤ A := by
    dsimp [A]
    have h := @CKN.Leray.rieszPressureOperator_norm_le
      (3 / 2 : ℝ) (by norm_num) (0 : Fin 3) (0 : Fin 3)
    exact le_trans (norm_nonneg
      (CKN.Leray.rieszPressureOperator (3 / 2 : ℝ) (by norm_num)
        (0 : Fin 3) (0 : Fin 3))) h
  have hM : 0 ≤ M := by
    dsimp [M, pressureSplitVelocityLpBound]
    exact ENNReal.toReal_nonneg
  have hMpow : (M ^ 2) ^ (3 / 2 : ℝ) = M ^ 3 := by
    rw [← Real.rpow_natCast M 2, ← Real.rpow_natCast M 3,
      ← Real.rpow_mul hM]
    norm_num
  let K : ℝ≥0∞ := ENNReal.ofReal ((A * 9) ^ (3 / 2 : ℝ))
  have hfactor : ENNReal.ofReal (A * (9 * M ^ 2)) ^ (3 / 2 : ℝ) =
      K * ENNReal.ofReal (M ^ 3) := by
    have hA9 : 0 ≤ A * 9 := mul_nonneg hA (by norm_num)
    rw [show A * (9 * M ^ 2) = (A * 9) * M ^ 2 by ring,
      ENNReal.ofReal_mul hA9,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 2),
      ENNReal.ofReal_rpow_of_nonneg hA9 (by norm_num : (0 : ℝ) ≤ 3 / 2),
      ENNReal.ofReal_rpow_of_nonneg (sq_nonneg M)
        (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    rw [hMpow]
  have hmassP : eLpNorm P (3 / 2 : ℝ≥0∞) μ ^ (3 / 2 : ℝ) ≤
      K * ENNReal.ofReal (M ^ 3) := by
    rw [hPpow, hmeasure]
    change (∫⁻ z in D, ENNReal.ofReal |P z| ^ (3 / 2 : ℝ)) ≤ _
    have hmass' : (∫⁻ z in D, ENNReal.ofReal |P z| ^ (3 / 2 : ℝ)) ≤
        ENNReal.ofReal (A * (9 * M ^ 2)) ^ (3 / 2 : ℝ) := by
      simpa only [D, P, F, hF, pressureSplitRieszPressure, A, M,
        pressureSplitVelocityLpBound,
        parabolicHomeomorph.apply_symm_apply] using hmass
    exact hmass'.trans_eq hfactor
  have hnormpow :
      eLpNorm (fun z : Vec3 × ℝ => p₂ (z.1, z.2))
          (3 / 2 : ℝ≥0∞) μ ^ (3 / 2 : ℝ) ≤
        (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
          (eLpNorm (fun z : Vec3 × ℝ => p (z.1, z.2))
              (3 / 2 : ℝ≥0∞) μ ^ (3 / 2 : ℝ) +
            K * ENNReal.ofReal (M ^ 3)) := by
    calc
      _ ≤ (eLpNorm (fun z : Vec3 × ℝ => p (z.1, z.2))
            (3 / 2 : ℝ≥0∞) μ + eLpNorm P (3 / 2 : ℝ≥0∞) μ) ^
              (3 / 2 : ℝ) := ENNReal.rpow_le_rpow htri (by norm_num)
      _ ≤ (2 : ℝ≥0∞) ^ ((3 / 2 : ℝ) - 1) *
            (eLpNorm (fun z : Vec3 × ℝ => p (z.1, z.2))
                (3 / 2 : ℝ≥0∞) μ ^ (3 / 2 : ℝ) +
              eLpNorm P (3 / 2 : ℝ≥0∞) μ ^ (3 / 2 : ℝ)) :=
          ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by norm_num)
      _ = (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
            (eLpNorm (fun z : Vec3 × ℝ => p (z.1, z.2))
                (3 / 2 : ℝ≥0∞) μ ^ (3 / 2 : ℝ) +
              eLpNorm P (3 / 2 : ℝ≥0∞) μ ^ (3 / 2 : ℝ)) := by
          congr 2
          norm_num
      _ ≤ _ := by
        gcongr
  let K' : ℝ≥0∞ := max 1 K
  let X : ℝ≥0∞ := eLpNorm (fun z : Vec3 × ℝ => p (z.1, z.2))
    (3 / 2 : ℝ≥0∞) μ ^ (3 / 2 : ℝ)
  let Y : ℝ≥0∞ := ENNReal.ofReal (M ^ 3)
  have hK'₁ : 1 ≤ K' := le_max_left _ _
  have hKK' : K ≤ K' := le_max_right _ _
  have hsum : X + K * Y ≤ K' * (X + Y) := by
    calc
      _ = 1 * X + K * Y := by rw [one_mul]
      _ ≤ K' * X + K' * Y := add_le_add
        (mul_le_mul_of_nonneg_right hK'₁ bot_le)
        (mul_le_mul_of_nonneg_right hKK' bot_le)
      _ = K' * (X + Y) := by rw [mul_add]
  let Csrc : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * K'
  let C : ℝ≥0∞ := Cₕ * Csrc
  have hK : K < ⊤ := by
    dsimp [K]
    exact ENNReal.ofReal_lt_top
  have hCsrc : Csrc < ⊤ := by
    dsimp [Csrc]
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofNat_ne_top)
      (max_lt ENNReal.one_lt_top hK)
  have hC : C < ⊤ := by
    dsimp [C]
    exact ENNReal.mul_lt_top hCₕ hCsrc
  have hind : (∫⁻ t : ℝ, blowupHarmonicSupExtended p₂ t ^
      (3 / 2 : ℝ)) =
      (∫⁻ t in Ioo (-1 : ℝ) 0,
        eLpNorm (fun x : Vec3 => p₂ (x, t)) ⊤
          (volume.restrict (CKN.euclideanBall 0 (3 / 4 : ℝ))) ^
            (3 / 2 : ℝ)) := by
    rw [← lintegral_indicator (measurableSet_Ioo)]
    congr 1
    funext t
    by_cases ht : t ∈ Ioo (-1 : ℝ) 0
    · simp [blowupHarmonicSupExtended, Set.indicator_of_mem ht]
    · simp [blowupHarmonicSupExtended, Set.indicator_of_notMem ht]
  refine ⟨C, hC, ?_⟩
  rw [hind]
  have hbase : eLpNorm (fun z : Vec3 × ℝ => p₂ (z.1, z.2))
      (3 / 2 : ℝ≥0∞) μ ^ (3 / 2 : ℝ) ≤ Csrc * (X + Y) := by
    have hnormpow' : eLpNorm (fun z : Vec3 × ℝ => p₂ (z.1, z.2))
        (3 / 2 : ℝ≥0∞) μ ^ (3 / 2 : ℝ) ≤
      (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (X + K * Y) := by
      simpa only [X, Y] using hnormpow
    calc
      _ ≤ (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (K' * (X + Y)) := by
        exact hnormpow'.trans (mul_le_mul_of_nonneg_left hsum bot_le)
      _ = Csrc * (X + Y) := by
        dsimp [Csrc]
        rw [← mul_assoc]
  calc
    _ ≤ Cₕ * eLpNorm (fun z : Vec3 × ℝ => p₂ (z.1, z.2))
          (3 / 2 : ℝ≥0∞) μ ^ (3 / 2 : ℝ) := hsup
    _ ≤ Cₕ * (Csrc * (X + Y)) := by
      gcongr
    _ = C * (eLpNorm (fun z : Vec3 × ℝ => p (z.1, z.2))
          (3 / 2 : ℝ≥0∞) μ ^ (3 / 2 : ℝ) + ENNReal.ofReal (M ^ 3)) := by
      dsimp [C, Csrc]
      dsimp [X, Y]
      ac_rfl

end ESS

end
