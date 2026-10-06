/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianShiftData
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCutoffL2Basis
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCutoffZero
public import LeanPool.EscauriazaSereginSverak.Linear.BUZeroExtendWeak
public import LeanPool.EscauriazaSereginSverak.Linear.UCWeakProduct

/-!
# Compact Gaussian data after the positive-time translation

The cutoff is translated together with the rescaled field. Its support then
lies strictly inside the positive-time cylinder used by the Gaussian weight.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

@[expose] def buGaussianShiftedFinalCutoff (s : ℝ) : ℝ :=
  ucFinalTimeCutoff (s - 1 / 6)

@[expose] def buGaussianShiftedInitialCutoff (ε s : ℝ) : ℝ :=
  ucInitialTimeCutoff ε (s - 1 / 6)

/-- The Gaussian cutoff field after translation by `1/6`. -/
@[expose] def buGaussianShiftedCutoffField (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ)
    (v : ParabolicPoint → Vec3) : ParabolicPoint → Vec3 :=
  ucCutoffField (ucSpatialCutoff ρ hρ) buGaussianShiftedFinalCutoff
    (buGaussianShiftedInitialCutoff ε) (buGaussianShiftedField (1 / 6) v)

/-- The first weak derivative data of the translated cutoff field. -/
@[expose] def buGaussianShiftedCutoffDw (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ)
    (v : ParabolicPoint → Vec3) (Dv : ParabolicPoint → Fin 3 → Vec3) :
    ParabolicPoint → Fin 3 → Vec3 :=
  ucCutoffDw (ucSpatialCutoff ρ hρ) buGaussianShiftedFinalCutoff
    (buGaussianShiftedInitialCutoff ε) (buGaussianShiftedField (1 / 6) v)
    (buGaussianShiftedDw (1 / 6) Dv)

/-- The second weak derivative data of the translated cutoff field. -/
@[expose] def buGaussianShiftedCutoffD2w (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ)
    (v : ParabolicPoint → Vec3) (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3) :
    ParabolicPoint → Fin 3 → Fin 3 → Vec3 :=
  ucCutoffD2 (ucSpatialCutoff ρ hρ) buGaussianShiftedFinalCutoff
    (buGaussianShiftedInitialCutoff ε) (buGaussianShiftedField (1 / 6) v)
    (buGaussianShiftedDw (1 / 6) Dv) (buGaussianShiftedD2w (1 / 6) D2v)

/-- The time derivative data of the translated cutoff field. -/
@[expose] def buGaussianShiftedCutoffDtw (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ)
    (v : ParabolicPoint → Vec3) (Dtv : ParabolicPoint → Vec3) :
    ParabolicPoint → Vec3 :=
  ucCutoffDt (ucSpatialCutoff ρ hρ) buGaussianShiftedFinalCutoff
    (buGaussianShiftedInitialCutoff ε) (buGaussianShiftedField (1 / 6) v)
    (buGaussianShiftedDtw (1 / 6) Dtv)

private theorem buGaussian_memLp_restrict_of_local_l2
    {Ω K : Set ParabolicPoint} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ParabolicPoint → E}
    (hf : LocallyIntegrableOn f Ω volume) (hK : K ⊆ Ω)
    (hfin : (∫⁻ z in K, ‖f z‖ₑ ^ (2 : ℝ)) < ⊤) :
    MemLp f 2 (volume.restrict K) := by
  have hloc := hf.mono_set hK
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    hloc.aestronglyMeasurable).2
  simpa using hfin

/-- A smooth cutoff supported in a compact subset of the source cylinder
extends the translated field and its weak derivatives to the Gaussian
Carleman cylinder. -/
theorem buGaussian_shifted_cutoff_admissible
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 (2 - 1 / 6))
      v Dv D2v Dtv)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2),
      ‖buGaussianShiftedField (1 / 6) v z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedDw (1 / 6) Dv z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedD2w (1 / 6) D2v z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedDtw (1 / 6) Dtv z‖ₑ ^ (2 : ℝ)) < ⊤) :
    HasSpaceTimeWeakDerivs univ (Ioo 0 2)
      (buGaussianShiftedCutoffField ρ hρ ε v)
      (buGaussianShiftedCutoffDw ρ hρ ε v Dv)
      (buGaussianShiftedCutoffD2w ρ hρ ε v Dv D2v)
      (buGaussianShiftedCutoffDtw ρ hρ ε v Dtv) ∧
    HasCompactSupport (buGaussianShiftedCutoffField ρ hρ ε v) ∧
    tsupport (buGaussianShiftedCutoffField ρ hρ ε v) ⊆
      spaceTimeSet univ (Ioo 0 2) ∧
    MemLp (buGaussianShiftedCutoffField ρ hρ ε v) 2 volume ∧
    MemLp (buGaussianShiftedCutoffDw ρ hρ ε v Dv) 2 volume ∧
    MemLp (buGaussianShiftedCutoffD2w ρ hρ ε v Dv D2v) 2 volume ∧
    MemLp (buGaussianShiftedCutoffDtw ρ hρ ε v Dtv) 2 volume := by
  let B : Set Vec3 := vec3Ball 0 ρ
  let I : Set ℝ := Ioo (1 / 6) 2
  let U : Set ParabolicPoint := spaceTimeSet B I
  let θ : Vec3 → ℝ := ucSpatialCutoff ρ hρ
  let η : ℝ → ℝ := buGaussianShiftedFinalCutoff
  let χ : ℝ → ℝ := buGaussianShiftedInitialCutoff ε
  let κ : Vec3 × ℝ → ℝ := fun q => ucCutoffScalar θ η χ q
  let K : Set ParabolicPoint := buCutSupportSet κ
  let vσ := buGaussianShiftedField (1 / 6) v
  let Dvσ := buGaussianShiftedDw (1 / 6) Dv
  let D2vσ := buGaussianShiftedD2w (1 / 6) D2v
  let Dtvσ := buGaussianShiftedDtw (1 / 6) Dtv
  have hκsmooth : ContDiff ℝ (⊤ : ℕ∞) κ := by
    have hθ : ContDiff ℝ (⊤ : ℕ∞) θ := ucSpatialCutoff_smooth hρ
    have hshift : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => s - 1 / 6) := by
      fun_prop
    have hη : ContDiff ℝ (⊤ : ℕ∞) η := by
      change ContDiff ℝ (⊤ : ℕ∞)
        (ucFinalTimeCutoff ∘ fun s : ℝ => s - 1 / 6)
      exact ucFinalTimeCutoff_smooth.comp hshift
    have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := by
      change ContDiff ℝ (⊤ : ℕ∞)
        (ucInitialTimeCutoff ε ∘ fun s : ℝ => s - 1 / 6)
      exact (ucInitialTimeCutoff_smooth ε).comp hshift
    dsimp [κ, ucCutoffScalar]
    exact ((hθ.comp contDiff_fst).mul
      (hη.comp contDiff_snd)).mul (hχ.comp contDiff_snd)
  let L : Set (Vec3 × ℝ) :=
    euclideanClosedBall 0 (3 * ρ / 4) ×ˢ Icc (1 / 6 + ε) (1 / 6 + 7 / 4)
  have hLcompact : IsCompact L := by
    exact (isCompact_euclideanClosedBall 0 (by positivity)).prod isCompact_Icc
  have hκsupport : Function.support κ ⊆ L := by
    intro q hq
    have hκeq : κ q = ucGaussianCutoff ρ hρ ε (q.1, q.2 - 1 / 6) := by
      simp [κ, ucCutoffScalar, θ, η, χ, buGaussianShiftedFinalCutoff,
        buGaussianShiftedInitialCutoff, ucGaussianCutoff, ucCutoffScalar]
    have hne : ucGaussianCutoff ρ hρ ε (q.1, q.2 - 1 / 6) ≠ 0 := by
      intro hzero
      apply hq
      rw [hκeq, hzero]
    have hbase := ucGaussianCutoff_support_subset hρ hε
      (Function.mem_support.mpr hne)
    refine ⟨hbase.1, ?_⟩
    rcases hbase.2 with ⟨hlo, hhi⟩
    constructor <;> linarith only [hlo, hhi]
  have hκcompact : HasCompactSupport κ :=
    HasCompactSupport.of_support_subset_isCompact hLcompact hκsupport
  have hκtsupport : tsupport κ ⊆ L :=
    closure_minimal hκsupport hLcompact.isClosed
  have hKclosed : IsClosed K := by
    dsimp [K, buCutSupportSet]
    exact (isClosed_tsupport (f := κ)).preimage parabolicHomeomorph.continuous
  have hKbig : IsCompact (parabolicHomeomorph.symm '' L) :=
    parabolicHomeomorph.symm.isCompact_image.mpr hLcompact
  have hKsub : K ⊆ parabolicHomeomorph.symm '' L := by
    intro z hz
    refine ⟨parabolicHomeomorph z, hκtsupport hz, ?_⟩
    exact parabolicHomeomorph.apply_symm_apply z
  have hKcompact : IsCompact K := hKbig.of_isClosed_subset hKclosed hKsub
  have hKsource : K ⊆ U := by
    intro z hz
    have hq := hκtsupport hz
    rcases hq with ⟨hqspace, hqtime⟩
    have hspace : z.1 ∈ B := by
      have hsp : z.1 ∈ euclideanBall 0 ρ :=
        euclideanClosedBall_subset_euclideanBall
          (by positivity : (0 : ℝ) ≤ 3 * ρ / 4)
          (by linarith only [hρ]) hqspace
      simpa [B, vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot,
        pow_two] using (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).1 hsp
    have htime : z.2 ∈ I := by
      change 1 / 6 < z.2 ∧ z.2 < 2
      rcases hqtime with ⟨hlo, hhi⟩
      constructor
      · linarith only [hlo, hε]
      · have hbound : (1 / 6 : ℝ) + 7 / 4 < 2 := by norm_num
        exact lt_of_le_of_lt hhi hbound
    exact ⟨hspace, htime⟩
  have hweakShift := buGaussian_timeShift_weak_derivatives
    hweak
  have hmemRawField : MemLp vσ 2 (volume.restrict K) := by
    apply buGaussian_memLp_restrict_of_local_l2 hweakShift.1 hKsource
    have hsmall : (∫⁻ z in U, ‖vσ z‖ₑ ^ (2 : ℝ)) < ⊤ := by
      apply (lintegral_mono ?_).trans_lt hL2
      intro z
      exact le_add_of_nonneg_right (by positivity) |>.trans
        (le_add_of_nonneg_right (by positivity) |>.trans
          (le_add_of_nonneg_right (by positivity)))
    exact (lintegral_mono_set hKsource).trans_lt hsmall
  have hmemRawDw : MemLp Dvσ 2 (volume.restrict K) := by
    apply buGaussian_memLp_restrict_of_local_l2 hweakShift.2.1 hKsource
    have hsmall : (∫⁻ z in U, ‖Dvσ z‖ₑ ^ (2 : ℝ)) < ⊤ := by
      apply (lintegral_mono ?_).trans_lt hL2
      intro z
      exact le_add_of_nonneg_left (by positivity) |>.trans
        (le_add_of_nonneg_right (by positivity) |>.trans
          (le_add_of_nonneg_right (by positivity)))
    exact (lintegral_mono_set hKsource).trans_lt hsmall
  have hmemRawD2 : MemLp D2vσ 2 (volume.restrict K) := by
    apply buGaussian_memLp_restrict_of_local_l2 hweakShift.2.2.1 hKsource
    have hsmall : (∫⁻ z in U, ‖D2vσ z‖ₑ ^ (2 : ℝ)) < ⊤ := by
      apply (lintegral_mono ?_).trans_lt hL2
      intro z
      exact le_add_of_nonneg_left (by positivity) |>.trans
        (le_add_of_nonneg_right (by positivity))
    exact (lintegral_mono_set hKsource).trans_lt hsmall
  have hmemRawDt : MemLp Dtvσ 2 (volume.restrict K) := by
    apply buGaussian_memLp_restrict_of_local_l2 hweakShift.2.2.2.1 hKsource
    have hsmall : (∫⁻ z in U, ‖Dtvσ z‖ₑ ^ (2 : ℝ)) < ⊤ := by
      apply (lintegral_mono ?_).trans_lt hL2
      intro z
      exact le_add_left le_rfl
    exact (lintegral_mono_set hKsource).trans_lt hsmall
  have hmemCut := buCut_memLp_data κ hκsmooth hκcompact vσ Dvσ D2vσ Dtvσ
    hmemRawField hmemRawDw hmemRawD2 hmemRawDt
  have hxi : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => ucCutoffScalar θ η χ q) := by
    simpa [κ] using hκsmooth
  have hweakCut := ucCutoff_hasSpaceTimeWeakDerivs
    (isOpen_vec3Ball 0 ρ) isOpen_Ioo θ η χ hxi hweakShift
  have hscalar (z : ParabolicPoint) : buCutScalar κ z = ucCutoffScalar θ η χ z := by
    rcases z with ⟨x, s⟩
    rfl
  have hscalarFun : buCutScalar κ = ucCutoffScalar θ η χ := by
    funext z
    exact hscalar z
  have hfieldEq : buCutField κ vσ =
      buGaussianShiftedCutoffField ρ hρ ε v := by
    funext z
    change buCutScalar κ z • vσ z =
      ucCutoffScalar θ η χ z • buGaussianShiftedField (1 / 6) v z
    rw [hscalarFun]
  have hDwEq : buCutDw κ vσ Dvσ =
      buGaussianShiftedCutoffDw ρ hρ ε v Dv := by
    funext z
    funext i
    funext j
    change buCutScalar κ z * Dvσ z i j + vσ z i *
        spatialPartial (buCutScalar κ) j z =
      ucCutoffScalar θ η χ z * buGaussianShiftedDw (1 / 6) Dv z i j +
        buGaussianShiftedField (1 / 6) v z i *
        spatialPartial (ucCutoffScalar θ η χ) j z
    rw [hscalarFun]
  have hD2Eq : buCutD2 κ vσ Dvσ D2vσ =
      buGaussianShiftedCutoffD2w ρ hρ ε v Dv D2v := by
    funext z
    funext i
    funext j
    funext k
    change buCutScalar κ z * D2vσ z i j k +
        spatialPartial (buCutScalar κ) k z * Dvσ z i j +
        spatialPartial (buCutScalar κ) j z * Dvσ z i k +
        vσ z i * spatialSecondPartial (buCutScalar κ) j k z =
      ucCutoffScalar θ η χ z * buGaussianShiftedD2w (1 / 6) D2v z i j k +
        spatialPartial (ucCutoffScalar θ η χ) k z *
          buGaussianShiftedDw (1 / 6) Dv z i j +
        spatialPartial (ucCutoffScalar θ η χ) j z *
          buGaussianShiftedDw (1 / 6) Dv z i k +
        buGaussianShiftedField (1 / 6) v z i *
          spatialSecondPartial (ucCutoffScalar θ η χ) j k z
    rw [hscalarFun]
  have hDtEq : buCutDt κ vσ Dtvσ =
      buGaussianShiftedCutoffDtw ρ hρ ε v Dtv := by
    funext z
    funext i
    change buCutScalar κ z * Dtvσ z i + vσ z i *
        timePartial (buCutScalar κ) z =
      ucCutoffScalar θ η χ z * buGaussianShiftedDtw (1 / 6) Dtv z i +
        buGaussianShiftedField (1 / 6) v z i *
          timePartial (ucCutoffScalar θ η χ) z
    rw [hscalarFun]
  have hzero (z : ParabolicPoint) (hz : z ∉ K) :
      buGaussianShiftedCutoffField ρ hρ ε v z = 0 ∧
        buGaussianShiftedCutoffDw ρ hρ ε v Dv z = 0 ∧
        buGaussianShiftedCutoffD2w ρ hρ ε v Dv D2v z = 0 ∧
        buGaussianShiftedCutoffDtw ρ hρ ε v Dtv z = 0 := by
    have h := buCut_data_zero_off_support κ vσ Dvσ D2vσ Dtvσ z hz
    rw [← hfieldEq, ← hDwEq, ← hD2Eq, ← hDtEq]
    exact h
  have hcompact : HasCompactSupport (buGaussianShiftedCutoffField ρ hρ ε v) := by
    apply HasCompactSupport.of_support_subset_isCompact hKcompact
    intro z hz
    by_contra hnot
    exact hz (hzero z hnot).1
  have hsupport : tsupport (buGaussianShiftedCutoffField ρ hρ ε v) ⊆
      spaceTimeSet univ (Ioo 0 2) := by
    have hfieldSupport : Function.support
        (buGaussianShiftedCutoffField ρ hρ ε v) ⊆ K := by
      intro z hz
      by_contra hnot
      exact hz (hzero z hnot).1
    have hts := closure_minimal hfieldSupport hKcompact.isClosed
    intro z hz
    have hKz := hKsource (hts hz)
    exact ⟨Set.mem_univ _, ⟨by linarith only [hKz.2.1], hKz.2.2⟩⟩
  have hweakFinal : HasSpaceTimeWeakDerivs univ (Ioo 0 2)
      (buGaussianShiftedCutoffField ρ hρ ε v)
      (buGaussianShiftedCutoffDw ρ hρ ε v Dv)
      (buGaussianShiftedCutoffD2w ρ hρ ε v Dv D2v)
      (buGaussianShiftedCutoffDtw ρ hρ ε v Dtv) := by
    have hweakCut' : HasSpaceTimeWeakDerivs B I
        (buGaussianShiftedCutoffField ρ hρ ε v)
        (buGaussianShiftedCutoffDw ρ hρ ε v Dv)
        (buGaussianShiftedCutoffD2w ρ hρ ε v Dv D2v)
        (buGaussianShiftedCutoffDtw ρ hρ ε v Dtv) := by
      have hucField : ucCutoffField θ η χ vσ = buCutField κ vσ := by
        funext z
        change ucCutoffScalar θ η χ z • vσ z = buCutScalar κ z • vσ z
        rw [← hscalarFun]
      have hucDw : ucCutoffDw θ η χ vσ Dvσ = buCutDw κ vσ Dvσ := by
        funext z
        funext i
        funext j
        change ucCutoffScalar θ η χ z * Dvσ z i j + vσ z i *
            spatialPartial (ucCutoffScalar θ η χ) j z =
          buCutScalar κ z * Dvσ z i j + vσ z i *
            spatialPartial (buCutScalar κ) j z
        rw [← hscalarFun]
      have hucD2 : ucCutoffD2 θ η χ vσ Dvσ D2vσ =
          buCutD2 κ vσ Dvσ D2vσ := by
        funext z
        funext i
        funext j
        funext k
        change ucCutoffScalar θ η χ z * D2vσ z i j k +
            spatialPartial (ucCutoffScalar θ η χ) k z * Dvσ z i j +
            spatialPartial (ucCutoffScalar θ η χ) j z * Dvσ z i k +
            vσ z i * spatialSecondPartial (ucCutoffScalar θ η χ) j k z =
          buCutScalar κ z * D2vσ z i j k +
            spatialPartial (buCutScalar κ) k z * Dvσ z i j +
            spatialPartial (buCutScalar κ) j z * Dvσ z i k +
            vσ z i * spatialSecondPartial (buCutScalar κ) j k z
        rw [← hscalarFun]
      have hucDt : ucCutoffDt θ η χ vσ Dtvσ = buCutDt κ vσ Dtvσ := by
        funext z
        funext i
        change ucCutoffScalar θ η χ z * Dtvσ z i + vσ z i *
            timePartial (ucCutoffScalar θ η χ) z =
          buCutScalar κ z * Dtvσ z i + vσ z i *
            timePartial (buCutScalar κ) z
        rw [← hscalarFun]
      change HasSpaceTimeWeakDerivs B I
        (ucCutoffField θ η χ vσ) (ucCutoffDw θ η χ vσ Dvσ)
        (ucCutoffD2 θ η χ vσ Dvσ D2vσ) (ucCutoffDt θ η χ vσ Dtvσ) at hweakCut
      rw [hucField, hucDw, hucD2, hucDt] at hweakCut
      rw [hfieldEq, hDwEq, hD2Eq, hDtEq] at hweakCut
      exact hweakCut
    exact bu_weak_extend_compact (isOpen_vec3Ball 0 ρ) isOpen_Ioo
      hKcompact hKsource (by
        intro z hz
        have h := hKsource hz
        exact ⟨Set.mem_univ _, ⟨by linarith only [h.2.1], h.2.2⟩⟩)
      (buGaussianShiftedCutoffField ρ hρ ε v)
      (buGaussianShiftedCutoffDw ρ hρ ε v Dv)
      (buGaussianShiftedCutoffD2w ρ hρ ε v Dv D2v)
      (buGaussianShiftedCutoffDtw ρ hρ ε v Dtv) hzero hweakCut'
      ⟨by simpa only [hfieldEq] using hmemCut.1,
        ⟨by simpa only [hDwEq] using hmemCut.2.1,
          ⟨by simpa only [hD2Eq] using hmemCut.2.2.1,
            by simpa only [hDtEq] using hmemCut.2.2.2⟩⟩⟩
  exact ⟨hweakFinal, hcompact, hsupport,
    by simpa only [hfieldEq] using hmemCut.1,
    by simpa only [hDwEq] using hmemCut.2.1,
    by simpa only [hD2Eq] using hmemCut.2.2.1,
    by simpa only [hDtEq] using hmemCut.2.2.2⟩

end ESS
