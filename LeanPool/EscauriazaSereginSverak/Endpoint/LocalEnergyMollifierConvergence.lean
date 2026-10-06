/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.SpaceTimeMollifier
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpConvolution
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Pi

public section

open CKN

open Filter Function MeasureTheory Set Topology
open scoped ENNReal Convolution Topology Pointwise
open CKN.Foundation.Parabolic


noncomputable section

namespace ESS

local instance localEnergyConvergenceVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure (volume : Measure Vec3) (volume : Measure ℝ)

local instance localEnergyConvergenceVolumeIsAddLeftInvariant :
    Measure.IsAddLeftInvariant (volume : Measure (Vec3 × ℝ)) :=
  localEnergyConvergenceVolumeIsAddHaarMeasure.toIsAddLeftInvariant

@[expose] abbrev LocalEnergyVec4 := CKN.Vec 4

@[expose] def localEnergySpaceTimeCoord : LocalEnergyVec4 ≃ᵐ (Vec3 × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) (Fin.last 3)).trans
    MeasurableEquiv.prodComm

private theorem localEnergySpaceTimeCoord_measurePreserving :
    MeasurePreserving localEnergySpaceTimeCoord
      (volume : Measure LocalEnergyVec4) (volume : Measure (Vec3 × ℝ)) := by
  have h1 := volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) (Fin.last 3)
  have h2 : MeasurePreserving Prod.swap
      ((volume : Measure ℝ).prod (volume : Measure Vec3))
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) :=
    Measure.measurePreserving_swap
  simpa only [localEnergySpaceTimeCoord, Measure.volume_eq_prod] using h1.trans h2

private theorem localEnergySpaceTimeCoord_apply (x : LocalEnergyVec4) :
    localEnergySpaceTimeCoord x =
      ((fun i : Fin 3 => x i.castSucc), x (Fin.last 3)) := by
  change ((Fin.last 3).removeNth x, x (Fin.last 3)) = _
  apply Prod.ext
  · ext i
    change x ((Fin.last 3).succAbove i) = x i.castSucc
    rw [Fin.succAbove_last_apply]
  · rfl

private theorem localEnergySpaceTimeCoord_sub (x y : LocalEnergyVec4) :
    localEnergySpaceTimeCoord (x - y) =
      localEnergySpaceTimeCoord x - localEnergySpaceTimeCoord y := by
  ext <;> simp [localEnergySpaceTimeCoord_apply]

private theorem localEnergy_convolution_transport
    {f : Vec3 × ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (x : LocalEnergyVec4) :
    convolution (fun z : LocalEnergyVec4 =>
        spaceTimeMollifier δ hδ (localEnergySpaceTimeCoord z))
      (fun z : LocalEnergyVec4 => f (localEnergySpaceTimeCoord z))
      (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure LocalEnergyVec4) x =
      spaceTimeMollify f δ hδ (localEnergySpaceTimeCoord x) := by
  let k : Vec3 × ℝ → ℝ := spaceTimeMollifier δ hδ
  let G : Vec3 × ℝ → ℝ := fun z => k z * f (localEnergySpaceTimeCoord x - z)
  have hchange : (fun z : LocalEnergyVec4 =>
      spaceTimeMollifier δ hδ (localEnergySpaceTimeCoord z) *
        f (localEnergySpaceTimeCoord (x - z))) =
      fun z => G (localEnergySpaceTimeCoord z) := by
    funext z
    change spaceTimeMollifier δ hδ (localEnergySpaceTimeCoord z) *
        f (localEnergySpaceTimeCoord (x - z)) =
      k (localEnergySpaceTimeCoord z) *
        f (localEnergySpaceTimeCoord x - localEnergySpaceTimeCoord z)
    rw [show spaceTimeMollifier δ hδ (localEnergySpaceTimeCoord z) =
      k (localEnergySpaceTimeCoord z) by rfl, localEnergySpaceTimeCoord_sub]
  rw [show convolution (fun z : LocalEnergyVec4 =>
        spaceTimeMollifier δ hδ (localEnergySpaceTimeCoord z))
      (fun z : LocalEnergyVec4 => f (localEnergySpaceTimeCoord z))
      (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure LocalEnergyVec4) x =
      ∫ z, spaceTimeMollifier δ hδ (localEnergySpaceTimeCoord z) *
        f (localEnergySpaceTimeCoord (x - z)) ∂(volume : Measure LocalEnergyVec4) by
          rw [convolution_def]
          simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]]
  rw [hchange,
    localEnergySpaceTimeCoord_measurePreserving.integral_comp
      localEnergySpaceTimeCoord.measurableEmbedding G]
  rfl

/-- The space-time kernel contracts every finite-exponent Lebesgue norm, by transport to
four Euclidean coordinates and the normalized convolution estimate. -/
theorem localEnergy_spaceTimeMollify_eLpNorm_le {f : Vec3 × ℝ → ℝ} {δ : ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hδ : 0 < δ)
    (hf : MemLp f p (volume : Measure (Vec3 × ℝ))) :
    eLpNorm (spaceTimeMollify f δ hδ) p (volume : Measure (Vec3 × ℝ)) ≤
      eLpNorm f p (volume : Measure (Vec3 × ℝ)) := by
  let k : Vec3 × ℝ → ℝ := spaceTimeMollifier δ hδ
  let k4 : LocalEnergyVec4 → ℝ := fun x => k (localEnergySpaceTimeCoord x)
  let f4 : LocalEnergyVec4 → ℝ := fun x => f (localEnergySpaceTimeCoord x)
  have hkmeas : Measurable k4 :=
    (spaceTimeMollifier_contDiff hδ (n := 0)).continuous.measurable.comp
      localEnergySpaceTimeCoord.measurable
  have hfae : AEMeasurable f4 (volume : Measure LocalEnergyVec4) :=
    (hf.aestronglyMeasurable.comp_measurePreserving
      localEnergySpaceTimeCoord_measurePreserving).aemeasurable
  have hkint : Integrable k volume :=
    (spaceTimeMollifier_contDiff hδ (n := 0)).continuous.integrable_of_hasCompactSupport
      (spaceTimeMollifier_hasCompactSupport hδ)
  have hk4int : Integrable k4 (volume : Measure LocalEnergyVec4) := by
    have hkA : AEStronglyMeasurable k volume :=
      (spaceTimeMollifier_contDiff hδ (n := 0)).continuous.aestronglyMeasurable
    exact (localEnergySpaceTimeCoord_measurePreserving.integrable_comp hkA).2 hkint
  have hknonneg : ∀ x : LocalEnergyVec4, 0 ≤ k4 x :=
    fun x => spaceTimeMollifier_nonneg hδ _
  have hkone : ∫ x : LocalEnergyVec4, k4 x ∂volume = 1 := by
    calc
      ∫ x : LocalEnergyVec4, k4 x ∂volume =
          ∫ x, k (localEnergySpaceTimeCoord x) ∂volume := by rfl
      _ = ∫ x, k x ∂(volume : Measure (Vec3 × ℝ)) :=
        localEnergySpaceTimeCoord_measurePreserving.integral_comp
          localEnergySpaceTimeCoord.measurableEmbedding k
      _ = 1 := spaceTimeMollifier_integral_one hδ
  have hbound := CKN.young_convolution_nonneg_integral_one_of_aemeasurable
    (d := 4) (p := p) hp hpTop hknonneg hk4int hkone hkmeas hfae
  have htrans : (fun x : LocalEnergyVec4 =>
      spaceTimeMollify f δ hδ (localEnergySpaceTimeCoord x)) =
      convolution k4 f4 (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    symm
    simpa [k4, f4] using localEnergy_convolution_transport hδ x
  have hloc : LocallyIntegrable f (volume : Measure (Vec3 × ℝ)) := hf.locallyIntegrable hp
  have hmollify : AEStronglyMeasurable (spaceTimeMollify f δ hδ)
      (volume : Measure (Vec3 × ℝ)) :=
    (spaceTimeMollify_contDiff (n := 0) hδ hloc).continuous.aestronglyMeasurable
  have hnorm_conv : eLpNorm (spaceTimeMollify f δ hδ) p
      (volume : Measure (Vec3 × ℝ)) = eLpNorm (convolution k4 f4
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) p (volume : Measure LocalEnergyVec4) := by
    calc
      eLpNorm (spaceTimeMollify f δ hδ) p (volume : Measure (Vec3 × ℝ)) =
          eLpNorm (fun x : LocalEnergyVec4 =>
            spaceTimeMollify f δ hδ (localEnergySpaceTimeCoord x))
            p (volume : Measure LocalEnergyVec4) :=
        (eLpNorm_comp_measurePreserving hmollify
          localEnergySpaceTimeCoord_measurePreserving).symm
      _ = eLpNorm (convolution k4 f4 (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          p (volume : Measure LocalEnergyVec4) := by rw [htrans]
  have hnorm_f : eLpNorm f4 p (volume : Measure LocalEnergyVec4) =
      eLpNorm f p (volume : Measure (Vec3 × ℝ)) := by
    change eLpNorm (fun x : LocalEnergyVec4 => f (localEnergySpaceTimeCoord x))
      p (volume : Measure LocalEnergyVec4) = _
    exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
      localEnergySpaceTimeCoord_measurePreserving
  rw [hnorm_conv, ← hnorm_f]
  exact hbound

theorem tendsto_eLpNorm_sub_zero_spaceTimeMollify_lp
    {g : Vec3 × ℝ → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (hg : MemLp g p (volume : Measure (Vec3 × ℝ)))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (nhds 0))
    (hε_pos : ∀ n, 0 < ε n) :
    Tendsto
      (fun n => eLpNorm
        (fun x => spaceTimeMollify g (ε n) (hε_pos n) x - g x)
        p (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  obtain ⟨η₁, hη₁_pos, hη₁⟩ :=
    MeasureTheory.exists_Lp_half (μ := (volume : Measure (Vec3 × ℝ)))
      (ε := ℝ) (p := p) hη.ne'
  obtain ⟨η₂, hη₂_pos, hη₂⟩ :=
    MeasureTheory.exists_Lp_half (μ := (volume : Measure (Vec3 × ℝ)))
      (ε := ℝ) (p := p) hη₁_pos.ne'
  let δ : ℝ≥0∞ := min η₁ η₂
  have hδ_pos : 0 < δ := lt_min hη₁_pos hη₂_pos
  obtain ⟨f', hf'_supp, happrox', hf'_cont, hf'_mem⟩ :=
    hg.exists_hasCompactSupport_eLpNorm_sub_le hpTop hδ_pos.ne'
  have hdiff_mem : MemLp (fun x => g x - f' x) p
      (volume : Measure (Vec3 × ℝ)) := hg.sub hf'_mem
  have hthird_norm :
      eLpNorm (fun x => f' x - g x) p (volume : Measure (Vec3 × ℝ)) ≤ η₁ := by
    have hneg : (fun x => f' x - g x) = -(fun x => g x - f' x) := by
      ext x
      change f' x - g x = -(g x - f' x)
      abel_nf
    rw [hneg, eLpNorm_neg]
    exact happrox'.trans (min_le_left _ _)
  have hmid_eventually : ∀ᶠ n in atTop,
      eLpNorm
        (fun x => spaceTimeMollify f' (ε n) (hε_pos n) x - f' x)
        p (volume : Measure (Vec3 × ℝ)) ≤ η₂ := by
    by_cases hη₂_top : η₂ = ⊤
    · exact Eventually.of_forall (fun _ => by simp [hη₂_top])
    · let K : Set (Vec3 × ℝ) := Metric.closedBall 0 1 + tsupport f'
      have hK_compact : IsCompact K :=
        (isCompact_closedBall (0 : Vec3 × ℝ) 1).add hf'_supp.isCompact
      have hK_meas : MeasurableSet K := hK_compact.measurableSet
      have hK_ne_top : volume K ≠ ⊤ := hK_compact.measure_lt_top.ne
      have hpow_ne_top : volume K ^ (1 / p.toReal) ≠ ⊤ :=
        (ENNReal.rpow_lt_top_of_nonneg (by positivity) hK_ne_top).ne
      let cK : ℝ := (volume K ^ (1 / p.toReal)).toReal
      have hcK_nonneg : 0 ≤ cK := ENNReal.toReal_nonneg
      have hpow_eq : ENNReal.ofReal cK = volume K ^ (1 / p.toReal) := by
        dsimp [cK]
        exact ENNReal.ofReal_toReal hpow_ne_top
      have hη₂_real : 0 < η₂.toReal := ENNReal.toReal_pos hη₂_pos.ne' hη₂_top
      let δr : ℝ := η₂.toReal / (cK + 1)
      have hδr_pos : 0 < δr := by dsimp [δr]; positivity
      obtain ⟨γ, hγ_pos, hγ⟩ :=
        Metric.uniformContinuous_iff.mp
          (hf'_supp.uniformContinuous_of_continuous hf'_cont) δr hδr_pos
      have hε_small : ∀ᶠ n in atTop, ε n < γ / 2 :=
        (tendsto_order.1 hε).2 _ (by positivity)
      have hε_le_one : ∀ᶠ n in atTop, ε n ≤ 1 :=
        ((tendsto_order.1 hε).2 _ zero_lt_one).mono (fun _ hn => le_of_lt hn)
      filter_upwards [hε_small, hε_le_one] with n hn_small hn_one
      have hkernel_support :
          support (spaceTimeMollifier (ε n) (hε_pos n)) ⊆ Metric.ball 0 (ε n) := by
        rw [spaceTimeMollifier_support]
      have hdist : ∀ x,
          dist (spaceTimeMollify f' (ε n) (hε_pos n) x) (f' x) ≤ δr := by
        intro x
        apply MeasureTheory.dist_convolution_le (le_of_lt hδr_pos)
        · exact hkernel_support
        · exact spaceTimeMollifier_nonneg (hε_pos n)
        · exact spaceTimeMollifier_integral_one (hε_pos n)
        · exact hf'_cont.aestronglyMeasurable
        · intro y hy
          rw [Metric.mem_ball, dist_eq_norm_sub] at hy
          apply (hγ ?_).le
          rw [dist_eq_norm_sub]
          exact hy.trans (by linarith only [hn_small, hγ_pos])
      have hconv_support : support (spaceTimeMollify f' (ε n) (hε_pos n)) ⊆ K := by
        calc
          support (spaceTimeMollify f' (ε n) (hε_pos n)) ⊆
              Metric.ball 0 (ε n) + support f' := spaceTimeMollify_support_subset (hε_pos n)
          _ ⊆ Metric.closedBall 0 1 + tsupport f' :=
            add_subset_add (Metric.ball_subset_closedBall.trans
              (Metric.closedBall_subset_closedBall hn_one)) (subset_tsupport _)
      have hf'_support : support f' ⊆ K := by
        intro x hx
        refine ⟨0, ?_, x, subset_tsupport f' hx, by simp only [zero_add]⟩
        simp only [Metric.mem_closedBall, dist_zero_right, norm_zero]
        exact zero_le_one
      have hbound :
          eLpNorm (fun x => spaceTimeMollify f' (ε n) (hε_pos n) x - f' x)
            p volume ≤ ENNReal.ofReal δr * volume K ^ (1 / p.toReal) := by
        have hmeas : AEStronglyMeasurable
            (fun x => spaceTimeMollify f' (ε n) (hε_pos n) x - f' x) volume :=
          ((spaceTimeMollify_contDiff (n := 0) (hε_pos n)
            (hf'_cont.integrable_of_hasCompactSupport hf'_supp).locallyIntegrable).continuous.sub
            hf'_cont).aestronglyMeasurable
        exact eLpNorm_sub_le_of_dist_bdd volume hpTop hK_meas.nullMeasurableSet
          hδr_pos.le hmeas hdist hconv_support hf'_support
      have hδmul : δr * cK ≤ η₂.toReal := by
        have hfrac_le : cK / (cK + 1) ≤ 1 :=
          div_le_one_of_le₀ (by linarith only [hcK_nonneg]) (by linarith only [hcK_nonneg])
        calc
          δr * cK = η₂.toReal * (cK / (cK + 1)) := by
            dsimp [δr]
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring_nf
          _ ≤ η₂.toReal * 1 := mul_le_mul_of_nonneg_left hfrac_le hη₂_real.le
          _ = η₂.toReal := mul_one _
      calc
        eLpNorm (fun x => spaceTimeMollify f' (ε n) (hε_pos n) x - f' x)
            p (volume : Measure (Vec3 × ℝ)) ≤
            ENNReal.ofReal δr * volume K ^ (1 / p.toReal) := hbound
        _ = ENNReal.ofReal (δr * cK) := by
          rw [← hpow_eq, ← ENNReal.ofReal_mul]
          positivity
        _ ≤ η₂ := by
          rw [← ENNReal.ofReal_toReal hη₂_top]
          exact ENNReal.ofReal_le_ofReal hδmul
  filter_upwards [hmid_eventually] with n hmid
  let k : Vec3 × ℝ → ℝ := spaceTimeMollifier (ε n) (hε_pos n)
  have hk_compact : HasCompactSupport k := spaceTimeMollifier_hasCompactSupport (hε_pos n)
  have hk_cont : Continuous k := (spaceTimeMollifier_contDiff (hε_pos n) (n := 0)).continuous
  have hg_loc : LocallyIntegrable g (volume : Measure (Vec3 × ℝ)) :=
    hg.locallyIntegrable hp
  have hf'_loc : LocallyIntegrable f' (volume : Measure (Vec3 × ℝ)) :=
    hf'_mem.locallyIntegrable hp
  have hdiff_loc : LocallyIntegrable (fun x => g x - f' x)
      (volume : Measure (Vec3 × ℝ)) := hg_loc.sub hf'_loc
  have hconv_g : ConvolutionExists k g (ContinuousLinearMap.lsmul ℝ ℝ)
      (volume : Measure (Vec3 × ℝ)) :=
    hk_compact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont hg_loc
  have hconv_f : ConvolutionExists k f' (ContinuousLinearMap.lsmul ℝ ℝ)
      (volume : Measure (Vec3 × ℝ)) :=
    hk_compact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont hf'_loc
  have hconv_diff : ConvolutionExists k (fun x => g x - f' x)
      (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure (Vec3 × ℝ)) :=
    hk_compact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont hdiff_loc
  have hsplit : g = (fun x => g x - f' x) + f' := by
    ext x
    change g x = (g x - f' x) + f' x
    abel_nf
  have hconv_split :
      k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g =
        (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f' := by
    calc
      k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g =
          k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((fun x => g x - f' x) + f') := by
            exact congrArg (fun v => k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) hsplit
      _ = (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f' := hconv_diff.distrib_add hconv_f
  have hfirst_norm :
      eLpNorm (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x)
        p (volume : Measure (Vec3 × ℝ)) ≤ η₂ := by
    calc
      eLpNorm (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x)
          p (volume : Measure (Vec3 × ℝ)) ≤
        eLpNorm (fun x => g x - f' x) p (volume : Measure (Vec3 × ℝ)) := by
          simpa only [spaceTimeMollify, k] using
            (localEnergy_spaceTimeMollify_eLpNorm_le hp hpTop (hε_pos n) hdiff_mem)
      _ ≤ η₂ := happrox'.trans (min_le_right _ _)
  have hfirst_middle :
      eLpNorm
        ((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f') x - f' x)
        p (volume : Measure (Vec3 × ℝ)) < η₁ := by
    exact hη₂ _ _ hfirst_norm (by simpa only [spaceTimeMollify, k] using hmid)
  have hsum :
      eLpNorm
        (((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f') x - f' x) +
          fun x => f' x - g x)
        p (volume : Measure (Vec3 × ℝ)) < η :=
    hη₁ _ _ hfirst_middle.le hthird_norm
  have hdecomp :
      eLpNorm
        (fun x => spaceTimeMollify g (ε n) (hε_pos n) x - g x)
        p (volume : Measure (Vec3 × ℝ)) =
      eLpNorm
        (((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f') x - f' x) +
          fun x => f' x - g x)
        p (volume : Measure (Vec3 × ℝ)) := by
    rw [show spaceTimeMollify g (ε n) (hε_pos n) =
        k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g by rfl, hconv_split]
    congr 1
    ext x
    simp only [Pi.add_apply]
    abel_nf
  exact hdecomp ▸ hsum.le


end ESS
