/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureSpaceTimeCore
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureSpaceTimeLp
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Spatial slices of the space-time pressure

The space-time pressure extension acts on almost every spatial slice by the
corresponding spatial Riesz operator (`def:riesz-pressure`).
-/

public section

open MeasureTheory
open Filter
open scoped ENNReal
open scoped Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem rieszPressure_double_sum_ae
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (q : ℝ≥0∞)
    (T : Fin 3 → Fin 3 → Lp ℝ q μ) :
    (fun x => ∑ i : Fin 3, ∑ j : Fin 3, T i j x) =ᵐ[μ]
      (∑ i : Fin 3, ∑ j : Fin 3, T i j : Lp ℝ q μ) := by
  have hOuter := Lp.coeFn_finsetSum Finset.univ
    (fun i : Fin 3 => ∑ j : Fin 3, T i j)
  have hInner (i : Fin 3) := Lp.coeFn_finsetSum Finset.univ (T i)
  filter_upwards [hOuter, ae_all_iff.2 hInner] with x hOuter hInner
  have hOuter' :
      (∑ i : Fin 3, ∑ j : Fin 3, T i j : Lp ℝ q μ) x =
        ∑ i : Fin 3, (∑ j : Fin 3, T i j : Lp ℝ q μ) x := by
    simpa only [Finset.sum_apply] using hOuter
  calc
    (∑ i : Fin 3, ∑ j : Fin 3, T i j x) =
        ∑ i : Fin 3, (∑ j : Fin 3, T i j : Lp ℝ q μ) x := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hInner i).symm
    _ = (∑ i : Fin 3, ∑ j : Fin 3, T i j : Lp ℝ q μ) x := hOuter'.symm

private theorem rieszPressureSpaceTimeCoreClass_tendsto
    (r : ℝ) (hr : 1 < r)
    (u : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    ∃ F : ℕ → RieszPressureCompactInput,
      Tendsto (fun n => rieszPressureCompactInputLpClass r hr (F n)) atTop
        (𝓝 u) := by
  let : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  let S : Set (Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) :=
    {v | v ∈ rieszPressureSpaceTimeCore r hr}
  have hDense : Dense S := by
    simpa only [S] using rieszPressureSpaceTimeCore_dense r hr
  have hclose : u ∈ closure S := by
    rw [hDense.closure_eq]
    exact Set.mem_univ u
  have happrox (n : ℕ) : ∃ v ∈ S,
      dist v u < (1 / 2 : ℝ) ^ n := by
    obtain ⟨v, hv, hdist⟩ :=
      (Metric.mem_closure_iff.mp hclose) ((1 / 2 : ℝ) ^ n) (by positivity)
    have hdist' : dist v u < (1 / 2 : ℝ) ^ n := by
      rw [dist_comm]
      exact hdist
    exact ⟨v, hv, hdist'⟩
  let v (n : ℕ) := Classical.choose (happrox n)
  have hvS (n : ℕ) : v n ∈ S := (Classical.choose_spec (happrox n)).1
  have hdist (n : ℕ) : dist (v n) u < (1 / 2 : ℝ) ^ n :=
    (Classical.choose_spec (happrox n)).2
  let F (n : ℕ) : RieszPressureCompactInput := Classical.choose (hvS n)
  have hclass (n : ℕ) : (v n : Lp ℝ (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ))) = rieszPressureCompactInputLpClass r hr (F n) :=
    Classical.choose_spec (hvS n)
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one
      (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨F, ?_⟩
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hpow.eventually (gt_mem_nhds hε))
  refine ⟨N, ?_⟩
  intro n hn
  change dist (rieszPressureCompactInputLpClass r hr (F n)) u < ε
  rw [← hclass n]
  exact lt_trans (hdist n) (hN n hn)

private theorem rieszPressureSpaceTimeComponent_ae_slice_eq_of_compact
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    {F : Vec3 × ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      (fun x : Vec3 => ((Lp.aestronglyMeasurable
        (rieszPressureSpaceTimeComponent r hr i j
          ((hF.memLp_of_hasCompactSupport hFc).toLp F))).aemeasurable.mk
            (rieszPressureSpaceTimeComponent r hr i j
              ((hF.memLp_of_hasCompactSupport hFc).toLp F))) (x,t)) =ᵐ[volume]
      fun x : Vec3 => rieszPressureOperator r hr i j
        (((hF.comp (continuous_id.prodMk continuous_const)).memLp_of_hasCompactSupport
          (continuous_spaceTimeSlice_hasCompactSupport hFc t)).toLp
          (fun y => F (y,t))) x := by
  obtain ⟨P, hPm, hPmem, hPclass, hPslice⟩ :=
    exists_rieszPressureComponentCompactClass_representative r hr i j hF hFc
  have hEq : rieszPressureSpaceTimeComponent r hr i j
      ((hF.memLp_of_hasCompactSupport hFc).toLp F) =
        rieszPressureComponentCompactClass r hr i j (F := F) hF hFc :=
    rieszPressureSpaceTimeComponent_eq_compact r hr i j hF hFc
  let O := rieszPressureSpaceTimeComponent r hr i j
    ((hF.memLp_of_hasCompactSupport hFc).toLp F)
  let Pout := (Lp.aestronglyMeasurable O).aemeasurable.mk O
  have hPoutMeas : Measurable Pout :=
    (Lp.aestronglyMeasurable O).aemeasurable.measurable_mk
  have hOAE : (O : Vec3 × ℝ → ℝ) =ᵐ[volume] Pout :=
    (Lp.aestronglyMeasurable O).aemeasurable.ae_eq_mk
  have hOP : (O : Vec3 × ℝ → ℝ) =ᵐ[volume] P := by
    rw [show O = rieszPressureComponentCompactClass r hr i j
        (F := F) hF hFc from hEq]
    exact hPclass.symm
  have hRepP : Pout =ᵐ[volume] P := hOAE.symm.trans hOP
  have hRep := ae_time_sections_of_ae_eq hPoutMeas hPm hRepP
  filter_upwards [hRep, hPslice] with t hPt hSlice
  exact hPt.trans hSlice

private theorem rieszPressure_exists_slice_subsequence
    (r : ℝ) (hr : 1 < r)
    [Fact (1 ≤ ENNReal.ofReal r)]
    {F : ℕ → Vec3 × ℝ → ℝ} {f : Vec3 × ℝ → ℝ}
    (hF : ∀ n, MemLp (F n) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ)))
    (hf : MemLp f (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)))
    (hconv : Tendsto (fun n => (hF n).toLp (F n)) atTop
      (𝓝 (hf.toLp f))) :
    ∃ n : ℕ → ℕ, Tendsto n atTop atTop ∧
      ∀ᵐ t ∂(volume : Measure ℝ),
        (∀ k, MemLp (fun x : Vec3 => F (n k) (x, t) - f (x, t))
          (ENNReal.ofReal r) (volume : Measure Vec3)) ∧
        Tendsto (fun k => eLpNorm
          (fun x : Vec3 => F (n k) (x, t) - f (x, t))
          (ENNReal.ofReal r) (volume : Measure Vec3)) atTop (𝓝 0) := by
  let : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  let δ (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k
  have hδpos (k : ℕ) : 0 < δ k := by
    dsimp [δ]
    positivity
  have hnear (k : ℕ) :
      ∀ᶠ m : ℕ in atTop,
        dist ((hF m).toLp (F m)) (hf.toLp f) < δ k :=
    hconv.eventually (Metric.ball_mem_nhds _ (hδpos k))
  let N (k : ℕ) : ℕ := Classical.choose (Filter.eventually_atTop.1 (hnear k))
  have hN (k m : ℕ) (hm : N k ≤ m) :
      dist ((hF m).toLp (F m)) (hf.toLp f) < δ k :=
    Classical.choose_spec (Filter.eventually_atTop.1 (hnear k)) m hm
  let n (k : ℕ) : ℕ := max k (N k)
  have hnle (k : ℕ) : k ≤ n k := le_max_left _ _
  have hdist (k : ℕ) :
      dist ((hF (n k)).toLp (F (n k))) (hf.toLp f) < δ k := by
    exact hN k (n k) (le_max_right _ _)
  have hnTendsto : Tendsto n atTop atTop :=
    tendsto_atTop_mono hnle tendsto_id
  let H (k : ℕ) (t : ℝ) : ℝ≥0∞ :=
    eLpNorm (fun x : Vec3 => F (n k) (x, t) - f (x, t))
      (ENNReal.ofReal r) (volume : Measure Vec3) ^ r
  have hDiff (k : ℕ) : MemLp (fun z : Vec3 × ℝ => F (n k) z - f z)
      (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) :=
    (hF (n k)).sub hf
  have hProdBound (k : ℕ) :
      eLpNorm (fun z : Vec3 × ℝ => F (n k) z - f z)
          (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ^ r ≤
        (ENNReal.ofReal (1 / 2 : ℝ)) ^ k := by
    have hErr : eLpNorm (fun z : Vec3 × ℝ => F (n k) z - f z)
        (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) <
          ENNReal.ofReal (δ k) := by
      calc
        _ = edist ((hF (n k)).toLp (F (n k))) (hf.toLp f) :=
          (Lp.edist_toLp_toLp (F (n k)) f (hF (n k)) hf).symm
        _ = ENNReal.ofReal
            (dist ((hF (n k)).toLp (F (n k))) (hf.toLp f)) :=
          Lp.edist_dist _ _
        _ < ENNReal.ofReal (δ k) := by
          rw [ENNReal.ofReal_lt_ofReal_iff (hδpos k)]
          exact hdist k
    have hδle : δ k ≤ 1 := by
      dsimp [δ]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    calc
      _ ≤ ENNReal.ofReal (δ k) ^ r :=
        ENNReal.rpow_le_rpow hErr.le (le_of_lt (lt_trans zero_lt_one hr))
      _ ≤ ENNReal.ofReal (δ k) :=
        ENNReal.rpow_le_self_of_le_one
          (ENNReal.ofReal_le_one.mpr hδle) hr.le
      _ = (ENNReal.ofReal (1 / 2 : ℝ)) ^ k := by
        dsimp [δ]
        rw [ENNReal.ofReal_pow (by norm_num)]
  have hHmeas (k : ℕ) : AEMeasurable (H k) (volume : Measure ℝ) := by
    have hDiffProd : AEStronglyMeasurable
        (fun z : Vec3 × ℝ => F (n k) z - f z)
        ((volume : Measure Vec3).prod (volume : Measure ℝ)) := by
      rw [← Measure.volume_eq_prod]
      exact (hDiff k).aestronglyMeasurable
    have hPow : AEMeasurable
        (fun z : Vec3 × ℝ => ‖F (n k) z - f z‖ₑ ^ r)
        ((volume : Measure Vec3).prod (volume : Measure ℝ)) := by
      exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
        hDiffProd.aemeasurable.enorm
    let G : ℝ → ℝ≥0∞ := fun t =>
      ∫⁻ x : Vec3, ‖F (n k) (x, t) - f (x, t)‖ₑ ^ r ∂(volume : Measure Vec3)
    have hGmeas : AEMeasurable G (volume : Measure ℝ) := by
      exact hPow.lintegral_prod_left'
    have hEq : H k =ᵐ[volume] G := by
      filter_upwards [hDiffProd.prodMk_right] with t ht
      have hp0 : (ENNReal.ofReal r) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one hr)).ne'
      rw [show H k t = eLpNorm
          (fun x : Vec3 => F (n k) (x, t) - f (x, t))
            (ENNReal.ofReal r) (volume : Measure Vec3) ^ r from rfl,
        eLpNorm_eq_eLpNorm' hp0 ENNReal.ofReal_ne_top ht,
        ENNReal.toReal_ofReal (le_trans zero_le_one hr.le),
        ← lintegral_rpow_enorm_eq_rpow_eLpNorm'
          (f := fun x : Vec3 => F (n k) (x, t) - f (x, t))
          (lt_trans zero_lt_one hr)]
    exact hGmeas.congr hEq.symm
  have hIntegralBound (k : ℕ) :
      (∫⁻ t, H k t ∂(volume : Measure ℝ)) ≤
        (ENNReal.ofReal (1 / 2 : ℝ)) ^ k := by
    have hFubini := eLpNorm_spaceTime_pow_eq_integral_slice r
      (lt_trans zero_lt_one hr) (hDiff k).aestronglyMeasurable
    calc
      _ = eLpNorm (fun z : Vec3 × ℝ => F (n k) z - f z)
            (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ^ r :=
          hFubini.symm
      _ ≤ (ENNReal.ofReal (1 / 2 : ℝ)) ^ k := hProdBound k
  have hsumGeom :
      (∫⁻ t, ∑' k : ℕ, H k t ∂(volume : Measure ℝ)) < ⊤ := by
    rw [lintegral_tsum hHmeas]
    calc
      ∑' k : ℕ, ∫⁻ t, H k t ∂(volume : Measure ℝ) ≤
          ∑' k : ℕ, (ENNReal.ofReal (1 / 2 : ℝ)) ^ k :=
        ENNReal.tsum_le_tsum hIntegralBound
      _ < ⊤ := by
        rw [ENNReal.tsum_geometric]
        norm_num
  have hsumMeas : AEMeasurable (fun t : ℝ => ∑' k : ℕ, H k t)
      (volume : Measure ℝ) := AEMeasurable.tsum hHmeas
  have hsumTop : ∀ᵐ t ∂(volume : Measure ℝ),
      (∑' k : ℕ, H k t) < ⊤ := ae_lt_top' hsumMeas hsumGeom.ne
  have hdiffStrong (k : ℕ) : ∀ᵐ t ∂(volume : Measure ℝ),
      AEStronglyMeasurable
        (fun x : Vec3 => F (n k) (x, t) - f (x, t)) volume :=
    ((hDiff k).aestronglyMeasurable).prodMk_right
  have hdiffStrongAll : ∀ᵐ t ∂(volume : Measure ℝ),
      ∀ k, AEStronglyMeasurable
        (fun x : Vec3 => F (n k) (x, t) - f (x, t)) volume :=
    ae_all_iff.2 hdiffStrong
  refine ⟨n, hnTendsto, ?_⟩
  filter_upwards [hsumTop, hdiffStrongAll] with t ht hstrong
  have hsumne : (∑' k : ℕ, H k t) ≠ ⊤ := (ne_of_lt ht)
  have hpowTendsto : Tendsto (fun k : ℕ => H k t) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsumne
  have hrootTendsto : Tendsto (fun k : ℕ => H k t ^ r⁻¹)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hcont : ContinuousAt (fun a : ℝ≥0∞ => a ^ r⁻¹) 0 :=
      (ENNReal.continuous_rpow_const (y := r⁻¹)).continuousAt
    have hcont0 := hcont.tendsto
    have hcomp := hcont0.comp hpowTendsto
    have hrootpos : 0 < r⁻¹ := inv_pos.mpr (lt_trans zero_lt_one hr)
    have hzero : (0 : ℝ≥0∞) ^ r⁻¹ = 0 :=
      (ENNReal.rpow_eq_zero_iff_of_pos hrootpos).2 rfl
    simpa [Function.comp_def, hzero] using hcomp
  have hprofileTendsto : Tendsto
      (fun k => eLpNorm (fun x : Vec3 => F (n k) (x, t) - f (x, t))
        (ENNReal.ofReal r) (volume : Measure Vec3)) atTop (𝓝 0) := by
    have heq : (fun k : ℕ => eLpNorm
        (fun x : Vec3 => F (n k) (x, t) - f (x, t))
          (ENNReal.ofReal r) (volume : Measure Vec3)) =
        fun k => H k t ^ r⁻¹ := by
      funext k
      rw [show H k t = eLpNorm
          (fun x : Vec3 => F (n k) (x, t) - f (x, t))
            (ENNReal.ofReal r) (volume : Measure Vec3) ^ r from rfl,
        ← ENNReal.rpow_mul]
      have hrmul : r * r⁻¹ = 1 := by
        field_simp [ne_of_gt (lt_trans zero_lt_one hr)]
      rw [hrmul, ENNReal.rpow_one]
    rw [heq]
    exact hrootTendsto
  refine ⟨?_, hprofileTendsto⟩
  intro k
  rw [memLp_iff]
  have hHk : H k t < ⊤ := lt_of_le_of_lt
    (ENNReal.le_tsum (f := fun j : ℕ => H j t) k) ht
  have hpowfin :
      eLpNorm (fun x : Vec3 => F (n k) (x, t) - f (x, t))
          (ENNReal.ofReal r) (volume : Measure Vec3) ^ r < ⊤ := by
    exact hHk
  exact (ENNReal.rpow_lt_top_iff_of_pos (lt_trans zero_lt_one hr)).mp hpowfin

/-- A measurable representative of one space-time pressure component. -/
@[expose]
noncomputable def rieszPressureSpaceTimeComponentRepresentative
    (r : ℝ) (hr : 1 < r) (i j : Fin 3) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) →
      Vec3 × ℝ → ℝ := by
  letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  intro u
  exact (Lp.aestronglyMeasurable
    (rieszPressureSpaceTimeComponent r hr i j u)).aemeasurable.mk
      (rieszPressureSpaceTimeComponent r hr i j u)

/-- The chosen space-time component representative is measurable. -/
theorem rieszPressureSpaceTimeComponentRepresentative_measurable
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    (u : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    Measurable (rieszPressureSpaceTimeComponentRepresentative r hr i j u) := by
  let : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  exact (Lp.aestronglyMeasurable
    (rieszPressureSpaceTimeComponent r hr i j u)).aemeasurable.measurable_mk

/-- The space-time double Riesz transform acts on almost every spatial slice
as the spatial double Riesz transform, used by lem:pressure-split. -/
theorem rieszPressureSpaceTimeComponent_slice_ae_eq
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    {F : Vec3 × ℝ → ℝ}
    (hF : MemLp F (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      ∃ hFt : MemLp (fun x : Vec3 => F (x, t))
          (ENNReal.ofReal r) (volume : Measure Vec3),
        (fun x : Vec3 => rieszPressureSpaceTimeComponentRepresentative r hr i j
          (hF.toLp F) (x, t)) =ᵐ[volume]
          fun x => rieszPressureOperator r hr i j
            (hFt.toLp (fun y : Vec3 => F (y, t))) x := by
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  obtain ⟨C, hCconv⟩ := rieszPressureSpaceTimeCoreClass_tendsto r hr
    (hF.toLp F)
  let fseq (n : ℕ) : Vec3 × ℝ → ℝ := (C n).value
  have hfseq (n : ℕ) : MemLp (fseq n) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ)) :=
    (C n).continuous_value.memLp_of_hasCompactSupport (C n).compact_support_value
  have hfseqClass (n : ℕ) : (hfseq n).toLp (fseq n) =
      rieszPressureCompactInputLpClass r hr (C n) := rfl
  have hFconv : Tendsto (fun n => (hfseq n).toLp (fseq n)) atTop
      (𝓝 (hF.toLp F)) := hCconv.congr fun n => hfseqClass n
  let T := rieszPressureSpaceTimeComponent r hr i j
  let Pclass : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) :=
    T (hF.toLp F)
  let Prep : Vec3 × ℝ → ℝ :=
    rieszPressureSpaceTimeComponentRepresentative r hr i j (hF.toLp F)
  have hPrepMeas : Measurable Prep :=
    rieszPressureSpaceTimeComponentRepresentative_measurable r hr i j (hF.toLp F)
  have hPrepClassAE : Prep =ᵐ[volume] (Pclass : Vec3 × ℝ → ℝ) :=
    (Lp.aestronglyMeasurable Pclass).aemeasurable.ae_eq_mk.symm
  have hPrep : MemLp Prep (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) :=
    (memLp_congr_ae hPrepClassAE).2 (Lp.memLp Pclass)
  have hPrepClass : hPrep.toLp Prep = Pclass := by
    apply Lp.ext
    filter_upwards [hPrep.coeFn_toLp, hPrepClassAE] with z h₁ h₂
    exact h₁.trans h₂
  have hTconv : Tendsto (fun n => T ((hfseq n).toLp (fseq n))) atTop
      (𝓝 Pclass) :=
    T.continuous.continuousAt.tendsto.comp hFconv
  let G (n : ℕ) : Vec3 × ℝ → ℝ := Classical.choose
    (exists_rieszPressureComponentCompactClass_representative r hr i j
      (C n).continuous_value (C n).compact_support_value)
  have hGprops (n : ℕ) := Classical.choose_spec
    (exists_rieszPressureComponentCompactClass_representative r hr i j
      (C n).continuous_value (C n).compact_support_value)
  have hGmem (n : ℕ) : MemLp (G n) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ)) := (hGprops n).2.1
  have hGclassAE (n : ℕ) : G n =ᵐ[volume]
      (rieszPressureComponentCompactClass r hr i j (F := fseq n)
        (C n).continuous_value (C n).compact_support_value :
        Vec3 × ℝ → ℝ) := (hGprops n).2.2.1
  have hGslice (n : ℕ) := (hGprops n).2.2.2
  have hGclass (n : ℕ) : (hGmem n).toLp (G n) =
      T ((hfseq n).toLp (fseq n)) := by
    have hToCompact : (hGmem n).toLp (G n) =
        rieszPressureComponentCompactClass r hr i j (F := fseq n)
          (C n).continuous_value (C n).compact_support_value := by
      apply Lp.ext
      filter_upwards [(hGmem n).coeFn_toLp, hGclassAE n] with z h₁ h₂
      exact h₁.trans h₂
    have hCompact := rieszPressureSpaceTimeComponent_eq_compact r hr i j
      (C n).continuous_value (C n).compact_support_value
    exact hToCompact.trans hCompact.symm
  have hGconv : Tendsto (fun n => (hGmem n).toLp (G n)) atTop
      (𝓝 Pclass) := hTconv.congr fun n => (hGclass n).symm
  obtain ⟨n₁, hn₁, hInputAE⟩ := rieszPressure_exists_slice_subsequence
    r hr (F := fseq) (f := F) hfseq hF hFconv
  have hGconv₁ : Tendsto (fun k => (hGmem (n₁ k)).toLp (G (n₁ k))) atTop
      (𝓝 Pclass) := hGconv.comp hn₁
  obtain ⟨n₂, hn₂, hOutputAE⟩ := rieszPressure_exists_slice_subsequence
    r hr (F := fun k => G (n₁ k)) (f := Prep)
    (fun k => hGmem (n₁ k)) hPrep (by
      rw [hPrepClass]
      exact hGconv₁)
  filter_upwards [hInputAE, hOutputAE,
    ae_all_iff.mpr (fun k => hGslice (n₁ (n₂ k)))] with t hIn hOut hGs
  have hFt : MemLp (fun x : Vec3 => F (x, t)) (ENNReal.ofReal r)
      (volume : Measure Vec3) := by
    have hBaseSlice : MemLp (fun x : Vec3 => fseq (n₁ (n₂ 0)) (x, t))
        (ENNReal.ofReal r) (volume : Measure Vec3) :=
      (C (n₁ (n₂ 0))).continuous_value.comp
        (continuous_id.prodMk continuous_const) |>.memLp_of_hasCompactSupport
          (continuous_spaceTimeSlice_hasCompactSupport
            (C (n₁ (n₂ 0))).compact_support_value t)
    have hRaw : MemLp
        (fun x : Vec3 => fseq (n₁ (n₂ 0)) (x, t) -
          (fseq (n₁ (n₂ 0)) (x, t) - F (x, t)))
        (ENNReal.ofReal r) (volume : Measure Vec3) := by
      change MemLp ((fun x : Vec3 => fseq (n₁ (n₂ 0)) (x, t)) -
        (fun x : Vec3 => fseq (n₁ (n₂ 0)) (x, t) - F (x, t)))
        (ENNReal.ofReal r) (volume : Measure Vec3)
      exact hBaseSlice.sub (hIn.1 (n₂ 0))
    have hEq : (fun x : Vec3 => fseq (n₁ (n₂ 0)) (x, t) -
        (fseq (n₁ (n₂ 0)) (x, t) - F (x, t))) =ᵐ[volume]
          fun x => F (x, t) := by
      filter_upwards [] with x
      ring
    exact (memLp_congr_ae hEq).1 hRaw
  have hPsliceMem : MemLp (fun x : Vec3 => Prep (x, t))
      (ENNReal.ofReal r) (volume : Measure Vec3) := by
    have hfBaseSlice : MemLp
        (fun x : Vec3 => fseq (n₁ (n₂ 0)) (x, t))
        (ENNReal.ofReal r) (volume : Measure Vec3) :=
      (C (n₁ (n₂ 0))).continuous_value.comp
        (continuous_id.prodMk continuous_const) |>.memLp_of_hasCompactSupport
          (continuous_spaceTimeSlice_hasCompactSupport
            (C (n₁ (n₂ 0))).compact_support_value t)
    have hSpatial := Lp.memLp (rieszPressureOperator r hr i j
      (hfBaseSlice.toLp (fun x : Vec3 => fseq (n₁ (n₂ 0)) (x, t))))
    have hBaseSlice : MemLp (fun x : Vec3 => G (n₁ (n₂ 0)) (x, t))
        (ENNReal.ofReal r) (volume : Measure Vec3) :=
      (memLp_congr_ae (hGs 0)).2 hSpatial
    have hRaw : MemLp
        (fun x : Vec3 => G (n₁ (n₂ 0)) (x, t) -
          (G (n₁ (n₂ 0)) (x, t) - Prep (x, t)))
        (ENNReal.ofReal r) (volume : Measure Vec3) := by
      change MemLp ((fun x : Vec3 => G (n₁ (n₂ 0)) (x, t)) -
        (fun x : Vec3 => G (n₁ (n₂ 0)) (x, t) - Prep (x, t)))
        (ENNReal.ofReal r) (volume : Measure Vec3)
      exact hBaseSlice.sub (hOut.1 0)
    have hEq : (fun x : Vec3 => G (n₁ (n₂ 0)) (x, t) -
        (G (n₁ (n₂ 0)) (x, t) - Prep (x, t))) =ᵐ[volume]
          fun x => Prep (x, t) := by
      filter_upwards [] with x
      ring
    exact (memLp_congr_ae hEq).1 hRaw
  let finput (k : ℕ) : Vec3 → ℝ := fun x => fseq (n₁ (n₂ k)) (x, t)
  let goutput (k : ℕ) : Vec3 → ℝ := fun x => G (n₁ (n₂ k)) (x, t)
  have hfinput (k : ℕ) : MemLp (finput k) (ENNReal.ofReal r)
      (volume : Measure Vec3) :=
    (C (n₁ (n₂ k))).continuous_value.comp
      (continuous_id.prodMk continuous_const) |>.memLp_of_hasCompactSupport
        (continuous_spaceTimeSlice_hasCompactSupport
          (C (n₁ (n₂ k))).compact_support_value t)
  have hInputClassConv : Tendsto
      (fun k => (hfinput k).toLp (finput k)) atTop
      (𝓝 (hFt.toLp (fun x : Vec3 => F (x, t)))) := by
    have hProfile := hIn.2.comp hn₂
    have hToReal := (ENNReal.continuousAt_toReal
      (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hProfile
    have hDist (k : ℕ) : dist
        ((hfinput k).toLp (finput k))
        (hFt.toLp (fun x : Vec3 => F (x, t))) =
          (eLpNorm (fun x : Vec3 => fseq (n₁ (n₂ k)) (x, t) - F (x, t))
            (ENNReal.ofReal r) (volume : Measure Vec3)).toReal := by
      rw [Lp.dist_edist, Lp.edist_toLp_toLp]
      congr 1
    have hDistTendsto : Tendsto (fun k => dist
        ((hfinput k).toLp (finput k))
        (hFt.toLp (fun x : Vec3 => F (x, t)))) atTop (𝓝 0) := by
      simpa [hDist, finput, Function.comp_def] using hToReal
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      (hDistTendsto.eventually (gt_mem_nhds hε))
    exact ⟨N, fun k hk => hN k hk⟩
  have hGsliceMem (k : ℕ) : MemLp (goutput k)
      (ENNReal.ofReal r) (volume : Measure Vec3) :=
    (memLp_congr_ae (hGs k)).2
      (Lp.memLp (rieszPressureOperator r hr i j
        ((hfinput k).toLp (finput k))))
  have hOutputClassConv : Tendsto
      (fun k => (hGsliceMem k).toLp (goutput k)) atTop
      (𝓝 (hPsliceMem.toLp (fun x : Vec3 => Prep (x, t)))) := by
    have hProfile := hOut.2
    have hToReal := (ENNReal.continuousAt_toReal
      (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hProfile
    have hDist (k : ℕ) : dist ((hGsliceMem k).toLp (goutput k))
        (hPsliceMem.toLp (fun x : Vec3 => Prep (x, t))) =
          (eLpNorm (fun x : Vec3 => G (n₁ (n₂ k)) (x, t) - Prep (x, t))
            (ENNReal.ofReal r) (volume : Measure Vec3)).toReal := by
      rw [Lp.dist_edist, Lp.edist_toLp_toLp]
      congr 1
    have hDistTendsto : Tendsto (fun k => dist ((hGsliceMem k).toLp (goutput k))
        (hPsliceMem.toLp (fun x : Vec3 => Prep (x, t)))) atTop (𝓝 0) := by
      simpa [hDist, goutput, Function.comp_def] using hToReal
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      (hDistTendsto.eventually (gt_mem_nhds hε))
    exact ⟨N, fun k hk => hN k hk⟩
  have hSpatialClassConv : Tendsto
      (fun k => rieszPressureOperator r hr i j
        ((hfinput k).toLp (finput k))) atTop
      (𝓝 (rieszPressureOperator r hr i j
        (hFt.toLp (fun x : Vec3 => F (x, t))))) :=
    (rieszPressureOperator r hr i j).continuous.continuousAt.tendsto.comp
      hInputClassConv
  have hSeqEq (k : ℕ) : (hGsliceMem k).toLp (goutput k) =
      rieszPressureOperator r hr i j
        ((hfinput k).toLp (finput k)) := by
    apply Lp.ext
    filter_upwards [(hGs k), (hGsliceMem k).coeFn_toLp] with x hx₁ hx₂
    exact hx₂.trans hx₁
  have hOutputToSpatial := hSpatialClassConv.congr fun k => (hSeqEq k).symm
  have hLimitEq := tendsto_nhds_unique hOutputClassConv hOutputToSpatial
  have hFunEq : (fun x : Vec3 => Prep (x, t)) =ᵐ[volume]
      fun x => rieszPressureOperator r hr i j
        (hFt.toLp (fun y : Vec3 => F (y, t))) x := by
    have hCoeEq := Lp.ext_iff.mp hLimitEq
    filter_upwards [hPsliceMem.coeFn_toLp, hCoeEq] with x hx₁ hx₂
    exact hx₁.symm.trans hx₂
  exact ⟨hFt, hFunEq⟩

/-- Almost every time slice of the space-time pressure is the spatial pressure
of the corresponding tensor slice, used by lem:pressure-split. -/
theorem rieszPressureSpaceTime_slice_ae_eq
    (r : ℝ) (hr : 1 < r)
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ))) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      ∃ hFt : ∀ i j, MemLp (fun x : Vec3 => F i j (x, t))
          (ENNReal.ofReal r) (volume : Measure Vec3),
        (fun x : Vec3 => rieszPressureSpaceTime r hr F hF (x, t)) =ᵐ[volume]
          fun x => rieszPressureSlice r hr
            (fun i j => (hFt i j).toLp (fun y : Vec3 => F i j (y, t))) x := by
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  let Ftensor : RieszPressureSpaceTimeTensorLp r :=
    rieszPressureSpaceTimeTensorToLp r hr F hF
  let Sclass := rieszPressureSpaceTimeClass r hr Ftensor
  have hPressureMeas : Measurable (rieszPressureSpaceTime r hr F hF) :=
    rieszPressureSpaceTime_measurable r hr F hF
  have hPressureAE :
      rieszPressureSpaceTime r hr F hF =ᵐ[volume] (Sclass : Vec3 × ℝ → ℝ) := by
    simpa [Sclass, Ftensor, rieszPressureSpaceTime,
      rieszPressureSpaceTimeRepresentative] using
        ((Lp.aestronglyMeasurable Sclass).aemeasurable.ae_eq_mk.symm)
  let Q (i j : Fin 3) : Vec3 × ℝ → ℝ :=
    rieszPressureSpaceTimeComponentRepresentative r hr i j (Ftensor i j)
  have hQmeas (i j : Fin 3) : Measurable (Q i j) :=
    rieszPressureSpaceTimeComponentRepresentative_measurable r hr i j (Ftensor i j)
  have hQclass (i j : Fin 3) :
      Q i j =ᵐ[volume]
        (rieszPressureSpaceTimeComponent r hr i j (Ftensor i j) :
          Vec3 × ℝ → ℝ) := by
    exact (Lp.aestronglyMeasurable
      (rieszPressureSpaceTimeComponent r hr i j (Ftensor i j))).aemeasurable.ae_eq_mk.symm
  have hAllQ : ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      ∀ i j, Q i j z =
        rieszPressureSpaceTimeComponent r hr i j (Ftensor i j) z := by
    exact ae_all_iff.2 fun i => ae_all_iff.2 fun j => hQclass i j
  have hSumAE :
      (fun z : Vec3 × ℝ => ∑ i : Fin 3, ∑ j : Fin 3, Q i j z) =ᵐ[volume]
        (Sclass : Vec3 × ℝ → ℝ) := by
    have hClass := rieszPressure_double_sum_ae
      (volume : Measure (Vec3 × ℝ)) (ENNReal.ofReal r)
      (fun i j => rieszPressureSpaceTimeComponent r hr i j (Ftensor i j))
    filter_upwards [hAllQ, hClass] with z hz hClassPoint
    have hQsum : ∑ i : Fin 3, ∑ j : Fin 3, Q i j z =
        ∑ i : Fin 3, ∑ j : Fin 3,
          rieszPressureSpaceTimeComponent r hr i j (Ftensor i j) z := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hz i j
    exact hQsum.trans hClassPoint
  have hPressureSum :
      rieszPressureSpaceTime r hr F hF =ᵐ[volume]
        fun z : Vec3 × ℝ => ∑ i : Fin 3, ∑ j : Fin 3, Q i j z :=
    hPressureAE.trans hSumAE.symm
  have hSumMeas : Measurable
      (fun z : Vec3 × ℝ => ∑ i : Fin 3, ∑ j : Fin 3, Q i j z) := by
    fun_prop
  have hSumSlice := ae_time_sections_of_ae_eq hPressureMeas hSumMeas hPressureSum
  have hComponents :
      ∀ᵐ t ∂(volume : Measure ℝ), ∀ i j,
        ∃ hFt : MemLp (fun x : Vec3 => F i j (x, t))
            (ENNReal.ofReal r) (volume : Measure Vec3),
          (fun x : Vec3 => Q i j (x, t)) =ᵐ[volume]
            fun x => rieszPressureOperator r hr i j
              (hFt.toLp (fun y : Vec3 => F i j (y, t))) x := by
    exact ae_all_iff.2 fun i => ae_all_iff.2 fun j =>
      rieszPressureSpaceTimeComponent_slice_ae_eq r hr i j (hF i j)
  filter_upwards [hSumSlice, hComponents] with t hsum hcomp
  let hFt (i j : Fin 3) : MemLp (fun x : Vec3 => F i j (x, t))
      (ENNReal.ofReal r) (volume : Measure Vec3) :=
    Classical.choose (hcomp i j)
  have hComponentEq (i j : Fin 3) :
      (fun x : Vec3 => Q i j (x, t)) =ᵐ[volume]
        fun x => rieszPressureOperator r hr i j
          ((hFt i j).toLp (fun y : Vec3 => F i j (y, t))) x :=
    Classical.choose_spec (hcomp i j)
  have hSpatialSum :
      (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3, Q i j (x, t)) =ᵐ[volume]
        fun x => rieszPressureSlice r hr
          (fun i j => (hFt i j).toLp (fun y : Vec3 => F i j (y, t))) x := by
    have hClass := rieszPressure_double_sum_ae
      (volume : Measure Vec3) (ENNReal.ofReal r)
      (fun i j => rieszPressureOperator r hr i j
        ((hFt i j).toLp (fun y : Vec3 => F i j (y, t))))
    filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j => hComponentEq i j,
      hClass] with x hx hClassPoint
    have hQsum : ∑ i : Fin 3, ∑ j : Fin 3, Q i j (x, t) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          rieszPressureOperator r hr i j
            ((hFt i j).toLp (fun y : Vec3 => F i j (y, t))) x := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hx i j
    exact hQsum.trans hClassPoint
  refine ⟨hFt, ?_⟩
  filter_upwards [hsum, hSpatialSum] with x hxsum hxspatial
  exact hxsum.trans hxspatial

end CKN.Leray

end
