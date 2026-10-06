/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.Prod
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Trace Initial L3

The strong initial trace inherits an almost-every-time critical `L³` bound
(paper label `lem:pv-initial-l3`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


namespace ESS

private theorem exists_good_time_in_interval {T : ℝ}
    {s : Set ℝ} (hs : s ∈ ae (volume.restrict (Ioo 0 T)))
    {δ : ℝ} (hδ : 0 < δ) (hδT : δ ≤ T) :
    ∃ t, t ∈ Ioo 0 δ ∧ t ∈ s := by
  let μ : Measure ℝ := volume.restrict (Ioo 0 T)
  have hsubset : Ioo 0 δ ⊆ Ioo 0 T := by
    intro t ht
    exact ⟨ht.1, lt_of_lt_of_le ht.2 hδT⟩
  have hμinterval : μ (Ioo 0 δ) = volume (Ioo 0 δ) := by
    rw [Measure.restrict_apply measurableSet_Ioo]
    simp [inter_eq_left.mpr hsubset]
  have hpos : 0 < μ (Ioo 0 δ) := by
    rw [hμinterval, Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by simpa using hδ)
  have hsZero : μ sᶜ = 0 := mem_ae_iff.mp hs
  by_contra hEmpty
  have hsubsetNull : Ioo 0 δ ⊆ sᶜ := by
    intro t ht
    by_contra hts
    apply hEmpty
    exact ⟨t, ⟨ht, by simpa using hts⟩⟩
  have hzero : μ (Ioo 0 δ) = 0 := le_antisymm
    (measure_mono hsubsetNull |>.trans_eq hsZero) bot_le
  exact (ne_of_gt hpos) hzero

/-- The strong initial trace inherits an almost-every-time critical `L³` bound
(paper label `lem:pv-initial-l3`). -/
theorem lerayHopf_initialTrace_memLp_three
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    (M : ℝ≥0∞) (hM : M < ⊤)
    (hL3 : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal (3 : ℝ)) volume ≤ M) :
    MemLp a (ENNReal.ofReal (3 : ℝ)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (a x))
        (ENNReal.ofReal (3 : ℝ)) volume ≤ M := by
  rcases hLH with ⟨hT, hJ, huMeas, hDuMeas, hSliceTop, hJointTop,
    hWeakGrad, hDiv, hWeakCont, hMomentum, hEnergy, hTrace⟩
  have huMeasProd : AEStronglyMeasurable u
      ((volume.restrict (Set.univ : Set Vec3)).prod
        (volume.restrict (Ioo 0 T))) := by
    rw [Measure.prod_restrict Set.univ (Ioo 0 T)
      (μ := (volume : Measure Vec3)) (ν := (volume : Measure ℝ))]
    exact huMeas
  have hSlices : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      AEStronglyMeasurable (fun x : Vec3 => u (x, t)) volume := by
    filter_upwards [huMeasProd.prodMk_right] with t ht
    simpa [Measure.restrict_univ] using ht
  have hGood : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      AEStronglyMeasurable (fun x : Vec3 => u (x, t)) volume ∧
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
          (ENNReal.ofReal (3 : ℝ)) volume ≤ M := by
    filter_upwards [hSlices, hL3] with t htm htl3
    exact ⟨htm, htl3⟩
  let G : Set ℝ := {t | AEStronglyMeasurable (fun x : Vec3 => u (x, t)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal (3 : ℝ)) volume ≤ M}
  have hG : G ∈ ae (volume.restrict (Ioo 0 T)) := hGood
  let δ : ℕ → ℝ := fun n => min T (1 / (n + 1 : ℝ))
  have hδpos (n : ℕ) : 0 < δ n :=
    lt_min hT (one_div_pos.mpr (by positivity : (0 : ℝ) < n + 1))
  have hδT (n : ℕ) : δ n ≤ T := min_le_left _ _
  let ts : ℕ → ℝ := fun n => Classical.choose
    (exists_good_time_in_interval hG (hδpos n) (hδT n))
  have htsSpec (n : ℕ) : ts n ∈ Ioo 0 (δ n) ∧ ts n ∈ G :=
    Classical.choose_spec (exists_good_time_in_interval hG (hδpos n) (hδT n))
  have htsSmall (n : ℕ) : ts n < 1 / (n + 1 : ℝ) :=
    lt_of_lt_of_le (htsSpec n).1.2 (min_le_right _ _)
  have htsPos (n : ℕ) : 0 < ts n := (htsSpec n).1.1
  have htsZero : Tendsto ts atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat
    · exact Filter.Eventually.of_forall fun n => le_of_lt (htsPos n)
    · exact Filter.Eventually.of_forall fun n => le_of_lt (htsSmall n)
  have htsWithin : Tendsto ts atTop (nhdsWithin 0 (Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨htsZero, Filter.Eventually.of_forall fun n => htsPos n⟩
  have hGoodTime (n : ℕ) :
      AEStronglyMeasurable (fun x : Vec3 => u (x, ts n)) volume ∧
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, ts n)))
          (ENNReal.ofReal (3 : ℝ)) volume ≤ M := (htsSpec n).2
  have hTraceSeq : Tendsto
      (fun n : ℕ => ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, ts n) - a x)) ^ (2 : ℝ))
      atTop (nhds 0) := hTrace.comp htsWithin
  have hRoot : Tendsto
      (fun n : ℕ => (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, ts n) - a x)) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ)) atTop (nhds 0) := by
    have h := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto
      (0 : ℝ≥0∞) |>.comp hTraceSeq
    convert h using 1 <;> simp [Function.comp_def]
  have hScalarMeas (n : ℕ) : AEStronglyMeasurable
      (fun x : Vec3 => vec3EuclideanNorm (u (x, ts n) - a x)) volume :=
    continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      ((hGoodTime n).1.sub hJ.1.aestronglyMeasurable)
  have hScalarNormEq (n : ℕ) :
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, ts n) - a x)) 2 volume =
        (∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, ts n) - a x)) ^ (2 : ℝ)) ^
            (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num) (by norm_num) (hScalarMeas n)]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [] with x
    rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)]
    norm_num
  have hScalarTendsto : Tendsto
      (fun n : ℕ => eLpNorm
        (fun x : Vec3 => vec3EuclideanNorm (u (x, ts n) - a x)) 2 volume)
      atTop (nhds 0) := by
    have heq : (fun n : ℕ => eLpNorm
        (fun x : Vec3 => vec3EuclideanNorm (u (x, ts n) - a x)) 2 volume) =
        (fun n => (∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, ts n) - a x)) ^ (2 : ℝ)) ^
            (1 / 2 : ℝ)) := by
      funext n
      exact hScalarNormEq n
    rw [heq]
    exact hRoot
  have hVectorLeScalar (n : ℕ) :
      eLpNorm (fun x : Vec3 => u (x, ts n) - a x) 2 volume ≤
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, ts n) - a x)) 2 volume := by
    apply eLpNorm_mono_ae_real
      ((hGoodTime n).1.sub hJ.1.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x =>
      norm_le_vec3EuclideanNorm (u (x, ts n) - a x)
  have hVectorTendsto : Tendsto
      (fun n : ℕ => eLpNorm (fun x : Vec3 => u (x, ts n) - a x) 2 volume)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hScalarTendsto
      (Filter.Eventually.of_forall fun _ => bot_le)
      (Filter.Eventually.of_forall hVectorLeScalar)
  have hInMeasure : TendstoInMeasure volume
      (fun n : ℕ => fun x : Vec3 => u (x, ts n)) atTop a :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hVectorTendsto
  obtain ⟨ns, hns, hAE⟩ := hInMeasure.exists_seq_tendsto_ae'
  let f : ℕ → Vec3 → ℝ := fun n x => vec3EuclideanNorm (u (x, ts (ns n)))
  let g : Vec3 → ℝ := fun x => vec3EuclideanNorm (a x)
  have hBoundAll (n : ℕ) : eLpNorm (f n) (ENNReal.ofReal (3 : ℝ)) volume ≤ M :=
    (hGoodTime (ns n)).2
  have hfMeas (n : ℕ) : AEStronglyMeasurable (f n) volume :=
    continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      (hGoodTime (ns n)).1
  have hgMeas : AEStronglyMeasurable g volume :=
    continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      hJ.1.aestronglyMeasurable
  have hAE' : ∀ᵐ x ∂volume, Tendsto (fun n => f n x) atTop (nhds (g x)) := by
    filter_upwards [hAE] with x hx
    exact (continuous_vec3EuclideanNorm.continuousAt (x := a x)).tendsto.comp hx
  have hLimitBound : eLpNorm g (ENNReal.ofReal (3 : ℝ)) volume ≤ M :=
    Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hBoundAll)
      hfMeas hgMeas hAE'
  have hVecBound : eLpNorm a (ENNReal.ofReal (3 : ℝ)) volume ≤ M := by
    calc
      eLpNorm a (ENNReal.ofReal (3 : ℝ)) volume ≤ eLpNorm g
          (ENNReal.ofReal (3 : ℝ)) volume := by
        apply eLpNorm_mono_ae_real hJ.1.aestronglyMeasurable
        exact Filter.Eventually.of_forall fun x => norm_le_vec3EuclideanNorm (a x)
      _ ≤ M := hLimitBound
  exact ⟨memLp_iff.mpr (lt_of_le_of_lt hVecBound hM), hLimitBound⟩

end ESS
