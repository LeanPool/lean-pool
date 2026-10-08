/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGlobalRepresentative
public import LeanPool.HighContrastHomogenization.Analytic.EuclideanAmbient
public import LeanPool.HighContrastHomogenization.Analytic.NormEquivalence
public import LeanPool.HighContrastHomogenization.Support.Sobolev.CubeEmbedding.Extension
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeCalderonZygmund.GlobalParentGeometry

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorGlobalH1sLoc

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Local weighted Sobolev membership of global corrector representatives

The global representatives of a projective local `H¹` carrier agree on every
exhaustion cube with an actual `H1Function`.  Convex smooth approximation on a
containing cube therefore supplies the ballwise approximation required by
`MemH1sLoc`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

private theorem tendsto_eLpNorm_one_of_tendsto_eLpNorm_two
    {d : ℕ} {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    {F : ℕ → Vec d → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) (volume.restrict U))
    (h : Tendsto (fun n => eLpNorm (F n) 2 (volume.restrict U))
      atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (F n) 1 (volume.restrict U))
      atTop (nhds 0) := by
  let q : ℝ := 1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal
  let M : ℝ≥0∞ := (volume.restrict U) Set.univ ^ q
  have hq : 0 ≤ q := by norm_num [q]
  have hM : M ≠ ⊤ := by
    exact (ENNReal.rpow_lt_top_of_nonneg hq
      (measure_lt_top (volume.restrict U) Set.univ).ne).ne
  have hbound : ∀ n,
      eLpNorm (F n) 1 (volume.restrict U) ≤
        eLpNorm (F n) 2 (volume.restrict U) * M := by
    intro n
    simpa only [M, q] using
      (eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (by norm_num : (1 : ENNReal) ≤ 2) (hF n))
  have hscaled := ENNReal.Tendsto.mul_const h (Or.inr hM)
  rw [zero_mul] at hscaled
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hscaled (fun _ => zero_le) hbound

private theorem eLpNorm_hilbert_single {α : Type*} [MeasurableSpace α]
    {d : ℕ} (i : Fin d) {μ : Measure α} {p : ℝ≥0∞} (f : α → ℝ)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => HilbertVec.ofVec (Pi.single i (f x))) p μ =
      eLpNorm f p μ := by
  let L : ℝ →L[ℝ] HilbertVec d :=
    (HilbertVec.ofVecL d).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)
  have hg : AEStronglyMeasurable
      (fun x => HilbertVec.ofVec (Pi.single i (f x))) μ :=
    L.continuous.comp_aestronglyMeasurable hf
  apply eLpNorm_congr_norm_ae hg hf
  exact ae_of_all μ fun x => by
    rw [show HilbertVec.ofVec (Pi.single i (f x)) = PiLp.single 2 i (f x) from rfl,
      PiLp.norm_single]

private theorem tendsto_eLpNorm_hilbertGradient_sub_convexApproxSmoothH1
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) :
    Tendsto
      (fun n => eLpNorm
        (hilbertifyVecField (fun x =>
          (H1Function.convexApproxSmoothH1 hU u x0 hr n).grad x - u.grad x))
        2 (volume.restrict U)) atTop (nhds 0) := by
  let psi : ℕ → H1Function U := fun n =>
    H1Function.convexApproxSmoothH1 hU u x0 hr n
  have hcoord : ∀ i : Fin d,
      Tendsto
        (fun n => eLpNorm (fun x => (psi n).grad x i - u.grad x i)
          2 (volume.restrict U)) atTop (nhds 0) := by
    intro i
    simpa only [psi] using
      tendsto_eLpNorm_grad_convexApproxSmoothH1 hU u hr hball i
  have hsum : Tendsto
      (fun n => ∑ i : Fin d,
        eLpNorm (fun x => (psi n).grad x i - u.grad x i)
          2 (volume.restrict U)) atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ fun i _ => hcoord i
  have hbound : ∀ n,
      eLpNorm
          (hilbertifyVecField (fun x => (psi n).grad x - u.grad x))
          2 (volume.restrict U) ≤
        ∑ i : Fin d,
          eLpNorm (fun x => (psi n).grad x i - u.grad x i)
            2 (volume.restrict U) := by
    intro n
    let singleField : Fin d → Vec d → HilbertVec d := fun i x =>
      HilbertVec.ofVec (Pi.single i ((psi n).grad x i - u.grad x i))
    have hfield :
        hilbertifyVecField (fun x => (psi n).grad x - u.grad x) =
          ∑ i : Fin d, singleField i := by
      funext x
      apply HilbertVec.ext
      intro j
      simp [hilbertifyVecField, singleField, HilbertVec.ofVec]
    rw [hfield]
    refine (eLpNorm_sum_le (by norm_num : (1 : ENNReal) ≤ 2)).trans_eq ?_
    apply Finset.sum_congr rfl
    intro i _
    exact eLpNorm_hilbert_single i _
      (((psi n).grad_memL2 i).aestronglyMeasurable.sub
        (u.grad_memL2 i).aestronglyMeasurable)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hsum (fun _ => zero_le) hbound

private theorem eLpNorm_two_sq_eq_lintegral_enorm
    {α E : Type*} [MeasurableSpace α] [ENorm E] [TopologicalSpace E]
    (μ : Measure α) (F : α → E) (hF : AEStronglyMeasurable F μ) :
    eLpNorm F 2 μ ^ (2 : ℕ) = ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hF]
  norm_num only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast (_ ^ (1 / (2 : ℝ))) 2,
    ← ENNReal.rpow_mul]
  norm_num

private theorem tendsto_h1NormSqOnUnweighted_of_tendsto_eLpNorm_two
    {d : ℕ} {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    {f : ℕ → Vec d → ℝ} {F : ℕ → Vec d → Vec d}
    (hf : ∀ n, AEStronglyMeasurable (f n) (volume.restrict U))
    (hf2 : Tendsto (fun n => eLpNorm (f n) 2 (volume.restrict U))
      atTop (nhds 0))
    (hF2 : Tendsto (fun n => eLpNorm (hilbertifyVecField (F n)) 2
      (volume.restrict U)) atTop (nhds 0)) :
    Tendsto (fun n => h1NormSqOnUnweighted U (f n) (F n))
      atTop (nhds 0) := by
  have hf1 : Tendsto (fun n => eLpNorm (f n) 1 (volume.restrict U))
      atTop (nhds 0) :=
    tendsto_eLpNorm_one_of_tendsto_eLpNorm_two hf hf2
  have hvalue : Tendsto
      (fun n => (∫⁻ x in U, ENNReal.ofReal |f n x| ∂volume) ^ 2)
      atTop (nhds 0) := by
    have hpow : Tendsto
        (fun n => eLpNorm (f n) 1 (volume.restrict U) ^ (2 : ℝ))
        atTop (nhds (0 ^ (2 : ℝ))) :=
      (ENNReal.continuous_rpow_const.tendsto 0).comp hf1
    norm_num at hpow
    have hpow' : Tendsto
        (fun n => eLpNorm (f n) 1 (volume.restrict U) ^ (2 : ℕ))
        atTop (nhds 0) := by
      simpa only [ENNReal.rpow_two] using hpow
    convert hpow' using 1
    funext n
    rw [eLpNorm_one_eq_lintegral_enorm (hf n)]
    congr 2
    funext x
    rw [← ofReal_norm]
    simp only [Real.norm_eq_abs]
  have hgradient : Tendsto
      (fun n => ∫⁻ x in U, ENNReal.ofReal (vecNormSq (F n x)) ∂volume)
      atTop (nhds 0) := by
    have hpow : Tendsto
        (fun n => eLpNorm (hilbertifyVecField (F n)) 2
          (volume.restrict U) ^ (2 : ℝ)) atTop (nhds (0 ^ (2 : ℝ))) :=
      (ENNReal.continuous_rpow_const.tendsto 0).comp hF2
    norm_num at hpow
    have hpow' : Tendsto
        (fun n => eLpNorm (hilbertifyVecField (F n)) 2
          (volume.restrict U) ^ (2 : ℕ)) atTop (nhds 0) := by
      simpa only [ENNReal.rpow_two] using hpow
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpow'
      (fun _ => zero_le) fun n => ?_
    by_cases hmeas :
        AEStronglyMeasurable (hilbertifyVecField (F n)) (volume.restrict U)
    swap
    · simp [eLpNorm_of_not_aestronglyMeasurable hmeas]
    refine le_of_eq ?_
    rw [eLpNorm_two_sq_eq_lintegral_enorm _ _ hmeas]
    apply lintegral_congr
    intro x
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg
      (norm_nonneg _) (by norm_num)]
    congr 1
    rw [Real.rpow_two, HilbertVec.norm_sq_eq_sum_sq,
      vecNormSq_eq_sum_sq]
    rfl
  simpa only [h1NormSqOnUnweighted, zero_add] using hvalue.add hgradient

/-- Smooth convex approximation converges to an `H1Function` in the exact
unweighted quantity used by the definition of `MemH1sLoc`. -/
theorem exists_contDiff_tendsto_h1NormSqOnUnweighted_sub
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) :
    ∃ w : ℕ → Vec d → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (w n)) ∧
      Tendsto
        (fun n => h1NormSqOnUnweighted U
          (fun x => w n x - u.toFun x)
          (fun x => smoothGrad (w n) x - u.grad x))
        atTop (nhds 0) := by
  let w : ℕ → Vec d → ℝ := fun n =>
    convexApproxSmoothRepresentative U (unitConvexApproxKernel (d := d)) u
      x0 r (unitConvexApproxScale n)
  refine ⟨w, ?_, ?_⟩
  · intro n
    have hscale : 0 < unitConvexApproxScale n := by
      dsimp [unitConvexApproxScale]
      positivity
    exact contDiff_convexApproxSmoothRepresentative
      hU.isOpen.measurableSet
      (isConvexApproxKernel_unitConvexApproxKernel (d := d))
      (by norm_num : (1 : ENNReal) ≤ 2) u.memL2 hr
      hscale
  · let _ : IsFiniteMeasure (volume.restrict U) := by
      simpa only using hU.isFiniteMeasure_restrict_volume
    apply tendsto_h1NormSqOnUnweighted_of_tendsto_eLpNorm_two
    · intro n
      exact ((H1Function.convexApproxSmoothH1 hU u x0 hr n).memL2.sub
        u.memL2).aestronglyMeasurable.congr
          (Eventually.of_forall fun x => by
            rw [H1Function.convexApproxSmoothH1_toFun]
            rfl)
    · simpa only [w, H1Function.convexApproxSmoothH1_toFun] using
        tendsto_eLpNorm_convexApproxSmoothH1 hU u hr hball
    · simpa only [w, smoothGrad, H1Function.convexApproxSmoothH1_grad] using!
        tendsto_eLpNorm_hilbertGradient_sub_convexApproxSmoothH1
          hU u hball hr

theorem exists_closedBall_zero_subset_localGradientCube
    {d : ℕ} {R : ℝ} (hR : 0 < R) :
    ∃ n : ℕ, Metric.closedBall (0 : Vec d) R ⊆ localGradientCube d n := by
  obtain ⟨m, hm⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3)).eventually_gt_atTop
      (4 * R)).exists
  have hm' : 4 * R < (3 : ℝ) ^ (m : ℤ) := by
    simpa only [zpow_natCast] using hm
  have hzero : (0 : Vec d) ∈ localGradientCube d m := by
    rw [localGradientCube, mem_openCubeSet_originCube_iff]
    intro i
    have hp : 0 < (3 : ℝ) ^ (m : ℤ) := by positivity
    constructor <;> dsimp only [Pi.zero_apply] <;> linarith only [hp]
  have hquarter : R ≤ cubeRadius (originCube d (m : ℤ)) / 2 := by
    dsimp [cubeRadius, cubeScaleFactor, originCube]
    linarith only [hm']
  refine ⟨m + 1, ?_⟩
  simpa only [localGradientCube, Nat.cast_add, Nat.cast_one] using
    CubeCalderonZygmund.closedBall_subset_openCubeSet_originCube_succ_of_mem
      hzero hR.le hquarter

theorem h1NormSqOnUnweighted_mono {d : ℕ} {V U : Set (Vec d)}
    (hVU : V ⊆ U) (u : Vec d → ℝ) (Du : Vec d → Vec d) :
    h1NormSqOnUnweighted V u Du ≤ h1NormSqOnUnweighted U u Du := by
  unfold h1NormSqOnUnweighted
  have hμ : volume.restrict V ≤ volume.restrict U :=
    Measure.restrict_mono_set volume hVU
  gcongr

theorem h1NormSqOnUnweighted_congr_ae {d : ℕ} {V : Set (Vec d)}
    {u v : Vec d → ℝ} {Du Dv : Vec d → Vec d}
    (hu : u =ᵐ[volume.restrict V] v)
    (hDu : Du =ᵐ[volume.restrict V] Dv) :
    h1NormSqOnUnweighted V u Du = h1NormSqOnUnweighted V v Dv := by
  unfold h1NormSqOnUnweighted
  congr 1
  · congr 1
    exact lintegral_congr_ae (hu.mono fun x hx => by simp only [hx])
  · exact lintegral_congr_ae (hDu.mono fun x hx => by simp only [hx])

end

end HighContrast
end HCPolySupport
