/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedHessianLocal
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SmoothMax
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PositiveTestFunctional
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.UscWeightEventually
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.SmoothMeasureTests

/-!
# Bedford–Taylor convergence for decreasing smooth approximations

We prove, by induction on the number `q` of slots whose approximating
sequences are allowed to vary, that the mixed Monge–Ampère densities of
decreasing smooth plurisubharmonic approximations converge weakly on an open
set to a measure depending only on the limits, and that the same holds after
multiplying by a decreasing weight sequence.

This file fixes the notions used by the induction and proves its base case.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder ENNReal

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- Smooth with positive semidefinite complex Hessian on an open set. -/
def IsSmoothPsdOn (U : Opens (ComplexModel n)) (f : ComplexModel n → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f U ∧ ∀ z ∈ U, (complexHessian f z).PosSemidef

/-- A pointwise decreasing smooth PSD approximation of `u` on `U`, whose limit
is bounded below on compact subsets of `U`. -/
def IsDecApprox (U : Opens (ComplexModel n)) (u : ComplexModel n → ℝ)
    (F : ℕ → ComplexModel n → ℝ) : Prop :=
  (∀ k, IsSmoothPsdOn U (F k)) ∧ (∀ z ∈ U, Antitone fun k ↦ F k z) ∧
    (∀ z ∈ U, Tendsto (fun k ↦ F k z) atTop (𝓝 (u z))) ∧
    ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ U → BddBelow (u '' K)

theorem IsSmoothPsdOn.continuousOn_complexHessian {U : Opens (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f U) (j k : Fin n) :
    ContinuousOn (fun z ↦ complexHessian f z j k) U := by
  have hR (a b : ComplexModel n) : ContinuousOn (fun z ↦ realHessian f z a b) U := by
    have h2 : ContinuousOn (iteratedFDeriv ℝ 2 f) U :=
      ContinuousOn.continuousOn_iteratedFDeriv hf U.isOpen
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    change ContinuousOn (fun z ↦ iteratedFDeriv ℝ 2 f z ![a, b]) U
    exact (continuous_eval_const ![a, b]).comp_continuousOn h2
  unfold complexHessian
  have ha := Complex.continuous_ofReal.comp_continuousOn
    ((hR (coordinateVector j) (coordinateVector k)).add
      (hR (Complex.I • coordinateVector j) (Complex.I • coordinateVector k)))
  have hb := Complex.continuous_ofReal.comp_continuousOn
    ((hR (coordinateVector j) (Complex.I • coordinateVector k)).sub
      (hR (Complex.I • coordinateVector j) (coordinateVector k)))
  exact (ha.div_const 4).add ((continuousOn_const.mul hb).div_const 4)

theorem continuousOn_mixedDensity {U : Opens (ComplexModel n)}
    {f : Fin n → ComplexModel n → ℝ} (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U) :
    ContinuousOn (mixedDensity f) U := by
  have hmat (i : Fin n) : ContinuousOn (complexHessian (f i)) U :=
    continuousOn_pi.2 fun j ↦ continuousOn_pi.2 fun k ↦
      IsSmoothPsdOn.continuousOn_complexHessian (hf i) j k
  have hC : ContinuousOn (fun z ↦ mixedCoefficient fun i ↦ complexHessian (f i) z) U := by
    unfold mixedCoefficient
    refine continuousOn_finsetSum _ fun σ _ ↦ ?_
    have : ContinuousOn (fun z ↦ (Matrix.of fun j k ↦ complexHessian (f (σ j)) z j k)) U :=
      continuousOn_pi.2 fun j ↦ continuousOn_pi.2 fun k ↦
        IsSmoothPsdOn.continuousOn_complexHessian (hf (σ j)) j k
    exact continuous_id.matrix_det.comp_continuousOn this
  unfold mixedDensity
  exact (Complex.continuous_re.comp_continuousOn hC).div_const _

theorem mixedDensity_nonneg {f : Fin n → ComplexModel n → ℝ} {z : ComplexModel n}
    (hf : ∀ i, (complexHessian (f i) z).PosSemidef) : 0 ≤ mixedDensity f z :=
  div_nonneg (MixedMongeAmpere.mixedCoefficient_re_nonneg _ hf) (pow_nonneg Real.pi_pos.le n)

theorem mixedDensity_congr {f g : Fin n → ComplexModel n → ℝ} {z : ComplexModel n}
    (h : ∀ i, f i =ᶠ[𝓝 z] g i) : mixedDensity f z = mixedDensity g z := by
  simp only [mixedDensity, fun i ↦ MixedHessian.complexHessian_congr (h i)]

/-- The smooth mixed density measure on `U`, extended by zero. -/
def densityMeasure (U : Opens (ComplexModel n)) (f : Fin n → ComplexModel n → ℝ) :
    Measure (ComplexModel n) :=
  (volume.restrict (U : Set (ComplexModel n))).withDensity
    fun z ↦ ENNReal.ofReal (mixedDensity f z)

theorem densityMeasure_compl (U : Opens (ComplexModel n)) (f : Fin n → ComplexModel n → ℝ) :
    densityMeasure U f (U : Set (ComplexModel n))ᶜ = 0 := by
  rw [densityMeasure, withDensity_apply _ U.isOpen.measurableSet.compl,
    Measure.restrict_restrict U.isOpen.measurableSet.compl]
  simp

theorem densityMeasure_lt_top {U : Opens (ComplexModel n)} {f : Fin n → ComplexModel n → ℝ}
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U) {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKU : K ⊆ U) : densityMeasure U f K < ⊤ := by
  have hint : IntegrableOn (mixedDensity f) K :=
    ((continuousOn_mixedDensity hf).mono hKU).integrableOn_compact hK
  rw [densityMeasure, withDensity_apply _ hK.measurableSet,
    Measure.restrict_restrict_of_subset hKU]
  refine lt_of_le_of_lt (lintegral_mono fun z ↦ ?_) hint.2
  rw [Real.eNorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

theorem integral_densityMeasure {U : Opens (ComplexModel n)} {f : Fin n → ComplexModel n → ℝ}
    (hf : ∀ i, IsSmoothPsdOn U (f i)) {φ : ComplexModel n → ℝ} (hφU : tsupport φ ⊆ U) :
    ∫ z, φ z ∂(densityMeasure U f) = ∫ z, φ z * mixedDensity f z := by
  have hcont := continuousOn_mixedDensity fun i ↦ (hf i).1
  have hw : AEMeasurable (fun z ↦ ENNReal.ofReal (mixedDensity f z))
      (volume.restrict (U : Set (ComplexModel n))) :=
    (hcont.aemeasurable U.isOpen.measurableSet).ennreal_ofReal
  rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul₀ hw
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  have hzero : ∀ z ∉ (U : Set (ComplexModel n)), φ z * mixedDensity f z = 0 := fun z hz ↦ by
    simp [image_eq_zero_of_notMem_tsupport fun h ↦ hz (hφU h)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  refine setIntegral_congr_fun U.isOpen.measurableSet fun z hz ↦ ?_
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (mixedDensity_nonneg fun i ↦ (hf i).2 z hz), mul_comm]

/-- Weak convergence on `U` of the mixed densities of a family of sequences. -/
def TendstoMixed (U : Opens (ComplexModel n)) (F : Fin n → ℕ → ComplexModel n → ℝ)
    (μ : Measure (ComplexModel n)) : Prop :=
  ∀ φ : ComplexModel n → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
    Tendsto (fun k ↦ ∫ z, φ z * mixedDensity (fun i ↦ F i k) z) atTop (𝓝 (∫ z, φ z ∂μ))

/-- Weak convergence on `U` of the weighted mixed densities. -/
def TendstoMixedWeighted (U : Opens (ComplexModel n)) (F : Fin n → ℕ → ComplexModel n → ℝ)
    (G : ℕ → ComplexModel n → ℝ) (w : ComplexModel n → ℝ) (μ : Measure (ComplexModel n)) :
    Prop :=
  ∀ χ : ComplexModel n → ℝ, Continuous χ → HasCompactSupport χ → tsupport χ ⊆ U →
    Tendsto (fun k ↦ ∫ z, χ z * G k z * mixedDensity (fun i ↦ F i k) z) atTop
      (𝓝 (∫ z, χ z * w z ∂μ))

/-- Admissible families at level `q`: decreasing smooth PSD approximations of
the limits, constant in every slot of index at least `q`. -/
def IsAdmissible (q : ℕ) (U : Opens (ComplexModel n)) (u : Fin n → ComplexModel n → ℝ)
    (F : Fin n → ℕ → ComplexModel n → ℝ) : Prop :=
  (∀ i, IsDecApprox U (u i) (F i)) ∧ ∀ i : Fin n, q ≤ i.val → ∀ k, EqOn (F i k) (F i 0) U

/-- Unweighted convergence claim at level `q`. -/
def PClaim (n q : ℕ) : Prop :=
  ∀ (U : Opens (ComplexModel n)) (u : Fin n → ComplexModel n → ℝ),
    ∃ μ : Measure (ComplexModel n), μ (U : Set (ComplexModel n))ᶜ = 0 ∧
      (∀ K, IsCompact K → K ⊆ U → μ K < ⊤) ∧
      ∀ F, IsAdmissible q U u F → TendstoMixed U F μ

/-- Weighted convergence claim at level `q`, for any measure satisfying the
unweighted claim. -/
def WClaim (n q : ℕ) : Prop :=
  ∀ (U : Opens (ComplexModel n)) (u : Fin n → ComplexModel n → ℝ)
    (μ : Measure (ComplexModel n)), μ (U : Set (ComplexModel n))ᶜ = 0 →
      (∀ K, IsCompact K → K ⊆ U → μ K < ⊤) →
      (∀ F, IsAdmissible q U u F → TendstoMixed U F μ) →
      ∀ F, IsAdmissible q U u F → ∀ (w : ComplexModel n → ℝ) (G : ℕ → ComplexModel n → ℝ),
        IsDecApprox U w G → TendstoMixedWeighted U F G w μ

/-- **Base case.** With every slot constant, the mixed density is fixed and the
limit is the smooth density measure. -/
theorem pClaim_zero : PClaim n 0 := by
  classical
  intro U u
  by_cases hex : ∃ F, IsAdmissible 0 U u F
  · obtain ⟨F₀, hF₀⟩ := hex
    refine ⟨densityMeasure U (fun i ↦ F₀ i 0), densityMeasure_compl _ _,
      fun K hK hKU ↦ densityMeasure_lt_top (fun i ↦ ((hF₀.1 i).1 0).1) hK hKU, ?_⟩
    intro F hF φ hφ hφc hφU
    -- on `U` every slot equals its limit, hence the corresponding slot of `F₀`
    have hlim (G : Fin n → ℕ → ComplexModel n → ℝ) (hG : IsAdmissible 0 U u G) (i : Fin n) :
        EqOn (G i 0) (u i) U := fun z hz ↦ by
      have h := (hG.1 i).2.2.1 z hz
      have hc : (fun k ↦ G i k z) = fun _ ↦ G i 0 z :=
        funext fun k ↦ hG.2 i (Nat.zero_le _) k hz
      rw [hc] at h
      exact tendsto_nhds_unique tendsto_const_nhds h
    have hdens (k : ℕ) (z : ComplexModel n) (hz : z ∈ U) :
        mixedDensity (fun i ↦ F i k) z = mixedDensity (fun i ↦ F₀ i 0) z := by
      refine mixedDensity_congr fun i ↦ ?_
      filter_upwards [U.isOpen.mem_nhds hz] with y hy
      rw [hF.2 i (Nat.zero_le _) k hy, hlim F hF i hy, hlim F₀ hF₀ i hy]
    have hconst : (fun k ↦ ∫ z, φ z * mixedDensity (fun i ↦ F i k) z) =
        fun _ ↦ ∫ z, φ z * mixedDensity (fun i ↦ F₀ i 0) z := by
      funext k
      congr 1
      funext z
      by_cases hz : z ∈ U
      · rw [hdens k z hz]
      · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hz (hφU h)]
    rw [hconst, integral_densityMeasure (fun i ↦ (hF₀.1 i).1 0) hφU]
    exact tendsto_const_nhds
  · exact ⟨0, by simp, fun _ _ _ ↦ by simp, fun F hF ↦ absurd ⟨F, hF⟩ hex⟩

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
