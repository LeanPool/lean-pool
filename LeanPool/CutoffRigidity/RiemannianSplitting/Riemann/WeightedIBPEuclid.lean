/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # Euclidean divergence theorem for compactly supported C¹ fields -/

@[expose] public section
open MeasureTheory Set
open scoped Topology

namespace CutoffRigidity

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem integral_fderiv_apply_eq_zero {h : F → ℝ} (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h)
    (w : F) : ∫ z, fderiv ℝ h z w = 0 := by
  have hcont : Continuous h := hh.continuous
  have hd : Continuous (fun z => fderiv ℝ h z w) :=
    (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdc : HasCompactSupport (fun z => fderiv ℝ h z w) := by
    have := hc.fderiv (𝕜 := ℝ)
    exact this.comp_left (g := fun L : F →L[ℝ] ℝ => L w) (by simp)
  have hhInt := hd.integrable_of_hasCompactSupport (μ := volume) hdc
  have hInt := hcont.integrable_of_hasCompactSupport (μ := volume) hc
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := h)
    (g := fun _ : F => (1 : ℝ)) (v := w)
    (by simpa using hhInt) (by simp) (by simpa using hInt)
    (fun _ _ => hh.differentiable one_ne_zero _) (fun _ _ => differentiableAt_const _)
  simpa using this

theorem integral_trace_fderiv_eq_zero {H : F → F} (hH : ContDiff ℝ 1 H) (hc : HasCompactSupport H) :
    ∫ z, LinearMap.trace ℝ F (fderiv ℝ H z).toLinearMap = 0 := by
  let b := stdOrthonormalBasis ℝ F
  have hterm : ∀ i, ∫ z, inner ℝ (b i) (fderiv ℝ H z (b i)) = 0 := by
    intro i
    have hh : ContDiff ℝ 1 (fun z => inner ℝ (b i) (H z)) :=
      contDiff_const.inner ℝ hH
    have hcs : HasCompactSupport (fun z => inner ℝ (b i) (H z)) :=
      hc.comp_left (g := fun w : F => inner ℝ (b i) w) (by simp)
    have := integral_fderiv_apply_eq_zero hh hcs (b i)
    rw [← this]
    congr 1
    funext z
    have hd : HasFDerivAt (fun z => inner ℝ (b i) (H z))
        ((innerSL ℝ (b i)).comp (fderiv ℝ H z)) z :=
      (innerSL ℝ (b i)).hasFDerivAt.comp z ((hH.differentiable one_ne_zero z).hasFDerivAt)
    rw [hd.fderiv]
    rfl
  have hint : ∀ i, Integrable (fun z => inner ℝ (b i) (fderiv ℝ H z (b i))) := by
    intro i
    have hcont : Continuous (fun z => inner ℝ (b i) (fderiv ℝ H z (b i))) :=
      continuous_const.inner ((hH.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    have hcs : HasCompactSupport (fun z => inner ℝ (b i) (fderiv ℝ H z (b i))) :=
      ((hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : F →L[ℝ] F => inner ℝ (b i) (L (b i)))
        (by simp))
    exact hcont.integrable_of_hasCompactSupport (μ := volume) hcs
  simp_rw [LinearMap.trace_eq_sum_inner _ b, ContinuousLinearMap.coe_coe]
  rw [integral_finsetSum _ (fun i _ => hint i)]
  exact Finset.sum_eq_zero fun i _ => hterm i

/-- The trace of a continuous linear endomorphism, as a continuous linear functional. -/
noncomputable def traceCLM : (F →L[ℝ] F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((LinearMap.trace ℝ F).comp (ContinuousLinearMap.coeLM ℝ))

omit [MeasurableSpace F] [BorelSpace F] in
theorem traceCLM_apply (L : F →L[ℝ] F) : traceCLM L = LinearMap.trace ℝ F L.toLinearMap := rfl

/-- Integrability of a function continuous on an open `T` and vanishing on `T \ K`, `K ⊆ T`
compact. -/
theorem integrableOn_of_vanishing {T K : Set F} {f : F → ℝ} (hT : MeasurableSet T)
    (hK : IsCompact K) (hKT : K ⊆ T) (hf : ContinuousOn f T) (h0 : ∀ z ∈ T, z ∉ K → f z = 0) :
    IntegrableOn f T := by
  have h1 : IntegrableOn f K := (hf.mono hKT).integrableOn_compact hK
  have h2 : IntegrableOn f (T \ K) := by
    refine (integrableOn_zero (μ := volume)).congr_fun (fun z hz => (h0 z hz.1 hz.2).symm)
      (hT.diff hK.measurableSet)
  have := h1.union h2
  rwa [union_sdiff_cancel hKT] at this

/-- **Divergence theorem in a chart**: for a `C¹` field `ρ Yc` and a `C¹` function `ũ`
supported (inside the open set `T`) in the compact `K ⊆ T`,
`∫_T ρ dũ(Yc) + ũ (dρ(Yc) + ρ tr dYc) = 0`. -/
theorem chart_divergence_zero {T K : Set F} {u ρ : F → ℝ} {Y : F → F}
    (hT : IsOpen T) (hK : IsCompact K) (hKT : K ⊆ T)
    (hu : ContDiffOn ℝ 1 u T) (hρ : ContDiffOn ℝ 1 ρ T) (hY : ContDiffOn ℝ 1 Y T)
    (hvan : ∀ z ∈ T, z ∉ K → u =ᶠ[nhds z] fun _ => 0) :
    IntegrableOn (fun z => ρ z * fderiv ℝ u z (Y z)) T ∧
    IntegrableOn (fun z => u z * (fderiv ℝ ρ z (Y z) +
        ρ z * LinearMap.trace ℝ F (fderiv ℝ Y z).toLinearMap)) T ∧
    (∫ z in T, ρ z * fderiv ℝ u z (Y z)) +
      ∫ z in T, u z * (fderiv ℝ ρ z (Y z) +
        ρ z * LinearMap.trace ℝ F (fderiv ℝ Y z).toLinearMap) = 0 := by
  have hTm : MeasurableSet T := hT.measurableSet
  have hdu : ContinuousOn (fun z => fderiv ℝ u z) T := hu.continuousOn_fderiv_of_isOpen hT le_rfl
  have hdρ : ContinuousOn (fun z => fderiv ℝ ρ z) T := hρ.continuousOn_fderiv_of_isOpen hT le_rfl
  have hdY : ContinuousOn (fun z => fderiv ℝ Y z) T := hY.continuousOn_fderiv_of_isOpen hT le_rfl
  have hAc : ContinuousOn (fun z => ρ z * fderiv ℝ u z (Y z)) T :=
    hρ.continuousOn.mul (hdu.clm_apply hY.continuousOn)
  have hBc : ContinuousOn (fun z => u z * (fderiv ℝ ρ z (Y z) +
      ρ z * LinearMap.trace ℝ F (fderiv ℝ Y z).toLinearMap)) T :=
    hu.continuousOn.mul ((hdρ.clm_apply hY.continuousOn).add
      (hρ.continuousOn.mul (traceCLM.continuous.comp_continuousOn hdY)))
  have hA0 : ∀ z ∈ T, z ∉ K → ρ z * fderiv ℝ u z (Y z) = 0 := by
    intro z hz hzK
    have : fderiv ℝ u z = 0 := by
      rw [(hvan z hz hzK).fderiv_eq]; simp
    simp [this]
  have hB0 : ∀ z ∈ T, z ∉ K → u z * (fderiv ℝ ρ z (Y z) +
      ρ z * LinearMap.trace ℝ F (fderiv ℝ Y z).toLinearMap) = 0 := by
    intro z hz hzK
    simp [(hvan z hz hzK).self_of_nhds]
  have hAi := integrableOn_of_vanishing hTm hK hKT hAc hA0
  have hBi := integrableOn_of_vanishing hTm hK hKT hBc hB0
  refine ⟨hAi, hBi, ?_⟩
  rw [← integral_add hAi hBi]
  set Hfun : F → F := fun z => u z • (ρ z • Y z) with hHfun
  set Hext : F → F := T.indicator Hfun with hHext
  have hHext0 : ∀ z, z ∉ K → Hext z = 0 := by
    intro z hzK
    by_cases hzT : z ∈ T
    · have := (hvan z hzT hzK).self_of_nhds
      simp [hHext, indicator_of_mem hzT, hHfun, this]
    · simp [hHext, indicator_of_notMem hzT]
  have hHextEv : ∀ z ∈ T, Hext =ᶠ[nhds z] Hfun := fun z hz => by
    filter_upwards [hT.mem_nhds hz] with w hw
    simp [hHext, indicator_of_mem hw]
  have hHextEv0 : ∀ z, z ∉ K → Hext =ᶠ[nhds z] fun _ => 0 := fun z hz => by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz] with w hw
    exact hHext0 w hw
  have hHfunCD : ∀ z ∈ T, ContDiffAt ℝ 1 Hfun z := fun z hz =>
    (hu.contDiffAt (hT.mem_nhds hz)).smul
      ((hρ.contDiffAt (hT.mem_nhds hz)).smul (hY.contDiffAt (hT.mem_nhds hz)))
  have hCD : ContDiff ℝ 1 Hext := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ T
    · exact (hHfunCD z hz).congr_of_eventuallyEq (hHextEv z hz)
    · exact contDiffAt_const.congr_of_eventuallyEq (hHextEv0 z (fun h => hz (hKT h)))
  have hcs : HasCompactSupport Hext := HasCompactSupport.intro hK hHext0
  have h0 := integral_trace_fderiv_eq_zero hCD hcs
  have hform : ∀ z ∈ T, LinearMap.trace ℝ F (fderiv ℝ Hext z).toLinearMap =
      ρ z * fderiv ℝ u z (Y z) + u z * (fderiv ℝ ρ z (Y z) +
        ρ z * LinearMap.trace ℝ F (fderiv ℝ Y z).toLinearMap) := by
    intro z hz
    have hn := hT.mem_nhds hz
    have hu' := (hu.contDiffAt hn).differentiableAt one_ne_zero
    have hρ' := (hρ.contDiffAt hn).differentiableAt one_ne_zero
    have hY' := (hY.contDiffAt hn).differentiableAt one_ne_zero
    have hW := hρ'.hasFDerivAt.smul hY'.hasFDerivAt
    have hH := hu'.hasFDerivAt.smul hW
    have hfd : fderiv ℝ Hfun z = _ := hH.fderiv
    rw [(hHextEv z hz).fderiv_eq, hfd]
    rw [← traceCLM_apply]
    simp only [map_add, map_smul, smul_eq_mul]
    have e1 : traceCLM ((fderiv ℝ u z).smulRight ((ρ • Y) z)) = fderiv ℝ u z ((ρ • Y) z) := by
      rw [traceCLM_apply]; exact LinearMap.trace_smulRight (fderiv ℝ u z).toLinearMap _
    have e2 : traceCLM ((fderiv ℝ ρ z).smulRight (Y z)) = fderiv ℝ ρ z (Y z) := by
      rw [traceCLM_apply]; exact LinearMap.trace_smulRight (fderiv ℝ ρ z).toLinearMap _
    rw [e1, e2, traceCLM_apply]
    have e3 : (fderiv ℝ u z) ((ρ • Y) z) = ρ z * (fderiv ℝ u z) (Y z) := by
      simp
    rw [e3]
    ring
  have hout : ∀ z, z ∉ T → LinearMap.trace ℝ F (fderiv ℝ Hext z).toLinearMap = 0 := by
    intro z hz
    rw [(hHextEv0 z (fun h => hz (hKT h))).fderiv_eq]
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout] at h0
  rw [← h0]
  exact setIntegral_congr_fun hTm (fun z hz => (hform z hz).symm)

end CutoffRigidity
