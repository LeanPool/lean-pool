/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierCoordinateL2Bridge
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierHeatDivergence
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Fourier orthogonality of smooth solenoidal fields

Compact smooth divergence-free approximants to J data have Fourier
transforms orthogonal to frequency, the input condition for heat preservation.
-/

public section

open MeasureTheory Filter
open scoped ENNReal FourierTransform SchwartzMap ComplexInnerProductSpace Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

@[expose]
def coordinateEquiv : L2Vec3 ≃L[ℝ] Vec3 :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)

@[expose]
def coordinateToHilbertValueOrth : Vec3 →L[ℝ] L2Vec3 :=
  coordinateEquiv.symm.toContinuousLinearMap

@[expose]
def coordinateBasis (i : Fin 3) : L2Vec3 :=
  WithLp.toLp 2 (CKN.basisVec i)

@[expose]
def complexCoordinateValue : Vec3 →L[ℝ] ComplexVec3 :=
  complexifyValue.comp coordinateToHilbertValueOrth

@[expose]
def solenoidalSchwartz (a : Vec3 → Vec3)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hcompact : HasCompactSupport a) :
    SchwartzMap L2Vec3 ComplexVec3 :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ coordinateEquiv
      (hcompact.toSchwartzMap ha)).postcompCLM complexCoordinateValue

@[expose]
def divergenceTraceLinear :
    (L2Vec3 →L[ℝ] ComplexVec3) →ₗ[ℂ] ℂ where
  toFun D := ∑ i : Fin 3, D (coordinateBasis i) i
  map_add' D E := by simp [Finset.sum_add_distrib]
  map_smul' c D := by simp [Finset.mul_sum]

theorem divergenceTrace_norm_bound
    (D : L2Vec3 →L[ℝ] ComplexVec3) :
    ‖divergenceTraceLinear D‖ ≤ 3 * ‖D‖ := by
  calc
    ‖∑ i : Fin 3, D (coordinateBasis i) i‖ ≤
        ∑ i : Fin 3, ‖D (coordinateBasis i) i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖D‖ := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ‖D (coordinateBasis i) i‖ ≤ ‖D (coordinateBasis i)‖ :=
          PiLp.norm_apply_le _ _
        _ ≤ ‖D‖ * ‖coordinateBasis i‖ := D.le_opNorm _
        _ = ‖D‖ := by simp [coordinateBasis, CKN.basisVec]
    _ = 3 * ‖D‖ := by simp

@[expose]
def divergenceTrace : (L2Vec3 →L[ℝ] ComplexVec3) →L[ℂ] ℂ :=
  divergenceTraceLinear.mkContinuous 3 divergenceTrace_norm_bound

@[expose]
def schwartzDivergence (f : SchwartzMap L2Vec3 ComplexVec3) :
    SchwartzMap L2Vec3 ℂ :=
  (SchwartzMap.fderivCLM ℂ L2Vec3 ComplexVec3 f).postcompCLM divergenceTrace

private theorem schwartzDivergence_fourier
    (f : SchwartzMap L2Vec3 ComplexVec3) (ξ : L2Vec3) :
    𝓕 (schwartzDivergence f) ξ =
      (2 * Real.pi * Complex.I) *
        inner ℂ (complexifyFrequency ξ) (𝓕 f ξ) := by
  have hpost := fourier_postcompCLM divergenceTrace
    (SchwartzMap.fderivCLM ℂ L2Vec3 ComplexVec3 f)
  rw [schwartzDivergence, hpost, SchwartzMap.fourier_fderivCLM_eq]
  change (∑ i : Fin 3,
      ((2 * Real.pi * Complex.I) •
        ((innerSL ℝ) ξ).smulRight (𝓕 f ξ)) (coordinateBasis i) i) = _
  have hterm (i : Fin 3) :
      ((2 * Real.pi * Complex.I) •
        ((innerSL ℝ) ξ).smulRight (𝓕 f ξ)) (coordinateBasis i) i =
        (2 * Real.pi * Complex.I) * (ξ i : ℂ) * (𝓕 f ξ) i := by
    simp [coordinateBasis, PiLp.inner_apply, CKN.basisVec]
    ring
  simp_rw [hterm]
  have hsum : (∑ i : Fin 3, ξ i * (𝓕 f ξ) i) =
      inner ℂ (complexifyFrequency ξ) (𝓕 f ξ) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    simp [complexifyFrequency]
    ring
  calc
    ∑ i : Fin 3, (2 * Real.pi * Complex.I) * (ξ i : ℂ) * (𝓕 f ξ) i =
        (2 * Real.pi * Complex.I) *
          ∑ i : Fin 3, (ξ i : ℂ) * (𝓕 f ξ) i := by
            calc
              _ = ∑ i : Fin 3,
                  (2 * Real.pi * Complex.I) *
                    ((ξ i : ℂ) * (𝓕 f ξ) i) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
              _ = _ := by rw [← Finset.mul_sum]
    _ = (2 * Real.pi * Complex.I) *
          inner ℂ (complexifyFrequency ξ) (𝓕 f ξ) := by rw [← hsum]

private theorem solenoidalSchwartz_fderiv
    (a : Vec3 → Vec3) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hcompact : HasCompactSupport a) (x : L2Vec3) :
    fderiv ℝ (solenoidalSchwartz a ha hcompact) x =
      complexCoordinateValue.comp
        ((fderiv ℝ a (coordinateEquiv x)).comp
          (coordinateEquiv : L2Vec3 →L[ℝ] Vec3)) := by
  have hsourceEq : (hcompact.toSchwartzMap ha : Vec3 → Vec3) = a := rfl
  have hsource : ContDiff ℝ (⊤ : ℕ∞) (hcompact.toSchwartzMap ha) := by
    change ContDiff ℝ (⊤ : ℕ∞) a
    exact ha
  change fderiv ℝ
      (complexCoordinateValue ∘
        ((hcompact.toSchwartzMap ha) ∘ coordinateEquiv)) x = _
  rw [fderiv_comp (x := x) complexCoordinateValue.differentiableAt
    ((hsource.comp coordinateEquiv.contDiff).differentiable (by simp)).differentiableAt]
  rw [complexCoordinateValue.hasFDerivAt.fderiv]
  rw [fderiv_comp (x := x)
    (hsource.differentiable (by simp)).differentiableAt
    coordinateEquiv.differentiableAt]
  rw [coordinateEquiv.hasFDerivAt.fderiv]
  rw [hsourceEq]

private theorem fderiv_coordinate_component
    (a : Vec3 → Vec3) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (x v : Vec3) (i : Fin 3) :
    (fderiv ℝ a x v) i =
      (fderiv ℝ (fun y : Vec3 => a y i) x) v := by
  have hcomp := fderiv_comp (x := x)
    (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).differentiableAt
    (ha.differentiable (by simp)).differentiableAt
  have hv := congrArg (fun D : Vec3 →L[ℝ] ℝ => D v) hcomp
  rw [ContinuousLinearMap.fderiv] at hv
  change (fderiv ℝ (fun y : Vec3 => a y i) x) v =
    (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ) (fderiv ℝ a x v) at hv
  simpa only [ContinuousLinearMap.proj_apply] using hv.symm

/-- Every compact smooth divergence-free vector field has a Fourier
transform orthogonal to frequency. -/
theorem compactSolenoidal_fourierOrthogonal
    (a : Vec3 → Vec3) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hcompact : HasCompactSupport a)
    (hdiv : ∀ x, ∑ i : Fin 3, CKN.spatialDeriv (fun y => a y i) i x = 0) :
    ∀ ξ : L2Vec3,
      inner ℂ (complexifyFrequency ξ) (𝓕 (solenoidalSchwartz a ha hcompact) ξ) = 0 := by
  intro ξ
  have hdivS : schwartzDivergence (solenoidalSchwartz a ha hcompact) = 0 := by
    ext x
    change divergenceTrace
      ((fderiv ℝ (solenoidalSchwartz a ha hcompact) x)) = 0
    rw [solenoidalSchwartz_fderiv]
    simp only [divergenceTrace, LinearMap.mkContinuous_apply, divergenceTraceLinear]
    change (∑ i : Fin 3,
      ((complexCoordinateValue.comp
        ((fderiv ℝ a (coordinateEquiv x)).comp
          (coordinateEquiv : L2Vec3 →L[ℝ] Vec3))) (coordinateBasis i)) i) = 0
    have htrace :
        (∑ i : Fin 3,
          (complexCoordinateValue.comp
            ((fderiv ℝ a (coordinateEquiv x)).comp
              (coordinateEquiv : L2Vec3 →L[ℝ] Vec3)))
            (coordinateBasis i) i) =
          (∑ i : Fin 3, CKN.spatialDeriv (fun y => a y i) i
            (coordinateEquiv x) : ℂ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hbasis : (coordinateEquiv : L2Vec3 →L[ℝ] Vec3)
          (coordinateBasis i) = CKN.basisVec i := by
        ext j
        simp [coordinateEquiv, coordinateBasis, CKN.basisVec, Pi.single_apply]
      simp only [ContinuousLinearMap.comp_apply, complexCoordinateValue,
        coordinateToHilbertValueOrth]
      rw [hbasis]
      simp only [complexifyValue, complexifyValueLinear, coordinateEquiv,
        ContinuousLinearEquiv.coe_coe, PiLp.continuousLinearEquiv_symm_apply,
        LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
        complexifyFrequency, spatialDeriv, Complex.ofReal_inj]
      exact fderiv_coordinate_component a ha (coordinateEquiv x)
        (CKN.basisVec i) i
    rw [htrace]
    exact_mod_cast hdiv (coordinateEquiv x)
  have hzero := congrArg (fun g : SchwartzMap L2Vec3 ℂ => 𝓕 g ξ) hdivS
  rw [schwartzDivergence_fourier] at hzero
  have hcoef : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    · exact Complex.I_ne_zero
  have hzero' : (2 * Real.pi * Complex.I) *
      inner ℂ (complexifyFrequency ξ) (𝓕 (solenoidalSchwartz a ha hcompact) ξ) = 0 := by
    simpa using hzero
  exact (mul_eq_zero.mp hzero').resolve_left hcoef

private theorem realVectorL2OfCoordinateLp_eq_function
    (a : Vec3 → Vec3) (ha : MemLp a 2 volume) :
    realVectorL2OfCoordinateLp (ha.toLp a) =
      realVectorL2OfCoordinateFunction a ha := by
  apply realVectorL2Representative_injective_ae
  have h₁ := realVectorL2OfCoordinateLp_rep (ha.toLp a)
  have h₂ := realVectorL2OfCoordinateFunction_rep a ha
  exact h₁.trans (ha.coeFn_toLp.trans h₂.symm)

private theorem compactSolenoidal_complexLp_eq
    (a : Vec3 → Vec3) (ha : MemLp a 2 volume)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) a) (hcompact : HasCompactSupport a) :
    complexifyVectorL2 (realVectorL2OfCoordinateFunction a ha) =
      (solenoidalSchwartz a hsmooth hcompact).toLp 2 volume := by
  apply Lp.ext
  have hu : ∀ᵐ x : L2Vec3 ∂volume,
      realVectorL2OfCoordinateFunction a ha x =
        coordinateToHilbertValueOrth (a (coordinateEquiv x)) := by
    have hrep := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
      (realVectorL2OfCoordinateFunction_rep a ha)
    filter_upwards [hrep] with x hx
    have hx' : coordinateEquiv
        (realVectorL2OfCoordinateFunction a ha x) = a (coordinateEquiv x) := by
      change realVectorL2Representative (realVectorL2OfCoordinateFunction a ha)
        (WithLp.ofLp x) = a (WithLp.ofLp x) at hx
      convert hx using 1 <;> rfl
    apply coordinateEquiv.injective
    simpa [coordinateToHilbertValueOrth] using hx'
  have hmap := ContinuousLinearMap.coeFn_compLpL
    (L := complexifyValue) (p := 2) (μ := volume)
      (realVectorL2OfCoordinateFunction a ha)
  have hschwartz := (solenoidalSchwartz a hsmooth hcompact).memLp 2 volume
  have htoLp : (solenoidalSchwartz a hsmooth hcompact).toLp 2 volume =
      hschwartz.toLp (solenoidalSchwartz a hsmooth hcompact) := by
    apply Lp.ext
    filter_upwards [] with x
    rfl
  filter_upwards [hmap, hu, hschwartz.coeFn_toLp] with x hmapx hux hsx
  change complexifyValue.compLpL 2 volume
      (realVectorL2OfCoordinateFunction a ha) x = _
  rw [hmapx, hux]
  calc
    complexifyValue (coordinateToHilbertValueOrth (a (coordinateEquiv x))) =
        solenoidalSchwartz a hsmooth hcompact x := by
          simp [solenoidalSchwartz, complexCoordinateValue,
            coordinateToHilbertValueOrth, coordinateEquiv, complexifyValue,
            complexifyValueLinear, complexifyFrequency]
    _ = hschwartz.toLp (solenoidalSchwartz a hsmooth hcompact) x := hsx.symm
    _ = (solenoidalSchwartz a hsmooth hcompact).toLp 2 volume x := by
          rw [htoLp.symm]

private theorem compactSolenoidal_transform_ae
    (a : Vec3 → Vec3) (ha : MemLp a 2 volume)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) a) (hcompact : HasCompactSupport a)
    (hdiv : ∀ x, ∑ i : Fin 3,
      CKN.spatialDeriv (fun y => a y i) i x = 0) :
    ∀ᵐ ξ ∂volume,
      inner ℂ (complexifyFrequency ξ)
        ((MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3)
          (complexifyVectorL2 (realVectorL2OfCoordinateFunction a ha)) ξ) = 0 := by
  let g := solenoidalSchwartz a hsmooth hcompact
  have hF :
      (MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3)
          (complexifyVectorL2 (realVectorL2OfCoordinateFunction a ha)) =
        (𝓕 g).toLp 2 volume := by
    rw [compactSolenoidal_complexLp_eq a ha hsmooth hcompact]
    exact SchwartzMap.toLp_fourier_eq g
  have hFae : ∀ᵐ ξ ∂volume,
      (MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3)
          (complexifyVectorL2 (realVectorL2OfCoordinateFunction a ha)) ξ =
        𝓕 g ξ := by
    rw [hF]
    exact (𝓕 g).memLp 2 volume |>.coeFn_toLp
  filter_upwards [hFae] with ξ hξ
  rw [hξ]
  exact compactSolenoidal_fourierOrthogonal a hsmooth hcompact hdiv ξ

private theorem realVectorL2Representative_memLp
    (f : RealVectorL2) : MemLp (realVectorL2Representative f) 2 volume := by
  have h := (Lp.memLp f).comp_measurePreserving vec3ToL2Vec3_measurePreserving
  have hcomp : MemLp (fun x : Vec3 =>
      (coordinateEquiv : L2Vec3 →L[ℝ] Vec3) (f (WithLp.toLp 2 x))) 2 volume :=
    h.continuousLinearMap_comp (coordinateEquiv : L2Vec3 →L[ℝ] Vec3)
  have heq : (fun x : Vec3 =>
      (coordinateEquiv : L2Vec3 →L[ℝ] Vec3) (f (WithLp.toLp 2 x))) =
      realVectorL2Representative f := by
    funext x
    ext i
    rfl
  exact hcomp.ae_eq (Filter.Eventually.of_forall (fun x => congrFun heq x))

private theorem realVectorL2_coordinateApprox_tendsto
    (a : Vec3 → Vec3) (ha : MemLp a 2 volume)
    (aSeq : ℕ → Vec3 → Vec3) (hMem : ∀ n, MemLp (aSeq n) 2 volume)
    (hApprox : Tendsto (fun n => eLpNorm (aSeq n - a) 2 volume)
      atTop (𝓝 0)) :
    Tendsto (fun n => realVectorL2OfCoordinateFunction (aSeq n) (hMem n)) atTop
      (𝓝 (realVectorL2OfCoordinateFunction a ha)) := by
  let sourceLp : Lp (α := Vec3) Vec3 2 volume := ha.toLp a
  let seqLp (n : ℕ) : Lp (α := Vec3) Vec3 2 volume := (hMem n).toLp (aSeq n)
  have hLp : Tendsto seqLp atTop (𝓝 sourceLp) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hApprox
    have hnorm (n : ℕ) : ‖seqLp n - sourceLp‖ =
        ENNReal.toReal (eLpNorm (aSeq n - a) 2 volume) := by
      rw [← dist_eq_norm, Lp.dist_def]
      congr 1
      exact eLpNorm_congr_ae ((hMem n).coeFn_toLp.sub ha.coeFn_toLp)
    have hreal' : Tendsto (fun n => ‖seqLp n - sourceLp‖) atTop (𝓝 0) :=
      Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => (hnorm n).symm) hreal
    simpa only [ENNReal.toReal_zero] using hreal'
  have htransfer : Tendsto
      (fun n => realVectorL2OfCoordinateLp (seqLp n)) atTop
      (𝓝 (realVectorL2OfCoordinateLp sourceLp)) := by
    have hcont : Continuous realVectorL2OfCoordinateLp := by
      fun_prop [realVectorL2OfCoordinateLp]
    exact (hcont.tendsto _).comp hLp
  simpa only [seqLp, sourceLp, realVectorL2OfCoordinateLp_eq_function] using htransfer

private theorem ae_fourierInner_zero_of_tendsto
    (F : ℕ → ComplexVectorL2) (g : ComplexVectorL2)
    (hlim : Tendsto F atTop (𝓝 g))
    (horth : ∀ n, ∀ᵐ ξ ∂volume,
      inner ℂ (complexifyFrequency ξ) (F n ξ) = 0) :
    ∀ᵐ ξ ∂volume,
      inner ℂ (complexifyFrequency ξ) (g ξ) = 0 := by
  obtain ⟨ns, hns, hlimAE⟩ :=
    (MeasureTheory.tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have horthAll : ∀ᵐ ξ ∂volume, ∀ n : ℕ,
      inner ℂ (complexifyFrequency ξ) (F n ξ) = 0 :=
    ae_all_iff.mpr horth
  filter_upwards [hlimAE, horthAll] with ξ hξ hξorth
  have hscalar : Tendsto
      (fun k => inner ℂ (complexifyFrequency ξ) (F (ns k) ξ)) atTop
      (𝓝 (inner ℂ (complexifyFrequency ξ) (g ξ))) := by
    exact (continuous_inner.tendsto _).comp
      (tendsto_const_nhds.prodMk_nhds hξ)
  have hzero : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop
      (𝓝 (inner ℂ (complexifyFrequency ξ) (g ξ))) := by
    convert hscalar using 1
    · funext k
      exact (hξorth (ns k)).symm
  have htarget := tendsto_nhds_unique tendsto_const_nhds hzero
  exact htarget.symm

/-- Fourier orthogonality holds for the complexification of every field in
the closure space `J`. -/
theorem realVectorL2_fourierOrthogonal_of_isInJ
    (f : RealVectorL2)
    (hf : CKN.IsInJ (realVectorL2Representative f)) :
    ∀ᵐ ξ ∂volume,
      inner ℂ (complexifyFrequency ξ)
        ((MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3)
          (complexifyVectorL2 f) ξ) = 0 := by
  rcases hf with ⟨_, aSeq, hSmooth, hCompact, hDiv, hApprox⟩
  have hTarget : MemLp (realVectorL2Representative f) 2 volume :=
    realVectorL2Representative_memLp f
  have hMem (n : ℕ) : MemLp (aSeq n) 2 volume :=
    (hSmooth n).continuous.memLp_of_hasCompactSupport (hCompact n)
  let source : RealVectorL2 :=
    realVectorL2OfCoordinateFunction (realVectorL2Representative f) hTarget
  let seq (n : ℕ) : RealVectorL2 :=
    realVectorL2OfCoordinateFunction (aSeq n) (hMem n)
  have hsource : Tendsto seq atTop (𝓝 source) :=
    realVectorL2_coordinateApprox_tendsto
      (realVectorL2Representative f) hTarget aSeq hMem hApprox
  let F (n : ℕ) := (MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3)
    (complexifyVectorL2 (seq n))
  let g := (MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3)
    (complexifyVectorL2 source)
  have hlim : Tendsto F atTop (𝓝 g) := by
    have hc : Tendsto (fun n => complexifyVectorL2 (seq n)) atTop
        (𝓝 (complexifyVectorL2 source)) :=
      (complexifyVectorL2.continuous.tendsto _).comp hsource
    exact ((MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3).continuous.tendsto _)
      |>.comp hc
  have horth (n : ℕ) : ∀ᵐ ξ ∂volume,
      inner ℂ (complexifyFrequency ξ) (F n ξ) = 0 := by
    let gS := solenoidalSchwartz (aSeq n) (hSmooth n) (hCompact n)
    have hF : F n = (𝓕 gS).toLp 2 volume := by
      dsimp [F, seq]
      rw [compactSolenoidal_complexLp_eq (aSeq n) (hMem n) (hSmooth n) (hCompact n)]
      exact SchwartzMap.toLp_fourier_eq gS
    have hFae : ∀ᵐ ξ ∂volume, F n ξ = 𝓕 gS ξ := by
      rw [hF]
      exact (𝓕 gS).memLp 2 volume |>.coeFn_toLp
    filter_upwards [hFae] with ξ hξ
    rw [hξ]
    exact compactSolenoidal_fourierOrthogonal (aSeq n) (hSmooth n)
      (hCompact n) (hDiv n) ξ
  have hzero := ae_fourierInner_zero_of_tendsto F g hlim horth
  have hsourceEq : source = f := by
    exact realVectorL2OfCoordinateFunction_representation f
  have hFourierEq : g =
      (MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3)
        (complexifyVectorL2 f) := by
    simp only [g, source, hsourceEq]
  have hclassAE := (Lp.ext_iff).mp hFourierEq
  filter_upwards [hzero, hclassAE] with ξ hξ hξclass
  rw [← hξclass]
  exact hξ

end CKN.Leray

end
