/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanCoreCommutatorAlgebra
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Integrated scalar Carleman commutator estimate

Compact support eliminates the space-time fluxes in
`eq:carleman-commutator`; the remaining two squares give the lower bound.
-/

public section


open MeasureTheory CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS

/-- The product norm on parabolic space-time used in this identity. -/
local instance carlemanCoreCommutatorIntegralNormedAddCommGroup :
    NormedAddCommGroup ParabolicPoint :=
  carlemanProductNormedAddCommGroup

/-- The real scalar action compatible with the product norm on parabolic space-time. -/
local instance carlemanCoreCommutatorIntegralNormedSpace : NormedSpace ℝ ParabolicPoint :=
  carlemanProductNormedSpace

/-- Product Lebesgue measure on parabolic space-time. -/
local instance carlemanCoreCommutatorIntegralMeasureSpace : MeasureSpace ParabolicPoint :=
  Measure.prod.measureSpace

private theorem tsupport_subset_of_zero_off
    {f g : ParabolicPoint → ℝ}
    (h : ∀ z, z ∉ tsupport g → f z = 0) :
    tsupport f ⊆ tsupport g := by
  rw [tsupport]
  apply closure_minimal _ (isClosed_tsupport g)
  intro z hz
  by_contra hn
  exact hz (h z hn)

/-- A function smooth on an open set containing its support is smooth. -/
theorem contDiff_of_local_and_tsupport
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {f : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hFU : tsupport f ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) f := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact hf.contDiffAt (hU.mem_nhds hz)
  · have hzs : z ∉ tsupport f := fun h => hz (hFU h)
    have hnhds : (tsupport f)ᶜ ∈ 𝓝 z :=
      (isClosed_tsupport f).isOpen_compl.mem_nhds hzs
    have heq : f =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [hnhds] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    exact (contDiffAt_const (𝕜 := ℝ) (c := (0 : ℝ))).congr_of_eventuallyEq heq

private theorem hasCompactSupport_of_tsupport_subset
    {f g : ParabolicPoint → ℝ}
    (hgc : HasCompactSupport g)
    (hfg : tsupport f ⊆ tsupport g) : HasCompactSupport f :=
  hgc.isCompact.of_isClosed_subset (isClosed_tsupport f) hfg

private theorem commutator_terms_zero_off
    {φ v : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hz : z ∉ tsupport v) :
    commutatorSymmetric φ v z = 0 ∧
      commutatorSkew φ v z = 0 ∧
      commutatorTimeFlux φ v z = 0 ∧
      (∀ i, commutatorSpaceFlux φ v i z = 0) ∧
      carlemanConj φ v z = 0 ∧
      carlemanCommutatorDensity φ v z = 0 := by
  have hv0 : v z = 0 := image_eq_zero_of_notMem_tsupport hz
  have ht0 : timePartial v z = 0 :=
    CKN.timePartial_eq_zero_off_tsupport hz
  have hq0 (i : Fin 3) : spatialPartial v i z = 0 :=
    CKN.spatialPartial_eq_zero_off_tsupport hz i
  have hr0 (i j : Fin 3) : spatialSecondPartial v i j z = 0 :=
    CKN.spatialSecondPartial_eq_zero_off_tsupport hz i j
  simp [commutatorSymmetric, commutatorSkew,
    commutatorTimeFlux, commutatorSpaceFlux, carlemanConj,
    carlemanCommutatorDensity, scalarLaplacian, scalarGradSq,
    hv0, ht0, hq0, hr0]

private theorem commutator_tsupports_subset
    (φ v : ParabolicPoint → ℝ) :
    tsupport (commutatorSymmetric φ v) ⊆ tsupport v ∧
      tsupport (commutatorSkew φ v) ⊆ tsupport v ∧
      tsupport (commutatorTimeFlux φ v) ⊆ tsupport v ∧
      (∀ i, tsupport (commutatorSpaceFlux φ v i) ⊆ tsupport v) ∧
      tsupport (carlemanConj φ v) ⊆ tsupport v ∧
      tsupport (carlemanCommutatorDensity φ v) ⊆ tsupport v := by
  refine ⟨tsupport_subset_of_zero_off (fun z hz =>
      (commutator_terms_zero_off (φ := φ) hz).1),
    tsupport_subset_of_zero_off (fun z hz =>
      (commutator_terms_zero_off (φ := φ) hz).2.1),
    tsupport_subset_of_zero_off (fun z hz =>
      (commutator_terms_zero_off (φ := φ) hz).2.2.1),
    fun i => tsupport_subset_of_zero_off (fun z hz =>
      (commutator_terms_zero_off (φ := φ) hz).2.2.2.1 i),
    tsupport_subset_of_zero_off (fun z hz =>
      (commutator_terms_zero_off (φ := φ) hz).2.2.2.2.1),
    tsupport_subset_of_zero_off (fun z hz =>
      (commutator_terms_zero_off (φ := φ) hz).2.2.2.2.2)⟩

private theorem commutatorTimeFlux_contDiffOn
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiffOn ℝ (⊤ : ℕ∞) (commutatorTimeFlux φ v) U := by
  have hQ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => scalarGradSq φ z - timePartial φ z) U :=
    (contDiffOn_scalarGradSq hU hφ).sub (contDiffOn_timePartial hU hφ)
  have hgrad : ContDiffOn ℝ (⊤ : ℕ∞) (scalarGradSq v) U :=
    contDiffOn_scalarGradSq hU hv.contDiffOn
  unfold commutatorTimeFlux
  fun_prop (disch := assumption)

private theorem commutatorSymmetric_contDiffOn
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiffOn ℝ (⊤ : ℕ∞) (commutatorSymmetric φ v) U := by
  have hQ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => scalarGradSq φ z - timePartial φ z) U :=
    (contDiffOn_scalarGradSq hU hφ).sub (contDiffOn_timePartial hU hφ)
  have hLap : ContDiffOn ℝ (⊤ : ℕ∞) (scalarLaplacian v) U :=
    contDiffOn_scalarLaplacian hU hv.contDiffOn
  unfold commutatorSymmetric
  fun_prop (disch := assumption)

private theorem commutatorSkew_contDiffOn
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiffOn ℝ (⊤ : ℕ∞) (commutatorSkew φ v) U := by
  have htime : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => timePartial v z) U :=
    contDiffOn_timePartial hU hv.contDiffOn
  have hp (i : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => spatialPartial φ i z) U :=
    contDiffOn_spatialPartial hU hφ i
  have hq (i : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => spatialPartial v i z) U :=
    contDiffOn_spatialPartial hU hv.contDiffOn i
  have hLap : ContDiffOn ℝ (⊤ : ℕ∞) (scalarLaplacian φ) U :=
    contDiffOn_scalarLaplacian hU hφ
  unfold commutatorSkew
  fun_prop (disch := assumption)

private theorem commutatorSpaceFlux_contDiffOn
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (i : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (commutatorSpaceFlux φ v i) U := by
  have htime : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => timePartial v z) U :=
    contDiffOn_timePartial hU hv.contDiffOn
  have hp (j : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => spatialPartial φ j z) U :=
    contDiffOn_spatialPartial hU hφ j
  have hq (j : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => spatialPartial v j z) U :=
    contDiffOn_spatialPartial hU hv.contDiffOn j
  have hLap : ContDiffOn ℝ (⊤ : ℕ∞) (scalarLaplacian φ) U :=
    contDiffOn_scalarLaplacian hU hφ
  have hdi : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => spatialPartial (scalarLaplacian φ) i z) U :=
    contDiffOn_spatialPartial hU hLap i
  have hQ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => scalarGradSq φ z - timePartial φ z) U :=
    (contDiffOn_scalarGradSq hU hφ).sub (contDiffOn_timePartial hU hφ)
  have hgrad : ContDiffOn ℝ (⊤ : ℕ∞) (scalarGradSq v) U :=
    contDiffOn_scalarGradSq hU hv.contDiffOn
  unfold commutatorSpaceFlux
  fun_prop (disch := assumption)

private theorem integrable_mul_smooth_compact
    {f g : ParabolicPoint → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfc : HasCompactSupport f) :
    Integrable (fun z => f z * g z) volume :=
  integrable_contDiff_compact (hf.mul hg) hfc.mul_right

/-- The square of a smooth compactly supported scalar field is integrable. -/
theorem integrable_sq_smooth_compact
    {f : ParabolicPoint → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) :
    Integrable (fun z => f z ^ 2) volume := by
  have h := integrable_mul_smooth_compact hf hf hfc
  simpa only [pow_two] using h

private theorem commutator_flux_integrals_zero
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) (hvU : tsupport v ⊆ U) :
    (∫ z : Vec3 × ℝ, timePartial (commutatorTimeFlux φ v) z ∂volume) = 0 ∧
    (∫ z : Vec3 × ℝ, ∑ i : Fin 3,
      spatialPartial (commutatorSpaceFlux φ v i) i z ∂volume) = 0 := by
  have hs := commutator_tsupports_subset φ v
  have hF0smooth : ContDiff ℝ (⊤ : ℕ∞) (commutatorTimeFlux φ v) :=
    contDiff_of_local_and_tsupport hU
      (commutatorTimeFlux_contDiffOn hU hφ hv) (hs.2.2.1.trans hvU)
  have hF0compact : HasCompactSupport (commutatorTimeFlux φ v) :=
    hasCompactSupport_of_tsupport_subset hvc hs.2.2.1
  have hFis (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (commutatorSpaceFlux φ v i) :=
    contDiff_of_local_and_tsupport hU
      (commutatorSpaceFlux_contDiffOn hU hφ hv i)
      ((hs.2.2.2.1 i).trans hvU)
  have hFic (i : Fin 3) : HasCompactSupport
      (commutatorSpaceFlux φ v i) :=
    hasCompactSupport_of_tsupport_subset hvc (hs.2.2.2.1 i)
  have hFi0 (i : Fin 3) := integral_spatialPartial_eq_zero
    (hFis i) (hFic i) i
  have hFiInt (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => spatialPartial
        (commutatorSpaceFlux φ v i) i z) volume := by
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun z => spatialPartial (commutatorSpaceFlux φ v i) i z) :=
      contDiffOn_univ.mp
        (contDiffOn_spatialPartial isOpen_univ (hFis i).contDiffOn i)
    have hcompact : HasCompactSupport
        (fun z : Vec3 × ℝ => spatialPartial
          (commutatorSpaceFlux φ v i) i z) :=
      CKN.hasCompactSupport_spatialPartial (hFic i) i
    exact integrable_contDiff_compact hsmooth hcompact
  refine ⟨integral_timePartial_eq_zero hF0smooth hF0compact, ?_⟩
  rw [integral_finsetSum Finset.univ (fun i _ => hFiInt i)]
  simp only [hFi0, Finset.sum_const_zero]

private theorem commutator_pointwise_divergence_global
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvU : tsupport v ⊆ U) (z : ParabolicPoint) :
    2 * commutatorSymmetric φ v z * commutatorSkew φ v z =
      carlemanCommutatorDensity φ v z +
        timePartial (commutatorTimeFlux φ v) z +
        ∑ i, spatialPartial (commutatorSpaceFlux φ v i) i z := by
  by_cases hz : z ∈ U
  · exact commutator_pointwise_divergence hU hφ hv hz
  · have hnot : z ∉ tsupport v := fun h => hz (hvU h)
    rcases commutator_terms_zero_off (φ := φ) hnot with
      ⟨hS, hA, _, _, _, hD⟩
    have hs := commutator_tsupports_subset φ v
    have hF0 : timePartial (commutatorTimeFlux φ v) z = 0 :=
      CKN.timePartial_eq_zero_off_tsupport
        (fun h => hnot (hs.2.2.1 h))
    have hFi (i : Fin 3) :
        spatialPartial (commutatorSpaceFlux φ v i) i z = 0 :=
      CKN.spatialPartial_eq_zero_off_tsupport
        (fun h => hnot (hs.2.2.2.1 i h)) i
    simp [hS, hA, hD, hF0, hFi]

private theorem commutator_integrability
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) (hvU : tsupport v ⊆ U) :
    Integrable (fun z => commutatorSymmetric φ v z ^ 2) volume ∧
    Integrable (fun z => commutatorSkew φ v z ^ 2) volume ∧
    Integrable (fun z =>
      commutatorSymmetric φ v z * commutatorSkew φ v z) volume ∧
    Integrable (fun z => z.2 ^ 2 * carlemanConj φ v z ^ 2) volume ∧
    Integrable (fun z => timePartial (commutatorTimeFlux φ v) z) volume ∧
    Integrable (fun z => ∑ i,
      spatialPartial (commutatorSpaceFlux φ v i) i z) volume ∧
    Integrable (carlemanCommutatorDensity φ v) volume := by
  have hs := commutator_tsupports_subset φ v
  have hSsmooth : ContDiff ℝ (⊤ : ℕ∞) (commutatorSymmetric φ v) :=
    contDiff_of_local_and_tsupport hU
      (commutatorSymmetric_contDiffOn hU hφ hv) (hs.1.trans hvU)
  have hAsmooth : ContDiff ℝ (⊤ : ℕ∞) (commutatorSkew φ v) :=
    contDiff_of_local_and_tsupport hU
      (commutatorSkew_contDiffOn hU hφ hv) (hs.2.1.trans hvU)
  have hPsmooth : ContDiff ℝ (⊤ : ℕ∞) (carlemanConj φ v) :=
    contDiff_of_local_and_tsupport hU
      (contDiffOn_carlemanConj hU hφ hv) (hs.2.2.2.2.1.trans hvU)
  have hF0smooth : ContDiff ℝ (⊤ : ℕ∞) (commutatorTimeFlux φ v) :=
    contDiff_of_local_and_tsupport hU
      (commutatorTimeFlux_contDiffOn hU hφ hv) (hs.2.2.1.trans hvU)
  have hFis (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (commutatorSpaceFlux φ v i) :=
    contDiff_of_local_and_tsupport hU
      (commutatorSpaceFlux_contDiffOn hU hφ hv i)
      ((hs.2.2.2.1 i).trans hvU)
  have hSc : HasCompactSupport (commutatorSymmetric φ v) :=
    hasCompactSupport_of_tsupport_subset hvc hs.1
  have hAc : HasCompactSupport (commutatorSkew φ v) :=
    hasCompactSupport_of_tsupport_subset hvc hs.2.1
  have hPc : HasCompactSupport (carlemanConj φ v) :=
    hasCompactSupport_of_tsupport_subset hvc hs.2.2.2.2.1
  have hF0c : HasCompactSupport (commutatorTimeFlux φ v) :=
    hasCompactSupport_of_tsupport_subset hvc hs.2.2.1
  have hFic (i : Fin 3) : HasCompactSupport (commutatorSpaceFlux φ v i) :=
    hasCompactSupport_of_tsupport_subset hvc (hs.2.2.2.1 i)
  have hS2 : Integrable (fun z => commutatorSymmetric φ v z ^ 2) volume :=
    integrable_sq_smooth_compact hSsmooth hSc
  have hA2 : Integrable (fun z => commutatorSkew φ v z ^ 2) volume :=
    integrable_sq_smooth_compact hAsmooth hAc
  have hSA : Integrable (fun z =>
      commutatorSymmetric φ v z * commutatorSkew φ v z) volume :=
    integrable_mul_smooth_compact hSsmooth hAsmooth hSc
  have hP2 : Integrable (fun z => z.2 ^ 2 * carlemanConj φ v z ^ 2) volume := by
    have ht : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : ParabolicPoint => z.2 ^ 2) := by fun_prop
    have h := integrable_mul_smooth_compact hPsmooth (ht.mul hPsmooth) hPc
    have heq : (fun z => z.2 ^ 2 * carlemanConj φ v z ^ 2) =
        (fun z => carlemanConj φ v z *
          (z.2 ^ 2 * carlemanConj φ v z)) := by
      funext z
      ring
    rw [heq]
    exact h
  have hF0 : Integrable
      (fun z => timePartial (commutatorTimeFlux φ v) z) volume := by
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun z => timePartial (commutatorTimeFlux φ v) z) :=
      contDiffOn_univ.mp
        (contDiffOn_timePartial isOpen_univ hF0smooth.contDiffOn)
    have hcompact : HasCompactSupport
        (fun z => timePartial (commutatorTimeFlux φ v) z) :=
      CKN.hasCompactSupport_timePartial hF0c
    exact integrable_contDiff_compact hsmooth hcompact
  have hFi (i : Fin 3) : Integrable
      (fun z => spatialPartial (commutatorSpaceFlux φ v i) i z) volume := by
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun z => spatialPartial (commutatorSpaceFlux φ v i) i z) :=
      contDiffOn_univ.mp
        (contDiffOn_spatialPartial isOpen_univ (hFis i).contDiffOn i)
    have hcompact : HasCompactSupport
        (fun z => spatialPartial (commutatorSpaceFlux φ v i) i z) :=
      CKN.hasCompactSupport_spatialPartial (hFic i) i
    exact integrable_contDiff_compact hsmooth hcompact
  have hFiSum : Integrable (fun z => ∑ i,
      spatialPartial (commutatorSpaceFlux φ v i) i z) volume :=
    integrable_finsetSum Finset.univ (fun i _ => hFi i)
  have hD : Integrable (carlemanCommutatorDensity φ v) volume := by
    have heq : carlemanCommutatorDensity φ v =
        (fun z => 2 * (commutatorSymmetric φ v z *
          commutatorSkew φ v z) -
          timePartial (commutatorTimeFlux φ v) z -
          (∑ i, spatialPartial (commutatorSpaceFlux φ v i) i z)) := by
      funext z
      have hp := commutator_pointwise_divergence_global hU hφ hv hvU z
      linarith only [hp]
    rw [heq]
    exact ((hSA.const_mul 2).sub hF0).sub hFiSum
  exact ⟨hS2, hA2, hSA, hP2, hF0, hFiSum, hD⟩

private theorem commutator_integral_identity
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) (hvU : tsupport v ⊆ U) :
    (∫ z, z.2 ^ 2 * carlemanConj φ v z ^ 2 ∂volume) =
      (∫ z, commutatorSymmetric φ v z ^ 2 ∂volume) +
        (∫ z, commutatorSkew φ v z ^ 2 ∂volume) +
        (∫ z, carlemanCommutatorDensity φ v z ∂volume) := by
  rcases commutator_integrability hU hφ hv hvc hvU with
    ⟨hS2, hA2, _, _, hF0, hFi, hD⟩
  rcases commutator_flux_integrals_zero hU hφ hv hvc hvU with
    ⟨hF0zero, hFizero⟩
  have hpoint (z : ParabolicPoint) :
      z.2 ^ 2 * carlemanConj φ v z ^ 2 =
        commutatorSymmetric φ v z ^ 2 +
          commutatorSkew φ v z ^ 2 +
          carlemanCommutatorDensity φ v z +
          timePartial (commutatorTimeFlux φ v) z +
          (∑ i, spatialPartial (commutatorSpaceFlux φ v i) i z) := by
    have hsum : commutatorSymmetric φ v z + commutatorSkew φ v z =
        z.2 * carlemanConj φ v z := by
      unfold commutatorSymmetric commutatorSkew carlemanConj
      ring
    have hdiv := commutator_pointwise_divergence_global hU hφ hv hvU z
    calc
      _ = (z.2 * carlemanConj φ v z) ^ 2 := by ring
      _ = (commutatorSymmetric φ v z + commutatorSkew φ v z) ^ 2 := by
        rw [hsum]
      _ = commutatorSymmetric φ v z ^ 2 +
            commutatorSkew φ v z ^ 2 +
            2 * commutatorSymmetric φ v z * commutatorSkew φ v z := by ring
      _ = _ := by rw [hdiv]; ring
  have h12 : Integrable (fun z =>
      commutatorSymmetric φ v z ^ 2 + commutatorSkew φ v z ^ 2) volume :=
    hS2.add hA2
  have h123 : Integrable (fun z =>
      commutatorSymmetric φ v z ^ 2 + commutatorSkew φ v z ^ 2 +
        carlemanCommutatorDensity φ v z) volume :=
    h12.add hD
  have h1234 : Integrable (fun z =>
      commutatorSymmetric φ v z ^ 2 + commutatorSkew φ v z ^ 2 +
        carlemanCommutatorDensity φ v z +
        timePartial (commutatorTimeFlux φ v) z) volume :=
    h123.add hF0
  calc
    (∫ z, z.2 ^ 2 * carlemanConj φ v z ^ 2 ∂volume) =
        ∫ z, commutatorSymmetric φ v z ^ 2 +
          commutatorSkew φ v z ^ 2 +
          carlemanCommutatorDensity φ v z +
          timePartial (commutatorTimeFlux φ v) z +
          (∑ i, spatialPartial (commutatorSpaceFlux φ v i) i z) ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact hpoint z
    _ = _ := by
      have he1 :
          (∫ z, commutatorSymmetric φ v z ^ 2 +
            commutatorSkew φ v z ^ 2 +
            carlemanCommutatorDensity φ v z +
            timePartial (commutatorTimeFlux φ v) z +
            (∑ i, spatialPartial (commutatorSpaceFlux φ v i) i z) ∂volume) =
          (∫ z, commutatorSymmetric φ v z ^ 2 +
            commutatorSkew φ v z ^ 2 +
            carlemanCommutatorDensity φ v z +
            timePartial (commutatorTimeFlux φ v) z ∂volume) +
          (∫ z, ∑ i, spatialPartial
            (commutatorSpaceFlux φ v i) i z ∂volume) :=
        integral_add h1234 hFi
      have he2 :
          (∫ z, commutatorSymmetric φ v z ^ 2 +
            commutatorSkew φ v z ^ 2 +
            carlemanCommutatorDensity φ v z +
            timePartial (commutatorTimeFlux φ v) z ∂volume) =
          (∫ z, commutatorSymmetric φ v z ^ 2 +
            commutatorSkew φ v z ^ 2 +
            carlemanCommutatorDensity φ v z ∂volume) +
          (∫ z, timePartial (commutatorTimeFlux φ v) z ∂volume) :=
        integral_add h123 hF0
      have he3 :
          (∫ z, commutatorSymmetric φ v z ^ 2 +
            commutatorSkew φ v z ^ 2 +
            carlemanCommutatorDensity φ v z ∂volume) =
          (∫ z, commutatorSymmetric φ v z ^ 2 +
            commutatorSkew φ v z ^ 2 ∂volume) +
          (∫ z, carlemanCommutatorDensity φ v z ∂volume) :=
        integral_add h12 hD
      have he4 :
          (∫ z, commutatorSymmetric φ v z ^ 2 +
            commutatorSkew φ v z ^ 2 ∂volume) =
          (∫ z, commutatorSymmetric φ v z ^ 2 ∂volume) +
          (∫ z, commutatorSkew φ v z ^ 2 ∂volume) :=
        integral_add hS2 hA2
      have hF0zero' : (∫ z : ParabolicPoint,
          timePartial (commutatorTimeFlux φ v) z ∂volume) = 0 := hF0zero
      have hFizero' : (∫ z : ParabolicPoint, ∑ i,
          spatialPartial (commutatorSpaceFlux φ v i) i z ∂volume) = 0 := hFizero
      rw [he1, he2, he3, he4, hF0zero', hFizero']
      ring

/-- The commutator density is bounded by the square of the conjugated heat
operator, as used in `eq:carleman-commutator-energy`. -/
theorem carleman_commutator_le
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) (hvU : tsupport v ⊆ U) :
    (∫ z, carlemanCommutatorDensity φ v z ∂volume) ≤
      ∫ z, z.2 ^ 2 * carlemanConj φ v z ^ 2 ∂volume := by
  have hEq := commutator_integral_identity hU hφ hv hvc hvU
  have hS0 : 0 ≤ (∫ z, commutatorSymmetric φ v z ^ 2 ∂volume) :=
    integral_nonneg (fun z => sq_nonneg _)
  have hA0 : 0 ≤ (∫ z, commutatorSkew φ v z ^ 2 ∂volume) :=
    integral_nonneg (fun z => sq_nonneg _)
  linarith only [hEq, hS0, hA0]

end ESS
