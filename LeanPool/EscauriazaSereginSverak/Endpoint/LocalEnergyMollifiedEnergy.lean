/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.LocalEnergyMollifiedData
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.LocalEnergyCylinderL4
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalEnergyMomentumEquation
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalEnergyMollifierConvergence
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Local Energy Mollified Energy

Local energy identities and limit passages for the endpoint regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace ESS

local instance localEnergyHolderTripleFourFourTwo :
    ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
  have hreal : Real.HolderTriple 4 4 2 := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using hreal.ennrealOfReal

@[expose] def localEnergySpatialDir (j : Fin 3) : Vec3 × ℝ := (basisVec j, 0)

private theorem localEnergy_spatialPartial_eq_fderiv_apply
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (j : Fin 3) (z : Vec3 × ℝ) :
    spatialPartial (show ParabolicPoint → ℝ from ψ) j z =
      (fderiv ℝ ψ z) (localEnergySpatialDir j) := by
  have hinner : HasFDerivAt (fun x : Vec3 => (x, z.2))
      (ContinuousLinearMap.inl ℝ Vec3 ℝ) z.1 :=
    hasFDerivAt_prodMk_left z.1 z.2
  have houter : HasFDerivAt ψ (fderiv ℝ ψ z) z :=
    (hψ.differentiable (by norm_num) z).hasFDerivAt
  have hcomp := houter.comp z.1 hinner
  have hfd : fderiv ℝ (fun x : Vec3 => ψ (x, z.2)) z.1 =
      (fderiv ℝ ψ z).comp (ContinuousLinearMap.inl ℝ Vec3 ℝ) := hcomp.fderiv
  change (fderiv ℝ (fun x : Vec3 => ψ (x, z.2)) z.1) (basisVec j) = _
  rw [hfd]
  simp [localEnergySpatialDir, basisVec]

/-- Products converge in the Hölder exponent when both factors converge in their respective
Lebesgue norms. -/
theorem localEnergy_tendsto_eLpNorm_mul_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p q r : ℝ≥0∞} [htriple : ENNReal.HolderTriple p q r]
    (hr : 1 ≤ r) {f g : α → ℝ} (hf : MemLp f p μ) (hg : MemLp g q μ)
    {fn gn : ℕ → α → ℝ}
    (hfn : ∀ n, MemLp (fn n) p μ) (hgn : ∀ n, MemLp (gn n) q μ)
    (hfnLim : Tendsto (fun n => eLpNorm (fun x => fn n x - f x) p μ)
      atTop (nhds 0))
    (hgnLim : Tendsto (fun n => eLpNorm (fun x => gn n x - g x) q μ)
      atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (fun x => fn n x * gn n x - f x * g x) r μ)
      atTop (nhds 0) := by
  have hp : 1 ≤ p := hr.trans htriple.le
  have hq : 1 ≤ q := hr.trans htriple.symm.le
  have hmul (a b : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (hb : AEStronglyMeasurable b μ) :
      eLpNorm (fun x => a x * b x) r μ ≤ eLpNorm a p μ * eLpNorm b q μ := by
    simpa using (eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm
      (b := fun x y : ℝ => x * y) (c := (1 : ℝ≥0∞))
      (by fun_prop) ha hb (by filter_upwards with x; simp [enorm_mul]))
  have hsum : ∀ n,
      eLpNorm (fun x => fn n x * gn n x - f x * g x) r μ ≤
        eLpNorm (fun x => fn n x - f x) p μ * eLpNorm (gn n) q μ +
          eLpNorm f p μ * eLpNorm (fun x => gn n x - g x) q μ := by
    intro n
    have hdiff : (fun x => fn n x * gn n x - f x * g x) =
        (fun x => (fn n x - f x) * gn n x + f x * (gn n x - g x)) := by
      funext x
      ring
    rw [hdiff]
    calc
      _ ≤ eLpNorm (fun x => (fn n x - f x) * gn n x) r μ +
          eLpNorm (fun x => f x * (gn n x - g x)) r μ := eLpNorm_add_le hr
      _ ≤ _ := add_le_add
        (hmul (fun x => fn n x - f x) (gn n)
          ((hfn n).sub hf).aestronglyMeasurable (hgn n).aestronglyMeasurable)
        (hmul f (fun x => gn n x - g x)
          hf.aestronglyMeasurable ((hgn n).sub hg).aestronglyMeasurable)
  let C := eLpNorm g q μ
  have hC : C < ⊤ := hg
  have hC1 : C + 1 ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hC.ne, ENNReal.one_ne_top⟩
  have hgnBound : ∀ᶠ n : ℕ in atTop, eLpNorm (gn n) q μ ≤ C + 1 := by
    filter_upwards [hgnLim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))]
      with n hn
    have htriangle := eLpNorm_add_le (μ := μ) (p := q) hq
      (f := fun x => gn n x - g x) (g := g)
    have hidentity : (fun x => gn n x) = (fun x => gn n x - g x + g x) := by
      funext x
      ring
    calc
      eLpNorm (gn n) q μ = eLpNorm (fun x => (gn n x - g x) + g x) q μ := by
        exact congrArg (fun k => eLpNorm k q μ) hidentity
      _ ≤ eLpNorm (fun x => gn n x - g x) q μ + eLpNorm g q μ := htriangle
      _ ≤ 1 + C := add_le_add hn.le le_rfl
      _ = C + 1 := add_comm _ _
  have hfirst : Tendsto
      (fun n => eLpNorm (fun x => fn n x - f x) p μ * (C + 1))
      atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.mul_const hfnLim (Or.inr hC1)
  have hsecond : Tendsto
      (fun n => eLpNorm f p μ * eLpNorm (fun x => gn n x - g x) q μ)
      atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hgnLim (Or.inr hf.ne)
  have hmajor : Tendsto
      (fun n => eLpNorm (fun x => fn n x - f x) p μ * (C + 1) +
        eLpNorm f p μ * eLpNorm (fun x => gn n x - g x) q μ)
      atTop (nhds 0) := by
    simpa using hfirst.add hsecond
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
  · filter_upwards with n
    exact bot_le
  · filter_upwards [hgnBound] with n hn
    exact (hsum n).trans (add_le_add (mul_le_mul_right hn _) le_rfl)

/-- The zero-extended energy inputs have locally integrable components and smooth
space-time mollifications. -/
private theorem localEnergy_mollified_input_regularities
    {U : Set (Vec3 × ℝ)} {u : Vec3 × ℝ → Vec3}
    {Du : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ} {p : Vec3 × ℝ → ℝ}
    (hUmeas : MeasurableSet U)
    (hu4 : MemLp (fun z : Vec3 × ℝ => u z) 4
      ((volume : Measure (Vec3 × ℝ)).restrict U))
    (hDu2 : MemLp (fun z : Vec3 × ℝ => Du z) 2
      ((volume : Measure (Vec3 × ℝ)).restrict U))
    (hpProd : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict U))
    {δ : ℝ} (hδ : 0 < δ) :
    (∀ i, LocallyIntegrable (fun z : Vec3 × ℝ =>
      U.indicator (fun q => u q i) z) volume) ∧
    (∀ i j, LocallyIntegrable (fun z : Vec3 × ℝ =>
      U.indicator (fun q => u q i * u q j) z) volume) ∧
    (∀ i j, LocallyIntegrable (fun z : Vec3 × ℝ =>
      U.indicator (fun q => Du q i j) z) volume) ∧
    LocallyIntegrable (U.indicator p) volume ∧
    (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun z =>
      spaceTimeMollify (U.indicator (fun q => u q i)) δ hδ z)) ∧
    (∀ i, (fun y : Vec3 × ℝ => U.indicator u y i) =
      U.indicator (fun q => u q i)) ∧
    (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun z =>
      spaceTimeMollify (fun q => U.indicator u q i) δ hδ z)) ∧
    (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun z =>
      spaceTimeMollify (U.indicator (fun q => u q i * u q j)) δ hδ z)) ∧
    (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun z =>
      spaceTimeMollify (U.indicator (fun q => Du q i j)) δ hδ z)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (spaceTimeMollify (U.indicator p) δ hδ) := by
  have hu4i (i : Fin 3) : MemLp (fun z : Vec3 × ℝ => u z i) 4
      ((volume : Measure (Vec3 × ℝ)).restrict U) := (memLp_pi_iff.mp hu4) i
  have hDu2ij (i j : Fin 3) : MemLp (fun z : Vec3 × ℝ => Du z i j) 2
      ((volume : Measure (Vec3 × ℝ)).restrict U) :=
    (memLp_pi_iff.mp ((memLp_pi_iff.mp hDu2) i)) j
  have hF2ij (i j : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => u z i * u z j) 2
      ((volume : Measure (Vec3 × ℝ)).restrict U) :=
    MeasureTheory.MemLp.mul (p := 4) (q := 4) (r := 2)
      (hu4i i) (hu4i j)
  have huExtLp (i : Fin 3) : MemLp
      (U.indicator (fun z : Vec3 × ℝ => u z i)) 4
      (volume : Measure (Vec3 × ℝ)) :=
    (memLp_indicator_iff_restrict hUmeas).2 (hu4i i)
  have hFExtLp (i j : Fin 3) : MemLp
      (U.indicator (fun z : Vec3 × ℝ => u z i * u z j)) 2
      (volume : Measure (Vec3 × ℝ)) :=
    (memLp_indicator_iff_restrict hUmeas).2 (hF2ij i j)
  have hGExtLp (i j : Fin 3) : MemLp
      (U.indicator (fun z : Vec3 × ℝ => Du z i j)) 2
      (volume : Measure (Vec3 × ℝ)) :=
    (memLp_indicator_iff_restrict hUmeas).2 (hDu2ij i j)
  have hpExtLp : MemLp (U.indicator p) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) :=
    (memLp_indicator_iff_restrict hUmeas).2 hpProd
  have huLoc (i : Fin 3) : LocallyIntegrable
      (fun z : Vec3 × ℝ => U.indicator (fun q => u q i) z)
      (volume : Measure (Vec3 × ℝ)) := huExtLp i |>.locallyIntegrable (by norm_num)
  have hFLoc (i j : Fin 3) : LocallyIntegrable
      (fun z : Vec3 × ℝ => U.indicator (fun q => u q i * u q j) z)
      (volume : Measure (Vec3 × ℝ)) := hFExtLp i j |>.locallyIntegrable (by norm_num)
  have hGLoc (i j : Fin 3) : LocallyIntegrable
      (fun z : Vec3 × ℝ => U.indicator (fun q => Du q i j) z)
      (volume : Measure (Vec3 × ℝ)) := hGExtLp i j |>.locallyIntegrable (by norm_num)
  have hpLoc : LocallyIntegrable (U.indicator p) (volume : Measure (Vec3 × ℝ)) :=
    hpExtLp.locallyIntegrable (by norm_num)
  have huSmooth (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spaceTimeMollify
        (U.indicator (fun q => u q i)) δ hδ z) :=
    spaceTimeMollify_contDiff hδ (huLoc i)
  have huIndicatorEq (i : Fin 3) :
      (fun y : Vec3 × ℝ => U.indicator u y i) =
        U.indicator (fun q => u q i) := by
    funext y
    by_cases hy : y ∈ U <;> simp [Set.indicator, hy]
  have huVectorSmooth (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spaceTimeMollify
        (fun q => U.indicator u q i) δ hδ z) := by
    rw [huIndicatorEq i]
    exact huSmooth i
  have hFSmooth (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spaceTimeMollify
        (U.indicator (fun q => u q i * u q j)) δ hδ z) :=
    spaceTimeMollify_contDiff hδ (hFLoc i j)
  have hGSmooth (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spaceTimeMollify
        (U.indicator (fun q => Du q i j)) δ hδ z) :=
    spaceTimeMollify_contDiff hδ (hGLoc i j)
  have hpSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (spaceTimeMollify (U.indicator p) δ hδ) :=
    spaceTimeMollify_contDiff hδ hpLoc
  exact ⟨huLoc, hFLoc, hGLoc, hpLoc, huSmooth, huIndicatorEq,
    huVectorSmooth, hFSmooth, hGSmooth, hpSmooth⟩

/-- A compactly supported smooth energy test has zero mollified energy density on every
interior scale for which its support stays inside the unit cylinder. -/
theorem localEnergy_mollified_base_integral_zero
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) i) (fun x => Du (x, t) i))
    (hS2 : ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0)
    (hS3 : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z = 0)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    {δ : ℝ} (hδ : 0 < δ)
    (hcover : ∀ z ∈ tsupport ψ,
      Metric.closedBall z (3 * δ) ⊆ vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0) :
    ∫ z, smoothEnergyBaseIntegrand
        (fun y i => spaceTimeMollify
          ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
            (fun q : Vec3 × ℝ => u q i)) δ hδ y)
        (fun y i j => spaceTimeMollify
          ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
            (fun q : Vec3 × ℝ => u q i * u q j)) δ hδ y -
            spaceTimeMollify
              ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
                (fun q : Vec3 × ℝ => u q i)) δ hδ y *
              spaceTimeMollify
                ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
                  (fun q : Vec3 × ℝ => u q j)) δ hδ y)
        (fun y i j => spaceTimeMollify
          ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator
            (fun q : Vec3 × ℝ => Du q i j)) δ hδ y)
        (spaceTimeMollify
          ((vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0).indicator p) δ hδ) ψ z
        ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
  let B : Set Vec3 := vec3Ball (0 : Vec3) 1
  let J : Set ℝ := Ioo (-1) 0
  let U : Set (Vec3 × ℝ) := B ×ˢ J
  have hUmeas : MeasurableSet U := by
    exact (isOpen_vec3Ball (0 : Vec3) 1).measurableSet.prod measurableSet_Ioo
  have hUopen : IsOpen U := by
    exact (isOpen_vec3Ball (0 : Vec3) 1).prod isOpen_Ioo
  have hu4para := velocity_memLp_four_unit_of_essLocalData hu hDu henergy hL3 hgrad
  have hu4 : MemLp (fun z : Vec3 × ℝ => u z) 4
      ((volume : Measure (Vec3 × ℝ)).restrict U) := by
    have h := localEnergy_memLp_parabolic_to_product hu4para
    simpa [U, B, J] using h
  have hu2Du2 := energyL2_components_memLp hu hDu henergy
  have hDu2 : MemLp (fun z : Vec3 × ℝ => Du z) 2
      ((volume : Measure (Vec3 × ℝ)).restrict U) := by
    have h := localEnergy_memLp_parabolic_to_product hu2Du2.2
    simpa [U, B, J] using h
  have hpProd : MemLp (fun z : Vec3 × ℝ => p z) (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict U) := by
    have h := localEnergy_memLp_parabolic_to_product hpLp
    simpa [U, B, J] using h
  have ⟨huLoc, hFLoc, hGLoc, hpLoc, huSmooth, huIndicatorEq,
      huVectorSmooth, hFSmooth, hGSmooth, hpSmooth⟩ :=
    localEnergy_mollified_input_regularities hUmeas hu4 hDu2 hpProd hδ
  let uδ : Vec3 × ℝ → Vec3 := fun z i =>
    spaceTimeMollify (fun q => U.indicator u q i) δ hδ z
  let Fδ : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun z i j =>
    spaceTimeMollify (U.indicator (fun q => u q i * u q j)) δ hδ z
  let Gδ : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun z i j =>
    spaceTimeMollify (U.indicator (fun q => Du q i j)) δ hδ z
  let pδ : Vec3 × ℝ → ℝ := spaceTimeMollify (U.indicator p) δ hδ
  let Rδ : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun z i j =>
    Fδ z i j - uδ z i * uδ z j
  have huδSmooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun z => uδ z i) := by
    intro i
    exact huVectorSmooth i
  have hFδSmooth : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun z => Fδ z i j) := by
    intro i j
    exact hFSmooth i j
  have hGδSmooth : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun z => Gδ z i j) := by
    intro i j
    exact hGSmooth i j
  have hRδSmooth : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun z => Rδ z i j) := by
    intro i j
    dsimp [Rδ]
    exact (hFδSmooth i j).sub ((huδSmooth i).mul (huδSmooth j))
  have hPDE (z : Vec3 × ℝ) (hz : Metric.closedBall z δ ⊆ U) :=
    essLocal_mollifiedMomentumEquation_of_essLocalData
      hu hDu henergy hpLp hS2 hS3 hδ (z := z) (by simpa [U, B, J] using hz)
  have hweak : ∀ φ : Vec3 × ℝ → Vec3,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ tsupport ψ →
      ∫ z, smoothMomentumTestIntegrand uδ Rδ Gδ pδ φ z = 0 := by
    intro φ hφ hφc hφsupport
    have hmom : ∀ z, z ∈ tsupport φ → ∀ i : Fin 3,
        dirDeriv (fun y => uδ y i) timeDir z
          + ∑ j : Fin 3, dirDeriv (fun y => Fδ y i j) (spatialDir j) z
          - ∑ j : Fin 3, dirDeriv (fun y => Gδ y i j) (spatialDir j) z
          + dirDeriv pδ (spatialDir i) z = 0 := by
      intro z hz i
      have hzcover : Metric.closedBall z δ ⊆ U := by
        have hδ3 : δ ≤ 3 * δ := by linarith only [hδ]
        exact (Metric.closedBall_subset_closedBall hδ3).trans
          (by simpa [U, B, J] using hcover z (hφsupport hz))
      have hEq := (hPDE z hzcover).1 i
      simpa [uδ, Fδ, Gδ, pδ, dirDeriv, energySpatialDir, energyTimeDir,
        spatialDir, timeDir, U, B, J] using hEq
    exact smoothMomentumEquation_tested huδSmooth hFδSmooth hGδSmooth hpSmooth
      hφ hφc hmom
  have hgradLocal : ∀ z ∈ tsupport ψ, ∀ i j : Fin 3,
      dirDeriv (fun y => uδ y i) (spatialDir j) z = Gδ z i j := by
    intro z hz i j
    have hweakGrad : ∀ φ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ Metric.closedBall z (3 * δ) →
        (∫ y in U, U.indicator (fun q => u q i) y *
          (fderiv ℝ φ y) (spatialDir j) ∂(volume : Measure (Vec3 × ℝ))) =
        -∫ y in U, U.indicator (fun q => Du q i j) y * φ y
          ∂(volume : Measure (Vec3 × ℝ)) := by
      intro φ hφ hφc hφsupport
      have hIBP := essLocal_sliceGradient_integrationByParts
        hu hDu henergy hgrad hφ hφc
        ((hφsupport.trans (hcover z hz))) i j
      have hleft : (∫ y in U, U.indicator (fun q => u q i) y *
          (fderiv ℝ φ y) (spatialDir j) ∂(volume : Measure (Vec3 × ℝ))) =
          ∫ y in U, u y i * spatialPartial (show ParabolicPoint → ℝ from φ) j y
            ∂(volume : Measure (Vec3 × ℝ)) := by
        apply setIntegral_congr_fun hUmeas
        intro y hy
        change U.indicator (fun q : Vec3 × ℝ => u q i) y *
            (fderiv ℝ φ y) (localEnergySpatialDir j) =
          u y i * spatialPartial (show ParabolicPoint → ℝ from φ) j y
        have hpartial := localEnergy_spatialPartial_eq_fderiv_apply hφ j y
        simp only [localEnergySpatialDir] at hpartial ⊢
        rw [hpartial.symm]
        rw [Set.indicator_of_mem hy]
      have hright : (∫ y in U, U.indicator (fun q => Du q i j) y * φ y
          ∂(volume : Measure (Vec3 × ℝ))) =
          ∫ y in U, Du y i j * φ y ∂(volume : Measure (Vec3 × ℝ)) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hUmeas] with y hy
        simp only [Set.indicator_of_mem hy]
      rw [hleft, hright]
      simpa [U, B, J] using hIBP
    have hcomm := spaceTimeMollify_fderiv_eq_of_local_weak
      hUopen ((huLoc i).locallyIntegrableOn U) ((hGLoc i j).locallyIntegrableOn U)
      hδ (hcover z hz) hweakGrad
    have hcomm' : (fderiv ℝ (spaceTimeMollify
        (U.indicator (fun q => u q i)) δ hδ) z) (spatialDir j) =
        spaceTimeMollify (U.indicator (fun q => Du q i j)) δ hδ z := by
      simpa [U, B, J, spatialDir, localEnergySpatialDir] using hcomm.2
    rw [← huIndicatorEq i] at hcomm'
    simpa [uδ, Gδ, dirDeriv, spatialDir, energySpatialDir, U, B, J] using hcomm'
  have hdivLocal : ∀ z ∈ tsupport ψ, ∑ i : Fin 3, Gδ z i i = 0 := by
    intro z hz
    have hzcover : Metric.closedBall z δ ⊆ U := by
      have hδ3 : δ ≤ 3 * δ := by linarith only [hδ]
      exact (Metric.closedBall_subset_closedBall hδ3).trans
        (by simpa [U, B, J] using hcover z hz)
    have hdiv := (hPDE z hzcover).2
    have hsum : ∑ i : Fin 3,
        dirDeriv (fun y => uδ y i) (spatialDir i) z = 0 := by
      simpa [uδ, dirDeriv, spatialDir, energySpatialDir, U, B, J] using hdiv
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (hgradLocal z hz i i).symm
  have henergyTest := smoothMomentum_tested_energy huδSmooth hψ hψc hweak hgradLocal
  have hbase := smoothEnergyTestIntegrand_integral_eq_base huδSmooth hRδSmooth
    hGδSmooth hpSmooth hψ hψc hgradLocal hdivLocal
  have hbase' : ∫ z, smoothEnergyTestIntegrand uδ Rδ Gδ pδ ψ z
        ∂(volume : Measure (Vec3 × ℝ)) =
      ∫ z, smoothEnergyBaseIntegrand uδ Rδ Gδ pδ ψ z
        ∂(volume : Measure (Vec3 × ℝ)) := by
    simpa [pδ] using hbase
  calc
    _ = ∫ z, smoothEnergyBaseIntegrand uδ Rδ Gδ pδ ψ z
        ∂(volume : Measure (Vec3 × ℝ)) := by
          simp [uδ, Fδ, Rδ, Gδ, pδ, U, B, J, huIndicatorEq]
    _ = 0 := by
      calc
        _ = ∫ z, smoothEnergyTestIntegrand uδ Rδ Gδ pδ ψ z
            ∂(volume : Measure (Vec3 × ℝ)) := hbase'.symm
      _ = 0 := henergyTest


end ESS
