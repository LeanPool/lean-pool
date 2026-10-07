/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedMeasurableCurve
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureMeasurable
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierPhysicalRange

/-!
# Space-time representatives of the forced regularized solution

A continuous curve of real `L²` fields has a jointly measurable space-time
representative whose every time slice represents the curve. Its weak
gradient is represented by the limit of the gradients of spatial
mollifications, which is jointly measurable and whose slices are the weak
gradients of the slices wherever those exist. These are the velocity and
gradient fields of `lem:regularised-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

theorem exists_forcedCurveRep (U : ℝ → RealVectorL2) (hU : StronglyMeasurable U) :
    ∃ u : Vec3 × ℝ → Vec3, StronglyMeasurable u ∧
      ∀ t, (fun x => u (x, t)) =ᵐ[volume] realVectorL2Representative (U t) := by
  obtain ⟨Γ, hΓ, hrep⟩ := exists_jointRep_of_stronglyMeasurable (μ := volume) U hU
  let e : L2Vec3 ≃L[ℝ] Vec3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  refine ⟨fun z => e (Γ (WithLp.toLp 2 z.1, z.2)), ?_, fun t => ?_⟩
  · have hm : Measurable fun z : Vec3 × ℝ => (WithLp.toLp 2 z.1, z.2) :=
      (vec3ToL2Vec3_measurePreserving.measurable.comp measurable_fst).prodMk measurable_snd
    exact (e.continuous.comp_stronglyMeasurable (hΓ.comp_measurable hm))
  · have h := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae (hrep t)
    filter_upwards [h] with x hx
    simp only [realVectorL2Representative]
    rw [hx]
    rfl

/-- A jointly measurable space-time representative of a strongly measurable
curve of real `L²` fields, whose time slices represent the curve. -/
@[expose]
def forcedCurveRep (U : ℝ → RealVectorL2) (hU : StronglyMeasurable U) : Vec3 × ℝ → Vec3 :=
  Classical.choose (exists_forcedCurveRep U hU)

theorem forcedCurveRep_stronglyMeasurable (U : ℝ → RealVectorL2) (hU : StronglyMeasurable U) :
    StronglyMeasurable (forcedCurveRep U hU) :=
  (Classical.choose_spec (exists_forcedCurveRep U hU)).1

theorem forcedCurveRep_slice (U : ℝ → RealVectorL2) (hU : StronglyMeasurable U) (t : ℝ) :
    (fun x => forcedCurveRep U hU (x, t)) =ᵐ[volume] realVectorL2Representative (U t) :=
  (Classical.choose_spec (exists_forcedCurveRep U hU)).2 t

/-- The gradient field obtained as the limit of the gradients of the spatial
mollifications of the slices. -/
@[expose]
def forcedMollifiedGrad (u : Vec3 × ℝ → Vec3) (z : Vec3 × ℝ) (i j : Fin 3) : ℝ :=
  limUnder atTop fun n : ℕ =>
    fderiv ℝ (CKN.mollify (fun y => u (y, z.2) i) (1 / ((n : ℝ) + 1))
      (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))) z.1 (CKN.basisVec j)

theorem mollify_eq_integral {g : Vec3 → ℝ} {δ : ℝ} (hδ : 0 < δ) (x : Vec3) :
    CKN.mollify g δ hδ x = ∫ τ, CKN.mollifier δ hδ τ * g (x - τ) := by
  simp [CKN.mollify, convolution_def]

/-- At a fixed point, the mollification of the slices of a jointly measurable
field is measurable in time. -/
theorem measurable_mollify_slice {u : Vec3 × ℝ → ℝ} (hu : StronglyMeasurable u) {δ : ℝ}
    (hδ : 0 < δ) (x : Vec3) :
    Measurable fun t => CKN.mollify (fun y => u (y, t)) δ hδ x := by
  simp_rw [mollify_eq_integral hδ x]
  have hm : StronglyMeasurable (Function.uncurry fun (τ : Vec3) (t : ℝ) =>
      CKN.mollifier δ hδ τ * u (x - τ, t)) := by
    have h1 : Measurable fun q : Vec3 × ℝ => CKN.mollifier δ hδ q.1 :=
      (CKN.mollifier_contDiff (d := 3) hδ (n := 0)).continuous.measurable.comp measurable_fst
    have h2 : Measurable fun q : Vec3 × ℝ => u (x - q.1, q.2) :=
      hu.measurable.comp ((measurable_const.sub measurable_fst).prodMk measurable_snd)
    exact (h1.mul h2).stronglyMeasurable
  exact (StronglyMeasurable.integral_prod_left hm).measurable

/-- The mollified-gradient field of a jointly measurable field with locally
integrable slices is jointly measurable. -/
theorem forcedMollifiedGrad_stronglyMeasurable {u : Vec3 × ℝ → Vec3} (hu : StronglyMeasurable u)
    (hloc : ∀ t i, LocallyIntegrable (fun y => u (y, t) i) volume) (i j : Fin 3) :
    StronglyMeasurable fun z => forcedMollifiedGrad u z i j := by
  refine StronglyMeasurable.limUnder fun n => ?_
  let δ := 1 / ((n : ℝ) + 1)
  have hδ : 0 < δ := (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
  have hui : StronglyMeasurable fun z : Vec3 × ℝ => u z i :=
    (continuous_apply i).comp_stronglyMeasurable hu
  refine (measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : Vec3) (t : ℝ) => fderiv ℝ (CKN.mollify (fun y => u (y, t) i) δ hδ) x
      (CKN.basisVec j)) (fun t => ?_) (fun x => ?_)).stronglyMeasurable
  · exact ((CKN.mollify_contDiff (n := 1) hδ (hloc t i)).continuous_fderiv one_ne_zero).clm_apply
      continuous_const
  · let c : ℕ → ℝ := fun m => (m : ℝ) + 1
    have hc0 : Tendsto c atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hc : Tendsto (fun m => ‖c m‖) atTop atTop := tendsto_norm_atTop_atTop.comp hc0
    refine measurable_of_tendsto_metrizable (f := fun m t => c m •
      (CKN.mollify (fun y => u (y, t) i) δ hδ (x + (c m)⁻¹ • CKN.basisVec j) -
        CKN.mollify (fun y => u (y, t) i) δ hδ x)) (fun m => ?_) ?_
    · have h := ((measurable_mollify_slice hui hδ (x + (c m)⁻¹ • CKN.basisVec j)).sub
        (measurable_mollify_slice hui hδ x)).const_smul (c m)
      exact h
    · rw [tendsto_pi_nhds]
      intro t
      exact ((CKN.mollify_contDiff (n := 1) hδ (hloc t i)).differentiable one_ne_zero
        x).hasFDerivAt.lim (CKN.basisVec j) hc

/-- Where a slice has a locally integrable weak partial derivative, the
mollified-gradient field represents it. -/
theorem forcedMollifiedGrad_slice_ae_eq {u : Vec3 × ℝ → Vec3} {t : ℝ} {i j : Fin 3}
    (hloc : LocallyIntegrable (fun y => u (y, t) i) volume) {G : Vec3 → ℝ}
    (hG : LocallyIntegrable G volume)
    (hweak : CKN.HasWeakPartialDerivOn (Set.univ : Set Vec3) j (fun y => u (y, t) i) G) :
    (fun x => forcedMollifiedGrad u (x, t) i j) =ᵐ[volume] G := by
  have hconv := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure Vec3)) (l := atTop) (K := 2)
    (φ := fun n : ℕ => CKN.standardMollifier (d := 3) (1 / ((n : ℝ) + 1))
      (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
    (by simpa only [CKN.standardMollifier] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    (Eventually.of_forall fun n => by
      simp only [CKN.standardMollifier]
      linarith only [(by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))])
    hG
  filter_upwards [hconv] with x hx
  unfold forcedMollifiedGrad
  have heq : (fun n : ℕ => fderiv ℝ (CKN.mollify (fun y => u (y, t) i) (1 / ((n : ℝ) + 1))
      (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))) x (CKN.basisVec j)) =
      fun n : ℕ => CKN.mollify G (1 / ((n : ℝ) + 1))
        (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) x := by
    funext n
    exact CKN.fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn isOpen_univ hloc hG hweak
      (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) (Set.subset_univ _)
  simp only
  rw [heq]
  exact hx.limUnder_eq

end CKN.Leray

end
