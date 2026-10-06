/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import LeanPool.CIVAxisymmetric.Identities.VorticityEquation
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution
public import LeanPool.CIVAxisymmetric.Reduction.ClassicalIBPIntegrability

/-!
# From the weak Navier–Stokes identities to pointwise equations: calculus core

For a field smooth on the open unit cylinder `Q` and a smooth test function compactly supported
in `Q`, spatial and temporal derivatives move across the integral, and a continuous function on
`Q` whose products with all such test functions integrate to zero vanishes on `Q`. As a first
application the tested divergence identity of a suitable weak solution that is smooth on `Q`
gives `div u = 0` pointwise. These are the first steps from the weak formulation to the classical
equations used in the proof of `lem:aniso:annulus`.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV




/-- A function continuous on `S` times a continuous compactly supported function whose support
lies in `S` is integrable on `Vec3 × ℝ`. -/
theorem integrable_mul_of_continuousOn_of_tsupport_subset_prod {S : Set (Vec3 × ℝ)}
    {g ρ : Vec3 × ℝ → ℝ} (hg : ContinuousOn g S) (hρ : Continuous ρ)
    (hρc : HasCompactSupport ρ) (hsupp : tsupport ρ ⊆ S) :
    Integrable (fun x => g x * ρ x) := by
  have hK : IsCompact (tsupport ρ) := hρc
  have h_intOn : IntegrableOn (fun x => g x * ρ x) (tsupport ρ) :=
    ((hg.mono hsupp).mul hρ.continuousOn).integrableOn_compact hK
  refine h_intOn.integrable_of_forall_notMem_eq_zero ?_
  intro x hx
  simp [image_eq_zero_of_notMem_tsupport hx]

/-- Integration by parts in a direction `v` of `Vec3 × ℝ` for a field smooth on an open set `S`
against a test function supported in `S`. -/
theorem integral_mul_fderiv_eq_neg_of_contDiffOn {S : Set (Vec3 × ℝ)} (hS : IsOpen S)
    {h ψ : Vec3 × ℝ → ℝ} (hh : ContDiffOn ℝ (⊤ : ℕ∞) h S)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ S)
    (v : Vec3 × ℝ) :
    ∫ x, h x * fderiv ℝ ψ x v = -∫ x, fderiv ℝ h x v * ψ x := by
  have : (volume : Measure (Vec3 × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_continuousOn hS hψc hsupp hh hψ hψc subset_rfl

/-- Integration by parts in the spatial direction `i` on the unit cylinder. -/
theorem integral_mul_spatialPartial_eq_neg_of_contDiffOn {h ψ : ParabolicPoint → ℝ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => h z) unitCylinder)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => ψ z))
    (hψc : HasCompactSupport (fun z : Vec3 × ℝ => ψ z))
    (hsupp : tsupport (fun z : Vec3 × ℝ => ψ z) ⊆ unitCylinder) (i : Fin 3) :
    ∫ z : Vec3 × ℝ, h z * spatialPartial ψ i z = -∫ z : Vec3 × ℝ, spatialPartial h i z * ψ z := by
  have key := integral_mul_fderiv_eq_neg_of_contDiffOn isOpen_unitCylinder_prod hh hψ hψc hsupp
    (basisVec i, 0)
  have e1 : ∀ z : Vec3 × ℝ, spatialPartial ψ i z = fderiv ℝ (fun w : Vec3 × ℝ => ψ w) z
    (basisVec i, 0) :=
    fun z => spatialPartial_eq_jointFDeriv ((hψ.differentiable (by simp)).differentiableAt) i
  have e2 : ∀ z ∈ unitCylinder, spatialPartial h i z =
      fderiv ℝ (fun w : Vec3 × ℝ => h w) z (basisVec i, 0) := fun z hz =>
    spatialPartial_eq_jointFDeriv ((hh.differentiableOn (by simp)).differentiableAt
      (isOpen_unitCylinder_prod.mem_nhds hz)) i
  simp_rw [e1]
  rw [key]
  congr 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun z => ?_)
  by_cases hz : z ∈ unitCylinder
  · simp only [e2 z hz]
  · have : ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hz (hsupp h'))
    simp [this]

/-- Integration by parts in time on the unit cylinder. -/
theorem integral_mul_timePartial_eq_neg_of_contDiffOn {h ψ : ParabolicPoint → ℝ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => h z) unitCylinder)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => ψ z))
    (hψc : HasCompactSupport (fun z : Vec3 × ℝ => ψ z))
    (hsupp : tsupport (fun z : Vec3 × ℝ => ψ z) ⊆ unitCylinder) :
    ∫ z : Vec3 × ℝ, h z * timePartial ψ z = -∫ z : Vec3 × ℝ, timePartial h z * ψ z := by
  have key := integral_mul_fderiv_eq_neg_of_contDiffOn isOpen_unitCylinder_prod hh hψ hψc hsupp
    ((0 : Vec3), (1 : ℝ))
  have e1 : ∀ z : Vec3 × ℝ, timePartial ψ z = fderiv ℝ (fun w : Vec3 × ℝ => ψ w) z (0, 1) :=
    fun z => timePartial_eq_jointFDeriv ((hψ.differentiable (by simp)).differentiableAt)
  have e2 : ∀ z ∈ unitCylinder, timePartial h z =
      fderiv ℝ (fun w : Vec3 × ℝ => h w) z (0, 1) := fun z hz =>
    timePartial_eq_jointFDeriv ((hh.differentiableOn (by simp)).differentiableAt
      (isOpen_unitCylinder_prod.mem_nhds hz))
  simp_rw [e1]
  rw [key]
  congr 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun z => ?_)
  by_cases hz : z ∈ unitCylinder
  · simp only [e2 z hz]
  · have : ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hz (hsupp h'))
    simp [this]

/-- The fundamental lemma of the calculus of variations on the unit cylinder, pointwise for a
continuous function. -/
theorem eq_zero_on_unitCylinder_of_forall_test {F : ParabolicPoint → ℝ}
    (hF : ContinuousOn (fun z : Vec3 × ℝ => F z) unitCylinder)
    (hzero : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ unitCylinder → ∫ z : Vec3 × ℝ, F z * ψ z = 0) :
    ∀ z ∈ unitCylinder, F z = 0 := by
  have hloc : LocallyIntegrableOn (fun z : Vec3 × ℝ => F z) unitCylinder :=
    hF.locallyIntegrableOn isOpen_unitCylinder_prod.measurableSet
  have hae := isOpen_unitCylinder_prod.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun g hg hgc hgs => by
      have := hzero g (hg.of_le (by simp)) hgc hgs
      simpa [smul_eq_mul, mul_comm] using this)
  intro z hz
  exact Measure.eqOn_open_of_ae_eq (μ := volume) (f := fun z : Vec3 × ℝ => F z)
    (g := fun _ => (0 : ℝ)) ((ae_restrict_iff' isOpen_unitCylinder_prod.measurableSet).mpr hae)
    isOpen_unitCylinder_prod hF continuousOn_const hz

/-- Against a test function supported in the unit cylinder, the integral over the cylinder is
the integral over all of space-time. -/
theorem integral_unitCylinder_eq_integral_of_tsupport {F ψ : Vec3 × ℝ → ℝ}
    (hsupp : tsupport ψ ⊆ unitCylinder) :
    ∫ z in unitCylinder, F z * ψ z = ∫ z, F z * ψ z := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)
  simp [image_eq_zero_of_notMem_tsupport (fun h' => hz (hsupp h'))]

/-- The spatial partial of a smooth test function is its joint derivative in the direction
`(eᵢ, 0)`. -/
theorem spatialPartial_test_eq_fderiv {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i : Fin 3) (z : Vec3 × ℝ) :
    spatialPartial ψ i z = fderiv ℝ ψ z (basisVec i, 0) :=
  spatialPartial_eq_jointFDeriv ((hψ.differentiable (by simp)).differentiableAt) i

/-- The time partial of a smooth test function is its joint derivative in the direction
`(0, 1)`. -/
theorem timePartial_test_eq_fderiv {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (z : Vec3 × ℝ) :
    timePartial ψ z = fderiv ℝ ψ z (0, 1) :=
  timePartial_eq_jointFDeriv ((hψ.differentiable (by simp)).differentiableAt)

/-- A function continuous on the unit cylinder times a directional derivative of a test
function supported in the cylinder is integrable. -/
theorem integrable_mul_spatialPartial_test {h : ParabolicPoint → ℝ} {ψ : Vec3 × ℝ → ℝ}
    (hh : ContinuousOn (fun z : Vec3 × ℝ => h z) unitCylinder)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ unitCylinder)
    (v : Vec3 × ℝ) :
    Integrable (fun z : Vec3 × ℝ => h z * fderiv ℝ ψ z v) :=
  integrable_mul_of_continuousOn_of_tsupport_subset_prod hh
    ((hψ.continuous_fderiv_apply (by simp)).comp (Continuous.prodMk continuous_id continuous_const))
    (hψc.fderiv_apply (𝕜 := ℝ) v) ((tsupport_fderiv_apply_subset ℝ v).trans hsupp)

/-- A suitable weak solution on the unit cylinder that is smooth there is pointwise
divergence free. -/
theorem classical_divergence_free_of_suitable {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ∀ z ∈ unitCylinder, ∑ j, spatialPartial (fun w => u w j) j z = 0 := by
  have hcomp : ∀ j : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z j) unitCylinder :=
    fun j => (contDiffOn_pi.mp hu) j
  apply eq_zero_on_unitCylinder_of_forall_test
  · refine continuousOn_finsetSum _ (fun j _ => ?_)
    exact (contDiffOn_spatialPartial (hcomp j) j).continuousOn
  · intro ψ hψ hψc hsupp
    have hdiv := hsol.2.2.2.2.2.2.1 ψ ⟨hψ, hψc, hsupp⟩
    have e : ∀ z : Vec3 × ℝ, (∑ i, u z i * fderiv ℝ ψ z (basisVec i, 0)) =
        ∑ i, u z i * spatialPartial ψ i z := fun z =>
      Finset.sum_congr rfl (fun i _ => by rw [spatialPartial_test_eq_fderiv hψ])
    have hdiv2 : ∫ z : Vec3 × ℝ in vec3Ball 0 1 ×ˢ Ioo (-1) 0,
        ∑ i, u z i * spatialPartial ψ i z = 0 := hdiv
    have hsupp2 : tsupport ψ ⊆ vec3Ball 0 1 ×ˢ Ioo (-1) 0 := hsupp
    have hdiv' : ∫ z : Vec3 × ℝ, ∑ i, u z i * fderiv ℝ ψ z (basisVec i, 0) = 0 := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := vec3Ball 0 1 ×ˢ Ioo (-1) 0)]
      · exact (integral_congr_ae (ae_of_all _ e)).trans hdiv2
      · intro z hz
        have hz' : fderiv ℝ ψ z = 0 :=
          Function.notMem_support.mp (fun h' => hz (hsupp2 (support_fderiv_subset ℝ h')))
        rw [hz']
        exact Finset.sum_eq_zero (fun i _ => by rw [zero_apply, mul_zero])
    rw [integral_finsetSum _ (fun i _ => integrable_mul_spatialPartial_test
      (hcomp i).continuousOn hψ hψc hsupp _)] at hdiv'
    have hibp : ∀ i : Fin 3, ∫ z : Vec3 × ℝ, u z i * fderiv ℝ ψ z (basisVec i, 0) =
        -∫ z : Vec3 × ℝ, spatialPartial (fun w => u w i) i z * ψ z := by
      intro i
      have := integral_mul_spatialPartial_eq_neg_of_contDiffOn (h := fun w => u w i)
        (ψ := fun w => ψ w) (hcomp i) hψ hψc hsupp i
      simpa [spatialPartial_test_eq_fderiv hψ] using this
    simp_rw [hibp] at hdiv'
    have hint : ∀ i ∈ (Finset.univ : Finset (Fin 3)), Integrable
        (fun z : Vec3 × ℝ => spatialPartial (fun w => u w i) i z * ψ z) := fun i _ =>
      integrable_mul_of_continuousOn_of_tsupport_subset_prod
        (contDiffOn_spatialPartial (hcomp i) i).continuousOn hψ.continuous hψc hsupp
    calc ∫ z : Vec3 × ℝ, (∑ j, spatialPartial (fun w => u w j) j z) * ψ z
        = ∫ z : Vec3 × ℝ, ∑ j, spatialPartial (fun w => u w j) j z * ψ z :=
          integral_congr_ae (ae_of_all _ (fun z => Finset.sum_mul _ _ _))
      _ = ∑ j, ∫ z : Vec3 × ℝ, spatialPartial (fun w => u w j) j z * ψ z :=
          integral_finsetSum _ hint
      _ = 0 := by
          rw [← neg_eq_zero, ← Finset.sum_neg_distrib]
          exact hdiv'

end CIV
