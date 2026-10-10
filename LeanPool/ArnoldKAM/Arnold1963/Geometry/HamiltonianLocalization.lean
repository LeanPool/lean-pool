/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.Localization
public import LeanPool.ArnoldKAM.Arnold1963.Step.Integrable
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
Nondegeneracy of the Hamiltonian Hessian supplies local frequency data. HamiltonianPatch
is an output format whose existence is proved before the perturbation is chosen.
-/

@[expose] public section
noncomputable section
open Set Filter Function Metric
open scoped Topology NNReal
namespace KamProject.Arnold1963

/-- The determinant of the derivative of the action-frequency map. -/
def hessianDet {n : ℕ} (H₀ : ComplexSpace n → ℂ) (p : ComplexSpace n) : ℂ :=
  LinearMap.det (fderiv ℂ (actionFrequency H₀) p).toLinearMap

theorem frequency_derivative_apply {n : ℕ} {H₀ : ComplexSpace n → ℂ}
    {p : ComplexSpace n} (ha : AnalyticAt ℂ H₀ p) (v : ComplexSpace n) (j : Fin n) :
    fderiv ℂ (actionFrequency H₀) p v j =
      fderiv ℂ (fderiv ℂ H₀) p v (Pi.single j 1) := by
  let L : (ComplexSpace n →L[ℂ] ℂ) →L[ℂ] ComplexSpace n :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1))
  exact congrArg (fun D : ComplexSpace n →L[ℂ] ComplexSpace n => D v j)
    ((L.hasFDerivAt.comp p ha.fderiv.differentiableAt.hasFDerivAt).fderiv)

theorem hessianDet_eq_matrix {n : ℕ} {H₀ : ComplexSpace n → ℂ}
    {p : ComplexSpace n} (ha : AnalyticAt ℂ H₀ p) :
    hessianDet H₀ p = Matrix.det (fun i j : Fin n =>
      fderiv ℂ (fderiv ℂ H₀) p (Pi.single j 1) (Pi.single i 1)) := by
  rw [hessianDet, ← LinearMap.det_toMatrix']
  congr 1
  ext i j
  exact frequency_derivative_apply ha (Pi.single j 1) i

theorem isUnit_frequency_derivative_iff {n : ℕ} (H₀ : ComplexSpace n → ℂ)
    (p : ComplexSpace n) :
    IsUnit (fderiv ℂ (actionFrequency H₀) p) ↔ hessianDet H₀ p ≠ 0 := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]
  rfl

/-- A compact Hamiltonian patch with an analytic frequency chart and uniform derivative bounds. -/
structure HamiltonianPatch (n : ℕ) (H₀ : ComplexSpace n → ℂ)
    (ambient : Set (ComplexSpace n)) where
  /-- The patch's compact complex action domain. -/
  domain : Set (ComplexSpace n)
  subset : domain ⊆ ambient
  /-- The real center of the patch's frequency polydisc. -/
  center : RealSpace n
  /-- The common coordinate radius of the patch's frequency polydisc. -/
  radius : ℝ
  radius_pos : 0 < radius
  /-- The analytic inverse of the action-frequency chart on its frequency polydisc. -/
  inverse : ComplexSpace n → ComplexSpace n
  chart : AnalyticFrequencyChart (actionFrequency H₀) inverse domain
    (realCenteredPolydisc center (fun _ => radius))
  analytic : AnalyticOnNhd ℂ H₀ domain
  conj : ∀ p ∈ domain, H₀ (conjVec p) = star (H₀ p)
  /-- The positive lower bound on the frequency derivative, chosen below one. -/
  lower : ℝ≥0
  /-- The upper bound on the frequency derivative, chosen above one. -/
  upper : ℝ≥0
  lower_pos : 0 < lower
  lower_lt_one : lower < 1
  upper_gt_one : 1 < upper
  derivative_lower : ∀ p ∈ domain, ∀ v,
    (lower : ℝ) * ‖v‖ ≤ ‖fderiv ℂ (actionFrequency H₀) p v‖
  derivative_upper : ∀ p ∈ domain, ‖fderiv ℂ (actionFrequency H₀) p‖ ≤ upper

namespace HamiltonianPatch
variable {n : ℕ} {H₀ : ComplexSpace n → ℂ} {ambient : Set (ComplexSpace n)}

/-- The frequency polydisc associated with the Hamiltonian patch. -/
def frequencyDomain (c : HamiltonianPatch n H₀ ambient) : Set (ComplexSpace n) :=
  realCenteredPolydisc c.center (fun _ => c.radius)

/-- The geometric type constant for the patch's frequency polydisc. -/
def typeConstant (c : HamiltonianPatch n H₀ ambient) : ℝ :=
  polydiscTypeConstant (fun _ : Fin n => c.radius)

theorem typeD (c : HamiltonianPatch n H₀ ambient) (hn : 0 < n) :
    TypeD c.frequencyDomain c.typeConstant :=
  realCenteredPolydisc_typeD hn c.center _ (fun _ => c.radius_pos)

theorem exists_at {x : RealSpace n} {V : Set (ComplexSpace n)}
    (hV : V ∈ 𝓝 (complexify x)) (hVG : V ⊆ ambient)
    (ha : AnalyticOnNhd ℂ H₀ ambient)
    (hc : ∀ p ∈ ambient, H₀ (conjVec p) = star (H₀ p))
    (hnd : hessianDet H₀ (complexify x) ≠ 0) :
    ∃ c : HamiltonianPatch n H₀ ambient,
      c.domain ⊆ V ∧ complexify x ∈ interior c.domain := by
  obtain ⟨a, ha0, hab⟩ := Metric.mem_nhds_iff.mp hV
  have hball : ball (complexify x) a ⊆ ambient := hab.trans hVG
  have hfc : ∀ p ∈ ball (complexify x) a,
      actionFrequency H₀ (conjVec p) = conjVec (actionFrequency H₀ p) := by
    intro p hp
    have hcp : conjVec p ∈ ball (complexify x) a := by
      change dist (star p) (complexify x) < a
      have hxstar : star (complexify x) = complexify x := conjVec_complexify x
      rw [← hxstar, dist_star_star]
      exact hp
    exact actionFrequency_conj_of_mem_nhds (ha _ (hball hp)) hc
      (mem_of_superset (isOpen_ball.mem_nhds hcp) hball)
  obtain ⟨g, G, r, hr, hG, hxG, hchart⟩ := exists_polydisc_frequency_chart x
    (ball_mem_nhds _ ha0) (analyticOnNhd_actionFrequency ha _ (hVG (mem_of_mem_nhds hV)))
    ((isUnit_frequency_derivative_iff H₀ _).mpr hnd) hfc
  obtain ⟨θ, Θ, hθ, hθ1, hΘ, hlo, hup⟩ := hchart.exists_derivative_bounds
  exact ⟨{
    domain := G
    subset := hG.trans hball
    center := realPart (actionFrequency H₀ (complexify x))
    radius := r
    radius_pos := hr
    inverse := g
    chart := hchart
    analytic := ha.mono (hG.trans hball)
    conj := fun p hp => hc p (hball (hG hp))
    lower := θ
    upper := Θ
    lower_pos := hθ
    lower_lt_one := hθ1
    upper_gt_one := hΘ
    derivative_lower := hlo
    derivative_upper := hup }, hG.trans hab, hxG⟩

theorem exists_finite_cover {K : Set (RealSpace n)} (hK : IsCompact K)
    (hKG : ∀ x ∈ K, complexify x ∈ interior ambient)
    (ha : AnalyticOnNhd ℂ H₀ ambient)
    (hc : ∀ p ∈ ambient, H₀ (conjVec p) = star (H₀ p))
    (hnd : ∀ x ∈ K, hessianDet H₀ (complexify x) ≠ 0) :
    ∃ s : Finset (HamiltonianPatch n H₀ ambient),
      K ⊆ ⋃ c ∈ s, realSlice (interior c.domain) := by
  classical
  have hex : ∀ x : K, ∃ c : HamiltonianPatch n H₀ ambient,
      complexify x.val ∈ interior c.domain := by
    intro x
    obtain ⟨c, _, hx⟩ := exists_at (mem_interior_iff_mem_nhds.mp (hKG x x.property))
      (Subset.refl ambient) ha hc (hnd x x.property)
    exact ⟨c, hx⟩
  choose c hcx using hex
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => realSlice (interior (c x).domain))
    (fun _ => isOpen_realSlice isOpen_interior) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hcx ⟨x, hx⟩⟩)
  refine ⟨s.image c, ?_⟩
  intro x hx
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hs hx)
  exact mem_iUnion₂.mpr ⟨c j, Finset.mem_image.mpr ⟨j, hj, rfl⟩, hxj⟩

end HamiltonianPatch
end KamProject.Arnold1963
