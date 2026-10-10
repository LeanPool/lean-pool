/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.GeneratingInjective

/-!
Global generating transformations on a fixed source, their analytic inverses, and estimates
used by the next iteration step.
-/

@[expose] public section
noncomputable section
open Set Function Filter
open scoped NNReal Topology
namespace KamProject.Arnold1963

theorem canonicalAt_inverse_generating_branch {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {g : ComplexPhaseSpace n → ComplexPhaseSpace n} {y : ComplexPhaseSpace n}
    (hS : AnalyticAt ℂ S (g y)) (hg : AnalyticAt ℂ g y)
    (he : ∀ᶠ z in 𝓝 y, generatingOutput S (g z) = z) :
    CanonicalAt (generatingInput S ∘ g) y := by
  have hF := analyticAt_generatingInput hS
  have hH := analyticAt_generatingOutput hS
  have hd : (fderiv ℂ (generatingOutput S) (g y)).comp (fderiv ℂ g y) =
      ContinuousLinearMap.id ℂ _ := by
    rw [← fderiv_comp y hH.differentiableAt hg.differentiableAt]
    exact (Filter.EventuallyEq.fderiv_eq he).trans fderiv_id
  refine ⟨hF.differentiableAt.comp y hg.differentiableAt, ?_⟩
  intro v w
  rw [fderiv_comp y hF.differentiableAt hg.differentiableAt]
  change symplecticForm
    (fderiv ℂ (generatingInput S) (g y) (fderiv ℂ g y v))
    (fderiv ℂ (generatingInput S) (g y) (fderiv ℂ g y w)) = _
  rw [← generating_symplectic_identity hS]
  exact congrArg₂ symplecticForm
    (congrArg (fun L : ComplexPhaseSpace n →L[ℂ] ComplexPhaseSpace n => L v) hd)
    (congrArg (fun L : ComplexPhaseSpace n →L[ℂ] ComplexPhaseSpace n => L w) hd)

/-- The eroded phase source used to invert the generating input map. -/
def generatingSource {n : ℕ} (G U : Set (ComplexSpace n)) (r : ℝ≥0) := erosion (G ×ˢ U) r
/-- The asymmetric action-angle erosion retained by the generating transformation. -/
def generatingTarget {n : ℕ} (G U : Set (ComplexSpace n)) (r : ℝ≥0) :=
  erosion G (r + r) ×ˢ erosion U (r + r + r)

/-- A set-restricted inverse of the generating input map on its phase source. -/
def generatingInverse {n : ℕ} (S : ComplexPhaseSpace n → ℂ)
    (G U : Set (ComplexSpace n)) (r : ℝ≥0) :=
  invFunOn (generatingInput S) (generatingSource G U r)

/-- The generating output map composed with the inverse generating input map. -/
def generatingTransform {n : ℕ} (S : ComplexPhaseSpace n → ℂ)
    (G U : Set (ComplexSpace n)) (r : ℝ≥0) :=
  generatingOutput S ∘ generatingInverse S G U r

/-- The reverse generating transformation obtained by inverting the generating output map. -/
def generatingTransformInv {n : ℕ} (S : ComplexPhaseSpace n → ℂ)
    (G U : Set (ComplexSpace n)) (r : ℝ≥0) :=
  generatingInput S ∘ invFunOn (generatingOutput S) (generatingSource G U r)

/-- Analyticity and smallness data ensuring the generating transformation is well defined. -/
structure GeneratingData {n : ℕ} (S : ComplexPhaseSpace n → ℂ)
    (G U : Set (ComplexSpace n)) (r : ℝ≥0) (M : ℝ) : Prop where
  radius_pos : 0 < r
  analytic : AnalyticOnNhd ℂ S (G ×ˢ U)
  bounded : NormBoundOn S (G ×ˢ U) M
  small : M / r / r < 1 / 16

namespace GeneratingData
variable {n : ℕ} {S : ComplexPhaseSpace n → ℂ} {G U : Set (ComplexSpace n)}
  {r : ℝ≥0} {M : ℝ} (d : GeneratingData S G U r M)

include d

theorem input_injOn : InjOn (generatingInput S) (generatingSource G U r) :=
  (generating_injOn d.radius_pos d.analytic d.bounded d.small).1
theorem output_injOn : InjOn (generatingOutput S) (generatingSource G U r) :=
  (generating_injOn d.radius_pos d.analytic d.bounded d.small).2

theorem inverse_eq_of_input {x y : ComplexPhaseSpace n}
    (hx : x ∈ generatingSource G U r) (he : generatingInput S x = y) :
    generatingInverse S G U r y = x := by
  rw [← he]
  exact d.input_injOn.leftInvOn_invFunOn hx

theorem inverse_spec {y : ComplexPhaseSpace n} (hy : y ∈ generatingTarget G U r) :
    generatingInverse S G U r y ∈ erosion (G ×ˢ U) (r + r) ∧
      generatingInput S (generatingInverse S G U r y) = y ∧
      (generatingInverse S G U r y).1 = y.1 ∧
      (generatingInverse S G U r y).2 ∈ Metric.closedBall y.2 r := by
  obtain ⟨q, ⟨hq, he⟩, _⟩ := existsUnique_generating_root d.radius_pos d.analytic d.bounded
    (d.small.trans (by norm_num)) hy.1 hy.2
  have hx := generating_ball_buffer hy.1 hy.2 hq
  have hD : (y.1, q) ∈ generatingSource G U r :=
    erosion_antitone_radius _ (show r ≤ r + r from le_add_self) hx
  have hF : generatingInput S (y.1, q) = y := Prod.ext rfl he
  have hi : generatingInverse S G U r y = (y.1, q) := by
    rw [← hF]
    exact d.input_injOn.leftInvOn_invFunOn hD
  rw [hi]
  exact ⟨hx, hF, rfl, hq⟩

theorem inverse_mem {y : ComplexPhaseSpace n} (hy : y ∈ generatingTarget G U r) :
    generatingInverse S G U r y ∈ generatingSource G U r :=
  erosion_antitone_radius _ (show r ≤ r + r from le_add_self) (d.inverse_spec hy).1

theorem inverse_analytic_right {y : ComplexPhaseSpace n} (hy : y ∈ generatingTarget G U r) :
    AnalyticAt ℂ (generatingInverse S G U r) y ∧
      ∀ᶠ z in 𝓝 y, generatingInput S (generatingInverse S G U r z) = z := by
  have hs := d.inverse_spec hy
  have ha := d.analytic _ (erosion_subset _ _ hs.1)
  have hh := analytic_invFunOn d.input_injOn (erosion_mem_nhds d.radius_pos hs.1)
    (analyticAt_generatingInput ha)
    ((norm_fderiv_generatingInput_sub_id_le ha).trans_lt
      ((norm_fderiv_pGradient_le d.radius_pos d.analytic d.bounded hs.1).trans_lt
        (d.small.trans (by norm_num))))
  rw [hs.2.1] at hh
  exact ⟨hh.1, hh.2.2⟩

theorem transform_analytic : AnalyticOnNhd ℂ (generatingTransform S G U r)
    (generatingTarget G U r) := by
  intro y hy
  exact (analyticAt_generatingOutput (d.analytic _
    (erosion_subset _ _ (d.inverse_spec hy).1))).comp (d.inverse_analytic_right hy).1

theorem transform_canonical : CanonicalOn (generatingTransform S G U r)
    (generatingTarget G U r) := by
  intro y hy
  exact canonicalAt_generating_branch (d.analytic _
    (erosion_subset _ _ (d.inverse_spec hy).1))
    (d.inverse_analytic_right hy).1 (d.inverse_analytic_right hy).2

theorem transform_bounds {y : ComplexPhaseSpace n} (hy : y ∈ generatingTarget G U r) :
    ‖generatingTransform S G U r y - y‖ ≤ M / r ∧
      generatingTransform S G U r y ∈ G ×ˢ U := by
  obtain ⟨hx, he, hp, hq⟩ := d.inverse_spec hy
  have hpair : generatingInverse S G U r y = (y.1, (generatingInverse S G U r y).2) :=
    Prod.ext hp rfl
  rw [hpair] at he
  have hh := generating_root_bounds d.radius_pos d.analytic d.bounded
    (d.small.le.trans (by norm_num)) hy.1 hy.2 hq (congrArg Prod.snd he)
  change ‖generatingOutput S (generatingInverse S G U r y) - y‖ ≤ _ ∧
    generatingOutput S (generatingInverse S G U r y) ∈ G ×ˢ U
  rw [hpair]
  exact hh

theorem displacement_bound : NormBoundOn (fun y => generatingTransform S G U r y - y)
    (generatingTarget G U r) (M / r) :=
  ⟨div_nonneg d.bounded.nonneg r.coe_nonneg, fun _ hy => (d.transform_bounds hy).1⟩

theorem transform_mapsTo : MapsTo (generatingTransform S G U r)
    (generatingTarget G U r) (G ×ˢ U) := fun _ hy => (d.transform_bounds hy).2

theorem derivative_bound {y : ComplexPhaseSpace n} (hy : y ∈ generatingTarget G U r) :
    ‖fderiv ℂ (generatingTransform S G U r) y‖ ≤ 5 / 3 := by
  have hx := (d.inverse_spec hy).1
  exact norm_fderiv_generating_branch_le (d.analytic _ (erosion_subset _ _ hx))
    (d.inverse_analytic_right hy).1 (d.inverse_analytic_right hy).2
    ((norm_fderiv_pGradient_le d.radius_pos d.analytic d.bounded hx).trans
      (d.small.le.trans (by norm_num)))
    ((norm_fderiv_qGradient_le d.radius_pos d.analytic d.bounded hx).trans
      (d.small.le.trans (by norm_num)))

theorem transform_injOn : InjOn (generatingTransform S G U r) (generatingTarget G U r) := by
  intro y hy z hz he
  have hh := d.output_injOn (d.inverse_mem hy) (d.inverse_mem hz) he
  rw [← (d.inverse_spec hy).2.1, ← (d.inverse_spec hz).2.1, hh]

theorem transform_left_inv {y : ComplexPhaseSpace n} (hy : y ∈ generatingTarget G U r) :
    generatingTransformInv S G U r (generatingTransform S G U r y) = y := by
  change generatingInput S (invFunOn (generatingOutput S) (generatingSource G U r)
    (generatingOutput S (generatingInverse S G U r y))) = y
  rw [d.output_injOn.leftInvOn_invFunOn (d.inverse_mem hy)]
  exact (d.inverse_spec hy).2.1

theorem transformInv_analytic : AnalyticOnNhd ℂ (generatingTransformInv S G U r)
    (generatingTransform S G U r '' generatingTarget G U r) := by
  rintro z ⟨y, hy, rfl⟩
  have hx := (d.inverse_spec hy).1
  have ha := d.analytic _ (erosion_subset _ _ hx)
  have hh := analytic_invFunOn d.output_injOn (erosion_mem_nhds d.radius_pos hx)
    (analyticAt_generatingOutput ha)
    ((norm_fderiv_generatingOutput_sub_id_le ha).trans_lt
      ((norm_fderiv_qGradient_le d.radius_pos d.analytic d.bounded hx).trans_lt
        (d.small.trans (by norm_num))))
  exact ((show AnalyticAt ℂ (generatingInput S)
    (invFunOn (generatingOutput S) (generatingSource G U r)
      (generatingTransform S G U r y)) by
        change AnalyticAt ℂ (generatingInput S)
          (invFunOn (generatingOutput S) (generatingSource G U r)
            (generatingOutput S (generatingInverse S G U r y)))
        rw [hh.2.1]
        exact analyticAt_generatingInput ha)).comp hh.1

theorem transform_right_inv {z : ComplexPhaseSpace n}
    (hz : z ∈ generatingTransform S G U r '' generatingTarget G U r) :
    generatingTransform S G U r (generatingTransformInv S G U r z) = z := by
  obtain ⟨y, hy, rfl⟩ := hz
  rw [d.transform_left_inv hy]

theorem transformInv_canonical : CanonicalOn (generatingTransformInv S G U r)
    (generatingTransform S G U r '' generatingTarget G U r) := by
  rintro z ⟨y, hy, rfl⟩
  have hx := (d.inverse_spec hy).1
  have ha := d.analytic _ (erosion_subset _ _ hx)
  have hh := analytic_invFunOn d.output_injOn (erosion_mem_nhds d.radius_pos hx)
    (analyticAt_generatingOutput ha)
    ((norm_fderiv_generatingOutput_sub_id_le ha).trans_lt
      ((norm_fderiv_qGradient_le d.radius_pos d.analytic d.bounded hx).trans_lt
        (d.small.trans (by norm_num))))
  apply canonicalAt_inverse_generating_branch (g := invFunOn (generatingOutput S)
    (generatingSource G U r)) (y := generatingOutput S (generatingInverse S G U r y))
  · rw [hh.2.1]
    exact ha
  · exact hh.1
  · exact hh.2.2

theorem equations {y : ComplexPhaseSpace n} (hy : y ∈ generatingTarget G U r) :
    (generatingTransform S G U r y).1 = y.1 +
      qGradient S (y.1, (generatingTransform S G U r y).2) ∧
    y.2 = (generatingTransform S G U r y).2 +
      pGradient S (y.1, (generatingTransform S G U r y).2) := by
  have he := (d.inverse_spec hy).2.1
  have hp := (d.inverse_spec hy).2.2.1
  have hpair : generatingInverse S G U r y = (y.1, (generatingInverse S G U r y).2) :=
    Prod.ext hp rfl
  constructor
  · change (generatingInverse S G U r y).1 + qGradient S (generatingInverse S G U r y) = _
    simp only [generatingTransform, Function.comp_apply, generatingOutput]
    rw [hp, hpair]
  · change y.2 = (generatingInverse S G U r y).2 +
      pGradient S (y.1, (generatingInverse S G U r y).2)
    rw [← hpair]
    exact (congrArg Prod.snd he).symm

end GeneratingData
end KamProject.Arnold1963
