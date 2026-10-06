/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionBundleForce
public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatRoughSolution
public import LeanPool.EscauriazaSereginSverak.PartV.HeatOrbitSolutionWeak
public import LeanPool.EscauriazaSereginSverak.PartV.HeatOrbitSolutionTrace

/-!
# Ingredients for the local solution bundle

Elementary facts used to assemble the finite-energy weak solution of
`prop:pv-local-solution` from its heat part and its forced part: weak
gradients add, the time slices of the heat orbit and their gradients are
locally integrable, and the derivatives of a space-time test function are
square integrable on the slab.
-/

public section

open CKN

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Weak gradients on `ℝ³` of locally integrable functions add. -/
theorem hasWeakGradientOn_univ_add {u v : Vec3 → ℝ} {Du Dv : Vec3 → Vec3}
    (hu : LocallyIntegrable u volume) (hv : LocallyIntegrable v volume)
    (hDu : ∀ j, LocallyIntegrable (fun x => Du x j) volume)
    (hDv : ∀ j, LocallyIntegrable (fun x => Dv x j) volume)
    (h1 : CKN.HasWeakGradientOn (Set.univ : Set Vec3) u Du)
    (h2 : CKN.HasWeakGradientOn (Set.univ : Set Vec3) v Dv) :
    CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun x => u x + v x) (fun x => Du x + Dv x) := by
  intro j φ hφ hφc hφs
  have e1 := h1 j φ hφ hφc hφs
  have e2 := h2 j φ hφ hφc hφs
  simp only [Measure.restrict_univ] at e1 e2 ⊢
  have hdφc : Continuous (fun x => fderiv ℝ φ x (CKN.basisVec j)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφs : HasCompactSupport (fun x => fderiv ℝ φ x (CKN.basisVec j)) :=
    hφc.fderiv_apply (𝕜 := ℝ) _
  have i1 : Integrable (fun x => u x * fderiv ℝ φ x (CKN.basisVec j)) volume := by
    simpa only [smul_eq_mul] using hu.integrable_smul_right_of_hasCompactSupport hdφc hdφs
  have i2 : Integrable (fun x => v x * fderiv ℝ φ x (CKN.basisVec j)) volume := by
    simpa only [smul_eq_mul] using hv.integrable_smul_right_of_hasCompactSupport hdφc hdφs
  have i3 : Integrable (fun x => Du x j * φ x) volume := by
    simpa only [smul_eq_mul] using
      (hDu j).integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  have i4 : Integrable (fun x => Dv x j * φ x) volume := by
    simpa only [smul_eq_mul] using
      (hDv j).integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  have hl : (fun x => (u x + v x) * fderiv ℝ φ x (CKN.basisVec j)) =
      fun x => u x * fderiv ℝ φ x (CKN.basisVec j) + v x * fderiv ℝ φ x (CKN.basisVec j) := by
    funext x
    ring
  have hr : (fun x => (Du x + Dv x) j * φ x) = fun x => Du x j * φ x + Dv x j * φ x := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [hl, hr, integral_add i1 i2, integral_add i3 i4, e1, e2]
  ring

/-- At a positive time each component of the heat orbit of a square integrable
datum is continuous in space. -/
theorem heatOrbit_slice_continuous {a : Vec3 → Vec3} (ha : MemLp a 2 volume) {s : ℝ}
    (hs : 0 < s) (i : Fin 3) : Continuous (fun x : Vec3 => heatOrbit a (x, s) i) := by
  have hai : MemLp (fun y => a y i) 2 volume := memLp_pi_iff.1 ha i
  have hd : Differentiable ℝ (heatConv s (fun y => a y i)) := fun x =>
    (heatConv_hasFDerivAt_of_memLp hai hs x).differentiableAt
  exact hd.continuous

/-- At a positive time the spatial derivatives of the heat orbit of a square
integrable datum are bounded and measurable, hence locally integrable. -/
theorem heatOrbit_slice_grad_locallyIntegrable {a : Vec3 → Vec3} (ha : MemLp a 2 volume)
    {s : ℝ} (hs : 0 < s) (i j : Fin 3) :
    LocallyIntegrable (fun x => CKN.spatialDeriv (fun y => heatOrbit a (y, s) i) j x) volume := by
  have hai : MemLp (fun y => a y i) 2 volume := memLp_pi_iff.1 ha i
  obtain ⟨M, _, hM⟩ := heatConv_heatConvGrad_bound hs hai
  have hm : Measurable (fun x => CKN.spatialDeriv (fun y => heatOrbit a (y, s) i) j x) :=
    (ContinuousLinearMap.measurable_apply (CKN.basisVec j)).comp (measurable_fderiv ℝ _)
  have hb : MemLp (fun x => CKN.spatialDeriv (fun y => heatOrbit a (y, s) i) j x) ⊤ volume := by
    refine memLp_top_of_bound hm.aestronglyMeasurable M (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, heatOrbit_spatialDeriv_eq ha hs x i j]
    exact ((hM s le_rfl x).2 j)
  exact hb.locallyIntegrable le_top

/-- The derivatives of a scalar space-time test function are square integrable
on the slab. -/
theorem spaceTimeTest_derivs_memLp_two {φ : ParabolicPoint → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => φ p))
    (hφc : HasCompactSupport (fun p : Vec3 × ℝ => φ p)) (σ : ℝ) :
    MemLp (fun z => CKN.timePartial φ z) 2
        (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))) ∧
      ∀ j : Fin 3, MemLp (fun z => CKN.spatialPartial φ j z) 2
        (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))) := by
  let ψ : Vec3 × ℝ → ℝ := fun p => φ p
  have hDψc (v : Vec3 × ℝ) : Continuous (fun p => fderiv ℝ ψ p v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDψs (v : Vec3 × ℝ) : HasCompactSupport (fun p => fderiv ℝ ψ p v) :=
    hφc.fderiv_apply (𝕜 := ℝ) v
  have hmem (v : Vec3 × ℝ) : MemLp (fun p => fderiv ℝ ψ p v) 2
      (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))) :=
    ((hDψc v).memLp_of_hasCompactSupport (μ := (volume : Measure (Vec3 × ℝ))) (hDψs v)).restrict _
  constructor
  · have heq : (fun z : ParabolicPoint => CKN.timePartial φ z) = fun p => fderiv ℝ ψ p (0, 1) :=
      funext fun z => timePartial_eq_fderiv_apply hφ z.1 z.2
    rw [heq]
    exact hmem (0, 1)
  · intro j
    have heq : (fun z : ParabolicPoint => CKN.spatialPartial φ j z) =
        fun p => fderiv ℝ ψ p (CKN.basisVec j, 0) :=
      funext fun z => spatialPartial_eq_fderiv_apply hφ j z.1 z.2
    rw [heq]
    exact hmem (CKN.basisVec j, 0)

/-- The heat orbit of a datum in `J` and its spatial gradient are square
integrable on the slab. -/
theorem heatOrbit_memLp_two_slab {a : Vec3 → Vec3} (ha : IsInJ a) {σ : ℝ} (hσ : 0 < σ) :
    MemLp (heatOrbit a) 2 (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))) ∧
      MemLp (fun z : ParabolicPoint => fun i j =>
          CKN.spatialDeriv (fun y => heatOrbit a (y, z.2) i) j z.1)
        2 (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))) := by
  obtain ⟨hhm, hDhm⟩ := heatOrbit_grad_aestronglyMeasurable ha σ
  have hE := heatOrbit_energy_lintegral_lt_top ha hσ
  refine ⟨(memLp_two_iff_lintegral_enorm_sq hhm).2 ?_, (memLp_two_iff_lintegral_enorm_sq hDhm).2 ?_⟩
  · exact lt_of_le_of_lt (lintegral_mono fun z => le_self_add) hE
  · exact lt_of_le_of_lt (lintegral_mono fun z => le_add_self) hE

end ESS

end
