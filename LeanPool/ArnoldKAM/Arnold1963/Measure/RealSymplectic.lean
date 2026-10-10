/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Convergence.RealDerivative
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.MeasureTheory.Group.Prod

/-!
Real symplectic Jacobians. Real derivatives commute with complexification, and the symplectic
matrix determinant theorem gives the real change-of-variables identity.
-/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory Module
open scoped NNReal Topology ENNReal
namespace KamProject.Arnold1963

/-- The coordinate basis of unwrapped real action-angle phase space. -/
def realPhaseBasis (n : ℕ) : Basis (Fin n ⊕ Fin n) ℝ (RealPhaseCover n) :=
  (Pi.basisFun ℝ (Fin n)).prod (Pi.basisFun ℝ (Fin n))

theorem complexifyPhase_realPhaseBasis {n : ℕ} (j : Fin n ⊕ Fin n) :
    complexifyPhase (realPhaseBasis n j) = phaseDirection j := by
  cases j with
  | inl j =>
    ext i <;> by_cases hij : i = j <;>
      simp [realPhaseBasis, complexifyPhase, complexify,
        phaseDirection, pDirection, hij]
  | inr j =>
    ext i <;> by_cases hij : i = j <;>
      simp [realPhaseBasis, complexifyPhase, complexify,
        phaseDirection, qDirection, hij]

theorem realPhase_det_eq_one {n : ℕ}
    (L : ComplexPhaseSpace n →L[ℂ] ComplexPhaseSpace n)
    (A : RealPhaseCover n →L[ℝ] RealPhaseCover n)
    (hL : IsSymplecticLinear L.toLinearMap)
    (hA : ∀ v, complexifyPhase (A v) = L (complexifyPhase v)) :
    A.toLinearMap.det = 1 := by
  let M := LinearMap.toMatrix (realPhaseBasis n) (realPhaseBasis n) A.toLinearMap
  have hm : M.map Complex.ofRealHom = phaseLinearMatrix L.toLinearMap := by
    ext i j
    have hh := hA (realPhaseBasis n j)
    rw [complexifyPhase_realPhaseBasis] at hh
    cases i with
    | inl i =>
      simpa [M, Matrix.map_apply, LinearMap.toMatrix_apply, realPhaseBasis,
        phaseLinearMatrix, phaseCoordinate, complexifyPhase, complexify] using
        congrArg (fun z : ComplexPhaseSpace n => z.1 i) hh
    | inr i =>
      simpa [M, Matrix.map_apply, LinearMap.toMatrix_apply, realPhaseBasis,
        phaseLinearMatrix, phaseCoordinate, complexifyPhase, complexify] using
        congrArg (fun z : ComplexPhaseSpace n => z.2 i) hh
  have hd : (phaseLinearMatrix L.toLinearMap).det = 1 :=
    SymplecticGroup.det_eq_one (SymplecticGroup.mem_iff'.mpr
      ((symplectic_matrix_identity_iff_mathlib _).mp hL.matrix_identity))
  have he := congrArg Matrix.det hm
  change (Complex.ofRealHom.mapMatrix M).det = _ at he
  rw [← RingHom.map_det, hd] at he
  apply Complex.ofReal_injective
  simpa [M, LinearMap.det_toMatrix] using he

theorem realPhaseDerivative_commutes {n : ℕ}
    {f : ComplexPhaseSpace n → ComplexPhaseSpace n} {x : RealPhaseCover n}
    (hf : DifferentiableAt ℂ f (complexifyPhase x))
    (hr : ∀ᶠ y in 𝓝 x, complexifyPhase (realPhaseRestriction f y) =
      f (complexifyPhase y)) (v : RealPhaseCover n) :
    complexifyPhase (realPhaseDerivative (fderiv ℂ f (complexifyPhase x)) v) =
      fderiv ℂ f (complexifyPhase x) (complexifyPhase v) := by
  have ha := (complexifyPhaseCLM n).hasFDerivAt.comp x
    (hasFDerivAt_realPhaseRestriction hf)
  have hb := (hf.hasFDerivAt.restrictScalars ℝ).comp x (complexifyPhaseCLM n).hasFDerivAt
  have he := (ha.congr_of_eventuallyEq (hr.mono fun y hy => hy.symm)).unique hb
  exact congrArg (fun L : RealPhaseCover n →L[ℝ] ComplexPhaseSpace n => L v) he

namespace Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

theorem cumulative_real_near (s : ℕ) {x : RealPhaseCover n}
    (hx : x.1 ∈ realSlice (h.limitDomain b)) :
    ∀ᶠ y in 𝓝 x, complexifyPhase (realPhaseRestriction (h.cumulative b s) y) =
      h.cumulative b s (complexifyPhase y) := by
  have hz : complexifyPhase x ∈ h.limitPhase b :=
    h.commonPhase_subset b ⟨hx, complexify_mem_angleStrip _ _⟩
  have he := h.phase_buffer b s (h.limitPhase_subset b (s+1) hz)
  have hp : (0 : ℝ≥0) < beta δ₁ s := pow_pos (b.delta_step_pos s) 3
  have hne : h.phase b s ∈ 𝓝 (complexifyPhase x) :=
    Filter.mem_of_superset (Metric.closedBall_mem_nhds (complexifyPhase x) hp) he
  have hn := (complexifyPhaseCLM n).continuous.continuousAt hne
  filter_upwards [hn] with y hy
  exact h.cumulative_realPhase_value b s hy

theorem cumulative_real_det (s : ℕ) {x : RealPhaseCover n}
    (hx : x.1 ∈ realSlice (h.limitDomain b)) :
    (fderiv ℝ (realPhaseRestriction (h.cumulative b s)) x).toLinearMap.det = 1 := by
  have hz : complexifyPhase x ∈ h.limitPhase b :=
    h.commonPhase_subset b ⟨hx, complexify_mem_angleStrip _ _⟩
  have hs := h.limitPhase_subset b s hz
  have hf := (h.cumulative_analytic b s _ hs).differentiableAt
  rw [(hasFDerivAt_realPhaseRestriction hf).fderiv]
  exact realPhase_det_eq_one _ _ (h.cumulative_canonical b s _ hs).2
    (realPhaseDerivative_commutes hf (h.cumulative_real_near b s hx))

theorem cumulative_real_volume (s : ℕ) {K : Set (RealPhaseCover n)}
    (hK : MeasurableSet K)
    (hsub : ∀ x ∈ K, x.1 ∈ realSlice (h.limitDomain b)) :
    volume (realPhaseRestriction (h.cumulative b s) '' K) = volume K := by
  let : (volume : Measure (RealPhaseCover n)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hz (x : RealPhaseCover n) (hx : x ∈ K) :
      complexifyPhase x ∈ h.phase b s :=
    h.limitPhase_subset b s (h.commonPhase_subset b
      ⟨hsub x hx, complexify_mem_angleStrip _ _⟩)
  have hd (x : RealPhaseCover n) (hx : x ∈ K) :=
    hasFDerivAt_realPhaseRestriction (h.cumulative_analytic b s _ (hz x hx)).differentiableAt
  have hi : InjOn (realPhaseRestriction (h.cumulative b s)) K := by
    intro x hx y hy he
    have hec := congrArg complexifyPhase he
    rw [h.cumulative_realPhase_value b s (hz x hx),
      h.cumulative_realPhase_value b s (hz y hy)] at hec
    have hh := h.cumulative_injOn b s (hz x hx) (hz y hy) hec
    simpa using congrArg realPartPhase hh
  have he := lintegral_abs_det_fderiv_eq_addHaar_image volume hK
    (fun x hx => (hd x hx).differentiableAt.hasFDerivAt.hasFDerivWithinAt) hi
  rw [← he]
  calc
    _ = ∫⁻ _ in K, (1 : ℝ≥0∞) := by
      apply setLIntegral_congr_fun hK
      intro x hx
      simp [h.cumulative_real_det b s (hsub x hx)]
    _ = _ := by simp

end Iteration.InitialData
end KamProject.Arnold1963
