/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.PDE.DirichletRHS
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior

/-!
# High-contrast homogenization: Provider.Regularity.HarmonicAffineResidual

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport

open MeasureTheory

noncomputable section

/-- Subtracting an affine function from a weakly harmonic function on an open
cube preserves weak harmonicity, with the value and gradient representatives
kept explicit for the later affine-error calculation. -/
theorem WeakPoissonEquationOn.exists_sub_affine_harmonic
    {d : ℕ} (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (hu : WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0))
    (c : ℝ) (e : Vec d) :
    ∃ v : H1Function (openCubeSet Q),
      v.toFun = (fun x => u.toFun x - (c + vecDot e x)) ∧
      v.grad = (fun x => u.grad x - e) ∧
      WeakPoissonEquationOn (openCubeSet Q) v (fun _ => 0) := by
  let : MeasureTheory.IsFiniteMeasure
      (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let a : H1Function (openCubeSet Q) :=
    (H1Function.affineOnIsSobolevRegularDomain
      (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain e).addConst c
  let v : H1Function (openCubeSet Q) := u - a
  have hva : v.toFun = fun x => u.toFun x - (c + vecDot e x) := by
    funext x
    simp [v, a, vecDot, add_comm]
  have hvgrad : v.grad = fun x => u.grad x - e := by
    funext x
    ext i
    simp [v, a, sub_eq_add_neg]
  have hvharmonic : WeakPoissonEquationOn (openCubeSet Q) v (fun _ => 0) := by
    intro phi hphi hphi_compact hphi_sub
    let psi : H10Function (openCubeSet Q) :=
      H10Function.ofContDiff (isOpen_openCubeSet Q) hphi hphi_compact hphi_sub
    have hpsi_grad : psi.toH1Function.grad = euclideanGradient phi := rfl
    have hu_zero :
        ∫ x in openCubeSet Q,
            vecDot (u.grad x) (euclideanGradient phi x) ∂volume = 0 := by
      have htest := hu.test phi hphi hphi_compact hphi_sub
      simpa using htest
    have he_zero :
        ∫ x in openCubeSet Q,
            vecDot e (euclideanGradient phi x) ∂volume = 0 := by
      simpa [hpsi_grad] using integral_vecDot_const_zeroTraceGrad_eq_zero psi e
    have hu_int : IntegrableOn
        (fun x => vecDot (u.grad x) (euclideanGradient phi x))
        (openCubeSet Q) := by
      rw [← hpsi_grad]
      exact integrableOn_vecDot_of_memVectorL2
        u.grad_memVectorL2 psi.toH1Function.grad_memVectorL2
    have he_mem : MemVectorL2 (openCubeSet Q) (fun _ : Vec d => e) := by
      exact MeasureTheory.memLp_const
        (μ := volumeMeasureOn (openCubeSet Q)) (p := (2 : ENNReal)) e
    have he_int : IntegrableOn
        (fun x => vecDot e (euclideanGradient phi x)) (openCubeSet Q) := by
      rw [← hpsi_grad]
      exact integrableOn_vecDot_of_memVectorL2
        he_mem psi.toH1Function.grad_memVectorL2
    calc
      ∫ x in openCubeSet Q,
          vecDot (v.grad x) (euclideanGradient phi x) ∂volume =
          ∫ x in openCubeSet Q,
            (vecDot (u.grad x) (euclideanGradient phi x) -
              vecDot e (euclideanGradient phi x)) ∂volume := by
            apply MeasureTheory.setIntegral_congr_fun
              (measurableSet_openCubeSet Q)
            intro x _hx
            rw [hvgrad]
            simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
      _ = (∫ x in openCubeSet Q,
              vecDot (u.grad x) (euclideanGradient phi x) ∂volume) -
            ∫ x in openCubeSet Q,
              vecDot e (euclideanGradient phi x) ∂volume :=
          MeasureTheory.integral_sub hu_int he_int
      _ = 0 := by rw [hu_zero, he_zero, sub_zero]
      _ = ∫ x in openCubeSet Q, (fun _ : Vec d => (0 : ℝ)) x * phi x
          ∂volume := by simp
  exact ⟨v, hva, hvgrad, hvharmonic⟩

end

end HCPolySupport
