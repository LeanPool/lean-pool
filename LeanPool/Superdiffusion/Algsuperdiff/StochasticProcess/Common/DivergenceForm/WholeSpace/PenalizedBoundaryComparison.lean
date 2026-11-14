/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.MaximumPrinciple
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.Pointwise
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PenalizedTail

/-!
# PenalizedBoundaryComparison

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Boundary-collar comparison for potential equations

The whole-space penalization interchange compares two Dirichlet solutions on
nested cubes.  This module isolates the weak maximum-principle step: if the
larger solution is at most `eps` on a collar of the smaller boundary, then it
is at most the smaller solution plus `eps` throughout the smaller domain.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped RealInnerProductSpace

noncomputable section

variable {d : ℕ} {U W : Set (Vec d)}

/-- Replace the pointwise representative of an `H¹` function without
changing its weak gradient or its equivalence class on the domain. -/
def h1FunctionWithAeRepresentative (u : H1Function U) (v : Vec d → ℝ)
    (hvu : v =ᵐ[volumeMeasureOn U] u.toFun) : H1Function U where
  toFun := v
  grad := u.grad
  memL2 := (memLp_congr_ae hvu.symm).mp u.memL2
  gradMemL2 := u.gradMemL2
  hasWeakGradient := by
    intro i phi hphi hsupp hsub
    have h := u.hasWeakGradient i phi hphi hsupp hsub
    rw [← h]
    apply integral_congr_ae
    filter_upwards [hvu] with x hx
    rw [hx]

/-- A scalar-forced equation is unchanged when both its solution and forcing
are replaced by almost-everywhere equal representatives. -/
theorem IsScalarForcedWeakSolution.withAeRepresentative
    {a : CoeffField d} {g g' : Vec d → ℝ} {u : H1Function U}
    (hu : IsScalarForcedWeakSolution a U g u) (v : Vec d → ℝ)
    (hvu : v =ᵐ[volumeMeasureOn U] u.toFun)
    (hgg' : g' =ᵐ[volumeMeasureOn U] g) :
    IsScalarForcedWeakSolution a U g'
      (h1FunctionWithAeRepresentative u v hvu) := by
  refine ⟨(memLp_congr_ae hgg'.symm).mp hu.1, ?_⟩
  intro phi
  calc
    (∫ x in U, vecDot (matVecMul (a x)
          ((h1FunctionWithAeRepresentative u v hvu).grad x))
        (phi.toH1Function.grad x) ∂volume) =
        ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume := rfl
    _ = ∫ x in U, g x * phi.toH1Function.toFun x ∂volume := hu.2 phi
    _ = ∫ x in U, g' x * phi.toH1Function.toFun x ∂volume := by
      apply integral_congr_ae
      filter_upwards [hgg'] with x hx
      rw [hx]

/-- A scalar-forced weak equation restricts to an open subdomain. -/
theorem IsScalarForcedWeakSolution.restrictToOpen
    {a : CoeffField d} {g : Vec d → ℝ} {u : H1Function W}
    (hu : IsScalarForcedWeakSolution a W g u) (hW : IsOpen W)
    (hU : IsOpen U) (hUW : U ⊆ W) :
    IsScalarForcedWeakSolution a U g (u.restrict hU hUW) := by
  refine ⟨hu.1.mono_measure (Measure.restrict_mono hUW le_rfl), ?_⟩
  intro phi
  have h := Decay.zerothOrderOn_restrict_of_isScalarForcedWeakSolution
    hW hU hUW hu phi
  simpa only [Pi.zero_apply, vecDot_zero_left, integral_zero, sub_zero] using h

/-- Subtracting two equations with the same source produces the homogeneous
potential equation for their difference. -/
theorem isScalarForcedWeakSolution_sub_same_potential
    {a : CoeffField d} {lam Lam alpha : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (q f : Vec d → ℝ) (u v : H1Function U)
    (hu : IsScalarForcedWeakSolution a U
      (fun x ↦ f x - (alpha + q x) * u.toFun x) u)
    (hv : IsScalarForcedWeakSolution a U
      (fun x ↦ f x - (alpha + q x) * v.toFun x) v) :
    IsScalarForcedWeakSolution a U
      (fun x ↦ -((alpha + q x) * (u - v).toFun x)) (u - v) := by
  have hsource : (fun x ↦ -((alpha + q x) * (u - v).toFun x)) =
      fun x ↦ (f x - (alpha + q x) * u.toFun x) -
        (f x - (alpha + q x) * v.toFun x) := by
    funext x
    simp only [H1Function.sub_toFun]
    ring
  refine ⟨?_, ?_⟩
  · rw [hsource]
    exact hu.1.sub hv.1
  · intro phi
    have hfluxU : Integrable
        (fun x ↦ vecDot (matVecMul (a x) (u.grad x))
          (phi.toH1Function.grad x)) (volumeMeasureOn U) :=
      integrableOn_vecDot_of_memVectorL2
        (memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2)
        phi.toH1Function.grad_memVectorL2
    have hfluxV : Integrable
        (fun x ↦ vecDot (matVecMul (a x) (v.grad x))
          (phi.toH1Function.grad x)) (volumeMeasureOn U) :=
      integrableOn_vecDot_of_memVectorL2
        (memVectorL2_matVecMul_of_isEllipticFieldOn hEll v.grad_memVectorL2)
        phi.toH1Function.grad_memVectorL2
    have hforceU := hu.1.integrable_mul phi.toH1Function.memL2
    have hforceV := hv.1.integrable_mul phi.toH1Function.memL2
    calc
      (∫ x in U, vecDot (matVecMul (a x) ((u - v).grad x))
          (phi.toH1Function.grad x) ∂volume) =
          (∫ x in U, vecDot (matVecMul (a x) (u.grad x))
            (phi.toH1Function.grad x) ∂volume) -
          ∫ x in U, vecDot (matVecMul (a x) (v.grad x))
            (phi.toH1Function.grad x) ∂volume := by
        rw [← integral_sub hfluxU hfluxV]
        apply integral_congr_ae
        filter_upwards with x
        simp only [H1Function.sub_grad, matVecMul, vecDot, Pi.sub_apply,
          mul_sub, sub_mul, Finset.sum_sub_distrib]
      _ = (∫ x in U, (f x - (alpha + q x) * u.toFun x) *
            phi.toH1Function.toFun x ∂volume) -
          ∫ x in U, (f x - (alpha + q x) * v.toFun x) *
            phi.toH1Function.toFun x ∂volume := by rw [hu.2 phi, hv.2 phi]
      _ = ∫ x in U,
          ((f x - (alpha + q x) * u.toFun x) -
            (f x - (alpha + q x) * v.toFun x)) *
              phi.toH1Function.toFun x ∂volume := by
        change (∫ x, (f x - (alpha + q x) * u.toFun x) *
            phi.toH1Function.toFun x ∂volumeMeasureOn U) -
            (∫ x, (f x - (alpha + q x) * v.toFun x) *
              phi.toH1Function.toFun x ∂volumeMeasureOn U) =
            ∫ x, ((f x - (alpha + q x) * u.toFun x) -
              (f x - (alpha + q x) * v.toFun x)) *
                phi.toH1Function.toFun x ∂volumeMeasureOn U
        trans ∫ x,
            (((fun y ↦ f y - (alpha + q y) * u.toFun y) *
                phi.toH1Function.toFun) x -
              ((fun y ↦ f y - (alpha + q y) * v.toFun y) *
                phi.toH1Function.toFun) x) ∂volumeMeasureOn U
        · exact (integral_sub hforceU hforceV).symm
        · apply integral_congr_ae
          filter_upwards with x
          simp only [Pi.mul_apply]
          ring
      _ = ∫ x in U, -((alpha + q x) * (u - v).toFun x) *
          phi.toH1Function.toFun x ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [H1Function.sub_toFun]
        ring

/-- A homogeneous potential difference with a compactly supported positive
part is bounded by its boundary-collar level. -/
theorem ae_le_add_of_homogeneous_difference_boundary
    (hU : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam alpha eps : ℝ} (halpha : 0 < alpha)
    (heps : 0 ≤ eps) (hEll : IsEllipticFieldOn lam Lam U a)
    {q : Vec d → ℝ} (hq : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ q x)
    (u v : H1Function U)
    (hsol : IsScalarForcedWeakSolution a U
      (fun x ↦ -((alpha + q x) * (u - v).toFun x)) (u - v))
    {K : Set (Vec d)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hcollar : ∀ x, x ∉ K → u.toFun x ≤ v.toFun x + eps) :
    ∀ᵐ x ∂volumeMeasureOn U, u.toFun x ≤ v.toFun x + eps := by
  obtain ⟨p, hp, -⟩ := exists_h1_max_sub_const hU (u - v) eps
  have hpzero : ∀ x, x ∉ K → p.toFun x = 0 := by
    intro x hx
    rw [congrFun hp x]
    exact max_eq_right (sub_nonpos.mpr (by
      simp only [H1Function.sub_toFun]
      exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using hcollar x hx)))
  have htrace : MemH10 U (fun x ↦ max ((u - v).toFun x - eps) 0) := by
    rw [← hp]
    exact memH10_of_compactSupport hU p hK hKU hpzero
  have hle := Decay.ae_le_of_positivePart_zeroTrace hU halpha heps hEll hq hsol htrace
  filter_upwards [hle] with x hx
  have hx' : u.toFun x ≤ eps + v.toFun x := by
    exact sub_le_iff_le_add.mp (by simpa only [H1Function.sub_toFun] using hx)
  simpa only [add_comm] using hx'

/-- Continuous representatives upgrade the boundary-collar comparison from
almost everywhere to every point of the open domain. -/
theorem le_add_of_homogeneous_difference_boundary
    (hU : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam alpha eps : ℝ} (halpha : 0 < alpha)
    (heps : 0 ≤ eps) (hEll : IsEllipticFieldOn lam Lam U a)
    {q : Vec d → ℝ} (hq : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ q x)
    (u v : H1Function U) (hu : ContinuousOn u.toFun U)
    (hv : ContinuousOn v.toFun U)
    (hsol : IsScalarForcedWeakSolution a U
      (fun x ↦ -((alpha + q x) * (u - v).toFun x)) (u - v))
    {K : Set (Vec d)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hcollar : ∀ x, x ∉ K → u.toFun x ≤ v.toFun x + eps) :
    ∀ x ∈ U, u.toFun x ≤ v.toFun x + eps := by
  exact le_of_ae_le_of_continuousOn hU.isOpen hu (hv.add continuousOn_const)
    (ae_le_add_of_homogeneous_difference_boundary hU halpha heps hEll hq
      u v hsol hK hKU hcollar)

end

end DivergenceFormProcess.Form
