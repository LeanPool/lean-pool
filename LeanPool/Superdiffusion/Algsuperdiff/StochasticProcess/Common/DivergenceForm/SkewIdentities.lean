/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.Basic
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.Algebra.Membership

/-!
# Shared skew-field identities

Smooth-test density and finite-dimensional antisymmetry identities extracted from
scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
-/

@[expose] public section

namespace Algsuperdiff.StochasticProcess.Common.DivergenceForm

open HCPolySupport MeasureTheory Filter
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

private theorem integrable_mul_of_memScalarL2 {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : MemScalarL2 U f) (hg : MemScalarL2 U g) :
    Integrable (fun x => f x * g x) (volume.restrict U) := by
  simpa only [Pi.mul_apply] using! hf.integrable_mul hg

private theorem integral_vecDot_eq_sum_coord {U : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : ∀ i : Fin d, MemScalarL2 U fun x => F x i)
    (hG : ∀ i : Fin d, MemScalarL2 U fun x => G x i) :
    ∫ x in U, vecDot (F x) (G x) ∂volume =
      ∑ i : Fin d, ∫ x in U, F x i * G x i ∂volume := by
  rw [show (fun x : Vec d => vecDot (F x) (G x)) =
      fun x : Vec d => ∑ i : Fin d, F x i * G x i from funext fun _ => rfl]
  exact integral_finsetSum Finset.univ fun i _ => integrable_mul_of_memScalarL2 (hF i) (hG i)

/-- Smooth compact tests determine the zero-trace gradient pairing. -/
theorem integral_vecDot_congr_of_forall_smooth {U : Set (Vec d)} {P Q : Vec d → Vec d}
    (hP : ∀ i : Fin d, MemScalarL2 U fun x => P x i)
    (hQ : ∀ i : Fin d, MemScalarL2 U fun x => Q x i)
    (hsmooth : ∀ psi : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) psi → HasCompactSupport psi →
      tsupport psi ⊆ U →
      ∫ x in U, vecDot (P x) (euclideanGradient psi x) ∂volume =
        ∫ x in U, vecDot (Q x) (euclideanGradient psi x) ∂volume)
    (phi : H10Function U) :
    ∫ x in U, vecDot (P x) (phi.toH1Function.grad x) ∂volume =
      ∫ x in U, vecDot (Q x) (phi.toH1Function.grad x) ∂volume := by
  set Dn : ℕ → Vec d → Vec d := fun n => euclideanGradient (phi.approx n) with hDn_def
  have hDn : ∀ (n : ℕ) (i : Fin d), MemScalarL2 U fun x => Dn n x i := by
    intro n i
    exact memScalarL2_coord_of_memVectorL2
      (memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport
        (phi.approx_smooth n) (phi.approx_hasCompactSupport n)) i
  have hDlim : ∀ i : Fin d, MemScalarL2 U fun x => phi.toH1Function.grad x i :=
    fun i => phi.toH1Function.gradMemL2 i
  have hconv : ∀ i : Fin d, Tendsto (fun n => toScalarL2 (hDn n i)) atTop
      (nhds (toScalarL2 (hDlim i))) := by
    intro i
    refine tendsto_toScalarL2_of_tendsto_eLpNorm (fun n => hDn n i) (hDlim i) ?_
    simpa only [hDn_def, euclideanGradient, euclideanCoordDeriv, volumeMeasureOn]
      using phi.tendsto_approx_grad i
  have hPconv : Tendsto (fun n => ∑ i : Fin d, ∫ x in U, P x i * Dn n x i ∂volume) atTop
      (nhds (∑ i : Fin d, ∫ x in U, P x i * phi.toH1Function.grad x i ∂volume)) :=
    tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_integral_mul_of_tendsto_toScalarL2 (hP i) (fun n => hDn n i) (hDlim i) (hconv i)
  have hQconv : Tendsto (fun n => ∑ i : Fin d, ∫ x in U, Q x i * Dn n x i ∂volume) atTop
      (nhds (∑ i : Fin d, ∫ x in U, Q x i * phi.toH1Function.grad x i ∂volume)) :=
    tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_integral_mul_of_tendsto_toScalarL2 (hQ i) (fun n => hDn n i) (hDlim i) (hconv i)
  have heq : ∀ n : ℕ, (∑ i : Fin d, ∫ x in U, P x i * Dn n x i ∂volume) =
      ∑ i : Fin d, ∫ x in U, Q x i * Dn n x i ∂volume := by
    intro n
    rw [← integral_vecDot_eq_sum_coord hP (hDn n), ← integral_vecDot_eq_sum_coord hQ (hDn n)]
    exact hsmooth (phi.approx n) (phi.approx_smooth n) (phi.approx_hasCompactSupport n)
      (phi.approx_support_subset n)
  rw [integral_vecDot_eq_sum_coord hP hDlim, integral_vecDot_eq_sum_coord hQ hDlim]
  exact tendsto_nhds_unique (hPconv.congr' (EventuallyEq.of_eq (funext heq))) hQconv

/-- Contracting an antisymmetric matrix with a symmetric matrix gives zero. -/
theorem sum_sum_mul_eq_zero_of_skew_of_symm {K : Mat d}
    (hK : ∀ i j : Fin d, K j i = -K i j) {T : Fin d → Fin d → ℝ}
    (hT : ∀ i j : Fin d, T i j = T j i) :
    ∑ i : Fin d, ∑ j : Fin d, K i j * T i j = 0 := by
  have hpoint : ∀ i j : Fin d, K j i * T j i = -(K i j * T i j) := by
    intro i j
    rw [hK i j, ← hT i j]
    ring
  have hswap : ∑ i : Fin d, ∑ j : Fin d, K i j * T i j =
      ∑ i : Fin d, ∑ j : Fin d, K j i * T j i := Finset.sum_comm
  have hneg : ∑ i : Fin d, ∑ j : Fin d, K j i * T j i =
      -∑ i : Fin d, ∑ j : Fin d, K i j * T i j := by
    rw [show (∑ i : Fin d, ∑ j : Fin d, K j i * T j i) =
        ∑ i : Fin d, ∑ j : Fin d, -(K i j * T i j) from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpoint i j]
    simp only [Finset.sum_neg_distrib]
  have h2 := hswap.trans hneg
  linarith only [h2]

end

end Algsuperdiff.StochasticProcess.Common.DivergenceForm
