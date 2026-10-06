/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalAssemblySupport
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedConvolutionSmooth
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMomentum
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SpatialDerivSupport

/-!
# Spatial integration by parts for the momentum pairing flux

On a positive-time slice, the flux of the weak momentum identity paired with
a compactly supported smooth spatial field `η`,
`∫ (J_ε u)_j u_i ∂_j η_i − ∂_j u_i ∂_j η_i + p ∂_i η_i`,
equals the pairing `∫ (Δu − (J_ε u · ∇) u − ∇p) · η` of the right-hand side
`regR12TimeRHS`. The transport term uses that the mollified velocity is
smooth and divergence free on each slice.
-/

public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

/-- Integration by parts against a compactly supported smooth test, in the
form `∫ (F ∂_j q + (∂_j F) q) = 0`, together with integrability of the
integrand. -/
private theorem regularisedR12TimeIBP_integral_eq_zero
    {F DF q : Vec3 → ℝ} (j : Fin 3)
    (hFc : Continuous F) (hFdiff : ∀ x, DifferentiableAt ℝ F x)
    (hFd : ∀ x, (fderiv ℝ F x) (basisVec j) = DF x)
    (hDFc : Continuous DF)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hqc : HasCompactSupport q) :
    Integrable (fun x : Vec3 => F x * spatialDeriv q j x + DF x * q x) ∧
      ∫ x : Vec3, (F x * spatialDeriv q j x + DF x * q x) = 0 := by
  have hqdc : Continuous (spatialDeriv q j) :=
    (contDiff_spatialDeriv_smooth hq j).continuous
  have hqds : HasCompactSupport (spatialDeriv q j) :=
    hqc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  have h1 : Integrable (fun x : Vec3 => F x * spatialDeriv q j x) :=
    (hFc.mul hqdc).integrable_of_hasCompactSupport hqds.mul_left
  have h2 : Integrable (fun x : Vec3 => DF x * q x) :=
    (hDFc.mul hq.continuous).integrable_of_hasCompactSupport hqc.mul_left
  have h3 : Integrable (fun x : Vec3 => F x * q x) :=
    (hFc.mul hq.continuous).integrable_of_hasCompactSupport hqc.mul_left
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Vec3)) (f := F) (g := q) (v := basisVec j)
    (by simpa only [hFd] using h2) h1 h3
    (fun x _ => hFdiff x) (fun x _ => (hq.differentiable (by norm_num)) x)
  refine ⟨h1.add h2, ?_⟩
  rw [integral_add h1 h2]
  have hIBP' : ∫ x : Vec3, F x * spatialDeriv q j x = -∫ x : Vec3, DF x * q x := by
    simpa only [spatialDeriv, hFd] using hIBP
  rw [hIBP', neg_add_cancel]

/-- The component identity on one slice, for abstract fields: a divergence-free
`C¹` transport field, a differentiable component with differentiable
continuous first derivatives, and a differentiable pressure. -/
private theorem regularisedR12TimeIBP_component_abstract
    {J : Fin 3 → Vec3 → ℝ} {U P dP q : Vec3 → ℝ} {dU d2U : Fin 3 → Vec3 → ℝ}
    (i : Fin 3)
    (hJ : ∀ j : Fin 3, ContDiff ℝ 1 (J j))
    (hdiv : ∀ x : Vec3, ∑ j : Fin 3, (fderiv ℝ (J j) x) (basisVec j) = 0)
    (hUdiff : ∀ x : Vec3, DifferentiableAt ℝ U x)
    (hUd : ∀ j : Fin 3, ∀ x : Vec3, (fderiv ℝ U x) (basisVec j) = dU j x)
    (hdUc : ∀ j : Fin 3, Continuous (dU j))
    (hdUdiff : ∀ j : Fin 3, ∀ x : Vec3, DifferentiableAt ℝ (dU j) x)
    (hd2 : ∀ j : Fin 3, ∀ x : Vec3, (fderiv ℝ (dU j) x) (basisVec j) = d2U j x)
    (hd2c : ∀ j : Fin 3, Continuous (d2U j))
    (hPdiff : ∀ x : Vec3, DifferentiableAt ℝ P x)
    (hPd : ∀ x : Vec3, (fderiv ℝ P x) (basisVec i) = dP x)
    (hdPc : Continuous dP)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hqc : HasCompactSupport q) :
    Integrable (fun x : Vec3 =>
      (∑ j : Fin 3, J j x * U x * spatialDeriv q j x)
        - (∑ j : Fin 3, dU j x * spatialDeriv q j x)
        + P x * spatialDeriv q i x) ∧
    Integrable (fun x : Vec3 =>
      ((∑ j : Fin 3, d2U j x) - (∑ j : Fin 3, J j x * dU j x) - dP x) * q x) ∧
    (∫ x : Vec3,
      (∑ j : Fin 3, J j x * U x * spatialDeriv q j x)
        - (∑ j : Fin 3, dU j x * spatialDeriv q j x)
        + P x * spatialDeriv q i x) =
      ∫ x : Vec3,
        ((∑ j : Fin 3, d2U j x) - (∑ j : Fin 3, J j x * dU j x) - dP x) * q x := by
  have hUc : Continuous U := continuous_iff_continuousAt.2 fun x => (hUdiff x).continuousAt
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun x => (hPdiff x).continuousAt
  have hJc (j : Fin 3) : Continuous (J j) := (hJ j).continuous
  have hJdiff (j : Fin 3) (x : Vec3) : DifferentiableAt ℝ (J j) x :=
    ((hJ j).differentiable (by norm_num)) x
  have hdJc (j : Fin 3) : Continuous (fun x : Vec3 => (fderiv ℝ (J j) x) (basisVec j)) :=
    ((hJ j).continuous_fderiv (by norm_num)).clm_apply continuous_const
  -- the three families of integration by parts
  have hX (j : Fin 3) := regularisedR12TimeIBP_integral_eq_zero (F := fun x => J j x * U x)
    (DF := fun x => (fderiv ℝ (J j) x) (basisVec j) * U x + J j x * dU j x) j
    ((hJc j).mul hUc) (fun x => (hJdiff j x).mul (hUdiff x))
    (fun x => by
      rw [fderiv_fun_mul (hJdiff j x) (hUdiff x)]
      simp only [add_apply, smul_apply, smul_eq_mul,
        hUd j x]
      ring)
    (((hdJc j).mul hUc).add ((hJc j).mul (hdUc j))) hq hqc
  have hY (j : Fin 3) := regularisedR12TimeIBP_integral_eq_zero (F := dU j) (DF := d2U j) j
    (hdUc j) (hdUdiff j) (hd2 j) (hd2c j) hq hqc
  have hZ := regularisedR12TimeIBP_integral_eq_zero (F := P) (DF := dP) i
    hPc hPdiff hPd hdPc hq hqc
  have hRint : Integrable (fun x : Vec3 =>
      ((∑ j : Fin 3, d2U j x) - (∑ j : Fin 3, J j x * dU j x) - dP x) * q x) := by
    have hc : Continuous (fun x : Vec3 =>
        (∑ j : Fin 3, d2U j x) - (∑ j : Fin 3, J j x * dU j x) - dP x) :=
      ((continuous_finsetSum _ fun j _ => hd2c j).sub
        (continuous_finsetSum _ fun j _ => (hJc j).mul (hdUc j))).sub hdPc
    exact (hc.mul hq.continuous).integrable_of_hasCompactSupport hqc.mul_left
  let W : Vec3 → ℝ := fun x =>
    (∑ j : Fin 3, (J j x * U x * spatialDeriv q j x +
        ((fderiv ℝ (J j) x) (basisVec j) * U x + J j x * dU j x) * q x))
      - (∑ j : Fin 3, (dU j x * spatialDeriv q j x + d2U j x * q x))
      + (P x * spatialDeriv q i x + dP x * q x)
  have hXint : Integrable (fun x : Vec3 => ∑ j : Fin 3, (J j x * U x * spatialDeriv q j x +
      ((fderiv ℝ (J j) x) (basisVec j) * U x + J j x * dU j x) * q x)) :=
    integrable_finsetSum _ fun j _ => (hX j).1
  have hYint : Integrable (fun x : Vec3 =>
      ∑ j : Fin 3, (dU j x * spatialDeriv q j x + d2U j x * q x)) :=
    integrable_finsetSum _ fun j _ => (hY j).1
  have hXY : Integrable (fun x : Vec3 =>
      (∑ j : Fin 3, (J j x * U x * spatialDeriv q j x +
        ((fderiv ℝ (J j) x) (basisVec j) * U x + J j x * dU j x) * q x))
      - (∑ j : Fin 3, (dU j x * spatialDeriv q j x + d2U j x * q x))) := hXint.sub hYint
  have hWint : Integrable W := hXY.add hZ.1
  have hWzero : ∫ x : Vec3, W x = 0 := by
    change ∫ x : Vec3, ((∑ j : Fin 3, (J j x * U x * spatialDeriv q j x +
        ((fderiv ℝ (J j) x) (basisVec j) * U x + J j x * dU j x) * q x))
      - (∑ j : Fin 3, (dU j x * spatialDeriv q j x + d2U j x * q x))
      + (P x * spatialDeriv q i x + dP x * q x)) = 0
    rw [integral_add hXY hZ.1, integral_sub hXint hYint,
      integral_finsetSum _ fun j _ => (hX j).1, integral_finsetSum _ fun j _ => (hY j).1,
      hZ.2]
    simp only [fun j => (hX j).2, fun j => (hY j).2, Finset.sum_const_zero, sub_zero, add_zero]
  have hpt : (fun x : Vec3 =>
      (∑ j : Fin 3, J j x * U x * spatialDeriv q j x)
        - (∑ j : Fin 3, dU j x * spatialDeriv q j x)
        + P x * spatialDeriv q i x) = fun x =>
      ((∑ j : Fin 3, d2U j x) - (∑ j : Fin 3, J j x * dU j x) - dP x) * q x + W x := by
    funext x
    have hd := hdiv x
    simp only [W]
    simp only [Fin.sum_univ_three] at hd ⊢
    linear_combination (-(U x * q x)) * hd
  refine ⟨?_, hRint, ?_⟩
  · rw [hpt]
    exact hRint.add hWint
  · rw [hpt, integral_add hRint hWint, hWzero, add_zero]

/-- The component identity on a positive-time slice for the regularized
fields. -/
private theorem regularisedR12TimeIBP_component
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (hD : ∀ i j : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => u y i) j z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDD : ∀ i j k : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDp : ∀ i : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => p y) i z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hUdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i : Fin 3,
      DifferentiableAt ℝ (fun x : Vec3 => u (x, z.2) i) z.1)
    (hDdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i j : Fin 3,
      DifferentiableAt ℝ
        (fun x : Vec3 => spatialPartial (fun y => u y i) j (x, z.2)) z.1)
    (hPdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1)
    (t : ℝ) (ht : 0 < t)
    (hSliceT : MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hDivT : CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, t)))
    (i : Fin 3) (q : Vec3 → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqc : HasCompactSupport q) :
    Integrable (fun x : Vec3 =>
      (∑ j : Fin 3, regUniformMollifiedVelocity ρ ε hε u (x, t) j * u (x, t) i *
          spatialDeriv q j x)
        - (∑ j : Fin 3, spatialPartial (fun y => u y i) j (x, t) * spatialDeriv q j x)
        + p (x, t) * spatialDeriv q i x) ∧
    Integrable (fun x : Vec3 => regR12TimeRHS ρ ε hε u p (x, t) i * q x) ∧
    (∫ x : Vec3,
      (∑ j : Fin 3, regUniformMollifiedVelocity ρ ε hε u (x, t) j * u (x, t) i *
          spatialDeriv q j x)
        - (∑ j : Fin 3, spatialPartial (fun y => u y i) j (x, t) * spatialDeriv q j x)
        + p (x, t) * spatialDeriv q i x) =
      ∫ x : Vec3, regR12TimeRHS ρ ε hε u p (x, t) i * q x := by
  have hmem (x : Vec3) : ((x, t) : ParabolicPoint) ∈
      spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) := ⟨Set.mem_univ _, ht⟩
  have hslice {F : ParabolicPoint → ℝ}
      (hF : ContinuousOn F (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) :
      Continuous (fun x : Vec3 => F (x, t)) := by
    have hprod := regUniform_continuousOn_pullback
      (Sprod := Set.univ ×ˢ Set.Ioi 0) hF (fun z hz => ⟨Set.mem_univ _, hz.2⟩)
    exact hprod.comp_continuous (continuous_id.prodMk continuous_const)
      (fun x => ⟨Set.mem_univ _, ht⟩)
  have hJvec : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t)) :=
    regUniformMollifiedInitial_contDiff_of_memLp ρ ε hε hSliceT
  have hJ (j : Fin 3) : ContDiff ℝ 1
      (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) j) :=
    (hJvec.continuousLinearMap_comp (ContinuousLinearMap.proj (R := ℝ) j)).of_le
      (by exact_mod_cast le_top)
  exact regularisedR12TimeIBP_component_abstract
    (J := fun j x => regUniformMollifiedVelocity ρ ε hε u (x, t) j)
    (U := fun x => u (x, t) i) (P := fun x => p (x, t))
    (dP := fun x => spatialPartial (fun y => p y) i (x, t))
    (dU := fun j x => spatialPartial (fun y => u y i) j (x, t))
    (d2U := fun j x => spatialPartial (fun y => spatialPartial (fun x => u x i) j y) j (x, t))
    i hJ (regUniform_mollified_velocity_divergence_eq_zero ρ ε hε u t hDivT)
    (fun x => hUdiff (x, t) (hmem x) i) (fun _ _ => rfl)
    (fun j => hslice (hD i j)) (fun j x => hDdiff (x, t) (hmem x) i j) (fun _ _ => rfl)
    (fun j => hslice (hDD i j j)) (fun x => hPdiff (x, t) (hmem x)) (fun _ => rfl)
    (hslice (hDp i)) hq hqc

/-- Spatial integration by parts for the momentum pairing flux: on a
positive-time slice, the flux of the weak momentum identity against a
compactly supported smooth field `η` equals the pairing of `η` with the
right-hand side `Δu − (J_ε u · ∇) u − ∇p` (`thm:regularised`). -/
theorem regularisedR12TimeIBP_flux_eq
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (hD : ∀ i j : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => u y i) j z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDD : ∀ i j k : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDp : ∀ i : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => p y) i z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hUdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i : Fin 3,
      DifferentiableAt ℝ (fun x : Vec3 => u (x, z.2) i) z.1)
    (hDdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i j : Fin 3,
      DifferentiableAt ℝ
        (fun x : Vec3 => spatialPartial (fun y => u y i) j (x, z.2)) z.1)
    (hPdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1)
    (t : ℝ) (ht : 0 < t)
    (hSliceT : MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hDivT : CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, t)))
    (η : Vec3 → Vec3) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) :
    (∫ x : Vec3,
      (∑ i : Fin 3, ∑ j : Fin 3,
        regUniformMollifiedVelocity ρ ε hε u (x, t) j * u (x, t) i *
          spatialDeriv (fun y => η y i) j x)
        - (∑ i : Fin 3, ∑ j : Fin 3,
          spatialPartial (fun y => u y i) j (x, t) *
            spatialDeriv (fun y => η y i) j x)
        + p (x, t) * (∑ i : Fin 3, spatialDeriv (fun y => η y i) i x)) =
      ∫ x : Vec3, ∑ i : Fin 3, regR12TimeRHS ρ ε hε u p (x, t) i * η x i := by
  have hq (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y => η y i) :=
    hη.continuousLinearMap_comp (ContinuousLinearMap.proj (R := ℝ) i)
  have hqc (i : Fin 3) : HasCompactSupport (fun y => η y i) :=
    hηc.comp_left (g := fun v : Vec3 => v i) rfl
  have hC (i : Fin 3) := regularisedR12TimeIBP_component ρ ε hε u p hD hDD hDp hUdiff hDdiff
    hPdiff t ht hSliceT hDivT i (fun y => η y i) (hq i) (hqc i)
  calc
    _ = ∫ x : Vec3, ∑ i : Fin 3,
          ((∑ j : Fin 3, regUniformMollifiedVelocity ρ ε hε u (x, t) j * u (x, t) i *
              spatialDeriv (fun y => η y i) j x)
            - (∑ j : Fin 3, spatialPartial (fun y => u y i) j (x, t) *
              spatialDeriv (fun y => η y i) j x)
            + p (x, t) * spatialDeriv (fun y => η y i) i x) := by
        congr 1
        funext x
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = ∑ i : Fin 3, ∫ x : Vec3,
          ((∑ j : Fin 3, regUniformMollifiedVelocity ρ ε hε u (x, t) j * u (x, t) i *
              spatialDeriv (fun y => η y i) j x)
            - (∑ j : Fin 3, spatialPartial (fun y => u y i) j (x, t) *
              spatialDeriv (fun y => η y i) j x)
            + p (x, t) * spatialDeriv (fun y => η y i) i x) :=
        integral_finsetSum _ fun i _ => (hC i).1
    _ = ∑ i : Fin 3, ∫ x : Vec3, regR12TimeRHS ρ ε hε u p (x, t) i * η x i :=
        Finset.sum_congr rfl fun i _ => (hC i).2.2
    _ = _ := (integral_finsetSum _ fun i _ => (hC i).2.1).symm

end CKN.Leray

end
