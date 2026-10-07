/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegLocalEnergyTime

/-!
# The limiting energy pairing on one time slice

For a weakly divergence-free square-integrable velocity slice `u` with weak
gradient `D`, a divergence-free `C¹` transport field `V`, a square-integrable
pressure `q`, a force pressure `p_f` with square-integrable weak gradient `G`,
a square-integrable force `F` and a smooth compactly supported weight `ψ`, the
sum over the components of the limiting energy pairings is
`∫ |D|² ψ - ½ ∫ (|u|² Δψ + (|u|² V + 2 (q + p_f) u)·∇ψ + 2 (F·u) ψ)`.
This is the spatial identity behind `eq:reg-local-energy-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

/-- A product of two square-integrable functions and a continuous compactly
supported weight is integrable. -/
theorem integrable_mul_mul_compact {a b c : Vec3 → ℝ} (ha : MemLp a 2 volume)
    (hb : MemLp b 2 volume) (hc : Continuous c) (hcc : HasCompactSupport c) :
    Integrable fun x => a x * (b x * c x) :=
  ha.integrable_mul (memLp_mul_compact hb hc hcc)

theorem hasCompactSupport_sum_fin_three {g : Fin 3 → Vec3 → ℝ}
    (h : ∀ j, HasCompactSupport (g j)) : HasCompactSupport fun x => ∑ j : Fin 3, g j x := by
  simp only [Fin.sum_univ_three]
  exact ((h 0).add (h 1)).add (h 2)

section Slice

variable {u : Vec3 → Vec3} (hdf : CKN.IsWeakDivFreeL2 u)
  {D : Vec3 → Fin 3 → Vec3} (hD : ∀ k j, MemLp (fun x => D x k j) 2 volume)
  (hweak : ∀ k, CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun x => u x k) (fun x => D x k))
  {V : Vec3 → Vec3} (hV : ∀ j, ContDiff ℝ 1 fun x => V x j)
  (hdiv : ∀ x, ∑ j : Fin 3, fderiv ℝ (fun y => V y j) x (CKN.basisVec j) = 0)
  {q : Vec3 → ℝ} (hq : MemLp q 2 volume)
  {pf : Vec3 → ℝ} (hpl : LocallyIntegrable pf volume)
  {G : Vec3 → Vec3} (hG : ∀ k, MemLp (fun x => G x k) 2 volume)
  (hpG : CKN.HasWeakGradientOn (Set.univ : Set Vec3) pf G)
  {F : Vec3 → Vec3} (hF : ∀ k, MemLp (fun x => F x k) 2 volume)
  {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
  (hpψ : ∀ k, MemLp (fun x => pf x * fderiv ℝ ψ x (CKN.basisVec k)) 2 volume)

include hdf hD hweak hV hdiv hq hψ hψc in
/-- The limiting energy pairing of one component, after the chain rule and the
transport identity. -/
theorem leLimit_slice_eq (k : Fin 3) :
    leLimit (fun x => u x k) (fun j x => D x k j) (fun j x => V x j * u x k - D x k j) q
        (fun x => G x k) (fun x => F x k) ψ k =
      (∑ j : Fin 3, ∫ x, D x k j * (D x k j * ψ x)) -
        (1 / 2) * (∫ x, u x k * (u x k * CKN.spatialLaplacian ψ x)) -
        (1 / 2) * (∫ x, u x k * (u x k * ∑ j : Fin 3, V x j * fderiv ℝ ψ x (CKN.basisVec j))) -
        (∫ x, q x * (D x k k * ψ x)) -
        (∫ x, q x * (u x k * fderiv ℝ ψ x (CKN.basisVec k))) +
        (∫ x, u x k * (ψ x * G x k)) - ∫ x, F x k * (u x k * ψ x) := by
  have hu : ∀ k, MemLp (fun x => u x k) 2 volume := fun k => hdf.1.eval k
  have hdψ : ∀ j, Continuous fun x => fderiv ℝ ψ x (CKN.basisVec j) := fun j =>
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψc : ∀ j, HasCompactSupport fun x => fderiv ℝ ψ x (CKN.basisVec j) := fun j =>
    hψc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec j)
  have hVc : ∀ j, Continuous fun x => V x j := fun j => (hV j).continuous
  have hVψ : ∀ j, Continuous fun x => V x j * ψ x := fun j => (hVc j).mul hψ.continuous
  have hVψc : ∀ j, HasCompactSupport fun x => V x j * ψ x := fun j => hψc.mul_left
  have hVd : ∀ j, Continuous fun x => V x j * fderiv ℝ ψ x (CKN.basisVec j) := fun j =>
    (hVc j).mul (hdψ j)
  have hVdc : ∀ j, HasCompactSupport fun x => V x j * fderiv ℝ ψ x (CKN.basisVec j) := fun j =>
    (hdψc j).mul_left
  -- the transport-minus-viscous pairing in one direction
  have hsplit : ∀ j, ∫ x, (V x j * u x k - D x k j) *
      (D x k j * ψ x + u x k * fderiv ℝ ψ x (CKN.basisVec j)) =
      (∫ x, D x k j * (u x k * (V x j * ψ x))) +
        (∫ x, u x k * (u x k * (V x j * fderiv ℝ ψ x (CKN.basisVec j)))) -
        (∫ x, D x k j * (D x k j * ψ x)) -
        ∫ x, D x k j * (u x k * fderiv ℝ ψ x (CKN.basisVec j)) := by
    intro j
    have i1 := integrable_mul_mul_compact (hD k j) (hu k) (hVψ j) (hVψc j)
    have i2 := integrable_mul_mul_compact (hu k) (hu k) (hVd j) (hVdc j)
    have i3 := integrable_mul_mul_compact (hD k j) (hD k j) hψ.continuous hψc
    have i4 := integrable_mul_mul_compact (hD k j) (hu k) (hdψ j) (hdψc j)
    have e : ∫ x, (V x j * u x k - D x k j) *
        (D x k j * ψ x + u x k * fderiv ℝ ψ x (CKN.basisVec j)) =
        ∫ x, (D x k j * (u x k * (V x j * ψ x)) +
          u x k * (u x k * (V x j * fderiv ℝ ψ x (CKN.basisVec j))) -
          D x k j * (D x k j * ψ x) - D x k j * (u x k * fderiv ℝ ψ x (CKN.basisVec j))) :=
      integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
    have i12 : Integrable fun x => D x k j * (u x k * (V x j * ψ x)) +
        u x k * (u x k * (V x j * fderiv ℝ ψ x (CKN.basisVec j))) := i1.add i2
    have i123 : Integrable fun x => D x k j * (u x k * (V x j * ψ x)) +
        u x k * (u x k * (V x j * fderiv ℝ ψ x (CKN.basisVec j))) -
        D x k j * (D x k j * ψ x) := i12.sub i3
    rw [e, integral_sub i123 i4, integral_sub i12 i3, integral_add i1 i2]
  have htr := sum_integral_transport_eq hu hD hweak hV hdiv hψ hψc k
  have hch := sum_integral_grad_mul_eq hu hD hweak hψ hψc k
  have hsumV : ∑ j : Fin 3, ∫ x, u x k * (u x k * (V x j * fderiv ℝ ψ x (CKN.basisVec j))) =
      ∫ x, u x k * (u x k * ∑ j : Fin 3, V x j * fderiv ℝ ψ x (CKN.basisVec j)) := by
    rw [← integral_finsetSum _ fun j _ => integrable_mul_mul_compact (hu k) (hu k) (hVd j)
      (hVdc j)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Finset.mul_sum]
  have hqsplit : ∫ x, q x * (D x k k * ψ x + u x k * fderiv ℝ ψ x (CKN.basisVec k)) =
      (∫ x, q x * (D x k k * ψ x)) + ∫ x, q x * (u x k * fderiv ℝ ψ x (CKN.basisVec k)) := by
    rw [← integral_add (integrable_mul_mul_compact hq (hD k k) hψ.continuous hψc)
      (integrable_mul_mul_compact hq (hu k) (hdψ k) (hdψc k))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  have hGeq : ∫ x, G x k * (u x k * ψ x) = ∫ x, u x k * (ψ x * G x k) :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  unfold leLimit
  simp only [Finset.sum_congr rfl fun j _ => hsplit j]
  rw [hqsplit, hGeq]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [htr, hch, hsumV]
  ring

include hdf hD hweak hV hdiv hq hpl hG hpG hF hψ hψc hpψ in
/-- The sum over the components of the limiting energy pairings on one time
slice. -/
theorem sum_leLimit_slice_eq :
    ∑ k : Fin 3, leLimit (fun x => u x k) (fun j x => D x k j)
        (fun j x => V x j * u x k - D x k j) q (fun x => G x k) (fun x => F x k) ψ k =
      (∫ x, (∑ k : Fin 3, ∑ j : Fin 3, D x k j ^ 2) * ψ x) -
        (1 / 2) * ∫ x, ((∑ k : Fin 3, u x k ^ 2) * CKN.spatialLaplacian ψ x +
          ∑ i : Fin 3, ((∑ k : Fin 3, u x k ^ 2) * V x i + 2 * (q x + pf x) * u x i) *
            fderiv ℝ ψ x (CKN.basisVec i) +
          2 * (∑ i : Fin 3, F x i * u x i) * ψ x) := by
  have hu : ∀ k, MemLp (fun x => u x k) 2 volume := fun k => hdf.1.eval k
  have hdψ : ∀ j, Continuous fun x => fderiv ℝ ψ x (CKN.basisVec j) := fun j =>
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψc : ∀ j, HasCompactSupport fun x => fderiv ℝ ψ x (CKN.basisVec j) := fun j =>
    hψc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec j)
  have hΔ : Continuous (CKN.spatialLaplacian ψ) :=
    continuous_finsetSum _ fun i _ =>
      (CKN.contDiff_spatialDeriv_smooth (CKN.contDiff_spatialDeriv_smooth hψ i) i).continuous
  have hΔc : HasCompactSupport (CKN.spatialLaplacian ψ) :=
    CKN.hasCompactSupport_spatialLaplacian hψc
  have hVc : ∀ j, Continuous fun x => V x j := fun j => (hV j).continuous
  have hW : Continuous fun x => ∑ j : Fin 3, V x j * fderiv ℝ ψ x (CKN.basisVec j) :=
    continuous_finsetSum _ fun j _ => (hVc j).mul (hdψ j)
  have hWc : HasCompactSupport fun x => ∑ j : Fin 3, V x j * fderiv ℝ ψ x (CKN.basisVec j) :=
    hasCompactSupport_sum_fin_three fun j => (hdψc j).mul_left
  -- integrability of the pieces
  have iD : ∀ k j, Integrable fun x => D x k j * (D x k j * ψ x) := fun k j =>
    integrable_mul_mul_compact (hD k j) (hD k j) hψ.continuous hψc
  have iΔ : ∀ k, Integrable fun x => u x k * (u x k * CKN.spatialLaplacian ψ x) := fun k =>
    integrable_mul_mul_compact (hu k) (hu k) hΔ hΔc
  have iW : ∀ k, Integrable fun x =>
      u x k * (u x k * ∑ j : Fin 3, V x j * fderiv ℝ ψ x (CKN.basisVec j)) := fun k =>
    integrable_mul_mul_compact (hu k) (hu k) hW hWc
  have iq : ∀ k, Integrable fun x => q x * (u x k * fderiv ℝ ψ x (CKN.basisVec k)) := fun k =>
    integrable_mul_mul_compact hq (hu k) (hdψ k) (hdψc k)
  have ip : ∀ k, Integrable fun x => u x k * (pf x * fderiv ℝ ψ x (CKN.basisVec k)) := fun k =>
    (hu k).integrable_mul (hpψ k)
  have iF : ∀ k, Integrable fun x => F x k * (u x k * ψ x) := fun k =>
    integrable_mul_mul_compact (hF k) (hu k) hψ.continuous hψc
  have iqD : ∀ k, Integrable fun x => q x * (D x k k * ψ x) := fun k =>
    integrable_mul_mul_compact hq (hD k k) hψ.continuous hψc
  -- the trace term vanishes
  have htrace : ∑ k : Fin 3, ∫ x, q x * (D x k k * ψ x) = 0 := by
    rw [← integral_finsetSum _ fun k _ => iqD k]
    have hdiag := ae_sum_diag_eq_zero hdf (fun k => hD k k) hweak
    have h0 : (fun x => ∑ k : Fin 3, q x * (D x k k * ψ x)) =ᵐ[volume] fun _ => (0 : ℝ) := by
      filter_upwards [hdiag] with x hx
      rw [← Finset.mul_sum, ← Finset.sum_mul, hx, zero_mul, mul_zero]
    rw [integral_congr_ae h0, integral_zero]
  have hpres := sum_integral_pressure_eq hdf hpl hG hpG hψ hψc hpψ
  -- the right-hand side as a sum of simple pairings
  have hrhs1 : ∫ x, (∑ k : Fin 3, ∑ j : Fin 3, D x k j ^ 2) * ψ x =
      ∑ k : Fin 3, ∑ j : Fin 3, ∫ x, D x k j * (D x k j * ψ x) := by
    simp_rw [← integral_finsetSum _ fun j _ => iD _ j]
    rw [← integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => iD k j]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hpt : ∀ x, (∑ k : Fin 3, u x k ^ 2) * CKN.spatialLaplacian ψ x +
        ∑ i : Fin 3, ((∑ k : Fin 3, u x k ^ 2) * V x i + 2 * (q x + pf x) * u x i) *
          fderiv ℝ ψ x (CKN.basisVec i) +
        2 * (∑ i : Fin 3, F x i * u x i) * ψ x =
      ∑ k : Fin 3, (u x k * (u x k * CKN.spatialLaplacian ψ x) +
        u x k * (u x k * ∑ j : Fin 3, V x j * fderiv ℝ ψ x (CKN.basisVec j)) +
        2 * (q x * (u x k * fderiv ℝ ψ x (CKN.basisVec k))) +
        2 * (u x k * (pf x * fderiv ℝ ψ x (CKN.basisVec k))) +
        2 * (F x k * (u x k * ψ x))) := by
    intro x
    simp only [Fin.sum_univ_three]
    ring
  have hk : ∀ k : Fin 3, ∫ x, (u x k * (u x k * CKN.spatialLaplacian ψ x) +
        u x k * (u x k * ∑ j : Fin 3, V x j * fderiv ℝ ψ x (CKN.basisVec j)) +
        2 * (q x * (u x k * fderiv ℝ ψ x (CKN.basisVec k))) +
        2 * (u x k * (pf x * fderiv ℝ ψ x (CKN.basisVec k))) +
        2 * (F x k * (u x k * ψ x))) =
      (∫ x, u x k * (u x k * CKN.spatialLaplacian ψ x)) +
        (∫ x, u x k * (u x k * ∑ j : Fin 3, V x j * fderiv ℝ ψ x (CKN.basisVec j))) +
        2 * (∫ x, q x * (u x k * fderiv ℝ ψ x (CKN.basisVec k))) +
        2 * (∫ x, u x k * (pf x * fderiv ℝ ψ x (CKN.basisVec k))) +
        2 * ∫ x, F x k * (u x k * ψ x) := by
    intro k
    have j1 : Integrable fun x => u x k * (u x k * CKN.spatialLaplacian ψ x) +
        u x k * (u x k * ∑ j : Fin 3, V x j * fderiv ℝ ψ x (CKN.basisVec j)) := (iΔ k).add (iW k)
    have j2 : Integrable fun x => u x k * (u x k * CKN.spatialLaplacian ψ x) +
        u x k * (u x k * ∑ j : Fin 3, V x j * fderiv ℝ ψ x (CKN.basisVec j)) +
        2 * (q x * (u x k * fderiv ℝ ψ x (CKN.basisVec k))) := j1.add ((iq k).const_mul 2)
    have j3 : Integrable fun x => u x k * (u x k * CKN.spatialLaplacian ψ x) +
        u x k * (u x k * ∑ j : Fin 3, V x j * fderiv ℝ ψ x (CKN.basisVec j)) +
        2 * (q x * (u x k * fderiv ℝ ψ x (CKN.basisVec k))) +
        2 * (u x k * (pf x * fderiv ℝ ψ x (CKN.basisVec k))) := j2.add ((ip k).const_mul 2)
    rw [integral_add j3 ((iF k).const_mul 2), integral_add j2 ((ip k).const_mul 2),
      integral_add j1 ((iq k).const_mul 2), integral_add (iΔ k) (iW k), integral_const_mul,
      integral_const_mul, integral_const_mul]
  have hint : ∀ k : Fin 3, Integrable fun x => u x k * (u x k * CKN.spatialLaplacian ψ x) +
        u x k * (u x k * ∑ j : Fin 3, V x j * fderiv ℝ ψ x (CKN.basisVec j)) +
        2 * (q x * (u x k * fderiv ℝ ψ x (CKN.basisVec k))) +
        2 * (u x k * (pf x * fderiv ℝ ψ x (CKN.basisVec k))) +
        2 * (F x k * (u x k * ψ x)) := fun k =>
    (((((iΔ k).add (iW k)).add ((iq k).const_mul 2)).add ((ip k).const_mul 2)).add
      ((iF k).const_mul 2))
  have hrhs2 : ∫ x, ((∑ k : Fin 3, u x k ^ 2) * CKN.spatialLaplacian ψ x +
        ∑ i : Fin 3, ((∑ k : Fin 3, u x k ^ 2) * V x i + 2 * (q x + pf x) * u x i) *
          fderiv ℝ ψ x (CKN.basisVec i) +
        2 * (∑ i : Fin 3, F x i * u x i) * ψ x) =
      ∑ k : Fin 3, ((∫ x, u x k * (u x k * CKN.spatialLaplacian ψ x)) +
        (∫ x, u x k * (u x k * ∑ j : Fin 3, V x j * fderiv ℝ ψ x (CKN.basisVec j))) +
        2 * (∫ x, q x * (u x k * fderiv ℝ ψ x (CKN.basisVec k))) +
        2 * (∫ x, u x k * (pf x * fderiv ℝ ψ x (CKN.basisVec k))) +
        2 * ∫ x, F x k * (u x k * ψ x)) := by
    simp_rw [hpt]
    rw [integral_finsetSum _ fun k _ => hint k]
    exact Finset.sum_congr rfl fun k _ => hk k
  simp only [leLimit_slice_eq hdf hD hweak hV hdiv hq hψ hψc]
  rw [hrhs1, hrhs2]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [htrace, hpres]
  ring

end Slice

end CKN.Leray

end
