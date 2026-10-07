/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityLocalizedEnergyMollifier
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLocalizedEnergyScalar
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitCurve

/-!
# The slice pairing of a mollified equation

For a fixed smooth compact kernel, pairing the mollified momentum equation
with the mollified velocity gives the mollified energy identity: the
Laplacian contributes minus the squared mollified gradient, the pressure
drops out by the solenoidal condition, and the transport term remains as the
pairing of the mollified quadratic tensor with the mollified gradient
(`prop:lps-local-strong`).
-/

public section

open CKN

open MeasureTheory Set Filter
open scoped Interval Topology ENNReal
open CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- Integration by parts moving the derivative from the kernel of the first
factor to the kernel of the second. -/
theorem lps_conv_pair_ibp {η : Vec3 → ℝ} (hη : IsVlKernel η) {h₁ h₂ : Vec3 → ℝ}
    (hh₁ : MemLp h₁ 2 volume) (hh₂ : MemLp h₂ 2 volume) (j : Fin 3) :
    ∫ x, vlConv (vlDeriv η j) h₁ x * vlConv η h₂ x =
      -∫ x, vlConv η h₁ x * vlConv (vlDeriv η j) h₂ x := by
  have h := vlConv_integral_mul_deriv (k := η) (l := η) hη hη hh₁ hh₂ j
  linarith only [h]

/-- The mollified energy identity on one time slice. -/
theorem lps_slice_mollified_energy {η : Vec3 → ℝ} (hη : IsVlKernel η)
    {U W : Fin 3 → Vec3 → ℝ} {G H F : Fin 3 → Fin 3 → Vec3 → ℝ} {P : Vec3 → ℝ}
    (hU : ∀ i, MemLp (U i) 2 volume) (hW : ∀ i, MemLp (W i) 2 volume)
    (hG : ∀ i j, MemLp (G i j) 2 volume) (hH : ∀ i j, MemLp (H i j) 2 volume)
    (hF : ∀ i j, MemLp (F i j) 2 volume) (hP : MemLp P 2 volume)
    (hM : ∀ i, ∀ᵐ x ∂(volume : Measure Vec3),
      vlConv η (W i) x + ∑ j : Fin 3, vlConv (vlDeriv η j) (F i j) x -
        ∑ j : Fin 3, vlConv η (H i j) x + vlConv (vlDeriv η i) P x = 0)
    (hG1 : ∀ i j, ∀ᵐ x ∂(volume : Measure Vec3),
      vlConv (vlDeriv η j) (U i) x = vlConv η (G i j) x)
    (hH1 : ∀ i j, ∀ᵐ x ∂(volume : Measure Vec3),
      vlConv (vlDeriv η j) (G i j) x = vlConv η (H i j) x)
    (hdiv : ∀ᵐ x ∂(volume : Measure Vec3), ∑ i : Fin 3, vlConv (vlDeriv η i) (U i) x = 0) :
    ∑ i : Fin 3, ∫ x, vlConv η (W i) x * vlConv η (U i) x =
      (∑ i : Fin 3, ∑ j : Fin 3, ∫ x, vlConv η (F i j) x * vlConv η (G i j) x) -
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, (vlConv η (G i j) x) ^ 2 := by
  have hη' : ∀ j, IsVlKernel (vlDeriv η j) := fun j => hη.deriv j
  have int : ∀ {k l : Vec3 → ℝ}, IsVlKernel k → IsVlKernel l → ∀ {h₁ h₂ : Vec3 → ℝ},
      MemLp h₁ 2 volume → MemLp h₂ 2 volume →
      Integrable (fun x => vlConv k h₁ x * vlConv l h₂ x) volume :=
    fun {_ _} hk hl {_ _} hh₁ hh₂ =>
      (vlConv_memLp hk hh₁).integrable_mul (vlConv_memLp hl hh₂)
  -- pairing of the equation with the mollified velocity, component by component
  have hcomp : ∀ i : Fin 3,
      (∫ x, vlConv η (W i) x * vlConv η (U i) x) +
        (∑ j : Fin 3, ∫ x, vlConv (vlDeriv η j) (F i j) x * vlConv η (U i) x) -
        (∑ j : Fin 3, ∫ x, vlConv η (H i j) x * vlConv η (U i) x) +
        (∫ x, vlConv (vlDeriv η i) P x * vlConv η (U i) x) = 0 := by
    intro i
    have hzero : ∫ x, (vlConv η (W i) x + ∑ j : Fin 3, vlConv (vlDeriv η j) (F i j) x -
        ∑ j : Fin 3, vlConv η (H i j) x + vlConv (vlDeriv η i) P x) *
          vlConv η (U i) x = 0 := by
      have : ∀ᵐ x ∂(volume : Measure Vec3), (vlConv η (W i) x +
          ∑ j : Fin 3, vlConv (vlDeriv η j) (F i j) x -
          ∑ j : Fin 3, vlConv η (H i j) x + vlConv (vlDeriv η i) P x) *
            vlConv η (U i) x = 0 := by
        filter_upwards [hM i] with x hx
        rw [hx, zero_mul]
      rw [integral_congr_ae this]
      simp
    have iW := int hη hη (hW i) (hU i)
    have iF : ∀ j, Integrable (fun x => vlConv (vlDeriv η j) (F i j) x * vlConv η (U i) x)
        volume := fun j => int (hη' j) hη (hF i j) (hU i)
    have iH : ∀ j, Integrable (fun x => vlConv η (H i j) x * vlConv η (U i) x) volume :=
      fun j => int hη hη (hH i j) (hU i)
    have iP := int (hη' i) hη hP (hU i)
    have iFs : Integrable (fun x => (∑ j : Fin 3, vlConv (vlDeriv η j) (F i j) x) *
        vlConv η (U i) x) volume := by
      have := integrable_finsetSum (Finset.univ : Finset (Fin 3)) fun j _ => iF j
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp [Finset.sum_mul]
    have iHs : Integrable (fun x => (∑ j : Fin 3, vlConv η (H i j) x) *
        vlConv η (U i) x) volume := by
      have := integrable_finsetSum (Finset.univ : Finset (Fin 3)) fun j _ => iH j
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp [Finset.sum_mul]
    have hexp : ∀ x, (vlConv η (W i) x + ∑ j : Fin 3, vlConv (vlDeriv η j) (F i j) x -
        ∑ j : Fin 3, vlConv η (H i j) x + vlConv (vlDeriv η i) P x) * vlConv η (U i) x =
        vlConv η (W i) x * vlConv η (U i) x +
          (∑ j : Fin 3, vlConv (vlDeriv η j) (F i j) x) * vlConv η (U i) x -
          (∑ j : Fin 3, vlConv η (H i j) x) * vlConv η (U i) x +
          vlConv (vlDeriv η i) P x * vlConv η (U i) x := fun x => by ring
    simp_rw [hexp] at hzero
    have i1 : Integrable (fun x => vlConv η (W i) x * vlConv η (U i) x +
        (∑ j : Fin 3, vlConv (vlDeriv η j) (F i j) x) * vlConv η (U i) x) volume :=
      iW.add iFs
    have i2 : Integrable (fun x => vlConv η (W i) x * vlConv η (U i) x +
        (∑ j : Fin 3, vlConv (vlDeriv η j) (F i j) x) * vlConv η (U i) x -
        (∑ j : Fin 3, vlConv η (H i j) x) * vlConv η (U i) x) volume := i1.sub iHs
    rw [integral_add i2 iP, integral_sub i1 iHs, integral_add iW iFs] at hzero
    have e1 : ∫ x, (∑ j : Fin 3, vlConv (vlDeriv η j) (F i j) x) * vlConv η (U i) x =
        ∑ j : Fin 3, ∫ x, vlConv (vlDeriv η j) (F i j) x * vlConv η (U i) x := by
      simp_rw [Finset.sum_mul]
      exact integral_finsetSum _ fun j _ => iF j
    have e2 : ∫ x, (∑ j : Fin 3, vlConv η (H i j) x) * vlConv η (U i) x =
        ∑ j : Fin 3, ∫ x, vlConv η (H i j) x * vlConv η (U i) x := by
      simp_rw [Finset.sum_mul]
      exact integral_finsetSum _ fun j _ => iH j
    rw [e1, e2] at hzero
    exact hzero
  -- identify each pairing
  have hT2 : ∀ i j, ∫ x, vlConv (vlDeriv η j) (F i j) x * vlConv η (U i) x =
      -∫ x, vlConv η (F i j) x * vlConv η (G i j) x := by
    intro i j
    rw [lps_conv_pair_ibp hη (hF i j) (hU i) j]
    congr 1
    exact integral_congr_ae (by
      filter_upwards [hG1 i j] with x hx
      rw [hx])
  have hT3 : ∀ i j, ∫ x, vlConv η (H i j) x * vlConv η (U i) x =
      -∫ x, (vlConv η (G i j) x) ^ 2 := by
    intro i j
    have h1 : ∫ x, vlConv η (H i j) x * vlConv η (U i) x =
        ∫ x, vlConv (vlDeriv η j) (G i j) x * vlConv η (U i) x :=
      integral_congr_ae (by
        filter_upwards [hH1 i j] with x hx
        rw [hx])
    rw [h1, lps_conv_pair_ibp hη (hG i j) (hU i) j]
    congr 1
    exact integral_congr_ae (by
      filter_upwards [hG1 i j] with x hx
      rw [hx, sq])
  have hT4 : ∑ i : Fin 3, ∫ x, vlConv (vlDeriv η i) P x * vlConv η (U i) x = 0 := by
    have h1 : ∀ i : Fin 3, ∫ x, vlConv (vlDeriv η i) P x * vlConv η (U i) x =
        -∫ x, vlConv η P x * vlConv (vlDeriv η i) (U i) x := fun i =>
      lps_conv_pair_ibp hη hP (hU i) i
    simp_rw [h1]
    rw [Finset.sum_neg_distrib, neg_eq_zero]
    have iPU : ∀ i : Fin 3, Integrable (fun x => vlConv η P x * vlConv (vlDeriv η i) (U i) x)
        volume := fun i => int hη (hη' i) hP (hU i)
    rw [← integral_finsetSum _ (fun i _ => iPU i)]
    have : ∀ᵐ x ∂(volume : Measure Vec3),
        ∑ i : Fin 3, vlConv η P x * vlConv (vlDeriv η i) (U i) x = 0 := by
      filter_upwards [hdiv] with x hx
      rw [← Finset.mul_sum, hx, mul_zero]
    rw [integral_congr_ae this]
    simp
  have hsum := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hcomp i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const_zero] at hsum
  simp_rw [hT2, hT3] at hsum
  rw [hT4] at hsum
  simp only [Finset.sum_neg_distrib, sub_neg_eq_add, add_zero] at hsum
  linarith only [hsum]

/-- The slice energy identity, in the limit of vanishing mollification. -/
theorem lps_slice_energy_limit
    {U W : Fin 3 → Vec3 → ℝ} {G H F : Fin 3 → Fin 3 → Vec3 → ℝ} {P : Vec3 → ℝ}
    (hU : ∀ i, MemLp (U i) 2 volume) (hW : ∀ i, MemLp (W i) 2 volume)
    (hG : ∀ i j, MemLp (G i j) 2 volume) (hH : ∀ i j, MemLp (H i j) 2 volume)
    (hF : ∀ i j, MemLp (F i j) 2 volume) (hP : MemLp P 2 volume)
    (hM : ∀ n, ∀ i, ∀ᵐ x ∂(volume : Measure Vec3),
      vlConv (vlMoll n) (W i) x + ∑ j : Fin 3, vlConv (vlDeriv (vlMoll n) j) (F i j) x -
        ∑ j : Fin 3, vlConv (vlMoll n) (H i j) x +
          vlConv (vlDeriv (vlMoll n) i) P x = 0)
    (hG1 : ∀ n, ∀ i j, ∀ᵐ x ∂(volume : Measure Vec3),
      vlConv (vlDeriv (vlMoll n) j) (U i) x = vlConv (vlMoll n) (G i j) x)
    (hH1 : ∀ n, ∀ i j, ∀ᵐ x ∂(volume : Measure Vec3),
      vlConv (vlDeriv (vlMoll n) j) (G i j) x = vlConv (vlMoll n) (H i j) x)
    (hdiv : ∀ n, ∀ᵐ x ∂(volume : Measure Vec3),
      ∑ i : Fin 3, vlConv (vlDeriv (vlMoll n) i) (U i) x = 0) :
    ∑ i : Fin 3, ∫ x, W i x * U i x =
      (∑ i : Fin 3, ∑ j : Fin 3, ∫ x, F i j x * G i j x) -
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, (G i j x) ^ 2 := by
  have hconv : ∀ (f g : Vec3 → ℝ), MemLp f 2 volume → MemLp g 2 volume →
      Tendsto (fun n => ∫ x, vlConv (vlMoll n) f x * vlConv (vlMoll n) g x) atTop
        (nhds (∫ x, f x * g x)) := by
    intro f g hf hg
    exact lps_integral_mul_tendsto (μ := (volume : Measure Vec3))
      (F := fun n => vlConv (vlMoll n) f) (G := fun n => vlConv (vlMoll n) g)
      (fun n => vlConv_memLp (vlMoll_kernel n) hf) (fun n => vlConv_memLp (vlMoll_kernel n) hg)
      hf hg (vlMoll_tendsto hf) (vlMoll_tendsto hg)
  have hstep := fun n => lps_slice_mollified_energy (vlMoll_kernel n) hU hW hG hH hF hP
    (hM n) (hG1 n) (hH1 n) (hdiv n)
  have hL : Tendsto (fun n => ∑ i : Fin 3, ∫ x, vlConv (vlMoll n) (W i) x *
      vlConv (vlMoll n) (U i) x) atTop (nhds (∑ i : Fin 3, ∫ x, W i x * U i x)) :=
    tendsto_finsetSum _ fun i _ => hconv _ _ (hW i) (hU i)
  have hR1 : Tendsto (fun n => ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, vlConv (vlMoll n) (F i j) x *
      vlConv (vlMoll n) (G i j) x) atTop
      (nhds (∑ i : Fin 3, ∑ j : Fin 3, ∫ x, F i j x * G i j x)) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => hconv _ _ (hF i j) (hG i j)
  have hR2 : Tendsto (fun n => ∑ i : Fin 3, ∑ j : Fin 3, ∫ x,
      (vlConv (vlMoll n) (G i j) x) ^ 2) atTop
      (nhds (∑ i : Fin 3, ∑ j : Fin 3, ∫ x, (G i j x) ^ 2)) := by
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    have := hconv _ _ (hG i j) (hG i j)
    simpa [sq] using this
  exact tendsto_nhds_unique (hL.congr fun n => hstep n) (hR1.sub hR2)

end ESS.LPS

end
