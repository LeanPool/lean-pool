/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatOrbit
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Newtonian

/-!
# Heat PDE

A smooth compact input evolves by the heat equation under Gaussian convolution.
-/

public section

open MeasureTheory
open CKN.Foundation.Heat CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A smooth compact input evolves by the heat equation under Gaussian convolution. -/
theorem heatConv_hasDerivAt_laplacianInput {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    {t : ℝ} (ht : 0 < t) (x : Vec3) :
    HasDerivAt (fun s : ℝ => heatConv s f x)
      (heatConv t (CKN.spatialLaplacian f) x) t := by
  have h := heatConv_hasDerivAt_laplacianIntegral_smooth hf hfc ht x
  convert h using 1
  exact (CKN.Foundation.Heat.heatKernel_laplacian_integral_eq_smooth hf hfc ht x).symm

/-- Spatial differentiation of a smooth Gaussian heat orbit commutes with the
Laplacian on its compactly supported input. -/
theorem heatConv_spatialLaplacian_input {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    {t : ℝ} (ht : 0 < t) (x : Vec3) :
    CKN.spatialLaplacian (heatConv t f) x =
      heatConv t (CKN.spatialLaplacian f) x := by
  rw [CKN.spatialLaplacian]
  have hterm (i : Fin 3) :
      CKN.spatialDeriv (CKN.spatialDeriv (heatConv t f) i) i x =
        heatConv t (CKN.spatialDeriv (CKN.spatialDeriv f i) i) x := by
    let ei : Vec3 := CKN.basisVec i
    have hdf : ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialDeriv f i) :=
      CKN.contDiff_spatialDeriv_smooth hf i
    have hdfc : HasCompactSupport (CKN.spatialDeriv f i) := by
      change HasCompactSupport (fun z => (fderiv ℝ f z) (CKN.basisVec i))
      exact hfc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i)
    have hfirst : (fun z : Vec3 => CKN.spatialDeriv (heatConv t f) i z) =
        heatConv t (CKN.spatialDeriv f i) := by
      funext z
      change fderiv ℝ (heatConv t f) z (CKN.basisVec i) = _
      exact heatConv_fderiv hf hfc ht z (CKN.basisVec i)
    change fderiv ℝ (fun z : Vec3 => CKN.spatialDeriv (heatConv t f) i z)
        x (CKN.basisVec i) = _
    rw [hfirst]
    exact heatConv_fderiv hdf hdfc ht x (CKN.basisVec i)
  calc
    (∑ i : Fin 3, CKN.spatialDeriv (CKN.spatialDeriv (heatConv t f) i) i x) =
        ∑ i : Fin 3, heatConv t
          (CKN.spatialDeriv (CKN.spatialDeriv f i) i) x := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm i
    _ = heatConv t (fun y : Vec3 =>
          ∑ i : Fin 3, CKN.spatialDeriv (CKN.spatialDeriv f i) i y) x := by
      rw [heatConv_eq_integral]
      have hlap (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
          (CKN.spatialDeriv (CKN.spatialDeriv f i) i) :=
        CKN.contDiff_spatialDeriv_smooth (CKN.contDiff_spatialDeriv_smooth hf i) i
      have hlapc (i : Fin 3) : HasCompactSupport
          (CKN.spatialDeriv (CKN.spatialDeriv f i) i) := by
        change HasCompactSupport (fun z : Vec3 =>
          (fderiv ℝ (fun y : Vec3 => (fderiv ℝ f y) (CKN.basisVec i)) z)
            (CKN.basisVec i))
        exact (hfc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i)).fderiv_apply
          (𝕜 := ℝ) (CKN.basisVec i)
      have hk : Continuous (fun y : Vec3 => heatKernel y t) := by
        rw [show (fun y : Vec3 => heatKernel y t) = fun y : Vec3 =>
            (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
              Real.exp (-(∑ j, y j ^ 2) / (4 * t)) by
          funext y
          exact heatKernel_eq_formula_sum ht]
        fun_prop (disch := positivity)
      have hcont (i : Fin 3) : Continuous (fun y : Vec3 =>
          CKN.spatialDeriv (CKN.spatialDeriv f i) i (x - y)) :=
        (hlap i).continuous.comp (by fun_prop)
      have hcompact (i : Fin 3) : HasCompactSupport (fun y : Vec3 =>
          CKN.spatialDeriv (CKN.spatialDeriv f i) i (x - y)) := by
        exact (hlapc i).comp_homeomorph (Homeomorph.subLeft x)
      have hint (i : Fin 3) : Integrable (fun y : Vec3 =>
          heatKernel y t * CKN.spatialDeriv (CKN.spatialDeriv f i) i (x-y)) volume := by
        exact (hk.mul (hcont i)).integrable_of_hasCompactSupport
          (hcompact i).mul_left
      have hsum := integral_finsetSum Finset.univ
        (f := fun (i : Fin 3) (y : Vec3) => heatKernel y t *
          CKN.spatialDeriv (CKN.spatialDeriv f i) i (x-y))
        (fun i hi => hint i)
      calc
        ∑ i : Fin 3, heatConv t
            (CKN.spatialDeriv (CKN.spatialDeriv f i) i) x =
            ∑ i : Fin 3, ∫ y : Vec3, heatKernel y t *
              CKN.spatialDeriv (CKN.spatialDeriv f i) i (x-y) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [heatConv_eq_integral]
        _ = ∫ y : Vec3, heatKernel y t *
              ∑ i : Fin 3, CKN.spatialDeriv (CKN.spatialDeriv f i) i (x-y) := by
                have hfun : (fun y : Vec3 => ∑ i : Fin 3,
                    heatKernel y t * CKN.spatialDeriv
                      (CKN.spatialDeriv f i) i (x-y)) =
                    (fun y : Vec3 => heatKernel y t * ∑ i : Fin 3,
                      CKN.spatialDeriv (CKN.spatialDeriv f i) i (x-y)) := by
                  funext y
                  rw [Finset.mul_sum]
                rw [← hfun]
                simpa only [Finset.sum_attach, Finset.mem_univ, true_and] using hsum.symm

/-- Each component of a smooth compact vector heat orbit satisfies the heat
equation. -/
theorem heatConvVec3_component_hasDerivAt_laplacianInput
    {b : Vec3 → Vec3} (hb : ∀ i : Fin 3,
      ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t : ℝ} (ht : 0 < t) (x : Vec3) (i : Fin 3) :
    HasDerivAt (fun s : ℝ => heatConvVec3 s b x i)
      (heatConv t (CKN.spatialLaplacian (fun y => b y i)) x) t := by
  simpa [heatConvVec3] using
    heatConv_hasDerivAt_laplacianInput (hb i) (hbc i) ht x

/-- The spatial Laplacian of each component of a smooth compact vector heat
orbit is convolution with the input Laplacian. -/
theorem heatConvVec3_component_spatialLaplacian_input
    {b : Vec3 → Vec3} (hb : ∀ i : Fin 3,
      ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t : ℝ} (ht : 0 < t) (x : Vec3) (i : Fin 3) :
    CKN.spatialLaplacian (fun z => heatConvVec3 t b z i) x =
      heatConv t (CKN.spatialLaplacian (fun y => b y i)) x := by
  simpa [heatConvVec3] using
    heatConv_spatialLaplacian_input (hb i) (hbc i) ht x


end ESS

end
