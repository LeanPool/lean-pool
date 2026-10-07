/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityWeightedGradientMatrix
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityEnergyQuadratic
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityFluxProduct
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanGaussVector
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityEnergySupport
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalFinite
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityEnergyTest
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityEnergyDerivatives
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityTestBounds

/-!
# Leray Assembly Energy

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN.Leray

/-- Weak convergence of the regularized gradient gives the weighted mixed
energy limit and the polarization bound used in (S4). -/
theorem lerayAssembly_weightedGradient_matrix
    (μ : Measure ParabolicPoint) [IsFiniteMeasure μ]
    (D : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (d : ParabolicPoint → Fin 3 → Vec3)
    (hD : ∀ n, MemLp (D n) 2 μ)
    (hd : MemLp d 2 μ)
    (hweak : ∀ i j : Fin 3, ∀ w : ParabolicPoint → ℝ,
      MemLp w 2 μ →
      Tendsto (fun n => ∫ z, D n z i j * w z ∂μ) atTop
        (nhds (∫ z, d z i j * w z ∂μ)))
    (ψ : ParabolicPoint → ℝ)
    (hψ : MemLp ψ ∞ μ)
    (hψpos : ∀ᵐ z ∂μ, 0 ≤ ψ z) :
    Tendsto (fun n => ∑ i : Fin 3, ∑ j : Fin 3,
      ∫ z, D n z i j * d z i j * ψ z ∂μ) atTop
      (nhds (∫ z, spatialGradientSq (fun _ => 0) d z * ψ z ∂μ)) ∧
    (∀ n, 2 * (∑ i : Fin 3, ∑ j : Fin 3,
      ∫ z, D n z i j * d z i j * ψ z ∂μ) ≤
      (∫ z, spatialGradientSq (fun _ => 0) (D n) z * ψ z ∂μ) +
      (∫ z, spatialGradientSq (fun _ => 0) d z * ψ z ∂μ)) := by
  have hFi (n : ℕ) (i j : Fin 3) : MemLp
      (fun z : ParabolicPoint => D n z i j) 2 μ :=
    (memLp_pi_iff.mp ((memLp_pi_iff.mp (hD n)) i)) j
  have hGi (i j : Fin 3) : MemLp
      (fun z : ParabolicPoint => d z i j) 2 μ :=
    (memLp_pi_iff.mp ((memLp_pi_iff.mp hd) i)) j
  have hscalar (i j : Fin 3) := stability_weighted_gradient_scalar μ
    (fun n z => D n z i j) (fun z => d z i j) ψ
    (fun n => hFi n i j) (hGi i j) hψ hψpos
    (fun w hw => hweak i j w hw)
  have hIntN (n : ℕ) (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint => D n z i j * D n z i j * ψ z) μ :=
    stability_weighted_product_integrable μ (hFi n i j) (hFi n i j) hψ
  have hIntG (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint => d z i j * d z i j * ψ z) μ :=
    stability_weighted_product_integrable μ (hGi i j) (hGi i j) hψ
  have hEnergyN (n : ℕ) :
      (∫ z, spatialGradientSq (fun _ => 0) (D n) z * ψ z ∂μ) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z, D n z i j * D n z i j * ψ z ∂μ := by
    have hpoint : (fun z : ParabolicPoint =>
        spatialGradientSq (fun _ => 0) (D n) z * ψ z) =
        (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
          D n z i j * D n z i j * ψ z) := by
      funext z
      simp [spatialGradientSq, Finset.sum_mul, pow_two, mul_assoc]
    rw [hpoint]
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hIntN n i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum Finset.univ (fun j _ => hIntN n i j)
  have hEnergyG :
      (∫ z, spatialGradientSq (fun _ => 0) d z * ψ z ∂μ) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z, d z i j * d z i j * ψ z ∂μ := by
    have hpoint : (fun z : ParabolicPoint =>
        spatialGradientSq (fun _ => 0) d z * ψ z) =
        (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
          d z i j * d z i j * ψ z) := by
      funext z
      simp [spatialGradientSq, Finset.sum_mul, pow_two, mul_assoc]
    rw [hpoint]
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hIntG i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum Finset.univ (fun j _ => hIntG i j)
  have hcrossConv : Tendsto (fun n => ∑ i : Fin 3, ∑ j : Fin 3,
      ∫ z, D n z i j * d z i j * ψ z ∂μ) atTop
      (nhds (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z, d z i j * d z i j * ψ z ∂μ)) := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (hscalar i j).1
  refine ⟨by simpa only [hEnergyG] using hcrossConv, ?_⟩
  intro n
  rw [hEnergyN n, hEnergyG]
  calc
    2 * (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z, D n z i j * d z i j * ψ z ∂μ) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        2 * (∫ z, D n z i j * d z i j * ψ z ∂μ) := by
        simp_rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        ((∫ z, D n z i j * D n z i j * ψ z ∂μ) +
        (∫ z, d z i j * d z i j * ψ z ∂μ)) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact (hscalar i j).2 n
    _ = (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z, D n z i j * D n z i j * ψ z ∂μ) +
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z, d z i j * d z i j * ψ z ∂μ) := by
        simp_rw [Finset.sum_add_distrib]

/-- Strong local L³ convergence passes the quadratic energy term against a
bounded test derivative. -/
theorem lerayAssembly_quadraticTerm_tendsto
    (μ : Measure ParabolicPoint) [IsFiniteMeasure μ]
    (U : ℕ → ParabolicPoint → Vec3) (u : ParabolicPoint → Vec3)
    (hU : ∀ n, MemLp (U n) 3 μ) (hu : MemLp u 3 μ)
    (hconv : Tendsto (fun n => eLpNorm (U n - u) 3 μ) atTop (nhds 0))
    (T : ParabolicPoint → ℝ) (hT : MemLp T ∞ μ) :
    (∀ n, Integrable (fun z => ∑ i : Fin 3,
      U n z i * U n z i * T z) μ) ∧
    Integrable (fun z => ∑ i : Fin 3, u z i * u z i * T z) μ ∧
    Tendsto (fun n => ∫ z, ∑ i : Fin 3, U n z i * U n z i * T z ∂μ)
      atTop (nhds (∫ z, ∑ i : Fin 3, u z i * u z i * T z ∂μ)) := by
  let : ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (3 / 2 : ℝ≥0∞) := by
    have hreal : Real.HolderTriple 3 3 (3 / 2) :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa only [CKN.ofReal_threeHalves, ENNReal.ofReal_ofNat] using
      hreal.ennrealOfReal
  have hOne : (1 : ℝ≥0∞) ≤ (3 / 2 : ℝ≥0∞) := by
    rw [← CKN.ofReal_threeHalves]
    simpa using ENNReal.ofReal_le_ofReal
      (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have hcomp (i : Fin 3) :=
    stability_tendsto_eLpNorm_component_three μ U u hU hconv i
  have hFn (n : ℕ) (i : Fin 3) : MemLp
      (fun z : ParabolicPoint => U n z i * U n z i)
      (3 / 2 : ℝ≥0∞) μ := by
    have h : MemLp
        ((fun z : ParabolicPoint => U n z i) *
          (fun z : ParabolicPoint => U n z i))
        (3 / 2 : ℝ≥0∞) μ :=
      ((memLp_pi_iff.mp (hU n)) i).mul
        ((memLp_pi_iff.mp (hU n)) i)
    exact h
  have hFg (i : Fin 3) : MemLp
      (fun z : ParabolicPoint => u z i * u z i)
      (3 / 2 : ℝ≥0∞) μ := by
    have h : MemLp
        ((fun z : ParabolicPoint => u z i) *
          (fun z : ParabolicPoint => u z i))
        (3 / 2 : ℝ≥0∞) μ :=
      ((memLp_pi_iff.mp hu) i).mul ((memLp_pi_iff.mp hu) i)
    exact h
  have hIntN (n : ℕ) (i : Fin 3) : Integrable
      (fun z : ParabolicPoint => U n z i * U n z i * T z) μ :=
    stability_integrable_mul_bounded_test μ hOne (hFn n i) hT
  have hIntG (i : Fin 3) : Integrable
      (fun z : ParabolicPoint => u z i * u z i * T z) μ :=
    stability_integrable_mul_bounded_test μ hOne (hFg i) hT
  have hterm (i : Fin 3) :=
    stability_tendsto_integral_quadratic_test μ
      (fun n z => U n z i) (fun n z => U n z i)
      (fun z => u z i) (fun z => u z i) T
      (fun n => (memLp_pi_iff.mp (hU n)) i)
      (fun n => (memLp_pi_iff.mp (hU n)) i)
      ((memLp_pi_iff.mp hu) i) ((memLp_pi_iff.mp hu) i)
      hT (hcomp i) (hcomp i)
  refine ⟨fun n => integrable_finsetSum Finset.univ
      (fun i _ => hIntN n i),
    integrable_finsetSum Finset.univ (fun i _ => hIntG i), ?_⟩
  exact stability_tendsto_integral_finsetSum μ Finset.univ
    (fun n i z => U n z i * U n z i * T z)
    (fun i z => u z i * u z i * T z)
    (fun n i _ => hIntN n i) (fun i _ => hIntG i)
    (fun i _ => hterm i)

private instance : ENNReal.HolderTriple (3 / 2 : ℝ≥0∞) 3 1 := by
  have hreal : Real.HolderTriple (3 / 2) 3 1 :=
    ⟨by norm_num, by norm_num, by norm_num⟩
  simpa [CKN.ofReal_threeHalves] using hreal.ennrealOfReal

/-- An L^{3/2} field times an L³ field can be paired with a bounded energy
test derivative. -/
theorem lerayAssembly_flux_integrable
    {μ : Measure ParabolicPoint}
    (F G φ : ParabolicPoint → ℝ)
    (hF : MemLp F (3 / 2 : ℝ≥0∞) μ)
    (hG : MemLp G 3 μ) (hφ : MemLp φ ∞ μ) :
    Integrable (fun z => F z * G z * φ z) μ := by
  have hprod : MemLp (F * G) 1 μ := hF.mul hG
  have htest : MemLp (φ • (F * G)) 1 μ := hφ.smul hprod
  have hres : MemLp (fun z => F z * G z * φ z) 1 μ := by
    convert htest using 1
    funext z
    simp [smul_eq_mul, mul_comm, mul_left_comm]
  exact memLp_one_iff_integrable.mp hres

/-- Strong L³ convergence of velocity and mollified transport velocity
passes the regularized cubic energy flux to its limit. -/
theorem lerayAssembly_cubicTerm_tendsto
    (μ : Measure ParabolicPoint)
    (U J : ℕ → ParabolicPoint → Vec3) (u : ParabolicPoint → Vec3)
    (hU : ∀ n, MemLp (U n) 3 μ) (hJ : ∀ n, MemLp (J n) 3 μ)
    (hu : MemLp u 3 μ)
    (hUconv : Tendsto (fun n => eLpNorm (U n - u) 3 μ) atTop (nhds 0))
    (hJconv : Tendsto (fun n => eLpNorm (J n - u) 3 μ) atTop (nhds 0))
    (φ : Fin 3 → ParabolicPoint → ℝ)
    (hφ : ∀ j, MemLp (φ j) ∞ μ) :
    (∀ n, Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
      U n z i * U n z i * J n z j * φ j z) μ) ∧
    Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
      u z i * u z i * u z j * φ j z) μ ∧
    Tendsto (fun n => ∫ z, ∑ i : Fin 3, ∑ j : Fin 3,
      U n z i * U n z i * J n z j * φ j z ∂μ) atTop
      (nhds (∫ z, ∑ i : Fin 3, ∑ j : Fin 3,
        u z i * u z i * u z j * φ j z ∂μ)) := by
  let : ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (3 / 2 : ℝ≥0∞) := by
    have hreal : Real.HolderTriple 3 3 (3 / 2) :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa only [CKN.ofReal_threeHalves, ENNReal.ofReal_ofNat] using
      hreal.ennrealOfReal
  have hUcomp (i : Fin 3) :=
    stability_tendsto_eLpNorm_component_three μ U u hU hUconv i
  have hJcomp (j : Fin 3) :=
    stability_tendsto_eLpNorm_component_three μ J u hJ hJconv j
  have hFn (n : ℕ) (i : Fin 3) : MemLp
      (fun z : ParabolicPoint => U n z i * U n z i)
      (3 / 2 : ℝ≥0∞) μ := by
    have h : MemLp
        ((fun z : ParabolicPoint => U n z i) *
          (fun z : ParabolicPoint => U n z i))
        (3 / 2 : ℝ≥0∞) μ :=
      ((memLp_pi_iff.mp (hU n)) i).mul
        ((memLp_pi_iff.mp (hU n)) i)
    exact h
  have hFg (i : Fin 3) : MemLp
      (fun z : ParabolicPoint => u z i * u z i)
      (3 / 2 : ℝ≥0∞) μ := by
    have h : MemLp
        ((fun z : ParabolicPoint => u z i) *
          (fun z : ParabolicPoint => u z i))
        (3 / 2 : ℝ≥0∞) μ :=
      ((memLp_pi_iff.mp hu) i).mul ((memLp_pi_iff.mp hu) i)
    exact h
  have hQconv (i : Fin 3) :=
    stability_tendsto_eLpNorm_product_three
      (fun n z => U n z i) (fun n z => U n z i)
      (fun z => u z i) (fun z => u z i)
      (fun n => (memLp_pi_iff.mp (hU n)) i)
      (fun n => (memLp_pi_iff.mp (hU n)) i)
      ((memLp_pi_iff.mp hu) i) ((memLp_pi_iff.mp hu) i)
      (hUcomp i) (hUcomp i)
  have hIntN (n : ℕ) (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint =>
        U n z i * U n z i * J n z j * φ j z) μ :=
    lerayAssembly_flux_integrable
      (fun z => U n z i * U n z i)
      (fun z => J n z j) (φ j)
      (hFn n i) ((memLp_pi_iff.mp (hJ n)) j) (hφ j)
  have hIntG (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint => u z i * u z i * u z j * φ j z) μ :=
    lerayAssembly_flux_integrable
      (fun z => u z i * u z i) (fun z => u z j) (φ j)
      (hFg i) ((memLp_pi_iff.mp hu) j) (hφ j)
  have hterm (i j : Fin 3) :=
    stability_flux_product_tendsto
      (fun n z => U n z i * U n z i)
      (fun n z => J n z j)
      (fun z => u z i * u z i) (fun z => u z j) (φ j)
      (fun n => hFn n i) (fun n => (memLp_pi_iff.mp (hJ n)) j)
      (hFg i) ((memLp_pi_iff.mp hu) j) (hφ j)
      (hQconv i) (hJcomp j)
  have hinner (i : Fin 3) :=
    stability_tendsto_integral_finsetSum μ Finset.univ
      (fun n j z => U n z i * U n z i * J n z j * φ j z)
      (fun j z => u z i * u z i * u z j * φ j z)
      (fun n j _ => hIntN n i j) (fun j _ => hIntG i j)
      (fun j _ => hterm i j)
  refine ⟨fun n => integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hIntN n i j)),
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hIntG i j)), ?_⟩
  exact stability_tendsto_integral_finsetSum μ Finset.univ
    (fun n i z => ∑ j : Fin 3,
      U n z i * U n z i * J n z j * φ j z)
    (fun i z => ∑ j : Fin 3,
      u z i * u z i * u z j * φ j z)
    (fun n i _ => integrable_finsetSum Finset.univ (fun j _ => hIntN n i j))
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hIntG i j))
    (fun i _ => hinner i)

/-- Strong local pressure and velocity convergence passes the pressure
energy flux to its limit. -/
theorem lerayAssembly_pressureFlux_tendsto
    (μ : Measure ParabolicPoint)
    (P : ℕ → ParabolicPoint → ℝ) (p : ParabolicPoint → ℝ)
    (U : ℕ → ParabolicPoint → Vec3) (u : ParabolicPoint → Vec3)
    (hP : ∀ n, MemLp (P n) (3 / 2 : ℝ≥0∞) μ)
    (hp : MemLp p (3 / 2 : ℝ≥0∞) μ)
    (hU : ∀ n, MemLp (U n) 3 μ) (hu : MemLp u 3 μ)
    (hPconv : Tendsto (fun n => eLpNorm (P n - p)
      (3 / 2 : ℝ≥0∞) μ) atTop (nhds 0))
    (hUconv : Tendsto (fun n => eLpNorm (U n - u) 3 μ)
      atTop (nhds 0))
    (φ : Fin 3 → ParabolicPoint → ℝ)
    (hφ : ∀ j, MemLp (φ j) ∞ μ) :
    (∀ n, Integrable (fun z => ∑ j : Fin 3,
      P n z * U n z j * φ j z) μ) ∧
    Integrable (fun z => ∑ j : Fin 3,
      p z * u z j * φ j z) μ ∧
    Tendsto (fun n => ∫ z, ∑ j : Fin 3,
      P n z * U n z j * φ j z ∂μ) atTop
      (nhds (∫ z, ∑ j : Fin 3,
        p z * u z j * φ j z ∂μ)) := by
  have hUcomp (j : Fin 3) :=
    stability_tendsto_eLpNorm_component_three μ U u hU hUconv j
  have hIntN (n : ℕ) (j : Fin 3) : Integrable
      (fun z : ParabolicPoint => P n z * U n z j * φ j z) μ :=
    lerayAssembly_flux_integrable (P n) (fun z => U n z j) (φ j)
      (hP n) ((memLp_pi_iff.mp (hU n)) j) (hφ j)
  have hIntG (j : Fin 3) : Integrable
      (fun z : ParabolicPoint => p z * u z j * φ j z) μ :=
    lerayAssembly_flux_integrable p (fun z => u z j) (φ j)
      hp ((memLp_pi_iff.mp hu) j) (hφ j)
  have hterm (j : Fin 3) :=
    stability_flux_product_tendsto P (fun n z => U n z j)
      p (fun z => u z j) (φ j)
      hP (fun n => (memLp_pi_iff.mp (hU n)) j)
      hp ((memLp_pi_iff.mp hu) j) (hφ j)
      hPconv (hUcomp j)
  refine ⟨fun n => integrable_finsetSum Finset.univ
      (fun j _ => hIntN n j),
    integrable_finsetSum Finset.univ (fun j _ => hIntG j), ?_⟩
  exact stability_tendsto_integral_finsetSum μ Finset.univ
    (fun n j z => P n z * U n z j * φ j z)
    (fun j z => p z * u z j * φ j z)
    (fun n j _ => hIntN n j) (fun j _ => hIntG j)
    (fun j _ => hterm j)

/-- The regularized local-energy right side splits into quadratic energy,
transport flux, and pressure flux. -/
theorem lerayAssembly_energyRhs_decompose
    (μ : Measure ParabolicPoint)
    (U J : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (T : ParabolicPoint → ℝ)
    (φ : Fin 3 → ParabolicPoint → ℝ)
    (hA : Integrable (fun z => ∑ i : Fin 3,
      U z i * U z i * T z) μ)
    (hB : Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
      U z i * U z i * J z j * φ j z) μ)
    (hC : Integrable (fun z => ∑ j : Fin 3,
      p z * U z j * φ j z) μ) :
    (∫ z, vec3EuclideanNorm (U z) ^ (2 : ℕ) * T z +
      ∑ j : Fin 3,
        (vec3EuclideanNorm (U z) ^ (2 : ℕ) * J z j +
          2 * p z * U z j) * φ j z ∂μ) =
      (∫ z, ∑ i : Fin 3, U z i * U z i * T z ∂μ) +
      (∫ z, ∑ i : Fin 3, ∑ j : Fin 3,
        U z i * U z i * J z j * φ j z ∂μ) +
      2 * (∫ z, ∑ j : Fin 3, p z * U z j * φ j z ∂μ) := by
  let A : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, U z i * U z i * T z
  let B : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, ∑ j : Fin 3,
      U z i * U z i * J z j * φ j z
  let C : ParabolicPoint → ℝ := fun z =>
    ∑ j : Fin 3, p z * U z j * φ j z
  have hpoint : (fun z => vec3EuclideanNorm (U z) ^ (2 : ℕ) * T z +
      ∑ j : Fin 3,
        (vec3EuclideanNorm (U z) ^ (2 : ℕ) * J z j +
          2 * p z * U z j) * φ j z) =
      (fun z => A z + B z + 2 * C z) := by
    funext z
    rw [gauss_vec3EuclideanNorm_sq]
    simp only [A, B, C, Fin.sum_univ_three]
    ring
  rw [hpoint]
  change (∫ z, A z + B z + 2 * C z ∂μ) =
    (∫ z, A z ∂μ) + (∫ z, B z ∂μ) + 2 * (∫ z, C z ∂μ)
  have hAB : Integrable (fun z => A z + B z) μ := hA.add hB
  rw [integral_add hAB (hC.const_mul 2), integral_add hA hB,
    integral_const_mul]

/-- The regularized local-energy right side converges to the unregularized
right side under the strong velocity, transport, and pressure limits. -/
theorem lerayAssembly_energyRhs_tendsto
    (μ : Measure ParabolicPoint) [IsFiniteMeasure μ]
    (U J : ℕ → ParabolicPoint → Vec3) (u : ParabolicPoint → Vec3)
    (P : ℕ → ParabolicPoint → ℝ) (p : ParabolicPoint → ℝ)
    (hU : ∀ n, MemLp (U n) 3 μ) (hJ : ∀ n, MemLp (J n) 3 μ)
    (hu : MemLp u 3 μ)
    (hP : ∀ n, MemLp (P n) (3 / 2 : ℝ≥0∞) μ)
    (hp : MemLp p (3 / 2 : ℝ≥0∞) μ)
    (hUconv : Tendsto (fun n => eLpNorm (U n - u) 3 μ) atTop (nhds 0))
    (hJconv : Tendsto (fun n => eLpNorm (J n - u) 3 μ) atTop (nhds 0))
    (hPconv : Tendsto (fun n => eLpNorm (P n - p)
      (3 / 2 : ℝ≥0∞) μ) atTop (nhds 0))
    (T : ParabolicPoint → ℝ) (hT : MemLp T ∞ μ)
    (φ : Fin 3 → ParabolicPoint → ℝ)
    (hφ : ∀ j, MemLp (φ j) ∞ μ) :
    Tendsto (fun n => ∫ z,
      vec3EuclideanNorm (U n z) ^ (2 : ℕ) * T z +
        ∑ j : Fin 3,
          (vec3EuclideanNorm (U n z) ^ (2 : ℕ) * J n z j +
            2 * P n z * U n z j) * φ j z ∂μ) atTop
      (nhds (∫ z,
        vec3EuclideanNorm (u z) ^ (2 : ℕ) * T z +
          ∑ j : Fin 3,
            (vec3EuclideanNorm (u z) ^ (2 : ℕ) * u z j +
              2 * p z * u z j) * φ j z ∂μ)) := by
  obtain ⟨hAn, hA, hAc⟩ :=
    lerayAssembly_quadraticTerm_tendsto μ U u hU hu hUconv T hT
  obtain ⟨hBn, hB, hBc⟩ :=
    lerayAssembly_cubicTerm_tendsto μ U J u
      hU hJ hu hUconv hJconv φ hφ
  obtain ⟨hCn, hC, hCc⟩ :=
    lerayAssembly_pressureFlux_tendsto μ P p U u
      hP hp hU hu hPconv hUconv φ hφ
  have hseq (n : ℕ) := lerayAssembly_energyRhs_decompose μ
    (U n) (J n) (P n) T φ (hAn n) (hBn n) (hCn n)
  have hlim := lerayAssembly_energyRhs_decompose μ
    u u p T φ hA hB hC
  have hconv := (hAc.add hBc).add (hCc.const_mul 2)
  simpa only [hseq, hlim] using hconv

/-- The regularized local-energy flux is supported in the test function's
compact support. -/
theorem lerayAssembly_regEnergyRhs_localBox
    {Ω' : Set Vec3} {J : Set ℝ}
    (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (Set.univ : Set Vec3) (Ioi 0))
    (hKbox : tsupport (show ParabolicPoint → ℝ from ψ) ⊆
      spaceTimeSet Ω' J)
    (U Jv : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      vec3EuclideanNorm (U z) ^ (2 : ℕ) *
          (timePartial ψ z + ∑ i : Fin 3,
            spatialSecondPartial ψ i i z) +
        ∑ i : Fin 3,
          (vec3EuclideanNorm (U z) ^ (2 : ℕ) * Jv z i +
            2 * p z * U z i) * spatialPartial ψ i z) =
      ∫ z in spaceTimeSet Ω' J,
        vec3EuclideanNorm (U z) ^ (2 : ℕ) *
            (timePartial ψ z + ∑ i : Fin 3,
              spatialSecondPartial ψ i i z) +
          ∑ i : Fin 3,
            (vec3EuclideanNorm (U z) ^ (2 : ℕ) * Jv z i +
              2 * p z * U z i) * spatialPartial ψ i z := by
  let F : ParabolicPoint → ℝ := fun z =>
    vec3EuclideanNorm (U z) ^ (2 : ℕ) *
        (timePartial ψ z + ∑ i : Fin 3,
          spatialSecondPartial ψ i i z) +
      ∑ i : Fin 3,
        (vec3EuclideanNorm (U z) ^ (2 : ℕ) * Jv z i +
          2 * p z * U z i) * spatialPartial ψ i z
  have hzero {z : ParabolicPoint}
      (hz : z ∉ tsupport (show ParabolicPoint → ℝ from ψ)) : F z = 0 := by
    have hzprod : (z : Vec3 × ℝ) ∉ tsupport ψ := by
      intro hmem
      exact hz (by rwa [tsupport_parabolic_eq])
    have htime : timePartial ψ z = 0 :=
      timePartial_eq_zero_off_tsupport hzprod
    have hspace (i : Fin 3) : spatialPartial ψ i z = 0 :=
      spatialPartial_eq_zero_off_tsupport hzprod i
    have hsecond (i : Fin 3) : spatialSecondPartial ψ i i z = 0 :=
      spatialSecondPartial_eq_zero_off_tsupport hzprod i i
    simp [F, htime, hspace, hsecond]
  have hglob : ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), F z =
      ∫ z, F z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    exact hzero (fun hmem => hz
      (tsupport_parabolic_subset_spaceTimeSet hψ hmem))
  have hloc : ∫ z in spaceTimeSet Ω' J, F z = ∫ z, F z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    exact hzero (fun hmem => hz (hKbox hmem))
  exact hglob.trans hloc.symm

/-- The regularized local-energy equality passes directly to the limit on a
local box by weighted gradient lower semicontinuity and strong flux convergence
((S4) of `thm:leray`). -/
theorem lerayAssembly_localEnergy_limit
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : CKN.localBox (Set.univ : Set Vec3) (Ioi 0) Ω' J)
    (U Jv : ℕ → ParabolicPoint → Vec3)
    (Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (Pseq : ℕ → ParabolicPoint → ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ)
    (ψ : ParabolicPoint → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (Set.univ : Set Vec3) (Ioi 0))
    (hKbox : tsupport (show ParabolicPoint → ℝ from ψ) ⊆
      spaceTimeSet Ω' J)
    (hψpos : ∀ z, 0 ≤ ψ z)
    (hULocal : ∀ n, MemLp (U n) 3
      (volume.restrict (spaceTimeSet Ω' J)))
    (hJLocal : ∀ n, MemLp (Jv n) 3
      (volume.restrict (spaceTimeSet Ω' J)))
    (huLocal : MemLp u 3 (volume.restrict (spaceTimeSet Ω' J)))
    (hUconv : Tendsto (fun n => eLpNorm (U n - u) 3
      (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0))
    (hJconv : Tendsto (fun n => eLpNorm (Jv n - u) 3
      (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0))
    (hDseqLocal : ∀ n, MemLp (Dseq n) 2
      (volume.restrict (spaceTimeSet Ω' J)))
    (hDuLocal : MemLp Du 2 (volume.restrict (spaceTimeSet Ω' J)))
    (hweak : ∀ i j : Fin 3, ∀ w : ParabolicPoint → ℝ,
      MemLp w 2 (volume.restrict (spaceTimeSet Ω' J)) →
      Tendsto (fun n => ∫ z in spaceTimeSet Ω' J,
        Dseq n z i j * w z) atTop
        (nhds (∫ z in spaceTimeSet Ω' J, Du z i j * w z)))
    (hPseqLocal : ∀ n, MemLp (Pseq n) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet Ω' J)))
    (hpLocal : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet Ω' J)))
    (hPconv : Tendsto
      (fun n => eLpNorm (Pseq n - p) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0))
    (hreg : ∀ n,
      2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          spatialGradientSq (U n) (Dseq n) z * ψ z =
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          vec3EuclideanNorm (U n z) ^ (2 : ℕ) *
              (timePartial ψ z + ∑ i : Fin 3,
                spatialSecondPartial ψ i i z) +
            ∑ i : Fin 3,
              (vec3EuclideanNorm (U n z) ^ (2 : ℕ) * Jv n z i +
                2 * Pseq n z * U n z i) * spatialPartial ψ i z) :
    2 * ∫ z in spaceTimeSet Ω' J, spatialGradientSq u Du z * ψ z ≤
      ∫ z in spaceTimeSet Ω' J,
        vec3EuclideanNorm (u z) ^ (2 : ℕ) *
            (timePartial ψ z + ∑ i : Fin 3,
              spatialSecondPartial ψ i i z) +
          ∑ i : Fin 3,
            (vec3EuclideanNorm (u z) ^ (2 : ℕ) * u z i +
              2 * p z * u z i) * spatialPartial ψ i z := by
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  let : IsFiniteMeasure μ := stability_localBox_finiteMeasure hbox
  have hψTop : MemLp (fun z : ParabolicPoint => ψ z) ∞ μ :=
    stability_energyTest_memLp_top ψ hψ
  have hψnonneg : ∀ᵐ z ∂μ, 0 ≤ ψ z :=
    Eventually.of_forall fun z => hψpos (parabolicHomeomorph z)
  have hgrad := lerayAssembly_weightedGradient_matrix μ
    Dseq Du hDseqLocal hDuLocal hweak
    (fun z => ψ z) hψTop hψnonneg
  have hPseqLocalThreeHalves (n : ℕ) : MemLp (Pseq n) (3 / 2 : ℝ≥0∞) μ := by
    simpa only [CKN.ofReal_threeHalves] using hPseqLocal n
  have hpLocalThreeHalves : MemLp p (3 / 2 : ℝ≥0∞) μ := by
    simpa only [CKN.ofReal_threeHalves] using hpLocal
  have hPconvThreeHalves : Tendsto
      (fun n => eLpNorm (Pseq n - p) (3 / 2 : ℝ≥0∞) μ)
      atTop (nhds 0) := by
    simpa only [CKN.ofReal_threeHalves] using hPconv
  have hRconv := lerayAssembly_energyRhs_tendsto μ
    U Jv u Pseq p hULocal hJLocal huLocal hPseqLocalThreeHalves
    hpLocalThreeHalves hUconv hJconv hPconvThreeHalves
    (fun z => timePartial ψ z + ∑ i : Fin 3,
      spatialSecondPartial ψ i i z)
    (stability_energyLaplacian_memLp_top ψ hψ)
    (fun i z => spatialPartial ψ i z)
    (fun i => stability_energySpatial_memLp_top ψ hψ i)
  let A (n : ℕ) : ℝ :=
    ∫ z in spaceTimeSet Ω' J, spatialGradientSq (U n) (Dseq n) z * ψ z
  let B : ℝ :=
    ∫ z in spaceTimeSet Ω' J, spatialGradientSq u Du z * ψ z
  let C (n : ℕ) : ℝ := ∑ i : Fin 3, ∑ j : Fin 3,
    ∫ z in spaceTimeSet Ω' J, Dseq n z i j * Du z i j * ψ z
  let R (n : ℕ) : ℝ := ∫ z in spaceTimeSet Ω' J,
    vec3EuclideanNorm (U n z) ^ (2 : ℕ) *
        (timePartial ψ z + ∑ i : Fin 3,
          spatialSecondPartial ψ i i z) +
      ∑ i : Fin 3,
        (vec3EuclideanNorm (U n z) ^ (2 : ℕ) * Jv n z i +
          2 * Pseq n z * U n z i) * spatialPartial ψ i z
  let S : ℝ := ∫ z in spaceTimeSet Ω' J,
    vec3EuclideanNorm (u z) ^ (2 : ℕ) *
        (timePartial ψ z + ∑ i : Fin 3,
          spatialSecondPartial ψ i i z) +
      ∑ i : Fin 3,
        (vec3EuclideanNorm (u z) ^ (2 : ℕ) * u z i +
          2 * p z * u z i) * spatialPartial ψ i z
  have hCconv : Tendsto C atTop (nhds B) := hgrad.1
  have hpolar : ∀ n, 2 * C n ≤ A n + B := hgrad.2
  have hRconv' : Tendsto R atTop (nhds S) := hRconv
  have henergyN (n : ℕ) : 2 * A n = R n := by
    have h := hreg n
    rw [stability_energy_gradient_integral_eq_localBox ψ hψ hKbox
      (U n) (Dseq n),
      lerayAssembly_regEnergyRhs_localBox ψ hψ hKbox
        (U n) (Jv n) (Pseq n)] at h
    exact h
  have hpoint (n : ℕ) : 4 * C n ≤ R n + 2 * B := by
    linarith only [hpolar n, henergyN n]
  have hlimit : 4 * B ≤ S + 2 * B :=
    le_of_tendsto_of_tendsto' (hCconv.const_mul 4)
      (hRconv'.add_const (2 * B)) hpoint
  have hlocal : 2 * B ≤ S := by
    linarith only [hlimit]
  simpa [A, B, S] using hlocal

end CKN.Leray
