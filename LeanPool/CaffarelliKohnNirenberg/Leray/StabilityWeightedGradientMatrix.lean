/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityWeightedProductIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityWeakComponentLocal
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalGradientLp
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityEnergyTest

/-!
# Stability Weighted Gradient Matrix

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- Weak gradient convergence supplies the weighted mixed-energy limit and
the polarization bound used in (S4). -/
theorem stability_weighted_gradient_matrix
    {Ω Ω' : Set Vec3} {I J : Set ℝ} {q : ℝ}
    (u : ℕ → ParabolicPoint → Vec3)
    (Du : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (p : ℕ → ParabolicPoint → ℝ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (hsol : ∀ n, IsSuitableWeakSolution Ω I q (u n) (Du n) (p n) 0)
    (hbox : localBox Ω I Ω' J)
    (hDv : MemLp Dv 2 (volume.restrict (spaceTimeSet Ω' J)))
    (hDuWeak : ∀ i j : Fin 3, ∀ w : Vec3 × ℝ → ℝ,
      MemLp w 2 ((volume.restrict Ω').prod (volume.restrict J)) →
      Tendsto (fun n => ∫ z, Du n (z.1, z.2) i j * w z
        ∂(volume.restrict Ω').prod (volume.restrict J)) atTop
        (nhds (∫ z, Dv (z.1, z.2) i j * w z
          ∂(volume.restrict Ω').prod (volume.restrict J))))
    (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hψpos : ∀ z, 0 ≤ ψ z) :
    Tendsto (fun n => ∑ i : Fin 3, ∑ j : Fin 3,
      ∫ z in spaceTimeSet Ω' J, Du n z i j * Dv z i j * ψ z) atTop
      (nhds (∫ z in spaceTimeSet Ω' J,
        spatialGradientSq v Dv z * ψ z)) ∧
    (∀ n, 2 * (∑ i : Fin 3, ∑ j : Fin 3,
      ∫ z in spaceTimeSet Ω' J, Du n z i j * Dv z i j * ψ z) ≤
      (∫ z in spaceTimeSet Ω' J,
        spatialGradientSq (u n) (Du n) z * ψ z) +
      (∫ z in spaceTimeSet Ω' J,
        spatialGradientSq v Dv z * ψ z)) := by
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  let _ : IsFiniteMeasure μ := stability_localBox_finiteMeasure hbox
  have hψTop : MemLp (fun z : ParabolicPoint => ψ z) ∞ μ :=
    stability_energyTest_memLp_top ψ hψ
  have hψnonneg : ∀ᵐ z ∂μ, 0 ≤ ψ z :=
    Eventually.of_forall fun z => hψpos (parabolicHomeomorph z)
  have hDN (n : ℕ) : MemLp (Du n) 2 μ :=
    stability_gradient_memLp_two_on_localBox (hsol n) hbox
  have hFi (n : ℕ) (i j : Fin 3) : MemLp
      (fun z : ParabolicPoint => Du n z i j) 2 μ :=
    (memLp_pi_iff.mp ((memLp_pi_iff.mp (hDN n)) i)) j
  have hGi (i j : Fin 3) : MemLp
      (fun z : ParabolicPoint => Dv z i j) 2 μ :=
    (memLp_pi_iff.mp ((memLp_pi_iff.mp hDv) i)) j
  have hscalar (i j : Fin 3) := stability_weighted_gradient_scalar μ
    (fun n z => Du n z i j) (fun z => Dv z i j) (fun z => ψ z)
    (fun n => hFi n i j) (hGi i j) hψTop hψnonneg
    (fun w hw => stability_weak_component_localBox hbox Du Dv
      hDuWeak i j w hw)
  have hIntN (n : ℕ) (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint => Du n z i j * Du n z i j * ψ z) μ :=
    stability_weighted_product_integrable μ (hFi n i j) (hFi n i j) hψTop
  have hIntG (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint => Dv z i j * Dv z i j * ψ z) μ :=
    stability_weighted_product_integrable μ (hGi i j) (hGi i j) hψTop
  have hEnergyN (n : ℕ) :
      (∫ z in spaceTimeSet Ω' J,
        spatialGradientSq (u n) (Du n) z * ψ z) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z in spaceTimeSet Ω' J,
          Du n z i j * Du n z i j * ψ z := by
    have hpoint : (fun z : ParabolicPoint =>
        spatialGradientSq (u n) (Du n) z * ψ z) =
        (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
          Du n z i j * Du n z i j * ψ z) := by
      funext z
      simp [spatialGradientSq, Finset.sum_mul, pow_two, mul_assoc]
    rw [hpoint]
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hIntN n i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum Finset.univ (fun j _ => hIntN n i j)
  have hEnergyG :
      (∫ z in spaceTimeSet Ω' J, spatialGradientSq v Dv z * ψ z) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z in spaceTimeSet Ω' J,
          Dv z i j * Dv z i j * ψ z := by
    have hpoint : (fun z : ParabolicPoint => spatialGradientSq v Dv z * ψ z) =
        (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
          Dv z i j * Dv z i j * ψ z) := by
      funext z
      simp [spatialGradientSq, Finset.sum_mul, pow_two, mul_assoc]
    rw [hpoint]
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hIntG i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum Finset.univ (fun j _ => hIntG i j)
  have hcrossConv : Tendsto (fun n => ∑ i : Fin 3, ∑ j : Fin 3,
      ∫ z in spaceTimeSet Ω' J, Du n z i j * Dv z i j * ψ z) atTop
      (nhds (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z in spaceTimeSet Ω' J, Dv z i j * Dv z i j * ψ z)) := by
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
        ∫ z in spaceTimeSet Ω' J, Du n z i j * Dv z i j * ψ z) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        2 * (∫ z in spaceTimeSet Ω' J,
          Du n z i j * Dv z i j * ψ z) := by
        simp_rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        ((∫ z in spaceTimeSet Ω' J,
          Du n z i j * Du n z i j * ψ z) +
        (∫ z in spaceTimeSet Ω' J,
          Dv z i j * Dv z i j * ψ z)) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact (hscalar i j).2 n
    _ = (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z in spaceTimeSet Ω' J,
          Du n z i j * Du n z i j * ψ z) +
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z in spaceTimeSet Ω' J,
          Dv z i j * Dv z i j * ψ z) := by
        simp_rw [Finset.sum_add_distrib]

end CKN
