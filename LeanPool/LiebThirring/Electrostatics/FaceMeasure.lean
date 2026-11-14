/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.FaceMeasureDirected
public import LeanPool.LiebThirring.Electrostatics.FaceMeasureMass
public import LeanPool.LiebThirring.Electrostatics.FaceMeasureDensityDecay
public import LeanPool.LiebThirring.Electrostatics.FaceMeasureDecay
import all LeanPool.LiebThirring.Electrostatics.Basic

/-!
# Analytic bounds for the positive Voronoi face measure

The explicit Voronoi face charge satisfies the finite-mass, energy, and decay bounds required by
the potential argument.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace LiebThirring

variable {M : ℕ}

/-- The actual face potential is everywhere finite, including at face points. -/
theorem coulombPotential_voronoiFaceMeasure_lt_top (R : Fin M → Position)
    (hR : Function.Injective R) {Z : ℝ} (hZ : 0 ≤ Z) (x : Position) :
    coulombPotential (voronoiFaceMeasure R hR Z) x < ⊤ := by
  have := isFiniteMeasure_voronoiFaceMeasure R hR hZ
  exact coulombPotential_lt_top_of_local_bound _ _
    (fun x _ε hε => lintegral_coulombKernel_ball_voronoiFaceMeasure_le R hR hZ x hε) x

/-- Self-energy is finite as a consequence of the proved uniform potential bound. -/
theorem coulombEnergy_voronoiFaceMeasure_lt_top (R : Fin M → Position)
    (hR : Function.Injective R) {Z : ℝ} (hZ : 0 ≤ Z) :
    coulombEnergy (voronoiFaceMeasure R hR Z) (voronoiFaceMeasure R hR Z) < ⊤ := by
  have := isFiniteMeasure_voronoiFaceMeasure R hR hZ
  exact coulombEnergy_lt_top_of_local_bound _ _
    (fun x _ε hε => lintegral_coulombKernel_ball_voronoiFaceMeasure_le R hR hZ x hε)

/-- The finite potential, regarded as a real function, is also continuous. -/
theorem continuous_toReal_coulombPotential_voronoiFaceMeasure (R : Fin M → Position)
    (hR : Function.Injective R) {Z : ℝ} (hZ : 0 ≤ Z) :
    Continuous (fun x => (coulombPotential (voronoiFaceMeasure R hR Z) x).toReal) := by
  have := isFiniteMeasure_voronoiFaceMeasure R hR hZ
  exact continuous_toReal_coulombPotential_of_local_bound _ _
    (voronoiLocalCoefficient_nonneg R hZ)
    (fun x _ε hε => lintegral_coulombKernel_ball_voronoiFaceMeasure_le R hR hZ x hε)

/-- Explicit data-dependent coefficient in (6.2). -/
noncomputable def voronoiDecayCoefficient (R : Fin M → Position) (Z : ℝ) : ℝ :=
  ∑ p : NuclearPair M, (4 * Real.pi * nuclearFaceDensityBound R Z p.val.1 p.val.2 +
    6 * Z + 16 * Real.pi * nuclearFaceDecayCoefficient R Z p.val.1 p.val.2)

theorem voronoiDecayCoefficient_nonneg (R : Fin M → Position) {Z : ℝ} (hZ : 0 ≤ Z) :
    0 ≤ voronoiDecayCoefficient R Z := by
  unfold voronoiDecayCoefficient
  apply Finset.sum_nonneg
  intro p _
  have hB := nuclearFaceDensityBound_nonneg R hZ p.val.1 p.val.2
  have hA := nuclearFaceDecayCoefficient_nonneg R hZ p.val.1 p.val.2
  positivity

/-- Apply cubic density decay and the exact planar kernel estimate to one face. -/
theorem coulombPotential_nuclearFaceMeasure_decay (R : Fin M → Position)
    (hR : Function.Injective R) {Z : ℝ} (hZ : 0 ≤ Z)
    (k l : Fin M) (hkl : k ≠ l) (x : Position) :
    coulombPotential (nuclearFaceMeasure R hR Z k l hkl) x ≤ ENNReal.ofReal
      ((4 * Real.pi * nuclearFaceDensityBound R Z k l + 6 * Z +
        16 * Real.pi * nuclearFaceDecayCoefficient R Z k l) / (1 + ‖x‖)) := by
  exact coulombPotential_withDensity_planeMeasure_decay (bisectorNormal R k l)
    (midpoint ℝ (R k) (R l)) (norm_bisectorNormal R hR hkl)
    (bisectorSurfaceFrame R hR k l hkl) (voronoiFaceDensity R Z k l)
    (measurable_voronoiFaceDensity R Z k l) _ _ Z
    (nuclearFaceDecayCoefficient_nonneg R hZ k l) (nuclearFaceDensityBound_nonneg R hZ k l) hZ
    (Eventually.of_forall (voronoiFaceDensity_le_bound R hR hZ k l hkl))
    (Eventually.of_forall (voronoiFaceDensity_le_decay R hR hZ k l hkl))
    (nuclearFaceMeasure_mass_le R hR hZ k l hkl) x

/-- Equation (6.2), with an explicit coefficient depending only on the nuclei and charge. -/
theorem coulombPotential_voronoiFaceMeasure_decay (R : Fin M → Position)
    (hR : Function.Injective R) {Z : ℝ} (hZ : 0 ≤ Z) (x : Position) :
    coulombPotential (voronoiFaceMeasure R hR Z) x ≤
      ENNReal.ofReal (voronoiDecayCoefficient R Z / (1 + ‖x‖)) := by
  change (∫⁻ y, coulombKernel x y ∂voronoiFaceMeasure R hR Z) ≤ _
  rw [voronoiFaceMeasure, lintegral_finsetSum_measure]
  calc
    _ ≤ ∑ p : NuclearPair M, ENNReal.ofReal
        ((4 * Real.pi * nuclearFaceDensityBound R Z p.val.1 p.val.2 + 6 * Z +
          16 * Real.pi * nuclearFaceDecayCoefficient R Z p.val.1 p.val.2) / (1 + ‖x‖)) :=
      Finset.sum_le_sum fun p _ => coulombPotential_nuclearFaceMeasure_decay R hR hZ _ _ _ x
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · congr 1
        simp only [voronoiDecayCoefficient, Finset.sum_div]
      · intro p _
        have hB := nuclearFaceDensityBound_nonneg R hZ p.val.1 p.val.2
        have hA := nuclearFaceDecayCoefficient_nonneg R hZ p.val.1 p.val.2
        positivity

/-- The decay at infinity used in the potential identity. -/
theorem tendsto_coulombPotential_voronoiFaceMeasure_zero (R : Fin M → Position)
    (hR : Function.Injective R) {Z : ℝ} (hZ : 0 ≤ Z) :
    Tendsto (coulombPotential (voronoiFaceMeasure R hR Z))
      (Bornology.cobounded Position) (𝓝 0) :=
  tendsto_coulombPotential_zero_of_decay _ _ (coulombPotential_voronoiFaceMeasure_decay R hR hZ)

/-- The finite real-valued potential tends to zero at infinity as well. -/
theorem tendsto_toReal_coulombPotential_voronoiFaceMeasure_zero (R : Fin M → Position)
    (hR : Function.Injective R) {Z : ℝ} (hZ : 0 ≤ Z) :
    Tendsto (fun x => (coulombPotential (voronoiFaceMeasure R hR Z) x).toReal)
      (Bornology.cobounded Position) (𝓝 0) := by
  simpa only [ENNReal.toReal_zero, Function.comp_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_coulombPotential_voronoiFaceMeasure_zero R hR hZ)

end LiebThirring

end
