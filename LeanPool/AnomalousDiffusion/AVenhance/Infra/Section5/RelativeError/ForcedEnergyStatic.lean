/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.DivergenceFreeEnergy

/-!
# Static divergence-free cancellation on periodic `H¹`

For a bounded measurable periodic field that is divergence free against smooth periodic tests, the
transport pairing `∫ b·Du u` vanishes for every periodic `H¹` function `u`. The public names below
reuse the Fourier approximation argument of `Infra.Parabolic.WeakUniqueness.DivergenceFreeEnergy`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Heat
open AVenhance.Infra.Torus
open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Classical
open AVenhance.Infra.Parabolic.WeakUniqueness

local instance divFreeEnergyFiniteUnitCube :
    IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  unfold AVenhance.unitCube
  rw [Measure.restrict_apply_univ, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

local instance divFreeEnergyFiniteUnitCell :
    IsFiniteMeasure (volume.restrict (AVenhance.Infra.Torus.unitCell 2)) := by
  rw [Measure.restrict_congr_set AVenhance.Infra.Torus.unitCell_ae_eq_unitCube]
  infer_instance

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance divFreeEnergyMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance divFreeEnergyIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance divFreeEnergyProbabilityUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance divFreeEnergyProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

theorem ForcedEnergyStatic.divFree_torusInner_cell {f g : Vec 2 → ℝ}
    (hf : MemL2On AVenhance.unitCube f) (hg : MemL2On AVenhance.unitCube g) :
    inner ℝ
        ((weakProjection_realCellToTorus_memLp hf).toLp
          (AVenhance.Infra.Torus.periodicToTorus f))
        ((weakProjection_realCellToTorus_memLp hg).toLp
          (AVenhance.Infra.Torus.periodicToTorus g)) =
      ∫ x in unitCell 2, f x * g x := by
  exact DivergenceFreeEnergy.divFree_torusInner_cell hf hg

theorem ForcedEnergyStatic.divFree_unitCube_measurable :
    MeasurableSet AVenhance.unitCube := by
  exact DivergenceFreeEnergy.divFree_unitCube_measurable

theorem ForcedEnergyStatic.divFree_component_memLp_top_cell
    {b : Vec 2 → Vec 2} (hbMeas : AEStronglyMeasurable b volume)
    (hbBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C) (i : Fin 2) :
    MemLp (fun x => b x i) ⊤ (volume.restrict AVenhance.unitCube) := by
  exact DivergenceFreeEnergy.divFree_component_memLp_top_cell hbMeas hbBound i

theorem ForcedEnergyStatic.divFree_periodicComponent_memLp_top_torus
    {b : Vec 2 → Vec 2} (hbMeas : AEStronglyMeasurable b volume)
    (hbBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C) (i : Fin 2) :
    MemLp (AVenhance.Infra.Torus.periodicToTorus (fun x => b x i)) ⊤ volume := by
  exact DivergenceFreeEnergy.divFree_periodicComponent_memLp_top_torus hbMeas hbBound i

theorem ForcedEnergyStatic.divFree_torus_product_memLp_two
    {b : Vec 2 → Vec 2} (hbMeas : AEStronglyMeasurable b volume)
    (hbBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C)
    {g : Vec 2 → ℝ} (hg : MemL2On AVenhance.unitCube g) (i : Fin 2) :
    MemLp (AVenhance.Infra.Torus.periodicToTorus (fun x => b x i * g x)) 2 volume := by
  exact DivergenceFreeEnergy.divFree_torus_product_memLp_two hbMeas hbBound hg i

theorem ForcedEnergyStatic.divFree_cell_pairing_tendsto
    {F : ℕ → Vec 2 → ℝ} {f g : Vec 2 → ℝ}
    (hFN : ∀ N, MemL2On AVenhance.unitCube (F N))
    (hf : MemL2On AVenhance.unitCube f) (hg : MemL2On AVenhance.unitCube g)
    (hconv : Tendsto (fun N =>
      (weakProjection_realCellToTorus_memLp (hFN N)).toLp
        (AVenhance.Infra.Torus.periodicToTorus (F N))) atTop
      (𝓝 ((weakProjection_realCellToTorus_memLp hf).toLp
        (AVenhance.Infra.Torus.periodicToTorus f)))) :
    Tendsto (fun N => ∫ x in unitCell 2, F N x * g x) atTop
      (𝓝 (∫ x in unitCell 2, f x * g x)) := by
  exact DivergenceFreeEnergy.divFree_cell_pairing_tendsto hFN hf hg hconv

theorem static_divFree_h1_cancellation
    {b : Vec 2 → Vec 2} (hbMeas : AEStronglyMeasurable b volume)
    (hbBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C)
    (hdiv : ∀ f : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
      AVenhance.IsZ2Periodic f →
      ∫ x in unitCell 2, Homogenization.vecDot (b x)
        (AVenhance.spaceGrad f x) = 0)
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hu : AVenhance.IsPeriodicH1With u Du) :
    ∫ x in unitCell 2,
      Homogenization.vecDot (b x) (Du x) * u x = 0 := by
  exact DivergenceFreeEnergy.divFree_static_h1_cancellation hbMeas hbBound hdiv hu

end AVenhance.Infra.Section5.RelativeError

end
