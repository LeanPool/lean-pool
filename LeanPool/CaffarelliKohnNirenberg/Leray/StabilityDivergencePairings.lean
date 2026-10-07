/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityComponentConvergence
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalFinite
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport

/-!
# Stability Divergence Pairings

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- The linear divergence pairings pass to a strong local `L³` limit
(`thm:stability`, clause (S2)). -/
theorem stability_divergence_pairings_tendsto
    {Ω Ω' : Set Vec3} {I J : Set ℝ} {q : ℝ}
    (u : ℕ → ParabolicPoint → Vec3)
    (Du : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (p : ℕ → ParabolicPoint → ℝ)
    (v : ParabolicPoint → Vec3)
    (hsol : ∀ n, IsSuitableWeakSolution Ω I q (u n) (Du n) (p n) 0)
    (hbox : localBox Ω I Ω' J)
    (huConv : Tendsto
      (fun n => eLpNorm (u n - v) 3
        (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0))
    (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    Tendsto
      (fun n => ∑ i : Fin 3,
        ∫ z in spaceTimeSet Ω' J,
          spatialPartial ψ i z * u n z i)
      atTop
      (nhds (∑ i : Fin 3,
        ∫ z in spaceTimeSet Ω' J,
          spatialPartial ψ i z * v z i)) := by
  let μ := volume.restrict (spaceTimeSet Ω' J)
  let _ : IsFiniteMeasure μ := stability_localBox_finiteMeasure hbox
  have hFn (n : ℕ) : MemLp (u n) 3 μ :=
    stability_velocity_memLp_three_on_localBox (hsol n) hbox
  apply tendsto_finsetSum
  intro i _hi
  have hFi (n : ℕ) : MemLp (fun z => u n z i) 3 μ :=
    (memLp_pi_iff.mp (hFn n)) i
  have hFiConv := stability_tendsto_eLpNorm_component_three μ u v hFn huConv i
  have htestCont : Continuous
      (fun z : ParabolicPoint => spatialPartial ψ i z) :=
    (spatialPartial_contDiff hψ.1 i).continuous.comp
      parabolicHomeomorph.continuous
  obtain ⟨C, hC⟩ := exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hψ i
  have htest : MemLp (fun z : ParabolicPoint => spatialPartial ψ i z) ∞ μ :=
    memLp_top_of_bound htestCont.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun z => hC (parabolicHomeomorph z))
  exact stability_tendsto_integral_mul_test_of_Lthree μ
    (fun n z => u n z i) (fun z => v z i)
    (fun z => spatialPartial ψ i z) hFi htest hFiConv

end CKN
