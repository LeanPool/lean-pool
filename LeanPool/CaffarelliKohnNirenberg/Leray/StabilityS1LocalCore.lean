/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityS1Slice
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalEnergy

/-!
# Stability S1Local Core

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- Strong velocity and pressure convergence, weak-gradient `L²` membership,
and the uniform slice bound provide the local integrability clauses of (S1)
in `thm:stability`. -/
theorem stability_s1_local_integrability
    {Ω Ω' : Set Vec3} {I J : Set ℝ} {q : ℝ}
    (u : ℕ → ParabolicPoint → Vec3)
    (Du : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (p : ℕ → ParabolicPoint → ℝ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (r : ParabolicPoint → ℝ)
    (hsol : ∀ n, CKN.IsSuitableWeakSolution Ω I q (u n) (Du n) (p n) 0)
    (hbox : CKN.localBox Ω I Ω' J)
    (huConv : Tendsto
      (fun n => eLpNorm (u n - v) 3
        (volume.restrict (CKN.spaceTimeSet Ω' J))) atTop (nhds 0))
    (hDv : MemLp Dv 2 (volume.restrict (CKN.spaceTimeSet Ω' J)))
    (hpConv : Tendsto
      (fun n => eLpNorm (p n - r) (3 / 2 : ℝ≥0∞)
        (volume.restrict (CKN.spaceTimeSet Ω' J))) atTop (nhds 0))
    (M : ℝ≥0∞) (hM : M < ⊤)
    (hbound : ∀ n,
      essSup (fun t => ∫⁻ x in Ω', ‖u n (x, t)‖ₑ ^ (2 : ℝ))
        (volume.restrict J) ≤ M) :
    AEStronglyMeasurable v (volume.restrict (CKN.spaceTimeSet Ω' J)) ∧
    AEStronglyMeasurable Dv (volume.restrict (CKN.spaceTimeSet Ω' J)) ∧
    AEStronglyMeasurable r (volume.restrict (CKN.spaceTimeSet Ω' J)) ∧
    essSup (fun t => ∫⁻ x in Ω', ‖v (x, t)‖ₑ ^ (2 : ℝ))
      (volume.restrict J) < ⊤ ∧
    (∫⁻ z in CKN.spaceTimeSet Ω' J,
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
    MemLp r (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (CKN.spaceTimeSet Ω' J)) := by
  have huN (n : ℕ) : MemLp (u n) 3
      (volume.restrict (CKN.spaceTimeSet Ω' J)) :=
    stability_velocity_memLp_three_on_localBox (hsol n) hbox
  have hv : MemLp v 3 (volume.restrict (CKN.spaceTimeSet Ω' J)) :=
    Lp.memLp_of_cauchy_tendsto (by norm_num) huN v huConv
  have hpN (n : ℕ) : MemLp (p n) (3 / 2 : ℝ≥0∞)
      (volume.restrict (CKN.spaceTimeSet Ω' J)) := by
    have hdata := (CKN.isSuitableWeakSolution_iff_integrable.mp (hsol n)).toData
    simpa only [CKN.ofReal_threeHalves] using hdata.memLp_pressure hbox
  have hr : MemLp r (3 / 2 : ℝ≥0∞)
      (volume.restrict (CKN.spaceTimeSet Ω' J)) :=
    Lp.memLp_of_cauchy_tendsto (by
      rw [← CKN.ofReal_threeHalves]
      simpa using ENNReal.ofReal_le_ofReal (by norm_num : (1 : ℝ) ≤ 3 / 2))
      hpN r hpConv
  refine ⟨hv.aestronglyMeasurable, hDv.aestronglyMeasurable,
    hr.aestronglyMeasurable, ?_, ?_, ?_⟩
  · exact stability_suitable_limit_slice_energy_lt_top u Du p v hsol hbox
      huConv M hM hbound
  · exact stability_local_energy_lintegral_lt_top hbox v Dv hv hDv
  · simpa only [CKN.ofReal_threeHalves] using hr

end CKN
