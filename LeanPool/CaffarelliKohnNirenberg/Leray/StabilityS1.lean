/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityS1LocalCore
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityS1WeakGradient

/-!
# Stability S1

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- The local data clauses of suitable weak solutions are stable under the
convergences and the uniform slice bound in `thm:stability`. -/
theorem stability_suitable_data
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (u : ℕ → ParabolicPoint → Vec3)
    (Du : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (p : ℕ → ParabolicPoint → ℝ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (r : ParabolicPoint → ℝ)
    (hsol : ∀ n, IsSuitableWeakSolution Ω I q (u n) (Du n) (p n) 0)
    (hbound : ∀ Ω' J, localBox Ω I Ω' J →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n,
        essSup (fun t => ∫⁻ x in Ω', ‖u n (x, t)‖ₑ ^ (2 : ℝ))
          (volume.restrict J) ≤ M)
    (huConv : ∀ Ω' J, localBox Ω I Ω' J → Tendsto
      (fun n => eLpNorm (u n - v) 3
        (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0))
    (hDv : ∀ Ω' J, localBox Ω I Ω' J →
      MemLp Dv 2 (volume.restrict (spaceTimeSet Ω' J)))
    (hDuWeak : ∀ Ω' J, localBox Ω I Ω' J →
      ∀ i j : Fin 3, ∀ w : Vec3 × ℝ → ℝ,
      MemLp w 2 ((volume.restrict Ω').prod (volume.restrict J)) →
      Tendsto (fun n => ∫ z, Du n (z.1, z.2) i j * w z
        ∂(volume.restrict Ω').prod (volume.restrict J)) atTop
        (nhds (∫ z, Dv (z.1, z.2) i j * w z
          ∂(volume.restrict Ω').prod (volume.restrict J))))
    (hpConv : ∀ Ω' J, localBox Ω I Ω' J → Tendsto
      (fun n => eLpNorm (p n - r) (3 / 2 : ℝ≥0∞)
        (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0)) :
    IsSuitableWeakSolutionData Ω I q v Dv r 0 := by
  have hdata := (isSuitableWeakSolution_iff_integrable.mp (hsol 0)).toData
  refine ⟨hdata.isOpen_space, hdata.isOpen_time,
    hdata.ordConnected_time, hdata.five_halves_lt_exponent,
    (fun Ω' J hbox => hdata.force_localVecLp hbox), ?_⟩
  intro Ω' J hbox
  obtain ⟨M, hM, hMbnd⟩ := hbound Ω' J hbox
  obtain ⟨hvMeas, hDvMeas, hrMeas, hvSlice, hEnergy, hrLp⟩ :=
    stability_s1_local_integrability u Du p v Dv r hsol hbox
      (huConv Ω' J hbox) (hDv Ω' J hbox) (hpConv Ω' J hbox)
      M hM hMbnd
  exact ⟨hvMeas, hDvMeas, hrMeas,
    hdata.aestronglyMeasurable_force hbox,
    hvSlice, hEnergy, hrLp, hdata.memLp_force hbox,
    stability_s1_weak_gradient_on_localBox u Du p v Dv hsol hbox
      (huConv Ω' J hbox) (hDv Ω' J hbox) (hDuWeak Ω' J hbox)⟩

end CKN
