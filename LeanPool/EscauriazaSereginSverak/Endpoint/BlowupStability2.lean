/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Stability

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Suitability of a limit follows when the approximating solutions are
suitable from some index onward on the chosen cylinder. -/
theorem blowup_stability_suitable_of_eventually
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (u : ℕ → ParabolicPoint → Vec3)
    (Du : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (p : ℕ → ParabolicPoint → ℝ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (r : ParabolicPoint → ℝ)
    (hsol : ∀ᶠ n in atTop,
      IsSuitableWeakSolution Ω I q (u n) (Du n) (p n) 0)
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
    IsSuitableWeakSolution Ω I q v Dv r 0 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsol
  let u' : ℕ → ParabolicPoint → Vec3 := fun n => u (n + N)
  let Du' : ℕ → ParabolicPoint → Fin 3 → Vec3 := fun n => Du (n + N)
  let p' : ℕ → ParabolicPoint → ℝ := fun n => p (n + N)
  have hsol' (n : ℕ) :
      IsSuitableWeakSolution Ω I q (u' n) (Du' n) (p' n) 0 :=
    hN (n + N) (Nat.le_add_left N n)
  have hbound' : ∀ Ω' J, localBox Ω I Ω' J →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n,
        essSup (fun t => ∫⁻ x in Ω', ‖u' n (x, t)‖ₑ ^ (2 : ℝ))
          (volume.restrict J) ≤ M := by
    intro Ω' J hbox
    obtain ⟨M, hM, hMn⟩ := hbound Ω' J hbox
    exact ⟨M, hM, fun n => hMn (n + N)⟩
  have huConv' : ∀ Ω' J, localBox Ω I Ω' J → Tendsto
      (fun n => eLpNorm (u' n - v) 3
        (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0) := by
    intro Ω' J hbox
    exact (huConv Ω' J hbox).comp (tendsto_add_atTop_nat N)
  have hDuWeak' : ∀ Ω' J, localBox Ω I Ω' J →
      ∀ i j : Fin 3, ∀ w : Vec3 × ℝ → ℝ,
      MemLp w 2 ((volume.restrict Ω').prod (volume.restrict J)) →
      Tendsto (fun n => ∫ z, Du' n (z.1, z.2) i j * w z
        ∂(volume.restrict Ω').prod (volume.restrict J)) atTop
        (nhds (∫ z, Dv (z.1, z.2) i j * w z
          ∂(volume.restrict Ω').prod (volume.restrict J))) := by
    intro Ω' J hbox i j w hw
    exact (hDuWeak Ω' J hbox i j w hw).comp (tendsto_add_atTop_nat N)
  have hpConv' : ∀ Ω' J, localBox Ω I Ω' J → Tendsto
      (fun n => eLpNorm (p' n - r) (3 / 2 : ℝ≥0∞)
        (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0) := by
    intro Ω' J hbox
    exact (hpConv Ω' J hbox).comp (tendsto_add_atTop_nat N)
  exact stability_suitable_limit u' Du' p' v Dv r
    hsol' hbound' huConv' hDv hDuWeak' hpConv'

end ESS
