/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityS1
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityS2
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityS3
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityS4

/-!
# Stability

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- Strong local convergence of velocity and pressure, weak local convergence
of the gradient, and a uniform local slice bound preserve suitable weak
solutions with zero force, as in `thm:stability`. -/
theorem stability_suitable_limit
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
    IsSuitableWeakSolution Ω I q v Dv r 0 := by
  have hdata := stability_suitable_data u Du p v Dv r
    hsol hbound huConv hDv hDuWeak hpConv
  have hdiv := stability_suitable_divergence u Du p v hsol huConv
  have hmom := stability_suitable_momentum u Du p v Dv r
    hsol hdata huConv hDv hDuWeak hpConv
  have hlei := stability_suitable_energy u Du p v Dv r
    hsol hdata huConv hDv hDuWeak hpConv
  rcases hdata with ⟨hΩ, hI, hconn, hq, hforce, hlocal⟩
  exact ⟨hΩ, hI, hconn, hq, hforce, hlocal, hdiv, hmom, hlei⟩

end CKN
