/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingAssembly
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingLadder

/-!
# Smoothing of strong solutions

`prop:lps-smoothing`: a strong solution on `[t₀, t₁]` has a representative that is `C^∞` on
`ℝ³ × (t₀, t₁]`.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- `prop:lps-smoothing`: a strong solution of the Navier–Stokes equations on `ℝ³ × (t₀, t₁)`
agrees almost everywhere with a representative that is `C^∞` on `ℝ³ × (t₀, t₁]`. -/
theorem lps_smoothing {t₀ t₁ : ℝ} {U : ParabolicPoint → Vec3}
    {DU : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (h : IsLpsStrongSolution t₀ t₁ U DU p) :
    ∃ R : ParabolicPoint → Vec3,
      R =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))] U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => R z)
        ((Set.univ : Set Vec3) ×ˢ Ioc t₀ t₁) := by
  obtain ⟨-, -, -, ⟨D2u, Dtu, hderiv, hu, hDu, hD2u, hDtu⟩, -⟩ := id h
  exact lps_smoothing_of_ladder h hderiv hu hDu hD2u hDtu
    fun M hM δ hδ hδT => lps_ladder h hderiv hu hDu hD2u hDtu M hM hδ hδT

end ESS
