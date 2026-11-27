/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Literal statement construction extracted from Shell/NullDiscs

The moved declarations retain their original text. Later target proofs remain separate.
-/

@[expose] public section

namespace VacuumBellSeparation

noncomputable section

/-- Bilinear spatial product `𝐳 · 𝐰 = Σ_j z_j w_j` on `ℂ³` (no conjugation). -/
def spatialDot (z w : Fin 3 → ℂ) : ℂ := ∑ j, z j * w j

/-- The complex mass shell `𝒬_μ = {z : z₀² - 𝐳·𝐳 = μ²}`; points are pairs `(z₀, 𝐳)`. -/
def complexShell (μ : ℝ) : Set (ℂ × (Fin 3 → ℂ)) :=
  {z | z.1 ^ 2 - spatialDot z.2 z.2 = (μ : ℂ) ^ 2}

/-- Squared Euclidean norm `|z|_E² = |z₀|² + Σ_j |z_j|²`. -/
def euclidSq (z : ℂ × (Fin 3 → ℂ)) : ℝ := ‖z.1‖ ^ 2 + ∑ j, ‖z.2 j‖ ^ 2

/-- Squared Euclidean length of the real part of the spatial components, `|Re 𝐳|²`. -/
def reSpatialSq (z : Fin 3 → ℂ) : ℝ := ∑ j, (z j).re ^ 2

/-- Lorentzian square of the real part, `(Re z)² = (Re z₀)² - |Re 𝐳|²`. -/
def reLorentzSq (z : ℂ × (Fin 3 → ℂ)) : ℝ := z.1.re ^ 2 - reSpatialSq z.2

/-- The compact normalized set `𝒵` of equation (5.4), with `|z|_E ≤ 16` written in squared form. -/
def normalizedTarget : Set (ℝ × (ℂ × (Fin 3 → ℂ))) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ∈ complexShell p.1 ∧ euclidSq p.2 ≤ 16 ^ 2 ∧ reLorentzSq p.2 ≤ -16}

/-- The affine disc `ζ ↦ z + 8𝓔 ζ (0, 𝐧)`. -/
def nullDisc (z : ℂ × (Fin 3 → ℂ)) (En : ℝ) (n : Fin 3 → ℂ) (ζ : ℂ) : ℂ × (Fin 3 → ℂ) :=
  (z.1, fun j => z.2 j + (8 * En : ℂ) * ζ * n j)

/-- Rescaling of a spacetime point by a real factor `1/𝓔`. -/
def scaleBy (En : ℝ) (z : ℂ × (Fin 3 → ℂ)) : ℂ × (Fin 3 → ℂ) :=
  (z.1 / (En : ℂ), fun j => z.2 j / (En : ℂ))

/-! ### Coordinate helpers -/


end
end VacuumBellSeparation
