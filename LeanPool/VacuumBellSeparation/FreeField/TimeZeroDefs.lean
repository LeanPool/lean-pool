/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Defs

/-!
# Primitive time-zero source definitions

Literal compact real spatial tests and their physical one-particle map.
This module has no local proof-module imports.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory

namespace VacuumBellSeparation

/-- Real smooth compactly supported time-zero test functions in three dimensions. -/
abbrev SpatialTestFunction : Type :=
  {f : EuclideanSpace ℝ (Fin 3) → ℝ // ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f}

/-- The position and momentum smearing pair `(f,g)` of Section 2.1. -/
abbrev TimeZeroSource := SpatialTestFunction × SpatialTestFunction

instance : Add SpatialTestFunction where
  add f g := ⟨f.1 + g.1, f.2.1.add g.2.1, f.2.2.add g.2.2⟩

instance : Zero SpatialTestFunction where
  zero := ⟨0, contDiff_const, HasCompactSupport.zero⟩

instance : Neg SpatialTestFunction where
  neg f := ⟨-f.1, f.2.1.neg, f.2.2.neg⟩

instance : AddCommGroup SpatialTestFunction where
  add_assoc f g h := Subtype.ext (add_assoc f.1 g.1 h.1)
  zero_add f := Subtype.ext (zero_add f.1)
  add_zero f := Subtype.ext (add_zero f.1)
  nsmul := nsmulRec
  neg_add_cancel f := Subtype.ext (neg_add_cancel f.1)
  zsmul := zsmulRec
  add_comm f g := Subtype.ext (add_comm f.1 g.1)

/-- The manuscript's unnormalized spatial Fourier transform. -/
noncomputable def spatialFourier (f : SpatialTestFunction) (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  ∫ x : EuclideanSpace ℝ (Fin 3),
    Complex.exp (-(Complex.I * (⟪p, x⟫_ℝ : ℂ))) * (f.1 x : ℂ)

/-- The time-zero source map appearing before (2.6). -/
noncomputable def timeZeroOneParticle (m : ℝ) (u : TimeZeroSource)
    (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  spatialFourier u.1 p + Complex.I * (dispersion m p : ℂ) * spatialFourier u.2 p

/-- The mass-shell pairing of literal time-zero sources. -/
noncomputable def timeZeroOneParticleInner (m : ℝ) (u v : TimeZeroSource) : ℂ :=
  ∫ p : EuclideanSpace ℝ (Fin 3),
    conj (timeZeroOneParticle m u p) * timeZeroOneParticle m v p *
      ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ)

/-- The two Fourier multiplier terms, with the exact `1/(2(2π)^3)` normalization. -/
noncomputable def timeZeroFourierDiagonal (m : ℝ) (u v : TimeZeroSource) : ℂ :=
  ((∫ p, (conj (spatialFourier u.1 p) * spatialFourier v.1 p) *
      ((dispersion m p)⁻¹ : ℝ)) +
    (∫ p, (conj (spatialFourier u.2 p) * spatialFourier v.2 p) * (dispersion m p : ℂ))) *
    ((1 / (2 * (2 * Real.pi) ^ 3) : ℝ) : ℂ)

/-- The real covariance expressed by the energy Fourier multipliers. -/
noncomputable def timeZeroFourierCovariance (m : ℝ) (u v : TimeZeroSource) : ℝ :=
  (timeZeroFourierDiagonal m u v).re

end VacuumBellSeparation
