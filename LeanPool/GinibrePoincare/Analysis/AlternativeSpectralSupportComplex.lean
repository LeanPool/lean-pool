/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeSpectralSupportComplex.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
/-!
# Alternative spectral support complex

Part of the poincaré deficits and equality development of the
Ginibre Poincaré formalization.

Main results: `spectralSupportComplex_pencil_isUnit`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open Set
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every off-real parameter of the actual self-adjoint resolvent pencil is
invertible. The conclusion needs no spectral-gap certificate. -/
theorem spectralSupportComplex_pencil_isUnit (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (z : ℂ) (hz : z.im ≠ 0) : IsUnit (1+(z-1) • R) := by
  have hz1 : z-1 ≠ 0 := by
    intro he
    have h := congrArg Complex.im he
    exact hz (by simpa using h)
  let w : ℂ := -(z-1)⁻¹
  have hw : w ∉ spectrum ℂ R := by
    intro hs
    have hr := hR.mem_spectrum_eq_re hs
    have he : 1 + (z - 1) * w = 0 := by
      dsimp [w]
      field_simp
      ring
    rw [hr] at he
    have hi := congrArg Complex.im he
    simp [Complex.mul_im] at hi
    have hw0 : w.re = 0 := hi.resolve_left hz
    rw [hw0] at he
    simp at he
  have hu : IsUnit (algebraMap ℂ (H →L[ℂ] H) w - R) := spectrum.notMem_iff.mp hw
  have hs : IsUnit ((z-1) • (algebraMap ℂ (H →L[ℂ] H) w - R)) := by
    simpa only [Units.smul_def, Units.val_mk0] using IsUnit.smul (Units.mk0 (z-1) hz1) hu
  have he : (z-1) • (algebraMap ℂ (H →L[ℂ] H) w - R) = -(1+(z-1) • R) := by
    rw [smul_sub, Algebra.algebraMap_eq_smul_one, smul_smul]
    have hw : (z - 1) * w = -1 := by
      dsimp [w]
      field_simp
    rw [hw]
    simp [sub_eq_add_neg, add_comm]
  rw [he] at hs
  simpa only [neg_neg] using hs.neg

end
end GinibrePoincare
