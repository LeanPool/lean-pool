/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.ProjectivePlaneResidueDeterminant
import LeanPool.CCDN.Determinant.ProjectiveHypersurfaceMultiplicity

/-! Singular projective residue classes are counted in their selected affine
charts. The correction is polynomial in the degree and does not change the
leading finite-field point-count term. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The singular correction does not multiply the leading point-count term. -/
theorem projectivePlaneTotalMultiplicity_le_card_add_correction {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f)) (hchar : d < p) :
    projectivePlaneTotalMultiplicity f hf hir.ne_zero ≤
      Fintype.card (ProjectivePlaneResidue f p) + 3 * d ^ 2 * (d - 1) := by
  simpa only [Nat.zero_add, pow_zero, Nat.mul_one] using
    projectiveHypersurfaceTotalMultiplicity_le_card_add_correction (n := 0) f hf hd hir hchar

end
end CCDN
