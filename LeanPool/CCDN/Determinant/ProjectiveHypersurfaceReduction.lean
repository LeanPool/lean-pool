/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.ProjectiveHypersurfaceLocal
public import LeanPool.CCDN.Determinant.ProjectiveReduction
import LeanPool.CCDN.Height.ProjectiveZeroLocus

/-! Projective residue points determine unit charts and integral lifts
in arbitrary dimension. Their reduced affine equations vanish at those lifts. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A coordinate index at which the chosen representative of a point of `ℙⁿ⁺²(𝔽_p)` is nonzero. -/
abbrev hypersurfaceResiduePivot {n p : ℕ} [Fact p.Prime] (r : ProjectiveResidueSpace (n + 2) p) :
    Fin (n + 3) := projectiveResiduePivot r

/-- The representative of `r` is nonzero at the coordinate `hypersurfaceResiduePivot r`. -/
lemma hypersurfaceResiduePivot_ne_zero {n p : ℕ} [Fact p.Prime]
    (r : ProjectiveResidueSpace (n + 2) p) : r.rep (hypersurfaceResiduePivot r) ≠ 0 :=
  projectiveResiduePivot_ne_zero r

/-- Integer lifts of the affine coordinates of a point `r` of `ℙⁿ⁺²(𝔽_p)` in the chart where its
pivot coordinate `hypersurfaceResiduePivot r` is moved to the front and set to `1`. -/
abbrev hypersurfaceResidueChartLift {n p : ℕ} [Fact p.Prime]
    (r : ProjectiveResidueSpace (n + 2) p) :
    Fin (n + 2) → ℤ := projectiveResidueChartLift r

/-- Modulo `p`, `hypersurfaceResidueChartLift r` gives the coordinates of `r` divided by its pivot
coordinate, with the pivot coordinate swapped to the front. -/
lemma cast_hypersurfaceResidueChartLift {n p : ℕ} [Fact p.Prime]
    (r : ProjectiveResidueSpace (n + 2) p) (j : Fin (n + 2)) :
    (hypersurfaceResidueChartLift r j : ZMod p) =
      r.rep (Equiv.swap 0 (hypersurfaceResiduePivot r) j.succ) /
        r.rep (hypersurfaceResiduePivot r) :=
  cast_projectiveResidueChartLift r j

/-- Reduction determines both a unit coordinate and all affine congruences;
these are derived from equality of projective residue points. -/
theorem primitiveProjectiveReduction_hypersurface_chart {n p : ℕ} [Fact p.Prime]
    (z : IntPoint (n + 3)) (hz : Finset.univ.gcd z = 1)
    (r : ProjectiveResidueSpace (n + 2) p) (he : primitiveProjectiveReduction z hz = r) :
    IsCoprime (p : ℤ) (z (hypersurfaceResiduePivot r)) ∧
      ∀ j : Fin (n + 2), (p : ℤ) ∣ z (Equiv.swap 0 (hypersurfaceResiduePivot r) j.succ) -
        hypersurfaceResidueChartLift r j * z (hypersurfaceResiduePivot r) :=
  primitiveProjectiveReduction_chart z hz r he

/-- The integer chart representative of a projective residue zero satisfies
the reduced affine equation. -/
theorem hypersurfaceResidueChartLift_zero {n p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (r : ProjectiveResidueSpace (n + 2) p)
    (hr : eval r.rep (map (Int.castRingHom (ZMod p)) f) = 0) :
    eval₂ (Int.castRingHom (ZMod p))
      (fun j => (hypersurfaceResidueChartLift r j : ZMod p))
      (projectiveHypersurfaceChart (hypersurfaceResiduePivot r) f) = 0 :=
  projectiveResidueChartLift_zero f hf r hr

end
end CCDN
