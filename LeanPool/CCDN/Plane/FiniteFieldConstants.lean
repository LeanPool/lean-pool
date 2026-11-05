/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The prime cutoff `27 d⁴` and the absolute constants of the finite-field point counts.

Every count below holds for primes `p > stepanovThreshold d = 27 d⁴` and has the shape
`main term + C d² √p · (lower-order power of p)`. The constants are derived from the plane
constant `planeResidueConstant = 161` by explicit additive corrections, recorded in the
docstrings and in the `_eq_add` lemmas. They are defined as numerals, so statements quoting
the numerals are definitionally equal to statements using the names. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The prime cutoff `27 d⁴` of the Stepanov method. For `p > 27 d⁴` the integer Stepanov
parameters `A = ⌊√p / d⌋`, `D = ⌊(p - 1) / d⌋`, `N = d A - 4 d²` exist with `N > 0`
(`exists_stepanov_integer_parameters`), the Hilbert-dimension inequality holds
(`stepanov_numeric_dimension`), and `√p < 32 N` (`stepanov_real_bound`), since
`31² · 27 > 160²`. Bad primes are only counted above this cutoff; below it the trivial
bounds are used. The definition is polymorphic so that it reads the same over `ℕ` and `ℝ`. -/
def stepanovThreshold {R : Type*} [Semiring R] (d : R) : R := 27 * d ^ 4

/-- The cast of the natural-number cutoff `stepanovThreshold d` is the cutoff of the cast of `d`. -/
@[simp, norm_cast]
lemma Nat.cast_stepanovThreshold {R : Type*} [Semiring R] (d : ℕ) :
    ((stepanovThreshold d : ℕ) : R) = stepanovThreshold (d : R) := by
  simp [stepanovThreshold]

/-- The cutoff `stepanovThreshold` is monotone on nonnegative arguments. -/
@[gcongr]
lemma stepanovThreshold_le_stepanovThreshold {R : Type*} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] {a b : R} (ha : 0 ≤ a) (hab : a ≤ b) :
    stepanovThreshold a ≤ stepanovThreshold b := by
  unfold stepanovThreshold
  have : (0 : R) ≤ 27 := Nat.ofNat_nonneg 27
  gcongr

/-- The constant `161` of the affine plane-curve count `#C(𝔽_p) ≤ p + 161 d² √p`
(`plane_finite_field_card_bound`). In `stepanov_real_bound` the Stepanov count
`t N ≤ d D + p (N + 4 d²) + d² N` is bounded using `d D < p`, `(4 d² + 1) p ≤ 5 d² p`,
`p ≤ 32 N √p` and `1 ≤ √p`, giving `t ≤ p + (5 · 32 + 1) d² √p`. -/
def planeResidueConstant : ℝ := 161

/-- The constant `162 = 161 + 1` of the projective plane-curve count
(`projective_plane_finite_field_card_bound`): the affine chart contributes
`p + 161 d² √p` and the line at infinity at most `d ≤ d² √p` further points
(`projectivePlaneResidueConstant_eq_add`). -/
def projectivePlaneResidueConstant : ℝ := 162

/-- The constant `C = 164 = 162 + 2` for which the projective plane total multiplicity is
at most `p + (C + 1) d² √p` (`projectivePlaneTotalMultiplicity_le`). The singular
correction `3 d² (d - 1) ≤ 3 d² √p` adds `3` to `162`; the shift by one matches the affine
convention of `degreeFourDeterminantError`, whose singular correction `d² (d - 1)` costs `1`
(`projectivePlaneDeterminantConstant_eq_add`). -/
def projectivePlaneDeterminantConstant : ℝ := 164

/-- The constant `164 = 161 + 3` of the affine hypersurface count
`#X(𝔽_p) ≤ p^(m-1) + 164 d² p^(m-2) √p` (`affine_hypersurface_finite_field_bound`). Averaging
the plane count over plane sections gives `161`; bad and zero plane sections cost at most
`3 d² p √p` (`hypersurface_bad_section_error`, `hypersurfaceResidueConstant_eq_add`). -/
def hypersurfaceResidueConstant : ℝ := 164

/-- The constant `330 = 2 (164 + 1)` of the projective hypersurface count
(`projective_hypersurface_finite_field_bound`). Applied to the affine cone count with error
`H = 164 d² √p`, `homogeneous_projective_count_of_cone_bound` gives the projective error
`2 (H + 1) p^(m-2)`, and `1 ≤ d² √p` (`projectiveHypersurfaceResidueConstant_eq_add`). -/
def projectiveHypersurfaceResidueConstant : ℝ := 330

/-- The value of `planeResidueConstant` is `161`. -/
lemma planeResidueConstant_eq : planeResidueConstant = 161 := rfl

/-- The value of `projectivePlaneResidueConstant` is `162`. -/
lemma projectivePlaneResidueConstant_eq : projectivePlaneResidueConstant = 162 := rfl

/-- The value of `projectivePlaneDeterminantConstant` is `164`. -/
lemma projectivePlaneDeterminantConstant_eq : projectivePlaneDeterminantConstant = 164 := rfl

/-- The value of `hypersurfaceResidueConstant` is `164`. -/
lemma hypersurfaceResidueConstant_eq : hypersurfaceResidueConstant = 164 := rfl

/-- The value of `projectiveHypersurfaceResidueConstant` is `330`. -/
lemma projectiveHypersurfaceResidueConstant_eq : projectiveHypersurfaceResidueConstant = 330 :=
  rfl

/-- The projective plane constant exceeds the affine plane constant by `1`, accounting for the
points on the line at infinity. -/
lemma projectivePlaneResidueConstant_eq_add :
    projectivePlaneResidueConstant = planeResidueConstant + 1 := by
  norm_num [projectivePlaneResidueConstant, planeResidueConstant]

/-- The projective plane determinant constant exceeds the projective plane residue constant
by `2`. -/
lemma projectivePlaneDeterminantConstant_eq_add :
    projectivePlaneDeterminantConstant = projectivePlaneResidueConstant + 2 := by
  norm_num [projectivePlaneDeterminantConstant, projectivePlaneResidueConstant]

/-- The affine hypersurface constant exceeds the plane constant by `3`, accounting for bad and
zero plane sections. -/
lemma hypersurfaceResidueConstant_eq_add :
    hypersurfaceResidueConstant = planeResidueConstant + 3 := by
  norm_num [hypersurfaceResidueConstant, planeResidueConstant]

/-- The projective hypersurface constant is twice the affine hypersurface constant plus one. -/
lemma projectiveHypersurfaceResidueConstant_eq_add :
    projectiveHypersurfaceResidueConstant = 2 * (hypersurfaceResidueConstant + 1) := by
  norm_num [projectiveHypersurfaceResidueConstant, hypersurfaceResidueConstant]

/-- The plane constant `planeResidueConstant` is positive. -/
lemma planeResidueConstant_pos : 0 < planeResidueConstant := by
  norm_num [planeResidueConstant]

/-- The constant `projectivePlaneDeterminantConstant` is positive. -/
lemma projectivePlaneDeterminantConstant_pos : 0 < projectivePlaneDeterminantConstant := by
  norm_num [projectivePlaneDeterminantConstant]

/-- The constant `projectiveHypersurfaceResidueConstant` is positive. -/
lemma projectiveHypersurfaceResidueConstant_pos : 0 < projectiveHypersurfaceResidueConstant := by
  norm_num [projectiveHypersurfaceResidueConstant]

end
end CCDN
