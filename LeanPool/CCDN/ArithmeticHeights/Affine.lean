/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.NumberTheory.Height.NumberField

/-!
# The affine height of a tuple

Mathlib's `Height.mulHeight` is a height on *projective* space: it is invariant under scaling, and
so is a function of the line through a tuple rather than of the tuple. That is the right object
for a point of `ℙⁿ` and the wrong one for anything not homogeneous — the value `∑ i, a i * x i` of
a linear form, or the determinant of a matrix, both of which scale with the tuple. This file adds
the **affine** height, the projective height of the tuple with a coordinate `1` appended:

`Height.mulHeightAff x := Height.mulHeight fun o : Option ι ↦ o.elim 1 x`.

It is the tuple analogue of Mathlib's `Height.mulHeight₁ x = mulHeight ![x, 1]`, and agrees with it
on a one-element tuple (`Height.mulHeightAff_fin_one`). Being a normalization and not a theorem, it
is stated here in Layer 0 rather than at its first use.

`mulHeightAff` is deliberately **not** scaling-invariant, and `Height.exists_mulHeightAff_smul_ne`
records that as a theorem: over `ℚ` the tuples `![1]` and `![2]` have affine heights `1` and `2`.
That failure is the content of the definition, not a defect of it. What survives is one-sided:
the affine height dominates the projective height and the height of every single coordinate, and
is monotone under re-indexing.

## Main definitions

* `Height.mulHeightAff x` for `x : ι → K`, and `Height.logHeightAff x` its logarithm.

## Main results

* `Height.mulHeight_le_mulHeightAff` and `Height.mulHeight₁_le_mulHeightAff`: the affine height
  dominates the projective height of the tuple and the height of each coordinate. The second is
  false for `Height.mulHeight`.
* `Height.mulHeightAff_comp_le` and `Height.mulHeightAff_comp_equiv`: monotonicity under
  re-indexing, and invariance under a bijective one.
* `Height.mulHeightAff_fin_one`: on a one-element tuple the affine height is `Height.mulHeight₁`.
* `Height.exists_mulHeightAff_smul_ne`: the affine height is not scaling-invariant.

## Implementation notes

The appended coordinate is indexed by `none : Option ι` rather than by `Sum.inl` of a `Unit` or by
`Fin.succ`: `Option ι` needs no `Fintype` bookkeeping, inherits `Finite ι` by instance resolution,
and makes re-indexing along `f : ι → ι'` literally `Option.map f`.

No Arakelov analogue is defined here. Layer 0.1 already has the one-variable
`NumberField.arakelovMulHeight₁`, and no bound in the roadmap needs an affine Arakelov height of a
tuple; the Arakelov bounds that would want one carry the constant `1` and need no affine height at
all.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.5, where the affine and projective heights of a point are distinguished throughout.

This is Layer 0.5 of the `ArithmeticHeights` roadmap.
-/

public section

open Function Real

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι ι' : Type*}

/-- The **affine height** of a tuple: the projective height of the tuple with a coordinate `1`
appended.

Unlike `Height.mulHeight` this is not invariant under scaling
(`Height.exists_mulHeightAff_smul_ne`), and that is exactly what a bound on a non-homogeneous
quantity needs: the value `∑ i, a i * x i` of a linear form is not a function on projective
space, so no scaling-invariant quantity can bound its height. The affine height dominates the
projective height (`Height.mulHeight_le_mulHeightAff`) and the height of every single coordinate
(`Height.mulHeight₁_le_mulHeightAff`), neither of which `mulHeight` does. -/
@[expose] noncomputable def mulHeightAff (x : ι → K) : ℝ := mulHeight fun o : Option ι ↦ o.elim 1 x

/-- The affine logarithmic height of a tuple. As everywhere in this development, the logarithmic
height is *defined* as the logarithm of the multiplicative one. -/
@[expose] noncomputable def logHeightAff (x : ι → K) : ℝ := log (mulHeightAff x)

theorem logHeightAff_eq_log_mulHeightAff (x : ι → K) :
    logHeightAff x = log (mulHeightAff x) :=
  rfl

omit [AdmissibleAbsValues K] in
/-- The tuple whose height is `Height.mulHeightAff x` is never zero: its coordinate at `none`
is `1`. This is what makes the affine height positive with no hypothesis on `x`, and it is the
nondegeneracy that consumers of the Segre relation need. -/
theorem optionElim_one_ne_zero (x : ι → K) : (fun o : Option ι ↦ o.elim 1 x) ≠ 0 :=
  fun h ↦ one_ne_zero (congrFun h none)

section Affine

variable [Finite ι]

theorem one_le_mulHeightAff (x : ι → K) : 1 ≤ mulHeightAff x := one_le_mulHeight _

theorem mulHeightAff_pos (x : ι → K) : 0 < mulHeightAff x := mulHeight_pos _

theorem mulHeightAff_ne_zero (x : ι → K) : mulHeightAff x ≠ 0 := mulHeight_ne_zero _

theorem logHeightAff_nonneg (x : ι → K) : 0 ≤ logHeightAff x := logHeight_nonneg _

/-- The projective height of a tuple is at most its affine height. -/
theorem mulHeight_le_mulHeightAff (x : ι → K) : mulHeight x ≤ mulHeightAff x :=
  mulHeight_comp_le some fun o : Option ι ↦ o.elim 1 x

/-- The logarithmic form of `Height.mulHeight_le_mulHeightAff`. -/
theorem logHeight_le_logHeightAff (x : ι → K) : logHeight x ≤ logHeightAff x :=
  log_le_log (mulHeight_pos _) (mulHeight_le_mulHeightAff x)

/-- The affine height of a tuple dominates the affine height of each of its coordinates. This is
false for `Height.mulHeight`, which is invariant under scaling. -/
theorem mulHeight₁_le_mulHeightAff (x : ι → K) (i : ι) : mulHeight₁ (x i) ≤ mulHeightAff x := by
  have h : (![x i, 1] : Fin 2 → K) = (fun o : Option ι ↦ o.elim 1 x) ∘ ![some i, none] := by
    ext j
    fin_cases j <;> rfl
  rw [mulHeight₁_eq_mulHeight, h]
  exact mulHeight_comp_le _ _

/-- The logarithmic form of `Height.mulHeight₁_le_mulHeightAff`. -/
theorem logHeight₁_le_logHeightAff (x : ι → K) (i : ι) : logHeight₁ (x i) ≤ logHeightAff x :=
  log_le_log (mulHeight₁_pos _) (mulHeight₁_le_mulHeightAff x i)

/-- The affine height is monotone under re-indexing: the appended coordinate `1` is common to
both tuples, so re-indexing along `f` is re-indexing along `Option.map f`. -/
theorem mulHeightAff_comp_le [Finite ι'] (f : ι → ι') (x : ι' → K) :
    mulHeightAff (x ∘ f) ≤ mulHeightAff x := by
  have h : (fun o : Option ι ↦ o.elim 1 (x ∘ f))
      = (fun o : Option ι' ↦ o.elim 1 x) ∘ Option.map f := by
    funext o
    cases o <;> rfl
  rw [mulHeightAff, mulHeightAff, h]
  exact mulHeight_comp_le _ _

/-- The logarithmic form of `Height.mulHeightAff_comp_le`. -/
theorem logHeightAff_comp_le [Finite ι'] (f : ι → ι') (x : ι' → K) :
    logHeightAff (x ∘ f) ≤ logHeightAff x :=
  log_le_log (mulHeightAff_pos _) (mulHeightAff_comp_le f x)

omit [Finite ι] in
/-- The affine height does not change under a bijective re-indexing. -/
theorem mulHeightAff_comp_equiv (e : ι ≃ ι') (x : ι' → K) :
    mulHeightAff (x ∘ e) = mulHeightAff x := by
  have h : (fun o : Option ι ↦ o.elim 1 (x ∘ e))
      = (fun o : Option ι' ↦ o.elim 1 x) ∘ Equiv.optionCongr e := by
    funext o
    cases o <;> rfl
  rw [mulHeightAff, mulHeightAff, h]
  exact mulHeight_comp_equiv _ _

omit [Finite ι] in
/-- The logarithmic form of `Height.mulHeightAff_comp_equiv`. -/
theorem logHeightAff_comp_equiv (e : ι ≃ ι') (x : ι' → K) :
    logHeightAff (x ∘ e) = logHeightAff x := by
  rw [logHeightAff_eq_log_mulHeightAff, logHeightAff_eq_log_mulHeightAff, mulHeightAff_comp_equiv]

/-- The affine height of the zero tuple is `1` — not by a junk-value convention but because the
tuple whose height is taken is `(1, 0, …, 0)`. -/
@[simp]
theorem mulHeightAff_zero : mulHeightAff (0 : ι → K) = 1 := by
  have hsup (v : AbsoluteValue K ℝ) :
      (⨆ o : Option ι, v (Option.elim o 1 (0 : ι → K))) = 1 :=
    le_antisymm (ciSup_le fun o ↦ by cases o <;> simp)
      (Finite.le_ciSup_of_le none (by simp))
  rw [mulHeightAff, mulHeight_eq (optionElim_one_ne_zero (0 : ι → K))]
  simp [hsup]

@[simp]
theorem logHeightAff_zero : logHeightAff (0 : ι → K) = 0 := by
  rw [logHeightAff_eq_log_mulHeightAff, mulHeightAff_zero, log_one]

end Affine

/-- **The affine height extends Mathlib's `Height.mulHeight₁`**: on a one-element tuple the two
agree. This is the check that the appended coordinate is the right one; a definition that
appended a different constant, or that normalized by the degree, would fail it. -/
theorem mulHeightAff_fin_one (x : K) : mulHeightAff ![x] = mulHeight₁ x := by
  have h : (fun o : Option (Fin 1) ↦ o.elim 1 ![x]) ∘ finSuccEquiv 1 = ![(1 : K), x] := by
    ext j
    fin_cases j <;> rfl
  rw [mulHeightAff, ← mulHeight_comp_equiv (finSuccEquiv 1), h, mulHeight_swap,
    ← mulHeight₁_eq_mulHeight]

/-- The logarithmic form of `Height.mulHeightAff_fin_one`. -/
theorem logHeightAff_fin_one (x : K) : logHeightAff ![x] = logHeight₁ x := by
  rw [logHeightAff_eq_log_mulHeightAff, logHeight₁_eq_log_mulHeight₁, mulHeightAff_fin_one]

/-- The affine height of `![2]` over `ℚ` is `2`. -/
private lemma mulHeightAff_two : mulHeightAff (![2] : Fin 1 → ℚ) = 2 := by
  rw [show (![2] : Fin 1 → ℚ) = ![((2 : ℕ) : ℚ)] by norm_num, mulHeightAff_fin_one,
    Rat.mulHeight₁_natCast]
  norm_num

/-- **The affine height is not invariant under scaling.** Over `ℚ`, doubling the tuple `![1]`
doubles its affine height. This is the whole point of the definition: a bound on a quantity that
scales with its argument — the value of a linear form, the determinant of a matrix — cannot have
a scaling-invariant right-hand side, so `Height.mulHeight` cannot appear there and
`Height.mulHeightAff` must. -/
theorem exists_mulHeightAff_smul_ne :
    ∃ (c : ℚ) (x : Fin 1 → ℚ), c ≠ 0 ∧ mulHeightAff (c • x) ≠ mulHeightAff x := by
  refine ⟨2, ![1], two_ne_zero, ?_⟩
  have h : (2 : ℚ) • (![1] : Fin 1 → ℚ) = ![2] := by
    ext j
    fin_cases j
    norm_num
  rw [h, mulHeightAff_two, mulHeightAff_fin_one, mulHeight₁_one]
  norm_num

/-!
### Examples

The acceptance criterion the roadmap states for this milestone: the affine and projective heights
of one and the same tuple differ, so the appended coordinate is doing something.
-/

/-- Over `ℚ` the tuple `![2]` has affine height `2` and projective height `1`. A definition of
the affine height that made the two agree has appended the wrong coordinate, and a bound on a
non-homogeneous quantity stated with the projective height is refuted here. -/
example : mulHeightAff (![2] : Fin 1 → ℚ) = 2 ∧ mulHeight (![2] : Fin 1 → ℚ) = 1 :=
  ⟨mulHeightAff_two, mulHeight_eq_one_of_subsingleton _⟩

end Height

end
