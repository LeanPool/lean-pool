/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ArithmeticHeights.Absolute
public import LeanPool.CCDN.ArithmeticHeights.Arakelov
public import LeanPool.CCDN.ArithmeticHeights.Plucker

/-!
# The height of a linear subspace

Schmidt's height of a subspace `V : Submodule K (ι → K)`: the height of its Plücker point
`Submodule.pluckerPoint`, a point of `Projectivization K (Set.powersetCard ι k → K)`, in each of
the three normalizations the roadmap carries — Mathlib's sup-norm height, the Arakelov height of
Layer 0.1, and the absolute height of Layer 0.4 — with the logarithmic form of each alongside.

The definition is Bombieri–Gubler 2.8.4 and Schmidt 1967, §1. What makes it the right definition
is `Submodule.mulHeight_span_singleton`: the height of a line is the projective height of the
point that spans it.

## Main definitions

* `Submodule.mulHeight`, `Submodule.logHeight`: the height of a subspace of `ι → K`, over any
  field with `Height.AdmissibleAbsValues`.
* `Submodule.arakelovMulHeight`, `Submodule.arakelovLogHeight`: the ℓ²-at-infinity variant, over a
  number field.
* `Submodule.absMulHeight`, `Submodule.absLogHeight`: the absolute variant, over a field of
  algebraic numbers.

## Main results

* `Submodule.mulHeight_span_singleton`: `Submodule.mulHeight (span K {x}) = Height.mulHeight x`
  for `x ≠ 0`, and the same for the other three heights. This is the compatibility that fixes the
  definition; it is `exteriorPower.plucker_one_comp` of Layer 3.1 read through
  `Height.mulHeight_comp_equiv`.
* `Submodule.mulHeight_span_range`: the height of the span of a linearly independent family is
  the height of its tuple of Plücker coordinates, which by `exteriorPower.plucker_apply` is its
  tuple of maximal minors. This is the form the matrix dictionary of 3.3 consumes.
* `Submodule.mulHeight_bot` and `Submodule.mulHeight_top`: the two degenerate ranks, where the
  exterior power is a line, have height `1`.
* `Submodule.one_le_mulHeight`, and positivity and nonnegativity beside it.
* `Submodule.mulHeight_eq_mulHeight_pluckerPoint`: the definition, re-typed along any proof that
  the rank of `V` is `k`. Every proof enters through this rather than through the definition.
* `Submodule.absMulHeight_eq`: over a number field the absolute height of a subspace is the
  relative one normalized by the degree, as it is for tuples and for projective points.
* `Submodule.mulHeight_le_arakelovMulHeight`: the height of a subspace is at most its Arakelov
  height, the comparison of Layer 0.2 read at the Plücker point.

`Set.powersetCard.subsingleton_iff` and `Projectivization.mulHeight_eq_one_of_subsingleton` are
stated here because Mathlib has neither, although both are about Mathlib's own objects — the first
sits beside `Set.powersetCard.nontrivial_iff`, the second beside
`Projectivization.mulHeight`. They belong upstream rather than in this library.

## Implementation notes

The rank is not a parameter of the definition. `Submodule.mulHeight V` is
`Projectivization.mulHeight (V.pluckerPoint rfl)`, taking `k := Module.finrank K V`, so it is a
total function of `V` alone: `Submodule.mulHeight (V ⊓ W)` is well formed without producing a rank
for `V ⊓ W` first, which is what the submodularity of 3.6 needs.
`Submodule.mulHeight_eq_mulHeight_pluckerPoint` re-types it along an arbitrary
`hV : Module.finrank K V = k` — by `subst`, since `k` is a variable — and that lemma, not the
definition, is what every proof below uses.

Both degenerate cases are one argument, and neither is a computation of Plücker coordinates: for
`Module.finrank K V = 0` and for `Module.finrank K V = Fintype.card ι` the index type
`Set.powersetCard ι (Module.finrank K V)` is a subsingleton — only `∅`, only `Finset.univ` — so
every tuple over it has height `1` by the product formula. In particular `mulHeight ⊤ = 1` does
not go through `exteriorPower.plucker_fin_eq_det`, which is stated for `ι = Fin n`.

The four height families are separate sections rather than one definition parametrized by a
height, because their hypotheses differ: `Height.AdmissibleAbsValues K` for the first,
`NumberField K` for the Arakelov height, and `CharZero K` with `Algebra.IsAlgebraic ℚ K` for the
absolute one. As the roadmap's convention records, the duplication is in the statements only.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
2.8.4 for the Plücker construction, Definition 1.5.4 for the absolute sup-norm height, and
Definition 2.8.5 (p. 67) for the absolute Arakelov height of a subspace.
The relative variants here use unnormalized place-weighted products. `absMulHeight` and
`absLogHeight` give the absolute sup-norm variants; the Arakelov variants here remain relative.
W. M. Schmidt, "On heights of algebraic subspaces and diophantine approximations", *Annals of
Mathematics* **85** (1967), 430–472, §1, where the height of a subspace is defined through its
Grassmann coordinates.

This is Layer 3.2 of the `ArithmeticHeights` roadmap.
-/

public section

open Module

/-!
### Two lemmas that belong upstream

`Set.powersetCard.nontrivial_iff` is in Mathlib; its negation is not, and it is what makes the two
degenerate ranks of a subspace height degenerate. Mathlib's `Projectivization.mulHeight` has no
subsingleton lemma either, although the tuple-level `Height.mulHeight_eq_one_of_subsingleton` is
there.
-/

namespace Set.powersetCard

/-- A type of `n`-element subsets is a subsingleton exactly when there is at most one such subset:
`n = 0`, when only `∅` qualifies, or `n` at least the cardinality, when only `Finset.univ` does.
This is the negation of `Set.powersetCard.nontrivial_iff`. -/
theorem subsingleton_iff {α : Type*} [Finite α] {n : ℕ} :
    Subsingleton (Set.powersetCard α n) ↔ n = 0 ∨ Nat.card α ≤ n := by
  rw [← not_nontrivial_iff_subsingleton, nontrivial_iff]
  omega

end Set.powersetCard

namespace Projectivization

variable {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {ι : Type*} [Finite ι]

/-- On a subsingleton index type every point of projective space has height `1`; the projective
form of `Height.mulHeight_eq_one_of_subsingleton`. -/
@[simp]
theorem mulHeight_eq_one_of_subsingleton [Subsingleton ι] (x : Projectivization K (ι → K)) :
    mulHeight x = 1 := by
  rw [← x.mk_rep, mulHeight_mk]
  exact Height.mulHeight_eq_one_of_subsingleton _

@[simp]
theorem logHeight_eq_zero_of_subsingleton [Subsingleton ι] (x : Projectivization K (ι → K)) :
    logHeight x = 0 := by
  simp [logHeight_eq_log_mulHeight]

end Projectivization

namespace Submodule

open exteriorPower

section Degenerate

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] {V : Submodule K (ι → K)}

/-- The index type of the Plücker coordinates collapses to a point exactly in the two degenerate
ranks. Every `= 1` statement below is this lemma followed by the product formula. -/
private lemma subsingleton_powersetCard_finrank
    (h : finrank K V = 0 ∨ Fintype.card ι ≤ finrank K V) :
    Subsingleton (Set.powersetCard ι (finrank K V)) :=
  Set.powersetCard.subsingleton_iff.2 (by rwa [Nat.card_eq_fintype_card])

end Degenerate

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}
  {V : Submodule K (ι → K)}

/-!
### The height of a subspace
-/

section Relative

variable [Height.AdmissibleAbsValues K]

/-- **The multiplicative height of a linear subspace of `ι → K`**: the projective height of its
Plücker point, following Schmidt. The rank is read off `V` rather than supplied, so this is a
total function of `V`. -/
noncomputable def mulHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.mulHeight (V.pluckerPoint rfl)

/-- **The logarithmic height of a linear subspace of `ι → K`.** -/
noncomputable def logHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.logHeight (V.pluckerPoint rfl)

/-- The definition, re-typed along an arbitrary proof that `V` has rank `k`. Every proof enters
through this. -/
theorem mulHeight_eq_mulHeight_pluckerPoint (hV : finrank K V = k) :
    V.mulHeight = Projectivization.mulHeight (V.pluckerPoint hV) := by
  subst hV
  rfl

/-- The logarithmic form of `Submodule.mulHeight_eq_mulHeight_pluckerPoint`. -/
theorem logHeight_eq_logHeight_pluckerPoint (hV : finrank K V = k) :
    V.logHeight = Projectivization.logHeight (V.pluckerPoint hV) := by
  subst hV
  rfl

theorem logHeight_eq_log_mulHeight (V : Submodule K (ι → K)) :
    V.logHeight = Real.log V.mulHeight :=
  Projectivization.logHeight_eq_log_mulHeight _

/-- The height of a subspace is at least `1`. -/
theorem one_le_mulHeight (V : Submodule K (ι → K)) : 1 ≤ V.mulHeight :=
  Projectivization.one_le_mulHeight _

theorem mulHeight_pos (V : Submodule K (ι → K)) : 0 < V.mulHeight :=
  Projectivization.mulHeight_pos _

theorem mulHeight_ne_zero (V : Submodule K (ι → K)) : V.mulHeight ≠ 0 :=
  Projectivization.mulHeight_ne_zero _

theorem logHeight_nonneg (V : Submodule K (ι → K)) : 0 ≤ V.logHeight :=
  Projectivization.logHeight_nonneg _

/-- The zero subspace has height `1`: its exterior power is the line spanned by the empty wedge,
whose single coordinate is indexed by `∅`. -/
@[simp]
theorem mulHeight_bot : (⊥ : Submodule K (ι → K)).mulHeight = 1 :=
  have := subsingleton_powersetCard_finrank (.inl (finrank_bot K (ι → K)))
  Projectivization.mulHeight_eq_one_of_subsingleton _

@[simp]
theorem logHeight_bot : (⊥ : Submodule K (ι → K)).logHeight = 0 := by
  rw [logHeight_eq_log_mulHeight, mulHeight_bot, Real.log_one]

/-- The whole space has height `1`: its exterior power is the line spanned by the wedge of the
standard basis, whose single coordinate is indexed by `Finset.univ`. -/
@[simp]
theorem mulHeight_top : (⊤ : Submodule K (ι → K)).mulHeight = 1 :=
  have := subsingleton_powersetCard_finrank (V := (⊤ : Submodule K (ι → K)))
    (.inr (by rw [finrank_top, finrank_fintype_fun_eq_card]))
  Projectivization.mulHeight_eq_one_of_subsingleton _

@[simp]
theorem logHeight_top : (⊤ : Submodule K (ι → K)).logHeight = 0 := by
  rw [logHeight_eq_log_mulHeight, mulHeight_top, Real.log_one]

/-- **The height of a line is the projective height of a point spanning it.** This is the
compatibility that makes the Plücker point the right carrier of the definition: in rank one the
coordinates are the coordinates of the vector itself, re-indexed along
`Set.powersetCard.ofSingleton`. -/
theorem mulHeight_span_singleton {x : ι → K} (hx : x ≠ 0) :
    (span K {x}).mulHeight = Height.mulHeight x := by
  have hV : finrank K (span K {x} : Submodule K (ι → K)) = 1 := finrank_span_singleton hx
  rw [mulHeight_eq_mulHeight_pluckerPoint hV, pluckerPoint_span_singleton hx hV,
    Projectivization.mulHeight_mk,
    ← Height.mulHeight_comp_equiv Set.powersetCard.ofSingleton (plucker 1 ![x]), plucker_one_comp]

/-- The logarithmic form of `Submodule.mulHeight_span_singleton`. -/
theorem logHeight_span_singleton {x : ι → K} (hx : x ≠ 0) :
    (span K {x}).logHeight = Height.logHeight x := by
  rw [logHeight_eq_log_mulHeight, mulHeight_span_singleton hx,
    Height.logHeight_eq_log_mulHeight]

/-- **The height of the span of a linearly independent family is the height of its tuple of
Plücker coordinates** — by `exteriorPower.plucker_apply`, of its tuple of maximal minors. This is
the form the matrix dictionary of 3.3 consumes. -/
theorem mulHeight_span_range {v : Fin k → (ι → K)} (hv : LinearIndependent K v) :
    (span K (Set.range v)).mulHeight = Height.mulHeight (plucker k v) := by
  have hV : finrank K (span K (Set.range v)) = k :=
    (finrank_span_eq_card hv).trans (Fintype.card_fin k)
  rw [mulHeight_eq_mulHeight_pluckerPoint hV, pluckerPoint_span_range hv hV,
    Projectivization.mulHeight_mk]

/-- The logarithmic form of `Submodule.mulHeight_span_range`. -/
theorem logHeight_span_range {v : Fin k → (ι → K)} (hv : LinearIndependent K v) :
    (span K (Set.range v)).logHeight = Height.logHeight (plucker k v) := by
  rw [logHeight_eq_log_mulHeight, mulHeight_span_range hv, Height.logHeight_eq_log_mulHeight]

end Relative

/-!
### The Arakelov height of a subspace

The same definition with the ℓ² norm at the archimedean places, which is the normalization the
Siegel-lemma literature states its constants in.
-/

section Arakelov

variable [NumberField K]

/-- **The relative multiplicative Arakelov height of a linear subspace of `ι → K`**,
`exp([K : ℚ] · h_Ar(V))` in the absolute logarithmic convention of
Bombieri–Gubler Definition 2.8.5. -/
noncomputable def arakelovMulHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.arakelovMulHeight (V.pluckerPoint rfl)

/-- **The relative logarithmic Arakelov height of a linear subspace of `ι → K`**,
`[K : ℚ] · h_Ar(V)` in the absolute convention of Bombieri–Gubler Definition 2.8.5. -/
noncomputable def arakelovLogHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.arakelovLogHeight (V.pluckerPoint rfl)

theorem arakelovMulHeight_eq_arakelovMulHeight_pluckerPoint (hV : finrank K V = k) :
    V.arakelovMulHeight = Projectivization.arakelovMulHeight (V.pluckerPoint hV) := by
  subst hV
  rfl

theorem arakelovLogHeight_eq_arakelovLogHeight_pluckerPoint (hV : finrank K V = k) :
    V.arakelovLogHeight = Projectivization.arakelovLogHeight (V.pluckerPoint hV) := by
  subst hV
  rfl

theorem arakelovLogHeight_eq_log_arakelovMulHeight (V : Submodule K (ι → K)) :
    V.arakelovLogHeight = Real.log V.arakelovMulHeight :=
  Projectivization.arakelovLogHeight_eq_log_arakelovMulHeight _

theorem one_le_arakelovMulHeight (V : Submodule K (ι → K)) : 1 ≤ V.arakelovMulHeight :=
  Projectivization.one_le_arakelovMulHeight _

theorem arakelovMulHeight_pos (V : Submodule K (ι → K)) : 0 < V.arakelovMulHeight :=
  Projectivization.arakelovMulHeight_pos _

theorem arakelovMulHeight_ne_zero (V : Submodule K (ι → K)) : V.arakelovMulHeight ≠ 0 :=
  Projectivization.arakelovMulHeight_ne_zero _

theorem arakelovLogHeight_nonneg (V : Submodule K (ι → K)) : 0 ≤ V.arakelovLogHeight :=
  Projectivization.arakelovLogHeight_nonneg _

@[simp]
theorem arakelovMulHeight_bot : (⊥ : Submodule K (ι → K)).arakelovMulHeight = 1 :=
  have := subsingleton_powersetCard_finrank (.inl (finrank_bot K (ι → K)))
  Projectivization.arakelovMulHeight_eq_one_of_subsingleton _

@[simp]
theorem arakelovLogHeight_bot : (⊥ : Submodule K (ι → K)).arakelovLogHeight = 0 := by
  rw [arakelovLogHeight_eq_log_arakelovMulHeight, arakelovMulHeight_bot, Real.log_one]

@[simp]
theorem arakelovMulHeight_top : (⊤ : Submodule K (ι → K)).arakelovMulHeight = 1 :=
  have := subsingleton_powersetCard_finrank (V := (⊤ : Submodule K (ι → K)))
    (.inr (by rw [finrank_top, finrank_fintype_fun_eq_card]))
  Projectivization.arakelovMulHeight_eq_one_of_subsingleton _

@[simp]
theorem arakelovLogHeight_top : (⊤ : Submodule K (ι → K)).arakelovLogHeight = 0 := by
  rw [arakelovLogHeight_eq_log_arakelovMulHeight, arakelovMulHeight_top, Real.log_one]

/-- **The Arakelov height of a line is the projective Arakelov height of a point spanning it.** -/
theorem arakelovMulHeight_span_singleton {x : ι → K} (hx : x ≠ 0) :
    (span K {x}).arakelovMulHeight = NumberField.arakelovMulHeight x := by
  have hV : finrank K (span K {x} : Submodule K (ι → K)) = 1 := finrank_span_singleton hx
  rw [arakelovMulHeight_eq_arakelovMulHeight_pluckerPoint hV, pluckerPoint_span_singleton hx hV,
    Projectivization.arakelovMulHeight_mk,
    ← NumberField.arakelovMulHeight_comp_equiv Set.powersetCard.ofSingleton (plucker 1 ![x]),
    plucker_one_comp]

/-- The logarithmic form of `Submodule.arakelovMulHeight_span_singleton`. -/
theorem arakelovLogHeight_span_singleton {x : ι → K} (hx : x ≠ 0) :
    (span K {x}).arakelovLogHeight = NumberField.arakelovLogHeight x := by
  rw [arakelovLogHeight_eq_log_arakelovMulHeight, arakelovMulHeight_span_singleton hx,
    NumberField.arakelovLogHeight_eq_log_arakelovMulHeight]

/-- **The Arakelov height of the span of a linearly independent family is the Arakelov height of
its tuple of maximal minors.** -/
theorem arakelovMulHeight_span_range {v : Fin k → (ι → K)} (hv : LinearIndependent K v) :
    (span K (Set.range v)).arakelovMulHeight = NumberField.arakelovMulHeight (plucker k v) := by
  have hV : finrank K (span K (Set.range v)) = k :=
    (finrank_span_eq_card hv).trans (Fintype.card_fin k)
  rw [arakelovMulHeight_eq_arakelovMulHeight_pluckerPoint hV, pluckerPoint_span_range hv hV,
    Projectivization.arakelovMulHeight_mk]

/-- The logarithmic form of `Submodule.arakelovMulHeight_span_range`. -/
theorem arakelovLogHeight_span_range {v : Fin k → (ι → K)} (hv : LinearIndependent K v) :
    (span K (Set.range v)).arakelovLogHeight = NumberField.arakelovLogHeight (plucker k v) := by
  rw [arakelovLogHeight_eq_log_arakelovMulHeight, arakelovMulHeight_span_range hv,
    NumberField.arakelovLogHeight_eq_log_arakelovMulHeight]

/-- **The height of a subspace is at most its Arakelov height**, with no constant: the two
normalizations differ only at the archimedean places, where `‖·‖_∞ ≤ ‖·‖_2`. This is
`Projectivization.mulHeight_le_arakelovMulHeight` at the Plücker point, and it is what carries
Northcott for subspaces (3.7) from one normalization to the other.

The reverse bound is not stated: it carries the constant
`(Fintype.card ι).choose (finrank K V) ^ (Height.totalWeight K / 2)`, the number of Plücker
coordinates rather than the dimension of the ambient space, and nothing below needs it. -/
theorem mulHeight_le_arakelovMulHeight (V : Submodule K (ι → K)) :
    V.mulHeight ≤ V.arakelovMulHeight := by
  rw [mulHeight_eq_mulHeight_pluckerPoint (k := finrank K V) rfl,
    arakelovMulHeight_eq_arakelovMulHeight_pluckerPoint (k := finrank K V) rfl]
  exact Projectivization.mulHeight_le_arakelovMulHeight _

/-- The logarithmic form of `Submodule.mulHeight_le_arakelovMulHeight`. -/
theorem logHeight_le_arakelovLogHeight (V : Submodule K (ι → K)) :
    V.logHeight ≤ V.arakelovLogHeight := by
  rw [logHeight_eq_log_mulHeight, arakelovLogHeight_eq_log_arakelovMulHeight]
  exact Real.log_le_log (mulHeight_pos V) (mulHeight_le_arakelovMulHeight V)

end Arakelov

/-!
### The absolute height of a subspace

The sup-norm variant that does not depend on the field the subspace is written over.
`absLogHeight` is the literature's `h(V)`, and `absMulHeight` is its exponential.
This is one of the six Northcott statements of 3.7.
-/

section Absolute

variable [CharZero K] [Algebra.IsAlgebraic ℚ K]

/-- **The absolute multiplicative height of a linear subspace of `ι → K`**,
`exp(h(V))` via Bombieri–Gubler 2.8.4 and Definition 1.5.4. -/
noncomputable def absMulHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.absMulHeight (V.pluckerPoint rfl)

/-- **The absolute logarithmic height of a linear subspace of `ι → K`**,
`h(V)` via Bombieri–Gubler 2.8.4 and Definition 1.5.4. -/
noncomputable def absLogHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.absLogHeight (V.pluckerPoint rfl)

theorem absMulHeight_eq_absMulHeight_pluckerPoint (hV : finrank K V = k) :
    V.absMulHeight = Projectivization.absMulHeight (V.pluckerPoint hV) := by
  subst hV
  rfl

theorem absLogHeight_eq_absLogHeight_pluckerPoint (hV : finrank K V = k) :
    V.absLogHeight = Projectivization.absLogHeight (V.pluckerPoint hV) := by
  subst hV
  rfl

theorem absLogHeight_eq_log_absMulHeight (V : Submodule K (ι → K)) :
    V.absLogHeight = Real.log V.absMulHeight :=
  Projectivization.absLogHeight_eq_log_absMulHeight _

theorem one_le_absMulHeight (V : Submodule K (ι → K)) : 1 ≤ V.absMulHeight :=
  Projectivization.one_le_absMulHeight _

theorem absMulHeight_pos (V : Submodule K (ι → K)) : 0 < V.absMulHeight :=
  Projectivization.absMulHeight_pos _

theorem absMulHeight_ne_zero (V : Submodule K (ι → K)) : V.absMulHeight ≠ 0 :=
  Projectivization.absMulHeight_ne_zero _

theorem absLogHeight_nonneg (V : Submodule K (ι → K)) : 0 ≤ V.absLogHeight :=
  Projectivization.absLogHeight_nonneg _

@[simp]
theorem absMulHeight_bot : (⊥ : Submodule K (ι → K)).absMulHeight = 1 :=
  have := subsingleton_powersetCard_finrank (.inl (finrank_bot K (ι → K)))
  Projectivization.absMulHeight_eq_one_of_subsingleton _

@[simp]
theorem absLogHeight_bot : (⊥ : Submodule K (ι → K)).absLogHeight = 0 := by
  rw [absLogHeight_eq_log_absMulHeight, absMulHeight_bot, Real.log_one]

@[simp]
theorem absMulHeight_top : (⊤ : Submodule K (ι → K)).absMulHeight = 1 :=
  have := subsingleton_powersetCard_finrank (V := (⊤ : Submodule K (ι → K)))
    (.inr (by rw [finrank_top, finrank_fintype_fun_eq_card]))
  Projectivization.absMulHeight_eq_one_of_subsingleton _

@[simp]
theorem absLogHeight_top : (⊤ : Submodule K (ι → K)).absLogHeight = 0 := by
  rw [absLogHeight_eq_log_absMulHeight, absMulHeight_top, Real.log_one]

/-- **The absolute height of a line is the absolute height of a point spanning it.** -/
theorem absMulHeight_span_singleton {x : ι → K} (hx : x ≠ 0) :
    (span K {x}).absMulHeight = NumberField.absMulHeight x := by
  have hV : finrank K (span K {x} : Submodule K (ι → K)) = 1 := finrank_span_singleton hx
  rw [absMulHeight_eq_absMulHeight_pluckerPoint hV, pluckerPoint_span_singleton hx hV,
    Projectivization.absMulHeight_mk,
    ← NumberField.absMulHeight_comp_equiv Set.powersetCard.ofSingleton (plucker 1 ![x]),
    plucker_one_comp]

/-- The logarithmic form of `Submodule.absMulHeight_span_singleton`. -/
theorem absLogHeight_span_singleton {x : ι → K} (hx : x ≠ 0) :
    (span K {x}).absLogHeight = NumberField.absLogHeight x := by
  rw [absLogHeight_eq_log_absMulHeight, absMulHeight_span_singleton hx,
    NumberField.absLogHeight_eq_log_absMulHeight]

/-- **The absolute height of the span of a linearly independent family is the absolute height of
its tuple of maximal minors.** -/
theorem absMulHeight_span_range {v : Fin k → (ι → K)} (hv : LinearIndependent K v) :
    (span K (Set.range v)).absMulHeight = NumberField.absMulHeight (plucker k v) := by
  have hV : finrank K (span K (Set.range v)) = k :=
    (finrank_span_eq_card hv).trans (Fintype.card_fin k)
  rw [absMulHeight_eq_absMulHeight_pluckerPoint hV, pluckerPoint_span_range hv hV,
    Projectivization.absMulHeight_mk]

/-- The logarithmic form of `Submodule.absMulHeight_span_range`. -/
theorem absLogHeight_span_range {v : Fin k → (ι → K)} (hv : LinearIndependent K v) :
    (span K (Set.range v)).absLogHeight = NumberField.absLogHeight (plucker k v) := by
  rw [absLogHeight_eq_log_absMulHeight, absMulHeight_span_range hv,
    NumberField.absLogHeight_eq_log_absMulHeight]

/-- **Over a number field the absolute height of a subspace is the relative one normalized by the
degree**, exactly as for tuples and for projective points. -/
theorem absMulHeight_eq [NumberField K] (V : Submodule K (ι → K)) :
    V.absMulHeight = V.mulHeight ^ ((finrank ℚ K : ℝ))⁻¹ :=
  Projectivization.absMulHeight_eq _

/-- The logarithmic form of `Submodule.absMulHeight_eq`. -/
theorem absLogHeight_eq [NumberField K] (V : Submodule K (ι → K)) :
    V.absLogHeight = ((finrank ℚ K : ℝ))⁻¹ * V.logHeight := by
  rw [absLogHeight_eq_log_absMulHeight, absMulHeight_eq, Real.log_rpow (mulHeight_pos V),
    logHeight_eq_log_mulHeight, mul_comm]

end Absolute

end Submodule

/-!
### Worked examples
-/

section Examples

open Submodule

/-- **Acceptance test.** The height of the line `ℚ · (1, 3)` in `ℚ²` is `3`: the Plücker
coordinates of a line are the coordinates of a vector spanning it, and the projective height of
`(1, 3)` is `3`. -/
example : (span ℚ {![(1 : ℚ), 3]}).mulHeight = 3 := by
  rw [mulHeight_span_singleton (by simp), Height.mulHeight_swap,
    ← Height.mulHeight₁_eq_mulHeight, Rat.mulHeight₁_eq_max]
  norm_num

/-- **Rejection test: the height of a subspace is not monotone under inclusion.** The line above
is contained in `⊤`, whose height is `1`. So no bound on the height of a subspace of `V` in terms
of the height of `V` is available, and in particular the vectors of a basis of `V` are not bounded
by `Submodule.mulHeight V`. Layer 5 bounds the vectors it produces through the successive minima
and never through the height of the space they span. -/
example : (⊤ : Submodule ℚ (Fin 2 → ℚ)).mulHeight = 1 ∧
    (⊤ : Submodule ℚ (Fin 2 → ℚ)).mulHeight < (span ℚ {![(1 : ℚ), 3]}).mulHeight := by
  refine ⟨mulHeight_top, ?_⟩
  rw [mulHeight_top]
  rw [show (span ℚ {![(1 : ℚ), 3]}).mulHeight = 3 from by
    rw [mulHeight_span_singleton (by simp), Height.mulHeight_swap,
      ← Height.mulHeight₁_eq_mulHeight, Rat.mulHeight₁_eq_max]
    norm_num]
  norm_num

/-- **Conformance.** The two degenerate ranks of the roadmap's milestone, and the compatibility
that fixes the definition, over an arbitrary field with admissible absolute values. -/
example {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {ι : Type*} [Fintype ι]
    [LinearOrder ι] {x : ι → K} (hx : x ≠ 0) :
    (⊥ : Submodule K (ι → K)).mulHeight = 1 ∧ (⊤ : Submodule K (ι → K)).mulHeight = 1 ∧
      (span K {x}).mulHeight = Height.mulHeight x :=
  ⟨mulHeight_bot, mulHeight_top, mulHeight_span_singleton hx⟩

end Examples

end
