/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.Actions
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Limit

/-!
# ShellSum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The additive layer on the frozen shell-field carrier

The frozen `ShellField` carrier of ABK26 bundles a matrix value field with its
stored first and second derivatives; up to now the repository only carried the
multiplicative actions (amplitude scaling, translation, spatial and triadic
scaling, negation, signed-permutation conjugation).  This module adds the
missing additive operations.

All three defining clauses of the frozen carrier are additive: the two `HasFDerivAt`
clauses by `Has.sum`, and entrywise antisymmetry linearly.  So there is no
structural obstruction, and the sum of shell fields carries honest derivative
data rather than a re-derived one.

The resulting `shellIncrement omega n m` is a genuine `ShellField` whose values
are exactly the stream increment `k_m - k_n` of the manuscript, by
`shellIncrement_apply_eq_cutoff_sub`.

## Main definitions

* `ShellField.zero`, `ShellField.add`, `ShellField.sum`: the additive layer.
* `shellIncrement`: the finite stream increment as a shell field.

## Main results

* `ShellField.zero_apply`, `ShellField.add_apply`, `ShellField.sum_apply` and
  their first- and second-derivative analogues: the defining pointwise
  characterizations.
* `shellIncrement_apply`: the increment's values are the proved regular-field
  increment `finiteShellIncrement`.
* `shellIncrement_apply_eq_cutoff_sub`: the increment's values are literally
  `k_m x - k_n x`.

## References

* ABK26, `e.Bosc.def`, `e.Bosc.decomp`.
-/

namespace Algsuperdiff.Frozen.Assumptions.ShellField

open HCPolySupport
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-- Migration cache (mathlib v4.33.1): `ContinuousLinearMap.add` on the nested second-derivative
fibre needs `ContinuousAdd (Vec d →L[ℝ] Mat d)` as a hypothesis (the codomain of the outer map).
A blind search for that hypothesis tries the `IsTopologicalAddGroup.toContinuousAdd` route only
after first wandering, unsuccessfully, through every `Vec d →L[ℝ] Mat d`-as-endomorphism-ring
candidate (`IsSemitopologicalSemiring`, `IsTopologicalSemiring`, down through `CStarAlgebra`,
`NormedRing`, `Field`, …), and gives up before ever reaching the right one.  Naming the direct
term sidesteps that search entirely; it is what the nested-level caches below build on. -/
instance instContinuousAddVecMatCLM (d : ℕ) :
    ContinuousAdd (Vec d →L[ℝ] Mat d) :=
  ContinuousLinearMap.isTopologicalAddGroup.toContinuousAdd

/-- Migration cache (mathlib v4.33.1): pin the nested second-derivative fibre's
`TopologicalSpace`/`IsTopologicalAddGroup`/`ContinuousAdd` directly via
`ContinuousLinearMap.topologicalSpace` / `ContinuousLinearMap.topologicalAddGroup`, now that the
one-level-down hypothesis (`instContinuousAddVecMatCLM` above) resolves immediately instead of
wandering.  An earlier version of this cache instead proved `ContinuousAdd` at the nested type via
a bare `inferInstance`-built `private theorem` turned into a `local instance`; under mathlib
v4.33.0 that candidate's explicit `(d : ℕ)` argument fails to unify with the ambient section `d`
at the actual `Continuous.add` use sites below (`tryResolve` reports a stray metavariable), even
though the identical goal succeeds when posed in isolation.  Building `ContinuousAdd` directly
from a plain (non-`local`) instance avoids that failure entirely. -/
instance instTopologicalSpaceVecVecMatCLM (d : ℕ) :
    TopologicalSpace (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  ContinuousLinearMap.topologicalSpace

instance instIsTopologicalAddGroupVecVecMatCLM (d : ℕ) :
    IsTopologicalAddGroup (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  ContinuousLinearMap.isTopologicalAddGroup

instance instContinuousAddVecVecMatCLM (d : ℕ) :
    ContinuousAdd (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  (instIsTopologicalAddGroupVecVecMatCLM d).toContinuousAdd

instance instAddCommGroupVecVecMatCLM (d : ℕ) :
    AddCommGroup (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  ContinuousLinearMap.addCommGroup

/-! ## The zero shell field -/

/-- The identically zero shell field, with zero derivative data. -/
def zero (d : ℕ) : ShellField d :=
  ⟨(⟨fun _ => 0, continuous_const⟩,
      (⟨fun _ => 0, continuous_const⟩, ⟨fun _ => 0, continuous_const⟩)), by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact hasFDerivAt_const (0 : Mat d) x
    · intro x
      exact hasFDerivAt_const (0 : Vec d →L[ℝ] Mat d) x
    · intro _ _ _
      simp⟩

@[simp]
theorem zero_apply (x : Vec d) : zero d x = 0 :=
  rfl

@[simp]
theorem zero_deriv (x : Vec d) : deriv (zero d) x = 0 :=
  rfl

@[simp]
theorem zero_secondDeriv (x : Vec d) : secondDeriv (zero d) x = 0 :=
  rfl

/-! ## Binary sums -/

/-- Continuity of the summed second-derivative field, as a standalone lemma.  Ordinary instance
search for `ContinuousAdd` on the nested second-derivative fibre leaves `d` tied to an unresolved
metavariable at every use site below (mathlib v4.33.0), even though the identical goal resolves
immediately once posed on its own; supplying `instContinuousAddVecVecMatCLM` explicitly via `@`
sidesteps that search rather than relying on it. -/
theorem continuous_add_secondDeriv (j k : ShellField d) :
    Continuous (fun x => secondDeriv j x + secondDeriv k x) :=
  @Continuous.add (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) _ _ (instContinuousAddVecVecMatCLM d)
    (Vec d) _ _ _ (secondDeriv j).continuous (secondDeriv k).continuous

/-- The pointwise sum of two shell fields, with the summed derivative data. -/
def add (j k : ShellField d) : ShellField d :=
  ⟨(⟨fun x => j x + k x, j.1.1.continuous.add k.1.1.continuous⟩,
      (⟨fun x => deriv j x + deriv k x,
          (deriv j).continuous.add (deriv k).continuous⟩,
        ⟨fun x => secondDeriv j x + secondDeriv k x,
          continuous_add_secondDeriv j k⟩)), by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact (j.hasFDerivAt x).add (k.hasFDerivAt x)
    · intro x
      exact (j.deriv_hasFDerivAt x).add (k.deriv_hasFDerivAt x)
    · intro x i l
      change j x i l + k x i l = -(j x l i + k x l i)
      rw [j.skew_entry x i l, k.skew_entry x i l]
      ring⟩

@[simp]
theorem add_apply (j k : ShellField d) (x : Vec d) :
    add j k x = j x + k x :=
  rfl

@[simp]
theorem add_deriv (j k : ShellField d) (x : Vec d) :
    deriv (add j k) x = deriv j x + deriv k x :=
  rfl

@[simp]
theorem add_secondDeriv (j k : ShellField d) (x : Vec d) :
    secondDeriv (add j k) x = secondDeriv j x + secondDeriv k x :=
  rfl

/-! ## Finite sums -/

/-- Continuity of the finite-summed second-derivative field, as a standalone lemma; see
`continuous_add_secondDeriv` for why the needed instances are supplied explicitly via `@`
rather than left to search. -/
theorem continuous_sum_secondDeriv {ι : Type*} (s : Finset ι) (f : ι → ShellField d) :
    Continuous (fun x => ∑ i ∈ s, secondDeriv (f i) x) :=
  @continuous_finsetSum ι (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) (Vec d) _ _
    (instAddCommGroupVecVecMatCLM d).toAddCommMonoid (instContinuousAddVecVecMatCLM d)
    (fun i => secondDeriv (f i)) s fun i _ => (secondDeriv (f i)).continuous

/-- The pointwise `Finset` sum of shell fields, with the summed derivative
data.  This is the finite-sum carrier required by the literal oscillation
event of `e.Bosc.def`. -/
def sum {ι : Type*} (s : Finset ι) (f : ι → ShellField d) : ShellField d :=
  ⟨(⟨fun x => ∑ i ∈ s, f i x,
        continuous_finsetSum s fun i _ => (f i).1.1.continuous⟩,
      (⟨fun x => ∑ i ∈ s, deriv (f i) x,
          continuous_finsetSum s fun i _ => (deriv (f i)).continuous⟩,
        ⟨fun x => ∑ i ∈ s, secondDeriv (f i) x,
          continuous_sum_secondDeriv s f⟩)), by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      have h : HasFDerivAt (fun y => ∑ i ∈ s, f i y)
          (∑ i ∈ s, deriv (f i) x) x := by
        refine (HasFDerivAt.sum (u := s)
          (fun i _ => (f i).hasFDerivAt x)).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun y => ?_)
        exact (Finset.sum_apply y s _).symm
      exact h
    · intro x
      have h : HasFDerivAt (fun y => ∑ i ∈ s, deriv (f i) y)
          (∑ i ∈ s, secondDeriv (f i) x) x := by
        refine (HasFDerivAt.sum (u := s)
          (fun i _ => (f i).deriv_hasFDerivAt x)).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun y => ?_)
        exact (Finset.sum_apply y s _).symm
      exact h
    · intro x a b
      change (∑ i ∈ s, f i x) a b = -(∑ i ∈ s, f i x) b a
      simp only [Matrix.sum_apply]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => (f i).skew_entry x a b⟩

@[simp]
theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → ShellField d) (x : Vec d) :
    sum s f x = ∑ i ∈ s, f i x :=
  rfl

@[simp]
theorem sum_empty {ι : Type*} (f : ι → ShellField d) :
    sum (∅ : Finset ι) f = zero d :=
  ext fun x => by
    simp only [sum_apply, Finset.sum_empty, zero_apply]

theorem sum_cons {ι : Type*} {a : ι} {s : Finset ι} (ha : a ∉ s)
    (f : ι → ShellField d) :
    sum (Finset.cons a s ha) f = add (f a) (sum s f) :=
  ext fun x => by
    simp only [sum_apply, Finset.sum_cons, add_apply]

/-- Translation commutes with finite sums of shell fields. -/
theorem translate_sum {ι : Type*} (z : Vec d) (s : Finset ι)
    (f : ι → ShellField d) :
    translate z (sum s f) = sum s fun i => translate z (f i) :=
  ext fun x => by
    simp only [translate_apply, sum_apply]

end

end Algsuperdiff.Frozen.Assumptions.ShellField

namespace Algsuperdiff.Section3.Provider.Stream

open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- The finite stream increment `k_m - k_n` as a genuine shell field: the
literal sum of the shells with indices in `(n, m]`, carrying honest first and
second derivative data. -/
def shellIncrement (omega : ShellSeq d) (n m : ℤ) : ShellField d :=
  ShellField.sum (Finset.Ioc n m) omega

/-- The increment shell field has exactly the values of the proved
regular-coefficient-field increment. -/
theorem shellIncrement_apply (omega : ShellSeq d) (n m : ℤ) (x : Vec d) :
    shellIncrement omega n m x = finiteShellIncrement omega n m x := by
  rw [finiteShellIncrement_apply]
  rfl

/-- The values of the increment shell field are literally `k_m x - k_n x`.
This is the identification the literal oscillation event `e.Bosc.def` needs. -/
theorem shellIncrement_apply_eq_cutoff_sub (omega : CutoffSample d) {n m : ℤ}
    (hnm : n ≤ m) (x : Vec d) :
    shellIncrement omega.1 n m x = cutoff m omega x - cutoff n omega x := by
  rw [shellIncrement_apply,
    cutoff_sub_cutoff_eq_finiteShellIncrement omega hnm x]

end

end Algsuperdiff.Section3.Provider.Stream
