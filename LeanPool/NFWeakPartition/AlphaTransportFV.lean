/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaTransport

/-! NF weak partition development: AlphaTransportFV. -/


public section

namespace NFChoice.DefinitionLeaves.AlphaTransport

open NFChoice.Foundation
open NFChoice.SemanticCore

/-! Free-variable reflexivity for alpha certificates.

`EnvFresh env p.vars` is intentionally stronger than the semantic freshness
needed when an unchanged subtree is reused beneath renamed external binders:
`vars` also exposes binders internal to `p`.  `ReflOn` records the exact
structural invariant instead.  Every free occurrence in the subtree must
already possess a reflexive `AlphaVar` certificate.  Extending the environment
with an identical binder `(x,x)` then handles occurrences of `x` by `here` and
lifts every other certificate by `there`.
-/


/-- Every name in `support` has a reflexive alpha-variable certificate. -/
@[expose]
def ReflOn (env : BinderEnv) (support : Finset Var) : Prop :=
  ∀ ⦃u⦄, u ∈ support → AlphaVar env u u

theorem ReflOn.mono {env : BinderEnv} {small large : Finset Var} (h : ReflOn env large)
    (hsub : small ⊆ large) : ReflOn env small :=
  by
  intro u hu
  exact h (hsub hu)

/-- The old external-freshness contract implies the exact reflexive invariant. -/
theorem EnvFresh.reflOn {env : BinderEnv} {support : Finset Var}
    (h : EnvFresh env support) : ReflOn env support :=
  by
  intro u hu
  apply AlphaVar.reflOfFresh env u
  exact h.mono (by simpa using (Finset.singleton_subset_iff.mpr hu))

theorem ReflOn.extendSame {env : BinderEnv} {support : Finset Var}
    (h : ReflOn env (support.erase x)) : ReflOn ((x, x) :: env) support :=
  by
  intro u hu
  by_cases hux : u = x
  · subst u
    exact .here _ _ _
  · exact .there hux hux (h (Finset.mem_erase.mpr ⟨hux, hu⟩))

mutual
  /-- Reflexive class alpha certificate from semantic free-variable support. -/
  theorem AlphaClass.reflOfReflOn (env : BinderEnv) (A : Class) (h : ReflOn env A.fv) :
      AlphaClass env A A := by
    cases A with
    | cv x => exact .cv (h (by simp [Class.fv]))
    | cab x p =>
      apply AlphaClass.cab
      exact AlphaWff.reflOfReflOn ((x, x) :: env) p (ReflOn.extendSame h)
  /-- Reflexive formula alpha certificate from semantic free-variable support. -/
  theorem AlphaWff.reflOfReflOn (env : BinderEnv) (p : Wff) (h : ReflOn env p.fv) :
      AlphaWff env p p := by
    cases p with
    | falsum => exact .falsum
    | imp p q =>
      apply AlphaWff.imp
      · exact AlphaWff.reflOfReflOn env p (h.mono (by intro u hu; simp [Wff.fv, hu]))
      · exact AlphaWff.reflOfReflOn env q (h.mono (by intro u hu; simp [Wff.fv, hu]))
    | all x p =>
      apply AlphaWff.all
      exact AlphaWff.reflOfReflOn ((x, x) :: env) p (ReflOn.extendSame h)
    | objEq x y => exact .objEq (h (by simp [Wff.fv])) (h (by simp [Wff.fv]))
    | objMem x y => exact .objMem (h (by simp [Wff.fv])) (h (by simp [Wff.fv]))
    | classEq A B =>
      apply AlphaWff.classEq
      · exact AlphaClass.reflOfReflOn env A (h.mono (by intro u hu; simp [Wff.fv, hu]))
      · exact AlphaClass.reflOfReflOn env B (h.mono (by intro u hu; simp [Wff.fv, hu]))
    | classMem A B =>
      apply AlphaWff.classMem
      · exact AlphaClass.reflOfReflOn env A (h.mono (by intro u hu; simp [Wff.fv, hu]))
      · exact AlphaClass.reflOfReflOn env B (h.mono (by intro u hu; simp [Wff.fv, hu]))
end

/-- Drop-in replacement for `AlphaClass.refl_of_fresh` using only `fv`. -/
theorem _root_.NFChoice.DefinitionLeaves.AlphaTransport.AlphaClass.reflOfFvFresh
    (env : BinderEnv) (A : Class)
    (h : EnvFresh env A.fv) : AlphaClass env A A :=
  AlphaClass.reflOfReflOn env A h.reflOn

/-- Drop-in replacement for `AlphaWff.refl_of_fresh` using only `fv`. -/
theorem _root_.NFChoice.DefinitionLeaves.AlphaTransport.AlphaWff.reflOfFvFresh
    (env : BinderEnv) (p : Wff) (h : EnvFresh env p.fv) :
    AlphaWff env p p :=
  AlphaWff.reflOfReflOn env p h.reflOn


end NFChoice.DefinitionLeaves.AlphaTransport
