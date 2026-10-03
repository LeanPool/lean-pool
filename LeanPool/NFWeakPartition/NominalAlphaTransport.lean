/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalDfEu

/-! NF weak partition development: NominalAlphaTransport. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore

/-! Proof-relevant alpha certificates for the direct syntactic replay.

The semantic replay's `AlphaVar`/`AlphaWff`/`AlphaClass` live in `Prop`, so
Lean may not eliminate them into the proof-object type `Fol.prf`.  These
parallel `Type`-valued certificates retain the same constructor shapes.  Their
eliminator proves that paired nominal binders lower to identical de-Bruijn
formulas; the public handlers then reduce alpha transport to reflexivity.
-/


/-- Paired nominal binders, nearest binder first. -/
abbrev TBinderEnv :=
  List (Var × Var)

/-- Proof-relevant correspondence of variable occurrences. -/
inductive TAlphaVar : TBinderEnv → Var → Var → Type where
  | here (env : TBinderEnv) (x y : Var) : TAlphaVar ((x, y) :: env) x y
  |
  there {env : TBinderEnv} {x y a b : Var} (ha : a ≠ x) (hb : b ≠ y)
    (h : TAlphaVar env a b) : TAlphaVar ((x, y) :: env) a b
  |
  free {env : TBinderEnv} {x : Var} (hl : x ∉ env.map Prod.fst)
    (hr : x ∉ env.map Prod.snd) : TAlphaVar env x x

mutual
  /-- Proof-relevant alpha equivalence of nominal classes. -/
  inductive TAlphaClass : TBinderEnv → Class → Class → Type where
    |
    cv {env : TBinderEnv} {x y : Var} (h : TAlphaVar env x y) :
      TAlphaClass env (.cv x) (.cv y)
    |
    cab {env : TBinderEnv} {x y : Var} {p q : Wff} (h : TAlphaWff ((x, y) :: env) p q) :
      TAlphaClass env (.cab x p) (.cab y q)
  /-- Proof-relevant alpha equivalence of nominal formulas. -/
  inductive TAlphaWff : TBinderEnv → Wff → Wff → Type where
    | falsum {env : TBinderEnv} : TAlphaWff env .falsum .falsum
    |
    imp {env : TBinderEnv} {p p' q q' : Wff} (hp : TAlphaWff env p p')
      (hq : TAlphaWff env q q') : TAlphaWff env (.imp p q) (.imp p' q')
    |
    all {env : TBinderEnv} {x y : Var} {p q : Wff} (h : TAlphaWff ((x, y) :: env) p q) :
      TAlphaWff env (.all x p) (.all y q)
    |
    objEq {env : TBinderEnv} {x x' y y' : Var} (hx : TAlphaVar env x x')
      (hy : TAlphaVar env y y') : TAlphaWff env (.objEq x y) (.objEq x' y')
    |
    objMem {env : TBinderEnv} {x x' y y' : Var} (hx : TAlphaVar env x x')
      (hy : TAlphaVar env y y') : TAlphaWff env (.objMem x y) (.objMem x' y')
    |
    classEq {env : TBinderEnv} {A A' B B' : Class} (hA : TAlphaClass env A A')
      (hB : TAlphaClass env B B') : TAlphaWff env (.classEq A B) (.classEq A' B')
    |
    classMem {env : TBinderEnv} {A A' B B' : Class} (hA : TAlphaClass env A A')
      (hB : TAlphaClass env B B') : TAlphaWff env (.classMem A B) (.classMem A' B')
end

/-- The two de-Bruijn environments agree on every paired occurrence. -/
@[expose]
def TRhoAgree (env : TBinderEnv) (rho sigma : Var → Nat) : Prop :=
  ∀ ⦃x y⦄, TAlphaVar env x y → rho x = sigma y

theorem TRhoAgree.bind {env : TBinderEnv} {rho sigma : Var → Nat}
    (h : TRhoAgree env rho sigma) (x y : Var) :
    TRhoAgree ((x, y) :: env) (bindRho rho x) (bindRho sigma y) :=
  by
  intro u v huv
  cases huv with
  | here => simp [bindRho]
  | there hu hv htail => simp [bindRho, hu, hv, h htail]
  | free hl hr =>
    simp only [List.map_cons, List.mem_cons, not_or] at hl hr
    have htail : TAlphaVar env u u := .free hl.2 hr.2
    simp [bindRho, hl.1, hr.1, h htail]

theorem TRhoAgree.update {env : TBinderEnv} {rho sigma : Var → Nat}
    (h : TRhoAgree env rho sigma) (x y : Var) (candidate : Nat) :
    TRhoAgree ((x, y) :: env) (updateRho rho x candidate) (updateRho sigma y candidate) :=
  by
  intro u v huv
  cases huv with
  | here => simp [updateRho]
  | there hu hv htail => simp [updateRho, hu, hv, h htail]
  | free hl hr =>
    simp only [List.map_cons, List.mem_cons, not_or] at hl hr
    have htail : TAlphaVar env u u := .free hl.2 hr.2
    simp [updateRho, hl.1, hr.1, h htail]

theorem TRhoAgree.lift {env : TBinderEnv} {rho sigma : Var → Nat}
    (h : TRhoAgree env rho sigma) : TRhoAgree env (liftRho rho) (liftRho sigma) :=
  by
  intro x y hxy
  simp [liftRho, h hxy]

theorem tRhoAgree_empty (rho : Var → Nat) : TRhoAgree [] rho rho :=
  by
  intro x y hxy
  cases hxy with
  | free => rfl

mutual
  /-- Alpha-equivalent classes lower to the same candidate predicate. -/
  theorem TAlphaClass.lower_eq {env : TBinderEnv} {A B : Class} (h : TAlphaClass env A B)
      {rho sigma : Var → Nat} (hrho : TRhoAgree env rho sigma) (candidate : Nat) :
      lowerClassPred rho candidate A = lowerClassPred sigma candidate B := by
    cases h with
    | cv hx => simp [lowerClassPred, hrho hx]
    | cab hp =>
      simp only [lowerClassPred]
      exact TAlphaWff.lower_eq hp (TRhoAgree.update hrho _ _ candidate)
  /-- Alpha-equivalent formulas lower to the same de-Bruijn formula. -/
  theorem TAlphaWff.lower_eq {env : TBinderEnv} {p q : Wff} (h : TAlphaWff env p q)
      {rho sigma : Var → Nat} (hrho : TRhoAgree env rho sigma) :
      lowerWff rho p = lowerWff sigma q := by
    cases h with
    | falsum => rfl
    | imp hp hq =>
      simp only [lowerWff]
      rw [TAlphaWff.lower_eq hp hrho, TAlphaWff.lower_eq hq hrho]
    | all hp =>
      simp only [lowerWff]
      exact congrArg Fol.preformula.all (TAlphaWff.lower_eq hp (TRhoAgree.bind hrho _ _))
    | objEq hx hy => simp [lowerWff, hrho hx, hrho hy]
    | objMem hx hy => simp [lowerWff, hrho hx, hrho hy]
    | classEq hA hB =>
      simp only [lowerWff]
      rw [TAlphaClass.lower_eq hA (TRhoAgree.lift hrho) 0]
      rw [TAlphaClass.lower_eq hB (TRhoAgree.lift hrho) 0]
    | classMem hA hB =>
      simp only [lowerWff]
      rw [TAlphaClass.lower_eq hA (TRhoAgree.lift (TRhoAgree.lift hrho)) 0]
      rw [TAlphaClass.lower_eq hB (TRhoAgree.lift hrho) 0]
end

namespace TAlphaWff

@[expose]
def neg {env : TBinderEnv} {p q : Wff} (h : TAlphaWff env p q) :
    TAlphaWff env (Wff.neg p) (Wff.neg q) :=
  .imp h .falsum

@[expose]
def conj {env : TBinderEnv} {p p' q q' : Wff} (hp : TAlphaWff env p p')
    (hq : TAlphaWff env q q') : TAlphaWff env (Wff.conj p q) (Wff.conj p' q') :=
  neg (.imp hp (neg hq))

@[expose]
def biimp {env : TBinderEnv} {p p' q q' : Wff} (hp : TAlphaWff env p p')
    (hq : TAlphaWff env q q') : TAlphaWff env (Wff.biimp p q) (Wff.biimp p' q') :=
  conj (.imp hp hq) (.imp hq hp)

@[expose]
def ex {env : TBinderEnv} {x y : Var} {p q : Wff} (h : TAlphaWff ((x, y) :: env) p q) :
    TAlphaWff env (Wff.ex x p) (Wff.ex y q) :=
  neg (.all (neg h))

end TAlphaWff

/-- Freshness condition used by mechanically emitted reflexive subtrees. -/
@[expose]
def TEnvFresh (env : TBinderEnv) (support : Finset Var) : Prop :=
  ∀ ⦃x y⦄, (x, y) ∈ env → x ≠ y → x ∉ support ∧ y ∉ support

/-- Every binder environment is fresh for an empty support. -/
theorem TEnvFresh.of_empty {env : TBinderEnv} {support : Finset Var} (h : support = ∅) :
    TEnvFresh env support := by
  rw [h]
  intro x y _ _
  exact ⟨Finset.notMem_empty x, Finset.notMem_empty y⟩

/-- Extend a fresh binder environment by two fresh endpoints. -/
theorem TEnvFresh.cons {env : TBinderEnv} {support : Finset Var} {x y : Var}
    (hx : x ∉ support) (hy : y ∉ support) (htail : TEnvFresh env support) :
    TEnvFresh ((x, y) :: env) support :=
  by
  intro a b hab hne
  rcases List.mem_cons.mp hab with h | h
  · rcases Prod.mk.inj h with ⟨rfl, rfl⟩
    exact ⟨hx, hy⟩
  · exact htail h hne

theorem TEnvFresh.mono {env : TBinderEnv} {small large : Finset Var}
    (h : TEnvFresh env large) (hsub : small ⊆ large) : TEnvFresh env small :=
  by
  intro x y hxy hne
  rcases h hxy hne with ⟨hx, hy⟩
  exact ⟨fun hm => hx (hsub hm), fun hm => hy (hsub hm)⟩

@[expose]
def TAlphaVar.refl_of_fresh (env : TBinderEnv) (u : Var) (h : TEnvFresh env { u }) :
    TAlphaVar env u u := by
  induction env with
  | nil => exact .free (by simp) (by simp)
  | cons head tail ih =>
    rcases head with ⟨x, y⟩
    have htail : TEnvFresh tail { u } :=
      by
      intro a b hab hne
      exact h (by simp [hab]) hne
    by_cases hxy : x = y
    · subst y
      by_cases hux : u = x
      · subst u
        exact .here _ _ _
      · exact .there hux hux (ih htail)
    · have hfresh := h (by simp) hxy
      have hux : u ≠ x := by simpa [ne_eq, eq_comm] using hfresh.1
      have huy : u ≠ y := by simpa [ne_eq, eq_comm] using hfresh.2
      exact .there hux huy (ih htail)

/-- Proof-relevant reflexivity for every free variable in a support. -/
@[expose]
def TReflOn (env : TBinderEnv) (support : Finset Var) : Type :=
  ∀ ⦃u⦄, u ∈ support → TAlphaVar env u u

@[expose]
def TReflOn.mono {env : TBinderEnv} {small large : Finset Var} (h : TReflOn env large)
    (hsub : small ⊆ large) : TReflOn env small := fun _ hu => h (hsub hu)

@[expose]
def TEnvFresh.reflOn {env : TBinderEnv} {support : Finset Var}
    (h : TEnvFresh env support) : TReflOn env support :=
  by
  intro u hu
  apply TAlphaVar.refl_of_fresh env u
  exact h.mono (by simpa using (Finset.singleton_subset_iff.mpr hu))

@[expose]
def TReflOn.extend_same {env : TBinderEnv} {support : Finset Var}
    (h : TReflOn env (support.erase x)) : TReflOn ((x, x) :: env) support :=
  by
  intro u hu
  by_cases hux : u = x
  · subst u
    exact .here _ _ _
  · exact .there hux hux (h (Finset.mem_erase.mpr ⟨hux, hu⟩))

mutual
  /-- Reflexive class certificate from exact semantic free-variable support. -/
  @[expose]
  def TAlphaClass.refl_of_reflOn (env : TBinderEnv) (A : Class) (h : TReflOn env A.fv) :
      TAlphaClass env A A := by
    cases A with
    | cv x => exact .cv (h (by simp [Class.fv]))
    | cab x p =>
      apply TAlphaClass.cab
      exact TAlphaWff.refl_of_reflOn ((x, x) :: env) p (TReflOn.extend_same h)
  /-- Reflexive formula certificate from exact semantic free-variable support. -/
  @[expose]
  def TAlphaWff.refl_of_reflOn (env : TBinderEnv) (p : Wff) (h : TReflOn env p.fv) :
      TAlphaWff env p p := by
    cases p with
    | falsum => exact .falsum
    | imp p q =>
      apply TAlphaWff.imp
      · exact TAlphaWff.refl_of_reflOn env p (h.mono (by intro u hu; simp [Wff.fv, hu]))
      · exact TAlphaWff.refl_of_reflOn env q (h.mono (by intro u hu; simp [Wff.fv, hu]))
    | all x p =>
      apply TAlphaWff.all
      exact TAlphaWff.refl_of_reflOn ((x, x) :: env) p (TReflOn.extend_same h)
    | objEq x y => exact .objEq (h (by simp [Wff.fv])) (h (by simp [Wff.fv]))
    | objMem x y => exact .objMem (h (by simp [Wff.fv])) (h (by simp [Wff.fv]))
    | classEq A B =>
      apply TAlphaWff.classEq
      · exact TAlphaClass.refl_of_reflOn env A (h.mono (by intro u hu; simp [Wff.fv, hu]))
      · exact TAlphaClass.refl_of_reflOn env B (h.mono (by intro u hu; simp [Wff.fv, hu]))
    | classMem A B =>
      apply TAlphaWff.classMem
      · exact TAlphaClass.refl_of_reflOn env A (h.mono (by intro u hu; simp [Wff.fv, hu]))
      · exact TAlphaClass.refl_of_reflOn env B (h.mono (by intro u hu; simp [Wff.fv, hu]))
end

/-- Drop-in `fv`-based reflexivity expected by the frozen AlphaEmitter. -/
@[expose]
def TAlphaClass.refl_of_fv_fresh (env : TBinderEnv) (A : Class) (h : TEnvFresh env A.fv) :
    TAlphaClass env A A :=
  TAlphaClass.refl_of_reflOn env A h.reflOn

/-- A closed nominal class is alpha-reflexive in every binder environment. -/
@[expose]
def TAlphaClass.refl_of_closed (env : TBinderEnv) (A : Class) (hclosed : A.fv = ∅) :
    TAlphaClass env A A :=
  TAlphaClass.refl_of_fv_fresh env A
    (by
      rw [hclosed]
      intro x y hxy hne
      exact ⟨Finset.notMem_empty x, Finset.notMem_empty y⟩)

/-- Drop-in `fv`-based reflexivity expected by the frozen AlphaEmitter. -/
@[expose]
def TAlphaWff.refl_of_fv_fresh (env : TBinderEnv) (p : Wff) (h : TEnvFresh env p.fv) :
    TAlphaWff env p p :=
  TAlphaWff.refl_of_reflOn env p h.reflOn

mutual
  /-- Reflexive class certificate under externally fresh renamed binders. -/
  @[expose]
  def TAlphaClass.refl_of_fresh (env : TBinderEnv) (A : Class)
      (h : TEnvFresh env A.vars) : TAlphaClass env A A := by
    cases A with
    | cv x =>
      apply TAlphaClass.cv
      apply TAlphaVar.refl_of_fresh env x
      exact h.mono (by simp [Class.vars])
    | cab x p =>
      apply TAlphaClass.cab
      apply TAlphaWff.refl_of_fresh ((x, x) :: env) p
      intro a b hab hne
      rcases List.mem_cons.mp hab with hab | hab
      · cases hab
        exact (hne rfl).elim
      · have hf := h hab hne
        simp only [Class.vars, Finset.mem_insert, not_or] at hf
        exact ⟨hf.1.2, hf.2.2⟩
  /-- Reflexive formula certificate under externally fresh renamed binders. -/
  @[expose]
  def TAlphaWff.refl_of_fresh (env : TBinderEnv) (p : Wff) (h : TEnvFresh env p.vars) :
      TAlphaWff env p p := by
    cases p with
    | falsum => exact .falsum
    | imp p q =>
      apply TAlphaWff.imp
      · exact TAlphaWff.refl_of_fresh env p (h.mono (by intro u hu; simp [Wff.vars, hu]))
      · exact TAlphaWff.refl_of_fresh env q (h.mono (by intro u hu; simp [Wff.vars, hu]))
    | all x p =>
      apply TAlphaWff.all
      apply TAlphaWff.refl_of_fresh ((x, x) :: env) p
      intro a b hab hne
      rcases List.mem_cons.mp hab with hab | hab
      · cases hab
        exact (hne rfl).elim
      · have hf := h hab hne
        simp only [Wff.vars, Finset.mem_insert, not_or] at hf
        exact ⟨hf.1.2, hf.2.2⟩
    | objEq x y =>
      apply TAlphaWff.objEq
      · apply TAlphaVar.refl_of_fresh env x
        exact h.mono (by simp [Wff.vars])
      · apply TAlphaVar.refl_of_fresh env y
        exact h.mono (by simp [Wff.vars])
    | objMem x y =>
      apply TAlphaWff.objMem
      · apply TAlphaVar.refl_of_fresh env x
        exact h.mono (by simp [Wff.vars])
      · apply TAlphaVar.refl_of_fresh env y
        exact h.mono (by simp [Wff.vars])
    | classEq A B =>
      apply TAlphaWff.classEq
      · exact
          TAlphaClass.refl_of_fresh env A (h.mono (by intro u hu; simp [Wff.vars, hu]))
      · exact
          TAlphaClass.refl_of_fresh env B (h.mono (by intro u hu; simp [Wff.vars, hu]))
    | classMem A B =>
      apply TAlphaWff.classMem
      · exact
          TAlphaClass.refl_of_fresh env A (h.mono (by intro u hu; simp [Wff.vars, hu]))
      · exact
          TAlphaClass.refl_of_fresh env B (h.mono (by intro u hu; simp [Wff.vars, hu]))
end

/-- Direct syntactic transport for Wff-valued alpha definitions. -/
@[expose]
noncomputable def alphaBiimp {p q : Wff} (h : TAlphaWff [] p q) : NPrf (Wff.biimp p q) :=
  fun rho => by
  have heq := TAlphaWff.lower_eq h (tRhoAgree_empty rho)
  change Fol.prf _ (biimp (lowerWff rho p) (lowerWff rho q))
  rw [← heq]
  exact Fol.biimp_refl _ _

/-- Direct syntactic transport for class-valued alpha definitions. -/
@[expose]
noncomputable def alphaClassEq {A B : Class} (h : TAlphaClass [] A B) :
    NPrf (.classEq A B) := fun rho =>
  by
  have heq := TAlphaClass.lower_eq h (TRhoAgree.lift (tRhoAgree_empty rho)) 0
  simp only [lowerWff]
  rw [heq]
  exact Fol.prf.allI (Fol.biimp_refl _ _)


end NFChoice.DirectNominalPrf.Nominal
