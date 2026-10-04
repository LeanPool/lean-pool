/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.DefinitionLeaves.Basic

/-! NF weak partition development: AlphaTransport. -/


public section

namespace NFChoice.DefinitionLeaves.AlphaTransport

open NFChoice.Foundation
open NFChoice.SemanticCore

/-- A paired stack of corresponding nominal binders, nearest binder first. -/
abbrev BinderEnv :=
  List (Var × Var)

/-- Two variable occurrences denote the same de Bruijn position, or are the same
free nominal variable outside the paired binder environment.
-/
inductive AlphaVar : BinderEnv → Var → Var → Prop where
  | here (env : BinderEnv) (x y : Var) : AlphaVar ((x, y) :: env) x y
  |
  there {env : BinderEnv} {x y a b : Var} (ha : a ≠ x) (hb : b ≠ y)
    (h : AlphaVar env a b) : AlphaVar ((x, y) :: env) a b
  |
  free {env : BinderEnv} {x : Var} (hl : x ∉ env.map Prod.fst)
    (hr : x ∉ env.map Prod.snd) : AlphaVar env x x

mutual
  /-- Alpha-equivalence of nominal class terms under paired binders. -/
  inductive AlphaClass : BinderEnv → Class → Class → Prop where
    |
    cv {env : BinderEnv} {x y : Var} (h : AlphaVar env x y) :
      AlphaClass env (.cv x) (.cv y)
    |
    cab {env : BinderEnv} {x y : Var} {p q : Wff} (h : AlphaWff ((x, y) :: env) p q) :
      AlphaClass env (.cab x p) (.cab y q)
  /-- Alpha-equivalence of nominal formulas under paired binders. -/
  inductive AlphaWff : BinderEnv → Wff → Wff → Prop where
    | falsum {env : BinderEnv} : AlphaWff env .falsum .falsum
    |
    imp {env : BinderEnv} {p p' q q' : Wff} (hp : AlphaWff env p p')
      (hq : AlphaWff env q q') : AlphaWff env (.imp p q) (.imp p' q')
    |
    all {env : BinderEnv} {x y : Var} {p q : Wff} (h : AlphaWff ((x, y) :: env) p q) :
      AlphaWff env (.all x p) (.all y q)
    |
    objEq {env : BinderEnv} {x x' y y' : Var} (hx : AlphaVar env x x')
      (hy : AlphaVar env y y') : AlphaWff env (.objEq x y) (.objEq x' y')
    |
    objMem {env : BinderEnv} {x x' y y' : Var} (hx : AlphaVar env x x')
      (hy : AlphaVar env y y') : AlphaWff env (.objMem x y) (.objMem x' y')
    |
    classEq {env : BinderEnv} {A A' B B' : Class} (hA : AlphaClass env A A')
      (hB : AlphaClass env B B') : AlphaWff env (.classEq A B) (.classEq A' B')
    |
    classMem {env : BinderEnv} {A A' B B' : Class} (hA : AlphaClass env A A')
      (hB : AlphaClass env B B') : AlphaWff env (.classMem A B) (.classMem A' B')
end

/-- Corresponding nominal variables have equal values in paired valuations. -/
@[expose]
def _root_.NFChoice.DefinitionLeaves.AlphaTransport.ValAgree
    {S : Type _} (env : BinderEnv) (v w : Var → S) : Prop :=
  ∀ ⦃x y⦄, AlphaVar env x y → v x = w y

theorem _root_.NFChoice.DefinitionLeaves.AlphaTransport.ValAgree.extend
    {S : Type _} {env : BinderEnv} {v w : Var → S}
    (h : ValAgree env v w) (x y : Var) (a : S) :
    ValAgree ((x, y) :: env) (update v x a) (update w y a) :=
  by
  intro u z huz
  cases huz with
  | here => simp
  | there hu hz htail => simpa [update_noteq, hu, hz] using h htail
  | free hl hr =>
    simp only [List.map_cons, List.mem_cons, not_or] at hl hr
    have htail : AlphaVar env u u := AlphaVar.free hl.2 hr.2
    simpa [update_noteq, hl.1, hr.1] using h htail

theorem _root_.NFChoice.DefinitionLeaves.AlphaTransport.valAgree_empty
    {S : Type _} (v : Var → S) : ValAgree [] v v :=
  by
  intro x y h
  cases h with
  | free => rfl

mutual
  /-- Alpha-equivalent classes have identical denotations. -/
  theorem _root_.NFChoice.DefinitionLeaves.AlphaTransport.AlphaClass.holds_iff
      {S : Fol.Structure LNF} {env : BinderEnv} {A B : Class}
      (h : AlphaClass env A B) {v w : Var → S} (hv : ValAgree env v w) (a : S) :
      Class.Holds S v A a ↔ Class.Holds S w B a := by
    cases h with
    | cv hx =>
      simp only [Class.Holds]
      rw [hv hx]
    | cab hp =>
      simp only [Class.Holds]
      exact AlphaWff.holds_iff hp (hv.extend _ _ a)
  /-- Alpha-equivalent formulas have identical truth values. -/
  theorem _root_.NFChoice.DefinitionLeaves.AlphaTransport.AlphaWff.holds_iff
      {S : Fol.Structure LNF} {env : BinderEnv} {p q : Wff}
      (h : AlphaWff env p q) {v w : Var → S} (hv : ValAgree env v w) :
      Wff.Holds S v p ↔ Wff.Holds S w q := by
    cases h with
    | falsum => rfl
    | imp hp hq =>
      simp only [Wff.Holds]
      exact Iff.imp (AlphaWff.holds_iff hp hv) (AlphaWff.holds_iff hq hv)
    | all hp =>
      simp only [Wff.Holds]
      apply forall_congr'
      intro a
      exact AlphaWff.holds_iff hp (hv.extend _ _ a)
    | objEq hx hy =>
      simp only [Wff.Holds]
      rw [hv hx, hv hy]
    | objMem hx hy =>
      simp only [Wff.Holds]
      rw [hv hx, hv hy]
    | classEq hA hB =>
      simp only [Wff.Holds]
      apply forall_congr'
      intro a
      have ha := AlphaClass.holds_iff hA hv a
      have hb := AlphaClass.holds_iff hB hv a
      tauto
    | classMem hA hB =>
      simp only [Wff.Holds]
      apply exists_congr
      intro a
      apply and_congr
      · apply forall_congr'
        intro z
        have ha := AlphaClass.holds_iff hA hv z
        tauto
      · exact AlphaClass.holds_iff hB hv a
end

namespace AlphaWff

theorem _root_.NFChoice.DefinitionLeaves.AlphaTransport.AlphaWff.neg
    {env : BinderEnv} {p q : Wff} (h : AlphaWff env p q) :
    AlphaWff env (Wff.neg p) (Wff.neg q) :=
  .imp h .falsum

theorem _root_.NFChoice.DefinitionLeaves.AlphaTransport.AlphaWff.conj
    {env : BinderEnv} {p p' q q' : Wff} (hp : AlphaWff env p p')
    (hq : AlphaWff env q q') : AlphaWff env (Wff.conj p q) (Wff.conj p' q') :=
  neg (.imp hp (neg hq))

theorem _root_.NFChoice.DefinitionLeaves.AlphaTransport.AlphaWff.biimp
    {env : BinderEnv} {p p' q q' : Wff} (hp : AlphaWff env p p')
    (hq : AlphaWff env q q') : AlphaWff env (Wff.biimp p q) (Wff.biimp p' q') :=
  conj (.imp hp hq) (.imp hq hp)

theorem _root_.NFChoice.DefinitionLeaves.AlphaTransport.AlphaWff.ex
    {env : BinderEnv} {x y : Var} {p q : Wff} (h : AlphaWff ((x, y) :: env) p q) :
    AlphaWff env (Wff.ex x p) (Wff.ex y q) :=
  neg (.all (neg h))

end AlphaWff

/-- A finite support is fresh for every genuinely renamed environment pair. -/
@[expose]
def _root_.NFChoice.DefinitionLeaves.AlphaTransport.EnvFresh
    (env : BinderEnv) (support : Finset Var) : Prop :=
  ∀ ⦃x y⦄, (x, y) ∈ env → x ≠ y → x ∉ support ∧ y ∉ support

theorem _root_.NFChoice.DefinitionLeaves.AlphaTransport.EnvFresh.mono
    {env : BinderEnv} {small large : Finset Var}
    (h : EnvFresh env large) (hsub : small ⊆ large) : EnvFresh env small :=
  by
  intro x y hxy hne
  rcases h hxy hne with ⟨hx, hy⟩
  exact ⟨fun hm => hx (hsub hm), fun hm => hy (hsub hm)⟩

theorem _root_.NFChoice.DefinitionLeaves.AlphaTransport.AlphaVar.reflOfFresh
    (env : BinderEnv) (u : Var) (h : EnvFresh env { u }) :
    AlphaVar env u u := by
  induction env with
  | nil => exact .free (by simp) (by simp)
  | cons head tail ih =>
    rcases head with ⟨x, y⟩
    have htail : EnvFresh tail { u } :=
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

mutual
  /-- Reflexive alpha certificate under externally fresh renamed binders. -/
  theorem _root_.NFChoice.DefinitionLeaves.AlphaTransport.AlphaClass.reflOfFresh
      (env : BinderEnv) (A : Class)
      (h : EnvFresh env A.vars) : AlphaClass env A A := by
    cases A with
    | cv x =>
      apply AlphaClass.cv
      apply AlphaVar.reflOfFresh env x
      exact h.mono (by simp [Class.vars])
    | cab x p =>
      apply AlphaClass.cab
      apply AlphaWff.reflOfFresh ((x, x) :: env) p
      intro a b hab hne
      rcases List.mem_cons.mp hab with hab | hab
      · cases hab
        exact (hne rfl).elim
      · have hf := h hab hne
        simp only [Class.vars, Finset.mem_insert, not_or] at hf
        exact ⟨hf.1.2, hf.2.2⟩
  /-- Reflexive formula alpha certificate under externally fresh binders. -/
  theorem _root_.NFChoice.DefinitionLeaves.AlphaTransport.AlphaWff.reflOfFresh
      (env : BinderEnv) (p : Wff) (h : EnvFresh env p.vars) :
      AlphaWff env p p := by
    cases p with
    | falsum => exact .falsum
    | imp p q =>
      apply AlphaWff.imp
      · exact AlphaWff.reflOfFresh env p (h.mono (by intro u hu; simp [Wff.vars, hu]))
      · exact AlphaWff.reflOfFresh env q (h.mono (by intro u hu; simp [Wff.vars, hu]))
    | all x p =>
      apply AlphaWff.all
      apply AlphaWff.reflOfFresh ((x, x) :: env) p
      intro a b hab hne
      rcases List.mem_cons.mp hab with hab | hab
      · cases hab
        exact (hne rfl).elim
      · have hf := h hab hne
        simp only [Wff.vars, Finset.mem_insert, not_or] at hf
        exact ⟨hf.1.2, hf.2.2⟩
    | objEq x y =>
      apply AlphaWff.objEq
      · apply AlphaVar.reflOfFresh env x
        exact h.mono (by simp [Wff.vars])
      · apply AlphaVar.reflOfFresh env y
        exact h.mono (by simp [Wff.vars])
    | objMem x y =>
      apply AlphaWff.objMem
      · apply AlphaVar.reflOfFresh env x
        exact h.mono (by simp [Wff.vars])
      · apply AlphaVar.reflOfFresh env y
        exact h.mono (by simp [Wff.vars])
    | classEq A B =>
      apply AlphaWff.classEq
      · exact AlphaClass.reflOfFresh env A (h.mono (by intro u hu; simp [Wff.vars, hu]))
      · exact AlphaClass.reflOfFresh env B (h.mono (by intro u hu; simp [Wff.vars, hu]))
    | classMem A B =>
      apply AlphaWff.classMem
      · exact AlphaClass.reflOfFresh env A (h.mono (by intro u hu; simp [Wff.vars, hu]))
      · exact AlphaClass.reflOfFresh env B (h.mono (by intro u hu; simp [Wff.vars, hu]))
end

/-- Semantic alpha transport for the Wff-definition leaves. -/
theorem _root_.NFChoice.DefinitionLeaves.AlphaTransport.valid_biimp_of_alpha
    {S : Fol.Structure LNF} {p q : Wff} (h : AlphaWff [] p q) :
    Wff.Valid S (Wff.biimp p q) :=
  by
  apply NFChoice.DefinitionLeaves.Wff.valid_biimp_of_holds_iff
  intro v
  exact h.holds_iff (valAgree_empty v)

/-- Semantic alpha transport for the class-definition leaves. -/
theorem _root_.NFChoice.DefinitionLeaves.AlphaTransport.valid_classEq_of_alpha
    {S : Fol.Structure LNF} {A B : Class}
    (h : AlphaClass [] A B) : Wff.Valid S (.classEq A B) :=
  by
  apply NFChoice.DefinitionLeaves.Class.valid_classEq_of_holds_iff
  intro v z
  exact h.holds_iff (valAgree_empty v) z


end NFChoice.DefinitionLeaves.AlphaTransport
