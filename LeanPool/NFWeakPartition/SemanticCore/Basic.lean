/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFChoiceFoundation.Basic

/-! NF weak partition development: SemanticCore.Basic. -/


public section

namespace NFChoice.SemanticCore

open NFChoice.Foundation

/-! This is a nominal semantic front end for replaying the `nf.mm` proof.
Metamath set variables are natural-number names.  A class denotes a unary
predicate on the carrier of an arbitrary membership-only first-order
structure.

The object/class distinction is retained at atomic formulas.  In particular,
object equality and membership have their ordinary first-order meanings.
Generic class equality and membership always use the standard extensional and
representative semantics, including when both arguments happen to be
set-variable classes.  Transport from those generic atoms to primitive object
atoms is therefore explicit and requires extensionality, just as `df-cleq` and
`df-clel` require at the NF boundary.
-/


abbrev Var :=
  Nat

mutual
  /-- The primitive class fragment needed before expanding defined symbols. -/
  inductive Class where
    | cv : Var → Class
    | cab : Var → Wff → Class
    deriving DecidableEq, Repr
  /-- The primitive nominal wff fragment used by the semantic replay. -/
  inductive Wff where
    | falsum : Wff
    | imp : Wff → Wff → Wff
    | all : Var → Wff → Wff
    | objEq : Var → Var → Wff
    | objMem : Var → Var → Wff
    | classEq : Class → Class → Wff
    | classMem : Class → Class → Wff
    deriving DecidableEq, Repr
end

/-! `vars` records every nominal variable name occurring in an expression, while
`fv` removes names bound by `all` and `cab`.  The compiler uses `vars` to
validate Metamath `$d` substitutions and `fv` to discharge semantic
freshness.
-/


mutual
  @[expose]
  def Class.vars : Class → Finset Var
    | .cv x => { x }
    | .cab x p => insert x p.vars
  @[expose]
  def Wff.vars : Wff → Finset Var
    | .falsum => ∅
    | .imp p q => p.vars ∪ q.vars
    | .all x p => insert x p.vars
    | .objEq x y => { x, y }
    | .objMem x y => { x, y }
    | .classEq A B => A.vars ∪ B.vars
    | .classMem A B => A.vars ∪ B.vars
end

mutual
  @[expose]
  def Class.fv : Class → Finset Var
    | .cv x => { x }
    | .cab x p => p.fv.erase x
  @[expose]
  def Wff.fv : Wff → Finset Var
    | .falsum => ∅
    | .imp p q => p.fv ∪ q.fv
    | .all x p => p.fv.erase x
    | .objEq x y => { x, y }
    | .objMem x y => { x, y }
    | .classEq A B => A.fv ∪ B.fv
    | .classMem A B => A.fv ∪ B.fv
end

mutual
  theorem Class.mem_vars_of_mem_fv (A : Class) {x : Var} (hx : x ∈ A.fv) : x ∈ A.vars :=
    by
    cases A with
    | cv y => simpa [Class.fv, Class.vars] using hx
    | cab y p =>
      have hp : x ∈ p.fv := (Finset.mem_erase.mp hx).2
      have hv := Wff.mem_vars_of_mem_fv p hp
      simp [Class.vars, hv]
  theorem Wff.mem_vars_of_mem_fv (p : Wff) {x : Var} (hx : x ∈ p.fv) : x ∈ p.vars := by
    cases p with
    | falsum => simp [Wff.fv] at hx
    | imp p q =>
      rcases Finset.mem_union.mp hx with hp | hq
      · exact Finset.mem_union_left _ (Wff.mem_vars_of_mem_fv p hp)
      · exact Finset.mem_union_right _ (Wff.mem_vars_of_mem_fv q hq)
    | all y p =>
      have hp : x ∈ p.fv := (Finset.mem_erase.mp hx).2
      simp [Wff.vars, Wff.mem_vars_of_mem_fv p hp]
    | objEq y z => simpa [Wff.fv, Wff.vars] using hx
    | objMem y z => simpa [Wff.fv, Wff.vars] using hx
    | classEq A B =>
      rcases Finset.mem_union.mp hx with hA | hB
      · exact Finset.mem_union_left _ (Class.mem_vars_of_mem_fv A hA)
      · exact Finset.mem_union_right _ (Class.mem_vars_of_mem_fv B hB)
    | classMem A B =>
      rcases Finset.mem_union.mp hx with hA | hB
      · exact Finset.mem_union_left _ (Class.mem_vars_of_mem_fv A hA)
      · exact Finset.mem_union_right _ (Class.mem_vars_of_mem_fv B hB)
end

theorem Class.fv_subset_vars (A : Class) : A.fv ⊆ A.vars := fun _ => A.mem_vars_of_mem_fv

theorem Wff.fv_subset_vars (p : Wff) : p.fv ⊆ p.vars := fun _ => p.mem_vars_of_mem_fv

theorem Wff.not_mem_fv_of_not_mem_vars (p : Wff) {x : Var} (hx : x ∉ p.vars) : x ∉ p.fv :=
  fun hxfv => hx (p.mem_vars_of_mem_fv hxfv)


/-- Update a named set-variable valuation. -/
@[expose]
def update {α : Sort _} (v : Var → α) (x : Var) (a : α) : Var → α :=
  Function.update v x a

@[simp]
theorem update_same {α : Sort _} (v : Var → α) (x : Var) (a : α) : update v x a x = a :=
  by simp [update]

@[simp]
theorem update_noteq {α : Sort _} (v : Var → α) {x y : Var} (h : y ≠ x) (a : α) :
    update v x a y = v y := by simp [update, h]

@[simp]
theorem update_overwrite {α : Sort _} (v : Var → α) (x : Var) (a b : α) :
    update (update v x a) x b = update v x b :=
  by
  funext y
  by_cases h : y = x
  · subst h
    simp
  · simp [update_noteq, h]

/-- The sole relation of an `LNF` structure, in source argument order. -/
@[expose]
def Mem (S : Fol.Structure LNF) (a b : S) : Prop :=
  S.rel_map LNFRelation.mem (DVec.cons a (DVec.cons b DVec.nil))

/-- Kernel check of the relation argument order: bounded variables `[a,b]` in the
front-end atom `0 e. 1` realize to the relation vector `[a,b]`.
-/
theorem realize_mem_argument_order (S : Fol.Structure LNF) (a b : S) :
    Fol.realize_bounded_formula (DVec.cons a (DVec.cons b DVec.nil))
        (Formula.toFlypitch (.mem 0 1 : Formula 2)) DVec.nil ↔
      Mem S a b :=
  Iff.rfl

mutual
  /-- Membership in the class denoted by a class expression. -/
  @[expose]
  def Class.Holds (S : Fol.Structure LNF) (v : Var → S) : Class → S → Prop
    | .cv x, a => Mem S a (v x)
    | .cab x p, a => Wff.Holds S (update v x a) p
  /-- Truth of a nominal wff under a named valuation. -/
  @[expose]
  def Wff.Holds (S : Fol.Structure LNF) (v : Var → S) : Wff → Prop
    | .falsum => False
    | .imp p q => Wff.Holds S v p → Wff.Holds S v q
    | .all x p => ∀ a : S, Wff.Holds S (update v x a) p
    | .objEq x y => v x = v y
    | .objMem x y => Mem S (v x) (v y)
    | .classEq A B => ∀ a : S, Class.Holds S v A a ↔ Class.Holds S v B a
    | .classMem A B =>
      ∃ a : S, (∀ z : S, Mem S z a ↔ Class.Holds S v A z) ∧ Class.Holds S v B a
end

/-- Two named valuations agree on a finite support. -/
@[expose]
def AgreesOn {α : Sort _} (s : Finset Var) (v v' : Var → α) : Prop :=
  ∀ x ∈ s, v x = v' x

mutual
  /-- A class denotation depends only on the free variables of the class. -/
  theorem Class.holds_congr_fv {S : Fol.Structure LNF} (A : Class) (v v' : Var → S)
      (h : AgreesOn A.fv v v') (a : S) : Class.Holds S v A a ↔ Class.Holds S v' A a := by
    cases A with
    | cv x =>
      simp only [Class.Holds]
      rw [h x (by simp [Class.fv])]
    | cab x p =>
      simp only [Class.Holds]
      apply Wff.holds_congr_fv p
      intro y hy
      by_cases hyx : y = x
      · subst y
        simp
      · have hv := h y (Finset.mem_erase.mpr ⟨hyx, hy⟩)
        simpa [update_noteq, hyx] using hv
  /-- A wff's truth value depends only on its free variables. -/
  theorem Wff.holds_congr_fv {S : Fol.Structure LNF} (p : Wff) (v v' : Var → S)
      (h : AgreesOn p.fv v v') : Wff.Holds S v p ↔ Wff.Holds S v' p := by
    cases p with
    | falsum => rfl
    | imp p q =>
      simp only [Wff.Holds]
      exact
        Iff.imp (Wff.holds_congr_fv p v v' (fun x hx => h x (by simp [Wff.fv, hx])))
          (Wff.holds_congr_fv q v v' (fun x hx => h x (by simp [Wff.fv, hx])))
    | all x p =>
      simp only [Wff.Holds]
      apply forall_congr'
      intro a
      apply Wff.holds_congr_fv p
      intro y hy
      by_cases hyx : y = x
      · subst y
        simp
      · have hv := h y (Finset.mem_erase.mpr ⟨hyx, hy⟩)
        simpa [update_noteq, hyx] using hv
    | objEq x y =>
      simp only [Wff.Holds]
      rw [h x (by simp [Wff.fv]), h y (by simp [Wff.fv])]
    | objMem x y =>
      simp only [Wff.Holds]
      rw [h x (by simp [Wff.fv]), h y (by simp [Wff.fv])]
    | classEq A B =>
      simp only [Wff.Holds]
      apply forall_congr'
      intro a
      have hA := Class.holds_congr_fv A v v' (fun x hx => h x (by simp [Wff.fv, hx])) a
      have hB := Class.holds_congr_fv B v v' (fun x hx => h x (by simp [Wff.fv, hx])) a
      tauto
    | classMem A B =>
      simp only [Wff.Holds]
      apply exists_congr
      intro a
      apply and_congr
      · apply forall_congr'
        intro z
        have hA := Class.holds_congr_fv A v v' (fun x hx => h x (by simp [Wff.fv, hx])) z
        tauto
      · exact Class.holds_congr_fv B v v' (fun x hx => h x (by simp [Wff.fv, hx])) a
end

/-- Updating a variable fresh for a wff cannot change its truth value. -/
theorem Wff.holds_update_fresh {S : Fol.Structure LNF} (p : Wff) (v : Var → S) {x : Var}
    (hx : x ∉ p.fv) (a : S) : Wff.Holds S (update v x a) p ↔ Wff.Holds S v p :=
  by
  apply Wff.holds_congr_fv p
  intro y hy
  have hyx : y ≠ x := by
    intro h
    subst y
    exact hx hy
  simp [update_noteq, hyx]

namespace Wff

/-- A nominal wff is valid in a fixed structure. -/
@[expose]
def Valid (S : Fol.Structure LNF) (p : Wff) : Prop :=
  ∀ v : Var → S, Holds S v p

/-- Negation in the primitive implication/falsity basis. -/
@[expose]
def neg (p : Wff) : Wff :=
  .imp p .falsum

/-- Classical conjunction in the primitive implication/falsity basis. -/
@[expose]
def conj (p q : Wff) : Wff :=
  neg (.imp p (neg q))

/-- Classical disjunction in the primitive implication/falsity basis. -/
@[expose]
def disj (p q : Wff) : Wff :=
  .imp (neg p) q

/-- Biconditional in the primitive implication/falsity basis. -/
@[expose]
def biimp (p q : Wff) : Wff :=
  conj (.imp p q) (.imp q p)

/-- Existential quantification in the primitive implication/falsity basis. -/
@[expose]
def ex (x : Var) (p : Wff) : Wff :=
  neg (.all x (neg p))

@[simp]
theorem holds_neg {S : Fol.Structure LNF} {v : Var → S} {p : Wff} :
    Holds S v (neg p) ↔ ¬Holds S v p :=
  Iff.rfl

@[simp]
theorem holds_conj {S : Fol.Structure LNF} {v : Var → S} {p q : Wff} :
    Holds S v (conj p q) ↔ Holds S v p ∧ Holds S v q :=
  by
  simp only [conj, neg, Holds]
  tauto

@[simp]
theorem holds_disj {S : Fol.Structure LNF} {v : Var → S} {p q : Wff} :
    Holds S v (disj p q) ↔ Holds S v p ∨ Holds S v q :=
  by
  simp only [disj, neg, Holds]
  tauto

@[simp]
theorem holds_biimp {S : Fol.Structure LNF} {v : Var → S} {p q : Wff} :
    Holds S v (biimp p q) ↔ (Holds S v p ↔ Holds S v q) :=
  by
  simp only [biimp, holds_conj, Holds]
  tauto

@[simp]
theorem holds_ex {S : Fol.Structure LNF} {v : Var → S} {x : Var} {p : Wff} :
    Holds S v (ex x p) ↔ ∃ a : S, Holds S (update v x a) p :=
  by
  simp only [ex, neg, Holds]
  constructor
  · intro h
    by_contra hn
    apply h
    intro a ha
    exact hn ⟨a, ha⟩
  · rintro ⟨a, ha⟩ h
    exact h a ha

/-- Semantic modus ponens for the replay checker. -/
theorem holds_mp {S : Fol.Structure LNF} {v : Var → S} {p q : Wff}
    (hpq : Holds S v (.imp p q)) (hp : Holds S v p) : Holds S v q :=
  hpq hp

/-- Global semantic modus ponens, matching source rule `ax-mp`. -/
theorem valid_mp {S : Fol.Structure LNF} {p q : Wff} (hp : Valid S p)
    (hpq : Valid S (.imp p q)) : Valid S q := fun v => holds_mp (hpq v) (hp v)

/-- The semantic form of propositional axiom `ax-1`. -/
theorem holds_ax1 {S : Fol.Structure LNF} (v : Var → S) (p q : Wff) :
    Holds S v (.imp p (.imp q p)) := by
  intro hp _
  exact hp

/-- Global semantic form of source axiom `ax-1`. -/
theorem valid_ax1 {S : Fol.Structure LNF} (p q : Wff) : Valid S (.imp p (.imp q p)) :=
  fun v => holds_ax1 v p q

/-- Generalization preserves validity, exactly matching source rule `ax-gen`. -/
theorem valid_generalization {S : Fol.Structure LNF} {p : Wff} (hp : Valid S p)
    (x : Var) : Valid S (.all x p) := by
  intro v a
  exact hp (update v x a)

/-- Semantic form of source axiom `ax-17`, using free-variable freshness. -/
theorem valid_ax17 {S : Fol.Structure LNF} (p : Wff) (x : Var) (hx : x ∉ p.fv) :
    Valid S (.imp p (.all x p)) := by
  intro v hp a
  exact (holds_update_fresh p v hx a).mpr hp

/-- The source `$d x ph` condition is stronger than the freshness ax-17 needs. -/
theorem valid_ax17_of_not_mem_vars {S : Fol.Structure LNF} (p : Wff) (x : Var)
    (hx : x ∉ p.vars) : Valid S (.imp p (.all x p)) :=
  valid_ax17 p x (p.not_mem_fv_of_not_mem_vars hx)

end Wff

/-- Extensionality of the sole membership relation of a structure. -/
@[expose]
def Extensional (S : Fol.Structure LNF) : Prop :=
  ∀ a b : S, (∀ z : S, Mem S z a ↔ Mem S z b) → a = b

/-- A set `a` represents the class `A` under valuation `v`. -/
@[expose]
def Represents (S : Fol.Structure LNF) (v : Var → S) (A : Class) (a : S) : Prop :=
  ∀ z : S, Mem S z a ↔ Class.Holds S v A z

/-- Uniform extensional equality of two class denotations. -/
@[expose]
def ExtClassEq (S : Fol.Structure LNF) (v : Var → S) (A B : Class) : Prop :=
  ∀ z : S, Class.Holds S v A z ↔ Class.Holds S v B z

/-- Uniform representative semantics for membership between two classes. -/
@[expose]
def ExtClassMem (S : Fol.Structure LNF) (v : Var → S) (A B : Class) : Prop :=
  ∃ a : S, Represents S v A a ∧ Class.Holds S v B a

/-- Under extensionality, actual equality of set variables is extensional equality. -/
theorem cv_eq_iff_extensional {S : Fol.Structure LNF} (hExt : Extensional S) (v : Var → S)
    (x y : Var) : v x = v y ↔ ExtClassEq S v (.cv x) (.cv y) :=
  by
  constructor
  · intro h
    simp [ExtClassEq, Class.Holds, h]
  · exact hExt (v x) (v y)

/-- Under extensionality, actual membership is representative class membership. -/
theorem cv_mem_iff_extensional {S : Fol.Structure LNF} (hExt : Extensional S)
    (v : Var → S) (x y : Var) : Mem S (v x) (v y) ↔ ExtClassMem S v (.cv x) (.cv y) :=
  by
  constructor
  · intro hxy
    exact ⟨v x, fun _ => Iff.rfl, hxy⟩
  · rintro ⟨a, ha, hab⟩
    have hax : a = v x := hExt a (v x) ha
    simpa only [hax, Class.Holds] using hab

/-- Generic class equality is definitionally its uniform extensional reading. -/
theorem classEq_iff_extensional {S : Fol.Structure LNF} (v : Var → S) (A B : Class) :
    Wff.Holds S v (.classEq A B) ↔ ExtClassEq S v A B := by rfl

/-- Generic class membership definitionally has representative semantics. -/
theorem classMem_iff_extensional {S : Fol.Structure LNF} (v : Var → S) (A B : Class) :
    Wff.Holds S v (.classMem A B) ↔ ExtClassMem S v A B := by rfl

/-- Explicit `df-cleq` transport from primitive equality to generic equality. -/
theorem objEq_iff_classEq {S : Fol.Structure LNF} (hExt : Extensional S) (v : Var → S)
    (x y : Var) : Wff.Holds S v (.objEq x y) ↔ Wff.Holds S v (.classEq (.cv x) (.cv y)) :=
  cv_eq_iff_extensional hExt v x y

/-- Explicit `df-clel` transport from primitive membership to generic membership. -/
theorem objMem_iff_classMem {S : Fol.Structure LNF} (hExt : Extensional S) (v : Var → S)
    (x y : Var) :
    Wff.Holds S v (.objMem x y) ↔ Wff.Holds S v (.classMem (.cv x) (.cv y)) :=
  cv_mem_iff_extensional hExt v x y

/-! The following theorem pins the nominal extensionality assumption to the exact
closed first-order sentence placed in `HailperinNF` by the foundation.
-/

theorem extensional_iff_foundation_axExt (S : Fol.Structure LNF) :
    Extensional S ↔ Fol.realize_sentence S (axiomFormula .axExt) :=
  by
  change
    Extensional S ↔
      ∀ a b : S, (∀ z : S, ¬((Mem S z a → Mem S z b) → ¬(Mem S z b → Mem S z a))) → a = b
  simp only [Extensional]
  have encodedBiimp (P Q : Prop) : (¬((P → Q) → ¬(Q → P))) ↔ (P ↔ Q) := by tauto
  constructor
  · intro h a b hab
    exact h a b (fun z => (encodedBiimp _ _).mp (hab z))
  · intro h a b hab
    exact h a b (fun z => (encodedBiimp _ _).mpr (hab z))

/-! Semantics of the three source definitions most sensitive to binding. -/


/-- The source definiens of `F/ x ph`. -/
@[expose]
def notFree (x : Var) (p : Wff) : Wff :=
  .all x (.imp p (.all x p))

/-- Semantic unfolding of source definition `df-nf`. -/
theorem df_nf_semantics {S : Fol.Structure LNF} (v : Var → S) (x : Var) (p : Wff) :
    Wff.Holds S v (notFree x p) ↔
      ∀ a : S, Wff.Holds S (update v x a) p → ∀ b : S, Wff.Holds S (update v x b) p :=
  by simp only [notFree, Wff.Holds, update_overwrite]

/-- Semantic proper substitution of set variable `y` for free `x`. -/
@[expose]
def SubstHolds (S : Fol.Structure LNF) (v : Var → S) (y x : Var) (p : Wff) : Prop :=
  Wff.Holds S (update v x (v y)) p

/-- The right-hand side of source definition `df-sb`. -/
@[expose]
def sbDefiniens (y x : Var) (p : Wff) : Wff :=
  Wff.conj (.imp (.objEq x y) p) (Wff.ex x (Wff.conj (.objEq x y) p))

/-- Semantic soundness of the unrestricted proper-substitution definition `df-sb`. -/
theorem df_sb_semantics {S : Fol.Structure LNF} (v : Var → S) (y x : Var) (p : Wff) :
    SubstHolds S v y x p ↔ Wff.Holds S v (sbDefiniens y x p) :=
  by
  simp only [SubstHolds, sbDefiniens, Wff.holds_conj, Wff.Holds, Wff.holds_ex]
  by_cases hxyVar : x = y
  · subst y
    have hself : update v x (v x) = v := by
      funext z
      by_cases hzx : z = x
      · subst z
        simp
      · simp [update_noteq, hzx]
    rw [hself]
    constructor
    · intro hp
      exact ⟨fun _ => hp, v x, rfl, by simpa [hself] using hp⟩
    · exact fun h => h.1 rfl
  · have hyxVar : y ≠ x := Ne.symm hxyVar
    constructor
    · intro hp
      constructor
      · intro hxy
        have hself : update v x (v y) = v :=
          by
          funext z
          by_cases hzx : z = x
          · subst z
            simp [hxy]
          · simp [update_noteq, hzx]
        simpa [hself] using hp
      · refine ⟨v y, ?_, hp⟩
        simp [update_noteq, hyxVar]
    · rintro ⟨_, a, hay, hp⟩
      have hay' : a = v y := by simpa [update_noteq, hyxVar] using hay
      subst a
      exact hp

/-- Semantic right-hand side of `[ x / y ] ph`. -/
@[expose]
def CvSubstHolds (S : Fol.Structure LNF) (v : Var → S) (x y : Var) (p : Wff) : Prop :=
  Wff.Holds S (update v y (v x)) p

/-- `df-clab`: membership of a set variable in an abstraction is proper substitution. -/
theorem df_clab_semantics {S : Fol.Structure LNF} (hExt : Extensional S) (v : Var → S)
    (x y : Var) (p : Wff) :
    Wff.Holds S v (.classMem (.cv x) (.cab y p)) ↔ CvSubstHolds S v x y p :=
  by
  simp only [Wff.Holds, Class.Holds, CvSubstHolds]
  constructor
  · rintro ⟨a, ha, hp⟩
    have hax : a = v x := hExt a (v x) ha
    simpa [hax] using hp
  · intro hp
    exact ⟨v x, fun _ => Iff.rfl, hp⟩

end NFChoice.SemanticCore
