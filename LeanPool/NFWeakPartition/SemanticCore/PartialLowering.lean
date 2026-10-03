/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.SemanticCore.Lowering

/-! NF weak partition development: SemanticCore.PartialLowering. -/


public section

namespace NFChoice.SemanticCore.PartialLowering

open NFChoice.Foundation
open NFChoice.SemanticCore.Lowering

/-- Shift every mapped variable under a new de Bruijn binder. -/
@[expose]
def liftRho? {n : Nat} (rho : Var → Option (Fin n)) : Var → Option (Fin (n + 1)) :=
  fun x => (rho x).map Fin.succ

/-- Shift the old mappings and bind `x` at de Bruijn index zero. -/
@[expose]
def bindRho? {n : Nat} (rho : Var → Option (Fin n)) (x : Var) :
    Var → Option (Fin (n + 1)) :=
  Function.update (liftRho? rho) x (some 0)

mutual
  /-- Partial class-predicate lowering; failure means an unmapped free name. -/
  @[expose]
  def lowerClassPred? {n : Nat} (rho : Var → Option (Fin n)) (candidate : Fin n) :
      Class → Option (Formula n)
    | .cv x => do
      let i ← rho x
      pure (.mem candidate i)
    | .cab x p => lowerWff? (Function.update rho x (some candidate)) p
  /-- Partial nominal lowering, usable at depth zero with the empty environment. -/
  @[expose]
  def lowerWff? {n : Nat} (rho : Var → Option (Fin n)) : Wff → Option (Formula n)
    | .falsum => some .falsum
    | .imp p q => do
      let p' ← lowerWff? rho p
      let q' ← lowerWff? rho q
      pure (.imp p' q')
    | .all x p => do
      let p' ← lowerWff? (bindRho? rho x) p
      pure (.all p')
    | .objEq x y => do
      let x' ← rho x
      let y' ← rho y
      pure (.equal x' y')
    | .objMem x y => do
      let x' ← rho x
      let y' ← rho y
      pure (.mem x' y')
    | .classEq A B => do
      let A' ← lowerClassPred? (liftRho? rho) 0 A
      let B' ← lowerClassPred? (liftRho? rho) 0 B
      pure (.all (Formula.biimp A' B'))
    | .classMem A B => do
      let A' ← lowerClassPred? (liftRho? (liftRho? rho)) 0 A
      let B' ← lowerClassPred? (liftRho? rho) 0 B
      pure (Formula.ex (Formula.conj (.all (Formula.biimp (.mem 0 1) A')) B'))
end

/-- The partial environment supplies the values of all names in `support`. -/
@[expose]
def MappedAgreement {S : Type _} {n : Nat} (rho : Var → Option (Fin n)) (xs : DVec S n)
    (v : Var → S) (support : Finset Var) : Prop :=
  ∀ x ∈ support, ∃ i : Fin n, rho x = some i ∧ lookup xs i = v x

/-- An empty partial environment, available even at de Bruijn depth zero. -/
@[expose]
def emptyRho : Var → Option (Fin 0) := fun _ => none

/-- Lower a closed nominal wff directly to a sentence. -/
@[expose]
def lowerClosed (p : Wff) : Option Sentence :=
  lowerWff? emptyRho p

/-- Universally close the listed nominal names, in list order. -/
@[expose]
def closeNames : List Var → Wff → Wff
  | [], p => p
  | x :: xs, p => .all x (closeNames xs p)

/-- Assign every listed name its value in a target valuation. -/
@[expose]
def assignNames {S : Type _} : List Var → (Var → S) → (Var → S) → Var → S
  | [], base, _target => base
  | x :: xs, base, target => assignNames xs (update base x (target x)) target

theorem assignNames_eq_of_not_mem {S : Type _} (names : List Var) (base target : Var → S)
    {x : Var} (hx : x ∉ names) : assignNames names base target x = base x := by
  induction names generalizing base with
  | nil => rfl
  | cons y ys
    ih =>
    have hxy : x ≠ y := by
      intro h
      subst y
      exact hx (by simp)
    rw [assignNames]
    have hxys : x ∉ ys := fun hmem => hx (List.mem_cons_of_mem y hmem)
    rw [ih (update base y (target y)) hxys]
    simp [update_noteq, hxy]

theorem assignNames_eq_of_mem {S : Type _} (names : List Var) (base target : Var → S)
    {x : Var} (hx : x ∈ names) : assignNames names base target x = target x := by
  induction names generalizing base with
  | nil => simp at hx
  | cons y ys ih =>
    rw [assignNames]
    rcases List.mem_cons.mp hx with hxy | hxs
    · subst y
      by_cases htail : x ∈ ys
      · exact ih (update base x (target x)) htail
      · rw [assignNames_eq_of_not_mem ys (update base x (target x)) target htail]
        simp
    · exact ih (update base y (target y)) hxs

/-- Specialize a nominal universal closure at a target valuation. -/
theorem holds_closeNames_assign {S : Fol.Structure LNF} (names : List Var) (p : Wff)
    (base target : Var → S) (h : Wff.Holds S base (closeNames names p)) :
    Wff.Holds S (assignNames names base target) p := by
  induction names generalizing base with
  | nil => exact h
  | cons x xs ih =>
    apply ih (update base x (target x))
    exact h (target x)

/-- Truth of a universal nominal closure yields global validity of its open body,
provided the list covers all free names.
-/
theorem valid_of_holds_closeNames {S : Fol.Structure LNF} (names : List Var) (p : Wff)
    (base : Var → S) (hcover : p.fv ⊆ names.toFinset)
    (h : Wff.Holds S base (closeNames names p)) : Wff.Valid S p :=
  by
  intro target
  have ha := holds_closeNames_assign names p base target h
  exact
    (Wff.holds_congr_fv p (assignNames names base target) target (fun x hx =>
            assignNames_eq_of_mem names base target (List.mem_toFinset.mp (hcover hx)))).mp
      ha

/-- A valid universal nominal closure yields validity of its open body. -/
theorem valid_of_valid_closeNames {S : Fol.Structure LNF} (names : List Var) (p : Wff)
    (hcover : p.fv ⊆ names.toFinset) (h : Wff.Valid S (closeNames names p)) :
    Wff.Valid S p := by
  intro target
  exact valid_of_holds_closeNames names p target hcover (h target) target

theorem fv_closeNames (names : List Var) (p : Wff) :
    (closeNames names p).fv = p.fv \ names.toFinset := by
  induction names with
  | nil => simp [closeNames]
  | cons x xs ih =>
    rw [closeNames, Wff.fv, ih]
    ext y
    simp [and_left_comm]

theorem MappedAgreement.mono {S : Type _} {n : Nat} {rho : Var → Option (Fin n)}
    {xs : DVec S n} {v : Var → S} {s t : Finset Var} (h : MappedAgreement rho xs v t)
    (hst : s ⊆ t) : MappedAgreement rho xs v s := fun x hx => h x (hst hx)

theorem mappedAgreement_update {S : Type _} {n : Nat} (rho : Var → Option (Fin n))
    (xs : DVec S n) (v : Var → S) (x : Var) (candidate : Fin n) (p : Wff)
    (h : MappedAgreement rho xs v (p.fv.erase x)) :
    MappedAgreement (Function.update rho x (some candidate)) xs
      (update v x (lookup xs candidate)) p.fv :=
  by
  intro y hy
  by_cases hyx : y = x
  · subst y
    exact ⟨candidate, by simp, by simp⟩
  · rcases h y (Finset.mem_erase.mpr ⟨hyx, hy⟩) with ⟨i, hi, hv⟩
    exact ⟨i, by simpa [Function.update, hyx] using hi, by simpa [update, hyx] using hv⟩

theorem mappedAgreement_bind {S : Type _} {n : Nat} (rho : Var → Option (Fin n))
    (xs : DVec S n) (v : Var → S) (x : Var) (a : S) (p : Wff)
    (h : MappedAgreement rho xs v (p.fv.erase x)) :
    MappedAgreement (bindRho? rho x) (DVec.cons a xs) (update v x a) p.fv :=
  by
  intro y hy
  by_cases hyx : y = x
  · subst y
    exact ⟨0, by simp [bindRho?], by simp⟩
  · rcases h y (Finset.mem_erase.mpr ⟨hyx, hy⟩) with ⟨i, hi, hv⟩
    refine ⟨Fin.succ i, ?_, ?_⟩
    · simp [bindRho?, liftRho?, Function.update, hyx, hi]
    · simpa [update, hyx] using hv

theorem mappedAgreement_lift {S : Type _} {n : Nat} (rho : Var → Option (Fin n))
    (xs : DVec S n) (v : Var → S) (s : Finset Var) (a : S)
    (h : MappedAgreement rho xs v s) :
    MappedAgreement (liftRho? rho) (DVec.cons a xs) v s :=
  by
  intro x hx
  rcases h x hx with ⟨i, hi, hv⟩
  exact ⟨Fin.succ i, by simp [liftRho?, hi], by simpa using hv⟩

mutual
  /-- Soundness of successful partial class-predicate lowering. -/
  theorem lowerClassPred?_sound {S : Fol.Structure LNF} {n : Nat}
      (rho : Var → Option (Fin n)) (xs : DVec S n) (v : Var → S) (candidate : Fin n)
      (A : Class) (f : Formula n) (hlower : lowerClassPred? rho candidate A = some f)
      (hmap : MappedAgreement rho xs v A.fv) :
      Class.Holds S v A (lookup xs candidate) ↔ FormulaHolds S xs f := by
    cases A with
    | cv x =>
      rcases hmap x (by simp [Class.fv]) with ⟨i, hi, hv⟩
      simp [lowerClassPred?, hi] at hlower
      subst f
      simp [Class.Holds, FormulaHolds, hv]
    | cab x
      p =>
      apply
        lowerWff?_sound (Function.update rho x (some candidate)) xs
          (update v x (lookup xs candidate)) p f hlower
      exact mappedAgreement_update rho xs v x candidate p hmap
  /-- Soundness of every successful partial nominal-wff lowering. -/
  theorem lowerWff?_sound {S : Fol.Structure LNF} {n : Nat} (rho : Var → Option (Fin n))
      (xs : DVec S n) (v : Var → S) (p : Wff) (f : Formula n)
      (hlower : lowerWff? rho p = some f) (hmap : MappedAgreement rho xs v p.fv) :
      Wff.Holds S v p ↔ FormulaHolds S xs f := by
    cases p with
    | falsum =>
      simp [lowerWff?] at hlower
      subst f
      rfl
    | imp p q =>
      cases hp : lowerWff? rho p with
      | none => simp [lowerWff?, hp] at hlower
      | some p' =>
        cases hq : lowerWff? rho q with
        | none => simp [lowerWff?, hp, hq] at hlower
        | some
          q' =>
          simp only [lowerWff?, hp, hq, Option.pure_def, Option.bind_eq_bind,
            Option.bind_some, Option.some.injEq] at hlower
          subst f
          simp only [Wff.Holds, FormulaHolds]
          exact
            Iff.imp
              (lowerWff?_sound rho xs v p p' hp (hmap.mono (by intro x hx; simp [Wff.fv, hx])))
              (lowerWff?_sound rho xs v q q' hq (hmap.mono (by intro x hx; simp [Wff.fv, hx])))
    | all x p =>
      cases hp : lowerWff? (bindRho? rho x) p with
      | none => simp [lowerWff?, hp] at hlower
      | some
        p' =>
        simp only [lowerWff?, hp, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
          Option.some.injEq] at hlower
        subst f
        simp only [Wff.Holds, FormulaHolds]
        apply forall_congr'
        intro a
        apply lowerWff?_sound (bindRho? rho x) (DVec.cons a xs) (update v x a) p p' hp
        exact mappedAgreement_bind rho xs v x a p hmap
    | objEq x y =>
      rcases hmap x (by simp [Wff.fv]) with ⟨i, hi, hvx⟩
      rcases hmap y (by simp [Wff.fv]) with ⟨j, hj, hvy⟩
      simp [lowerWff?, hi, hj] at hlower
      subst f
      simp [Wff.Holds, FormulaHolds, hvx, hvy]
    | objMem x y =>
      rcases hmap x (by simp [Wff.fv]) with ⟨i, hi, hvx⟩
      rcases hmap y (by simp [Wff.fv]) with ⟨j, hj, hvy⟩
      simp [lowerWff?, hi, hj] at hlower
      subst f
      simp [Wff.Holds, FormulaHolds, hvx, hvy]
    | classEq A B =>
      cases hA : lowerClassPred? (liftRho? rho) 0 A with
      | none => simp [lowerWff?, hA] at hlower
      | some A' =>
        cases hB : lowerClassPred? (liftRho? rho) 0 B with
        | none => simp [lowerWff?, hA, hB] at hlower
        | some
          B' =>
          simp only [lowerWff?, hA, hB, Option.pure_def, Option.bind_eq_bind,
            Option.bind_some, Option.some.injEq] at hlower
          subst f
          simp only [Wff.Holds, FormulaHolds, formulaHolds_biimp]
          apply forall_congr'
          intro a
          have hmA : MappedAgreement rho xs v A.fv :=
            hmap.mono (by intro x hx; simp [Wff.fv, hx])
          have hmB : MappedAgreement rho xs v B.fv :=
            hmap.mono (by intro x hx; simp [Wff.fv, hx])
          have hsA :=
            lowerClassPred?_sound (liftRho? rho) (DVec.cons a xs) v 0 A A' hA
              (mappedAgreement_lift rho xs v A.fv a hmA)
          have hsB :=
            lowerClassPred?_sound (liftRho? rho) (DVec.cons a xs) v 0 B B' hB
              (mappedAgreement_lift rho xs v B.fv a hmB)
          simp only [lookup_cons_zero] at hsA hsB
          tauto
    | classMem A B =>
      cases hA : lowerClassPred? (liftRho? (liftRho? rho)) 0 A with
      | none => simp [lowerWff?, hA] at hlower
      | some A' =>
        cases hB : lowerClassPred? (liftRho? rho) 0 B with
        | none => simp [lowerWff?, hA, hB] at hlower
        | some
          B' =>
          simp only [lowerWff?, hA, hB, Option.pure_def, Option.bind_eq_bind,
            Option.bind_some, Option.some.injEq] at hlower
          subst f
          simp only [Wff.Holds, formulaHolds_ex, formulaHolds_conj, FormulaHolds,
            formulaHolds_biimp]
          apply exists_congr
          intro a
          apply and_congr
          · apply forall_congr'
            intro z
            have hmA : MappedAgreement rho xs v A.fv :=
              hmap.mono (by intro x hx; simp [Wff.fv, hx])
            have hmA' := mappedAgreement_lift rho xs v A.fv a hmA
            have hsA :=
              lowerClassPred?_sound (liftRho? (liftRho? rho))
                (DVec.cons z (DVec.cons a xs)) v 0 A A' hA
                (mappedAgreement_lift (liftRho? rho) (DVec.cons a xs) v A.fv z hmA')
            simp only [lookup_cons_zero] at hsA
            tauto
          · have hmB : MappedAgreement rho xs v B.fv :=
              hmap.mono (by intro x hx; simp [Wff.fv, hx])
            have hsB :=
              lowerClassPred?_sound (liftRho? rho) (DVec.cons a xs) v 0 B B' hB
                (mappedAgreement_lift rho xs v B.fv a hmB)
            simpa using hsB
end

/-- A successful closed lowering has exactly the nominal closed semantics. -/
theorem lowerClosed_sound {S : Fol.Structure LNF} (p : Wff) (f : Sentence)
    (hpClosed : p.fv = ∅) (hlower : lowerClosed p = some f) (v : Var → S) :
    Wff.Holds S v p ↔ FormulaHolds S DVec.nil f :=
  by
  apply lowerWff?_sound emptyRho DVec.nil v p f hlower
  intro x hx
  rw [hpClosed] at hx
  simp at hx

/-- Closed nominal lowering reaches the exact Flypitch sentence semantics. -/
theorem lowerClosed_realize_iff {S : Fol.Structure LNF} (p : Wff) (f : Sentence)
    (hpClosed : p.fv = ∅) (hlower : lowerClosed p = some f) (v : Var → S) :
    Wff.Holds S v p ↔ Fol.realize_sentence S (Formula.toFlypitch f) :=
  (lowerClosed_sound p f hpClosed hlower v).trans (formulaHolds_toFlypitch DVec.nil f)

/-- Any realized closed lowering is globally valid in the nominal evaluator. -/
theorem valid_of_lowerClosed_realize {S : Fol.Structure LNF} (p : Wff) (f : Sentence)
    (hpClosed : p.fv = ∅) (hlower : lowerClosed p = some f)
    (hrealize : Fol.realize_sentence S (Formula.toFlypitch f)) : Wff.Valid S p :=
  by
  intro v
  exact (lowerClosed_realize_iff p f hpClosed hlower v).mpr hrealize

/-- Generic NF-leaf bridge.  The compiler supplies only a reduction-checkable
lowering equation for the source schema's universal closure; the theorem
turns realization of that exact literal sentence into validity of the open
nominal schema.
-/
theorem valid_open_of_closed_lowering {S : Fol.Structure LNF} (names : List Var) (p : Wff)
    (f : Sentence) (hcover : p.fv ⊆ names.toFinset)
    (hlower : lowerClosed (closeNames names p) = some f)
    (hrealize : Fol.realize_sentence S (Formula.toFlypitch f)) : Wff.Valid S p :=
  by
  apply valid_of_valid_closeNames names p hcover
  apply valid_of_lowerClosed_realize (closeNames names p) f
  · rw [fv_closeNames]
    exact Finset.sdiff_eq_empty_iff_subset.mpr hcover
  · exact hlower
  · exact hrealize

end NFChoice.SemanticCore.PartialLowering
