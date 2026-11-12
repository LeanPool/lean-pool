/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.OrderWalk
public import LeanPool.DescriptiveCounting.Problems.HornSat.Unsat
import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Lattice
import all LeanPool.DescriptiveCounting.Problems.HornSat.Unsat

/-!
# HORN-SAT is SO-Horn definable

`HORNSAT ∈ PTIME` (`DescriptiveComplexity.hornSat_mem_PTIME`): Horn satisfiability is
itself definable in the Horn fragment, which with the discharge of
`DescriptiveComplexity.Problems.HornSat.Hardness` makes HORN-SAT **PTIME-complete**
(`DescriptiveComplexity.HORNSAT_PTIME_complete`).

The obstacle, and what the order is for: a clause of the *input* has an
unbounded number of negative literals, so the rule “if all negative literals
of `c` are forced then its positive literal is forced” is not a Horn clause –
its body would have unboundedly many atoms. The standard fix walks the
literals of a clause along the order. The program guesses

* `T x`, the set of variables forced true by unit propagation, and
* `B c z`, meaning “every negative literal of `c` up to `z` is in `T`”,

and derives `B` by four rules following the order (base case at the minimum,
step case along the successor relation, each split on whether the current
element is a negative literal of `c`), so that `B c max` *is* the unbounded
conjunction, assembled one element at a time. One further rule derives `T`
from a clause whose body is complete, and two goal clauses reject the two ways
of failing: a clause with no positive literal whose body is complete, and a
clause with two distinct positive literals (the Horn condition itself, which
`DescriptiveComplexity.HORNSAT` folds into its yes-instances).

All the order-dependent predicates – being minimal or maximal, being the
immediate successor – are first-order over `Language.sat.sum Language.order`
(the shared guards of `DescriptiveComplexity.OrderWalk`),
and appear only in *guards*, where arbitrary first-order formulas are allowed.
The second-order atoms are `T` and `B` only, one or two per clause body: the
program is Horn.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The Horn program -/

section Program

/-- The block of the SO-Horn definition of HORN-SAT: a unary relation variable
`T` (the variables forced true) and a binary one `B` (`B c z`: every negative
literal of the clause `c` up to `z` is forced). -/
def hsBlock : SOBlock where
  ι := Bool
  arity := fun i => cond i 1 2

/-- The atom `T xᵢ`. -/
def tAt (i : Fin 4) : SOAtom hsBlock 4 := ⟨true, ![i]⟩

/-- The atom `B (xᵢ, xⱼ)`. -/
def bAt (i j : Fin 4) : SOAtom hsBlock 4 := ⟨false, ![i, j]⟩

/-- The “is a clause” symbol over the ordered expansion. -/
abbrev sIsClSym : (Language.sat.sum Language.order).Relations 1 := Sum.inl satIsClause

/-- The positive-occurrence symbol over the ordered expansion. -/
abbrev sPosSym : (Language.sat.sum Language.order).Relations 2 := Sum.inl satPosIn

/-- The negative-occurrence symbol over the ordered expansion. -/
abbrev sNegSym : (Language.sat.sum Language.order).Relations 2 := Sum.inl satNegIn

/-- The guard `isClause xᵢ`. -/
noncomputable def isClG (i : Fin 4) : (Language.sat.sum Language.order).Formula (Fin 4) :=
  Relations.formula₁ sIsClSym (Term.var i)

/-- The guard `posIn (xᵢ, xⱼ)`. -/
noncomputable def posG (i j : Fin 4) : (Language.sat.sum Language.order).Formula (Fin 4) :=
  Relations.formula₂ sPosSym (Term.var i) (Term.var j)

/-- The guard `negIn (xᵢ, xⱼ)`. -/
noncomputable def negG (i j : Fin 4) : (Language.sat.sum Language.order).Formula (Fin 4) :=
  Relations.formula₂ sNegSym (Term.var i) (Term.var j)

/-- The guard “the clause `xᵢ` has no positive literal”. -/
noncomputable def noPosG (i : Fin 4) : (Language.sat.sum Language.order).Formula (Fin 4) :=
  fo%[i] ∀ y, ¬ sPosSym(i, y)

/-- The guard `xᵢ ≠ xⱼ`. -/
noncomputable def neqG (i j : Fin 4) : (Language.sat.sum Language.order).Formula (Fin 4) :=
  ∼(Term.equal (Term.var i) (Term.var j))

section Realize

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] {v : Fin 4 → A}

@[simp]
theorem realize_isClG (i : Fin 4) : (isClG i).Realize v ↔ RelMap satIsClause ![v i] := by
  rw [isClG, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_posG (i j : Fin 4) :
    (posG i j).Realize v ↔ RelMap satPosIn ![v i, v j] := by
  rw [posG, Formula.realize_rel₂, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_negG (i j : Fin 4) :
    (negG i j).Realize v ↔ RelMap satNegIn ![v i, v j] := by
  rw [negG, Formula.realize_rel₂, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_noPosG (i : Fin 4) :
    (noPosG i).Realize v ↔ ∀ a : A, ¬RelMap satPosIn ![v i, a] := by
  rw [noPosG]
  simp only [Formula.realize_iAlls, Formula.realize_not, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr, relMap_sumInl]
  exact ⟨fun h a => h fun _ => a, fun h k => h (k 0)⟩

@[simp]
theorem realize_neqG (i j : Fin 4) : (neqG i j).Realize v ↔ v i ≠ v j := by
  rw [neqG, Formula.realize_not, Formula.realize_equal, Term.realize_var, Term.realize_var]

end Realize

/-- Base rule: at the minimum, a non-literal position starts a complete
body. -/
noncomputable def hsC1 : HornClause (Language.sat.sum Language.order) hsBlock 4 :=
  { guard := minF 1 ⊓ ∼(negG 0 1), body := [], head := some (bAt 0 1) }

/-- Base rule: at the minimum, a negative literal must be forced. -/
noncomputable def hsC2 : HornClause (Language.sat.sum Language.order) hsBlock 4 :=
  { guard := minF 1 ⊓ negG 0 1, body := [tAt 1], head := some (bAt 0 1) }

/-- Step rule at a non-literal position. -/
noncomputable def hsC3 : HornClause (Language.sat.sum Language.order) hsBlock 4 :=
  { guard := succF 2 1 ⊓ ∼(negG 0 1), body := [bAt 0 2], head := some (bAt 0 1) }

/-- Step rule at a negative literal, which must be forced. -/
noncomputable def hsC4 : HornClause (Language.sat.sum Language.order) hsBlock 4 :=
  { guard := succF 2 1 ⊓ negG 0 1, body := [bAt 0 2, tAt 1], head := some (bAt 0 1) }

/-- Propagation: a clause whose body is complete forces its positive
literal. -/
noncomputable def hsC5 : HornClause (Language.sat.sum Language.order) hsBlock 4 :=
  { guard := isClG 0 ⊓ posG 0 1 ⊓ maxF 3, body := [bAt 0 3], head := some (tAt 1) }

/-- Goal clause: a clause with a complete body and no positive literal is
falsified. -/
noncomputable def hsG1 : HornClause (Language.sat.sum Language.order) hsBlock 4 :=
  { guard := isClG 0 ⊓ maxF 3 ⊓ noPosG 0, body := [bAt 0 3], head := none }

/-- Goal clause: two distinct positive literals in a clause violate the Horn
condition, which `DescriptiveComplexity.HORNSAT` folds into its yes-instances. -/
noncomputable def hsG2 : HornClause (Language.sat.sum Language.order) hsBlock 4 :=
  { guard := isClG 0 ⊓ posG 0 1 ⊓ posG 0 2 ⊓ neqG 1 2, body := [], head := none }

/-- The Horn program defining HORN-SAT. -/
noncomputable def hsProgram : HornProgram (Language.sat.sum Language.order) hsBlock 4 :=
  [hsC1, hsC2, hsC3, hsC4, hsC5, hsG1, hsG2]

section AtomHolds

variable {A : Type} [Language.sat.Structure A] (ρ : hsBlock.Assignment A) (v : Fin 4 → A)

omit [Language.sat.Structure A] in
theorem tAt_holds (i : Fin 4) : (tAt i).Holds ρ v ↔ ρ true ![v i] := by
  refine iff_of_eq (congrArg (ρ true) (funext fun l => ?_))
  fin_cases l
  rfl

omit [Language.sat.Structure A] in
theorem bAt_holds (i j : Fin 4) : (bAt i j).Holds ρ v ↔ ρ false ![v i, v j] := by
  refine iff_of_eq (congrArg (ρ false) (funext fun l => ?_))
  fin_cases l <;> rfl

end AtomHolds

/-! ### Correctness -/

section Correctness

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- The intended interpretation of the variable `B`: every negative literal of
the clause `c` up to `z` is forced. -/
private def BodyUpTo (c z : A) : Prop :=
  ∀ y : A, y ≤ z → RelMap satNegIn ![c, y] → Forced y

variable (A) in
/-- The canonical assignment: the propagation closure and its partial
bodies. -/
private noncomputable def hsAssign : hsBlock.Assignment A :=
  fun i => match i with
    | true => fun w : Fin 1 → A => Forced (w 0)
    | false => fun w : Fin 2 → A => BodyUpTo (w 0) (w 1)

omit [Finite A] [Nonempty A] in
/-- A complete body at a maximum means that all negative literals are
forced. -/
private theorem allNeg_of_bodyUpTo_max {c m : A} (hm : ∀ a : A, a ≤ m) (h : BodyUpTo c m)
    (y : A) (hy : RelMap satNegIn ![c, y]) : Forced y :=
  h y (hm y) hy

/-- **HORN-SAT is SO-Horn definable.** The guessed relations are the
propagation closure and its partial bodies; the order assembles the unbounded
body of a clause one element at a time. -/
theorem hornSat_sigmaSOHornDefinable : SigmaSOHornDefinable HORNSAT := by
  refine ⟨hsBlock, 4, hsProgram, ?_⟩
  intro A _ _ _ _
  constructor
  · rintro ⟨hhorn, ν, hν⟩
    refine ⟨hsAssign A, ?_⟩
    intro v c hc
    simp only [hsProgram, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rintro ⟨hg, -⟩
      simp only [hsC1, Formula.realize_inf, Formula.realize_not, realize_minF,
        realize_negG] at hg
      refine (bAt_holds (hsAssign A) v 0 1).mpr fun y hy hny => ?_
      have hy' : y ≤ v 1 := hy
      have hny' : RelMap satNegIn ![v 0, y] := hny
      have heq : y = v 1 := le_antisymm hy' (hg.1 y)
      subst heq
      exact absurd hny' hg.2
    · rintro ⟨hg, hb⟩
      simp only [hsC2, Formula.realize_inf, realize_minF, realize_negG] at hg
      have ht := (tAt_holds (hsAssign A) v 1).mp (hb _ (by simp [hsC2]))
      refine (bAt_holds (hsAssign A) v 0 1).mpr fun y hy _ => ?_
      exact le_antisymm hy (hg.1 y) ▸ ht
    · rintro ⟨hg, hb⟩
      simp only [hsC3, Formula.realize_inf, Formula.realize_not, realize_succF,
        realize_negG] at hg
      have hbw := (bAt_holds (hsAssign A) v 0 2).mp (hb _ (by simp [hsC3]))
      refine (bAt_holds (hsAssign A) v 0 1).mpr fun y hy hny => ?_
      rcases lt_or_ge y (v 1) with hlt | hge
      · rcases le_or_gt y (v 2) with hle | hgt
        · exact hbw y hle hny
        · exact absurd ⟨hgt, hlt⟩ (hg.1.2 y)
      · have hy' : y ≤ v 1 := hy
        have hny' : RelMap satNegIn ![v 0, y] := hny
        have heq : y = v 1 := le_antisymm hy' hge
        subst heq
        exact absurd hny' hg.2
    · rintro ⟨hg, hb⟩
      simp only [hsC4, Formula.realize_inf, realize_succF, realize_negG] at hg
      have hbw := (bAt_holds (hsAssign A) v 0 2).mp (hb _ (by simp [hsC4]))
      have ht := (tAt_holds (hsAssign A) v 1).mp (hb _ (by simp [hsC4]))
      refine (bAt_holds (hsAssign A) v 0 1).mpr fun y hy hny => ?_
      rcases lt_or_ge y (v 1) with hlt | hge
      · rcases le_or_gt y (v 2) with hle | hgt
        · exact hbw y hle hny
        · exact absurd ⟨hgt, hlt⟩ (hg.1.2 y)
      · have hy' : y ≤ v 1 := hy
        have heq : y = v 1 := le_antisymm hy' hge
        subst heq
        exact ht
    · rintro ⟨hg, hb⟩
      simp only [hsC5, Formula.realize_inf, realize_isClG, realize_posG, realize_maxF] at hg
      have hbm := (bAt_holds (hsAssign A) v 0 3).mp (hb _ (by simp [hsC5]))
      exact (tAt_holds (hsAssign A) v 1).mpr
        (forced_of_allNeg hg.1.1 hg.1.2 (allNeg_of_bodyUpTo_max hg.2 hbm))
    · rintro ⟨hg, hb⟩
      simp only [hsG1, Formula.realize_inf, realize_isClG, realize_maxF, realize_noPosG] at hg
      have hbm := (bAt_holds (hsAssign A) v 0 3).mp (hb _ (by simp [hsG1]))
      obtain ⟨z, hz⟩ := hν (v 0) hg.1.1
      rcases hz with ⟨hpz, -⟩ | ⟨hnz, hνz⟩
      · exact hg.2 z hpz
      · exact hνz (forced_subset_model hhorn hν z
          (allNeg_of_bodyUpTo_max hg.1.2 hbm z hnz))
    · rintro ⟨hg, -⟩
      simp only [hsG2, Formula.realize_inf, realize_isClG, realize_posG, realize_neqG] at hg
      exact hg.2 (hhorn (v 0) (v 1) (v 2) hg.1.1.1 hg.1.1.2 hg.1.2)
  · rintro ⟨ρ, hρ⟩
    obtain ⟨m, hm⟩ : ∃ m : A, ∀ a : A, a ≤ m := Finite.exists_max (id : A → A)
    -- the Horn condition, from the second goal clause
    have hhorn : AtMostOnePositive A := by
      intro c x y hc hx hy
      by_contra hne
      exact hρ ![c, x, y, m] hsG2 (by simp [hsProgram]) ⟨by
        simp only [hsG2, Formula.realize_inf, realize_isClG, realize_posG, realize_neqG]
        exact ⟨⟨⟨by simpa using hc, by simpa using hx⟩, by simpa using hy⟩, by simpa using hne⟩,
        by simp [hsG2]⟩
    refine ⟨hhorn, fun x => ρ true ![x], fun c hc => ?_⟩
    by_cases hall : ∀ y : A, RelMap satNegIn ![c, y] → ρ true ![y]
    · -- the body of `c` is complete, so `B c z` holds all along the order
      have hB : ∀ z : A, ρ false ![c, z] := by
        refine order_induction (fun z hz => ?_) (fun w z hwz hnb ih => ?_)
        · by_cases hn : RelMap satNegIn ![c, z]
          · refine (bAt_holds ρ ![c, z, z, m] 0 1).mp
              (hρ ![c, z, z, m] hsC2 (by simp [hsProgram]) ⟨?_, ?_⟩)
            · simp only [hsC2, Formula.realize_inf, realize_minF, realize_negG]
              exact ⟨by simpa using hz, by simpa using hn⟩
            · intro a ha
              simp only [hsC2, List.mem_singleton] at ha
              subst ha
              exact (tAt_holds ρ ![c, z, z, m] 1).mpr (by simpa using hall z hn)
          · refine (bAt_holds ρ ![c, z, z, m] 0 1).mp
              (hρ ![c, z, z, m] hsC1 (by simp [hsProgram]) ⟨?_, by simp [hsC1]⟩)
            simp only [hsC1, Formula.realize_inf, Formula.realize_not, realize_minF,
              realize_negG]
            exact ⟨by simpa using hz, by simpa using hn⟩
        · by_cases hn : RelMap satNegIn ![c, z]
          · refine (bAt_holds ρ ![c, z, w, m] 0 1).mp
              (hρ ![c, z, w, m] hsC4 (by simp [hsProgram]) ⟨?_, ?_⟩)
            · simp only [hsC4, Formula.realize_inf, realize_succF, realize_negG]
              exact ⟨⟨by simpa using hwz, by simpa using hnb⟩, by simpa using hn⟩
            · intro a ha
              simp only [hsC4, List.mem_cons, List.not_mem_nil, or_false] at ha
              rcases ha with rfl | rfl
              · exact (bAt_holds ρ ![c, z, w, m] 0 2).mpr (by simpa using ih)
              · exact (tAt_holds ρ ![c, z, w, m] 1).mpr (by simpa using hall z hn)
          · refine (bAt_holds ρ ![c, z, w, m] 0 1).mp
              (hρ ![c, z, w, m] hsC3 (by simp [hsProgram]) ⟨?_, ?_⟩)
            · simp only [hsC3, Formula.realize_inf, Formula.realize_not, realize_succF,
                realize_negG]
              exact ⟨⟨by simpa using hwz, by simpa using hnb⟩, by simpa using hn⟩
            · intro a ha
              simp only [hsC3, List.mem_singleton] at ha
              subst ha
              exact (bAt_holds ρ ![c, z, w, m] 0 2).mpr (by simpa using ih)
      by_cases hpos : ∃ x : A, RelMap satPosIn ![c, x]
      · obtain ⟨x, hx⟩ := hpos
        refine ⟨x, Or.inl ⟨hx, ?_⟩⟩
        have := hρ ![c, x, x, m] hsC5 (by simp [hsProgram]) ⟨?_, ?_⟩
        · exact (tAt_holds ρ ![c, x, x, m] 1).mp this
        · simp only [hsC5, Formula.realize_inf, realize_isClG, realize_posG, realize_maxF]
          exact ⟨⟨by simpa using hc, by simpa using hx⟩, by simpa using hm⟩
        · intro a ha
          simp only [hsC5, List.mem_singleton] at ha
          subst ha
          exact (bAt_holds ρ ![c, x, x, m] 0 3).mpr (by simpa using hB m)
      · push Not at hpos
        refine absurd (hρ ![c, m, m, m] hsG1 (by simp [hsProgram]) ⟨?_, ?_⟩) not_false
        · simp only [hsG1, Formula.realize_inf, realize_isClG, realize_maxF, realize_noPosG]
          exact ⟨⟨by simpa using hc, by simpa using hm⟩, by simpa using hpos⟩
        · intro a ha
          simp only [hsG1, List.mem_singleton] at ha
          subst ha
          exact (bAt_holds ρ ![c, m, m, m] 0 3).mpr (by simpa using hB m)
    · push Not at hall
      obtain ⟨y, hy, hny⟩ := hall
      exact ⟨y, Or.inr ⟨hy, hny⟩⟩

/-- HORN-SAT is in PTIME. -/
theorem hornSat_mem_PTIME : HORNSAT ∈ PTIME :=
  hornSat_sigmaSOHornDefinable

end Correctness

end Program

end DescriptiveComplexity
