/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.Problems.HornSat.Defs

/-!
# HORN-SAT is existential second-order definable

HORN-SAT is `Σ₁`-definable (`DescriptiveComplexity.hornSat_sigmaSODefinable`), hence in
NP: its kernel is the one of SAT (`DescriptiveComplexity.satKernel` – every clause
contains a true literal) conjoined with the *first-order* Horn condition
(`DescriptiveComplexity.hornCondKernel` – no clause has two distinct positive literals),
over the same single existential block guessing a truth assignment.

Membership in NP is of course not the sharp statement: Horn satisfiability is
decidable in linear time ([Dowling & Gallier 1984][dowling1984linear]), and
HORN-SAT is the canonical complete problem for polynomial time. What the
library can state without a definition of PTIME is the hardness half, in
`DescriptiveComplexity.Problems.HornSat.Hardness`.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock

section SigmaOne

/-- The first-order Horn condition, in the kernel's vocabulary: two variables
occurring positively in the same clause coincide. -/
private noncomputable def hornCondKernel : satSOLang.Sentence :=
  fo% ∀ c x y, (kIsClSym(c) ∧ kPosSym(c, x)) ∧ kPosSym(c, y) → x ≐ y

/-- Realization of the Horn condition: it does not depend on the guessed truth
assignment, and says exactly that every clause has at most one positive
literal. -/
private theorem realize_hornCondKernel {A : Type} [Language.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) hornCondKernel) ↔
      AtMostOnePositive A := by
  let := satAssignBlock.structure ρ
  rw [hornCondKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_rel₁, Formula.realize_rel₂,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr, Language.relMap_sumInl]
  constructor
  · intro h c x y hc hx hy
    exact h ![c, x, y] ⟨⟨hc, hx⟩, hy⟩
  · intro h i hi
    exact h (i 0) (i 1) (i 2) hi.1.1 hi.1.2 hi.2

/-- Realization of the full kernel: the Horn condition and the SAT kernel. -/
private theorem realize_hornSatKernel {A : Type} [Language.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) (hornCondKernel ⊓ satKernel)) ↔
      AtMostOnePositive A ∧
        ∀ c : A, RelMap satIsClause ![c] → ∃ x : A,
          (RelMap satPosIn ![c, x] ∧ ρ satNuSym.1 fun _ => x) ∨
            (RelMap satNegIn ![c, x] ∧ ¬ρ satNuSym.1 fun _ => x) := by
  let := satAssignBlock.structure ρ
  exact Formula.realize_inf.trans
    (and_congr (realize_hornCondKernel ρ) (realize_satKernel ρ))

/-- **HORN-SAT is `Σ₁`-definable**: guess a truth assignment and check, in
first-order logic, that every clause contains a true literal and that no clause
has two positive literals. Since NP is defined as `Σ₁`-definability, this is
the statement `HORNSAT ∈ NP`. -/
theorem hornSat_sigmaSODefinable : SigmaSODefinable 1 HORNSAT := by
  refine ⟨[satAssignBlock], rfl, hornCondKernel ⊓ satKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨hhorn, ν, hν⟩
    exact ⟨fun _ x => ν (x ⟨0, Nat.one_pos⟩),
      (realize_hornSatKernel _).mpr ⟨hhorn, fun c hc => hν c hc⟩⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨hhorn, hsat⟩ := (realize_hornSatKernel ρ).mp hρ
    exact ⟨hhorn, fun a => ρ satNuSym.1 fun _ => a, hsat⟩

/-- HORN-SAT is in NP. -/
theorem hornSat_mem_NP : HORNSAT ∈ NP :=
  hornSat_sigmaSODefinable

end SigmaOne

end DescriptiveComplexity
