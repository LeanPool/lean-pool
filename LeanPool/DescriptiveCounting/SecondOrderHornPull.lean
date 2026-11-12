/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.SecondOrderHorn
public import LeanPool.DescriptiveCounting.SecondOrderPull
import LeanPool.DescriptiveCounting.OrderedComposition
import all LeanPool.DescriptiveCounting.SecondOrderHorn
import all LeanPool.DescriptiveCounting.SecondOrderPull

/-!
# Pulling SO-Horn definability back through an interpretation

SO-Horn definability is closed under (ordered) first-order reductions
(`DescriptiveComplexity.SigmaSOHornDefinable.of_orderedReduction`). This is what makes
the fragment a `DescriptiveComplexity.ComplexityClass` – the class
`DescriptiveComplexity.PTIME` – rather than a mere definability predicate.

The closure is *not* an instance of the general pullback of
`DescriptiveComplexity.SecondOrderPull`, which only says that the pulled-back kernel is
some first-order formula: here the pulled-back kernel has to stay *Horn*. It
does, and for a structural reason worth stating, since it is exactly what the
Horn condition is careful about: the condition constrains the occurrences of
the *second-order* variables only, while an interpretation rewrites the
*input-vocabulary* atoms – which live in the guard, where anything is allowed.
Concretely, pulling a clause back through a `d`-dimensional interpretation
with tag type `Tag`:

* the block is pulled as in `DescriptiveComplexity.SOBlock.pull`: an `n`-ary relation
  variable on `Tag × A^d` becomes one `(n·d)`-ary relation variable on `A` per
  `n`-tuple of tags;
* a clause becomes one clause per assignment `t : Fin k → Tag` of tags to its
  universally quantified variables (`DescriptiveComplexity.HornClause.pull`), with the
  `k` variables replaced by `k · d` coordinates;
* its guard becomes the ordinary formula pullback
  `DescriptiveComplexity.FOInterpretation.pull` at the tag assignment `t` – an arbitrary
  first-order formula, which is fine, guards being unconstrained;
* each body and head atom becomes the atom of the corresponding pulled
  relation variable (`DescriptiveComplexity.SOAtom.pull`) – *still an atom*, which is
  what keeps the clause Horn.

The one place the order is needed is that the guards of the target may mention
it: the pullback interprets the target's order by the lexicographic order on
tagged tuples (`DescriptiveComplexity.FOInterpretation.ordExtend`), which is why the
definability notion quantifies over ordered structures in the first place.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ}
variable {B : SOBlock} {k : ℕ}

variable [L₂.IsRelational]

/-! ### Pulling back a clause and a program -/

/-- The pullback of a Horn clause at a tag assignment: guards pull back as
formulas, atoms as atoms – so the result is again a Horn clause. -/
noncomputable def HornClause.pull (I : FOInterpretation L₁ L₂ Tag d)
    (c : HornClause L₂ B k) (t : Fin k → Tag) : HornClause L₁ (B.pull Tag d) (k * d) where
  guard := guardPull I c.guard t
  body := c.body.map fun a => a.pull d t
  head := c.head.map fun a => a.pull d t

theorem HornClause.pull_holds {A : Type} [L₁.Structure A]
    (I : FOInterpretation L₁ L₂ Tag d) (c : HornClause L₂ B k) (t : Fin k → Tag)
    (ρ : B.Assignment (I.Map A)) (w : Fin (k * d) → A) :
    (c.pull I t).Holds (B.pullAssign ρ) w ↔ c.Holds ρ (tagVal I t w) := by
  have hhead : (c.pull I t).HeadHolds (B.pullAssign ρ) w ↔ c.HeadHolds ρ (tagVal I t w) := by
    rw [HornClause.HeadHolds, HornClause.HeadHolds, HornClause.pull]
    cases c.head with
    | none => exact Iff.rfl
    | some a => exact a.pull_holds I t ρ w
  refine imp_congr (and_congr ?_ ?_) hhead
  · exact realize_guardPull I c.guard t w
  · rw [HornClause.pull]
    constructor
    · intro h a ha
      exact (a.pull_holds I t ρ w).mp (h _ (List.mem_map_of_mem ha))
    · intro h a' ha'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
      exact (a.pull_holds I t ρ w).mpr (h a ha)

/-- The pullback of a Horn program: one clause per clause of the program and
per assignment of tags to its universally quantified variables. -/
noncomputable def HornProgram.pull (I : FOInterpretation L₁ L₂ Tag d)
    (prog : HornProgram L₂ B k) : HornProgram L₁ (B.pull Tag d) (k * d) :=
  prog.flatMap fun c => (allTagAssign Tag k).map fun t => c.pull I t

theorem HornProgram.pull_mem (I : FOInterpretation L₁ L₂ Tag d)
    {prog : HornProgram L₂ B k} {c : HornClause L₂ B k} (hc : c ∈ prog)
    (t : Fin k → Tag) : c.pull I t ∈ prog.pull I := by
  rw [HornProgram.pull, List.mem_flatMap]
  exact ⟨c, hc, List.mem_map.mpr ⟨t, mem_allTagAssign t, rfl⟩⟩

theorem HornProgram.pull_cases (I : FOInterpretation L₁ L₂ Tag d)
    {prog : HornProgram L₂ B k} {c' : HornClause L₁ (B.pull Tag d) (k * d)}
    (hc' : c' ∈ prog.pull I) : ∃ c ∈ prog, ∃ t : Fin k → Tag, c' = c.pull I t := by
  rw [HornProgram.pull, List.mem_flatMap] at hc'
  obtain ⟨c, hc, hmem⟩ := hc'
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hmem
  exact ⟨c, hc, t, rfl⟩

/-! ### Correctness of the pullback -/

section Correctness

variable {A : Type} [L₁.Structure A] (I : FOInterpretation L₁ L₂ Tag d)
variable (prog : HornProgram L₂ B k)

/-- An assignment satisfies a program on the interpreted structure iff its
transfer satisfies the pulled program on the base structure. -/
theorem HornProgram.pull_holds (ρ : B.Assignment (I.Map A)) :
    (prog.pull I).Holds (B.pullAssign ρ) ↔ prog.Holds ρ := by
  constructor
  · intro h v c hc
    have hp := h (fun m => (v (finProdFinEquiv.symm m).1).2 (finProdFinEquiv.symm m).2)
      (c.pull I fun p => (v p).1) (HornProgram.pull_mem I hc _)
    have h2 := (HornClause.pull_holds I c (fun p => (v p).1) ρ _).mp hp
    rwa [tagVal_split I v] at h2
  · intro h w c' hc'
    obtain ⟨c, hc, t, rfl⟩ := HornProgram.pull_cases I hc'
    exact (HornClause.pull_holds I c t ρ w).mpr (h (tagVal I t w) c hc)

/-- **The pullback is correct**: the program is satisfiable on the interpreted
structure iff its pullback is satisfiable on the base structure. -/
private theorem exists_holds_pull :
    (∃ ρ : B.Assignment (I.Map A), prog.Holds ρ) ↔
      ∃ σ : (B.pull Tag d).Assignment A, (prog.pull I).Holds σ := by
  constructor
  · rintro ⟨ρ, hρ⟩
    exact ⟨B.pullAssign ρ, (HornProgram.pull_holds I prog ρ).mpr hρ⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨B.mergeAssign σ, (HornProgram.pull_holds I prog (B.mergeAssign σ)).mp ?_⟩
    rw [B.pullAssign_mergeAssign σ]
    exact hσ

end Correctness

/-! ### Closure under reductions -/

section Closure

variable [L₁.IsRelational] {P : DecisionProblem L₁} {Q : DecisionProblem L₂}

/-- **SO-Horn definability is closed under ordered first-order reductions.**
The Horn shape survives the pullback because an interpretation only rewrites
the input-vocabulary atoms, which live in the guards; the second-order atoms
are merely re-indexed. -/
theorem SigmaSOHornDefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q)
    (h : SigmaSOHornDefinable Q) : SigmaSOHornDefinable P := by
  obtain ⟨B, k, prog, hprog⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  refine ⟨B.pull f.Tag f.dim, k * f.dim,
    HornProgram.pull f.toInterpretation.ordExtend prog, ?_⟩
  intro A _ _ _ _
  let := f.toInterpretation.mapLinearOrder A
  have := f.toInterpretation.map_finite A
  have := f.toInterpretation.map_nonempty A
  refine (f.correct A).trans ((hprog (f.toInterpretation.Map A)).trans ?_)
  refine Iff.trans ?_ (exists_holds_pull f.toInterpretation.ordExtend prog)
  exact (exists_holds_equiv (f.toInterpretation.ordExtendLEquiv A) prog).symm

/-- SO-Horn definability is closed under first-order reductions. -/
theorem SigmaSOHornDefinable.of_foReduction (f : P ≤ᶠᵒ Q)
    (h : SigmaSOHornDefinable Q) : SigmaSOHornDefinable P :=
  h.of_orderedReduction f.toOrdered

end Closure

end DescriptiveComplexity
