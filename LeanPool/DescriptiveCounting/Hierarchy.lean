/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

import LeanPool.DescriptiveCounting.SecondOrderLift
public import LeanPool.DescriptiveCounting.SecondOrderOrdered
public import LeanPool.DescriptiveCounting.SecondOrderHornPull
import LeanPool.DescriptiveCounting.RelComposition
import all LeanPool.DescriptiveCounting.Composition
import all LeanPool.DescriptiveCounting.RelComposition
import all LeanPool.DescriptiveCounting.Relativized

/-!
# The polynomial hierarchy, defined by second-order alternation

The levels `Σₖᵖ`/`Πₖᵖ` of the polynomial hierarchy for `k ≥ 1` – in
particular `NP = Σ₁ᵖ` and `coNP = Π₁ᵖ` – are *defined* here as
`ComplexityClass`es, via Fagin's ([Fagin 1974][fagin1974generalized]) and
Stockmeyer's ([Stockmeyer 1976][stockmeyer1976polynomial]) theorems: membership is
second-order definability with `k` alternating quantifier blocks
(`DescriptiveComplexity.SigmaSODefinable` / `DescriptiveComplexity.PiSODefinable`), and the closure
of membership under (ordered) FO reductions is provided by the pullback
theorems of `DescriptiveComplexity.SecondOrderPull` and
`DescriptiveComplexity.SecondOrderOrdered`.

Hardness is defined *cofinally*: `P` is hard when every problem of the class
reduces (by an ordered FO reduction) to every problem that `P` itself reduces
to. This is equivalent to the usual “everything in the class reduces to `P`”
(`DescriptiveComplexity.cofinalHard_iff`, with per-class specializations
`DescriptiveComplexity.hard_sigmaP_succ_iff`, `DescriptiveComplexity.hard_piP_succ_iff` and
`DescriptiveComplexity.hard_PTIME_iff`), and the formulation makes hardness travel
forward along reductions by composition alone.

Level 0 is `DescriptiveComplexity.PTIME`, polynomial time, *defined* here as
definability in the Horn fragment SO-Horn of existential second-order logic
([Grädel 1992][gradel1992capturing]) – the same move as defining NP by
`Σ₁`-definability, and equally a definition rather than an axiom: the library
declares **no axioms**, every theorem depending on nothing beyond Lean's
standard `propext`, `Classical.choice` and `Quot.sound` (check with
`#print axioms`). The order-free characterization of PTIME is the
Chandra–Harel/Gurevich problem and is not needed here: SO-Horn definability,
like ordered FO reductions, is stated over ordered structures.

**What level 0 does and does not give.** It is a genuine class, closed under
(ordered) FO reductions by the shape-preserving pullback of
`DescriptiveComplexity.SecondOrderHornPull`, and `Πₖᵖ` is the complements of `Σₖᵖ` at
*every* level (`DescriptiveComplexity.mem_piP_iff`) – at level 0 by definition, above
it by the quantifier duality.

All four inclusions of level 0 into level 1 are proved – `PTIME ⊆ NP`,
`PTIME ⊆ coNP` and their complements (`DescriptiveComplexity.PTIME_subset_NP`,
`DescriptiveComplexity.PTIME_subset_coNP`, `DescriptiveComplexity.coPTIME_subset_NP`,
`DescriptiveComplexity.coPTIME_subset_coNP`); they live downstream with HORN-SAT, since
they go through the Horn discharge and, for the two crossing ones, through the
certificate of Horn *un*satisfiability of
`DescriptiveComplexity.Problems.HornSat.Unsat`.

That the two zeroth levels *coincide* – `PiP 0 = SigmaP 0`, polynomial time
closed under complement – is proved downstream, as
`DescriptiveComplexity.piP_zero_eq`: it is Grädel's capture theorem at level 0, and
its route is the logic-to-logic equivalence of SO-Horn with FO(LFP)
(`DescriptiveComplexity.lfpDefinable_iff_sigmaSOHornDefinable`, in
`DescriptiveComplexity.FixedPointHorn`), a full logic being closed under negation by
construction; no machine model is involved.

The level inclusions above 0, the duality `Πₖᵖ = co-Σₖᵖ` and the class `PH` are
all proved (`DescriptiveComplexity.sigmaP_subset_sigmaP_succ`,
`DescriptiveComplexity.mem_piP_iff`…).
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-! ### Congruence of definability in the problem -/

/-- `Σₖ`-definability only depends on the finite instances of a problem.
Registered in the Lax archive (for `NP`) as
[`Lax904597.NPClass.NP_mem_congr_finite`](https://laxarchive.org/lax-904597/Lax904597.NPClass.html#s-Lax904597.NPClass.NP_mem_congr_finite). -/
theorem sigmaSODefinable_congr {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) (k : ℕ) :
    SigmaSODefinable k P ↔ SigmaSODefinable k Q := by
  constructor <;> rintro ⟨Bs, hk, φ, hφ⟩ <;> refine ⟨Bs, hk, φ, ?_⟩ <;> intro A _ _ _
  · exact (h A).symm.trans (hφ A)
  · exact (h A).trans (hφ A)

/-- `Πₖ`-definability only depends on the finite instances of a problem. -/
theorem piSODefinable_congr {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) (k : ℕ) :
    PiSODefinable k P ↔ PiSODefinable k Q := by
  constructor <;> rintro ⟨Bs, hk, φ, hφ⟩ <;> refine ⟨Bs, hk, φ, ?_⟩ <;> intro A _ _ _
  · exact (h A).symm.trans (hφ A)
  · exact (h A).trans (hφ A)

/-- An ordered FO reduction can be transported along an agreement of the
source problems on finite structures. -/
def OrderedFOReduction.congrSource {L' : Language.{0, 0}} [L'.IsRelational]
    {P P' : DecisionProblem L} {S : DecisionProblem L'}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ P' A) (g : P ≤ᶠᵒ[≤] S) :
    P' ≤ᶠᵒ[≤] S :=
  letI := g.tagFinite
  letI := g.tagNonempty
  { Tag := g.Tag
    dim := g.dim
    toInterpretation := g.toInterpretation
    correct := fun A _ _ _ _ => (h A).symm.trans (g.correct A) }

/-! ### Cofinal hardness -/

/-- Hardness for a collection of problems, cofinally: every problem of the
collection reduces to every problem that `P` reduces to. This is the usual
notion (see `DescriptiveComplexity.cofinalHard_iff`), in a formulation closed
under reductions by composition alone. -/
def CofinalHard (Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop)
    (P : DecisionProblem L) : Prop :=
  ∀ {L' : Language.{0, 0}} [L'.IsRelational] (S : DecisionProblem L'),
    Nonempty (P ≤ʳᶠᵒ[≤] S) →
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
        Mem Q → Nonempty (Q ≤ʳᶠᵒ[≤] S)

/-- Cofinal hardness travels forward along first-order reductions.
Registered in the Lax archive as
[`Lax904597.NPClass.cofinalHard_of_foReduction`](https://laxarchive.org/lax-904597/Lax904597.NPClass.html#s-Lax904597.NPClass.cofinalHard_of_foReduction). -/
theorem CofinalHard.of_foReduction
    {Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop}
    {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
    {P : DecisionProblem L₁} {Q : DecisionProblem L₂}
    (f : P ≤ᶠᵒ Q) (hP : CofinalHard Mem P) : CofinalHard Mem Q := by
  intro L' _ S hQS L'' _ R hR
  exact hP S (hQS.map fun g => f.toOrdered.toRel.trans g) R hR

/-- Cofinal hardness travels forward along ordered first-order reductions.
Registered in the Lax archive as
[`Lax904597.NPClass.cofinalHard_of_orderedReduction`](https://laxarchive.org/lax-904597/Lax904597.NPClass.html#s-Lax904597.NPClass.cofinalHard_of_orderedReduction). -/
theorem CofinalHard.of_orderedReduction
    {Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop}
    {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
    {P : DecisionProblem L₁} {Q : DecisionProblem L₂}
    (f : P ≤ᶠᵒ[≤] Q) (hP : CofinalHard Mem P) : CofinalHard Mem Q := by
  intro L' _ S hQS L'' _ R hR
  exact hP S (hQS.map fun g => f.toRel.trans g) R hR

/-- Cofinal hardness travels forward along relativized ordered first-order
reductions.
Registered in the Lax archive as
[`Lax904597.NPClass.cofinalHard_of_relOrderedReduction`](https://laxarchive.org/lax-904597/Lax904597.NPClass.html#s-Lax904597.NPClass.cofinalHard_of_relOrderedReduction). -/
theorem CofinalHard.of_relOrderedReduction
    {Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop}
    {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
    {P : DecisionProblem L₁} {Q : DecisionProblem L₂}
    (f : P ≤ʳᶠᵒ[≤] Q) (hP : CofinalHard Mem P) : CofinalHard Mem Q := by
  intro L' _ S hQS L'' _ R hR
  exact hP S (hQS.map fun g => f.trans g) R hR

/-- Cofinal hardness only depends on the finite instances of a problem.
Registered in the Lax archive as
[`Lax904597.NPClass.cofinalHard_congr`](https://laxarchive.org/lax-904597/Lax904597.NPClass.html#s-Lax904597.NPClass.cofinalHard_congr). -/
theorem CofinalHard.congr
    {Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop}
    {L₁ : Language.{0, 0}} [L₁.IsRelational] {P P' : DecisionProblem L₁}
    (h : ∀ (A : Type) [L₁.Structure A] [Finite A], P A ↔ P' A)
    (hP : CofinalHard Mem P) : CofinalHard Mem P' := by
  intro L' _ S hS L'' _ R hR
  exact hP S (hS.map fun g => g.congrSource fun A _ _ => (h A).symm) R hR

/-- **Cofinal hardness is the usual notion**: every problem of the collection
reduces to `P` itself. This holds whatever the
collection is – the proof only uses reflexivity and transitivity of reductions
– so the specializations to the individual classes below
(`DescriptiveComplexity.hard_sigmaP_succ_iff`, `DescriptiveComplexity.hard_piP_succ_iff`,
`DescriptiveComplexity.hard_PTIME_iff`) are corollaries by definitional unfolding.

The left-to-right direction is what a *user* of a hardness result needs, to
extract an actual reduction; it is where relationality of `P` is used, to
instantiate the cofinal quantifier at `P` itself.
Registered in the Lax archive as
[`Lax904597.NPClass.cofinalHard_iff`](https://laxarchive.org/lax-904597/Lax904597.NPClass.html#s-Lax904597.NPClass.cofinalHard_iff). -/
theorem cofinalHard_iff
    (Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop)
    (P : DecisionProblem L) :
    CofinalHard Mem P ↔
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
        Mem Q → Nonempty (Q ≤ʳᶠᵒ[≤] P) := by
  constructor
  · intro h L'' _ Q hQ
    exact h P ⟨(FOReduction.refl P).toOrdered.toRel⟩ Q hQ
  · intro h L' _ S hS L'' _ Q hQ
    exact ⟨(h Q hQ).some.trans hS.some⟩

/-! ### Classes defined by their members -/

/-- The complexity class with a given membership predicate, hardness being
cofinal hardness for it (`DescriptiveComplexity.CofinalHard`) – the shape of every
logically-defined class of this library. Only the three *membership*
obligations have to be supplied: the hardness half of the closure requirements
is discharged uniformly, by `DescriptiveComplexity.CofinalHard.of_foReduction` and
its siblings.

A class whose hardness is not cofinal hardness for its own members is built by
hand instead: `DescriptiveComplexity.ComplexityClass.empty`, where hardness is
outright trivial, and `DescriptiveComplexity.PH`, whose hardness is stated level by
level (an equivalent statement, since membership is the union of the levels,
but not a definitional one). -/
def ComplexityClass.ofMem
    (Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop)
    (mem_of_foReduction : ∀ {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
      {P : DecisionProblem L₁} {Q : DecisionProblem L₂}, (P ≤ᶠᵒ Q) → Mem Q → Mem P)
    (mem_of_orderedReduction : ∀ {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
      {P : DecisionProblem L₁} {Q : DecisionProblem L₂}, (P ≤ᶠᵒ[≤] Q) → Mem Q → Mem P)
    (mem_congr_finite : ∀ {L₁ : Language.{0, 0}} [L₁.IsRelational] {P Q : DecisionProblem L₁},
      (∀ (A : Type) [L₁.Structure A] [Finite A], P A ↔ Q A) → (Mem P ↔ Mem Q)) :
    ComplexityClass where
  Mem P := Mem P
  Hard P := CofinalHard Mem P
  mem_of_foReduction f h := mem_of_foReduction f h
  hard_of_foReduction f hP := CofinalHard.of_foReduction f hP
  mem_of_orderedReduction f h := mem_of_orderedReduction f h
  hard_of_orderedReduction f hP := CofinalHard.of_orderedReduction f hP
  hard_of_relOrderedReduction f hP := CofinalHard.of_relOrderedReduction f hP
  mem_congr_finite h := mem_congr_finite h
  hard_congr_finite h :=
    ⟨fun hP => CofinalHard.congr h hP,
      fun hP' => CofinalHard.congr (fun A _ _ => (h A).symm) hP'⟩

/-! ### The complement of a class -/

/-- The *complement* of a complexity class: the problems whose complement
belongs to it – the “co-” operator. Closure under reductions is inherited,
since a reduction complements (`DescriptiveComplexity.FOReduction.compl`). -/
noncomputable def ComplexityClass.compl (C : ComplexityClass) : ComplexityClass :=
  .ofMem (fun P => C.Mem Pᶜ)
    (fun f h => C.mem_of_foReduction f.compl h)
    (fun f h => C.mem_of_orderedReduction f.compl h)
    (fun h => C.mem_congr_finite fun A _ _ => not_congr (h A))

@[simp]
theorem ComplexityClass.mem_compl (C : ComplexityClass) {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) : P ∈ C.compl ↔ Pᶜ ∈ C :=
  Iff.rfl

/-! ### The levels of the hierarchy -/

/-- The class `Σₖ₊₁ᵖ`, defined by second-order definability with `k + 1`
alternating blocks starting existentially. -/
noncomputable def sigmaLevel (k : ℕ) : ComplexityClass :=
  .ofMem (fun P => SigmaSODefinable (k + 1) P)
    (fun f h => h.of_foReduction f)
    (fun f h => h.of_orderedReduction f)
    (fun h => sigmaSODefinable_congr h _)

/-- The class `Πₖ₊₁ᵖ`, defined by second-order definability with `k + 1`
alternating blocks starting universally. -/
noncomputable def piLevel (k : ℕ) : ComplexityClass :=
  .ofMem (fun P => PiSODefinable (k + 1) P)
    (fun f h => h.of_foReduction f)
    (fun f h => h.of_orderedReduction f)
    (fun h => piSODefinable_congr h _)

/-! ### Polynomial time, by the Horn fragment -/

/-- **The class PTIME**: the problems definable in the Horn fragment SO-Horn of
existential second-order logic ([Grädel 1992][gradel1992capturing]), which
captures polynomial time on ordered structures. It is a bona fide
`DescriptiveComplexity.ComplexityClass` because SO-Horn definability is closed under
(ordered) first-order reductions – the Horn shape survives the pullback, see
`DescriptiveComplexity.SecondOrderHornPull`.

This is level 0 of the hierarchy below (`DescriptiveComplexity.SigmaP`,
`DescriptiveComplexity.PiP`), and it has a complete problem, HORN-SAT
(`DescriptiveComplexity.HORNSAT_PTIME_complete`). That the class is closed under
complement – `PiP 0 = SigmaP 0` – is `DescriptiveComplexity.piP_zero_eq`, through the
equivalence with FO(LFP). -/
noncomputable def PTIME : ComplexityClass :=
  .ofMem (fun P => SigmaSOHornDefinable P)
    (fun f h => h.of_foReduction f)
    (fun f h => h.of_orderedReduction f)
    (fun h => sigmaSOHornDefinable_congr h)

/-! ### The hierarchy -/

/-- The `Σₖᵖ` levels of the polynomial hierarchy: polynomial time at level 0
(`DescriptiveComplexity.PTIME`, defined by the Horn fragment SO-Horn), second-order
definability with `k` alternations above. -/
noncomputable def SigmaP : ℕ → ComplexityClass
  | 0 => PTIME
  | k + 1 => sigmaLevel k

/-- The `Πₖᵖ` levels of the polynomial hierarchy; level 0 is *co*-polynomial
time, the complements of the SO-Horn definable problems. That this coincides
with `DescriptiveComplexity.PTIME` is the closure of polynomial time under complement,
`DescriptiveComplexity.piP_zero_eq` – see the module docstring. -/
noncomputable def PiP : ℕ → ComplexityClass
  | 0 => PTIME.compl
  | k + 1 => piLevel k

/-- NP is `Σ₁ᵖ`: by definition, the existential-second-order definable
problems (Fagin's theorem). -/
noncomputable abbrev NP : ComplexityClass := SigmaP 1

/-- coNP is `Π₁ᵖ`: the universal-second-order definable problems. -/
noncomputable abbrev coNP : ComplexityClass := PiP 1

/-- **`Πₖᵖ` consists of the complements of the `Σₖᵖ` problems**, at every
level: by definition at level 0, and by the quantifier duality
`DescriptiveComplexity.piSODefinable_iff_compl` above from level 1 on.

(That moreover `PiP 0 = SigmaP 0` – polynomial time closed under complement –
is `DescriptiveComplexity.piP_zero_eq`: complementing a Horn program needs its least
model computed inside the fragment, which is what the translation from FO(LFP)
provides.)
Registered in the Lax archive as
[`Lax564036.HierarchyDuality.mem_piP_iff`](https://laxarchive.org/lax-564036/Lax564036.HierarchyDuality.html#s-Lax564036.HierarchyDuality.mem_piP_iff). -/
theorem mem_piP_iff (k : ℕ) {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    P ∈ PiP k ↔ Pᶜ ∈ SigmaP k := by
  cases k with
  | zero => exact Iff.rfl
  | succ k => exact piSODefinable_iff_compl (k + 1) P

/-- `Σₖ₊₁ᵖ ⊆ Σₖ₊₂ᵖ`, by padding. (The level-0 inclusions are proved downstream
with HORN-SAT, which their proofs go through: `DescriptiveComplexity.PTIME_subset_NP`
and friends. Uniform monotonicity, `j ≤ k → Σⱼᵖ ⊆ Σₖᵖ`, therefore also lives
there: `DescriptiveComplexity.sigmaP_mono`.) -/
theorem sigmaP_subset_sigmaP_succ (k : ℕ) : SigmaP (k + 1) ⊆ SigmaP (k + 2) :=
  fun _ _ _ hP => SigmaSODefinable.succ hP

/-- `Σₖ₊₁ᵖ ⊆ Πₖ₊₂ᵖ`. -/
theorem sigmaP_subset_piP_succ (k : ℕ) : SigmaP (k + 1) ⊆ PiP (k + 2) :=
  fun _ _ _ hP => SigmaSODefinable.piSucc hP

/-- `Πₖ₊₁ᵖ ⊆ Σₖ₊₂ᵖ`. -/
theorem piP_subset_sigmaP_succ (k : ℕ) : PiP (k + 1) ⊆ SigmaP (k + 2) :=
  fun _ _ _ hP => PiSODefinable.sigmaSucc hP

/-- `Πₖ₊₁ᵖ ⊆ Πₖ₊₂ᵖ`. -/
theorem piP_subset_piP_succ (k : ℕ) : PiP (k + 1) ⊆ PiP (k + 2) :=
  fun _ _ _ hP => PiSODefinable.succ hP

/-- The polynomial hierarchy: union of all the levels. A problem is PH-hard
if it is hard for every level. -/
noncomputable def PH : ComplexityClass where
  Mem P := ∃ k, (SigmaP k).Mem P
  Hard P := ∀ k, (SigmaP k).Hard P
  mem_of_foReduction h := fun ⟨k, hk⟩ => ⟨k, (SigmaP k).mem_of_foReduction h hk⟩
  hard_of_foReduction h hP k := (SigmaP k).hard_of_foReduction h (hP k)
  mem_of_orderedReduction h := fun ⟨k, hk⟩ => ⟨k, (SigmaP k).mem_of_orderedReduction h hk⟩
  hard_of_orderedReduction h hP k := (SigmaP k).hard_of_orderedReduction h (hP k)
  hard_of_relOrderedReduction h hP k := (SigmaP k).hard_of_relOrderedReduction h (hP k)
  mem_congr_finite h := exists_congr fun k => (SigmaP k).mem_congr_finite h
  hard_congr_finite h := forall_congr' fun k => (SigmaP k).hard_congr_finite h

theorem sigmaP_subset_PH (k : ℕ) : SigmaP k ⊆ PH :=
  fun _ _ _ hP => ⟨k, hP⟩

/-- `Πₖ₊₁ᵖ ⊆ PH`. (At level 0 this is
`DescriptiveComplexity.piP_zero_subset_PH`, which needs `PTIME ⊆ NP` and so lives
downstream, with HORN-SAT.) -/
theorem piP_subset_PH (k : ℕ) : PiP (k + 1) ⊆ PH :=
  fun _ _ _ hP => ⟨k + 2, piP_subset_sigmaP_succ k hP⟩

/-- A problem's complement is in coNP iff the problem is in NP.
Registered in the Lax archive as
[`Lax564036.HierarchyDuality.compl_mem_coNP_iff`](https://laxarchive.org/lax-564036/Lax564036.HierarchyDuality.html#s-Lax564036.HierarchyDuality.compl_mem_coNP_iff). -/
theorem compl_mem_coNP_iff {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    Pᶜ ∈ coNP ↔ P ∈ NP := by
  rw [mem_piP_iff, DecisionProblem.compl_compl]

/-! ### Hardness, class by class -/

/-- Cofinal `Σₖ₊₁ᵖ`-hardness is the usual notion: every `Σₖ₊₁`-definable
problem reduces to `P`. -/
theorem hard_sigmaP_succ_iff (k : ℕ) (P : DecisionProblem L) :
    (SigmaP (k + 1)).Hard P ↔
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
        SigmaSODefinable (k + 1) Q → Nonempty (Q ≤ʳᶠᵒ[≤] P) :=
  cofinalHard_iff _ P

/-- Cofinal `Πₖ₊₁ᵖ`-hardness is the usual notion: every `Πₖ₊₁`-definable
problem reduces to `P`. -/
theorem hard_piP_succ_iff (k : ℕ) (P : DecisionProblem L) :
    (PiP (k + 1)).Hard P ↔
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
        PiSODefinable (k + 1) Q → Nonempty (Q ≤ʳᶠᵒ[≤] P) :=
  cofinalHard_iff _ P

/-- Cofinal PTIME-hardness is the usual notion: every SO-Horn definable
problem reduces to `P`. -/
theorem hard_PTIME_iff (P : DecisionProblem L) :
    PTIME.Hard P ↔
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
        SigmaSOHornDefinable Q → Nonempty (Q ≤ʳᶠᵒ[≤] P) :=
  cofinalHard_iff _ P

end DescriptiveComplexity
