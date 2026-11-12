/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Set.Card
public import LeanPool.DescriptiveCounting.Iterate
public import LeanPool.DescriptiveCounting.SecondOrderHorn
public import LeanPool.DescriptiveCounting.SecondOrderHornPull
public import LeanPool.DescriptiveCounting.Padding
public import LeanPool.DescriptiveCounting.OrderedComposition
import all LeanPool.DescriptiveCounting.Padding
import all LeanPool.DescriptiveCounting.SecondOrderHornPull
import all LeanPool.DescriptiveCounting.SecondOrderPull

/-!
# FO(LFP): first-order logic with a least fixed point

The logic FO(LFP) ([Immerman 1986][immerman1986relational]; [Vardi
1982][vardi1982complexity]), in the clausal normal form this library uses for
kernels everywhere else: a `DescriptiveComplexity.LFPDef` bundles

* a block of relation variables and a finite list of *rules* deriving them –
  the same `DescriptiveComplexity.HornClause` data as an SO-Horn program, read here as
  an inductive definition rather than a constraint;
* an arbitrary first-order *output* sentence over the input vocabulary
  expanded by those variables, evaluated at the least fixed point.

## Why the output formula is the point

The fixed point is the same object in both logics – the least model of a set
of rules. What distinguishes FO(LFP) from SO-Horn is what one is allowed to
say *about* it. An SO-Horn program can only reject models, through goal
clauses, and a goal clause tests its atoms positively; FO(LFP) evaluates an
unrestricted first-order sentence, so it may negate fixed-point atoms.

That is exactly the closure that SO-Horn lacks: `DescriptiveComplexity.LFPDefinable` is
closed under complement by negating the output
(`DescriptiveComplexity.LFPDefinable.compl`, a one-liner), whereas the corresponding
statement for SO-Horn is open – see `DescriptiveComplexity.Problems.HornSat`. The
inclusion `DescriptiveComplexity.SigmaSOHornDefinable.lfpDefinable` transports every
SO-Horn definition into this logic, so PTIME as defined by the Horn fragment
sits inside FO(LFP) together with its complements.

## What is proved here, and where the equivalence is completed

`DescriptiveComplexity.SigmaSOHornDefinable.lfpDefinable` is one half of the equivalence
of the two formalisms: every SO-Horn definition is an FO(LFP) definition. The
other half – bringing an FO(LFP) definition back into the Horn fragment – is
the translation of `DescriptiveComplexity.FixedPointHorn`, built on the stage theory of
this file: the stages `DescriptiveComplexity.derivesIn` stabilize once the atom count is
reached (`DescriptiveComplexity.derivesIn_iff_derives_of_card_le`), so a stage indexed by
a large enough tuple stands in for the fixed point, and its *complement* can
be derived positively, one stage at a time. Together the two halves make the
notions interchangeable (`DescriptiveComplexity.lfpDefinable_iff_sigmaSOHornDefinable`)
and give `PiP 0 = SigmaP 0` (`DescriptiveComplexity.piP_zero_eq`).

The notion is also closed under (ordered) first-order reductions
(`DescriptiveComplexity.LFPDefinable.of_orderedReduction`), so it is class-worthy in the
sense of `DescriptiveComplexity.ComplexityClass`.

A second consumer of the stage theory is not formalized: a `Σ₁` definition,
giving `FO(LFP) ⊆ NP` directly, would *guess* a fixed point together with a
well-founded derivation order and check both first-order. The semantic key is
provided here – `DescriptiveComplexity.derives_eq_of_closed_of_wf` says that a relation
*closed* under the rules and *well-foundedly derivable* is exactly the least
fixed point, `DescriptiveComplexity.derives_step_of_depth` supplies the witnessing
order from the stages, and `DescriptiveComplexity.LFPDef.holds_iff_of_certificate`
packages this; the formulas themselves are not built. (The inclusion itself
follows by composing the translation with the Horn membership of
`DescriptiveComplexity.Problems.HornSat`.)

## The fixed point

Rather than a stage-indexed iteration, the least model is the inductive
predicate `DescriptiveComplexity.Derives`: a tuple is derived when some rule fires on
already-derived tuples. Being an inductive definition it comes with exactly the
two properties a least fixed point needs – it satisfies the rules
(`DescriptiveComplexity.lfpAssign_rule`) and it is contained in every assignment that
does (`DescriptiveComplexity.lfpAssign_least`).

Rules whose head is `none` derive nothing and are simply inert here, so an
SO-Horn program can be handed over unchanged: its goal clauses reappear in the
output formula.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The least model of a rule system -/

section Derives

variable {Lg : Language.{0, 0}} {B : SOBlock} {k : ℕ}
variable {A : Type} [Lg.Structure A]

/-- The tuples derivable by a system of rules: the least fixed point, as an
inductive predicate. A rule fires when its guard holds and all its body atoms
are already derived, and it derives its head atom. -/
inductive Derives (rules : List (HornClause Lg B k)) :
    (Σ i : B.ι, Fin (B.arity i) → A) → Prop
  | rule {c : HornClause Lg B k} (hc : c ∈ rules) {a : SOAtom B k}
      (ha : c.head = some a) {v : Fin k → A} (hg : c.guard.Realize v)
      (hb : ∀ b ∈ c.body, Derives rules ⟨b.idx, fun j => v (b.args j)⟩) :
      Derives rules ⟨a.idx, fun j => v (a.args j)⟩

/-- The least fixed point of a rule system, as an assignment of the block. -/
def lfpAssign (rules : List (HornClause Lg B k)) : B.Assignment A :=
  fun i x => Derives rules ⟨i, x⟩

/-- The least fixed point satisfies every rule with a head. (A clause with no
head is a *constraint*, not a rule: it derives nothing, and is what the output
formula of `DescriptiveComplexity.LFPDef` takes over.) -/
theorem lfpAssign_rule {rules : List (HornClause Lg B k)}
    {c : HornClause Lg B k} (hc : c ∈ rules) {a : SOAtom B k}
    (ha : c.head = some a) (v : Fin k → A) : c.Holds (lfpAssign rules) v := by
  rintro ⟨hg, hb⟩
  rw [HornClause.HeadHolds, ha, Option.elim_some]
  exact Derives.rule hc ha hg fun b hbmem => hb b hbmem

/-- **The least fixed point is contained in every prefixpoint**: in every
assignment closed under the rules. -/
theorem lfpAssign_least_of_closed {rules : List (HornClause Lg B k)}
    {ρ : B.Assignment A}
    (hρ : ∀ c ∈ rules, ∀ a : SOAtom B k, c.head = some a → ∀ v : Fin k → A,
      c.guard.Realize v → (∀ b ∈ c.body, b.Holds ρ v) → a.Holds ρ v)
    {p : Σ i : B.ι, Fin (B.arity i) → A} (hp : Derives rules p) : ρ p.1 p.2 := by
  induction hp with
  | rule hc ha hg hb ih => exact hρ _ hc _ ha _ hg fun b hbmem => ih b hbmem

/-- The least fixed point is contained in every assignment satisfying the
rules. -/
theorem lfpAssign_least {rules : List (HornClause Lg B k)}
    {ρ : B.Assignment A} (hρ : ∀ v : Fin k → A, ∀ c ∈ rules, c.Holds ρ v)
    {p : Σ i : B.ι, Fin (B.arity i) → A} (hp : Derives rules p) : ρ p.1 p.2 := by
  refine lfpAssign_least_of_closed (fun c hc a ha v hg hb => ?_) hp
  have := hρ v c hc ⟨hg, hb⟩
  rwa [HornClause.HeadHolds, ha, Option.elim_some] at this

end Derives

/-! ### Stages, depth, and the certificate characterization

Putting FO(LFP) back into the Horn fragment, and certifying a fixed point in
`Σ₁`, both need the same thing: a way to say
“this relation *is* the least fixed point” that a *positive* formalism can
test. Closure alone is not enough (anything larger is closed too); what pins
the least fixed point down is closure together with *well-founded
derivability* – every element derived by a rule from strictly earlier
elements. That is `DescriptiveComplexity.derives_eq_of_closed_of_wf` below, and the
stages provide the witnessing order. -/

section Stages

variable {Lg : Language.{0, 0}} {B : SOBlock} {k : ℕ}
variable {A : Type} [Lg.Structure A]

/-- The atoms of a block over a structure: a relation variable and a tuple. -/
abbrev BAtom (B : SOBlock) (A : Type) : Type := Σ i : B.ι, Fin (B.arity i) → A

/-- A block has at most its number of relation symbols times the largest tuple space. -/
theorem SOBlock.card_atoms_le (B : SOBlock) (A : Type) [Finite A] [Nonempty A] :
    Nat.card (BAtom B A) ≤ Nat.card B.ι * Nat.card A ^ blockArityBound B := by
  have := Fintype.ofFinite B.ι
  rw [Nat.card_sigma]
  have hbound : ∀ i : B.ι,
      Nat.card (Fin (B.arity i) → A) ≤ Nat.card A ^ blockArityBound B := by
    intro i
    rw [Nat.card_fun, Nat.card_fin]
    exact Nat.pow_le_pow_right Nat.card_pos (arity_le_blockArityBound B i)
  calc
    ∑ i, Nat.card (Fin (B.arity i) → A) ≤ ∑ _i : B.ι, Nat.card A ^ blockArityBound B :=
      Finset.sum_le_sum fun i _ => hbound i
    _ = Nat.card B.ι * Nat.card A ^ blockArityBound B := by
      rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card (α := B.ι)]
      rfl

/-- One application of the rules to a set of atoms. -/
def stepDerives (rules : List (HornClause Lg B k)) (S : BAtom B A → Prop) :
    BAtom B A → Prop :=
  fun q => ∃ c ∈ rules, ∃ a : SOAtom B k, c.head = some a ∧ ∃ v : Fin k → A,
    q = ⟨a.idx, fun j => v (a.args j)⟩ ∧ c.guard.Realize v ∧
      ∀ b ∈ c.body, S ⟨b.idx, fun j => v (b.args j)⟩

/-- The stages of the derivation: what is derivable in at most `n` rounds. -/
def derivesIn (rules : List (HornClause Lg B k)) : ℕ → BAtom B A → Prop
  | 0 => fun _ => False
  | n + 1 => fun q => derivesIn rules n q ∨ stepDerives rules (derivesIn rules n) q

private theorem derivesIn_succ {rules : List (HornClause Lg B k)} {n : ℕ} {q : BAtom B A}
    (h : derivesIn rules n q) : derivesIn rules (n + 1) q := Or.inl h

private theorem derivesIn_le {rules : List (HornClause Lg B k)} {m n : ℕ} (hmn : m ≤ n)
    {q : BAtom B A} (h : derivesIn rules m q) : derivesIn rules n q := by
  induction n with
  | zero => rwa [Nat.le_zero.mp hmn] at h
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with hlt | heq
    · exact derivesIn_succ (ih (Nat.lt_succ_iff.mp hlt))
    · rwa [heq] at h

/-- Finitely many derivable atoms share a stage. -/
private theorem exists_common_stage {rules : List (HornClause Lg B k)}
    (l : List (BAtom B A)) (h : ∀ q ∈ l, ∃ n, derivesIn rules n q) :
    ∃ N, ∀ q ∈ l, derivesIn rules N q := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons q l ih =>
    obtain ⟨n, hn⟩ := h q (List.mem_cons_self ..)
    obtain ⟨N, hN⟩ := ih fun r hr => h r (List.mem_cons_of_mem _ hr)
    refine ⟨max n N, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact derivesIn_le (le_max_left _ _) hn
    · exact derivesIn_le (le_max_right _ _) (hN r hr')

/-- The stages exhaust the least fixed point. -/
private theorem derives_iff_derivesIn {rules : List (HornClause Lg B k)} {q : BAtom B A} :
    Derives rules q ↔ ∃ n, derivesIn rules n q := by
  constructor
  · intro h
    induction h with
    | @rule c hc a ha v hg hb ih =>
      obtain ⟨N, hN⟩ :=
        exists_common_stage (rules := rules)
          (c.body.map fun b : SOAtom B k => (⟨b.idx, fun j => v (b.args j)⟩ : BAtom B A))
          (fun q hq => by
            obtain ⟨b, hbmem, rfl⟩ := List.mem_map.mp hq
            exact ih b hbmem)
      exact ⟨N + 1, Or.inr ⟨c, hc, a, ha, v, rfl, hg,
        fun b hbmem => hN _ (List.mem_map_of_mem hbmem)⟩⟩
  · rintro ⟨n, hn⟩
    induction n generalizing q with
    | zero => exact hn.elim
    | succ n ih =>
      rcases hn with h | ⟨c, hc, a, ha, v, rfl, hg, hb⟩
      · exact ih h
      · exact Derives.rule hc ha hg fun b hbmem => ih (hb b hbmem)

/-! #### Depth, and the certificate -/

/-- The stage at which an atom first appears. -/
noncomputable def depth (rules : List (HornClause Lg B k)) (q : BAtom B A) : ℕ :=
  sInf {n | derivesIn rules n q}

private theorem derivesIn_depth {rules : List (HornClause Lg B k)} {q : BAtom B A}
    (h : Derives rules q) : derivesIn rules (depth rules q) q :=
  Nat.sInf_mem (derives_iff_derivesIn.mp h)

private theorem depth_le {rules : List (HornClause Lg B k)} {n : ℕ} {q : BAtom B A}
    (h : derivesIn rules n q) : depth rules q ≤ n :=
  Nat.sInf_le h

/-- **Every derived atom is derived from atoms of strictly smaller depth**: the
least fixed point comes with a well-founded derivation order. -/
theorem derives_step_of_depth {rules : List (HornClause Lg B k)} {q : BAtom B A}
    (h : Derives rules q) :
    ∃ c ∈ rules, ∃ a : SOAtom B k, c.head = some a ∧ ∃ v : Fin k → A,
      q = ⟨a.idx, fun j => v (a.args j)⟩ ∧ c.guard.Realize v ∧
        ∀ b ∈ c.body, Derives rules (⟨b.idx, fun j => v (b.args j)⟩ : BAtom B A) ∧
          depth rules (⟨b.idx, fun j => v (b.args j)⟩ : BAtom B A) < depth rules q := by
  have hd := derivesIn_depth h
  cases hn : depth rules q with
  | zero => rw [hn] at hd; exact hd.elim
  | succ n =>
    rw [hn] at hd
    rcases hd with hprev | ⟨c, hc, a, ha, v, rfl, hg, hb⟩
    · exact absurd (depth_le hprev) (by omega)
    · refine ⟨c, hc, a, ha, v, rfl, hg, fun b hbmem => ⟨?_, ?_⟩⟩
      · exact derives_iff_derivesIn.mpr ⟨n, hb b hbmem⟩
      · exact lt_of_le_of_lt (depth_le (hb b hbmem)) (by omega)

/-! #### Stabilization: the stages close within `Nat.card` many rounds

On a finite structure the stages are an increasing chain of subsets of the
finitely many atoms, so they stabilize by the time the atom count is reached
(`DescriptiveComplexity.exists_succ_eq_of_monotone_subset`, the one chain
pigeonhole of the library, in `DescriptiveComplexity.Iterate`) – after that many
rounds, `DescriptiveComplexity.derivesIn` *is* the least fixed point. This is
what lets a stage indexed by a large enough tuple stand in for the fixed point
itself in `DescriptiveComplexity.FixedPointHorn`. -/

private theorem stepDerives_congr {rules : List (HornClause Lg B k)}
    {S S' : BAtom B A → Prop} (h : ∀ q, S q ↔ S' q) (q : BAtom B A) :
    stepDerives rules S q ↔ stepDerives rules S' q := by
  unfold stepDerives
  exact exists_congr fun c => and_congr Iff.rfl <| exists_congr fun a =>
    and_congr Iff.rfl <| exists_congr fun v => and_congr Iff.rfl <| and_congr Iff.rfl <|
      forall_congr' fun b => forall_congr' fun _ => h _

private theorem derivesIn_of_stab {rules : List (HornClause Lg B k)} {N : ℕ}
    (hN : ∀ q : BAtom B A, derivesIn rules N q ↔ derivesIn rules (N + 1) q) :
    ∀ (s : ℕ) (q : BAtom B A), N ≤ s → (derivesIn rules s q ↔ derivesIn rules N q) := by
  intro s
  induction s with
  | zero =>
    intro q hq
    rw [Nat.le_zero.mp hq]
  | succ s ih =>
    intro q hs
    rcases Nat.lt_or_ge N (s + 1) with h | h
    · have hNs : N ≤ s := by omega
      constructor
      · rintro (h1 | h2)
        · exact (ih q hNs).mp h1
        · exact (hN q).mpr (Or.inr ((stepDerives_congr (fun r => ih r hNs) q).mp h2))
      · intro h1
        exact Or.inl ((ih q hNs).mpr h1)
    · have : N = s + 1 := le_antisymm hs h
      rw [this]

private theorem exists_stab [Finite A] (rules : List (HornClause Lg B k)) :
    ∃ N ≤ Nat.card (BAtom B A),
      ∀ q : BAtom B A, derivesIn rules N q ↔ derivesIn rules (N + 1) q := by
  obtain ⟨N, hN, heq⟩ := exists_succ_eq_of_monotone_subset
    (c := fun n => {q : BAtom B A | derivesIn rules n q}) fun n q hq => derivesIn_succ hq
  exact ⟨N, hN, fun q =>
    ⟨fun hq => (Set.ext_iff.mp heq q).mpr hq, fun hq => (Set.ext_iff.mp heq q).mp hq⟩⟩

/-- **The stages stabilize at the atom count**: after `Nat.card (BAtom B A)`
many rounds, being derivable within that many rounds is being derivable. -/
theorem derivesIn_iff_derives_of_card_le [Finite A] {rules : List (HornClause Lg B k)}
    {r : ℕ} (hr : Nat.card (BAtom B A) ≤ r) {q : BAtom B A} :
    derivesIn rules r q ↔ Derives rules q := by
  obtain ⟨N, hN, hstab⟩ := exists_stab (A := A) rules
  constructor
  · exact fun h => derives_iff_derivesIn.mpr ⟨r, h⟩
  · intro h
    obtain ⟨n, hn⟩ := derives_iff_derivesIn.mp h
    rcases Nat.lt_or_ge r n with hnr | hnr
    · exact (derivesIn_of_stab hstab r q (by omega)).mpr
        ((derivesIn_of_stab hstab n q (by omega)).mp hn)
    · exact derivesIn_le hnr hn

/-- **The certificate characterization**: a relation closed under the rules and
all of whose atoms are derived from strictly `≺`-earlier ones, for a
well-founded `≺`, *is* the least fixed point.

This is what makes the least fixed point testable by a positive formalism:
it is the shape a `Σ₁` certificate for FO(LFP) would check. (The translation
back into the Horn fragment, `DescriptiveComplexity.FixedPointHorn`, instead walks the
stages directly, through their stabilization
`DescriptiveComplexity.derivesIn_iff_derives_of_card_le` below.) -/
theorem derives_eq_of_closed_of_wf {rules : List (HornClause Lg B k)}
    {R : BAtom B A → Prop} {lt : BAtom B A → BAtom B A → Prop} (hwf : WellFounded lt)
    (hclosed : ∀ c ∈ rules, ∀ a : SOAtom B k, c.head = some a → ∀ v : Fin k → A,
      c.guard.Realize v →
        (∀ b ∈ c.body, R ⟨b.idx, fun j => v (b.args j)⟩) →
        R ⟨a.idx, fun j => v (a.args j)⟩)
    (hderiv : ∀ q, R q → ∃ c ∈ rules, ∃ a : SOAtom B k, c.head = some a ∧
      ∃ v : Fin k → A, q = ⟨a.idx, fun j => v (a.args j)⟩ ∧ c.guard.Realize v ∧
        ∀ b ∈ c.body, R (⟨b.idx, fun j => v (b.args j)⟩ : BAtom B A) ∧
          lt (⟨b.idx, fun j => v (b.args j)⟩ : BAtom B A) q) :
    ∀ q, R q ↔ Derives rules q := by
  have hsub : ∀ q, R q → Derives rules q := by
    intro q
    induction q using hwf.induction with
    | _ q ih =>
      intro hq
      obtain ⟨c, hc, a, ha, v, rfl, hg, hb⟩ := hderiv q hq
      exact Derives.rule hc ha hg fun b hbmem => ih _ (hb b hbmem).2 (hb b hbmem).1
  refine fun q => ⟨hsub q, fun hq => ?_⟩
  exact lfpAssign_least_of_closed (ρ := fun i x => R ⟨i, x⟩)
    (fun c hc a ha v hg hb => hclosed c hc a ha v hg hb) hq

end Stages

/-! ### The fixed point transports along isomorphisms -/

section Map

variable {Lg : Language.{0, 0}} {B : SOBlock} {k : ℕ}
variable {M N : Type} [Lg.Structure M] [Lg.Structure N]

/-- Derivability transports along an isomorphism of structures: the rules only
see the guards, which an isomorphism preserves. -/
private theorem derives_map (e : M ≃[Lg] N) {rules : List (HornClause Lg B k)}
    {q : BAtom B M} (h : Derives rules q) :
    Derives rules (⟨q.1, fun j => e (q.2 j)⟩ : BAtom B N) := by
  induction h with
  | @rule c hc a ha v hg hb ih =>
    refine Derives.rule hc ha (v := fun j => e (v j)) ?_ fun b hbmem => ih b hbmem
    exact (StrongHomClass.realize_formula e c.guard).mpr hg

/-- The least fixed point transports along an isomorphism. -/
private theorem lfpAssign_map (e : M ≃[Lg] N) (rules : List (HornClause Lg B k)) :
    lfpAssign (A := N) rules = B.mapAssign e.toEquiv (lfpAssign (A := M) rules) := by
  funext i x
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · have := derives_map e.symm h
    exact this
  · have h2 : Derives rules (⟨i, fun j => e (e.symm (x j))⟩ : BAtom B N) :=
      derives_map e (h : Derives rules ⟨i, fun j => e.symm (x j)⟩)
    have hx : (fun j => e (e.symm (x j))) = x := funext fun j => e.toEquiv.apply_symm_apply (x j)
    rw [hx] at h2
    exact h2

end Map

/-! ### The fixed point commutes with pullbacks

The least fixed point of the pulled rules is the pullback of the least fixed
point: both inclusions are an application of leastness, since each side is
closed under the other's rules (`DescriptiveComplexity.HornProgram.pull_holds`). This is
the fixed-point half of closure of `DescriptiveComplexity.LFPDefinable` under (ordered)
first-order reductions; what remains for that closure is to pull the *output*
sentence back, through `DescriptiveComplexity.FOInterpretation.extendSO` and
`DescriptiveComplexity.FOInterpretation.ordExtendLEquiv`, which is bookkeeping between
the three structures involved rather than mathematics. -/

section Pull

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational] {Tag : Type} [Finite Tag] {d : ℕ}
variable {B : SOBlock} {k : ℕ} {A : Type} [L₁.Structure A]

theorem lfpAssign_pull (I : FOInterpretation L₁ L₂ Tag d)
    (rules : List (HornClause L₂ B k)) :
    lfpAssign (HornProgram.pull I rules) = B.pullAssign (lfpAssign rules (A := I.Map A)) := by
  funext p x
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · -- the pulled fixed point is contained in the pullback of the fixed point
    refine lfpAssign_least_of_closed (ρ := B.pullAssign (lfpAssign rules (A := I.Map A)))
      (fun c' hc' a' ha' w hg hb => ?_) h
    obtain ⟨c, hc, t, rfl⟩ := HornProgram.pull_cases I hc'
    have hcl : (c.pull I t).Holds (B.pullAssign (lfpAssign rules (A := I.Map A))) w := by
      refine (HornClause.pull_holds I c t (lfpAssign rules (A := I.Map A)) w).mpr ?_
      cases hh : c.head with
      | none => exact absurd ha' (by simp [HornClause.pull, hh])
      | some a => exact lfpAssign_rule hc hh _
    have hhead := hcl ⟨hg, hb⟩
    rwa [HornClause.HeadHolds, ha', Option.elim_some] at hhead
  · -- and conversely, by leastness on the interpreted side
    set σ : (B.pull Tag d).Assignment A := lfpAssign (HornProgram.pull I rules) with hσ
    have hsub : ∀ q : Σ i : B.ι, Fin (B.arity i) → I.Map A,
        Derives (A := I.Map A) rules q → B.mergeAssign σ q.1 q.2 := by
      intro q hq
      refine lfpAssign_least_of_closed (A := I.Map A) (ρ := B.mergeAssign σ)
        (fun c hc a ha v hg hb => ?_) hq
      have hsplit := tagVal_split I v
      have hpull : (c.pull I (fun j => (v j).1)).Holds (B.pullAssign (B.mergeAssign σ))
          (fun m => (v (finProdFinEquiv.symm m).1).2 (finProdFinEquiv.symm m).2) := by
        rw [B.pullAssign_mergeAssign σ, hσ]
        exact lfpAssign_rule (HornProgram.pull_mem I hc _)
          (by rw [HornClause.pull, ha]; rfl) _
      rw [HornClause.pull_holds I c _ (B.mergeAssign σ) _, hsplit] at hpull
      have hhead := hpull ⟨hg, hb⟩
      unfold HornClause.HeadHolds at hhead
      rwa [ha, Option.elim_some] at hhead
    have key := congrFun (congrFun (B.pullAssign_mergeAssign σ) p) x
    exact key ▸ hsub ⟨p.1, fun kk => (p.2 kk, fun j => x (finProdFinEquiv (kk, j)))⟩ h

end Pull

/-! ### Definitions in FO(LFP) -/

/-- A definition in FO(LFP), in clausal normal form: a block of relation
variables, a list of rules defining them inductively, and a first-order output
sentence over the vocabulary expanded by the variables, read at the least fixed
point. -/
structure LFPDef (L : Language.{0, 0}) : Type 1 where
  /-- The relation variables computed by the fixed point. -/
  B : SOBlock
  /-- The number of first-order variables shared by the rules. -/
  k : ℕ
  /-- The rules defining the variables. Rules with no head derive nothing. -/
  rules : List (HornClause (L.sum Language.order) B k)
  /-- The first-order output, over the expanded vocabulary – *unrestricted*,
  in particular free to negate fixed-point atoms. -/
  out : ((L.sum Language.order).sum B.lang).Sentence

namespace LFPDef

variable {L : Language.{0, 0}} (d : LFPDef L)

/-- The value of a definition on a structure: the output read at the least
fixed point of the rules. -/
def Holds (A : Type) [L.Structure A] [LinearOrder A] : Prop :=
  @Sentence.Realize ((L.sum Language.order).sum d.B.lang) A
    (@sumStructure _ _ A _ (d.B.structure (lfpAssign d.rules))) d.out

/-- Negating the output complements the defined property: FO(LFP) is closed
under complement *by construction*, being a logic rather than a fragment. -/
private def not : LFPDef L :=
  { B := d.B, k := d.k, rules := d.rules, out := ∼d.out }

private theorem holds_not (A : Type) [L.Structure A] [LinearOrder A] :
    d.not.Holds A ↔ ¬d.Holds A :=
  Iff.rfl

end LFPDef

/-- **A certified fixed point can be used in place of the real one.** If `ρ`
is closed under the rules and every one of its atoms is derived from
`≺`-earlier ones, for a well-founded `≺`, then reading the output at `ρ` gives
the value of the definition.

This is the interface a `Σ₁` definition of an FO(LFP) definable problem would
consume: guess `ρ` and `≺` and check these conditions first-order, `≺` coming
from the stages (`DescriptiveComplexity.derives_step_of_depth`). The translation into
the Horn fragment (`DescriptiveComplexity.FixedPointHorn`) instead derives the stages
themselves. -/
theorem LFPDef.holds_iff_of_certificate {L : Language.{0, 0}} (d : LFPDef L) {A : Type}
    [L.Structure A] [LinearOrder A] {ρ : d.B.Assignment A}
    {lt : BAtom d.B A → BAtom d.B A → Prop} (hwf : WellFounded lt)
    (hclosed : ∀ c ∈ d.rules, ∀ a : SOAtom d.B d.k, c.head = some a →
      ∀ v : Fin d.k → A, c.guard.Realize v → (∀ b ∈ c.body, b.Holds ρ v) → a.Holds ρ v)
    (hderiv : ∀ q : BAtom d.B A, ρ q.1 q.2 → ∃ c ∈ d.rules, ∃ a : SOAtom d.B d.k,
      c.head = some a ∧ ∃ v : Fin d.k → A, q = ⟨a.idx, fun j => v (a.args j)⟩ ∧
        c.guard.Realize v ∧ ∀ b ∈ c.body,
          ρ b.idx (fun j => v (b.args j)) ∧
            lt (⟨b.idx, fun j => v (b.args j)⟩ : BAtom d.B A) q) :
    d.Holds A ↔
      @Sentence.Realize ((L.sum Language.order).sum d.B.lang) A
        (@sumStructure _ _ A _ (d.B.structure ρ)) d.out := by
  have heq : ρ = lfpAssign d.rules := by
    funext i x
    exact propext (derives_eq_of_closed_of_wf hwf hclosed hderiv ⟨i, x⟩)
  rw [heq]
  exact Iff.rfl

/-- A decision problem is *FO(LFP) definable* if, on nonempty finite ordered
structures, it is the value of a definition in FO(LFP). As for
`DescriptiveComplexity.SigmaSOHornDefinable`, the equivalence is required for every
linear order, so the notion is order-invariant – and, as there, the order is
genuinely needed: it is the setting of the capture theorem, and no guess
replaces it the way one does for SO(TC)
(`DescriptiveComplexity.sotcDefinable_iff_free`). -/
def LFPDefinable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ d : LFPDef L, ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ d.Holds A

/-- **FO(LFP) definability is closed under complement.** This is the one line
that the Horn fragment cannot supply, and the reason to have the logic at all:
negate the output formula.
Registered in the Lax archive as
[`Lax535992.LeastFixedPointComplement.lfpDefinable_compl`](https://laxarchive.org/lax-535992/Lax535992.LeastFixedPointComplement.html#s-Lax535992.LeastFixedPointComplement.lfpDefinable_compl). -/
theorem LFPDefinable.compl {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : LFPDefinable P) : LFPDefinable Pᶜ := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d.not, ?_⟩
  intro A _ _ _ _
  exact (not_congr (hd A)).trans (d.holds_not A).symm

/-! ### SO-Horn definitions are FO(LFP) definitions

A Horn program splits into its *rules* (the clauses with a head), which define
the fixed point, and its *goal clauses* (those without), which merely say that
the fixed point avoids certain configurations – a first-order statement about
it, and so exactly what an output formula can express. -/

section OfHorn

variable {L : Language.{0, 0}} {B : SOBlock} {k : ℕ}

/-- The symbol of a relation variable of the block. -/
abbrev varSym (B : SOBlock) (i : B.ι) : B.lang.Relations (B.arity i) := ⟨i, rfl⟩

/-- The symbol of a relation variable, in the expanded vocabulary. -/
abbrev varOutSym (L : Language.{0, 0}) (B : SOBlock) (i : B.ι) :
    ((L.sum Language.order).sum B.lang).Relations (B.arity i) :=
  Sum.inr (varSym B i)

/-- A second-order atom, as a first-order atom over the expanded
vocabulary. -/
noncomputable def atomF (a : SOAtom B k) :
    ((L.sum Language.order).sum B.lang).Formula (Empty ⊕ Fin k) :=
  Relations.formula (varOutSym L B a.idx) fun j => Term.var (Sum.inr (a.args j))

/-- A guard, transported to the expanded vocabulary. -/
noncomputable def guardOutF (φ : (L.sum Language.order).Formula (Fin k)) :
    ((L.sum Language.order).sum B.lang).Formula (Empty ⊕ Fin k) :=
  (LHom.sumInl.onFormula φ).relabel Sum.inr

/-- A goal clause, as the first-order statement that it never fires. -/
noncomputable def goalOutF (c : HornClause (L.sum Language.order) B k) :
    ((L.sum Language.order).sum B.lang).Sentence :=
  (show ((L.sum Language.order).sum B.lang).Formula (Empty ⊕ Fin k) from
    ∼(guardOutF c.guard ⊓ listInf (c.body.map atomF))).iAlls (Fin k)

/-- The output formula of the translation: no goal clause of the program ever
fires at the fixed point. -/
noncomputable def hornOutF (prog : HornProgram (L.sum Language.order) B k) :
    ((L.sum Language.order).sum B.lang).Sentence :=
  listInf ((prog.filter fun c => c.head.isNone).map goalOutF)

section Realize

variable {A : Type} [L.Structure A] [LinearOrder A] (ρ : B.Assignment A)

private theorem realize_atomF (a : SOAtom B k) (v : (Empty ⊕ Fin k) → A) :
    (@Formula.Realize ((L.sum Language.order).sum B.lang) A
        (@sumStructure _ _ A _ (B.structure ρ)) _ (atomF a) v) ↔
      a.Holds ρ fun j => v (Sum.inr j) := by
  let := B.structure ρ
  rw [atomF, Formula.realize_rel]
  exact Iff.rfl

private theorem realize_guardOutF (φ : (L.sum Language.order).Formula (Fin k))
    (v : (Empty ⊕ Fin k) → A) :
    (@Formula.Realize ((L.sum Language.order).sum B.lang) A
        (@sumStructure _ _ A _ (B.structure ρ)) _ (guardOutF φ) v) ↔
      φ.Realize fun j => v (Sum.inr j) := by
  let := B.structure ρ
  rw [guardOutF, Formula.realize_relabel, LHom.realize_onFormula]
  rfl

private theorem realize_goalOutF (c : HornClause (L.sum Language.order) B k) :
    (@Sentence.Realize ((L.sum Language.order).sum B.lang) A
        (@sumStructure _ _ A _ (B.structure ρ)) (goalOutF c)) ↔
      ∀ v : Fin k → A, ¬(c.guard.Realize v ∧ ∀ b ∈ c.body, b.Holds ρ v) := by
  let := B.structure ρ
  rw [goalOutF]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_not,
    Formula.realize_inf, realize_guardOutF ρ, realize_listInf]
  refine ⟨fun h v hv => h (fun j => v j) ⟨hv.1, fun ψ hψ => ?_⟩,
    fun h i hi => h (fun j => i j) ⟨hi.1, fun b hb => ?_⟩⟩
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hψ
    exact (realize_atomF ρ b _).mpr (hv.2 b hb)
  · exact (realize_atomF ρ b _).mp (hi.2 _ (List.mem_map_of_mem hb))

private theorem realize_hornOutF (prog : HornProgram (L.sum Language.order) B k) :
    (@Sentence.Realize ((L.sum Language.order).sum B.lang) A
        (@sumStructure _ _ A _ (B.structure ρ)) (hornOutF prog)) ↔
      ∀ c ∈ prog, c.head = none →
        ∀ v : Fin k → A, ¬(c.guard.Realize v ∧ ∀ b ∈ c.body, b.Holds ρ v) := by
  let := B.structure ρ
  rw [hornOutF]
  simp only [Sentence.Realize, realize_listInf]
  constructor
  · intro h c hc hnone
    exact (realize_goalOutF ρ c).mp
      (h _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hc, by rw [hnone]; rfl⟩)))
  · intro h ψ hψ
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hψ
    obtain ⟨hcp, hnone⟩ := List.mem_filter.mp hc
    exact (realize_goalOutF ρ c).mpr (h c hcp (Option.isNone_iff_eq_none.mp hnone))

end Realize

/-- **Every SO-Horn definition is an FO(LFP) definition**: keep the rules,
and turn the goal clauses into the output formula.
Registered in the Lax archive as
[`Lax535992.HornIsLeastFixedPoint.sigmaSOHornDefinable_lfpDefinable`](https://laxarchive.org/lax-535992/Lax535992.HornIsLeastFixedPoint.html#s-Lax535992.HornIsLeastFixedPoint.sigmaSOHornDefinable_lfpDefinable). -/
theorem SigmaSOHornDefinable.lfpDefinable [L.IsRelational] {P : DecisionProblem L}
    (h : SigmaSOHornDefinable P) : LFPDefinable P := by
  obtain ⟨B, k, prog, hprog⟩ := h
  refine ⟨⟨B, k, prog, hornOutF prog⟩, ?_⟩
  intro A _ _ _ _
  refine (hprog A).trans ⟨?_, ?_⟩
  · rintro ⟨ρ, hρ⟩
    refine (realize_hornOutF (lfpAssign prog) prog).mpr fun c hc hnone v ⟨hg, hb⟩ => ?_
    have hsub : ∀ b : SOAtom B k, b.Holds (lfpAssign prog) v → b.Holds ρ v := fun b hbv =>
      lfpAssign_least (p := ⟨b.idx, fun j => v (b.args j)⟩) hρ hbv
    have := hρ v c hc ⟨hg, fun b hbmem => hsub b (hb b hbmem)⟩
    rw [HornClause.HeadHolds, hnone, Option.elim_none] at this
    exact this
  · intro hout
    refine ⟨lfpAssign prog, fun v c hc => ?_⟩
    cases hh : c.head with
    | some a => exact lfpAssign_rule hc hh v
    | none =>
      intro hpre
      exact absurd hpre ((realize_hornOutF (lfpAssign prog) prog).mp hout c hc hh v)

/-- The complements of the SO-Horn definable problems are FO(LFP) definable
too – which is what the Horn fragment on its own cannot say. -/
theorem SigmaSOHornDefinable.compl_lfpDefinable [L.IsRelational] {P : DecisionProblem L}
    (h : SigmaSOHornDefinable Pᶜ) : LFPDefinable P := by
  have h2 := (SigmaSOHornDefinable.lfpDefinable h).compl
  rwa [DecisionProblem.compl_compl] at h2

end OfHorn

/-! ### Closure under reductions -/

section Closure

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
variable {P : DecisionProblem L₁} {Q : DecisionProblem L₂}

/-- **FO(LFP) definability is closed under ordered first-order reductions.**
The rules pull back as a Horn program and their fixed point commutes with the
pullback (`DescriptiveComplexity.lfpAssign_pull`); the output sentence pulls back through
`DescriptiveComplexity.FOInterpretation.extendSO`, the two views of the interpreted
structure being identified by
`DescriptiveComplexity.FOInterpretation.extendSOEquiv` and
`DescriptiveComplexity.FOInterpretation.ordExtendLEquiv`. -/
theorem LFPDefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q) (h : LFPDefinable Q) :
    LFPDefinable P := by
  obtain ⟨d, hd⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  refine ⟨⟨d.B.pull f.Tag f.dim, d.k * f.dim,
    HornProgram.pull f.toInterpretation.ordExtend d.rules,
    (f.toInterpretation.ordExtend.extendSO d.B).pullSentence d.out⟩, ?_⟩
  intro A _ _ _ _
  let := f.toInterpretation.mapLinearOrder A
  have := f.toInterpretation.map_finite A
  have := f.toInterpretation.map_nonempty A
  refine (f.correct A).trans ((hd (f.toInterpretation.Map A)).trans ?_)
  rw [LFPDef.Holds, LFPDef.Holds, lfpAssign_pull f.toInterpretation.ordExtend d.rules]
  let := (d.B.pull f.Tag f.dim).structure
    (d.B.pullAssign (lfpAssign (A := f.toInterpretation.ordExtend.Map A) d.rules))
  have e₁ := f.toInterpretation.ordExtend.extendSOEquiv d.B A
    (lfpAssign (A := f.toInterpretation.ordExtend.Map A) d.rules)
  have e₂ := d.B.extendEquiv (f.toInterpretation.ordExtendLEquiv A)
    (lfpAssign (A := f.toInterpretation.ordExtend.Map A) d.rules)
  rw [← lfpAssign_map (f.toInterpretation.ordExtendLEquiv A) d.rules] at e₂
  let : ((L₂.sum Language.order).sum d.B.lang).Structure
      ((f.toInterpretation.ordExtend.extendSO d.B).Map A) :=
    FOInterpretation.mapStructure (f.toInterpretation.ordExtend.extendSO d.B) A
  let : ((L₂.sum Language.order).sum d.B.lang).Structure
      (f.toInterpretation.ordExtend.Map A) :=
    @sumStructure (L₂.sum Language.order) d.B.lang (f.toInterpretation.ordExtend.Map A)
      (FOInterpretation.mapStructure f.toInterpretation.ordExtend A)
      (d.B.structure (lfpAssign d.rules))
  let : ((L₂.sum Language.order).sum d.B.lang).Structure (f.toInterpretation.Map A) :=
    @sumStructure (L₂.sum Language.order) d.B.lang (f.toInterpretation.Map A) _
      (d.B.structure (lfpAssign d.rules))
  have hout := StrongHomClass.realize_sentence
    (L := (L₂.sum Language.order).sum d.B.lang) (e₂.comp e₁) d.out
  have hpull := (f.toInterpretation.ordExtend.extendSO d.B).realize_pullSentence d.out A
  exact (hpull.trans hout).symm

end Closure

end DescriptiveComplexity
