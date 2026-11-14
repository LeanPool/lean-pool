/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# RandomScaleWitness

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The random minimal scale as an `ℕ∞`-valued witness

A *bad-window predicate* is a family `bad : ℕ → Ω → Prop`, where `bad n ω` says
that the window of length `n` is bad for the sample `ω`.  The associated
**random minimal scale** is

`minimalScale bad ω = ⨆ (n) (_ : bad n ω), (n + 1)`,

taken in the complete lattice `ℕ∞ = WithTop ℕ`.  Working in `ℕ∞` rather than `ℕ` is what
makes the *domination* property "every bad window length is `< Z`" hold for **every** `ω`
with no boundedness hypothesis: `le_iSup` needs none in a complete lattice.  Consequently
the deterministic extraction `minimalScaleEN_not_bad_of_le` is a genuine, `ω`-uniform fact
— vacuous precisely on the `⊤`-event where bad windows of unbounded length occur.

## Contents

* `minimalScaleEN` — the witness.
* `minimalScaleEN_not_bad_of_le` and `minimalScaleEN_tail_eq` — its two
  deterministic extractions.
* `minimalScaleEN_tail_subset` — the tail-event inclusion used by summation.
* `minimalScaleEN_sup` — the witness for a disjunction is the pointwise maximum.
* `measurable_minimalScaleEN` — measurability from measurable bad-window events.

Everything is generic over the sample space `Ω`: no source-specific carrier and
no measure appears in this module.
-/

namespace Algsuperdiff.Probability

open MeasureTheory

section Witness

variable {Ω : Type*}

/-- **The random minimal scale**, `ℕ∞`-valued: `minimalScale bad ω = ⨆ (n) (_ : bad
n ω), (n + 1)`.  It is `0` when no window is bad, and `⊤` when bad windows of
unbounded length occur. -/
noncomputable def minimalScaleEN (bad : ℕ → Ω → Prop) (ω : Ω) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : bad n ω), ((n : ℕ∞) + 1)

/-- The successor cast identity in `ℕ∞`, used to compare the summands
`(n : ℕ∞) + 1` with the `ℕ`-casts appearing in the tail events. -/
private theorem enat_cast_succ (n : ℕ) : ((n : ℕ∞) + 1) = ((n + 1 : ℕ) : ℕ∞) := by
  rw [Nat.cast_add, Nat.cast_one]

/-- **Deterministic extraction.**  If the random scale is at most the window length
`L`, then the window of length `L` is *not* bad.  (Vacuous when `minimalScale
bad ω = ⊤`, since then no finite `L` bounds it.) -/
theorem minimalScaleEN_not_bad_of_le {bad : ℕ → Ω → Prop} {ω : Ω} {L : ℕ}
    (h : minimalScaleEN bad ω ≤ (L : ℕ∞)) : ¬ bad L ω := by
  intro hbad
  have hle : ((L : ℕ∞) + 1) ≤ minimalScaleEN bad ω :=
    le_iSup₂ (f := fun n (_ : bad n ω) => (n : ℕ∞) + 1) L hbad
  have hcontra : ((L : ℕ∞) + 1) ≤ (L : ℕ∞) := le_trans hle h
  rw [enat_cast_succ L] at hcontra
  rw [ENat.natCast_le_natCast] at hcontra
  omega

/-- **The tail event of the minimal scale is exactly a union of bad windows.**
Since `minimalScale bad ω = ⨆ (l) (_ : bad l ω), (l + 1)`, the event `{N + 1 ≤
Z}` says that some bad window has length `≥ N`.  Note the index shift: the
union starts at `N`, not at `N + 1`. -/
theorem minimalScaleEN_tail_eq (bad : ℕ → Ω → Prop) (N : ℕ) :
    {ω | ((N + 1 : ℕ) : ℕ∞) ≤ minimalScaleEN bad ω} = ⋃ i : ℕ, {ω | bad (N + i) ω} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro hω
    by_contra hcon
    push Not at hcon
    have hbound : minimalScaleEN bad ω ≤ ((N : ℕ) : ℕ∞) := by
      refine iSup_le fun n => iSup_le fun hbad => ?_
      have hlt : n < N := by
        by_contra hnl
        push Not at hnl
        exact hcon (n - N) (by rwa [Nat.add_sub_cancel' hnl])
      rw [enat_cast_succ n, ENat.natCast_le_natCast]
      omega
    have hcontra : ((N + 1 : ℕ) : ℕ∞) ≤ ((N : ℕ) : ℕ∞) := le_trans hω hbound
    rw [ENat.natCast_le_natCast] at hcontra
    omega
  · rintro ⟨i, hi⟩
    refine le_trans ?_ (le_iSup₂ (f := fun n (_ : bad n ω) => (n : ℕ∞) + 1) (N + i) hi)
    rw [enat_cast_succ (N + i), ENat.natCast_le_natCast]
    omega

/-- **The tail event of the minimal scale is contained in a union of bad
windows** — the half consumed by the geometric summation. -/
theorem minimalScaleEN_tail_subset (bad : ℕ → Ω → Prop) (N : ℕ) :
    {ω | ((N + 1 : ℕ) : ℕ∞) ≤ minimalScaleEN bad ω} ⊆ ⋃ i : ℕ, {ω | bad (N + i) ω} :=
  (minimalScaleEN_tail_eq bad N).subset

/-- **The maximum of two witnesses is the witness of the disjunction.**  This is
the assembly rule for a scale built from two independent families of bad
windows. -/
theorem minimalScaleEN_sup (bad₁ bad₂ : ℕ → Ω → Prop) (ω : Ω) :
    minimalScaleEN (fun n ω => bad₁ n ω ∨ bad₂ n ω) ω
      = max (minimalScaleEN bad₁ ω) (minimalScaleEN bad₂ ω) := by
  refine le_antisymm (iSup_le fun n => iSup_le fun h => ?_) (max_le ?_ ?_)
  · rcases h with h | h
    · exact le_max_of_le_left (le_iSup₂ (f := fun n (_ : bad₁ n ω) => (n : ℕ∞) + 1) n h)
    · exact le_max_of_le_right (le_iSup₂ (f := fun n (_ : bad₂ n ω) => (n : ℕ∞) + 1) n h)
  · exact iSup_le fun n => iSup_le fun h =>
      le_iSup₂ (f := fun n (_ : bad₁ n ω ∨ bad₂ n ω) => (n : ℕ∞) + 1) n (Or.inl h)
  · exact iSup_le fun n => iSup_le fun h =>
      le_iSup₂ (f := fun n (_ : bad₁ n ω ∨ bad₂ n ω) => (n : ℕ∞) + 1) n (Or.inr h)

end Witness

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Measurability of the `ℕ∞`-tail events.**  If every bad-window event is
measurable, then so is every tail event `{(N : ℕ∞) ≤ Z}` of the witness. -/
theorem measurableSet_minimalScaleEN_tail {bad : ℕ → Ω → Prop}
    (hbad : ∀ n, MeasurableSet {ω | bad n ω}) (N : ℕ) :
    MeasurableSet {ω | (N : ℕ∞) ≤ minimalScaleEN bad ω} := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have huniv : {ω : Ω | ((0 : ℕ) : ℕ∞) ≤ minimalScaleEN bad ω} = Set.univ :=
      Set.eq_univ_of_forall fun ω => by
        simp only [Set.mem_ofPred_eq, Nat.cast_zero]
        exact zero_le
    rw [huniv]
    exact MeasurableSet.univ
  · obtain ⟨M, rfl⟩ : ∃ M : ℕ, N = M + 1 := ⟨N - 1, by omega⟩
    rw [minimalScaleEN_tail_eq]
    exact MeasurableSet.iUnion fun i => hbad (M + i)

/-- **The measurability criterion for the random minimal scale.**

If every bad-window event `{ω | bad n ω}` is measurable, then the witness
`minimalScale bad` is measurable as a map into `ℕ∞`.

The mechanism: `{Z = n}` is the difference of the two tail events `{n ≤ Z}` and
`{n + 1 ≤ Z}`, each of which is a countable union of bad-window events; the
`⊤`-fibre is then automatic because `ℕ∞` is countable. -/
theorem measurable_minimalScaleEN {bad : ℕ → Ω → Prop}
    (hbad : ∀ n, MeasurableSet {ω | bad n ω}) :
    Measurable (minimalScaleEN bad) := by
  refine ENat.measurable_iff.mpr fun n => ?_
  have hset : minimalScaleEN bad ⁻¹' {((n : ℕ) : ℕ∞)}
      = {ω | ((n : ℕ) : ℕ∞) ≤ minimalScaleEN bad ω}
        \ {ω | ((n + 1 : ℕ) : ℕ∞) ≤ minimalScaleEN bad ω} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
    constructor
    · refine fun h => ⟨h.ge, fun hcon => ?_⟩
      rw [h, ENat.natCast_le_natCast] at hcon
      omega
    · rintro ⟨h1, h2⟩
      have hlt : minimalScaleEN bad ω < ((n : ℕ∞) + 1) := by
        rw [enat_cast_succ n]
        exact not_le.mp h2
      exact le_antisymm ((ENat.lt_add_one_iff (ENat.natCast_ne_top n)).mp hlt) h1
  rw [hset]
  exact (measurableSet_minimalScaleEN_tail hbad n).diff
    (measurableSet_minimalScaleEN_tail hbad (n + 1))

end Measurability

end Algsuperdiff.Probability
