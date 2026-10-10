/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import LeanPool.ScottMeasurement.Probability.Finite

/-!
# The Kraft–Pratt–Seidenberg five-atom counterexample

This file formalizes the simple ordering displayed in Section 4 of
Kraft–Pratt–Seidenberg, *Intuitive Probability on Finite Sets* (1959).
The five atoms `p q r s t` are represented by `0 1 2 3 4 : Fin 5`.

The rank table below is the paper's displayed order, from the empty event
through the full event.  Its four decisive comparisons are

`qs < p`, `pq < rs`, `ps < tq`, and `rt < spq`.

The finite de Finetti properties are checked by evaluating all events.
The non-representability argument itself is symbolic: finite additivity
turns the four strict event comparisons into four incompatible linear
inequalities between singleton weights.
-/

@[expose] public section

namespace Scott1964.MeasurementStructures.Probability.KPSCounterexample

/-- The five outcomes in the Kraft--Pratt--Seidenberg example. -/
abbrev Atom := Fin 5
/-- Events are subsets of the five outcomes. -/
abbrev Event := Finset Atom

/-- Outcome `p` in the notation of the original rank table. -/
def p : Atom := 0
/-- Outcome `q` in the notation of the original rank table. -/
def q : Atom := 1
/-- Outcome `r` in the notation of the original rank table. -/
def r : Atom := 2
/-- Outcome `s` in the notation of the original rank table. -/
def s : Atom := 3
/-- Outcome `t` in the notation of the original rank table. -/
def t : Atom := 4

/-- Binary code for an event, with `p q r s t` as bits `0 1 2 3 4`. -/
def eventCode (A : Event) : Nat :=
  ∑ i ∈ A, 2 ^ i.val

/-- Position in the strict 32-event order printed by KPS. -/
def kpsRank (A : Event) : Nat :=
  match eventCode A with
  | 0  => 0   -- 1 (the empty event)
  | 2  => 1   -- q
  | 4  => 2   -- r
  | 8  => 3   -- s
  | 6  => 4   -- qr
  | 10 => 5   -- qs
  | 1  => 6   -- p
  | 3  => 7   -- pq
  | 12 => 8   -- rs
  | 16 => 9   -- t
  | 14 => 10  -- qrs
  | 5  => 11  -- rp
  | 9  => 12  -- ps
  | 18 => 13  -- tq
  | 7  => 14  -- qrp
  | 20 => 15  -- rt
  | 11 => 16  -- spq
  | 24 => 17  -- st
  | 13 => 18  -- rsp
  | 22 => 19  -- qrt
  | 26 => 20  -- qst
  | 17 => 21  -- pt
  | 15 => 22  -- qrsp
  | 19 => 23  -- qpt
  | 28 => 24  -- rst
  | 30 => 25  -- qrst
  | 21 => 26  -- rpt
  | 25 => 27  -- spt
  | 23 => 28  -- qrpt
  | 27 => 29  -- qspt
  | 29 => 30  -- rspt
  | 31 => 31  -- pqrst
  | _  => 0   -- unreachable for an event on five atoms

/-- The weak comparison induced by the original 32-event rank table. -/
def KPSLe (A B : Event) : Prop := kpsRank A ≤ kpsRank B
/-- The strict comparison induced by the original 32-event rank table. -/
def KPSLt (A B : Event) : Prop := kpsRank A < kpsRank B

/-- The KPS order oriented as “at least as probable”, matching the shared
qualitative-probability API. -/
def KPSGe (A B : Event) : Prop := KPSLe B A

instance : DecidableRel KPSLe := by
  intro A B
  unfold KPSLe
  infer_instance

instance : DecidableRel KPSLt := by
  intro A B
  unfold KPSLt
  infer_instance

instance : DecidableRel KPSGe := by
  intro A B
  unfold KPSGe
  infer_instance

/-- The table gives distinct ranks to all 32 events. -/
theorem kpsRank_injective : Function.Injective kpsRank := by
  decide +kernel +revert

/-- Comparability (C). -/
theorem comparable (A B : Event) : KPSLe A B ∨ KPSLe B A := by
  simp only [KPSLe]
  omega

/-- Transitivity (T). -/
theorem transitive {A B C : Event} :
    KPSLe A B → KPSLe B C → KPSLe A C := by
  simp only [KPSLe]
  omega

/-- The empty event is no more likely than every event. -/
theorem empty_le (A : Event) : KPSLe ∅ A := by
  exact Nat.zero_le _

private theorem insert_invariance (A B : Event) (a : Atom)
    (haA : a ∉ A) (haB : a ∉ B) :
    KPSLe A B ↔ KPSLe (insert a A) (insert a B) := by
  decide +kernel +revert

/-- De Finetti's disjoint-union invariance (A). The finite check only concerns
inserting one atom; induction gives arbitrary disjoint unions. -/
theorem disjoint_union_invariance (A B C : Event)
    (hCA : Disjoint C A) (hCB : Disjoint C B) :
    KPSLe A B ↔ KPSLe (A ∪ C) (B ∪ C) := by
  induction C using Finset.induction_on with
  | empty => simp
  | @insert a C ha ih =>
      rw [Finset.disjoint_insert_left] at hCA hCB
      have haAC : a ∉ A ∪ C := by simp [hCA.1, ha]
      have haBC : a ∉ B ∪ C := by simp [hCB.1, ha]
      exact (ih hCA.2 hCB.2).trans (by
        simpa [Finset.union_insert] using insert_invariance (A ∪ C) (B ∪ C) a haAC haBC)

theorem qs_lt_p : KPSLt {q, s} {p} := by decide +kernel
theorem pq_lt_rs : KPSLt {p, q} {r, s} := by decide +kernel
theorem ps_lt_tq : KPSLt {p, s} {t, q} := by decide +kernel
theorem rt_lt_spq : KPSLt {r, t} {s, p, q} := by decide +kernel

/-- Finite additivity determines every event from its singleton values. -/
theorem measure_eq_sum_singletons {μ : Event → ℝ}
    (hμ : IsProbability μ) (A : Event) :
    μ A = ∑ i ∈ A, μ {i} := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      simpa using hμ.bot
  | @insert a A ha ih =>
      calc
        μ (insert a A) = μ ({a} ∪ A) := by rw [Finset.singleton_union]
        _ = μ {a} + μ A := hμ.additive _ _
          (Finset.disjoint_singleton_left.mpr ha)
        _ = μ {a} + ∑ i ∈ A, μ {i} := by rw [ih]
        _ = ∑ i ∈ insert a A, μ {i} := by simp [ha]

/-- Strict numerical representation of the KPS strict order. -/
def StrictlyRepresents (μ : Event → ℝ) : Prop :=
  ∀ A B, KPSLt A B ↔ μ A < μ B

/--
No real finitely additive probability strictly represents the displayed
Kraft–Pratt–Seidenberg order.
-/
theorem no_strictly_representing_probability :
    ¬ ∃ μ : Event → ℝ,
      IsProbability μ ∧ StrictlyRepresents μ := by
  rintro ⟨μ, hμ, hrep⟩
  have h1 : μ {q, s} < μ {p} := (hrep _ _).mp qs_lt_p
  have h2 : μ {p, q} < μ {r, s} := (hrep _ _).mp pq_lt_rs
  have h3 : μ {p, s} < μ {t, q} := (hrep _ _).mp ps_lt_tq
  have h4 : μ {r, t} < μ {s, p, q} := (hrep _ _).mp rt_lt_spq
  rw [measure_eq_sum_singletons hμ, measure_eq_sum_singletons hμ] at h1
  rw [measure_eq_sum_singletons hμ, measure_eq_sum_singletons hμ] at h2
  rw [measure_eq_sum_singletons hμ, measure_eq_sum_singletons hμ] at h3
  rw [measure_eq_sum_singletons hμ, measure_eq_sum_singletons hμ] at h4
  simp [p, q, r, s, t] at h1 h2 h3 h4
  linarith

theorem kpsGe_nontrivial : ¬KPSGe (⊥ : Event) ⊤ := by
  decide +kernel

theorem kpsGe_bottom (A : Event) : KPSGe A ⊥ :=
  empty_le A

theorem kpsGe_total : ProbTotal KPSGe := by
  intro A B
  exact (comparable B A).imp id id

theorem kpsGe_transitive : ProbTransitive KPSGe := by
  intro A B C hAB hBC
  exact transitive hBC hAB

theorem kpsGe_disjointUnionInvariant :
    ProbDisjointUnionInvariant KPSGe := by
  intro A B C hCA hCB
  exact disjoint_union_invariance (A := B) (B := A) (C := C) hCB hCA

/-- The exact KPS order satisfies de Finetti's five axioms, with condition
(i) in its original weak form `¬ R ⊥ ⊤`. -/
theorem kpsGe_deFinettiAxioms : DeFinettiAxioms KPSGe where
  nontrivial := kpsGe_nontrivial
  bottom := kpsGe_bottom
  total := kpsGe_total
  transitive := kpsGe_transitive
  disjointUnionInvariant := kpsGe_disjointUnionInvariant

theorem measure_strict_of_kpsLt {μ : Event → ℝ}
    (hrep : ∀ A B, KPSGe A B ↔ μ A ≥ μ B)
    {A B : Event} (hAB : KPSLt A B) :
    μ A < μ B := by
  have hBA : KPSGe B A := by
    exact hAB.le
  have hnAB : ¬KPSGe A B := by
    simp only [KPSGe, KPSLe, KPSLt] at hAB ⊢
    omega
  have hle := (hrep B A).1 hBA
  have hnle : ¬μ A ≥ μ B := fun h ↦ hnAB ((hrep A B).2 h)
  linarith

/-- No shared-API probability weakly represents the exact KPS “at least as
probable” order.  The contradiction uses the paper's four decisive
inequalities. -/
theorem not_realizableProbability_kpsGe :
    ¬RealizableProbability KPSGe := by
  rintro ⟨μ, hμ, hrep⟩
  apply no_strictly_representing_probability
  refine ⟨μ, hμ, fun A B ↦ ?_⟩
  constructor
  · exact measure_strict_of_kpsLt hrep
  · intro hlt
    by_contra hnot
    have hge : KPSGe A B := Nat.le_of_not_gt hnot
    exact (not_lt_of_ge ((hrep A B).mp hge)) hlt

/-- De Finetti's five axioms are insufficient for finite additive-probability
representation. -/
theorem deFinetti_axioms_insufficient :
    DeFinettiAxioms KPSGe ∧ ¬RealizableProbability KPSGe :=
  ⟨kpsGe_deFinettiAxioms, not_realizableProbability_kpsGe⟩

end Scott1964.MeasurementStructures.Probability.KPSCounterexample
