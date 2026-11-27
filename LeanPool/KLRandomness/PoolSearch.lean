/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PoolAdviceComputable
public import Mathlib.Computability.PartrecCode
import Mathlib.Tactic.Tauto

/-!
# The fixed-advice pool-producing program

For each fixed finite family of scans and each fixed finite advice record,
there is a single partial-recursive program taking only the requested pool
size M. It enumerates pairs consisting of a finite pool and a finite horizon,
and returns the first pair passing all three exact rational tests.

The equivalence between halting and existence of an accepted candidate is
unconditional. The analytic argument must separately establish that accepted
candidates exist for sufficiently large M; that condition is not built into
the computation as an oracle or a computability assumption.
-/

@[expose] public section

namespace Klr.PoolAdvice

open SparseSearch SparseListSearch RationalComputability

/-- A bounded duplicate test, checking that every listed value occurs once. -/
def nodupCheck (G : List ℕ) : Bool :=
  G.all fun a => decide (G.countP (fun b => decide (b = a)) = 1)

theorem nodupCheck_eq_true (G : List ℕ) : nodupCheck G = true ↔ G.Nodup := by
  simpa only [nodupCheck, List.all_eq_true, decide_eq_true_eq, List.count,
    Bool.beq_eq_decide_eq] using (List.nodup_iff_count_eq_one (l := G)).symm

theorem computable_nodupCheck : Computable nodupCheck := by
  have he : Computable (fun p : (List ℕ × ℕ) × ℕ => decide (p.2 = p.1.2)) :=
    Primrec.eq.decide.to_comp.comp Computable.snd (Computable.snd.comp Computable.fst)
  have hc := computable_list_countP (p := fun p : List ℕ × ℕ => fun b => decide (b = p.2))
    Computable.fst he
  have hb := Primrec.eq.decide.to_comp.comp hc (Computable.const 1)
  exact computable_list_all
    (p := fun (G : List ℕ) (a : ℕ) => decide (G.countP (fun b => decide (b = a)) = 1))
    Computable.id hb

/-- The exact finite verifier for an M-element pool and a finite horizon. -/
def check (rules : List ScanRule) (A : Advice) (M : ℕ) (C : Candidate) : Bool :=
  decide (C.1.length = M) && nodupCheck C.1 &&
  C.1.all (fun a => decide (A.positionBound ≤ a)) &&
  EffectiveScan.boundedAll (fun i => decide (highMiss rules A C.1 C.2 i < 3 * A.error))
    A.protectedCount &&
  EffectiveScan.boundedAll (fun i => decide (distance rules A C.1 C.2 i < 3 * A.error))
    A.protectedCount &&
  decide (A.threshold < weightedMass rules A C.1 C.2)

theorem check_eq_true (rules : List ScanRule) (A : Advice) (M : ℕ) (C : Candidate) :
    check rules A M C = true ↔ Accepted rules A M C := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, nodupCheck_eq_true,
    List.all_eq_true, EffectiveScan.boundedAll_eq_true, Accepted]
  tauto

/-- The scans and advice are constants of this total computable verifier. -/
theorem computable_check (rules : List ScanRule) (A : Advice) :
    Computable₂ (check rules A) := by
  have hG : Computable (fun p : ℕ × Candidate => p.2.1) :=
    Computable.fst.comp Computable.snd
  have hs := Primrec.eq.decide.to_comp.comp (Computable.list_length.comp hG) Computable.fst
  have hd := computable_nodupCheck.comp hG
  have hb := computable_list_all (p := fun (_ : ℕ × Candidate) a => decide (A.positionBound ≤ a))
    hG (Primrec.nat_le.decide.to_comp.comp (Computable.const A.positionBound) Computable.snd)
  have hpair : Computable (fun p : (ℕ × Candidate) × ℕ => (p.1.2, p.2)) :=
    (Computable.snd.comp Computable.fst).pair Computable.snd
  have hh := computable_rat_lt.comp ((computable_highMiss rules A).comp hpair)
    (Computable.const (3 * A.error))
  have hl := computable_rat_lt.comp ((computable_distance rules A).comp hpair)
    (Computable.const (3 * A.error))
  have hhigh := (EffectiveScan.computable_boundedAll
    (p := fun p : ℕ × Candidate => fun i => decide (highMiss rules A p.2.1 p.2.2 i < 3 * A.error))
    hh).comp (Computable.id.pair (Computable.const A.protectedCount))
  have hlow := (EffectiveScan.computable_boundedAll
    (p := fun p : ℕ × Candidate => fun i => decide (distance rules A p.2.1 p.2.2 i < 3 * A.error))
    hl).comp (Computable.id.pair (Computable.const A.protectedCount))
  have hm : Computable (fun p : ℕ × Candidate =>
      decide (A.threshold < weightedMass rules A p.2.1 p.2.2)) :=
    computable_rat_lt.comp (Computable.const A.threshold)
    ((computable_weightedMass rules A).comp Computable.snd)
  exact Primrec.and.to_comp.comp
    (Primrec.and.to_comp.comp (Primrec.and.to_comp.comp
      (Primrec.and.to_comp.comp (Primrec.and.to_comp.comp hs hd) hb) hhigh) hlow) hm

/-- Use the canonical primitive coding of a candidate throughout the search. -/
def encodeCandidate (C : Candidate) : ℕ :=
  @Encodable.encode Candidate (inferInstance : Primcodable Candidate).toEncodable C

/-- Decode one ordinary natural-number candidate and run the finite verifier. -/
def trial (rules : List ScanRule) (A : Advice) (M n : ℕ) : Option Candidate :=
  (@Encodable.decode Candidate (inferInstance : Primcodable Candidate).toEncodable n).bind
    fun C => if check rules A M C then some C else none

theorem computable_trial (rules : List ScanRule) (A : Advice) :
    Computable₂ (trial rules A) := by
  have hf : Computable₂ (fun M C => if check rules A M C then some C else none) := by
    have h := Computable.cond (computable_check rules A)
      (Computable.option_some.comp Computable.snd) (Computable.const none)
    exact h.of_eq fun _ => by simp [Bool.cond_eq_ite]
  exact Computable.bind_decode_iff.mpr hf

/-- The actual fixed-advice exhaustive search, whose only input is M. -/
def search (rules : List ScanRule) (A : Advice) (M : ℕ) : Part Candidate :=
  Nat.rfindOpt (trial rules A M)

theorem partrec_search (rules : List ScanRule) (A : Advice) :
    Partrec (search rules A) := Partrec.rfindOpt (computable_trial rules A)

theorem search_check {rules : List ScanRule} {A : Advice} {M : ℕ} {C : Candidate}
    (hC : C ∈ search rules A M) : check rules A M C = true := by
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hC
  simp only [trial, Option.mem_bind_iff] at hn
  obtain ⟨B, _, hB⟩ := hn
  split_ifs at hB with hv
  · have he : B = C := Option.mem_some_iff.mp hB
    simpa only [he] using hv
  · simp at hB

theorem search_spec {rules : List ScanRule} {A : Advice} {M : ℕ} {C : Candidate}
    (hC : C ∈ search rules A M) : Accepted rules A M C :=
  (check_eq_true rules A M C).mp (search_check hC)

/-- Analytic finite existence is exactly what is needed to prove halting. -/
theorem search_dom_iff (rules : List ScanRule) (A : Advice) (M : ℕ) :
    (search rules A M).Dom ↔ ∃ C, Accepted rules A M C := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := Part.dom_iff_mem.mp h
    exact ⟨C, search_spec hC⟩
  · rintro ⟨C, hC⟩
    apply Nat.rfindOpt_dom.mpr
    refine ⟨encodeCandidate C, C, ?_⟩
    simp only [trial, encodeCandidate, Encodable.encodek, Option.bind_some]
    rw [(check_eq_true rules A M C).mpr hC]
    exact Option.mem_some_self C

/-- One fixed program handles every requested M. All non-effective choices
are in the finite list of scans and the finite advice record before ∀M. -/
theorem exists_search_program (rules : List ScanRule) (A : Advice) :
    ∃ e : Nat.Partrec.Code, ∀ M : ℕ,
      e.eval M = (search rules A M).map encodeCandidate := by
  obtain ⟨e, he⟩ := Nat.Partrec.Code.exists_code.mp (partrec_search rules A)
  refine ⟨e, fun M => ?_⟩
  rw [he]
  simp only [Encodable.decode_nat, Part.coe_some, Part.bind_some]
  rfl

/-- When the analytic existence theorem is supplied, the same program halts
on every sufficiently large input and every output satisfies all finite tests. -/
theorem exists_eventually_halting_program (rules : List ScanRule) (A : Advice)
    (h : ∀ᶠ M in Filter.atTop, ∃ C, Accepted rules A M C) :
    ∃ e : Nat.Partrec.Code,
      (∀ M, e.eval M = (search rules A M).map encodeCandidate) ∧
      ∀ᶠ M in Filter.atTop, (e.eval M).Dom := by
  obtain ⟨e, he⟩ := exists_search_program rules A
  refine ⟨e, he, ?_⟩
  filter_upwards [h] with M hM
  rw [he]
  exact (search_dom_iff rules A M).mpr hM

/-- The pool-producing partial function forgets the search horizon. -/
def pool (rules : List ScanRule) (A : Advice) (M : ℕ) : Part (List ℕ) :=
  (search rules A M).map Prod.fst

theorem partrec_pool (rules : List ScanRule) (A : Advice) :
    Partrec (pool rules A) :=
  (partrec_search rules A).map (Computable.fst.comp Computable.snd)

/-- Every pool returned by the program has a horizon witnessing all three tests. -/
theorem pool_spec {rules : List ScanRule} {A : Advice} {M : ℕ} {G : List ℕ}
    (hG : G ∈ pool rules A M) : ∃ V, Accepted rules A M (G, V) := by
  obtain ⟨C, hC, hCG⟩ := (Part.mem_map_iff Prod.fst).mp hG
  exact ⟨C.2, hCG ▸ search_spec hC⟩

theorem pool_dom_iff (rules : List ScanRule) (A : Advice) (M : ℕ) :
    (pool rules A M).Dom ↔ ∃ G V, Accepted rules A M (G, V) := by
  change (search rules A M).Dom ↔ _
  rw [search_dom_iff]
  exact ⟨fun ⟨⟨G, V⟩, h⟩ => ⟨G, V, h⟩, fun ⟨G, V, h⟩ => ⟨(G, V), h⟩⟩

/-- The output encoding is the canonical computability presentation of lists. -/
def encodePool (G : List ℕ) : ℕ :=
  @Encodable.encode (List ℕ) (inferInstance : Primcodable (List ℕ)).toEncodable G

/-- A single program returns a finite pool from its requested size; the finite
advice, the scans, and the compiler are all fixed outside the input quantifier. -/
theorem exists_pool_program (rules : List ScanRule) (A : Advice) :
    ∃ e : Nat.Partrec.Code, ∀ M : ℕ,
      e.eval M = (pool rules A M).map encodePool := by
  obtain ⟨e, he⟩ := Nat.Partrec.Code.exists_code.mp (partrec_pool rules A)
  refine ⟨e, fun M => ?_⟩
  rw [he]
  simp only [Encodable.decode_nat, Part.coe_some, Part.bind_some]
  rfl

/-- Once accepted candidates exist eventually, one fixed program eventually
returns pools satisfying the finite acceptance specification. -/
theorem exists_eventual_pool_program (rules : List ScanRule) (A : Advice)
    (h : ∀ᶠ M in Filter.atTop, ∃ C, Accepted rules A M C) :
    ∃ e : Nat.Partrec.Code, ∀ᶠ M in Filter.atTop,
      ∃ G V, encodePool G ∈ e.eval M ∧ Accepted rules A M (G, V) := by
  obtain ⟨e, he⟩ := exists_pool_program rules A
  refine ⟨e, ?_⟩
  filter_upwards [h] with M hM
  obtain ⟨C, hC⟩ := Part.dom_iff_mem.mp ((search_dom_iff rules A M).mpr hM)
  refine ⟨C.1, C.2, ?_, search_spec hC⟩
  rw [he]
  exact Part.mem_map encodePool (Part.mem_map Prod.fst hC)

end Klr.PoolAdvice
