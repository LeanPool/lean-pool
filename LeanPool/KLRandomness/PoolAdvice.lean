/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.SparseListSearchComputable

/-!
# Finite advice and the three finite pool tests

All functions in this file act on finite answer words. A scan is fed the
successive prefixes of that word; these are not the scan's input-space
transcripts. The finite advice is chosen once, before the requested pool size.
The associated computability and exhaustive-search theorems are in
`PoolAdviceComputable` and `PoolSearch`.
-/

@[expose] public section

namespace Klr.PoolAdvice

open SparseSearch

/-- A fixed finite list of total scans has a total query dispatcher. Indices
outside the list are harmlessly assigned the constant-zero query. -/
def query : List ScanRule → ℕ → List Bool → ℕ
  | [], _, _ => 0
  | π :: _, 0, s => π.query s
  | _ :: ps, i + 1, s => query ps i s

theorem query_of_getElem? {rules : List ScanRule} {i : ℕ} {π : ScanRule}
    (hi : rules[i]? = some π) (s : List Bool) : query rules i s = π.query s := by
  induction rules generalizing i with
  | nil => simp at hi
  | cons ρ rules ih =>
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst ρ; rfl
    | succ i => exact ih (by simpa using hi)

/-- One Boolean table and one rational table, indexed by ordinary encodings
of finite binary prefixes. The default values allow arbitrary finite tables. -/
abbrev Table := List Bool × List ℚ

/-- Exactly the finite data hard-coded into a pool search. `protectedCount`
corresponds to ℓ, and the length of the separately fixed scan list to D. -/
structure Advice where
  /-- Finite bound on positions that the existing construction needs to avoid. -/
  positionBound : ℕ
  /-- Number of scans protected by the advice. -/
  protectedCount : ℕ
  /-- Length of the input prefixes used for the clopen approximations. -/
  depth : ℕ
  /-- Rational tolerance used by the finite pool search. -/
  error : ℚ
  /-- Rational threshold used to separate the approximating tables. -/
  threshold : ℚ
  /-- The finite clopen tables for the protected scans and partitions. -/
  tables : List Table

/-- The clopen approximation is determined by one finite prefix. -/
def highTable (A : Advice) (i : ℕ) (s : List Bool) : Bool :=
  ((A.tables.getD i ([], [])).1).getD (Encodable.encode (s.take A.depth)) false

/-- The rational-valued cylinder approximation uses the same finite prefix. -/
def approxTable (A : Advice) (i : ℕ) (s : List Bool) : ℚ :=
  ((A.tables.getD i ([], [])).2).getD (Encodable.encode (s.take A.depth)) 0

/-- Whether a fixed scan queries a position in its first `V` steps. -/
def readsBefore (rules : List ScanRule) (i a V : ℕ) (s : List Bool) : Bool :=
  (List.range V).any fun t => decide (query rules i (s.take t) = a)

theorem readsBefore_eq_true (rules : List ScanRule) (i a V : ℕ) (s : List Bool) :
    readsBefore rules i a V s = true ↔
      ∃ t < V, query rules i (s.take t) = a := by
  simp [readsBefore, List.any_eq_true]

/-- Fraction of the listed pool read by the finite horizon. Repetitions count
with multiplicity here; the acceptance predicate separately checks nodup. -/
def finiteReads (rules : List ScanRule) (i : ℕ) (G : List ℕ) (V : ℕ)
    (s : List Bool) : ℚ :=
  (G.countP (fun a => readsBefore rules i a V s) : ℚ) / G.length

/-- Exact uniform expectation of a rational function of `n` fair bits. -/
def average (n : ℕ) (f : List Bool → ℚ) : ℚ :=
  ((words n).map f).sum / (2 : ℚ) ^ n

/-- Common cylinder depth for advice and the finite scan computation. -/
def testDepth (A : Advice) (V : ℕ) : ℕ := max V A.depth

/-- Finite approximation to the measure of the high-set points missing a
member of the pool. -/
def highMiss (rules : List ScanRule) (A : Advice) (G : List ℕ) (V i : ℕ) : ℚ :=
  average (testDepth A V) fun s =>
    if highTable A i s && decide (finiteReads rules i G V s < 1) then 1 else 0

/-- Exact finite L1 distance from the rational cylinder advice. -/
def distance (rules : List ScanRule) (A : Advice) (G : List ℕ) (V i : ℕ) : ℚ :=
  average (testDepth A V) fun s =>
    |finiteReads rules i G V s - approxTable A i s|

/-- The paper numbers scans from one; our zero-based scan i has weight
`(1/2)^(i+1)`. -/
def weight (i : ℕ) : ℚ := (1 / 2 : ℚ) ^ (i + 1)

/-- Weighted finite-time read mass of all D fixed scans. -/
def weightedMass (rules : List ScanRule) (A : Advice) (G : List ℕ) (V : ℕ) : ℚ :=
  ((List.range rules.length).map fun i =>
    weight i * average (testDepth A V) (finiteReads rules i G V)).sum

/-- A candidate is a finite pool and a finite scan horizon. -/
abbrev Candidate := List ℕ × ℕ

/-- The exact mathematical specification of the finite checker. This contains
no limiting functions, Borel sets, convergence moduli, or oracle calls. -/
def Accepted (rules : List ScanRule) (A : Advice) (M : ℕ) (C : Candidate) : Prop :=
  C.1.length = M ∧ C.1.Nodup ∧
  (∀ a ∈ C.1, A.positionBound ≤ a) ∧
  (∀ i < A.protectedCount, highMiss rules A C.1 C.2 i < 3 * A.error) ∧
  (∀ i < A.protectedCount, distance rules A C.1 C.2 i < 3 * A.error) ∧
  A.threshold < weightedMass rules A C.1 C.2

@[simp] theorem length_words (n : ℕ) : (words n).length = 2 ^ n := by
  induction n with
  | zero => simp [words]
  | succ n ih => simp [words, ih, pow_succ]; omega

theorem nodup_words (n : ℕ) : (words n).Nodup := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    apply List.Nodup.append (ih.map (fun _ _ h => List.cons.inj h |>.2))
      (ih.map (fun _ _ h => List.cons.inj h |>.2))
    intro s hs ht
    obtain ⟨u, _, hu⟩ := List.mem_map.mp hs
    obtain ⟨v, _, hv⟩ := List.mem_map.mp ht
    rw [← hu] at hv
    cases hv

/-- The exact prefix interpretation of the finite high-set advice. -/
def highSet (A : Advice) (i : ℕ) : Set Cantor :=
  {Z | highTable A i (ScanRule.inputPrefix Z A.depth) = true}

/-- The exact prefix interpretation of the finite rational advice. -/
def approx (A : Advice) (i : ℕ) (Z : Cantor) : ℝ :=
  approxTable A i (ScanRule.inputPrefix Z A.depth)

end Klr.PoolAdvice
