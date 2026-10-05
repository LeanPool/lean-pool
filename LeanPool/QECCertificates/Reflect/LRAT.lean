/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Std.Data.TreeMap.Lemmas
public import Std.Data.DTreeMap.Lemmas

/-!
# Sound checking of the RUP fragment of LRAT certificates

`rupCheck` checks reverse unit propagation along supplied clause indices.
`checkStepsWith` checks a sequence of such additions and requires an empty clause.
`unsat_of_checkSteps` proves that acceptance implies unsatisfiability of the input CNF.
External solvers supply certificates; their correctness is unnecessary for this theorem.

`ClauseDB` abstracts lookup, append and initialization together with the membership laws
consumed by soundness. Both the array and balanced-tree implementations prove those laws.
The theorem covers RUP additions, not general RAT additions. Concrete certificate data
and upstream performance experiments are outside this import.
-/

@[expose] public section

namespace QECCertificates.LRAT

/-- A zero-based variable index and its polarity. -/
abbrev Lit := Nat × Bool
/-- A disjunction of literals. -/
abbrev Clause := List Lit
/-- A conjunction of clauses. -/
abbrev CNF := List Clause
/-- A total Boolean assignment. -/
abbrev Assign := Nat → Bool
/-- Literals asserted true by a partial assignment. -/
abbrev PAssign := List Lit

/-- Negation changes only the polarity. -/
def litNeg (l : Lit) : Lit := (l.1, !l.2)

/-- A clause is satisfied by an assignment. -/
def SatClause (σ : Assign) (C : Clause) : Prop := ∃ l ∈ C, σ l.1 = l.2

/-- A CNF is satisfied by an assignment. -/
def SatFormula (σ : Assign) (F : CNF) : Prop := ∀ C ∈ F, SatClause σ C

/-- The CNF is satisfiable. -/
def Satisfiable (F : CNF) : Prop := ∃ σ, SatFormula σ F

/-- The partial assignment `a` agrees with the total assignment `σ`. -/
def agrees (σ : Assign) (a : PAssign) : Prop := ∀ l ∈ a, σ l.1 = l.2

/-- The literal is not known false: its negation is absent from the partial assignment. -/
def litFree (a : PAssign) (l : Lit) : Bool := !(decide (litNeg l ∈ a))

/-! ## 1. Scanning a clause -/

/-- Collect literals not known false, accumulating them in reverse order. -/
def scanAux (a : PAssign) (fr : List Lit) : Clause → List Lit
  | [] => fr
  | l :: rest => if litFree a l then scanAux a (l :: fr) rest else scanAux a fr rest

/-- Scan a clause: return the list of its literals not known false under the current assignment.
    Emptiness means "all false", a conflict, and a singleton means
"exactly one free literal", a unit step. -/
def scan (a : PAssign) (D : Clause) : List Lit := scanAux a [] D

theorem scanAux_spec (a : PAssign) (D : Clause) (fr : List Lit) :
    ∃ tail : List Lit,
      scanAux a fr D = tail ++ fr ∧
        (∀ l ∈ tail, l ∈ D ∧ litFree a l = true) ∧
        (∀ l ∈ D, litFree a l = true → l ∈ tail) := by
  induction D generalizing fr with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons l rest ih =>
      by_cases hf : litFree a l = true
      · rw [scanAux, ite_eq_left hf]
        obtain ⟨tail, h1, h2, h3⟩ := ih (l :: fr)
        refine ⟨tail ++ [l], ?_, ?_, ?_⟩
        · rw [h1, List.append_assoc, List.singleton_append]
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact ⟨List.mem_cons_of_mem _ (h2 x hx).1, (h2 x hx).2⟩
          · rw [List.mem_singleton] at hx
            subst hx
            exact ⟨by simp, hf⟩
        · intro x hx hx'
          rcases List.mem_cons.mp hx with rfl | hx
          · exact List.mem_append_right _ (by simp)
          · exact List.mem_append_left _ (h3 x hx hx')
      · rw [scanAux, ite_eq_right hf]
        obtain ⟨tail, h1, h2, h3⟩ := ih fr
        exact ⟨tail, h1, fun x hx => ⟨List.mem_cons_of_mem _ (h2 x hx).1, (h2 x hx).2⟩,
          fun x hx hx' => by
            rcases List.mem_cons.mp hx with rfl | hx
            · exact absurd hx' hf
            · exact h3 x hx hx'⟩

/-- `scan a D = []` implies that every literal of `D` is false under the current
assignment. -/
theorem scan_nil {a : PAssign} {D : Clause} (h : scan a D = []) :
    ∀ l ∈ D, litFree a l = false := by
  obtain ⟨tail, h1, _, h3⟩ := scanAux_spec a D []
  have htail : tail = [] := by simpa [scan, h1] using h
  intro l hl
  by_cases hf : litFree a l = true
  · exact absurd (by rw [htail] at h3; exact h3 l hl hf) (by simp)
  · simpa using hf

/-- `scan a D = [l]` implies that `l ∈ D` and that every other literal of `D` is false. -/
theorem scan_singleton {a : PAssign} {D : Clause} {l : Lit} (h : scan a D = [l]) :
    l ∈ D ∧ ∀ l' ∈ D, l' ≠ l → litFree a l' = false := by
  obtain ⟨tail, h1, h2, h3⟩ := scanAux_spec a D []
  have htail : tail = [l] := by simpa [scan, h1] using h
  refine ⟨(h2 l (by rw [htail]; simp)).1, ?_⟩
  intro l' hl' hne
  by_cases hf : litFree a l' = true
  · have hmem := h3 l' hl' hf
    rw [htail] at hmem
    exact absurd (List.mem_singleton.mp hmem) hne
  · simpa using hf

/-- If a literal is not free under the current assignment, then its negation has been
assigned. -/
theorem litFree_eq_false {a : PAssign} {l : Lit} (h : litFree a l = false)
    {σ : Assign} (hσ : agrees σ a) : σ l.1 = !l.2 := by
  have hmem : litNeg l ∈ a := by
    by_contra hc
    simp [litFree, hc] at h
  have := hσ _ hmem
  simpa [litNeg] using this

private theorem bool_not_self (b : Bool) : (!b : Bool) = b → False := by
  cases b <;> simp

/-! ## 2. The clause database interface

Kernel replay uses only **four operations** of the database, namely lookup, length,
append and build, and **three laws**. Changing the representation, from `Array` to a
balanced tree, is therefore an **instantiation**, not a re-proof of a load-bearing
module.

**Why the interface is opened up** (measured in this library). Inside the **kernel**,
`Array`'s `push` and `get?` are both **linear in the index**, so each step of `rupCheck`
costs more than the last and the whole certificate is quadratic in the number of steps,
whereas a balanced tree is logarithmic. Measured in **reduction steps**, which are
deterministic and free of start-up noise, for $N = 200 \to 400$: `Array` 40,803 to
161,603 (3.96×) and `Std.TreeMap` 4,757 to 11,066 (2.33×, against a theoretical 2.26×).
Extrapolated to the 570,883 steps of the replay, the two differ by about a factor of
9,400.
-/

/-- **The clause database interface**: `rupCheck` and `checkAux` use only these four
operations and three laws. -/
structure ClauseDB (Carrier : Type) where
  /-- Look up a clause at a zero-based index. -/
  get? : Carrier → Nat → Option Clause
  /-- The index at which the next clause is appended. -/
  size : Carrier → Nat
  /-- Append a clause to the database. -/
  push : Carrier → Clause → Carrier
  /-- Semantic membership of a clause in the database. -/
  Mem : Carrier → Clause → Prop
  /-- A clause that is looked up is certainly in the database. -/
  get?_mem : ∀ {d i C}, get? d i = some C → Mem d C
  /-- After one append, every clause in the database is **either the new one or was already
  there**. **Only the half that soundness needs** is required: `checkAux_sound` consumes
  this direction only, while the missing converse,
  `C' = C ∨ Mem d C' → Mem (push d C) C'`, is exactly where a balanced-tree instance needs
  the invariant "key < size". Stating the laws at the **strength that is used** keeps both
  instances clean. -/
  push_mem : ∀ {d C C'}, Mem (push d C) C' → C' = C ∨ Mem d C'
  /-- Build a database from a CNF. -/
  ofCNF : CNF → Carrier
  /-- Every clause of the initial database **comes from** that CNF, again only the half
  that is used. -/
  ofCNF_mem : ∀ {F C}, Mem (ofCNF F) C → C ∈ F

namespace ClauseDB

/-- The `Array` version: the **verbatim** representation from before the interface was
opened, and the one the downstream `LRATData` uses. -/
def array : ClauseDB (Array Clause) where
  get? := fun d i => d[i]?
  size := Array.size
  push := Array.push
  Mem := fun d C => C ∈ d
  get?_mem := by
    intro d i C h
    rw [Array.mem_def]
    exact List.mem_of_getElem? (by simpa using h)
  push_mem := by
    intro d C C' h
    rw [Array.mem_push] at h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  ofCNF := List.toArray
  ofCNF_mem := by
    intro F C h
    exact (List.mem_toArray).mp h

/-- Membership for the tree database: `C` is the value at some key.

**Factored out into a separate `def`**: writing `Mem` inside the structure literal would
resolve to the structure projection `ClauseDB.Mem`, which takes the structure itself as
its first argument, so `Mem d C` would expect a `ClauseDB` as its first argument. -/
def treeMem (d : Std.TreeMap Nat Clause compare) (C : Clause) : Prop := ∃ i, d.get? i = some C

/-- **The balanced-tree version**: each lookup and insertion is $O(\log n)$ in the
kernel, so the whole certificate accumulates logarithmically rather than quadratically as
with `Array`. The key is the **clause number minus one**, 0-based, and `push` appends at
`size`. -/
def tree : ClauseDB (Std.TreeMap Nat Clause compare) where
  get? := fun d i => d.get? i
  size := fun d => Std.TreeMap.size d
  push := fun (d : Std.TreeMap Nat Clause compare) C =>
    Std.TreeMap.insert d (Std.TreeMap.size d) C
  Mem := treeMem
  get?_mem := fun h => ⟨_, h⟩
  push_mem := by
    intro d C C' h
    obtain ⟨i, hi⟩ := h
    simp only [Std.TreeMap.get?, Std.TreeMap.insert] at hi
    rw [Std.DTreeMap.Const.get?_insert] at hi
    split at hi
    · exact Or.inl (Option.some.inj hi).symm
    · exact Or.inr ⟨i, hi⟩
  ofCNF := fun F =>
    F.foldl (fun (d : Std.TreeMap Nat Clause compare) C =>
      Std.TreeMap.insert d (Std.TreeMap.size d) C) ∅
  ofCNF_mem := by
    intro F C h
    -- Generalize over the accumulator: intermediate folds start from a nonempty database.
    have key : ∀ (l : List Clause) (acc : Std.TreeMap Nat Clause compare),
        treeMem (l.foldl (fun (d : Std.TreeMap Nat Clause compare) C =>
          Std.TreeMap.insert d (Std.TreeMap.size d) C) acc) C
          → C ∈ l ∨ treeMem acc C := by
      intro l
      induction l with
      | nil =>
          intro acc h
          exact Or.inr h
      | cons D ds ih =>
          intro acc h
          rw [List.foldl_cons] at h
          rcases ih _ h with hmem | hmem
          · exact Or.inl (List.mem_cons_of_mem _ hmem)
          · obtain ⟨i, hi⟩ := hmem
            simp only [Std.TreeMap.get?, Std.TreeMap.insert] at hi
            rw [Std.DTreeMap.Const.get?_insert] at hi
            split at hi
            · exact Or.inl (by simp [Option.some.inj hi])
            · exact Or.inr ⟨i, hi⟩
    rcases key F ∅ h with hmem | hmem
    · exact hmem
    · -- Simplification matches the empty-tree lemma up to definitional equality.
      obtain ⟨i, hi⟩ := hmem
      simp at hi

end ClauseDB

/-- Unit propagation along the hint sequence. `h` is a 1-based clause number. -/
def rupAux {K : Type} (D : ClauseDB K) (d : K) (a : PAssign) : List Nat → Bool
  | [] => false
  | h :: rest =>
      match D.get? d (h - 1) with
      | none => false
      | some E =>
          match scan a E with
          | [] => true
          | [l] => rupAux D d (l :: a) rest
          | _ => false

/-- The clause `C` is RUP with respect to the database `d`: negating `C` and propagating
along `hints` reaches a conflict. -/
def rupCheck {K : Type} (D : ClauseDB K) (d : K) (C : Clause) (hints : List Nat) : Bool :=
  rupAux D d (C.map litNeg) hints

/-- **Soundness of RUP**: if propagation along the hints reaches a conflict, then any
assignment satisfying the clauses the hints point to satisfies `C`. -/
theorem rupAux_sound {K : Type} (D : ClauseDB K) {σ : Assign} {d : K} :
    ∀ (hints : List Nat) (a : PAssign), agrees σ a →
      (∀ h ∈ hints, ∀ E, D.get? d (h - 1) = some E → SatClause σ E) →
      rupAux D d a hints = true → False := by
  intro hints
  induction hints with
  | nil =>
      intro a _ _ hr
      simp [rupAux] at hr
  | cons h rest ih =>
      intro a ha hsat hr
      rw [rupAux] at hr
      cases hE : D.get? d (h - 1) with
      | none =>
          rw [hE] at hr
          simp at hr
      | some E =>
          rw [hE] at hr
          dsimp only at hr
          have hsatE : SatClause σ E := hsat h (by simp) E hE
          cases hs : scan a E with
          | nil =>
              rw [hs] at hr
              obtain ⟨l, hl, hsatl⟩ := hsatE
              have h1 : σ l.1 = (!l.2 : Bool) := litFree_eq_false (scan_nil hs l hl) ha
              exact bool_not_self l.2 (h1.symm.trans hsatl)
          | cons x xs =>
              cases xs with
              | nil =>
                  rw [hs] at hr
                  have hx : σ x.1 = x.2 := by
                    obtain ⟨l', hl', hsatl'⟩ := hsatE
                    by_cases hne : l' = x
                    · rw [hne] at hsatl'
                      exact hsatl'
                    · have hlf : litFree a l' = false := (scan_singleton hs).2 l' hl' hne
                      have h1 : σ l'.1 = (!l'.2 : Bool) := litFree_eq_false hlf ha
                      exact absurd (h1.symm.trans hsatl') (bool_not_self l'.2)
                  exact ih (x :: a)
                    (fun l hl => by
                      rcases List.mem_cons.mp hl with rfl | hl
                      · exact hx
                      · exact ha l hl)
                    (fun h' hh' E' hE' => hsat h' (List.mem_cons_of_mem _ hh') E' hE') hr
              | cons y ys =>
                  rw [hs] at hr
                  simp at hr

/-! ## 3. The certificate checking layer -/

/-- One LRAT step: `id` is the clause number given by LRAT, the original clauses being
`1..m` and the lemmas running consecutively from `m+1`. -/
structure LStep where
  /-- One-based number of the added clause. -/
  id : Nat
  /-- The clause justified by this step. -/
  clause : Clause
  /-- One-based indices to follow during reverse unit propagation. -/
  hints : List Nat

/-- Step-by-step checking: the clause numbers must be consecutive, namely `D.size d + 1`,
and each clause must be RUP; deriving the empty clause means success. -/
def checkAux {K : Type} (D : ClauseDB K) (d : K) : List LStep → Bool
  | [] => false
  | s :: rest =>
      if s.id = D.size d + 1 ∧ rupCheck D d s.clause s.hints then
        s.clause.isEmpty || checkAux D (D.push d s.clause) rest
      else false

/-- **Checking with a given representation**: build the database from the CNF via
`D.ofCNF`, then check the steps one by one. -/
def checkStepsWith {K : Type} (D : ClauseDB K) (F : CNF) (steps : List LStep) : Bool :=
  checkAux D (D.ofCNF F) steps

/-- The entry point, with the **verbatim signature** from before the interface was
opened: it uses the `Array` database, so the two downstream data modules are
unaffected. -/
abbrev checkSteps (F : CNF) (steps : List LStep) : Bool := checkStepsWith ClauseDB.array F steps

/-- **Soundness of the checker (the core)**: if `checkAux` returns true, then `σ` does
not satisfy the database. -/
theorem checkAux_sound {K : Type} (D : ClauseDB K) {σ : Assign} :
    ∀ (d : K) (steps : List LStep), (∀ C, D.Mem d C → SatClause σ C) →
      checkAux D d steps = true → False := by
  intro d steps
  induction steps generalizing d with
  | nil => intro _ h; simp [checkAux] at h
  | cons s rest ih =>
      intro hdb h
      rw [checkAux] at h
      by_cases hcond : s.id = D.size d + 1 ∧ rupCheck D d s.clause s.hints
      · rw [ite_eq_left hcond] at h
        have hrup : rupCheck D d s.clause s.hints = true := hcond.2
        have hsat : SatClause σ s.clause := by
          by_contra hc
          simp only [SatClause, not_exists, not_and] at hc
          refine rupAux_sound D (d := d) (σ := σ) s.hints (s.clause.map litNeg) ?_ ?_ hrup
          · intro l hl
            rcases List.mem_map.mp hl with ⟨l₀, hl₀, rfl⟩
            have hne : ¬(σ l₀.1 = l₀.2) := hc l₀ hl₀
            simp only [litNeg]
            cases h1 : σ l₀.1 <;> cases h2 : l₀.2 <;> simp_all
          · intro _ _ E hE
            exact hdb E (D.get?_mem hE)
        rcases Bool.or_eq_true_iff.mp h with hemp | hrest
        · rw [List.isEmpty_iff.mp hemp] at hsat
          obtain ⟨l, hl, _⟩ := hsat
          simp at hl
        · exact ih (D.push d s.clause) (fun C hC => by
            rcases D.push_mem hC with hEq | hC
            · subst hEq
              exact hsat
            · exact hdb C hC) hrest
      · rw [ite_eq_right hcond] at h
        simp at h

/-- **The main theorem, entry point**: a successful kernel check implies that the CNF is
unsatisfiable. -/
theorem checkSteps_sound {F : CNF} {steps : List LStep}
    (h : checkSteps F steps = true) : ¬ Satisfiable F := by
  rintro ⟨σ, hσ⟩
  exact checkAux_sound ClauseDB.array (ClauseDB.array.ofCNF F) steps
    (fun C hC => hσ C (ClauseDB.array.ofCNF_mem hC)) h

/-- The entry point used by the generator: the same content as `checkSteps_sound`, as a
proof term. -/
theorem unsat_of_checkSteps {F : CNF} {steps : List LStep}
    (h : checkSteps F steps = true) : ¬ Satisfiable F := checkSteps_sound h

end QECCertificates.LRAT
