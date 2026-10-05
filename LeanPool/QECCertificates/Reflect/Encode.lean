/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module
public import LeanPool.QECCertificates.Reflect.LRAT

/-!
# Encoding fidelity: a model of the CNF is a light logical operator

`Reflect/LRAT.lean` turns successful kernel replay into unsatisfiability of a CNF.
This module supplies Boolean semantic soundness of the encoder; `Reflect/Complete`
proves the converse, and `Reflect/Distance` connects these semantics to binary matrices
and Hamming weight. Concrete solver output and replay data are outside this import.

What the encoder asserts is (see the module note of the external encoder)

    exists x, w  with  x in ker(Hker),  w in ker(Hpair),  x.w = 1,  wt(x) <= k

The three parts are each realised by one class of clauses, and for each class this module
establishes **soundness** ("all clauses satisfied implies that the semantics holds"):

| part | clauses | soundness |
|---|---|---|
| `xorChain` | a Tseitin chain plus one fixing clause | `dotS σ xs = want` (`dotS` is the GF(2)
    dot product over a support set) |
| `atMostK` | a sequential counter (Sinz) | `cntS σ xs ≤ k` |

The product variables (a Tseitin conjunction of three clauses) are given in a later section
of this same file.
The fact that "`x` is not in the row space of `Hpair`" follows from `x.w = 1` together with
`w ∈ ker(Hpair)`: if `x = Σ c_r r` is a combination of rows, then `x.w = Σ c_r (r.w) = 0`,
contradicting `x.w = 1`. This step uses only the one half **row space ⊆ (ker)⊥**; the
converse inclusion `(ker)⊥ ⊆ row` is not needed.
-/

@[expose] public section

namespace QECCertificates.LRAT

/-! ## The GF(2) dot product over a support set, and the support size -/

/-- The GF(2) dot product `Σ_{j ∈ s} σ j` over the support set `s` (with XOR of `Bool` as
the addition). -/
def dotS (σ : Assign) : List Nat → Bool
  | [] => false
  | j :: s => σ j ^^ dotS σ s

@[simp] theorem dotS_nil (σ : Assign) : dotS σ [] = false := rfl

@[simp] theorem dotS_cons (σ : Assign) (j : Nat) (s : List Nat) :
    dotS σ (j :: s) = (σ j ^^ dotS σ s) := rfl

/-- The concatenation law: the dot product is additive under concatenation of support
sets. -/
theorem dotS_append (σ : Assign) (s t : List Nat) :
    dotS σ (s ++ t) = (dotS σ s ^^ dotS σ t) := by
  induction s with
  | nil => simp
  | cons j s ih => simp only [List.cons_append, dotS_cons, ih]; rw [Bool.xor_assoc]

/-- The support size: the number of variables that `σ` assigns true. -/
def cntS (σ : Assign) (l : List Nat) : Nat := (l.filter (fun t => σ t)).length

@[simp] theorem cntS_nil (σ : Assign) : cntS σ [] = 0 := rfl

theorem cntS_append (σ : Assign) (l₁ l₂ : List Nat) :
    cntS σ (l₁ ++ l₂) = cntS σ l₁ + cntS σ l₂ := by
  simp [cntS, List.filter_append]

theorem cntS_singleton_true (σ : Assign) (x : Nat) (h : σ x = true) : cntS σ [x] = 1 := by
  simp [cntS, h]

theorem cntS_singleton_false (σ : Assign) (x : Nat) (h : σ x = false) : cntS σ [x] = 0 := by
  simp [cntS, h]

theorem cntS_le_length (σ : Assign) (l : List Nat) : cntS σ l ≤ l.length :=
  List.length_filter_le _ _

/-! ## General clause lemmas -/

/-- The semantics of a two-literal clause. -/
theorem sat_two {σ : Assign} {a b : Lit} (h : SatClause σ [a, b]) :
    σ a.1 = a.2 ∨ σ b.1 = b.2 := by
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact Or.inl hv
  · exact Or.inr hv

/-- The semantics of a three-literal clause. -/
theorem sat_three {σ : Assign} {a b c : Lit} (h : SatClause σ [a, b, c]) :
    σ a.1 = a.2 ∨ σ b.1 = b.2 ∨ σ c.1 = c.2 := by
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · exact Or.inl hv
  · exact Or.inr (Or.inl hv)
  · exact Or.inr (Or.inr hv)

/-! ## Tseitin chain: `Σ xs = want` -/

/-- The four clauses of one Tseitin step, pinning `nxt = cur ⊕ x`.

The polarities of the four clauses must not be swapped: dropping the negation of `nxt` in
the first two leaves the chain computing an equivalence rather than an XOR, which detaches
the UNSAT result from the physical assertion (a self-check on a small example in the
external encoder guards against exactly this). -/
def xorStepClauses (cur x nxt : Nat) : List Clause :=
  [[(cur, false), (x, false), (nxt, false)],
   [(cur, false), (x, true), (nxt, true)],
   [(cur, true), (x, false), (nxt, true)],
   [(cur, true), (x, true), (nxt, false)]]

/-- Soundness of one step: all four clauses true implies that `nxt` takes the value
`cur ⊕ x`. -/
theorem xorStep_sat {σ : Assign} {cur x nxt : Nat}
    (h : ∀ C ∈ xorStepClauses cur x nxt, SatClause σ C) :
    σ nxt = (σ cur ^^ σ x) := by
  have h1 : SatClause σ [(cur, false), (x, false), (nxt, false)] :=
    h _ (by simp [xorStepClauses])
  have h2 : SatClause σ [(cur, false), (x, true), (nxt, true)] :=
    h _ (by simp [xorStepClauses])
  have h3 : SatClause σ [(cur, true), (x, false), (nxt, true)] :=
    h _ (by simp [xorStepClauses])
  have h4 : SatClause σ [(cur, true), (x, true), (nxt, false)] :=
    h _ (by simp [xorStepClauses])
  have k1 : σ cur = false ∨ σ x = false ∨ σ nxt = false := sat_three h1
  have k2 : σ cur = false ∨ σ x = true ∨ σ nxt = true := sat_three h2
  have k3 : σ cur = true ∨ σ x = false ∨ σ nxt = true := sat_three h3
  have k4 : σ cur = true ∨ σ x = true ∨ σ nxt = false := sat_three h4
  by_cases hc : σ cur = true <;> by_cases hx : σ x = true <;> simp_all

/-- The chain: starting from `cur`, XOR in each variable of `rest` in turn, with the new
variables numbered consecutively from `c`.

The final clause (emitted once `rest` is exhausted) pins the result of the chain to
`want`. -/
def xorChainAux : List Nat → Bool → Nat → Nat → List Clause × Nat
  | [], want, cur, c => ([[(cur, want)]], c)
  | x :: rest, want, cur, c =>
      let (tl, c') := xorChainAux rest want c (c + 1)
      (xorStepClauses cur x c ++ tl, c')

/-- Soundness of the chain: all clauses true implies `dotS σ (cur :: rest) = want`. -/
theorem xorChainAux_sat : ∀ (rest : List Nat) (want : Bool) (cur c : Nat) (σ : Assign),
    (∀ C ∈ (xorChainAux rest want cur c).1, SatClause σ C) →
    dotS σ (cur :: rest) = want := by
  intro rest
  induction rest with
  | nil =>
      intro want cur c σ h
      have hc : SatClause σ [(cur, want)] := h _ (by simp [xorChainAux])
      obtain ⟨l, hl, hv⟩ := hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      obtain rfl : l = (cur, want) := hl
      simp only [dotS_cons, dotS_nil]
      rw [hv]
      cases want <;> rfl
  | cons x rest ih =>
      intro want cur c σ h
      have hstep : ∀ C ∈ xorStepClauses cur x c, SatClause σ C :=
        fun C hC => h C (List.mem_append_left _ hC)
      have htl : ∀ C ∈ (xorChainAux rest want c (c + 1)).1, SatClause σ C :=
        fun C hC => h C (List.mem_append_right _ hC)
      have hnxt : σ c = (σ cur ^^ σ x) := xorStep_sat hstep
      have hIH : dotS σ (c :: rest) = want := ih want c (c + 1) σ htl
      simp only [dotS_cons] at hIH ⊢
      rw [hnxt] at hIH
      rw [← hIH, Bool.xor_assoc]

/-- The complete chain (`xs` nonempty; an empty list can only come from an empty support
set, in which case **no clause is emitted** at all, since the encoder never produces an
empty support set and a `[-start]` clause would create a constraint out of nothing). -/
def xorChain (xs : List Nat) (want : Bool) (start : Nat) : List Clause × Nat :=
  match xs with
  | [] => ([], start)
  | x₀ :: rest => xorChainAux rest want x₀ start

/-- Soundness of the chain (the nonempty form). -/
theorem xorChain_sat {σ : Assign} {x₀ : Nat} {rest : List Nat} {want : Bool} {start : Nat}
    (h : ∀ C ∈ (xorChainAux rest want x₀ start).1, SatClause σ C) :
    dotS σ (x₀ :: rest) = want :=
  xorChainAux_sat rest want x₀ start σ h

/-- Soundness of the chain for an arbitrary nonempty list of variables; used when a
definition such as `prodVars` does not reduce syntactically. -/
theorem xorChain_sat' {σ : Assign} {xs : List Nat} {want : Bool} {start : Nat}
    (hne : xs ≠ []) (h : ∀ C ∈ (xorChain xs want start).1, SatClause σ C) :
    dotS σ xs = want := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x₀ rest => exact xorChain_sat h

/-! ## Sequential counter: `wt ≤ k` -/

/-- The slot convention: `s i j` is the variable number meaning "at least `j` of the first
`i` variables are true"; `none` marks the slot as a **constant** (true when `j = 0`, false
when `j > min i (k + 1)`).

The external encoder writes `0` for those two constant slots, and it must discharge them
before emitting clauses: `0` is the clause terminator in DIMACS, so writing it out would
split one clause into two. -/
def SlotOK (s : Nat → Nat → Option Nat) (k : Nat) : Prop :=
  ∀ i j, s i j = none ↔ ¬(1 ≤ j ∧ j ≤ min i (k + 1))

theorem SlotOK.some_of {s : Nat → Nat → Option Nat} {k : Nat} (hok : SlotOK s k) {i j : Nat}
    (h1 : 1 ≤ j) (h2 : j ≤ min i (k + 1)) : ∃ v, s i j = some v := by
  have hne : s i j ≠ none := fun h => (hok i j).mp h ⟨h1, h2⟩
  cases h : s i j with
  | none => exact absurd h hne
  | some v => exact ⟨v, rfl⟩

theorem SlotOK.none_of {s : Nat → Nat → Option Nat} {k : Nat} (hok : SlotOK s k) {i j : Nat}
    (h : ¬(1 ≤ j ∧ j ≤ min i (k + 1))) : s i j = none := (hok i j).mpr h

/-- The three or four clauses of the slot `(i,j)`, transcribed verbatim from the encoder
`none` slots are discharged as constants (always false or always true). -/
def slotClauses (s : Nat → Nat → Option Nat) (i j x : Nat) : List Clause :=
  match s (i - 1) j, s (i - 1) (j - 1), s i j with
  | some a, some b, some si =>
      [[(a, false), (si, true)],
       [(b, false), (x, false), (si, true)],
       [(si, false), (a, true), (x, true)],
       [(si, false), (a, true), (b, true)]]
  | some a, none, some si =>
      [[(a, false), (si, true)],
       [(x, false), (si, true)],
       [(si, false), (a, true), (x, true)]]
  | none, some b, some si =>
      [[(b, false), (x, false), (si, true)],
       [(si, false), (x, true)],
       [(si, false), (b, true)]]
  | none, none, some si =>
      [[(x, false), (si, true)],
       [(si, false), (x, true)]]
  | _, _, none => []

/-- All clauses of the `i`-th row (which processes the variable `x`), expanded over
`j = 1..min i (k + 1)`. -/
def rowClauses (s : Nat → Nat → Option Nat) (k i x : Nat) : List Clause :=
  (List.range (min i (k + 1))).flatMap (fun j' => slotClauses s i (j' + 1) x)

/-- The sequential counter: `pre` holds the variables already processed (the slot numbers
are computed from its length) and `suf` the remaining ones. When `k+1 ≤ pre.length`, that is
on reaching the last row, one further clause is emitted pinning `s n (k + 1)` to false. -/
def atMostKAux (s : Nat → Nat → Option Nat) (k : Nat) (pre suf : List Nat) : List Clause :=
  match suf with
  | [] =>
      if k + 1 ≤ pre.length then
        (match s pre.length (k + 1) with
         | some v => [[(v, false)]]
         | none => [])
      else []
  | x :: rest => rowClauses s k (pre.length + 1) x ++ atMostKAux s k (pre ++ [x]) rest

/-- All clauses of the counter (starting from an empty prefix). -/
def atMostK (s : Nat → Nat → Option Nat) (k : Nat) (xs : List Nat) : List Clause :=
  atMostKAux s k [] xs

/-- Membership for the row clauses: for `1 ≤ j ≤ min i (k + 1)`, the clauses of the slot
`(i,j)` all occur in the `i`-th row. -/
theorem mem_rowClauses {s : Nat → Nat → Option Nat} {k i j x : Nat} {C : Clause}
    (h1 : 1 ≤ j) (h2 : j ≤ min i (k + 1)) (hC : C ∈ slotClauses s i j x) :
    C ∈ rowClauses s k i x := by
  refine List.mem_flatMap.mpr ⟨j - 1, List.mem_range.mpr (by omega), ?_⟩
  have : j - 1 + 1 = j := by omega
  rwa [this]

/-- **Soundness of the counter**: all clauses satisfied implies that the number of true
variables is at most `k`.

The invariant is: at least `j` of the first `i` variables are true implies that the slot
`(i,j)` is true. The induction runs along the list of variables (`pre` is the prefix already
processed and `suf` the remainder), so the step needs only `List.filter_append` and not the
index bookkeeping of `List.take`. -/
theorem atMostKAux_sat {σ : Assign} {s : Nat → Nat → Option Nat} {k : Nat}
    (hok : SlotOK s k) :
    ∀ (pre suf : List Nat),
      (∀ j, 1 ≤ j → j ≤ min pre.length (k + 1) → j ≤ cntS σ pre →
        ∃ v, s pre.length j = some v ∧ σ v = true) →
      (∀ C ∈ atMostKAux s k pre suf, SatClause σ C) →
      cntS σ (pre ++ suf) ≤ k := by
  intro pre suf hinv0 hcl0
  have aux : ∀ (suf pre : List Nat),
      (∀ j, 1 ≤ j → j ≤ min pre.length (k + 1) → j ≤ cntS σ pre →
        ∃ v, s pre.length j = some v ∧ σ v = true) →
      (∀ C ∈ atMostKAux s k pre suf, SatClause σ C) → cntS σ (pre ++ suf) ≤ k := by
    intro suf
    induction suf with
    | nil =>
      intro pre hinv hcl
      by_cases hk : k + 1 ≤ pre.length
      · obtain ⟨v, hsv⟩ := hok.some_of (i := pre.length) (j := k + 1)
          (by omega) (by simp [Nat.min_eq_right hk])
        have hmem : [(v, false)] ∈ atMostKAux s k pre [] := by
          simp only [atMostKAux, ite_eq_left hk, hsv]
          exact List.mem_singleton_self _
        obtain ⟨l, hl, hv⟩ := hcl _ hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        obtain rfl : l = (v, false) := hl
        by_contra hle
        have hge : k + 1 ≤ cntS σ pre := by
          simp only [List.append_nil] at hle
          omega
        obtain ⟨v', hsv', hv'⟩ := hinv (k + 1) (by omega)
          (by simp [Nat.min_eq_right hk]) hge
        rw [hsv] at hsv'
        injection hsv' with hvv
        rw [← hvv] at hv'
        exact absurd hv' (by simp [hv])
      · have hpre : pre.length ≤ k := by omega
        simp only [List.append_nil]
        exact le_trans (cntS_le_length σ pre) hpre
    | cons x rest ih =>
      intro pre hinv hcl
      have hrow : ∀ C ∈ rowClauses s k (pre.length + 1) x, SatClause σ C :=
        fun C hC => hcl C (List.mem_append_left _ hC)
      have htl : ∀ C ∈ atMostKAux s k (pre ++ [x]) rest, SatClause σ C :=
        fun C hC => hcl C (List.mem_append_right _ hC)
      have hlen : (pre ++ [x]).length = pre.length + 1 := by simp
      have hcl_pre : cntS σ pre ≤ pre.length := cntS_le_length σ pre
      have hinv' : ∀ j, 1 ≤ j → j ≤ min (pre ++ [x]).length (k + 1) →
          j ≤ cntS σ (pre ++ [x]) → ∃ v, s (pre ++ [x]).length j = some v ∧ σ v = true := by
        intro j hj1 hj2 hj3
        rw [hlen] at hj2
        rw [cntS_append] at hj3
        obtain ⟨w, hsw⟩ := hok.some_of (i := pre.length + 1) (j := j) hj1 hj2
        have hswA : s (pre ++ [x]).length j = some w := by rw [hlen]; exact hsw
        cases hx : σ x
        · rw [cntS_singleton_false σ x hx, Nat.add_zero] at hj3
          obtain ⟨v, hsv, hv⟩ := hinv j hj1 (by omega) hj3
          have hmem : [(v, false), (w, true)] ∈ slotClauses s (pre.length + 1) j x := by
            by_cases hb : ∃ u, s pre.length (j - 1) = some u
            · obtain ⟨u, hu⟩ := hb
              simp [slotClauses, hsv, hsw, hu]
            · have hu : s pre.length (j - 1) = none := by
                cases h : s pre.length (j - 1) with
                | none => rfl
                | some u => exact absurd ⟨u, h⟩ hb
              simp [slotClauses, hsv, hsw, hu]
          rcases sat_two (hrow _ (mem_rowClauses hj1 hj2 hmem)) with h | h
          · rw [hv] at h; exact absurd h (by simp)
          · exact ⟨w, hswA, h⟩
        · rw [cntS_singleton_true σ x hx] at hj3
          by_cases hj : j = 1
          · subst hj
            have hb : s pre.length 0 = none := hok.none_of (i := pre.length) (j := 0) (by simp)
            have hmem : [(x, false), (w, true)] ∈ slotClauses s (pre.length + 1) 1 x := by
              by_cases ha : ∃ u, s pre.length 1 = some u
              · obtain ⟨u, hu⟩ := ha
                simp [slotClauses, hu, hb, hsw]
              · have hu : s pre.length 1 = none := by
                  cases h : s pre.length 1 with
                  | none => rfl
                  | some u => exact absurd ⟨u, h⟩ ha
                simp [slotClauses, hu, hb, hsw]
            rcases sat_two (hrow _ (mem_rowClauses (by omega) hj2 hmem)) with h | h
            · rw [hx] at h; exact absurd h (by simp)
            · exact ⟨w, hswA, h⟩
          · have hj2' : 2 ≤ j := by omega
            obtain ⟨v, hsv, hv⟩ := hinv (j - 1) (by omega) (by omega) (by omega)
            have hmem : [(v, false), (x, false), (w, true)] ∈
                slotClauses s (pre.length + 1) j x := by
              by_cases ha : ∃ u, s pre.length j = some u
              · obtain ⟨u, hu⟩ := ha
                simp [slotClauses, hu, hsv, hsw]
              · have hu : s pre.length j = none := by
                  cases h : s pre.length j with
                  | none => rfl
                  | some u => exact absurd ⟨u, h⟩ ha
                simp [slotClauses, hu, hsv, hsw]
            rcases sat_three (hrow _ (mem_rowClauses (by omega) hj2 hmem)) with h | h | h
            · rw [hv] at h; exact absurd h (by simp)
            · rw [hx] at h; exact absurd h (by simp)
            · exact ⟨w, hswA, h⟩
      have hgoal : (pre ++ x :: rest) = (pre ++ [x]) ++ rest := by
        rw [List.append_assoc, List.singleton_append]
      rw [hgoal]
      exact ih (pre ++ [x]) hinv' htl
  exact aux suf pre hinv0 hcl0

/-- **Soundness of the counter (the prefix-free form)**: the existence of a `σ` satisfying
all clauses implies that the number of true variables is at most `k`. -/
theorem atMostK_sat {σ : Assign} {s : Nat → Nat → Option Nat} {k : Nat}
    (hok : SlotOK s k) {xs : List Nat}
    (h : ∀ C ∈ atMostK s k xs, SatClause σ C) :
    cntS σ xs ≤ k := by
  have hinv0 : ∀ j, 1 ≤ j → j ≤ min ([] : List Nat).length (k + 1) →
      j ≤ cntS σ ([] : List Nat) → ∃ v, s ([] : List Nat).length j = some v ∧ σ v = true := by
    intro j hj1 hj2 _
    simp only [List.length_nil, Nat.min_eq_left (Nat.zero_le _), Nat.le_zero] at hj2
    omega
  have := atMostKAux_sat hok (pre := []) (suf := xs) hinv0 h
  simpa using this

/-! ## Assembly, matching `build_pair` of the external encoder -/

theorem satFormula_append {σ : Assign} {A B : CNF} :
    SatFormula σ (A ++ B) ↔ SatFormula σ A ∧ SatFormula σ B := by
  constructor
  · intro h
    exact ⟨fun C hC => h C (List.mem_append_left _ hC),
      fun C hC => h C (List.mem_append_right _ hC)⟩
  · rintro ⟨hA, hB⟩ C hC
    rcases List.mem_append.mp hC with h | h
    · exact hA C h
    · exact hB C h

/-- `SatFormula` is a `def` and does not unfold automatically at implicit transparency; use
this to obtain the `∀ C ∈ F` form. -/
theorem SatFormula.forall {σ : Assign} {F : CNF} (h : SatFormula σ F) :
    ∀ C ∈ F, SatClause σ C := h

theorem dotS_map (σ : Assign) (f : Nat → Nat) (l : List Nat) :
    dotS σ (l.map f) = dotS (fun t => σ (f t)) l := by
  induction l with
  | nil => rfl
  | cons j l ih => simp only [List.map_cons, dotS_cons, ih]

theorem dotS_congr {σ τ : Assign} {l : List Nat} (h : ∀ j ∈ l, σ j = τ j) :
    dotS σ l = dotS τ l := by
  induction l with
  | nil => rfl
  | cons j l ih =>
      have hj : σ j = τ j := h j (List.mem_cons_self ..)
      have hl : ∀ t ∈ l, σ t = τ t := fun t ht => h t (List.mem_cons_of_mem _ ht)
      simp only [dotS_cons, hj, ih hl]

/-- The invariance of the support size under a map, exchanging a list of variable numbers
for an assignment indexed by column. -/
theorem cntS_map (σ : Assign) (f : Nat → Nat) (l : List Nat) :
    cntS σ (l.map f) = cntS (fun t => σ (f t)) l := by
  simp only [cntS, List.filter_map, List.length_map, Function.comp_def]

/-- The block of product variables: `a_j ↔ x_j ∧ w_j`, with three clauses each. -/
def prodClauses (c n : Nat) : List Clause :=
  (List.range n).flatMap (fun j =>
    [[(c + j, false), (j, true)],
     [(c + j, false), (n + j, true)],
     [(c + j, true), (j, false), (n + j, false)]])

/-- The three clauses of the product block imply `a = x ∧ w`. -/
theorem prod_sat {σ : Assign} {a x w : Nat}
    (h1 : SatClause σ [(a, false), (x, true)])
    (h2 : SatClause σ [(a, false), (w, true)])
    (h3 : SatClause σ [(a, true), (x, false), (w, false)]) :
    σ a = (σ x && σ w) := by
  have k1 : σ a = false ∨ σ x = true := sat_two h1
  have k2 : σ a = false ∨ σ w = true := sat_two h2
  have k3 : σ a = true ∨ σ x = false ∨ σ w = false := sat_three h3
  by_cases ha : σ a = true
  · have hx : σ x = true := by
      rcases k1 with h | h
      · exact absurd h (by simp [ha])
      · exact h
    have hw : σ w = true := by
      rcases k2 with h | h
      · exact absurd h (by simp [ha])
      · exact h
    simp [ha, hx, hw]
  · have ha' : σ a = false := by
      cases hh : σ a with
      | false => rfl
      | true => exact absurd hh ha
    rcases k3 with h | h | h
    · exact absurd (ha' ▸ h) (by simp)
    · simp [ha', h]
    · simp [ha', h]

/-- All of the product block satisfied implies that every product variable takes the value
of the conjunction. -/
theorem prodClauses_sat {σ : Assign} {c n : Nat}
    (h : ∀ C ∈ prodClauses c n, SatClause σ C) :
    ∀ j < n, σ (c + j) = (σ j && σ (n + j)) := by
  intro j hj
  have mem : ∀ C ∈ [[(c + j, false), (j, true)],
      [(c + j, false), (n + j, true)],
      [(c + j, true), (j, false), (n + j, false)]], C ∈ prodClauses c n := by
    intro C hC
    refine List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, ?_⟩
    exact hC
  exact prod_sat (h _ (mem _ (by simp)))
    (h _ (mem _ (by simp))) (h _ (mem _ (by simp)))

/-- A sequence of `xorChain`s, one per row, returning the clauses and the next variable
number. -/
def chainsFrom (f : Nat → Nat) : List (List Nat) → Nat → List Clause × Nat
  | [], c => ([], c)
  | r :: rest, c =>
      let (cl, c') := xorChain (r.map f) false c
      let (cl', c'') := chainsFrom f rest c'
      (cl ++ cl', c'')

theorem chainsFrom_sat {σ : Assign} {f : Nat → Nat} {rows : List (List Nat)}
    (hne : ∀ r ∈ rows, r ≠ []) :
    ∀ c, (∀ C ∈ (chainsFrom f rows c).1, SatClause σ C) →
      ∀ r ∈ rows, dotS (fun t => σ (f t)) r = false := by
  induction rows with
  | nil => intro c h r hr; exact absurd hr (List.not_mem_nil)
  | cons r₀ rest ih =>
      intro c h r hr
      rcases List.mem_cons.mp hr with hmem | hr
      · rw [hmem]
        have hcl : ∀ C ∈ (xorChain (r₀.map f) false c).1, SatClause σ C :=
          fun C hC => h C (by simp only [chainsFrom]; exact List.mem_append_left _ hC)
        obtain ⟨x₀, rest₀, hx₀⟩ : ∃ x₀ rest₀, r₀.map f = x₀ :: rest₀ := by
          cases hm : r₀.map f with
          | nil => exact absurd (List.map_eq_nil_iff.mp hm) (hne r₀ (List.mem_cons_self ..))
          | cons x₀ rest₀ => exact ⟨x₀, rest₀, rfl⟩
        have hcl' : ∀ C ∈ (xorChainAux rest₀ false x₀ c).1, SatClause σ C := by
          rw [hx₀] at hcl
          simpa only [xorChain] using hcl
        have hsat : dotS σ (x₀ :: rest₀) = false :=
          xorChain_sat (want := false) (start := c) hcl'
        simpa only [← hx₀, dotS_map σ f r₀] using hsat
      · set c' := (xorChain (r₀.map f) false c).2 with hc'
        have hrest : ∀ C ∈ (chainsFrom f rest c').1, SatClause σ C := by
          intro C hC
          have hmem2 : C ∈ (chainsFrom f (r₀ :: rest) c).1 := by
            simp only [chainsFrom]
            exact List.mem_append_right _ (hc' ▸ hC)
          exact h C hmem2
        exact ih (fun r' hr' => hne r' (List.mem_cons_of_mem _ hr')) c' hrest r hr

/-- The slot base: the number of slots allocated before the `i`-th row (agreeing with the
row-major allocation order of the encoder). -/
def slotBase (k i : Nat) : Nat := ((List.range i).map (fun i' => min i' (k + 1))).sum

/-- The slot variable numbers of the sequential counter (`none` marks a constant
slot). -/
def slotVar (c k i j : Nat) : Option Nat :=
  if 1 ≤ j ∧ j ≤ min i (k + 1) then some (c + slotBase k i + (j - 1)) else none

theorem slotVar_ok (c k : Nat) : SlotOK (slotVar c k) k := by
  intro i j
  by_cases h : 1 ≤ j ∧ j ≤ min i (k + 1) <;> simp [slotVar, h]

/-- The kernel-constraint section (the rows of `x`, with variable number = column + 1),
together with the counter that follows it. -/
def kerClauses (Rker : List (List Nat)) (n : Nat) : List Clause :=
  (chainsFrom (fun j => j) Rker (2 * n)).1

/-- First unused auxiliary variable after the kernel constraints. -/
def c1Of (Rker : List (List Nat)) (n : Nat) : Nat :=
  (chainsFrom (fun j => j) Rker (2 * n)).2

/-- The pairing-constraint section (the rows of `w`, with variable number =
`n + column + 1`). -/
def pairClauses (Rker Rpair : List (List Nat)) (n : Nat) : List Clause :=
  (chainsFrom (fun j => n + j) Rpair (c1Of Rker n)).1

/-- First unused auxiliary variable after the pairing constraints. -/
def c2Of (Rker Rpair : List (List Nat)) (n : Nat) : Nat :=
  (chainsFrom (fun j => n + j) Rpair (c1Of Rker n)).2

/-- The product-variable section, together with the chain for `x·w = 1`. -/
def prodVars (Rker Rpair : List (List Nat)) (n : Nat) : List Nat :=
  (List.range n).map (fun j => c2Of Rker Rpair n + j)

/-- Clauses asserting that the componentwise product has odd parity. -/
def xwClauses (Rker Rpair : List (List Nat)) (n : Nat) : List Clause :=
  (xorChain (prodVars Rker Rpair n) true (c2Of Rker Rpair n + n)).1

/-- First unused auxiliary variable after the odd-pairing chain. -/
def c3Of (Rker Rpair : List (List Nat)) (n : Nat) : Nat :=
  (xorChain (prodVars Rker Rpair n) true (c2Of Rker Rpair n + n)).2

/-- **The encoding used by this package's pipeline**, transcribed verbatim from `build_pair`
of the external encoder.

Rows are given as **lists of column indices** (the form before `to_masks`):
`x_j ↔ variable j+1` and `w_j ↔ variable n+j+1`. The order of assembly must match verbatim
as well, otherwise the instance identity checked by `by decide` does not go through. -/
def buildPair (Rker Rpair : List (List Nat)) (n k : Nat) : CNF :=
  ((kerClauses Rker n ++ pairClauses Rker Rpair n) ++
    (prodClauses (c2Of Rker Rpair n) n ++ xwClauses Rker Rpair n)) ++
  atMostK (slotVar (c3Of Rker Rpair n) k) k (List.range n)

/-- **Encoding fidelity (the soundness direction)**: every satisfying assignment yields

* an `x` of weight at most `k` (`cntS` counts the true positions)
* `x` in the kernel of `Rker` and `w` in the kernel of `Rpair`
* `x.w = 1` (a pointwise conjunction followed by an XOR).

Together with `x.w = 1`, the third and fourth items make it impossible for `x` to lie in the
row space of `Rpair` (row space ⊆ (ker)⊥), that is, `x` is a **light logical operator**. -/
theorem buildPair_sat {Rker Rpair : List (List Nat)} {n k : Nat} {σ : Assign}
    (hn : 0 < n) (hne₁ : ∀ r ∈ Rker, r ≠ []) (hne₂ : ∀ r ∈ Rpair, r ≠ [])
    (h : SatFormula σ (buildPair Rker Rpair n k)) :
    cntS σ (List.range n) ≤ k ∧
    (∀ r ∈ Rker, dotS σ r = false) ∧
    (∀ r ∈ Rpair, dotS (fun t => σ (n + t)) r = false) ∧
    dotS (fun t => σ t && σ (n + t)) (List.range n) = true := by
  unfold buildPair at h
  obtain ⟨hHead, hE⟩ := satFormula_append.mp h
  obtain ⟨hAB, hCD⟩ := satFormula_append.mp hHead
  obtain ⟨hA, hB⟩ := satFormula_append.mp hAB
  obtain ⟨hC, hD⟩ := satFormula_append.mp hCD
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact atMostK_sat (s := slotVar (c3Of Rker Rpair n) k) (slotVar_ok _ k)
      (SatFormula.forall hE)
  · unfold kerClauses at hA
    exact chainsFrom_sat hne₁ (2 * n) (SatFormula.forall hA)
  · unfold pairClauses at hB
    exact chainsFrom_sat hne₂ (c1Of Rker n) (SatFormula.forall hB)
  · -- `x·w = 1`
    unfold xwClauses at hD
    have hne_prod : prodVars Rker Rpair n ≠ [] := by
      intro h0
      have hlen := congrArg List.length h0
      simp [prodVars, List.length_map, List.length_range] at hlen
      omega
    have hxw : dotS σ (prodVars Rker Rpair n) = true :=
      xorChain_sat' hne_prod (SatFormula.forall hD)
    rw [prodVars, dotS_map] at hxw
    rw [← hxw]
    apply dotS_congr
    intro j hj
    exact (prodClauses_sat (SatFormula.forall hC) j (List.mem_range.mp hj)).symm

end QECCertificates.LRAT
