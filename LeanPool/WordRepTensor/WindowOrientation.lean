/-
Copyright (c) 2026 Horace Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horace Dong
-/

module

public import LeanPool.WordRepTensor.WindowData

/-!
# The Mycielskians of odd cycles are not word-representable

Word-representability form of Kitaev–Pyatkin, Theorem 4 and Remark 5 (arXiv:2408.05066v1), and
of Hameed (Discrete Appl. Math. 359 (2024)) for the extended Mycielskian; written by Claude,
2026-09-28. The proof does not follow those papers.

Orient each edge of a represented graph from the vertex whose first occurrence comes first.
By the chord lemma (`WRWords.chord`), no directed path `a → c → d → b` with `a ~ b` misses a chord.
For `n ≥ 5`, look at the seven vertices `r, v i, v (i+1), v (i+2), u i, u (i+1), u (i+2)`: a
kernel-checked finite computation over every orientation of the window's edges that satisfies
the chord condition on the listed patterns shows that the state of the five edges between the
columns `i` and `i+1` (`v i – v (i+1)`, `v i – u (i+1)`, `u i – v (i+1)` and the root edges
`r – u i`, `r – u (i+1)`) and the state of the corresponding edges between the columns `i+1` and
`i+2` have different colours under a fixed 2-colouring.
Going once around the odd cycle gives a contradiction. For `n = 3` no orientation of the twelve
edges of `mu 3` passes the chord condition (again a kernel-checked computation).
-/

@[expose] public section

namespace WordRepTensor

open SimpleGraph

/-! ## Boolean checks -/

/-- Read the orientation of an edge in the given direction. -/
def arc (o : ℕ → Bool) (e : ℕ) (d : Bool) : Bool := if d then o e else !o e

/-- Test whether an orientation avoids all listed forbidden directed paths. -/
def cond3B (o : ℕ → Bool) (P : List Pat) : Bool :=
  P.all fun p => !(arc o p.e1 p.d1 && arc o p.e2 p.d2 && arc o p.e3 p.d3)

/-- Encode a list of oriented edge tests as a binary integer. -/
def stateOf (o : ℕ → Bool) (S : List (ℕ × Bool)) : ℕ :=
  S.foldr (fun ed acc => 2 * acc + (if arc o ed.1 ed.2 then 1 else 0)) 0

/-- Look up the colour of an encoded state, with false as the default. -/
def colOf (col : List Bool) (s : ℕ) : Bool := col.getD s false

/-- Enumerate all Boolean lists of the given length. -/
def allLists : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allLists n).flatMap fun l => [false :: l, true :: l]

theorem mem_allLists : ∀ l : List Bool, l ∈ allLists l.length
  | [] => by simp [allLists]
  | b :: l => by
    simp only [List.length_cons, allLists, List.mem_flatMap]
    exact ⟨l, mem_allLists l, by cases b <;> simp⟩

/-- Check that every admissible orientation has opposite input and output colours. -/
def flipOK (N : ℕ) (P : List Pat) (S0 S1 : List (ℕ × Bool)) (col : List Bool) : Bool :=
  (allLists N).all fun l =>
    !(cond3B (fun e => l.getD e false) P) ||
      (colOf col (stateOf (fun e => l.getD e false) S1) !=
        colOf col (stateOf (fun e => l.getD e false) S0))

/-- Check that every orientation contains a listed forbidden path. -/
def noneOK (N : ℕ) (P : List Pat) : Bool :=
  (allLists N).all fun l => !(cond3B (fun e => l.getD e false) P)

/-- Read the endpoints of the indexed edge in the given direction. -/
def edgeDir (E : List (Fin 7 × Fin 7)) (e : ℕ) (d : Bool) : Fin 7 × Fin 7 :=
  if d then E.getD e (0, 0) else (E.getD e (0, 0)).swap

/-- Test adjacency in the undirected graph represented by the edge list. -/
def wadjOf (E : List (Fin 7 × Fin 7)) (x y : Fin 7) : Bool :=
  E.any fun p => (p.1 == x && p.2 == y) || (p.1 == y && p.2 == x)

/-- Verify that a path uses the listed edges and has a closing edge with a missing chord. -/
def patValid (E : List (Fin 7 × Fin 7)) (p : Pat) : Bool :=
  decide (p.e1 < E.length) && decide (p.e2 < E.length) && decide (p.e3 < E.length) &&
  edgeDir E p.e1 p.d1 == (p.a, p.c) && edgeDir E p.e2 p.d2 == (p.c, p.d) &&
  edgeDir E p.e3 p.d3 == (p.d, p.b) &&
  p.a != p.c && p.c != p.d && p.d != p.b && p.a != p.b &&
  wadjOf E p.a p.c && wadjOf E p.c p.d && wadjOf E p.d p.b && wadjOf E p.a p.b &&
  !(wadjOf E p.a p.d && wadjOf E p.c p.b)

/-! ## From the Boolean checks to an actual orientation -/

theorem getD_map_range (N : ℕ) (oF : ℕ → Bool) (h : ∀ e, N ≤ e → oF e = false) :
    (fun e => ((List.range N).map oF).getD e false) = oF := by
  funext e
  by_cases he : e < N
  · simp [List.getD_eq_getElem?_getD, he]
  · rw [h e (by omega)]
    have hnone : (List.range N)[e]? = none := List.getElem?_eq_none (by simp; omega)
    simp [List.getD_eq_getElem?_getD, hnone]

theorem flip_of_flipOK {N : ℕ} {P : List Pat} {S0 S1 : List (ℕ × Bool)} {col : List Bool}
    (hOK : flipOK N P S0 S1 col = true) (oF : ℕ → Bool) (h : ∀ e, N ≤ e → oF e = false)
    (hc : cond3B oF P = true) :
    colOf col (stateOf oF S1) = !colOf col (stateOf oF S0) := by
  unfold flipOK at hOK
  rw [List.all_eq_true] at hOK
  have hmem : (List.range N).map oF ∈ allLists N := by
    simpa using mem_allLists ((List.range N).map oF)
  have := hOK _ hmem
  rw [getD_map_range N oF h, hc] at this
  revert this
  cases colOf col (stateOf oF S1) <;> cases colOf col (stateOf oF S0) <;> simp

theorem none_of_noneOK {N : ℕ} {P : List Pat} (hOK : noneOK N P = true) (oF : ℕ → Bool)
    (h : ∀ e, N ≤ e → oF e = false) : cond3B oF P = false := by
  unfold noneOK at hOK
  rw [List.all_eq_true] at hOK
  have hmem : (List.range N).map oF ∈ allLists N := by
    simpa using mem_allLists ((List.range N).map oF)
  have := hOK _ hmem
  rw [getD_map_range N oF h] at this
  simpa using this

section Orient

variable {V : Type} [DecidableEq V]

/-- The orientation of the edge list `E` (through `ι`) by first occurrences in `w`. -/
def orient (w : List V) (ι : Fin 7 → V) (E : List (Fin 7 × Fin 7)) (e : ℕ) : Bool :=
  if e < E.length then
    decide (w.idxOf (ι (E.getD e (0, 0)).1) < w.idxOf (ι (E.getD e (0, 0)).2))
  else false

theorem orient_out (w : List V) (ι : Fin 7 → V) (E : List (Fin 7 × Fin 7)) :
    ∀ e, E.length ≤ e → orient w ι E e = false := by
  intro e he
  simp [orient, show ¬ e < E.length by omega]

theorem arc_orient {w : List V} (hw : ∀ v, v ∈ w) {ι : Fin 7 → V} (hinj : Function.Injective ι)
    {E : List (Fin 7 × Fin 7)} {e : ℕ} {d : Bool} {x y : Fin 7} (he : e < E.length)
    (hxy : x ≠ y) (hE : edgeDir E e d = (x, y)) :
    arc (orient w ι E) e d = true ↔ w.idxOf (ι x) < w.idxOf (ι y) := by
  have hne : w.idxOf (ι x) ≠ w.idxOf (ι y) := by
    intro h
    exact hxy (hinj ((List.idxOf_inj (hw (ι x))).mp h))
  cases d
  · simp only [edgeDir, Bool.false_eq_true, ite_false] at hE
    have h1 : (E.getD e (0, 0)).1 = y := by rw [← Prod.swap_swap (E.getD e (0, 0)), hE]; rfl
    have h2 : (E.getD e (0, 0)).2 = x := by rw [← Prod.swap_swap (E.getD e (0, 0)), hE]; rfl
    simp only [arc, orient, he, ite_true, h1, h2, Bool.false_eq_true, ite_false,
      Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
    omega
  · simp only [edgeDir, ite_true] at hE
    simp only [arc, orient, he, ite_true, hE, decide_eq_true_eq]

/-- The chord condition holds for the orientation by first occurrences. -/
theorem cond3_of_word {G : SimpleGraph V} {w : List V} (hw : Represents G w) (ι : Fin 7 → V)
    (hinj : Function.Injective ι) (E : List (Fin 7 × Fin 7))
    (hadj : ∀ x y, G.Adj (ι x) (ι y) ↔ wadjOf E x y = true) (P : List Pat)
    (hP : P.all (patValid E) = true) : cond3B (orient w ι E) P = true := by
  unfold cond3B
  rw [List.all_eq_true] at hP ⊢
  intro p hp
  have hv := hP p hp
  simp only [patValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.and_eq_false_iff] at hv
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨he1, he2⟩, he3⟩, hd1⟩, hd2⟩, hd3⟩, hac⟩, hcd⟩, hdb⟩, hab⟩, wac⟩, wcd⟩,
    wdb⟩, wab⟩, hbad⟩ := hv
  rw [Bool.not_eq_true', Bool.and_eq_false_iff, Bool.and_eq_false_iff]
  by_contra hcon
  simp only [not_or, Bool.not_eq_false] at hcon
  obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
  rw [arc_orient hw.1 hinj he1 hac hd1] at h1
  rw [arc_orient hw.1 hinj he2 hcd hd2] at h2
  rw [arc_orient hw.1 hinj he3 hdb hd3] at h3
  obtain ⟨had, hcb⟩ := chord hw ((hadj _ _).mpr wac) ((hadj _ _).mpr wcd) ((hadj _ _).mpr wdb)
    ((hadj _ _).mpr wab) h1 h2 h3
  rw [hadj] at had hcb
  rcases hbad with h | h
  · exact absurd had (by simp [h])
  · exact absurd hcb (by simp [h])

end Orient

/-! ## Going around an odd cycle -/

open Fin.NatCast in
theorem no_flip_cycle {n : ℕ} [NeZero n] (hodd : n % 2 = 1) (c : Fin n → Bool)
    (h : ∀ i, c (i + 1) = !c i) : False := by
  have hg : ∀ j : ℕ, c (j : Fin n) = (c 0 ^^ (j % 2 == 1)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.cast_succ, h, ih]
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · have : (j + 1) % 2 = 1 := by omega
        simp [hj, this]
      · have : (j + 1) % 2 = 0 := by omega
        simp [hj, this]
  have := hg n
  rw [Fin.natCast_self, hodd] at this
  cases hc : c 0 <;> simp [hc] at this

end WordRepTensor
