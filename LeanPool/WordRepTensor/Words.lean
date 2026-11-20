/-
Copyright (c) 2026 Horace Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horace Dong
-/

module

public import LeanPool.WordRepTensor.Basic

/-!
# Words: prefix counts and the chord lemma

Part of the proof of the frozen statements of `Research/WordRepTensor/Challenge.lean`
(written by Claude while Codex was out of quota, 2026-09-28).

For distinct letters `x`, `y` of a word `w`, alternation (the frozen `Alternate`) is
characterised by prefix counts: if the first of the two letters to occur is `x`, then every
prefix `w.take j` contains at least as many `x` as `y` and at most one more; conversely, this
bound on all prefixes implies alternation. From this we get the *chord lemma*: in a word that
represents `G`, if `a ~ c ~ d ~ b` is a path, `a ~ b`, and the first occurrences of `a, c, d, b`
appear in this order, then `a ~ d` and `c ~ b`.
-/

@[expose] public section

namespace WordRepTensor

variable {V : Type} [DecidableEq V]

theorem noRepeat_nil : noRepeat ([] : List V) = true := rfl

theorem noRepeat_cons (a : V) (t : List V) :
    noRepeat (a :: t) = true ↔ noRepeat t = true ∧ ∀ b, t.head? = some b → a ≠ b := by
  cases t with
  | nil => simp [noRepeat]
  | cons b t =>
    simp only [noRepeat, Bool.and_eq_true, bne_iff_ne, ne_eq, List.head?_cons, Option.some.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, fun c hc => hc ▸ h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨h1 b rfl, h2⟩

theorem filter_swap (x y : V) (w : List V) :
    w.filter (fun z => z == x || z == y) = w.filter (fun z => z == y || z == x) := by
  congr 1
  funext z
  exact Bool.or_comm _ _

/-- Alternation with `x` first gives the prefix bounds. -/
theorem counts_of_alt : ∀ (w : List V) (x y : V), x ≠ y →
    noRepeat (w.filter (fun z => z == x || z == y)) = true →
    (∀ b, (w.filter (fun z => z == x || z == y)).head? = some b → b = x) →
    ∀ j, (w.take j).count y ≤ (w.take j).count x ∧
      (w.take j).count x ≤ (w.take j).count y + 1 := by
  intro w
  induction w with
  | nil => intro x y _ _ _ j; simp
  | cons a t ih =>
    intro x y hxy hnr hhead j
    cases j with
    | zero => simp
    | succ j =>
      rw [List.take_succ_cons, List.count_cons, List.count_cons]
      by_cases hax : a = x
      · subst hax
        have hf : (a :: t).filter (fun z => z == a || z == y) =
            a :: t.filter (fun z => z == a || z == y) := by simp
        rw [hf, noRepeat_cons] at hnr
        have hne : ∀ b, (t.filter (fun z => z == y || z == a)).head? = some b → b = y := by
          intro b hb
          rw [← filter_swap] at hb
          have hmem : b ∈ t.filter (fun z => z == a || z == y) := List.mem_of_mem_head? hb
          rw [List.mem_filter] at hmem
          have hba : b ≠ a := fun h => hnr.2 b hb h.symm
          simp only [Bool.or_eq_true, beq_iff_eq] at hmem
          rcases hmem.2 with h | h
          · exact absurd h hba
          · exact h
        have := ih y a (Ne.symm hxy) (by rw [← filter_swap]; exact hnr.1) hne j
        simp only [beq_self_eq_true, ite_true, beq_iff_eq]
        have hya : ¬ (a = y) := hxy
        simp only [hya, ite_false]
        omega
      · by_cases hay : a = y
        · subst hay
          exfalso
          have hf : (a :: t).filter (fun z => z == x || z == a) =
              a :: t.filter (fun z => z == x || z == a) := by simp
          rw [hf] at hhead
          exact hax (hhead a rfl)
        · have hf : (a :: t).filter (fun z => z == x || z == y) =
              t.filter (fun z => z == x || z == y) := by
            simp [hax, hay]
          rw [hf] at hnr hhead
          have := ih x y hxy hnr hhead j
          simp only [beq_iff_eq, hax, hay, ite_false]
          omega

/-- The prefix bounds give alternation, with `x` first. -/
theorem alt_of_counts : ∀ (w : List V) (x y : V), x ≠ y →
    (∀ j, (w.take j).count y ≤ (w.take j).count x ∧
      (w.take j).count x ≤ (w.take j).count y + 1) →
    noRepeat (w.filter (fun z => z == x || z == y)) = true ∧
      ∀ b, (w.filter (fun z => z == x || z == y)).head? = some b → b = x := by
  intro w
  induction w with
  | nil => intro x y _ _; simp [noRepeat]
  | cons a t ih =>
    intro x y hxy hc
    by_cases hax : a = x
    · subst hax
      have hc' : ∀ j, (t.take j).count a ≤ (t.take j).count y ∧
          (t.take j).count y ≤ (t.take j).count a + 1 := by
        intro j
        have h := hc (j + 1)
        rw [List.take_succ_cons, List.count_cons, List.count_cons] at h
        have hya : ¬ (a = y) := hxy
        simp only [beq_self_eq_true, ite_true, beq_iff_eq, hya, ite_false] at h
        omega
      obtain ⟨h1, h2⟩ := ih y a (Ne.symm hxy) hc'
      have hf : (a :: t).filter (fun z => z == a || z == y) =
          a :: t.filter (fun z => z == a || z == y) := by simp
      rw [hf]
      refine ⟨?_, ?_⟩
      · rw [noRepeat_cons]
        refine ⟨by rw [filter_swap]; exact h1, ?_⟩
        intro b hb hab
        rw [filter_swap] at hb
        exact hxy (hab.trans (h2 b hb))
      · intro b hb
        simpa using hb.symm
    · by_cases hay : a = y
      · subst hay
        exfalso
        have h := hc 1
        simp [hax] at h
      · have hc' : ∀ j, (t.take j).count y ≤ (t.take j).count x ∧
            (t.take j).count x ≤ (t.take j).count y + 1 := by
          intro j
          have h := hc (j + 1)
          rw [List.take_succ_cons, List.count_cons, List.count_cons] at h
          simp only [beq_iff_eq, hax, hay, ite_false] at h
          omega
        have hf : (a :: t).filter (fun z => z == x || z == y) =
            t.filter (fun z => z == x || z == y) := by
          simp [hax, hay]
        rw [hf]
        exact ih x y hxy hc'

/-- In `w`, the first of `x` and `y` to occur is the one with the smaller `idxOf`. -/
theorem filter_head_of_idxOf_lt (w : List V) (x y : V) (hx : x ∈ w)
    (hlt : w.idxOf x < w.idxOf y) :
    ∀ b, (w.filter (fun z => z == x || z == y)).head? = some b → b = x := by
  induction w with
  | nil => simp at hx
  | cons a t ih =>
    intro b hb
    by_cases hax : a = x
    · subst hax
      have hf : (a :: t).filter (fun z => z == a || z == y) =
          a :: t.filter (fun z => z == a || z == y) := by simp
      rw [hf] at hb
      simpa using hb.symm
    · have hay : a ≠ y := by
        intro hay
        subst hay
        simp [List.idxOf_cons_self] at hlt
      have hf : (a :: t).filter (fun z => z == x || z == y) =
          t.filter (fun z => z == x || z == y) := by
        simp [hax, hay]
      rw [hf] at hb
      have hx' : x ∈ t := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h.symm hax
        · exact h
      have hlt' : t.idxOf x < t.idxOf y := by
        rw [List.idxOf_cons_ne _ hax, List.idxOf_cons_ne _ hay] at hlt
        omega
      exact ih hx' hlt' b hb

/-- Prefix bounds for an edge of a represented graph, oriented by first occurrence. -/
theorem counts_of_adj {G : SimpleGraph V} {w : List V} (hw : Represents G w) {x y : V}
    (hxy : x ≠ y) (hadj : G.Adj x y) (hlt : w.idxOf x < w.idxOf y) :
    ∀ j, (w.take j).count y ≤ (w.take j).count x ∧
      (w.take j).count x ≤ (w.take j).count y + 1 :=
  counts_of_alt w x y hxy ((hw.2 x y hxy).mp hadj)
    (filter_head_of_idxOf_lt w x y (hw.1 x) hlt)

/-- The chord lemma. -/
theorem chord {G : SimpleGraph V} {w : List V} (hw : Represents G w) {a c d b : V}
    (hac : G.Adj a c) (hcd : G.Adj c d) (hdb : G.Adj d b) (hab : G.Adj a b)
    (h1 : w.idxOf a < w.idxOf c) (h2 : w.idxOf c < w.idxOf d) (h3 : w.idxOf d < w.idxOf b) :
    G.Adj a d ∧ G.Adj c b := by
  have hA := counts_of_adj hw hac.ne hac h1
  have hB := counts_of_adj hw hcd.ne hcd h2
  have hC := counts_of_adj hw hdb.ne hdb h3
  have hD := counts_of_adj hw hab.ne hab (by omega)
  have had : a ≠ d := fun h => by subst h; omega
  have hcb : c ≠ b := fun h => by subst h; omega
  constructor
  · refine (hw.2 a d had).mpr ?_
    refine (alt_of_counts w a d had ?_).1
    intro j
    have := hA j; have := hB j; have := hC j; have := hD j
    omega
  · refine (hw.2 c b hcb).mpr ?_
    refine (alt_of_counts w c b hcb ?_).1
    intro j
    have := hA j; have := hB j; have := hC j; have := hD j
    omega

end WordRepTensor
