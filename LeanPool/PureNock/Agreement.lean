/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import LeanPool.PureNock.Verb
public import LeanPool.PureNock.Semantics

/-!
# Agreement with the standard evaluator

`den` is a compositional Nat-level denotation of verbs using `evalN` at `*`
nodes. `den_step` proves one-step preservation; `runProgram_sound` is
small-step-to-big-step agreement.
-/

@[expose] public section

namespace Nock
namespace Verb

open Noun

/-! ### The compositional denotation `den` of a verb -/

/-- Compositional denotation: `*` nodes use `evalN`; operator nodes apply the matching
    `Nock.Noun` operator; `⊥`-nodes are cons; leaves are atoms. -/
def den : Nat → Verb → Option Noun
  | _,        .leaf k       => some (.atom k)
  | 0,        .node _ _ _   => none
  | fuel + 1, .node act l r =>
      match act with
      | .null  =>
          match den fuel l, den fuel r with
          | some a, some b => some (.cell a b)
          | _, _           => none
      | .star  =>
          match den fuel l, den fuel r with
          | some a, some b => evalN fuel a b
          | _, _           => none
      | .slot  =>
          match den fuel l, den fuel r with
          | some (.atom ax), some b => Noun.slot ax b
          | _, _                    => none
      | .equal =>
          match den fuel l, den fuel r with
          | some a, some b => some (Noun.tis a b)
          | _, _           => none
      | .minus =>
          match den fuel l, den fuel r with
          | some (.atom 3), some b => some (Noun.wut b)
          | some (.atom 4), some b => Noun.lus b
          | _, _                   => none
      | .edit  =>
          match r with
          | .node _ nw od =>
              match den fuel l, den fuel nw, den fuel od with
              | some (.atom ax), some n, some o => Noun.edit ax n o
              | _, _, _                          => none
          | .leaf _ => none
      | .wut   => none   -- unreachable (see Verb note 2a)

/-! ### `den` is fuel-monotone (same shape as `evalN_succ`) -/

theorem den_succ {n : Nat} {v : Verb} {r : Noun}
    (h : den n v = some r) : den (n + 1) v = some r := by
  induction n, v using den.induct generalizing r with
  | case1 k => simp only [den] at h ⊢; exact h
  | case5 f l r' a b hrb hla ih2 ih1 =>
      have hla' : den (f + 1) l = some a := ih2 hla
      have hrb' : den (f + 1) r' = some b := ih1 hrb
      simp only [den, hla, hrb] at h
      simp only [den, hla', hrb']
      exact evalN_succ h
  | _ => simp_all only [den, Option.some.injEq, reduceCtorEq]

theorem den_mono {n m : Nat} {v : Verb} {r : Noun}
    (hle : n ≤ m) (h : den n v = some r) : den m v = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact den_succ ih

/-! ### (A) `den` of a terminal noun-verb is the noun itself -/

theorem den_ofNoun : ∀ (n : Noun) (fuel : Nat), n.size ≤ fuel → den fuel (ofNoun n) = some n := by
  intro n
  induction n with
  | atom k => intro fuel _; simp [ofNoun, den]
  | cell l r ihl ihr =>
      intro fuel hf
      simp only [Noun.size] at hf
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfl : l.size ≤ f := by omega
      have hfr : r.size ≤ f := by omega
      simp only [ofNoun, den, ihl f hfl, ihr f hfr]

/-- Terminal verbs denote their underlying noun (given adequate fuel). -/
theorem den_terminal : ∀ (v : Verb) (fuel : Nat),
    isTerminal v = true → v.noun.size ≤ fuel → den fuel v = some v.noun := by
  intro v
  induction v with
  | leaf k => intro fuel _ _; simp [den, noun]
  | node a l r ihl ihr =>
      intro fuel hterm hsize
      simp only [isTerminal, Bool.and_eq_true] at hterm
      obtain ⟨⟨hnull, hl⟩, hr⟩ := hterm
      have ha : a = Action.null := by cases a <;> simp_all [Action.isNull]
      subst ha
      simp only [noun, Noun.size] at hsize ⊢
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfl : l.noun.size ≤ f := by omega
      have hfr : r.noun.size ≤ f := by omega
      simp only [den, ihl f hl hfl, ihr f hr hfr]

/-! ### (B) The initial program verb denotes exactly what `evalN` computes -/

-- main.tex:1090-1094  (`F = *[subject, formula]`)
/-- `den` of the initial program verb `*[s, f]` equals `evalN s f`. -/
theorem den_program (s f : Noun) (fuel : Nat) (hs : s.size ≤ fuel) (hf : f.size ≤ fuel) :
    den (fuel + 1) (program s f) = evalN fuel s f := by
  simp only [program, den, den_ofNoun s fuel hs, den_ofNoun f fuel hf]

/-- `den` of `*[s, f]` and `evalN s f` define the same partial function. -/
theorem den_iff_evalN (s f r : Noun) :
    (∃ fuel, den fuel (program s f) = some r) ↔ (∃ fuel, evalN fuel s f = some r) := by
  constructor
  · rintro ⟨fuel, h⟩
    refine ⟨max fuel (max s.size f.size), ?_⟩
    have hm : fuel ≤ max fuel (max s.size f.size) + 1 := by omega
    have hs : s.size ≤ max fuel (max s.size f.size) := by omega
    have hf : f.size ≤ max fuel (max s.size f.size) := by omega
    have := den_mono hm h
    rwa [den_program s f _ hs hf] at this
  · rintro ⟨fuel, h⟩
    refine ⟨max fuel (max s.size f.size) + 1, ?_⟩
    have hm : fuel ≤ max fuel (max s.size f.size) := by omega
    have hs : s.size ≤ max fuel (max s.size f.size) := by omega
    have hf : f.size ≤ max fuel (max s.size f.size) := by omega
    rw [den_program s f _ hs hf]
    exact evalN_mono hm h

/-! ### Small-step to big-step simulation -/

/-- A verb has a denotation when its evaluator succeeds with some finite fuel. -/
def Den (v : Verb) (x : Noun) : Prop := ∃ fuel, den fuel v = some x
/-- Natural-number Nock evaluation succeeds with some finite fuel. -/
def Ev (a b x : Noun) : Prop := ∃ fuel, evalN fuel a b = some x

theorem den_pair {l r a b} (hl : Den l a) (hr : Den r b) :
    ∃ f, den f l = some a ∧ den f r = some b := by
  obtain ⟨fl, hl⟩ := hl; obtain ⟨fr, hr⟩ := hr
  exact ⟨max fl fr, den_mono (Nat.le_max_left _ _) hl, den_mono (Nat.le_max_right _ _) hr⟩

theorem den_triple {a b c va vb vc} (ha : Den a va) (hb : Den b vb) (hc : Den c vc) :
    ∃ f, den f a = some va ∧ den f b = some vb ∧ den f c = some vc := by
  obtain ⟨fa, ha⟩ := ha; obtain ⟨fb, hb⟩ := hb; obtain ⟨fc, hc⟩ := hc
  refine ⟨max fa (max fb fc), den_mono (by omega) ha, den_mono (by omega) hb, den_mono (by omega)
    hc⟩

theorem Den_leaf {k x} : Den (.leaf k) x ↔ x = .atom k := by
  constructor
  · rintro ⟨fuel, h⟩; simp only [den] at h; exact (Option.some.inj h).symm
  · rintro rfl; exact ⟨0, by simp [den]⟩

theorem Den_null {l r x} : Den (.node .null l r) x ↔ ∃ a b, x = .cell a b ∧ Den l a ∧ Den r b := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [den] at h
    | succ f =>
      simp only [den] at h
      cases hl : den f l with
      | none => rw [hl] at h; simp at h
      | some a =>
        cases hr : den f r with
        | none => rw [hl, hr] at h; simp at h
        | some b =>
          rw [hl, hr] at h; simp only [Option.some.injEq] at h
          exact ⟨a, b, h.symm, ⟨f, hl⟩, ⟨f, hr⟩⟩
  · rintro ⟨a, b, rfl, hl, hr⟩
    obtain ⟨f, hl, hr⟩ := den_pair hl hr
    exact ⟨f + 1, by simp only [den, hl, hr]⟩

theorem Den_star {l r x} : Den (.node .star l r) x ↔ ∃ a b, Den l a ∧ Den r b ∧ Ev a b x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [den] at h
    | succ f =>
      simp only [den] at h
      cases hl : den f l with
      | none => rw [hl] at h; simp at h
      | some a =>
        cases hr : den f r with
        | none => rw [hl, hr] at h; simp at h
        | some b =>
          rw [hl, hr] at h
          exact ⟨a, b, ⟨f, hl⟩, ⟨f, hr⟩, ⟨f, h⟩⟩
  · rintro ⟨a, b, hl, hr, hev⟩
    obtain ⟨f, hl, hr⟩ := den_pair hl hr
    obtain ⟨fe, hev⟩ := hev
    refine ⟨max f fe + 1, ?_⟩
    simp only [den, den_mono (show f ≤ max f fe by omega) hl, den_mono (show f ≤ max f fe by omega)
      hr]
    exact evalN_mono (by omega) hev

theorem Den_slot {l r x} : Den (.node .slot l r) x ↔
    ∃ ax b, Den l (.atom ax) ∧ Den r b ∧ Noun.slot ax b = some x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [den] at h
    | succ f =>
      simp only [den] at h
      split at h
      · rename_i ax b hl hr
        exact ⟨ax, b, ⟨f, hl⟩, ⟨f, hr⟩, h⟩
      · simp at h
  · rintro ⟨ax, b, hl, hr, hs⟩
    obtain ⟨f, hl, hr⟩ := den_pair hl hr
    exact ⟨f + 1, by simp only [den, hl, hr]; exact hs⟩

theorem Den_equal {l r x} : Den (.node .equal l r) x ↔
    ∃ a b, Den l a ∧ Den r b ∧ x = Noun.tis a b := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [den] at h
    | succ f =>
      simp only [den] at h
      split at h
      · rename_i a b hl hr
        exact ⟨a, b, ⟨f, hl⟩, ⟨f, hr⟩, (Option.some.inj h).symm⟩
      · simp at h
  · rintro ⟨a, b, hl, hr, rfl⟩
    obtain ⟨f, hl, hr⟩ := den_pair hl hr
    exact ⟨f + 1, by simp only [den, hl, hr]⟩

theorem Den_minus {l r x} : Den (.node .minus l r) x ↔
    ∃ b, Den r b ∧ ((Den l (.atom 3) ∧ x = Noun.wut b) ∨ (Den l (.atom 4) ∧ Noun.lus b = some x)) :=
      by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [den] at h
    | succ f =>
      simp only [den] at h
      split at h
      · rename_i b hl hr
        exact ⟨b, ⟨f, hr⟩, Or.inl ⟨⟨f, hl⟩, (Option.some.inj h).symm⟩⟩
      · rename_i b hl hr
        exact ⟨b, ⟨f, hr⟩, Or.inr ⟨⟨f, hl⟩, h⟩⟩
      · simp at h
  · rintro ⟨b, hr, hor⟩
    rcases hor with ⟨hl, rfl⟩ | ⟨hl, hlus⟩
    · obtain ⟨f, hl, hr⟩ := den_pair hl hr
      exact ⟨f + 1, by simp only [den, hl, hr]⟩
    · obtain ⟨f, hl, hr⟩ := den_pair hl hr
      exact ⟨f + 1, by simp only [den, hl, hr]; exact hlus⟩

theorem Den_edit_node {l b nw od x} : Den (.node .edit l (.node b nw od)) x ↔
    ∃ ax n o, Den l (.atom ax) ∧ Den nw n ∧ Den od o ∧ Noun.edit ax n o = some x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [den] at h
    | succ f =>
      simp only [den] at h
      split at h
      · rename_i ax n o hl hnw hod
        exact ⟨ax, n, o, ⟨f, hl⟩, ⟨f, hnw⟩, ⟨f, hod⟩, h⟩
      · simp at h
  · rintro ⟨ax, n, o, hl, hnw, hod, he⟩
    obtain ⟨f, hl, hnw, hod⟩ := den_triple hl hnw hod
    exact ⟨f + 1, by simp only [den, hl, hnw, hod]; exact he⟩

theorem Den_edit_leaf {l k x} : ¬ Den (.node .edit l (.leaf k)) x := by
  rintro ⟨fuel, h⟩
  cases fuel with
  | zero => simp [den] at h
  | succ f => simp [den] at h

theorem Den_wut {l r x} : ¬ Den (.node .wut l r) x := by
  rintro ⟨fuel, h⟩
  cases fuel with
  | zero => simp [den] at h
  | succ f => simp [den] at h

theorem ev2 {s1 f1 x1 s2 f2 x2} (h1 : Ev s1 f1 x1) (h2 : Ev s2 f2 x2) :
    ∃ f, evalN f s1 f1 = some x1 ∧ evalN f s2 f2 = some x2 := by
  obtain ⟨a, h1⟩ := h1; obtain ⟨b, h2⟩ := h2
  exact ⟨max a b, evalN_mono (Nat.le_max_left _ _) h1, evalN_mono (Nat.le_max_right _ _) h2⟩

theorem ev3 {s1 f1 x1 s2 f2 x2 s3 f3 x3} (h1 : Ev s1 f1 x1) (h2 : Ev s2 f2 x2) (h3 : Ev s3 f3 x3) :
    ∃ f, evalN f s1 f1 = some x1 ∧ evalN f s2 f2 = some x2 ∧ evalN f s3 f3 = some x3 := by
  obtain ⟨a, h1⟩ := h1; obtain ⟨b, h2⟩ := h2; obtain ⟨c, h3⟩ := h3
  exact ⟨max a (max b c), evalN_mono (by omega) h1, evalN_mono (by omega) h2, evalN_mono (by omega)
    h3⟩

theorem EvN_autocons {subj hb hc d x} : Ev subj (.cell (.cell hb hc) d) x ↔
    ∃ l r, x = .cell l r ∧ Ev subj (.cell hb hc) l ∧ Ev subj d r := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN] at h
      split at h
      · rename_i l r hl hr
        exact ⟨l, r, (Option.some.inj h).symm, ⟨f, hl⟩, ⟨f, hr⟩⟩
      · simp at h
  · rintro ⟨l, r, rfl, hl, hr⟩
    obtain ⟨f, hl, hr⟩ := ev2 hl hr
    exact ⟨f + 1, by simp only [evalN, hl, hr]⟩

theorem EvN_op0 {subj tail x} : Ev subj (.cell (.atom 0) tail) x ↔
    ∃ ax, tail = .atom ax ∧ Noun.slot ax subj = some x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN] at h
      cases tail with
      | atom ax => exact ⟨ax, rfl, h⟩
      | cell => simp at h
  · rintro ⟨ax, rfl, hs⟩
    exact ⟨1, by simp only [evalN]; exact hs⟩

theorem EvN_op1 {subj tail x} : Ev subj (.cell (.atom 1) tail) x ↔ x = tail := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f => simp only [evalN] at h; exact (Option.some.inj h).symm
  · rintro rfl; exact ⟨1, by simp only [evalN]⟩

theorem EvN_op2 {subj tail x} : Ev subj (.cell (.atom 2) tail) x ↔
    ∃ hb hc sb sc, tail = .cell hb hc ∧ Ev subj hb sb ∧ Ev subj hc sc ∧ Ev sb sc x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN] at h
      cases tail with
      | atom => simp at h
      | cell hb hc =>
        simp only at h
        split at h
        · rename_i sb sc hsb hsc
          exact ⟨hb, hc, sb, sc, rfl, ⟨f, hsb⟩, ⟨f, hsc⟩, ⟨f, h⟩⟩
        · simp at h
  · rintro ⟨hb, hc, sb, sc, rfl, hsb, hsc, hx⟩
    obtain ⟨f, hsb, hsc, hx⟩ := ev3 hsb hsc hx
    exact ⟨f + 1, by simp only [evalN, hsb, hsc]; exact hx⟩

theorem EvN_op3 {subj tail x} : Ev subj (.cell (.atom 3) tail) x ↔
    ∃ y, Ev subj tail y ∧ x = Noun.wut y := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN, Option.map_eq_some_iff] at h
      obtain ⟨y, hy, hx⟩ := h
      exact ⟨y, ⟨f, hy⟩, hx.symm⟩
  · rintro ⟨y, ⟨fy, hy⟩, rfl⟩
    exact ⟨fy + 1, by simp only [evalN, hy, Option.map_some]⟩

theorem EvN_op4 {subj tail x} : Ev subj (.cell (.atom 4) tail) x ↔
    ∃ y, Ev subj tail y ∧ Noun.lus y = some x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN, Option.bind_eq_some_iff] at h
      obtain ⟨y, hy, hx⟩ := h
      exact ⟨y, ⟨f, hy⟩, hx⟩
  · rintro ⟨y, ⟨fy, hy⟩, hx⟩
    exact ⟨fy + 1, by simp only [evalN, hy]; exact hx⟩

theorem EvN_op5 {subj tail x} : Ev subj (.cell (.atom 5) tail) x ↔
    ∃ hb hc sb sc, tail = .cell hb hc ∧ Ev subj hb sb ∧ Ev subj hc sc ∧ x = Noun.tis sb sc := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN] at h
      cases tail with
      | atom => simp at h
      | cell hb hc =>
        simp only at h
        split at h
        · rename_i sb sc hsb hsc
          exact ⟨hb, hc, sb, sc, rfl, ⟨f, hsb⟩, ⟨f, hsc⟩, (Option.some.inj h).symm⟩
        · simp at h
  · rintro ⟨hb, hc, sb, sc, rfl, hsb, hsc, rfl⟩
    obtain ⟨f, hsb, hsc⟩ := ev2 hsb hsc
    exact ⟨f + 1, by simp only [evalN, hsb, hsc]⟩

theorem EvN_op7 {subj tail x} : Ev subj (.cell (.atom 7) tail) x ↔
    ∃ hb hc sb, tail = .cell hb hc ∧ Ev subj hb sb ∧ Ev sb hc x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN] at h
      cases tail with
      | atom => simp at h
      | cell hb hc =>
        simp only at h
        cases hsb : evalN f subj hb with
        | none => rw [hsb] at h; simp at h
        | some sb => rw [hsb] at h; exact ⟨hb, hc, sb, rfl, ⟨f, hsb⟩, ⟨f, h⟩⟩
  · rintro ⟨hb, hc, sb, rfl, hsb, hx⟩
    obtain ⟨f, hsb, hx⟩ := ev2 hsb hx
    exact ⟨f + 1, by simp only [evalN, hsb]; exact hx⟩

theorem EvN_op8 {subj tail x} : Ev subj (.cell (.atom 8) tail) x ↔
    ∃ hb hc sb, tail = .cell hb hc ∧ Ev subj hb sb ∧ Ev (.cell sb subj) hc x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN] at h
      cases tail with
      | atom => simp at h
      | cell hb hc =>
        simp only at h
        cases hsb : evalN f subj hb with
        | none => rw [hsb] at h; simp at h
        | some sb => rw [hsb] at h; exact ⟨hb, hc, sb, rfl, ⟨f, hsb⟩, ⟨f, h⟩⟩
  · rintro ⟨hb, hc, sb, rfl, hsb, hx⟩
    obtain ⟨f, hsb, hx⟩ := ev2 hsb hx
    exact ⟨f + 1, by simp only [evalN, hsb]; exact hx⟩

theorem EvN_op10 {subj tail x} : Ev subj (.cell (.atom 10) tail) x ↔
    ∃ ax c d new old, tail = .cell (.cell (.atom ax) c) d ∧
      Ev subj c new ∧ Ev subj d old ∧ Noun.edit ax new old = some x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN] at h
      split at h
      · rename_i ax c d
        split at h
        · rename_i new old hnew hold
          exact ⟨ax, c, d, new, old, rfl, ⟨f, hnew⟩, ⟨f, hold⟩, h⟩
        · simp at h
      · simp at h
  · rintro ⟨ax, c, d, new, old, rfl, hnew, hold, he⟩
    obtain ⟨f, hnew, hold⟩ := ev2 hnew hold
    refine ⟨f + 1, ?_⟩
    rw [evalN, hnew, hold]
    exact he

theorem EvN_op6 {subj tail x} : Ev subj (.cell (.atom 6) tail) x ↔
    ∃ b c d cv, tail = .cell b (.cell c d) ∧ Ev subj b cv ∧
      ((cv = .atom 0 ∧ Ev subj c x) ∨ (cv = .atom 1 ∧ Ev subj d x)) := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN] at h
      cases tail with
      | atom => simp at h
      | cell b rest =>
        cases rest with
        | atom => simp at h
        | cell c d =>
          simp only at h
          cases hb : evalN f subj b with
          | none => rw [hb] at h; simp at h
          | some bv =>
            cases bv with
            | cell => rw [hb] at h; simp at h
            | atom k =>
              rw [hb] at h
              cases k with
              | zero => exact ⟨b, c, d, .atom 0, rfl, ⟨f, hb⟩, Or.inl ⟨rfl, ⟨f, h⟩⟩⟩
              | succ k =>
                cases k with
                | zero => exact ⟨b, c, d, .atom 1, rfl, ⟨f, hb⟩, Or.inr ⟨rfl, ⟨f, h⟩⟩⟩
                | succ k => simp at h
  · rintro ⟨b, c, d, cv, rfl, hcv, hor⟩
    rcases hor with ⟨rfl, hc⟩ | ⟨rfl, hd⟩
    · obtain ⟨f, hcv, hc⟩ := ev2 hcv hc
      refine ⟨f + 1, ?_⟩; rw [evalN, hcv]; exact hc
    · obtain ⟨f, hcv, hd⟩ := ev2 hcv hd
      refine ⟨f + 1, ?_⟩; rw [evalN, hcv]; exact hd

theorem EvN_op9 {subj tail x} : Ev subj (.cell (.atom 9) tail) x ↔
    ∃ ax c core arm, tail = .cell (.atom ax) c ∧ Ev subj c core ∧
      Noun.slot ax core = some arm ∧ Ev core arm x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN] at h
      cases tail with
      | atom => simp at h
      | cell head c =>
        cases head with
        | cell => simp at h
        | atom ax =>
          simp only at h
          cases hcore : evalN f subj c with
          | none => rw [hcore] at h; simp at h
          | some core =>
            rw [hcore] at h
            simp only at h
            cases hslot : Noun.slot ax core with
            | none => rw [hslot] at h; simp at h
            | some arm =>
              rw [hslot] at h
              exact ⟨ax, c, core, arm, rfl, ⟨f, hcore⟩, hslot, ⟨f, h⟩⟩
  · rintro ⟨ax, c, core, arm, rfl, hcore, hslot, hx⟩
    obtain ⟨f, hcore, hx⟩ := ev2 hcore hx
    refine ⟨f + 1, ?_⟩
    rw [evalN]; simp only [hcore, hslot]; exact hx

/-! ### helpers: determinism of `den`, terminal denotation, `ofNoun` facts -/

theorem den_det {v r1 r2} (h1 : Den v r1) (h2 : Den v r2) : r1 = r2 := by
  obtain ⟨f1, h1⟩ := h1; obtain ⟨f2, h2⟩ := h2
  have k1 := den_mono (Nat.le_max_left f1 f2) h1
  have k2 := den_mono (Nat.le_max_right f1 f2) h2
  exact Option.some.inj (k1.symm.trans k2)

theorem Den_terminal_iff {v x} (ht : isTerminal v = true) : Den v x ↔ x = v.noun := by
  constructor
  · intro hd; exact den_det hd ⟨v.noun.size, den_terminal v v.noun.size ht (Nat.le_refl _)⟩
  · rintro rfl; exact ⟨v.noun.size, den_terminal v v.noun.size ht (Nat.le_refl _)⟩

theorem ofNoun_noun (n : Noun) : (ofNoun n).noun = n := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr => simp only [ofNoun, noun, ihl, ihr]

theorem ofNoun_terminal (n : Noun) : isTerminal (ofNoun n) = true := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr => simp [ofNoun, isTerminal, Action.isNull, ihl, ihr]

theorem Den_ofNoun_iff {n x} : Den (ofNoun n) x ↔ x = n := by
  rw [Den_terminal_iff (ofNoun_terminal n), ofNoun_noun]

/-! ### well-formedness: edit nodes never carry a pending r-child -/

/-- Every edit node has a non-pending right child, recursively throughout the verb. -/
def editOk : Verb → Bool
  | .leaf _ => true
  | .node a l r =>
      (match a with | .edit => !r.isPending | _ => true) && editOk l && editOk r

theorem editOk_ofNoun (n : Noun) : editOk (ofNoun n) = true := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr => simp [ofNoun, editOk, ihl, ihr]

theorem editOk_program (s f : Noun) : editOk (program s f) = true := by
  simp [program, editOk, editOk_ofNoun]

theorem editOk_null_eq {l r} : editOk (.node .null l r) = (editOk l && editOk r) := rfl
theorem editOk_star_eq {l r} : editOk (.node .star l r) = (editOk l && editOk r) := rfl

theorem editOk_children {a l r} (h : editOk (.node a l r) = true) :
    editOk l = true ∧ editOk r = true := by
  simp only [editOk, Bool.and_eq_true] at h; exact ⟨h.1.2, h.2⟩

/-! ### `slot` equation lemmas -/

theorem slot_one {n : Noun} : Noun.slot 1 n = some n := by simp [Noun.slot]
theorem slot_two {a b : Noun} : Noun.slot 2 (.cell a b) = some a := by simp [Noun.slot]
theorem slot_three {a b : Noun} : Noun.slot 3 (.cell a b) = some b := by simp [Noun.slot]
theorem slot_two_atom {k : Nat} : Noun.slot 2 (.atom k) = none := by simp [Noun.slot]
theorem slot_three_atom {k : Nat} : Noun.slot 3 (.atom k) = none := by simp [Noun.slot]
theorem lus_atom {k : Nat} : Noun.lus (.atom k) = some (.atom (k+1)) := by simp [Noun.lus]

/-- On a pair of atoms `[p,q]`, only axes `1,2,3` are addressable. -/
theorem slot_pair_some {p q : Nat} : ∀ (m : Nat) (v : Noun),
    Noun.slot m (.cell (.atom p) (.atom q)) = some v → m = 1 ∨ m = 2 ∨ m = 3 := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro v hv
    match m with
    | 0 => simp [Noun.slot] at hv
    | 1 => exact Or.inl rfl
    | 2 => exact Or.inr (Or.inl rfl)
    | 3 => exact Or.inr (Or.inr rfl)
    | (k+4) =>
        exfalso
        rw [Noun.slot] at hv
        cases hs : Noun.slot ((k+4)/2) (.cell (.atom p) (.atom q)) with
        | none => rw [hs] at hv; simp at hv
        | some w =>
            rw [hs] at hv
            rcases ih ((k+4)/2) (by omega) w hs with h1 | h2 | h3
            · omega
            · rw [h2, slot_two] at hs; obtain rfl := Option.some.inj hs; simp at hv
            · rw [h3, slot_three] at hs; obtain rfl := Option.some.inj hs; simp at hv

/-! ### STEP-LOCAL: a `reduce` on an operator-ready node preserves `Den` -/

theorem den_local_opReady {sub r₀ x} (hor : opReady sub = true) (hr : reduce sub = some r₀) :
    (Den sub x ↔ Den r₀ x) := by
  cases sub with
  | leaf => simp [opReady] at hor
  | node a l r =>
    simp only [opReady, Bool.and_eq_true] at hor
    obtain ⟨⟨hao, htl⟩, htr⟩ := hor
    have hDl : ∀ v, Den l v ↔ v = l.noun := fun v => Den_terminal_iff htl
    have hDr : ∀ v, Den r v ↔ v = r.noun := fun v => Den_terminal_iff htr
    have atominj : ∀ {ax' ax : Nat}, Den l (.atom ax') → l.noun = .atom ax → ax' = ax := by
      intro ax' ax hd he; have := (hDl _).1 hd; rw [he] at this; exact Noun.atom.inj this
    cases a with
    | null => simp [Action.isOperator] at hao
    | star => simp [Action.isOperator] at hao
    | wut => simp [reduce] at hr
    | equal =>
        rw [reduce] at hr; obtain rfl := Option.some.inj hr
        rw [Den_equal, Den_ofNoun_iff]
        constructor
        · rintro ⟨va, vb, hva, hvb, rfl⟩; rw [(hDl va).1 hva, (hDr vb).1 hvb]
        · rintro rfl; exact ⟨l.noun, r.noun, (hDl _).2 rfl, (hDr _).2 rfl, rfl⟩
    | slot =>
        rw [reduce] at hr
        rw [Den_slot]
        split at hr
        · rename_i ax heq
          rw [Option.map_eq_some_iff] at hr
          obtain ⟨sr, hslot, rfl⟩ := hr
          rw [Den_ofNoun_iff]
          constructor
          · rintro ⟨ax', b, hax', hb, hs⟩
            obtain rfl := atominj hax' heq
            rw [(hDr _).1 hb] at hs; rw [hs] at hslot; exact (Option.some.inj hslot)
          · rintro rfl
            exact ⟨ax, r.noun, (hDl _).2 heq.symm, (hDr _).2 rfl, hslot⟩
        · simp at hr
    | minus =>
        rw [reduce] at hr
        rw [Den_minus]
        split at hr
        · rename_i heq
          obtain rfl := Option.some.inj hr
          rw [Den_ofNoun_iff]
          constructor
          · rintro ⟨b, hb, hor2⟩
            rcases hor2 with ⟨_, hx⟩ | ⟨h4, _⟩
            · rw [(hDr _).1 hb] at hx; exact hx
            · exact absurd (atominj h4 heq) (by decide)
          · rintro rfl; exact ⟨r.noun, (hDr _).2 rfl, Or.inl ⟨(hDl _).2 heq.symm, rfl⟩⟩
        · rename_i heq
          rw [Option.map_eq_some_iff] at hr
          obtain ⟨sr, hlus, rfl⟩ := hr
          rw [Den_ofNoun_iff]
          constructor
          · rintro ⟨b, hb, hor2⟩
            rcases hor2 with ⟨h3, _⟩ | ⟨_, hlus2⟩
            · exact absurd (atominj h3 heq) (by decide)
            · rw [(hDr _).1 hb] at hlus2; rw [hlus2] at hlus; exact (Option.some.inj hlus)
          · rintro rfl; exact ⟨r.noun, (hDr _).2 rfl, Or.inr ⟨(hDl _).2 heq.symm, hlus⟩⟩
        · simp at hr
    | edit =>
        cases hln : l.noun with
        | cell => simp [reduce, hln] at hr
        | atom ax =>
            cases hr2 : r with
            | leaf => simp [reduce, hln, hr2] at hr
            | node b nw od =>
                simp only [reduce, hln, hr2, Option.map_eq_some_iff] at hr
                obtain ⟨er, hedit, rfl⟩ := hr
                have htr2 : isTerminal (.node b nw od) = true := hr2 ▸ htr
                simp only [isTerminal, Bool.and_eq_true] at htr2
                obtain ⟨⟨_, htnw⟩, htod⟩ := htr2
                have hDnw : ∀ v, Den nw v ↔ v = nw.noun := fun v => Den_terminal_iff htnw
                have hDod : ∀ v, Den od v ↔ v = od.noun := fun v => Den_terminal_iff htod
                rw [Den_edit_node, Den_ofNoun_iff]
                constructor
                · rintro ⟨ax', n, o, hax', hn, ho, he⟩
                  obtain rfl := atominj hax' hln
                  rw [(hDnw _).1 hn, (hDod _).1 ho] at he
                  rw [he] at hedit; exact (Option.some.inj hedit)
                · rintro rfl
                  exact ⟨ax, nw.noun, od.noun, (hDl _).2 hln.symm, (hDnw _).2 rfl, (hDod _).2 rfl,
                    hedit⟩

/-! ### STEP-LOCAL: a `reduce` (opcode `redex`) on an in-`D` node preserves `Den` -/

-- main.tex:1060-1076  (STEP-LOCAL: each opcode redex `reduce` preserves the denotation)
private theorem denotation_conditional_reduction {r₀ : Verb} {x : Noun} (n1 n2 : Verb) (htn2 :
  n2.isTerminal = true)
  (hn1 : ∀ (v : Noun), n1.Den v ↔ v = n1.noun)
  (star_term : ∀ (W : Verb) (p : Noun), W.isTerminal = true → ((node Action.star n1 W).Den p ↔ Ev
    n1.noun W.noun p))
  (hr :
    (match (generalizing := false) n2 with
      | node _ b c =>
        some
          (node Action.star n1
            (node Action.star c
              (node Action.null (leaf 0)
                (node Action.star (node Action.null (leaf 2) (leaf 3))
                  (node Action.null (leaf 0)
                    (node Action.star n1 (node Action.null (leaf 4) (node Action.null (leaf 4)
                      b))))))))
      | _ => none) =
      some r₀) :
  Ev n1.noun ((atom 6).cell n2.noun) x ↔ r₀.Den x := by
  cases n2 with
  | leaf => simp at hr
  | node bn b c =>
      obtain rfl := Option.some.inj hr
      simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
      obtain ⟨⟨_, htb⟩, htc⟩ := htn2
      have dStar : ∀ (W : Verb) y,
          (Den (Verb.node .star n1 W) y ↔ ∃ q, Den W q ∧ Ev n1.noun q y) := by
        intro W y; rw [Den_star]
        exact ⟨fun ⟨p,q,hp,hq,hev⟩ => ⟨q, hq, (hn1 p).1 hp ▸ hev⟩,
               fun ⟨q,hq,hev⟩ => ⟨n1.noun, q, (hn1 _).2 rfl, hq, hev⟩⟩
      have dStarC : ∀ (W : Verb) y,
          (Den (Verb.node .star c W) y ↔ ∃ q, Den W q ∧ Ev c.noun q y) := by
        intro W y; rw [Den_star]
        exact ⟨fun ⟨p,q,hp,hq,hev⟩ => ⟨q, hq, (Den_terminal_iff htc).1 hp ▸ hev⟩,
               fun ⟨q,hq,hev⟩ => ⟨c.noun, q, (Den_terminal_iff htc).2 rfl, hq, hev⟩⟩
      have hIarg : isTerminal (Verb.node .null (.leaf 4) (.node .null (.leaf 4) b)) = true := by
        simp [isTerminal, Action.isNull, htb]
      rw [EvN_op6]
      constructor
      · -- EvN_op6 ⇒ Den (macro)
        rintro ⟨B, C, D, cv, heq, hcv, hor⟩
        obtain ⟨hBeq, hCDeq⟩ := Noun.cell.inj heq
        subst hBeq
        rcases hor with ⟨rfl, hCx⟩ | ⟨rfl, hDx⟩
        · -- cv = 0 → head arm
          refine (dStar _ _).2 ⟨C, ?_, hCx⟩
          refine (dStarC _ _).2 ⟨Noun.cell (.atom 0) (.atom 2), ?_,
                  (EvN_op0).2 ⟨2, rfl, hCDeq ▸ slot_two⟩⟩
          refine (Den_null).2 ⟨.atom 0, .atom 2, rfl, Den_leaf.2 rfl, ?_⟩
          refine (Den_star).2 ⟨Noun.cell (.atom 2) (.atom 3), Noun.cell (.atom 0) (.atom 2),
                  (Den_null).2 ⟨.atom 2, .atom 3, rfl, Den_leaf.2 rfl, Den_leaf.2 rfl⟩, ?_,
                  (EvN_op0).2 ⟨2, rfl, slot_two⟩⟩
          refine (Den_null).2 ⟨.atom 0, .atom 2, rfl, Den_leaf.2 rfl, ?_⟩
          refine (dStar _ _).2 ⟨_, (Den_terminal_iff hIarg).2 rfl, ?_⟩
          exact (EvN_op4).2 ⟨.atom 1, (EvN_op4).2 ⟨.atom 0, hcv, lus_atom⟩, lus_atom⟩
        · -- cv = 1 → tail arm
          refine (dStar _ _).2 ⟨D, ?_, hDx⟩
          refine (dStarC _ _).2 ⟨Noun.cell (.atom 0) (.atom 3), ?_,
                  (EvN_op0).2 ⟨3, rfl, hCDeq ▸ slot_three⟩⟩
          refine (Den_null).2 ⟨.atom 0, .atom 3, rfl, Den_leaf.2 rfl, ?_⟩
          refine (Den_star).2 ⟨Noun.cell (.atom 2) (.atom 3), Noun.cell (.atom 0) (.atom 3),
                  (Den_null).2 ⟨.atom 2, .atom 3, rfl, Den_leaf.2 rfl, Den_leaf.2 rfl⟩, ?_,
                  (EvN_op0).2 ⟨3, rfl, slot_three⟩⟩
          refine (Den_null).2 ⟨.atom 0, .atom 3, rfl, Den_leaf.2 rfl, ?_⟩
          refine (dStar _ _).2 ⟨_, (Den_terminal_iff hIarg).2 rfl, ?_⟩
          exact (EvN_op4).2 ⟨.atom 2, (EvN_op4).2 ⟨.atom 1, hcv, lus_atom⟩, lus_atom⟩
      · -- Den (macro) ⇒ EvN_op6
        intro hmacro
        obtain ⟨qa0, ha0, hC4⟩ := (dStar _ _).1 hmacro
        obtain ⟨qb0, hb0, hC3⟩ := (dStarC _ _).1 ha0
        rw [Den_null] at hb0; obtain ⟨v0, vc0, rfl, hv0, hc0⟩ := hb0
        rw [Den_leaf] at hv0; subst hv0
        rw [Den_star] at hc0; obtain ⟨p23, qd0, hp23, hd0, hC2⟩ := hc0
        rw [Den_null] at hp23; obtain ⟨w2, w3, rfl, hw2, hw3⟩ := hp23
        rw [Den_leaf] at hw2 hw3; subst hw2; subst hw3
        rw [Den_null] at hd0; obtain ⟨u0, vinner, rfl, hu0, hinner⟩ := hd0
        rw [Den_leaf] at hu0; subst hu0
        rw [star_term _ _ hIarg] at hinner
        obtain ⟨y, hy1, hly⟩ := (EvN_op4).1 hinner
        obtain ⟨z, hz1, hlz⟩ := (EvN_op4).1 hy1
        cases z with
        | cell => simp [Noun.lus] at hlz
        | atom k =>
            rw [lus_atom] at hlz; obtain rfl := Option.some.inj hlz
            rw [lus_atom] at hly; obtain rfl := Option.some.inj hly
            obtain ⟨ax, hax, hs23⟩ := (EvN_op0).1 hC2
            have haxv : ax = k + 2 := by injection hax with h; omega
            subst haxv
            rcases slot_pair_some _ _ hs23 with h1 | h2 | h3
            · omega
            · -- k = 0
              have hk : k = 0 := by omega
              subst hk
              rw [slot_two] at hs23; obtain rfl := Option.some.inj hs23
              obtain ⟨ax', hax', hs3⟩ := (EvN_op0).1 hC3
              have : ax' = 2 := by injection hax' with h; omega
              subst this
              cases hcn : c.noun with
              | atom => rw [hcn, slot_two_atom] at hs3; simp at hs3
              | cell C D =>
                  rw [hcn, slot_two] at hs3; obtain rfl := Option.some.inj hs3
                  exact ⟨b.noun, C, D, .atom 0, rfl, hz1, Or.inl ⟨rfl, hC4⟩⟩
            · -- k = 1
              have hk : k = 1 := by omega
              subst hk
              rw [slot_three] at hs23; obtain rfl := Option.some.inj hs23
              obtain ⟨ax', hax', hs3⟩ := (EvN_op0).1 hC3
              have : ax' = 3 := by injection hax' with h; omega
              subst this
              cases hcn : c.noun with
              | atom => rw [hcn, slot_three_atom] at hs3; simp at hs3
              | cell C D =>
                  rw [hcn, slot_three] at hs3; obtain rfl := Option.some.inj hs3
                  exact ⟨b.noun, C, D, .atom 1, rfl, hz1, Or.inr ⟨rfl, hC4⟩⟩

private theorem denotation_composition_reduction {r₀ : Verb} {x : Noun} (n1 n2 : Verb) (htn2 :
  n2.isTerminal = true)
  (star_term : ∀ (W : Verb) (p : Noun), W.isTerminal = true → ((node Action.star n1 W).Den p ↔ Ev
    n1.noun W.noun p))
  (hr :
    (match (generalizing := false) n2 with
      | node _ b c => some (node Action.star (node Action.star n1 b) (node Action.star n1 c))
      | _ => none) =
      some r₀) :
  Ev n1.noun ((atom 2).cell n2.noun) x ↔ r₀.Den x := by
  cases n2 with
  | leaf => simp at hr
  | node bn b c =>
      obtain rfl := Option.some.inj hr
      simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
      obtain ⟨⟨_, htb⟩, htc⟩ := htn2
      rw [EvN_op2, Den_star]
      constructor
      · rintro ⟨hb, hc, sb, sc, heq, hsb, hsc, hev⟩
        obtain ⟨rfl, rfl⟩ := Noun.cell.inj heq
        exact ⟨sb, sc, (star_term _ _ htb).2 hsb, (star_term _ _ htc).2 hsc, hev⟩
      · rintro ⟨sb, sc, hsb, hsc, hev⟩
        exact ⟨b.noun, c.noun, sb, sc, rfl, (star_term _ _ htb).1 hsb,
               (star_term _ _ htc).1 hsc, hev⟩

theorem den_local_opcode {sub r₀ x} (hd : inOpcodeDomain sub = true) (hr : reduce sub = some r₀) :
    (Den sub x ↔ Den r₀ x) := by
  cases sub with
  | leaf => simp [inOpcodeDomain] at hd
  | node a n1 t =>
    cases t with
    | leaf => cases a <;> simp [inOpcodeDomain] at hd
    | node ra i n2 =>
      cases a with
      | null => simp [inOpcodeDomain] at hd
      | wut => simp [inOpcodeDomain] at hd
      | equal => simp [inOpcodeDomain] at hd
      | slot => simp [inOpcodeDomain] at hd
      | edit => simp [inOpcodeDomain] at hd
      | minus => simp [inOpcodeDomain] at hd
      | star =>
        simp only [inOpcodeDomain, Bool.and_eq_true] at hd
        obtain ⟨⟨⟨⟨htn1, hra⟩, hti⟩, htn2⟩, hhead⟩ := hd
        have htt : isTerminal (Verb.node ra i n2) = true := by
          simp only [isTerminal, Bool.and_eq_true]; exact ⟨⟨hra, hti⟩, htn2⟩
        have hn1 : ∀ v, Den n1 v ↔ v = n1.noun := fun v => Den_terminal_iff htn1
        have hn2 : ∀ v, Den n2 v ↔ v = n2.noun := fun v => Den_terminal_iff htn2
        have star_term : ∀ (W : Verb) (p : Noun), isTerminal W = true →
            (Den (Verb.node .star n1 W) p ↔ Ev n1.noun W.noun p) := by
          intro W p htW
          rw [Den_star]
          constructor
          · rintro ⟨va, vb, hva, hvb, hev⟩
            rw [(Den_terminal_iff htn1).1 hva, (Den_terminal_iff htW).1 hvb] at hev; exact hev
          · intro hev
            exact ⟨n1.noun, W.noun, (Den_terminal_iff htn1).2 rfl, (Den_terminal_iff htW).2 rfl,
              hev⟩
        have hsub : (Den (Verb.node .star n1 (.node ra i n2)) x
                     ↔ Ev n1.noun (Noun.cell i.noun n2.noun) x) := by
          rw [star_term (Verb.node ra i n2) x htt]; simp only [noun]
        rw [hsub]
        rw [reduce] at hr
        cases i with
        | node bi ic id =>
            rw [redex] at hr
            obtain rfl := Option.some.inj hr
            simp only [noun]
            rw [Den_null, EvN_autocons]
            constructor
            · rintro ⟨l, r, rfl, hl, hr⟩
              refine ⟨l, r, rfl, (star_term _ _ hti).2 ?_, (star_term _ _ htn2).2 hr⟩
              simpa [noun] using hl
            · rintro ⟨p, q, rfl, hp, hq⟩
              refine ⟨p, q, rfl, ?_, (star_term _ _ htn2).1 hq⟩
              have := (star_term (Verb.node bi ic id) p hti).1 hp
              simpa [noun] using this
        | leaf op =>
            simp only [noun]
            simp only [redex] at hr
            split at hr
            · -- op 0
              obtain rfl := Option.some.inj hr
              rw [EvN_op0, Den_slot]
              constructor
              · rintro ⟨ax, hax, hs⟩; exact ⟨ax, n1.noun, (hn2 _).2 hax.symm, (hn1 _).2 rfl, hs⟩
              · rintro ⟨ax, b, hax, hb, hs⟩
                rw [(hn1 _).1 hb] at hs; exact ⟨ax, ((hn2 _).1 hax).symm, hs⟩
            · -- op 1
              obtain rfl := Option.some.inj hr
              rw [EvN_op1]; exact (hn2 x).symm
            · -- op 2
              exact denotation_composition_reduction n1 n2 htn2 star_term hr
            · -- op 3
              obtain rfl := Option.some.inj hr
              rw [EvN_op3, Den_minus]
              constructor
              · rintro ⟨y, hy, rfl⟩
                exact ⟨y, (star_term _ _ htn2).2 hy, Or.inl ⟨(Den_leaf).2 rfl, rfl⟩⟩
              · rintro ⟨b, hb, hor⟩
                rcases hor with ⟨_, rfl⟩ | ⟨h4, _⟩
                · exact ⟨b, (star_term _ _ htn2).1 hb, rfl⟩
                · exact absurd ((Den_leaf).1 h4) (by decide)
            · -- op 4
              obtain rfl := Option.some.inj hr
              rw [EvN_op4, Den_minus]
              constructor
              · rintro ⟨y, hy, hlus⟩
                exact ⟨y, (star_term _ _ htn2).2 hy, Or.inr ⟨(Den_leaf).2 rfl, hlus⟩⟩
              · rintro ⟨b, hb, hor⟩
                rcases hor with ⟨h3, _⟩ | ⟨_, hlus⟩
                · exact absurd ((Den_leaf).1 h3) (by decide)
                · exact ⟨b, (star_term _ _ htn2).1 hb, hlus⟩
            · -- op 5
              cases n2 with
              | leaf => simp at hr
              | node bn b c =>
                  obtain rfl := Option.some.inj hr
                  simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
                  obtain ⟨⟨_, htb⟩, htc⟩ := htn2
                  rw [EvN_op5, Den_equal]
                  constructor
                  · rintro ⟨hb, hc, sb, sc, heq, hsb, hsc, rfl⟩
                    obtain ⟨rfl, rfl⟩ := Noun.cell.inj heq
                    exact ⟨sb, sc, (star_term _ _ htb).2 hsb, (star_term _ _ htc).2 hsc, rfl⟩
                  · rintro ⟨sb, sc, hsb, hsc, rfl⟩
                    exact ⟨b.noun, c.noun, sb, sc, rfl, (star_term _ _ htb).1 hsb,
                           (star_term _ _ htc).1 hsc, rfl⟩
            · -- op 6  (if-then-else macro; main.tex:1067)
              exact denotation_conditional_reduction n1 n2 htn2 hn1 star_term hr
            · -- op 7
              cases n2 with
              | leaf => simp at hr
              | node bn b c =>
                  obtain rfl := Option.some.inj hr
                  simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
                  obtain ⟨⟨_, htb⟩, htc⟩ := htn2
                  rw [EvN_op7, Den_star]
                  constructor
                  · rintro ⟨hb, hc, sb, heq, hsb, hev⟩
                    obtain ⟨rfl, rfl⟩ := Noun.cell.inj heq
                    exact ⟨sb, c.noun, (star_term _ _ htb).2 hsb, (Den_terminal_iff htc).2 rfl, hev⟩
                  · rintro ⟨p, q, hp, hq, hev⟩
                    rw [(Den_terminal_iff htc).1 hq] at hev
                    exact ⟨b.noun, c.noun, p, rfl, (star_term _ _ htb).1 hp, hev⟩
            · -- op 8
              cases n2 with
              | leaf => simp at hr
              | node bn b c =>
                  obtain rfl := Option.some.inj hr
                  simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
                  obtain ⟨⟨_, htb⟩, htc⟩ := htn2
                  rw [EvN_op8, Den_star]
                  constructor
                  · rintro ⟨hb, hc, sb, heq, hsb, hev⟩
                    obtain ⟨rfl, rfl⟩ := Noun.cell.inj heq
                    refine ⟨Noun.cell sb n1.noun, c.noun, ?_, (Den_terminal_iff htc).2 rfl, hev⟩
                    rw [Den_null]
                    exact ⟨sb, n1.noun, rfl, (star_term _ _ htb).2 hsb, (hn1 _).2 rfl⟩
                  · rintro ⟨p, q, hp, hq, hev⟩
                    rw [Den_null] at hp
                    obtain ⟨pb, pn, rfl, hpb, hpn⟩ := hp
                    rw [(hn1 _).1 hpn] at hev
                    rw [(Den_terminal_iff htc).1 hq] at hev
                    exact ⟨b.noun, c.noun, pb, rfl, (star_term _ _ htb).1 hpb, hev⟩
            · -- op 9
              cases n2 with
              | leaf => simp at hr
              | node bn b c =>
                  obtain rfl := Option.some.inj hr
                  simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
                  obtain ⟨⟨_, htb⟩, htc⟩ := htn2
                  have htform : isTerminal (Verb.node .null (.leaf 2)
                      (.node .null (.node .null (.leaf 0) (.leaf 1)) (.node .null (.leaf 0) b))) =
                        true := by
                    simp [isTerminal, Action.isNull, htb]
                  rw [EvN_op9, Den_star]
                  constructor
                  · rintro ⟨ax, c', core, arm, heq, hcore, hslot, hev⟩
                    obtain ⟨hbn, rfl⟩ := Noun.cell.inj heq
                    refine ⟨core, _, (star_term c core htc).2 hcore,
                            (Den_terminal_iff htform).2 rfl, ?_⟩
                    refine (EvN_op2).2 ⟨_, _, core, arm, rfl, ?_, ?_, hev⟩
                    · exact (EvN_op0).2 ⟨1, rfl, slot_one⟩
                    · exact (EvN_op0).2 ⟨ax, hbn, hslot⟩
                  · rintro ⟨p, q, hp, hq, hev⟩
                    have hp' := (star_term c p htc).1 hp
                    rw [(Den_terminal_iff htform).1 hq] at hev
                    obtain ⟨hb2, hc2, sb, sc, heq2, hsb, hsc, hev2⟩ := (EvN_op2).1 hev
                    obtain ⟨rfl, rfl⟩ := Noun.cell.inj heq2
                    obtain ⟨ax1, hax1, hs1⟩ := (EvN_op0).1 hsb
                    obtain ⟨ax2, hax2, hs2⟩ := (EvN_op0).1 hsc
                    have hax1' : ax1 = 1 := by injection hax1 with h; omega
                    rw [hax1', slot_one] at hs1; obtain rfl := Option.some.inj hs1
                    exact ⟨ax2, c.noun, p, sc, by rw [hax2], hp', hs2, hev2⟩
            · -- op 10
              cases n2 with
              | leaf => simp at hr
              | node bn hd d =>
                  cases hd with
                  | leaf => simp at hr
                  | node bhd ax c =>
                      obtain rfl := Option.some.inj hr
                      simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
                      obtain ⟨⟨_, ⟨_, htax⟩, htc⟩, htd⟩ := htn2
                      have hax : ∀ v, Den ax v ↔ v = ax.noun := fun v => Den_terminal_iff htax
                      rw [EvN_op10, Den_edit_node]
                      constructor
                      · rintro ⟨axv, cc, dd, new, old, heq, hnew, hold, hedit⟩
                        obtain ⟨heq1, rfl⟩ := Noun.cell.inj heq
                        obtain ⟨haxn, rfl⟩ := Noun.cell.inj heq1
                        exact ⟨axv, new, old, (hax _).2 haxn.symm, (star_term _ _ htc).2 hnew,
                               (star_term _ _ htd).2 hold, hedit⟩
                      · rintro ⟨axv, n, o, haxd, hn, ho, hedit⟩
                        refine ⟨axv, c.noun, d.noun, n, o, ?_, (star_term _ _ htc).1 hn,
                                (star_term _ _ htd).1 ho, hedit⟩
                        rw [(hax _).1 haxd]
            · -- default
              simp at hr

/-! ### STEP-CONG: `den`-congruence for splicing a den-equivalent redex back via `replaceAt` -/

/-- Structural relation: `w` is `v` with the subtree at one *pending* node replaced by a
    `Den`-equivalent verb.  `base` is restricted to pending nodes so it can never sit at an
    `edit` node's `⊥` r-child (where `den` reads structure), the one place congruence needs care. -/
inductive Rel : Verb → Verb → Prop where
  | leaf {k} : Rel (.leaf k) (.leaf k)
  | base {v w} : v.isPending = true → (∀ x, Den v x ↔ Den w x) → Rel v w
  | cong {a l l' r r'} : Rel l l' → Rel r r' → Rel (.node a l r) (.node a l' r')

theorem Rel.refl : ∀ v, Rel v v
  | .leaf _   => .leaf
  | .node _ l r => .cong (Rel.refl l) (Rel.refl r)

theorem replaceAux_counter (i : Nat) (new : Verb) : ∀ (v : Verb) (c : Nat),
    (replaceAux i new v c).1 = (enum v c).1 := by
  intro v
  induction v with
  | leaf k => intro c; simp [replaceAux, enum]
  | node a l r ihl ihr =>
      intro c
      simp only [replaceAux, enum]
      rw [ihl (c+1), ihr]

theorem replaceAux_rel (i : Nat) (r₀ : Verb) :
    ∀ (v : Verb) (c : Nat),
      (∀ sub, findAt i (enum v c).2 = some sub →
        sub.isPending = true ∧ (∀ x, Den sub x ↔ Den r₀ x)) →
      Rel v (replaceAux i r₀ v c).2 := by
  intro v
  induction v with
  | leaf k => intro c _; exact Rel.leaf
  | node a l r ihl ihr =>
      intro c hyp
      simp only [replaceAux]
      by_cases hci : c = i
      · subst hci
        have hf : findAt c (enum (.node a l r) c).2 = some (.node a l r) := by
          simp [enum, findAt]
        obtain ⟨hp, hd⟩ := hyp _ hf
        rw [ite_eq_left rfl]
        exact Rel.base hp hd
      · simp only [ite_eq_right hci]
        have hine : ¬ (i = c) := fun h => hci h.symm
        have hcL : (replaceAux i r₀ l (c+1)).1 = (enum l (c+1)).1 := replaceAux_counter i r₀ l (c+1)
        refine Rel.cong (ihl (c+1) ?_) ?_
        · intro sub hsub
          apply hyp sub
          simp only [enum, findAt, ite_eq_right hine]
          rw [findAt_append, hsub]
        · rw [hcL]
          apply ihr
          intro sub hsub
          apply hyp sub
          simp only [enum, findAt, ite_eq_right hine]
          rw [findAt_append]
          have hnone : findAt i (enum l (c+1)).2 = none := by
            apply findAt_eq_none
            intro q hq
            have := enum_index_range l (c+1) q hq
            have := enum_index_range r (enum l (c+1)).1 (i, sub) (findAt_some_mem hsub)
            omega
          rw [hnone, hsub]

/-- **STEP-CONG (den-preservation of `Rel`).**  If `Rel v w` and `v` is edit-well-formed,
    then `v` and `w` have the same denotation. -/
theorem Rel_den : ∀ (n : Nat) (v w : Verb), v.noun.size ≤ n → Rel v w → editOk v = true →
    ∀ x, (Den v x ↔ Den w x) := by
  intro n
  induction n with
  | zero => intro v w hn _ _ x; cases v <;> simp [Noun.size, Verb.noun] at hn
  | succ n ih =>
      intro v w hn hrel hok x
      cases hrel with
      | leaf => exact Iff.rfl
      | base _ hd => exact hd x
      | @cong a l l' r r' hl hr =>
          simp only [Verb.noun, Noun.size] at hn
          simp only [editOk, Bool.and_eq_true] at hok
          obtain ⟨⟨hcond, hokl⟩, hokr⟩ := hok
          have El : ∀ y, Den l y ↔ Den l' y := fun y => ih l l' (by omega) hl hokl y
          have Er : ∀ y, Den r y ↔ Den r' y := fun y => ih r r' (by omega) hr hokr y
          cases a with
          | null =>
              rw [Den_null, Den_null]
              exact ⟨fun ⟨p,q,he,hp,hq⟩ => ⟨p,q,he,(El p).1 hp,(Er q).1 hq⟩,
                     fun ⟨p,q,he,hp,hq⟩ => ⟨p,q,he,(El p).2 hp,(Er q).2 hq⟩⟩
          | star =>
              rw [Den_star, Den_star]
              exact ⟨fun ⟨p,q,hp,hq,he⟩ => ⟨p,q,(El p).1 hp,(Er q).1 hq,he⟩,
                     fun ⟨p,q,hp,hq,he⟩ => ⟨p,q,(El p).2 hp,(Er q).2 hq,he⟩⟩
          | slot =>
              rw [Den_slot, Den_slot]
              exact ⟨fun ⟨ax,b,hp,hq,hs⟩ => ⟨ax,b,(El _).1 hp,(Er _).1 hq,hs⟩,
                     fun ⟨ax,b,hp,hq,hs⟩ => ⟨ax,b,(El _).2 hp,(Er _).2 hq,hs⟩⟩
          | equal =>
              rw [Den_equal, Den_equal]
              exact ⟨fun ⟨p,q,hp,hq,he⟩ => ⟨p,q,(El p).1 hp,(Er q).1 hq,he⟩,
                     fun ⟨p,q,hp,hq,he⟩ => ⟨p,q,(El p).2 hp,(Er q).2 hq,he⟩⟩
          | minus =>
              rw [Den_minus, Den_minus]
              exact ⟨fun ⟨b,hq,hor⟩ => ⟨b,(Er _).1 hq,
                        hor.imp (fun ⟨h,e⟩ => ⟨(El _).1 h,e⟩) (fun ⟨h,e⟩ => ⟨(El _).1 h,e⟩)⟩,
                     fun ⟨b,hq,hor⟩ => ⟨b,(Er _).2 hq,
                        hor.imp (fun ⟨h,e⟩ => ⟨(El _).2 h,e⟩) (fun ⟨h,e⟩ => ⟨(El _).2 h,e⟩)⟩⟩
          | wut =>
              exact ⟨fun h => (Den_wut h).elim, fun h => (Den_wut h).elim⟩
          | edit =>
              cases hr with
              | leaf => exact ⟨fun h => (Den_edit_leaf h).elim, fun h => (Den_edit_leaf h).elim⟩
              | base hp _ =>
                  rw [hp] at hcond; simp at hcond
              | @cong b nw nw' od od' hnw hod =>
                  simp only [Verb.noun, Noun.size] at hn
                  simp only [editOk, Bool.and_eq_true] at hokr
                  obtain ⟨⟨_, hoknw⟩, hokod⟩ := hokr
                  have Enw : ∀ y, Den nw y ↔ Den nw' y := fun y => ih nw nw' (by omega) hnw hoknw y
                  have Eod : ∀ y, Den od y ↔ Den od' y := fun y => ih od od' (by omega) hod hokod y
                  rw [Den_edit_node, Den_edit_node]
                  exact ⟨fun ⟨ax,nn,oo,ha,hn2,ho,he⟩ =>
                          ⟨ax,nn,oo,(El _).1 ha,(Enw _).1 hn2,(Eod _).1 ho,he⟩,
                         fun ⟨ax,nn,oo,ha,hn2,ho,he⟩ =>
                          ⟨ax,nn,oo,(El _).2 ha,(Enw _).2 hn2,(Eod _).2 ho,he⟩⟩

/-! ### `editOk` is preserved by `next` (the invariant discharging `den_step`'s hypothesis) -/

theorem editOk_reduce {sub r₀} (hr : reduce sub = some r₀) (hok : editOk sub = true) :
    editOk r₀ = true := by
  cases sub with
  | leaf => simp [reduce] at hr
  | node a n1 t =>
    simp only [editOk, Bool.and_eq_true] at hok
    obtain ⟨⟨_, hokn1⟩, hokt⟩ := hok
    cases a with
    | null => simp [reduce] at hr
    | wut => simp [reduce] at hr
    | equal => rw [reduce] at hr; obtain rfl := Option.some.inj hr; exact editOk_ofNoun _
    | slot =>
        rw [reduce] at hr
        cases hln : n1.noun with
        | cell => simp [hln] at hr
        | atom ax =>
            rw [hln, Option.map_eq_some_iff] at hr
            obtain ⟨sr, _, rfl⟩ := hr; exact editOk_ofNoun _
    | minus =>
        rw [reduce] at hr
        split at hr
        · obtain rfl := Option.some.inj hr; exact editOk_ofNoun _
        · rw [Option.map_eq_some_iff] at hr; obtain ⟨sr, _, rfl⟩ := hr; exact editOk_ofNoun _
        · simp at hr
    | edit =>
        cases hln : n1.noun with
        | cell => simp [reduce, hln] at hr
        | atom ax =>
            cases t with
            | leaf => simp [reduce, hln] at hr
            | node b nw od =>
                simp only [reduce, hln, Option.map_eq_some_iff] at hr
                obtain ⟨sr, _, rfl⟩ := hr; exact editOk_ofNoun _
    | star =>
        -- redex
        cases t with
        | leaf => simp [reduce, redex] at hr
        | node ra i n2 =>
          simp only [editOk, Bool.and_eq_true] at hokt
          obtain ⟨⟨_, hoki⟩, hokn2⟩ := hokt
          rw [reduce] at hr
          cases i with
          | node bi ic id =>
              rw [redex] at hr
              obtain rfl := Option.some.inj hr
              simp only [editOk_null_eq, editOk_star_eq, hokn1, hoki, hokn2, Bool.and_self]
          | leaf op =>
              simp only [redex] at hr
              have ecell : ∀ (bn b c : _), n2 = Verb.node bn b c →
                  editOk b = true ∧ editOk c = true := by
                intro bn b c he; subst he; exact editOk_children hokn2
              split at hr
              · obtain rfl := Option.some.inj hr; simp [editOk, hokn1, hokn2]
              · obtain rfl := Option.some.inj hr; exact hokn2
              · cases n2 with
                | leaf => simp at hr
                | node bn b c =>
                    obtain ⟨hokb, hokc⟩ := ecell bn b c rfl
                    obtain rfl := Option.some.inj hr; simp [editOk, hokn1, hokb, hokc]
              · obtain rfl := Option.some.inj hr; simp [editOk, hokn1, hokn2]
              · obtain rfl := Option.some.inj hr; simp [editOk, hokn1, hokn2]
              · cases n2 with
                | leaf => simp at hr
                | node bn b c =>
                    obtain ⟨hokb, hokc⟩ := ecell bn b c rfl
                    obtain rfl := Option.some.inj hr; simp [editOk, hokn1, hokb, hokc]
              · cases n2 with
                | leaf => simp at hr
                | node bn b c =>
                    obtain ⟨hokb, hokc⟩ := ecell bn b c rfl
                    obtain rfl := Option.some.inj hr
                    simp [editOk, hokn1, hokb, hokc]
              · cases n2 with
                | leaf => simp at hr
                | node bn b c =>
                    obtain ⟨hokb, hokc⟩ := ecell bn b c rfl
                    obtain rfl := Option.some.inj hr; simp [editOk, hokn1, hokb, hokc]
              · cases n2 with
                | leaf => simp at hr
                | node bn b c =>
                    obtain ⟨hokb, hokc⟩ := ecell bn b c rfl
                    obtain rfl := Option.some.inj hr
                    simp [editOk, hokn1, hokb, hokc]
              · cases n2 with
                | leaf => simp at hr
                | node bn b c =>
                    obtain ⟨hokb, hokc⟩ := ecell bn b c rfl
                    obtain rfl := Option.some.inj hr
                    simp [editOk, hokn1, hokb, hokc]
              · cases n2 with
                | leaf => simp at hr
                | node bn hd d =>
                    cases hd with
                    | leaf => simp at hr
                    | node bhd ax c =>
                        obtain ⟨hokhd, hokd⟩ := editOk_children hokn2
                        obtain ⟨hokax, hokc⟩ := editOk_children hokhd
                        obtain rfl := Option.some.inj hr
                        simp [editOk, Verb.isPending, Action.isNull, hokn1, hokax, hokc, hokd]
              · simp at hr

theorem editOk_edit_cond {l r} (h : editOk (.node .edit l r) = true) : Verb.isPending r = false :=
  by
  simp only [editOk, Bool.and_eq_true] at h
  have := h.1.1
  simpa using this

theorem editOk_editN_eq {l r} : editOk (.node .edit l r) = (!Verb.isPending r && editOk l && editOk
  r) := rfl

theorem isPending_replaceAux (i : Nat) (r₀ : Verb) : ∀ (v : Verb) (c : Nat), c ≠ i →
    Verb.isPending (replaceAux i r₀ v c).2 = Verb.isPending v := by
  intro v c hci; cases v with
  | leaf => simp [replaceAux, Verb.isPending]
  | node a l r => simp [replaceAux, ite_eq_right hci, Verb.isPending]

theorem editOk_replaceAux (i : Nat) (r₀ : Verb) (hr0 : editOk r₀ = true) :
    ∀ (v : Verb) (c : Nat), editOk v = true →
      (∀ s, findAt i (enum v c).2 = some s → s.isPending = true) →
      editOk (replaceAux i r₀ v c).2 = true := by
  intro v
  induction v with
  | leaf k => intro c _ _; simp [replaceAux, editOk]
  | node a l r ihl ihr =>
      intro c hok hpend
      obtain ⟨hokl, hokr⟩ := editOk_children hok
      simp only [replaceAux]
      by_cases hci : c = i
      · subst hci; rw [ite_eq_left rfl]; exact hr0
      · simp only [ite_eq_right hci]
        have hine : ¬ (i = c) := fun h => hci h.symm
        have hcL : (replaceAux i r₀ l (c+1)).1 = (enum l (c+1)).1 := replaceAux_counter i r₀ l (c+1)
        have hpl : ∀ s, findAt i (enum l (c+1)).2 = some s → s.isPending = true := by
          intro s hs; apply hpend s; simp only [enum, findAt, ite_eq_right hine]; rw [findAt_append,
            hs]
        have hokl' : editOk (replaceAux i r₀ l (c+1)).2 = true := ihl (c+1) hokl hpl
        have hleftNone : ∀ s, findAt i (enum r (enum l (c+1)).1).2 = some s →
            findAt i (enum l (c+1)).2 = none := by
          intro s hs
          apply findAt_eq_none; intro q hq
          have := enum_index_range l (c+1) q hq
          have := enum_index_range r (enum l (c+1)).1 (i, s) (findAt_some_mem hs)
          omega
        have hpr : ∀ s, findAt i (enum r (enum l (c+1)).1).2 = some s → s.isPending = true := by
          intro s hs; apply hpend s
          simp only [enum, findAt, ite_eq_right hine]; rw [findAt_append, hleftNone s hs, hs]
        have hokr' : editOk (replaceAux i r₀ r (enum l (c+1)).1).2 = true :=
          ihr (enum l (c+1)).1 hokr hpr
        rw [hcL]
        cases a with
        | edit =>
            have hcond : Verb.isPending r = false := editOk_edit_cond hok
            have hnp : Verb.isPending (replaceAux i r₀ r (enum l (c+1)).1).2 = false := by
              by_cases hcLi : (enum l (c+1)).1 = i
              · cases r with
                | leaf => simp [replaceAux, Verb.isPending]
                | node b nw od =>
                    exfalso
                    have hn : findAt i (enum l (c+1)).2 = none := by
                      apply findAt_eq_none; intro q hq
                      have := enum_index_range l (c+1) q hq; omega
                    have hf : findAt i (enum (Verb.node .edit l (Verb.node b nw od)) c).2
                              = some (Verb.node b nw od) := by
                      simp only [enum, findAt, ite_eq_right hine, findAt_append, hn]
                      rw [← hcLi]; simp
                    have := hpend _ hf
                    rw [hcond] at this; simp at this
              · rw [isPending_replaceAux i r₀ r _ hcLi, hcond]
            simp only [editOk_editN_eq, hnp, hokl', hokr', Bool.not_false, Bool.and_self]
        | null => simp only [editOk_null_eq, hokl', hokr', Bool.and_self]
        | star => simp only [editOk_star_eq, hokl', hokr', Bool.and_self]
        | wut => simp only [editOk, hokl', hokr', Bool.and_self]
        | slot => simp only [editOk, hokl', hokr', Bool.and_self]
        | equal => simp only [editOk, hokl', hokr', Bool.and_self]
        | minus => simp only [editOk, hokl', hokr', Bool.and_self]

theorem editOk_enum : ∀ (v : Verb) (c : Nat), editOk v = true →
    ∀ p ∈ (enum v c).2, editOk p.2 = true := by
  intro v
  induction v with
  | leaf k => intro c _ p hp; simp [enum] at hp
  | node a l r ihl ihr =>
      intro c hok p hp
      obtain ⟨hokl, hokr⟩ := editOk_children hok
      simp only [enum, List.mem_cons, List.mem_append] at hp
      rcases hp with rfl | hpl | hpr
      · exact hok
      · exact ihl (c+1) hokl p hpl
      · exact ihr _ hokr p hpr

/-! ### STEP-LOCAL combined, `den_step`, and the `editOk` invariant threaded through -/

theorem den_local {sub r₀ x} (hd : inDomain sub = true) (hr : reduce sub = some r₀) :
    (Den sub x ↔ Den r₀ x) := by
  rw [inDomain, Bool.or_eq_true] at hd
  rcases hd with h | h
  · exact den_local_opcode h hr
  · exact den_local_opReady h hr

theorem editOk_next {v v'} (h : next v = some v') (hok : editOk v = true) : editOk v' = true := by
  obtain ⟨i, sub, r₀, hmax, hmap, hdom, hred, hv'⟩ := next_eq_some_iff.1 h
  have hoksub : editOk sub = true := editOk_enum v 0 hok (i, sub) (mem_nodes_of_map hmap)
  have hokr0 : editOk r₀ = true := editOk_reduce hred hoksub
  obtain ⟨w, hmapw, hpw⟩ := hmax.1
  have hpsub : Verb.isPending sub = true := (Option.some.inj (hmapw.symm.trans hmap)) ▸ hpw
  rw [hv', replaceAt]
  apply editOk_replaceAux i r₀ hokr0 v 0 hok
  intro s hs
  have hms : map i v = some s := hs
  exact (Option.some.inj (hms.symm.trans hmap)) ▸ hpsub

-- main.tex:1052,1156  (one `next`-step preserves `den`: small-step ↦ big-step adequacy)
theorem den_step {v v' : Verb} (hwf : editOk v = true) (h : next v = some v') {r : Noun} :
    (∃ fuel, den fuel v = some r) ↔ (∃ fuel, den fuel v' = some r) := by
  obtain ⟨i, sub, r₀, hmax, hmap, hdom, hred, hv'⟩ := next_eq_some_iff.1 h
  obtain ⟨w, hmapw, hpw⟩ := hmax.1
  have hpsub : Verb.isPending sub = true := (Option.some.inj (hmapw.symm.trans hmap)) ▸ hpw
  have hrel : Rel v v' := by
    rw [hv', replaceAt]
    apply replaceAux_rel i r₀ v 0
    intro s hs
    have hms : map i v = some s := hs
    have hss : s = sub := Option.some.inj (hms.symm.trans hmap)
    subst hss
    exact ⟨hpsub, fun x => den_local hdom hred⟩
  exact Rel_den v.noun.size v v' (Nat.le_refl _) hrel hwf r

theorem run_sound {v : Verb} {r : Noun} :
    ∀ fuel, editOk v = true → run fuel v = some r → (∃ f, den f v = some r) := by
  intro fuel
  induction fuel generalizing v with
  | zero => intro _ h; simp [run] at h
  | succ fuel ih =>
      intro hwf h
      rw [run] at h
      cases hnext : next v with
      | some v' =>
          rw [hnext] at h
          exact (den_step hwf hnext).2 (ih (editOk_next hnext hwf) h)
      | none =>
          rw [hnext] at h
          simp only [result] at h
          split at h
          · rename_i hterm
            have hr : v.noun = r := Option.some.inj h
            subst hr
            exact ⟨v.noun.size, den_terminal v v.noun.size hterm (Nat.le_refl _)⟩
          · simp at h

theorem runProgram_sound {s f r : Noun} {fuel : Nat}
    (h : runProgram fuel s f = some r) : ∃ fuel', evalN fuel' s f = some r := by
  have : ∃ f', den f' (program s f) = some r := run_sound fuel (editOk_program s f) h
  exact (den_iff_evalN s f r).1 this

/-! ### `edit`/`slot` characterization — the `%10` soundness relation

    `Noun.edit ax new old` (the `#` operator, opcode 10's structural write, `main.tex:1071`,
    `1587–1607`) replaces the subtree of `old` at axis `ax` with `new`.  The paper's
    `NockVMROM` excludes `%10` entirely, so this relation is stated nowhere in the manuscript;
    it is the noun-level soundness relation an `%edit`-table arithmetization must prove
    against.  Two **necessary** properties an `%edit`-table arithmetization must discharge
    (sufficiency / uniqueness of `res` is not proved here):

      * `slot_edit_eq`      — **read-back**: on a successful edit, reading axis `ax` of the
                              result yields `new`.
      * `slot_edit_sibling` — **sibling carry**: every off-path sibling encountered from `ax`
                              to the root is carried unchanged from `old` (the property whose
                              absence lets a fraudulent proof mutate an unrelated subtree).

    Both are over the fuel-free `Noun.slot`/`Noun.edit` (`Algorithm:Noun_Operators`,
    `main.tex:1537–1607`).  `Noun.edit` recurses bottom-up — it rebuilds each parent by
    pairing `new` with the sibling read from the *original* `old`, then edits the halved
    (parent) axis.  Read-back uses strong induction on `ax`; full sibling carry then follows by
    induction over the siblings encountered by that same `ax / 2` walk. -/

/-- The sibling axis of `ax = a+2`: its co-child under the shared parent `ax / 2`.
    Even axes are left children (sibling `ax+1`); odd axes are right children (sibling
    `ax-1`).  This is exactly the `sibAxis` local of `Noun.edit`'s `a+2` branch. -/
def siblingAxis (ax : Nat) : Nat := if ax % 2 == 0 then ax + 1 else ax - 1

/-- `SiblingOf ax sib` says that `sib` is an off-path sibling encountered while following
    `ax` toward the root: either the immediate sibling of `ax`, or a sibling of one of `ax`'s
    proper ancestors.  For example, both axes `5` and `3` are siblings of target axis `4`. -/
inductive SiblingOf : Nat → Nat → Prop where
  | immediate (a : Nat) : SiblingOf (a + 2) (siblingAxis (a + 2))
  | ancestor (a : Nat) {sib : Nat} : SiblingOf ((a + 2) / 2) sib → SiblingOf (a + 2) sib

/-- A sibling shares its parent: `siblingAxis (a+2) / 2 = (a+2) / 2`. -/
theorem siblingAxis_half (a : Nat) : siblingAxis (a + 2) / 2 = (a + 2) / 2 := by
  unfold siblingAxis
  by_cases hb : ((a + 2) % 2 == 0) = true
  · rw [ite_eq_left hb]
    have hbn : (a + 2) % 2 = 0 := by simpa using hb
    omega
  · rw [ite_eq_right hb]
    have hbn : (a + 2) % 2 ≠ 0 := by simpa using hb
    omega

/-- A sibling has the opposite parity to its axis. -/
theorem siblingAxis_parity (a : Nat) :
    ((siblingAxis (a + 2)) % 2 == 0) = !((a + 2) % 2 == 0) := by
  unfold siblingAxis
  by_cases hb : ((a + 2) % 2 == 0) = true
  · have hbn : (a + 2) % 2 = 0 := by simpa using hb
    rw [ite_eq_left hb, hb]
    have h1 : (a + 2 + 1) % 2 = 1 := by omega
    rw [h1]; decide
  · have hbf : ((a + 2) % 2 == 0) = false := by
      cases hh : (a + 2) % 2 == 0 with
      | true => exact absurd hh hb
      | false => rfl
    have hbn : (a + 2) % 2 ≠ 0 := by simpa using hb
    rw [ite_eq_right hb, hbf]
    have h0 : (a + 2 - 1) % 2 = 0 := by omega
    rw [h0]; decide

/-- **Read-back (`#`/`/` round-trip).**  If editing `old` at axis `ax` with `new` succeeds,
    reading axis `ax` of the result `res` returns `new`: `slot ax res = some new`
    (conditional on `edit ax new old = some res`).
    The "terminal replaced node equals the patch" half of the `%10` relation. -/
theorem slot_edit_eq :
    ∀ (ax : Nat) {new old res : Noun},
      Noun.edit ax new old = some res → Noun.slot ax res = some new := by
  intro ax
  induction ax using Nat.strongRecOn with
  | ind ax ih =>
    intro new old res h
    match ax with
    | 0 => rw [Noun.edit] at h; exact absurd h (by simp)
    | 1 =>
        rw [Noun.edit] at h
        obtain rfl := Option.some.inj h
        exact slot_one
    | (a + 2) =>
        rw [Noun.edit] at h
        simp only at h
        cases hs : Noun.slot (if (a + 2) % 2 == 0 then a + 2 + 1 else a + 2 - 1) old with
        | none => rw [hs] at h; exact absurd h (by simp)
        | some sib =>
            rw [hs] at h
            have hres :
                Noun.slot ((a + 2) / 2)
                    res
                  = some (if (a + 2) % 2 == 0 then Noun.cell new sib else Noun.cell sib new) :=
              ih ((a + 2) / 2) (by omega) h
            rw [Noun.slot, hres]
            by_cases hpar : ((a + 2) % 2 == 0) = true
            · simp only [hpar, ite_true]
            · simp only [Bool.not_eq_true] at hpar
              simp only [hpar, ite_false, Bool.false_eq_true]

/-- `slot` at any axis `≥ 2` in terms of the parent read `slot (m/2)` and the parity pick —
    the `slot` equation stated for a general `m` rather than the `a+2` constructor pattern. -/
theorem slot_ge_two (m : Nat) (hm : 2 ≤ m) (n : Noun) :
    Noun.slot m n
      = (match Noun.slot (m / 2) n with
         | some (.cell l r) => some (if m % 2 == 0 then l else r)
         | _ => none) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  simp only [Noun.slot]
  rfl

/-- The immediate sibling written into the rebuilt parent by one recursive `edit` step is
    carried unchanged from `old`. -/
private theorem slot_edit_immediate_sibling :
    ∀ (a : Nat) {new old res : Noun},
      Noun.edit (a + 2) new old = some res →
        Noun.slot (siblingAxis (a + 2)) res = Noun.slot (siblingAxis (a + 2)) old := by
  intro a new old res h
  rw [Noun.edit] at h
  simp only at h
  cases hs : Noun.slot (if (a + 2) % 2 == 0 then a + 2 + 1 else a + 2 - 1) old with
  | none => rw [hs] at h; exact absurd h (by simp)
  | some sib =>
      rw [hs] at h
      have hres : Noun.slot ((a + 2) / 2) res
            = some (if (a + 2) % 2 == 0 then Noun.cell new sib else Noun.cell sib new) :=
        slot_edit_eq ((a + 2) / 2) h
      have hsib_old : Noun.slot (siblingAxis (a + 2)) old = some sib := by
        unfold siblingAxis; exact hs
      have hge : 2 ≤ siblingAxis (a + 2) := by
        unfold siblingAxis
        by_cases hb : ((a + 2) % 2 == 0) = true
        · rw [ite_eq_left hb]; omega
        · rw [ite_eq_right hb]
          have hbn : (a + 2) % 2 ≠ 0 := by simpa using hb
          omega
      rw [hsib_old, slot_ge_two _ hge, siblingAxis_half, hres, siblingAxis_parity]
      by_cases hb : ((a + 2) % 2 == 0) = true
      · simp only [hb, ite_true, Bool.not_true, ite_false, Bool.false_eq_true]
      · have hbf : ((a + 2) % 2 == 0) = false := by
          cases hh : (a + 2) % 2 == 0 with
          | true => exact absurd hh hb
          | false => rfl
        simp only [hbf, ite_false, Bool.not_false, ite_true, Bool.false_eq_true]

/-- **Sibling carry.**  If editing `old` at axis `ax` succeeds, every off-path sibling subtree
    encountered from `ax` to the root is unchanged in the result.  Thus an edit cannot mutate
    either the target's immediate sibling or a sibling branching from any proper ancestor of the
    target. -/
theorem slot_edit_sibling {ax sib : Nat} (hsib : SiblingOf ax sib) :
    ∀ {new old res : Noun},
      Noun.edit ax new old = some res → Noun.slot sib res = Noun.slot sib old := by
  induction hsib with
  | immediate a =>
      intro new old res h
      exact slot_edit_immediate_sibling a h
  | ancestor a hsib ih =>
      intro new old res h
      rw [Noun.edit] at h
      simp only at h
      cases hs : Noun.slot (if (a + 2) % 2 == 0 then a + 2 + 1 else a + 2 - 1) old with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some sibling =>
          rw [hs] at h
          exact ih h

end Verb
end Nock
