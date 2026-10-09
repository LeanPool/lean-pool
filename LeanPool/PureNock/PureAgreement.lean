/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import LeanPool.PureNock.Agreement
public import LeanPool.PureNock.Trace
public import LeanPool.PureNock.PaperReference
public import Mathlib.Tactic.IntervalCases

/-!
# OP₀–OP₁₀ consistency and OP₁₁ extension

`denP` is `den` with `evalPaper` at `*` nodes. Also defines the OP₁₁ hint
machine (`nextHint`/`runHint`) by expanding hints at reduction time.
-/

@[expose] public section

namespace Nock
namespace Verb

open Noun

/-! ### OP₀–OP₁₀ denotation -/

/-- Like `den`, but `*` nodes use `evalPaper` (OP₀–OP₁₀; crashes on OP₁₁). -/
def denP : Nat → Verb → Option Noun
  | _,        .leaf k       => some (.atom k)
  | 0,        .node _ _ _   => none
  | fuel + 1, .node act l r =>
      match act with
      | .null  =>
          match denP fuel l, denP fuel r with
          | some a, some b => some (.cell a b)
          | _, _           => none
      | .star  =>
          match denP fuel l, denP fuel r with
          | some a, some b => evalPaper fuel a b
          | _, _           => none
      | .slot  =>
          match denP fuel l, denP fuel r with
          | some (.atom ax), some b => Noun.slot ax b
          | _, _                    => none
      | .equal =>
          match denP fuel l, denP fuel r with
          | some a, some b => some (Noun.tis a b)
          | _, _           => none
      | .minus =>
          match denP fuel l, denP fuel r with
          | some (.atom 3), some b => some (Noun.wut b)
          | some (.atom 4), some b => Noun.lus b
          | _, _                   => none
      | .edit  =>
          match r with
          | .node _ nw od =>
              match denP fuel l, denP fuel nw, denP fuel od with
              | some (.atom ax), some n, some o => Noun.edit ax n o
              | _, _, _                          => none
          | .leaf _ => none
      | .wut   => none

theorem denP_succ {n : Nat} {v : Verb} {r : Noun}
    (h : denP n v = some r) : denP (n + 1) v = some r := by
  induction n, v using denP.induct generalizing r with
  | case1 k => simp only [denP] at h ⊢; exact h
  | case5 f l r' a b hrb hla ih2 ih1 =>
      have hla' : denP (f + 1) l = some a := ih2 hla
      have hrb' : denP (f + 1) r' = some b := ih1 hrb
      simp only [denP, hla, hrb] at h
      simp only [denP, hla', hrb']
      exact evalPaper_succ h
  | _ => simp_all only [denP, Option.some.injEq, reduceCtorEq]

theorem denP_mono {n m : Nat} {v : Verb} {r : Noun}
    (hle : n ≤ m) (h : denP n v = some r) : denP m v = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact denP_succ ih

/-- `denP` of any terminal verb is its underlying noun (given adequate fuel).  Identical to
    `den_terminal`: a terminal verb has no `*`-node, so `evalPaper`/`evalN` never enter. -/
theorem denP_terminal : ∀ (v : Verb) (fuel : Nat),
    isTerminal v = true → v.noun.size ≤ fuel → denP fuel v = some v.noun := by
  intro v
  induction v with
  | leaf k => intro fuel _ _; simp [denP, noun]
  | node a l r ihl ihr =>
      intro fuel hterm hsize
      simp only [isTerminal, Bool.and_eq_true] at hterm
      obtain ⟨⟨hnull, hl⟩, hr⟩ := hterm
      have ha : a = Action.null := by cases a <;> simp_all only [Action.isNull, reduceCtorEq]
      subst ha
      simp only [noun, Noun.size] at hsize ⊢
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfl : l.noun.size ≤ f := by omega
      have hfr : r.noun.size ≤ f := by omega
      simp only [denP, ihl f hl hfl, ihr f hr hfr]

/-- `denP` of the terminal verb `ofNoun n` is `n` (given adequate fuel; cf. `den_ofNoun`). -/
theorem denP_ofNoun : ∀ (n : Noun) (fuel : Nat), n.size ≤ fuel → denP fuel (ofNoun n) = some n := by
  intro n
  induction n with
  | atom k => intro fuel _; simp [ofNoun, denP]
  | cell l r ihl ihr =>
      intro fuel hf
      simp only [Noun.size] at hf
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfl : l.size ≤ f := by omega
      have hfr : r.size ≤ f := by omega
      simp only [ofNoun, denP, ihl f hfl, ihr f hfr]

/-- `denP` of the initial program verb `*[s, f]` is `evalPaper s f` (cf. `den_program`). -/
theorem denP_program (s f : Noun) (fuel : Nat) (hs : s.size ≤ fuel) (hf : f.size ≤ fuel) :
    denP (fuel + 1) (program s f) = evalPaper fuel s f := by
  simp only [program, denP, denP_ofNoun s fuel hs, denP_ofNoun f fuel hf]

/-- **`denP` ≡ `evalPaper` on program verbs, as partial functions** (cf. `den_iff_evalN`). -/
theorem denP_iff_evalPaper (s f r : Noun) :
    (∃ fuel, denP fuel (program s f) = some r) ↔ (∃ fuel, evalPaper fuel s f = some r) := by
  constructor
  · rintro ⟨fuel, h⟩
    refine ⟨max fuel (max s.size f.size), ?_⟩
    have hm : fuel ≤ max fuel (max s.size f.size) + 1 := by omega
    have hs : s.size ≤ max fuel (max s.size f.size) := by omega
    have hf : f.size ≤ max fuel (max s.size f.size) := by omega
    have := denP_mono hm h
    rwa [denP_program s f _ hs hf] at this
  · rintro ⟨fuel, h⟩
    refine ⟨max fuel (max s.size f.size) + 1, ?_⟩
    have hm : fuel ≤ max fuel (max s.size f.size) := by omega
    have hs : s.size ≤ max fuel (max s.size f.size) := by omega
    have hf : f.size ≤ max fuel (max s.size f.size) := by omega
    rw [denP_program s f _ hs hf]
    exact evalPaper_mono hm h

/-- A verb has a paper-fragment denotation at some finite fuel. -/
def DenP (v : Verb) (x : Noun) : Prop := ∃ fuel, denP fuel v = some x

/-- Paper-fragment Nock evaluation succeeds with some finite fuel. -/
def EvP (a b x : Noun) : Prop := ∃ fuel, evalPaper fuel a b = some x

theorem denP_pair {l r a b} (hl : DenP l a) (hr : DenP r b) :
    ∃ f, denP f l = some a ∧ denP f r = some b := by
  obtain ⟨fl, hl⟩ := hl; obtain ⟨fr, hr⟩ := hr
  exact ⟨max fl fr, denP_mono (Nat.le_max_left _ _) hl, denP_mono (Nat.le_max_right _ _) hr⟩

theorem denP_triple {a b c va vb vc} (ha : DenP a va) (hb : DenP b vb) (hc : DenP c vc) :
    ∃ f, denP f a = some va ∧ denP f b = some vb ∧ denP f c = some vc := by
  obtain ⟨fa, ha⟩ := ha; obtain ⟨fb, hb⟩ := hb; obtain ⟨fc, hc⟩ := hc
  refine ⟨max fa (max fb fc), denP_mono (by omega) ha, denP_mono (by omega) hb,
    denP_mono (by omega) hc⟩

theorem denP_det {v r1 r2} (h1 : DenP v r1) (h2 : DenP v r2) : r1 = r2 := by
  obtain ⟨f1, h1⟩ := h1; obtain ⟨f2, h2⟩ := h2
  have k1 := denP_mono (Nat.le_max_left f1 f2) h1
  have k2 := denP_mono (Nat.le_max_right f1 f2) h2
  exact Option.some.inj (k1.symm.trans k2)

theorem ev2P {s1 f1 x1 s2 f2 x2} (h1 : EvP s1 f1 x1) (h2 : EvP s2 f2 x2) :
    ∃ f, evalPaper f s1 f1 = some x1 ∧ evalPaper f s2 f2 = some x2 := by
  obtain ⟨a, h1⟩ := h1; obtain ⟨b, h2⟩ := h2
  exact ⟨max a b, evalPaper_mono (Nat.le_max_left _ _) h1, evalPaper_mono (Nat.le_max_right _ _) h2⟩

theorem ev3P {s1 f1 x1 s2 f2 x2 s3 f3 x3}
    (h1 : EvP s1 f1 x1) (h2 : EvP s2 f2 x2) (h3 : EvP s3 f3 x3) :
    ∃ f, evalPaper f s1 f1 = some x1 ∧ evalPaper f s2 f2 = some x2 ∧ evalPaper f s3 f3 = some x3 :=
      by
  obtain ⟨a, h1⟩ := h1; obtain ⟨b, h2⟩ := h2; obtain ⟨c, h3⟩ := h3
  exact ⟨max a (max b c), evalPaper_mono (by omega) h1, evalPaper_mono (by omega) h2,
    evalPaper_mono (by omega) h3⟩

/-! ### `EvP` inversions (evalPaper analogues of the `EvN_*` family) -/

theorem EvP_autocons {subj hb hc d x} : EvP subj (.cell (.cell hb hc) d) x ↔
    ∃ l r, x = .cell l r ∧ EvP subj (.cell hb hc) l ∧ EvP subj d r := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f =>
      simp only [evalPaper] at h
      split at h
      · rename_i l r hl hr
        exact ⟨l, r, (Option.some.inj h).symm, ⟨f, hl⟩, ⟨f, hr⟩⟩
      · simp at h
  · rintro ⟨l, r, rfl, hl, hr⟩
    obtain ⟨f, hl, hr⟩ := ev2P hl hr
    exact ⟨f + 1, by simp only [evalPaper, hl, hr]⟩

theorem EvP_op0 {subj tail x} : EvP subj (.cell (.atom 0) tail) x ↔
    ∃ ax, tail = .atom ax ∧ Noun.slot ax subj = some x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f =>
      simp only [evalPaper] at h
      cases tail with
      | atom ax => exact ⟨ax, rfl, h⟩
      | cell => simp at h
  · rintro ⟨ax, rfl, hs⟩
    exact ⟨1, by simp only [evalPaper]; exact hs⟩

theorem EvP_op1 {subj tail x} : EvP subj (.cell (.atom 1) tail) x ↔ x = tail := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f => simp only [evalPaper] at h; exact (Option.some.inj h).symm
  · rintro rfl; exact ⟨1, by simp only [evalPaper]⟩

theorem EvP_op2 {subj tail x} : EvP subj (.cell (.atom 2) tail) x ↔
    ∃ hb hc sb sc, tail = .cell hb hc ∧ EvP subj hb sb ∧ EvP subj hc sc ∧ EvP sb sc x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f =>
      simp only [evalPaper] at h
      cases tail with
      | atom => simp at h
      | cell hb hc =>
        simp only at h
        split at h
        · rename_i sb sc hsb hsc
          exact ⟨hb, hc, sb, sc, rfl, ⟨f, hsb⟩, ⟨f, hsc⟩, ⟨f, h⟩⟩
        · simp at h
  · rintro ⟨hb, hc, sb, sc, rfl, hsb, hsc, hx⟩
    obtain ⟨f, hsb, hsc, hx⟩ := ev3P hsb hsc hx
    exact ⟨f + 1, by simp only [evalPaper, hsb, hsc]; exact hx⟩

theorem EvP_op3 {subj tail x} : EvP subj (.cell (.atom 3) tail) x ↔
    ∃ y, EvP subj tail y ∧ x = Noun.wut y := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f =>
      simp only [evalPaper, Option.map_eq_some_iff] at h
      obtain ⟨y, hy, hx⟩ := h
      exact ⟨y, ⟨f, hy⟩, hx.symm⟩
  · rintro ⟨y, ⟨fy, hy⟩, rfl⟩
    exact ⟨fy + 1, by simp only [evalPaper, hy, Option.map_some]⟩

theorem EvP_op4 {subj tail x} : EvP subj (.cell (.atom 4) tail) x ↔
    ∃ y, EvP subj tail y ∧ Noun.lus y = some x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f =>
      simp only [evalPaper, Option.bind_eq_some_iff] at h
      obtain ⟨y, hy, hx⟩ := h
      exact ⟨y, ⟨f, hy⟩, hx⟩
  · rintro ⟨y, ⟨fy, hy⟩, hx⟩
    exact ⟨fy + 1, by simp only [evalPaper, hy]; exact hx⟩

theorem EvP_op5 {subj tail x} : EvP subj (.cell (.atom 5) tail) x ↔
    ∃ hb hc sb sc, tail = .cell hb hc ∧ EvP subj hb sb ∧ EvP subj hc sc ∧ x = Noun.tis sb sc := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f =>
      simp only [evalPaper] at h
      cases tail with
      | atom => simp at h
      | cell hb hc =>
        simp only at h
        split at h
        · rename_i sb sc hsb hsc
          exact ⟨hb, hc, sb, sc, rfl, ⟨f, hsb⟩, ⟨f, hsc⟩, (Option.some.inj h).symm⟩
        · simp at h
  · rintro ⟨hb, hc, sb, sc, rfl, hsb, hsc, rfl⟩
    obtain ⟨f, hsb, hsc⟩ := ev2P hsb hsc
    exact ⟨f + 1, by simp only [evalPaper, hsb, hsc]⟩

theorem EvP_op6 {subj tail x} : EvP subj (.cell (.atom 6) tail) x ↔
    ∃ b c d cv, tail = .cell b (.cell c d) ∧ EvP subj b cv ∧
      ((cv = .atom 0 ∧ EvP subj c x) ∨ (cv = .atom 1 ∧ EvP subj d x)) := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f =>
      simp only [evalPaper] at h
      cases tail with
      | atom => simp at h
      | cell b rest =>
        cases rest with
        | atom => simp at h
        | cell c d =>
          simp only at h
          cases hb : evalPaper f subj b with
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
    · obtain ⟨f, hcv, hc⟩ := ev2P hcv hc
      refine ⟨f + 1, ?_⟩; rw [evalPaper, hcv]; exact hc
    · obtain ⟨f, hcv, hd⟩ := ev2P hcv hd
      refine ⟨f + 1, ?_⟩; rw [evalPaper, hcv]; exact hd

theorem EvP_op7 {subj tail x} : EvP subj (.cell (.atom 7) tail) x ↔
    ∃ hb hc sb, tail = .cell hb hc ∧ EvP subj hb sb ∧ EvP sb hc x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f =>
      simp only [evalPaper] at h
      cases tail with
      | atom => simp at h
      | cell hb hc =>
        simp only at h
        cases hsb : evalPaper f subj hb with
        | none => rw [hsb] at h; simp at h
        | some sb => rw [hsb] at h; exact ⟨hb, hc, sb, rfl, ⟨f, hsb⟩, ⟨f, h⟩⟩
  · rintro ⟨hb, hc, sb, rfl, hsb, hx⟩
    obtain ⟨f, hsb, hx⟩ := ev2P hsb hx
    exact ⟨f + 1, by simp only [evalPaper, hsb]; exact hx⟩

theorem EvP_op8 {subj tail x} : EvP subj (.cell (.atom 8) tail) x ↔
    ∃ hb hc sb, tail = .cell hb hc ∧ EvP subj hb sb ∧ EvP (.cell sb subj) hc x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f =>
      simp only [evalPaper] at h
      cases tail with
      | atom => simp at h
      | cell hb hc =>
        simp only at h
        cases hsb : evalPaper f subj hb with
        | none => rw [hsb] at h; simp at h
        | some sb => rw [hsb] at h; exact ⟨hb, hc, sb, rfl, ⟨f, hsb⟩, ⟨f, h⟩⟩
  · rintro ⟨hb, hc, sb, rfl, hsb, hx⟩
    obtain ⟨f, hsb, hx⟩ := ev2P hsb hx
    exact ⟨f + 1, by simp only [evalPaper, hsb]; exact hx⟩

theorem EvP_op9 {subj tail x} : EvP subj (.cell (.atom 9) tail) x ↔
    ∃ ax c core arm, tail = .cell (.atom ax) c ∧ EvP subj c core ∧
      Noun.slot ax core = some arm ∧ EvP core arm x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f =>
      simp only [evalPaper] at h
      cases tail with
      | atom => simp at h
      | cell head c =>
        cases head with
        | cell => simp at h
        | atom ax =>
          simp only at h
          cases hcore : evalPaper f subj c with
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
    obtain ⟨f, hcore, hx⟩ := ev2P hcore hx
    refine ⟨f + 1, ?_⟩
    rw [evalPaper]; simp only [hcore, hslot]; exact hx

theorem EvP_op10 {subj tail x} : EvP subj (.cell (.atom 10) tail) x ↔
    ∃ ax c d new old, tail = .cell (.cell (.atom ax) c) d ∧
      EvP subj c new ∧ EvP subj d old ∧ Noun.edit ax new old = some x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f =>
      simp only [evalPaper] at h
      split at h
      · rename_i ax c d
        split at h
        · rename_i new old hnew hold
          exact ⟨ax, c, d, new, old, rfl, ⟨f, hnew⟩, ⟨f, hold⟩, h⟩
        · simp at h
      · simp at h
  · rintro ⟨ax, c, d, new, old, rfl, hnew, hold, he⟩
    obtain ⟨f, hnew, hold⟩ := ev2P hnew hold
    refine ⟨f + 1, ?_⟩
    rw [evalPaper, hnew, hold]
    exact he

/-! ### `DenP` node characterizations (paper-denotation analogues of the `Den_*` family) -/

theorem DenP_leaf {k x} : DenP (.leaf k) x ↔ x = .atom k := by
  constructor
  · rintro ⟨fuel, h⟩; simp only [denP] at h; exact (Option.some.inj h).symm
  · rintro rfl; exact ⟨0, by simp [denP]⟩

theorem DenP_null {l r x} : DenP (.node .null l r) x ↔ ∃ a b, x = .cell a b ∧ DenP l a ∧ DenP r b :=
  by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [denP] at h
    | succ f =>
      simp only [denP] at h
      cases hl : denP f l with
      | none => rw [hl] at h; simp at h
      | some a =>
        cases hr : denP f r with
        | none => rw [hl, hr] at h; simp at h
        | some b =>
          rw [hl, hr] at h; simp only [Option.some.injEq] at h
          exact ⟨a, b, h.symm, ⟨f, hl⟩, ⟨f, hr⟩⟩
  · rintro ⟨a, b, rfl, hl, hr⟩
    obtain ⟨f, hl, hr⟩ := denP_pair hl hr
    exact ⟨f + 1, by simp only [denP, hl, hr]⟩

theorem DenP_star {l r x} : DenP (.node .star l r) x ↔ ∃ a b, DenP l a ∧ DenP r b ∧ EvP a b x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [denP] at h
    | succ f =>
      simp only [denP] at h
      cases hl : denP f l with
      | none => rw [hl] at h; simp at h
      | some a =>
        cases hr : denP f r with
        | none => rw [hl, hr] at h; simp at h
        | some b =>
          rw [hl, hr] at h
          exact ⟨a, b, ⟨f, hl⟩, ⟨f, hr⟩, ⟨f, h⟩⟩
  · rintro ⟨a, b, hl, hr, hev⟩
    obtain ⟨f, hl, hr⟩ := denP_pair hl hr
    obtain ⟨fe, hev⟩ := hev
    refine ⟨max f fe + 1, ?_⟩
    simp only [denP, denP_mono (show f ≤ max f fe by omega) hl, denP_mono (show f ≤ max f fe by
      omega) hr]
    exact evalPaper_mono (by omega) hev

theorem DenP_slot {l r x} : DenP (.node .slot l r) x ↔
    ∃ ax b, DenP l (.atom ax) ∧ DenP r b ∧ Noun.slot ax b = some x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [denP] at h
    | succ f =>
      simp only [denP] at h
      split at h
      · rename_i ax b hl hr
        exact ⟨ax, b, ⟨f, hl⟩, ⟨f, hr⟩, h⟩
      · simp at h
  · rintro ⟨ax, b, hl, hr, hs⟩
    obtain ⟨f, hl, hr⟩ := denP_pair hl hr
    exact ⟨f + 1, by simp only [denP, hl, hr]; exact hs⟩

theorem DenP_equal {l r x} : DenP (.node .equal l r) x ↔
    ∃ a b, DenP l a ∧ DenP r b ∧ x = Noun.tis a b := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [denP] at h
    | succ f =>
      simp only [denP] at h
      split at h
      · rename_i a b hl hr
        exact ⟨a, b, ⟨f, hl⟩, ⟨f, hr⟩, (Option.some.inj h).symm⟩
      · simp at h
  · rintro ⟨a, b, hl, hr, rfl⟩
    obtain ⟨f, hl, hr⟩ := denP_pair hl hr
    exact ⟨f + 1, by simp only [denP, hl, hr]⟩

theorem DenP_minus {l r x} : DenP (.node .minus l r) x ↔
    ∃ b, DenP r b ∧ ((DenP l (.atom 3) ∧ x = Noun.wut b) ∨ (DenP l (.atom 4) ∧ Noun.lus b = some x))
      := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [denP] at h
    | succ f =>
      simp only [denP] at h
      split at h
      · rename_i b hl hr
        exact ⟨b, ⟨f, hr⟩, Or.inl ⟨⟨f, hl⟩, (Option.some.inj h).symm⟩⟩
      · rename_i b hl hr
        exact ⟨b, ⟨f, hr⟩, Or.inr ⟨⟨f, hl⟩, h⟩⟩
      · simp at h
  · rintro ⟨b, hr, hor⟩
    rcases hor with ⟨hl, rfl⟩ | ⟨hl, hlus⟩
    · obtain ⟨f, hl, hr⟩ := denP_pair hl hr
      exact ⟨f + 1, by simp only [denP, hl, hr]⟩
    · obtain ⟨f, hl, hr⟩ := denP_pair hl hr
      exact ⟨f + 1, by simp only [denP, hl, hr]; exact hlus⟩

theorem DenP_edit_node {l b nw od x} : DenP (.node .edit l (.node b nw od)) x ↔
    ∃ ax n o, DenP l (.atom ax) ∧ DenP nw n ∧ DenP od o ∧ Noun.edit ax n o = some x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [denP] at h
    | succ f =>
      simp only [denP] at h
      split at h
      · rename_i ax n o hl hnw hod
        exact ⟨ax, n, o, ⟨f, hl⟩, ⟨f, hnw⟩, ⟨f, hod⟩, h⟩
      · simp at h
  · rintro ⟨ax, n, o, hl, hnw, hod, he⟩
    obtain ⟨f, hl, hnw, hod⟩ := denP_triple hl hnw hod
    exact ⟨f + 1, by simp only [denP, hl, hnw, hod]; exact he⟩

theorem DenP_edit_leaf {l k x} : ¬ DenP (.node .edit l (.leaf k)) x := by
  rintro ⟨fuel, h⟩
  cases fuel with
  | zero => simp [denP] at h
  | succ f => simp [denP] at h

theorem DenP_wut {l r x} : ¬ DenP (.node .wut l r) x := by
  rintro ⟨fuel, h⟩
  cases fuel with
  | zero => simp [denP] at h
  | succ f => simp [denP] at h

theorem DenP_terminal_iff {v x} (ht : isTerminal v = true) : DenP v x ↔ x = v.noun := by
  constructor
  · intro hd; exact denP_det hd ⟨v.noun.size, denP_terminal v v.noun.size ht (Nat.le_refl _)⟩
  · rintro rfl; exact ⟨v.noun.size, denP_terminal v v.noun.size ht (Nat.le_refl _)⟩

/-! ### The OP₁₁ hint macro (reduction-time desugaring into OP₇/OP₈) -/

/-- Is `v` an OP₁₁ hint redex? A `*`-node whose formula head is the atom `11`, with subject
    and formula-tail in terminal state, and whose tail `n2` is a *cell* (`[t d]` — a hint with a
    body `d`).  This is the OP₁₁ analogue of `inOpcodeDomain` (which rejects `11` via `opHeadOk`,
    `op < 11`), and is aligned exactly with `hintExpand`'s success set: `isHintRedex v = true`
    iff `hintExpand v` is `some`. -/
def isHintRedex : Verb → Bool
  | .node .star n1 (.node ra (.leaf 11) (.node rn h b)) =>
      isTerminal n1 && ra.isNull && isTerminal (.node rn h b)
  | _ => false

/-- **Reduction-time hint expansion.**  Rewrite an OP₁₁ redex into its paper-opcode macro:
    a dynamic hint `*[n1 11 [t c] d]` becomes `*[n1 8 c [7 [0 3] d]]` (evaluate the clue `c`
    against `n1`, pair with `n1`, project `n1` back out via `/[3]`, then run the body `d`); a
    static hint `*[n1 11 t d]` (atom tag `t`) becomes `*[n1 d]`.  Non-OP₁₁ verbs map to `none`. -/
def hintExpand : Verb → Option Verb
  | .node .star n1 (.node ra (.leaf 11) n2) =>
      if isTerminal n1 && ra.isNull && isTerminal n2 then
        match n2 with
        | .node _ (.node _ _ clue) body =>            -- dynamic: [11 [t c] d]
            some (.node .star n1
              (.node .null (.leaf 8)
                (.node .null clue
                  (.node .null (.leaf 7)
                    (.node .null (.node .null (.leaf 0) (.leaf 3)) body)))))
        | .node _ (.leaf _) body =>                   -- static: [11 t d]
            some (.node .star n1 body)
        | _ => none
      else none
  | _ => none

/-- The extended local rewrite: expand an OP₁₁ hint redex (`hintExpand`), otherwise the
    standard paper local rewrite `reduce` (opcode `redex` on a `*`-node, or an
    operator-application step).  Additive: `redex`/`reduce` themselves are untouched. -/
def redexHint (v : Verb) : Option Verb :=
  match hintExpand v with
  | some v' => some v'
  | none    => reduce v

/-- The extended transition domain: `inDomain` plus OP₁₁ hint redexes. -/
def inDomainHint (v : Verb) : Bool := inDomain v || isHintRedex v

-- main.tex:1052 + Urbit OP₁₁  (one step of the OP₁₁-extended machine)
/-- One step of the OP₁₁-extended Nock machine: exactly `next`, but with the extended domain
    `inDomainHint` and the extended local rewrite `redexHint` (so a selected OP₁₁ hint redex
    expands to its OP₇/OP₈ macro instead of crashing). -/
def nextHint (v : Verb) : Option Verb :=
  match getIndex v with
  | none   => none
  | some i =>
      match map i v with
      | none     => none
      | some sub =>
          if inDomainHint sub then
            match redexHint sub with
            | some r => some (replaceAt i v r)
            | none   => none
          else none

/-- Fuel-indexed iteration of `nextHint` to a terminal/⊥ state (the OP₁₁-extended `run`). -/
def runHint : Nat → Verb → Option Noun
  | 0,        _ => none
  | fuel + 1, v =>
      match nextHint v with
      | some v' => runHint fuel v'
      | none    => result v

/-- Run a Nock program `*[subject, formula]` through the OP₁₁-extended machine. -/
def runHintProgram (fuel : Nat) (subject formula : Noun) : Option Noun :=
  runHint fuel (program subject formula)

/-! ### OP₁₁ soundness -/

/-- **A hint redex is not a paper redex: `reduce` crashes on it.**  An OP₁₁ head fails
    `opHeadOk` (`op < 11`), so the paper local rewrite `redex`/`reduce` returns `⊥`.  This is
    what forces the extended domain to be `inDomain ∨ isHintRedex`, disjointly. -/
theorem reduce_none_of_isHintRedex {sub} (h : isHintRedex sub = true) : reduce sub = none := by
  unfold isHintRedex at h
  split at h
  · rename_i n1 ra rn hh b
    simp [reduce, redex]
  · simp at h

/-- Big-step denotation of a `*`-node with *both* children terminal is `evalN` of the two
    underlying nouns. -/
theorem Den_star_terminal {n1 t x} (h1 : isTerminal n1 = true) (ht : isTerminal t = true) :
    Den (.node .star n1 t) x ↔ Ev n1.noun t.noun x := by
  rw [Den_star]
  constructor
  · rintro ⟨a, b, ha, hb, hev⟩
    rw [(Den_terminal_iff h1).1 ha] at hev
    rw [(Den_terminal_iff ht).1 hb] at hev
    exact hev
  · intro hev
    exact ⟨n1.noun, t.noun, (Den_terminal_iff h1).2 rfl, (Den_terminal_iff ht).2 rfl, hev⟩

/-- **`evalN` OP₁₁ dynamic clause**, as a big-step equivalence: `*[a 11 [t c] d]` succeeds iff
    the clue `c` converges and the body `d` yields the result (the clue value is discarded). -/
theorem EvN_op11_dyn {subj tb clue body x} :
    Ev subj (.cell (.atom 11) (.cell (.cell tb clue) body)) x ↔
      (∃ cv, Ev subj clue cv) ∧ Ev subj body x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN] at h
      cases hcv : evalN f subj clue with
      | none => rw [hcv] at h; simp at h
      | some cv => rw [hcv] at h; exact ⟨⟨cv, f, hcv⟩, f, h⟩
  · rintro ⟨⟨cv, hcv⟩, hbody⟩
    obtain ⟨f, hcv, hbody⟩ := ev2 hcv hbody
    exact ⟨f + 1, by simp only [evalN, hcv]; exact hbody⟩

/-- **`evalN` OP₁₁ static clause**, as a big-step equivalence: `*[a 11 t d] = *[a d]`. -/
theorem EvN_op11_static {subj t body x} :
    Ev subj (.cell (.atom 11) (.cell (.atom t) body)) x ↔ Ev subj body x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f => simp only [evalN] at h; exact ⟨f, h⟩
  · rintro ⟨fuel, h⟩; exact ⟨fuel + 1, by simp only [evalN]; exact h⟩

/-- **The dynamic-hint macro `*[a 8 c [7 [0 3] d]]` has the same big-step value as OP₁₁**:
    evaluate the clue `c`, keep the original subject `a` via `/[3]`, then run the body `d`. -/
theorem EvN_macro_dyn {subj clue body x} :
    Ev subj (.cell (.atom 8)
        (.cell clue (.cell (.atom 7) (.cell (.cell (.atom 0) (.atom 3)) body)))) x ↔
      (∃ cv, Ev subj clue cv) ∧ Ev subj body x := by
  rw [EvN_op8]
  constructor
  · rintro ⟨hb, hc, sb, heq, hclue, hrest⟩
    obtain ⟨rfl, rfl⟩ := Noun.cell.inj heq
    rw [EvN_op7] at hrest
    obtain ⟨hb2, hc2, sb2, heq2, hslot, hbody⟩ := hrest
    obtain ⟨rfl, rfl⟩ := Noun.cell.inj heq2
    rw [EvN_op0] at hslot
    obtain ⟨ax, hax, hs⟩ := hslot
    obtain rfl := Noun.atom.inj hax
    rw [slot_three] at hs
    obtain rfl := Option.some.inj hs
    exact ⟨⟨sb, hclue⟩, hbody⟩
  · rintro ⟨⟨cv, hclue⟩, hbody⟩
    refine ⟨clue, _, cv, rfl, hclue, ?_⟩
    rw [EvN_op7]
    refine ⟨.cell (.atom 0) (.atom 3), body, subj, rfl, ?_, hbody⟩
    rw [EvN_op0]
    exact ⟨3, rfl, slot_three⟩

/-- Hint expansion preserves `den`: `Den sub x ↔ Den e x` (OP₁₁ analogue of `den_local`). -/
theorem denHint_expand {sub e x} (he : hintExpand sub = some e) : Den sub x ↔ Den e x := by
  unfold hintExpand at he
  split at he
  · rename_i n1 ra n2
    split at he
    · rename_i hguard
      simp only [Bool.and_eq_true] at hguard
      obtain ⟨⟨h1, hra⟩, hn2⟩ := hguard
      have hraN : ra = Action.null := by cases ra <;> simp_all only [Action.isNull, reduceCtorEq]
      subst hraN
      have hform : isTerminal (Verb.node .null (.leaf 11) n2) = true := by
        simp [isTerminal, Action.isNull, hn2]
      split at he
      · -- dynamic hint  n2 = [[tb clue] body]
        rename_i rn2 innerA tb clue body
        obtain rfl := Option.some.inj he
        simp only [isTerminal, Bool.and_eq_true] at hn2
        obtain ⟨⟨_, ⟨_, hclue⟩⟩, hbody⟩ := hn2
        have hE : isTerminal (Verb.node .null (.leaf 8)
            (.node .null clue (.node .null (.leaf 7)
              (.node .null (.node .null (.leaf 0) (.leaf 3)) body)))) = true := by
          simp [isTerminal, Action.isNull, hclue, hbody]
        rw [Den_star_terminal h1 hform, Den_star_terminal h1 hE]
        simp only [noun]
        rw [EvN_op11_dyn, EvN_macro_dyn]
      · -- static hint  n2 = [t body]  (t an atom)
        rename_i rn2 t body
        obtain rfl := Option.some.inj he
        simp only [isTerminal, Bool.and_eq_true] at hn2
        obtain ⟨_, hbody⟩ := hn2
        rw [Den_star_terminal h1 hform, Den_star_terminal h1 hbody]
        simp only [noun]
        rw [EvN_op11_static]
      · simp at he
    · simp at he
  · simp at he

/-- A terminal verb (all actions `⊥`) is trivially edit-well-formed. -/
theorem editOk_of_terminal : ∀ {v : Verb}, isTerminal v = true → editOk v = true := by
  intro v
  induction v with
  | leaf => intro _; rfl
  | node a l r ihl ihr =>
      intro h
      simp only [isTerminal, Bool.and_eq_true] at h
      obtain ⟨⟨ha, hl⟩, hr⟩ := h
      have haN : a = Action.null := by cases a <;> simp_all only [Action.isNull, reduceCtorEq]
      subst haN
      simp [editOk_null_eq, ihl hl, ihr hr]

/-- `hintExpand` produces an edit-well-formed verb (its pieces `n1`, clue, body are terminal). -/
theorem editOk_hintExpand {sub e} (he : hintExpand sub = some e) : editOk e = true := by
  unfold hintExpand at he
  split at he
  · rename_i n1 ra n2
    split at he
    · rename_i hguard
      simp only [Bool.and_eq_true] at hguard
      obtain ⟨⟨h1, _⟩, hn2⟩ := hguard
      split at he
      · rename_i rn2 innerA tb clue body
        obtain rfl := Option.some.inj he
        simp only [isTerminal, Bool.and_eq_true] at hn2
        obtain ⟨⟨_, ⟨_, hclue⟩⟩, hbody⟩ := hn2
        simp [editOk, editOk_of_terminal h1,
          editOk_of_terminal hclue, editOk_of_terminal hbody]
      · rename_i rn2 t body
        obtain rfl := Option.some.inj he
        simp only [isTerminal, Bool.and_eq_true] at hn2
        obtain ⟨_, hbody⟩ := hn2
        simp [editOk, editOk_of_terminal h1,
          editOk_of_terminal hbody]
      · simp at he
    · simp at he
  · simp at he

/-- `redexHint` (hint expand, else `reduce`) preserves `den`. -/
theorem denHint_local {sub r₀ x} (hd : inDomainHint sub = true) (hr : redexHint sub = some r₀) :
    (Den sub x ↔ Den r₀ x) := by
  cases he : hintExpand sub with
  | some e =>
      have hre : r₀ = e := by
        unfold redexHint at hr; rw [he] at hr; exact (Option.some.inj hr).symm
      subst hre; exact denHint_expand he
  | none =>
      have hr' : reduce sub = some r₀ := by unfold redexHint at hr; rw [he] at hr; exact hr
      have hin : inDomain sub = true := by
        rw [inDomainHint, Bool.or_eq_true] at hd
        rcases hd with h | h
        · exact h
        · have hnone := reduce_none_of_isHintRedex h
          rw [hnone] at hr'; exact absurd hr' (by simp)
      exact den_local hin hr'

/-- `editOk` is preserved by the extended local rewrite. -/
theorem editOk_redexHint {sub r₀} (hr : redexHint sub = some r₀) (hok : editOk sub = true) :
    editOk r₀ = true := by
  cases he : hintExpand sub with
  | some e =>
      have hre : r₀ = e := by
        unfold redexHint at hr; rw [he] at hr; exact (Option.some.inj hr).symm
      subst hre; exact editOk_hintExpand he
  | none =>
      have hr' : reduce sub = some r₀ := by unfold redexHint at hr; rw [he] at hr; exact hr
      exact editOk_reduce hr' hok

/-- `nextHint` realizes the strict DFS selection step over `inDomainHint`/`redexHint`
    (OP₁₁ analogue of `next_eq_some_iff`). -/
theorem nextHint_eq_some_iff {a b : Verb} : nextHint a = some b ↔
    ∃ i sub r, IsMaxPending dfsLt a i ∧ map i a = some sub ∧ inDomainHint sub = true
      ∧ redexHint sub = some r ∧ b = replaceAt i a r := by
  constructor
  · intro h
    unfold nextHint at h
    split at h
    · simp at h
    · rename_i i hgi
      split at h
      · simp at h
      · rename_i sub hmap
        split at h
        · rename_i hdom
          split at h
          · rename_i r hred
            exact ⟨i, sub, r, getIndex_eq_some_iff.1 hgi, hmap, hdom, hred, (Option.some.inj
              h).symm⟩
          · simp at h
        · simp at h
  · rintro ⟨i, sub, r, hmax, hmap, hdom, hred, hb⟩
    have hgi : getIndex a = some i := getIndex_eq_some_iff.2 hmax
    unfold nextHint
    simp only [hgi, hmap, hdom, hred, ite_true]
    rw [hb]

/-- `editOk` is preserved by `nextHint` (the invariant discharging `denHint_step`). -/
theorem editOk_nextHint {v v'} (h : nextHint v = some v') (hok : editOk v = true) :
    editOk v' = true := by
  obtain ⟨i, sub, r₀, hmax, hmap, hdom, hred, hv'⟩ := nextHint_eq_some_iff.1 h
  have hoksub : editOk sub = true := editOk_enum v 0 hok (i, sub) (mem_nodes_of_map hmap)
  have hokr0 : editOk r₀ = true := editOk_redexHint hred hoksub
  obtain ⟨w, hmapw, hpw⟩ := hmax.1
  have hpsub : Verb.isPending sub = true := (Option.some.inj (hmapw.symm.trans hmap)) ▸ hpw
  rw [hv', replaceAt]
  apply editOk_replaceAux i r₀ hokr0 v 0 hok
  intro s hs
  have hms : map i v = some s := hs
  exact (Option.some.inj (hms.symm.trans hmap)) ▸ hpsub

/-- One `nextHint` step preserves `den`. -/
theorem denHint_step {v v' : Verb} (hwf : editOk v = true) (h : nextHint v = some v') {r : Noun} :
    (∃ fuel, den fuel v = some r) ↔ (∃ fuel, den fuel v' = some r) := by
  obtain ⟨i, sub, r₀, hmax, hmap, hdom, hred, hv'⟩ := nextHint_eq_some_iff.1 h
  obtain ⟨w, hmapw, hpw⟩ := hmax.1
  have hpsub : Verb.isPending sub = true := (Option.some.inj (hmapw.symm.trans hmap)) ▸ hpw
  have hrel : Rel v v' := by
    rw [hv', replaceAt]
    apply replaceAux_rel i r₀ v 0
    intro s hs
    have hms : map i v = some s := hs
    have hss : s = sub := Option.some.inj (hms.symm.trans hmap)
    subst hss
    exact ⟨hpsub, fun x => denHint_local hdom hred⟩
  exact Rel_den v.noun.size v v' (Nat.le_refl _) hrel hwf r

/-- Iterating `nextHint` to a terminal state computes `den`. -/
theorem runHint_sound {v : Verb} {r : Noun} :
    ∀ fuel, editOk v = true → runHint fuel v = some r → (∃ f, den f v = some r) := by
  intro fuel
  induction fuel generalizing v with
  | zero => intro _ h; simp [runHint] at h
  | succ fuel ih =>
      intro hwf h
      rw [runHint] at h
      cases hnext : nextHint v with
      | some v' =>
          rw [hnext] at h
          exact (denHint_step hwf hnext).2 (ih (editOk_nextHint hnext hwf) h)
      | none =>
          rw [hnext] at h
          simp only [result] at h
          split at h
          · rename_i hterm
            have hr : v.noun = r := Option.some.inj h
            subst hr
            exact ⟨v.noun.size, den_terminal v v.noun.size hterm (Nat.le_refl _)⟩
          · simp at h

-- main.tex:1090-1094 + Urbit OP₁₁
/-- Whenever `runHintProgram` returns a value, `evalN` agrees. -/
theorem runHintProgram_sound {s f r : Noun} {fuel : Nat}
    (h : runHintProgram fuel s f = some r) : ∃ fuel', evalN fuel' s f = some r := by
  have : ∃ f', den f' (program s f) = some r := runHint_sound fuel (editOk_program s f) h
  exact (den_iff_evalN s f r).1 this

/-! ### Concrete OP₁₁ boundary witnesses -/

/-- Static hint `*[42 11 33 0 1] = 42` (evaluate-and-discard atom tag `33`, then `/[1] = 42`). -/
def hintProgStatic : Noun := .cell (.atom 11) (.cell (.atom 33) (.cell (.atom 0) (.atom 1)))

/-- Dynamic hint `*[42 11 [1 1 33] 0 1] = 42` (clue `[1 33]` computed then discarded). -/
def hintProgDyn : Noun :=
  .cell (.atom 11)
    (.cell (.cell (.atom 1) (.cell (.atom 1) (.atom 33)))
      (.cell (.atom 0) (.atom 1)))

/-- Dynamic hint over an increment: `*[42 11 [1 1 33] 4 0 1] = 43`. -/
def hintProgInc : Noun :=
  .cell (.atom 11)
    (.cell (.cell (.atom 1) (.cell (.atom 1) (.atom 33)))
      (.cell (.atom 4) (.cell (.atom 0) (.atom 1))))

/-- **A `*`-node with terminal children has only its root pending.**  If `map i` retrieves a
    pending node from `*[L, R]` with `L`, `R` terminal, that node is the root itself. -/
theorem star_pending_is_root {L R : Verb}
    (hL : isTerminal L = true) (hR : isTerminal R = true)
    {i : Nat} {sub : Verb}
    (hmap : map i (.node .star L R) = some sub) (hp : sub.isPending = true) :
    sub = .node .star L R := by
  have hmem : (i, sub) ∈ nodes (.node .star L R) := mem_nodes_of_map hmap
  simp only [nodes, enum, List.mem_cons, List.mem_append] at hmem
  rcases hmem with hz | hl | hr
  · exact (Prod.mk.injEq .. ▸ hz).2
  · exact absurd (enum_nonpending_of_terminal L hL 1 (i, sub) hl) (by rw [hp]; simp)
  · exact absurd (enum_nonpending_of_terminal R hR _ (i, sub) hr) (by rw [hp]; simp)

/-- The paper machine crashes at the root OP₁₁ redex of a hint program: `next` of the
    program verb is `⊥`, because an OP₁₁ head is out of the paper domain (`opHeadOk`,
    `op < 11`) and the root `*`-node carries no operator. -/
theorem next_hintProg_none (subj n2 : Noun) :
    next (program subj (.cell (.atom 11) n2)) = none := by
  cases hb : next (program subj (.cell (.atom 11) n2)) with
  | none => rfl
  | some b =>
      exfalso
      obtain ⟨i, sub, r, hmax, hmap, hdom, _, _⟩ := next_eq_some_iff.1 hb
      obtain ⟨w, hmapw, hpw⟩ := hmax.1
      have hsw : sub = w := Option.some.inj (hmap.symm.trans hmapw)
      have hpsub : sub.isPending = true := hsw ▸ hpw
      have hL : isTerminal (ofNoun subj) = true := ofNoun_terminal subj
      have hR : isTerminal (ofNoun (.cell (.atom 11) n2)) = true := ofNoun_terminal _
      have hroot : sub = .node .star (ofNoun subj) (ofNoun (.cell (.atom 11) n2)) :=
        star_pending_is_root hL hR (by simpa [program] using hmap) hpsub
      rw [hroot] at hdom
      simp [inDomain, inOpcodeDomain, opReady, ofNoun, opHeadOk, Action.isOperator,
        Action.isNull, isTerminal] at hdom

/-- **Paper machine crashes on hints (all fuel).**  For every fuel budget, `runProgram` of a
    hint program `*[subj 11 …]` is `⊥`: the very first step crashes (OP₁₁ ∉ paper domain),
    and the crashed root `*`-verb is not terminal, so `result` is `⊥`. -/
theorem runProgram_hint_crash (subj n2 : Noun) :
    ∀ fuel, runProgram fuel subj (.cell (.atom 11) n2) = none := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ f =>
      unfold runProgram
      rw [run, next_hintProg_none subj n2]
      simp [result, program, isTerminal, ofNoun, Action.isNull]

theorem runHint_hintStatic : runHintProgram 32 (Noun.atom 42) hintProgStatic = some (Noun.atom 42)
  := by
  decide +kernel

theorem runHint_hintDyn : runHintProgram 64 (Noun.atom 42) hintProgDyn = some (Noun.atom 42) := by
  decide +kernel

theorem runHint_hintInc : runHintProgram 64 (Noun.atom 42) hintProgInc = some (Noun.atom 43) := by
  decide +kernel

/-- On `*[42 11 33 0 1]`, `runProgram` crashes at every fuel while `runHint` yields `42`. -/
theorem paper_hint_separation :
    (∀ fuel, runProgram fuel (Noun.atom 42) hintProgStatic = none)
    ∧ (∃ fuel, runHintProgram fuel (Noun.atom 42) hintProgStatic = some (Noun.atom 42)) :=
  ⟨runProgram_hint_crash _ _, 32, runHint_hintStatic⟩

/-- **Positive verifiable crash.**  A `*[subj 11 …]` program — a non-opcode head atom `11`
    (`11 ∉ [11] = {0,…,10}`, `main.tex:1052,1083`), outside the paper's opcode domain — reports
    `Outcome.crash` under `eval`, not merely `none` under `run`: the first step is stuck
    (`next_hintProg_none`) and the crashed `*`-root is non-terminal, so `haltOutcome` is
    `crash`.  By
    `eval_crash_invalid` the evaluated program is `Invalid` (the paper's ⊥, `main.tex:1124`),
    not fuel
    exhaustion. -/
theorem evalProgram_hint_crash (subj n2 : Noun) :
    evalProgram 1 subj (.cell (.atom 11) n2) = .crash := by
  unfold evalProgram
  rw [eval_succ, next_hintProg_none subj n2]
  exact haltOutcome_crash rfl

/-- Sharpened separation: `eval` reports a positive `crash` on the non-opcode-head program while
    `runHint` yields `42` — "provably crashes", not just "produces no value". -/
theorem paper_hint_separation_crash :
    evalProgram 1 (Noun.atom 42) hintProgStatic = .crash
    ∧ (∃ fuel, runHintProgram fuel (Noun.atom 42) hintProgStatic = some (Noun.atom 42)) :=
  ⟨evalProgram_hint_crash _ _, 32, runHint_hintStatic⟩

/-! ### Soundness and completeness interfaces -/

/-- Every successful `evalN` evaluation is realized by `runHintProgram`. -/
def HintComplete : Prop :=
  ∀ s f r : Noun, (∃ fuel, evalN fuel s f = some r) → (∃ fuel, runHintProgram fuel s f = some r)

/-- Every successful `evalPaper` evaluation is realized by `runProgram`. -/
def PaperComplete : Prop :=
  ∀ s f r : Noun, (∃ fuel, evalPaper fuel s f = some r) → (∃ fuel, runProgram fuel s f = some r)

/-- Every successful `runProgram` evaluation is realized by `evalPaper`. -/
def PaperSound : Prop :=
  ∀ s f r : Noun, (∃ fuel, runProgram fuel s f = some r) → (∃ fuel, evalPaper fuel s f = some r)

/-! ### OP₀–OP₁₀ soundness replay -/

/-- Paper-denotation analogue of `Den_ofNoun_iff` (helper). -/
theorem DenP_ofNoun_iff {n x} : DenP (ofNoun n) x ↔ x = n := by
  rw [DenP_terminal_iff (ofNoun_terminal n), ofNoun_noun]

theorem den_localP_opReady {sub r₀ x} (hor : opReady sub = true) (hr : reduce sub = some r₀) :
    (DenP sub x ↔ DenP r₀ x) := by
  cases sub with
  | leaf => simp [opReady] at hor
  | node a l r =>
    simp only [opReady, Bool.and_eq_true] at hor
    obtain ⟨⟨hao, htl⟩, htr⟩ := hor
    have hDl : ∀ v, DenP l v ↔ v = l.noun := fun v => DenP_terminal_iff htl
    have hDr : ∀ v, DenP r v ↔ v = r.noun := fun v => DenP_terminal_iff htr
    have atominj : ∀ {ax' ax : Nat}, DenP l (.atom ax') → l.noun = .atom ax → ax' = ax := by
      intro ax' ax hd he; have := (hDl _).1 hd; rw [he] at this; exact Noun.atom.inj this
    cases a with
    | null => simp [Action.isOperator] at hao
    | star => simp [Action.isOperator] at hao
    | wut => simp [reduce] at hr
    | equal =>
        rw [reduce] at hr; obtain rfl := Option.some.inj hr
        rw [DenP_equal, DenP_ofNoun_iff]
        constructor
        · rintro ⟨va, vb, hva, hvb, rfl⟩; rw [(hDl va).1 hva, (hDr vb).1 hvb]
        · rintro rfl; exact ⟨l.noun, r.noun, (hDl _).2 rfl, (hDr _).2 rfl, rfl⟩
    | slot =>
        rw [reduce] at hr
        rw [DenP_slot]
        split at hr
        · rename_i ax heq
          rw [Option.map_eq_some_iff] at hr
          obtain ⟨sr, hslot, rfl⟩ := hr
          rw [DenP_ofNoun_iff]
          constructor
          · rintro ⟨ax', b, hax', hb, hs⟩
            obtain rfl := atominj hax' heq
            rw [(hDr _).1 hb] at hs; rw [hs] at hslot; exact (Option.some.inj hslot)
          · rintro rfl
            exact ⟨ax, r.noun, (hDl _).2 heq.symm, (hDr _).2 rfl, hslot⟩
        · simp at hr
    | minus =>
        rw [reduce] at hr
        rw [DenP_minus]
        split at hr
        · rename_i heq
          obtain rfl := Option.some.inj hr
          rw [DenP_ofNoun_iff]
          constructor
          · rintro ⟨b, hb, hor2⟩
            rcases hor2 with ⟨_, hx⟩ | ⟨h4, _⟩
            · rw [(hDr _).1 hb] at hx; exact hx
            · exact absurd (atominj h4 heq) (by decide)
          · rintro rfl; exact ⟨r.noun, (hDr _).2 rfl, Or.inl ⟨(hDl _).2 heq.symm, rfl⟩⟩
        · rename_i heq
          rw [Option.map_eq_some_iff] at hr
          obtain ⟨sr, hlus, rfl⟩ := hr
          rw [DenP_ofNoun_iff]
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
                have hDnw : ∀ v, DenP nw v ↔ v = nw.noun := fun v => DenP_terminal_iff htnw
                have hDod : ∀ v, DenP od v ↔ v = od.noun := fun v => DenP_terminal_iff htod
                rw [DenP_edit_node, DenP_ofNoun_iff]
                constructor
                · rintro ⟨ax', n, o, hax', hn, ho, he⟩
                  obtain rfl := atominj hax' hln
                  rw [(hDnw _).1 hn, (hDod _).1 ho] at he
                  rw [he] at hedit; exact (Option.some.inj hedit)
                · rintro rfl
                  exact ⟨ax, nw.noun, od.noun, (hDl _).2 hln.symm, (hDnw _).2 rfl, (hDod _).2 rfl,
                    hedit⟩

private theorem paper_denotation_conditional_reduction {r₀ : Verb} {x : Noun} (n1 n2 : Verb) (htn2 :
  n2.isTerminal = true)
  (hn1 : ∀ (v : Noun), n1.DenP v ↔ v = n1.noun)
  (star_term : ∀ (W : Verb) (p : Noun), W.isTerminal = true → ((node Action.star n1 W).DenP p ↔ EvP
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
  EvP n1.noun ((atom 6).cell n2.noun) x ↔ r₀.DenP x := by
  cases n2 with
  | leaf => simp at hr
  | node bn b c =>
      obtain rfl := Option.some.inj hr
      simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
      obtain ⟨⟨_, htb⟩, htc⟩ := htn2
      have dStar : ∀ (W : Verb) y,
          (DenP (Verb.node .star n1 W) y ↔ ∃ q, DenP W q ∧ EvP n1.noun q y) := by
        intro W y; rw [DenP_star]
        exact ⟨fun ⟨p,q,hp,hq,hev⟩ => ⟨q, hq, (hn1 p).1 hp ▸ hev⟩,
               fun ⟨q,hq,hev⟩ => ⟨n1.noun, q, (hn1 _).2 rfl, hq, hev⟩⟩
      have dStarC : ∀ (W : Verb) y,
          (DenP (Verb.node .star c W) y ↔ ∃ q, DenP W q ∧ EvP c.noun q y) := by
        intro W y; rw [DenP_star]
        exact ⟨fun ⟨p,q,hp,hq,hev⟩ => ⟨q, hq, (DenP_terminal_iff htc).1 hp ▸ hev⟩,
               fun ⟨q,hq,hev⟩ => ⟨c.noun, q, (DenP_terminal_iff htc).2 rfl, hq, hev⟩⟩
      have hIarg : isTerminal (Verb.node .null (.leaf 4) (.node .null (.leaf 4) b)) = true := by
        simp [isTerminal, Action.isNull, htb]
      rw [EvP_op6]
      constructor
      · rintro ⟨B, C, D, cv, heq, hcv, hor⟩
        obtain ⟨hBeq, hCDeq⟩ := Noun.cell.inj heq
        subst hBeq
        rcases hor with ⟨rfl, hCx⟩ | ⟨rfl, hDx⟩
        · refine (dStar _ _).2 ⟨C, ?_, hCx⟩
          refine (dStarC _ _).2 ⟨Noun.cell (.atom 0) (.atom 2), ?_,
                  (EvP_op0).2 ⟨2, rfl, hCDeq ▸ slot_two⟩⟩
          refine (DenP_null).2 ⟨.atom 0, .atom 2, rfl, DenP_leaf.2 rfl, ?_⟩
          refine (DenP_star).2 ⟨Noun.cell (.atom 2) (.atom 3), Noun.cell (.atom 0) (.atom 2),
                  (DenP_null).2 ⟨.atom 2, .atom 3, rfl, DenP_leaf.2 rfl, DenP_leaf.2 rfl⟩, ?_,
                  (EvP_op0).2 ⟨2, rfl, slot_two⟩⟩
          refine (DenP_null).2 ⟨.atom 0, .atom 2, rfl, DenP_leaf.2 rfl, ?_⟩
          refine (dStar _ _).2 ⟨_, (DenP_terminal_iff hIarg).2 rfl, ?_⟩
          exact (EvP_op4).2 ⟨.atom 1, (EvP_op4).2 ⟨.atom 0, hcv, lus_atom⟩, lus_atom⟩
        · refine (dStar _ _).2 ⟨D, ?_, hDx⟩
          refine (dStarC _ _).2 ⟨Noun.cell (.atom 0) (.atom 3), ?_,
                  (EvP_op0).2 ⟨3, rfl, hCDeq ▸ slot_three⟩⟩
          refine (DenP_null).2 ⟨.atom 0, .atom 3, rfl, DenP_leaf.2 rfl, ?_⟩
          refine (DenP_star).2 ⟨Noun.cell (.atom 2) (.atom 3), Noun.cell (.atom 0) (.atom 3),
                  (DenP_null).2 ⟨.atom 2, .atom 3, rfl, DenP_leaf.2 rfl, DenP_leaf.2 rfl⟩, ?_,
                  (EvP_op0).2 ⟨3, rfl, slot_three⟩⟩
          refine (DenP_null).2 ⟨.atom 0, .atom 3, rfl, DenP_leaf.2 rfl, ?_⟩
          refine (dStar _ _).2 ⟨_, (DenP_terminal_iff hIarg).2 rfl, ?_⟩
          exact (EvP_op4).2 ⟨.atom 2, (EvP_op4).2 ⟨.atom 1, hcv, lus_atom⟩, lus_atom⟩
      · intro hmacro
        obtain ⟨qa0, ha0, hC4⟩ := (dStar _ _).1 hmacro
        obtain ⟨qb0, hb0, hC3⟩ := (dStarC _ _).1 ha0
        rw [DenP_null] at hb0; obtain ⟨v0, vc0, rfl, hv0, hc0⟩ := hb0
        rw [DenP_leaf] at hv0; subst hv0
        rw [DenP_star] at hc0; obtain ⟨p23, qd0, hp23, hd0, hC2⟩ := hc0
        rw [DenP_null] at hp23; obtain ⟨w2, w3, rfl, hw2, hw3⟩ := hp23
        rw [DenP_leaf] at hw2 hw3; subst hw2; subst hw3
        rw [DenP_null] at hd0; obtain ⟨u0, vinner, rfl, hu0, hinner⟩ := hd0
        rw [DenP_leaf] at hu0; subst hu0
        rw [star_term _ _ hIarg] at hinner
        obtain ⟨y, hy1, hly⟩ := (EvP_op4).1 hinner
        obtain ⟨z, hz1, hlz⟩ := (EvP_op4).1 hy1
        cases z with
        | cell => simp [Noun.lus] at hlz
        | atom k =>
            rw [lus_atom] at hlz; obtain rfl := Option.some.inj hlz
            rw [lus_atom] at hly; obtain rfl := Option.some.inj hly
            obtain ⟨ax, hax, hs23⟩ := (EvP_op0).1 hC2
            have haxv : ax = k + 2 := by injection hax with h; omega
            subst haxv
            rcases slot_pair_some _ _ hs23 with h1 | h2 | h3
            · omega
            · have hk : k = 0 := by omega
              subst hk
              rw [slot_two] at hs23; obtain rfl := Option.some.inj hs23
              obtain ⟨ax', hax', hs3⟩ := (EvP_op0).1 hC3
              have : ax' = 2 := by injection hax' with h; omega
              subst this
              cases hcn : c.noun with
              | atom => rw [hcn, slot_two_atom] at hs3; simp at hs3
              | cell C D =>
                  rw [hcn, slot_two] at hs3; obtain rfl := Option.some.inj hs3
                  exact ⟨b.noun, C, D, .atom 0, rfl, hz1, Or.inl ⟨rfl, hC4⟩⟩
            · have hk : k = 1 := by omega
              subst hk
              rw [slot_three] at hs23; obtain rfl := Option.some.inj hs23
              obtain ⟨ax', hax', hs3⟩ := (EvP_op0).1 hC3
              have : ax' = 3 := by injection hax' with h; omega
              subst this
              cases hcn : c.noun with
              | atom => rw [hcn, slot_three_atom] at hs3; simp at hs3
              | cell C D =>
                  rw [hcn, slot_three] at hs3; obtain rfl := Option.some.inj hs3
                  exact ⟨b.noun, C, D, .atom 1, rfl, hz1, Or.inr ⟨rfl, hC4⟩⟩

theorem den_localP_opcode {sub r₀ x} (hd : inOpcodeDomain sub = true) (hr : reduce sub = some r₀) :
    (DenP sub x ↔ DenP r₀ x) := by
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
        have hn1 : ∀ v, DenP n1 v ↔ v = n1.noun := fun v => DenP_terminal_iff htn1
        have hn2 : ∀ v, DenP n2 v ↔ v = n2.noun := fun v => DenP_terminal_iff htn2
        have star_term : ∀ (W : Verb) (p : Noun), isTerminal W = true →
            (DenP (Verb.node .star n1 W) p ↔ EvP n1.noun W.noun p) := by
          intro W p htW
          rw [DenP_star]
          constructor
          · rintro ⟨va, vb, hva, hvb, hev⟩
            rw [(DenP_terminal_iff htn1).1 hva, (DenP_terminal_iff htW).1 hvb] at hev; exact hev
          · intro hev
            exact ⟨n1.noun, W.noun, (DenP_terminal_iff htn1).2 rfl, (DenP_terminal_iff htW).2 rfl,
              hev⟩
        have hsub : (DenP (Verb.node .star n1 (.node ra i n2)) x
                     ↔ EvP n1.noun (Noun.cell i.noun n2.noun) x) := by
          rw [star_term (Verb.node ra i n2) x htt]; simp only [noun]
        rw [hsub]
        rw [reduce] at hr
        cases i with
        | node bi ic id =>
            rw [redex] at hr
            obtain rfl := Option.some.inj hr
            simp only [noun]
            rw [DenP_null, EvP_autocons]
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
            · obtain rfl := Option.some.inj hr
              rw [EvP_op0, DenP_slot]
              constructor
              · rintro ⟨ax, hax, hs⟩; exact ⟨ax, n1.noun, (hn2 _).2 hax.symm, (hn1 _).2 rfl, hs⟩
              · rintro ⟨ax, b, hax, hb, hs⟩
                rw [(hn1 _).1 hb] at hs; exact ⟨ax, ((hn2 _).1 hax).symm, hs⟩
            · obtain rfl := Option.some.inj hr
              rw [EvP_op1]; exact (hn2 x).symm
            · cases n2 with
              | leaf => simp at hr
              | node bn b c =>
                  obtain rfl := Option.some.inj hr
                  simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
                  obtain ⟨⟨_, htb⟩, htc⟩ := htn2
                  rw [EvP_op2, DenP_star]
                  constructor
                  · rintro ⟨hb, hc, sb, sc, heq, hsb, hsc, hev⟩
                    obtain ⟨rfl, rfl⟩ := Noun.cell.inj heq
                    exact ⟨sb, sc, (star_term _ _ htb).2 hsb, (star_term _ _ htc).2 hsc, hev⟩
                  · rintro ⟨sb, sc, hsb, hsc, hev⟩
                    exact ⟨b.noun, c.noun, sb, sc, rfl, (star_term _ _ htb).1 hsb,
                           (star_term _ _ htc).1 hsc, hev⟩
            · obtain rfl := Option.some.inj hr
              rw [EvP_op3, DenP_minus]
              constructor
              · rintro ⟨y, hy, rfl⟩
                exact ⟨y, (star_term _ _ htn2).2 hy, Or.inl ⟨(DenP_leaf).2 rfl, rfl⟩⟩
              · rintro ⟨b, hb, hor⟩
                rcases hor with ⟨_, rfl⟩ | ⟨h4, _⟩
                · exact ⟨b, (star_term _ _ htn2).1 hb, rfl⟩
                · exact absurd ((DenP_leaf).1 h4) (by decide)
            · obtain rfl := Option.some.inj hr
              rw [EvP_op4, DenP_minus]
              constructor
              · rintro ⟨y, hy, hlus⟩
                exact ⟨y, (star_term _ _ htn2).2 hy, Or.inr ⟨(DenP_leaf).2 rfl, hlus⟩⟩
              · rintro ⟨b, hb, hor⟩
                rcases hor with ⟨h3, _⟩ | ⟨_, hlus⟩
                · exact absurd ((DenP_leaf).1 h3) (by decide)
                · exact ⟨b, (star_term _ _ htn2).1 hb, hlus⟩
            · cases n2 with
              | leaf => simp at hr
              | node bn b c =>
                  obtain rfl := Option.some.inj hr
                  simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
                  obtain ⟨⟨_, htb⟩, htc⟩ := htn2
                  rw [EvP_op5, DenP_equal]
                  constructor
                  · rintro ⟨hb, hc, sb, sc, heq, hsb, hsc, rfl⟩
                    obtain ⟨rfl, rfl⟩ := Noun.cell.inj heq
                    exact ⟨sb, sc, (star_term _ _ htb).2 hsb, (star_term _ _ htc).2 hsc, rfl⟩
                  · rintro ⟨sb, sc, hsb, hsc, rfl⟩
                    exact ⟨b.noun, c.noun, sb, sc, rfl, (star_term _ _ htb).1 hsb,
                           (star_term _ _ htc).1 hsc, rfl⟩
            · -- op6
              exact paper_denotation_conditional_reduction n1 n2 htn2 hn1 star_term hr
            · cases n2 with
              | leaf => simp at hr
              | node bn b c =>
                  obtain rfl := Option.some.inj hr
                  simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
                  obtain ⟨⟨_, htb⟩, htc⟩ := htn2
                  rw [EvP_op7, DenP_star]
                  constructor
                  · rintro ⟨hb, hc, sb, heq, hsb, hev⟩
                    obtain ⟨rfl, rfl⟩ := Noun.cell.inj heq
                    exact ⟨sb, c.noun, (star_term _ _ htb).2 hsb, (DenP_terminal_iff htc).2 rfl,
                      hev⟩
                  · rintro ⟨p, q, hp, hq, hev⟩
                    rw [(DenP_terminal_iff htc).1 hq] at hev
                    exact ⟨b.noun, c.noun, p, rfl, (star_term _ _ htb).1 hp, hev⟩
            · cases n2 with
              | leaf => simp at hr
              | node bn b c =>
                  obtain rfl := Option.some.inj hr
                  simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
                  obtain ⟨⟨_, htb⟩, htc⟩ := htn2
                  rw [EvP_op8, DenP_star]
                  constructor
                  · rintro ⟨hb, hc, sb, heq, hsb, hev⟩
                    obtain ⟨rfl, rfl⟩ := Noun.cell.inj heq
                    refine ⟨Noun.cell sb n1.noun, c.noun, ?_, (DenP_terminal_iff htc).2 rfl, hev⟩
                    rw [DenP_null]
                    exact ⟨sb, n1.noun, rfl, (star_term _ _ htb).2 hsb, (hn1 _).2 rfl⟩
                  · rintro ⟨p, q, hp, hq, hev⟩
                    rw [DenP_null] at hp
                    obtain ⟨pb, pn, rfl, hpb, hpn⟩ := hp
                    rw [(hn1 _).1 hpn] at hev
                    rw [(DenP_terminal_iff htc).1 hq] at hev
                    exact ⟨b.noun, c.noun, pb, rfl, (star_term _ _ htb).1 hpb, hev⟩
            · cases n2 with
              | leaf => simp at hr
              | node bn b c =>
                  obtain rfl := Option.some.inj hr
                  simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
                  obtain ⟨⟨_, htb⟩, htc⟩ := htn2
                  have htform : isTerminal (Verb.node .null (.leaf 2)
                      (.node .null (.node .null (.leaf 0) (.leaf 1)) (.node .null (.leaf 0) b))) =
                        true := by
                    simp [isTerminal, Action.isNull, htb]
                  rw [EvP_op9, DenP_star]
                  constructor
                  · rintro ⟨ax, c', core, arm, heq, hcore, hslot, hev⟩
                    obtain ⟨hbn, rfl⟩ := Noun.cell.inj heq
                    refine ⟨core, _, (star_term c core htc).2 hcore,
                            (DenP_terminal_iff htform).2 rfl, ?_⟩
                    refine (EvP_op2).2 ⟨_, _, core, arm, rfl, ?_, ?_, hev⟩
                    · exact (EvP_op0).2 ⟨1, rfl, slot_one⟩
                    · exact (EvP_op0).2 ⟨ax, hbn, hslot⟩
                  · rintro ⟨p, q, hp, hq, hev⟩
                    have hp' := (star_term c p htc).1 hp
                    rw [(DenP_terminal_iff htform).1 hq] at hev
                    obtain ⟨hb2, hc2, sb, sc, heq2, hsb, hsc, hev2⟩ := (EvP_op2).1 hev
                    obtain ⟨rfl, rfl⟩ := Noun.cell.inj heq2
                    obtain ⟨ax1, hax1, hs1⟩ := (EvP_op0).1 hsb
                    obtain ⟨ax2, hax2, hs2⟩ := (EvP_op0).1 hsc
                    have hax1' : ax1 = 1 := by injection hax1 with h; omega
                    rw [hax1', slot_one] at hs1; obtain rfl := Option.some.inj hs1
                    exact ⟨ax2, c.noun, p, sc, by rw [hax2], hp', hs2, hev2⟩
            · cases n2 with
              | leaf => simp at hr
              | node bn hd d =>
                  cases hd with
                  | leaf => simp at hr
                  | node bhd ax c =>
                      obtain rfl := Option.some.inj hr
                      simp only [noun, isTerminal, Bool.and_eq_true] at htn2 ⊢
                      obtain ⟨⟨_, ⟨_, htax⟩, htc⟩, htd⟩ := htn2
                      have hax : ∀ v, DenP ax v ↔ v = ax.noun := fun v => DenP_terminal_iff htax
                      rw [EvP_op10, DenP_edit_node]
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
            · simp at hr

/-- Congruence generated by equal denotations of pending subverbs in the paper fragment. -/
inductive RelP : Verb → Verb → Prop where
  | leaf {k} : RelP (.leaf k) (.leaf k)
  | base {v w} : v.isPending = true → (∀ x, DenP v x ↔ DenP w x) → RelP v w
  | cong {a l l' r r'} : RelP l l' → RelP r r' → RelP (.node a l r) (.node a l' r')

theorem RelP.refl : ∀ v, RelP v v
  | .leaf _   => .leaf
  | .node _ l r => .cong (RelP.refl l) (RelP.refl r)

theorem replaceAux_relP (i : Nat) (r₀ : Verb) :
    ∀ (v : Verb) (c : Nat),
      (∀ sub, findAt i (enum v c).2 = some sub →
        sub.isPending = true ∧ (∀ x, DenP sub x ↔ DenP r₀ x)) →
      RelP v (replaceAux i r₀ v c).2 := by
  intro v
  induction v with
  | leaf k => intro c _; exact RelP.leaf
  | node a l r ihl ihr =>
      intro c hyp
      simp only [replaceAux]
      by_cases hci : c = i
      · subst hci
        have hf : findAt c (enum (.node a l r) c).2 = some (.node a l r) := by
          simp [enum, findAt]
        obtain ⟨hp, hd⟩ := hyp _ hf
        rw [ite_eq_left rfl]
        exact RelP.base hp hd
      · simp only [ite_eq_right hci]
        have hine : ¬ (i = c) := fun h => hci h.symm
        have hcL : (replaceAux i r₀ l (c+1)).1 = (enum l (c+1)).1 := replaceAux_counter i r₀ l (c+1)
        refine RelP.cong (ihl (c+1) ?_) ?_
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

theorem Rel_denP : ∀ (n : Nat) (v w : Verb), v.noun.size ≤ n → RelP v w → editOk v = true →
    ∀ x, (DenP v x ↔ DenP w x) := by
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
          have El : ∀ y, DenP l y ↔ DenP l' y := fun y => ih l l' (by omega) hl hokl y
          have Er : ∀ y, DenP r y ↔ DenP r' y := fun y => ih r r' (by omega) hr hokr y
          cases a with
          | null =>
              rw [DenP_null, DenP_null]
              exact ⟨fun ⟨p,q,he,hp,hq⟩ => ⟨p,q,he,(El p).1 hp,(Er q).1 hq⟩,
                     fun ⟨p,q,he,hp,hq⟩ => ⟨p,q,he,(El p).2 hp,(Er q).2 hq⟩⟩
          | star =>
              rw [DenP_star, DenP_star]
              exact ⟨fun ⟨p,q,hp,hq,he⟩ => ⟨p,q,(El p).1 hp,(Er q).1 hq,he⟩,
                     fun ⟨p,q,hp,hq,he⟩ => ⟨p,q,(El p).2 hp,(Er q).2 hq,he⟩⟩
          | slot =>
              rw [DenP_slot, DenP_slot]
              exact ⟨fun ⟨ax,b,hp,hq,hs⟩ => ⟨ax,b,(El _).1 hp,(Er _).1 hq,hs⟩,
                     fun ⟨ax,b,hp,hq,hs⟩ => ⟨ax,b,(El _).2 hp,(Er _).2 hq,hs⟩⟩
          | equal =>
              rw [DenP_equal, DenP_equal]
              exact ⟨fun ⟨p,q,hp,hq,he⟩ => ⟨p,q,(El p).1 hp,(Er q).1 hq,he⟩,
                     fun ⟨p,q,hp,hq,he⟩ => ⟨p,q,(El p).2 hp,(Er q).2 hq,he⟩⟩
          | minus =>
              rw [DenP_minus, DenP_minus]
              exact ⟨fun ⟨b,hq,hor⟩ => ⟨b,(Er _).1 hq,
                        hor.imp (fun ⟨h,e⟩ => ⟨(El _).1 h,e⟩) (fun ⟨h,e⟩ => ⟨(El _).1 h,e⟩)⟩,
                     fun ⟨b,hq,hor⟩ => ⟨b,(Er _).2 hq,
                        hor.imp (fun ⟨h,e⟩ => ⟨(El _).2 h,e⟩) (fun ⟨h,e⟩ => ⟨(El _).2 h,e⟩)⟩⟩
          | wut =>
              exact ⟨fun h => (DenP_wut h).elim, fun h => (DenP_wut h).elim⟩
          | edit =>
              cases hr with
              | leaf => exact ⟨fun h => (DenP_edit_leaf h).elim, fun h => (DenP_edit_leaf h).elim⟩
              | base hp _ =>
                  rw [hp] at hcond; simp at hcond
              | @cong b nw nw' od od' hnw hod =>
                  simp only [Verb.noun, Noun.size] at hn
                  simp only [editOk, Bool.and_eq_true] at hokr
                  obtain ⟨⟨_, hoknw⟩, hokod⟩ := hokr
                  have Enw : ∀ y, DenP nw y ↔ DenP nw' y := fun y => ih nw nw' (by omega) hnw hoknw
                    y
                  have Eod : ∀ y, DenP od y ↔ DenP od' y := fun y => ih od od' (by omega) hod hokod
                    y
                  rw [DenP_edit_node, DenP_edit_node]
                  exact ⟨fun ⟨ax,nn,oo,ha,hn2,ho,he⟩ =>
                          ⟨ax,nn,oo,(El _).1 ha,(Enw _).1 hn2,(Eod _).1 ho,he⟩,
                         fun ⟨ax,nn,oo,ha,hn2,ho,he⟩ =>
                          ⟨ax,nn,oo,(El _).2 ha,(Enw _).2 hn2,(Eod _).2 ho,he⟩⟩

theorem den_localP {sub r₀ x} (hd : inDomain sub = true) (hr : reduce sub = some r₀) :
    (DenP sub x ↔ DenP r₀ x) := by
  rw [inDomain, Bool.or_eq_true] at hd
  rcases hd with h | h
  · exact den_localP_opcode h hr
  · exact den_localP_opReady h hr

theorem den_stepP {v v' : Verb} (hwf : editOk v = true) (h : next v = some v') {r : Noun} :
    (∃ fuel, denP fuel v = some r) ↔ (∃ fuel, denP fuel v' = some r) := by
  obtain ⟨i, sub, r₀, hmax, hmap, hdom, hred, hv'⟩ := next_eq_some_iff.1 h
  obtain ⟨w, hmapw, hpw⟩ := hmax.1
  have hpsub : Verb.isPending sub = true := (Option.some.inj (hmapw.symm.trans hmap)) ▸ hpw
  have hrel : RelP v v' := by
    rw [hv', replaceAt]
    apply replaceAux_relP i r₀ v 0
    intro s hs
    have hms : map i v = some s := hs
    have hss : s = sub := Option.some.inj (hms.symm.trans hmap)
    subst hss
    exact ⟨hpsub, fun x => den_localP hdom hred⟩
  exact Rel_denP v.noun.size v v' (Nat.le_refl _) hrel hwf r

theorem run_soundP {v : Verb} {r : Noun} :
    ∀ fuel, editOk v = true → run fuel v = some r → (∃ f, denP f v = some r) := by
  intro fuel
  induction fuel generalizing v with
  | zero => intro _ h; simp [run] at h
  | succ fuel ih =>
      intro hwf h
      rw [run] at h
      cases hnext : next v with
      | some v' =>
          rw [hnext] at h
          exact (den_stepP hwf hnext).2 (ih (editOk_next hnext hwf) h)
      | none =>
          rw [hnext] at h
          simp only [result] at h
          split at h
          · rename_i hterm
            have hr : v.noun = r := Option.some.inj h
            subst hr
            exact ⟨v.noun.size, denP_terminal v v.noun.size hterm (Nat.le_refl _)⟩
          · simp at h

/-- `runProgram` soundness against the derived OP₀–OP₁₀ oracle. -/
theorem paperSound_holds : PaperSound := by
  intro s f r hrun
  obtain ⟨fuel, h⟩ := hrun
  have hd : ∃ f', denP f' (program s f) = some r := run_soundP fuel (editOk_program s f) h
  exact (denP_iff_evalPaper s f r).1 hd

-- main.tex:1090-1094 + Urbit OP₁₁
/-- Conditional wrapper for OP₁₁ adequacy (see `runHint_adequate_complete`). -/
theorem runHint_adequate (hc : HintComplete) (s f r : Noun) :
    (∃ fuel, runHintProgram fuel s f = some r) ↔ (∃ fuel, evalN fuel s f = some r) :=
  ⟨fun ⟨_, h⟩ => runHintProgram_sound h, hc s f r⟩

/-! ### Progress (`denP`-defined + non-terminal ⇒ `next` fires) -/

/-- `denP` of a `*`/operator node forces the LEFT child to be `denP`-defined. -/
theorem denP_left_defined {a : Action} {l r : Verb} {f : Nat} {x : Noun}
    (h : denP (f + 1) (Verb.node a l r) = some x) : ∃ y, denP f l = some y := by
  cases hl : denP f l with
  | some y => exact ⟨y, rfl⟩
  | none =>
      exfalso
      cases a with
      | edit =>
          cases r with
          | leaf k => simp [denP] at h
          | node rb nw od => simp [denP, hl] at h
      | wut => simp [denP] at h
      | _ => simp [denP, hl] at h

/-- `denP` of an `editOk` node forces the RIGHT child to be `denP`-defined (the `edit` case uses
    `editOk`: its right child is non-pending, hence a `⊥`-cons of its two `denP`-defined args). -/
theorem denP_right_defined_of_editOk {a : Action} {l r : Verb} {f : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : denP (f + 1) (Verb.node a l r) = some x) :
    ∃ g y, denP g r = some y := by
  cases a with
  | wut => simp [denP] at h
  | edit =>
      have hrp : Verb.isPending r = false := editOk_edit_cond hok
      cases r with
      | leaf k => simp [denP] at h
      | node rb nw od =>
          have hrb : rb = Action.null := by
            simp only [isPending] at hrp
            cases rb <;> simp_all only [Action.isNull, Bool.not_false, reduceCtorEq]
          subst hrb
          simp only [denP] at h
          cases hnw : denP f nw with
          | none => rw [hnw] at h; simp at h
          | some n =>
              cases hod : denP f od with
              | none => rw [hnw, hod] at h; simp at h
              | some o => exact ⟨f + 1, .cell n o, by simp [denP, hnw, hod]⟩
  | null => cases hr : denP f r with | some y => exact ⟨f, y, hr⟩ | none => exfalso; simp [denP, hr]
    at h
  | star => cases hr : denP f r with | some y => exact ⟨f, y, hr⟩ | none => exfalso; simp [denP, hr]
    at h
  | slot => cases hr : denP f r with | some y => exact ⟨f, y, hr⟩ | none => exfalso; simp [denP, hr]
    at h
  | equal => cases hr : denP f r with | some y => exact ⟨f, y, hr⟩ | none => exfalso; simp [denP,
    hr] at h
  | minus => cases hr : denP f r with | some y => exact ⟨f, y, hr⟩ | none => exfalso; simp [denP,
    hr] at h

/-- **`denP`-definedness descends to every enumerated subnode** (given `editOk`). -/
theorem enum_denP_defined :
    ∀ (v : Verb), editOk v = true → ∀ (c f : Nat) (x : Noun),
      denP f v = some x → ∀ p ∈ (enum v c).2, ∃ g y, denP g p.2 = some y := by
  intro v
  induction v with
  | leaf k => intro _ c f x _ p hp; simp [enum] at hp
  | node a l r ihl ihr =>
      intro hok c f x hdenP p hp
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := by
        cases f with
        | zero => simp [denP] at hdenP
        | succ n => exact ⟨n, rfl⟩
      have hokl := (editOk_children hok).1
      have hokr := (editOk_children hok).2
      simp only [enum, List.mem_cons, List.mem_append] at hp
      rcases hp with hroot | hleft | hright
      · subst hroot; exact ⟨f + 1, x, hdenP⟩
      · obtain ⟨yl, hyl⟩ := denP_left_defined hdenP
        exact ihl hokl (c + 1) f yl hyl p hleft
      · obtain ⟨g, yr, hyr⟩ := denP_right_defined_of_editOk hok hdenP
        exact ihr hokr _ g yr hyr p hright

/-- The subnode `map i v = some sub` of a `denP`-defined `editOk` verb is itself `denP`-defined. -/
theorem DenP_subnode {v : Verb} {x : Noun} (hok : editOk v = true) (hv : DenP v x)
    {i : Nat} {sub : Verb} (hmap : map i v = some sub) : ∃ y, DenP sub y := by
  obtain ⟨f, hf⟩ := hv
  have hmem : (i, sub) ∈ nodes v := mem_nodes_of_map hmap
  obtain ⟨g, y, hg⟩ := enum_denP_defined v hok 0 f x hf (i, sub) hmem
  exact ⟨y, g, hg⟩

/-- `evalPaper` crashes when the formula is an atom (bare noun, no opcode). -/
theorem evalPaper_atom_none (f : Nat) (s : Noun) (k : Nat) :
    evalPaper f s (.atom k) = none := by
  cases f <;> simp [evalPaper]

/-- `evalPaper` crashes on an out-of-fragment opcode head (`op ≥ 11`). -/
theorem evalPaper_op_ge11 (f : Nat) (s tail : Noun) (op : Nat) (h : 11 ≤ op) :
    evalPaper f s (.cell (.atom op) tail) = none := by
  cases f with
  | zero => rfl
  | succ ff =>
      simp only [evalPaper]
      split <;> first | rfl | omega

/-- A `*`-redex with terminal children and a valid opcode head is in the transition domain. -/
theorem inDomain_star_of {L I n2 : Verb} {rb : Action}
    (hL : isTerminal L = true) (hrb : rb.isNull = true) (hI : isTerminal I = true)
    (hn2 : isTerminal n2 = true) (hhead : opHeadOk I = true) :
    inDomain (Verb.node .star L (Verb.node rb I n2)) = true := by
  simp [inDomain, inOpcodeDomain, hL, hrb, hI, hn2, hhead]

private theorem paper_progress_for_evaluation {v : Verb} (L R : Verb) (hL
  : L.isTerminal = true)
  (hR : R.isTerminal = true) (y : Noun) (hsuby : (node Action.star L R).DenP y)
  (hstep :
    (node Action.star L R).inDomain = true → (node Action.star L R).reduce.isSome = true → ∃ v',
      v.next = some v') :
  ∃ v', v.next = some v' := by
  obtain ⟨a', b', hLa, hRb, hev⟩ := DenP_star.1 hsuby
  have haL : a' = L.noun := (DenP_terminal_iff hL).1 hLa
  have hbR : b' = R.noun := (DenP_terminal_iff hR).1 hRb
  subst haL; subst hbR
  cases R with
  | leaf k =>
      exfalso; obtain ⟨f, hf⟩ := hev
      simp [noun, evalPaper_atom_none] at hf
  | node rb fi n2 =>
      simp only [isTerminal, Bool.and_eq_true] at hR
      obtain ⟨⟨hrb, hfi_t⟩, hn2⟩ := hR
      simp only [noun] at hev
      cases fi with
      | node bi ic id =>
          exact hstep (inDomain_star_of hL hrb hfi_t hn2 rfl) (by simp [reduce, redex])
      | leaf op =>
          simp only [noun] at hev
          have hop : op < 11 := by
            rcases Nat.lt_or_ge op 11 with h | h
            · exact h
            · exfalso
              obtain ⟨f, hf⟩ := hev
              rw [evalPaper_op_ge11 f L.noun n2.noun op h] at hf
              exact absurd hf (by simp)
          interval_cases op
          · exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · obtain ⟨hb, hc, _, _, hn2eq, _⟩ := EvP_op2.1 hev
            cases n2 with
            | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
            | node b2 c2 d2 =>
                exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · obtain ⟨hb, hc, _, _, hn2eq, _⟩ := EvP_op5.1 hev
            cases n2 with
            | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
            | node b2 c2 d2 =>
                exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · obtain ⟨b, c, d, cv, hn2eq, _⟩ := EvP_op6.1 hev
            cases n2 with
            | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
            | node b2 c2 d2 =>
                exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · obtain ⟨hb, hc, _, hn2eq, _⟩ := EvP_op7.1 hev
            cases n2 with
            | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
            | node b2 c2 d2 =>
                exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · obtain ⟨hb, hc, _, hn2eq, _⟩ := EvP_op8.1 hev
            cases n2 with
            | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
            | node b2 c2 d2 =>
                exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · obtain ⟨ax, c, _, _, hn2eq, _⟩ := EvP_op9.1 hev
            cases n2 with
            | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
            | node b2 c2 d2 =>
                exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · obtain ⟨ax, c, d, new, old, hn2eq, _⟩ := EvP_op10.1 hev
            cases n2 with
            | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
            | node b2 hd d2 =>
                rw [noun] at hn2eq
                have hhd : hd.noun = Noun.cell (Noun.atom ax) c := (Noun.cell.inj hn2eq).1
                cases hd with
                | leaf k => rw [noun] at hhd; exact absurd hhd (by simp)
                | node bhd axv cc =>
                    exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce,
                      redex])

/-- A `denP`-defined, `editOk`, non-terminal verb has a `next` successor. -/
theorem progressP {v : Verb} {x : Noun} (hwf : editOk v = true) (hd : DenP v x)
    (hnt : isTerminal v = false) : ∃ v', next v = some v' := by
  have hne : getIndex v ≠ none := by
    intro h; rw [getIndex_none_iff_terminal] at h; rw [h] at hnt; simp at hnt
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨sub, hmap⟩ := map_some_of_getIndex hi
  have hmax : IsMaxPending dfsLt v i := getIndex_eq_some_iff.1 hi
  have hsubp : sub.isPending = true := by
    obtain ⟨w, hw, hwp⟩ := hmax.1
    rw [hmap] at hw
    have heq : sub = w := Option.some.inj hw
    rw [heq]; exact hwp
  cases sub with
  | leaf k => simp [isPending] at hsubp
  | node a L R =>
      obtain ⟨hL, hR⟩ := children_terminal_of_getIndex hi hmap
      obtain ⟨y, hsuby⟩ := DenP_subnode hwf hd hmap
      have hstep : inDomain (Verb.node a L R) = true →
          (reduce (Verb.node a L R)).isSome = true → ∃ v', next v = some v' := by
        intro hdom hred
        cases hrr : reduce (Verb.node a L R) with
        | none => rw [hrr] at hred; simp at hred
        | some rr =>
            exact ⟨replaceAt i v rr,
              next_eq_some_iff.2 ⟨i, Verb.node a L R, rr, hmax, hmap, hdom, hrr, rfl⟩⟩
      cases a with
      | null => simp [isPending, Action.isNull] at hsubp
      | wut => exact absurd hsuby DenP_wut
      | equal =>
          have hdom : inDomain (Verb.node .equal L R) = true := by
            simp [inDomain, inOpcodeDomain, opReady, Action.isOperator, hL, hR]
          exact hstep hdom (by simp [reduce])
      | slot =>
          obtain ⟨ax, b, hLax, hRb, hslot⟩ := DenP_slot.1 hsuby
          have hLn : L.noun = Noun.atom ax := ((DenP_terminal_iff hL).1 hLax).symm
          have hbR : b = R.noun := (DenP_terminal_iff hR).1 hRb
          subst hbR
          have hdom : inDomain (Verb.node .slot L R) = true := by
            simp [inDomain, inOpcodeDomain, opReady, Action.isOperator, hL, hR]
          exact hstep hdom (by simp [reduce, hLn, hslot])
      | minus =>
          obtain ⟨b, hRb, hcase⟩ := DenP_minus.1 hsuby
          have hbR : b = R.noun := (DenP_terminal_iff hR).1 hRb
          subst hbR
          have hdom : inDomain (Verb.node .minus L R) = true := by
            simp [inDomain, inOpcodeDomain, opReady, Action.isOperator, hL, hR]
          rcases hcase with ⟨hL3, _⟩ | ⟨hL4, hlus⟩
          · have hLn : L.noun = Noun.atom 3 := ((DenP_terminal_iff hL).1 hL3).symm
            exact hstep hdom (by simp [reduce, hLn])
          · have hLn : L.noun = Noun.atom 4 := ((DenP_terminal_iff hL).1 hL4).symm
            exact hstep hdom (by simp [reduce, hLn, hlus])
      | edit =>
          cases R with
          | leaf k => exact absurd hsuby DenP_edit_leaf
          | node rb nw od =>
              simp only [isTerminal, Bool.and_eq_true] at hR
              obtain ⟨⟨hrb, hnw⟩, hod⟩ := hR
              obtain ⟨ax, n, o, hLax, hnwn, hodo, hedit⟩ := DenP_edit_node.1 hsuby
              have hLn : L.noun = Noun.atom ax := ((DenP_terminal_iff hL).1 hLax).symm
              have hnwn' : n = nw.noun := (DenP_terminal_iff hnw).1 hnwn
              have hodo' : o = od.noun := (DenP_terminal_iff hod).1 hodo
              subst hnwn'; subst hodo'
              have hdom : inDomain (Verb.node .edit L (Verb.node rb nw od)) = true := by
                simp [inDomain, inOpcodeDomain, opReady, Action.isOperator, hL,
                      isTerminal, hrb, hnw, hod]
              exact hstep hdom (by simp [reduce, hLn, hedit])
      | star =>
          exact paper_progress_for_evaluation L R hL hR y hsuby hstep
/-! ### Denotation-keyed cost measure -/

/-- Weighted `evalPaper`-derivation cost: mirrors `evalPaper` clause-for-clause (same recursive
    calls), each opcode contributing a positive weight.  Returns 0 where `evalPaper` crashes. -/
def pcost : Nat → Noun → Noun → Nat
  | 0, _, _ => 0
  | _ + 1, _, .atom _ => 0
  | f + 1, subj, .cell (.cell b c) d =>
      1 + pcost f subj (.cell b c) + pcost f subj d
  | f + 1, subj, .cell (.atom op) tail =>
    match op with
    | 0 => 2
    | 1 => 1
    | 2 =>
        match tail with
        | .cell b c =>
            let inner := match evalPaper f subj b, evalPaper f subj c with
                         | some sb, some sc => pcost f sb sc
                         | _, _ => 0
            1 + pcost f subj b + pcost f subj c + inner
        | _ => 0
    | 3 => 2 + pcost f subj tail
    | 4 => 2 + pcost f subj tail
    | 5 =>
        match tail with
        | .cell b c => 2 + pcost f subj b + pcost f subj c
        | _ => 0
    | 6 =>
        match tail with
        | .cell b (.cell c d) =>
            let inner := match evalPaper f subj b with
                         | some (.atom 0) => pcost f subj c
                         | some (.atom 1) => pcost f subj d
                         | _ => 0
            100 + pcost f subj b + inner
        | _ => 0
    | 7 =>
        match tail with
        | .cell b c =>
            let inner := match evalPaper f subj b with
                         | some sb => pcost f sb c
                         | _ => 0
            1 + pcost f subj b + inner
        | _ => 0
    | 8 =>
        match tail with
        | .cell b c =>
            let inner := match evalPaper f subj b with
                         | some sb => pcost f (.cell sb subj) c
                         | _ => 0
            1 + pcost f subj b + inner
        | _ => 0
    | 9 =>
        match tail with
        | .cell (.atom ax) c =>
            let inner := match evalPaper f subj c with
                         | some core =>
                             match Noun.slot ax core with
                             | some arm => pcost f core arm
                             | _ => 0
                         | _ => 0
            20 + pcost f subj c + inner
        | _ => 0
    | 10 =>
        match tail with
        | .cell (.cell (.atom _) c) d => 2 + pcost f subj c + pcost f subj d
        | _ => 0
    | _ => 0

/-- Verb cost (structural in the verb; `F` is a fixed lookup-fuel for denotations).  A `*`-node
    charges `pcost` of its two denotations (the firing cost); an operator node charges `1`;
    `⊥`/leaf charge only their children.  Being structural (not fuel-recursive), `replaceAt`
    swaps exactly one subtree's cost, so the step-congruence is immediate. -/
def vcost (F : Nat) : Verb → Nat
  | .leaf _ => 0
  | .node a l r =>
      (match a with
       | .star => match denP F l, denP F r with
                  | some sa, some fo => pcost F sa fo
                  | _, _ => 0
       | .slot => 1
       | .equal => 1
       | .minus => 1
       | .edit => 1
       | .null => 0
       | .wut => 0) + vcost F l + vcost F r

/-- `pcost` is unchanged by extra fuel once `evalPaper` succeeds (mirrors `evalPaper_succ`). -/
theorem pcost_succ {n : Nat} {a b : Noun} {r : Noun}
    (hb : evalPaper n a b = some r) : pcost (n + 1) a b = pcost n a b := by
  induction n, a, b using evalPaper.induct generalizing r <;>
    simp only [evalPaper] at hb <;>
    simp_all only [pcost, Option.map_eq_some_iff, Option.bind_eq_some_iff,
      Option.some.injEq, reduceCtorEq] <;>
    grind only [evalPaper_succ]

/-- `pcost` stabilizes for any fuel `≥ n` once `evalPaper n` succeeds. -/
theorem pcost_mono {n m : Nat} {a b r : Noun} (hle : n ≤ m) (hb : evalPaper n a b = some r) :
    pcost m a b = pcost n a b := by
  induction hle with
  | refl => rfl
  | step hk ih => rw [pcost_succ (evalPaper_mono hk hb)]; exact ih

/-- `vcost` of a terminal verb is `0`. -/
theorem vcost_terminal : ∀ (v : Verb), isTerminal v = true → ∀ F, vcost F v = 0 := by
  intro v
  induction v with
  | leaf k => intro _ F; rfl
  | node a l r ihl ihr =>
      intro hterm F
      simp only [isTerminal, Bool.and_eq_true] at hterm
      obtain ⟨⟨hnull, hl⟩, hr⟩ := hterm
      have ha : a = Action.null := by cases a <;> simp_all only [Action.isNull, reduceCtorEq]
      subst ha
      simp only [vcost]; rw [ihl hl F, ihr hr F]

-- main.tex:1052-1083  (`i ∈ [11]` = {0,…,10})
/-- Conditional wrapper for OP₀–OP₁₀ consistency (see `runProgram_adequate_complete`). -/
theorem runProgram_adequate (hc : PaperComplete) (s f r : Noun) :
    (∃ fuel, runProgram fuel s f = some r) ↔ (∃ fuel, evalPaper fuel s f = some r) :=
  ⟨paperSound_holds s f r, hc s f r⟩

end Verb
end Nock
