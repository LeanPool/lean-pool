/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import LeanPool.PureNock.Reference
public import Mathlib.Data.ZMod.Basic

/-!
# Modular (field-noun) evaluation

The paper's nouns are field-valued: leaves carry elements of a field `𝔽`
(`main.tex:345–349`, `1023`) and the increment operator reduces modulo the
characteristic, `+(n) = (1 + n) mod p` (`main.tex:1531–1534`).  The Nat-level
reference `evalN` (`Nock/Reference.lean`) instead uses the unbounded successor
`n ↦ n + 1`.

This module makes the modulus-generic embedding precise over `Nat`-atom nouns,
parameterized by an arbitrary modulus `q` (so it never needs a concrete prime and
never declares a project axiom).  It defines:

* `BoundedBy q n` — every atom of `n` is `< q` (a `q`-bounded / canonical field noun);
* `evalFBy q`     — the **modular** evaluator (OP₄ increment `mod q`);
* `evalGBy q`     — the **guarded** evaluator that *crashes* rather than reaching an
                    atom `≥ q`; a successful `evalGBy q` run witnesses no-overflow;
* `agreeBy`       — on `q`-bounded inputs, a successful guarded run makes the Nat
                    reference `evalN` and the modular `evalFBy q` return the same
                    (`q`-bounded) noun.

Everything is `q`-generic; the ZMod injectivity fact `zmod_natCast_inj_of_lt`
requires no primality assumption.  Axioms stay within `{propext, Classical.choice, Quot.sound}`.
-/

@[expose] public section

namespace Nock.FieldEmbedding

open Nock Nock.Noun

/-! ## Field nouns: bounded leaf labels -/

/-- `BoundedBy q n` means that every atom (leaf) of `n` is in the numeric range `[0,q)`.
    This is the bound needed when the operative modulus varies with a security parameter. -/
def BoundedBy (q : ℕ) : Noun → Prop
  | .atom n   => n < q
  | .cell l r => BoundedBy q l ∧ BoundedBy q r

@[simp] theorem BoundedBy_atom {q n : ℕ} : BoundedBy q (.atom n) ↔ n < q := Iff.rfl
@[simp] theorem BoundedBy_cell {q : ℕ} {l r : Noun} :
    BoundedBy q (.cell l r) ↔ BoundedBy q l ∧ BoundedBy q r := Iff.rfl

/-! ## The field increment `+(n) = (1 + n) mod q` (`main.tex:1531–1534`) -/

/-- Increment modulo `q` on an atom, crash on a cell. -/
def lusFBy (q : ℕ) : Noun → Option Noun
  | .atom n   => some (.atom ((n + 1) % q))
  | .cell _ _ => none

/-- Guarded Nat increment: like `Noun.lus` (`n ↦ n+1`) but **crashes** instead of overflowing
    the selected range, i.e. it refuses to produce an atom `≥ q`.  A successful guarded run
    witnesses that no increment reached `q` — this is how the no-overflow side condition is
    encoded honestly. -/
def lusGBy (q : ℕ) : Noun → Option Noun
  | .atom n   => if n + 1 < q then some (.atom (n + 1)) else none
  | .cell _ _ => none

/-! ## The field-valued evaluator `evalFBy`

`evalFBy q` is `Nock.evalN` verbatim EXCEPT that OP₄ (`+`) uses increment modulo `q`.
All other operators are structural (they only rearrange existing leaves) or produce the
constants `0`/`1`, so over field nouns they coincide with the Nat versions; hence `evalFBy`
reuses `Noun.slot`, `Noun.edit`, `Noun.wut`, `Noun.tis` from `Nock/Reference.lean`.  Equality
(OP₅, `main.tex:1525`) compares nouns structurally; over `q`-bounded nouns this is field
equality (distinct `< q` atoms are distinct in `ZMod q`). -/
/-- Fuel-indexed Nock evaluation with increment reduced modulo the supplied modulus. -/
def evalFBy (q : ℕ) : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | fuel + 1, subj, .cell (.cell b c) d =>
      match evalFBy q fuel subj (.cell b c), evalFBy q fuel subj d with
      | some l, some r => some (.cell l r)
      | _, _ => none
  | fuel + 1, subj, .cell (.atom op) tail =>
    match op with
    | 0 => match tail with
           | .atom ax => slot ax subj
           | _ => none
    | 1 => some tail
    | 2 => match tail with
           | .cell b c =>
             match evalFBy q fuel subj b, evalFBy q fuel subj c with
             | some sb, some sc => evalFBy q fuel sb sc
             | _, _ => none
           | _ => none
    | 3 => (evalFBy q fuel subj tail).map wut
    | 4 => (evalFBy q fuel subj tail).bind (lusFBy q)
    | 5 => match tail with
           | .cell b c =>
             match evalFBy q fuel subj b, evalFBy q fuel subj c with
             | some sb, some sc => some (tis sb sc)
             | _, _ => none
           | _ => none
    | 6 => match tail with
           | .cell b (.cell c d) =>
             match evalFBy q fuel subj b with
             | some (.atom 0) => evalFBy q fuel subj c
             | some (.atom 1) => evalFBy q fuel subj d
             | _ => none
           | _ => none
    | 7 => match tail with
           | .cell b c =>
             match evalFBy q fuel subj b with
             | some sb => evalFBy q fuel sb c
             | none => none
           | _ => none
    | 8 => match tail with
           | .cell b c =>
             match evalFBy q fuel subj b with
             | some sb => evalFBy q fuel (.cell sb subj) c
             | none => none
           | _ => none
    | 9 => match tail with
           | .cell (.atom ax) c =>
             match evalFBy q fuel subj c with
             | some core =>
               match slot ax core with
               | some arm => evalFBy q fuel core arm
               | none => none
             | none => none
           | _ => none
    | 10 => match tail with
            | .cell (.cell (.atom ax) c) d =>
              match evalFBy q fuel subj c, evalFBy q fuel subj d with
              | some new, some old => edit ax new old
              | _, _ => none
            | _ => none
    | 11 => match tail with
            | .cell (.cell _ clue) body =>
              match evalFBy q fuel subj clue with
              | some _ => evalFBy q fuel subj body
              | none => none
            | .cell (.atom _) body => evalFBy q fuel subj body
            | _ => none
    | _ => none

/-! ## The guarded (no-overflow) evaluator `evalGBy`

`evalGBy q` is `Nock.evalN` verbatim EXCEPT that OP₄ uses `lusGBy q`, which crashes on overflow. -/
/-- Fuel-indexed Nock evaluation that rejects increments reaching the supplied modulus. -/
def evalGBy (q : ℕ) : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | fuel + 1, subj, .cell (.cell b c) d =>
      match evalGBy q fuel subj (.cell b c), evalGBy q fuel subj d with
      | some l, some r => some (.cell l r)
      | _, _ => none
  | fuel + 1, subj, .cell (.atom op) tail =>
    match op with
    | 0 => match tail with
           | .atom ax => slot ax subj
           | _ => none
    | 1 => some tail
    | 2 => match tail with
           | .cell b c =>
             match evalGBy q fuel subj b, evalGBy q fuel subj c with
             | some sb, some sc => evalGBy q fuel sb sc
             | _, _ => none
           | _ => none
    | 3 => (evalGBy q fuel subj tail).map wut
    | 4 => (evalGBy q fuel subj tail).bind (lusGBy q)
    | 5 => match tail with
           | .cell b c =>
             match evalGBy q fuel subj b, evalGBy q fuel subj c with
             | some sb, some sc => some (tis sb sc)
             | _, _ => none
           | _ => none
    | 6 => match tail with
           | .cell b (.cell c d) =>
             match evalGBy q fuel subj b with
             | some (.atom 0) => evalGBy q fuel subj c
             | some (.atom 1) => evalGBy q fuel subj d
             | _ => none
           | _ => none
    | 7 => match tail with
           | .cell b c =>
             match evalGBy q fuel subj b with
             | some sb => evalGBy q fuel sb c
             | none => none
           | _ => none
    | 8 => match tail with
           | .cell b c =>
             match evalGBy q fuel subj b with
             | some sb => evalGBy q fuel (.cell sb subj) c
             | none => none
           | _ => none
    | 9 => match tail with
           | .cell (.atom ax) c =>
             match evalGBy q fuel subj c with
             | some core =>
               match slot ax core with
               | some arm => evalGBy q fuel core arm
               | none => none
             | none => none
           | _ => none
    | 10 => match tail with
            | .cell (.cell (.atom ax) c) d =>
              match evalGBy q fuel subj c, evalGBy q fuel subj d with
              | some new, some old => edit ax new old
              | _, _ => none
            | _ => none
    | 11 => match tail with
            | .cell (.cell _ clue) body =>
              match evalGBy q fuel subj clue with
              | some _ => evalGBy q fuel subj body
              | none => none
            | .cell (.atom _) body => evalGBy q fuel subj body
            | _ => none
    | _ => none

/-! ## `BoundedBy` is preserved by the structural operators -/

/-- `slot` returns a subtree of `n`, so it preserves every numeric leaf bound. -/
theorem slot_boundedBy (q : ℕ) (ax : Nat) (n : Noun) :
    BoundedBy q n → ∀ {m : Noun}, slot ax n = some m → BoundedBy q m := by
  induction ax, n using Nock.Noun.slot.induct with
  | case1 x => intro _ m h; simp [slot] at h
  | case2 n => intro hn m h; simp only [slot] at h; obtain rfl := Option.some.inj h; exact hn
  | case3 a n l r hrec ih =>
      intro hn m h
      have hlr : BoundedBy q (Noun.cell l r) := ih hn hrec
      simp only [slot, hrec] at h
      split at h
      · obtain rfl := Option.some.inj h; exact hlr.1
      · obtain rfl := Option.some.inj h; exact hlr.2
  | case4 a n hno ih =>
      intro hn m h
      simp only [slot] at h
      cases hs : slot ((a + 2) / 2) n with
      | none => simp at h
      | some w =>
        cases w with
        | atom k => simp at h
        | cell l r => exact (hno l r hs).elim

/-- `edit` grafts `new` into `old`, so it preserves every numeric leaf bound. -/
theorem edit_boundedBy (q : ℕ) (ax : Nat) (new old : Noun) :
    BoundedBy q new → BoundedBy q old →
      ∀ {m : Noun}, edit ax new old = some m → BoundedBy q m := by
  induction ax, new, old using Nock.Noun.edit.induct with
  | case1 x y => intro _ _ m h; simp [edit] at h
  | case2 new x => intro hnew _ m h; simp only [edit] at h; obtain rfl := Option.some.inj h; exact
    hnew
  | case3 a new old sibAxis sib hsib paired ih =>
      intro hnew hold m h
      have hsibB : BoundedBy q sib := slot_boundedBy q _ _ hold hsib
      have hpair : ∀ b : Bool, BoundedBy q
          (if b = true then new.cell sib else sib.cell new) := by
        intro b; cases b <;> exact ⟨by assumption, by assumption⟩
      simp only [edit] at h
      rw [show slot (if ((a + 2) % 2 == 0) = true then a + 2 + 1 else a + 2 - 1) old = some sib
            from hsib] at h
      exact ih (hpair _) hold h
  | case4 a new old sibAxis hnone =>
      intro _ _ m h
      simp only [edit] at h
      rw [show slot (if ((a + 2) % 2 == 0) = true then a + 2 + 1 else a + 2 - 1) old = none
            from hnone] at h
      simp at h

/-- Increment modulo a positive `q` always produces an atom `< q`. -/
theorem lusFBy_bounded {q : ℕ} (hq : 0 < q) {x m : Noun}
    (h : lusFBy q x = some m) : BoundedBy q m := by
  cases x with
  | atom n => simp only [lusFBy] at h; obtain rfl := Option.some.inj h; exact Nat.mod_lt _ hq
  | cell l r => simp [lusFBy] at h

theorem wut_boundedBy {q : ℕ} (hq : 1 < q) (x : Noun) : BoundedBy q (wut x) := by
  cases x with
  | cell _ _ =>
      simp only [wut, BoundedBy_atom]
      omega
  | atom _ => exact hq

theorem tis_boundedBy {q : ℕ} (hq : 1 < q) (a b : Noun) : BoundedBy q (tis a b) := by
  unfold tis; split
  · simp only [BoundedBy_atom]
    omega
  · exact hq

/-! ## Main agreement lemma (the no-overflow simulation)

`agreeBy` is proved by induction on `fuel`.  Its conclusion bundles the three facts that must
be carried through the recursion simultaneously:
* `evalN … = some r`   — the Nat reference reproduces the guarded result;
* `evalFBy q … = some r` — the modular evaluator reproduces it too; and
* `BoundedBy q r`      — the result is again a field noun (needed to feed nested calls).

The ONLY place the three evaluators differ is OP₄ (`+`): there `evalGBy q` succeeds exactly when
`n + 1 < q`, and under that guard the Nat increment (`n+1`) and the modular increment
(`(n+1) mod q`) coincide — this is where no-overflow discharges the divergence. -/
private theorem guarded_hint_agreement (q fuel : ℕ)
  (ih :
    ∀ (s f r : Noun),
      BoundedBy q s →
        BoundedBy q f →
          evalGBy q fuel s f = some r → evalN fuel s f = some r ∧ evalFBy q fuel s f = some r ∧
            BoundedBy q r)
  (s r : Noun) (hs : BoundedBy q s) (tail : Noun) (hft : BoundedBy q tail)
  (hG : evalGBy q (fuel + 1) s ((atom 11).cell tail) = some r) :
  evalN (fuel + 1) s ((atom 11).cell tail) = some r ∧
    evalFBy q (fuel + 1) s ((atom 11).cell tail) = some r ∧ BoundedBy q r := by
  match tail with
  | .cell (.cell hd clue) body =>
      obtain ⟨⟨-, hfclue⟩, hfbody⟩ := hft
      simp only [evalGBy] at hG
      cases hcl : evalGBy q fuel s clue with
      | none => rw [hcl] at hG; simp at hG
      | some vc =>
        rw [hcl] at hG
        obtain ⟨hNcl, hFcl, _⟩ := ih s clue vc hs hfclue hcl
        obtain ⟨hNb, hFb, hBr⟩ := ih s body r hs hfbody hG
        exact ⟨by simp only [evalN, hNcl, hNb],
               by simp only [evalFBy, hFcl, hFb], hBr⟩
  | .cell (.atom hint) body =>
      obtain ⟨-, hfbody⟩ := hft
      simp only [evalGBy] at hG
      obtain ⟨hNb, hFb, hBr⟩ := ih s body r hs hfbody hG
      exact ⟨by simp only [evalN, hNb],
             by simp only [evalFBy, hFb], hBr⟩
  | .atom _ => simp [evalGBy] at hG

private theorem guarded_conditional_agreement (q fuel : ℕ)
  (ih :
    ∀ (s f r : Noun),
      BoundedBy q s →
        BoundedBy q f →
          evalGBy q fuel s f = some r → evalN fuel s f = some r ∧ evalFBy q fuel s f = some r ∧
            BoundedBy q r)
  (s r : Noun) (hs : BoundedBy q s) (tail : Noun) (hft : BoundedBy q tail)
  (hG : evalGBy q (fuel + 1) s ((atom 6).cell tail) = some r) :
  evalN (fuel + 1) s ((atom 6).cell tail) = some r ∧
    evalFBy q (fuel + 1) s ((atom 6).cell tail) = some r ∧ BoundedBy q r := by
  match tail with
  | .cell b (.cell c d) =>
      obtain ⟨hfb, hfc, hfd⟩ := hft
      simp only [evalGBy] at hG
      cases hb : evalGBy q fuel s b with
      | none => rw [hb] at hG; simp at hG
      | some vb =>
        obtain ⟨hNb, hFb, _⟩ := ih s b vb hs hfb hb
        rw [hb] at hG
        match vb, hNb, hFb, hG with
        | .atom 0, hNb, hFb, hG =>
            obtain ⟨hNc, hFc, hBr⟩ := ih s c r hs hfc hG
            exact ⟨by simp only [evalN, hNb, hNc],
                   by simp only [evalFBy, hFb, hFc], hBr⟩
        | .atom 1, hNb, hFb, hG =>
            obtain ⟨hNd, hFd, hBr⟩ := ih s d r hs hfd hG
            exact ⟨by simp only [evalN, hNb, hNd],
                   by simp only [evalFBy, hFb, hFd], hBr⟩
        | .atom (n+2), _, _, hG => simp at hG
        | .cell _ _, _, _, hG => simp at hG
  | .cell b (.atom _) => simp [evalGBy] at hG
  | .atom _ => simp [evalGBy] at hG

theorem agreeBy (q : ℕ) (hq : 1 < q) :
    ∀ (fuel : Nat) (s f r : Noun), BoundedBy q s → BoundedBy q f →
      evalGBy q fuel s f = some r →
        evalN fuel s f = some r ∧ evalFBy q fuel s f = some r ∧ BoundedBy q r := by
  intro fuel
  induction fuel with
  | zero => intro s f r _ _ hG; simp [evalGBy] at hG
  | succ fuel ih =>
    intro s f r hs hf hG
    match f with
    | .atom a => simp [evalGBy] at hG
    | .cell (.cell b c) d =>
        obtain ⟨hfbc, hfd⟩ := hf
        simp only [evalGBy] at hG
        cases hbc : evalGBy q fuel s (.cell b c) with
        | none => rw [hbc] at hG; simp at hG
        | some l =>
          cases hd : evalGBy q fuel s d with
          | none => rw [hbc, hd] at hG; simp at hG
          | some r' =>
            rw [hbc, hd] at hG
            simp only [Option.some.injEq] at hG
            obtain ⟨hNbc, hFbc, hBl⟩ := ih s (.cell b c) l hs hfbc hbc
            obtain ⟨hNd, hFd, hBr⟩ := ih s d r' hs hfd hd
            subst hG
            refine ⟨?_, ?_, ⟨hBl, hBr⟩⟩
            · simp only [evalN, hNbc, hNd]
            · simp only [evalFBy, hFbc, hFd]
    | .cell (.atom op) tail =>
        obtain ⟨-, hft⟩ := hf
        match op with
        | 0 =>
            simp only [evalGBy] at hG
            match tail with
            | .atom ax =>
                refine ⟨?_, ?_, slot_boundedBy q ax s hs hG⟩
                · simpa only [evalN] using hG
                · simpa only [evalFBy] using hG
            | .cell _ _ => simp at hG
        | 1 =>
            simp only [evalGBy] at hG
            obtain rfl := Option.some.inj hG
            exact ⟨by simp only [evalN], by simp only [evalFBy], hft⟩
        | 2 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGBy] at hG
                cases hb : evalGBy q fuel s b with
                | none => rw [hb] at hG; simp at hG
                | some sb =>
                  cases hc : evalGBy q fuel s c with
                  | none => rw [hb, hc] at hG; simp at hG
                  | some sc =>
                    rw [hb, hc] at hG
                    obtain ⟨hNb, hFb, hBb⟩ := ih s b sb hs hfb hb
                    obtain ⟨hNc, hFc, hBc⟩ := ih s c sc hs hfc hc
                    obtain ⟨hN2, hF2, hBr⟩ := ih sb sc r hBb hBc hG
                    exact ⟨by simp only [evalN, hNb, hNc, hN2],
                           by simp only [evalFBy, hFb, hFc, hF2], hBr⟩
            | .atom _ => simp [evalGBy] at hG
        | 3 =>
            simp only [evalGBy] at hG
            cases ht : evalGBy q fuel s tail with
            | none => rw [ht] at hG; simp at hG
            | some v =>
              rw [ht] at hG
              simp only [Option.map_some, Option.some.injEq] at hG
              obtain ⟨hN, hF, _⟩ := ih s tail v hs hft ht
              subst hG
              exact ⟨by simp only [evalN, hN, Option.map_some],
                     by simp only [evalFBy, hF, Option.map_some], wut_boundedBy hq v⟩
        | 4 =>
            simp only [evalGBy] at hG
            cases ht : evalGBy q fuel s tail with
            | none => rw [ht] at hG; simp at hG
            | some v =>
              rw [ht] at hG
              obtain ⟨hN, hF, hBv⟩ := ih s tail v hs hft ht
              cases v with
              | cell _ _ => simp [lusGBy] at hG
              | atom n =>
                simp only [Option.bind_some, lusGBy] at hG
                split at hG
                · rename_i hlt
                  obtain rfl := Option.some.inj hG
                  refine ⟨?_, ?_, ?_⟩
                  · simp only [evalN, hN, Option.bind_some, Noun.lus]
                  · simp only [evalFBy, hF, Option.bind_some, lusFBy, Nat.mod_eq_of_lt hlt]
                  · exact hlt
                · simp at hG
        | 5 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGBy] at hG
                cases hb : evalGBy q fuel s b with
                | none => rw [hb] at hG; simp at hG
                | some sb =>
                  cases hc : evalGBy q fuel s c with
                  | none => rw [hb, hc] at hG; simp at hG
                  | some sc =>
                    rw [hb, hc] at hG
                    simp only [Option.some.injEq] at hG
                    obtain ⟨hNb, hFb, _⟩ := ih s b sb hs hfb hb
                    obtain ⟨hNc, hFc, _⟩ := ih s c sc hs hfc hc
                    subst hG
                    exact ⟨by simp only [evalN, hNb, hNc],
                           by simp only [evalFBy, hFb, hFc], tis_boundedBy hq sb sc⟩
            | .atom _ => simp [evalGBy] at hG
        | 6 =>
            exact guarded_conditional_agreement q fuel ih s r hs tail hft hG
        | 7 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGBy] at hG
                cases hb : evalGBy q fuel s b with
                | none => rw [hb] at hG; simp at hG
                | some sb =>
                  rw [hb] at hG
                  obtain ⟨hNb, hFb, hBb⟩ := ih s b sb hs hfb hb
                  obtain ⟨hN7, hF7, hBr⟩ := ih sb c r hBb hfc hG
                  exact ⟨by simp only [evalN, hNb, hN7],
                         by simp only [evalFBy, hFb, hF7], hBr⟩
            | .atom _ => simp [evalGBy] at hG
        | 8 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGBy] at hG
                cases hb : evalGBy q fuel s b with
                | none => rw [hb] at hG; simp at hG
                | some sb =>
                  rw [hb] at hG
                  obtain ⟨hNb, hFb, hBb⟩ := ih s b sb hs hfb hb
                  obtain ⟨hN8, hF8, hBr⟩ := ih (.cell sb s) c r ⟨hBb, hs⟩ hfc hG
                  exact ⟨by simp only [evalN, hNb, hN8],
                         by simp only [evalFBy, hFb, hF8], hBr⟩
            | .atom _ => simp [evalGBy] at hG
        | 9 =>
            match tail with
            | .cell (.atom ax) c =>
                obtain ⟨-, hfc⟩ := hft
                simp only [evalGBy] at hG
                cases hc : evalGBy q fuel s c with
                | none => rw [hc] at hG; simp at hG
                | some core =>
                  rw [hc] at hG
                  dsimp only at hG
                  obtain ⟨hNc, hFc, hBcore⟩ := ih s c core hs hfc hc
                  cases harm : slot ax core with
                  | none => rw [harm] at hG; simp at hG
                  | some arm =>
                    rw [harm] at hG
                    dsimp only at hG
                    have hBarm : BoundedBy q arm := slot_boundedBy q ax core hBcore harm
                    obtain ⟨hN9, hF9, hBr⟩ := ih core arm r hBcore hBarm hG
                    exact ⟨by simp only [evalN, hNc, harm, hN9],
                           by simp only [evalFBy, hFc, harm, hF9], hBr⟩
            | .cell (.cell _ _) _ => simp [evalGBy] at hG
            | .atom _ => simp [evalGBy] at hG
        | 10 =>
            match tail with
            | .cell (.cell (.atom ax) c) d =>
                obtain ⟨⟨-, hfc⟩, hfd⟩ := hft
                simp only [evalGBy] at hG
                cases hc : evalGBy q fuel s c with
                | none => rw [hc] at hG; simp at hG
                | some new =>
                  cases hd : evalGBy q fuel s d with
                  | none => rw [hc, hd] at hG; simp at hG
                  | some old =>
                    rw [hc, hd] at hG
                    obtain ⟨hNc, hFc, hBnew⟩ := ih s c new hs hfc hc
                    obtain ⟨hNd, hFd, hBold⟩ := ih s d old hs hfd hd
                    refine ⟨?_, ?_, edit_boundedBy q ax new old hBnew hBold hG⟩
                    · simp only [evalN, hNc, hNd]; exact hG
                    · simp only [evalFBy, hFc, hFd]; exact hG
            | .cell (.cell (.cell _ _) _) _ => simp [evalGBy] at hG
            | .cell (.atom _) _ => simp [evalGBy] at hG
            | .atom _ => simp [evalGBy] at hG
        | 11 =>
            exact guarded_hint_agreement q fuel ih s r hs tail hft hG
        | (n+12) => simp [evalGBy] at hG

/-! ## The guarded evaluator refines `evalN`: the guard only removes behaviours -/

theorem evalGBy_le_evalN {q : ℕ} (hq : 1 < q) {fuel : Nat} {s f r : Noun}
    (hs : BoundedBy q s) (hf : BoundedBy q f) (h : evalGBy q fuel s f = some r) :
    evalN fuel s f = some r :=
  (agreeBy q hq fuel s f r hs hf h).1

/-! ## The no-overflow agreement theorem -/

/-- **No-overflow agreement.**  For `q`-bounded inputs, a successful guarded run contains no
    modular wrap at `q`, so the Nat and modulo-`q` evaluators return the same `q`-bounded noun. -/
theorem noOverflow_agreeBy {q : ℕ} (hq : 1 < q) {fuel : Nat} {s f r : Noun}
    (hs : BoundedBy q s) (hf : BoundedBy q f) (hno : evalGBy q fuel s f = some r) :
    evalN fuel s f = some r ∧ evalFBy q fuel s f = some r ∧ BoundedBy q r :=
  agreeBy q hq fuel s f r hs hf hno

/-! ## The modular evaluator is a field-noun endomorphism

Unconditionally (no guard): on `q`-bounded inputs, every successful modular run returns a
`q`-bounded noun.  `evalFBy q` maps canonical field nouns to canonical field nouns — its OP₄
increment is `(n+1) mod q < q`, and every other opcode only rearranges existing (bounded) leaves
or produces `0`/`1`. -/
theorem evalFBy_boundedBy {q : ℕ} (hq : 1 < q) :
    ∀ (fuel : Nat) (s f r : Noun), BoundedBy q s → BoundedBy q f →
      evalFBy q fuel s f = some r → BoundedBy q r := by
  intro fuel
  induction fuel with
  | zero => intro s f r _ _ h; simp [evalFBy] at h
  | succ fuel ih =>
    intro s f r hs hf h
    match f with
    | .atom a => simp [evalFBy] at h
    | .cell (.cell b c) d =>
        obtain ⟨hfbc, hfd⟩ := hf
        simp only [evalFBy] at h
        cases hbc : evalFBy q fuel s (.cell b c) with
        | none => rw [hbc] at h; simp at h
        | some l =>
          cases hd : evalFBy q fuel s d with
          | none => rw [hbc, hd] at h; simp at h
          | some r' =>
            rw [hbc, hd] at h; simp only [Option.some.injEq] at h; subst h
            exact ⟨ih s (.cell b c) l hs hfbc hbc, ih s d r' hs hfd hd⟩
    | .cell (.atom op) tail =>
        obtain ⟨-, hft⟩ := hf
        match op with
        | 0 =>
            simp only [evalFBy] at h
            match tail with
            | .atom ax => exact slot_boundedBy q ax s hs h
            | .cell _ _ => simp at h
        | 1 => simp only [evalFBy] at h; obtain rfl := Option.some.inj h; exact hft
        | 2 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalFBy] at h
                cases hb : evalFBy q fuel s b with
                | none => rw [hb] at h; simp at h
                | some sb =>
                  cases hc : evalFBy q fuel s c with
                  | none => rw [hb, hc] at h; simp at h
                  | some sc =>
                    rw [hb, hc] at h
                    exact ih sb sc r (ih s b sb hs hfb hb) (ih s c sc hs hfc hc) h
            | .atom _ => simp [evalFBy] at h
        | 3 =>
            simp only [evalFBy] at h
            cases ht : evalFBy q fuel s tail with
            | none => rw [ht] at h; simp at h
            | some v =>
              rw [ht] at h; simp only [Option.map_some, Option.some.injEq] at h
              subst h; exact wut_boundedBy hq v
        | 4 =>
            simp only [evalFBy] at h
            cases ht : evalFBy q fuel s tail with
            | none => rw [ht] at h; simp at h
            | some v => rw [ht] at h; exact lusFBy_bounded (by omega) h
        | 5 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalFBy] at h
                cases hb : evalFBy q fuel s b with
                | none => rw [hb] at h; simp at h
                | some sb =>
                  cases hc : evalFBy q fuel s c with
                  | none => rw [hb, hc] at h; simp at h
                  | some sc =>
                    rw [hb, hc] at h; simp only [Option.some.injEq] at h; subst h
                    exact tis_boundedBy hq sb sc
            | .atom _ => simp [evalFBy] at h
        | 6 =>
            match tail with
            | .cell b (.cell c d) =>
                obtain ⟨hfb, hfc, hfd⟩ := hft
                simp only [evalFBy] at h
                cases hb : evalFBy q fuel s b with
                | none => rw [hb] at h; simp at h
                | some vb =>
                  rw [hb] at h
                  match vb, h with
                  | .atom 0, h => exact ih s c r hs hfc h
                  | .atom 1, h => exact ih s d r hs hfd h
                  | .atom (n+2), h => simp at h
                  | .cell _ _, h => simp at h
            | .cell b (.atom _) => simp [evalFBy] at h
            | .atom _ => simp [evalFBy] at h
        | 7 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalFBy] at h
                cases hb : evalFBy q fuel s b with
                | none => rw [hb] at h; simp at h
                | some sb =>
                  rw [hb] at h
                  exact ih sb c r (ih s b sb hs hfb hb) hfc h
            | .atom _ => simp [evalFBy] at h
        | 8 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalFBy] at h
                cases hb : evalFBy q fuel s b with
                | none => rw [hb] at h; simp at h
                | some sb =>
                  rw [hb] at h
                  exact ih (.cell sb s) c r ⟨ih s b sb hs hfb hb, hs⟩ hfc h
            | .atom _ => simp [evalFBy] at h
        | 9 =>
            match tail with
            | .cell (.atom ax) c =>
                obtain ⟨-, hfc⟩ := hft
                simp only [evalFBy] at h
                cases hc : evalFBy q fuel s c with
                | none => rw [hc] at h; simp at h
                | some core =>
                  rw [hc] at h; dsimp only at h
                  cases harm : slot ax core with
                  | none => rw [harm] at h; simp at h
                  | some arm =>
                    rw [harm] at h; dsimp only at h
                    have hBcore := ih s c core hs hfc hc
                    exact ih core arm r hBcore (slot_boundedBy q ax core hBcore harm) h
            | .cell (.cell _ _) _ => simp [evalFBy] at h
            | .atom _ => simp [evalFBy] at h
        | 10 =>
            match tail with
            | .cell (.cell (.atom ax) c) d =>
                obtain ⟨⟨-, hfc⟩, hfd⟩ := hft
                simp only [evalFBy] at h
                cases hc : evalFBy q fuel s c with
                | none => rw [hc] at h; simp at h
                | some new =>
                  cases hd : evalFBy q fuel s d with
                  | none => rw [hc, hd] at h; simp at h
                  | some old =>
                    rw [hc, hd] at h
                    exact edit_boundedBy q ax new old (ih s c new hs hfc hc)
                      (ih s d old hs hfd hd) h
            | .cell (.cell (.cell _ _) _) _ => simp [evalFBy] at h
            | .cell (.atom _) _ => simp [evalFBy] at h
            | .atom _ => simp [evalFBy] at h
        | 11 =>
            match tail with
            | .cell (.cell hd clue) body =>
                obtain ⟨⟨-, -⟩, hfbody⟩ := hft
                simp only [evalFBy] at h
                cases hcl : evalFBy q fuel s clue with
                | none => rw [hcl] at h; simp at h
                | some vc => rw [hcl] at h; exact ih s body r hs hfbody h
            | .cell (.atom hint) body =>
                obtain ⟨-, hfbody⟩ := hft
                simp only [evalFBy] at h
                exact ih s body r hs hfbody h
            | .atom _ => simp [evalFBy] at h
        | (n+12) => simp [evalFBy] at h

/-! ## `ZMod q` representative-level injectivity

On `q`-bounded nouns the structural Nock equality used by OP₅ (`main.tex:1525`) coincides with
field equality in `ZMod q`: distinct canonical residues `< q` stay distinct.  Primality is not
needed for this representative-level fact. -/

/-- The `Nat` cast into `ZMod q` is injective on canonical representatives `[0,q)`. -/
theorem zmod_natCast_inj_of_lt {q m n : ℕ} (hm : m < q) (hn : n < q)
    (h : (m : ZMod q) = (n : ZMod q)) : m = n := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt hm, ZMod.val_natCast_of_lt hn] at this

end Nock.FieldEmbedding
