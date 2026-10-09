/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import LeanPool.PureNock.PaperReference
public import LeanPool.PureNock.ModularEval

/-!
# Strict modular paper oracle

`evalPaperMod q`: the paper's OP₀–OP₁₀ fragment (`main.tex:1054–1076`) over
`Nat`-atom nouns, with the OP₄ increment taken **modulo `q`**, exactly as the paper
specifies `+(n) = (1+n) mod p` (`main.tex:1531–1534`).

It is the strict-language counterpart of `evalPaper`:

* `evalPaper`      = OP₀–OP₁₀ fragment with the *unbounded* Nat increment `n ↦ n+1`;
* `evalPaperMod q` = the same fragment with the *modular* increment `n ↦ (n+1) mod q`.

Two facts must not be conflated:

1. `evalPaperMod q` refines the full modular evaluator `FieldEmbedding.evalFBy q`
   (`evalPaperMod_le_evalFBy`): they agree on the whole OP₀–OP₁₀ fragment and differ only
   where `evalFBy` would fire OP₁₁, which the paper fragment crashes on.
2. `evalPaperMod q` is **not** `evalPaper`: at the top atom `q−1` the modular OP₄ wraps to
   `0` while the unbounded `evalPaper` produces `q` (`evalPaperMod_ne_evalPaper_at_top`).
   This is the compiled no-overflow distinction, not a claim that the two coincide.
-/

@[expose] public section

namespace Nock

open Noun

/-- `*[subject formula]`, fuel-indexed, **strict paper fragment** (OP₀–OP₁₀ + `cons`) with the
    paper's **modular** OP₄ increment `+(n) = (1+n) mod q` (`main.tex:1531–1534`).

    Identical to `FieldEmbedding.evalFBy q` except an OP₁₁ head (`op = 11`) is an unknown opcode
    and crashes (`none`), matching the paper's `opHeadOk` (`op < 11`) and the small-step machine
    `runProgram`. -/
def evalPaperMod (q : Nat) : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | fuel + 1, subj, .cell (.cell b c) d =>
      match evalPaperMod q fuel subj (.cell b c), evalPaperMod q fuel subj d with
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
             match evalPaperMod q fuel subj b, evalPaperMod q fuel subj c with
             | some sb, some sc => evalPaperMod q fuel sb sc
             | _, _ => none
           | _ => none
    | 3 => (evalPaperMod q fuel subj tail).map wut
    | 4 => (evalPaperMod q fuel subj tail).bind (FieldEmbedding.lusFBy q)
    | 5 => match tail with
           | .cell b c =>
             match evalPaperMod q fuel subj b, evalPaperMod q fuel subj c with
             | some sb, some sc => some (tis sb sc)
             | _, _ => none
           | _ => none
    | 6 => match tail with
           | .cell b (.cell c d) =>
             match evalPaperMod q fuel subj b with
             | some (.atom 0) => evalPaperMod q fuel subj c
             | some (.atom 1) => evalPaperMod q fuel subj d
             | _ => none
           | _ => none
    | 7 => match tail with
           | .cell b c =>
             match evalPaperMod q fuel subj b with
             | some sb => evalPaperMod q fuel sb c
             | none => none
           | _ => none
    | 8 => match tail with
           | .cell b c =>
             match evalPaperMod q fuel subj b with
             | some sb => evalPaperMod q fuel (.cell sb subj) c
             | none => none
           | _ => none
    | 9 => match tail with
           | .cell (.atom ax) c =>
             match evalPaperMod q fuel subj c with
             | some core =>
               match slot ax core with
               | some arm => evalPaperMod q fuel core arm
               | none => none
             | none => none
           | _ => none
    | 10 => match tail with
            | .cell (.cell (.atom ax) c) d =>
              match evalPaperMod q fuel subj c, evalPaperMod q fuel subj d with
              | some new, some old => edit ax new old
              | _, _ => none
            | _ => none
    | _ => none                          -- op ≥ 11 (incl. OP₁₁ hints) ⇒ crash (paper fragment)

/-- Convenience wrapper with a large fuel budget, for `#eval` sanity checks. -/
def evalPaperModTop (q : Nat) (subj formula : Noun) : Option Noun := evalPaperMod q 100000 subj formula

/-- **Fuel monotonicity (single step)** for `evalPaperMod`. -/
theorem evalPaperMod_succ {q n : Nat} {s form r : Noun}
    (h : evalPaperMod q n s form = some r) : evalPaperMod q (n + 1) s form = some r := by
  induction n, s, form using evalPaperMod.induct q generalizing r with
  | case11 fuel subj tail ih =>
      simp only [evalPaperMod, Option.map_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | case12 fuel subj tail ih =>
      simp only [evalPaperMod, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | _ =>
      simp_all [evalPaperMod]

/-- **Fuel monotonicity** for `evalPaperMod`. -/
theorem evalPaperMod_mono {q n m : Nat} {s form r : Noun}
    (hle : n ≤ m) (h : evalPaperMod q n s form = some r) : evalPaperMod q m s form = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact evalPaperMod_succ ih

/-- **`evalPaperMod q` refines `evalFBy q`.** Every strict-paper modular evaluation is a full
    modular evaluation with the same result: they differ only where `evalFBy` fires OP₁₁, which
    `evalPaperMod` crashes on. -/
theorem evalPaperMod_le_evalFBy {q n : Nat} {s form r : Noun}
    (h : evalPaperMod q n s form = some r) : FieldEmbedding.evalFBy q n s form = some r := by
  induction n, s, form using evalPaperMod.induct q generalizing r <;>
    simp_all only [evalPaperMod, FieldEmbedding.evalFBy, Option.map_eq_some_iff,
      Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq] <;>
    grind

-- main.tex:345–349, 1531–1534  (the strict modular oracle is a field-noun endomorphism)
/-- **`evalPaperMod q` preserves `q`-boundedness (unconditionally).**  On canonical field-noun
    inputs (`BoundedBy q`), every successful modular run returns a canonical field noun — the
    modular oracle maps `𝒩(𝔽)` into `𝒩(𝔽)`, handling the wrap exactly (no guard needed). -/
theorem evalPaperMod_boundedBy {q fuel : Nat} {s f r : Noun} (hq : 1 < q)
    (hs : FieldEmbedding.BoundedBy q s) (hf : FieldEmbedding.BoundedBy q f)
    (h : evalPaperMod q fuel s f = some r) : FieldEmbedding.BoundedBy q r :=
  FieldEmbedding.evalFBy_boundedBy hq fuel s f r hs hf (evalPaperMod_le_evalFBy h)

-- main.tex:1531–1534  (modular OP₄ ≠ unbounded increment at the top atom)
/-- **Modular OP₄ differs from the unbounded increment at the top atom.**  On `+(2)` at `q = 3`
    the modular oracle wraps (`(2+1) mod 3 = 0`) while the unbounded `evalPaper` produces `3`.
    This is the compiled distinction: the strict paper language is the modular one, not the
    unbounded `evalPaper`. -/
theorem evalPaperMod_ne_evalPaper_at_top :
    evalPaperMod 3 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 2)))
      ≠ evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 2))) := by
  decide

end Nock
