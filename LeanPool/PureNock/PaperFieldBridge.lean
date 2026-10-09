/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import LeanPool.PureNock.PaperReferenceMod
public import LeanPool.PureNock.PureComplete

/-!
# Paper-fragment ↔ finite-field bridge

`FieldEmbedding.agreeBy` (`Nock/ModularEval.lean`) identifies the *full* evaluators — `evalN`
(unbounded Nat increment) and `evalFBy q` (modular increment, `main.tex:1531–1534`) — conditional
on a successful run of the *guarded* evaluator `evalGBy q`, which crashes rather than letting any
increment reach `q`.  But all three of those evaluators include OP₁₁, while

* the small-step machine `Verb.runProgram` and its unconditional adequacy partner `evalPaper`
  (`Verb.runProgram_adequate_complete`), and
* the strict modular paper oracle `evalPaperMod q` (`Nock/PaperReferenceMod.lean`)

live in the paper's OP₀–OP₁₀ fragment (`main.tex:1054–1076`).

This module supplies the guarded paper-fragment evaluator `evalGPaper q` (`evalPaperMod q` with the
crashing increment `lusGBy q`) and threads one conditional through every layer, ending in
`paper_field_bridge`: on `q`-bounded inputs, a successful guarded fragment run makes the small-step
machine, `evalPaper`, `evalPaperMod q`, `evalFBy q`, and `evalN` all return the *same* noun, itself
`q`-bounded.

The conditional is no-overflow; injectivity is the payoff, not a second hypothesis: the `BoundedBy q`
conclusion makes the leaf cast `ℕ → ZMod q` injective (`embBy_inj_of_boundedBy`), so the structural
noun equality used by OP₅ (`main.tex:1525`) *is* field equality on bridged results.  Primality is
never used — `1 < q` and `NeZero q` suffice — so nothing here declares or pulls a project axiom.

The conditional is STRICTLY STRONGER than the paper's own total modular language: `evalGPaper q`
crashes where the paper's modular OP₄ merely wraps, so this identifies the five evaluators on the
*no-overflow sublanguage* only (`evalGPaper_fails_where_evalPaperMod_wraps`).
-/

@[expose] public section

namespace Nock

open Noun

/-! ## The guarded paper-fragment evaluator -/

-- main.tex:1054-1076 (fragment OP₀..OP₁₀ + `cons`), main.tex:1531-1534 (the OP₄ increment)
/-- `*[subject formula]`, fuel-indexed, **guarded paper fragment**: the paper's OP₀–OP₁₀ fragment
    with the OP₄ increment `lusGBy q`, which *crashes* rather than reaching an atom `≥ q`.

    `evalGPaper q fuel s f = some r` is therefore exactly the statement "this paper-fragment
    computation runs without any **OP₄** modular wrap at `q`" — the honest no-overflow side
    condition, in the fragment where `Verb.runProgram` and `evalPaperMod q` live.  (OP₄ is the only
    opcode these evaluators reduce with a modular increment; see the OP₆ note below.)

    OP₆ NOTE.  These modular evaluators reduce OP₆ by the standard Nock loobean if/else on the
    condition (`main.tex:1067` computes the same thing over ℕ via an increment macro).  Over ℕ they
    coincide (`runProgram_adequate_complete`), and under the bridge's `BoundedBy q` hypotheses for
    `q ≥ 4` every intermediate atom is `< q` so no OP₆ increment could wrap either; hence the guard
    is complete on the bridge's domain.  The paper's *literal* OP₆ macro, whose two increments are
    modular, diverges from the if/else only for an unbounded (`≥ q`) or small-modulus (`q ∈ {2,3}`)
    condition — inputs outside the bounded domain — so `paper_field_bridge` is unaffected at
    `q ≥ 4`.  This is a representation choice (if/else vs increment-macro), documented, not an
    OP₄-style wrap. -/
def evalGPaper (q : Nat) : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | fuel + 1, subj, .cell (.cell b c) d =>
      match evalGPaper q fuel subj (.cell b c), evalGPaper q fuel subj d with
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
             match evalGPaper q fuel subj b, evalGPaper q fuel subj c with
             | some sb, some sc => evalGPaper q fuel sb sc
             | _, _ => none
           | _ => none
    | 3 => (evalGPaper q fuel subj tail).map wut
    | 4 => (evalGPaper q fuel subj tail).bind (FieldEmbedding.lusGBy q)
    | 5 => match tail with
           | .cell b c =>
             match evalGPaper q fuel subj b, evalGPaper q fuel subj c with
             | some sb, some sc => some (tis sb sc)
             | _, _ => none
           | _ => none
    | 6 => match tail with
           | .cell b (.cell c d) =>
             match evalGPaper q fuel subj b with
             | some (.atom 0) => evalGPaper q fuel subj c
             | some (.atom 1) => evalGPaper q fuel subj d
             | _ => none
           | _ => none
    | 7 => match tail with
           | .cell b c =>
             match evalGPaper q fuel subj b with
             | some sb => evalGPaper q fuel sb c
             | none => none
           | _ => none
    | 8 => match tail with
           | .cell b c =>
             match evalGPaper q fuel subj b with
             | some sb => evalGPaper q fuel (.cell sb subj) c
             | none => none
           | _ => none
    | 9 => match tail with
           | .cell (.atom ax) c =>
             match evalGPaper q fuel subj c with
             | some core =>
               match slot ax core with
               | some arm => evalGPaper q fuel core arm
               | none => none
             | none => none
           | _ => none
    | 10 => match tail with
            | .cell (.cell (.atom ax) c) d =>
              match evalGPaper q fuel subj c, evalGPaper q fuel subj d with
              | some new, some old => edit ax new old
              | _, _ => none
            | _ => none
    | _ => none                          -- op ≥ 11 (incl. OP₁₁ hints) ⇒ crash (paper fragment)

/-! ## The increment agrees under the guard

The guard is the only place the three fragment evaluators can differ: a successful `lusGBy q`
pins `n + 1 < q`, and there the unbounded increment `Noun.lus` and the modular increment
`lusFBy q` produce the same atom. -/

/-- A successful guarded increment is the unbounded increment (`main.tex:1531–1534` vs `Noun.lus`). -/
theorem lusGBy_le_lus {q : Nat} {x m : Noun}
    (h : FieldEmbedding.lusGBy q x = some m) : Noun.lus x = some m := by
  cases x with
  | atom n =>
      by_cases hlt : n + 1 < q
      · simp only [FieldEmbedding.lusGBy, if_pos hlt, Option.some.injEq] at h
        simp [Noun.lus, ← h]
      · simp [FieldEmbedding.lusGBy, hlt] at h
  | cell _ _ => simp [FieldEmbedding.lusGBy] at h

/-- A successful guarded increment is the paper's modular increment (`main.tex:1531–1534`). -/
theorem lusGBy_le_lusFBy {q : Nat} {x m : Noun}
    (h : FieldEmbedding.lusGBy q x = some m) : FieldEmbedding.lusFBy q x = some m := by
  cases x with
  | atom n =>
      by_cases hlt : n + 1 < q
      · simp only [FieldEmbedding.lusGBy, if_pos hlt, Option.some.injEq] at h
        simp [FieldEmbedding.lusFBy, ← h, Nat.mod_eq_of_lt hlt]
      · simp [FieldEmbedding.lusGBy, hlt] at h
  | cell _ _ => simp [FieldEmbedding.lusGBy] at h

/-! ## The three refinements out of the guarded fragment -/

/-- **`evalGPaper q` refines `evalGBy q`.**  The guarded fragment run is a guarded full run with
    the same value; they differ only where `evalGBy` fires OP₁₁, which the fragment crashes on.
    This is what makes `FieldEmbedding.agreeBy` reusable inside the fragment. -/
theorem evalGPaper_le_evalGBy {q n : Nat} {s form r : Noun}
    (h : evalGPaper q n s form = some r) : FieldEmbedding.evalGBy q n s form = some r := by
  induction n, s, form using evalGPaper.induct q generalizing r <;>
    simp_all only [evalGPaper, FieldEmbedding.evalGBy, Option.map_eq_some_iff,
      Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq] <;>
    grind

/-- **`evalGPaper q` refines `evalPaper`.**  Under the guard the fragment's modular-range OP₄ and
    the unbounded Nat OP₄ coincide, so a successful guarded run is a `evalPaper` run with the same
    value — the entry point into the unconditional `runProgram ⟺ evalPaper` adequacy. -/
theorem evalGPaper_le_evalPaper {q n : Nat} {s form r : Noun}
    (h : evalGPaper q n s form = some r) : evalPaper n s form = some r := by
  induction n, s, form using evalGPaper.induct q generalizing r <;>
    simp_all only [evalGPaper, evalPaper, Option.map_eq_some_iff,
      Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq] <;>
    grind [lusGBy_le_lus]

/-- **`evalGPaper q` refines `evalPaperMod q`.**  A successful guarded run is a strict-paper
    modular run with the same value: the guard rules out the wrap that is the only difference. -/
theorem evalGPaper_le_evalPaperMod {q n : Nat} {s form r : Noun}
    (h : evalGPaper q n s form = some r) : evalPaperMod q n s form = some r := by
  induction n, s, form using evalGPaper.induct q generalizing r <;>
    simp_all only [evalGPaper, evalPaperMod, Option.map_eq_some_iff,
      Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq] <;>
    grind [lusGBy_le_lusFBy]

/-! ## The injectivity carry

`BoundedBy q` is precisely the condition under which the leaf cast `ℕ → ZMod q` is injective, so on
bridged results the *structural* noun equality used by OP₅ (`main.tex:1525`) coincides with equality
of field images.  Injectivity is thus a consequence of the bridge's conclusion, not an extra
hypothesis.  These do not use any project axiom. -/

namespace FieldEmbedding

-- main.tex:345-348
/-- Field nouns at a supplied modulus: proper binary trees with leaves in `ZMod q`. -/
inductive FNounBy (q : Nat) where
  | atom : ZMod q → FNounBy q
  | cell : FNounBy q → FNounBy q → FNounBy q

-- main.tex:345
/-- The leaf map `n ↦ (n : ZMod q)`, structural on cells. -/
def embBy (q : Nat) : Noun → FNounBy q
  | .atom n   => .atom (n : ZMod q)
  | .cell l r => .cell (embBy q l) (embBy q r)

@[simp] theorem embBy_atom {q n : Nat} : embBy q (.atom n) = .atom (n : ZMod q) := rfl

/-- **`embBy q` is injective on `q`-bounded nouns.**  Distinct canonical residues `< q` stay
    distinct in `ZMod q`, so structural Nock equality is field equality there (`main.tex:1525`). -/
theorem embBy_inj_of_boundedBy {q : Nat} [NeZero q] :
    ∀ {a b : Noun}, BoundedBy q a → BoundedBy q b → embBy q a = embBy q b → a = b := by
  intro a
  induction a with
  | atom m =>
      intro b hm hb h
      cases b with
      | atom n =>
          simp only [embBy, FNounBy.atom.injEq] at h
          rw [zmod_natCast_inj_of_lt hm hb h]
      | cell _ _ => simp [embBy] at h
  | cell la ra ihl ihr =>
      intro b ha hb h
      cases b with
      | atom _ => simp [embBy] at h
      | cell lb rb =>
          simp only [embBy, FNounBy.cell.injEq] at h
          rw [ihl ha.1 hb.1 h.1, ihr ha.2 hb.2 h.2]

end FieldEmbedding

/-! ## The capstone bridge -/

/-- **Paper ↔ finite-field bridge.**  On `q`-bounded inputs (every atom is a canonical residue
    `< q`), a successful *guarded* paper-fragment run makes all five formalizations of the paper's
    evaluation agree on one noun, which is again `q`-bounded:

    * the small-step machine `Verb.runProgram` (`main.tex:1052–1083`),
    * the Nat paper oracle `evalPaper`,
    * the strict modular paper oracle `evalPaperMod q` (`main.tex:1531–1534`),
    * the full modular evaluator `FieldEmbedding.evalFBy q`, and
    * the Nat reference `evalN`.

    The single hypothesis `evalGPaper q fuel s f = some r` is no-overflow: it is discharged by
    *running* the guarded evaluator, not assumed.  The `BoundedBy q r` conclusion then delivers
    leaf-cast injectivity for free (`bridge_reflects_field_equality`). -/
theorem paper_field_bridge (q : Nat) (hq : 1 < q) {fuel : Nat} {s f r : Noun}
    (hs : FieldEmbedding.BoundedBy q s) (hf : FieldEmbedding.BoundedBy q f)
    (hG : evalGPaper q fuel s f = some r) :
    (∃ n, Verb.runProgram n s f = some r) ∧
      evalPaper fuel s f = some r ∧
      evalPaperMod q fuel s f = some r ∧
      FieldEmbedding.evalFBy q fuel s f = some r ∧
      evalN fuel s f = some r ∧
      FieldEmbedding.BoundedBy q r := by
  have hP : evalPaper fuel s f = some r := evalGPaper_le_evalPaper hG
  have hM : evalPaperMod q fuel s f = some r := evalGPaper_le_evalPaperMod hG
  have hB : FieldEmbedding.BoundedBy q r :=
    (FieldEmbedding.agreeBy q hq fuel s f r hs hf (evalGPaper_le_evalGBy hG)).2.2
  exact ⟨(Verb.runProgram_adequate_complete s f r).2 ⟨fuel, hP⟩, hP, hM,
    evalPaperMod_le_evalFBy hM, evalPaper_le_evalN hP, hB⟩

/-- The bridge's small-step half in the form the machine consumes. -/
theorem runProgram_of_evalGPaper {q fuel : Nat} {s f r : Noun}
    (hG : evalGPaper q fuel s f = some r) : ∃ n, Verb.runProgram n s f = some r :=
  (Verb.runProgram_adequate_complete s f r).2 ⟨fuel, evalGPaper_le_evalPaper hG⟩

/-- The bridge's field half: a successful guarded fragment run is a full modular run. -/
theorem evalFBy_of_evalGPaper {q fuel : Nat} {s f r : Noun}
    (hG : evalGPaper q fuel s f = some r) :
    FieldEmbedding.evalFBy q fuel s f = some r :=
  evalPaperMod_le_evalFBy (evalGPaper_le_evalPaperMod hG)

/-- **The bridge carries the equivalence through the field embedding.**  Two guarded fragment runs
    on `q`-bounded inputs whose results have the same field image have the *same result noun*: the
    no-overflow conditional yields boundedness, and boundedness yields injectivity. -/
theorem bridge_reflects_field_equality (q : Nat) [NeZero q] (hq : 1 < q)
    {fuel₁ fuel₂ : Nat} {s₁ f₁ s₂ f₂ r₁ r₂ : Noun}
    (hs₁ : FieldEmbedding.BoundedBy q s₁) (hf₁ : FieldEmbedding.BoundedBy q f₁)
    (hs₂ : FieldEmbedding.BoundedBy q s₂) (hf₂ : FieldEmbedding.BoundedBy q f₂)
    (hG₁ : evalGPaper q fuel₁ s₁ f₁ = some r₁)
    (hG₂ : evalGPaper q fuel₂ s₂ f₂ = some r₂)
    (himg : FieldEmbedding.embBy q r₁ = FieldEmbedding.embBy q r₂) : r₁ = r₂ :=
  FieldEmbedding.embBy_inj_of_boundedBy
    (paper_field_bridge q hq hs₁ hf₁ hG₁).2.2.2.2.2
    (paper_field_bridge q hq hs₂ hf₂ hG₂).2.2.2.2.2 himg

/-! ## Non-vacuity, and the guard cuts exactly at the wrap

The witnesses instantiate the full six-fold bridge conclusion at a genuine prime and at the paper's
own characteristic (`main.tex:158`), given as a *literal* modulus so no primality axiom is needed
(the bridge never uses primality). -/

/-- The Goldilocks modulus `p = 2^64 − 2^32 + 1` (`main.tex:158`), as a literal `Nat` constant.
    Used only to instantiate a bridge witness at the paper's own characteristic; primality is not
    assumed anywhere. -/
def goldilocksModulus : Nat := 2 ^ 64 - 2 ^ 32 + 1

theorem one_lt_goldilocksModulus : 1 < goldilocksModulus := by
  norm_num [goldilocksModulus]

/-- **Non-vacuity at a genuine prime.**  `*[0 [4 [1 3]]] = 4` at `q = 5`, where `ZMod q` really is a
    field, with the full six-fold bridge conclusion. -/
theorem bridge_nonvacuous_at_prime_5 :
    (∃ n, Verb.runProgram n (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4)) ∧
      evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3))) = some (.atom 4) ∧
      evalPaperMod 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) ∧
      FieldEmbedding.evalFBy 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) ∧
      evalN 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3))) = some (.atom 4) ∧
      FieldEmbedding.BoundedBy 5 (.atom 4) :=
  paper_field_bridge 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

-- main.tex:158
/-- **Non-vacuity at the paper's own characteristic** `goldilocksModulus = 2^64 − 2^32 + 1`.
    Uses the literal modulus; no primality axiom. -/
theorem bridge_nonvacuous_at_goldilocks :
    (∃ n, Verb.runProgram n (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42)))
        = some (.atom 43)) ∧
      evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42))) = some (.atom 43) ∧
      evalPaperMod goldilocksModulus 5 (.atom 0)
          (.cell (.atom 4) (.cell (.atom 1) (.atom 42))) = some (.atom 43) ∧
      FieldEmbedding.evalFBy goldilocksModulus 5 (.atom 0)
          (.cell (.atom 4) (.cell (.atom 1) (.atom 42))) = some (.atom 43) ∧
      evalN 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42))) = some (.atom 43) ∧
      FieldEmbedding.BoundedBy goldilocksModulus (.atom 43) :=
  paper_field_bridge goldilocksModulus one_lt_goldilocksModulus
    (by norm_num [goldilocksModulus]) (by norm_num [goldilocksModulus])
    (by have hgm : goldilocksModulus = 18446744069414584321 := by norm_num [goldilocksModulus]
        rw [hgm]; decide)

/-- **The guard rejects exactly the divergent computation.**  At the top residue `q−1 = 4` the
    strict modular oracle wraps to `0` while the unbounded oracle produces `5`
    (`evalPaperMod_ne_evalPaper_at_top`); the guarded fragment evaluator crashes there, so the
    bridge never claims agreement across the wrap. -/
theorem evalGPaper_fails_where_evalPaperMod_wraps :
    evalGPaper 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 4))) = none ∧
      evalPaperMod 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 4)))
        = some (.atom 0) ∧
      evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 4)))
        = some (.atom 5) := by
  refine ⟨by decide, by decide, by decide⟩

/-- One residue below the top the guard holds and all three fragment oracles agree. -/
theorem evalGPaper_succeeds_below_top :
    evalGPaper 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) ∧
      evalPaperMod 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) ∧
      evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) := by
  refine ⟨by decide, by decide, by decide⟩

end Nock
