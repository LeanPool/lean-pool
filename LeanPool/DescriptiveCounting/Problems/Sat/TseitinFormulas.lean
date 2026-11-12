/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.Problems.Sat.Tseitin
import all LeanPool.DescriptiveCounting.Padding
import all LeanPool.DescriptiveCounting.Problems.Sat.Tseitin

/-!
# The Tseitin encoding of a first-order kernel: defining formulas

First-order counterpart of `DescriptiveComplexity.Problems.Sat.Tseitin`: formulas over
the ordered expansion `L.sum Language.order` defining, inside an input
structure, the clauses of the Tseitin ([Tseitin 1968][tseitin1968complexity])
encoding of a kernel formula and their literals –
`DescriptiveComplexity.Tseitin.isClauseF` mirroring
`DescriptiveComplexity.Tseitin.IsClauseSem` and `DescriptiveComplexity.Tseitin.litF` mirroring
`DescriptiveComplexity.Tseitin.LitSem`, with realization lemmas
(`DescriptiveComplexity.Tseitin.realize_isClauseF`, `DescriptiveComplexity.Tseitin.realize_litF`).

All builders are parameterized by maps `Fin D → γ` selecting the free
variables holding the clause and literal tuples, so that they can be
instantiated at the variable types of the defining formulas of an
interpretation (`Fin 1 × Fin D`, `Fin 2 × Fin D`). The order is used in a
single place: the formula `DescriptiveComplexity.botF` expressing that a
coordinate is a minimum, which pins down the canonical padding of tuples.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

namespace Tseitin

open Language Structure

section Builders

variable {L : Language.{0, 0}} {γ : Type} {D : ℕ}

variable {B : SOBlock}

/-- A term of the kernel, over the ordered expansion, its variables read from
the coordinates selected by `c`. -/
noncomputable def tTerm {m : ℕ} (h : m ≤ D)
    (t : (L.sum B.lang).Term (Empty ⊕ Fin m)) (c : Fin D → γ) :
    (L.sum Language.order).Term γ :=
  (LHom.sumInl.onTerm (stripTerm t)).relabel
    (Sum.elim isEmptyElim fun j => c (Fin.castLE h j))

/-- The equality atom of the kernel, as a formula over the ordered
expansion. -/
noncomputable def termEqF {m : ℕ} (h : m ≤ D)
    (t₁ t₂ : (L.sum B.lang).Term (Empty ⊕ Fin m)) (c : Fin D → γ) :
    (L.sum Language.order).Formula γ :=
  Term.equal (tTerm h t₁ c) (tTerm h t₂ c)

/-- An input-relation symbol, in the ordered expansion. -/
abbrev inRelSym {l : ℕ} (r : L.Relations l) : (L.sum Language.order).Relations l :=
  Sum.inl r

/-- An input-relation atom of the kernel, as a formula over the ordered
expansion. -/
noncomputable def relAtF {m l : ℕ} (h : m ≤ D) (r : L.Relations l)
    (ts : Fin l → (L.sum B.lang).Term (Empty ⊕ Fin m)) (c : Fin D → γ) :
    (L.sum Language.order).Formula γ :=
  Relations.formula (inRelSym r) fun k => tTerm h (ts k) c

/-- The tuple held by `x` is the canonically padded tuple of values of the
terms of a block-variable atom, as a formula. -/
noncomputable def atomLitF {m l : ℕ} (h : m ≤ D)
    (ts : Fin l → (L.sum B.lang).Term (Empty ⊕ Fin m)) (u x : Fin D → γ) :
    (L.sum Language.order).Formula γ :=
  canonF l x ⊓
    listInf ((List.finRange D).map fun (j : Fin D) =>
      if hj : (j : ℕ) < l then
        Term.equal (Term.var (x j)) (tTerm h (ts ⟨(j : ℕ), hj⟩) u)
      else ⊤)

end Builders

/-! ### Realization of the builders -/

section RealizeBuilders

variable {L : Language.{0, 0}} {γ : Type} {D : ℕ}
variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

variable {B : SOBlock}

private theorem realize_tTerm {m : ℕ} (h : m ≤ D)
    (t : (L.sum B.lang).Term (Empty ⊕ Fin m)) (c : Fin D → γ) :
    (tTerm h t c).realize v =
      (stripTerm t).realize (Sum.elim isEmptyElim fun j => v (c (Fin.castLE h j))) := by
  rw [tTerm, Term.realize_relabel, LHom.realize_onTerm]
  refine congrArg (fun g => Term.realize (M := A) g (stripTerm t)) (funext fun a => ?_)
  cases a with
  | inl e => exact isEmptyElim e
  | inr j => rfl

private theorem realize_termEqF {m : ℕ} (h : m ≤ D)
    (t₁ t₂ : (L.sum B.lang).Term (Empty ⊕ Fin m)) (c : Fin D → γ) :
    (termEqF h t₁ t₂ c).Realize v ↔
      eqGuard (A := A) t₁ t₂ fun j => v (c (Fin.castLE h j)) := by
  rw [termEqF, Formula.realize_equal, realize_tTerm, realize_tTerm, eqGuard]

private theorem realize_relAtF {m l : ℕ} (h : m ≤ D) (r : L.Relations l)
    (ts : Fin l → (L.sum B.lang).Term (Empty ⊕ Fin m)) (c : Fin D → γ) :
    (relAtF h r ts c).Realize v ↔
      relGuard (A := A) r ts fun j => v (c (Fin.castLE h j)) := by
  rw [relAtF, relGuard]
  simp only [Formula.realize_rel, realize_tTerm]
  exact Iff.rfl

private theorem realize_atomLitF {m l : ℕ} (h : m ≤ D)
    (ts : Fin l → (L.sum B.lang).Term (Empty ⊕ Fin m)) (u x : Fin D → γ) :
    (atomLitF h ts u x).Realize v ↔
      atomLit ts (fun j => v (u (Fin.castLE h j))) fun j => v (x j) := by
  rw [atomLitF, Formula.realize_inf, realize_canonF, realize_listInf, atomLit]
  refine and_congr Iff.rfl ?_
  constructor
  · intro hval j hj
    have := hval _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    rw [dite_eq_left hj] at this
    rwa [Formula.realize_equal, Term.realize_var, realize_tTerm] at this
  · intro hval ψ hψ
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
    split_ifs with hj
    · rw [Formula.realize_equal, Term.realize_var, realize_tTerm]
      exact hval j hj
    · exact Formula.realize_top.mpr trivial

end RealizeBuilders

/-! ### The clause-existence formulas -/

section ClauseFormulas

variable {L : Language.{0, 0}} {B : SOBlock} {γ : Type} {D : ℕ}

/-- The defining formula of clause existence, mirroring
`DescriptiveComplexity.Tseitin.IsClauseSem`: the clause tuple is read from the
coordinates selected by `c`. -/
noncomputable def isClauseF :
    ∀ {n : ℕ} (f : (L.sum B.lang).BoundedFormula Empty n), contextBound f ≤ D →
      ∀ {m : ℕ}, NodeAt f m → Fin 3 → (Fin D → γ) →
        (L.sum Language.order).Formula γ
  | n, .falsum, _, _, _, k, c => if k = 0 then canonF n c else ⊥
  | n, .equal t₁ t₂, h, _, _, k, c =>
      if k = 0 then canonF n c ⊓ termEqF ((le_contextBound _).trans h) t₁ t₂ c
      else if k = 1 then canonF n c ⊓ ∼(termEqF ((le_contextBound _).trans h) t₁ t₂ c)
      else ⊥
  | n, .rel R ts, h, _, _, k, c =>
      (match R with
       | Sum.inl r =>
           if k = 0 then canonF n c ⊓ relAtF ((le_contextBound _).trans h) r ts c
           else if k = 1 then canonF n c ⊓ ∼(relAtF ((le_contextBound _).trans h) r ts c)
           else ⊥
       | Sum.inr _ => if k = 0 ∨ k = 1 then canonF n c else ⊥)
  | n, .imp f₁ f₂, h, _, p, k, c =>
      (match p with
       | Sum.inl _ => canonF n c
       | Sum.inr (Sum.inl q) => isClauseF f₁ ((le_max_left _ _).trans h) q k c
       | Sum.inr (Sum.inr q) => isClauseF f₂ ((le_max_right _ _).trans h) q k c)
  | n, .all f, h, _, p, k, c =>
      (match p with
       | Sum.inl _ =>
           if k = 0 then canonF (n + 1) c else if k = 1 then canonF n c else ⊥
       | Sum.inr q => isClauseF f h q k c)

variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

private theorem realize_ite_bot (P : Prop) [Decidable P]
    (φ : (L.sum Language.order).Formula γ) :
    (if P then φ else ⊥).Realize v ↔ P ∧ φ.Realize v := by
  split_ifs with h
  · exact (and_iff_right h).symm
  · rw [Formula.realize_bot]
    exact iff_of_false id fun hc => h hc.1

/-- Realization of the clause-existence formulas. -/
theorem realize_isClauseF :
    ∀ {n : ℕ} (f : (L.sum B.lang).BoundedFormula Empty n) (hctx : contextBound f ≤ D)
      {m : ℕ} (p : NodeAt f m) (k : Fin 3) (c : Fin D → γ),
      (isClauseF f hctx p k c).Realize v ↔
        IsClauseSem f hctx p k fun j => v (c j)
  | n, .falsum, hctx, _, p, k, c => by
      obtain ⟨rfl⟩ := p
      change (if k = 0 then canonF n c else ⊥).Realize v ↔ _
      rw [realize_ite_bot, realize_canonF]
      exact Iff.rfl
  | n, .equal t₁ t₂, hctx, _, p, k, c => by
      obtain ⟨rfl⟩ := p
      by_cases hk : k = 0
      · subst hk
        change (canonF n c ⊓ termEqF ((le_contextBound _).trans hctx) t₁ t₂ c).Realize v ↔ _
        rw [Formula.realize_inf, realize_canonF, realize_termEqF]
        constructor
        · rintro ⟨hc, hg⟩
          exact ⟨hc, Or.inl ⟨rfl, hg⟩⟩
        · rintro ⟨hc, ⟨-, hg⟩ | ⟨h1, -⟩⟩
          · exact ⟨hc, hg⟩
          · exact absurd h1 (by decide)
      · by_cases hk1 : k = 1
        · subst hk1
          change (canonF n c ⊓
            ∼(termEqF ((le_contextBound _).trans hctx) t₁ t₂ c)).Realize v ↔ _
          rw [Formula.realize_inf, Formula.realize_not, realize_canonF,
            realize_termEqF]
          constructor
          · rintro ⟨hc, hg⟩
            exact ⟨hc, Or.inr ⟨rfl, hg⟩⟩
          · rintro ⟨hc, ⟨h0, -⟩ | ⟨-, hg⟩⟩
            · exact absurd h0 (by decide)
            · exact ⟨hc, hg⟩
        · change (if k = 0 then canonF n c ⊓ termEqF ((le_contextBound _).trans hctx) t₁ t₂ c
              else if k = 1 then
                canonF n c ⊓ ∼(termEqF ((le_contextBound _).trans hctx) t₁ t₂ c)
              else ⊥).Realize v ↔ _
          rw [ite_eq_right hk, ite_eq_right hk1, Formula.realize_bot]
          refine iff_of_false id ?_
          rintro ⟨-, ⟨h, -⟩ | ⟨h, -⟩⟩
          exacts [hk h, hk1 h]
  | n, .rel R ts, hctx, _, p, k, c => by
      obtain ⟨rfl⟩ := p
      cases R with
      | inl r =>
          by_cases hk : k = 0
          · subst hk
            change (canonF n c ⊓
              relAtF ((le_contextBound _).trans hctx) r ts c).Realize v ↔ _
            rw [Formula.realize_inf, realize_canonF, realize_relAtF]
            constructor
            · rintro ⟨hc, hg⟩
              exact ⟨hc, Or.inl ⟨rfl, hg⟩⟩
            · rintro ⟨hc, ⟨-, hg⟩ | ⟨h1, -⟩⟩
              · exact ⟨hc, hg⟩
              · exact absurd h1 (by decide)
          · by_cases hk1 : k = 1
            · subst hk1
              change (canonF n c ⊓
                ∼(relAtF ((le_contextBound _).trans hctx) r ts c)).Realize v ↔ _
              rw [Formula.realize_inf, Formula.realize_not, realize_canonF,
                realize_relAtF]
              constructor
              · rintro ⟨hc, hg⟩
                exact ⟨hc, Or.inr ⟨rfl, hg⟩⟩
              · rintro ⟨hc, ⟨h0, -⟩ | ⟨-, hg⟩⟩
                · exact absurd h0 (by decide)
                · exact ⟨hc, hg⟩
            · change (if k = 0 then
                  canonF n c ⊓ relAtF ((le_contextBound _).trans hctx) r ts c
                else if k = 1 then
                  canonF n c ⊓ ∼(relAtF ((le_contextBound _).trans hctx) r ts c)
                else ⊥).Realize v ↔ _
              rw [ite_eq_right hk, ite_eq_right hk1, Formula.realize_bot]
              refine iff_of_false id ?_
              rintro ⟨-, ⟨h, -⟩ | ⟨h, -⟩⟩
              exacts [hk h, hk1 h]
      | inr r =>
          change (if k = 0 ∨ k = 1 then canonF n c else ⊥).Realize v ↔ _
          rw [realize_ite_bot, realize_canonF]
          exact and_comm
  | n, .imp f₁ f₂, hctx, _, p, k, c => by
      obtain ⟨⟨rfl⟩⟩ | q | q := p
      · exact realize_canonF
      · exact realize_isClauseF f₁ ((le_max_left _ _).trans hctx) q k c
      · exact realize_isClauseF f₂ ((le_max_right _ _).trans hctx) q k c
  | n, .all f, hctx, _, p, k, c => by
      obtain ⟨⟨rfl⟩⟩ | q := p
      · by_cases hk : k = 0
        · subst hk
          change (canonF (n + 1) c).Realize v ↔ _
          rw [realize_canonF]
          constructor
          · intro hc
            exact Or.inl ⟨rfl, hc⟩
          · rintro (⟨-, hc⟩ | ⟨h1, -⟩)
            · exact hc
            · exact absurd h1 (by decide)
        · by_cases hk1 : k = 1
          · subst hk1
            change (canonF n c).Realize v ↔ _
            rw [realize_canonF]
            constructor
            · intro hc
              exact Or.inr ⟨rfl, hc⟩
            · rintro (⟨h0, -⟩ | ⟨-, hc⟩)
              · exact absurd h0 (by decide)
              · exact hc
          · change (if k = 0 then canonF (n + 1) c
                else if k = 1 then canonF n c else ⊥).Realize v ↔ _
            rw [ite_eq_right hk, ite_eq_right hk1, Formula.realize_bot]
            refine iff_of_false id ?_
            rintro (⟨h, -⟩ | ⟨h, -⟩)
            exacts [hk h, hk1 h]
      · exact realize_isClauseF f hctx q k c

/-! ### The literal formulas -/

open Classical in
/-- The defining formula of literal occurrence with sign `s`, mirroring
`DescriptiveComplexity.Tseitin.LitSem`: the clause tuple is read from the coordinates
selected by `u`, the literal tuple from those selected by `x`. Root positions
of subformulas are recognized by `DescriptiveComplexity.Tseitin.isRootB`. -/
noncomputable def litF (s : Bool) :
    ∀ {n : ℕ} (f : (L.sum B.lang).BoundedFormula Empty n), contextBound f ≤ D →
      ∀ {m : ℕ}, NodeAt f m → Fin 3 → (B.ι ⊕ Σ m', NodeAt f m') →
        (Fin D → γ) → (Fin D → γ) → (L.sum Language.order).Formula γ
  | _, .falsum, _, _, _, k, vt, u, x =>
      (match vt with
       | Sum.inr _ => if s = false ∧ k = 0 then eqTupF u x else ⊥
       | Sum.inl _ => ⊥)
  | _, .equal _ _, _, _, _, k, vt, u, x =>
      (match vt with
       | Sum.inr _ =>
           if (s = true ∧ k = 0) ∨ (s = false ∧ k = 1) then eqTupF u x else ⊥
       | Sum.inl _ => ⊥)
  | _, .rel R ts, h, _, _, k, vt, u, x =>
      (match R with
       | Sum.inl _ =>
           (match vt with
            | Sum.inr _ =>
                if (s = true ∧ k = 0) ∨ (s = false ∧ k = 1) then eqTupF u x else ⊥
            | Sum.inl _ => ⊥)
       | Sum.inr r =>
           (match vt with
            | Sum.inr _ =>
                if (s = false ∧ k = 0) ∨ (s = true ∧ k = 1) then eqTupF u x else ⊥
            | Sum.inl i =>
                if i = r.1 ∧ ((s = true ∧ k = 0) ∨ (s = false ∧ k = 1)) then
                  atomLitF ((le_contextBound _).trans h) ts u x
                else ⊥))
  | _, .imp f₁ f₂, h, _, p, k, vt, u, x =>
      (match p with
       | Sum.inl _ =>
           (match vt with
            | Sum.inl _ => ⊥
            | Sum.inr ⟨_, Sum.inl _⟩ =>
                if (s = false ∧ k = 0) ∨ (s = true ∧ (k = 1 ∨ k = 2)) then
                  eqTupF u x
                else ⊥
            | Sum.inr ⟨_, Sum.inr (Sum.inl q')⟩ =>
                if isRootB f₁ q' ∧ ((s = false ∧ k = 0) ∨ (s = true ∧ k = 1)) then
                  eqTupF u x
                else ⊥
            | Sum.inr ⟨_, Sum.inr (Sum.inr q')⟩ =>
                if isRootB f₂ q' ∧ ((s = true ∧ k = 0) ∨ (s = false ∧ k = 2)) then
                  eqTupF u x
                else ⊥)
       | Sum.inr (Sum.inl q) =>
           (match vt with
            | Sum.inl i => litF s f₁ ((le_max_left _ _).trans h) q k (Sum.inl i) u x
            | Sum.inr ⟨m', Sum.inr (Sum.inl q')⟩ =>
                litF s f₁ ((le_max_left _ _).trans h) q k (Sum.inr ⟨m', q'⟩) u x
            | _ => ⊥)
       | Sum.inr (Sum.inr q) =>
           (match vt with
            | Sum.inl i => litF s f₂ ((le_max_right _ _).trans h) q k (Sum.inl i) u x
            | Sum.inr ⟨m', Sum.inr (Sum.inr q')⟩ =>
                litF s f₂ ((le_max_right _ _).trans h) q k (Sum.inr ⟨m', q'⟩) u x
            | _ => ⊥))
  | n, .all f, h, _, p, k, vt, u, x =>
      (match p with
       | Sum.inl _ =>
           (match vt with
            | Sum.inl _ => ⊥
            | Sum.inr ⟨_, Sum.inl _⟩ =>
                if k = 0 ∧ s = false then agreeF n u x ⊓ canonF n x
                else if k = 1 ∧ s = true then eqTupF u x
                else ⊥
            | Sum.inr ⟨_, Sum.inr q'⟩ =>
                if isRootB f q' then
                  if k = 0 ∧ s = true then eqTupF u x
                  else if k = 1 ∧ s = false then agreeF n u x ⊓ canonF (n + 1) x
                  else ⊥
                else ⊥)
       | Sum.inr q =>
           (match vt with
            | Sum.inl i => litF s f h q k (Sum.inl i) u x
            | Sum.inr ⟨m', Sum.inr q'⟩ => litF s f h q k (Sum.inr ⟨m', q'⟩) u x
            | _ => ⊥))

section RealizeLit

variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

/-- Realization of the literal formulas. -/
theorem realize_litF (s : Bool) :
    ∀ {n : ℕ} (f : (L.sum B.lang).BoundedFormula Empty n) (hctx : contextBound f ≤ D)
      {m : ℕ} (p : NodeAt f m) (k : Fin 3) (vt : B.ι ⊕ Σ m', NodeAt f m')
      (u x : Fin D → γ),
      (litF s f hctx p k vt u x).Realize v ↔
        LitSem s f hctx p k (fun j => v (u j)) vt fun j => v (x j)
  | n, .falsum, hctx, _, p, k, vt, u, x => by
      classical
      obtain ⟨rfl⟩ := p
      rcases vt with i | ⟨m', q⟩
      · refine iff_of_false (id : ¬(⊥ : (L.sum Language.order).Formula γ).Realize v) ?_
        rintro ⟨-, -, h, -⟩
        exact absurd h (by rintro ⟨⟩)
      · obtain ⟨rfl⟩ := q
        change (if s = false ∧ k = 0 then eqTupF u x else ⊥).Realize v ↔ _
        rw [realize_ite_bot, realize_eqTupF]
        constructor
        · rintro ⟨⟨hs, hk⟩, he⟩
          exact ⟨hs, hk, rfl, he⟩
        · rintro ⟨hs, hk, -, he⟩
          exact ⟨⟨hs, hk⟩, he⟩
  | n, .equal t₁ t₂, hctx, _, p, k, vt, u, x => by
      classical
      obtain ⟨rfl⟩ := p
      rcases vt with i | ⟨m', q⟩
      · refine iff_of_false (id : ¬(⊥ : (L.sum Language.order).Formula γ).Realize v) ?_
        rintro ⟨h, -⟩
        exact absurd h (by rintro ⟨⟩)
      · obtain ⟨rfl⟩ := q
        change (if (s = true ∧ k = 0) ∨ (s = false ∧ k = 1) then eqTupF u x
          else ⊥).Realize v ↔ _
        rw [realize_ite_bot, realize_eqTupF]
        constructor
        · rintro ⟨hsk, he⟩
          exact ⟨rfl, he, hsk⟩
        · rintro ⟨-, he, hsk⟩
          exact ⟨hsk, he⟩
  | n, .rel R ts, hctx, _, p, k, vt, u, x => by
      classical
      obtain ⟨rfl⟩ := p
      cases R with
      | inl r =>
          rcases vt with i | ⟨m', q⟩
          · refine iff_of_false
              (id : ¬(⊥ : (L.sum Language.order).Formula γ).Realize v) ?_
            rintro ⟨h, -⟩
            exact absurd h (by rintro ⟨⟩)
          · obtain ⟨rfl⟩ := q
            change (if (s = true ∧ k = 0) ∨ (s = false ∧ k = 1) then eqTupF u x
              else ⊥).Realize v ↔ _
            rw [realize_ite_bot, realize_eqTupF]
            constructor
            · rintro ⟨hsk, he⟩
              exact ⟨rfl, he, hsk⟩
            · rintro ⟨-, he, hsk⟩
              exact ⟨hsk, he⟩
      | inr r =>
          rcases vt with i | ⟨m', q⟩
          · change (if i = r.1 ∧ ((s = true ∧ k = 0) ∨ (s = false ∧ k = 1)) then
                atomLitF ((le_contextBound _).trans hctx) ts u x
              else ⊥).Realize v ↔ _
            rw [realize_ite_bot, realize_atomLitF]
            constructor
            · rintro ⟨⟨rfl, hsk⟩, hal⟩
              exact Or.inr ⟨rfl, hal, hsk⟩
            · rintro (⟨h, -⟩ | ⟨h, hal, hsk⟩)
              · exact absurd h (by rintro ⟨⟩)
              · obtain rfl : i = r.1 := Sum.inl_injective h
                exact ⟨⟨rfl, hsk⟩, hal⟩
          · obtain ⟨rfl⟩ := q
            change (if (s = false ∧ k = 0) ∨ (s = true ∧ k = 1) then eqTupF u x
              else ⊥).Realize v ↔ _
            rw [realize_ite_bot, realize_eqTupF]
            constructor
            · rintro ⟨hsk, he⟩
              exact Or.inl ⟨rfl, he, hsk⟩
            · rintro (⟨-, he, hsk⟩ | ⟨h, -⟩)
              · exact ⟨hsk, he⟩
              · exact absurd h (by rintro ⟨⟩)
  | n, .imp f₁ f₂, hctx, _, p, k, vt, u, x => by
      classical
      obtain ⟨⟨rfl⟩⟩ | q | q := p
      · -- root clauses
        rcases vt with i | ⟨m', ⟨⟨hq⟩⟩ | q' | q'⟩
        · refine iff_of_false
            (id : ¬(⊥ : (L.sum Language.order).Formula γ).Realize v) ?_
          rintro ⟨-, ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩⟩ <;> exact absurd h (by rintro ⟨⟩)
        · obtain rfl := hq
          change (if (s = false ∧ k = 0) ∨ (s = true ∧ (k = 1 ∨ k = 2)) then
              eqTupF u x else ⊥).Realize v ↔ _
          rw [realize_ite_bot, realize_eqTupF]
          constructor
          · rintro ⟨hsk, he⟩
            exact ⟨he, Or.inl ⟨rfl, hsk⟩⟩
          · rintro ⟨he, ⟨-, hsk⟩ | ⟨h, -⟩ | ⟨h, -⟩⟩
            · exact ⟨hsk, he⟩
            · have h' := Sum.inr_injective h
              injection h' with h1 h2
              exact absurd h2 (by rintro ⟨⟩)
            · have h' := Sum.inr_injective h
              injection h' with h1 h2
              exact absurd h2 (by rintro ⟨⟩)
        · have hsig := sigma_map_eq_iff
            (fun m (q : NodeAt f₁ m) => (Sum.inr (Sum.inl q) : NodeAt (f₁.imp f₂) m))
            (fun m a b h => Sum.inl_injective (Sum.inr_injective h)) q' (rootAt f₁)
          have hroot : (Sum.inr ⟨m', Sum.inr (Sum.inl q')⟩ :
              B.ι ⊕ Σ m'', NodeAt (f₁.imp f₂) m'') =
                Sum.inr ⟨n, Sum.inr (Sum.inl (rootAt f₁))⟩ ↔ isRootB f₁ q' = true :=
            ⟨fun h => (isRootB_iff f₁ q').mpr (hsig.mp (Sum.inr_injective h)),
             fun h => congrArg Sum.inr (hsig.mpr ((isRootB_iff f₁ q').mp h))⟩
          change (if isRootB f₁ q' ∧ ((s = false ∧ k = 0) ∨ (s = true ∧ k = 1)) then
              eqTupF u x else ⊥).Realize v ↔ _
          rw [realize_ite_bot, realize_eqTupF]
          constructor
          · rintro ⟨⟨hr, hsk⟩, he⟩
            exact ⟨he, Or.inr (Or.inl ⟨hroot.mpr hr, hsk⟩)⟩
          · rintro ⟨he, ⟨h, -⟩ | ⟨h, hsk⟩ | ⟨h, -⟩⟩
            · have h' := Sum.inr_injective h
              injection h' with h1 h2
              subst h1
              exact absurd (eq_of_heq h2) (by rintro ⟨⟩)
            · exact ⟨⟨hroot.mp h, hsk⟩, he⟩
            · have h' := Sum.inr_injective h
              injection h' with h1 h2
              subst h1
              have h3 := eq_of_heq h2
              exact absurd (Sum.inr_injective h3) (by rintro ⟨⟩)
        · have hsig := sigma_map_eq_iff
            (fun m (q : NodeAt f₂ m) => (Sum.inr (Sum.inr q) : NodeAt (f₁.imp f₂) m))
            (fun m a b h => Sum.inr_injective (Sum.inr_injective h)) q' (rootAt f₂)
          have hroot : (Sum.inr ⟨m', Sum.inr (Sum.inr q')⟩ :
              B.ι ⊕ Σ m'', NodeAt (f₁.imp f₂) m'') =
                Sum.inr ⟨n, Sum.inr (Sum.inr (rootAt f₂))⟩ ↔ isRootB f₂ q' = true :=
            ⟨fun h => (isRootB_iff f₂ q').mpr (hsig.mp (Sum.inr_injective h)),
             fun h => congrArg Sum.inr (hsig.mpr ((isRootB_iff f₂ q').mp h))⟩
          change (if isRootB f₂ q' ∧ ((s = true ∧ k = 0) ∨ (s = false ∧ k = 2)) then
              eqTupF u x else ⊥).Realize v ↔ _
          rw [realize_ite_bot, realize_eqTupF]
          constructor
          · rintro ⟨⟨hr, hsk⟩, he⟩
            exact ⟨he, Or.inr (Or.inr ⟨hroot.mpr hr, hsk⟩)⟩
          · rintro ⟨he, ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, hsk⟩⟩
            · have h' := Sum.inr_injective h
              injection h' with h1 h2
              subst h1
              exact absurd (eq_of_heq h2) (by rintro ⟨⟩)
            · have h' := Sum.inr_injective h
              injection h' with h1 h2
              subst h1
              have h3 := eq_of_heq h2
              exact absurd (Sum.inr_injective h3) (by rintro ⟨⟩)
            · exact ⟨⟨hroot.mp h, hsk⟩, he⟩
      · -- left subtree
        rcases vt with i | ⟨m', ⟨-⟩ | q' | q'⟩
        · exact realize_litF s f₁ ((le_max_left _ _).trans hctx) q k (Sum.inl i) u x
        · exact Iff.rfl
        · exact realize_litF s f₁ ((le_max_left _ _).trans hctx) q k
            (Sum.inr ⟨m', q'⟩) u x
        · exact Iff.rfl
      · -- right subtree
        rcases vt with i | ⟨m', ⟨-⟩ | q' | q'⟩
        · exact realize_litF s f₂ ((le_max_right _ _).trans hctx) q k (Sum.inl i) u x
        · exact Iff.rfl
        · exact Iff.rfl
        · exact realize_litF s f₂ ((le_max_right _ _).trans hctx) q k
            (Sum.inr ⟨m', q'⟩) u x
  | n, .all f, hctx, _, p, k, vt, u, x => by
      classical
      obtain ⟨⟨rfl⟩⟩ | q := p
      · -- root clauses
        rcases vt with i | ⟨m', ⟨⟨hq⟩⟩ | q'⟩
        · refine iff_of_false
            (id : ¬(⊥ : (L.sum Language.order).Formula γ).Realize v) ?_
          rintro (⟨-, ⟨-, h, -⟩ | ⟨-, h, -⟩⟩ | ⟨-, ⟨-, h, -⟩ | ⟨-, h, -⟩⟩) <;>
            exact absurd h (by rintro ⟨⟩)
        · obtain rfl := hq
          change (if k = 0 ∧ s = false then agreeF n u x ⊓ canonF n x
            else if k = 1 ∧ s = true then eqTupF u x else ⊥).Realize v ↔ _
          split_ifs with h1 h2
          · obtain ⟨rfl, rfl⟩ := h1
            rw [Formula.realize_inf, realize_agreeF, realize_canonF]
            constructor
            · rintro ⟨hag, hc⟩
              exact Or.inl ⟨rfl, Or.inl ⟨rfl, rfl, hag, hc⟩⟩
            · rintro (⟨-, ⟨-, -, hag, hc⟩ | ⟨hs, -⟩⟩ | ⟨hk, -⟩)
              · exact ⟨hag, hc⟩
              · exact absurd hs (by simp)
              · exact absurd hk (by decide)
          · obtain ⟨rfl, rfl⟩ := h2
            rw [realize_eqTupF]
            constructor
            · intro he
              exact Or.inr ⟨rfl, Or.inl ⟨rfl, rfl, he⟩⟩
            · rintro (⟨hk, -⟩ | ⟨-, ⟨-, -, he⟩ | ⟨hs, -⟩⟩)
              · exact absurd hk (by decide)
              · exact he
              · exact absurd hs (by simp)
          · rw [Formula.realize_bot]
            refine iff_of_false id ?_
            rintro (⟨rfl, ⟨rfl, -⟩ | ⟨rfl, h, -⟩⟩ | ⟨rfl, ⟨rfl, -⟩ | ⟨rfl, h, -⟩⟩)
            · exact h1 ⟨rfl, rfl⟩
            · have h' := Sum.inr_injective h
              injection h' with hm h''
              exact absurd hm (by omega)
            · exact h2 ⟨rfl, rfl⟩
            · have h' := Sum.inr_injective h
              injection h' with hm h''
              exact absurd hm (by omega)
        · have hsig := sigma_map_eq_iff
            (fun m (q : NodeAt f m) => (Sum.inr q : NodeAt f.all m))
            (fun m a b h => Sum.inr_injective h) q' (rootAt f)
          have hroot : (Sum.inr ⟨m', Sum.inr q'⟩ :
              B.ι ⊕ Σ m'', NodeAt f.all m'') =
                Sum.inr ⟨n + 1, Sum.inr (rootAt f)⟩ ↔ isRootB f q' = true :=
            ⟨fun h => (isRootB_iff f q').mpr (hsig.mp (Sum.inr_injective h)),
             fun h => congrArg Sum.inr (hsig.mpr ((isRootB_iff f q').mp h))⟩
          change (if isRootB f q' then
              if k = 0 ∧ s = true then eqTupF u x
              else if k = 1 ∧ s = false then agreeF n u x ⊓ canonF (n + 1) x
              else ⊥
            else ⊥).Realize v ↔ _
          split_ifs with hr h1 h2
          · obtain ⟨rfl, rfl⟩ := h1
            rw [realize_eqTupF]
            constructor
            · intro he
              exact Or.inl ⟨rfl, Or.inr ⟨rfl, hroot.mpr hr, he⟩⟩
            · rintro (⟨-, ⟨hs, -⟩ | ⟨-, -, he⟩⟩ | ⟨hk, -⟩)
              · exact absurd hs (by simp)
              · exact he
              · exact absurd hk (by decide)
          · obtain ⟨rfl, rfl⟩ := h2
            rw [Formula.realize_inf, realize_agreeF, realize_canonF]
            constructor
            · rintro ⟨hag, hc⟩
              exact Or.inr ⟨rfl, Or.inr ⟨rfl, hroot.mpr hr, hag, hc⟩⟩
            · rintro (⟨hk, -⟩ | ⟨-, ⟨hs, -⟩ | ⟨-, -, hag, hc⟩⟩)
              · exact absurd hk (by decide)
              · exact absurd hs (by simp)
              · exact ⟨hag, hc⟩
          · rw [Formula.realize_bot]
            refine iff_of_false id ?_
            rintro (⟨rfl, ⟨rfl, h, -⟩ | ⟨rfl, -, -⟩⟩ | ⟨rfl, ⟨rfl, h, -⟩ | ⟨rfl, -, -⟩⟩)
            · have h' := Sum.inr_injective h
              injection h' with hm h''
              subst hm
              exact absurd (eq_of_heq h'') (by rintro ⟨⟩)
            · exact h1 ⟨rfl, rfl⟩
            · have h' := Sum.inr_injective h
              injection h' with hm h''
              subst hm
              exact absurd (eq_of_heq h'') (by rintro ⟨⟩)
            · exact h2 ⟨rfl, rfl⟩
          · rw [Formula.realize_bot]
            refine iff_of_false id ?_
            rintro (⟨rfl, ⟨rfl, h, -⟩ | ⟨rfl, h, -⟩⟩ | ⟨rfl, ⟨rfl, h, -⟩ | ⟨rfl, h, -⟩⟩)
            · have h' := Sum.inr_injective h
              injection h' with hm h''
              subst hm
              exact absurd (eq_of_heq h'') (by rintro ⟨⟩)
            · exact hr (hroot.mp h)
            · have h' := Sum.inr_injective h
              injection h' with hm h''
              subst hm
              exact absurd (eq_of_heq h'') (by rintro ⟨⟩)
            · exact hr (hroot.mp h)
      · -- subtree
        rcases vt with i | ⟨m', ⟨-⟩ | q'⟩
        · exact realize_litF s f hctx q k (Sum.inl i) u x
        · exact Iff.rfl
        · exact realize_litF s f hctx q k (Sum.inr ⟨m', q'⟩) u x

end RealizeLit

end ClauseFormulas

end Tseitin

end DescriptiveComplexity
