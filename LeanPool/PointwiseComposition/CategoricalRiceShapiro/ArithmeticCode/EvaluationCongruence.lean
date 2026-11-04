/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.Evaluation
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.EncodedList
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.Pairing

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Valuation-local congruence for the minimized constructors

`CategoricalRiceShapiro.ArithmeticCode.Evaluation` proves congruence at a fixed
assignment for composition and for the constructors built directly from the
primitives.  This module continues the same discipline through the constructors
defined by minimization.

The congruence laws assume only `ORingStructure M`.  The general laws compare
two arities and assignments; their fixed-assignment specializations quantify
only over possible values of the argument codes.

The minimization step is the substantive one.  `Nat.ArithPart₁.Code.rfind`
translates to a conjunction of two occurrences of the body formula, one at the
found value and one under a bounded quantifier, and an equivalence of bodies at
every extended assignment transports both.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace ArithmeticCode

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

variable {M : Type*} [ORingStructure M]

/-!
### Minimization -/

/-- `code` differs from `codeAux` by a renaming that evaluation absorbs. -/
private theorem evalb_iff_evalf {k : ℕ} (c : Code k) (z : M) (w : Fin k → M) :
    Semiformula.Evalb (z :> w) (code c) ↔ Semiformula.Evalf (M := M) (z :> w) (codeAux c) := by
  simp [code, Semiformula.eval_rew, Matrix.empty_eq, Function.comp_def]

/-- Evaluation of a search for a zero: the body vanishes at the found value,
and below it the body is somewhere nonzero. -/
private theorem eval_rfind_iff {k : ℕ} (c : Code (k + 1)) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (code (Code.rfind c)) ↔
      (Semiformula.Evalb ((0 : M) :> z :> v) (code c) ∧
        ∀ t : M, t < z → ∃ x : M, x ≠ 0 ∧ Semiformula.Evalb (x :> t :> v) (code c)) :=
  by
  simp only [evalb_iff_evalf]
  simp [codeAux, Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons']

/-- Evaluation of a substitution: the body holds at the value the substituted
code takes.

`codeBind` is a composition whose argument vector is the substituted code
followed by the projections, so this is `eval_comp_iff` with that vector
identified. -/
theorem eval_codeBind_iff {n : ℕ} (dg : Code n) (dc : Code (n + 1)) (y : M) (v : Fin n → M) :
    Semiformula.Evalb (y :> v) (code (codeBind dg dc)) ↔
      ∃ x : M,
        Semiformula.Evalb (x :> v) (code dg) ∧ Semiformula.Evalb (y :> x :> v) (code dc) :=
  by
  simp only [codeBind]
  rw [eval_comp_iff]
  constructor
  · rintro ⟨w, hc, hi⟩
    have hw : w = (w 0 :> v) := by
      funext i
      refine Fin.cases rfl ?_ i
      intro j
      have hj := hi j.succ
      simp only [Fin.cases_succ] at hj
      have : w j.succ = v j := (eval_proj_iff j (w j.succ) v).mp hj
      simpa using this
    refine ⟨w 0, by simpa using hi 0, ?_⟩
    rw [hw] at hc
    exact hc
  · rintro ⟨x, hg, hy⟩
    refine ⟨x :> v, hy, ?_⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa using hg
    · intro j
      simp only [Fin.cases_succ]
      exact (eval_proj_iff j _ v).mpr (by simp)

/-- Evaluation of a minimization: the body is positive somewhere at the found
value, and vanishes at every smaller one.

`codeRfindPos` searches for the least argument at which its body is positive,
which `Code.rfind` reaches by inverting the body twice.  This states the search
directly in terms of the body, and is the form every use below needs. -/
theorem eval_codeRfindPos_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (d : Code (k + 1)) (s : M)
    (v : Fin k → M) :
    Semiformula.Evalb (s :> v) (code (codeRfindPos d)) ↔
      ((∃ a : M, 0 < a ∧ Semiformula.Evalb (a :> s :> v) (code d)) ∧
        ∀ t : M, t < s → Semiformula.Evalb ((0 : M) :> t :> v) (code d)) :=
  by
  have hinv :
    ∀ (w : M) (u : Fin (k + 1) → M),
      Semiformula.Evalb (w :> u) (code (codeInv (codePos d))) ↔
        ((w = 1 ∧ Semiformula.Evalb ((0 : M) :> u) (code d)) ∨
          (w = 0 ∧ ∃ a : M, 0 < a ∧ Semiformula.Evalb (a :> u) (code d))) :=
    by
    intro w u
    rw [eval_codeInv_iff]
    constructor
    · rintro ⟨p, hp, hcase⟩
      rw [eval_codePos_iff] at hp
      obtain ⟨b, hb, hbcase⟩ := hp
      rcases hbcase with ⟨hbpos, rfl⟩ | ⟨hbnpos, rfl⟩
      · rcases hcase with ⟨h10, _⟩ | ⟨_, rfl⟩
        · exact absurd h10.symm _root_.zero_ne_one
        · exact Or.inr ⟨rfl, b, hbpos, hb⟩
      · rcases hcase with ⟨_, rfl⟩ | ⟨h00, _⟩
        · refine Or.inl ⟨rfl, ?_⟩
          have : b = 0 := le_antisymm (not_lt.mp hbnpos) (by simp)
          rwa [this] at hb
        · exact absurd rfl h00
    · rintro (⟨rfl, hd⟩ | ⟨rfl, a, hapos, ha⟩)
      · refine ⟨0, ?_, Or.inl ⟨rfl, rfl⟩⟩
        rw [eval_codePos_iff]
        exact ⟨0, hd, Or.inr ⟨by simp, rfl⟩⟩
      · refine ⟨1, ?_, Or.inr ⟨_root_.one_ne_zero, rfl⟩⟩
        rw [eval_codePos_iff]
        exact ⟨a, ha, Or.inl ⟨hapos, rfl⟩⟩
  simp only [codeRfindPos]
  rw [eval_rfind_iff]
  refine and_congr ?_ ?_
  · rw [hinv]
    constructor
    · rintro (⟨h01, _⟩ | ⟨_, h⟩)
      · exact absurd h01 (Ne.symm _root_.one_ne_zero)
      · exact h
    · intro h
      exact Or.inr ⟨rfl, h⟩
  · refine forall_congr' fun t => imp_congr Iff.rfl ?_
    constructor
    · rintro ⟨x, hx0, hx⟩
      rw [hinv] at hx
      rcases hx with ⟨_, hd⟩ | ⟨rfl, _⟩
      · exact hd
      · exact absurd rfl hx0
    · intro hd
      exact ⟨1, _root_.one_ne_zero, (hinv 1 (t :> v)).mpr (Or.inl ⟨rfl, hd⟩)⟩

/-!
### Congruence across two arities and two assignments

Congruence at a fixed assignment compares two codes of one arity.
Relating an entry that `codePrec` reads with the entry its step relation supplies
needs more: the two `codeBeta` applications there have different argument codes,
different arities and different assignments, and agree only through the values
their arguments take.  `EvalEq` records exactly that agreement, and the closure
lemmas below propagate it.

Nothing here evaluates a code in the model, and no arithmetic meaning is
attached to remainder, unpairing or `codeBeta`; each is delta-reduced as a syntax
tree.  No arithmetic theory is assumed. -/

/-- Minimization preserves graph agreement under every extra search input. -/
theorem evalEq_rfind {k l : ℕ} {A : Code (k + 1)} {A' : Code (l + 1)} {v : Fin k → M}
    {v' : Fin l → M} (hA : ∀ t : M, EvalEq A (t :> v) A' (t :> v')) :
    EvalEq (Code.rfind A) v (Code.rfind A') v' :=
  by
  intro x
  rw [eval_rfind_iff, eval_rfind_iff]
  exact
    and_congr (hA x 0)
      (forall_congr' fun t =>
        imp_congr Iff.rfl (exists_congr fun y => and_congr Iff.rfl (hA t y)))

/-- Positive-test minimization preserves agreement at every extra search input. -/
theorem evalEq_codeRfindPos {k l : ℕ} {A : Code (k + 1)} {A' : Code (l + 1)}
    {v : Fin k → M} {v' : Fin l → M} (hA : ∀ t : M, EvalEq A (t :> v) A' (t :> v')) :
    EvalEq (codeRfindPos A) v (codeRfindPos A') v' :=
  by
  simp only [codeRfindPos]
  exact evalEq_rfind (fun t => evalEq_codeInv (evalEq_codePos (hA t)))

/-- Code binding preserves heterogeneous graph agreement. -/
theorem evalEq_codeBind {k l : ℕ} {dg : Code k} {dc : Code (k + 1)} {dg' : Code l}
    {dc' : Code (l + 1)} {v : Fin k → M} {v' : Fin l → M} (hg : EvalEq dg v dg' v')
    (hc : ∀ t : M, EvalEq dc (t :> v) dc' (t :> v')) :
    EvalEq (codeBind dg dc) v (codeBind dg' dc') v' :=
  by
  intro x
  rw [eval_codeBind_iff, eval_codeBind_iff]
  exact exists_congr fun t => and_congr (hg t) (hc t x)

/-!
### The derived constructors, across two arities and assignments -/

/-- Subtraction-code construction preserves heterogeneous graph agreement. -/
theorem evalEq_codeSub {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeSub A B) v (codeSub A' B') v' :=
  by
  simp only [codeSub]
  refine evalEq_codeRfindPos (fun t => ?_)
  exact
    evalEq_codeOr
      (evalEq_codeEq (evalEq_codeAdd (evalEq_codeHead t v v') (evalEq_codeLift t t hB))
        (evalEq_codeLift t t hA))
      (evalEq_codeAnd (evalEq_codeLt (evalEq_codeLift t t hA) (evalEq_codeLift t t hB))
        (evalEq_codeEq (evalEq_codeHead t v v') (evalEq_zero _ _)))

/-- Square-root-code construction preserves heterogeneous graph agreement. -/
theorem evalEq_codeSqrt {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') : EvalEq (codeSqrt A) v (codeSqrt A') v' :=
  by
  simp only [codeSqrt]
  refine evalEq_codeRfindPos (fun t => ?_)
  exact
    evalEq_codeAnd
      (evalEq_codeOr
        (evalEq_codeLt (evalEq_codeMul (evalEq_codeHead t v v') (evalEq_codeHead t v v'))
          (evalEq_codeLift t t hA))
        (evalEq_codeEq (evalEq_codeMul (evalEq_codeHead t v v') (evalEq_codeHead t v v'))
          (evalEq_codeLift t t hA)))
      (evalEq_codeLt (evalEq_codeLift t t hA)
        (evalEq_codeMul (evalEq_codeSucc (evalEq_codeHead t v v'))
          (evalEq_codeSucc (evalEq_codeHead t v v'))))

/-- Conditional-code construction preserves heterogeneous graph agreement. -/
theorem evalEq_codeIfPos {k l : ℕ} {F G H : Code k} {F' G' H' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hF : EvalEq F v F' v') (hG : EvalEq G v G' v') (hH : EvalEq H v H' v') :
    EvalEq (codeIfPos F G H) v (codeIfPos F' G' H') v' :=
  by
  simp only [codeIfPos]
  exact
    evalEq_codeAdd (evalEq_codeMul (evalEq_codePos hF) hG)
      (evalEq_codeMul (evalEq_codeInv hF) hH)

/-- Non-strict order-test code construction preserves heterogeneous graph agreement. -/
theorem evalEq_codeLe {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeLe A B) v (codeLe A' B') v' :=
  by
  simp only [codeLe]
  exact evalEq_codeOr (evalEq_codeLt hA hB) (evalEq_codeEq hA hB)

/-- First-unpairing code construction preserves heterogeneous graph agreement. -/
theorem evalEq_codeUnpair₁ {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') : EvalEq (codeUnpair₁ A) v (codeUnpair₁ A') v' :=
  by
  simp only [codeUnpair₁]
  have hsq := evalEq_codeSqrt hA
  have hdiff := evalEq_codeSub hA (evalEq_codeMul hsq hsq)
  exact evalEq_codeIfPos (evalEq_codeLt hdiff hsq) hdiff hsq

/-- Second-unpairing code construction preserves heterogeneous graph agreement. -/
theorem evalEq_codeUnpair₂ {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') : EvalEq (codeUnpair₂ A) v (codeUnpair₂ A') v' :=
  by
  simp only [codeUnpair₂]
  have hsq := evalEq_codeSqrt hA
  have hdiff := evalEq_codeSub hA (evalEq_codeMul hsq hsq)
  exact evalEq_codeIfPos (evalEq_codeLt hdiff hsq) hsq (evalEq_codeSub hdiff hsq)

/-- Pairing-code construction preserves heterogeneous graph agreement. -/
theorem evalEq_codePair {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codePair A B) v (codePair A' B') v' :=
  by
  simp only [codePair]
  exact
    evalEq_codeIfPos (evalEq_codeLt hA hB) (evalEq_codeAdd (evalEq_codeMul hB hB) hA)
      (evalEq_codeAdd (evalEq_codeAdd (evalEq_codeMul hA hA) hA) hB)

/-- Divisibility-test code construction preserves heterogeneous graph agreement. -/
theorem evalEq_codeDvd {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeDvd A B) v (codeDvd A' B') v' :=
  by
  simp only [codeDvd]
  refine evalEq_codeBind (evalEq_codeRfindPos (fun t => ?_)) (fun t => ?_)
  · exact
      evalEq_codeOr
        (evalEq_codeEq (evalEq_codeMul (evalEq_codeHead t v v') (evalEq_codeLift t t hA))
          (evalEq_codeLift t t hB))
        (evalEq_codeLt (evalEq_codeLift t t hB) (evalEq_codeHead t v v'))
  · exact evalEq_codeLe (evalEq_codeHead t v v') (evalEq_codeLift t t hB)

/-- Remainder-code construction preserves heterogeneous graph agreement. -/
theorem evalEq_codeRem {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeRem A B) v (codeRem A' B') v' :=
  by
  simp only [codeRem]
  refine evalEq_codeRfindPos (fun t => ?_)
  exact
    evalEq_codeDvd (evalEq_codeLift t t hB)
      (evalEq_codeSub (evalEq_codeLift t t hA) (evalEq_codeHead t v v'))

/-- Two `codeBeta` applications agree whenever their argument codes do, even at
different arities and under different assignments.

`codeBeta` is delta-reduced here as a syntax tree only; nothing evaluates it, and
no arithmetic meaning is attached to remainder or unpairing. -/
theorem eval_codeBeta_congr_at {k l : ℕ} (N I : Code k) (N' I' : Code l) (z : M) (v : Fin k → M)
    (v' : Fin l → M)
    (hN : ∀ x : M, Semiformula.Evalb (x :> v) (code N) ↔ Semiformula.Evalb (x :> v') (code N'))
    (hI :
      ∀ x : M, Semiformula.Evalb (x :> v) (code I) ↔ Semiformula.Evalb (x :> v') (code I')) :
    Semiformula.Evalb (z :> v) (code (codeBeta N I)) ↔
      Semiformula.Evalb (z :> v') (code (codeBeta N' I')) :=
  by
  simp only [codeBeta]
  exact
    evalEq_codeRem (evalEq_codeUnpair₁ hN)
      (evalEq_codeSucc (evalEq_codeMul (evalEq_codeSucc hI) (evalEq_codeUnpair₂ hN))) z

/-- Equivalent bodies determine equivalent minimizations.

This is the congruence law for the minimization context, stated at the
assignment `v` and quantified over the value and the search argument. -/
theorem eval_codeRfindPos_congr {k : ℕ} (A A' : Code (k + 1)) (z : M) (v : Fin k → M)
    (hA :
      ∀ x t : M,
        Semiformula.Evalb (x :> t :> v) (code A) ↔ Semiformula.Evalb (x :> t :> v) (code A')) :
    Semiformula.Evalb (z :> v) (code (codeRfindPos A)) ↔
      Semiformula.Evalb (z :> v) (code (codeRfindPos A')) :=
  evalEq_codeRfindPos (fun t x => hA x t) z

/-!
### Constructors defined by minimization -/

theorem eval_codeSub_congr {k : ℕ} (A A' B B' : Code k) (z : M) (v : Fin k → M)
    (hA : ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v) (code A'))
    (hB : ∀ x : M, Semiformula.Evalb (x :> v) (code B) ↔ Semiformula.Evalb (x :> v) (code B')) :
    Semiformula.Evalb (z :> v) (code (codeSub A B)) ↔
      Semiformula.Evalb (z :> v) (code (codeSub A' B')) :=
  evalEq_codeSub hA hB z

theorem eval_codeSqrt_congr {k : ℕ} (A A' : Code k) (z : M) (v : Fin k → M)
    (hA : ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v) (code A')) :
    Semiformula.Evalb (z :> v) (code (codeSqrt A)) ↔
      Semiformula.Evalb (z :> v) (code (codeSqrt A')) :=
  evalEq_codeSqrt hA z

theorem eval_codeIfPos_congr {k : ℕ} (F F' G G' H H' : Code k) (z : M) (v : Fin k → M)
    (hF : ∀ x : M, Semiformula.Evalb (x :> v) (code F) ↔ Semiformula.Evalb (x :> v) (code F'))
    (hG : ∀ x : M, Semiformula.Evalb (x :> v) (code G) ↔ Semiformula.Evalb (x :> v) (code G'))
    (hH : ∀ x : M, Semiformula.Evalb (x :> v) (code H) ↔ Semiformula.Evalb (x :> v) (code H')) :
    Semiformula.Evalb (z :> v) (code (codeIfPos F G H)) ↔
      Semiformula.Evalb (z :> v) (code (codeIfPos F' G' H')) :=
  evalEq_codeIfPos hF hG hH z

theorem eval_codeUnpair₁_congr {k : ℕ} (A A' : Code k) (z : M) (v : Fin k → M)
    (hA : ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v) (code A')) :
    Semiformula.Evalb (z :> v) (code (codeUnpair₁ A)) ↔
      Semiformula.Evalb (z :> v) (code (codeUnpair₁ A')) :=
  evalEq_codeUnpair₁ hA z

theorem eval_codeUnpair₂_congr {k : ℕ} (A A' : Code k) (z : M) (v : Fin k → M)
    (hA : ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v) (code A')) :
    Semiformula.Evalb (z :> v) (code (codeUnpair₂ A)) ↔
      Semiformula.Evalb (z :> v) (code (codeUnpair₂ A')) :=
  evalEq_codeUnpair₂ hA z

/-!
### Pairing -/

theorem eval_codePair_congr {k : ℕ} (A A' B B' : Code k) (z : M) (v : Fin k → M)
    (hA : ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v) (code A'))
    (hB : ∀ x : M, Semiformula.Evalb (x :> v) (code B) ↔ Semiformula.Evalb (x :> v) (code B')) :
    Semiformula.Evalb (z :> v) (code (codePair A B)) ↔
      Semiformula.Evalb (z :> v) (code (codePair A' B')) :=
  evalEq_codePair hA hB z

/-!
### Encoded lists -/

theorem eval_codeListHeadOptional_congr {k : ℕ} (A A' : Code k) (z : M) (v : Fin k → M)
    (hA : ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v) (code A')) :
    Semiformula.Evalb (z :> v) (code (codeListHeadOptional A)) ↔
      Semiformula.Evalb (z :> v) (code (codeListHeadOptional A')) :=
  by
  simp only [codeListHeadOptional]
  exact
    eval_codeIfPos_congr _ _ _ _ _ _ z v hA
      (fun x =>
        eval_codeSucc_congr _ _ x v
          (fun y =>
            eval_codeUnpair₁_congr _ _ y v
              (fun w => eval_codeSub_congr _ _ _ _ w v hA (fun _ => Iff.rfl))))
      (fun _ => Iff.rfl)

theorem eval_codeListTail_congr {k : ℕ} (A A' : Code k) (z : M) (v : Fin k → M)
    (hA : ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v) (code A')) :
    Semiformula.Evalb (z :> v) (code (codeListTail A)) ↔
      Semiformula.Evalb (z :> v) (code (codeListTail A')) :=
  by
  simp only [codeListTail]
  exact
    eval_codeUnpair₂_congr _ _ z v
      (fun x => eval_codeSub_congr _ _ _ _ x v hA (fun _ => Iff.rfl))

theorem eval_codeListDrop_congr {k : ℕ} (L L' I I' : Code k) (z : M) (v : Fin k → M)
    (hL : ∀ x : M, Semiformula.Evalb (x :> v) (code L) ↔ Semiformula.Evalb (x :> v) (code L'))
    (hI : ∀ x : M, Semiformula.Evalb (x :> v) (code I) ↔ Semiformula.Evalb (x :> v) (code I')) :
    Semiformula.Evalb (z :> v) (code (codeListDrop L I)) ↔
      Semiformula.Evalb (z :> v) (code (codeListDrop L' I')) :=
  by
  rw [codeListDrop_eq_comp, codeListDrop_eq_comp]
  refine eval_comp_congr _ _ _ z v ?_
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · intro x
    simpa using hI x
  · intro x
    simpa using hL x

theorem eval_codeListGetOptional_congr {k : ℕ} (L L' I I' : Code k) (z : M) (v : Fin k → M)
    (hL : ∀ x : M, Semiformula.Evalb (x :> v) (code L) ↔ Semiformula.Evalb (x :> v) (code L'))
    (hI : ∀ x : M, Semiformula.Evalb (x :> v) (code I) ↔ Semiformula.Evalb (x :> v) (code I')) :
    Semiformula.Evalb (z :> v) (code (codeListGetOptional L I)) ↔
      Semiformula.Evalb (z :> v) (code (codeListGetOptional L' I')) :=
  by
  simp only [codeListGetOptional]
  exact
    eval_codeListHeadOptional_congr _ _ z v
      (fun x => eval_codeListDrop_congr L L' I I' x v hL hI)

end ArithmeticCode
end CategoricalRiceShapiro

end

end PointwiseComposition
