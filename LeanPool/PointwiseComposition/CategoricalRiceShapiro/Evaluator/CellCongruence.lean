/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.Cell
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.EvaluationCongruence

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Heterogeneous congruence for the evaluator cell

`eval_codeEvaluatorCell_congr_at` compares two evaluator cells written at
different arities and read under different assignments.  It is the analogue for
`codeEvaluatorCell` of `eval_codeBeta_congr_at`, and is proved the same way: a
relation saying that two codes have the same graph, each under its own
assignment, is propagated through every constructor the cell is built from.

Every branch of the eager conditional is treated; none is discarded because its
tag is unused.  The derived constructors are delta-reduced as syntax trees only.
No arithmetic meaning is attached to any of them, no totality is asserted, and
the results hold in an arbitrary `ORingStructure`.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace Evaluator

open CategoricalRiceShapiro.ArithmeticCode

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

variable {M : Type*} [ORingStructure M]

/-- Two codes have the same graph, each under its own assignment. -/
private abbrev EvalEq {k l : ℕ} (A : Code k) (v : Fin k → M) (A' : Code l) (v' : Fin l → M) :
    Prop :=
  ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v') (code A')

/-!
### Primitives -/

private theorem evalEq_proj {k l : ℕ} (i : Fin k) (j : Fin l) (v : Fin k → M) (v' : Fin l → M)
    (h : v i = v' j) : EvalEq (Code.proj i) v (Code.proj j) v' := by
  intro x;
  rw [eval_proj_iff, eval_proj_iff, h]

private theorem evalEq_zero {k l : ℕ} (v : Fin k → M) (v' : Fin l → M) :
    EvalEq (Code.zero k) v (Code.zero l) v' := by intro x; rw [eval_zero_iff, eval_zero_iff]

private theorem evalEq_one {k l : ℕ} (v : Fin k → M) (v' : Fin l → M) :
    EvalEq (Code.one k) v (Code.one l) v' := by intro x; rw [eval_one_iff, eval_one_iff]

private theorem evalEq_codeHead {k l : ℕ} (t : M) (v : Fin k → M) (v' : Fin l → M) :
    EvalEq (codeHead (n := k)) (t :> v) (codeHead (n := l)) (t :> v') :=
  evalEq_proj 0 0 _ _ rfl

/-- A lift ignores its head, so the two heads need not agree. -/
private theorem evalEq_codeLift {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (t t' : M) (hA : EvalEq A v A' v') :
    EvalEq (codeLift A) (t :> v) (codeLift A') (t' :> v') := by
  intro x;
  rw [eval_codeLift_iff, eval_codeLift_iff]; exact hA x

/-- Composition with a shared outer code. -/
private theorem evalEq_comp {k l m : ℕ} (c : Code m) (ds : Fin m → Code k)
    (ds' : Fin m → Code l) {v : Fin k → M} {v' : Fin l → M}
    (h : ∀ i, EvalEq (ds i) v (ds' i) v') : EvalEq (c.comp ds) v (c.comp ds') v' :=
  by
  intro x
  rw [eval_comp_iff, eval_comp_iff]
  constructor
  · rintro ⟨w, hw, hwi⟩; exact ⟨w, hw, fun i => (h i (w i)).mp (hwi i)⟩
  · rintro ⟨w, hw, hwi⟩; exact ⟨w, hw, fun i => (h i (w i)).mpr (hwi i)⟩

/-!
### Arithmetic and boolean constructors -/

private theorem evalEq_codeSucc {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') : EvalEq (codeSucc A) v (codeSucc A') v' :=
  by
  intro x
  rw [eval_codeSucc_iff, eval_codeSucc_iff]
  exact exists_congr fun a => and_congr (hA a) Iff.rfl

private theorem evalEq_codePos {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') : EvalEq (codePos A) v (codePos A') v' :=
  by
  intro x
  rw [eval_codePos_iff, eval_codePos_iff]
  exact exists_congr fun a => and_congr (hA a) Iff.rfl

private theorem evalEq_codeInv {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') : EvalEq (codeInv A) v (codeInv A') v' :=
  by
  intro x
  rw [eval_codeInv_iff, eval_codeInv_iff]
  exact exists_congr fun a => and_congr (hA a) Iff.rfl

private theorem evalEq_codeAdd {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeAdd A B) v (codeAdd A' B') v' :=
  by
  intro x
  rw [eval_codeAdd_iff, eval_codeAdd_iff]
  exact exists_congr fun a => exists_congr fun b => and_congr (hA a) (and_congr (hB b) Iff.rfl)

private theorem evalEq_codeMul {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeMul A B) v (codeMul A' B') v' :=
  by
  intro x
  rw [eval_codeMul_iff, eval_codeMul_iff]
  exact exists_congr fun a => exists_congr fun b => and_congr (hA a) (and_congr (hB b) Iff.rfl)

private theorem evalEq_codeEq {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeEq A B) v (codeEq A' B') v' :=
  by
  intro x
  rw [eval_codeEq_iff, eval_codeEq_iff]
  exact exists_congr fun a => exists_congr fun b => and_congr (hA a) (and_congr (hB b) Iff.rfl)

private theorem evalEq_codeLt {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeLt A B) v (codeLt A' B') v' :=
  by
  intro x
  rw [eval_codeLt_iff, eval_codeLt_iff]
  exact exists_congr fun a => exists_congr fun b => and_congr (hA a) (and_congr (hB b) Iff.rfl)

private theorem evalEq_codeAnd {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeAnd A B) v (codeAnd A' B') v' :=
  by
  intro x
  rw [eval_codeAnd_iff, eval_codeAnd_iff]
  exact exists_congr fun a => exists_congr fun b => and_congr (hA a) (and_congr (hB b) Iff.rfl)

private theorem evalEq_codeOr {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeOr A B) v (codeOr A' B') v' :=
  by
  intro x
  rw [eval_codeOr_iff, eval_codeOr_iff]
  exact exists_congr fun a => exists_congr fun b => and_congr (hA a) (and_congr (hB b) Iff.rfl)

private theorem evalEq_codeIfPos {k l : ℕ} {A B C : Code k} {A' B' C' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') (hC : EvalEq C v C' v') :
    EvalEq (codeIfPos A B C) v (codeIfPos A' B' C') v' :=
  by
  simp only [codeIfPos]
  exact
    evalEq_codeAdd (evalEq_codeMul (evalEq_codePos hA) hB)
      (evalEq_codeMul (evalEq_codeInv hA) hC)

private theorem evalEq_codeConst {k l : ℕ} (m : ℕ) (v : Fin k → M) (v' : Fin l → M) :
    EvalEq (codeConst (n := k) m) v (codeConst (n := l) m) v' := by
  induction m with
  | zero => exact evalEq_zero v v'
  | succ m ih => exact evalEq_codeSucc ih

/-!
### Minimization contexts -/

/-- `code` differs from `codeAux` by a renaming that evaluation absorbs. -/
private theorem evalb_iff_evalf {k : ℕ} (c : Code k) (z : M) (w : Fin k → M) :
    Semiformula.Evalb (z :> w) (code c) ↔ Semiformula.Evalf (M := M) (z :> w) (codeAux c) := by
  simp [code, Semiformula.eval_rew, Matrix.empty_eq, Function.comp_def]

/-- Evaluation of a search for a zero, without an arithmetic theory. -/
private theorem eval_rfind_iff {k : ℕ} (c : Code (k + 1)) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (code (Code.rfind c)) ↔
      (Semiformula.Evalb ((0 : M) :> z :> v) (code c) ∧
        ∀ t : M, t < z → ∃ x : M, x ≠ 0 ∧ Semiformula.Evalb (x :> t :> v) (code c)) :=
  by
  simp only [evalb_iff_evalf]
  simp [codeAux, Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons']

private theorem evalEq_rfind {k l : ℕ} {A : Code (k + 1)} {A' : Code (l + 1)} {v : Fin k → M}
    {v' : Fin l → M} (hA : ∀ t : M, EvalEq A (t :> v) A' (t :> v')) :
    EvalEq (Code.rfind A) v (Code.rfind A') v' :=
  by
  intro x
  rw [eval_rfind_iff, eval_rfind_iff]
  exact
    and_congr (hA x 0)
      (forall_congr' fun t =>
        imp_congr Iff.rfl (exists_congr fun y => and_congr Iff.rfl (hA t y)))

private theorem evalEq_codeRfindPos {k l : ℕ} {A : Code (k + 1)} {A' : Code (l + 1)}
    {v : Fin k → M} {v' : Fin l → M} (hA : ∀ t : M, EvalEq A (t :> v) A' (t :> v')) :
    EvalEq (codeRfindPos A) v (codeRfindPos A') v' :=
  by
  simp only [codeRfindPos]
  exact evalEq_rfind (fun t => evalEq_codeInv (evalEq_codePos (hA t)))

private theorem evalEq_codeBind {k l : ℕ} {dg : Code k} {dc : Code (k + 1)} {dg' : Code l}
    {dc' : Code (l + 1)} {v : Fin k → M} {v' : Fin l → M} (hg : EvalEq dg v dg' v')
    (hc : ∀ t : M, EvalEq dc (t :> v) dc' (t :> v')) :
    EvalEq (codeBind dg dc) v (codeBind dg' dc') v' :=
  by
  intro x
  rw [eval_codeBind_iff, eval_codeBind_iff]
  exact exists_congr fun t => and_congr (hg t) (hc t x)

/-!
### Derived arithmetic -/

private theorem evalEq_codeSub {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
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

private theorem evalEq_codeSqrt {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
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

private theorem evalEq_codeUnpair₁ {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') : EvalEq (codeUnpair₁ A) v (codeUnpair₁ A') v' :=
  by
  simp only [codeUnpair₁]
  exact
    evalEq_codeIfPos
      (evalEq_codeLt
        (evalEq_codeSub hA (evalEq_codeMul (evalEq_codeSqrt hA) (evalEq_codeSqrt hA)))
        (evalEq_codeSqrt hA))
      (evalEq_codeSub hA (evalEq_codeMul (evalEq_codeSqrt hA) (evalEq_codeSqrt hA)))
      (evalEq_codeSqrt hA)

private theorem evalEq_codeUnpair₂ {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') : EvalEq (codeUnpair₂ A) v (codeUnpair₂ A') v' :=
  by
  simp only [codeUnpair₂]
  exact
    evalEq_codeIfPos
      (evalEq_codeLt
        (evalEq_codeSub hA (evalEq_codeMul (evalEq_codeSqrt hA) (evalEq_codeSqrt hA)))
        (evalEq_codeSqrt hA))
      (evalEq_codeSqrt hA)
      (evalEq_codeSub
        (evalEq_codeSub hA (evalEq_codeMul (evalEq_codeSqrt hA) (evalEq_codeSqrt hA)))
        (evalEq_codeSqrt hA))

private theorem evalEq_codePair {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codePair A B) v (codePair A' B') v' :=
  by
  simp only [codePair]
  exact
    evalEq_codeIfPos (evalEq_codeLt hA hB) (evalEq_codeAdd (evalEq_codeMul hB hB) hA)
      (evalEq_codeAdd (evalEq_codeAdd (evalEq_codeMul hA hA) hA) hB)

private theorem evalEq_codeLe {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeLe A B) v (codeLe A' B') v' :=
  by
  simp only [codeLe]
  exact evalEq_codeOr (evalEq_codeLt hA hB) (evalEq_codeEq hA hB)

private theorem evalEq_codeDvd {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
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

private theorem evalEq_codeRem {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeRem A B) v (codeRem A' B') v' :=
  by
  simp only [codeRem]
  refine evalEq_codeRfindPos (fun t => ?_)
  exact
    evalEq_codeDvd (evalEq_codeLift t t hB)
      (evalEq_codeSub (evalEq_codeLift t t hA) (evalEq_codeHead t v v'))

/-!
### The partial-recursive index layer -/

private theorem evalEq_codeBodd {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') : EvalEq (codeBodd A) v (codeBodd A') v' :=
  by
  simp only [codeBodd]
  exact evalEq_codeRem hA (evalEq_codeConst 2 v v')

private theorem evalEq_codeDiv2 {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') : EvalEq (codeDiv2 A) v (codeDiv2 A') v' :=
  by
  simp only [codeDiv2]
  refine evalEq_comp _ _ _ (fun i => ?_)
  refine Fin.cases ?_ (fun j => Fin.elim0 j) i
  simpa using hA

private theorem evalEq_codePartrecTag {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') :
    EvalEq (codePartrecTag A) v (codePartrecTag A') v' :=
  by
  simp only [codePartrecTag]
  exact
    evalEq_codeIfPos (evalEq_codeLt hA (evalEq_codeConst 4 v v')) hA
      (evalEq_codeAdd
        (evalEq_codeAdd (evalEq_codeConst 4 v v')
          (evalEq_codeMul (evalEq_codeConst 2 v v')
            (evalEq_codeBodd (evalEq_codeSub hA (evalEq_codeConst 4 v v')))))
        (evalEq_codeBodd (evalEq_codeDiv2 (evalEq_codeSub hA (evalEq_codeConst 4 v v')))))

private theorem evalEq_codePartrecPayload {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') :
    EvalEq (codePartrecPayload A) v (codePartrecPayload A') v' :=
  by
  simp only [codePartrecPayload]
  exact evalEq_codeDiv2 (evalEq_codeDiv2 (evalEq_codeSub hA (evalEq_codeConst 4 v v')))

private theorem evalEq_codePartrecPayload₁ {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') :
    EvalEq (codePartrecPayload₁ A) v (codePartrecPayload₁ A') v' :=
  by
  simp only [codePartrecPayload₁]
  exact evalEq_codeUnpair₁ (evalEq_codePartrecPayload hA)

private theorem evalEq_codePartrecPayload₂ {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') :
    EvalEq (codePartrecPayload₂ A) v (codePartrecPayload₂ A') v' :=
  by
  simp only [codePartrecPayload₂]
  exact evalEq_codeUnpair₂ (evalEq_codePartrecPayload hA)

/-!
### The encoded-list layer -/

private theorem evalEq_codeListDrop {k l : ℕ} {A B : Code k} {A' B' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeListDrop A B) v (codeListDrop A' B') v' :=
  by
  rw [codeListDrop_eq_comp, codeListDrop_eq_comp]
  refine evalEq_comp _ _ _ (fun i => ?_)
  refine Fin.cases ?_ ?_ i
  · simpa using hB
  · intro j
    refine Fin.cases ?_ (fun j' => Fin.elim0 j') j
    simpa using hA

private theorem evalEq_codeListHeadOptional {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') :
    EvalEq (codeListHeadOptional A) v (codeListHeadOptional A') v' :=
  by
  simp only [codeListHeadOptional]
  exact
    evalEq_codeIfPos hA
      (evalEq_codeSucc (evalEq_codeUnpair₁ (evalEq_codeSub hA (evalEq_codeConst 1 v v'))))
      (evalEq_zero v v')

private theorem evalEq_codeListTail {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') : EvalEq (codeListTail A) v (codeListTail A') v' :=
  by
  simp only [codeListTail]
  exact evalEq_codeUnpair₂ (evalEq_codeSub hA (evalEq_codeConst 1 v v'))

private theorem evalEq_codeListGetOptional {k l : ℕ} {A B : Code k} {A' B' : Code l}
    {v : Fin k → M} {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v') :
    EvalEq (codeListGetOptional A B) v (codeListGetOptional A' B') v' :=
  by
  simp only [codeListGetOptional]
  exact evalEq_codeListHeadOptional (evalEq_codeListDrop hA hB)

private theorem evalEq_codeListLength {k l : ℕ} {A : Code k} {A' : Code l} {v : Fin k → M}
    {v' : Fin l → M} (hA : EvalEq A v A' v') :
    EvalEq (codeListLength A) v (codeListLength A') v' :=
  by
  simp only [codeListLength]
  refine evalEq_codeRfindPos (fun t => ?_)
  exact evalEq_codeInv (evalEq_codeListDrop (evalEq_codeLift t t hA) (evalEq_codeHead t v v'))

private theorem evalEq_codeOptionBind {k l : ℕ} {A : Code k} {B : Code (k + 1)} {A' : Code l}
    {B' : Code (l + 1)} {v : Fin k → M} {v' : Fin l → M} (hA : EvalEq A v A' v')
    (hB : ∀ t : M, EvalEq B (t :> v) B' (t :> v')) :
    EvalEq (codeOptionBind A B) v (codeOptionBind A' B') v' :=
  by
  simp only [codeOptionBind]
  exact
    evalEq_codeIfPos hA (evalEq_codeBind (evalEq_codeSub hA (evalEq_one v v')) hB)
      (evalEq_zero v v')

private theorem evalEq_codeTableLookup {k l : ℕ} {A B C D : Code k} {A' B' C' D' : Code l}
    {v : Fin k → M} {v' : Fin l → M} (hA : EvalEq A v A' v') (hB : EvalEq B v B' v')
    (hC : EvalEq C v C' v') (hD : EvalEq D v D' v') :
    EvalEq (codeTableLookup A B C D) v (codeTableLookup A' B' C' D') v' :=
  by
  rw [codeTableLookup_eq, codeTableLookup_eq]
  exact
    evalEq_codeSub
      (evalEq_codeListGetOptional
        (evalEq_codeSub (evalEq_codeListGetOptional hA (evalEq_codePair hB hC))
          (evalEq_codeConst 1 v v'))
        hD)
      (evalEq_codeConst 1 v v')

/-- Two encoded-list lengths agree whenever their list codes do, even at
different arities and under different assignments. -/
theorem eval_codeListLength_congr_at {k l : ℕ} (A : Code k) (A' : Code l) (z : M)
    (v : Fin k → M) (v' : Fin l → M)
    (hA :
      ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v') (code A')) :
    Semiformula.Evalb (z :> v) (code (codeListLength A)) ↔
      Semiformula.Evalb (z :> v') (code (codeListLength A')) :=
  evalEq_codeListLength hA z

/-- Two first Cantor components agree whenever their argument codes do, even at
different arities and under different assignments. -/
theorem eval_codeUnpair₁_congr_at {k l : ℕ} (A : Code k) (A' : Code l) (z : M) (v : Fin k → M)
    (v' : Fin l → M)
    (hA :
      ∀ x : M, Semiformula.Evalb (x :> v) (code A) ↔ Semiformula.Evalb (x :> v') (code A')) :
    Semiformula.Evalb (z :> v) (code (codeUnpair₁ A)) ↔
      Semiformula.Evalb (z :> v') (code (codeUnpair₁ A')) :=
  evalEq_codeUnpair₁ hA z

/-- Two table lookups agree whenever their four argument codes do, even at
different arities and under different assignments.

This is the public form of the private closure above; the chain is not
duplicated. -/
theorem eval_codeTableLookup_congr_at {k l : ℕ} (dtable dk dq dn : Code k)
    (dtable' dk' dq' dn' : Code l) (z : M) (v : Fin k → M) (v' : Fin l → M)
    (hT :
      ∀ x : M,
        Semiformula.Evalb (x :> v) (code dtable) ↔ Semiformula.Evalb (x :> v') (code dtable'))
    (hK :
      ∀ x : M, Semiformula.Evalb (x :> v) (code dk) ↔ Semiformula.Evalb (x :> v') (code dk'))
    (hQ :
      ∀ x : M, Semiformula.Evalb (x :> v) (code dq) ↔ Semiformula.Evalb (x :> v') (code dq'))
    (hN :
      ∀ x : M, Semiformula.Evalb (x :> v) (code dn) ↔ Semiformula.Evalb (x :> v') (code dn')) :
    Semiformula.Evalb (z :> v) (code (codeTableLookup dtable dk dq dn)) ↔
      Semiformula.Evalb (z :> v') (code (codeTableLookup dtable' dk' dq' dn')) :=
  evalEq_codeTableLookup hT hK hQ hN z

/-!
### The evaluator-cell branches -/

private theorem evalEq_codeBaseEvaluatorCell {k l : ℕ} {T N : Code k} {T' N' : Code l}
    {v : Fin k → M} {v' : Fin l → M} (hT : EvalEq T v T' v') (hN : EvalEq N v N' v') :
    EvalEq (codeBaseEvaluatorCell T N) v (codeBaseEvaluatorCell T' N') v' :=
  by
  simp only [codeBaseEvaluatorCell]
  have hp := evalEq_codeListLength hT
  have htag := evalEq_codePartrecTag (evalEq_codeUnpair₂ hp)
  exact
    evalEq_codeIfPos (evalEq_codeUnpair₁ hp)
      (evalEq_codeIfPos (evalEq_codeEq htag (evalEq_codeConst 0 v v')) (evalEq_codeConst 1 v v')
        (evalEq_codeIfPos (evalEq_codeEq htag (evalEq_codeConst 1 v v'))
          (evalEq_codeSucc (evalEq_codeSucc hN))
          (evalEq_codeIfPos (evalEq_codeEq htag (evalEq_codeConst 2 v v'))
            (evalEq_codeSucc (evalEq_codeUnpair₁ hN))
            (evalEq_codeIfPos (evalEq_codeEq htag (evalEq_codeConst 3 v v'))
              (evalEq_codeSucc (evalEq_codeUnpair₂ hN)) (evalEq_codeConst 0 v v')))))
      (evalEq_codeConst 0 v v')

private theorem evalEq_codePairEvaluatorCell {k l : ℕ} {T K F G N : Code k}
    {T' K' F' G' N' : Code l} {v : Fin k → M} {v' : Fin l → M} (hT : EvalEq T v T' v')
    (hK : EvalEq K v K' v') (hF : EvalEq F v F' v') (hG : EvalEq G v G' v')
    (hN : EvalEq N v N' v') :
    EvalEq (codePairEvaluatorCell T K F G N) v (codePairEvaluatorCell T' K' F' G' N') v' :=
  by
  simp only [codePairEvaluatorCell]
  refine evalEq_codeOptionBind (evalEq_codeTableLookup hT hK hF hN) (fun t => ?_)
  refine
    evalEq_codeOptionBind
      (evalEq_codeTableLookup (evalEq_codeLift t t hT) (evalEq_codeLift t t hK)
        (evalEq_codeLift t t hG) (evalEq_codeLift t t hN))
      (fun u => ?_)
  exact evalEq_codeSucc (evalEq_codePair (evalEq_proj 1 1 _ _ rfl) (evalEq_proj 0 0 _ _ rfl))

private theorem evalEq_codeCompEvaluatorCell {k l : ℕ} {T K F G N : Code k}
    {T' K' F' G' N' : Code l} {v : Fin k → M} {v' : Fin l → M} (hT : EvalEq T v T' v')
    (hK : EvalEq K v K' v') (hF : EvalEq F v F' v') (hG : EvalEq G v G' v')
    (hN : EvalEq N v N' v') :
    EvalEq (codeCompEvaluatorCell T K F G N) v (codeCompEvaluatorCell T' K' F' G' N') v' :=
  by
  simp only [codeCompEvaluatorCell]
  refine evalEq_codeOptionBind (evalEq_codeTableLookup hT hK hG hN) (fun t => ?_)
  exact
    evalEq_codeTableLookup (evalEq_codeLift t t hT) (evalEq_codeLift t t hK)
      (evalEq_codeLift t t hF) (evalEq_codeHead t v v')

private theorem evalEq_codePrecEvaluatorCell {k l : ℕ} {T K Q F G N : Code k}
    {T' K' Q' F' G' N' : Code l} {v : Fin k → M} {v' : Fin l → M} (hT : EvalEq T v T' v')
    (hK : EvalEq K v K' v') (hQ : EvalEq Q v Q' v') (hF : EvalEq F v F' v')
    (hG : EvalEq G v G' v') (hN : EvalEq N v N' v') :
    EvalEq (codePrecEvaluatorCell T K Q F G N) v (codePrecEvaluatorCell T' K' Q' F' G' N') v' :=
  by
  simp only [codePrecEvaluatorCell]
  have hz := evalEq_codeUnpair₁ hN
  have ht := evalEq_codeUnpair₂ hN
  have hy := evalEq_codeSub ht (evalEq_codeConst 1 v v')
  refine evalEq_codeIfPos ht ?_ (evalEq_codeTableLookup hT (evalEq_codeSucc hK) hF hz)
  refine
    evalEq_codeOptionBind (evalEq_codeTableLookup hT hK hQ (evalEq_codePair hz hy))
      (fun t => ?_)
  exact
    evalEq_codeTableLookup (evalEq_codeLift t t hT) (evalEq_codeLift t t (evalEq_codeSucc hK))
      (evalEq_codeLift t t hG)
      (evalEq_codePair (evalEq_codeLift t t hz)
        (evalEq_codePair (evalEq_codeLift t t hy) (evalEq_codeHead t v v')))

private theorem evalEq_codeRfindEvaluatorCell {k l : ℕ} {T K Q F N : Code k}
    {T' K' Q' F' N' : Code l} {v : Fin k → M} {v' : Fin l → M} (hT : EvalEq T v T' v')
    (hK : EvalEq K v K' v') (hQ : EvalEq Q v Q' v') (hF : EvalEq F v F' v')
    (hN : EvalEq N v N' v') :
    EvalEq (codeRfindEvaluatorCell T K Q F N) v (codeRfindEvaluatorCell T' K' Q' F' N') v' :=
  by
  simp only [codeRfindEvaluatorCell]
  have hz := evalEq_codeUnpair₁ hN
  have hm := evalEq_codeUnpair₂ hN
  refine
    evalEq_codeOptionBind
      (evalEq_codeTableLookup hT (evalEq_codeSucc hK) hF (evalEq_codePair hz hm)) (fun t => ?_)
  exact
    evalEq_codeIfPos (evalEq_codeHead t v v')
      (evalEq_codeTableLookup (evalEq_codeLift t t hT) (evalEq_codeLift t t hK)
        (evalEq_codeLift t t hQ)
        (evalEq_codePair (evalEq_codeLift t t hz) (evalEq_codeSucc (evalEq_codeLift t t hm))))
      (evalEq_codeSucc (evalEq_codeLift t t hm))

/-- Two evaluator cells agree whenever their table and index codes do, even at
different arities and under different assignments.

Every branch of the eager conditional is compared; none is discarded. -/
theorem eval_codeEvaluatorCell_congr_at {k l : ℕ} (dtable dn : Code k) (dtable' dn' : Code l)
    (z : M) (v : Fin k → M) (v' : Fin l → M)
    (hT :
      ∀ x : M,
        Semiformula.Evalb (x :> v) (code dtable) ↔ Semiformula.Evalb (x :> v') (code dtable'))
    (hN :
      ∀ x : M, Semiformula.Evalb (x :> v) (code dn) ↔ Semiformula.Evalb (x :> v') (code dn')) :
    Semiformula.Evalb (z :> v) (code (codeEvaluatorCell dtable dn)) ↔
      Semiformula.Evalb (z :> v') (code (codeEvaluatorCell dtable' dn')) :=
  by
  have hcell : EvalEq (codeEvaluatorCell dtable dn) v (codeEvaluatorCell dtable' dn') v' :=
    by
    simp only [codeEvaluatorCell]
    have hp := evalEq_codeListLength hT
    have hk := evalEq_codeUnpair₁ hp
    have hk' := evalEq_codeSub hk (evalEq_codeConst 1 v v')
    have hq := evalEq_codeUnpair₂ hp
    have htag := evalEq_codePartrecTag hq
    exact
      evalEq_codeIfPos hk
        (evalEq_codeIfPos (evalEq_codeEq htag (evalEq_codeConst 4 v v'))
          (evalEq_codePairEvaluatorCell hT hk (evalEq_codePartrecPayload₁ hq)
            (evalEq_codePartrecPayload₂ hq) hN)
          (evalEq_codeIfPos (evalEq_codeEq htag (evalEq_codeConst 5 v v'))
            (evalEq_codeCompEvaluatorCell hT hk (evalEq_codePartrecPayload₁ hq)
              (evalEq_codePartrecPayload₂ hq) hN)
            (evalEq_codeIfPos (evalEq_codeEq htag (evalEq_codeConst 6 v v'))
              (evalEq_codePrecEvaluatorCell hT hk' hq (evalEq_codePartrecPayload₁ hq)
                (evalEq_codePartrecPayload₂ hq) hN)
              (evalEq_codeIfPos (evalEq_codeEq htag (evalEq_codeConst 7 v v'))
                (evalEq_codeRfindEvaluatorCell hT hk' hq (evalEq_codePartrecPayload hq) hN)
                (evalEq_codeBaseEvaluatorCell hT hN)))))
        (evalEq_codeConst 0 v v')
  exact hcell z

end Evaluator
end CategoricalRiceShapiro

end

end PointwiseComposition
