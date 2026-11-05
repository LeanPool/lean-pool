/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.Recursion
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.Evaluation
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.EvaluationCongruence
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.NumeralEvaluation
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.BetaCoding
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.Schemata

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Evaluation properties of primitive-recursion codes

`codePrecStep dg` is the step relation of `codePrec`.  It has `n + 3`
arguments: the history index, the history code, the recursion argument, and the
`n` outer arguments.  It never reads argument `2`, the recursion argument:
`precStepArgs` supplies `Code.proj 0`, `codeBeta (Code.proj 1) (Code.proj 0)`,
and the outer projections, none of which is `Code.proj 2`.

`eval_codePrecStep_bound_irrel_iff` records that, so a caller may change the
recursion argument without disturbing the step relation.  The proof is
structural: `InputsAgree` is a conservative dependency relation on the nine
`Code` constructors, and `eval_iff_of_inputsAgree` turns it into an equivalence
of evaluations.

The proof of `eval_codePrecStep_bound_irrel_iff` does not evaluate `codeBeta`
or any other derived constructor in the model.  It inspects those codes only as
syntax trees and assumes no arithmetic theory: `ORingStructure M` alone.  The
existence theorem below instead uses arithmetic evaluation and beta extension
under `𝐏𝐀`.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace ArithmeticCode

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

section Syntactic

variable {M : Type*}

/-!
### A conservative dependency relation -/

/-- `InputsAgree c v v'` is a sufficient syntactic condition for `c` to evaluate the
same way under the two assignments.

The `comp` clause is the delicate one.  `Code.comp c d` evaluates **every**
argument code `d i`, and an argument may be partial, so an argument may not be
ignored merely because the outer code does not read its position.  Each argument
is therefore classified by `src`:

* `src i = some s` records that `d i` is the projection `Code.proj s`.
  Projections are total, so this argument contributes `v s` on one side and
  `v' s` on the other, and the two intermediate vectors may genuinely differ
  there.
* `src i = none` requires `d i` to agree outright, so it contributes one shared
  value to both intermediate vectors.

The outer code must then agree under the two assembled vectors, for every choice
of the shared values.  Both alternatives are needed:
`codeLift d = d.comp (fun i => Code.proj i.succ)` is all projections, and
`codeBind dg dc = dc.comp (Fin.cases dg fun i => Code.proj i)` mixes one
agreeing argument with projections.
-/
private noncomputable def InputsAgree : {k : ℕ} → Code k → (Fin k → M) → (Fin k → M) → Prop
  | _, .zero _, _, _ => True
  | _, .one _, _, _ => True
  | _, .add i j, v, v' => v i = v' i ∧ v j = v' j
  | _, .mul i j, v, v' => v i = v' i ∧ v j = v' j
  | _, .proj i, v, v' => v i = v' i
  | _, .equal i j, v, v' => v i = v' i ∧ v j = v' j
  | _, .lt i j, v, v' => v i = v' i ∧ v j = v' j
  | m, @Code.comp _ n c d, v, v' =>
    ∃ src : Fin n → Option (Fin m),
      (∀ i s, src i = some s → d i = Code.proj s) ∧
        (∀ i, src i = none → InputsAgree (d i) v v') ∧
          ∀ u : Fin n → M,
            InputsAgree c (fun i => (src i).elim (u i) v) (fun i => (src i).elim (u i) v')
  | _, .rfind body, v, v' => ∀ t : M, InputsAgree body (t :> v) (t :> v')

end Syntactic

section Semantic

variable {M : Type*} [ORingStructure M]

/-!
### Evaluation respects the dependency relation -/

/-- `code` differs from `codeAux` by a renaming that evaluation absorbs. -/
private theorem evalb_iff_evalf {k : ℕ} (c : Code k) (z : M) (w : Fin k → M) :
    Semiformula.Evalb (z :> w) (code c) ↔ Semiformula.Evalf (M := M) (z :> w) (codeAux c) := by
  simp [code, Semiformula.eval_rew, Matrix.empty_eq, Function.comp_def]

/-- Evaluation of a search for a zero.  Kept private: an identical
characterisation is already private to
`CategoricalRiceShapiro.ArithmeticCode.EvaluationCongruence`, which this module
cannot see. -/
private theorem eval_rfind_iff' {k : ℕ} (c : Code (k + 1)) (z : M) (v : Fin k → M) :
    Semiformula.Evalb (z :> v) (code (Code.rfind c)) ↔
      (Semiformula.Evalb ((0 : M) :> z :> v) (code c) ∧
        ∀ t : M, t < z → ∃ x : M, x ≠ 0 ∧ Semiformula.Evalb (x :> t :> v) (code c)) :=
  by
  simp only [evalb_iff_evalf]
  simp [codeAux, Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons']

/-- Agreeing inputs give equivalent evaluations. -/
private theorem eval_iff_of_inputsAgree :
    ∀ {k : ℕ} (c : Code k) (z : M) (v v' : Fin k → M),
      InputsAgree c v v' →
        (Semiformula.Evalb (z :> v) (code c) ↔ Semiformula.Evalb (z :> v') (code c)) :=
  by
  intro k c
  induction c with
  | zero m => intro z v v' _; rw [eval_zero_iff, eval_zero_iff]
  | one m => intro z v v' _; rw [eval_one_iff, eval_one_iff]
  | add i j =>
    intro z v v' h
    rw [InputsAgree] at h
    rw [eval_add_iff, eval_add_iff, h.1, h.2]
  | mul i j =>
    intro z v v' h
    rw [InputsAgree] at h
    rw [eval_mul_iff, eval_mul_iff, h.1, h.2]
  | proj i =>
    intro z v v' h
    rw [InputsAgree] at h
    rw [eval_proj_iff, eval_proj_iff, h]
  | equal i j =>
    intro z v v' h
    rw [InputsAgree] at h
    rw [eval_equal_iff, eval_equal_iff, h.1, h.2]
  | lt i j =>
    intro z v v' h
    rw [InputsAgree] at h
    rw [eval_lt_iff, eval_lt_iff, h.1, h.2]
  | comp c d ihc ihd =>
    intro z v v' h
    rw [InputsAgree] at h
    obtain ⟨src, hproj, hagree, houter⟩ := h
    rw [eval_comp_iff, eval_comp_iff]
    constructor
    · rintro ⟨w, hw, hi⟩
      have hwv : w = fun i => (src i).elim (w i) v :=
        by
        funext i
        cases hsi : src i with
        | none => simp
        | some t =>
          have hd := hi i
          rw [hproj i t hsi, eval_proj_iff] at hd
          simp [hd]
      refine ⟨fun i => (src i).elim (w i) v', ?_, ?_⟩
      · rw [hwv] at hw
        exact (ihc z _ _ (houter w)).mp hw
      · intro i
        cases hsi : src i with
        | none =>
          simp only [hsi, Option.elim]
          exact (ihd i (w i) v v' (hagree i hsi)).mp (hi i)
        | some t =>
          rw [hproj i t hsi, eval_proj_iff]
          simp [hsi]
    · rintro ⟨w, hw, hi⟩
      have hwv : w = fun i => (src i).elim (w i) v' :=
        by
        funext i
        cases hsi : src i with
        | none => simp
        | some t =>
          have hd := hi i
          rw [hproj i t hsi, eval_proj_iff] at hd
          simp [hd]
      refine ⟨fun i => (src i).elim (w i) v, ?_, ?_⟩
      · rw [hwv] at hw
        exact (ihc z _ _ (houter w)).mpr hw
      · intro i
        cases hsi : src i with
        | none =>
          simp only [hsi, Option.elim]
          exact (ihd i (w i) v v' (hagree i hsi)).mpr (hi i)
        | some t =>
          rw [hproj i t hsi, eval_proj_iff]
          simp [hsi]
  | rfind body ih =>
    intro z v v' h
    rw [InputsAgree] at h
    rw [eval_rfind_iff', eval_rfind_iff']
    refine and_congr (ih 0 (z :> v) (z :> v') (h z)) ?_
    refine forall_congr' fun t => imp_congr Iff.rfl ?_
    exact exists_congr fun x => and_congr Iff.rfl (ih x (t :> v) (t :> v') (h t))

end Semantic

section Closure

variable {M : Type*}

/-!
### Closure of the dependency relation under the derived constructors

Each lemma below inspects a code as a syntax tree only.  No arithmetic meaning
is attached to any of them, and `codeBeta` in particular is delta-reduced but
never evaluated. -/

/-- Every code agrees with itself. -/
private theorem inputsAgree_refl : ∀ {k : ℕ} (c : Code k) (v : Fin k → M), InputsAgree c v v :=
  by
  intro k c
  induction c with
  | zero m => intro v; rw [InputsAgree]; trivial
  | one m => intro v; rw [InputsAgree]; trivial
  | add i j => intro v; rw [InputsAgree]; exact ⟨rfl, rfl⟩
  | mul i j => intro v; rw [InputsAgree]; exact ⟨rfl, rfl⟩
  | proj i => intro v; rw [InputsAgree]
  | equal i j => intro v; rw [InputsAgree]; exact ⟨rfl, rfl⟩
  | lt i j => intro v; rw [InputsAgree]; exact ⟨rfl, rfl⟩
  | comp c d ihc ihd =>
    intro v
    rw [InputsAgree]
    exact ⟨fun _ => none, by simp, fun i _ => ihd i v, fun u => by simpa using ihc u⟩
  | rfind body ih => intro v; rw [InputsAgree]; exact fun t => ih (t :> v)

/-- A composition all of whose arguments agree. -/
private theorem inputsAgree_comp_of_all {m n : ℕ} (c : Code n) (d : Fin n → Code m)
    (v v' : Fin m → M) (hd : ∀ i, InputsAgree (d i) v v') : InputsAgree (Code.comp c d) v v' :=
  by
  rw [InputsAgree]
  exact ⟨fun _ => none, by simp, fun i _ => hd i, fun u => by simpa using inputsAgree_refl c u⟩

private theorem inputsAgree_comp₂ {k : ℕ} (c : Code 2) (d₀ d₁ : Code k) (v v' : Fin k → M)
    (h₀ : InputsAgree d₀ v v') (h₁ : InputsAgree d₁ v v') :
    InputsAgree (Code.comp c ![d₀, d₁]) v v' :=
  by
  refine inputsAgree_comp_of_all c _ v v' ?_
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using h₀
  · refine Fin.cases ?_ (fun j' => j'.elim0) j
    simpa using h₁

private theorem inputsAgree_zero {k : ℕ} (v v' : Fin k → M) : InputsAgree (Code.zero k) v v' :=
  by rw [InputsAgree]; trivial

private theorem inputsAgree_one {k : ℕ} (v v' : Fin k → M) : InputsAgree (Code.one k) v v' := by
  rw [InputsAgree]; trivial

private theorem inputsAgree_proj {k : ℕ} (i : Fin k) (v v' : Fin k → M) (h : v i = v' i) :
    InputsAgree (Code.proj i) v v' := by rw [InputsAgree]; exact h

private theorem inputsAgree_codeHead {k : ℕ} (t : M) (v v' : Fin k → M) :
    InputsAgree (codeHead (n := k)) (t :> v) (t :> v') :=
  inputsAgree_proj 0 _ _ rfl

private theorem inputsAgree_codeAdd {k : ℕ} (d₀ d₁ : Code k) (v v' : Fin k → M)
    (h₀ : InputsAgree d₀ v v') (h₁ : InputsAgree d₁ v v') : InputsAgree (codeAdd d₀ d₁) v v' :=
  inputsAgree_comp₂ _ _ _ v v' h₀ h₁

private theorem inputsAgree_codeMul {k : ℕ} (d₀ d₁ : Code k) (v v' : Fin k → M)
    (h₀ : InputsAgree d₀ v v') (h₁ : InputsAgree d₁ v v') : InputsAgree (codeMul d₀ d₁) v v' :=
  inputsAgree_comp₂ _ _ _ v v' h₀ h₁

private theorem inputsAgree_codeEq {k : ℕ} (d₀ d₁ : Code k) (v v' : Fin k → M)
    (h₀ : InputsAgree d₀ v v') (h₁ : InputsAgree d₁ v v') : InputsAgree (codeEq d₀ d₁) v v' :=
  inputsAgree_comp₂ _ _ _ v v' h₀ h₁

private theorem inputsAgree_codeLt {k : ℕ} (d₀ d₁ : Code k) (v v' : Fin k → M)
    (h₀ : InputsAgree d₀ v v') (h₁ : InputsAgree d₁ v v') : InputsAgree (codeLt d₀ d₁) v v' :=
  inputsAgree_comp₂ _ _ _ v v' h₀ h₁

private theorem inputsAgree_codeSucc {k : ℕ} (d : Code k) (v v' : Fin k → M)
    (h : InputsAgree d v v') : InputsAgree (codeSucc d) v v' :=
  inputsAgree_comp₂ _ _ _ v v' h (inputsAgree_one v v')

private theorem inputsAgree_codeInv {k : ℕ} (d : Code k) (v v' : Fin k → M)
    (h : InputsAgree d v v') : InputsAgree (codeInv d) v v' :=
  inputsAgree_comp₂ _ _ _ v v' h (inputsAgree_zero v v')

private theorem inputsAgree_codePos {k : ℕ} (d : Code k) (v v' : Fin k → M)
    (h : InputsAgree d v v') : InputsAgree (codePos d) v v' :=
  inputsAgree_comp₂ _ _ _ v v' (inputsAgree_zero v v') h

private theorem inputsAgree_codeAnd {k : ℕ} (d₀ d₁ : Code k) (v v' : Fin k → M)
    (h₀ : InputsAgree d₀ v v') (h₁ : InputsAgree d₁ v v') : InputsAgree (codeAnd d₀ d₁) v v' :=
  inputsAgree_comp₂ _ _ _ v v' (inputsAgree_zero v v') (inputsAgree_comp₂ _ _ _ v v' h₀ h₁)

private theorem inputsAgree_codeOr {k : ℕ} (d₀ d₁ : Code k) (v v' : Fin k → M)
    (h₀ : InputsAgree d₀ v v') (h₁ : InputsAgree d₁ v v') : InputsAgree (codeOr d₀ d₁) v v' :=
  inputsAgree_comp₂ _ _ _ v v' (inputsAgree_zero v v') (inputsAgree_comp₂ _ _ _ v v' h₀ h₁)

private theorem inputsAgree_codeConst {k : ℕ} (m : ℕ) (v v' : Fin k → M) :
    InputsAgree (codeConst (n := k) m) v v' := by
  induction m with
  | zero => exact inputsAgree_zero v v'
  | succ p ih => exact inputsAgree_codeSucc _ v v' ih

/-- A lift is a renaming, so it transports without demanding agreement at the
head. -/
private theorem inputsAgree_codeLift {k : ℕ} (d : Code k) (t : M) (v v' : Fin k → M)
    (h : InputsAgree d v v') : InputsAgree (codeLift d) (t :> v) (t :> v') :=
  by
  rw [codeLift, InputsAgree]
  refine ⟨fun i => some i.succ, fun i s hs => ?_, fun i hs => by simp at hs, fun u => ?_⟩
  · cases hs; rfl
  · have e : (fun i => Option.elim (some i.succ) (u i) (t :> v)) = v := by funext i; simp
    have e' : (fun i => Option.elim (some i.succ) (u i) (t :> v')) = v' := by funext i; simp
    rw [e, e']
    exact h

private theorem inputsAgree_codeRfindPos {k : ℕ} (d : Code (k + 1)) (v v' : Fin k → M)
    (h : ∀ t : M, InputsAgree d (t :> v) (t :> v')) : InputsAgree (codeRfindPos d) v v' :=
  by
  rw [codeRfindPos, InputsAgree]
  intro t
  exact inputsAgree_codeInv _ _ _ (inputsAgree_codePos _ _ _ (h t))

/-- Substitution keeps one shared value and renames the rest. -/
private theorem inputsAgree_codeBind {k : ℕ} (dg : Code k) (dc : Code (k + 1))
    (v v' : Fin k → M) (hg : InputsAgree dg v v')
    (hc : ∀ x : M, InputsAgree dc (x :> v) (x :> v')) : InputsAgree (codeBind dg dc) v v' :=
  by
  rw [codeBind, InputsAgree]
  refine ⟨Fin.cases none (fun i => some i), ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro s hs; simp at hs
    · intro s hs
      simp only [Fin.cases_succ] at hs ⊢
      injection hs with hs'
      subst hs'
      rfl
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro _; simpa using hg
    · intro hs
      simp only [Fin.cases_succ] at hs
      cases hs
  · intro u
    have e :
      ∀ w : Fin k → M,
        (fun i => Option.elim (Fin.cases none (fun j => some j) i) (u i) w) = (u 0 :> w) :=
      by
      intro w
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [e v, e v']
    exact hc (u 0)

private theorem inputsAgree_codeSub {k : ℕ} (d₀ d₁ : Code k) (v v' : Fin k → M)
    (h₀ : InputsAgree d₀ v v') (h₁ : InputsAgree d₁ v v') : InputsAgree (codeSub d₀ d₁) v v' :=
  by
  rw [codeSub]
  refine inputsAgree_codeRfindPos _ v v' (fun t => ?_)
  exact
    inputsAgree_codeOr _ _ _ _
      (inputsAgree_codeEq _ _ _ _
        (inputsAgree_codeAdd _ _ _ _ (inputsAgree_codeHead t v v')
          (inputsAgree_codeLift _ t v v' h₁))
        (inputsAgree_codeLift _ t v v' h₀))
      (inputsAgree_codeAnd _ _ _ _
        (inputsAgree_codeLt _ _ _ _ (inputsAgree_codeLift _ t v v' h₀)
          (inputsAgree_codeLift _ t v v' h₁))
        (inputsAgree_codeEq _ _ _ _ (inputsAgree_codeHead t v v') (inputsAgree_zero _ _)))

private theorem inputsAgree_codeSqrt {k : ℕ} (d : Code k) (v v' : Fin k → M)
    (h : InputsAgree d v v') : InputsAgree (codeSqrt d) v v' :=
  by
  rw [codeSqrt]
  refine inputsAgree_codeRfindPos _ v v' (fun t => ?_)
  exact
    inputsAgree_codeAnd _ _ _ _
      (inputsAgree_codeOr _ _ _ _
        (inputsAgree_codeLt _ _ _ _
          (inputsAgree_codeMul _ _ _ _ (inputsAgree_codeHead t v v')
            (inputsAgree_codeHead t v v'))
          (inputsAgree_codeLift _ t v v' h))
        (inputsAgree_codeEq _ _ _ _
          (inputsAgree_codeMul _ _ _ _ (inputsAgree_codeHead t v v')
            (inputsAgree_codeHead t v v'))
          (inputsAgree_codeLift _ t v v' h)))
      (inputsAgree_codeLt _ _ _ _ (inputsAgree_codeLift _ t v v' h)
        (inputsAgree_codeMul _ _ _ _ (inputsAgree_codeSucc _ _ _ (inputsAgree_codeHead t v v'))
          (inputsAgree_codeSucc _ _ _ (inputsAgree_codeHead t v v'))))

private theorem inputsAgree_codeIfPos {k : ℕ} (df dg dh : Code k) (v v' : Fin k → M)
    (hf : InputsAgree df v v') (hg : InputsAgree dg v v') (hh : InputsAgree dh v v') :
    InputsAgree (codeIfPos df dg dh) v v' :=
  by
  rw [codeIfPos]
  exact
    inputsAgree_codeAdd _ _ _ _ (inputsAgree_codeMul _ _ _ _ (inputsAgree_codePos _ _ _ hf) hg)
      (inputsAgree_codeMul _ _ _ _ (inputsAgree_codeInv _ _ _ hf) hh)

private theorem inputsAgree_codeLe {k : ℕ} (d₀ d₁ : Code k) (v v' : Fin k → M)
    (h₀ : InputsAgree d₀ v v') (h₁ : InputsAgree d₁ v v') : InputsAgree (codeLe d₀ d₁) v v' :=
  by
  rw [codeLe]
  exact
    inputsAgree_codeOr _ _ _ _ (inputsAgree_codeLt _ _ _ _ h₀ h₁)
      (inputsAgree_codeEq _ _ _ _ h₀ h₁)

private theorem inputsAgree_codeUnpair₁ {k : ℕ} (d : Code k) (v v' : Fin k → M)
    (h : InputsAgree d v v') : InputsAgree (codeUnpair₁ d) v v' :=
  by
  rw [codeUnpair₁]
  have hsq := inputsAgree_codeSqrt d v v' h
  have hdiff := inputsAgree_codeSub _ _ v v' h (inputsAgree_codeMul _ _ _ _ hsq hsq)
  exact inputsAgree_codeIfPos _ _ _ v v' (inputsAgree_codeLt _ _ _ _ hdiff hsq) hdiff hsq

private theorem inputsAgree_codeUnpair₂ {k : ℕ} (d : Code k) (v v' : Fin k → M)
    (h : InputsAgree d v v') : InputsAgree (codeUnpair₂ d) v v' :=
  by
  rw [codeUnpair₂]
  have hsq := inputsAgree_codeSqrt d v v' h
  have hdiff := inputsAgree_codeSub _ _ v v' h (inputsAgree_codeMul _ _ _ _ hsq hsq)
  exact
    inputsAgree_codeIfPos _ _ _ v v' (inputsAgree_codeLt _ _ _ _ hdiff hsq) hsq
      (inputsAgree_codeSub _ _ v v' hdiff hsq)

private theorem inputsAgree_codeDvd {k : ℕ} (d₀ d₁ : Code k) (v v' : Fin k → M)
    (h₀ : InputsAgree d₀ v v') (h₁ : InputsAgree d₁ v v') : InputsAgree (codeDvd d₀ d₁) v v' :=
  by
  rw [codeDvd]
  refine inputsAgree_codeBind _ _ v v' ?_ (fun x => ?_)
  · refine inputsAgree_codeRfindPos _ v v' (fun t => ?_)
    exact
      inputsAgree_codeOr _ _ _ _
        (inputsAgree_codeEq _ _ _ _
          (inputsAgree_codeMul _ _ _ _ (inputsAgree_codeHead t v v')
            (inputsAgree_codeLift _ t v v' h₀))
          (inputsAgree_codeLift _ t v v' h₁))
        (inputsAgree_codeLt _ _ _ _ (inputsAgree_codeLift _ t v v' h₁)
          (inputsAgree_codeHead t v v'))
  · exact
      inputsAgree_codeLe _ _ _ _ (inputsAgree_codeHead x v v')
        (inputsAgree_codeLift _ x v v' h₁)

private theorem inputsAgree_codeRem {k : ℕ} (d₀ d₁ : Code k) (v v' : Fin k → M)
    (h₀ : InputsAgree d₀ v v') (h₁ : InputsAgree d₁ v v') : InputsAgree (codeRem d₀ d₁) v v' :=
  by
  rw [codeRem]
  refine inputsAgree_codeRfindPos _ v v' (fun t => ?_)
  exact
    inputsAgree_codeDvd _ _ _ _ (inputsAgree_codeLift _ t v v' h₁)
      (inputsAgree_codeSub _ _ _ _ (inputsAgree_codeLift _ t v v' h₀)
        (inputsAgree_codeHead t v v'))

/-- `codeBeta` is delta-reduced here as a syntax tree; nothing evaluates it. -/
private theorem inputsAgree_codeBeta {k : ℕ} (dn di : Code k) (v v' : Fin k → M)
    (hn : InputsAgree dn v v') (hi : InputsAgree di v v') : InputsAgree (codeBeta dn di) v v' :=
  by
  rw [codeBeta]
  exact
    inputsAgree_codeRem _ _ v v' (inputsAgree_codeUnpair₁ _ _ _ hn)
      (inputsAgree_codeSucc _ _ _
        (inputsAgree_codeMul _ _ _ _ (inputsAgree_codeSucc _ _ _ hi)
          (inputsAgree_codeUnpair₂ _ _ _ hn)))

/-!
### The recursion argument is unused by the step relation -/

/-- Every argument `precStepArgs` supplies to `dg` ignores input slot `2`: the
first and the outer ones are projections away from it, and the second is a
`codeBeta` whose own two arguments are `Code.proj 1` and `Code.proj 0`.  The
outer `dg` is never inspected; it is applied to two assembled vectors that are
equal. -/
private theorem inputsAgree_codePrecStep_bound {n : ℕ} (dg : Code (n + 2)) (j hc c c' : M)
    (v : Fin n → M) : InputsAgree (codePrecStep dg) (j :> hc :> c :> v) (j :> hc :> c' :> v) :=
  by
  have hstep :
    codePrecStep dg =
      codeEq (codeBeta (Code.proj 1) (codeSucc (Code.proj 0)))
        (dg.comp
          (Fin.cases (Code.proj 0)
            (Fin.cases (codeBeta (Code.proj 1) (Code.proj 0))
              (fun i => Code.proj i.succ.succ.succ)))) :=
    rfl
  rw [hstep]
  refine inputsAgree_codeEq _ _ _ _ ?_ ?_
  · exact
      inputsAgree_codeBeta _ _ _ _ (inputsAgree_proj 1 _ _ rfl)
        (inputsAgree_codeSucc _ _ _ (inputsAgree_proj 0 _ _ rfl))
  · rw [InputsAgree]
    refine ⟨Fin.cases (some 0) (Fin.cases none (fun i => some i.succ.succ.succ)), ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · intro s hs
        simp only [Fin.cases_zero] at hs
        injection hs with hs'
        subst hs'
        rfl
      · refine Fin.cases ?_ (fun l => ?_) k
        · intro s hs
          simp only [Fin.cases_succ, Fin.cases_zero] at hs
          cases hs
        · intro s hs
          simp only [Fin.cases_succ] at hs ⊢
          injection hs with hs'
          subst hs'
          rfl
    · intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · intro hs
        simp only [Fin.cases_zero] at hs
        cases hs
      · refine Fin.cases ?_ (fun l => ?_) k
        · intro _
          simp only [Fin.cases_succ, Fin.cases_zero]
          exact
            inputsAgree_codeBeta _ _ _ _ (inputsAgree_proj 1 _ _ rfl)
              (inputsAgree_proj 0 _ _ rfl)
        · intro hs
          simp only [Fin.cases_succ] at hs
          cases hs
    · intro u
      have e :
        (fun i =>
            Option.elim (Fin.cases (some 0) (Fin.cases none (fun i => some i.succ.succ.succ)) i)
              (u i) (j :> hc :> c :> v)) =
          (fun i =>
            Option.elim (Fin.cases (some 0) (Fin.cases none (fun i => some i.succ.succ.succ)) i)
              (u i) (j :> hc :> c' :> v)) :=
        by
        funext i
        refine Fin.cases ?_ (fun k => ?_) i
        · rfl
        · refine Fin.cases ?_ (fun l => ?_) k
          · rfl
          · rfl
      rw [e]
      exact inputsAgree_refl dg _

/-!
### Bound irrelevance for the base conjunct of the recursion predicate -/

/-- The base equation of `codePrecPredicate` reads the history code and the
outer arguments, never the recursion argument. -/
private theorem inputsAgree_precBase_bound {k : ℕ} (df : Code k) (hc c c' : M) (v : Fin k → M) :
    InputsAgree
      (codeEq (codeBeta (Code.proj 0) (codeConst 0)) (df.comp (fun j => Code.proj j.succ.succ)))
      (hc :> c :> v) (hc :> c' :> v) :=
  by
  refine inputsAgree_codeEq _ _ _ _ ?_ ?_
  · exact
      inputsAgree_codeBeta _ _ _ _ (inputsAgree_proj 0 _ _ rfl) (inputsAgree_codeConst 0 _ _)
  · rw [InputsAgree]
    refine ⟨fun j => some j.succ.succ, ?_, ?_, ?_⟩
    · intro i s hs
      cases hs
      rfl
    · intro i hs
      cases hs
    · intro u
      have e :
        ∀ w : Fin k → M, (fun j => Option.elim (some j.succ.succ) (u j) (hc :> c :> w)) = w :=
        by intro w; funext j; simp
      have e' : (fun j => Option.elim (some j.succ.succ) (u j) (hc :> c' :> v)) = v := by
        funext j; simp
      rw [e v, e']
      exact inputsAgree_refl df v

end Closure

section Endpoint

variable {M : Type*} [ORingStructure M]

/-- The step relation of `codePrec` does not read the recursion argument.

The arguments of `codePrecStep dg` are the history index, the history code, the
recursion argument, and the outer arguments.  Argument `2`, the recursion
argument, is supplied to nothing: `precStepArgs` hands `dg` only
`Code.proj 0`, `codeBeta (Code.proj 1) (Code.proj 0)`, and the outer
projections.  A caller may therefore change it freely.

No arithmetic theory is assumed, and no code is evaluated in the model. -/
theorem eval_codePrecStep_bound_irrel_iff {n : ℕ} (dg : Code (n + 2)) (p j hc c c' : M)
    (v : Fin n → M) :
    Semiformula.Evalb (p :> j :> hc :> c :> v) (code (codePrecStep dg)) ↔
      Semiformula.Evalb (p :> j :> hc :> c' :> v) (code (codePrecStep dg)) :=
  eval_iff_of_inputsAgree _ p _ _ (inputsAgree_codePrecStep_bound dg j hc c c' v)

end Endpoint

section Restriction

variable {M : Type*} [ORingStructure M]

open scoped FFL.FirstOrder.Arithmetic

open HierarchySymbol

/-- The base equation of `codePrecPredicate`, at two recursion arguments. -/
private theorem eval_precBase_bound_irrel_iff {k : ℕ} (df : Code k) (p hc c c' : M)
    (v : Fin k → M) :
    Semiformula.Evalb (p :> hc :> c :> v)
        (code
          (codeEq (codeBeta (Code.proj 0) (codeConst 0))
            (df.comp (fun j => Code.proj j.succ.succ)))) ↔
      Semiformula.Evalb (p :> hc :> c' :> v)
        (code
          (codeEq (codeBeta (Code.proj 0) (codeConst 0))
            (df.comp (fun j => Code.proj j.succ.succ)))) :=
  eval_iff_of_inputsAgree _ p _ _ (inputsAgree_precBase_bound df hc c c' v)

/-- `codePrecStep` written out, with the argument codes of the step displayed
explicitly rather than through the private abbreviation of `Recursion`. -/
private theorem codePrecStep_eq {n : ℕ} (dg : Code (n + 2)) :
    codePrecStep dg =
      codeEq (codeBeta (Code.proj 1) (codeSucc (Code.proj 0)))
        (dg.comp
          (Fin.cases (Code.proj 0)
            (Fin.cases (codeBeta (Code.proj 1) (Code.proj 0))
              (fun j => Code.proj j.succ.succ.succ)))) :=
  rfl

/-- `codePrecPredicate` written out, with the base conjunct in the explicit form
the bound-irrelevance lemma above uses. -/
private theorem codePrecPredicate_eq {k : ℕ} (df : Code k) (dg : Code (k + 2)) :
    codePrecPredicate df dg =
      codeAnd
        (codeEq (codeBeta (Code.proj 0) (codeConst 0))
          (df.comp (fun j => Code.proj j.succ.succ)))
        (codeBall (codePrecStep dg) (1 : Fin (k + 2))) :=
  rfl

private theorem eq_zero_of_not_pos_add [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {x y : M} (h : ¬(0 : M) < x + y) :
    x = 0 := by
  have hsum : x + y = 0 := le_antisymm (not_lt.mp h) (by simp)
  have hx : x ≤ 0 := hsum ▸ le_self_add
  exact le_antisymm hx (by simp)

private theorem pos_of_pos_mul_left [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {x y : M} (h : 0 < x * y) : 0 < x :=
  by
  rcases eq_or_lt_of_le (show (0 : M) ≤ x from by simp) with h0 | hpos
  · rw [← h0, zero_mul] at h; exact absurd h (_root_.lt_irrefl 0)
  · exact hpos

private theorem pos_of_pos_mul_right [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {x y : M} (h : 0 < x * y) : 0 < y :=
  by
  rcases eq_or_lt_of_le (show (0 : M) ≤ y from by simp) with h0 | hpos
  · rw [← h0, mul_zero] at h; exact absurd h (_root_.lt_irrefl 0)
  · exact hpos

/-- Elimination for the non-strict comparison. -/
private theorem le_val_cases [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {m : ℕ} (A B : Code m) (x y zz : M)
    (vv : Fin m → M) (hA : Semiformula.Evalb (x :> vv) (code A))
    (hB : Semiformula.Evalb (y :> vv) (code B))
    (hz : Semiformula.Evalb (zz :> vv) (code (codeLe A B))) :
    (x ≤ y ∧ zz = 1) ∨ (¬x ≤ y ∧ zz = 0) :=
  by
  rw [codeLe, eval_codeOr_iff] at hz
  obtain ⟨p, q, hp, hq, hcase⟩ := hz
  rw [eval_codeLt_iff] at hp
  obtain ⟨x1, y1, hx1, hy1, hlt⟩ := hp
  rw [eval_codeEq_iff] at hq
  obtain ⟨x2, y2, hx2, hy2, heq⟩ := hq
  rw [eval_unique hx1 hA, eval_unique hy1 hB] at hlt
  rw [eval_unique hx2 hA, eval_unique hy2 hB] at heq
  by_cases hxy : x ≤ y
  · refine Or.inl ⟨hxy, ?_⟩
    have hpos : 0 < p + q := by
      rcases lt_or_eq_of_le hxy with hx | hx
      · rcases hlt with ⟨-, rfl⟩ | ⟨hn, -⟩
        · rcases heq with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
        · exact absurd hx hn
      · rcases heq with ⟨-, rfl⟩ | ⟨hn, -⟩
        · rcases hlt with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
        · exact absurd hx hn
    rcases hcase with ⟨-, hz1⟩ | ⟨hn, -⟩
    · exact hz1
    · exact absurd hpos hn
  · refine Or.inr ⟨hxy, ?_⟩
    have hp0 : p = 0 := by
      rcases hlt with ⟨hx, -⟩ | ⟨-, hp0⟩
      · exact absurd (le_of_lt hx) hxy
      · exact hp0
    have hq0 : q = 0 := by
      rcases heq with ⟨hx, -⟩ | ⟨-, hq0⟩
      · exact absurd (le_of_eq hx) hxy
      · exact hq0
    rcases hcase with ⟨hpos, -⟩ | ⟨-, hz0⟩
    · rw [hp0, hq0] at hpos; exact absurd hpos (by simp)
    · exact hz0

/-- A zero disjunction hands back the body. -/
private theorem body_of_or_zero [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (dg : Code (k + 2)) (t hc arg : M)
    (v : Fin k → M)
    (h :
      Semiformula.Evalb ((0 : M) :> t :> hc :> arg :> v)
        (code
          (codeOr (codeInv (codePrecStep dg))
            (codeLe (codeLift (Code.proj (1 : Fin (k + 2)))) (codeHead (n := k + 2)))))) :
    ∃ e : M, e ≠ 0 ∧ Semiformula.Evalb (e :> t :> hc :> arg :> v) (code (codePrecStep dg)) :=
  by
  rw [eval_codeOr_iff] at h
  obtain ⟨p', q', hp', hq', hc'⟩ := h
  have hp'0 : p' = 0 := by
    rcases hc' with ⟨-, h01⟩ | ⟨hnp, -⟩
    · exact absurd h01.symm _root_.one_ne_zero
    · exact eq_zero_of_not_pos_add hnp
  rw [hp'0, eval_codeInv_iff] at hp'
  obtain ⟨e, he, hecase⟩ := hp'
  rcases hecase with ⟨-, h01⟩ | ⟨hne, -⟩
  · exact absurd h01.symm _root_.one_ne_zero
  · exact ⟨e, hne, he⟩

/-- A successful bounded search hands back the body at every earlier index. -/
private theorem ball_body_of_pos [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (dg : Code (k + 2)) (y hc arg : M)
    (v : Fin k → M) (hy : 0 < y)
    (h :
      Semiformula.Evalb (y :> hc :> arg :> v)
        (code (codeBall (codePrecStep dg) (1 : Fin (k + 2))))) :
    ∀ t : M,
      t < arg →
        ∃ e : M,
          e ≠ 0 ∧ Semiformula.Evalb (e :> t :> hc :> arg :> v) (code (codePrecStep dg)) :=
  by
  rw [codeBall, eval_codeBind_iff] at h
  obtain ⟨j, hsearch, heq⟩ := h
  rw [eval_codeEq_iff] at heq
  obtain ⟨p, q, hp, hq, hcase⟩ := heq
  rw [eval_codeHead_iff] at hp
  rw [eval_codeLift_iff, eval_proj_iff] at hq
  have hja : j = arg := by
    rcases hcase with ⟨hpq, -⟩ | ⟨-, hy0⟩
    · exact hp.symm.trans (hpq.trans hq)
    · exact absurd hy0 (ne_of_gt hy)
  rw [eval_codeRfindPos_iff] at hsearch
  obtain ⟨-, hmin⟩ := hsearch
  intro t ht
  exact body_of_or_zero dg t hc arg v (hmin t (by rw [hja]; exact ht))

/-- Conversely, a body holding at every index up to the bound makes the bounded
search succeed, with the bound itself as the witness. -/
private theorem ball_pos_of_body [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (dg : Code (k + 2)) (hc arg : M)
    (v : Fin k → M)
    (hbody :
      ∀ t : M,
        t ≤ arg →
          ∃ e : M,
            e ≠ 0 ∧ Semiformula.Evalb (e :> t :> hc :> arg :> v) (code (codePrecStep dg))) :
    Semiformula.Evalb ((1 : M) :> hc :> arg :> v)
      (code (codeBall (codePrecStep dg) (1 : Fin (k + 2)))) :=
  by
  have hlift :
    ∀ t : M,
      Semiformula.Evalb (arg :> t :> hc :> arg :> v)
        (code (codeLift (Code.proj (1 : Fin (k + 2))))) :=
    fun t => (eval_codeLift_iff _ _ _ _).mpr ((eval_proj_iff _ _ _).mpr rfl)
  have hhead :
    ∀ t : M, Semiformula.Evalb (t :> t :> hc :> arg :> v) (code (codeHead (n := k + 2))) :=
    fun t => (eval_codeHead_iff _ _).mpr rfl
  rw [codeBall, eval_codeBind_iff]
  refine ⟨arg, ?_, ?_⟩
  · rw [eval_codeRfindPos_iff]
    constructor
    · obtain ⟨e, hne, he⟩ := hbody arg le_rfl
      refine ⟨1, by simp, (eval_codeOr_iff _ _ _ _).mpr ⟨0, 1, ?_, ?_, Or.inl ⟨by simp, rfl⟩⟩⟩
      · exact (eval_codeInv_iff _ _ _).mpr ⟨e, he, Or.inr ⟨hne, rfl⟩⟩
      · exact eval_codeLe_of _ _ arg arg 1 _ (hlift arg) (hhead arg) (Or.inl ⟨le_rfl, rfl⟩)
    · intro t ht
      obtain ⟨e, hne, he⟩ := hbody t (le_of_lt ht)
      refine (eval_codeOr_iff _ _ _ _).mpr ⟨0, 0, ?_, ?_, Or.inr ⟨by simp, rfl⟩⟩
      · exact (eval_codeInv_iff _ _ _).mpr ⟨e, he, Or.inr ⟨hne, rfl⟩⟩
      · exact eval_codeLe_of _ _ arg t 0 _ (hlift t) (hhead t) (Or.inr ⟨not_le.mpr ht, rfl⟩)
  · exact (eval_codeEq_iff _ _ _ _).mpr ⟨arg, arg, hhead arg, hlift arg, Or.inl ⟨rfl, rfl⟩⟩

/-- Once the bounded search has a witness the bounded quantifier has a value. -/
private theorem ball_val_of_rfind [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (dg : Code (k + 2)) (hc arg j : M)
    (v : Fin k → M)
    (hj :
      Semiformula.Evalb (j :> hc :> arg :> v)
        (code
          (codeRfindPos
            (codeOr (codeInv (codePrecStep dg))
              (codeLe (codeLift (Code.proj (1 : Fin (k + 2)))) (codeHead (n := k + 2))))))) :
    ∃ y : M,
      Semiformula.Evalb (y :> hc :> arg :> v)
        (code (codeBall (codePrecStep dg) (1 : Fin (k + 2)))) :=
  by
  have hhead : Semiformula.Evalb (j :> j :> hc :> arg :> v) (code (codeHead (n := k + 2))) :=
    (eval_codeHead_iff _ _).mpr rfl
  have hlift :
    Semiformula.Evalb (arg :> j :> hc :> arg :> v)
      (code (codeLift (Code.proj (1 : Fin (k + 2))))) :=
    (eval_codeLift_iff _ _ _ _).mpr ((eval_proj_iff _ _ _).mpr rfl)
  by_cases hja : j = arg
  · exact
      ⟨1, by
        rw [codeBall, eval_codeBind_iff]
        exact ⟨j, hj, (eval_codeEq_iff _ _ _ _).mpr ⟨j, arg, hhead, hlift, Or.inl ⟨hja, rfl⟩⟩⟩⟩
  · exact
      ⟨0, by
        rw [codeBall, eval_codeBind_iff]
        exact ⟨j, hj, (eval_codeEq_iff _ _ _ _).mpr ⟨j, arg, hhead, hlift, Or.inr ⟨hja, rfl⟩⟩⟩⟩

/-- The body of the bounded search inside `codeBall (codePrecStep dg) 1`, at
value zero: the step holds and the index is below the recursion argument. -/
private theorem eval_precSearch_zero_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (dg : Code (k + 2))
    (t hc arg : M) (v : Fin k → M) :
    Semiformula.Evalb ((0 : M) :> t :> hc :> arg :> v)
        (code
          (codeOr (codeInv (codePrecStep dg))
            (codeLe (codeLift (Code.proj (1 : Fin (k + 2)))) (codeHead (n := k + 2))))) ↔
      (∃ e : M, e ≠ 0 ∧ Semiformula.Evalb (e :> t :> hc :> arg :> v) (code (codePrecStep dg))) ∧
        t < arg :=
  by
  have hlift :
    Semiformula.Evalb (arg :> t :> hc :> arg :> v)
      (code (codeLift (Code.proj (1 : Fin (k + 2))))) :=
    (eval_codeLift_iff _ _ _ _).mpr ((eval_proj_iff _ _ _).mpr rfl)
  have hhead : Semiformula.Evalb (t :> t :> hc :> arg :> v) (code (codeHead (n := k + 2))) :=
    (eval_codeHead_iff _ _).mpr rfl
  constructor
  · intro h
    rw [eval_codeOr_iff] at h
    obtain ⟨p, q, hp, hq, hcase⟩ := h
    have hp0 : p = 0 := by
      rcases hcase with ⟨-, h01⟩ | ⟨hnp, -⟩
      · exact absurd h01.symm _root_.one_ne_zero
      · exact eq_zero_of_not_pos_add hnp
    have hq0 : q = 0 := by
      rcases hcase with ⟨-, h01⟩ | ⟨hnp, -⟩
      · exact absurd h01.symm _root_.one_ne_zero
      · exact eq_zero_of_not_pos_add (by rwa [add_comm] at hnp)
    rw [hp0, eval_codeInv_iff] at hp
    obtain ⟨e, he, hecase⟩ := hp
    have hstep :
      ∃ e : M, e ≠ 0 ∧ Semiformula.Evalb (e :> t :> hc :> arg :> v) (code (codePrecStep dg)) :=
      by
      rcases hecase with ⟨-, h01⟩ | ⟨hne, -⟩
      · exact absurd h01.symm _root_.one_ne_zero
      · exact ⟨e, hne, he⟩
    rw [hq0] at hq
    rcases le_val_cases _ _ arg t 0 _ hlift hhead hq with ⟨-, h01⟩ | ⟨hn, -⟩
    · exact absurd h01 _root_.zero_ne_one
    · exact ⟨hstep, not_le.mp hn⟩
  · rintro ⟨⟨e, hne, he⟩, hta⟩
    refine (eval_codeOr_iff _ _ _ _).mpr ⟨0, 0, ?_, ?_, Or.inr ⟨by simp, rfl⟩⟩
    · exact (eval_codeInv_iff _ _ _).mpr ⟨e, he, Or.inr ⟨hne, rfl⟩⟩
    · exact eval_codeLe_of _ _ arg t 0 _ hlift hhead (Or.inr ⟨not_le.mpr hta, rfl⟩)

/-- The search body is positive as soon as the step fails, or as soon as the
index has reached the recursion argument and the step has a value. -/
private theorem eval_precSearch_one [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (dg : Code (k + 2))
    (t hc arg e : M) (v : Fin k → M)
    (he : Semiformula.Evalb (e :> t :> hc :> arg :> v) (code (codePrecStep dg)))
    (hfail : e = 0 ∨ arg ≤ t) :
    Semiformula.Evalb ((1 : M) :> t :> hc :> arg :> v)
      (code
        (codeOr (codeInv (codePrecStep dg))
          (codeLe (codeLift (Code.proj (1 : Fin (k + 2)))) (codeHead (n := k + 2))))) :=
  by
  have hlift :
    Semiformula.Evalb (arg :> t :> hc :> arg :> v)
      (code (codeLift (Code.proj (1 : Fin (k + 2))))) :=
    (eval_codeLift_iff _ _ _ _).mpr ((eval_proj_iff _ _ _).mpr rfl)
  have hhead : Semiformula.Evalb (t :> t :> hc :> arg :> v) (code (codeHead (n := k + 2))) :=
    (eval_codeHead_iff _ _).mpr rfl
  by_cases hle : arg ≤ t
  · refine
      (eval_codeOr_iff _ _ _ _).mpr ⟨if e = 0 then 1 else 0, 1, ?_, ?_, Or.inl ⟨by simp, rfl⟩⟩
    · refine (eval_codeInv_iff _ _ _).mpr ⟨e, he, ?_⟩
      by_cases h0 : e = 0
      · exact Or.inl ⟨h0, by simp [h0]⟩
      · exact Or.inr ⟨h0, by simp [h0]⟩
    · exact eval_codeLe_of _ _ arg t 1 _ hlift hhead (Or.inl ⟨hle, rfl⟩)
  · have h0 : e = 0 := hfail.resolve_right hle
    refine (eval_codeOr_iff _ _ _ _).mpr ⟨1, 0, ?_, ?_, Or.inl ⟨by simp, rfl⟩⟩
    · exact (eval_codeInv_iff _ _ _).mpr ⟨e, he, Or.inl ⟨h0, rfl⟩⟩
    · exact eval_codeLe_of _ _ arg t 0 _ hlift hhead (Or.inr ⟨hle, rfl⟩)

/-- The bounded search inside `codeBall (codePrecStep dg) 1` still terminates
when the recursion argument is lowered by one. -/
private theorem rfind_at_lower_bound [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (dg : Code (k + 2)) (hc a j : M)
    (v : Fin k → M)
    (hj :
      Semiformula.Evalb (j :> hc :> (a + 1) :> v)
        (code
          (codeRfindPos
            (codeOr (codeInv (codePrecStep dg))
              (codeLe (codeLift (Code.proj (1 : Fin (k + 2)))) (codeHead (n := k + 2))))))) :
    ∃ j' : M,
      Semiformula.Evalb (j' :> hc :> a :> v)
        (code
          (codeRfindPos
            (codeOr (codeInv (codePrecStep dg))
              (codeLe (codeLift (Code.proj (1 : Fin (k + 2)))) (codeHead (n := k + 2)))))) := by
  rw [eval_codeRfindPos_iff] at hj
  obtain ⟨⟨y, hy, hFy⟩, hmin⟩ := hj
  have hbelow :
    ∀ t : M,
      t < j →
        ∃ e : M, e ≠ 0 ∧ Semiformula.Evalb (e :> t :> hc :> a :> v) (code (codePrecStep dg)) :=
    by
    intro t ht
    obtain ⟨⟨e, hne, he⟩, -⟩ := (eval_precSearch_zero_iff dg t hc (a + 1) v).mp (hmin t ht)
    exact ⟨e, hne, (eval_codePrecStep_bound_irrel_iff dg e t hc (a + 1) a v).mp he⟩
  by_cases hja : j ≤ a
  · refine ⟨j, (eval_codeRfindPos_iff _ _ _).mpr ⟨⟨1, by simp, ?_⟩, ?_⟩⟩
    · -- at `j` the search body is positive, and the comparison disjunct is zero
      rw [eval_codeOr_iff] at hFy
      obtain ⟨p, q, hp, hq, hcase⟩ := hFy
      have hlift :
        Semiformula.Evalb ((a + 1) :> j :> hc :> (a + 1) :> v)
          (code (codeLift (Code.proj (1 : Fin (k + 2))))) :=
        (eval_codeLift_iff _ _ _ _).mpr ((eval_proj_iff _ _ _).mpr rfl)
      have hhead :
        Semiformula.Evalb (j :> j :> hc :> (a + 1) :> v) (code (codeHead (n := k + 2))) :=
        (eval_codeHead_iff _ _).mpr rfl
      have hq0 : q = 0 :=
        by
        rcases le_val_cases _ _ (a + 1) j q _ hlift hhead hq with ⟨hle, -⟩ | ⟨-, h0⟩
        · exact absurd (le_trans hle hja) (by simp)
        · exact h0
      have hppos : 0 < p := by
        rcases hcase with ⟨hpq, -⟩ | ⟨-, h0⟩
        · rwa [hq0, add_zero] at hpq
        · exact absurd h0 (ne_of_gt hy)
      rw [eval_codeInv_iff] at hp
      obtain ⟨e, he, hecase⟩ := hp
      have he0 : e = 0 := by
        rcases hecase with ⟨h0, -⟩ | ⟨-, hp0⟩
        · exact h0
        · exact absurd hppos (by rw [hp0]; simp)
      exact
        eval_precSearch_one dg j hc a e v
          ((eval_codePrecStep_bound_irrel_iff dg e j hc (a + 1) a v).mp he) (Or.inl he0)
    · intro t ht
      exact (eval_precSearch_zero_iff dg t hc a v).mpr ⟨hbelow t ht, lt_of_lt_of_le ht hja⟩
  · have haj : a < j := not_le.mp hja
    refine ⟨a, (eval_codeRfindPos_iff _ _ _).mpr ⟨⟨1, by simp, ?_⟩, ?_⟩⟩
    · obtain ⟨e, -, he⟩ := hbelow a haj
      exact eval_precSearch_one dg a hc a e v he (Or.inr le_rfl)
    · intro t ht
      exact (eval_precSearch_zero_iff dg t hc a v).mpr ⟨hbelow t (lt_trans ht haj), ht⟩

/-- Lowering the recursion argument by one preserves a positive value of the
correctness predicate: the same history is still correct for the shorter run. -/
private theorem precPredicate_pos_step_down [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (df : Code k)
    (dg : Code (k + 2)) (hc a q : M) (v : Fin k → M) (hq : 0 < q)
    (h : Semiformula.Evalb (q :> hc :> (a + 1) :> v) (code (codePrecPredicate df dg))) :
    Semiformula.Evalb ((1 : M) :> hc :> a :> v) (code (codePrecPredicate df dg)) :=
  by
  rw [codePrecPredicate_eq, eval_codeAnd_iff] at h
  obtain ⟨p, r, hp, hr, hcase⟩ := h
  have hpr : 0 < p * r := by
    rcases hcase with ⟨hpos, -⟩ | ⟨-, h0⟩
    · exact hpos
    · exact absurd h0 (ne_of_gt hq)
  have hbody :
    ∀ t : M,
      t ≤ a →
        ∃ e : M, e ≠ 0 ∧ Semiformula.Evalb (e :> t :> hc :> a :> v) (code (codePrecStep dg)) :=
    by
    intro t ht
    obtain ⟨e, hne, he⟩ :=
      ball_body_of_pos dg r hc (a + 1) v (pos_of_pos_mul_right hpr) hr t
        (lt_of_le_of_lt ht (by simp))
    exact ⟨e, hne, (eval_codePrecStep_bound_irrel_iff dg e t hc (a + 1) a v).mp he⟩
  rw [codePrecPredicate_eq, eval_codeAnd_iff]
  exact
    ⟨p, 1, (eval_precBase_bound_irrel_iff df p hc (a + 1) a v).mp hp,
      ball_pos_of_body dg hc a v hbody,
      Or.inl ⟨by rw [mul_one]; exact pos_of_pos_mul_left hpr, rfl⟩⟩

/-- Lowering the recursion argument by one preserves having a value: the
correctness predicate is still decided at the shorter run. -/
private theorem precPredicate_val_step_down [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (df : Code k)
    (dg : Code (k + 2)) (hc a q : M) (v : Fin k → M)
    (h : Semiformula.Evalb (q :> hc :> (a + 1) :> v) (code (codePrecPredicate df dg))) :
    ∃ q' : M, Semiformula.Evalb (q' :> hc :> a :> v) (code (codePrecPredicate df dg)) :=
  by
  rw [codePrecPredicate_eq, eval_codeAnd_iff] at h
  obtain ⟨p, r, hp, hr, -⟩ := h
  rw [codeBall, eval_codeBind_iff] at hr
  obtain ⟨j, hjs, -⟩ := hr
  obtain ⟨j', hj'⟩ := rfind_at_lower_bound dg hc a j v hjs
  obtain ⟨r', hr'⟩ := ball_val_of_rfind dg hc a j' v hj'
  have hbase := (eval_precBase_bound_irrel_iff df p hc (a + 1) a v).mp hp
  by_cases hpr : 0 < p * r'
  · exact
      ⟨1, by
        rw [codePrecPredicate_eq, eval_codeAnd_iff]
        exact ⟨p, r', hbase, hr', Or.inl ⟨hpr, rfl⟩⟩⟩
  · exact
      ⟨0, by
        rw [codePrecPredicate_eq, eval_codeAnd_iff]
        exact ⟨p, r', hbase, hr', Or.inr ⟨hpr, rfl⟩⟩⟩

/-!
### Sigma-one definability of one argument slot of a literal code graph -/

open HierarchySymbol in
/-- Varying one argument of the graph formula of a code, with the output and the
remaining arguments fixed as parameters, is a Sigma-one condition. -/
private theorem definable_code_slot {m : ℕ} (A : Code m) (out : M) (target : Fin m)
    (par : Fin m → M) :
    Σ-[1].DefinablePred
      (fun i : M =>
        Semiformula.Evalb (out :> fun j => if j = target then i else par j) (code A)) :=
  by
  refine
    ⟨HierarchySymbol.Semiformula.mkSigma
        ((Rew.embSubsts
            (&out :> fun j => if j = target then (#0 : Semiterm ℒₒᵣ M 1) else &(par j))) ▹
          (code A))
        (Hierarchy.rew _ (code_sigma_one A)),
      ?_⟩
  intro w
  simp only [HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_embSubsts]
  have hv :
    (Semiterm.val w id ∘
        (&out :> fun j => if j = target then (#0 : Semiterm ℒₒᵣ M 1) else &(par j))) =
      (out :> fun j => if j = target then w 0 else par j) :=
    by
    funext j
    refine Fin.cases ?_ ?_ j
    · simp
    · intro j; by_cases h : j = target <;> simp [h]
  rw [hv]

open HierarchySymbol in
/-- The special case in which the varying argument is the first one. -/
private theorem definable_code_head_slot {m : ℕ} (A : Code (m + 1)) (out : M)
    (par : Fin m → M) :
    Σ-[1].DefinablePred (fun c : M => Semiformula.Evalb (out :> c :> par) (code A)) :=
  by
  have h := definable_code_slot A out (0 : Fin (m + 1)) ((0 : M) :> par)
  have he :
    (fun c : M => Semiformula.Evalb (out :> c :> par) (code A)) =
      (fun c : M =>
        Semiformula.Evalb
          (out :> fun j => if j = (0 : Fin (m + 1)) then c else ((0 : M) :> par) j) (code A)) :=
    by
    funext c
    have hv :
      ((c :> par) : Fin (m + 1) → M) =
        (fun j => if j = (0 : Fin (m + 1)) then c else ((0 : M) :> par) j) :=
      by
      funext j
      refine Fin.cases ?_ ?_ j
      · simp
      · intro j; simp
    rw [hv]
  rw [he]
  exact h

/-!
### Reading one history entry through different argument codes -/

/-- Two `codeBeta` applications whose argument codes evaluate to the same
history code and the same index have the same value, at whatever arities and
assignments they are written. -/
private theorem beta_align [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k l : ℕ} (N I : Code k) (N' I' : Code l)
    (x n idx : M) (v : Fin k → M) (v' : Fin l → M) (hN : Semiformula.Evalb (n :> v) (code N))
    (hN' : Semiformula.Evalb (n :> v') (code N')) (hI : Semiformula.Evalb (idx :> v) (code I))
    (hI' : Semiformula.Evalb (idx :> v') (code I'))
    (h : Semiformula.Evalb (x :> v) (code (codeBeta N I))) :
    Semiformula.Evalb (x :> v') (code (codeBeta N' I')) :=
  by
  refine (eval_codeBeta_congr_at N I N' I' x v v' ?_ ?_).mp h
  · intro y
    constructor
    · intro hy; rw [eval_unique hy hN]; exact hN'
    · intro hy; rw [eval_unique hy hN']; exact hN
  · intro y
    constructor
    · intro hy; rw [eval_unique hy hI]; exact hI'
    · intro hy; rw [eval_unique hy hI']; exact hI

/-!
### Reading a correct history -/

/-- The initial entry of a correct history is the base value. -/
private theorem prec_base_of_pos [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (df : Code k) (dg : Code (k + 2))
    (hc arg : M) (v : Fin k → M)
    (h : Semiformula.Evalb ((1 : M) :> hc :> arg :> v) (code (codePrecPredicate df dg))) :
    ∃ x : M,
      Semiformula.Evalb (x :> hc :> arg :> v) (code (codeBeta (Code.proj 0) (codeConst 0))) ∧
        Semiformula.Evalb (x :> v) (code df) :=
  by
  rw [codePrecPredicate_eq, eval_codeAnd_iff] at h
  obtain ⟨p, r, hp, -, hcase⟩ := h
  have hppos : 0 < p := by
    rcases hcase with ⟨hpos, -⟩ | ⟨-, h0⟩
    · exact pos_of_pos_mul_left hpos
    · exact absurd h0 _root_.one_ne_zero
  rw [eval_codeEq_iff] at hp
  obtain ⟨x, d, hx, hd, hdec⟩ := hp
  have hxd : x = d := by
    rcases hdec with ⟨heq, -⟩ | ⟨-, h0⟩
    · exact heq
    · exact absurd hppos (by rw [h0]; simp)
  rw [eval_comp_iff] at hd
  obtain ⟨w, hw, hwi⟩ := hd
  have hwv : w = v := by
    funext j
    exact eval_unique (hwi j) ((eval_proj_iff _ _ _).mpr rfl)
  rw [hwv] at hw
  exact ⟨x, hx, hxd ▸ hw⟩

/-- Below the recursion argument, consecutive entries of a correct history are
related by the step code. -/
private theorem prec_step_of_pos [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (df : Code k) (dg : Code (k + 2))
    (hc arg t : M) (v : Fin k → M) (ht : t < arg)
    (h : Semiformula.Evalb ((1 : M) :> hc :> arg :> v) (code (codePrecPredicate df dg))) :
    ∃ u b : M,
      Semiformula.Evalb (b :> t :> hc :> arg :> v)
          (code (codeBeta (Code.proj 1) (Code.proj 0))) ∧
        Semiformula.Evalb (u :> t :> hc :> arg :> v)
            (code (codeBeta (Code.proj 1) (codeSucc (Code.proj 0)))) ∧
          Semiformula.Evalb (u :> t :> b :> v) (code dg) :=
  by
  rw [codePrecPredicate_eq, eval_codeAnd_iff] at h
  obtain ⟨p, r, -, hr, hcase⟩ := h
  have hrpos : 0 < r := by
    rcases hcase with ⟨hpos, -⟩ | ⟨-, h0⟩
    · exact pos_of_pos_mul_right hpos
    · exact absurd h0 _root_.one_ne_zero
  obtain ⟨e, hne, he⟩ := ball_body_of_pos dg r hc arg v hrpos hr t ht
  rw [codePrecStep_eq, eval_codeEq_iff] at he
  obtain ⟨u, d, hu, hd, hdec⟩ := he
  have hud : u = d := by
    rcases hdec with ⟨heq, -⟩ | ⟨-, h0⟩
    · exact heq
    · exact absurd h0 hne
  rw [eval_comp_iff] at hd
  obtain ⟨w, hw, hwi⟩ := hd
  have hentry := hwi (Fin.succ 0)
  simp only [Fin.cases_succ, Fin.cases_zero] at hentry
  refine ⟨u, w (Fin.succ 0), hentry, hu, ?_⟩
  have hw0 : w 0 = t := by
    have h0 := hwi 0
    simp only [Fin.cases_zero] at h0
    exact eval_unique h0 ((eval_proj_iff _ _ _).mpr rfl)
  have hwv : ∀ j : Fin k, w j.succ.succ = v j :=
    by
    intro j
    have hj := hwi j.succ.succ
    simp only [Fin.cases_succ] at hj
    exact eval_unique hj ((eval_proj_iff _ _ _).mpr rfl)
  have hshape : w = (t :> w (Fin.succ 0) :> v) :=
    by
    funext j
    refine Fin.cases ?_ ?_ j
    · exact hw0
    · intro j'
      refine Fin.cases ?_ ?_ j'
      · rfl
      · intro j''; exact hwv j''
  rw [hshape] at hw
  exact hud ▸ hw

/-!
### Correct histories agree below the recursion argument -/

open HierarchySymbol in
/-- Two correct histories, one for `a` and one for `a + 1`, record the same
entry at every index up to `a`. The induction is on a literal code graph and
uses Sigma-one induction. -/
private theorem histories_agree [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {k : ℕ} (df : Code k) (dg : Code (k + 2))
    (hc₀ hc₁ a : M) (v : Fin k → M)
    (h₀ : Semiformula.Evalb ((1 : M) :> hc₀ :> a :> v) (code (codePrecPredicate df dg)))
    (h₁ : Semiformula.Evalb ((1 : M) :> hc₁ :> (a + 1) :> v) (code (codePrecPredicate df dg)))
    (i : M) (hia : i ≤ a) :
    ∃ x : M,
      Semiformula.Evalb (x :> i :> hc₀ :> hc₁ :> v)
          (code (codeBeta (Code.proj 1) (Code.proj (0 : Fin (k + 3))))) ∧
        Semiformula.Evalb (x :> i :> hc₀ :> hc₁ :> v)
          (code (codeBeta (Code.proj 2) (Code.proj (0 : Fin (k + 3))))) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  have hdef :
    Σ-[1].DefinablePred
      (fun c : M =>
        Semiformula.Evalb ((1 : M) :> c :> hc₀ :> hc₁ :> v)
            (code
              (codeEq (codeBeta (Code.proj 1) (Code.proj (0 : Fin (k + 3))))
                (codeBeta (Code.proj 2) (Code.proj (0 : Fin (k + 3)))))) ∨
          a < c) :=
    HierarchySymbol.Definable.or (definable_code_head_slot _ (1 : M) (hc₀ :> hc₁ :> v))
      (by definability)
  have key :
    ∀ c : M,
      Semiformula.Evalb ((1 : M) :> c :> hc₀ :> hc₁ :> v)
          (code
            (codeEq (codeBeta (Code.proj 1) (Code.proj (0 : Fin (k + 3))))
              (codeBeta (Code.proj 2) (Code.proj (0 : Fin (k + 3)))))) ∨
        a < c :=
    by
    refine InductionOnHierarchy.succ_induction Σ 1 hdef ?_ ?_
    · -- the initial entries are both the base value
      obtain ⟨x₀, hx₀, hd₀⟩ := prec_base_of_pos df dg hc₀ a v h₀
      obtain ⟨x₁, hx₁, hd₁⟩ := prec_base_of_pos df dg hc₁ (a + 1) v h₁
      have hzero₀ :
        Semiformula.Evalb ((0 : M) :> hc₀ :> a :> v) (code (codeConst (n := k + 2) 0)) := by
        rw [eval_codeConst_iff]; simp
      have hzero₁ :
        Semiformula.Evalb ((0 : M) :> hc₁ :> (a + 1) :> v) (code (codeConst (n := k + 2) 0)) :=
        by rw [eval_codeConst_iff]; simp
      refine
        Or.inl
          ((eval_codeEq_iff _ _ _ _).mpr ⟨x₀, x₁, ?_, ?_, Or.inl ⟨eval_unique hd₀ hd₁, rfl⟩⟩)
      · exact
          beta_align _ _ _ _ x₀ hc₀ 0 _ _ ((eval_proj_iff _ _ _).mpr rfl)
            ((eval_proj_iff _ _ _).mpr rfl) hzero₀ ((eval_proj_iff _ _ _).mpr rfl) hx₀
      · exact
          beta_align _ _ _ _ x₁ hc₁ 0 _ _ ((eval_proj_iff _ _ _).mpr rfl)
            ((eval_proj_iff _ _ _).mpr rfl) hzero₁ ((eval_proj_iff _ _ _).mpr rfl) hx₁
    · intro c IH
      by_cases hac : a < c + 1
      · exact Or.inr hac
      · have hca : c < a := lt_of_lt_of_le (by simp) (not_lt.mp hac)
        have hagree := IH.resolve_right (not_lt.mpr (le_of_lt hca))
        obtain ⟨y₀, y₁, hy₀, hy₁, hdec⟩ := (eval_codeEq_iff _ _ _ _).mp hagree
        have hyy : y₀ = y₁ := by
          rcases hdec with ⟨heq, -⟩ | ⟨-, h0⟩
          · exact heq
          · exact absurd h0 _root_.one_ne_zero
        obtain ⟨u₀, b₀, hb₀, hu₀, hdg₀⟩ := prec_step_of_pos df dg hc₀ a c v hca h₀
        obtain ⟨u₁, b₁, hb₁, hu₁, hdg₁⟩ :=
          prec_step_of_pos df dg hc₁ (a + 1) c v (lt_trans hca (by simp)) h₁
        have hb : b₀ = b₁ :=
          by
          have e₀ : y₀ = b₀ :=
            eval_unique
              (beta_align _ _ _ _ y₀ hc₀ c _ _ ((eval_proj_iff _ _ _).mpr rfl)
                ((eval_proj_iff _ _ _).mpr rfl) ((eval_proj_iff _ _ _).mpr rfl)
                ((eval_proj_iff _ _ _).mpr rfl) hy₀)
              hb₀
          have e₁ : y₁ = b₁ :=
            eval_unique
              (beta_align _ _ _ _ y₁ hc₁ c _ _ ((eval_proj_iff _ _ _).mpr rfl)
                ((eval_proj_iff _ _ _).mpr rfl) ((eval_proj_iff _ _ _).mpr rfl)
                ((eval_proj_iff _ _ _).mpr rfl) hy₁)
              hb₁
          rw [← e₀, ← e₁, hyy]
        have hu : u₀ = u₁ := by
          rw [hb] at hdg₀
          exact eval_unique hdg₀ hdg₁
        have hsucc₀ :
          Semiformula.Evalb ((c + 1) :> c :> hc₀ :> a :> v)
            (code (codeSucc (Code.proj (0 : Fin (k + 3))))) :=
          (eval_codeSucc_iff _ _ _).mpr ⟨c, (eval_proj_iff _ _ _).mpr rfl, rfl⟩
        have hsucc₁ :
          Semiformula.Evalb ((c + 1) :> c :> hc₁ :> (a + 1) :> v)
            (code (codeSucc (Code.proj (0 : Fin (k + 3))))) :=
          (eval_codeSucc_iff _ _ _).mpr ⟨c, (eval_proj_iff _ _ _).mpr rfl, rfl⟩
        refine Or.inl ((eval_codeEq_iff _ _ _ _).mpr ⟨u₀, u₁, ?_, ?_, Or.inl ⟨hu, rfl⟩⟩)
        · exact
            beta_align _ _ _ _ u₀ hc₀ (c + 1) _ _ ((eval_proj_iff _ _ _).mpr rfl)
              ((eval_proj_iff _ _ _).mpr rfl) hsucc₀ ((eval_proj_iff _ _ _).mpr rfl) hu₀
        · exact
            beta_align _ _ _ _ u₁ hc₁ (c + 1) _ _ ((eval_proj_iff _ _ _).mpr rfl)
              ((eval_proj_iff _ _ _).mpr rfl) hsucc₁ ((eval_proj_iff _ _ _).mpr rfl) hu₁
  obtain ⟨y₀, y₁, hy₀, hy₁, hdec⟩ :=
    (eval_codeEq_iff _ _ _ _).mp ((key i).resolve_right (not_lt.mpr hia))
  have hyy : y₀ = y₁ := by
    rcases hdec with ⟨heq, -⟩ | ⟨-, h0⟩
    · exact heq
    · exact absurd h0 _root_.one_ne_zero
  exact ⟨y₀, hy₀, hyy ▸ hy₁⟩

end Restriction

section Successor

variable {M : Type*} [ORingStructure M]

open scoped FFL.FirstOrder.Arithmetic

open HierarchySymbol

/-!
### The successor step of primitive recursion -/

open HierarchySymbol in
/-- Evaluating `codePrec df dg` at `a + 1` gives the value at `a` together with
one application of the step code.

The two evaluations read different correct histories, so the proof aligns their
entries by Sigma-one induction before reading the predecessor value. -/
theorem eval_codePrec_succ [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {k : ℕ} (df : Code k) (dg : Code (k + 2)) (a z : M)
    (v : Fin k → M) (h : Semiformula.Evalb (z :> (a + 1) :> v) (code (codePrec df dg))) :
    ∃ w : M,
      Semiformula.Evalb (w :> a :> v) (code (codePrec df dg)) ∧
        Semiformula.Evalb (z :> a :> w :> v) (code dg) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  rw [codePrec, eval_codeBind_iff] at h
  obtain ⟨hc₁, hsearch, hread⟩ := h
  rw [eval_codeRfindPos_iff] at hsearch
  obtain ⟨⟨q, hq, hP⟩, hmin⟩ := hsearch
  have hq1 : q = 1 := by
    rw [codePrecPredicate_eq, eval_codeAnd_iff] at hP
    obtain ⟨p, r, -, -, hcase⟩ := hP
    rcases hcase with ⟨-, h1⟩ | ⟨-, h0⟩
    · exact h1
    · exact absurd h0 (ne_of_gt hq)
  rw [hq1] at hP
  have hPa := precPredicate_pos_step_down df dg hc₁ a 1 v (by simp) hP
  have hdefQ :
    Σ-[1].DefinablePred
      (fun c : M =>
        Semiformula.Evalb ((1 : M) :> c :> a :> v) (code (codePrecPredicate df dg))) :=
    definable_code_head_slot _ (1 : M) (a :> v)
  obtain ⟨hc₀, hQ₀, hleast⟩ := InductionOnHierarchy.least_number Σ 1 hdefQ hPa
  have hle : hc₀ ≤ hc₁ := not_lt.mp fun hlt => hleast hc₁ hlt hPa
  have hsearch₀ :
    Semiformula.Evalb (hc₀ :> a :> v) (code (codeRfindPos (codePrecPredicate df dg))) :=
    by
    refine (eval_codeRfindPos_iff _ _ _).mpr ⟨⟨1, by simp, hQ₀⟩, ?_⟩
    intro t ht
    obtain ⟨q', hq'⟩ :=
      precPredicate_val_step_down df dg t a 0 v (hmin t (lt_of_lt_of_le ht hle))
    have hq'0 : q' = 0 :=
      by
      rw [codePrecPredicate_eq, eval_codeAnd_iff] at hq'
      obtain ⟨p, r, hp, hr, hcase⟩ := hq'
      rcases hcase with ⟨hpos, h1⟩ | ⟨-, h0⟩
      · refine absurd ?_ (hleast t ht)
        rw [codePrecPredicate_eq, eval_codeAnd_iff]
        exact ⟨p, r, hp, hr, Or.inl ⟨hpos, rfl⟩⟩
      · exact h0
    rwa [hq'0] at hq'
  obtain ⟨u, b, hb, hu, hdg⟩ := prec_step_of_pos df dg hc₁ (a + 1) a v (by simp) hP
  have huz : u = z :=
    eval_unique
      (beta_align _ _ _ _ u hc₁ (a + 1) _ _ ((eval_proj_iff _ _ _).mpr rfl)
        ((eval_codeHead_iff _ _).mpr rfl)
        ((eval_codeSucc_iff _ _ _).mpr ⟨a, (eval_proj_iff _ _ _).mpr rfl, rfl⟩)
        ((eval_codeLift_iff _ _ _ _).mpr ((eval_codeHead_iff _ _).mpr rfl)) hu)
      hread
  obtain ⟨x, hx₀, hx₁⟩ := histories_agree df dg hc₀ hc₁ a v hQ₀ hP a le_rfl
  have hxb : x = b :=
    eval_unique
      (beta_align _ _ _ _ x hc₁ a _ _ ((eval_proj_iff _ _ _).mpr rfl)
        ((eval_proj_iff _ _ _).mpr rfl) ((eval_proj_iff _ _ _).mpr rfl)
        ((eval_proj_iff _ _ _).mpr rfl) hx₁)
      hb
  refine ⟨b, ?_, huz ▸ hdg⟩
  rw [codePrec, eval_codeBind_iff]
  refine ⟨hc₀, hsearch₀, ?_⟩
  refine
    hxb ▸
      beta_align _ _ _ _ x hc₀ a _ _ ((eval_proj_iff _ _ _).mpr rfl)
        ((eval_codeHead_iff _ _).mpr rfl) ((eval_proj_iff _ _ _).mpr rfl)
        ((eval_codeLift_iff _ _ _ _).mpr ((eval_codeHead_iff _ _).mpr rfl)) hx₀

/-- Evaluating `codePrec df dg` at zero gives the same value for the base code.

This is the forward direction only: a successful evaluation of the recursion at
zero yields a successful evaluation of `df` with the same output.  Nothing here
asserts the converse. -/
theorem eval_codePrec_zero [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (df : Code k) (dg : Code (k + 2)) (z : M)
    (v : Fin k → M) (h : Semiformula.Evalb (z :> (0 : M) :> v) (code (codePrec df dg))) :
    Semiformula.Evalb (z :> v) (code df) :=
  by
  rw [codePrec, eval_codeBind_iff] at h
  obtain ⟨hc, hsearch, hread⟩ := h
  rw [eval_codeRfindPos_iff] at hsearch
  obtain ⟨⟨q, hq, hP⟩, -⟩ := hsearch
  have hq1 : q = 1 := by
    rw [codePrecPredicate_eq, eval_codeAnd_iff] at hP
    obtain ⟨p, r, -, -, hcase⟩ := hP
    rcases hcase with ⟨-, h1⟩ | ⟨-, h0⟩
    · exact h1
    · exact absurd h0 (ne_of_gt hq)
  rw [hq1] at hP
  obtain ⟨x, hx, hdf⟩ := prec_base_of_pos df dg hc 0 v hP
  have hzero :
    Semiformula.Evalb ((0 : M) :> hc :> (0 : M) :> v) (code (codeConst (n := k + 2) 0)) := by
    rw [eval_codeConst_iff]; simp
  have hxz : x = z :=
    eval_unique
      (beta_align _ _ _ _ x hc 0 _ _ ((eval_proj_iff _ _ _).mpr rfl)
        ((eval_codeHead_iff _ _).mpr rfl) hzero
        ((eval_codeLift_iff _ _ _ _).mpr ((eval_codeHead_iff _ _).mpr rfl)) hx)
      hread
  exact hxz ▸ hdf

end Successor

section Existence

variable {M : Type*} [ORingStructure M]

open scoped FFL.FirstOrder.Arithmetic

open HierarchySymbol

/-!
### Totality of the step relation -/

/-- The step code applied to the history entry at an index, read inside the
assignment of `codePrecStep`. -/
private theorem prec_step_comp_of {k : ℕ} (dg : Code (k + 2)) (i hc arg z w : M) (v : Fin k → M)
    (hz :
      Semiformula.Evalb (z :> i :> hc :> arg :> v)
        (code (codeBeta (Code.proj 1) (Code.proj (0 : Fin (k + 3))))))
    (hw : Semiformula.Evalb (w :> i :> z :> v) (code dg)) :
    Semiformula.Evalb (w :> i :> hc :> arg :> v)
      (code
        (dg.comp
          (Fin.cases (Code.proj 0)
            (Fin.cases (codeBeta (Code.proj 1) (Code.proj 0))
              (fun j => Code.proj j.succ.succ.succ))))) :=
  by
  rw [eval_comp_iff]
  refine ⟨i :> z :> v, hw, ?_⟩
  intro j
  refine Fin.cases ?_ ?_ j
  · simp only [Fin.cases_zero, Matrix.cons_val_zero]
    exact (eval_proj_iff (0 : Fin (k + 3)) i (i :> hc :> arg :> v)).mpr rfl
  · intro j1
    refine Fin.cases ?_ ?_ j1
    · simp only [Fin.cases_succ, Fin.cases_zero]
      exact hz
    · intro j2
      simp only [Fin.cases_succ]
      exact (eval_proj_iff j2.succ.succ.succ _ (i :> hc :> arg :> v)).mpr (by simp)

/-- A step evaluation with output one, from the two history entries it relates
and the step value between them. -/
private theorem prec_step_pos_of {k : ℕ} (dg : Code (k + 2)) (i hc arg z w : M) (v : Fin k → M)
    (hz :
      Semiformula.Evalb (z :> i :> hc :> arg :> v)
        (code (codeBeta (Code.proj 1) (Code.proj (0 : Fin (k + 3))))))
    (hu :
      Semiformula.Evalb (w :> i :> hc :> arg :> v)
        (code (codeBeta (Code.proj 1) (codeSucc (Code.proj (0 : Fin (k + 3)))))))
    (hw : Semiformula.Evalb (w :> i :> z :> v) (code dg)) :
    Semiformula.Evalb ((1 : M) :> i :> hc :> arg :> v) (code (codePrecStep dg)) :=
  by
  rw [codePrecStep_eq]
  exact
    (eval_codeEq_iff _ _ _ _).mpr
      ⟨w, w, hu, prec_step_comp_of dg i hc arg z w v hz hw, Or.inl ⟨rfl, rfl⟩⟩

/-- The step relation has a value at every index the step code is total at,
whatever history code and recursion argument accompany it. -/
private theorem prec_step_total [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {k : ℕ} (dg : Code (k + 2)) (a : M)
    (v : Fin k → M)
    (hdg : ∀ i : M, i ≤ a → ∀ z : M, ∃ w : M, Semiformula.Evalb (w :> i :> z :> v) (code dg))
    (i hc arg : M) (hi : i ≤ a) :
    ∃ e : M, Semiformula.Evalb (e :> i :> hc :> arg :> v) (code (codePrecStep dg)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  have hhc :
    Semiformula.Evalb (hc :> i :> hc :> arg :> v) (code (Code.proj (1 : Fin (k + 3)))) :=
    (eval_proj_iff _ _ _).mpr (by simp)
  have hidx :
    Semiformula.Evalb (i :> i :> hc :> arg :> v) (code (Code.proj (0 : Fin (k + 3)))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have hsucc :
    Semiformula.Evalb ((i + 1) :> i :> hc :> arg :> v)
      (code (codeSucc (Code.proj (0 : Fin (k + 3))))) :=
    (eval_codeSucc_iff _ _ _).mpr ⟨i, hidx, rfl⟩
  have hbeta :=
    eval_codeBeta_of_values (Code.proj (1 : Fin (k + 3))) (Code.proj (0 : Fin (k + 3))) hc i
      (i :> hc :> arg :> v) hhc hidx
  have hnext :=
    eval_codeBeta_of_values (Code.proj (1 : Fin (k + 3)))
      (codeSucc (Code.proj (0 : Fin (k + 3)))) hc (i + 1) (i :> hc :> arg :> v) hhc hsucc
  obtain ⟨w, hw⟩ := hdg i hi _
  have hcomp := prec_step_comp_of dg i hc arg _ w v hbeta hw
  rw [codePrecStep_eq]
  by_cases heq :
    (FFL.FirstOrder.Arithmetic.pi₁ hc % ((i + 1 + 1) * FFL.FirstOrder.Arithmetic.pi₂ hc + 1)) =
      w
  · exact ⟨1, (eval_codeEq_iff _ _ _ _).mpr ⟨_, w, hnext, hcomp, Or.inl ⟨heq, rfl⟩⟩⟩
  · exact ⟨0, (eval_codeEq_iff _ _ _ _).mpr ⟨_, w, hnext, hcomp, Or.inr ⟨heq, rfl⟩⟩⟩

/-!
### Introducing the bounded quantifier without a positive terminal step -/

/-- The bounded quantifier takes the value one as soon as the step is positive
strictly below the recursion argument and merely has a value at it.

`ball_pos_of_body` demands a positive step at the recursion argument as well.
The eager search only needs a value there, because the comparison disjunct is
already positive at that index. -/
private theorem ball_pos_of_body_weak [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (dg : Code (k + 2)) (hc arg : M)
    (v : Fin k → M)
    (hbelow :
      ∀ t : M,
        t < arg →
          ∃ e : M,
            e ≠ 0 ∧ Semiformula.Evalb (e :> t :> hc :> arg :> v) (code (codePrecStep dg)))
    (hterm : ∃ e : M, Semiformula.Evalb (e :> arg :> hc :> arg :> v) (code (codePrecStep dg))) :
    Semiformula.Evalb ((1 : M) :> hc :> arg :> v)
      (code (codeBall (codePrecStep dg) (1 : Fin (k + 2)))) :=
  by
  have hlift :
    Semiformula.Evalb (arg :> arg :> hc :> arg :> v)
      (code (codeLift (Code.proj (1 : Fin (k + 2))))) :=
    (eval_codeLift_iff _ _ _ _).mpr ((eval_proj_iff _ _ _).mpr rfl)
  have hhead :
    Semiformula.Evalb (arg :> arg :> hc :> arg :> v) (code (codeHead (n := k + 2))) :=
    (eval_codeHead_iff _ _).mpr rfl
  rw [codeBall, eval_codeBind_iff]
  refine ⟨arg, ?_, (eval_codeEq_iff _ _ _ _).mpr ⟨arg, arg, hhead, hlift, Or.inl ⟨rfl, rfl⟩⟩⟩
  rw [eval_codeRfindPos_iff]
  refine ⟨⟨1, by simp, ?_⟩, ?_⟩
  · obtain ⟨e, he⟩ := hterm
    exact eval_precSearch_one dg arg hc arg e v he (Or.inr le_rfl)
  · intro t ht
    exact (eval_precSearch_zero_iff dg t hc arg v).mpr ⟨hbelow t ht, ht⟩

/-!
### Totality of the correctness predicate at an arbitrary history -/

/-- The bounded quantifier has a value at every history code, correct or not. -/
private theorem ball_total [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {k : ℕ} (dg : Code (k + 2)) (a : M) (v : Fin k → M)
    (hdg : ∀ i : M, i ≤ a → ∀ z : M, ∃ w : M, Semiformula.Evalb (w :> i :> z :> v) (code dg))
    (hc : M) :
    ∃ y : M,
      Semiformula.Evalb (y :> hc :> a :> v)
        (code (codeBall (codePrecStep dg) (1 : Fin (k + 2)))) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  have hposA :
    Semiformula.Evalb ((1 : M) :> a :> hc :> a :> v)
      (code
        (codeOr (codeInv (codePrecStep dg))
          (codeLe (codeLift (Code.proj (1 : Fin (k + 2)))) (codeHead (n := k + 2))))) :=
    by
    obtain ⟨e, he⟩ := prec_step_total dg a v hdg a hc a le_rfl
    exact eval_precSearch_one dg a hc a e v he (Or.inr le_rfl)
  have hnotA :
    ¬Semiformula.Evalb ((0 : M) :> a :> hc :> a :> v)
        (code
          (codeOr (codeInv (codePrecStep dg))
            (codeLe (codeLift (Code.proj (1 : Fin (k + 2)))) (codeHead (n := k + 2))))) :=
    by
    intro h0
    exact absurd (eval_unique h0 hposA) (by simp)
  have hdef :
    Π-[1].DefinablePred
      (fun t : M =>
        ¬Semiformula.Evalb ((0 : M) :> t :> hc :> a :> v)
            (code
              (codeOr (codeInv (codePrecStep dg))
                (codeLe (codeLift (Code.proj (1 : Fin (k + 2)))) (codeHead (n := k + 2)))))) :=
    HierarchySymbol.Definable.not (definable_code_head_slot _ (0 : M) (hc :> a :> v))
  obtain ⟨j, hjnot, hjmin⟩ := InductionOnHierarchy.least_number Π 1 hdef hnotA
  have hja : j ≤ a := not_lt.mp fun hlt => hjmin a hlt hnotA
  have hbelow :
    ∀ t : M,
      t < j →
        Semiformula.Evalb ((0 : M) :> t :> hc :> a :> v)
          (code
            (codeOr (codeInv (codePrecStep dg))
              (codeLe (codeLift (Code.proj (1 : Fin (k + 2)))) (codeHead (n := k + 2))))) :=
    fun t ht => not_not.mp (hjmin t ht)
  have hposJ :
    Semiformula.Evalb ((1 : M) :> j :> hc :> a :> v)
      (code
        (codeOr (codeInv (codePrecStep dg))
          (codeLe (codeLift (Code.proj (1 : Fin (k + 2)))) (codeHead (n := k + 2))))) :=
    by
    obtain ⟨e, he⟩ := prec_step_total dg a v hdg j hc a hja
    by_cases he0 : e = 0
    · exact eval_precSearch_one dg j hc a e v he (Or.inl he0)
    · by_cases hlt : j < a
      · exact absurd ((eval_precSearch_zero_iff dg j hc a v).mpr ⟨⟨e, he0, he⟩, hlt⟩) hjnot
      · exact eval_precSearch_one dg j hc a e v he (Or.inr (not_lt.mp hlt))
  exact
    ball_val_of_rfind dg hc a j v
      ((eval_codeRfindPos_iff _ _ _).mpr ⟨⟨1, by simp, hposJ⟩, hbelow⟩)

/-- The correctness predicate has a value at every history code.  The outer
minimization inside `codePrec` needs this at incorrect histories too. -/
private theorem prec_predicate_total [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {k : ℕ} (df : Code k) (dg : Code (k + 2))
    (a : M) (v : Fin k → M) (hdf : ∃ z : M, Semiformula.Evalb (z :> v) (code df))
    (hdg : ∀ i : M, i ≤ a → ∀ z : M, ∃ w : M, Semiformula.Evalb (w :> i :> z :> v) (code dg))
    (hc : M) :
    ∃ q : M, Semiformula.Evalb (q :> hc :> a :> v) (code (codePrecPredicate df dg)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  have hhc : Semiformula.Evalb (hc :> hc :> a :> v) (code (Code.proj (0 : Fin (k + 2)))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have hzero : Semiformula.Evalb ((0 : M) :> hc :> a :> v) (code (codeConst (n := k + 2) 0)) :=
    by rw [eval_codeConst_iff]; simp
  have hb :=
    eval_codeBeta_of_values (Code.proj (0 : Fin (k + 2))) (codeConst (n := k + 2) 0) hc 0
      (hc :> a :> v) hhc hzero
  obtain ⟨x, hx⟩ := hdf
  have hcomp :
    Semiformula.Evalb (x :> hc :> a :> v) (code (df.comp (fun j => Code.proj j.succ.succ))) :=
    by
    rw [eval_comp_iff]
    exact ⟨v, hx, fun j => (eval_proj_iff _ _ _).mpr (by simp)⟩
  have hbase :
    ∃ p : M,
      Semiformula.Evalb (p :> hc :> a :> v)
        (code
          (codeEq (codeBeta (Code.proj 0) (codeConst 0))
            (df.comp (fun j => Code.proj j.succ.succ)))) :=
    by
    by_cases heq :
      (FFL.FirstOrder.Arithmetic.pi₁ hc % ((0 + 1) * FFL.FirstOrder.Arithmetic.pi₂ hc + 1)) = x
    · exact ⟨1, (eval_codeEq_iff _ _ _ _).mpr ⟨_, x, hb, hcomp, Or.inl ⟨heq, rfl⟩⟩⟩
    · exact ⟨0, (eval_codeEq_iff _ _ _ _).mpr ⟨_, x, hb, hcomp, Or.inr ⟨heq, rfl⟩⟩⟩
  obtain ⟨p, hp⟩ := hbase
  obtain ⟨y, hy⟩ := ball_total dg a v hdg hc
  rw [codePrecPredicate_eq]
  by_cases hpos : 0 < p * y
  · exact ⟨1, (eval_codeAnd_iff _ _ _ _).mpr ⟨p, y, hp, hy, Or.inl ⟨hpos, rfl⟩⟩⟩
  · exact ⟨0, (eval_codeAnd_iff _ _ _ _).mpr ⟨p, y, hp, hy, Or.inr ⟨hpos, rfl⟩⟩⟩

/-!
### Moving a history entry between the two-argument beta code and the
assignments of `codePrecPredicate` -/

/-- Read a two-argument beta evaluation at a wider assignment. -/
private theorem beta_of_pair [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {l : ℕ} (N' I' : Code l) (x n idx : M)
    (v' : Fin l → M) (hN' : Semiformula.Evalb (n :> v') (code N'))
    (hI' : Semiformula.Evalb (idx :> v') (code I'))
    (h :
      Semiformula.Evalb (x :> ![n, idx])
        (code (codeBeta (Code.proj (0 : Fin 2)) (Code.proj (1 : Fin 2))))) :
    Semiformula.Evalb (x :> v') (code (codeBeta N' I')) :=
  beta_align _ _ N' I' x n idx ![n, idx] v' ((eval_proj_iff _ _ _).mpr (by simp)) hN'
    ((eval_proj_iff _ _ _).mpr (by simp)) hI' h

/-- Read a beta evaluation at a wider assignment as a two-argument one. -/
private theorem beta_to_pair [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {l : ℕ} (N' I' : Code l) (x n idx : M)
    (v' : Fin l → M) (hN' : Semiformula.Evalb (n :> v') (code N'))
    (hI' : Semiformula.Evalb (idx :> v') (code I'))
    (h : Semiformula.Evalb (x :> v') (code (codeBeta N' I'))) :
    Semiformula.Evalb (x :> ![n, idx])
      (code (codeBeta (Code.proj (0 : Fin 2)) (Code.proj (1 : Fin 2)))) :=
  beta_align N' I' _ _ x n idx v' ![n, idx] hN' ((eval_proj_iff _ _ _).mpr (by simp)) hI'
    ((eval_proj_iff _ _ _).mpr (by simp)) h

/-!
### Sigma-one definability of a literal code graph in two argument slots -/

open HierarchySymbol in
/-- Substituting terms with model parameters into a code graph preserves Sigma-one definability. -/
theorem definable_code_graph_arguments {k n : ℕ} (A : Code k)
    (arguments : Fin (k + 1) → Semiterm ℒₒᵣ M n) :
    Σ-[1].Definable (fun w : Fin n → M =>
      Semiformula.Evalb (Semiterm.val w id ∘ arguments) (code A)) := by
  refine ⟨HierarchySymbol.Semiformula.mkSigma ((Rew.embSubsts arguments) ▹ code A)
    (Hierarchy.rew _ (code_sigma_one A)), ?_⟩
  intro w
  simp only [HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_embSubsts]

open HierarchySymbol in
/-- Varying the first two arguments of the graph formula of a code, with the
output and the remaining arguments fixed as parameters, is a Sigma-one
condition. -/
private theorem definable_code_two_slots {m : ℕ} (A : Code (m + 2)) (out : M)
    (par : Fin m → M) :
    Σ-[1].Definable
      (fun w : Fin 2 → M => Semiformula.Evalb (out :> w 0 :> w 1 :> par) (code A)) :=
  by
  simpa only [Nat.succ_eq_add_one, Fin.isValue, Function.comp_def, Matrix.comp_vecCons',
    Semiterm.val_fvar, id_eq, Semiterm.val_bvar] using
    definable_code_graph_arguments A
      ((&out : Semiterm ℒₒᵣ M 2) :>
        (#0 : Semiterm ℒₒᵣ M 2) :>
          (#1 : Semiterm ℒₒᵣ M 2) :> fun j => (&(par j) : Semiterm ℒₒᵣ M 2))

open HierarchySymbol in
/-- Existence of a history at which a literal code graph holds is a Sigma-one
condition on the remaining head argument. -/
private theorem definable_exists_history {k : ℕ} (A : Code (k + 2)) (out : M)
    (par : Fin k → M) :
    Σ-[1].DefinablePred
      (fun c : M => ∃ hc : M, Semiformula.Evalb (out :> hc :> c :> par) (code A)) :=
  by
  refine HierarchySymbol.Definable.exs ?_
  refine (definable_code_two_slots A out par).of_iff ?_
  intro w
  simp

/-!
### Building a correct history -/

/-- A history code whose correctness predicate takes the value one at the
recursion argument, built by Sigma-one induction on the argument.

The disjunct `a < c` lets the induction run past the range in which the step
code is assumed total. -/
private theorem exists_pos_history [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {k : ℕ} (df : Code k) (dg : Code (k + 2))
    (a : M) (v : Fin k → M) (hdf : ∃ z : M, Semiformula.Evalb (z :> v) (code df))
    (hdg : ∀ i : M, i ≤ a → ∀ z : M, ∃ w : M, Semiformula.Evalb (w :> i :> z :> v) (code dg)) :
    ∃ hc : M, Semiformula.Evalb ((1 : M) :> hc :> a :> v) (code (codePrecPredicate df dg)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  have hdef :
    Σ-[1].DefinablePred
      (fun c : M =>
        (∃ hc : M,
            Semiformula.Evalb ((1 : M) :> hc :> c :> v) (code (codePrecPredicate df dg))) ∨
          a < c) :=
    HierarchySymbol.Definable.or (definable_exists_history _ (1 : M) v) (by definability)
  have key :
    ∀ c : M,
      (∃ hc : M, Semiformula.Evalb ((1 : M) :> hc :> c :> v) (code (codePrecPredicate df dg))) ∨
        a < c :=
    by
    refine InductionOnHierarchy.succ_induction Σ 1 hdef ?_ ?_
    · obtain ⟨x, hx⟩ := hdf
      obtain ⟨hc, -, hxpair⟩ := exists_codeBeta_extension (0 : M) (0 : M) x
      refine Or.inl ⟨hc, ?_⟩
      have hhc :
        Semiformula.Evalb (hc :> hc :> (0 : M) :> v) (code (Code.proj (0 : Fin (k + 2)))) :=
        (eval_proj_iff _ _ _).mpr rfl
      have hzero :
        Semiformula.Evalb ((0 : M) :> hc :> (0 : M) :> v) (code (codeConst (n := k + 2) 0)) :=
        by rw [eval_codeConst_iff]; simp
      have hb :
        Semiformula.Evalb (x :> hc :> (0 : M) :> v)
          (code (codeBeta (Code.proj 0) (codeConst 0))) :=
        beta_of_pair _ _ x hc 0 _ hhc hzero hxpair
      have hcomp :
        Semiformula.Evalb (x :> hc :> (0 : M) :> v)
          (code (df.comp (fun j => Code.proj j.succ.succ))) :=
        by
        rw [eval_comp_iff]
        exact ⟨v, hx, fun j => (eval_proj_iff _ _ _).mpr (by simp)⟩
      rw [codePrecPredicate_eq]
      refine (eval_codeAnd_iff _ _ _ _).mpr ⟨1, 1, ?_, ?_, Or.inl ⟨by simp, rfl⟩⟩
      · exact (eval_codeEq_iff _ _ _ _).mpr ⟨x, x, hb, hcomp, Or.inl ⟨rfl, rfl⟩⟩
      · exact
          ball_pos_of_body_weak dg hc 0 v (fun t ht => absurd ht (by simp))
            (prec_step_total dg a v hdg 0 hc 0 (by simp))
    · intro c IH
      by_cases hac : a < c + 1
      · exact Or.inr hac
      · have hca1 : c + 1 ≤ a := not_lt.mp hac
        have hca : c < a := lt_of_lt_of_le (by simp) hca1
        obtain ⟨hc, hP⟩ := IH.resolve_right (not_lt.mpr (le_of_lt hca))
        have hpair :
          ∀ i : M,
            Semiformula.Evalb
              ((FFL.FirstOrder.Arithmetic.pi₁ hc %
                  ((i + 1) * FFL.FirstOrder.Arithmetic.pi₂ hc + 1)) :>
                ![hc, i])
              (code (codeBeta (Code.proj (0 : Fin 2)) (Code.proj (1 : Fin 2)))) :=
          fun i =>
          eval_codeBeta_of_values _ _ hc i ![hc, i] ((eval_proj_iff _ _ _).mpr (by simp))
            ((eval_proj_iff _ _ _).mpr (by simp))
        obtain ⟨w, hw⟩ := hdg c (le_of_lt hca) _
        obtain ⟨hc', htr, hnew⟩ := exists_codeBeta_extension hc (c + 1) w
        refine Or.inl ⟨hc', ?_⟩
        have hhc' :
          Semiformula.Evalb (hc' :> hc' :> (c + 1) :> v) (code (Code.proj (0 : Fin (k + 2)))) :=
          (eval_proj_iff _ _ _).mpr rfl
        have hzero' :
          Semiformula.Evalb ((0 : M) :> hc' :> (c + 1) :> v)
            (code (codeConst (n := k + 2) 0)) :=
          by rw [eval_codeConst_iff]; simp
        obtain ⟨x, hx0, hxdf⟩ := prec_base_of_pos df dg hc c v hP
        have hhc0 :
          Semiformula.Evalb (hc :> hc :> c :> v) (code (Code.proj (0 : Fin (k + 2)))) :=
          (eval_proj_iff _ _ _).mpr rfl
        have hzero0 :
          Semiformula.Evalb ((0 : M) :> hc :> c :> v) (code (codeConst (n := k + 2) 0)) := by
          rw [eval_codeConst_iff]; simp
        have hx0' :
          Semiformula.Evalb (x :> hc' :> (c + 1) :> v)
            (code (codeBeta (Code.proj 0) (codeConst 0))) :=
          beta_of_pair _ _ x hc' 0 _ hhc' hzero'
            (htr 0 x (by simp) (beta_to_pair _ _ x hc 0 _ hhc0 hzero0 hx0))
        have hcomp :
          Semiformula.Evalb (x :> hc' :> (c + 1) :> v)
            (code (df.comp (fun j => Code.proj j.succ.succ))) :=
          by
          rw [eval_comp_iff]
          exact ⟨v, hxdf, fun j => (eval_proj_iff _ _ _).mpr (by simp)⟩
        have hbelow :
          ∀ t : M,
            t < c + 1 →
              ∃ e : M,
                e ≠ 0 ∧
                  Semiformula.Evalb (e :> t :> hc' :> (c + 1) :> v) (code (codePrecStep dg)) :=
          by
          intro t ht
          have hidx' :
            Semiformula.Evalb (t :> t :> hc' :> (c + 1) :> v)
              (code (Code.proj (0 : Fin (k + 3)))) :=
            (eval_proj_iff _ _ _).mpr rfl
          have hhist' :
            Semiformula.Evalb (hc' :> t :> hc' :> (c + 1) :> v)
              (code (Code.proj (1 : Fin (k + 3)))) :=
            (eval_proj_iff _ _ _).mpr (by simp)
          have hsucc' :
            Semiformula.Evalb ((t + 1) :> t :> hc' :> (c + 1) :> v)
              (code (codeSucc (Code.proj (0 : Fin (k + 3))))) :=
            (eval_codeSucc_iff _ _ _).mpr ⟨t, hidx', rfl⟩
          rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp ht) with htc | rfl
          · obtain ⟨u, b, hb, hu, hdgv⟩ := prec_step_of_pos df dg hc c t v htc hP
            have hidx0 :
              Semiformula.Evalb (t :> t :> hc :> c :> v) (code (Code.proj (0 : Fin (k + 3)))) :=
              (eval_proj_iff _ _ _).mpr rfl
            have hhist0 :
              Semiformula.Evalb (hc :> t :> hc :> c :> v)
                (code (Code.proj (1 : Fin (k + 3)))) :=
              (eval_proj_iff _ _ _).mpr (by simp)
            have hsucc0 :
              Semiformula.Evalb ((t + 1) :> t :> hc :> c :> v)
                (code (codeSucc (Code.proj (0 : Fin (k + 3))))) :=
              (eval_codeSucc_iff _ _ _).mpr ⟨t, hidx0, rfl⟩
            refine ⟨1, _root_.one_ne_zero, prec_step_pos_of dg t hc' (c + 1) b u v ?_ ?_ hdgv⟩
            · exact
                beta_of_pair _ _ b hc' t _ hhist' hidx'
                  (htr t b ht (beta_to_pair _ _ b hc t _ hhist0 hidx0 hb))
            · exact
                beta_of_pair _ _ u hc' (t + 1) _ hhist' hsucc'
                  (htr (t + 1) u (by simpa using htc)
                    (beta_to_pair _ _ u hc (t + 1) _ hhist0 hsucc0 hu))
          · refine ⟨1, _root_.one_ne_zero, prec_step_pos_of dg _ hc' _ _ w v ?_ ?_ hw⟩
            · exact beta_of_pair _ _ _ hc' _ _ hhist' hidx' (htr _ _ ht (hpair _))
            · exact beta_of_pair _ _ w hc' _ _ hhist' hsucc' hnew
        rw [codePrecPredicate_eq]
        refine (eval_codeAnd_iff _ _ _ _).mpr ⟨1, 1, ?_, ?_, Or.inl ⟨by simp, rfl⟩⟩
        · exact (eval_codeEq_iff _ _ _ _).mpr ⟨x, x, hx0', hcomp, Or.inl ⟨rfl, rfl⟩⟩
        · exact
            ball_pos_of_body_weak dg hc' (c + 1) v hbelow
              (prec_step_total dg a v hdg (c + 1) hc' (c + 1) hca1)
  exact (key a).resolve_right (_root_.lt_irrefl a)

/-!
### Generic existence for the recursion constructor -/

open HierarchySymbol in
/-- `codePrec df dg` has a value at every recursion argument at which the base
code has one and the step code is total at every index up to that argument.

The step premise is uniform in the predecessor value and is required only up to
the recursion argument itself.  The index `a` is included because the eager
bounded search of `codeBall` evaluates the step there as well; nothing beyond
`a` is used. -/
theorem eval_codePrec_exists_of_total [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {k : ℕ} (df : Code k) (dg : Code (k + 2))
    (a : M) (v : Fin k → M) (hdf : ∃ z : M, Semiformula.Evalb (z :> v) (code df))
    (hdg : ∀ i : M, i ≤ a → ∀ z : M, ∃ w : M, Semiformula.Evalb (w :> i :> z :> v) (code dg)) :
    ∃ z : M, Semiformula.Evalb (z :> a :> v) (code (codePrec df dg)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  obtain ⟨hc, hP⟩ := exists_pos_history df dg a v hdf hdg
  have hdefQ :
    Σ-[1].DefinablePred
      (fun c : M =>
        Semiformula.Evalb ((1 : M) :> c :> a :> v) (code (codePrecPredicate df dg))) :=
    definable_code_head_slot _ (1 : M) (a :> v)
  obtain ⟨hc₀, hQ₀, hleast⟩ := InductionOnHierarchy.least_number Σ 1 hdefQ hP
  have hsearch :
    Semiformula.Evalb (hc₀ :> a :> v) (code (codeRfindPos (codePrecPredicate df dg))) :=
    by
    refine (eval_codeRfindPos_iff _ _ _).mpr ⟨⟨1, by simp, hQ₀⟩, ?_⟩
    intro t ht
    obtain ⟨q, hq⟩ := prec_predicate_total df dg a v hdf hdg t
    have hq0 : q = 0 := by
      rw [codePrecPredicate_eq, eval_codeAnd_iff] at hq
      obtain ⟨p, r, hp, hr, hcase⟩ := hq
      rcases hcase with ⟨hpos, -⟩ | ⟨-, h0⟩
      · refine absurd ?_ (hleast t ht)
        rw [codePrecPredicate_eq, eval_codeAnd_iff]
        exact ⟨p, r, hp, hr, Or.inl ⟨hpos, rfl⟩⟩
      · exact h0
    rwa [hq0] at hq
  have hhead : Semiformula.Evalb (hc₀ :> hc₀ :> a :> v) (code (codeHead (n := k + 1))) :=
    (eval_codeHead_iff _ _).mpr rfl
  have hlift : Semiformula.Evalb (a :> hc₀ :> a :> v) (code (codeLift (codeHead (n := k)))) :=
    (eval_codeLift_iff _ _ _ _).mpr ((eval_codeHead_iff _ _).mpr rfl)
  refine
    ⟨FFL.FirstOrder.Arithmetic.pi₁ hc₀ % ((a + 1) * FFL.FirstOrder.Arithmetic.pi₂ hc₀ + 1), ?_⟩
  rw [codePrec, eval_codeBind_iff]
  exact ⟨hc₀, hsearch, eval_codeBeta_of_values _ _ hc₀ a (hc₀ :> a :> v) hhead hlift⟩

/-!
### Halving -/

/-- `codeDiv2 A` has a value at any value of `A`.

`codeDiv2Unary` is `codePrec` with a zero base and an eager conditional on the
parity of the recursion index as step, so `eval_codePrec_exists_of_total`
applies: the step has a value at every index and every predecessor value.  Only
existence is asserted; the witness is not identified with any quotient of `a`. -/
theorem eval_codeDiv2_exists_of_value [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {k : ℕ} (A : Code k) (a : M)
    (v : Fin k → M) (hA : Semiformula.Evalb (a :> v) (code A)) :
    ∃ z : M, Semiformula.Evalb (z :> v) (code (codeDiv2 A)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  obtain ⟨w, hw⟩ :
    ∃ w : M, Semiformula.Evalb (w :> a :> (![] : Fin 0 → M)) (code codeDiv2Unary) :=
    by
    refine
      eval_codePrec_exists_of_total (Code.zero 0)
        (codeIfPos (codeBodd (Code.proj 0)) (codeSucc (Code.proj 1)) (Code.proj 1)) a ![]
        ⟨0, (eval_zero_iff _ _).mpr rfl⟩ ?_
    intro i _ z
    have hidx :
      Semiformula.Evalb (i :> i :> z :> (![] : Fin 0 → M)) (code (Code.proj (0 : Fin 2))) :=
      (eval_proj_iff _ _ _).mpr rfl
    have htwo :
      Semiformula.Evalb ((2 : M) :> i :> z :> (![] : Fin 0 → M))
        (code (codeConst (n := 2) 2)) :=
      by rw [eval_codeConst_iff]; simp
    have hbodd :
      Semiformula.Evalb ((i % 2) :> i :> z :> (![] : Fin 0 → M))
        (code (codeBodd (Code.proj (0 : Fin 2)))) :=
      eval_codeRem _ _ i 2 _ hidx htwo
    have hprev :
      Semiformula.Evalb (z :> i :> z :> (![] : Fin 0 → M)) (code (Code.proj (1 : Fin 2))) :=
      (eval_proj_iff _ _ _).mpr rfl
    have hsucc :
      Semiformula.Evalb ((z + 1) :> i :> z :> (![] : Fin 0 → M))
        (code (codeSucc (Code.proj (1 : Fin 2)))) :=
      (eval_codeSucc_iff _ _ _).mpr ⟨z, hprev, rfl⟩
    by_cases hpar : 0 < i % 2
    · exact
        ⟨z + 1,
          eval_codeIfPos_of _ _ _ (i % 2) (z + 1) z (z + 1) _ hbodd hsucc hprev
            (Or.inl ⟨hpar, rfl⟩)⟩
    · exact
        ⟨z,
          eval_codeIfPos_of _ _ _ (i % 2) (z + 1) z z _ hbodd hsucc hprev
            (Or.inr ⟨le_antisymm (not_lt.mp hpar) (by simp), rfl⟩)⟩
  refine ⟨w, (eval_comp_iff codeDiv2Unary ![A] w v).mpr ⟨![a], hw, ?_⟩⟩
  intro j
  refine Fin.cases ?_ (fun j1 => Fin.elim0 j1) j
  simpa using hA

end Existence

end ArithmeticCode
end CategoricalRiceShapiro

end

end PointwiseComposition
