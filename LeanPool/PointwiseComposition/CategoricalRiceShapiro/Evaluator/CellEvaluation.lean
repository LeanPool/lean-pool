/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.Cell
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.NumeralEvaluation
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.PartialRecursiveEvaluation
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.TableLookupEvaluation

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Success and totality of an evaluator cell

This module states two kinds of result, with different assumptions.

The success theorems describe a cell that has already reported a positive
value: the encoded `Option` is `x + 1` when the computation returned `x`.
`eval_codeOptionBind_succ_iff` and `eval_codeCompEvaluatorCell_succ_iff` use
`𝐏𝐀⁻`. `eval_codePairEvaluatorCell_succ_iff` characterises the two successful
lookups and their Cantor-pair result over `𝐈𝐎𝐩𝐞𝐧`; its proof uses the public
`eval_codePair` API at that fragment. None asserts that a cell has a value at
all.

Over `𝐏𝐀`, `eval_codeEvaluatorCell_exists_of_values` asserts exactly that: from
values for the table and the argument alone, the whole cell has a value.  The
cell is a nested eager conditional, so the proof evaluates all five branches —
base, pairing, composition, primitive recursion and minimization — together with
every lookup and every option continuation inside them, whichever branch the tag
comparisons end up selecting.  It asserts existence only and identifies no
value.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace Evaluator

open CategoricalRiceShapiro.ArithmeticCode

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

variable {M : Type*} [ORingStructure M]

/-- A successful bind on an encoded option: the bound code succeeds with some
value, and the body succeeds at that value. -/
theorem eval_codeOptionBind_succ_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {n : ℕ} (dopt : Code n)
    (dk : Code (n + 1)) (y : M) (v : Fin n → M) :
    Semiformula.Evalb ((y + 1) :> v) (code (codeOptionBind dopt dk)) ↔
      ∃ x : M,
        Semiformula.Evalb ((x + 1) :> v) (code dopt) ∧
          Semiformula.Evalb ((y + 1) :> x :> v) (code dk) :=
  by
  have hposS : ∀ a : M, (0 : M) < a + 1 := fun a =>
    lt_of_lt_of_le _root_.zero_lt_one le_add_self
  have hsubC :
    ∀ a : M,
      Semiformula.Evalb ((a + 1) :> v) (code dopt) →
        Semiformula.Evalb (a :> v) (code (codeSub dopt (Code.one n))) :=
    by
    intro a hdopt
    simp only [codeSub]
    rw [eval_codeRfindPos_iff]
    have hLiftD : ∀ t : M, Semiformula.Evalb ((a + 1) :> t :> v) (code (codeLift dopt)) :=
      fun t => (eval_codeLift_iff dopt (a + 1) t v).mpr hdopt
    have hLiftOne :
      ∀ t : M, Semiformula.Evalb ((1 : M) :> t :> v) (code (codeLift (Code.one n))) := fun t =>
      (eval_codeLift_iff _ 1 t v).mpr ((eval_one_iff 1 v).mpr rfl)
    have hHeadv : ∀ t : M, Semiformula.Evalb (t :> t :> v) (code (codeHead (n := n))) :=
      fun t => (eval_codeHead_iff t (t :> v)).mpr rfl
    have hSum :
      ∀ t : M,
        Semiformula.Evalb ((t + 1) :> t :> v)
          (code (codeAdd (codeHead (n := n)) (codeLift (Code.one n)))) :=
      fun t => (eval_codeAdd_iff _ _ (t + 1) (t :> v)).mpr ⟨t, 1, hHeadv t, hLiftOne t, rfl⟩
    have hNotLtOne : ¬(a + 1 < (1 : M)) := not_lt.mpr le_add_self
    have hLtPart :
      ∀ t : M,
        Semiformula.Evalb ((0 : M) :> t :> v)
          (code (codeLt (codeLift dopt) (codeLift (Code.one n)))) :=
      fun t =>
      (eval_codeLt_iff _ _ 0 (t :> v)).mpr
        ⟨a + 1, 1, hLiftD t, hLiftOne t, Or.inr ⟨hNotLtOne, rfl⟩⟩
    have hBPart :
      ∀ t : M,
        Semiformula.Evalb ((0 : M) :> t :> v)
          (code
            (codeAnd (codeLt (codeLift dopt) (codeLift (Code.one n)))
              (codeEq (codeHead (n := n)) (Code.zero (n + 1))))) :=
      by
      intro t
      by_cases ht : t = (0 : M)
      · exact
          (eval_codeAnd_iff _ _ 0 (t :> v)).mpr
            ⟨0, 1, hLtPart t,
              (eval_codeEq_iff _ _ 1 (t :> v)).mpr
                ⟨t, 0, hHeadv t, (eval_zero_iff 0 (t :> v)).mpr rfl, Or.inl ⟨ht, rfl⟩⟩,
              Or.inr ⟨by simp, rfl⟩⟩
      · exact
          (eval_codeAnd_iff _ _ 0 (t :> v)).mpr
            ⟨0, 0, hLtPart t,
              (eval_codeEq_iff _ _ 0 (t :> v)).mpr
                ⟨t, 0, hHeadv t, (eval_zero_iff 0 (t :> v)).mpr rfl, Or.inr ⟨ht, rfl⟩⟩,
              Or.inr ⟨by simp, rfl⟩⟩
    have hAPart :
      ∀ (t w : M),
        ((t + 1 = a + 1 ∧ w = 1) ∨ (¬t + 1 = a + 1 ∧ w = 0)) →
          Semiformula.Evalb (w :> t :> v)
            (code
              (codeEq (codeAdd (codeHead (n := n)) (codeLift (Code.one n))) (codeLift dopt))) :=
      fun t w hcase =>
      (eval_codeEq_iff _ _ w (t :> v)).mpr ⟨t + 1, a + 1, hSum t, hLiftD t, hcase⟩
    constructor
    · exact
        ⟨1, by simp,
          (eval_codeOr_iff _ _ 1 (a :> v)).mpr
            ⟨1, 0, hAPart a 1 (Or.inl ⟨rfl, rfl⟩), hBPart a, Or.inl ⟨by simp, rfl⟩⟩⟩
    · intro t ht
      have hne : ¬t + 1 = a + 1 := fun h => absurd (add_right_cancel h) (ne_of_lt ht)
      exact
        (eval_codeOr_iff _ _ 0 (t :> v)).mpr
          ⟨0, 0, hAPart t 0 (Or.inr ⟨hne, rfl⟩), hBPart t, Or.inr ⟨by simp, rfl⟩⟩
  constructor
  · intro hb
    rw [codeOptionBind, codeIfPos, eval_codeAdd_iff] at hb
    obtain ⟨p, q, hp, hq, hsum⟩ := hb
    rw [eval_codeMul_iff] at hp
    obtain ⟨pp, gg, hpp, hgg, hpv⟩ := hp
    rw [eval_codeMul_iff] at hq
    obtain ⟨ii, hh, hii, hhh, hqv⟩ := hq
    have hhh0 : hh = 0 := (eval_zero_iff hh v).mp hhh
    have hq0 : q = 0 := by rw [hqv, hhh0, mul_zero]
    rw [eval_codePos_iff] at hpp
    obtain ⟨a, ha, hcase⟩ := hpp
    rcases hcase with ⟨hpos, hpp1⟩ | ⟨-, hpp0⟩
    · have hy : y + 1 = gg := by rw [hsum, hq0, add_zero, hpv, hpp1, one_mul]
      rw [← hy, eval_codeBind_iff] at hgg
      obtain ⟨x, hx, hdk⟩ := hgg
      obtain ⟨x', hax⟩ := FFL.FirstOrder.Arithmetic.eq_succ_of_pos hpos
      rw [hax] at ha
      have hxx : x = x' := eval_unique hx (hsubC x' ha)
      rw [hxx] at hdk
      exact ⟨x', ha, hdk⟩
    · exfalso
      have hz : y + 1 = 0 := by rw [hsum, hq0, add_zero, hpv, hpp0, zero_mul]
      exact absurd hz (ne_of_gt (hposS y))
  · rintro ⟨x, hdopt, hdk⟩
    rw [codeOptionBind, codeIfPos, eval_codeAdd_iff]
    refine ⟨y + 1, 0, ?_, ?_, by simp⟩
    · rw [eval_codeMul_iff]
      refine ⟨1, y + 1, ?_, ?_, by simp⟩
      · exact (eval_codePos_iff _ 1 v).mpr ⟨x + 1, hdopt, Or.inl ⟨hposS x, rfl⟩⟩
      · rw [eval_codeBind_iff]
        exact ⟨x, hsubC x hdopt, hdk⟩
    · rw [eval_codeMul_iff]
      refine ⟨0, 0, ?_, (eval_zero_iff 0 v).mpr rfl, by simp⟩
      exact (eval_codeInv_iff _ 0 v).mpr ⟨x + 1, hdopt, Or.inr ⟨ne_of_gt (hposS x), rfl⟩⟩

/-- Success of the pairing branch: the first index succeeds on the argument, the
second index succeeds on the same argument, and the cell reports the Cantor pair
of the two results. -/
theorem eval_codePairEvaluatorCell_succ_iff [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {r : ℕ}
    (dtable dk dcf dcg dn : Code r) (y : M) (v : Fin r → M) :
    Semiformula.Evalb ((y + 1) :> v) (code (codePairEvaluatorCell dtable dk dcf dcg dn)) ↔
      ∃ a b : M,
        Semiformula.Evalb ((a + 1) :> v) (code (codeTableLookup dtable dk dcf dn)) ∧
          Semiformula.Evalb ((b + 1) :> a :> v)
              (code
                (codeTableLookup (codeLift dtable) (codeLift dk) (codeLift dcg)
                  (codeLift dn))) ∧
            y = FFL.FirstOrder.Arithmetic.pair a b :=
  by
  rw [codePairEvaluatorCell, eval_codeOptionBind_succ_iff]
  constructor
  · rintro ⟨a, ha, hbody⟩
    rw [eval_codeOptionBind_succ_iff] at hbody
    obtain ⟨b, hb, hsucc⟩ := hbody
    rw [eval_codeSucc_iff] at hsucc
    obtain ⟨p, hp, hyp⟩ := hsucc
    refine ⟨a, b, ha, hb, ?_⟩
    have hpa : Semiformula.Evalb (a :> (b :> a :> v)) (code (Code.proj (1 : Fin (r + 2)))) :=
      (eval_proj_iff (1 : Fin (r + 2)) a (b :> a :> v)).mpr (by simp)
    have hpb : Semiformula.Evalb (b :> (b :> a :> v)) (code (Code.proj (0 : Fin (r + 2)))) :=
      (eval_proj_iff (0 : Fin (r + 2)) b (b :> a :> v)).mpr (by simp)
    have hpair :=
      eval_codePair (M := M) (Code.proj (1 : Fin (r + 2))) (Code.proj (0 : Fin (r + 2))) a b
        (b :> a :> v) hpa hpb
    have hpeq : p = FFL.FirstOrder.Arithmetic.pair a b := eval_unique hp hpair
    exact add_right_cancel (hyp.trans (by rw [hpeq]))
  · rintro ⟨a, b, ha, hb, hy⟩
    refine ⟨a, ha, ?_⟩
    rw [eval_codeOptionBind_succ_iff]
    refine ⟨b, hb, ?_⟩
    rw [eval_codeSucc_iff]
    have hpa : Semiformula.Evalb (a :> (b :> a :> v)) (code (Code.proj (1 : Fin (r + 2)))) :=
      (eval_proj_iff (1 : Fin (r + 2)) a (b :> a :> v)).mpr (by simp)
    have hpb : Semiformula.Evalb (b :> (b :> a :> v)) (code (Code.proj (0 : Fin (r + 2)))) :=
      (eval_proj_iff (0 : Fin (r + 2)) b (b :> a :> v)).mpr (by simp)
    exact
      ⟨FFL.FirstOrder.Arithmetic.pair a b, eval_codePair (M := M) _ _ a b (b :> a :> v) hpa hpb,
        by rw [hy]⟩

/-- Success of the composition branch: the inner index succeeds on the argument,
and the outer index succeeds on that intermediate value. -/
theorem eval_codeCompEvaluatorCell_succ_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ}
    (dtable dk dcf dcg dn : Code r) (y : M) (v : Fin r → M) :
    Semiformula.Evalb ((y + 1) :> v) (code (codeCompEvaluatorCell dtable dk dcf dcg dn)) ↔
      ∃ x : M,
        Semiformula.Evalb ((x + 1) :> v) (code (codeTableLookup dtable dk dcg dn)) ∧
          Semiformula.Evalb ((y + 1) :> x :> v)
            (code
              (codeTableLookup (codeLift dtable) (codeLift dk) (codeLift dcf)
                (codeHead (n := r)))) :=
  by
  simpa only [codeCompEvaluatorCell] using
    eval_codeOptionBind_succ_iff (M := M) (dopt := codeTableLookup dtable dk dcg dn) (dk :=
      codeTableLookup (codeLift dtable) (codeLift dk) (codeLift dcf) (codeHead (n := r))) y v

/-!
### Totality of an evaluator cell -/

/-- The characteristic value of an equality exists once both sides have one. -/
private theorem eval_codeEq_exists [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {n : ℕ} (A B : Code n) (a b : M)
    (v : Fin n → M) (hA : Semiformula.Evalb (a :> v) (code A))
    (hB : Semiformula.Evalb (b :> v) (code B)) :
    ∃ z : M, Semiformula.Evalb (z :> v) (code (codeEq A B)) :=
  by
  by_cases hab : a = b
  · exact ⟨1, (eval_codeEq_iff _ _ _ _).mpr ⟨a, b, hA, hB, Or.inl ⟨hab, rfl⟩⟩⟩
  · exact ⟨0, (eval_codeEq_iff _ _ _ _).mpr ⟨a, b, hA, hB, Or.inr ⟨hab, rfl⟩⟩⟩

/-- The base-constructor cell has a value at any table and argument values.

Every arm of the nested eager conditional is evaluated: the four successor
readings of the argument and the two constants, together with the four tag
comparisons. -/
private theorem eval_codeBaseEvaluatorCell_exists [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {r : ℕ} (dtable dn : Code r)
    (table index : M) (v : Fin r → M) (htable : Semiformula.Evalb (table :> v) (code dtable))
    (hindex : Semiformula.Evalb (index :> v) (code dn)) :
    ∃ z : M, Semiformula.Evalb (z :> v) (code (codeBaseEvaluatorCell dtable dn)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  obtain ⟨p, hp⟩ := eval_codeListLength_exists_of_value dtable table v htable
  have hk := eval_codeUnpair₁ (codeListLength dtable) p v hp
  have hq := eval_codeUnpair₂ (codeListLength dtable) p v hp
  obtain ⟨tg, htag⟩ :=
    eval_codePartrecTag_exists_of_value (codeUnpair₂ (codeListLength dtable)) _ v hq
  have hsucc2 : Semiformula.Evalb ((index + 1 + 1) :> v) (code (codeSucc (codeSucc dn))) :=
    (eval_codeSucc_iff _ _ _).mpr
      ⟨index + 1, (eval_codeSucc_iff _ _ _).mpr ⟨index, hindex, rfl⟩, rfl⟩
  have hsuccu1 :
    Semiformula.Evalb ((FFL.FirstOrder.Arithmetic.pi₁ index + 1) :> v)
      (code (codeSucc (codeUnpair₁ dn))) :=
    (eval_codeSucc_iff _ _ _).mpr ⟨_, eval_codeUnpair₁ dn index v hindex, rfl⟩
  have hsuccu2 :
    Semiformula.Evalb ((FFL.FirstOrder.Arithmetic.pi₂ index + 1) :> v)
      (code (codeSucc (codeUnpair₂ dn))) :=
    (eval_codeSucc_iff _ _ _).mpr ⟨_, eval_codeUnpair₂ dn index v hindex, rfl⟩
  have hcmp :
    ∀ m : ℕ,
      ∃ z : M,
        Semiformula.Evalb (z :> v)
          (code
            (codeEq (codePartrecTag (codeUnpair₂ (codeListLength dtable)))
              (codeConst (n := r) m))) :=
    fun m => eval_codeEq_exists _ _ tg _ v htag (eval_codeConst m v)
  refine eval_codeIfPos_exists _ _ _ v ⟨_, hk⟩ ?_ ⟨_, eval_codeConst 0 v⟩
  refine eval_codeIfPos_exists _ _ _ v (hcmp 0) ⟨_, eval_codeConst 1 v⟩ ?_
  refine eval_codeIfPos_exists _ _ _ v (hcmp 1) ⟨_, hsucc2⟩ ?_
  refine eval_codeIfPos_exists _ _ _ v (hcmp 2) ⟨_, hsuccu1⟩ ?_
  exact eval_codeIfPos_exists _ _ _ v (hcmp 3) ⟨_, hsuccu2⟩ ⟨_, eval_codeConst 0 v⟩

/-- The pairing cell has a value: the two lookups have values, and the
continuation pairs the two payloads.  The inner bind is constructed at the
payload of the outer one, so both option layers are supplied. -/
private theorem eval_codePairEvaluatorCell_exists [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {r : ℕ}
    (dtable dk dcf dcg dn : Code r) (table kv cf cg index : M) (v : Fin r → M)
    (htable : Semiformula.Evalb (table :> v) (code dtable))
    (hk : Semiformula.Evalb (kv :> v) (code dk)) (hcf : Semiformula.Evalb (cf :> v) (code dcf))
    (hcg : Semiformula.Evalb (cg :> v) (code dcg))
    (hn : Semiformula.Evalb (index :> v) (code dn)) :
    ∃ z : M, Semiformula.Evalb (z :> v) (code (codePairEvaluatorCell dtable dk dcf dcg dn)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  obtain ⟨o₁, ho₁⟩ :=
    eval_codeTableLookup_exists_of_values dtable dk dcf dn table kv cf index v htable hk hcf hn
  refine eval_codeOptionBind_exists_of_value _ _ o₁ v ho₁ ?_
  have hL :
    ∀ (X : Code r) (x : M),
      Semiformula.Evalb (x :> v) (code X) →
        Semiformula.Evalb (x :> (o₁ - 1) :> v) (code (codeLift X)) :=
    fun X x hx => (eval_codeLift_iff X x (o₁ - 1) v).mpr hx
  obtain ⟨o₂, ho₂⟩ :=
    eval_codeTableLookup_exists_of_values (codeLift dtable) (codeLift dk) (codeLift dcg)
      (codeLift dn) table kv cg index ((o₁ - 1) :> v) (hL _ _ htable) (hL _ _ hk) (hL _ _ hcg)
      (hL _ _ hn)
  refine eval_codeOptionBind_exists_of_value _ _ o₂ ((o₁ - 1) :> v) ho₂ ?_
  exact
    ⟨_,
      (eval_codeSucc_iff _ _ _).mpr
        ⟨_,
          eval_codePair (Code.proj (1 : Fin (r + 2))) (Code.proj (0 : Fin (r + 2))) (o₁ - 1)
            (o₂ - 1) ((o₂ - 1) :> (o₁ - 1) :> v) ((eval_proj_iff _ _ _).mpr (by simp))
            ((eval_proj_iff _ _ _).mpr rfl),
          rfl⟩⟩

/-- The composition cell has a value: the inner lookup has one, and the outer
lookup is constructed at its payload. -/
private theorem eval_codeCompEvaluatorCell_exists [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {r : ℕ}
    (dtable dk dcf dcg dn : Code r) (table kv cf cg index : M) (v : Fin r → M)
    (htable : Semiformula.Evalb (table :> v) (code dtable))
    (hk : Semiformula.Evalb (kv :> v) (code dk)) (hcf : Semiformula.Evalb (cf :> v) (code dcf))
    (hcg : Semiformula.Evalb (cg :> v) (code dcg))
    (hn : Semiformula.Evalb (index :> v) (code dn)) :
    ∃ z : M, Semiformula.Evalb (z :> v) (code (codeCompEvaluatorCell dtable dk dcf dcg dn)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  obtain ⟨o₁, ho₁⟩ :=
    eval_codeTableLookup_exists_of_values dtable dk dcg dn table kv cg index v htable hk hcg hn
  refine eval_codeOptionBind_exists_of_value _ _ o₁ v ho₁ ?_
  have hL :
    ∀ (X : Code r) (x : M),
      Semiformula.Evalb (x :> v) (code X) →
        Semiformula.Evalb (x :> (o₁ - 1) :> v) (code (codeLift X)) :=
    fun X x hx => (eval_codeLift_iff X x (o₁ - 1) v).mpr hx
  exact
    eval_codeTableLookup_exists_of_values (codeLift dtable) (codeLift dk) (codeLift dcf)
      (codeHead (n := r)) table kv cf (o₁ - 1) ((o₁ - 1) :> v) (hL _ _ htable) (hL _ _ hk)
      (hL _ _ hcf) ((eval_codeHead_iff _ _).mpr rfl)

/-- The primitive-recursion cell has a value.  Both arms of its eager
conditional are evaluated: the step lookup with its continuation, and the base
lookup. -/
theorem eval_codePrecEvaluatorCell_exists [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {r : ℕ}
    (dtable dk' dq dcf dcg dn : Code r) (table k' qv cf cg index : M) (v : Fin r → M)
    (htable : Semiformula.Evalb (table :> v) (code dtable))
    (hk' : Semiformula.Evalb (k' :> v) (code dk')) (hq : Semiformula.Evalb (qv :> v) (code dq))
    (hcf : Semiformula.Evalb (cf :> v) (code dcf))
    (hcg : Semiformula.Evalb (cg :> v) (code dcg))
    (hn : Semiformula.Evalb (index :> v) (code dn)) :
    ∃ z : M,
      Semiformula.Evalb (z :> v) (code (codePrecEvaluatorCell dtable dk' dq dcf dcg dn)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  have hz := eval_codeUnpair₁ dn index v hn
  have ht := eval_codeUnpair₂ dn index v hn
  have hy := eval_codeSub (codeUnpair₂ dn) (codeConst 1) _ _ v ht (eval_codeConst 1 v)
  have hdk : Semiformula.Evalb ((k' + 1) :> v) (code (codeSucc dk')) :=
    (eval_codeSucc_iff _ _ _).mpr ⟨k', hk', rfl⟩
  have hzy :=
    eval_codePair (codeUnpair₁ dn) (codeSub (codeUnpair₂ dn) (codeConst 1)) _ _ v hz hy
  refine eval_codeIfPos_exists _ _ _ v ⟨_, ht⟩ ?_ ?_
  · obtain ⟨o₁, ho₁⟩ :=
      eval_codeTableLookup_exists_of_values dtable dk' dq
        (codePair (codeUnpair₁ dn) (codeSub (codeUnpair₂ dn) (codeConst 1))) table k' qv _ v
        htable hk' hq hzy
    refine eval_codeOptionBind_exists_of_value _ _ o₁ v ho₁ ?_
    have hL :
      ∀ (X : Code r) (x : M),
        Semiformula.Evalb (x :> v) (code X) →
          Semiformula.Evalb (x :> (o₁ - 1) :> v) (code (codeLift X)) :=
      fun X x hx => (eval_codeLift_iff X x (o₁ - 1) v).mpr hx
    have hinner :=
      eval_codePair (codeLift (codeSub (codeUnpair₂ dn) (codeConst 1))) (codeHead (n := r)) _
        (o₁ - 1) ((o₁ - 1) :> v) (hL _ _ hy) ((eval_codeHead_iff _ _).mpr rfl)
    exact
      eval_codeTableLookup_exists_of_values (codeLift dtable) (codeLift (codeSucc dk'))
        (codeLift dcg)
        (codePair (codeLift (codeUnpair₁ dn))
          (codePair (codeLift (codeSub (codeUnpair₂ dn) (codeConst 1))) (codeHead (n := r))))
        table (k' + 1) cg _ ((o₁ - 1) :> v) (hL _ _ htable) (hL _ _ hdk) (hL _ _ hcg)
        (eval_codePair _ _ _ _ ((o₁ - 1) :> v) (hL _ _ hz) hinner)
  · exact
      eval_codeTableLookup_exists_of_values dtable (codeSucc dk') dcf (codeUnpair₁ dn) table
        (k' + 1) cf _ v htable hdk hcf hz

/-- The minimization cell has a value.  Its continuation is an eager
conditional, so the recursive lookup and the returned successor are both
evaluated. -/
private theorem eval_codeRfindEvaluatorCell_exists [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {r : ℕ}
    (dtable dk' dq dcf dn : Code r) (table k' qv cf index : M) (v : Fin r → M)
    (htable : Semiformula.Evalb (table :> v) (code dtable))
    (hk' : Semiformula.Evalb (k' :> v) (code dk')) (hq : Semiformula.Evalb (qv :> v) (code dq))
    (hcf : Semiformula.Evalb (cf :> v) (code dcf))
    (hn : Semiformula.Evalb (index :> v) (code dn)) :
    ∃ z : M, Semiformula.Evalb (z :> v) (code (codeRfindEvaluatorCell dtable dk' dq dcf dn)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  have hz := eval_codeUnpair₁ dn index v hn
  have hm := eval_codeUnpair₂ dn index v hn
  have hdk : Semiformula.Evalb ((k' + 1) :> v) (code (codeSucc dk')) :=
    (eval_codeSucc_iff _ _ _).mpr ⟨k', hk', rfl⟩
  have hzm := eval_codePair (codeUnpair₁ dn) (codeUnpair₂ dn) _ _ v hz hm
  obtain ⟨o₁, ho₁⟩ :=
    eval_codeTableLookup_exists_of_values dtable (codeSucc dk') dcf
      (codePair (codeUnpair₁ dn) (codeUnpair₂ dn)) table (k' + 1) cf _ v htable hdk hcf hzm
  refine eval_codeOptionBind_exists_of_value _ _ o₁ v ho₁ ?_
  have hL :
    ∀ (X : Code r) (x : M),
      Semiformula.Evalb (x :> v) (code X) →
        Semiformula.Evalb (x :> (o₁ - 1) :> v) (code (codeLift X)) :=
    fun X x hx => (eval_codeLift_iff X x (o₁ - 1) v).mpr hx
  have hsuccm :
    Semiformula.Evalb ((FFL.FirstOrder.Arithmetic.pi₂ index + 1) :> (o₁ - 1) :> v)
      (code (codeSucc (codeLift (codeUnpair₂ dn)))) :=
    (eval_codeSucc_iff _ _ _).mpr ⟨_, hL _ _ hm, rfl⟩
  refine
    eval_codeIfPos_exists _ _ _ ((o₁ - 1) :> v) ⟨_, (eval_codeHead_iff _ _).mpr rfl⟩ ?_
      ⟨_, hsuccm⟩
  exact
    eval_codeTableLookup_exists_of_values (codeLift dtable) (codeLift dk') (codeLift dq)
      (codePair (codeLift (codeUnpair₁ dn)) (codeSucc (codeLift (codeUnpair₂ dn)))) table k' qv
      _ ((o₁ - 1) :> v) (hL _ _ htable) (hL _ _ hk') (hL _ _ hq)
      (eval_codePair _ _ _ _ ((o₁ - 1) :> v) (hL _ _ hz) hsuccm)

/-- An evaluator cell has a value at any table and argument values.

The cell is a nested eager conditional, so every one of its five branches is
evaluated before the tag comparisons select one, and each branch in turn
supplies every lookup and every option continuation it contains.  Only
existence is asserted: nothing here decodes the table, the index, or the
program, and no value is identified. -/
theorem eval_codeEvaluatorCell_exists_of_values {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀]
    {r : ℕ} (dtable dn : Code r) (table index : M) (v : Fin r → M)
    (htable : Semiformula.Evalb (table :> v) (code dtable))
    (hindex : Semiformula.Evalb (index :> v) (code dn)) :
    ∃ z : M, Semiformula.Evalb (z :> v) (code (codeEvaluatorCell dtable dn)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  obtain ⟨p, hp⟩ := eval_codeListLength_exists_of_value dtable table v htable
  have hk := eval_codeUnpair₁ (codeListLength dtable) p v hp
  have hq := eval_codeUnpair₂ (codeListLength dtable) p v hp
  have hk' :=
    eval_codeSub (codeUnpair₁ (codeListLength dtable)) (codeConst 1) _ _ v hk
      (eval_codeConst 1 v)
  obtain ⟨tg, htag⟩ :=
    eval_codePartrecTag_exists_of_value (codeUnpair₂ (codeListLength dtable)) _ v hq
  obtain ⟨cf, hcf⟩ :=
    eval_codePartrecPayload₁_exists_of_value (codeUnpair₂ (codeListLength dtable)) _ v hq
  obtain ⟨cg, hcg⟩ :=
    eval_codePartrecPayload₂_exists_of_value (codeUnpair₂ (codeListLength dtable)) _ v hq
  obtain ⟨pl, hpl⟩ :=
    eval_codePartrecPayload_exists_of_value (codeUnpair₂ (codeListLength dtable)) _ v hq
  have hcmp :
    ∀ m : ℕ,
      ∃ z : M,
        Semiformula.Evalb (z :> v)
          (code
            (codeEq (codePartrecTag (codeUnpair₂ (codeListLength dtable)))
              (codeConst (n := r) m))) :=
    fun m => eval_codeEq_exists _ _ tg _ v htag (eval_codeConst m v)
  refine eval_codeIfPos_exists _ _ _ v ⟨_, hk⟩ ?_ ⟨_, eval_codeConst 0 v⟩
  refine
    eval_codeIfPos_exists _ _ _ v (hcmp 4)
      (eval_codePairEvaluatorCell_exists _ _ _ _ _ _ _ _ _ _ v htable hk hcf hcg hindex) ?_
  refine
    eval_codeIfPos_exists _ _ _ v (hcmp 5)
      (eval_codeCompEvaluatorCell_exists _ _ _ _ _ _ _ _ _ _ v htable hk hcf hcg hindex) ?_
  refine
    eval_codeIfPos_exists _ _ _ v (hcmp 6)
      (eval_codePrecEvaluatorCell_exists _ _ _ _ _ _ _ _ _ _ _ _ v htable hk' hq hcf hcg hindex)
      ?_
  exact
    eval_codeIfPos_exists _ _ _ v (hcmp 7)
      (eval_codeRfindEvaluatorCell_exists _ _ _ _ _ _ _ _ _ _ v htable hk' hq hpl hindex)
      (eval_codeBaseEvaluatorCell_exists dtable dn table index v htable hindex)

end Evaluator
end CategoricalRiceShapiro

end

end PointwiseComposition
