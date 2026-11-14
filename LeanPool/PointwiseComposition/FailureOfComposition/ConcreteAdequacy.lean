/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteConstructorGraphs
public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteRecursionGraph
public import LeanPool.PointwiseComposition.FailureOfComposition.KleeneNormalForm

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Standard-model adequacy of the concrete evaluator graph.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

open Encodable Denumerable

open CategoricalRiceShapiro.Evaluator CategoricalRiceShapiro.ArithmeticCode

open CategoricalRiceShapiro.PartialRecursive

open FailureOfComposition.ConcreteWitnessGraphs

namespace FailureOfComposition
namespace ConcreteEvaluator

/-- The accepted computation formula interpreted over the natural numbers. -/
def stageComputation (s q x y : ℕ) : Prop :=
  Semiformula.Evalb ![s, q, x, y] (evalnCertificateFormula : ArithmeticSemisentence 4)

private theorem nat_pi₁ (x : ℕ) : FFL.FirstOrder.Arithmetic.pi₁ x = x.unpair.1 :=
  by
  have h : FFL.FirstOrder.Arithmetic.pair x.unpair.1 x.unpair.2 = x := by
    rw [nat_pair_eq, Nat.pair_unpair]
  rw [← h, FFL.FirstOrder.Arithmetic.pi₁_pair]
  rw [h]

private theorem nat_pi₂ (x : ℕ) : FFL.FirstOrder.Arithmetic.pi₂ x = x.unpair.2 :=
  by
  have h : FFL.FirstOrder.Arithmetic.pair x.unpair.1 x.unpair.2 = x := by
    rw [nat_pair_eq, Nat.pair_unpair]
  rw [← h, FFL.FirstOrder.Arithmetic.pi₂_pair]
  rw [h]

private theorem rfind_tag (c : Nat.Partrec.Code) :
    partrecCodeTag (encode (Nat.Partrec.Code.rfind' c)) = 7 :=
  by
  have hb (n : ℕ) : n.bodd.toNat = n % 2 := by rw [Nat.mod_two_of_bodd]
  simp only [Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.encodeCode]
  have h : ¬2 * (2 * Nat.Partrec.Code.encodeCode c + 1) + 1 + 4 < 4 := by omega
  simp only [partrecCodeTag, h, ite_false, hb, Nat.div2_val]
  omega

private theorem rfind_payload (c : Nat.Partrec.Code) :
    partrecCodePayload (encode (Nat.Partrec.Code.rfind' c)) = encode c :=
  by
  simp only [Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.encodeCode, partrecCodePayload,
    Nat.div2_val]
  omega

private theorem stage_zero (q x y : ℕ) : ¬stageComputation 0 q x y :=
  by
  intro h
  have hh := (evalnCertificateFormula_eval_history_iff (0 : ℕ) q x y).mp h
  have hx := ((eval_codeHistoryEvaluator_succ_iff_cell (0 : ℕ) q x y).mp hh).1
  exact Nat.not_lt_zero x hx

private theorem stage_rfind_succ (c : Nat.Partrec.Code) (k x y : ℕ) :
    stageComputation (k + 1) (encode (Nat.Partrec.Code.rfind' c)) x y ↔
      x ≤ k ∧
        ∃ v : ℕ,
          stageComputation (k + 1) (encode c) x v ∧
            ((v ≠ 0 ∧
                stageComputation k (encode (Nat.Partrec.Code.rfind' c))
                  (Nat.pair x.unpair.1 (x.unpair.2 + 1)) y) ∨
              (v = 0 ∧ y = x.unpair.2)) :=
  by
  have h :=
    evalnCertificateFormula_tag_seven_iff (M := ℕ) (encode (Nat.Partrec.Code.rfind' c))
      (rfind_tag c) (k + 1) x y (by omega)
  simp only [rfind_payload, natCast_nat, add_sub_self, nat_pi₁, nat_pi₂, nat_pair_eq,
    Nat.lt_succ_iff, Nat.pos_iff_ne_zero] at h
  exact h

private theorem stage_base (q : ℕ) (hq : q < 4) (s x y : ℕ) :
    stageComputation s q x y ↔ x < s ∧ y = baseOutput q x :=
  by
  have h := base_computation_iff (M := ℕ) q hq s x y
  simp only [natCast_nat] at h
  exact h

private theorem stage_pair (f g : Nat.Partrec.Code) (s x y : ℕ) :
    stageComputation s (encode (Nat.Partrec.Code.pair f g)) x y ↔
      ∃ a b : ℕ,
        stageComputation s (encode f) x a ∧
          stageComputation s (encode g) x b ∧ y = Nat.pair a b :=
  by
  have h := evalnCertificateFormula_pair_iff (M := ℕ) f g s x y
  simp only [natCast_nat, nat_pair_eq] at h
  exact h

private theorem stage_comp (f g : Nat.Partrec.Code) (s x y : ℕ) :
    stageComputation s (encode (Nat.Partrec.Code.comp f g)) x y ↔
      ∃ a : ℕ, stageComputation s (encode g) x a ∧ stageComputation s (encode f) a y :=
  by
  have h :=
    evalnCertificateFormula_canonicalPartrecCompIndex_iff (M := ℕ) s x y (encode f) (encode g)
  simp only [numeral_eq_natCast_app, natCast_nat, canonicalPartrecCompIndex,
    Denumerable.ofNat_encode] at h
  exact h

private theorem stage_prec_zero (f g : Nat.Partrec.Code) (k a y : ℕ) :
    stageComputation (k + 1) (encode (Nat.Partrec.Code.prec f g)) (Nat.pair a 0) y ↔
      Nat.pair a 0 ≤ k ∧ stageComputation (k + 1) (encode f) a y :=
  by
  have h :=
    evaln_tag_six_zero_iff (M := ℕ) (canonicalPartrecPrecIndex (encode f) (encode g))
      (canonicalPartrecPrecIndex_constructor_number _ _) (k + 1) a y (by omega)
  simp only [canonicalPartrecPrecIndex_base_index, natCast_nat, nat_pair_eq,
    Nat.lt_succ_iff] at h
  simp only [canonicalPartrecPrecIndex, Denumerable.ofNat_encode] at h
  exact h

private theorem stage_prec_succ (f g : Nat.Partrec.Code) (k a b y : ℕ) :
    stageComputation (k + 1) (encode (Nat.Partrec.Code.prec f g)) (Nat.pair a (b + 1)) y ↔
      Nat.pair a (b + 1) ≤ k ∧
        ∃ v : ℕ,
          stageComputation k (encode (Nat.Partrec.Code.prec f g)) (Nat.pair a b) v ∧
            stageComputation (k + 1) (encode g) (Nat.pair a (Nat.pair b v)) y :=
  by
  have h :=
    evaln_tag_six_succ_iff (M := ℕ) (canonicalPartrecPrecIndex (encode f) (encode g))
      (canonicalPartrecPrecIndex_constructor_number _ _) k a b y
  simp only [canonicalPartrecPrecIndex_step_index, natCast_nat, nat_pair_eq, ] at h
  simp only [canonicalPartrecPrecIndex, Denumerable.ofNat_encode] at h
  exact h.trans (and_congr (by omega) Iff.rfl)

/-- Exact finite-stage correspondence with Mathlib's evaluator. -/
theorem stageComputation_iff_evaln (s : ℕ) (c : Nat.Partrec.Code) (x y : ℕ) :
    stageComputation s (encode c) x y ↔ y ∈ Nat.Partrec.Code.evaln s c x := by
  induction s generalizing c x y with
  | zero => simp [stage_zero, Nat.Partrec.Code.evaln]
  | succ k ih =>
    induction c generalizing x y with
    | zero =>
      rw [show encode Nat.Partrec.Code.zero = 0 from rfl, stage_base 0 (by decide)]
      simp [baseOutput, Nat.Partrec.Code.evaln, bind, Option.bind_eq_some_iff,
        Option.guard_eq_some', Option.some.injEq]
      omega
    | succ =>
      rw [show encode Nat.Partrec.Code.succ = 1 from rfl, stage_base 1 (by decide)]
      simp [baseOutput, Nat.Partrec.Code.evaln, bind, Option.bind_eq_some_iff,
        Option.guard_eq_some', Option.some.injEq]
      omega
    | left =>
      rw [show encode Nat.Partrec.Code.left = 2 from rfl, stage_base 2 (by decide)]
      simp [baseOutput, nat_pi₁, Nat.Partrec.Code.evaln, bind, Option.bind_eq_some_iff,
        Option.guard_eq_some', Option.some.injEq]
      omega
    |
      right =>
      rw [show encode Nat.Partrec.Code.right = 3 from rfl, stage_base 3 (by decide)]
      simp [baseOutput, nat_pi₂, Nat.Partrec.Code.evaln, bind, Option.bind_eq_some_iff,
        Option.guard_eq_some', Option.some.injEq]
      omega
    | pair f g hf hg =>
      rw [stage_pair]
      simp only [hf, hg]
      simp only [Nat.Partrec.Code.evaln, bind, Option.mem_def, Option.bind_eq_some_iff,
        Option.guard_eq_some', exists_and_left, exists_const, Option.map_eq_some_iff, Seq.seq,
        bind, Functor.map, Option.map_eq_some_iff]
      constructor
      · rintro ⟨a, ha, b, hb, hy⟩
        have hx : x ≤ k := Nat.le_of_lt_succ (Nat.Partrec.Code.evaln_bound ha)
        exact ⟨hx, Nat.pair a, ⟨a, ha, rfl⟩, b, hb, hy.symm⟩
      · rintro ⟨_, _, ⟨a, ha, rfl⟩, b, hb, hy⟩
        exact ⟨a, ha, b, hb, hy.symm⟩
    | comp f g hf hg =>
      rw [stage_comp]
      simp only [hf, hg]
      simp only [Nat.Partrec.Code.evaln, bind, Option.mem_def, Option.bind_eq_some_iff,
        Option.guard_eq_some', exists_and_left, exists_const]
      constructor
      · rintro ⟨a, ha, hy⟩
        exact ⟨Nat.le_of_lt_succ (Nat.Partrec.Code.evaln_bound ha), a, ha, hy⟩
      · rintro ⟨_, a, ha, hy⟩
        exact ⟨a, ha, hy⟩
    | prec f g hf
      hg =>
      obtain ⟨a, b, rfl⟩ : ∃ a b, x = Nat.pair a b :=
        ⟨x.unpair.1, x.unpair.2, (Nat.pair_unpair x).symm⟩
      cases b with
      | zero =>
        rw [stage_prec_zero]
        simp [hf, Nat.Partrec.Code.evaln, Option.bind_eq_some_iff]
      | succ b =>
        rw [stage_prec_succ]
        simp [ih, hg, Nat.Partrec.Code.evaln, Option.bind_eq_some_iff]
    | rfind' f hf =>
      rw [stage_rfind_succ]
      simp only [hf, ih]
      simp only [Nat.Partrec.Code.evaln, bind, Nat.unpaired, Nat.pair_unpair, Option.mem_def,
        Option.bind_eq_some_iff, Option.guard_eq_some', exists_and_left, exists_const]
      apply and_congr_right
      intro _
      apply exists_congr
      intro v
      apply and_congr_right
      intro _
      by_cases hv : v = 0 <;> simp [hv, eq_comm]

/-- Standard-model adequacy of the PA-arithmetized graph for the actual Mathlib
program numbering. Every direction is proved for every program index. -/
theorem eventualGraph_adequate (q x y : ℕ) :
    (eventualGraph q).val.Evalb ![x, y] ↔ y ∈ Kleene.eval q x :=
  by
  rw [eventualGraph_eval]
  simp only [numeral_eq_natCast_app, natCast_nat, Matrix.cons_val_zero, Matrix.cons_val_one]
  change (∃ s : ℕ, stageComputation s q x y) ↔ y ∈ Kleene.eval q x
  have h := exists_congr fun s => stageComputation_iff_evaln s (ofNat Nat.Partrec.Code q) x y
  rw [Denumerable.encode_ofNat] at h
  exact h.trans Nat.Partrec.Code.evaln_complete.symm

/-- The graph arithmetized in PA has precisely the existing Kleene `T₁,U`
normal form over the standard natural numbers. -/
theorem eventualGraph_normal_form (q x y : ℕ) :
    (eventualGraph q).val.Evalb ![x, y] ↔ ∃ w, Kleene.T₁ q x w ∧ Kleene.U w = y :=
  (eventualGraph_adequate q x y).trans (Kleene.normal_form q x y)

end ConcreteEvaluator
end FailureOfComposition

end

end PointwiseComposition
