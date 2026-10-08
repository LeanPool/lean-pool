/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Host.Compression
public import LeanPool.SmallUndecidableGroups.GroupTheory.HNNLemmas
public import LeanPool.SmallUndecidableGroups.Borisov.Criterion
public import LeanPool.SmallUndecidableGroups.Host.CompressionInjective

/-!
# Tower

Part of the dependency closure of the small undecidable group constructions.
-/

@[expose] public section

namespace Undecidability
namespace Host

/--
The two proper HNN embeddings and the six Tietze eliminations preserve the
truth of Borisov's test word.
-/
theorem borisov_testWord_iff_compressed
    (datum : Thue.StandingDatum) (Q : List (Fin 2)) :
    (Borisov.presentation datum).wordProblem (Borisov.testWord Q) ↔
      (presentationOf datum).wordProblem (testWord Q) :=
  Compression.testWord_iff datum (compression_injective datum) Q

/-- The Thue predicate is represented by the compressed host test word. -/
theorem thueEq_iff_testWord
    (datum : Thue.StandingDatum) (Q : List (Fin 2)) :
    ThueEq (Thue.systemOf datum.F datum.E) Q datum.P ↔
      (presentationOf datum).wordProblem (testWord Q) :=
  (Borisov.criterion datum Q).trans
    (borisov_testWord_iff_compressed datum Q)

/-- Normal generation from Proposition 2.4 of the paper, proved in the
compressed presentation. -/
theorem z_normallyGenerates (datum : Thue.StandingDatum) :
    (presentationOf datum).NormallyGenerates zWord := by
  let P := presentationOf datum
  let N : Subgroup P.Group :=
    Subgroup.normalClosure ({P.evalWord zWord} : Set P.Group)
  let q : P.Group →* P.Group ⧸ N := QuotientGroup.mk' N
  let x : Fin 3 → P.Group ⧸ N := fun i => q (PresentedGroup.of i)
  have hz : x 2 = 1 := by
    apply (QuotientGroup.eq_one_iff _).2
    apply Subgroup.subset_normalClosure
    change PresentedGroup.of (2 : Fin 3) ∈ ({P.evalWord zWord} : Set P.Group)
    simp [FP.evalWord, zWord]
  have hrel (i : Fin 9) : Word.eval x (P.relator i) = 1 := by
    have h := congrArg q (P.relator_eq_one i)
    change q (Word.eval (fun j => PresentedGroup.of j) (P.relator i)) = q 1 at h
    rw [Word.map_eval] at h
    change Word.eval (q ∘ fun j => PresentedGroup.of j) (P.relator i) = 1
    simpa only [map_one] using h
  have h8 := hrel 8
  simp only [presentationOf, presentation, Fin.isValue, rho, oldSurvivingRelator, Matrix.cons_val,
    OldWord.evaluate_relation, OldWord.evaluate_product, Word.product, List.map_cons,
    OldWord.evaluate_inverse, OldWord.evaluate_generator, tau, yWord, zWord, cWord, tWord, dWord,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc, eWord, List.map_nil,
    Word.eval_relation, Word.eval_append, Word.eval_inverse, Word.eval_generator, hz, inv_one,
    mul_one, one_mul, inv_mul_cancel_left, inv_mul_cancel, P] at h8
  have hd2 : x 0 * x 0 = 1 := by
    calc
      x 0 * x 0 = (x 0)⁻¹⁻¹ * (x 0)⁻¹⁻¹ :=
        congrArg₂ (fun a b => a * b) (inv_inv _).symm (inv_inv _).symm
      _ = ((x 0)⁻¹ * (x 0)⁻¹)⁻¹ :=
        (mul_inv_rev (x 0)⁻¹ (x 0)⁻¹).symm
      _ = 1 := by rw [h8]; simp
  have hd4 : x 0 ^ 4 = 1 := by
    calc
      x 0 ^ 4 = (x 0 * x 0) * (x 0 * x 0) := by
        simp [pow_succ, mul_assoc]
      _ = 1 := by rw [hd2]; simp
  have hd := hrel 0
  simp only [presentationOf, presentation, Fin.isValue, rho, oldSurvivingRelator,
    Matrix.cons_val_zero, OldWord.evaluate_relation, OldWord.evaluate_product, Word.product,
    List.map_cons, OldWord.evaluate_inverse, OldWord.evaluate_generator, tau, sWord,
    OldWord.evaluate_pow, dWord, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, Word.eval_relation, Word.eval_append, Word.eval_inverse, Word.eval_generator,
    Word.eval_pow, hd4, one_mul, inv_mul_cancel, inv_eq_one, P] at hd
  have hsimulation := hrel 4
  simp only [presentationOf, presentation, Fin.isValue, rho, oldSurvivingRelator,
    oldSimulationRelator, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Nat.one_mod,
    Nat.reduceAdd, Nat.mod_succ, Matrix.cons_val, OldWord.evaluate_relation,
    OldWord.evaluate_product, Word.product, List.map_cons, OldWord.evaluate_inverse,
    OldWord.evaluate_generator, tau, cWord, zWord, tWord, dWord, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.append_assoc, OldWord.evaluate_pow,
    OldWord.evaluate_positive, sWord, s2Word, yWord, eWord, List.map_nil, Word.eval_relation,
    Word.eval_append, Word.eval_inverse, Word.eval_generator, hz, inv_one, hd, mul_one,
    Word.eval_pow, one_pow, Word.eval_substitutePositive, one_mul, P] at hsimulation
  have hFE :
      Thue.evalPositive (x 1) (x 1)⁻¹ (datum.F 1) =
        Thue.evalPositive (x 1) (x 1)⁻¹ (datum.E 1) :=
    eq_of_mul_inv_eq_one hsimulation
  have hs : x 1 = 1 :=
    (datum.kill (x 1) (x 1)⁻¹ rfl hFE).1
  have hx (i : Fin 3) : x i = 1 := by
    fin_cases i
    · exact hd
    · exact hs
    · exact hz
  have hq : q = 1 := by
    apply PresentedGroup.ext
    intro i
    change q (PresentedGroup.of i) = 1
    exact hx i
  have hsub : Subsingleton (P.Group ⧸ N) := by
    constructor
    intro a b
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N b
    change q a = q b
    rw [hq]
    rfl
  have hN : N = ⊤ := QuotientGroup.subsingleton_iff.mp hsub
  unfold FP.NormallyGenerates
  simpa only [P, N, FP.evalWord_eq_mk] using hN

/-- The explicit compressed host has unsolvable word problem. -/
theorem wordProblem_unsolvable (datum : Thue.StandingDatum) :
    ¬ ComputablePred (presentationOf datum).wordProblem := by
  apply not_computablePred_of_manyOneReducible datum.undecidable
  exact ⟨testWord, testWord_computable, thueEq_iff_testWord datum⟩

end Host
end Undecidability
