/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Host.Presentation
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Abelianization

Part of the dependency closure of the small undecidable group constructions.
-/

@[expose] public section

namespace Undecidability
namespace Host

/-- Every homomorphism from the host group to a commutative group kills `D`. -/
theorem map_d_eq_one_of_commGroup
    (datum : Thue.StandingDatum) {A : Type*} [CommGroup A]
    (f : (presentationOf datum).Group →* A) :
    f (PresentedGroup.of (0 : Fin 3)) = 1 := by
  let P := presentationOf datum
  let x : Fin 3 → A := fun i ↦ f (PresentedGroup.of i)
  have hrel (i : Fin 9) : Word.eval x (P.relator i) = 1 := by
    calc
      Word.eval x (P.relator i) = f (P.evalWord (P.relator i)) :=
        (Word.map_eval f
          (fun j ↦ (PresentedGroup.of j : P.Group)) (P.relator i)).symm
      _ = f 1 := congrArg f (P.relator_eq_one i)
      _ = 1 := map_one f
  have h₀ := hrel 0
  have h₈ := hrel 8
  simp only [presentationOf, presentation, Fin.isValue, rho, oldSurvivingRelator,
    Matrix.cons_val_zero, OldWord.evaluate_relation, OldWord.evaluate_product, List.map_cons,
    OldWord.evaluate_inverse, OldWord.evaluate_generator, tau, sWord, OldWord.evaluate_pow, dWord,
    List.map_nil, Word.eval_relation, Word.eval_product, Word.eval_inverse, Word.eval_generator,
    Word.eval_pow, List.prod_cons, List.prod_nil, mul_comm, one_mul, mul_inv_cancel_comm,
    Matrix.cons_val, yWord, zWord, cWord, tWord, eWord, mul_inv_cancel_right, mul_inv_cancel, P]
    at h₀ h₈
  change x 0 = 1
  have hd₄ : x 0 ^ 4 = x 0 := mul_inv_eq_one.mp h₀
  have hdinv : (x 0)⁻¹ = x 0 := mul_inv_eq_one.mp h₈
  have hd₂ : x 0 ^ 2 = 1 := by
    calc
      x 0 ^ 2 = (x 0)⁻¹ * x 0 := by rw [pow_two, hdinv]
      _ = 1 := by simp
  calc
    x 0 = x 0 ^ 4 := hd₄.symm
    _ = (x 0 ^ 2) ^ 2 := pow_mul (x 0) 2 2
    _ = 1 := by simp [hd₂]

/-- The image of `D` is trivial in the abelianization of the host group. -/
theorem d_eq_one_in_abelianization (datum : Thue.StandingDatum) :
    Abelianization.of
      (PresentedGroup.of (0 : Fin 3) : (presentationOf datum).Group) = 1 :=
  map_d_eq_one_of_commGroup datum Abelianization.of

end Host
end Undecidability
