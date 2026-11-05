/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Compatibility results for Foundation's arithmetic codes

Foundation defines `FFL.FirstOrder.Arithmetic.code`, the arithmetic formula
associated with a partial-recursive code `Nat.ArithPart₁.Code k`, together with
its auxiliary formula `codeAux`.  Foundation's own uniqueness statements for
these formulas are dormant source at the recorded revision, so this module
supplies the corresponding active result.

`eval_unique` states that the evaluation relation of an arithmetic code is
functional in every model of `𝐏𝐀⁻`, under an arbitrary assignment.
-/

@[expose] public section

namespace CategoricalRiceShapiro
namespace ArithmeticCode

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

private theorem evalAux_unique {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ}
    {c : Nat.ArithPart₁.Code k} {v : Fin k → M} {z z' : M}
    (hz : Semiformula.Evalf (M := M) (z :> v) (FFL.FirstOrder.Arithmetic.codeAux c))
    (hz' : Semiformula.Evalf (M := M) (z' :> v) (FFL.FirstOrder.Arithmetic.codeAux c)) :
    z = z' := by
  revert hz hz'
  induction c generalizing z z' <;> simp only [Nat.succ_eq_add_one, codeAux,
    Semiformula.eval_operator, Matrix.comp₂, Nat.reduceAdd, Semiterm.val_fvar,
    Matrix.cons_val_zero, Semiterm.val_operator, Matrix.comp₀,
    Tarski.Structure.numeral_eq_numeral, ORingStructure.zero_eq_zero, Tarski.Structure.eq_iff_eq,
    Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, ORingStructure.one_eq_one,
    Matrix.cons_val_succ, Tarski.Structure.Add.add, Tarski.Structure.Mul.mul,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.neg_eq, LogicalConnective.Prop.or_eq, Tarski.Structure.lt_iff_lt,
    not_lt, Semiformula.eval_exsClosure, Matrix.conj_hom_prop, forall_exists_index, and_imp,
    Matrix.zero_cons_succ_eq_self, Semiformula.eval_ball, Semiterm.val_bvar, Semiformula.eval_ex]
  case zero => rintro rfl rfl; rfl
  case one => rintro rfl rfl; rfl
  case add => rintro rfl rfl; rfl
  case mul => rintro rfl rfl; rfl
  case proj => rintro rfl rfl; rfl
  case equal i j =>
    by_cases hv : v i = v j <;> simp only [hv, true_and, not_true_eq_false, false_and, or_false,
      not_false_eq_true, false_or]
    · rintro rfl rfl; rfl
    · rintro rfl rfl; rfl
  case lt i j =>
    by_cases hv : v i < v j <;> simp only [hv, true_and, ← not_lt, not_true_eq_false, false_and,
      or_false, not_false_eq_true, false_or]
    · rintro rfl rfl; rfl
    · rintro rfl rfl; rfl
  case comp m n c d ihc
    ihd =>
    simp only [Semiformula.eval_rew, Matrix.empty_eq, Function.comp_def, Rew.bind_fvar,
      Matrix.comp_vecCons', Semiterm.val_fvar, Matrix.cons_val_zero, Semiterm.val_bvar,
      Matrix.cons_val_succ]
    intro w₁ hc₁ hd₁ w₂ hc₂ hd₂
    have hw : w₁ = w₂ := funext fun i => ihd i (hd₁ i) (hd₂ i)
    rcases hw with rfl
    exact ihc hc₁ hc₂
  case rfind c
    ih =>
    simp only [Semiformula.eval_rew, Matrix.empty_eq, Function.comp_def, Rew.bind_fvar,
      Matrix.comp_vecCons', Semiterm.val_operator, Tarski.Structure.numeral_eq_numeral,
      ORingStructure.zero_eq_zero, Semiterm.val_fvar, Fin.isValue, Semiterm.val_bvar,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_succ]
    intro h₁ hm₁ h₂ hm₂
    by_contra hzz
    wlog h : z < z' with Hz
    case isFalse =>
      have hlt : z' < z := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hzz)
      exact Hz (k := k) c ih h₂ hm₂ h₁ hm₁ (Ne.symm hzz) hlt
    have hex :
      ∃ x,
        x ≠ 0 ∧
          Semiformula.Evalf (M := M) (x :> z :> fun i => v i)
            (FFL.FirstOrder.Arithmetic.codeAux c) :=
      hm₂ z h
    rcases hex with ⟨x, xz, hx⟩
    exact xz (ih hx h₁)

theorem eval_unique {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ}
    {c : Nat.ArithPart₁.Code k} {v : Fin k → M} {z z' : M}
    (hz : Semiformula.Evalb (M := M) (z :> v) (FFL.FirstOrder.Arithmetic.code c))
    (hz' : Semiformula.Evalb (M := M) (z' :> v) (FFL.FirstOrder.Arithmetic.code c)) : z = z' :=
  by
  simp only [Nat.succ_eq_add_one, code, Matrix.zero_cons_succ_eq_self,
    Semiformula.eval_rew, Matrix.empty_eq, Function.comp_def, Rew.bind_fvar,
    Semiterm.val_bvar] at hz hz'
  exact evalAux_unique hz hz'

end ArithmeticCode
end CategoricalRiceShapiro

end

end PointwiseComposition
