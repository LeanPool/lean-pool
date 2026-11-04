/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.NumeralEvaluation

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Arithmetic terms and atomic formulas compiled to arithmetic programs. Evaluation
is proved in arbitrary arithmetic structures for terms and positive atoms,
and in arbitrary models of PA⁻ for their Boolean complements.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open Nat.ArithPart₁

open CategoricalRiceShapiro.ArithmeticCode

namespace FailureOfComposition
namespace ArithmeticFormulaAtoms

/-- Compilation of arithmetic terms with no free variables. -/
def termCode {n : ℕ} : ArithmeticSemiterm Empty n → Code n
  | .bvar i => .proj i
  | .fvar x => nomatch x
  | .func .zero _ => .zero n
  | .func .one _ => .one n
  | .func .add ts => codeAdd (termCode (ts 0)) (termCode (ts 1))
  | .func .mul ts => codeMul (termCode (ts 0)) (termCode (ts 1))

variable {M : Type*} [ORingStructure M]

/-- The compiled term returns exactly its semantic value. -/
theorem termCode_eval {n : ℕ} (t : ArithmeticSemiterm Empty n) (y : M) (v : Fin n → M) :
    Semiformula.Evalb (y :> v) (code (termCode t)) ↔ y = t.valb v := by
  induction t generalizing y with
  | bvar i => exact eval_proj_iff i y v
  | fvar x => exact x.elim
  | func f ts ih =>
    cases f with
    | zero =>
      change Semiformula.Evalb (y :> v) (code (Code.zero n)) ↔ y = 0
      exact eval_zero_iff y v
    | one =>
      change Semiformula.Evalb (y :> v) (code (Code.one n)) ↔ y = 1
      exact eval_one_iff y v
    |
      add =>
      change
        Semiformula.Evalb (y :> v) (code (codeAdd (termCode (ts 0)) (termCode (ts 1)))) ↔
          y = (ts 0).valb v + (ts 1).valb v
      simp [eval_codeAdd_iff, ih]
    |
      mul =>
      change
        Semiformula.Evalb (y :> v) (code (codeMul (termCode (ts 0)) (termCode (ts 1)))) ↔
          y = (ts 0).valb v * (ts 1).valb v
      simp [eval_codeMul_iff, ih]

/-- Term programs terminate at every internal input tuple. -/
theorem termCode_total {n : ℕ} (t : ArithmeticSemiterm Empty n) (v : Fin n → M) :
    ∃ y : M, Semiformula.Evalb (y :> v) (code (termCode t)) :=
  ⟨t.valb v, (termCode_eval t _ v).mpr rfl⟩

/-- Boolean programs return 1 for truth and 0 for falsehood. -/
def BoolValue (P : Prop) (y : M) : Prop :=
  (P ∧ y = 1) ∨ (¬P ∧ y = 0)

/-- Boolean compilation of an equality or strict-order atom. -/
def atomCode {n k : ℕ} :
    (r : Language.ORing.Rel k) → (Fin k → ArithmeticSemiterm Empty n) → Code n
  | .eq, ts => codeEq (termCode (ts 0)) (termCode (ts 1))
  | .lt, ts => codeLt (termCode (ts 0)) (termCode (ts 1))

/-- Boolean compilation of the negation of an arithmetic atom. -/
def negAtomCode {n k : ℕ} (r : Language.ORing.Rel k) (ts : Fin k → ArithmeticSemiterm Empty n) :
    Code n :=
  codeInv (atomCode r ts)

/-- Positive atomic formulas have total Boolean programs with the exact
internal semantics of the original formula. -/
theorem atomCode_eval {n k : ℕ} (r : Language.ORing.Rel k)
    (ts : Fin k → ArithmeticSemiterm Empty n) (y : M) (v : Fin n → M) :
    Semiformula.Evalb (y :> v) (code (atomCode r ts)) ↔
      BoolValue ((Semiformula.rel r ts).Evalb v) y :=
  by
  cases r with
  |
    eq =>
    change
      Semiformula.Evalb (y :> v) (code (codeEq (termCode (ts 0)) (termCode (ts 1)))) ↔
        BoolValue ((ts 0).valb v = (ts 1).valb v) y
    simp [eval_codeEq_iff, termCode_eval, BoolValue]
  |
    lt =>
    change
      Semiformula.Evalb (y :> v) (code (codeLt (termCode (ts 0)) (termCode (ts 1)))) ↔
        BoolValue ((ts 0).valb v < (ts 1).valb v) y
    simp [eval_codeLt_iff, termCode_eval, BoolValue]

/-- An exact Boolean specification always supplies a value. -/
theorem bool_total {n : ℕ} (c : Code n) (v : Fin n → M) (P : Prop)
    (hc : ∀ y : M, Semiformula.Evalb (y :> v) (code c) ↔ BoolValue P y) :
    ∃ y : M, Semiformula.Evalb (y :> v) (code c) := by
  classical
  by_cases hp : P
  · exact ⟨1, (hc 1).mpr (Or.inl ⟨hp, rfl⟩)⟩
  · exact ⟨0, (hc 0).mpr (Or.inr ⟨hp, rfl⟩)⟩

theorem atomCode_total {n k : ℕ} (r : Language.ORing.Rel k)
    (ts : Fin k → ArithmeticSemiterm Empty n) (v : Fin n → M) :
    ∃ y : M, Semiformula.Evalb (y :> v) (code (atomCode r ts)) :=
  bool_total _ v _ (fun y => atomCode_eval r ts y v)

/-- Arithmetic inversion exchanges the two Boolean values. -/
theorem bool_inverse_eval [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {n : ℕ} (c : Code n) (v : Fin n → M) (P : Prop)
    (hc : ∀ y : M, Semiformula.Evalb (y :> v) (code c) ↔ BoolValue P y) (z : M) :
    Semiformula.Evalb (z :> v) (code (codeInv c)) ↔ BoolValue (¬P) z :=
  by
  rw [eval_codeInv_iff]
  simp only [hc, BoolValue]
  by_cases hp : P <;> simp [hp]

/-- Negated atomic formulas have the exact complementary Boolean graph. -/
theorem negAtomCode_eval [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {n k : ℕ} (r : Language.ORing.Rel k)
    (ts : Fin k → ArithmeticSemiterm Empty n) (y : M) (v : Fin n → M) :
    Semiformula.Evalb (y :> v) (code (negAtomCode r ts)) ↔
      BoolValue ((Semiformula.nrel r ts).Evalb v) y :=
  by
  have h :=
    bool_inverse_eval (atomCode r ts) v ((Semiformula.rel r ts).Evalb v)
      (fun z => atomCode_eval r ts z v) y
  simpa [negAtomCode] using h

theorem negAtomCode_total [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {n k : ℕ} (r : Language.ORing.Rel k)
    (ts : Fin k → ArithmeticSemiterm Empty n) (v : Fin n → M) :
    ∃ y : M, Semiformula.Evalb (y :> v) (code (negAtomCode r ts)) :=
  bool_total _ v _ (fun y => negAtomCode_eval r ts y v)

/-- A Boolean graph returns 1 exactly when its proposition holds. -/
@[simp]
theorem boolValue_one [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] (P : Prop) : BoolValue P (1 : M) ↔ P := by
  simp [BoolValue]

/-- A Boolean graph returns 0 exactly when its proposition fails. -/
@[simp]
theorem boolValue_zero [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] (P : Prop) : BoolValue P (0 : M) ↔ ¬P := by
  simp [BoolValue]

theorem atomCode_one_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {n k : ℕ} (r : Language.ORing.Rel k)
    (ts : Fin k → ArithmeticSemiterm Empty n) (v : Fin n → M) :
    Semiformula.Evalb ((1 : M) :> v) (code (atomCode r ts)) ↔ (Semiformula.rel r ts).Evalb v :=
  by rw [atomCode_eval, boolValue_one]

theorem atomCode_zero_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {n k : ℕ} (r : Language.ORing.Rel k)
    (ts : Fin k → ArithmeticSemiterm Empty n) (v : Fin n → M) :
    Semiformula.Evalb ((0 : M) :> v) (code (atomCode r ts)) ↔ ¬(Semiformula.rel r ts).Evalb v :=
  by rw [atomCode_eval, boolValue_zero]

theorem negAtomCode_one_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {n k : ℕ} (r : Language.ORing.Rel k)
    (ts : Fin k → ArithmeticSemiterm Empty n) (v : Fin n → M) :
    Semiformula.Evalb ((1 : M) :> v) (code (negAtomCode r ts)) ↔
      (Semiformula.nrel r ts).Evalb v :=
  by rw [negAtomCode_eval, boolValue_one]

theorem negAtomCode_zero_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {n k : ℕ} (r : Language.ORing.Rel k)
    (ts : Fin k → ArithmeticSemiterm Empty n) (v : Fin n → M) :
    Semiformula.Evalb ((0 : M) :> v) (code (negAtomCode r ts)) ↔
      ¬(Semiformula.nrel r ts).Evalb v :=
  by rw [negAtomCode_eval, boolValue_zero]

end ArithmeticFormulaAtoms
end FailureOfComposition

end

end PointwiseComposition
