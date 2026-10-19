/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.HFS

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

/-!
# Internalized languages of first-order logic -/

namespace FFL
namespace FirstOrder
namespace Arithmetic
namespace Bootstrapping

variable {L : Language} [L.Encodable]

instance (k) : Semiterm.Operator.GödelNumber ℒₒᵣ (L.Func k) :=
  ⟨fun f ↦ Semiterm.Operator.numeral ℒₒᵣ (Encodable.encode f)⟩

instance (k) : Semiterm.Operator.GödelNumber ℒₒᵣ (L.Rel k) :=
  ⟨fun r ↦ Semiterm.Operator.numeral ℒₒᵣ (Encodable.encode r)⟩

variable (L)

/-- Data and laws for LORDefinable in `FFL.FirstOrder.Language`. -/
protected class _root_.PointwiseComposition.FFL.FirstOrder.Language.LORDefinable where
  /-- The func construction in `FFL.FirstOrder.Language.LORDefinable`. -/
  func : Σ₀.Semisentence 2
  /-- The rel construction in `FFL.FirstOrder.Language.LORDefinable`. -/
  rel : Σ₀.Semisentence 2
  func_iff {k c : ℕ} : c ∈ Set.range (Encodable.encode : L.Func k → ℕ) ↔ ℕ ⊧/![k, c] func.val
  rel_iff {k c : ℕ} : c ∈ Set.range (Encodable.encode : L.Rel k → ℕ) ↔ ℕ ⊧/![k, c] rel.val

alias _root_.PointwiseComposition.FFL.FirstOrder.Language.isFunc := Language.LORDefinable.func

alias _root_.PointwiseComposition.FFL.FirstOrder.Language.isRel := Language.LORDefinable.rel

alias _root_.PointwiseComposition.FFL.FirstOrder.Language.iff_isFunc :=
  Language.LORDefinable.func_iff

alias _root_.PointwiseComposition.FFL.FirstOrder.Language.iff_isRel :=
  Language.LORDefinable.rel_iff

variable {V : Type*} [ORingStructure V] [L.LORDefinable]

/-- The Is Func construction in `FFL.FirstOrder.Language`. -/
def _root_.PointwiseComposition.FFL.FirstOrder.Language.IsFunc (arity f : V) : Prop :=
  V ⊧/![arity, f] L.isFunc.val

/-- The Is Rel construction in `FFL.FirstOrder.Language`. -/
def _root_.PointwiseComposition.FFL.FirstOrder.Language.IsRel (arity f : V) : Prop :=
  V ⊧/![arity, f] L.isRel.val

variable {L}

lemma isFunc_def (k f : V) : L.IsFunc k f ↔ V ⊧/![k, f] L.isFunc.val := by rfl

lemma isRel_def (k R : V) : L.IsRel k R ↔ V ⊧/![k, R] L.isRel.val := by rfl

lemma eval_func (v : Fin 2 → V) : L.isFunc.val.Evalb v ↔ L.IsFunc (v 0) (v 1) := by
  simp [Language.IsFunc, ← Matrix.fun_eq_vec_two]

lemma eval_rel_iff (v : Fin 2 → V) : L.isRel.val.Evalb v ↔ L.IsRel (v 0) (v 1) := by
  simp [Language.IsRel, ← Matrix.fun_eq_vec_two]

instance _root_.PointwiseComposition.FFL.FirstOrder.Language.IsFunc.defined :
    Σ₀-Relation (L.IsFunc (V := V)) via L.isFunc :=
  .mk fun v ↦ eval_func (L := L) v

instance _root_.PointwiseComposition.FFL.FirstOrder.Language.IsRel.defined :
    Σ₀-Relation (L.IsRel (V := V)) via L.isRel :=
  .mk fun v ↦ eval_rel_iff (L := L) v

instance _root_.PointwiseComposition.FFL.FirstOrder.Language.IsFunc.definable :
    Σ₀-Relation (L.IsFunc (V := V)) :=
  Language.IsFunc.defined.to_definable

instance _root_.PointwiseComposition.FFL.FirstOrder.Language.IsRel.definable :
    Σ₀-Relation (L.IsRel (V := V)) :=
  Language.IsRel.defined.to_definable

@[simp, definability]
instance _root_.PointwiseComposition.FFL.FirstOrder.Language.IsFunc.definable' (ℌ) :
    ℌ-Relation (L.IsFunc (V := V)) :=
  HierarchySymbol.Definable.of_zero Language.IsFunc.definable

@[simp, definability]
instance _root_.PointwiseComposition.FFL.FirstOrder.Language.IsRel.definable' (ℌ) :
    ℌ-Relation (L.IsRel (V := V)) :=
  HierarchySymbol.Definable.of_zero Language.IsRel.definable

section

variable [V↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻]

instance gödelQuoteFunc (k) : GödelQuote (L.Func k) V :=
  ⟨fun f ↦ ↑(Encodable.encode f)⟩

instance gödelQuoteRel (k) : GödelQuote (L.Rel k) V :=
  ⟨fun R ↦ ↑(Encodable.encode R)⟩

omit [L.LORDefinable] in
lemma quote_func_def (f : L.Func k) : (⌜f⌝ : V) = ↑(Encodable.encode f) :=
  rfl

omit [L.LORDefinable] in
lemma quote_rel_def (R : L.Rel k) : (⌜R⌝ : V) = ↑(Encodable.encode R) :=
  rfl

lemma isFunc_quote_quote {k x : ℕ} :
    L.IsFunc (V := V) k x ↔ ∃ f : L.Func k, Encodable.encode f = x :=
  have : V ⊧/![k, x] L.isFunc.val ↔ ℕ ⊧/![k, x] L.isFunc.val := by
    simpa [Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
      models_iff_of_Sigma0 (V := V) (σ := L.isFunc.val) (by simp) (e := ![k, x])
  Iff.trans this <| Iff.trans L.iff_isFunc.symm <| by simp

lemma isRel_quote_quote {k x : ℕ} :
    L.IsRel (V := V) k x ↔ ∃ R : L.Rel k, Encodable.encode R = x :=
  have : V ⊧/![k, x] L.isRel.val ↔ ℕ ⊧/![k, x] L.isRel.val := by
    simpa [Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
      models_iff_of_Sigma0 (V := V) (σ := L.isRel.val) (by simp) (e := ![k, x])
  Iff.trans this <| Iff.trans L.iff_isRel.symm <| by simp

@[simp]
lemma codeIn_func_quote {k : ℕ} (f : L.Func k) : L.IsFunc (V := V) k ⌜f⌝ :=
  (isFunc_quote_quote (V := V)).mpr ⟨f, rfl⟩

@[simp]
lemma codeIn_rel_quote {k : ℕ} (r : L.Rel k) : L.IsRel (V := V) k ⌜r⌝ :=
  (isRel_quote_quote (V := V)).mpr ⟨r, rfl⟩

omit [L.LORDefinable]

@[simp]
lemma quote_func_inj (f₁ f₂ : L.Func k) : (⌜f₁⌝ : V) = (⌜f₂⌝ : V) ↔ f₁ = f₂ := by
  simp [quote_func_def]

@[simp]
lemma quote_rel_inj (R₁ R₂ : L.Rel k) : (⌜R₁⌝ : V) = (⌜R₂⌝ : V) ↔ R₁ = R₂ := by
  simp [quote_rel_def]

@[simp]
lemma coe_quote_func_nat (f : L.Func k) : ((⌜f⌝ : ℕ) : V) = (⌜f⌝ : V) := by
  simp [quote_func_def]

@[simp]
lemma coe_quote_rel_nat (R : L.Rel k) : ((⌜R⌝ : ℕ) : V) = (⌜R⌝ : V) := by simp [quote_rel_def]

end

lemma _root_.PointwiseComposition.FFL.FirstOrder.Language.ORing.of_mem_range_encode_func
    {k f : ℕ} :
    f ∈ Set.range (Encodable.encode : FirstOrder.Language.Func ℒₒᵣ k → ℕ) ↔
      (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1) :=
  by
  constructor
  · rintro ⟨f, rfl⟩
    match k, f with
    | 0, Language.ORing.Func.zero => simp; rfl
    | 0, Language.ORing.Func.one => simp; rfl
    | 2, Language.ORing.Func.add => simp; rfl
    | 2, Language.ORing.Func.mul => simp; rfl
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Language.ORing.Func.zero, rfl⟩
    · exact ⟨Language.ORing.Func.one, rfl⟩
    · exact ⟨Language.ORing.Func.add, rfl⟩
    · exact ⟨Language.ORing.Func.mul, rfl⟩

/-- TODO: move to Basic/Syntax/Bootstrapping.Language.lean -/
lemma _root_.PointwiseComposition.FFL.FirstOrder.Language.ORing.of_mem_range_encode_rel
    {k r : ℕ} :
    r ∈ Set.range (Encodable.encode : FirstOrder.Language.Rel ℒₒᵣ k → ℕ) ↔
      (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1) :=
  by
  constructor
  · rintro ⟨r, rfl⟩
    match k, r with
    | 2, Language.ORing.Rel.eq => simp; rfl
    | 2, Language.ORing.Rel.lt => simp; rfl
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Language.ORing.Rel.eq, rfl⟩
    · exact ⟨Language.ORing.Rel.lt, rfl⟩

instance : (ℒₒᵣ).LORDefinable
    where
  func :=
    .mkSigma (“k f. (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1)”)
  rel := .mkSigma (“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)”)
  func_iff {k c} := by simpa [models_iff] using! Language.ORing.of_mem_range_encode_func
  rel_iff {k c} := by simpa [models_iff] using! Language.ORing.of_mem_range_encode_rel

namespace ObjectArithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁]

/--
The zero Index construction in `FFL.FirstOrder.Arithmetic.Bootstrapping.ObjectArithmetic`. -/
def zeroIndex : ℕ :=
  Encodable.encode (Language.Zero.zero : (ℒₒᵣ : FirstOrder.Language).Func 0)

/-- The one Index construction in `FFL.FirstOrder.Arithmetic.Bootstrapping.ObjectArithmetic`. -/
def oneIndex : ℕ :=
  Encodable.encode (Language.One.one : (ℒₒᵣ : FirstOrder.Language).Func 0)

/-- The add Index construction in `FFL.FirstOrder.Arithmetic.Bootstrapping.ObjectArithmetic`. -/
def addIndex : ℕ :=
  Encodable.encode (Language.Add.add : (ℒₒᵣ : FirstOrder.Language).Func 2)

/-- The mul Index construction in `FFL.FirstOrder.Arithmetic.Bootstrapping.ObjectArithmetic`. -/
def mulIndex : ℕ :=
  Encodable.encode (Language.Mul.mul : (ℒₒᵣ : FirstOrder.Language).Func 2)

/-- The eq Index construction in `FFL.FirstOrder.Arithmetic.Bootstrapping.ObjectArithmetic`. -/
def eqIndex : ℕ :=
  Encodable.encode (Language.Eq.eq : (ℒₒᵣ : FirstOrder.Language).Rel 2)

/-- The lt Index construction in `FFL.FirstOrder.Arithmetic.Bootstrapping.ObjectArithmetic`. -/
def ltIndex : ℕ :=
  Encodable.encode (Language.LT.lt : (ℒₒᵣ : FirstOrder.Language).Rel 2)

@[simp]
lemma LOR_func_zeroIndex : (ℒₒᵣ).IsFunc 0 (zeroIndex : V) := by
  simpa using! codeIn_func_quote (V := V) (L := ℒₒᵣ) Language.Zero.zero

@[simp]
lemma LOR_func_oneIndex : (ℒₒᵣ).IsFunc 0 (oneIndex : V) := by
  simpa using! codeIn_func_quote (V := V) (L := ℒₒᵣ) Language.One.one

@[simp]
lemma LOR_func_addIndex : (ℒₒᵣ).IsFunc 2 (addIndex : V) := by
  simpa using! codeIn_func_quote (V := V) (L := ℒₒᵣ) Language.Add.add

@[simp]
lemma LOR_func_mulIndex : (ℒₒᵣ).IsFunc 2 (mulIndex : V) := by
  simpa using! codeIn_func_quote (V := V) (L := ℒₒᵣ) Language.Mul.mul

@[simp]
lemma LOR_rel_eqIndex : (ℒₒᵣ).IsRel 2 (eqIndex : V) := by
  simpa using! codeIn_rel_quote (V := V) (L := ℒₒᵣ) Language.Eq.eq

@[simp]
lemma LOR_rel_ltIndex : (ℒₒᵣ).IsRel 2 (ltIndex : V) := by
  simpa using! codeIn_rel_quote (V := V) (L := ℒₒᵣ) Language.LT.lt

lemma func_def_LOR :
    (ℒₒᵣ).isFunc =
      .mkSigma (“k f. (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1)”) :=
  rfl

lemma rel_def_LOR : (ℒₒᵣ).isRel = .mkSigma (“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)”) :=
  rfl

lemma coe_zeroIndex_eq : (zeroIndex : V) = 0 :=
  rfl

lemma coe_oneIndex_eq : (oneIndex : V) = 1 := by simp [oneIndex]; rfl

lemma coe_addIndex_eq : (addIndex : V) = 0 :=
  rfl

lemma coe_mulIndex_eq : (mulIndex : V) = 1 := by simp [mulIndex]; rfl

@[reducible]
instance gödelQuoteFuncLOR (k) : GödelQuote ((ℒₒᵣ).Func k) V :=
  gödelQuoteFunc k

@[reducible]
instance gödelQuoteRelLOR (k) : GödelQuote ((ℒₒᵣ).Rel k) V :=
  gödelQuoteRel k

lemma isFunc_iff_LOR {k f : V} :
    (ℒₒᵣ).IsFunc k f ↔
      (k = 0 ∧ f = ⌜(Language.Zero.zero : (ℒₒᵣ).Func 0)⌝) ∨
        (k = 0 ∧ f = ⌜(Language.One.one : (ℒₒᵣ).Func 0)⌝) ∨
          (k = 2 ∧ f = ⌜(Language.Add.add : (ℒₒᵣ).Func 2)⌝) ∨
            (k = 2 ∧ f = ⌜(Language.Mul.mul : (ℒₒᵣ).Func 2)⌝) :=
  by
  rw [isFunc_def (L := ℒₒᵣ), func_def_LOR]
  suffices k = 0 ∧ f = 0 ∨ k = 0 ∧ f = 1 ∨ k = 2 ∧ f = 0 ∨ k = 2 ∧ f = 1 ↔ _ by simpa
  apply iff_of_eq
  congr
  · calc
      (1 : V) = (1 : ℕ) := by simp
      _ = ⌜(Language.One.one : (ℒₒᵣ).Func 0)⌝ := by rfl
  · calc
      (1 : V) = (1 : ℕ) := by simp
      _ = ⌜(Language.Mul.mul : (ℒₒᵣ).Func 2)⌝ := by rfl

lemma isRel_iff_LOR {k R : V} :
    (ℒₒᵣ).IsRel k R ↔
      (k = 2 ∧ R = ⌜(Language.Eq.eq : (ℒₒᵣ).Rel 2)⌝) ∨
        (k = 2 ∧ R = ⌜(Language.LT.lt : (ℒₒᵣ).Rel 2)⌝) :=
  by
  rw [isRel_def (L := ℒₒᵣ), rel_def_LOR]
  suffices k = 2 ∧ R = 0 ∨ k = 2 ∧ R = 1 ↔ _ by simpa
  apply iff_of_eq
  congr
  · calc
      (1 : V) = (1 : ℕ) := by simp

end ObjectArithmetic

end Bootstrapping
end Arithmetic
end FirstOrder
end FFL

end

end PointwiseComposition
