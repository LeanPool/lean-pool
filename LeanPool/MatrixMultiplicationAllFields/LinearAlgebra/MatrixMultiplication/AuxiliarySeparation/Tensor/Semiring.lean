/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Tensor/Semiring.lean`, by
Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K` algebraically
closed; docstrings updated from ℂ to `K`.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.DirectSum
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankExponent
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Finite tensors modulo mutual restriction

Representatives have three natural-number dimensions and coefficients in `K`.
The order is actual linear restriction, and equality in the quotient is mutual
restriction. In particular, changing coordinates does not change the class.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.TensorSemiring

section Restriction

variable {X Y Z U V W P Q R : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]
variable [Fintype P] [Fintype Q] [Fintype R]

/-- `T` is obtained from `S` by three linear maps on its coordinate spaces. -/
def IsRestriction (T : Tensor K X Y Z) (S : Tensor K U V W) : Prop :=
  ∃ (A : X → U → K) (B : Y → V → K) (C : Z → W → K),
    T = Tensor.restrict A B C S

theorem IsRestriction.refl (T : Tensor K X Y Z) : IsRestriction T T := by
  classical
  exact ⟨_, _, _, (Tensor.restrict_identity T).symm⟩

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem IsRestriction.trans {T : Tensor K X Y Z} {S : Tensor K U V W}
    {L : Tensor K P Q R} (hTS : IsRestriction T S) (hSL : IsRestriction S L) :
    IsRestriction T L := by
  rcases hTS with ⟨A, B, C, rfl⟩
  rcases hSL with ⟨D, E, F, rfl⟩
  exact ⟨Tensor.composeRestrictionMatrix A D, Tensor.composeRestrictionMatrix B E,
    Tensor.composeRestrictionMatrix C F, Tensor.restrict_restrict D E F A B C L⟩

omit [Fintype U] [Fintype V] [Fintype W] in
theorem IsRestriction.pullback (T : Tensor K X Y Z)
    (fx : U → X) (fy : V → Y) (fz : W → Z) :
    IsRestriction (Tensor.pullback fx fy fz T) T := by
  classical
  exact ⟨_, _, _, Tensor.pullback_eq_restrict fx fy fz T⟩

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem IsRestriction.of_reindex (T : Tensor K X Y Z)
    (ex : U ≃ X) (ey : V ≃ Y) (ez : W ≃ Z) :
    IsRestriction T (Tensor.pullback ex ey ez T) := by
  have h := IsRestriction.pullback (Tensor.pullback ex ey ez T) ex.symm ey.symm ez.symm
  have heq : Tensor.pullback ex.symm ey.symm ez.symm (Tensor.pullback ex ey ez T) = T := by
    funext x y z
    simp [Tensor.pullback]
  rwa [heq] at h

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem IsRestriction.reindex_iff [Finite X] [Finite Y] [Finite Z]
    (T : Tensor K X Y Z) (S : Tensor K U V W)
    {X' Y' Z' U' V' W' : Type*}
    [Finite X'] [Finite Y'] [Finite Z']
    [Fintype U'] [Fintype V'] [Fintype W']
    (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z)
    (eu : U' ≃ U) (ev : V' ≃ V) (ew : W' ≃ W) :
    IsRestriction (Tensor.pullback ex ey ez T) (Tensor.pullback eu ev ew S) ↔
      IsRestriction T S := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let : Fintype Y := Fintype.ofFinite Y
  let : Fintype Z := Fintype.ofFinite Z
  let : Fintype X' := Fintype.ofFinite X'
  let : Fintype Y' := Fintype.ofFinite Y'
  let : Fintype Z' := Fintype.ofFinite Z'
  constructor
  · intro h
    exact (IsRestriction.of_reindex T ex ey ez).trans
      (h.trans (IsRestriction.pullback S eu ev ew))
  · intro h
    exact (IsRestriction.pullback T ex ey ez).trans
      (h.trans (IsRestriction.of_reindex S eu ev ew))

omit [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W] in
theorem IsRestriction.product {T : Tensor K X Y Z} {S : Tensor K U V W}
    {T' : Tensor K P Q R} {U' V' W' : Type*}
    [Fintype U'] [Fintype V'] [Fintype W'] {S' : Tensor K U' V' W'}
    (hT : IsRestriction T T') (hS : IsRestriction S S') :
    IsRestriction (Tensor.product T S) (Tensor.product T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  exact ⟨_, _, _, (Tensor.restrict_product A B C D E F T' S').symm⟩

omit [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W] in
theorem IsRestriction.sum {T : Tensor K X Y Z} {S : Tensor K U V W}
    {T' : Tensor K P Q R} {U' V' W' : Type*}
    [Fintype U'] [Fintype V'] [Fintype W'] {S' : Tensor K U' V' W'}
    (hT : IsRestriction T T') (hS : IsRestriction S S') :
    IsRestriction (sumTensor T S) (sumTensor T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  exact ⟨_, _, _, (sumTensor_restrict A B C D E F T' S').symm⟩

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem IsRestriction.zero (S : Tensor K U V W) :
    IsRestriction (0 : Tensor K X Y Z) S := by
  refine ⟨0, 0, 0, ?_⟩
  funext x y z
  simp [Tensor.restrict]

theorem IsRestriction.rank_le {T : Tensor K X Y Z} {S : Tensor K U V W}
    (h : IsRestriction T S) : exactRank T ≤ exactRank S := by
  rcases h with ⟨A, B, C, rfl⟩
  exact exactRank_restrict_le S A B C

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem IsRestriction.eq_zero_of_zero {T : Tensor K X Y Z}
    (h : IsRestriction T (0 : Tensor K U V W)) : T = 0 := by
  rcases h with ⟨A, B, C, h⟩
  funext x y z
  rw [h]
  simp [Tensor.restrict]

end Restriction

variable (K) in
/-- A set-sized presentation of any finite coefficient tensor over `K`. -/
structure FiniteTensor where
  /-- Dimension of the tensor's first coordinate space. -/
  nx : ℕ
  /-- Dimension of the tensor's second coordinate space. -/
  ny : ℕ
  /-- Dimension of the tensor's third coordinate space. -/
  nz : ℕ
  /-- Coefficient array in the three standard finite coordinate spaces. -/
  coeff : Tensor K (Fin nx) (Fin ny) (Fin nz)

namespace FiniteTensor

/-- Replace arbitrary finite coordinate sets by standard finite sets. -/
def ofTensor {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : (FiniteTensor K) where
  nx := Fintype.card X
  ny := Fintype.card Y
  nz := Fintype.card Z
  coeff := Tensor.pullback (Fintype.equivFin X).symm
    (Fintype.equivFin Y).symm (Fintype.equivFin Z).symm T

instance : LE (FiniteTensor K) := ⟨fun T S => IsRestriction T.coeff S.coeff⟩

instance : Preorder (FiniteTensor K) where
  le_refl T := IsRestriction.refl T.coeff
  le_trans _ _ _ := IsRestriction.trans

theorem ofTensor_le_iff {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    ofTensor T ≤ ofTensor S ↔ IsRestriction T S :=
  IsRestriction.reindex_iff T S _ _ _ _ _ _

/-- Tensor product represented again on standard finite coordinate sets. -/
def product (T S : (FiniteTensor K)) : (FiniteTensor K) :=
  ofTensor (Tensor.product T.coeff S.coeff)

/-- Direct sum represented again on standard finite coordinate sets. -/
def sum (T S : (FiniteTensor K)) : (FiniteTensor K) :=
  ofTensor (sumTensor T.coeff S.coeff)

theorem product_mono {T T' S S' : (FiniteTensor K)} (hT : T ≤ T') (hS : S ≤ S') :
    product T S ≤ product T' S' :=
  (ofTensor_le_iff _ _).mpr (IsRestriction.product hT hS)

theorem sum_mono {T T' S S' : (FiniteTensor K)} (hT : T ≤ T') (hS : S ≤ S') :
    sum T S ≤ sum T' S' :=
  (ofTensor_le_iff _ _).mpr (IsRestriction.sum hT hS)

end FiniteTensor

variable (K) in
/-- Finite tensors over `K`, with two presentations identified exactly when
each is a linear restriction of the other. -/
abbrev TensorClass := Antisymmetrization (FiniteTensor K) (· ≤ ·)

/-- The class of a finite tensor presentation. -/
def tensorClass (T : (FiniteTensor K)) : (TensorClass K) := toAntisymmetrization (· ≤ ·) T

@[simp] theorem tensorClass_eq_iff (T S : (FiniteTensor K)) :
    tensorClass T = tensorClass S ↔ T ≤ S ∧ S ≤ T :=
  toAntisymmetrization_eq (· ≤ ·) T S

@[simp] theorem tensorClass_le_iff (T S : (FiniteTensor K)) :
    tensorClass T ≤ tensorClass S ↔ T ≤ S := Iff.rfl

/-- The quotient class of a tensor on any three finite coordinate sets. -/
def classOf {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : (TensorClass K) := tensorClass (FiniteTensor.ofTensor T)

theorem classOf_le_iff {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf T ≤ classOf S ↔ IsRestriction T S := FiniteTensor.ofTensor_le_iff T S

theorem classOf_eq_iff {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf T = classOf S ↔ IsRestriction T S ∧ IsRestriction S T := by
  rw [le_antisymm_iff, classOf_le_iff, classOf_le_iff]

theorem classOf_reindex {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (ex : U ≃ X) (ey : V ≃ Y) (ez : W ≃ Z) :
    classOf (Tensor.pullback ex ey ez T) = classOf T :=
  (classOf_eq_iff _ _).mpr ⟨IsRestriction.pullback T ex ey ez,
    IsRestriction.of_reindex T ex ey ez⟩

theorem classOf_eq_of_reindex {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W}
    (ex : X ≃ U) (ey : Y ≃ V) (ez : Z ≃ W)
    (h : Tensor.pullback ex ey ez S = T) : classOf T = classOf S :=
  (congrArg classOf h).symm.trans (classOf_reindex S ex ey ez)

@[simp] theorem classOf_coeff (T : (FiniteTensor K)) : classOf T.coeff = tensorClass T := by
  apply (tensorClass_eq_iff _ _).mpr
  exact ⟨IsRestriction.pullback T.coeff _ _ _, IsRestriction.of_reindex T.coeff _ _ _⟩

instance : Mul (TensorClass K) where
  mul := Quotient.map₂ FiniteTensor.product (by
    intro T T' hT S S' hS
    exact ⟨FiniteTensor.product_mono hT.1 hS.1,
      FiniteTensor.product_mono hT.2 hS.2⟩)

instance : Add (TensorClass K) where
  add := Quotient.map₂ FiniteTensor.sum (by
    intro T T' hT S S' hS
    exact ⟨FiniteTensor.sum_mono hT.1 hS.1, FiniteTensor.sum_mono hT.2 hS.2⟩)

@[simp] theorem tensorClass_product (T S : (FiniteTensor K)) :
    tensorClass T * tensorClass S = tensorClass (FiniteTensor.product T S) := rfl

@[simp] theorem tensorClass_sum (T S : (FiniteTensor K)) :
    tensorClass T + tensorClass S = tensorClass (FiniteTensor.sum T S) := rfl

theorem classOf_product {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf (Tensor.product T S) = classOf T * classOf S := by
  symm
  exact classOf_reindex (Tensor.product T S)
    (Equiv.prodCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
    (Equiv.prodCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
    (Equiv.prodCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)

theorem classOf_sum {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf (sumTensor T S) = classOf T + classOf S := by
  symm
  have h := classOf_reindex (sumTensor T S)
    (Equiv.sumCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
    (Equiv.sumCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
    (Equiv.sumCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)
  change classOf (sumTensor (FiniteTensor.ofTensor T).coeff
    (FiniteTensor.ofTensor S).coeff) = _
  have heq : sumTensor (FiniteTensor.ofTensor T).coeff (FiniteTensor.ofTensor S).coeff =
      Tensor.pullback
        (Equiv.sumCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
        (Equiv.sumCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
        (Equiv.sumCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)
        (sumTensor T S) := by
    funext x y z
    cases x <;> cases y <;> cases z <;> rfl
  rw [heq]
  exact h

instance : Zero (TensorClass K) := ⟨classOf (0 : Tensor K Empty Empty Empty)⟩
instance : One (TensorClass K) := ⟨classOf (fun (_ _ _ : PUnit.{1}) => (1 : K))⟩

theorem classOf_zero {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] :
    classOf (0 : Tensor K X Y Z) = 0 :=
  (classOf_eq_iff _ _).mpr ⟨IsRestriction.zero _, IsRestriction.zero _⟩

theorem class_add_assoc (a b c : (TensorClass K)) : (a + b) + c = a + (b + c) := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  induction c using Quotient.inductionOn with | h c =>
  change (tensorClass a + tensorClass b) + tensorClass c =
    tensorClass a + (tensorClass b + tensorClass c)
  rw [← classOf_coeff a, ← classOf_coeff b, ← classOf_coeff c]
  simp only [← classOf_sum]
  exact classOf_eq_of_reindex _ _ _ (sumTensor_assoc a.coeff b.coeff c.coeff)

theorem class_add_comm (a b : (TensorClass K)) : a + b = b + a := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  change tensorClass a + tensorClass b = tensorClass b + tensorClass a
  rw [← classOf_coeff a, ← classOf_coeff b]
  simp only [← classOf_sum]
  exact classOf_eq_of_reindex _ _ _ (sumTensor_comm a.coeff b.coeff)

theorem class_add_zero (a : (TensorClass K)) : a + 0 = a := by
  induction a using Quotient.inductionOn with | h a =>
  change tensorClass a + 0 = tensorClass a
  rw [← classOf_coeff a]
  change classOf a.coeff + classOf (0 : Tensor K Empty Empty Empty) = classOf a.coeff
  rw [← classOf_sum]
  exact (classOf_eq_of_reindex _ _ _ (sumTensor_empty_right a.coeff
    (0 : Tensor K Empty Empty Empty))).symm

theorem class_zero_add (a : (TensorClass K)) : 0 + a = a :=
  (class_add_comm 0 a).trans (class_add_zero a)

theorem class_mul_assoc (a b c : (TensorClass K)) : (a * b) * c = a * (b * c) := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  induction c using Quotient.inductionOn with | h c =>
  change (tensorClass a * tensorClass b) * tensorClass c =
    tensorClass a * (tensorClass b * tensorClass c)
  rw [← classOf_coeff a, ← classOf_coeff b, ← classOf_coeff c]
  simp only [← classOf_product]
  exact classOf_eq_of_reindex _ _ _ (tensorProduct_assoc a.coeff b.coeff c.coeff)

theorem class_mul_comm (a b : (TensorClass K)) : a * b = b * a := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  change tensorClass a * tensorClass b = tensorClass b * tensorClass a
  rw [← classOf_coeff a, ← classOf_coeff b]
  simp only [← classOf_product]
  exact classOf_eq_of_reindex _ _ _ (tensorProduct_comm a.coeff b.coeff)

theorem class_mul_one (a : (TensorClass K)) : a * 1 = a := by
  induction a using Quotient.inductionOn with | h a =>
  change tensorClass a * 1 = tensorClass a
  rw [← classOf_coeff a]
  change classOf a.coeff * classOf (fun (_ _ _ : PUnit.{1}) => (1 : K)) = classOf a.coeff
  rw [← classOf_product]
  exact (classOf_eq_of_reindex _ _ _ (tensorProduct_one_right a.coeff)).symm

theorem class_one_mul (a : (TensorClass K)) : 1 * a = a :=
  (class_mul_comm 1 a).trans (class_mul_one a)

theorem class_mul_zero (a : (TensorClass K)) : a * 0 = 0 := by
  induction a using Quotient.inductionOn with | h a =>
  change tensorClass a * 0 = 0
  rw [← classOf_coeff a]
  change classOf a.coeff * classOf (0 : Tensor K Empty Empty Empty) = 0
  rw [← classOf_product]
  have heq : Tensor.product a.coeff (0 : Tensor K Empty Empty Empty) = 0 := by
    funext x y z
    simp [Tensor.product]
  rw [heq, classOf_zero]

theorem class_zero_mul (a : (TensorClass K)) : 0 * a = 0 :=
  (class_mul_comm 0 a).trans (class_mul_zero a)

theorem class_left_distrib (a b c : (TensorClass K)) : a * (b + c) = a * b + a * c := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  induction c using Quotient.inductionOn with | h c =>
  change tensorClass a * (tensorClass b + tensorClass c) =
    tensorClass a * tensorClass b + tensorClass a * tensorClass c
  rw [← classOf_coeff a, ← classOf_coeff b, ← classOf_coeff c]
  simp only [← classOf_product, ← classOf_sum]
  exact (classOf_eq_of_reindex _ _ _ (product_sumTensor a.coeff b.coeff c.coeff)).symm

theorem class_right_distrib (a b c : (TensorClass K)) : (a + b) * c = a * c + b * c := by
  rw [class_mul_comm, class_left_distrib, class_mul_comm c a, class_mul_comm c b]

instance : CommSemiring (TensorClass K) where
  add_assoc := class_add_assoc
  add_comm := class_add_comm
  zero_add := class_zero_add
  add_zero := class_add_zero
  nsmul := nsmulRec
  mul_assoc := class_mul_assoc
  mul_comm := class_mul_comm
  one_mul := class_one_mul
  mul_one := class_mul_one
  zero_mul := class_zero_mul
  mul_zero := class_mul_zero
  left_distrib := class_left_distrib
  right_distrib := class_right_distrib

theorem mul_mono {T T' S S' : (TensorClass K)} (hT : T ≤ T') (hS : S ≤ S') :
    T * S ≤ T' * S' := by
  induction T using Quotient.inductionOn with | h T =>
  induction T' using Quotient.inductionOn with | h T' =>
  induction S using Quotient.inductionOn with | h S =>
  induction S' using Quotient.inductionOn with | h S' =>
  exact FiniteTensor.product_mono hT hS

theorem add_mono {T T' S S' : (TensorClass K)} (hT : T ≤ T') (hS : S ≤ S') :
    T + S ≤ T' + S' := by
  induction T using Quotient.inductionOn with | h T =>
  induction T' using Quotient.inductionOn with | h T' =>
  induction S using Quotient.inductionOn with | h S =>
  induction S' using Quotient.inductionOn with | h S' =>
  exact FiniteTensor.sum_mono hT hS

/-- Every tensor class is nonnegative in the restriction order. -/
theorem zero_le (T : (TensorClass K)) : 0 ≤ T := by
  induction T using Quotient.inductionOn with | h T =>
  change (0 : (TensorClass K)) ≤ tensorClass T
  rw [← classOf_coeff T]
  exact (classOf_le_iff _ _).mpr (IsRestriction.zero T.coeff)

instance : OrderBot (TensorClass K) where
  bot := 0
  bot_le := zero_le

instance : IsOrderedAddMonoid (TensorClass K) where
  add_le_add_left _ _ h _c := add_mono h le_rfl

instance : IsOrderedMonoid (TensorClass K) where
  mul_le_mul_left _ _ h _c := mul_mono h le_rfl

instance : IsOrderedRing (TensorClass K) where
  zero_le_one := zero_le 1
  mul_le_mul_of_nonneg_left := by
    intro a ha b c hbc
    exact mul_mono le_rfl hbc
  mul_le_mul_of_nonneg_right := by
    intro a ha b c hbc
    exact mul_mono hbc le_rfl

/-- Exact rank descends to mutual-restriction classes. -/
def rank : (TensorClass K) → ℕ := Quotient.lift (fun T : (FiniteTensor K) => exactRank T.coeff)
  (by
    intro T S h
    exact le_antisymm (IsRestriction.rank_le h.1) (IsRestriction.rank_le h.2))

@[simp] theorem rank_tensorClass (T : (FiniteTensor K)) :
    rank (tensorClass T) = exactRank T.coeff := rfl

@[simp] theorem rank_classOf {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : rank (classOf T) = exactRank T :=
  exactRank_reindex T _ _ _

theorem rank_mono {T S : (TensorClass K)} (h : T ≤ S) : rank T ≤ rank S := by
  induction T using Quotient.inductionOn with | h T =>
  induction S using Quotient.inductionOn with | h S =>
  exact IsRestriction.rank_le h

theorem rank_mul_le (T S : (TensorClass K)) : rank (T * S) ≤ rank T * rank S := by
  induction T using Quotient.inductionOn with | h T =>
  induction S using Quotient.inductionOn with | h S =>
  change rank (tensorClass T * tensorClass S) ≤ rank (tensorClass T) * rank (tensorClass S)
  rw [← classOf_coeff T, ← classOf_coeff S, ← classOf_product]
  simp only [rank_classOf]
  exact exactRank_product_le _ _

variable (K) in
/-- Square matrix multiplication as an element of the tensor semiring. -/
def matrixClass (n : ℕ) : (TensorClass K) := classOf (Tensor.matMul K n n n)

@[simp] theorem rank_matrixClass (n : ℕ) : rank (matrixClass K n) = exactMatrixRank K n :=
  rank_classOf _

private theorem classOf_matrixCoefficients_equiv {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (e : A ≃ B) :
    classOf (Tensor.matrixCoefficients (K := K) A A A) =
      classOf (Tensor.matrixCoefficients (K := K) B B B) := by
  apply classOf_eq_of_reindex (Equiv.prodCongr e e) (Equiv.prodCongr e e)
    (Equiv.prodCongr e e)
  funext x y z
  simp [Tensor.pullback, Tensor.matrixCoefficients, e.injective.eq_iff]

theorem matrixClass_mul (m n : ℕ) : matrixClass K (m * n) = matrixClass K m * matrixClass K n := by
  let e : Fin (m * n) ≃ Fin m × Fin n := Fintype.equivOfCardEq (by simp)
  have h := classOf_matrixCoefficients_equiv (K := K) e
  change matrixClass K (m * n) = classOf (Tensor.matrixCoefficients (K := K)
    (Fin m × Fin n) (Fin m × Fin n) (Fin m × Fin n)) at h
  rw [h]
  change _ = classOf (Tensor.matrixCoefficients (K := K) (Fin m) (Fin m) (Fin m)) *
    classOf (Tensor.matrixCoefficients (K := K) (Fin n) (Fin n) (Fin n))
  rw [← classOf_product]
  apply classOf_eq_of_reindex (Equiv.prodProdProdComm _ _ _ _)
    (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)
  funext x y z
  exact Tensor.matrixCoefficients_product x y z

@[simp] theorem matrixClass_one : matrixClass K 1 = 1 := by
  let e : Fin 1 × Fin 1 ≃ PUnit.{1} := Fintype.equivOfCardEq (by simp)
  apply classOf_eq_of_reindex e e e
  funext x y z
  have hxy : x.2 = y.1 := Subsingleton.elim _ _
  have hyz : y.2 = z.1 := Subsingleton.elim _ _
  have hzx : z.2 = x.1 := Subsingleton.elim _ _
  simp [Tensor.pullback, Tensor.matMul, hxy, hyz, hzx]

theorem matrixClass_pow (m j : ℕ) : matrixClass K (m ^ j) = matrixClass K m ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, matrixClass_mul, ih, pow_succ]

theorem classOf_eq_zero_iff {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : classOf T = 0 ↔ T = 0 := by
  constructor
  · intro h
    have hr : IsRestriction T (0 : Tensor K Empty Empty Empty) :=
      ((classOf_eq_iff _ _).mp h).1
    exact hr.eq_zero_of_zero
  · rintro rfl
    exact classOf_zero

instance : Nontrivial (TensorClass K) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  have heq : (fun (_ _ _ : PUnit.{1}) => (1 : K)) = 0 :=
    (classOf_eq_zero_iff _).mp h
  have := congrFun (congrFun (congrFun heq PUnit.unit) PUnit.unit) PUnit.unit
  exact one_ne_zero this

/-- A nonzero tensor has a nonzero coefficient, which restricts to scalar multiplication. -/
theorem one_le_classOf_of_ne_zero {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] {T : Tensor K X Y Z} (hT : T ≠ 0) :
    1 ≤ classOf T := by
  classical
  have hex : ∃ x y z, T x y z ≠ 0 := by
    by_contra! h
    apply hT
    funext x y z
    exact h x y z
  obtain ⟨x, y, z, hxyz⟩ := hex
  apply (classOf_le_iff _ _).mpr
  refine ⟨(fun _ u => if u = x then (T x y z)⁻¹ else 0),
    (fun _ v => if v = y then 1 else 0),
    (fun _ w => if w = z then 1 else 0), ?_⟩
  funext a b c
  simp [Tensor.restrict, ite_mul, mul_ite, hxyz]

/-- Every nonzero class dominates the multiplicative unit. -/
theorem one_le_of_ne_zero {T : (TensorClass K)} (hT : T ≠ 0) : 1 ≤ T := by
  induction T using Quotient.inductionOn with | h T =>
  change tensorClass T ≠ 0 at hT
  change 1 ≤ tensorClass T
  rw [← classOf_coeff T] at hT ⊢
  exact one_le_classOf_of_ne_zero (fun h => hT ((classOf_eq_zero_iff _).mpr h))

end MatrixMultiplication.AuxiliarySeparation.TensorSemiring

end

end MatrixMultiplicationAllFields
