/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.LocalTensor
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.Blocks
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor

/-! # Finite coefficient tensors and the mutual restriction quotient -/

@[expose] public section

noncomputable section

open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.TensorSpectrum

variable {K : Type*} [CommSemiring K]

namespace CoefficientTensor

open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation.Tensor

variable {X Y Z U V W X' Y' Z' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- `Restricts A B` means that the source `A` restricts to the target `B`. -/
def Restricts (A : Tensor K X Y Z) (B : Tensor K U V W) : Prop :=
  B ∈ MatrixExponent.LocalTensor.orbit A

theorem Restricts.refl (A : Tensor K X Y Z) : Restricts A A := by
  classical
  exact ⟨_, _, _, (Tensor.restrict_identity A).symm⟩

theorem Restricts.trans [Fintype U] [Fintype V] [Fintype W]
    {A : Tensor K X Y Z} {B : Tensor K U V W} {C : Tensor K X' Y' Z'}
    (hAB : Restricts A B) (hBC : Restricts B C) : Restricts A C := by
  rcases hAB with ⟨a, b, c, rfl⟩
  rcases hBC with ⟨d, e, f, rfl⟩
  exact ⟨Tensor.composeRestrictionMatrix d a, Tensor.composeRestrictionMatrix e b,
    Tensor.composeRestrictionMatrix f c, Tensor.restrict_restrict a b c d e f A⟩

theorem Restricts.pullback (A : Tensor K X Y Z)
    (f : U → X) (g : V → Y) (h : W → Z) :
    Restricts A (Tensor.pullback f g h A) := by
  classical
  exact ⟨_, _, _, Tensor.pullback_eq_restrict f g h A⟩

theorem Restricts.rankAtMost {A : Tensor K X Y Z} {B : Tensor K U V W}
    {r : ℕ} (hAB : Restricts A B) (hA : Tensor.RankAtMost A r) :
    Tensor.RankAtMost B r := by
  rcases hAB with ⟨a, b, c, rfl⟩
  exact hA.restrict a b c

variable {X Y Z U V W X' Y' Z' U' V' W' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]

/-- Restriction is compatible with heterogeneous tensor direct sums. -/
theorem Restricts.blockSum
    {T : Tensor K X Y Z} {T' : Tensor K X' Y' Z'}
    {S : Tensor K U V W} {S' : Tensor K U' V' W'}
    (hT : Restricts T T') (hS : Restricts S S') :
    Restricts (blockSum T S) (blockSum T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  exact ⟨blockMatrix A D, blockMatrix B E, blockMatrix C F,
    (restrict_blockSum A B C D E F T S).symm⟩

/-- Restriction is compatible with tensor products through the actual products
of the three local coefficient matrices. -/
theorem Restricts.product
    {T : Tensor K X Y Z} {T' : Tensor K X' Y' Z'}
    {S : Tensor K U V W} {S' : Tensor K U' V' W'}
    (hT : Restricts T T') (hS : Restricts S S') :
    Restricts (Tensor.product T S) (Tensor.product T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  exact ⟨fun x u => A x.1 u.1 * D x.2 u.2,
    fun y v => B y.1 v.1 * E y.2 v.2,
    fun z w => C z.1 w.1 * F z.2 w.2,
    (Tensor.restrict_product A B C D E F T S).symm⟩


/-- Injective index maps preserve all three shared-index equalities of a matrix
tensor, including its zero coefficients. -/
theorem matrixCoefficients_pullback_injective
    {K A B C X Y Z : Type*} [CommSemiring K]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (a : X → A) (b : Y → B) (c : Z → C)
    (ha : Function.Injective a) (hb : Function.Injective b) (hc : Function.Injective c) :
    Tensor.pullback (Prod.map a b) (Prod.map b c) (Prod.map c a)
      (Tensor.matrixCoefficients (K := K) A B C) =
      Tensor.matrixCoefficients (K := K) X Y Z := by
  funext x y z
  change (if b x.2 = b y.1 ∧ c y.2 = c z.1 ∧ a z.2 = a x.1 then (1 : K) else 0) =
    if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  simp only [ha.eq_iff, hb.eq_iff, hc.eq_iff]

/-- The matrix multiplication tensor with the same dimension on all three wires. -/
abbrev squareMatrixTensor (n : ℕ) := Tensor.matrixCoefficients (K := K) (Fin n) (Fin n) (Fin n)

/-- Pair the row indices and column indices separately, then enumerate each
pair by the standard equivalence with `Fin (n * m)`. -/
def squareProductCoordinates (n m : ℕ) :
    ((Fin n × Fin n) × (Fin m × Fin m)) ≃ (Fin (n * m) × Fin (n * m)) where
  toFun p := (finProdFinEquiv (p.1.1, p.2.1), finProdFinEquiv (p.1.2, p.2.2))
  invFun p :=
    ((((finProdFinEquiv : Fin n × Fin m ≃ Fin (n * m)).symm p.1).1,
        ((finProdFinEquiv : Fin n × Fin m ≃ Fin (n * m)).symm p.2).1),
      (((finProdFinEquiv : Fin n × Fin m ≃ Fin (n * m)).symm p.1).2,
        ((finProdFinEquiv : Fin n × Fin m ≃ Fin (n * m)).symm p.2).2))
  left_inv p := by
    rcases p with ⟨⟨i, j⟩, ⟨u, v⟩⟩
    simp only [Equiv.symm_apply_apply]
  right_inv p := by
    rcases p with ⟨i, j⟩
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]

/-- The product of two square matrix tensors is the larger square tensor under
an explicit bijective relabeling of each local coordinate space. -/
theorem square_product_pullback (n m : ℕ) :
    Tensor.pullback (squareProductCoordinates n m) (squareProductCoordinates n m)
      (squareProductCoordinates n m) (squareMatrixTensor (K := K) (n * m)) =
      Tensor.product (squareMatrixTensor (K := K) n) (squareMatrixTensor (K := K) m) := by
  let e : (Fin n × Fin m) ≃ Fin (n * m) := finProdFinEquiv
  have he := matrixCoefficients_pullback_injective (K := K) e e e
    e.injective e.injective e.injective
  funext x y z
  let x' : (Fin n × Fin m) × (Fin n × Fin m) := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  let y' : (Fin n × Fin m) × (Fin n × Fin m) := ((y.1.1, y.2.1), (y.1.2, y.2.2))
  let z' : (Fin n × Fin m) × (Fin n × Fin m) := ((z.1.1, z.2.1), (z.1.2, z.2.2))
  calc
    _ = Tensor.matrixCoefficients (K := K) (Fin n × Fin m) (Fin n × Fin m)
        (Fin n × Fin m) x' y' z' := congrFun (congrFun (congrFun he x') y') z'
    _ = _ := (Tensor.matrixCoefficients_product (K := K) x' y' z').symm

/-- Taking the first `n` indices in each matrix direction is an actual local
restriction of the larger matrix multiplication tensor. -/
theorem square_restricts_of_le {n m : ℕ} (h : n ≤ m) :
    Restricts (squareMatrixTensor (K := K) m) (squareMatrixTensor (K := K) n) := by
  let e : Fin n → Fin m := fun i => ⟨i.val, lt_of_lt_of_le i.isLt h⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun k : Fin m => k.val) hij
  have hr := Restricts.pullback (squareMatrixTensor (K := K) m)
    (Prod.map e e) (Prod.map e e) (Prod.map e e)
  have hp := matrixCoefficients_pullback_injective (K := K) e e e he he he
  change Tensor.pullback (Prod.map e e) (Prod.map e e) (Prod.map e e)
    (squareMatrixTensor (K := K) m) = squareMatrixTensor (K := K) n at hp
  rwa [hp] at hr

/-- The usual cubic tensor decomposition, with one term for each triple of
matrix indices rather than one term for each ambient coefficient. -/
theorem square_rankAtMost_cubic (n : ℕ) :
    Tensor.RankAtMost (squareMatrixTensor (K := K) n) (n ^ 3) := by
  let a : (Fin n × Fin n × Fin n) → (Fin n × Fin n) → K :=
    fun p x => if p.1 = x.1 ∧ p.2.1 = x.2 then 1 else 0
  let b : (Fin n × Fin n × Fin n) → (Fin n × Fin n) → K :=
    fun p y => if p.2.1 = y.1 ∧ p.2.2 = y.2 then 1 else 0
  let c : (Fin n × Fin n × Fin n) → (Fin n × Fin n) → K :=
    fun p z => if p.2.2 = z.1 ∧ z.2 = p.1 then 1 else 0
  have hr := Tensor.rankAtMost_sum_rankOne a b c
  have heq : (fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z) =
      squareMatrixTensor (K := K) n := by
    funext x y z
    rw [Finset.sum_eq_single (x.1, x.2, y.2)]
    · by_cases hxy : x.2 = y.1 <;> by_cases hyz : y.2 = z.1 <;>
        by_cases hzx : z.2 = x.1 <;>
          simp [a, b, c, Tensor.rankOne, squareMatrixTensor, Tensor.matrixCoefficients, hxy, hyz,
            hzx]
    · intro p hp hne
      by_cases hi : p.1 = x.1
      · by_cases hj : p.2.1 = x.2
        · by_cases hk : p.2.2 = y.2
          · exact (hne (Prod.ext hi (Prod.ext hj hk))).elim
          · simp [a, b, c, Tensor.rankOne, hk]
        · simp [a, b, c, Tensor.rankOne, hj]
      · simp [a, b, c, Tensor.rankOne, hi]
    · simp
  rw [heq] at hr
  simpa [Fintype.card_prod, Fintype.card_fin, pow_succ, mul_assoc] using hr

end CoefficientTensor

/-- A finite coefficient tensor with an explicit dimension on every leg. -/
structure TensorRep (K : Type*) where
  /-- The size of the first tensor leg. -/
  xDim : ℕ
  /-- The size of the second tensor leg. -/
  yDim : ℕ
  /-- The size of the third tensor leg. -/
  zDim : ℕ
  /-- The `(TensorRep K)` component of type `Tensor K (Fin xDim) (Fin yDim) (Fin zDim)`. -/
  coeff : Tensor K (Fin xDim) (Fin yDim) (Fin zDim)

namespace TensorRep

/-- Encode arbitrary finite coordinates by their canonical finite enumeration. -/
noncomputable def ofTensor {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : (TensorRep K) where
  xDim := Fintype.card X
  yDim := Fintype.card Y
  zDim := Fintype.card Z
  coeff := Tensor.pullback (Fintype.equivFin X).symm
    (Fintype.equivFin Y).symm (Fintype.equivFin Z).symm T

/-- Requires `CoefficientTensor.Restricts A.coeff B.coeff`. -/
def Restricts (A B : (TensorRep K)) : Prop := CoefficientTensor.Restricts A.coeff B.coeff

theorem Restricts.refl (A : (TensorRep K)) : Restricts A A :=
  CoefficientTensor.Restricts.refl A.coeff

theorem Restricts.trans {A B C : (TensorRep K)}
    (hAB : Restricts A B) (hBC : Restricts B C) : Restricts A C :=
  CoefficientTensor.Restricts.trans hAB hBC

theorem restricts_ofTensor {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) :
    CoefficientTensor.Restricts T (ofTensor T).coeff :=
  CoefficientTensor.Restricts.pullback T _ _ _

theorem ofTensor_restricts {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) :
    CoefficientTensor.Restricts (ofTensor T).coeff T := by
  have h := CoefficientTensor.Restricts.pullback (ofTensor T).coeff
    (Fintype.equivFin X) (Fintype.equivFin Y) (Fintype.equivFin Z)
  have heq : Tensor.pullback (Fintype.equivFin X) (Fintype.equivFin Y)
      (Fintype.equivFin Z) (ofTensor T).coeff = T := by
    funext x y z
    simp only [ofTensor, Tensor.pullback, Equiv.symm_apply_apply]
  rcases h with ⟨a, b, c, hc⟩
  exact ⟨a, b, c, heq.symm.trans hc⟩

theorem Restricts.ofTensor {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {U' : Tensor K U V W}
    (h : CoefficientTensor.Restricts T U') : Restricts (ofTensor T) (ofTensor U') :=
  (ofTensor_restricts T).trans (h.trans (restricts_ofTensor U'))

/-- Mutual actual restriction, allowing unused or zero coordinates. -/
def Equivalent (A B : (TensorRep K)) : Prop := Restricts A B ∧ Restricts B A

instance mutualRestriction : Setoid (TensorRep K) where
  r := Equivalent
  iseqv := ⟨fun A => ⟨.refl A, .refl A⟩,
    fun h => ⟨h.2, h.1⟩,
    fun hAB hBC => ⟨hAB.1.trans hBC.1, hBC.2.trans hAB.2⟩⟩

theorem equivalent_ofTensor_coeff (A : (TensorRep K)) : Equivalent (ofTensor A.coeff) A :=
  ⟨ofTensor_restricts A.coeff, restricts_ofTensor A.coeff⟩

end TensorRep

/-- Finite coefficient tensors modulo mutual restriction. -/
def TensorClass (K : Type*) [CommSemiring K] :=
  Quotient (TensorRep.mutualRestriction (K := K))

namespace TensorClass

/-- Sends the representative to its class in the quotient. -/
def ofRep (A : (TensorRep K)) : (TensorClass K) := Quotient.mk _ A

/-- Computes the of tensor by the application `ofRep (TensorRep.ofTensor T)`. -/
noncomputable def ofTensor {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : (TensorClass K) := ofRep (TensorRep.ofTensor T)

theorem ofRep_eq {A B : (TensorRep K)} (h : TensorRep.Equivalent A B) :
    ofRep A = ofRep B := Quotient.sound h

theorem ofTensor_coeff (A : (TensorRep K)) : ofTensor A.coeff = ofRep A :=
  ofRep_eq (TensorRep.equivalent_ofTensor_coeff A)

theorem ofTensor_eq {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W}
    (hTS : CoefficientTensor.Restricts T S)
    (hST : CoefficientTensor.Restricts S T) : ofTensor T = ofTensor S :=
  ofRep_eq ⟨TensorRep.Restricts.ofTensor hTS, TensorRep.Restricts.ofTensor hST⟩

theorem ofTensor_pullback_equiv {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (f : U ≃ X) (g : V ≃ Y) (h : W ≃ Z) :
    ofTensor (Tensor.pullback f g h T) = ofTensor T := by
  apply ofTensor_eq
  · have h' := CoefficientTensor.Restricts.pullback (Tensor.pullback f g h T)
      f.symm g.symm h.symm
    have heq : Tensor.pullback f.symm g.symm h.symm (Tensor.pullback f g h T) = T := by
      funext x y z
      simp only [Tensor.pullback, Equiv.apply_symm_apply]
    rw [heq] at h'
    exact h'
  · exact CoefficientTensor.Restricts.pullback T f g h

instance : LE (TensorClass K) where
  le A B := Quotient.liftOn₂ A B (fun a b => TensorRep.Restricts b a) (by
    intro A B A' B' hA hB
    apply propext
    exact ⟨fun h => hB.2.trans (h.trans hA.1),
      fun h => hB.1.trans (h.trans hA.2)⟩)

instance : PartialOrder (TensorClass K) where
  le := (· ≤ ·)
  le_refl := by
    intro A
    induction A using Quotient.inductionOn with | h a =>
      exact TensorRep.Restricts.refl a
  le_trans := by
    intro A B C
    induction A using Quotient.inductionOn with | h A =>
      induction B using Quotient.inductionOn with | h B =>
        induction C using Quotient.inductionOn with | h C =>
          exact fun hAB hBC => TensorRep.Restricts.trans hBC hAB
  le_antisymm := by
    intro A B
    induction A using Quotient.inductionOn with | h A =>
      induction B using Quotient.inductionOn with | h B =>
        exact fun hAB hBA => Quotient.sound ⟨hBA, hAB⟩

theorem ofTensor_le {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W}
    (h : CoefficientTensor.Restricts T S) : ofTensor S ≤ ofTensor T :=
  TensorRep.Restricts.ofTensor h

end TensorClass
end MatrixMultiplicationAllFields.TensorSpectrum
