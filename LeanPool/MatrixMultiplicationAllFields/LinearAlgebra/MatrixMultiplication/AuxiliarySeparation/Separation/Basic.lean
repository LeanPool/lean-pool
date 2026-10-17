/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Separation/Basic.lean`, by
Jeroen Zuiddam, 2026: separation with a period `L` as in `FiniteProjection`; `ℂ` replaced by a field
`K`; removed the ℂ-only lemmas `finiteSeparation_degeneratesTo`,
`finiteSeparation_directSum_degeneratesTo` and `polynomial_degeneration_of_nonzero_restrictions`
(not needed by the retained proof); no declaration here needs `K` algebraically closed; unused
`simp` arguments removed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.FiniteProjection
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexDotPairing
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorSymmetrization
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# The tensor map with `L` copies

The branches have a common first coordinate space and common sizes on the other
two legs. Their second and third coordinates carry a matching sector label.
The three maps below are independent linear substitutions on the three legs of
`L` complete copies of the source tensor.  The paper takes `L = 5M`; here `L`
is any period with `3(M - 1) < L` that is nonzero in the coefficient field.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

variable {M L : ℕ} {X Y Z : Type*}

/-- The paper numbers sectors from one, while `Fin M` numbers them from zero. -/
def sectorNumber (i : Fin M) : ℤ := (i.val : ℤ) + 1

theorem sectorNumber_bounds (i : Fin M) :
    1 ≤ sectorNumber i ∧ sectorNumber i ≤ M := by
  have hi := i.isLt
  unfold sectorNumber
  omega

theorem sectorNumber_injective : Function.Injective (@sectorNumber M) := by
  intro i j hij
  apply Fin.ext
  unfold sectorNumber at hij
  omega

/-- Branches sharing X, with matching and disjoint Y and Z sectors. -/
def sharedFirstTensor (B : Fin M → Tensor K X Y Z) :
    Tensor K X (Fin M × Y) (Fin M × Z) :=
  fun x y z => if y.1 = z.1 then B y.1 x y.2 z.2 else 0

/-- The first local Fourier substitution guesses the missing sector. -/
def firstProjectionMap (ζ : K) :
    (X × Fin M) → (Fin L × X) → K := by
  classical
  exact fun x r => if r.2 = x.1 then
    ζ ^ ((r.1.val : ℤ) * (2 * sectorNumber x.2)) else 0

/-- The second local map knows the sector through its original coordinate. -/
def secondProjectionMap (ζ : K) :
    ((Fin M × Y) × Fin M) → (Fin L × (Fin M × Y)) → K := by
  classical
  exact fun y r => if r.2 = y.1 then
    ζ ^ ((r.1.val : ℤ) * (sectorNumber y.2 - sectorNumber y.1.1)) else 0

/-- The third local map carries the single Fourier normalization factor. -/
def thirdProjectionMap (ζ : K) :
    ((Fin M × Z) × Fin M) → (Fin L × (Fin M × Z)) → K := by
  classical
  exact fun z r => if r.2 = z.1 then
    (L : K)⁻¹ *
      ζ ^ ((r.1.val : ℤ) * (-sectorNumber z.2 - sectorNumber z.1.1)) else 0

private theorem restrict_constantCopies
    {K A B C A' B' C' R : Type*} [CommSemiring K]
    [Fintype A] [Fintype B] [Fintype C] [Fintype R] [DecidableEq R]
    (T : Tensor K A B C)
    (a : A' → R × A → K) (b : B' → R × B → K) (c : C' → R × C → K)
    (x : A') (y : B') (z : C') :
    Tensor.restrict a b c (Tensor.directSum (fun _ : R => T)) x y z =
      ∑ r : R, ∑ i, ∑ j, ∑ k, a x (r, i) * b y (r, j) * c z (r, k) * T i j k := by
  classical
  simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type, mul_ite, ite_and]

private theorem restrict_constantCopies_delta
    {K A B C A' B' C' R : Type*} [CommSemiring K]
    [Fintype A] [Fintype B] [Fintype C] [Fintype R] [DecidableEq R]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (T : Tensor K A B C) (fa : A' → A) (fb : B' → B) (fc : C' → C)
    (a : A' → R → K) (b : B' → R → K) (c : C' → R → K)
    (x : A') (y : B') (z : C') :
    Tensor.restrict
        (fun x r => if r.2 = fa x then a x r.1 else 0)
        (fun y r => if r.2 = fb y then b y r.1 else 0)
        (fun z r => if r.2 = fc z then c z r.1 else 0)
        (Tensor.directSum (fun _ : R => T)) x y z =
      (∑ r : R, a x r * b y r * c z r) * T (fa x) (fb y) (fc z) := by
  rw [restrict_constantCopies]
  simp [ite_mul, mul_ite, Finset.sum_mul]

/-- The exact coefficient tensor after Fourier projection, before weighting. -/
def projectedTensor (L : ℕ) (ζ : K) (B : Fin M → Tensor K X Y Z) :
    Tensor K (X × Fin M) ((Fin M × Y) × Fin M) ((Fin M × Z) × Fin M) :=
  fun x y z => if y.1.1 = z.1.1 then
    finiteFourierCoefficient ζ L
      (phase (sectorNumber x.2) (sectorNumber y.1.1)
        (sectorNumber y.2) (sectorNumber z.2)) (B y.1.1 x.1 y.1.2 z.1.2)
    else 0

/-- The `L` copies and the three explicit local Fourier maps realize
the projected tensor by an ordinary restriction. -/
theorem finiteProjection_restrict [Fintype X] [Fintype Y] [Fintype Z]
    (ζ : K) (hζ : ζ ≠ 0) (B : Fin M → Tensor K X Y Z) :
    Tensor.restrict (firstProjectionMap ζ) (secondProjectionMap ζ)
        (thirdProjectionMap ζ)
        (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B)) =
      projectedTensor L ζ B := by
  classical
  funext x y z
  unfold firstProjectionMap secondProjectionMap thirdProjectionMap
  rw [restrict_constantCopies_delta (R := Fin L)
    (sharedFirstTensor B) Prod.fst Prod.fst Prod.fst
    (fun x r => ζ ^ ((r.val : ℤ) * (2 * sectorNumber x.2)))
    (fun y r => ζ ^ ((r.val : ℤ) * (sectorNumber y.2 - sectorNumber y.1.1)))
    (fun z r => (L : K)⁻¹ *
      ζ ^ ((r.val : ℤ) * (-sectorNumber z.2 - sectorNumber z.1.1))) x y z]
  by_cases hyz : y.1.1 = z.1.1
  · simp only [sharedFirstTensor, projectedTensor, hyz, ↓reduceIte]
    have hterm (r : Fin L) :
        ζ ^ ((r.val : ℤ) * (2 * sectorNumber x.2)) *
          ζ ^ ((r.val : ℤ) * (sectorNumber y.2 - sectorNumber y.1.1)) *
          ((L : K)⁻¹ *
            ζ ^ ((r.val : ℤ) * (-sectorNumber z.2 - sectorNumber z.1.1))) =
        (L : K)⁻¹ *
          ζ ^ ((r.val : ℤ) * phase (sectorNumber x.2) (sectorNumber y.1.1)
            (sectorNumber y.2) (sectorNumber z.2)) := by
      rw [← hyz]
      calc
        _ = (L : K)⁻¹ *
            (ζ ^ ((r.val : ℤ) * (2 * sectorNumber x.2)) *
            ζ ^ ((r.val : ℤ) * (sectorNumber y.2 - sectorNumber y.1.1)) *
            ζ ^ ((r.val : ℤ) * (-sectorNumber z.2 - sectorNumber y.1.1))) := by ring
        _ = (L : K)⁻¹ * ζ ^
            ((r.val : ℤ) * (2 * sectorNumber x.2) +
             (r.val : ℤ) * (sectorNumber y.2 - sectorNumber y.1.1) +
             (r.val : ℤ) * (-sectorNumber z.2 - sectorNumber y.1.1)) := by
          rw [zpow_add₀ hζ, zpow_add₀ hζ]
        _ = _ := by congr 2; unfold phase; ring
    simp only [← hyz] at hterm ⊢
    simp_rw [hterm]
    rw [← Finset.mul_sum,
      Fin.sum_univ_eq_sum_range (fun r : ℕ => ζ ^ ((r : ℤ) *
        phase (sectorNumber x.2) (sectorNumber y.1.1)
          (sectorNumber y.2) (sectorNumber z.2))) L]
    unfold finiteFourierCoefficient
    rw [← Finset.sum_mul]
    simp only [mul_assoc]
  · simp [sharedFirstTensor, projectedTensor, hyz]

/-- The polynomial after the Fourier projection and square weighting. -/
def separationPolynomial (L : ℕ) (ζ : K) (B : Fin M → Tensor K X Y Z) :
    Tensor (Polynomial K) (X × Fin M)
      ((Fin M × Y) × Fin M) ((Fin M × Z) × Fin M) :=
  fun x y z => if y.1.1 = z.1.1 then
    projectedBranchPolynomial ζ L (sectorNumber x.2) (sectorNumber y.1.1)
      (sectorNumber y.2) (sectorNumber z.2) (B y.1.1 x.1 y.1.2 z.1.2)
    else 0

/-- The surviving tensor: sector labels match on all three legs, while the
additional second/third coordinates form a dot product. -/
def separationTarget (B : Fin M → Tensor K X Y Z) :
    Tensor K (X × Fin M) ((Fin M × Y) × Fin M) ((Fin M × Z) × Fin M) :=
  fun x y z => if x.2 = y.1.1 ∧ y.1.1 = z.1.1 ∧ y.2 = z.2 then
    B y.1.1 x.1 y.1.2 z.1.2 else 0

/-- The square-weighted polynomial has exactly the advertised constant tensor. -/
theorem separationPolynomial_coeff_zero {ζ : K} (hM : 0 < M)
    (hL : (L : K) ≠ 0) (hLM : 3 * M < L + 3) (hζ : IsPrimitiveRoot ζ L) (B : Fin M → Tensor K X Y Z) :
    (fun x y z => (separationPolynomial L ζ B x y z).coeff 0) =
      separationTarget B := by
  classical
  funext x y z
  by_cases hyz : y.1.1 = z.1.1
  · simp only [separationPolynomial, hyz, ↓reduceIte]
    rw [projectedBranchPolynomial_coeff_zero hM hL hLM hζ
      (sectorNumber_bounds _) (sectorNumber_bounds _)
      (sectorNumber_bounds _) (sectorNumber_bounds _)]
    simp only [sectorNumber_injective.eq_iff, separationTarget, hyz, true_and]
  · simp [separationPolynomial, separationTarget, hyz]

/-- Its degree is bounded for each fixed finite separation construction. -/
theorem separationPolynomial_degree {ζ : K} (hM : 0 < M)
    (hL : (L : K) ≠ 0) (hLM : 3 * M < L + 3) (hζ : IsPrimitiveRoot ζ L) (B : Fin M → Tensor K X Y Z)
    (x : X × Fin M) (y : (Fin M × Y) × Fin M) (z : (Fin M × Z) × Fin M) :
    (separationPolynomial L ζ B x y z).degree ≤ ((M - 1) ^ 2 : ℕ) := by
  apply Polynomial.degree_le_of_natDegree_le
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases hyz : y.1.1 = z.1.1
  · simp only [separationPolynomial, hyz, ↓reduceIte]
    exact projectedBranchPolynomial_coeff_eq_zero_of_lt hM hL hLM hζ
      (sectorNumber_bounds _) (sectorNumber_bounds _)
      (sectorNumber_bounds _) (sectorNumber_bounds _) hn _
  · simp [separationPolynomial, hyz]

private theorem restrict_target_scalars
    {A B C A' B' C' : Type*} [Fintype A] [Fintype B] [Fintype C]
    (T : Tensor K A B C) (a : A' → A → K) (b : B' → B → K)
    (c : C' → C → K) (s : A' → K) (t : B' → K) (u : C' → K) :
    Tensor.restrict (fun x i => s x * a x i) (fun y j => t y * b y j)
        (fun z k => u z * c z k) T =
      fun x y z => (s x * t y * u z) * Tensor.restrict a b c T x y z := by
  funext x y z
  simp only [Tensor.restrict, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The first local Fourier map followed by its integer weight. -/
def firstSeparationMap (ζ t : K) (x : X × Fin M) (r : Fin L × X) : K :=
  t ^ firstWeight (sectorNumber x.2) * firstProjectionMap ζ x r

/-- The second local Fourier map followed by its possibly negative weight. -/
def secondSeparationMap (ζ t : K) (y : (Fin M × Y) × Fin M)
    (r : Fin L × (Fin M × Y)) : K :=
  t ^ secondWeight (sectorNumber y.1.1) (sectorNumber y.2) * secondProjectionMap ζ y r

/-- The third local Fourier map followed by its possibly negative weight. -/
def thirdSeparationMap (ζ t : K) (z : (Fin M × Z) × Fin M)
    (r : Fin L × (Fin M × Z)) : K :=
  t ^ thirdWeight (sectorNumber z.1.1) (sectorNumber z.2) * thirdProjectionMap ζ z r

theorem weightedProjection_restrict [Fintype X] [Fintype Y] [Fintype Z]
    (ζ t : K) (hζ : ζ ≠ 0) (B : Fin M → Tensor K X Y Z) :
    Tensor.restrict (firstSeparationMap ζ t) (secondSeparationMap ζ t)
        (thirdSeparationMap ζ t)
        (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B)) =
      fun x y z =>
        (t ^ firstWeight (sectorNumber x.2) *
          t ^ secondWeight (sectorNumber y.1.1) (sectorNumber y.2) *
          t ^ thirdWeight (sectorNumber z.1.1) (sectorNumber z.2)) *
            projectedTensor L ζ B x y z := by
  unfold firstSeparationMap secondSeparationMap thirdSeparationMap
  rw [restrict_target_scalars, finiteProjection_restrict ζ hζ B]

/-- At every nonzero parameter the polynomial tensor is an ordinary restriction
of exactly `L` complete source copies. -/
theorem separationPolynomial_eval [Fintype X] [Fintype Y] [Fintype Z]
    {ζ : K} (hM : 0 < M) (hL : (L : K) ≠ 0) (hLM : 3 * M < L + 3) (hζ : IsPrimitiveRoot ζ L)
    (B : Fin M → Tensor K X Y Z) (t : K) (ht : t ≠ 0) :
    (fun x y z => (separationPolynomial L ζ B x y z).eval t) =
      Tensor.restrict (firstSeparationMap ζ t) (secondSeparationMap ζ t)
        (thirdSeparationMap ζ t)
        (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B)) := by
  rw [weightedProjection_restrict ζ t (hζ.ne_zero (by rintro rfl; simp at hL)) B]
  funext x y z
  by_cases hyz : y.1.1 = z.1.1
  · simp only [separationPolynomial, projectedTensor, hyz, ↓reduceIte,
      projectedBranchPolynomial, Polynomial.eval_monomial]
    simp only [← hyz]
    rw [fiveMFourierCoefficient_eq_ite hM hL hLM hζ
      (sectorNumber_bounds _) (sectorNumber_bounds _)
      (sectorNumber_bounds _) (sectorNumber_bounds _)]
    split_ifs with hp
    · have he : t ^ firstWeight (sectorNumber x.2) *
          t ^ secondWeight (sectorNumber y.1.1) (sectorNumber y.2) *
          t ^ thirdWeight (sectorNumber y.1.1) (sectorNumber z.2) =
          t ^ totalWeight (sectorNumber x.2) (sectorNumber y.1.1)
            (sectorNumber y.2) (sectorNumber z.2) := by
        rw [totalWeight, zpow_add₀ ht, zpow_add₀ ht]
      rw [he, ← totalDegree_cast_of_phase_eq_zero hp, zpow_natCast]
      exact mul_comm _ _
    · simp
  · simp [separationPolynomial, projectedTensor, hyz]

/-- The first-leg relabeling adds the trivial first coordinate of the dot product. -/
def separationFirstEquiv : (X × Fin M) ≃ (Fin M × (X × Unit)) where
  toFun x := (x.2, (x.1, ()))
  invFun x := (x.2.1, x.1)
  left_inv _ := rfl
  right_inv x := by rcases x with ⟨h, x, u⟩; cases u; rfl

/-- The other two relabelings merely reassociate their coordinates. -/
def separationSideEquiv (A : Type*) : ((Fin M × A) × Fin M) ≃
    (Fin M × (A × Fin M)) := Equiv.prodAssoc _ _ _

/-- The separated target, expressed as a genuine full direct sum of products. -/
theorem separationTarget_eq_directSum (B : Fin M → Tensor K X Y Z) :
    separationTarget B =
      Tensor.pullback
        separationFirstEquiv (separationSideEquiv Y) (separationSideEquiv Z)
        (Tensor.directSum (fun h => Tensor.product (B h)
          (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin M)))))) := by
  classical
  funext x y z
  simp only [separationTarget, Tensor.pullback, Tensor.directSum, Tensor.product,
    Tensor.cyclic, Tensor.dotPairing, separationFirstEquiv, separationSideEquiv,
    Equiv.coe_fn_mk, Equiv.prodAssoc_apply]
  by_cases hxy : x.2 = y.1.1
  · by_cases hyz : y.1.1 = z.1.1
    · simp [hxy, hyz]
    · simp [hxy, hyz]
  · simp [hxy]

end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
