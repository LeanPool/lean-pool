/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocalCurrents
public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Topology.Instances.Matrix

/-!
# Oriented coordinate pairing with test forms

The forward map uses the normalized exterior product: one summand per
`(k,q)` shuffle, represented by the quotient of permutations by permutations
within the two blocks. Thus there is no extra factorial. Every test coefficient
is obtained by continuous linear postcomposition on the actual test-function
space. The ordered basis fixes the volume normalization; changing its volume
can change the current. No positivity or chart compatibility is asserted.
-/

@[expose] public section

noncomputable section

open TopologicalSpace TensorProduct
open scoped Distributions

namespace SGPT.Foundations.Analysis.LocalCurrents

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Opens E} {k q : ℕ}

/-- Evaluation of a continuous alternating form at a fixed tuple is continuous
linear; this follows from the operator norm topology, not an extra hypothesis. -/
def formEvaluationCLM (v : Fin q → E) : (E [⋀^Fin q]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.id ℝ (E [⋀^Fin q]→L[ℝ] ℝ)).flipAlternating v

@[simp] theorem formEvaluationCLM_apply (v : Fin q → E)
    (η : E [⋀^Fin q]→L[ℝ] ℝ) : formEvaluationCLM v η = η v := rfl

/-- An actual continuous extraction of scalar test coefficients. -/
def testCoefficientCLM (v : Fin q → E) : TestForm Ω q →L[ℝ] 𝓓(Ω, ℝ) :=
  TestFunction.postcompCLM (formEvaluationCLM v)

@[simp] theorem testCoefficientCLM_apply (v : Fin q → E)
    (η : TestForm Ω q) (x : E) : testCoefficientCLM v η x = η x v := rfl

/-- A test form as an alternating map with scalar test-function coefficients. -/
def testFormAlternating (η : TestForm Ω q) : E [⋀^Fin q]→ₗ[ℝ] 𝓓(Ω, ℝ) where
  toFun v := testCoefficientCLM v η
  map_update_add' v i a b := by
    ext x
    exact (η x).map_update_add v i a b
  map_update_smul' v i c a := by
    ext x
    exact (η x).map_update_smul v i c a
  map_eq_zero_of_eq' v i j hv hij := by
    ext x
    exact (η x).map_eq_zero_of_eq v hv hij

@[simp] theorem testFormAlternating_apply (η : TestForm Ω q) (v : Fin q → E) :
    testFormAlternating η v = testCoefficientCLM v η := rfl

/-- Evaluation of distributions on tests, extended to the algebraic tensor product. -/
def distributionTestPairing : 𝓓'(Ω, ℝ) ⊗[ℝ] 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ :=
  TensorProduct.lift
    { toFun := fun T => T.toLinearMap
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp] theorem distributionTestPairing_tmul (T : 𝓓'(Ω, ℝ)) (φ : 𝓓(Ω, ℝ)) :
    distributionTestPairing (T ⊗ₜ[ℝ] φ) = T φ := rfl

/-- The normalized shuffle pairing evaluated on a top-degree frame. No basis
assumption is needed for this auxiliary construction. -/
def wedgePairing (v : Fin k ⊕ Fin q → E) (A : DistributionForm Ω k) :
    TestForm Ω q →L[ℝ] ℝ :=
  ∑ s : Equiv.Perm.ModSumCongr (Fin k) (Fin q),
    Equiv.Perm.sign s.out •
      (A (fun i => v (s.out (Sum.inl i)))).comp
        (testCoefficientCLM (fun j => v (s.out (Sum.inr j))))

theorem wedgePairing_apply (v : Fin k ⊕ Fin q → E) (A : DistributionForm Ω k)
    (η : TestForm Ω q) :
    wedgePairing v A η =
      ∑ s : Equiv.Perm.ModSumCongr (Fin k) (Fin q),
        Equiv.Perm.sign s.out •
          A (fun i => v (s.out (Sum.inl i)))
            (testCoefficientCLM (fun j => v (s.out (Sum.inr j))) η) := by
  simp only [wedgePairing, sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  rfl

/-- Identification with mathlib's exterior product checks both the sign and
the shuffle normalization, independently of the chosen quotient representatives. -/
theorem wedgePairing_eq_domCoprod (v : Fin k ⊕ Fin q → E)
    (A : DistributionForm Ω k) (η : TestForm Ω q) :
    wedgePairing v A η =
      distributionTestPairing ((A.domCoprod (testFormAlternating η)) v) := by
  rw [wedgePairing_apply, AlternatingMap.domCoprod_apply, sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  conv_rhs => rw [← Quotient.out_eq s, AlternatingMap.domCoprod.summand_mk'']
  change Equiv.Perm.sign s.out •
      A (fun i => v (s.out (Sum.inl i)))
        (testCoefficientCLM (fun j => v (s.out (Sum.inr j))) η) =
    distributionTestPairing (Equiv.Perm.sign s.out •
      (A (fun i => v (s.out (Sum.inl i))) ⊗ₜ[ℝ]
        (testCoefficientCLM (fun j => v (s.out (Sum.inr j))) η)))
  simp [Units.smul_def]

/-- Multiply a scalar test by a fixed continuous alternating form. -/
def constantTestFormCLM (β : E [⋀^Fin q]→L[ℝ] ℝ) :
    𝓓(Ω, ℝ) →L[ℝ] TestForm Ω q :=
  TestFunction.postcompCLM ((ContinuousLinearMap.id ℝ ℝ).smulRight β)

@[simp] theorem constantTestFormCLM_apply (β : E [⋀^Fin q]→L[ℝ] ℝ)
    (φ : 𝓓(Ω, ℝ)) (x : E) : constantTestFormCLM β φ x = φ x • β := rfl

/-- A test coefficient of a constant-form test has its expected scalar value. -/
theorem testCoefficient_constantTestForm (v : Fin q → E)
    (β : E [⋀^Fin q]→L[ℝ] ℝ) (φ : 𝓓(Ω, ℝ)) :
    testCoefficientCLM v (constantTestFormCLM β φ) = β v • φ := by
  ext x
  simp [mul_comm]

/-- Contraction in the first block of a continuous volume form. -/
def contractVolume (vol : E [⋀^(Fin k ⊕ Fin q)]→L[ℝ] ℝ) (v : Fin k → E) :
    E [⋀^Fin q]→L[ℝ] ℝ where
  toContinuousMultilinearMap := vol.toContinuousMultilinearMap.currySum v
  map_eq_zero_of_eq' w i j hw hij :=
    vol.map_eq_zero_of_eq (Sum.elim v w) (i := Sum.inr i) (j := Sum.inr j)
      hw (Sum.inr_injective.ne hij)

@[simp] theorem contractVolume_apply
    (vol : E [⋀^(Fin k ⊕ Fin q)]→L[ℝ] ℝ) (v : Fin k → E) (w : Fin q → E) :
    contractVolume vol v w = vol (Sum.elim v w) := rfl

/-- Volume contraction is itself alternating and multilinear in the inserted tuple. -/
def volumeContraction (vol : E [⋀^(Fin k ⊕ Fin q)]→L[ℝ] ℝ) :
    E [⋀^Fin k]→ₗ[ℝ] (E [⋀^Fin q]→L[ℝ] ℝ) where
  toFun := contractVolume vol
  map_update_add' v i a b := by
    ext w
    exact congrArg (fun f => f w)
      (vol.toContinuousMultilinearMap.currySum.map_update_add v i a b)
  map_update_smul' v i c a := by
    ext w
    exact congrArg (fun f => f w)
      (vol.toContinuousMultilinearMap.currySum.map_update_smul v i c a)
  map_eq_zero_of_eq' v i j hv hij := by
    ext w
    exact vol.map_eq_zero_of_eq (Sum.elim v w) (i := Sum.inl i) (j := Sum.inl j)
      hv (Sum.inl_injective.ne hij)

/-- Testing a current against scalar multiples of a constant form produces
an actual distribution, linearly in the constant form. -/
def constantFormDistribution (T : TestForm Ω q →L[ℝ] ℝ) :
    (E [⋀^Fin q]→L[ℝ] ℝ) →ₗ[ℝ] 𝓓'(Ω, ℝ) where
  toFun β := T.comp (constantTestFormCLM β)
  map_add' β γ := by
    ext φ
    change T (constantTestFormCLM (β + γ) φ) =
      T (constantTestFormCLM β φ) + T (constantTestFormCLM γ φ)
    rw [← map_add]
    congr 1
    ext x w
    simp [smul_add]
  map_smul' c β := by
    ext φ
    change T (constantTestFormCLM (c • β) φ) = c • T (constantTestFormCLM β φ)
    rw [← map_smul]
    congr 1
    ext x w
    simp [smul_smul, mul_comm]

/-- The reverse coefficient construction for an explicit continuous volume.
No inverse or nondegeneracy assertion is built into this definition. -/
def currentCoefficients (vol : E [⋀^(Fin k ⊕ Fin q)]→L[ℝ] ℝ)
    (T : TestForm Ω q →L[ℝ] ℝ) : DistributionForm Ω k :=
  (constantFormDistribution T).compAlternatingMap (volumeContraction vol)

@[simp] theorem currentCoefficients_apply
    (vol : E [⋀^(Fin k ⊕ Fin q)]→L[ℝ] ℝ) (T : TestForm Ω q →L[ℝ] ℝ)
    (v : Fin k → E) (φ : 𝓓(Ω, ℝ)) :
    currentCoefficients vol T v φ = T (constantTestFormCLM (contractVolume vol v) φ) := rfl

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- Split an ordered real basis into the current and test blocks, whose degrees
sum to the real dimension. -/
def currentPairingBasis (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (k : Fin (Module.finrank ℝ E + 1)) :
    Module.Basis (Fin k.val ⊕ Fin (Module.finrank ℝ E - k.val)) ℝ E :=
  b.reindex (finSumFinEquiv.trans (finCongr (by omega))).symm

/-- The continuous determinant form of a finite basis. -/
def basisVolume {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) :
    E [⋀^ι]→L[ℝ] ℝ :=
  { b.det with
    cont := by
      change Continuous (fun v => (b.toMatrix v).det)
      apply Continuous.matrix_det
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact (b.coord i).continuous_of_finiteDimensional.comp (continuous_apply j) }

@[simp] theorem basisVolume_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (v : ι → E) : basisVolume b v = b.det v := rfl

theorem basisVolume_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) : basisVolume b b = 1 := b.det_self

/-- Pair distribution-valued forms with actual complementary-degree test forms,
using the ordered basis volume (equal to one on that basis). -/
def toLocalCurrent (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (k : Fin (Module.finrank ℝ E + 1)) (A : DistributionForm Ω k.val) :
    LocalCurrent Ω k :=
  wedgePairing (currentPairingBasis b k) A

omit [FiniteDimensional ℝ E] in
theorem toLocalCurrent_eq_domCoprod
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (k : Fin (Module.finrank ℝ E + 1)) (A : DistributionForm Ω k.val)
    (η : TestForm Ω (Module.finrank ℝ E - k.val)) :
    toLocalCurrent b k A η = distributionTestPairing
      ((A.domCoprod (testFormAlternating η)) (currentPairingBasis b k)) :=
  wedgePairing_eq_domCoprod _ _ _

/-- Recover distribution coefficients by contracting the normalized basis volume. -/
def fromLocalCurrent (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (k : Fin (Module.finrank ℝ E + 1)) (T : LocalCurrent Ω k) :
    DistributionForm Ω k.val :=
  currentCoefficients (basisVolume (currentPairingBasis b k)) T

theorem fromLocalCurrent_apply
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (k : Fin (Module.finrank ℝ E + 1)) (T : LocalCurrent Ω k)
    (v : Fin k.val → E) (φ : 𝓓(Ω, ℝ)) :
    fromLocalCurrent b k T v φ = T (constantTestFormCLM
      (contractVolume (basisVolume (currentPairingBasis b k)) v) φ) := rfl

omit [FiniteDimensional ℝ E] in
/-- Changing a frame scales the pairing by its determinant. Equal orientation
alone is insufficient for equality; the normalized volumes must agree. -/
theorem wedgePairing_change_basis
    (b c : Module.Basis (Fin k ⊕ Fin q) ℝ E) (A : DistributionForm Ω k) :
    wedgePairing c A = b.det c • wedgePairing b A := by
  ext η
  simp only [smul_apply, wedgePairing_eq_domCoprod]
  let W := distributionTestPairing.compAlternatingMap (A.domCoprod (testFormAlternating η))
  change W c = b.det c • W b
  have h := congrArg (fun f : E [⋀^(Fin k ⊕ Fin q)]→ₗ[ℝ] ℝ => f c)
    (W.eq_smul_basis_det b)
  simpa [mul_comm] using h

omit [FiniteDimensional ℝ E] in
theorem toLocalCurrent_change_basis
    (b c : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (k : Fin (Module.finrank ℝ E + 1)) (A : DistributionForm Ω k.val) :
    toLocalCurrent c k A =
      (currentPairingBasis b k).det (currentPairingBasis c k) • toLocalCurrent b k A :=
  wedgePairing_change_basis _ _ _

end FiniteDimensional

end SGPT.Foundations.Analysis.LocalCurrents
