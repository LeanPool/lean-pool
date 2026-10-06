/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.MixedOrderFiniteRecurrenceCore
public import LeanPool.HighContrastHomogenization.Provider.Regularity.OrderDecouplingBoundary
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedReferenceConstantMatrix
public import LeanPool.HighContrastHomogenization.Support.Besov.Duality.CaccioppoliBridge
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.DualToCircLoss.FiniteLoss
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.HodgeProjectionL2

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderDualBesovPerturbationAlgebra

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Linear algebra for the cube full-dual vector norm

The vector norm used by the finite recurrence is the sum of its scalar
full-dual component norms.  This file records the corresponding triangle and
constant-matrix bounds on `L²` fields.  The induced matrix factor is written
explicitly as the sum of the absolute values of its entries.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

noncomputable section

private theorem cubeBesovConjExponent_two_eq :
    cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
  simpa [cubeBesovConjExponent] using
    (ENNReal.HolderConjugate.conjExponent_eq
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))

private theorem cubeBesovConjExponent_two_ne_zero :
    cubeBesovConjExponent (2 : ℝ≥0∞) ≠ 0 := by
  rw [cubeBesovConjExponent_two_eq]
  norm_num

private theorem cubeBesovConjExponent_two_ne_top :
    cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
  rw [cubeBesovConjExponent_two_eq]
  norm_num

private theorem fullTest_memLp_two
    {d : ℕ} {Q : TriadicCube d} {s : ℝ} {g : Vec d → ℝ}
    (hg : CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) g) :
    MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  have hmem := hg.memLp
  rw [show cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))] at hmem
  exact hmem

private theorem cubeBesovPairing_add_left_of_memLp_two
    {d : ℕ} (Q : TriadicCube d) (f h g : Vec d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hh : MemLp h (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovPairing Q (fun x ↦ f x + h x) g =
      cubeBesovPairing Q f g + cubeBesovPairing Q h g := by
  have hfg : Integrable (fun x ↦ f x * g x) (normalizedCubeMeasure Q) :=
    hf.integrable_mul hg
  have hhg : Integrable (fun x ↦ h x * g x) (normalizedCubeMeasure Q) :=
    hh.integrable_mul hg
  unfold cubeBesovPairing
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  rw [← integral_add hfg hhg]
  congr 1
  funext x
  ring

private theorem cubeBesovPairing_const_mul_left
    {d : ℕ} (Q : TriadicCube d) (c : ℝ) (f g : Vec d → ℝ) :
    cubeBesovPairing Q (fun x ↦ c * f x) g =
      c * cubeBesovPairing Q f g := by
  calc
    cubeBesovPairing Q (fun x ↦ c * f x) g =
        cubeBesovPairing Q g (fun x ↦ c * f x) :=
      cubeBesovPairing_comm Q _ _
    _ = c * cubeBesovPairing Q g f :=
      cubeBesovPairing_const_mul_right Q g f c
    _ = c * cubeBesovPairing Q f g := by rw [cubeBesovPairing_comm]

/-- The scalar full-dual norm is subadditive on `L²` fields. -/
theorem cubeBesovDualFullNorm_add_le_of_memLp_two
    {d : ℕ} (Q : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (f h : Vec d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hh : MemLp h (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
        (fun x ↦ f x + h x) ≤
      cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f +
        cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) h := by
  apply cubeBesovDualFullNorm_le_of_forall_fullTest_pairing_le
  · exact cubeBesovConjExponent_two_ne_zero
  · exact cubeBesovConjExponent_two_ne_top
  intro g hg
  rw [cubeBesovPairing_add_left_of_memLp_two Q f h g hf hh
    (fullTest_memLp_two hg)]
  calc
    |cubeBesovPairing Q f g + cubeBesovPairing Q h g| ≤
        |cubeBesovPairing Q f g| + |cubeBesovPairing Q h g| := abs_add_le _ _
    _ ≤ cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f +
        cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) h :=
      add_le_add
        (abs_cubeBesovPairing_le_cubeBesovDualFullNorm_of_full_test_of_memLp
          Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f g hs hf (by norm_num)
          (by norm_num) cubeBesovConjExponent_two_ne_top (by norm_num) hg)
        (abs_cubeBesovPairing_le_cubeBesovDualFullNorm_of_full_test_of_memLp
          Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) h g hs hh (by norm_num)
          (by norm_num) cubeBesovConjExponent_two_ne_top (by norm_num) hg)

/-- Multiplication by a scalar acts on the scalar full-dual norm by its
absolute value. -/
theorem cubeBesovDualFullNorm_const_mul_le_of_memLp_two
    {d : ℕ} (Q : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (c : ℝ) (f : Vec d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
        (fun x ↦ c * f x) ≤
      |c| * cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f := by
  apply cubeBesovDualFullNorm_le_of_forall_fullTest_pairing_le
  · exact cubeBesovConjExponent_two_ne_zero
  · exact cubeBesovConjExponent_two_ne_top
  intro g hg
  rw [cubeBesovPairing_const_mul_left Q c f g, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (abs_cubeBesovPairing_le_cubeBesovDualFullNorm_of_full_test_of_memLp
      Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f g hs hf (by norm_num)
      (by norm_num) cubeBesovConjExponent_two_ne_top (by norm_num) hg)
    (abs_nonneg c)

private theorem cubeBesovDualFullNorm_finset_sum_le
    {d : ℕ} (Q : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (S : Finset (Fin d)) (c : Fin d → ℝ) (F : Vec d → Vec d)
    (hF : ∀ j : Fin d,
      MemLp (fun x ↦ F x j) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
        (fun x ↦ ∑ j ∈ S, c j * F x j) ≤
      ∑ j ∈ S, |c j| *
        cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
          (fun x ↦ F x j) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      apply cubeBesovDualFullNorm_le_of_forall_fullTest_pairing_le
      · exact cubeBesovConjExponent_two_ne_zero
      · exact cubeBesovConjExponent_two_ne_top
      intro g _hg
      simp
  | @insert a S ha ih =>
      have hterm : MemLp (fun x ↦ c a * F x a) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) := by
        simpa [Pi.smul_apply, smul_eq_mul] using! (hF a).const_smul (c a)
      have hsum : MemLp (fun x ↦ ∑ j ∈ S, c j * F x j) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) := by
        exact MeasureTheory.memLp_finsetSum S fun j _hj ↦ by
          simpa [Pi.smul_apply, smul_eq_mul] using! (hF j).const_smul (c j)
      simp_rw [Finset.sum_insert ha]
      calc
        cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
            (fun x ↦ c a * F x a + ∑ j ∈ S, c j * F x j) ≤
          cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
              (fun x ↦ c a * F x a) +
            cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
              (fun x ↦ ∑ j ∈ S, c j * F x j) :=
          cubeBesovDualFullNorm_add_le_of_memLp_two Q hs _ _ hterm hsum
        _ ≤ |c a| * cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
              (fun x ↦ F x a) +
            ∑ j ∈ S, |c j| *
              cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
                (fun x ↦ F x j) :=
          add_le_add
            (cubeBesovDualFullNorm_const_mul_le_of_memLp_two Q hs (c a)
              (fun x ↦ F x a) (hF a)) ih

/-- Entry-sum matrix size induced by the component-sum full-dual vector
norm. -/
@[expose]
def dualBesovMatrixActionSize {d : ℕ} (A : Mat d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, |A i j|

theorem dualBesovMatrixActionSize_nonneg {d : ℕ} (A : Mat d) :
    0 ≤ dualBesovMatrixActionSize A := by
  exact Finset.sum_nonneg fun i _hi ↦ Finset.sum_nonneg fun j _hj ↦ abs_nonneg _

/-- Every matrix entry is bounded by the Euclidean operator norm. -/
theorem abs_matrix_entry_le_l2_opNorm {d : ℕ} (A : Mat d) (i j : Fin d) :
    |A i j| ≤ ‖A‖ := by
  let e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single j 1
  let y : EuclideanSpace ℝ (Fin d) :=
    (EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec e)
  have hyi : y i = A i j := by
    change (A.mulVec (Pi.single j 1)) i = A i j
    simp [Matrix.mulVec]
  have hcoord : ‖y i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
  have hop : ‖y‖ ≤ ‖A‖ * ‖e‖ := by
    simpa only [y] using Matrix.l2_opNorm_mulVec A e
  calc
    |A i j| = ‖y i‖ := by rw [hyi, Real.norm_eq_abs]
    _ ≤ ‖y‖ := hcoord
    _ ≤ ‖A‖ * ‖e‖ := hop
    _ = ‖A‖ := by simp [e]

/-- The entry-sum action size is controlled by the Euclidean operator norm
with the finite-dimensional factor forced by the component-sum vector norm. -/
theorem dualBesovMatrixActionSize_le_dim_sq_mul_norm
    {d : ℕ} (A : Mat d) :
    dualBesovMatrixActionSize A ≤ (d : ℝ) ^ 2 * ‖A‖ := by
  unfold dualBesovMatrixActionSize
  calc
    ∑ i : Fin d, ∑ j : Fin d, |A i j| ≤
        ∑ _i : Fin d, ∑ _j : Fin d, ‖A‖ :=
      Finset.sum_le_sum fun i _hi ↦ Finset.sum_le_sum fun j _hj ↦
        abs_matrix_entry_le_l2_opNorm A i j
    _ = (d : ℝ) ^ 2 * ‖A‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

/-- An ellipticity upper bound controls the induced entry-sum action size. -/
theorem dualBesovMatrixActionSize_le_dim_sq_mul_ellipticity
    {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) :
    dualBesovMatrixActionSize A ≤ (d : ℝ) ^ 2 * Lam := by
  unfold dualBesovMatrixActionSize
  calc
    ∑ i : Fin d, ∑ j : Fin d, |A i j| ≤
        ∑ _i : Fin d, ∑ _j : Fin d, Lam :=
      Finset.sum_le_sum fun i _hi ↦ Finset.sum_le_sum fun j _hj ↦
        abs_apply_le_of_isEllipticMatrix hA i j
    _ = (d : ℝ) ^ 2 * Lam := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

/-- A fixed matrix acts continuously on the component-sum cube full-dual
vector norm, with the exact entry-sum action size. -/
theorem cubeScaleNormalizedDualNegativeBesovVectorNormTwo_matVecMul_le
    {d : ℕ} (Q : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (A : Mat d) (F : Vec d → Vec d) (hF : MemVectorL2 (cubeSet Q) F) :
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s
        (fun x ↦ matVecMul A (F x)) ≤
      dualBesovMatrixActionSize A *
        cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F := by
  classical
  let N : Fin d → ℝ := fun j ↦
    cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x ↦ F x j)
  have hcoord : ∀ j : Fin d,
      MemLp (fun x ↦ F x j) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    Book.Ch01.Legacy.component_memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet_ch1
      Q hF
  have hcomponent : ∀ i : Fin d,
      cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
          (fun x ↦ matVecMul A (F x) i) ≤
        ∑ j : Fin d, |A i j| * N j := by
    intro i
    simpa only [matVecMul, Matrix.mulVec, dotProduct, N] using
      cubeBesovDualFullNorm_finset_sum_le Q hs Finset.univ (A i) F hcoord
  have hNnonneg : ∀ j : Fin d, 0 ≤ N j := by
    intro j
    exact cubeBesovDualFullNorm_nonneg Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
      (fun x ↦ F x j) cubeBesovConjExponent_two_ne_zero
      cubeBesovConjExponent_two_ne_top
  unfold cubeScaleNormalizedDualNegativeBesovVectorNormTwo
  calc
    cubeBesovScaleWeight s Q *
        ∑ i : Fin d, cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
          (fun x ↦ matVecMul A (F x) i) ≤
      cubeBesovScaleWeight s Q *
        ∑ i : Fin d, ∑ j : Fin d, |A i j| * N j := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun i _hi ↦ hcomponent i)
            (cubeBesovScaleWeight_nonneg s Q)
    _ ≤ dualBesovMatrixActionSize A *
        (cubeBesovScaleWeight s Q * ∑ j : Fin d, N j) := by
      have hNle : ∀ j : Fin d, N j ≤ ∑ k : Fin d, N k := by
        intro j
        exact Finset.single_le_sum (fun k _hk ↦ hNnonneg k) (Finset.mem_univ j)
      have hproduct :
          ∑ i : Fin d, ∑ j : Fin d, |A i j| * N j ≤
            dualBesovMatrixActionSize A * ∑ j : Fin d, N j := by
        calc
          ∑ i : Fin d, ∑ j : Fin d, |A i j| * N j ≤
              ∑ i : Fin d, ∑ j : Fin d,
                |A i j| * (∑ k : Fin d, N k) := by
            exact Finset.sum_le_sum fun i _hi ↦
              Finset.sum_le_sum fun j _hj ↦
                mul_le_mul_of_nonneg_left (hNle j) (abs_nonneg _)
          _ = dualBesovMatrixActionSize A * ∑ j : Fin d, N j := by
            simp only [← Finset.sum_mul, dualBesovMatrixActionSize]
      calc
        cubeBesovScaleWeight s Q *
            ∑ i : Fin d, ∑ j : Fin d, |A i j| * N j ≤
          cubeBesovScaleWeight s Q *
            (dualBesovMatrixActionSize A * ∑ j : Fin d, N j) :=
          mul_le_mul_of_nonneg_left hproduct (cubeBesovScaleWeight_nonneg s Q)
        _ = dualBesovMatrixActionSize A *
            (cubeBesovScaleWeight s Q * ∑ j : Fin d, N j) := by ring

/-- Triangle inequality for the component-sum cube full-dual vector norm. -/
theorem cubeScaleNormalizedDualNegativeBesovVectorNormTwo_add_le
    {d : ℕ} (Q : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (F G : Vec d → Vec d) (hF : MemVectorL2 (cubeSet Q) F)
    (hG : MemVectorL2 (cubeSet Q) G) :
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s
        (fun x ↦ F x + G x) ≤
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F +
        cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s G := by
  have hFc :=
    Book.Ch01.Legacy.component_memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet_ch1
      Q hF
  have hGc :=
    Book.Ch01.Legacy.component_memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet_ch1
      Q hG
  unfold cubeScaleNormalizedDualNegativeBesovVectorNormTwo
  rw [← mul_add, ← Finset.sum_add_distrib]
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i _hi ↦ by
      simpa only [Pi.add_apply] using
        cubeBesovDualFullNorm_add_le_of_memLp_two Q hs
          (fun x ↦ F x i) (fun x ↦ G x i) (hFc i) (hGc i))
    (cubeBesovScaleWeight_nonneg s Q)

end

end HighContrast
end HCPolySupport
