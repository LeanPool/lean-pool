/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145DRE8WeightedKernel
public import LeanPool.C145.C145DRE8PhysicalTensor

/-! Literal cubic cancellation in the orthonormal modal tensor variables,
DRE8 (6.2)-(6.3). No moment of E is assumed: V's moments come from the
actual weighted response bridge in C145DRE8WeightedKernel. -/

@[expose] public section

noncomputable section
namespace C145DRE8
open scoped BigOperators
open C145.H2 C145.ThreePlane
variable {n : ℕ}

/-- Contract the first tensor index against overlaps times a power of the modal rates. -/
def weightedPower (a rates : Fin n → ℝ) (V : Tensor n) (p : ℕ) (j k : Fin n) : ℝ :=
  ∑ i, (a i * rates i ^ p) * V i j k

/-- Expansion of the literal source Xi cubic in its contracted modal index. -/
theorem xi_cubic_first (x y z : ℝ) :
    MvPolynomial.eval ![-z, -x, -y] Xi =
      x ^ 3 - (y + z) * x ^ 2 - (y-z) ^ 2 * x +
        (y ^ 3 + z ^ 3-y ^ 2 * z-z ^ 2 * y) := by
  rw [xi_negative_node_expansion]
  ring

/-- The source's scaled expansion (6.2), with its constant explicitly retained. -/
theorem xi_scaled_cubic_first (theta x y z : ℝ) :
    MvPolynomial.eval ![-(theta + z), -(theta + x), -(theta + y)] Xi =
      x ^ 3 + (theta-y-z) * x ^ 2 -
      (theta ^ 2 + 2 * theta * (y + z) + (y-z) ^ 2) * x +
      (theta + z) ^ 3 + (theta + y) ^ 3-(theta + z) ^ 2 * (theta + y)-
      (theta + y) ^ 2 * (theta + z) + theta ^ 3 -
      ((theta + y) + (theta + z)) * theta ^ 2 - ((theta + y)-(theta + z)) ^ 2 * theta := by
  rw [xi_cubic_first]
  ring

/-- Three derived annihilations leave only the leading rate cubic. -/
theorem cubic_cancellation_rates (a rates : Fin n → ℝ) (V : Tensor n)
    (hm : WeightedMoments a rates V) (j k : Fin n) :
    tensorSlice (xiWeighted rates V) a j k = weightedPower a rates V 3 j k := by
  classical
  have h0 := hm.1 0 (by omega) j k
  have h1 := hm.1 1 (by omega) j k
  have h2 := hm.1 2 (by omega) j k
  calc
    _ = weightedPower a rates V 3 j k -
        (rates j + rates k) * weightedPower a rates V 2 j k -
        (rates j - rates k) ^ 2 * weightedPower a rates V 1 j k +
        (rates j ^ 3 + rates k ^ 3-rates j ^ 2 * rates k-rates k ^ 2 * rates j) *
          weightedPower a rates V 0 j k := by
      simp only [tensorSlice, xiWeighted, weightedPower, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i hi
      rw [xi_cubic_first]
      ring
    _ = _ := by
      change weightedPower a rates V 3 j k - _ *
        (∑ i, (a i * rates i ^ 2) * V i j k) - _ *
        (∑ i, (a i * rates i ^ 1) * V i j k) + _ *
        (∑ i, (a i * rates i ^ 0) * V i j k) = _
      rw [h2, h1, h0]; ring

/-- The lower terms also disappear after shifting and scaling the modal band. -/
theorem cubic_shift (a rates : Fin n → ℝ) (V : Tensor n)
    (hm : WeightedMoments a rates V) (ell w : ℝ) (hw : w ≠ 0) (j k : Fin n) :
    weightedPower a rates V 3 j k =
      w ^ 3 * weightedPower a (fun i => (rates i-ell) / w) V 3 j k := by
  classical
  have h0 := hm.1 0 (by omega) j k
  have h1 := hm.1 1 (by omega) j k
  have h2 := hm.1 2 (by omega) j k
  calc
    _ = w ^ 3 * weightedPower a (fun i => (rates i-ell) / w) V 3 j k +
      3 * ell * weightedPower a rates V 2 j k -
      3 * ell ^ 2 * weightedPower a rates V 1 j k +
      ell ^ 3 * weightedPower a rates V 0 j k := by
        simp only [weightedPower, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i hi
        field_simp [hw]
        ring
    _ = _ := by
      change _ + 3 * ell * (∑ i, (a i * rates i ^ 2) * V i j k) -
        3 * ell ^ 2 * (∑ i, (a i * rates i ^ 1) * V i j k) +
        ell ^ 3 * (∑ i, (a i * rates i ^ 0) * V i j k) = _
      rw [h2,h1,h0]; ring

/-- Exact source (6.3) in actual orthonormal modal coordinates. -/
theorem cubic_cancellation (a rates : Fin n → ℝ) (V : Tensor n)
    (hm : WeightedMoments a rates V) (ell w : ℝ) (hw : w ≠ 0) :
    tensorSlice (xiWeighted rates V) a =
      fun j k => w ^ 3 * tensorSlice V (fun i => a i * ((rates i-ell) / w) ^ 3) j k := by
  funext j k
  rw [cubic_cancellation_rates a rates V hm, cubic_shift a rates V hm ell w hw]
  rfl

/-- Any explicit weighted quadratic may be subtracted from the cubic signature.
This includes the source projection's residual and the Chebyshev residual. -/
theorem cubic_residual_slice (a t : Fin n → ℝ) (V : Tensor n)
    (hm : WeightedMoments a t V) (c0 c1 c2 : ℝ) :
    tensorSlice V (fun i => a i * t i ^ 3) =
    tensorSlice V (fun i => a i * (t i ^ 3-(c0 + c1 * t i + c2 * t i ^ 2))) := by
  classical
  funext j k
  have h0 := hm.1 0 (by omega) j k
  have h1 := hm.1 1 (by omega) j k
  have h2 := hm.1 2 (by omega) j k
  calc
    _ = tensorSlice V (fun i => a i * t i ^ 3) j k -
      c0 * (∑ i, (a i * t i ^ 0) * V i j k) -
      c1 * (∑ i, (a i * t i ^ 1) * V i j k) -
      c2 * (∑ i, (a i * t i ^ 2) * V i j k) := by rw [h0,h1,h2]; ring
    _ = _ := by
      simp only [tensorSlice, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i hi; ring

/-- Actual data yields the cubic matrix identity; no auxiliary moment certificate. -/
theorem actual_H2_cubic_cancellation (a rates : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hRates : Function.Injective rates)
    (E : Tensor n) (hSym : FullSymTensor E)
    (hData : NullRegular rates (weightedTensor a E)) (ell w : ℝ) (hw : w ≠ 0) :
    ∃ R : P3, SymPoly R ∧ QAdmissible n R ∧
      E = xiWeighted rates (physicalV a rates R) ∧
      tensorSlice E a = fun j k => w ^ 3 *
        tensorSlice (physicalV a rates R) (fun i => a i * ((rates i-ell) / w) ^ 3) j k := by
  obtain ⟨R,hR,hAdm,hE,hm,_⟩ := actual_H2_physical_kernel a rates ha hRates E hSym hData ell w
  exact ⟨R,hR,hAdm,hE,by rw [hE]; exact cubic_cancellation a rates _ hm ell w hw⟩

end C145DRE8

end
