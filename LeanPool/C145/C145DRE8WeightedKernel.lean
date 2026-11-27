/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145SixFixedProducts
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

/-! DRE8 (6.1): normalize the accepted *weighted* ordinary H2 kernel into
orthonormal modal coordinates. Nonzero calibrated overlaps are explicit.
All moments below are conclusions of actual H2 null data, never premises
in the final response bridge. Rates are the full rates, including decay. -/

@[expose] public section

noncomputable section
namespace C145DRE8
open scoped BigOperators
open C145.H2 C145.ThreePlane
variable {n : ℕ}

/-- Multiply each tensor entry by the product of its three modal overlaps. -/
def weightedTensor (a : Fin n → ℝ) (E : Tensor n) : Tensor n :=
  fun i j k => a i * a j * a k * E i j k

/-- Divide each tensor entry by the product of its three modal overlaps. -/
def unweightedTensor (a : Fin n → ℝ) (T : Tensor n) : Tensor n :=
  fun i j k => T i j k / (a i * a j * a k)

/-- The weighted moment and contraction identities used by the residual-kernel proof. -/
def WeightedMoments (a rates : Fin n → ℝ) (V : Tensor n) : Prop :=
  (∀ p : ℕ, p ≤ 2 → ∀ j k, ∑ i, (a i * rates i ^ p) * V i j k = 0) ∧
  (∀ p : ℕ, p ≤ 2 → ∀ i k, ∑ j, (a j * rates j ^ p) * V i j k = 0) ∧
  (∀ p : ℕ, p ≤ 2 → ∀ i j, ∑ k, (a k * rates k ^ p) * V i j k = 0)

/-- Nonzero calibration makes normalization an actual inverse, including n=0. -/
theorem unweighted_weighted (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) (E : Tensor n) :
    unweightedTensor a (weightedTensor a E) = E := by
  funext i j k
  simp [unweightedTensor, weightedTensor, ha]

/-- Calibration preserves full three-slot symmetry; the weight is a symmetric product. -/
theorem weightedTensor_symmetric (a : Fin n → ℝ) (E : Tensor n)
    (hE : FullSymTensor E) : FullSymTensor (weightedTensor a E) := by
  intro e v
  have hw : a (v (e 1)) * a (v (e 2)) * a (v (e 0)) =
      a (v 1) * a (v 2) * a (v 0) := by
    have h := Fintype.prod_equiv e (fun r => a (v (e r))) (fun r => a (v r))
      (fun r => rfl)
    convert h using 1 <;> simp [Fin.prod_univ_succ] <;> ring
  have hh := hE e v
  change E (v (e 1)) (v (e 2)) (v (e 0)) = E (v 1) (v 2) (v 0) at hh
  change a (v (e 1)) * a (v (e 2)) * a (v (e 0)) *
      E (v (e 1)) (v (e 2)) (v (e 0)) =
    a (v 1) * a (v 2) * a (v 0) * E (v 1) (v 2) (v 0)
  rw [hw, hh]

/-- Literal auxiliary physical V in DRE8 (6.1). -/
def physicalV (a rates : Fin n → ℝ) (R : P3) : Tensor n :=
  unweightedTensor a (gridResidue rates R)

/-- Actual weighted residue factorization becomes E=Xi*V, without changing norms. -/
theorem normalize_residue (a rates : Fin n → ℝ) (ha : ∀ i, a i ≠ 0)
    (E : Tensor n) (R : P3) (hE : weightedTensor a E = Res rates R) :
    E = xiWeighted rates (physicalV a rates R) := by
  funext i j k
  have h := congrFun (congrFun (congrFun hE i) j) k
  rw [res_eq_xiWeighted_gridResidue] at h
  change a i * a j * a k * E i j k =
    MvPolynomial.eval ![-rates k, -rates i, -rates j] Xi * gridResidue rates R i j k at h
  dsimp [xiWeighted, physicalV, unweightedTensor]
  field_simp [ha i, ha j, ha k]
  nlinarith [h]

/-- Divide the accepted quotient moments by the *other* two overlaps. -/
theorem normalize_moments (a rates : Fin n → ℝ) (ha : ∀ i, a i ≠ 0)
    (T : Tensor n) (hT : AllSlotMoments rates T) :
    WeightedMoments a rates (unweightedTensor a T) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro p hp j k
    calc
      _ = (∑ i, rates i ^ p * T i j k) / (a j * a k) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl; intro i hi
        dsimp [unweightedTensor]
        field_simp [ha i, ha j, ha k]
      _ = 0 := by rw [hT.1 p hp]; simp
  · intro p hp i k
    calc
      _ = (∑ j, rates j ^ p * T i j k) / (a i * a k) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl; intro j hj
        dsimp [unweightedTensor]
        field_simp [ha i, ha j, ha k]
      _ = 0 := by rw [hT.2.1 p hp]; simp
  · intro p hp i j
    calc
      _ = (∑ k, rates k ^ p * T i j k) / (a i * a j) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl; intro k hk
        dsimp [unweightedTensor]
        field_simp [ha i, ha j, ha k]
      _ = 0 := by rw [hT.2.2 p hp]; simp

/-- A scalar affine change of rate preserves the three annihilated moments.
No positivity or nonzero width is needed for this algebraic assertion. -/
theorem affine_scalar_moments (a rates f : Fin n → ℝ) (ell w : ℝ)
    (hm : ∀ p : ℕ, p ≤ 2 → ∑ i, (a i * rates i ^ p) * f i = 0)
    (p : ℕ) (hp : p ≤ 2) :
    ∑ i, (a i * ((rates i - ell) / w) ^ p) * f i = 0 := by
  classical
  have h0 := hm 0 (by omega)
  have h1 := hm 1 (by omega)
  have h2 := hm 2 (by omega)
  rcases (show p = 0 ∨ p = 1 ∨ p = 2 by omega) with rfl | rfl | rfl
  · simpa using h0
  · calc
      _ = ((∑ i, (a i * rates i ^ 1) * f i) -
        ell * (∑ i, (a i * rates i ^ 0) * f i)) / w := by
          simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro i hi; ring
      _ = 0 := by rw [h1, h0]; simp
  · calc
      _ = ((∑ i, (a i * rates i ^ 2) * f i) -
        (2 * ell) * (∑ i, (a i * rates i ^ 1) * f i) +
        ell ^ 2 * (∑ i, (a i * rates i ^ 0) * f i)) / w ^ 2 := by
          simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib,
            ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro i hi; ring
      _ = 0 := by rw [h2, h1, h0]; simp

theorem shifted_weighted_moments (a rates : Fin n → ℝ) (V : Tensor n)
    (hV : WeightedMoments a rates V) (ell w : ℝ) :
    WeightedMoments a (fun i => (rates i - ell) / w) V := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp j k
    exact affine_scalar_moments a rates (fun i => V i j k) ell w
      (fun p hp => hV.1 p hp j k) p hp
  · intro p hp i k
    exact affine_scalar_moments a rates (fun j => V i j k) ell w
      (fun p hp => hV.2.1 p hp i k) p hp
  · intro p hp i j
    exact affine_scalar_moments a rates (fun k => V i j k) ell w
      (fun p hp => hV.2.2 p hp i j) p hp

/-- Source-faithful actual H2 bridge. The desired weighted and shifted
moments, and E=Xi*V, are all derived from the accepted ordinary response.
The tensor E is orthonormal; only weightedTensor a E enters H2. -/
theorem actual_H2_physical_kernel (a rates : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hRates : Function.Injective rates)
    (E : Tensor n) (hSym : FullSymTensor E)
    (hData : NullRegular rates (weightedTensor a E)) (ell w : ℝ) :
    ∃ R : P3, SymPoly R ∧ QAdmissible n R ∧
      E = xiWeighted rates (physicalV a rates R) ∧
      WeightedMoments a rates (physicalV a rates R) ∧
      WeightedMoments a (fun i => (rates i - ell) / w) (physicalV a rates R) := by
  obtain ⟨R, hR, _⟩ :=
    (complete_ordinary_H2_receiving_kernel rates hRates (weightedTensor a E)
      (weightedTensor_symmetric a E hSym)).mp hData
  have hm := normalize_moments a rates ha (gridResidue rates R) hR.2.2.2
  exact ⟨R, hR.1, hR.2.1, normalize_residue a rates ha E R hR.2.2.1,
    hm, shifted_weighted_moments a rates _ hm ell w⟩

end C145DRE8

end
