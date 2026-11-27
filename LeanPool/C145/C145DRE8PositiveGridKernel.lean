/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145H2PositiveGrid
public import LeanPool.C145.C145DRE8TensorSpace
public import LeanPool.C145.C145DRE8WeightedKernel

/-! DRE8 Lemma D as actual Euclidean tensor measurement maps.
The domain norm is literal unweighted Frobenius, and the codomain norm is
Euclidean on the full Cartesian grid. Calibration parameters are fixed exactly.
The kernel theorem is proved on the ambient tensor space, hence on source V0
by restriction; no symmetry or ground-zero premise is needed for interpolation. -/

@[expose] public section

noncomputable section
namespace C145DRE8
open C145.H2
open scoped BigOperators
variable {N : ℕ}

/-- The actual calibrated second-transfer difference, linear in the physical
orthonormal tensor; overlap weights occur only inside the measured response. -/
def responseMap (a rates : Fin N → ℝ) (s t : ℝ) : TensorSpace N →ₗ[ℝ] ℝ where
  toFun E := H rates (weightedTensor a (toTensor E)) s t
  map_add' E F := by
    simp [H, weightedTensor, toTensor, mul_add, add_div, Finset.sum_add_distrib]
  map_smul' c E := by
    simp only [H, weightedTensor, toTensor, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    apply Finset.sum_congr rfl; intro k hk
    simp only [RingHom.id_apply]
    ring

@[simp] theorem responseMap_apply (a rates : Fin N → ℝ) (s t : ℝ) (E : TensorSpace N) :
    responseMap a rates s t E = H rates (weightedTensor a (toTensor E)) s t := rfl

/-- The literal `(2N-1)×(2N-1)` sampled actual response operator. -/
def positiveGridMap (a rates : Fin N → ℝ)
    (sNodes tNodes : Fin (2 * N - 1) → ℝ) :
    TensorSpace N →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * N - 1) × Fin (2 * N - 1)) where
  toFun E := WithLp.toLp 2 (fun p => responseMap a rates (sNodes p.1) (tNodes p.2) E)
  map_add' E F := by
    ext p
    exact (responseMap a rates (sNodes p.1) (tNodes p.2)).map_add E F
  map_smul' c E := by
    ext p
    exact (responseMap a rates (sNodes p.1) (tNodes p.2)).map_smul c E

@[simp] theorem positiveGridMap_apply (a rates : Fin N → ℝ)
    (sNodes tNodes : Fin (2 * N - 1) → ℝ) (E : TensorSpace N)
    (p : Fin (2 * N - 1) × Fin (2 * N - 1)) :
    positiveGridMap a rates sNodes tNodes E p =
      H rates (weightedTensor a (toTensor E)) (sNodes p.1) (tNodes p.2) := rfl

/-- The actual all-positive H2 nullspace, rather than a supplied model kernel. -/
def actualPositiveKernel (a rates : Fin N → ℝ) : Submodule ℝ (TensorSpace N) where
  carrier := {E | ∀ s t, 0 < s → 0 < t → responseMap a rates s t E = 0}
  zero_mem' := by intro s t hs ht; exact (responseMap a rates s t).map_zero
  add_mem' := by
    intro E F hE hF s t hs ht
    rw [map_add, hE s t hs ht, hF s t hs ht, add_zero]
  smul_mem' := by
    intro c E hE s t hs ht
    rw [map_smul, hE s t hs ht, smul_zero]

@[simp] theorem mem_actualPositiveKernel (a rates : Fin N → ℝ) (E : TensorSpace N) :
    E ∈ actualPositiveKernel a rates ↔ NullPositive rates (weightedTensor a (toTensor E)) :=
  Iff.rfl

/-- Source Lemma D: *any* two internally distinct positive grids have exactly
the full actual H2 nullspace. Positive rates derive all denominator guards.
No rate distinctness or nonzero overlaps are needed for this lemma itself. -/
theorem ker_positiveGridMap (hN : 0 < N) (a rates : Fin N → ℝ)
    (hRates : ∀ i, 0 < rates i) (sNodes tNodes : Fin (2 * N - 1) → ℝ)
    (hsNodes : Function.Injective sNodes) (htNodes : Function.Injective tNodes)
    (hsPos : ∀ i, 0 < sNodes i) (htPos : ∀ i, 0 < tNodes i) :
    LinearMap.ker (positiveGridMap a rates sNodes tNodes) = actualPositiveKernel a rates := by
  ext E
  rw [LinearMap.mem_ker, mem_actualPositiveKernel,
    ← positive_grid_iff_nullPositive hN rates hRates (weightedTensor a (toTensor E))
      sNodes tNodes hsNodes htNodes hsPos htPos]
  constructor
  · intro h i j
    exact congrArg (fun v => v (i,j)) h
  · intro h
    ext p
    exact h p.1 p.2

/-- In particular the exact kernel identity holds on any chosen linear tensor
space, including the source's fully symmetric ground-zero space V0. -/
theorem ker_positiveGridMap_restrict (hN : 0 < N) (a rates : Fin N → ℝ)
    (hRates : ∀ i, 0 < rates i) (sNodes tNodes : Fin (2 * N - 1) → ℝ)
    (hsNodes : Function.Injective sNodes) (htNodes : Function.Injective tNodes)
    (hsPos : ∀ i, 0 < sNodes i) (htPos : ∀ i, 0 < tNodes i)
    (V : Submodule ℝ (TensorSpace N)) :
    LinearMap.ker ((positiveGridMap a rates sNodes tNodes).comp V.subtype) =
      (actualPositiveKernel a rates).comap V.subtype := by
  rw [LinearMap.ker_comp, ker_positiveGridMap hN a rates hRates sNodes tNodes
    hsNodes htNodes hsPos htPos]

end C145DRE8

end
