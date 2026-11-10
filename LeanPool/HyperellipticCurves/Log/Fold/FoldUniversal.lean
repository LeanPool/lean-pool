/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.FoldIsobaric

/-!
# The universal numerator instance and its cuspidal specialization

The universal-polynomial content of `lem:fold-universal`: the numerator fold
(`ChabautyColeman.foldNum`) is instantiated once and for all over the polynomial ring in
the coordinate variables `x_i`, `y_i` (`i < g`) and the generic curve coefficients `a_r`
(`r < N`) — the three summands of the finite variable type `Fin g ⊕ Fin g ⊕ Fin (2g+1)`,
whose finiteness is what keeps the descent's valuation windows free of variable-support
side conditions. This gives the universal step-condition numerators
`ChabautyColeman.univCondNum` — the `𝒩_q` of the blueprint for the condition quantities.
They are weighted-homogeneous for the weights `x_i ↦ 2`, `y_i ↦ N = 2g+1`,
`a_r ↦ 2(N-r)` (`ChabautyColeman.univWt`); the second phase of the `2g`-step fold
revisits the same coordinate pairs in reverse order with negated `y`
(`ChabautyColeman.univXs`/`ChabautyColeman.univYs`, matching the cuspidal node sequence
`ChabautyColeman.foldNodes`; stages the fold never reaches are set to `0`).

The cuspidal specialization `ChabautyColeman.cuspSpec` sends `x_i ↦ t_i²`, `y_i ↦ t_i^N`,
`a_r ↦ 0`; it turns any weighted-homogeneous polynomial into a homogeneous one of the
same degree (`ChabautyColeman.isWeightedHomogeneous_aeval_cuspSpec`, one application of
the transport lemma `MvPolynomial.IsWeightedHomogeneous.aeval`). In particular the image
`ChabautyColeman.cuspNum` of a universal condition numerator — the `P_q` of the blueprint
— is homogeneous of degree its isobaric weight
(`ChabautyColeman.isWeightedHomogeneous_cuspNum`), and equals the numerator fold of the
cuspidal inputs themselves (`ChabautyColeman.cuspNum_eq_foldCondNum`), which ties it to
the cuspidal chain witness.

## Main definitions

* `ChabautyColeman.univWt`: the universal weights.
* `ChabautyColeman.univF`, `ChabautyColeman.univXs`, `ChabautyColeman.univYs`,
  `ChabautyColeman.univBase`: the universal inputs of the fold.
* `ChabautyColeman.univCondNum`: the universal step-condition numerators `𝒩_q`.
* `ChabautyColeman.cuspSpec`, `ChabautyColeman.cuspNum`: the cuspidal specialization and
  the cuspidal numerators `P_q`.

## Main statements

* `ChabautyColeman.isWeightedHomogeneous_univCondNum`: isobarity of the `𝒩_q`.
* `ChabautyColeman.isWeightedHomogeneous_aeval_cuspSpec`,
  `ChabautyColeman.isWeightedHomogeneous_cuspNum`: the specialization clause of
  `lem:fold-universal` — each `P_q` is homogeneous of degree the isobaric weight of
  `𝒩_q`.
* `ChabautyColeman.cuspNum_eq_foldCondNum`: `P_q` is the numerator fold of the cuspidal
  inputs.
-/

@[expose] public section

open Polynomial MvPolynomial

namespace ChabautyColeman

/-! ### The universal instance -/

/-- **The universal weights of the fold** (`lem:fold-universal`): the `x`-variables (left
summand) carry weight `2`, the `y`-variables (middle) weight `N = 2g+1`, and the generic
curve coefficients `a_r` (right) weight `2(N-r)`. -/
def univWt (g : ℕ) : Fin g ⊕ Fin g ⊕ Fin (2 * g + 1) → ℤ :=
  Sum.elim (fun _ ↦ 2) <| Sum.elim (fun _ ↦ 2 * g + 1) fun r ↦ 2 * (2 * g + 1 - r)

@[simp] theorem univWt_inl (g : ℕ) (i : Fin g) : univWt g (.inl i) = 2 := rfl

@[simp] theorem univWt_inr_inl (g : ℕ) (i : Fin g) :
    univWt g (.inr (.inl i)) = 2 * g + 1 := rfl

@[simp] theorem univWt_inr_inr (g : ℕ) (r : Fin (2 * g + 1)) :
    univWt g (.inr (.inr r)) = 2 * (2 * g + 1 - (r : ℤ)) := rfl

/-- **The generic odd-degree curve polynomial**: `X^N + ∑ a_r X^r` with the coefficients
`a_r` as variables. -/
noncomputable def univF (K : Type*) [CommRing K] (g : ℕ) :
    (MvPolynomial (Fin g ⊕ Fin g ⊕ Fin (2 * g + 1)) K)[X] :=
  Polynomial.X ^ (2 * g + 1)
    + ∑ r : Fin (2 * g + 1), Polynomial.C (X (.inr (.inr r))) * Polynomial.X ^ (r : ℕ)

/-- **The universal `x`-coordinate sequence of the `2g`-step fold**: the second phase
revisits the coordinates of the first in reverse order (the fold adds the conjugate
points, last added first); stages the fold never reaches are set to `0`. -/
noncomputable def univXs (K : Type*) [CommRing K] (g j : ℕ) :
    MvPolynomial (Fin g ⊕ Fin g ⊕ Fin (2 * g + 1)) K :=
  if h : j < g then X (.inl ⟨j, h⟩)
  else if h' : j - g < g then X (.inl (Fin.rev ⟨j - g, h'⟩)) else 0

/-- **The universal `y`-coordinate sequence**: the second phase negates the first, in
reverse order. -/
noncomputable def univYs (K : Type*) [CommRing K] (g j : ℕ) :
    MvPolynomial (Fin g ⊕ Fin g ⊕ Fin (2 * g + 1)) K :=
  if h : j < g then X (.inr (.inl ⟨j, h⟩))
  else if h' : j - g < g then -X (.inr (.inl (Fin.rev ⟨j - g, h'⟩))) else 0

/-- **The universal base state**: the scaled interpolating Mumford datum through the `g`
generic points. -/
noncomputable def univBase (K : Type*) [CommRing K] (g : ℕ) :
    MumfordNum (MvPolynomial (Fin g ⊕ Fin g ⊕ Fin (2 * g + 1)) K) :=
  foldBase (univF K g) (fun i ↦ X (.inl i)) fun i ↦ X (.inr (.inl i))

/-- **The universal step-condition numerators** — the `𝒩_q` of `lem:fold-universal` for
the condition quantities: the numerator fold at the universal inputs. -/
noncomputable def univCondNum (K : Type*) [CommRing K] (g j : ℕ) :
    MvPolynomial (Fin g ⊕ Fin g ⊕ Fin (2 * g + 1)) K :=
  foldCondNum (univF K g) (univXs K g) (univYs K g) (univBase K g) j

/-! ### Isobarity of the universal instance -/

variable {K : Type*} [CommRing K] {g : ℕ}

theorem isIsobaric_univF : IsIsobaric (univWt g) (2 * (2 * g + 1)) (univF K g) := by
  rw [univF]
  refine ((isIsobaric_X_pow (2 * g + 1)).of_weight_eq (by push_cast; ring)).add
    (IsIsobaric.sum _ _ fun r _ ↦ ?_)
  have hφ : (X (.inr (.inr r)) : MvPolynomial (Fin g ⊕ Fin g ⊕ Fin (2 * g + 1)) K)
      |>.IsWeightedHomogeneous (univWt g) (2 * (2 * g + 1 - (r : ℤ))) :=
    isWeightedHomogeneous_X ..
  exact ((isIsobaric_C hφ).mul (isIsobaric_X_pow (r : ℕ))).of_weight_eq (by ring)

theorem isWeightedHomogeneous_univXs (j : ℕ) :
    (univXs K g j).IsWeightedHomogeneous (univWt g) 2 := by
  rw [univXs]
  split_ifs
  · exact isWeightedHomogeneous_X ..
  · exact isWeightedHomogeneous_X ..
  · exact isWeightedHomogeneous_zero _ _ _

theorem isWeightedHomogeneous_univYs (j : ℕ) :
    (univYs K g j).IsWeightedHomogeneous (univWt g) (2 * g + 1) := by
  rw [univYs]
  split_ifs
  · exact isWeightedHomogeneous_X ..
  · exact (isWeightedHomogeneous_X ..).neg
  · exact isWeightedHomogeneous_zero _ _ _

theorem isIsobaricState_univBase [IsDomain K] :
    IsIsobaricState (univWt g) g (univBase K g) (4 * g * ((g : ℤ) - 1)) :=
  isIsobaricState_foldBase isIsobaric_univF (fun _ ↦ isWeightedHomogeneous_X ..)
    fun _ ↦ isWeightedHomogeneous_X ..

/-- **Isobarity of the universal step-condition numerators** (`lem:fold-universal`): each
`𝒩_q` is weighted-homogeneous of the weight computed by the recursion. -/
theorem isWeightedHomogeneous_univCondNum [IsDomain K] (j : ℕ) :
    (univCondNum K g j).IsWeightedHomogeneous (univWt g)
      (foldCondWt g (4 * g * ((g : ℤ) - 1)) j) :=
  isWeightedHomogeneous_foldCondNum isIsobaric_univF isWeightedHomogeneous_univXs
    isWeightedHomogeneous_univYs isIsobaricState_univBase j

/-! ### The cuspidal specialization -/

/-- **The cuspidal specialization** of `lem:fold-universal`: `x_i ↦ t_i²`, `y_i ↦ t_i^N`,
`a_r ↦ 0`. -/
noncomputable def cuspSpec (K : Type*) [CommRing K] (g : ℕ) :
    Fin g ⊕ Fin g ⊕ Fin (2 * g + 1) → MvPolynomial (Fin g) K :=
  Sum.elim (fun i ↦ X i ^ 2) <| Sum.elim (fun i ↦ X i ^ (2 * g + 1)) fun _ ↦ 0

/-- **The cuspidal specialization preserves the isobaric weight as homogeneity degree**:
the image of any weighted-homogeneous polynomial is homogeneous of the same degree (one
application of the transport lemma `MvPolynomial.IsWeightedHomogeneous.aeval`). -/
theorem isWeightedHomogeneous_aeval_cuspSpec {d : ℤ}
    {N : MvPolynomial (Fin g ⊕ Fin g ⊕ Fin (2 * g + 1)) K}
    (hN : N.IsWeightedHomogeneous (univWt g) d) :
    (MvPolynomial.aeval (cuspSpec K g) N).IsWeightedHomogeneous (fun _ ↦ 1) d := by
  refine hN.aeval fun s ↦ ?_
  rcases s with i | i | r
  · exact ((isWeightedHomogeneous_X ..).pow 2).of_weight_eq (by norm_num)
  · exact ((isWeightedHomogeneous_X ..).pow (2 * g + 1)).of_weight_eq
      (by rw [univWt_inr_inl, nsmul_eq_mul]; push_cast; ring)
  · exact isWeightedHomogeneous_zero _ _ _

/-- **The cuspidal numerators** — the `P_q` of `lem:fold-universal` for the condition
quantities: the cuspidal specialization of the universal step-condition numerators. -/
noncomputable def cuspNum (K : Type*) [CommRing K] (g j : ℕ) : MvPolynomial (Fin g) K :=
  MvPolynomial.aeval (cuspSpec K g) (univCondNum K g j)

/-- **The cuspidal numerators are homogeneous of the isobaric weight**
(`lem:fold-universal`, specialization clause). -/
theorem isWeightedHomogeneous_cuspNum [IsDomain K] (j : ℕ) :
    (cuspNum K g j).IsWeightedHomogeneous (fun _ ↦ 1)
      (foldCondWt g (4 * g * ((g : ℤ) - 1)) j) :=
  isWeightedHomogeneous_aeval_cuspSpec (isWeightedHomogeneous_univCondNum j)

/-- The cuspidal numerators are the numerator fold of the cuspidal inputs themselves
(naturality of the fold under the cuspidal specialization). -/
theorem cuspNum_eq_foldCondNum (j : ℕ) :
    cuspNum K g j
      = foldCondNum (Polynomial.X ^ (2 * g + 1))
          (fun j ↦ if h : j < g then X (⟨j, h⟩ : Fin g) ^ 2
            else if h' : j - g < g then X (Fin.rev ⟨j - g, h'⟩ : Fin g) ^ 2 else 0)
          (fun j ↦ if h : j < g then X (⟨j, h⟩ : Fin g) ^ (2 * g + 1)
            else if h' : j - g < g then -X (Fin.rev ⟨j - g, h'⟩ : Fin g) ^ (2 * g + 1)
            else 0)
          (foldBase (Polynomial.X ^ (2 * g + 1)) (fun i ↦ X i ^ 2)
            fun i ↦ X i ^ (2 * g + 1)) j := by
  set φ : MvPolynomial (Fin g ⊕ Fin g ⊕ Fin (2 * g + 1)) K →+* MvPolynomial (Fin g) K :=
    (MvPolynomial.aeval (cuspSpec K g)).toRingHom with hφdef
  have hF : (univF K g).map φ = Polynomial.X ^ (2 * g + 1) := by
    rw [univF, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      Finset.sum_eq_zero fun r _ ↦ by simp [hφdef, cuspSpec], add_zero]
  have hX : (fun i ↦ φ (univXs K g i))
      = fun j ↦ if h : j < g then (X (⟨j, h⟩ : Fin g) : MvPolynomial (Fin g) K) ^ 2
          else if h' : j - g < g then X (Fin.rev ⟨j - g, h'⟩ : Fin g) ^ 2 else 0 := by
    funext i
    rw [univXs]
    split_ifs <;> simp [hφdef, cuspSpec]
  have hY : (fun i ↦ φ (univYs K g i))
      = fun j ↦ if h : j < g
          then (X (⟨j, h⟩ : Fin g) : MvPolynomial (Fin g) K) ^ (2 * g + 1)
          else if h' : j - g < g then -X (Fin.rev ⟨j - g, h'⟩ : Fin g) ^ (2 * g + 1)
          else 0 := by
    funext i
    rw [univYs]
    split_ifs <;> simp [hφdef, cuspSpec]
  have hB : (univBase K g).map φ
      = foldBase (Polynomial.X ^ (2 * g + 1)) (fun i ↦ X i ^ 2)
        fun i ↦ X i ^ (2 * g + 1) := by
    rw [univBase, map_foldBase, hF]
    congr 1 <;> funext i <;> simp [hφdef, cuspSpec]
  have h := map_foldCondNum (f := univF K g) (xs := univXs K g) (ys := univYs K g)
    (s₀ := univBase K g) φ j
  rwa [hF, hX, hY, hB] at h

end ChabautyColeman

end
