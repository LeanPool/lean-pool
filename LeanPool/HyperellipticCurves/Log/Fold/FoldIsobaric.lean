/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.FoldNum
public import LeanPool.HyperellipticCurves.Log.Fold.Isobaric

/-!
# Isobarity of the numerator fold

The isobarity clause of `lem:fold-universal`: along the numerator fold
`ChabautyColeman.foldNum`, the state is isobaric for any weighting in which the
`x`-coordinates have weight `2`, the `y`-coordinates weight `N = 2g+1`, and the generic
curve is isobaric of weight `2N` — *unconditionally*, with no nonvanishing hypotheses
(which is what lets the descent run its valuation analysis before anything is known to be
nonzero). The layer is fully parametric: no universal variable ring is fixed here; the
consumers instantiate `σ` and the weights.

The invariant `ChabautyColeman.IsIsobaricState` carries the denominator weight `ω` with
the component offsets `2g`, `N`, `2g+2` fixed; one step lands at `ω + 4κ` for any step
pair with condition weight `κ` and scalar-numerator weight `κ + 1`
(`ChabautyColeman.IsIsobaricState.step` — the isobaric shadow of the step algebra's
ratio-only structure). The weight recursion is `ChabautyColeman.foldWt`/
`ChabautyColeman.foldCondWt`, and the interpolating base state sits at the weight
`ω₀ = 4m(m-1)` of the squared node denominator
(`ChabautyColeman.isIsobaricState_foldBase`).

## Main statements

* `ChabautyColeman.IsIsobaricState`, `ChabautyColeman.IsIsobaricState.step`: the invariant
  and its preservation.
* `ChabautyColeman.foldWt`, `ChabautyColeman.foldCondWt`: the weight recursion.
* `ChabautyColeman.isIsobaricState_foldNum`: isobarity along the fold.
* `ChabautyColeman.isWeightedHomogeneous_foldCondNum`,
  `ChabautyColeman.isWeightedHomogeneous_foldHNum`: the step pairs are
  weighted-homogeneous of the recursion's weights.
* `ChabautyColeman.isIsobaricState_foldBase`: isobarity of the interpolating base state.
-/

@[expose] public section

open Polynomial MvPolynomial

namespace ChabautyColeman

/-! ### The isobaric state and the step -/

section State

variable {K σ : Type*} [CommRing K] {w : σ → ℤ} {g : ℕ}

/-- **The isobarity invariant of the numerator fold**: the denominator is
weighted-homogeneous of weight `ω` and the three polynomial components are isobaric at
the fixed offsets `2g`, `N = 2g+1`, `2g+2` above it. -/
structure IsIsobaricState (w : σ → ℤ) (g : ℕ) (s : MumfordNum (MvPolynomial σ K))
    (ω : ℤ) : Prop where
  /-- The denominator is weighted-homogeneous of weight `ω`. -/
  den_wt : s.den.IsWeightedHomogeneous w ω
  /-- The scaled support is isobaric of weight `ω + 2g`. -/
  u_iso : IsIsobaric w (ω + 2 * g) s.u
  /-- The scaled square root is isobaric of weight `ω + N`. -/
  v_iso : IsIsobaric w (ω + (2 * g + 1)) s.v
  /-- The scaled cofactor is isobaric of weight `ω + 2g + 2`. -/
  w_iso : IsIsobaric w (ω + 2 * g + 2) s.w

/-- **One numerator step preserves isobarity**: for any step pair with `c` of weight `κ`
and `NH` of weight `κ + 1` (the offset `N - 2g`), the step lands at `ω + 4κ`. -/
theorem IsIsobaricState.step [Nontrivial K] {s : MumfordNum (MvPolynomial σ K)}
    {xP NH c : MvPolynomial σ K} {ω κ : ℤ} (hs : IsIsobaricState w g s ω)
    (hxP : xP.IsWeightedHomogeneous w 2) (hc : c.IsWeightedHomogeneous w κ)
    (hNH : NH.IsWeightedHomogeneous w (κ + 1)) :
    IsIsobaricState w g (s.step xP NH c) (ω + 4 * κ) := by
  have h2 : IsIsobaric w 0 (2 : (MvPolynomial σ K)[X]) := by
    simpa [map_ofNat] using isIsobaric_C (w := w) (isWeightedHomogeneous_C w (2 : K))
  have hCc : IsIsobaric w κ (Polynomial.C c) := isIsobaric_C hc
  have hCNH : IsIsobaric w (κ + 1) (Polynomial.C NH) := isIsobaric_C hNH
  have hCpow : ∀ k : ℕ, IsIsobaric w (k * κ) (Polynomial.C c ^ k) := fun k ↦ by
    rw [← Polynomial.C_pow]
    exact (isIsobaric_C (hc.pow k)).of_weight_eq (by rw [nsmul_eq_mul])
  have hCc2 : IsIsobaric w (2 * κ) (Polynomial.C c ^ 2) := (hCpow 2).of_weight_eq (by norm_num)
  have hCc3 : IsIsobaric w (3 * κ) (Polynomial.C c ^ 3) := (hCpow 3).of_weight_eq (by norm_num)
  have hCc4 : IsIsobaric w (4 * κ) (Polynomial.C c ^ 4) := (hCpow 4).of_weight_eq (by norm_num)
  have hCNH2 : IsIsobaric w (2 * (κ + 1)) (Polynomial.C NH ^ 2) := by
    rw [sq]
    exact (hCNH.mul hCNH).of_weight_eq (by ring)
  have hVc : IsIsobaric w (κ + (ω + (2 * g + 1))) (s.stepVc NH c) := by
    rw [MumfordNum.stepVc_def]
    exact (hCc.mul hs.v_iso).add ((hCNH.mul hs.u_iso).of_weight_eq (by ring))
  have hcof : IsIsobaric w (2 * κ + (ω + 2 * g)) (s.stepCof xP NH c) := by
    rw [MumfordNum.stepCof_def]
    have hnum : IsIsobaric w (2 * κ + (ω + 2 * g) + 2)
        (Polynomial.C c ^ 2 * s.w + 2 * (Polynomial.C c * Polynomial.C NH) * s.v
          + Polynomial.C NH ^ 2 * s.u) :=
      (((hCc2.mul hs.w_iso).of_weight_eq (by ring)).add
        (((h2.mul (hCc.mul hCNH)).mul hs.v_iso).of_weight_eq (by ring))).add
        ((hCNH2.mul hs.u_iso).of_weight_eq (by ring))
    exact (hnum.divByMonic ((isIsobaric_X_sub_C hxP).of_weight_eq (by norm_num))
      (monic_X_sub_C xP) (natDegree_X_sub_C xP)).of_weight_eq (by push_cast; ring)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [MumfordNum.step_den]
    exact (hs.den_wt.mul (hc.pow 4)).of_weight_eq (by rw [nsmul_eq_mul]; norm_num)
  · rw [MumfordNum.step_u]
    exact ((hCc2.mul hcof).neg).of_weight_eq (by ring)
  · rw [MumfordNum.step_v]
    exact (((hCc3.mul hVc).neg).of_weight_eq (by ring)).sub
      (((hCc.mul hCNH).mul hcof).of_weight_eq (by ring))
  · rw [MumfordNum.step_w]
    exact ((((hCc4.mul hs.u_iso).mul (isIsobaric_X_sub_C hxP)).neg).of_weight_eq
        (by ring)).sub
      (((h2.mul (hCc2.mul hCNH)).mul hVc).of_weight_eq (by ring)) |>.sub
      ((hCNH2.mul hcof).of_weight_eq (by ring))

end State

/-! ### The weight recursion and the fold -/

section Fold

variable {K σ : Type*} [CommRing K] {w : σ → ℤ} {g : ℕ}
  {f : (MvPolynomial σ K)[X]} {xs ys : ℕ → MvPolynomial σ K}
  {s₀ : MumfordNum (MvPolynomial σ K)} {ω₀ : ℤ}

/-- **The accumulated denominator weight of the numerator fold**: each step adds four
times the weight of its condition numerator (tangent pair at the doubling step `0`,
generic pair afterwards). -/
def foldWt (g : ℕ) (ω₀ : ℤ) : ℕ → ℤ
  | 0 => ω₀
  | j + 1 => foldWt g ω₀ j
      + 4 * (if j = 0 then ω₀ + 4 * g - 1 else foldWt g ω₀ j + 2 * g)

/-- The weight of the `j`-th step-condition numerator. -/
def foldCondWt (g : ℕ) (ω₀ : ℤ) (j : ℕ) : ℤ :=
  if j = 0 then ω₀ + 4 * g - 1 else foldWt g ω₀ j + 2 * g

@[simp] theorem foldWt_zero : foldWt g ω₀ 0 = ω₀ := rfl

theorem foldWt_succ (j : ℕ) :
    foldWt g ω₀ (j + 1) = foldWt g ω₀ j + 4 * foldCondWt g ω₀ j := rfl

theorem foldCondWt_zero : foldCondWt g ω₀ 0 = ω₀ + 4 * g - 1 := rfl

theorem foldCondWt_succ (j : ℕ) :
    foldCondWt g ω₀ (j + 1) = foldWt g ω₀ (j + 1) + 2 * g :=
  ite_eq_right (Nat.succ_ne_zero j)

/-- The step pair is weighted-homogeneous at the recursion's weights, given that the
stage-`j` state is. -/
private theorem pair_wt_aux (hf : IsIsobaric w (2 * (2 * g + 1)) f)
    (hxs : ∀ j, (xs j).IsWeightedHomogeneous w 2)
    (hys : ∀ j, (ys j).IsWeightedHomogeneous w (2 * g + 1))
    (hbase : IsIsobaricState w g s₀ ω₀) {j : ℕ}
    (h : IsIsobaricState w g (foldNum f xs ys s₀ j) (foldWt g ω₀ j)) :
    (foldHNum f xs ys s₀ j).IsWeightedHomogeneous w (foldCondWt g ω₀ j + 1)
      ∧ (foldCondNum f xs ys s₀ j).IsWeightedHomogeneous w (foldCondWt g ω₀ j) := by
  have h2 : (2 : MvPolynomial σ K).IsWeightedHomogeneous w 0 := by
    simpa [map_ofNat] using isWeightedHomogeneous_C w (2 : K)
  rcases j with - | j
  · rw [foldHNum_zero, foldCondNum_zero, foldCondWt_zero]
    constructor
    · exact ((hbase.den_wt.mul ((hf.derivative).eval (hxs 0))).sub
        (((h2.mul (hys 0)).mul ((hbase.v_iso.derivative).eval (hxs 0))).of_weight_eq
          (by ring))).of_weight_eq (by ring)
    · exact ((h2.mul (hys 0)).mul ((hbase.u_iso.derivative).eval (hxs 0))).of_weight_eq
        (by ring)
  · rw [foldHNum_succ, foldCondNum_succ, foldCondWt_succ]
    constructor
    · exact ((h.den_wt.mul (hys (j + 1))).sub
        ((h.v_iso).eval (hxs (j + 1)))).of_weight_eq (by ring)
    · exact (h.u_iso).eval (hxs (j + 1))

/-- **Isobarity of the numerator fold** (`lem:fold-universal`, isobarity clause): the
state at stage `m` is isobaric at the recursion's weights — unconditionally, with no
nonvanishing hypotheses. -/
theorem isIsobaricState_foldNum [Nontrivial K] (hf : IsIsobaric w (2 * (2 * g + 1)) f)
    (hxs : ∀ j, (xs j).IsWeightedHomogeneous w 2)
    (hys : ∀ j, (ys j).IsWeightedHomogeneous w (2 * g + 1))
    (hbase : IsIsobaricState w g s₀ ω₀) (m : ℕ) :
    IsIsobaricState w g (foldNum f xs ys s₀ m) (foldWt g ω₀ m) := by
  induction m with
  | zero => exact hbase
  | succ m ih =>
    obtain ⟨hH, hc⟩ := pair_wt_aux hf hxs hys hbase ih
    rw [foldNum_succ, foldWt_succ]
    exact ih.step (hxs m) hc hH

/-- **The step-condition numerators are weighted-homogeneous** of the recursion's
weights. -/
theorem isWeightedHomogeneous_foldCondNum [Nontrivial K]
    (hf : IsIsobaric w (2 * (2 * g + 1)) f)
    (hxs : ∀ j, (xs j).IsWeightedHomogeneous w 2)
    (hys : ∀ j, (ys j).IsWeightedHomogeneous w (2 * g + 1))
    (hbase : IsIsobaricState w g s₀ ω₀) (j : ℕ) :
    (foldCondNum f xs ys s₀ j).IsWeightedHomogeneous w (foldCondWt g ω₀ j) :=
  (pair_wt_aux hf hxs hys hbase (isIsobaricState_foldNum hf hxs hys hbase j)).2

/-- The scalar numerators are weighted-homogeneous, one above the condition weight. -/
theorem isWeightedHomogeneous_foldHNum [Nontrivial K]
    (hf : IsIsobaric w (2 * (2 * g + 1)) f)
    (hxs : ∀ j, (xs j).IsWeightedHomogeneous w 2)
    (hys : ∀ j, (ys j).IsWeightedHomogeneous w (2 * g + 1))
    (hbase : IsIsobaricState w g s₀ ω₀) (j : ℕ) :
    (foldHNum f xs ys s₀ j).IsWeightedHomogeneous w (foldCondWt g ω₀ j + 1) :=
  (pair_wt_aux hf hxs hys hbase (isIsobaricState_foldNum hf hxs hys hbase j)).1

end Fold

/-! ### Isobarity of the interpolating base state -/

section Base

variable {K σ : Type*} [CommRing K] {w : σ → ℤ} {m : ℕ}
  {x y : Fin m → MvPolynomial σ K}

theorem isWeightedHomogeneous_nodeDiff (hx : ∀ i, (x i).IsWeightedHomogeneous w 2)
    (i : Fin m) : (nodeDiff x i).IsWeightedHomogeneous w (2 * ((m : ℤ) - 1)) := by
  have h := IsWeightedHomogeneous.prod {i}ᶜ (fun j ↦ x i - x j) (fun _ ↦ 2)
    fun j _ ↦ (hx i).sub (hx j)
  rwa [Finset.sum_const, Finset.card_compl, Finset.card_singleton, Fintype.card_fin,
    show (m - 1) • (2 : ℤ) = 2 * ((m : ℤ) - 1) by
      rw [nsmul_eq_mul, Nat.cast_sub i.pos]
      push_cast
      ring] at h

theorem isWeightedHomogeneous_nodeDen (hx : ∀ i, (x i).IsWeightedHomogeneous w 2) :
    (nodeDen x).IsWeightedHomogeneous w (2 * m * ((m : ℤ) - 1)) := by
  have h := IsWeightedHomogeneous.prod Finset.univ (nodeDiff x)
    (fun _ ↦ 2 * ((m : ℤ) - 1)) fun i _ ↦ isWeightedHomogeneous_nodeDiff hx i
  rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    show m • (2 * ((m : ℤ) - 1)) = 2 * m * ((m : ℤ) - 1) by rw [nsmul_eq_mul]; ring]
    at h

theorem isWeightedHomogeneous_nodeCoDen (hx : ∀ i, (x i).IsWeightedHomogeneous w 2)
    (i : Fin m) :
    (nodeCoDen x i).IsWeightedHomogeneous w (2 * ((m : ℤ) - 1) * ((m : ℤ) - 1)) := by
  have h := IsWeightedHomogeneous.prod {i}ᶜ (nodeDiff x) (fun _ ↦ 2 * ((m : ℤ) - 1))
    fun k _ ↦ isWeightedHomogeneous_nodeDiff hx k
  rwa [Finset.sum_const, Finset.card_compl, Finset.card_singleton, Fintype.card_fin,
    show (m - 1) • (2 * ((m : ℤ) - 1)) = 2 * ((m : ℤ) - 1) * ((m : ℤ) - 1) by
      rw [nsmul_eq_mul, Nat.cast_sub i.pos]
      push_cast
      ring] at h

theorem isIsobaric_tupleU (hx : ∀ i, (x i).IsWeightedHomogeneous w 2) :
    IsIsobaric w (2 * m) (tupleU x) := by
  have h := IsIsobaric.prod Finset.univ (fun i ↦ Polynomial.X - Polynomial.C (x i))
    (fun _ ↦ 2) fun i _ ↦ isIsobaric_X_sub_C (hx i)
  rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    show m • (2 : ℤ) = 2 * m by rw [nsmul_eq_mul]; ring] at h

theorem isIsobaric_nodeLag (hx : ∀ i, (x i).IsWeightedHomogeneous w 2) (i : Fin m) :
    IsIsobaric w (2 * ((m : ℤ) - 1)) (nodeLag x i) := by
  have h := IsIsobaric.prod {i}ᶜ (fun j ↦ Polynomial.X - Polynomial.C (x j))
    (fun _ ↦ 2) fun j _ ↦ isIsobaric_X_sub_C (hx j)
  rwa [Finset.sum_const, Finset.card_compl, Finset.card_singleton, Fintype.card_fin,
    show (m - 1) • (2 : ℤ) = 2 * ((m : ℤ) - 1) by
      rw [nsmul_eq_mul, Nat.cast_sub i.pos]
      push_cast
      ring] at h

/-- The cleared interpolant of values of a fixed weight `ν` is isobaric of weight
`ν` plus the node-denominator weight. -/
theorem isIsobaric_tupleInterp {ν : ℤ} (hx : ∀ i, (x i).IsWeightedHomogeneous w 2)
    {c : Fin m → MvPolynomial σ K} (hc : ∀ i, (c i).IsWeightedHomogeneous w ν) :
    IsIsobaric w (ν + 2 * m * ((m : ℤ) - 1)) (tupleInterp x c) := by
  rw [tupleInterp]
  refine IsIsobaric.sum _ _ fun i _ ↦ ?_
  exact ((isIsobaric_C ((hc i).mul (isWeightedHomogeneous_nodeCoDen hx i))).mul
    (isIsobaric_nodeLag hx i)).of_weight_eq (by ring)

/-- **Isobarity of the interpolating base state** at the weight `ω₀ = 4m(m-1)` of the
squared node denominator. -/
theorem isIsobaricState_foldBase [Nontrivial K] {f : (MvPolynomial σ K)[X]}
    (hf : IsIsobaric w (2 * (2 * m + 1)) f)
    (hx : ∀ i, (x i).IsWeightedHomogeneous w 2)
    (hy : ∀ i, (y i).IsWeightedHomogeneous w (2 * m + 1)) :
    IsIsobaricState w m (foldBase f x y) (4 * m * ((m : ℤ) - 1)) := by
  have hden := isWeightedHomogeneous_nodeDen hx
  have hden2 : (nodeDen x ^ 2).IsWeightedHomogeneous w (4 * m * ((m : ℤ) - 1)) := by
    rw [sq]
    exact (hden.mul hden).of_weight_eq (by ring)
  have hint := isIsobaric_tupleInterp hx hy
  refine ⟨hden2, ?_, ?_, ?_⟩
  · exact (isIsobaric_C hden2).mul (isIsobaric_tupleU hx)
  · exact ((isIsobaric_C hden).mul hint).of_weight_eq (by ring)
  · rw [show (foldBase f x y).w = tupleWNum f x y from rfl, tupleWNum]
    have hnum : IsIsobaric w (2 * (2 * m + 1) + 4 * m * ((m : ℤ) - 1))
        (tupleInterp x y ^ 2 - Polynomial.C (nodeDen x ^ 2) * f) := by
      rw [sq]
      exact ((hint.mul hint).of_weight_eq (by ring)).sub
        (((isIsobaric_C hden2).mul hf).of_weight_eq (by ring))
    exact (hnum.divByMonic (isIsobaric_tupleU hx) (monic_tupleU x)
      (natDegree_tupleU x)).of_weight_eq (by ring)

end Base

end ChabautyColeman

end
