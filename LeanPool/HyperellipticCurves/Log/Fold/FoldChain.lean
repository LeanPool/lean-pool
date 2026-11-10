/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.CuspChain

/-!
# The honest point-by-point fold

This file defines the honest point-by-point fold on Mumford pairs over a curve `y² = f`
(`ChabautyColeman.foldChain`): the `(U, V)`-projection of the cuspidal fold chain
`ChabautyColeman.cuspChain`, freed from the cusp — the point composed at step `j` has
arbitrary `x`-coordinate `xs j`, and `f` is any monic polynomial of odd degree. The
recursion is `g`-free and `y`-free: the `y`-coordinates enter only through the composition
scalars `H`, which are data. This fold is the shared spine of the fold-witness route
(`lem:fold-universal` … `thm:fold-witness`) and of the fold pipeline of `F_τ`
(`ChabautyColeman.foldPipe`).

The invariant `ChabautyColeman.IsFoldState` is the Mumford half of
`ChabautyColeman.IsCuspState`; it propagates along the chain given each step's Mumford
divisibility (`ChabautyColeman.IsFoldState.step`). The canonical scalar values are computed
by `ChabautyColeman.foldGenH` (the tangent value at the initial doubling step, the generic
field-division value afterwards), and the two uniqueness lemmas
(`ChabautyColeman.foldH_eq_of_eval_eq`, `ChabautyColeman.foldH_eq_of_dvd_double`) pin any
scalars satisfying the composition conditions to these values — in particular the abstract
initial scalar of the cusp witness `ChabautyColeman.exists_genCuspFold_witness`.

## Main statements

* `ChabautyColeman.foldChain`, `ChabautyColeman.IsFoldState`: the fold recursion and its
  invariant state; `ChabautyColeman.IsFoldState.step` is the preservation lemma.
* `ChabautyColeman.cuspChain_eq_foldChain`: the Mumford components of the cuspidal fold
  chain are the honest fold at `f = X^(2g+1)` and the squared nodes.
* `ChabautyColeman.foldGenH`: the computed composition scalars.
* `ChabautyColeman.foldH_eq_of_eval_eq`, `ChabautyColeman.foldH_eq_of_dvd_double`:
  the composition conditions determine the scalars.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

/-! ### The fold recursion -/

section Chain

variable {R : Type*} [CommRing R]

/-- **The honest point-by-point fold** on Mumford pairs over `y² = f`: step `j` composes
with the point above `x`-coordinate `xs j` at composition scalar `H j` and reduces
canonically (`ChabautyColeman.cantorReduce` with certificate `-1`, the cofactor's leading
coefficient when `f` is monic of odd degree). The scalars `H` are data; the `y`-coordinates
enter only through them. -/
noncomputable def foldChain (f : R[X]) (xs H : ℕ → R) (U₀ V₀ : R[X]) : ℕ → R[X] × R[X]
  | 0 => (U₀, V₀)
  | j + 1 =>
    let s := foldChain f xs H U₀ V₀ j
    cantorReduce f (s.1 * (X - C (xs j))) (s.2 + C (H j) * s.1) (-1)

variable {f U₀ V₀ : R[X]} {xs H : ℕ → R}

@[simp] theorem foldChain_zero : foldChain f xs H U₀ V₀ 0 = (U₀, V₀) := rfl

theorem foldChain_succ (j : ℕ) :
    foldChain f xs H U₀ V₀ (j + 1)
      = cantorReduce f ((foldChain f xs H U₀ V₀ j).1 * (X - C (xs j)))
          ((foldChain f xs H U₀ V₀ j).2 + C (H j) * (foldChain f xs H U₀ V₀ j).1) (-1) := rfl

/-- The fold chain reads its coordinate and scalar sequences only below the current stage. -/
theorem foldChain_congr {xs' H' : ℕ → R} {m : ℕ} (hx : ∀ i < m, xs i = xs' i)
    (hH : ∀ i < m, H i = H' i) :
    foldChain f xs H U₀ V₀ m = foldChain f xs' H' U₀ V₀ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [foldChain_succ, foldChain_succ,
      ih (fun i hi ↦ hx i (by lia)) fun i hi ↦ hH i (by lia), hx m (by lia), hH m (by lia)]

/-- The fold chain reads its scalar sequence only below the current stage. -/
theorem foldChain_congr_H {H' : ℕ → R} {m : ℕ} (h : ∀ i < m, H i = H' i) :
    foldChain f xs H U₀ V₀ m = foldChain f xs H' U₀ V₀ m :=
  foldChain_congr (fun _ _ ↦ rfl) h

/-- **The Mumford components of the cuspidal fold chain are the honest fold** at
`f = X^(2g+1)` and the squared nodes: the `A`-support is a satellite of the pair. -/
theorem cuspChain_eq_foldChain (g : ℕ) (A₀ : R[X]) (t : ℕ → R) (m : ℕ) :
    ((cuspChain g U₀ V₀ A₀ t H m).1, (cuspChain g U₀ V₀ A₀ t H m).2.1)
      = foldChain (X ^ (2 * g + 1)) (fun j ↦ t j ^ 2) H U₀ V₀ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h1 : (foldChain (X ^ (2 * g + 1)) (fun j ↦ t j ^ 2) H U₀ V₀ m).1
        = (cuspChain g U₀ V₀ A₀ t H m).1 := by rw [← ih]
    have h2 : (foldChain (X ^ (2 * g + 1)) (fun j ↦ t j ^ 2) H U₀ V₀ m).2
        = (cuspChain g U₀ V₀ A₀ t H m).2.1 := by rw [← ih]
    simp only [cuspChain_succ, foldChain_succ, h1, h2]

theorem cuspChain_fst (g : ℕ) (A₀ : R[X]) (t : ℕ → R) (m : ℕ) :
    (cuspChain g U₀ V₀ A₀ t H m).1
      = (foldChain (X ^ (2 * g + 1)) (fun j ↦ t j ^ 2) H U₀ V₀ m).1 := by
  rw [← cuspChain_eq_foldChain g A₀ t m]

theorem cuspChain_snd_fst (g : ℕ) (A₀ : R[X]) (t : ℕ → R) (m : ℕ) :
    (cuspChain g U₀ V₀ A₀ t H m).2.1
      = (foldChain (X ^ (2 * g + 1)) (fun j ↦ t j ^ 2) H U₀ V₀ m).2 := by
  rw [← cuspChain_eq_foldChain g A₀ t m]

end Chain

/-! ### The invariant state and its preservation -/

section State

variable {R : Type*} [CommRing R] {g : ℕ}

/-- **The invariant state of the honest fold**: a reduced Mumford pair on `y² = f` with
monic support of the generic degree `g`. This is the Mumford half of
`ChabautyColeman.IsCuspState`, freed from the cusp. -/
structure IsFoldState (g : ℕ) (f U V : R[X]) : Prop where
  /-- The support is monic. -/
  monicU : U.Monic
  /-- The support has the generic degree `g`. -/
  natDegree_U : U.natDegree = g
  /-- The Mumford divisibility `U ∣ V² - f`. -/
  dvd_sq : U ∣ V ^ 2 - f
  /-- The interpolant is reduced against the support. -/
  degree_V : V.degree < (g : WithBot ℕ)

/-- The Mumford half of a cusp-fold state is an honest fold state on `y² = X^(2g+1)`. -/
theorem IsCuspState.toFoldState {U V A : R[X]} (hs : IsCuspState g U V A) :
    IsFoldState g (X ^ (2 * g + 1)) U V :=
  ⟨hs.monicU, hs.natDegree_U, hs.dvd_sq, hs.degree_V⟩

/-- The degree comparison of a fold state, in the currency of the reduced Mumford
data. -/
theorem IsFoldState.degree_V_lt [Nontrivial R] {f U V : R[X]} (h : IsFoldState g f U V) :
    V.degree < U.degree := by
  have hdeg : U.degree = (g : WithBot ℕ) := by
    rw [degree_eq_natDegree h.monicU.ne_zero, h.natDegree_U]
  exact h.degree_V.trans_eq hdeg.symm

/-- The fold-state invariants from the data of a `τ`-datum: degree comparison against
the support and the cofactor equation for the square root. -/
theorem isFoldState_of_datum [Nontrivial R] {f u v w : R[X]} (hu : u.Monic)
    (hne : u.natDegree = g) (hv : v.degree < u.degree) (hw : v ^ 2 - f = u * w) :
    IsFoldState g f u v :=
  ⟨hu, hne, Dvd.intro w hw.symm,
    hv.trans_eq (by rw [degree_eq_natDegree hu.ne_zero, hne])⟩

/-- The roots of a `τ`-datum's support are curve points. -/
theorem eval_sq_eq_of_root {f u v w : R[X]} (hw : v ^ 2 - f = u * w) {t : R}
    (ht : u.eval t = 0) : v.eval t ^ 2 = f.eval t := by
  have h := congrArg (Polynomial.eval t) hw
  rw [eval_sub, eval_pow, eval_mul, ht, zero_mul] at h
  exact sub_eq_zero.mp h

/-- Fold states are preserved by base change. -/
theorem IsFoldState.map {S : Type*} [CommRing S] [Nontrivial S] (φ : R →+* S)
    {f U V : R[X]} (h : IsFoldState g f U V) :
    IsFoldState g (f.map φ) (U.map φ) (V.map φ) :=
  ⟨h.monicU.map φ, by rw [h.monicU.natDegree_map, h.natDegree_U],
    by simpa using Polynomial.map_dvd φ h.dvd_sq, degree_map_le.trans_lt h.degree_V⟩

/-- **One fold step preserves the invariants**, given the composed pair's Mumford
divisibility (which certifies the composition scalar). -/
theorem IsFoldState.step [Nontrivial R] {f U V : R[X]} {xP H' : R} (hf : f.Monic)
    (hfdeg : f.natDegree = 2 * g + 1) (hs : IsFoldState g f U V)
    (hMum : U * (X - C xP) ∣ (V + C H' * U) ^ 2 - f) :
    IsFoldState g f (cantorReduce f (U * (X - C xP)) (V + C H' * U) (-1)).1
      (cantorReduce f (U * (X - C xP)) (V + C H' * U) (-1)).2 := by
  obtain ⟨hUm, hUdeg, -, hVdeg⟩ := hs
  set Vc := V + C H' * U
  set Uc := U * (X - C xP) with hUcdef
  have hUcm : Uc.Monic := hUm.mul (monic_X_sub_C _)
  have hUcdeg : Uc.natDegree = g + 1 := by
    rw [hUcdef, hUm.natDegree_mul (monic_X_sub_C _), natDegree_X_sub_C, hUdeg]
  have hVcdeg : Vc.natDegree ≤ g := by
    refine (natDegree_add_le _ _).trans
      (max_le (natDegree_le_iff_degree_le.mpr hVdeg.le) ?_)
    exact natDegree_mul_le.trans (by simp [hUdeg])
  set w := cantorCofactor f Uc Vc
  have hw : Vc ^ 2 - f = Uc * w := cantorCofactor_spec f hUcm hMum
  obtain ⟨hwlc, hwdeg⟩ := leadingCoeff_natDegree_cantorCofactor f hf hfdeg hUcm hUcdeg hMum
    (by
      refine degree_le_natDegree.trans_lt ?_
      rw [degree_eq_natDegree hUcm.ne_zero, hUcdeg]
      exact_mod_cast by lia)
    (by lia)
  have hU' : (cantorReduce f Uc Vc (-1)).1 = -w := by
    change C (-1) * w = -w
    rw [map_neg, map_one, neg_one_mul]
  have hU'm : (-w).Monic := by rw [Monic, leadingCoeff_neg, hwlc, neg_neg]
  have hU'deg : (-w).natDegree = g := by
    rw [natDegree_neg]
    lia
  have hV' : (cantorReduce f Uc Vc (-1)).2 = (-Vc) %ₘ (-w) := by
    change (-Vc) %ₘ (C (-1) * w) = (-Vc) %ₘ (-w)
    rw [map_neg, map_one, neg_one_mul]
  rw [hU', hV']
  refine ⟨hU'm, hU'deg, ?_, ?_⟩
  · have h5 : -w ∣ (-Vc) ^ 2 - f := by
      rw [neg_sq, hw]
      exact neg_dvd.mpr (dvd_mul_left w Uc)
    exact dvd_modByMonic_sq_sub_of_dvd f h5
  · have h6 := degree_modByMonic_lt (-Vc) hU'm
    rwa [degree_eq_natDegree hU'm.ne_zero, hU'deg] at h6

end State

/-! ### The computed scalars and their uniqueness -/

section GenH

variable {F : Type*} [Field F]

/-- **The computed fold scalars**: the tangent value at the initial (doubling) step, and
from stage `1` on the field-division value `H_j = (y_j - V_j(x_j))/U_j(x_j)` of the chain
run with the earlier scalars. -/
noncomputable def foldGenH (f : F[X]) (xs ys : ℕ → F) (U₀ V₀ : F[X]) : ℕ → F
  | 0 => (f.derivative.eval (xs 0) - 2 * ys 0 * V₀.derivative.eval (xs 0))
      / (2 * ys 0 * U₀.derivative.eval (xs 0))
  | j + 1 =>
    let s := foldChain f xs (fun i ↦ if _ : i < j + 1 then foldGenH f xs ys U₀ V₀ i else 0)
      U₀ V₀ (j + 1)
    (ys (j + 1) - s.2.eval (xs (j + 1))) / s.1.eval (xs (j + 1))
  decreasing_by assumption

variable {f U₀ V₀ : F[X]} {xs ys : ℕ → F}

theorem foldGenH_zero :
    foldGenH f xs ys U₀ V₀ 0
      = (f.derivative.eval (xs 0) - 2 * ys 0 * V₀.derivative.eval (xs 0))
        / (2 * ys 0 * U₀.derivative.eval (xs 0)) := by
  rw [foldGenH]

/-- The defining property of the computed scalars beyond the initial step, with the
truncation replaced by the full scalar sequence. -/
theorem foldGenH_succ (j : ℕ) :
    foldGenH f xs ys U₀ V₀ (j + 1)
      = (ys (j + 1)
          - (foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ (j + 1)).2.eval (xs (j + 1)))
        / (foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ (j + 1)).1.eval (xs (j + 1)) := by
  rw [foldGenH, show foldChain f xs
      (fun i ↦ if _ : i < j + 1 then foldGenH f xs ys U₀ V₀ i else 0) U₀ V₀ (j + 1)
    = foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ (j + 1) from
    foldChain_congr_H fun i hi ↦ dite_eq_left hi]

/-- **Uniqueness of the composition scalar at a disjoint step**: the value-matching
condition `V_c(x_P) = y_P` pins `H` to the generic field-division value. -/
theorem foldH_eq_of_eval_eq {U V : F[X]} {xP yP H' : F} (hU : U.eval xP ≠ 0)
    (h : (V + C H' * U).eval xP = yP) : H' = (yP - V.eval xP) / U.eval xP := by
  simp only [eval_add, eval_mul, eval_C] at h
  rw [eq_div_iff hU]
  linear_combination h

/-- **Uniqueness of the composition scalar at the doubling step**: when the composed pair
satisfies the Mumford divisibility and the support has the root `x_P` matching the point,
`H` is pinned to the tangent value. -/
theorem foldH_eq_of_dvd_double {U V : F[X]} {xP yP H' : F} (hU0 : U.eval xP = 0)
    (hV0 : V.eval xP = yP) (hy : yP ≠ 0) (h2 : (2 : F) ≠ 0)
    (hU' : U.derivative.eval xP ≠ 0)
    (hMum : U * (X - C xP) ∣ (V + C H' * U) ^ 2 - f) :
    H' = (f.derivative.eval xP - 2 * yP * V.derivative.eval xP)
      / (2 * yP * U.derivative.eval xP) := by
  -- the divisor has a double root at `x_P`, so the derivative also vanishes there
  have hsq : (X - C xP) ^ 2 ∣ U * (X - C xP) := by
    rw [sq]
    exact mul_dvd_mul (dvd_iff_isRoot.mpr hU0) dvd_rfl
  obtain ⟨q, hq⟩ := hsq.trans hMum
  have hder : (((V + C H' * U) ^ 2 - f).derivative).eval xP = 0 := by
    rw [hq]
    simp [derivative_mul, derivative_sq]
  have hval : (((V + C H' * U) ^ 2 - f).derivative).eval xP
      = 2 * yP * (V.derivative.eval xP + H' * U.derivative.eval xP)
        - f.derivative.eval xP := by
    simp only [derivative_sub, derivative_sq, derivative_add, derivative_C_mul, eval_sub,
      eval_mul, eval_add, eval_C, hV0, hU0]
    ring
  rw [hval] at hder
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero h2 hy) hU')]
  linear_combination hder

end GenH

end ChabautyColeman

end
