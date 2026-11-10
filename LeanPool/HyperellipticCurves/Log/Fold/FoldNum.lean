/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Witness.TupleDatum

/-!
# The numerator fold recursion

This file implements the fraction-free numerator form of the point-by-point fold
(`lem:fold-universal`): a state `ChabautyColeman.MumfordNum` carries the denominator-scaled
Mumford pair together with its cofactor `w = (v² - f)/u` and the common scalar denominator,
and one step (`ChabautyColeman.MumfordNum.step`) is pure ring arithmetic — the only
division is the exact synthetic division by the monic `X - x_P`, so the recursion
`ChabautyColeman.foldNum` is total over every commutative ring and commutes with ring
homomorphisms (`ChabautyColeman.map_foldNum`). All components are rescaled to the common
denominator `den·c⁴` per step (coarse bookkeeping; the sharp per-component law is
deliberately not tracked).

The step pair `(NH, c)` — the numerator of the composition scalar `H = NH/c` and the
step-condition numerator — is given by the tangent formulas at the initial doubling step
`j = 0` and by the generic formulas `(den·y_j - v(x_j), u(x_j))` afterwards
(`ChabautyColeman.foldHNum`, `ChabautyColeman.foldCondNum`); the base state is the scaled
interpolating Mumford datum `τ` (`ChabautyColeman.foldBase`). Over a field, the states are
the denominator-scaled values of the honest fold `ChabautyColeman.foldChain`; this
correctness identification lives in `LeanPool.HyperellipticCurves.Log.Fold.FoldCorrect`.

## Main definitions

* `ChabautyColeman.MumfordNum`: the scaled state, with `map` and `step`.
* `ChabautyColeman.foldNum`: the numerator fold recursion.
* `ChabautyColeman.foldHNum`, `ChabautyColeman.foldCondNum`: the step pairs; the latter
  are the step-condition numerators, the core conditions of the fold-witness route.
* `ChabautyColeman.foldBase`: the scaled interpolating base state.

## Main statements

* `ChabautyColeman.foldNum_succ`: the recursion advances by one `step` at the current pair.
* `ChabautyColeman.den_foldNum`: the accumulated denominator is the base denominator times
  the fourth powers of the earlier step-condition numerators.
* `ChabautyColeman.map_foldNum`, `ChabautyColeman.map_foldHNum`,
  `ChabautyColeman.map_foldCondNum`, `ChabautyColeman.map_foldBase`: naturality.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

/-! ### The scaled state -/

/-- **A denominator-scaled Mumford triple with cofactor**: represents the Mumford datum
`(u/den, v/den)` on `y² = f` together with its cofactor `w/den = ((v/den)² - f)/(u/den)`,
all three polynomial components at the common scalar denominator `den`. The recursion
`ChabautyColeman.foldNum` advances such states by pure ring arithmetic; the represented
values are recovered over a field by `LeanPool.HyperellipticCurves.Log.Fold.FoldCorrect`. -/
@[ext]
structure MumfordNum (R : Type*) [CommRing R] where
  /-- The scaled support polynomial (`den` times the monic `u`). -/
  u : R[X]
  /-- The scaled square-root polynomial (`den` times `v`). -/
  v : R[X]
  /-- The scaled cofactor (`den` times `(v² - f)/u`). -/
  w : R[X]
  /-- The common scalar denominator. -/
  den : R

namespace MumfordNum

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- Apply a ring homomorphism to all components. -/
noncomputable def map (φ : R →+* S) (s : MumfordNum R) : MumfordNum S :=
  ⟨s.u.map φ, s.v.map φ, s.w.map φ, φ s.den⟩

variable (φ : R →+* S) (s : MumfordNum R)

@[simp] theorem map_u : (s.map φ).u = s.u.map φ := rfl

@[simp] theorem map_v : (s.map φ).v = s.v.map φ := rfl

@[simp] theorem map_w : (s.map φ).w = s.w.map φ := rfl

@[simp] theorem map_den : (s.map φ).den = φ s.den := rfl

@[simp] theorem map_id : s.map (RingHom.id R) = s := by ext <;> simp

theorem map_map (ψ : S →+* T) : (s.map φ).map ψ = s.map (ψ.comp φ) := by
  ext <;> simp [Polynomial.map_map]

/-! ### The numerator step -/

variable {xP NH c : R}

/-- The composed scaled square root of a fold step: `c·v + NH·u`, at scale `den·c`. -/
noncomputable def stepVc (s : MumfordNum R) (NH c : R) : R[X] := C c * s.v + C NH * s.u

theorem stepVc_def (s : MumfordNum R) (NH c : R) : s.stepVc NH c = C c * s.v + C NH * s.u := rfl

/-- The scaled composed cofactor of a fold step, divided exactly by `X - x_P`
(at scale `den·c²`; the division is exact on the universal curve). -/
noncomputable def stepCof (s : MumfordNum R) (xP NH c : R) : R[X] :=
  (C c ^ 2 * s.w + 2 * (C c * C NH) * s.v + C NH ^ 2 * s.u) /ₘ (X - C xP)

theorem stepCof_def (s : MumfordNum R) (xP NH c : R) :
    s.stepCof xP NH c
      = (C c ^ 2 * s.w + 2 * (C c * C NH) * s.v + C NH ^ 2 * s.u) /ₘ (X - C xP) :=
  rfl

/-- **One numerator fold step** at the point above `x_P`, at step pair `(NH, c)` (the
composition scalar is `NH/c`): the fraction-free single-point Cantor addition with
cofactor bookkeeping, all components rescaled to the common denominator `den·c⁴`. -/
noncomputable def step (s : MumfordNum R) (xP NH c : R) : MumfordNum R where
  u := -(C c ^ 2 * s.stepCof xP NH c)
  v := -(C c ^ 3 * s.stepVc NH c) - C c * C NH * s.stepCof xP NH c
  w := -(C c ^ 4 * s.u * (X - C xP)) - 2 * (C c ^ 2 * C NH) * s.stepVc NH c
    - C NH ^ 2 * s.stepCof xP NH c
  den := s.den * c ^ 4

theorem step_u : (s.step xP NH c).u = -(C c ^ 2 * s.stepCof xP NH c) := rfl

theorem step_v :
    (s.step xP NH c).v = -(C c ^ 3 * s.stepVc NH c) - C c * C NH * s.stepCof xP NH c := rfl

theorem step_w :
    (s.step xP NH c).w = -(C c ^ 4 * s.u * (X - C xP)) - 2 * (C c ^ 2 * C NH) * s.stepVc NH c
      - C NH ^ 2 * s.stepCof xP NH c := rfl

@[simp] theorem step_den : (s.step xP NH c).den = s.den * c ^ 4 := rfl

theorem map_stepVc : (s.stepVc NH c).map φ = (s.map φ).stepVc (φ NH) (φ c) := by simp [stepVc]

theorem map_stepCof : (s.stepCof xP NH c).map φ = (s.map φ).stepCof (φ xP) (φ NH) (φ c) := by
  rw [stepCof, map_divByMonic φ (monic_X_sub_C xP), stepCof]
  simp

theorem map_step : (s.step xP NH c).map φ = (s.map φ).step (φ xP) (φ NH) (φ c) := by
  ext <;> simp [step_u, step_v, step_w, ← map_stepVc, ← map_stepCof]

end MumfordNum

/-! ### The fold recursion -/

section Fold

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **The numerator fold recursion**: starting from a scaled base state, step `j` performs
the fraction-free single-point Cantor addition `ChabautyColeman.MumfordNum.step` at the
point `(xs j, ys j)`, with the step pair given by the tangent formulas at the initial
doubling step `j = 0` (the base support contains the first point) and by the generic
formulas afterwards. Everything is total ring arithmetic; over a field the states are the
denominator-scaled honest fold (`LeanPool.HyperellipticCurves.Log.Fold.FoldCorrect`). -/
noncomputable def foldNum (f : R[X]) (xs ys : ℕ → R) (s₀ : MumfordNum R) : ℕ → MumfordNum R
  | 0 => s₀
  | j + 1 =>
    let s := foldNum f xs ys s₀ j
    if j = 0 then
      s.step (xs 0) (s.den * f.derivative.eval (xs 0) - 2 * ys 0 * s.v.derivative.eval (xs 0))
        (2 * ys 0 * s.u.derivative.eval (xs 0))
    else s.step (xs j) (s.den * ys j - s.v.eval (xs j)) (s.u.eval (xs j))

/-- The scalar numerator of the composition scalar at stage `j`: the tangent numerator at
the doubling step `j = 0`, the generic numerator `den·y_j - v(x_j)` afterwards. -/
noncomputable def foldHNum (f : R[X]) (xs ys : ℕ → R) (s₀ : MumfordNum R) (j : ℕ) : R :=
  if j = 0 then s₀.den * f.derivative.eval (xs 0) - 2 * ys 0 * s₀.v.derivative.eval (xs 0)
  else (foldNum f xs ys s₀ j).den * ys j - (foldNum f xs ys s₀ j).v.eval (xs j)

/-- **The step-condition numerators of the fold**: the scaled doubling condition
`2·y₀·u₀'(x₀)` at step `0` and the scaled disjointness values `u_j(x_j)` afterwards —
the core conditions of the fold-witness route. -/
noncomputable def foldCondNum (f : R[X]) (xs ys : ℕ → R) (s₀ : MumfordNum R) (j : ℕ) : R :=
  if j = 0 then 2 * ys 0 * s₀.u.derivative.eval (xs 0)
  else (foldNum f xs ys s₀ j).u.eval (xs j)

variable {f : R[X]} {xs ys : ℕ → R} {s₀ : MumfordNum R}

@[simp] theorem foldNum_zero : foldNum f xs ys s₀ 0 = s₀ := rfl

theorem foldHNum_zero :
    foldHNum f xs ys s₀ 0
      = s₀.den * f.derivative.eval (xs 0) - 2 * ys 0 * s₀.v.derivative.eval (xs 0) := rfl

theorem foldHNum_succ (j : ℕ) :
    foldHNum f xs ys s₀ (j + 1)
      = (foldNum f xs ys s₀ (j + 1)).den * ys (j + 1)
        - (foldNum f xs ys s₀ (j + 1)).v.eval (xs (j + 1)) :=
  ite_eq_right (Nat.succ_ne_zero j)

theorem foldCondNum_zero :
    foldCondNum f xs ys s₀ 0 = 2 * ys 0 * s₀.u.derivative.eval (xs 0) := rfl

theorem foldCondNum_succ (j : ℕ) :
    foldCondNum f xs ys s₀ (j + 1)
      = (foldNum f xs ys s₀ (j + 1)).u.eval (xs (j + 1)) :=
  ite_eq_right (Nat.succ_ne_zero j)

/-- The fold recursion advances by one `ChabautyColeman.MumfordNum.step` at the current
step pair, uniformly in the stage. -/
theorem foldNum_succ (j : ℕ) :
    foldNum f xs ys s₀ (j + 1) = (foldNum f xs ys s₀ j).step (xs j)
      (foldHNum f xs ys s₀ j) (foldCondNum f xs ys s₀ j) := by
  rcases j with _ | j
  · rfl
  · rw [foldNum, foldHNum, foldCondNum]
    simp only [ite_eq_right (Nat.succ_ne_zero j)]

/-- The accumulated denominator of the fold: the base denominator times the fourth powers
of all earlier step-condition numerators. -/
theorem den_foldNum (m : ℕ) :
    (foldNum f xs ys s₀ m).den
      = s₀.den * ∏ i ∈ Finset.range m, foldCondNum f xs ys s₀ i ^ 4 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [foldNum_succ, MumfordNum.step_den, ih, Finset.prod_range_succ, mul_assoc]

/-- The step pair reads only the current coordinates, given that the stage-`j` state
agrees. -/
private theorem pair_congr_aux {xs' ys' : ℕ → R} {j : ℕ} (hx : ∀ i ≤ j, xs i = xs' i)
    (hy : ∀ i ≤ j, ys i = ys' i)
    (h : foldNum f xs ys s₀ j = foldNum f xs' ys' s₀ j) :
    foldHNum f xs ys s₀ j = foldHNum f xs' ys' s₀ j
      ∧ foldCondNum f xs ys s₀ j = foldCondNum f xs' ys' s₀ j := by
  rcases j with _ | j
  · rw [foldHNum_zero, foldHNum_zero, foldCondNum_zero, foldCondNum_zero, hx 0 le_rfl,
      hy 0 le_rfl]
    exact ⟨rfl, rfl⟩
  · rw [foldHNum_succ, foldHNum_succ, foldCondNum_succ, foldCondNum_succ, h,
      hx (j + 1) le_rfl, hy (j + 1) le_rfl]
    exact ⟨rfl, rfl⟩

/-- The fold reads its coordinate sequences only below the current stage. -/
theorem foldNum_congr {xs' ys' : ℕ → R} {m : ℕ} (hx : ∀ i < m, xs i = xs' i)
    (hy : ∀ i < m, ys i = ys' i) :
    foldNum f xs ys s₀ m = foldNum f xs' ys' s₀ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h := ih (fun i hi ↦ hx i (by lia)) fun i hi ↦ hy i (by lia)
    obtain ⟨hH, hc⟩ := pair_congr_aux (fun i hi ↦ hx i (by lia)) (fun i hi ↦ hy i (by lia)) h
    rw [foldNum_succ, foldNum_succ, h, hH, hc, hx m (by lia)]

/-- The step-condition numerators read the coordinate sequences only up to their stage. -/
theorem foldCondNum_congr {xs' ys' : ℕ → R} {j : ℕ} (hx : ∀ i ≤ j, xs i = xs' i)
    (hy : ∀ i ≤ j, ys i = ys' i) :
    foldCondNum f xs ys s₀ j = foldCondNum f xs' ys' s₀ j :=
  (pair_congr_aux hx hy
    (foldNum_congr (fun i hi ↦ hx i (by lia)) fun i hi ↦ hy i (by lia))).2

/-- The scalar numerators read the coordinate sequences only up to their stage. -/
theorem foldHNum_congr {xs' ys' : ℕ → R} {j : ℕ} (hx : ∀ i ≤ j, xs i = xs' i)
    (hy : ∀ i ≤ j, ys i = ys' i) :
    foldHNum f xs ys s₀ j = foldHNum f xs' ys' s₀ j :=
  (pair_congr_aux hx hy
    (foldNum_congr (fun i hi ↦ hx i (by lia)) fun i hi ↦ hy i (by lia))).1

end Fold

/-! ### The interpolating base state -/

section Base

variable {R S : Type*} [CommRing R] [CommRing S] {m : ℕ}

/-- **The interpolating base state `τ` of the fold**: the scaled Mumford datum through the
`m` points `(x i, y i)`, at the common denominator `nodeDen x ^ 2` (the square of the node
denominator clears both the Lagrange interpolant and its cofactor). -/
noncomputable def foldBase (f : R[X]) (x y : Fin m → R) : MumfordNum R where
  u := C (nodeDen x ^ 2) * tupleU x
  v := C (nodeDen x) * tupleInterp x y
  w := tupleWNum f x y
  den := nodeDen x ^ 2

theorem map_foldBase (φ : R →+* S) (f : R[X]) (x y : Fin m → R) :
    (foldBase f x y).map φ
      = foldBase (f.map φ) (fun i ↦ φ (x i)) fun i ↦ φ (y i) := by
  ext <;>
    simp [foldBase, ← map_nodeDen, ← map_tupleU, ← map_tupleInterp, ← map_tupleWNum]

end Base

/-! ### Naturality of the fold -/

section Map

variable {R S : Type*} [CommRing R] [CommRing S] {f : R[X]} {xs ys : ℕ → R}
  {s₀ : MumfordNum R}

/-- The step pair transports along a ring homomorphism, given that the stage-`j` state
does. -/
private theorem map_pair_aux (φ : R →+* S) {j : ℕ}
    (h : (foldNum f xs ys s₀ j).map φ
      = foldNum (f.map φ) (fun i ↦ φ (xs i)) (fun i ↦ φ (ys i)) (s₀.map φ) j) :
    φ (foldHNum f xs ys s₀ j)
        = foldHNum (f.map φ) (fun i ↦ φ (xs i)) (fun i ↦ φ (ys i)) (s₀.map φ) j
      ∧ φ (foldCondNum f xs ys s₀ j)
        = foldCondNum (f.map φ) (fun i ↦ φ (xs i)) (fun i ↦ φ (ys i)) (s₀.map φ) j := by
  have hu := congrArg MumfordNum.u h
  have hv := congrArg MumfordNum.v h
  have hd := congrArg MumfordNum.den h
  simp only [MumfordNum.map_u, MumfordNum.map_v, MumfordNum.map_den] at hu hv hd
  rcases j with _ | j
  · simp only [foldNum_zero] at hu hv hd
    constructor <;>
      simp [foldHNum_zero, foldCondNum_zero, ← Polynomial.eval_map_apply, derivative_map,
        map_ofNat]
  · constructor
    · rw [foldHNum_succ, foldHNum_succ, map_sub, map_mul, hd,
        ← Polynomial.eval_map_apply, hv]
    · rw [foldCondNum_succ, foldCondNum_succ, ← Polynomial.eval_map_apply, hu]

/-- **Naturality of the numerator fold**: the recursion commutes with every ring
homomorphism. -/
theorem map_foldNum (φ : R →+* S) (m : ℕ) :
    (foldNum f xs ys s₀ m).map φ
      = foldNum (f.map φ) (fun i ↦ φ (xs i)) (fun i ↦ φ (ys i)) (s₀.map φ) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    obtain ⟨hH, hc⟩ := map_pair_aux φ ih
    rw [foldNum_succ, foldNum_succ, MumfordNum.map_step, ih, hH, hc]

/-- Naturality of the scalar numerators. -/
theorem map_foldHNum (φ : R →+* S) (j : ℕ) :
    φ (foldHNum f xs ys s₀ j)
      = foldHNum (f.map φ) (fun i ↦ φ (xs i)) (fun i ↦ φ (ys i)) (s₀.map φ) j :=
  (map_pair_aux φ (map_foldNum φ j)).1

/-- Naturality of the step-condition numerators. -/
theorem map_foldCondNum (φ : R →+* S) (j : ℕ) :
    φ (foldCondNum f xs ys s₀ j)
      = foldCondNum (f.map φ) (fun i ↦ φ (xs i)) (fun i ↦ φ (ys i)) (s₀.map φ) j :=
  (map_pair_aux φ (map_foldNum φ j)).2

end Map

end ChabautyColeman

end
