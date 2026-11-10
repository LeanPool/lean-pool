/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.PeelStage

/-!
# The node alphabets of the certificate atoms

Every certificate atom of `thm:cusp-witness` is a pattern determinant
(`ChabautyColeman.momentDet`) of a **doubles-and-singles alphabet** — a product of squared
node factors `(v + X)²` and single node factors `(u + X)` — possibly times a base factor
(`1` or `X`) and at most one *extension group* carrying a distinguished node `t`: the
signed pair `X² - t²` (step−), the signed trio `(t + X)²(X - t)` (mirror−) or the tripled
node `(t + X)³` (mirror+). This file collects the node polynomials and the coefficient
computations of all these factors:

* `ChabautyColeman.singlesPoly`, `ChabautyColeman.doublesPoly`: the node polynomials of
  `k` single resp. `d` doubled and `k` single nodes, with their recursion, naturality and
  degree API;
* `ChabautyColeman.coeff_C_add_X_sq`, `ChabautyColeman.coeff_X_sq_sub_C`,
  `ChabautyColeman.coeff_trio`, `ChabautyColeman.coeff_tripled`: the coefficients of the
  squared, signed-pair, signed-trio and tripled node factors, with their degree bounds;
* `ChabautyColeman.momentDet_X_peelPattern_one`: the terminal value of the zero-node
  cascades.

The peel induction itself (`LeanPool.HyperellipticCurves.Log.Fold.PeelCoeff`,
`LeanPool.HyperellipticCurves.Log.Fold.PeelCascade`) consumes these at the polynomial variable `u`
of a node.
-/
@[expose] public section

open Polynomial

namespace ChabautyColeman

section FactorCoeff

variable {R : Type*} [CommRing R]

theorem natDegree_C_add_X_lt (u : R) : (C u + X).natDegree < 2 :=
  (natDegree_add_le _ _).trans_lt
    (max_lt (by rw [natDegree_C]; lia) (natDegree_X_le.trans_lt one_lt_two))

/-- The coefficients of the squared node factor. -/
theorem coeff_C_add_X_sq (u : R) (j : ℕ) :
    ((C u + X) ^ 2).coeff j
      = if j = 0 then u ^ 2 else if j = 1 then 2 * u else if j = 2 then 1 else 0 := by
  have h1 : (C u + X) ^ 2
      = Polynomial.C (u ^ 2) + Polynomial.C (2 * u) * X + X ^ 2 := by
    rw [add_sq, ← map_pow, map_mul, map_ofNat]
  rw [h1, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C,
    Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  split_ifs <;> first | ring1 | (exfalso; lia)

theorem natDegree_C_add_X_sq_lt (u : R) : ((C u + X) ^ 2).natDegree < 3 := by
  refine lt_of_le_of_lt (natDegree_pow_le ..) ?_
  lia [natDegree_C_add_X_lt u]

/-- The coefficients of the signed-pair node factor. -/
theorem coeff_X_sq_sub_C (a : R) (j : ℕ) :
    (X ^ 2 - Polynomial.C a).coeff j = if j = 0 then -a else if j = 2 then 1 else 0 := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  split_ifs <;> first | ring1 | (exfalso; lia)

theorem natDegree_X_sq_sub_C_lt (a : R) : ((X : R[X]) ^ 2 - Polynomial.C a).natDegree < 3 :=
  lt_of_le_of_lt (natDegree_sub_le ..)
    (max_lt (lt_of_le_of_lt (natDegree_X_pow_le _) (by lia)) (by rw [natDegree_C]; lia))

/-- The coefficients of the signed-trio node factor. -/
theorem coeff_trio (v : R) (j : ℕ) :
    ((Polynomial.C v + X) ^ 2 * (X - Polynomial.C v)).coeff j
      = if j = 0 then -v ^ 3 else if j = 1 then -v ^ 2 else if j = 2 then v else
          if j = 3 then 1 else 0 := by
  have h1 : (Polynomial.C v + X) ^ 2 * (X - Polynomial.C v)
      = Polynomial.C (-v ^ 3) + Polynomial.C (-v ^ 2) * X + Polynomial.C v * X ^ 2
        + X ^ 3 := by
    simp only [map_neg, map_pow]
    ring
  rw [h1, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_X,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X_pow]
  split_ifs <;> first | ring1 | (exfalso; lia)

/-- The coefficients of the tripled node factor. -/
theorem coeff_tripled (v : R) (j : ℕ) :
    ((Polynomial.C v + X) ^ 3).coeff j
      = if j = 0 then v ^ 3 else if j = 1 then 3 * v ^ 2 else if j = 2 then 3 * v else
          if j = 3 then 1 else 0 := by
  have h1 : (Polynomial.C v + X) ^ 3
      = Polynomial.C (v ^ 3) + Polynomial.C (3 * v ^ 2) * X + Polynomial.C (3 * v) * X ^ 2
        + X ^ 3 := by
    simp only [map_mul, map_pow, map_ofNat]
    ring
  rw [h1, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_X,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X_pow]
  split_ifs <;> first | ring1 | (exfalso; lia)

theorem natDegree_trio_lt (v : R) :
    ((Polynomial.C v + X) ^ 2 * (X - Polynomial.C v)).natDegree < 4 := by
  refine lt_of_le_of_lt (natDegree_mul_le ..) ?_
  have h2 : ((X : R[X]) - Polynomial.C v).natDegree ≤ 1 :=
    (natDegree_sub_le ..).trans (max_le natDegree_X_le (by rw [natDegree_C]; lia))
  lia [natDegree_C_add_X_sq_lt v]

theorem natDegree_tripled_lt (v : R) : ((Polynomial.C v + X) ^ 3).natDegree < 4 := by
  refine lt_of_le_of_lt (natDegree_pow_le ..) ?_
  lia [natDegree_C_add_X_lt v]

end FactorCoeff

section NodePolys

variable {R : Type*} [CommRing R]

/-- The node polynomial of a singles cascade: the first `k` nodes, each once. -/
noncomputable def singlesPoly (u : ℕ → R) (k : ℕ) : R[X] :=
  ∏ i ∈ Finset.range k, (C (u i) + X)

theorem singlesPoly_zero (u : ℕ → R) : singlesPoly u 0 = 1 :=
  Finset.prod_range_zero _

theorem singlesPoly_succ (u : ℕ → R) (k : ℕ) :
    singlesPoly u (k + 1) = singlesPoly u k * (C (u k) + X) :=
  Finset.prod_range_succ _ k

theorem natDegree_singlesPoly_le (u : ℕ → R) (k : ℕ) :
    (singlesPoly u k).natDegree ≤ k := by
  induction k with
  | zero => simp [singlesPoly_zero]
  | succ k ih =>
    rw [singlesPoly_succ]
    refine le_trans (natDegree_mul_le ..) ?_
    lia [natDegree_C_add_X_lt (u k)]

theorem singlesPoly_map {S : Type*} [CommRing S] (ψ : R →+* S) (u : ℕ → R) (k : ℕ) :
    (singlesPoly u k).map ψ = singlesPoly (fun i ↦ ψ (u i)) k := by
  rw [singlesPoly, singlesPoly, Polynomial.map_prod]
  exact Finset.prod_congr rfl fun i _ ↦ by
    rw [Polynomial.map_add, Polynomial.map_C, Polynomial.map_X]

theorem singlesPoly_congr {u u' : ℕ → R} {k : ℕ} (h : ∀ i < k, u i = u' i) :
    singlesPoly u k = singlesPoly u' k := by
  rw [singlesPoly, singlesPoly]
  exact Finset.prod_congr rfl fun i hi ↦ by rw [h i (Finset.mem_range.mp hi)]

/-- The node polynomial of a doubles cascade: `d` doubled nodes and `k` single ones. -/
noncomputable def doublesPoly (v u : ℕ → R) (d k : ℕ) : R[X] :=
  (∏ i ∈ Finset.range d, (C (v i) + X) ^ 2) * singlesPoly u k

theorem doublesPoly_zero (v u : ℕ → R) (k : ℕ) :
    doublesPoly v u 0 k = singlesPoly u k := by
  rw [doublesPoly, Finset.prod_range_zero, one_mul]

theorem doublesPoly_succ (v u : ℕ → R) (d k : ℕ) :
    doublesPoly v u (d + 1) k = doublesPoly v u d k * (Polynomial.C (v d) + X) ^ 2 := by
  rw [doublesPoly, doublesPoly, Finset.prod_range_succ]
  ring

theorem doublesPoly_succ_right (v u : ℕ → R) (d k : ℕ) :
    doublesPoly v u d (k + 1) = doublesPoly v u d k * (C (u k) + X) := by
  rw [doublesPoly, doublesPoly, singlesPoly_succ, mul_assoc]

theorem doublesPoly_succ_left (v u : ℕ → R) (d k : ℕ) :
    doublesPoly v u (d + 1) k
      = (Polynomial.C (v 0) + X) ^ 2 * doublesPoly (fun l ↦ v (l + 1)) u d k := by
  rw [doublesPoly, doublesPoly, Finset.prod_range_succ']
  ring

theorem doublesPoly_map {S : Type*} [CommRing S] (ψ : R →+* S) (v u : ℕ → R) (d k : ℕ) :
    (doublesPoly v u d k).map ψ
      = doublesPoly (fun l ↦ ψ (v l)) (fun i ↦ ψ (u i)) d k := by
  simp [doublesPoly, singlesPoly, Polynomial.map_prod]

theorem doublesPoly_congr {v v' u u' : ℕ → R} {d k : ℕ} (hv : ∀ l < d, v l = v' l)
    (hu : ∀ i < k, u i = u' i) : doublesPoly v u d k = doublesPoly v' u' d k := by
  rw [doublesPoly, doublesPoly, singlesPoly_congr hu]
  exact congrArg (· * _)
    (Finset.prod_congr rfl fun l hl ↦ by rw [hv l (Finset.mem_range.mp hl)])

theorem natDegree_doublesPoly_le (v u : ℕ → R) (d k : ℕ) :
    (doublesPoly v u d k).natDegree ≤ 2 * d + k := by
  induction d with
  | zero => rw [doublesPoly_zero]; exact (natDegree_singlesPoly_le u k).trans (by lia)
  | succ d ih =>
    rw [doublesPoly_succ]
    refine le_trans (natDegree_mul_le ..) ?_
    lia [natDegree_C_add_X_sq_lt (v d)]

end NodePolys

section Terminal

variable {R : Type*} [CommRing R] {g : ℕ}

/-- **The terminal state of the zero-node cascades**: the matrix of the bare `X` at the
pattern `c₁ = (0, 2, 4, …)` is the identity — the base of the avoidance-value atoms. -/
theorem momentDet_X_peelPattern_one : momentDet g (X : R[X]) (peelPattern g 1) = 1 := by
  rw [momentDet]
  have h1 : (Matrix.of fun i m : Fin g ↦
      ((X : R[X]) * X ^ (peelPattern g 1 m)).coeff (2 * (i : ℕ) + 1)) = 1 := by
    ext i m
    rw [Matrix.of_apply, ← pow_succ', Polynomial.coeff_X_pow, Matrix.one_apply,
      peelPattern]
    have him : i = m ↔ (i : ℕ) = (m : ℕ) := Fin.ext_iff
    split_ifs with h2 h3 h4 h5 h6 h7 <;> first | rfl | (exfalso; lia)
  rw [h1, Matrix.det_one]

end Terminal

end ChabautyColeman

end
