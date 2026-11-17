/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.Moment

/-!
# Pattern determinants and the peel expansion

The nonvanishing certificates of the moment route (`thm:cusp-witness` and the informal
certificate remark preceding it in the blueprint) all concern determinants of
one uniform family, formalized here as `ChabautyColeman.momentDet`: the `g × g` determinant
whose `m`-th column extracts the odd coefficients of `q·X^(c m)`, for a column-shift pattern
`c : Fin g → ℕ`. The moment determinant is the identity pattern
(`ChabautyColeman.momentDet_id`); the intermediate minors of the certificate induction are
jump patterns — the matrix size never changes, so no dependent indexing arises.

The certificates peel one node variable at a time: multiplying `q` by the peeled factor
(`(u+X)`, `(u+X)²`, or the signed variants) makes each column a linear combination of shifted
columns, and the **peel expansion** (`ChabautyColeman.momentDet_mul`, from the multilinear
engine `ChabautyColeman.det_expand_cols`) rewrites the determinant as a weighted sum of
pattern determinants over all shift-choice functions. Most choices vanish — by a repeated
column (`ChabautyColeman.momentDet_eq_zero_of_eq`) or an out-of-range row
(`ChabautyColeman.momentDet_eq_zero_of_row`) — and collecting the survivors of the top
weight is where the `±2^a` certificate coefficients originate.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section MomentDet

variable {R : Type*} [CommRing R] {g : ℕ} {q F : R[X]}

/-- **The pattern determinant**: the determinant of the `g × g` matrix whose `m`-th column
extracts the odd coefficients `z^1, z^3, …, z^(2g-1)` of `q·X^(c m)`. With the identity
pattern this is the moment determinant; column-shift patterns `c` encode the intermediate
minors of the peeling induction — the matrix size never changes. -/
noncomputable def momentDet (g : ℕ) (q : R[X]) (c : Fin g → ℕ) : R :=
  (Matrix.of fun i m : Fin g ↦ (q * X ^ (c m)).coeff (2 * (i : ℕ) + 1)).det

/-- The identity pattern recovers the moment matrix. -/
theorem momentDet_id : momentDet g q (fun m ↦ (m : ℕ)) = (momentMatrix g q).det := rfl

/-- Pattern determinants are natural in the coefficient ring. -/
theorem momentDet_map {S : Type*} [CommRing S] (φ : R →+* S) (q : R[X]) (c : Fin g → ℕ) :
    momentDet g (q.map φ) c = φ (momentDet g q c) := by
  rw [momentDet, momentDet, RingHom.map_det]
  congr 1
  ext i m
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply,
    ← Polynomial.coeff_map, Polynomial.map_mul, Polynomial.map_pow, map_X]

/-- A pattern determinant is nonzero as soon as its image under a ring map is. -/
theorem momentDet_ne_zero_of_map {S : Type*} [CommRing S] (φ : R →+* S) {c : Fin g → ℕ}
    (h : momentDet g (q.map φ) c ≠ 0) : momentDet g q c ≠ 0 :=
  fun h0 ↦ h (by rw [momentDet_map, h0, map_zero])

/-- A constant factor of the alphabet scales the pattern determinant by its `g`-th power. -/
theorem momentDet_C_mul (a : R) (q : R[X]) (c : Fin g → ℕ) :
    momentDet g (C a * q) c = a ^ g * momentDet g q c := by
  rw [momentDet, momentDet]
  have h1 : (Matrix.of fun i m : Fin g ↦ ((C a * q) * X ^ (c m)).coeff (2 * (i : ℕ) + 1))
      = a • Matrix.of fun i m : Fin g ↦ ((q * X ^ (c m)).coeff (2 * (i : ℕ) + 1)) := by
    ext i m
    rw [Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, mul_assoc,
      Polynomial.coeff_C_mul, smul_eq_mul]
  rw [h1, Matrix.det_smul, Fintype.card_fin]

/-- A pattern determinant with a repeated column vanishes. -/
theorem momentDet_eq_zero_of_eq {c : Fin g → ℕ} {m m' : Fin g} (hc : c m = c m')
    (hmm : m ≠ m') : momentDet g q c = 0 :=
  Matrix.det_zero_of_column_eq hmm fun i ↦ by
    rw [Matrix.of_apply, Matrix.of_apply, hc]

/-- A coefficient of `q·X^s` below the shift vanishes. -/
theorem coeff_mul_X_pow_eq_zero_of_lt {s k : ℕ} (h : k < s) : (q * X ^ s).coeff k = 0 := by
  rw [coeff_mul_X_pow', ite_eq_right (by lia)]

/-- A coefficient of `q·X^s` above the degree vanishes. -/
theorem coeff_mul_X_pow_eq_zero_of_natDegree_lt {s k : ℕ} (h : q.natDegree + s < k) :
    (q * X ^ s).coeff k = 0 := by
  rw [coeff_mul_X_pow', ite_eq_left (by lia)]
  exact coeff_eq_zero_of_natDegree_lt (by lia)

/-- A pattern determinant with a row of out-of-range entries vanishes: row `i` is zero as
soon as every column's shift misses the window `[k - deg q, k]` around `k = 2i+1`. -/
theorem momentDet_eq_zero_of_row {c : Fin g → ℕ} {i : Fin g}
    (h : ∀ m, 2 * (i : ℕ) + 1 < c m ∨ q.natDegree + c m < 2 * (i : ℕ) + 1) :
    momentDet g q c = 0 := by
  refine Matrix.det_eq_zero_of_row_eq_zero i fun m ↦ ?_
  rcases h m with h | h
  · exact coeff_mul_X_pow_eq_zero_of_lt h
  · exact coeff_mul_X_pow_eq_zero_of_natDegree_lt h

/-- **The multilinear column expansion**: the determinant of a matrix whose `m`-th column is
a linear combination `Σ_r f m r · γ (d m r)` of a column family expands over all choice
functions `σ`, with weight `∏ f m (σ m)`. This is the engine of the peeling induction: one
lemma covers the single, doubled and signed peels — and fixed columns (constant `f m`) —
alike. -/
theorem det_expand_cols {ρ : ℕ} (γ : ℕ → Fin g → R) (f : Fin g → Fin ρ → R)
    (d : Fin g → Fin ρ → ℕ) :
    (Matrix.of fun i m : Fin g ↦ ∑ r : Fin ρ, f m r * γ (d m r) i).det
      = ∑ σ : Fin g → Fin ρ, (∏ m, f m (σ m))
          * (Matrix.of fun i m : Fin g ↦ γ (d m (σ m)) i).det := by
  calc (Matrix.of fun i m : Fin g ↦ ∑ r : Fin ρ, f m r * γ (d m r) i).det
      = Matrix.detRowAlternating (fun m : Fin g ↦ ∑ r : Fin ρ, f m r • γ (d m r)) := by
        rw [← Matrix.det_transpose]
        congr 1
        funext m i
        simp [Matrix.transpose_apply]
    _ = ∑ σ : Fin g → Fin ρ,
          Matrix.detRowAlternating (fun m ↦ f m (σ m) • γ (d m (σ m))) :=
        Matrix.detRowAlternating.toMultilinearMap.map_sum
          (g := fun m r ↦ f m r • γ (d m r))
    _ = ∑ σ : Fin g → Fin ρ, (∏ m, f m (σ m))
          * (Matrix.of fun i m : Fin g ↦ γ (d m (σ m)) i).det := by
        refine Finset.sum_congr rfl fun σ _ ↦ ?_
        rw [show Matrix.detRowAlternating (fun m ↦ f m (σ m) • γ (d m (σ m)))
            = Matrix.detRowAlternating.toMultilinearMap
              (fun m ↦ f m (σ m) • γ (d m (σ m))) from rfl,
          MultilinearMap.map_smul_univ, smul_eq_mul]
        congr 1
        rw [← Matrix.det_transpose]
        rfl

/-- **The peel expansion**: multiplying the node polynomial by a factor `F` with
`deg F < ρ` expands the pattern determinant over all shift-choice functions `σ`, weighted by
the products of the chosen coefficients of `F`. Peeling one node variable `u` is the case
`F = (u+X)^ε·(-u+X)^δ`; the choice weights are where the powers of `2` (and the signed
values) of the certificates originate. -/
theorem momentDet_mul {ρ : ℕ} (hF : F.natDegree < ρ) (c : Fin g → ℕ) :
    momentDet g (q * F) c
      = ∑ σ : Fin g → Fin ρ, (∏ m, F.coeff (σ m))
          * momentDet g q (fun m ↦ c m + (σ m : ℕ)) := by
  have hcol (m : Fin g) (k : ℕ) : (q * F * X ^ (c m)).coeff k
      = ∑ r : Fin ρ, F.coeff (r : ℕ) * (q * X ^ (c m + (r : ℕ))).coeff k := by
    have h1 := coeff_mul_eq_sum_coeff_mul_X_pow (A := F) (q := q * X ^ (c m))
      (g := ρ - 1) (by lia) k
    have h2 : ∑ r : Fin ρ, F.coeff (r : ℕ) * (q * X ^ (c m) * X ^ (r : ℕ)).coeff k
        = ∑ r ∈ Finset.range ρ, F.coeff r * (q * X ^ (c m) * X ^ r).coeff k :=
      Fin.sum_univ_eq_sum_range (fun r ↦ F.coeff r * (q * X ^ (c m) * X ^ r).coeff k) ρ
    rw [show F * (q * X ^ (c m)) = q * F * X ^ (c m) by ring,
      Nat.sub_add_cancel (by lia)] at h1
    rw [h1, ← h2]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [mul_assoc, ← pow_add]
  have h3 : (Matrix.of fun i m : Fin g ↦ (q * F * X ^ (c m)).coeff (2 * (i : ℕ) + 1))
      = Matrix.of fun i m : Fin g ↦
        ∑ r : Fin ρ, F.coeff (r : ℕ) * (q * X ^ (c m + (r : ℕ))).coeff (2 * (i : ℕ) + 1) := by
    ext i m
    rw [Matrix.of_apply, Matrix.of_apply, hcol]
  rw [momentDet, h3]
  exact det_expand_cols (fun s i ↦ (q * X ^ s).coeff (2 * (i : ℕ) + 1))
    (fun _ r ↦ F.coeff r) (fun m r ↦ c m + (r : ℕ))

/-- The peel expansion in the form the survivor analyses consume: fully applied to the
moment-column family, so that rewriting needs no higher-order matching. -/
theorem momentDet_expand {ρ : ℕ} (f : Fin g → Fin ρ → R) (d : Fin g → Fin ρ → ℕ) :
    (Matrix.of fun i m : Fin g ↦
        ∑ r : Fin ρ, f m r * (q * X ^ (d m r)).coeff (2 * (i : ℕ) + 1)).det
      = ∑ σ : Fin g → Fin ρ, (∏ m, f m (σ m)) * momentDet g q (fun m ↦ d m (σ m)) :=
  det_expand_cols (fun s i ↦ (q * X ^ s).coeff (2 * (i : ℕ) + 1)) f d

end MomentDet

end ChabautyColeman

end
