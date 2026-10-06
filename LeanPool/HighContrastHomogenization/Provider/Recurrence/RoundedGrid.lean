/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.SqrtOrder
public import LeanPool.HighContrastHomogenization.Setup.Moments

/-!
# High-contrast homogenization: Provider.Recurrence.RoundedGrid

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The rounded adapted grid

The rounded adapted grid of a metric replaces a positive symmetric
matrix `m` by the entrywise rounding

`Q_ℓ(m) = 3^{-ℓ} ⌈3^ℓ 𝓛(m)⌉`,   `𝓛(m) := |m^{-1}|^{1/2} m^{1/2}`,

at an alignment scale `ℓ ≥ k_0(d)`.  Two properties of that convention are what
the adapted geometry rests on, and both are proved here.

The first is that `Q_ℓ(m)` is again positive.  The eigenvalues of the normalized
square root `𝓛(m)` are the numbers `(λ_i(m)/λ_min(m))^{1/2} ≥ 1`, so
`𝓛(m) ≥ I`; rounding moves each entry by less than `3^{-ℓ}`, and the spectral
norm of a `d × d` matrix is at most `d` times the largest absolute value of its
entries, so the rounding perturbs the quadratic form by at most
`d 3^{-ℓ} ≤ d 3^{-k_0(d)}`.  This is exactly the quantity the choice of `k_0(d)`
controls, and `kZero_spec` bounds it by `1/101`.  Hence `Q_ℓ(m)` stays positive
definite, and the adapted cells `⋄_j^q = q□_j` are genuine cells.

The second is integrality.  Every entry of `Q_ℓ(m)` is `3^{-ℓ}` times an
integer, so for every scale `j ≥ ℓ` the matrix `3^j Q_ℓ(m)` has integer entries
and the aligned translation vectors `3^j q w`, `w ∈ ℤ^d`, lie in `ℤ^d`.  That is
the integrality clause of the aligned subdivision in the coarse-block properties
taken from HC, and it is what lets stationarity be applied to the
child cells.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## The normalized square root -/

/-- The square root of a nonnegative multiple of a positive semidefinite matrix
scales by the square root of the multiple. -/
theorem matSqrt_smul {c : ℝ} (hc : 0 ≤ c) {m : Mat d} (hm : m.PosSemidef) :
    matSqrt (c • m) = Real.sqrt c • matSqrt m := by
  refine matSqrt_eq (hm.smul (by exact_mod_cast hc)) ((matSqrt_spec hm).1.smul ?_) ?_
  · positivity
  · have h : (Real.sqrt c • matSqrt m) * (Real.sqrt c • matSqrt m)
        = (Real.sqrt c * Real.sqrt c) • (matSqrt m * matSqrt m) := by
      simp [smul_smul]
    rw [h, Real.mul_self_sqrt hc, (matSqrt_spec hm).2]

/-- The identity is its own square root. -/
theorem matSqrt_one : matSqrt (1 : Mat d) = 1 :=
  matSqrt_eq Matrix.PosSemidef.one Matrix.PosSemidef.one (by simp)

/-- **The normalization of the rounded adapted grid is at least the identity.**
Scaling a positive definite matrix by `|m^{-1}|` puts it above the identity:
conjugating `m^{-1} ≤ |m^{-1}| I` by `m^{1/2}` gives `I ≤ |m^{-1}| m`. -/
theorem one_le_specBound_inv_smul {m : Mat d} (hm : m.PosDef) :
    (1 : Mat d) ≤ specBound m⁻¹ • m := by
  have hc : (0 : ℝ) ≤ specBound (d := d) m⁻¹ := specBound_nonneg _
  have hle : m⁻¹ ≤ specBound m⁻¹ • (1 : Mat d) :=
    matLoewnerLE_matrixOrder_of_posSemidef hm.inv.posSemidef
      (Matrix.PosSemidef.one.smul (by exact_mod_cast hc))
      (matLoewnerLE_specBound_smul_one _)
  have hsymm : (matSqrt m)ᴴ = matSqrt m := (matSqrt_spec hm.posSemidef).1.isHermitian
  have hconj := conj_le_conj' hsymm hle
  have hleft : matSqrt m * m⁻¹ * matSqrt m = 1 := by
    have h := matSqrt_inv_conj hm.inv
    rwa [Matrix.nonsing_inv_nonsing_inv m (isUnit_det_of_posDef hm)] at h
  have hright : matSqrt m * (specBound m⁻¹ • (1 : Mat d)) * matSqrt m
      = specBound m⁻¹ • m := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, (matSqrt_spec hm.posSemidef).2]
  rwa [hleft, hright] at hconj

/-- **The normalized square root is at least the identity.**  Its eigenvalues are
the numbers `(λ_i(m)/λ_min(m))^{1/2}`, the least of which is one. -/
theorem one_le_normalized_matSqrt {m : Mat d} (hm : m.PosDef) :
    (1 : Mat d) ≤ Real.sqrt (specBound m⁻¹) • matSqrt m := by
  have h1 := one_le_specBound_inv_smul hm
  have hPD : (specBound m⁻¹ • m).PosDef := posDef_of_posDef_le Matrix.PosDef.one h1
  have hmono := matSqrt_le_matSqrt (Matrix.PosSemidef.one (n := Fin d) (R := ℝ)) hPD h1
  rwa [matSqrt_one, matSqrt_smul (specBound_nonneg _) hm.posSemidef] at hmono

/-- The normalized square root is symmetric. -/
theorem normalized_matSqrt_symm {m : Mat d} (hm : m.PosSemidef) (i k : Fin d) :
    Real.sqrt (specBound m⁻¹) * matSqrt m k i
      = Real.sqrt (specBound m⁻¹) * matSqrt m i k := by
  have h : (matSqrt m)ᴴ = matSqrt m := (matSqrt_spec hm).1.isHermitian
  have hik := congrArg (fun A : Mat d => A i k) h
  simp only [Matrix.conjTranspose_apply, star_trivial] at hik
  rw [hik]

/-! ## Rounding moves each entry by less than `3^{-ℓ}` -/

/-- The entries of the rounded grid, in terms of the normalized square root. -/
theorem roundedGrid_apply (j : ℤ) (m : Mat d) (i k : Fin d) :
    roundedGrid j m i k =
      (3 : ℝ) ^ (-j) *
        (⌈(3 : ℝ) ^ j * (Real.sqrt (specBound m⁻¹) * matSqrt m i k)⌉ : ℤ) := by
  rw [roundedGrid]
  simp only [Matrix.of_apply, mul_assoc]

/-- Rescaled rounding: if `b a = 1` then `b ⌈a t⌉` lies in `[t, t + b]`. -/
private theorem ceil_rescale_bounds {a b : ℝ} (hb : 0 < b) (hab : b * a = 1) (t : ℝ) :
    0 ≤ b * (⌈a * t⌉ : ℤ) - t ∧ b * (⌈a * t⌉ : ℤ) - t ≤ b := by
  have hba : b * (a * t) = t := by rw [← mul_assoc, hab, one_mul]
  have h1 := mul_le_mul_of_nonneg_left (Int.le_ceil (a * t)) hb.le
  have h2 := mul_le_mul_of_nonneg_left (Int.ceil_lt_add_one (a * t)).le hb.le
  rw [hba] at h1
  rw [mul_add, hba, mul_one] at h2
  exact ⟨by linarith only [h1], by linarith only [h2]⟩

/-- **The rounding error of the rounded adapted grid.**  Every entry of
`Q_ℓ(m) - 𝓛(m)` is nonnegative and at most `3^{-ℓ}`. -/
theorem roundedGrid_sub_normalized_matSqrt_mem (j : ℤ) (m : Mat d) (i k : Fin d) :
    0 ≤ roundedGrid j m i k - Real.sqrt (specBound m⁻¹) * matSqrt m i k ∧
      roundedGrid j m i k - Real.sqrt (specBound m⁻¹) * matSqrt m i k ≤ (3 : ℝ) ^ (-j) := by
  have hb : (0 : ℝ) < (3 : ℝ) ^ (-j) := by positivity
  have hab : (3 : ℝ) ^ (-j) * (3 : ℝ) ^ j = 1 := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    simp
  have h := ceil_rescale_bounds hb hab (Real.sqrt (specBound m⁻¹) * matSqrt m i k)
  rwa [← roundedGrid_apply] at h

/-- The rounded grid is symmetric. -/
theorem roundedGrid_symm (j : ℤ) {m : Mat d} (hm : m.PosSemidef) (i k : Fin d) :
    roundedGrid j m k i = roundedGrid j m i k := by
  rw [roundedGrid_apply, roundedGrid_apply, normalized_matSqrt_symm hm]

/-! ## Positivity of the rounded grid -/

/-- The quadratic form of a matrix with small entries is small: the entrywise
bound `δ` gives `|x · E x| ≤ dδ|x|²`, the spectral-norm-by-entries estimate the
reference text uses on the rounding error. -/
theorem neg_le_dotProduct_mulVec_of_abs_entry_le {E : Mat d} {delta : ℝ}
    (hE : ∀ i k, |E i k| ≤ delta) (x : Fin d → ℝ) :
    -(delta * (d : ℝ) * ∑ i, x i * x i) ≤ x ⬝ᵥ E *ᵥ x := by
  have hexp : x ⬝ᵥ E *ᵥ x = ∑ i, ∑ k, x i * (E i k * x k) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hterm : ∀ i k : Fin d,
      -(delta * ((x i * x i + x k * x k) / 2)) ≤ x i * (E i k * x k) := by
    intro i k
    have habs : |x i * (E i k * x k)| ≤ delta * ((x i * x i + x k * x k) / 2) := by
      have h1 : |x i * (E i k * x k)| = |E i k| * (|x i| * |x k|) := by
        rw [abs_mul, abs_mul]; ring
      have h2 : |x i| * |x k| ≤ (x i * x i + x k * x k) / 2 := by
        nlinarith only [sq_nonneg (|x i| - |x k|), sq_abs (x i), sq_abs (x k)]
      have h3 : (0 : ℝ) ≤ |x i| * |x k| := by positivity
      calc |x i * (E i k * x k)| = |E i k| * (|x i| * |x k|) := h1
        _ ≤ delta * (|x i| * |x k|) := mul_le_mul_of_nonneg_right (hE i k) h3
        _ ≤ delta * ((x i * x i + x k * x k) / 2) :=
            mul_le_mul_of_nonneg_left h2 (le_trans (abs_nonneg _) (hE i k))
    linarith only [habs, neg_abs_le (x i * (E i k * x k))]
  have hsum : ∑ i : Fin d, ∑ k : Fin d,
      -(delta * ((x i * x i + x k * x k) / 2))
        = -(delta * (d : ℝ) * ∑ i : Fin d, x i * x i) := by
    have hinner : ∀ i : Fin d, ∑ k : Fin d, -(delta * ((x i * x i + x k * x k) / 2))
        = -(delta / 2) * ((d : ℝ) * (x i * x i)) +
          -(delta / 2) * ∑ k : Fin d, x k * x k := by
      intro i
      have hpt : ∀ k : Fin d, -(delta * ((x i * x i + x k * x k) / 2))
          = -(delta / 2) * (x i * x i) + -(delta / 2) * (x k * x k) := by
        intro k; ring
      rw [Finset.sum_congr rfl fun k _ => hpt k, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl fun i _ => hinner i, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    ring
  rw [hexp, ← hsum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hterm i k

/-- **The rounded grid is positive definite.**  This is where the choice of
`k_0(d)` is used: at an alignment `ℓ ≥ k_0(d)` the rounding error `d 3^{-ℓ}` is
at most the `1/101` of `kZero_spec`, which the normalization `𝓛(m) ≥ I`
absorbs. -/
theorem posDef_roundedGrid {l : ℤ} (hl : (kZero d : ℤ) ≤ l) {m : Mat d} (hm : m.PosDef) :
    (roundedGrid l m).PosDef := by
  set L : Mat d := Real.sqrt (specBound m⁻¹) • matSqrt m with hL
  set E : Mat d := roundedGrid l m - L with hEdef
  have hdelta : (d : ℝ) * (3 : ℝ) ^ (-l) ≤ 1 / 101 := by
    have hmono : (3 : ℝ) ^ (-l) ≤ (3 : ℝ) ^ (-(kZero d : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    exact le_trans (mul_le_mul_of_nonneg_left hmono (by positivity)) (kZero_spec d)
  have hEentry : ∀ i k, |E i k| ≤ (3 : ℝ) ^ (-l) := by
    intro i k
    obtain ⟨h0, h1⟩ := roundedGrid_sub_normalized_matSqrt_mem l m i k
    have hE : E i k = roundedGrid l m i k - Real.sqrt (specBound m⁻¹) * matSqrt m i k := rfl
    rw [hE, abs_of_nonneg h0]
    exact h1
  have hsymm : (roundedGrid l m).IsHermitian := by
    refine Matrix.IsHermitian.ext fun i k => ?_
    simpa using roundedGrid_symm l hm.posSemidef i k
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hsymm fun x hx => ?_
  have hsplit : roundedGrid l m = L + E := by rw [hEdef]; abel
  have hone : x ⬝ᵥ (1 : Mat d) *ᵥ x ≤ x ⬝ᵥ L *ᵥ x := by
    have hPS : (L - 1).PosSemidef := Matrix.le_iff.mp (one_le_normalized_matSqrt hm)
    have := hPS.dotProduct_mulVec_nonneg x
    rw [Matrix.sub_mulVec, dotProduct_sub] at this
    simpa using this
  have hsq : x ⬝ᵥ (1 : Mat d) *ᵥ x = ∑ i, x i * x i := by
    simp [Matrix.one_mulVec, dotProduct]
  have hxpos : (0 : ℝ) < ∑ i, x i * x i := by
    rw [← hsq]
    have := (Matrix.PosDef.one (n := Fin d) (R := ℝ)).dotProduct_mulVec_pos hx
    simpa using this
  have hEbound := neg_le_dotProduct_mulVec_of_abs_entry_le hEentry x
  have hexp : x ⬝ᵥ roundedGrid l m *ᵥ x = x ⬝ᵥ L *ᵥ x + x ⬝ᵥ E *ᵥ x := by
    rw [hsplit, Matrix.add_mulVec, dotProduct_add]
  have hfinal : (3 : ℝ) ^ (-l) * (d : ℝ) * ∑ i, x i * x i < ∑ i, x i * x i := by
    have hd : (3 : ℝ) ^ (-l) * (d : ℝ) ≤ 1 / 101 := by
      rw [mul_comm]; exact hdelta
    nlinarith only [hxpos, hd]
  have : 0 < x ⬝ᵥ roundedGrid l m *ᵥ x := by
    rw [hexp]
    have h := hsq ▸ hone
    linarith only [h, hEbound, hfinal]
  simpa using this

/-- A rounded adapted grid is positive definite. -/
theorem posDef_of_isRoundedGrid {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q) :
    q.PosDef := by
  obtain ⟨hl, m, hm, rfl⟩ := hq
  exact posDef_roundedGrid hl hm

/-! ## Integrality of the aligned translations -/

/-- Every entry of the rounded grid is `3^{-ℓ}` times an integer. -/
theorem exists_int_roundedGrid (l : ℤ) (m : Mat d) (i k : Fin d) :
    ∃ c : ℤ, roundedGrid l m i k = (3 : ℝ) ^ (-l) * (c : ℝ) :=
  ⟨⌈(3 : ℝ) ^ l * (Real.sqrt (specBound m⁻¹) * matSqrt m i k)⌉, roundedGrid_apply l m i k⟩

/-- **`3^j q` has integer entries at every scale at or above the alignment.**
This is the integrality clause of the aligned subdivision in the coarse-block
properties taken from HC. -/
theorem exists_int_zpow_smul_of_isRoundedGrid {l : ℤ} {q : Mat d}
    (hq : IsRoundedGrid l q) {j : ℤ} (hj : l ≤ j) :
    ∃ n : Fin d → Fin d → ℤ, ∀ i k, (3 : ℝ) ^ j * q i k = (n i k : ℝ) := by
  obtain ⟨_, m, _, rfl⟩ := hq
  classical
  refine ⟨fun i k => 3 ^ (j - l).toNat * (exists_int_roundedGrid l m i k).choose, ?_⟩
  intro i k
  rw [(exists_int_roundedGrid l m i k).choose_spec]
  have hsplit : (3 : ℝ) ^ j * ((3 : ℝ) ^ (-l) * ((exists_int_roundedGrid l m i k).choose : ℝ))
      = (3 : ℝ) ^ (j - l) * ((exists_int_roundedGrid l m i k).choose : ℝ) := by
    rw [← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring_nf
  rw [hsplit]
  have hexp : (3 : ℝ) ^ (j - l) = ((3 ^ (j - l).toNat : ℤ) : ℝ) := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, j - l = (n : ℤ) :=
      ⟨(j - l).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hn, Int.toNat_natCast, zpow_natCast]
    push_cast
    ring
  rw [hexp]
  push_cast
  ring

/-- **The aligned translation vectors are integral.**  For a rounded grid at
alignment `ℓ` and any scale `j ≥ ℓ`, the center `3^j q w` of an aligned adapted
cell lies in `ℤ^d`. -/
theorem exists_intVec_adaptedCellCenter {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q)
    {j : ℤ} (hj : l ≤ j) (w : Fin d → ℤ) :
    ∃ v : Fin d → ℤ, adaptedCellCenter q j w = fun i => (v i : ℝ) := by
  obtain ⟨n, hn⟩ := exists_int_zpow_smul_of_isRoundedGrid hq hj
  refine ⟨fun i => ∑ k, n i k * w k, ?_⟩
  funext i
  have hentry : adaptedCellCenter q j w i = ∑ k, (3 : ℝ) ^ j * q i k * (w k : ℝ) := by
    simp only [adaptedCellCenter, matVecMul, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, mul_assoc]
  rw [hentry]
  push_cast
  exact Finset.sum_congr rfl fun k _ => by rw [hn i k]

end

end Recurrence
end HighContrast
end HCPolySupport
