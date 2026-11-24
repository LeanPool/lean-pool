/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Minkowski's determinant inequality

Blueprint `ana:minkowski-determinant` (`blueprint/src/analytic.tex`; TN.5, the first ingredient of
    Boucksom's upper
semicontinuity of the volume, `ana:volume-semicontinuity`).  Sources: Boucksom 2002
    (`bou02-volume`), the proof of the
semicontinuity of `T_ac^n` (arXiv Lemma 3.5, published Proposition 2.1) and of the log-concavity
    of the volume (Proposition 4.5,
published page 1056), which use that `A ↦ det(A)^{1/n}` is concave and homogeneous on the cone of
    Hermitian nonnegative
`n × n` matrices.

For positive semidefinite Hermitian complex matrices `A`, `B` of size `n ≥ 1` (indexed by a
    nonempty finite type), with real
determinants `a = Re det A ≥ 0`, `b = Re det B ≥ 0`:

* **Minkowski** (`rpow_inv_card_re_det_add_le`): `a^{1/n} + b^{1/n} ≤ (Re det (A + B))^{1/n}`;
* `re_det_le_re_det_add`: `Re det A ≤ Re det (A + B)` (monotonicity);
* `concaveOn_rpow_inv_card_re_det`: `A ↦ (Re det A)^{1/n}` is concave on the convex cone of
    positive semidefinite matrices
  (`convex_setOf_posSemidef`), and `rpow_inv_card_re_det_smul` (homogeneity).

Proof of Minkowski: if `det A = 0` and `det B = 0` there is nothing to prove; by symmetry let `A`
    be invertible, `A = y* y`.  With
`X = (y⁻¹)* B y⁻¹ ≥ 0`, of eigenvalues `λᵢ ≥ 0`, one has
    `det (A + B) = det (1 + X) det A = ∏(1 + λᵢ) a` and `det B = ∏ λᵢ a`;
and `1 + (∏ λᵢ)^{1/n} ≤ (∏ (1 + λᵢ))^{1/n}` (`one_add_rpow_prod_le`) by the arithmetic-geometric
    mean inequality applied to
`1/(1 + λᵢ)` and to `λᵢ/(1 + λᵢ)`, whose sum is `1`.

Generic matrix analysis: no complex-geometric, pluripotential, Kähler, volume or current constant.
    Sorry-free.
-/

@[expose] public section

open Finset Matrix
open scoped ComplexOrder MatrixOrder

namespace SGPT.Foundations.Analysis.Pending.MinkowskiDeterminant

noncomputable section

/-! ### The scalar inequality -/

/-- **`1 + (∏ λᵢ)^{1/n} ≤ (∏ (1 + λᵢ))^{1/n}`** for `n` nonnegative reals (`n ≥ 1`). -/
theorem one_add_rpow_prod_le {ι : Type*} [Fintype ι] [Nonempty ι] (l : ι → ℝ) (hl : ∀ i, 0 ≤ l i) :
    1 + (∏ i, l i) ^ ((Fintype.card ι : ℝ)⁻¹) ≤ (∏ i, (1 + l i)) ^ ((Fintype.card ι : ℝ)⁻¹) := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  set r : ℝ := n⁻¹ with hr
  have hr0 : 0 ≤ r := inv_nonneg.mpr hn0.le
  have hpos : ∀ i, 0 < 1 + l i := fun i => by linarith [hl i]
  have hw : ∑ _i : ι, r = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hr, ← hn, mul_inv_cancel₀ hn0.ne']
  -- the two AM-GM inequalities
  have h1 := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ) (fun _ => r)
    (fun i => (1 + l i)⁻¹)
    (fun _ _ => hr0) hw (fun i _ => (inv_pos.mpr (hpos i)).le)
  have h2 := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ) (fun _ => r)
    (fun i => l i / (1 + l i))
    (fun _ _ => hr0) hw (fun i _ => div_nonneg (hl i) (hpos i).le)
  have hfrac : ∀ i, (1 + l i)⁻¹ + l i / (1 + l i) = 1 := fun i => by
    have : (1 + l i)⁻¹ + l i / (1 + l i) = (1 + l i) * (1 + l i)⁻¹ := by ring
    rw [this, mul_inv_cancel₀ (hpos i).ne']
  have hsum : ∑ i, r * (1 + l i)⁻¹ + ∑ i, r * (l i / (1 + l i)) = 1 := by
    calc ∑ i, r * (1 + l i)⁻¹ + ∑ i, r * (l i / (1 + l i))
        = ∑ i, (r * (1 + l i)⁻¹ + r * (l i / (1 + l i))) := Finset.sum_add_distrib.symm
      _ = ∑ _i : ι, r := Finset.sum_congr rfl fun i _ => by rw [← mul_add, hfrac i, mul_one]
      _ = 1 := hw
  set P : ℝ := ∏ i, (1 + l i) with hP
  set G : ℝ := ∏ i, l i with hG
  have hP0 : 0 < P := Finset.prod_pos fun i _ => hpos i
  have hG0 : 0 ≤ G := Finset.prod_nonneg fun i _ => hl i
  have hPr : 0 < P ^ r := Real.rpow_pos_of_pos hP0 r
  -- rewrite the geometric means
  have e1 : ∏ i, ((1 + l i)⁻¹) ^ r = (P ^ r)⁻¹ := by
    rw [Real.finsetProd_rpow _ _ (fun i _ => (inv_pos.mpr (hpos i)).le), Finset.prod_inv_distrib,
      Real.inv_rpow hP0.le]
  have e2 : ∏ i, (l i / (1 + l i)) ^ r = G ^ r / P ^ r := by
    rw [Real.finsetProd_rpow _ _ (fun i _ => div_nonneg (hl i) (hpos i).le),
      Finset.prod_div_distrib,
      Real.div_rpow hG0 hP0.le]
  have key : (P ^ r)⁻¹ + G ^ r / P ^ r ≤ 1 := by
    have := add_le_add h1 h2
    rw [e1, e2, hsum] at this
    exact this
  have key' : (1 + G ^ r) / P ^ r ≤ 1 := by
    rw [add_div, one_div]
    exact key
  rwa [div_le_one hPr] at key'

/-! ### The determinant of a positive semidefinite matrix -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant of a Hermitian matrix is the (real) product of its eigenvalues. -/
theorem det_eq_ofReal_prod_eigenvalues {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    A.det = ((∏ i, hA.eigenvalues i : ℝ) : ℂ) := by
  rw [hA.det_eq_prod_eigenvalues]
  push_cast
  rfl

/-- The determinant of a positive semidefinite matrix is a nonnegative real. -/
theorem re_det_nonneg {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : 0 ≤ A.det.re := by
  rw [det_eq_ofReal_prod_eigenvalues hA.isHermitian, Complex.ofReal_re]
  exact Finset.prod_nonneg fun i _ => hA.eigenvalues_nonneg i

/-- The determinant of a positive semidefinite matrix is real. -/
theorem det_eq_ofReal_re {A : Matrix ι ι ℂ} (hA : A.IsHermitian) : A.det = ((A.det.re : ℝ) : ℂ)
    := by
  rw [det_eq_ofReal_prod_eigenvalues hA, Complex.ofReal_re]

/-- **`det (1 + X) = ∏ (1 + λᵢ)`** for a Hermitian `X` with eigenvalues `λᵢ`. -/
theorem det_one_add_eq_prod {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    (1 + X).det = ((∏ i, (1 + hX.eigenvalues i) : ℝ) : ℂ) := by
  have h1 : 1 + X = Unitary.conjStarAlgAut ℂ _ hX.eigenvectorUnitary
      (1 + Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues)) := by
    conv_lhs => rw [hX.spectral_theorem]
    simp only [map_add, map_one]
  rw [h1, Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
    ← Matrix.det_mul, Unitary.coe_star_mul_self, Matrix.det_one, one_mul,
    ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.det_diagonal]
  push_cast
  rfl

/-! ### Minkowski's inequality -/

/-- The main case of Minkowski's inequality: `A` invertible. -/
theorem rpow_inv_card_re_det_add_le_of_ne_zero [Nonempty ι] {A B : Matrix ι ι ℂ} (hA :
    A.PosSemidef)
    (hB : B.PosSemidef) (hdet : A.det ≠ 0) :
    A.det.re ^ ((Fintype.card ι : ℝ)⁻¹) + B.det.re ^ ((Fintype.card ι : ℝ)⁻¹) ≤
      (A + B).det.re ^ ((Fintype.card ι : ℝ)⁻¹) := by
  set r : ℝ := (Fintype.card ι : ℝ)⁻¹ with hr
  have hr0 : 0 ≤ r := inv_nonneg.mpr (Nat.cast_nonneg _)
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  simp only [Matrix.star_eq_conjTranspose] at hdet hA ⊢
  have hy : IsUnit y.det := by
    rw [Matrix.det_mul] at hdet
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)
  set X := (y⁻¹)ᴴ * B * y⁻¹ with hXdef
  have hX : X.PosSemidef := hB.conjTranspose_mul_mul_same _
  have hinv : y⁻¹ * y = 1 := Matrix.nonsing_inv_mul y hy
  have hinvH : yᴴ * (y⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one]
  have hBX : yᴴ * X * y = B := by
    calc yᴴ * X * y = (yᴴ * (y⁻¹)ᴴ) * B * (y⁻¹ * y) := by simp only [hXdef, mul_assoc]
      _ = B := by rw [hinv, hinvH, one_mul, mul_one]
  have hsum : yᴴ * (1 + X) * y = yᴴ * y + B := by
    rw [mul_add, add_mul, mul_one, hBX]
  set a : ℝ := (yᴴ * y).det.re with hadef
  have ha : 0 ≤ a := re_det_nonneg hA
  have hdetA : (yᴴ * y).det = (a : ℂ) := det_eq_ofReal_re hA.isHermitian
  -- the determinants in terms of the eigenvalues of `X`
  have hdetsum : (yᴴ * y + B).det.re = (∏ i, (1 + hX.isHermitian.eigenvalues i)) * a := by
    rw [← hsum]
    have : (yᴴ * (1 + X) * y).det = (1 + X).det * (yᴴ * y).det := by
      simp only [Matrix.det_mul]
      ring
    rw [this, det_one_add_eq_prod hX.isHermitian, hdetA, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hdetB : B.det.re = (∏ i, hX.isHermitian.eigenvalues i) * a := by
    rw [← hBX]
    have : (yᴴ * X * y).det = X.det * (yᴴ * y).det := by
      simp only [Matrix.det_mul]
      ring
    rw [this, det_eq_ofReal_prod_eigenvalues hX.isHermitian, hdetA, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  rw [hdetsum, hdetB]
  have hl : ∀ i, 0 ≤ hX.isHermitian.eigenvalues i := hX.eigenvalues_nonneg
  have hG : 0 ≤ ∏ i, hX.isHermitian.eigenvalues i := Finset.prod_nonneg fun i _ => hl i
  have hP : 0 ≤ ∏ i, (1 + hX.isHermitian.eigenvalues i) :=
    Finset.prod_nonneg fun i _ => by linarith [hl i]
  rw [Real.mul_rpow hP ha, Real.mul_rpow hG ha]
  have hkey := one_add_rpow_prod_le _ hl
  have har : 0 ≤ a ^ r := Real.rpow_nonneg ha r
  calc a ^ r + (∏ i, hX.isHermitian.eigenvalues i) ^ r * a ^ r
      = (1 + (∏ i, hX.isHermitian.eigenvalues i) ^ r) * a ^ r := by ring
    _ ≤ (∏ i, (1 + hX.isHermitian.eigenvalues i)) ^ r * a ^ r := mul_le_mul_of_nonneg_right hkey
      har

/-- **Minkowski's determinant inequality**: for positive semidefinite Hermitian `A`,
    `B` of size `n ≥ 1`,
`(det A)^{1/n} + (det B)^{1/n} ≤ (det (A + B))^{1/n}` (real determinants). -/
theorem rpow_inv_card_re_det_add_le [Nonempty ι] {A B : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    A.det.re ^ ((Fintype.card ι : ℝ)⁻¹) + B.det.re ^ ((Fintype.card ι : ℝ)⁻¹) ≤
      (A + B).det.re ^ ((Fintype.card ι : ℝ)⁻¹) := by
  by_cases hdA : A.det = 0
  · by_cases hdB : B.det = 0
    · have hr : (Fintype.card ι : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
      rw [hdA, hdB, Complex.zero_re, Real.zero_rpow hr, zero_add]
      exact Real.rpow_nonneg (re_det_nonneg (hA.add hB)) _
    · have h := rpow_inv_card_re_det_add_le_of_ne_zero hB hA hdB
      rwa [add_comm (B.det.re ^ _), add_comm B A] at h
  · exact rpow_inv_card_re_det_add_le_of_ne_zero hA hB hdA

/-- **Monotonicity of the determinant** on positive semidefinite matrices: `det A ≤ det (A + B)`.
-/
theorem re_det_le_re_det_add {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A.det.re ≤ (A + B).det.re := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Matrix.det_isEmpty]
  set r : ℝ := (Fintype.card ι : ℝ)⁻¹ with hr
  have hr0 : 0 < r := inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have h := rpow_inv_card_re_det_add_le hA hB
  have h' : A.det.re ^ r ≤ (A + B).det.re ^ r := le_trans (le_add_of_nonneg_right (Real.rpow_nonneg
    (re_det_nonneg hB) r)) h
  exact (Real.rpow_le_rpow_iff (re_det_nonneg hA) (re_det_nonneg (hA.add hB)) hr0).mp h'

/-! ### Homogeneity and concavity -/

/-- **Homogeneity**: `(det (t A))^{1/n} = t (det A)^{1/n}` for `t ≥ 0` (positive semidefinite `A`,
    `n ≥ 1`). -/
theorem rpow_inv_card_re_det_smul [Nonempty ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) :
    (t • A).det.re ^ ((Fintype.card ι : ℝ)⁻¹) = t * A.det.re ^ ((Fintype.card ι : ℝ)⁻¹) := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsmul : t • A = (t : ℂ) • A := by
    ext i j
    simp [Complex.real_smul]
  rw [hsmul, Matrix.det_smul, det_eq_ofReal_re hA.isHermitian, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul,
    Complex.ofReal_re, Real.mul_rpow (pow_nonneg ht _) (re_det_nonneg hA), ← Real.rpow_natCast,
    ← Real.rpow_mul ht, mul_inv_cancel₀ hcard, Real.rpow_one, Complex.ofReal_re]

omit [Fintype ι] [DecidableEq ι] in
/-- The positive semidefinite matrices form a convex cone. -/
theorem convex_setOf_posSemidef : Convex ℝ {A : Matrix ι ι ℂ | A.PosSemidef} := by
  intro A hA B hB s t hs ht _
  have hsA : (s • A).PosSemidef := by
    have : s • A = (s : ℂ) • A := by ext i j; simp [Complex.real_smul]
    rw [this]
    exact hA.smul (by exact_mod_cast hs)
  have htB : (t • B).PosSemidef := by
    have : t • B = (t : ℂ) • B := by ext i j; simp [Complex.real_smul]
    rw [this]
    exact hB.smul (by exact_mod_cast ht)
  exact hsA.add htB

/-- **Concavity of `A ↦ (det A)^{1/n}`** on the cone of positive semidefinite Hermitian matrices
    (`n ≥ 1`). -/
theorem concaveOn_rpow_inv_card_re_det [Nonempty ι] :
    ConcaveOn ℝ {A : Matrix ι ι ℂ | A.PosSemidef} fun A => A.det.re ^ ((Fintype.card ι : ℝ)⁻¹)
      := by
  refine ⟨convex_setOf_posSemidef, fun A hA B hB s t hs ht _ => ?_⟩
  have hsA : (s • A).PosSemidef := by
    have : s • A = (s : ℂ) • A := by ext i j; simp [Complex.real_smul]
    rw [this]
    exact (show A.PosSemidef from hA).smul (by exact_mod_cast hs)
  have htB : (t • B).PosSemidef := by
    have : t • B = (t : ℂ) • B := by ext i j; simp [Complex.real_smul]
    rw [this]
    exact (show B.PosSemidef from hB).smul (by exact_mod_cast ht)
  have h := rpow_inv_card_re_det_add_le hsA htB
  rw [rpow_inv_card_re_det_smul hA hs, rpow_inv_card_re_det_smul hB ht] at h
  simpa [smul_eq_mul] using h

end

end SGPT.Foundations.Analysis.Pending.MinkowskiDeterminant
