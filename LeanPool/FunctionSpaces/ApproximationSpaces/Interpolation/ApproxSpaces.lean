/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.Reiteration

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Approximation spaces as interpolation spaces

For every approximation scheme `A` in `X`, every `s ≥ 0` and `1 ≤ q ≤ ∞`, the couple `(X, A^s_q)`
(`ApproximationScheme.leftApproxCouple`, with the norm of `X` and the dyadic quasi-norm of
`A^s_q`) is quasi-normed and homogeneous.  For the couple `(X, A^r_∞)`
(`ApproximationScheme.reprCouple`), `0 < s < r` and `1 ≤ q ≤ ∞`

`A^s_q = (X, A^r_∞)_{s/r,q}`

(Pietsch 1981; DeVore–Popov, LNM 1302 (1988);
`ApproximationScheme.memApprox_iff_memKMethod_reprCouple`).  The proof uses the scheme alone:
Jackson's half is `E_{2^(k+1)}(f) ≤ K(2^(-kr), f)`
(`ApproximationScheme.approxError_le_kFunctional_reprCouple`), and Bernstein's half takes
near-best approximants `a_k ∈ A_{2^k}`, whose norm in `A^r_∞` is at most a finite sum, since
`E_{2^j}(a_k) = 0` for `j ≥ k` (`ApproximationScheme.interpNorm_reprCouple_le_approxNormDyadic`,
with the constant `ApproximationScheme.devorePopovConst`).

With the reiteration theorem of `ApproximationSpaces.Interpolation.Reiteration` this gives the
**reiteration of approximation spaces**: for `0 < s₀ < s₁`, `0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`,
`(A^{s₀}_{q₀}, A^{s₁}_{q₁})_{η,q} = A^{(1-η)s₀+ηs₁}_q` and `(X, A^{s₁}_{q₁})_{η,q} = A^{ηs₁}_q`
(`ApproximationScheme.memKMethod_approxCouple_iff`,
`ApproximationScheme.memKMethod_approxCouple_zero_iff`), and the **sandwich principle**: a couple
whose norms lie between two dyadic quasi-norms of the same smoothness has the corresponding
approximation spaces as interpolation spaces
(`ApproximationScheme.memKMethod_iff_memApprox_of_sandwich`,
`ApproximationScheme.memKMethod_iff_memApprox_of_two_sandwiches`).  For a smoothness space with
Jackson's and Bernstein's inequalities this gives the representation theorem once more
(`ApproximationScheme.memKMethod_ofMap_iff_memApprox`).  The exponent `(1-η)s₀ + ηs₁` lies
in `(0, θ)` whenever `0 < s₀ < s₁ < θ` (`ApproximationScheme.reiterationExponent_pos`,
`ApproximationScheme.reiterationExponent_lt`).
-/

@[expose] public section

open Finset
open scoped ENNReal
open ENNReal (lqNorm dyadicWeight)

namespace ApproximationScheme

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {A : ApproximationScheme X} {r s s₀ s₁ η θ : ℝ} {q q₀ q₁ : ℝ≥0∞}

/-! ### The couples `(X, A^s_q)` and `(X, A^r_∞)` -/

variable (A) in
/-- The **couple `(X, A^s_q)`** of the scheme: the norm `‖f‖` of `X` and the dyadic quasi-norm
`‖f‖ + ‖(2^(ks) E_{2^k}(f))_k‖_{ℓ_q}` of `A^s_q`.  Its interpolation spaces are the
approximation spaces `A^{ηs}_q`, `0 < η < 1` (`memKMethod_approxCouple_zero_iff`). -/
noncomputable def leftApproxCouple (s : ℝ) (q : ℝ≥0∞) : InterpCouple X :=
  ⟨fun f => ‖f‖ₑ, A.approxNormDyadic s q⟩

/-- The first norm of `(X, A^s_q)` is the norm of `X`. -/
@[simp]
theorem leftApproxCouple_norm0 (f : X) : (A.leftApproxCouple s q).norm0 f = ‖f‖ₑ := rfl

/-- The second norm of `(X, A^s_q)` is the dyadic quasi-norm of `A^s_q`. -/
@[simp]
theorem leftApproxCouple_norm1 (f : X) :
    (A.leftApproxCouple s q).norm1 f = A.approxNormDyadic s q f := rfl

/-- For `s ≥ 0` and `q ≥ 1` the couple `(X, A^s_q)` is quasi-normed with constant `2 · 2^s`
(`approxNormDyadic_add_le`). -/
theorem isQuasiNormed_leftApproxCouple (hs : 0 ≤ s) (hq : 1 ≤ q) :
    (A.leftApproxCouple s q).IsQuasiNormed (2 * 2 ^ s) where
  ne_top := ENNReal.mul_ne_top (by norm_num) (ENNReal.two_rpow_ne_top s)
  norm0_zero := eNorm_zero
  norm1_zero := approxNormDyadic_zero s q
  norm0_neg a := eNorm_neg a
  norm1_neg a := approxNormDyadic_neg a
  norm0_add_le a b :=
    (eNorm_add_le a b).trans (le_mul_of_one_le_left' (ENNReal.one_le_two_mul_two_rpow hs))
  norm1_add_le := approxNormDyadic_add_le hq hs

/-- The couple `(X, A^s_q)` is homogeneous (`approxNormDyadic_smul`). -/
theorem isHomogeneous_leftApproxCouple : (A.leftApproxCouple s q).IsHomogeneous where
  norm0_smul_le c a := (eNorm_smul c a).le
  norm1_smul_le c a := (approxNormDyadic_smul c a).le

variable (A) in
/-- The **couple `(X, A^r_∞)`** of the scheme, `leftApproxCouple r ∞`: the norm `‖f‖` of `X` and
the dyadic quasi-norm `‖f‖ + sup_k 2^(kr) E_{2^k}(f)` of `A^r_∞`.  Its interpolation spaces are
the approximation spaces `A^s_q`, `0 < s < r` (`memApprox_iff_memKMethod_reprCouple`). -/
noncomputable def reprCouple (r : ℝ) : InterpCouple X :=
  A.leftApproxCouple r ∞

/-- The first norm of `(X, A^r_∞)` is the norm of `X`. -/
@[simp]
theorem reprCouple_norm0 (f : X) : (A.reprCouple r).norm0 f = ‖f‖ₑ := rfl

/-- The second norm of `(X, A^r_∞)` is the dyadic quasi-norm of `A^r_∞`. -/
@[simp]
theorem reprCouple_norm1 (f : X) : (A.reprCouple r).norm1 f = A.approxNormDyadic r ∞ f := rfl

/-- For `r ≥ 0` the couple `(X, A^r_∞)` is quasi-normed with constant `2 · 2^r`. -/
theorem isQuasiNormed_reprCouple (hr : 0 ≤ r) : (A.reprCouple r).IsQuasiNormed (2 * 2 ^ r) :=
  isQuasiNormed_leftApproxCouple hr le_top

/-- The couple `(X, A^r_∞)` is homogeneous. -/
theorem isHomogeneous_reprCouple : (A.reprCouple r).IsHomogeneous :=
  isHomogeneous_leftApproxCouple

/-- The couple `(X, A^r_∞)` is ordered: `‖f‖ ≤ 1 · ‖f‖_{A^r_∞}`. -/
theorem norm0_reprCouple_le (f : X) : (A.reprCouple r).norm0 f ≤ 1 * (A.reprCouple r).norm1 f := by
  rw [one_mul]
  exact enorm_le_approxNormDyadic f

/-! ### Jackson's half -/

/-- One term of the dyadic quasi-norm of `A^r_∞`: `E_{2^k}(b) ≤ 2^(-kr) ‖b‖_{A^r_∞}`. -/
theorem approxError_pow_le_dyadicWeight_mul (b : X) (k : ℕ) :
    A.approxError b (2 ^ k) ≤ dyadicWeight (-r) k * A.approxNormDyadic r ∞ b :=
  (approxError_pow_le (s := r) ENNReal.top_ne_zero b k).trans
    (by gcongr; exact lqNorm_le_approxNormDyadic b)

/-- **Jackson's inequality for the couple `(X, A^r_∞)`**: `E_{2^(k+1)}(f) ≤ K(2^(-kr), f)`, since
`E_{2^(k+1)}(f) ≤ E_{2^k}(f - b) + E_{2^k}(b) ≤ ‖f - b‖ + 2^(-kr) ‖b‖_{A^r_∞}` for every `b`. -/
theorem approxError_le_kFunctional_reprCouple (f : X) (k : ℕ) :
    A.approxError f (2 ^ (k + 1)) ≤ (A.reprCouple r).kFunctional (dyadicWeight (-r) k) f := by
  unfold InterpCouple.kFunctional
  refine le_iInf fun b => ?_
  calc A.approxError f (2 ^ (k + 1)) = A.approxError ((f - b) + b) (2 ^ (k + 1)) := by
        rw [sub_add_cancel]
    _ ≤ A.approxError (f - b) (2 ^ k) + A.approxError b (2 ^ k) := approxError_add_le_pow_succ k _ _
    _ ≤ ‖f - b‖ₑ + dyadicWeight (-r) k * A.approxNormDyadic r ∞ b :=
        add_le_add (approxError_le_enorm _ _) (approxError_pow_le_dyadicWeight_mul b k)

/-- **Jackson's half of `A^s_q = (X, A^r_∞)_{s/r,q}`**: for `s ≥ 0`, `r ≠ 0` and `q ≥ 1`,
`‖f‖_{A^s_q} ≤ 2 · 2^s (‖f‖ + ‖(2^(ks) K(2^(-kr), f))_k‖_{ℓ_q})`, the dyadic quasi-norm against
the norm of the couple `(X, A^r_∞)` on the grid `t = 2^(-kr)`. -/
theorem approxNormDyadic_le_interpNorm_reprCouple (hs : 0 ≤ s) (hr : r ≠ 0) (hq : 1 ≤ q)
    (f : X) :
    A.approxNormDyadic s q f ≤ 2 * 2 ^ s * (A.reprCouple r).interpNorm (s / r) r q f := by
  have hshift : lqNorm q (fun k => A.approxSeqDyadic s f (k + 1)) ≤ 2 ^ s *
      lqNorm q (fun k : ℕ => dyadicWeight (r * (s / r)) k *
        (A.reprCouple r).kFunctional (dyadicWeight (-r) k) f) := by
    rw [← ENNReal.lqNorm_const_mul]
    refine ENNReal.lqNorm_mono fun k => ?_
    rw [approxSeqDyadic, ENNReal.dyadicWeight_succ, mul_div_cancel₀ s hr, mul_assoc]
    gcongr
    exact approxError_le_kFunctional_reprCouple f k
  calc A.approxNormDyadic s q f = ‖f‖ₑ + lqNorm q (A.approxSeqDyadic s f) := rfl
    _ ≤ ‖f‖ₑ + (‖f‖ₑ + 2 ^ s * lqNorm q (fun k : ℕ => dyadicWeight (r * (s / r)) k *
          (A.reprCouple r).kFunctional (dyadicWeight (-r) k) f)) := by
        gcongr
        refine (ENNReal.lqNorm_le_head_add_shift hq _).trans (add_le_add ?_ hshift)
        rw [approxSeqDyadic_zero]
        exact approxError_le_enorm f 1
    _ ≤ 2 * 2 ^ s * ‖f‖ₑ + 2 * 2 ^ s * lqNorm q (fun k : ℕ => dyadicWeight (r * (s / r)) k *
          (A.reprCouple r).kFunctional (dyadicWeight (-r) k) f) := by
        rw [← add_assoc, ← two_mul]
        gcongr
        · exact le_mul_of_one_le_right' (ENNReal.one_le_two_rpow hs)
        · exact le_mul_of_one_le_left' one_le_two
    _ = 2 * 2 ^ s * (A.reprCouple r).interpNorm (s / r) r q f := by
        rw [InterpCouple.interpNorm, mul_add]
        rfl

/-! ### Bernstein's half -/

/-- **One term of the interpolation norm of `(X, A^r_∞)` by near-best approximants**: for `s ≥ 0`,
`r ≠ 0` and near-best approximants `a_k` with the tolerances `t_k = tolerance f s k`,
`2^(ks) K(2^(-kr), f) ≤ (2^(ks) E_{2^k}(f) + 2^(ks) t_k) + 3 ‖f‖ 2^(-k(r-s))
+ 2 · 2^(-k(r-s)) ∑_{j ≤ k} 2^(jr) (E_{2^j}(f) + t_j)`, from
`K(2^(-kr), f) ≤ ‖f - a_k‖ + 2^(-kr) ‖a_k‖_{A^r_∞}`. -/
theorem dyadicWeight_mul_kFunctional_reprCouple_le (hs : 0 ≤ s) (hr : r ≠ 0) {f : X}
    (D : A.DyadicApprox f (tolerance f s)) (k : ℕ) :
    dyadicWeight (r * (s / r)) k * (A.reprCouple r).kFunctional (dyadicWeight (-r) k) f ≤
      (A.approxSeqDyadic s f k + dyadicWeight s k * tolerance f s k) +
        (3 * ‖f‖ₑ * dyadicWeight (-(r - s)) k + 2 * (dyadicWeight (-(r - s)) k *
          ∑ j ∈ range (k + 1),
            dyadicWeight r j * (A.approxError f (2 ^ j) + tolerance f s j))) := by
  have hK : (A.reprCouple r).kFunctional (dyadicWeight (-r) k) f ≤
      (A.approxError f (2 ^ k) + tolerance f s k) + dyadicWeight (-r) k * (3 * ‖f‖ₑ + 2 *
        ∑ j ∈ range (k + 1), dyadicWeight r j * (A.approxError f (2 ^ j) + tolerance f s j)) := by
    refine (InterpCouple.kFunctional_le (D.a k) f).trans ?_
    gcongr
    · exact D.eNorm_sub_le k
    · exact D.approxNormDyadic_top_le (tolerance_anti f hs) (tolerance_zero f s).le k
  have hw : dyadicWeight s k * dyadicWeight (-r) k = dyadicWeight (-(r - s)) k := by
    rw [← ENNReal.dyadicWeight_add]
    congr 1
    ring
  rw [mul_div_cancel₀ s hr]
  calc dyadicWeight s k * (A.reprCouple r).kFunctional (dyadicWeight (-r) k) f
      ≤ dyadicWeight s k * ((A.approxError f (2 ^ k) + tolerance f s k) +
          dyadicWeight (-r) k * (3 * ‖f‖ₑ + 2 * ∑ j ∈ range (k + 1),
            dyadicWeight r j * (A.approxError f (2 ^ j) + tolerance f s j))) := by gcongr
    _ = _ := by
        simp only [approxSeqDyadic, mul_add, ← mul_assoc, hw]
        ring

/-- **The `ℓ_q` part of the interpolation norm of `(X, A^r_∞)`**: for `0 ≤ s < r`, `q ≥ 1` and
near-best approximants with the tolerances `tolerance f s`,
`‖(2^(ks) K(2^(-kr), f))_k‖_{ℓ_q} ≤ (D + 2 ‖f‖) + 3 ‖f‖ c_{r-s} + 2 c_{r-s} (D + 2 ‖f‖)`, where
`D = ‖(2^(ks) E_{2^k}(f))_k‖_{ℓ_q}` and `c_{r-s} = (1 - 2^(-(r-s)))⁻¹`
(`lqNorm_le_of_le_partialSums` with `B = 3 ‖f‖` and `K = 2`). -/
theorem lqNorm_kFunctional_reprCouple_le (hs : 0 ≤ s) (hsr : s < r) (hq : 1 ≤ q) {f : X}
    (D : A.DyadicApprox f (tolerance f s)) :
    lqNorm q (fun k : ℕ => dyadicWeight (r * (s / r)) k *
        (A.reprCouple r).kFunctional (dyadicWeight (-r) k) f) ≤
      (lqNorm q (A.approxSeqDyadic s f) + 2 * ‖f‖ₑ) +
        (3 * ‖f‖ₑ * (1 - (2 : ℝ≥0∞) ^ (-(r - s)))⁻¹ +
          2 * ((1 - (2 : ℝ≥0∞) ^ (-(r - s)))⁻¹ * (lqNorm q (A.approxSeqDyadic s f) + 2 * ‖f‖ₑ))) :=
  lqNorm_le_of_le_partialSums hq
    (dyadicWeight_mul_kFunctional_reprCouple_le hs (hs.trans_lt hsr).ne' D)

/-- The constant `3 + 7 (1 - 2^(-(r-s)))⁻¹` of the proof here of Bernstein's half of the theorem
`A^s_q = (X, A^r_∞)_{s/r,q}` of DeVore–Popov, LNM 1302 (1988). -/
noncomputable def devorePopovConst (r s : ℝ) : ℝ≥0∞ :=
  3 + 7 * (1 - (2 : ℝ≥0∞) ^ (-(r - s)))⁻¹

/-- The constant `devorePopovConst r s` is finite for `s < r`. -/
theorem devorePopovConst_ne_top (h : s < r) : devorePopovConst r s ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨by norm_num, ENNReal.mul_ne_top (by norm_num)
    (ENNReal.one_sub_two_rpow_neg_inv_ne_top (sub_pos.2 h))⟩

/-- **Bernstein's half of `A^s_q = (X, A^r_∞)_{s/r,q}`** (DeVore–Popov, LNM 1302 (1988)): for
`0 ≤ s < r` and `q ≥ 1`,
`‖f‖ + ‖(2^(ks) K(2^(-kr), f))_k‖_{ℓ_q} ≤ devorePopovConst r s · ‖f‖_{A^s_q}`.  The near-best
approximants themselves lie in `A^r_∞` and take the place of the lifts of the representation
theorem (`enorm_add_le_mul_approxNormDyadic` with `B = 3` and `K = 2`). -/
theorem interpNorm_reprCouple_le_approxNormDyadic (hs : 0 ≤ s) (hsr : s < r) (hq : 1 ≤ q)
    (f : X) :
    (A.reprCouple r).interpNorm (s / r) r q f ≤
      devorePopovConst r s * A.approxNormDyadic s q f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [InterpCouple.interpNorm_zero eNorm_zero (approxNormDyadic_zero r ∞)]
    exact zero_le
  obtain ⟨D⟩ := exists_dyadicApprox A f (tolerance_ne_zero hf0 s)
  calc (A.reprCouple r).interpNorm (s / r) r q f
      = ‖f‖ₑ + lqNorm q (fun k : ℕ => dyadicWeight (r * (s / r)) k *
          (A.reprCouple r).kFunctional (dyadicWeight (-r) k) f) := rfl
    _ ≤ (3 + (3 + 2 * 2) * (1 - (2 : ℝ≥0∞) ^ (-(r - s)))⁻¹) * A.approxNormDyadic s q f :=
        enorm_add_le_mul_approxNormDyadic (lqNorm_kFunctional_reprCouple_le hs hsr hq D)
    _ = devorePopovConst r s * A.approxNormDyadic s q f := by
        rw [devorePopovConst]
        ring

/-! ### Approximation spaces are interpolation spaces -/

/-- **Approximation spaces are interpolation spaces** (Pietsch 1981; DeVore–Popov, LNM 1302
(1988)): for every scheme, `0 < s < r` and `1 ≤ q ≤ ∞`, `A^s_q = (X, A^r_∞)_{s/r,q}`, the real
interpolation space of the continuous K-method of the couple `(X, A^r_∞)`. -/
theorem memApprox_iff_memKMethod_reprCouple (hs : 0 < s) (hsr : s < r) (hq : 1 ≤ q) {f : X} :
    A.MemApprox s q f ↔ (A.reprCouple r).MemKMethod (s / r) q f := by
  have hr : 0 < r := hs.trans hsr
  rw [memApprox_iff_approxNormDyadic_lt_top hq hs.le,
    InterpCouple.memKMethod_iff_interpNorm_lt_top (isQuasiNormed_reprCouple hr.le)
      ENNReal.one_ne_top norm0_reprCouple_le (div_pos hs hr) hr (zero_lt_one.trans_le hq).ne']
  exact ⟨fun h => (interpNorm_reprCouple_le_approxNormDyadic hs.le hsr hq f).trans_lt
      (ENNReal.mul_lt_top (devorePopovConst_ne_top hsr).lt_top h),
    fun h => (approxNormDyadic_le_interpNorm_reprCouple hs.le hr.ne' hq f).trans_lt
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (ENNReal.two_rpow_ne_top s).lt_top) h)⟩

/-- **Approximation spaces are interpolation spaces**, as an equality of subspaces: for
`0 < s < r` and `1 ≤ q ≤ ∞`, the real interpolation space `(X, A^r_∞)_{s/r,q}` is `A^s_q`. -/
theorem kMethodSpace_reprCouple (hs : 0 < s) (hsr : s < r) (hq : 1 ≤ q) :
    InterpCouple.kMethodSpace (isQuasiNormed_reprCouple (A := A) (hs.trans hsr).le)
      isHomogeneous_reprCouple (s / r) q = A.approxSpace s q hs.le hq :=
  Submodule.ext fun _ => (memApprox_iff_memKMethod_reprCouple hs hsr hq).symm

/-- The constant `2 · 2^s (1 + 2 · 2^r) 2^s (r log 2)^(-1/q)` of the bound of the dyadic
quasi-norm of `A^s_q` by the continuous K-norm of `(X, A^r_∞)`. -/
noncomputable def reprLowerConst (r s : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  2 * 2 ^ s * ((1 + 2 * 2 ^ r) * (2 ^ s * (ENNReal.ofReal (r * Real.log 2) ^ (1 / q.toReal))⁻¹))

/-- The constant `reprLowerConst r s q` is finite for `r > 0`. -/
theorem reprLowerConst_ne_top (hr : 0 < r) (s : ℝ) (q : ℝ≥0∞) : reprLowerConst r s q ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.two_rpow_ne_top s))
    (ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      ENNReal.mul_ne_top (by norm_num) (ENNReal.two_rpow_ne_top r)⟩)
      (ENNReal.mul_ne_top (ENNReal.two_rpow_ne_top s)
        (ENNReal.inv_ne_top.2 (ofReal_mul_log_two_rpow_ne_zero hr q))))

/-- **The dyadic quasi-norm of `A^s_q` by the continuous K-norm of `(X, A^r_∞)`**: for `s ≥ 0`,
`r > 0` and `q ≥ 1`, `‖f‖_{A^s_q} ≤ reprLowerConst r s q · ‖f‖_{K,s/r,q}`. -/
theorem approxNormDyadic_le_kMethodNorm_reprCouple (hs : 0 ≤ s) (hr : 0 < r) (hq : 1 ≤ q)
    (f : X) :
    A.approxNormDyadic s q f ≤ reprLowerConst r s q * (A.reprCouple r).kMethodNorm (s / r) q f := by
  have h := InterpCouple.interpNorm_le_kMethodNorm (isQuasiNormed_reprCouple (A := A) hr.le)
    ENNReal.one_ne_top norm0_reprCouple_le (div_nonneg hs hr.le) hr (zero_lt_one.trans_le hq).ne'
    f
  rw [mul_div_cancel₀ s hr.ne', max_self, mul_one] at h
  calc A.approxNormDyadic s q f ≤ 2 * 2 ^ s * (A.reprCouple r).interpNorm (s / r) r q f :=
        approxNormDyadic_le_interpNorm_reprCouple hs hr.ne' hq f
    _ ≤ 2 * 2 ^ s * ((1 + 2 * 2 ^ r) * (2 ^ s *
          (ENNReal.ofReal (r * Real.log 2) ^ (1 / q.toReal))⁻¹) *
            (A.reprCouple r).kMethodNorm (s / r) q f) := by gcongr
    _ = reprLowerConst r s q * (A.reprCouple r).kMethodNorm (s / r) q f := by
        rw [reprLowerConst]
        ring

/-- The constant `kMethodUpperConst (s/r) r q · devorePopovConst r s` of the bound of the
continuous K-norm of `(X, A^r_∞)` by the dyadic quasi-norm of `A^s_q`. -/
noncomputable def reprUpperConst (r s : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  kMethodUpperConst (s / r) r q * devorePopovConst r s

/-- The constant `reprUpperConst r s q` is finite for `0 < s < r`. -/
theorem reprUpperConst_ne_top (hs : 0 < s) (hsr : s < r) (q : ℝ≥0∞) :
    reprUpperConst r s q ≠ ∞ :=
  ENNReal.mul_ne_top (kMethodUpperConst_ne_top (div_pos hs (hs.trans hsr)) (hs.trans hsr) q)
    (devorePopovConst_ne_top hsr)

/-- **The continuous K-norm of `(X, A^r_∞)` by the dyadic quasi-norm of `A^s_q`**: for
`0 < s < r` and `q ≥ 1`, `‖f‖_{K,s/r,q} ≤ reprUpperConst r s q · ‖f‖_{A^s_q}`. -/
theorem kMethodNorm_reprCouple_le_approxNormDyadic (hs : 0 < s) (hsr : s < r) (hq : 1 ≤ q)
    (f : X) :
    (A.reprCouple r).kMethodNorm (s / r) q f ≤ reprUpperConst r s q * A.approxNormDyadic s q f :=
  calc (A.reprCouple r).kMethodNorm (s / r) q f
      ≤ kMethodUpperConst (s / r) r q * (A.reprCouple r).interpNorm (s / r) r q f :=
        InterpCouple.kMethodNorm_le_interpNorm
          (isQuasiNormed_reprCouple (A := A) (hs.trans hsr).le).norm1_zero
          (div_pos hs (hs.trans hsr)).le (hs.trans hsr) f
    _ ≤ kMethodUpperConst (s / r) r q * (devorePopovConst r s * A.approxNormDyadic s q f) := by
        gcongr
        exact interpNorm_reprCouple_le_approxNormDyadic hs.le hsr hq f
    _ = reprUpperConst r s q * A.approxNormDyadic s q f := by rw [reprUpperConst, mul_assoc]

/-- **The dyadic quasi-norm of `A^s_q` by the discrete K-norm of `(X, A^r_∞)` on the grid
`t = 2^n`**: for `s ≥ 0`, `r > 0` and `q ≥ 1`,
`‖f‖_{A^s_q} ≤ reprLowerConst r s q (log 2)^(1/q) 2^(s/r) ‖(2^(-ns/r) K(2^n, f))_{n ∈ ℤ}‖_{ℓ_q}`
(`InterpCouple.kMethodNorm_le_mul_discreteKMethodNorm`). -/
theorem approxNormDyadic_le_discreteKMethodNorm_reprCouple (hs : 0 ≤ s) (hr : 0 < r)
    (hq : 1 ≤ q) (f : X) :
    A.approxNormDyadic s q f ≤ reprLowerConst r s q *
      (ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) * 2 ^ (s / r)) *
        (A.reprCouple r).discreteKMethodNorm (s / r) 1 q f := by
  rw [mul_assoc]
  exact (approxNormDyadic_le_kMethodNorm_reprCouple hs hr hq f).trans
    (by gcongr; exact InterpCouple.kMethodNorm_le_mul_discreteKMethodNorm (div_nonneg hs hr.le) f)

/-- **The discrete K-norm of `(X, A^r_∞)` on the grid `t = 2^n` by the dyadic quasi-norm of
`A^s_q`**: for `0 < s < r` and `q ≥ 1`,
`‖(2^(-ns/r) K(2^n, f))_{n ∈ ℤ}‖_{ℓ_q} ≤ ((log 2)^(1/q) 2^(-s/r))⁻¹ reprUpperConst r s q
‖f‖_{A^s_q}` (`InterpCouple.discreteKMethodNorm_le_mul_kMethodNorm`). -/
theorem discreteKMethodNorm_reprCouple_le_approxNormDyadic (hs : 0 < s) (hsr : s < r)
    (hq : 1 ≤ q) (f : X) :
    (A.reprCouple r).discreteKMethodNorm (s / r) 1 q f ≤
      (ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) * 2 ^ (-(s / r)))⁻¹ * reprUpperConst r s q *
        A.approxNormDyadic s q f := by
  rw [mul_assoc]
  exact (InterpCouple.discreteKMethodNorm_le_mul_kMethodNorm (div_pos hs (hs.trans hsr)).le f).trans
    (by gcongr; exact kMethodNorm_reprCouple_le_approxNormDyadic hs hsr hq f)

/-! ### Reiteration of approximation spaces -/

variable (A) in
/-- The **couple `(A^{s₀}_{q₀}, A^{s₁}_{q₁})`** of two approximation spaces, with their dyadic
quasi-norms. -/
noncomputable def approxCouple (s₀ : ℝ) (q₀ : ℝ≥0∞) (s₁ : ℝ) (q₁ : ℝ≥0∞) : InterpCouple X :=
  ⟨A.approxNormDyadic s₀ q₀, A.approxNormDyadic s₁ q₁⟩

/-- For `s₀, s₁ ≥ 0` and `q₀, q₁ ≥ 1` the couple `(A^{s₀}_{q₀}, A^{s₁}_{q₁})` is quasi-normed with
constant `2 · 2^max(s₀, s₁)` (`approxNormDyadic_add_le`). -/
theorem isQuasiNormed_approxCouple (hs₀ : 0 ≤ s₀) (hs₁ : 0 ≤ s₁) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) :
    (A.approxCouple s₀ q₀ s₁ q₁).IsQuasiNormed (2 * 2 ^ max s₀ s₁) where
  ne_top := ENNReal.mul_ne_top (by norm_num) (ENNReal.two_rpow_ne_top _)
  norm0_zero := approxNormDyadic_zero s₀ q₀
  norm1_zero := approxNormDyadic_zero s₁ q₁
  norm0_neg a := approxNormDyadic_neg a
  norm1_neg a := approxNormDyadic_neg a
  norm0_add_le a b := (approxNormDyadic_add_le hq₀ hs₀ a b).trans (mul_le_mul_left
    (mul_le_mul_right (ENNReal.rpow_le_rpow_of_exponent_le one_le_two (le_max_left _ _)) _) _)
  norm1_add_le a b := (approxNormDyadic_add_le hq₁ hs₁ a b).trans (mul_le_mul_left
    (mul_le_mul_right (ENNReal.rpow_le_rpow_of_exponent_le one_le_two (le_max_right _ _)) _) _)

/-- The couple `(A^{s₀}_{q₀}, A^{s₁}_{q₁})` is homogeneous (`approxNormDyadic_smul`). -/
theorem isHomogeneous_approxCouple : (A.approxCouple s₀ q₀ s₁ q₁).IsHomogeneous where
  norm0_smul_le c a := (approxNormDyadic_smul c a).le
  norm1_smul_le c a := (approxNormDyadic_smul c a).le

/-- **The reiteration exponent is positive**: for `0 < s₀ < s₁` and `0 < η < 1`,
`0 < (1-η)s₀ + ηs₁`. -/
theorem reiterationExponent_pos (hs₀ : 0 < s₀) (hs : s₀ < s₁) (hη : 0 < η) (hη' : η < 1) :
    0 < (1 - η) * s₀ + η * s₁ :=
  add_pos (mul_pos (sub_pos.2 hη') hs₀) (mul_pos hη (hs₀.trans hs))

/-- **The reiteration exponent stays below every bound of `s₁`**: for `s₀ < s₁ < θ` and
`η < 1`, `(1-η)s₀ + ηs₁ = s₁ - (1-η)(s₁ - s₀)` is at most `s₁`, hence `< θ`. -/
theorem reiterationExponent_lt (hs : s₀ < s₁) (hs₁ : s₁ < θ) (hη' : η < 1) :
    (1 - η) * s₀ + η * s₁ < θ :=
  calc (1 - η) * s₀ + η * s₁ ≤ (1 - η) * s₁ + η * s₁ := by gcongr
    _ = s₁ := by ring
    _ < θ := hs₁

/-- **The reiteration theorem for approximation spaces** (DeVore–Lorentz, Chapter 7; Pietsch
1981; DeVore–Popov, LNM 1302 (1988)): for `0 < s₀ < s₁`, `0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`,
`(A^{s₀}_{q₀}, A^{s₁}_{q₁})_{η,q} = A^{(1-η)s₀+ηs₁}_q`.  The proof represents both spaces in the
couple `(X, A^r_∞)` with `r = s₁ + 1` and applies `InterpCouple.memKMethod_kCouple_iff`. -/
theorem memKMethod_approxCouple_iff (hs₀ : 0 < s₀) (hs : s₀ < s₁) (hη : 0 < η) (hη' : η < 1)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) {f : X} :
    (A.approxCouple s₀ q₀ s₁ q₁).MemKMethod η q f ↔ A.MemApprox ((1 - η) * s₀ + η * s₁) q f := by
  have hs₁ : 0 < s₁ := hs₀.trans hs
  have hr : 0 < s₁ + 1 := by linarith
  have hsr₀ : s₀ < s₁ + 1 := by linarith
  have hsr₁ : s₁ < s₁ + 1 := by linarith
  have hθ : 0 < (1 - η) * s₀ + η * s₁ := reiterationExponent_pos hs₀ hs hη hη'
  have hθr : (1 - η) * s₀ + η * s₁ < s₁ + 1 := reiterationExponent_lt hs hsr₁ hη'
  rw [memApprox_iff_memKMethod_reprCouple hθ hθr hq,
    show ((1 - η) * s₀ + η * s₁) / (s₁ + 1) = (1 - η) * (s₀ / (s₁ + 1)) + η * (s₁ / (s₁ + 1)) by
      ring,
    ← InterpCouple.memKMethod_kCouple_iff (θ₀ := s₀ / (s₁ + 1)) (θ₁ := s₁ / (s₁ + 1))
      (isQuasiNormed_reprCouple hr.le) (div_pos hs₀ hr) (div_lt_div_of_pos_right hs hr)
      ((div_lt_one hr).2 hsr₁) hη hη' hq₀ hq₁ hq]
  exact InterpCouple.memKMethod_congr (A := A.approxCouple s₀ q₀ s₁ q₁)
    (B := (A.reprCouple (s₁ + 1)).kCouple (s₀ / (s₁ + 1)) q₀ (s₁ / (s₁ + 1)) q₁)
    (ENNReal.mul_ne_top (inv_log_two_rpow_mul_two_rpow_ne_top _ q₀)
      (reprUpperConst_ne_top hs₀ hsr₀ q₀))
    (ENNReal.mul_ne_top (inv_log_two_rpow_mul_two_rpow_ne_top _ q₁)
      (reprUpperConst_ne_top hs₁ hsr₁ q₁))
    (ENNReal.mul_ne_top (reprLowerConst_ne_top hr _ q₀) (log_two_rpow_mul_two_rpow_ne_top _ q₀))
    (ENNReal.mul_ne_top (reprLowerConst_ne_top hr _ q₁) (log_two_rpow_mul_two_rpow_ne_top _ q₁))
    (discreteKMethodNorm_reprCouple_le_approxNormDyadic hs₀ hsr₀ hq₀)
    (discreteKMethodNorm_reprCouple_le_approxNormDyadic hs₁ hsr₁ hq₁)
    (approxNormDyadic_le_discreteKMethodNorm_reprCouple hs₀.le hr hq₀)
    (approxNormDyadic_le_discreteKMethodNorm_reprCouple hs₁.le hr hq₁)

/-- **The reiteration theorem for approximation spaces at the left endpoint**: for `s₁ > 0`,
`0 < η < 1` and `1 ≤ q₁, q ≤ ∞`, `(X, A^{s₁}_{q₁})_{η,q} = A^{ηs₁}_q`, for the couple
`leftApproxCouple s₁ q₁` of the norm of `X` and the dyadic quasi-norm of `A^{s₁}_{q₁}`. -/
theorem memKMethod_approxCouple_zero_iff (hs₁ : 0 < s₁) (hη : 0 < η) (hη' : η < 1)
    (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) {f : X} :
    (A.leftApproxCouple s₁ q₁).MemKMethod η q f ↔ A.MemApprox (η * s₁) q f := by
  have hr : 0 < s₁ + 1 := by linarith
  have hsr₁ : s₁ < s₁ + 1 := by linarith
  have hθr : η * s₁ < s₁ + 1 := by nlinarith
  rw [memApprox_iff_memKMethod_reprCouple (mul_pos hη hs₁) hθr hq,
    show η * s₁ / (s₁ + 1) = η * (s₁ / (s₁ + 1)) by ring,
    ← InterpCouple.memKMethod_leftKCouple_iff (θ₁ := s₁ / (s₁ + 1))
      (isQuasiNormed_reprCouple hr.le) (div_pos hs₁ hr) ((div_lt_one hr).2 hsr₁) hη.le hη' hq₁
      hq]
  exact InterpCouple.memKMethod_congr (A := A.leftApproxCouple s₁ q₁)
    (B := (A.reprCouple (s₁ + 1)).leftKCouple (s₁ / (s₁ + 1)) q₁) ENNReal.one_ne_top
    (ENNReal.mul_ne_top (inv_log_two_rpow_mul_two_rpow_ne_top _ q₁)
      (reprUpperConst_ne_top hs₁ hsr₁ q₁))
    ENNReal.one_ne_top
    (ENNReal.mul_ne_top (reprLowerConst_ne_top hr _ q₁) (log_two_rpow_mul_two_rpow_ne_top _ q₁))
    (fun a => (one_mul ‖a‖ₑ).ge)
    (discreteKMethodNorm_reprCouple_le_approxNormDyadic hs₁ hsr₁ hq₁)
    (fun a => (one_mul ‖a‖ₑ).ge)
    (approxNormDyadic_le_discreteKMethodNorm_reprCouple hs₁.le hr hq₁)

/-- **The reiteration theorem for approximation spaces**, as an equality of subspaces: for
`0 < s₀ < s₁`, `0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`, the real interpolation space
`(A^{s₀}_{q₀}, A^{s₁}_{q₁})_{η,q}` is `A^{(1-η)s₀+ηs₁}_q`. -/
theorem kMethodSpace_approxCouple (hs₀ : 0 < s₀) (hs : s₀ < s₁) (hη : 0 < η) (hη' : η < 1)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) :
    InterpCouple.kMethodSpace (isQuasiNormed_approxCouple (A := A) hs₀.le (hs₀.trans hs).le hq₀ hq₁)
      isHomogeneous_approxCouple η q =
      A.approxSpace ((1 - η) * s₀ + η * s₁) q (reiterationExponent_pos hs₀ hs hη hη').le hq :=
  Submodule.ext fun _ => memKMethod_approxCouple_iff hs₀ hs hη hη' hq₀ hq₁ hq

/-- **The reiteration theorem for approximation spaces at the left endpoint**, as an equality of
subspaces: for `s₁ > 0`, `0 < η < 1` and `1 ≤ q₁, q ≤ ∞`, the real interpolation space
`(X, A^{s₁}_{q₁})_{η,q}` is `A^{ηs₁}_q`. -/
theorem kMethodSpace_approxCouple_zero (hs₁ : 0 < s₁) (hη : 0 < η) (hη' : η < 1)
    (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) :
    InterpCouple.kMethodSpace (isQuasiNormed_leftApproxCouple (A := A) hs₁.le hq₁)
      isHomogeneous_leftApproxCouple η q = A.approxSpace (η * s₁) q (mul_pos hη hs₁).le hq :=
  Submodule.ext fun _ => memKMethod_approxCouple_zero_iff hs₁ hη hη' hq₁ hq

/-! ### Sandwiches -/

/-- **The sandwich principle at the left endpoint**: if a function `N₁ : X → [0, ∞]` lies between
two dyadic quasi-norms of smoothness `r > 0`, `N₁ ≤ c ‖·‖_{A^r_{q'}}` and
`‖·‖_{A^r_{q''}} ≤ c' N₁` with finite `c, c'` and `q', q'' ≥ 1`, then for `0 < θ < 1` and
`1 ≤ q ≤ ∞`, `(X, N₁)_{θ,q} = A^{θr}_q`.  Smaller norms give larger interpolation spaces
(`InterpCouple.MemKMethod.of_le`), and both outer spaces are `A^{θr}_q`
(`memKMethod_approxCouple_zero_iff`). -/
theorem memKMethod_iff_memApprox_of_sandwich {N₁ : X → ℝ≥0∞} {c c' q' q'' : ℝ≥0∞}
    (hc : c ≠ ∞) (hc' : c' ≠ ∞) (hq' : 1 ≤ q') (hq'' : 1 ≤ q'') (hr : 0 < r) (hθ : 0 < θ)
    (hθ' : θ < 1) (hq : 1 ≤ q) (h : ∀ f, N₁ f ≤ c * A.approxNormDyadic r q' f)
    (h' : ∀ f, A.approxNormDyadic r q'' f ≤ c' * N₁ f) {f : X} :
    (⟨fun f => ‖f‖ₑ, N₁⟩ : InterpCouple X).MemKMethod θ q f ↔ A.MemApprox (θ * r) q f :=
  ⟨fun hf => (memKMethod_approxCouple_zero_iff hr hθ hθ' hq'' hq).1
      (InterpCouple.MemKMethod.of_le (A := ⟨fun f => ‖f‖ₑ, N₁⟩)
        (B := A.leftApproxCouple r q'') ENNReal.one_ne_top hc'
        (fun a => (one_mul ‖a‖ₑ).ge) h' hf),
    fun hf => InterpCouple.MemKMethod.of_le (A := A.leftApproxCouple r q')
      (B := ⟨fun f => ‖f‖ₑ, N₁⟩) ENNReal.one_ne_top hc (fun a => (one_mul ‖a‖ₑ).ge) h
      ((memKMethod_approxCouple_zero_iff hr hθ hθ' hq' hq).2 hf)⟩

/-- **The sandwich principle**: if `N₀` lies between two dyadic quasi-norms of smoothness `s₀`
and `N₁` between two of smoothness `s₁`, with `0 < s₀ < s₁`, finite constants and fine indices
`≥ 1`, then for `0 < η < 1` and `1 ≤ q ≤ ∞`, `(N₀, N₁)_{η,q} = A^{(1-η)s₀+ηs₁}_q`. -/
theorem memKMethod_iff_memApprox_of_two_sandwiches {N₀ N₁ : X → ℝ≥0∞}
    {c₀ c₀' c₁ c₁' q₀' q₀'' q₁' q₁'' : ℝ≥0∞} (hc₀ : c₀ ≠ ∞) (hc₀' : c₀' ≠ ∞) (hc₁ : c₁ ≠ ∞)
    (hc₁' : c₁' ≠ ∞) (hq₀' : 1 ≤ q₀') (hq₀'' : 1 ≤ q₀'') (hq₁' : 1 ≤ q₁') (hq₁'' : 1 ≤ q₁'')
    (hs₀ : 0 < s₀) (hs : s₀ < s₁) (hη : 0 < η) (hη' : η < 1) (hq : 1 ≤ q)
    (h₀ : ∀ f, N₀ f ≤ c₀ * A.approxNormDyadic s₀ q₀' f)
    (h₀' : ∀ f, A.approxNormDyadic s₀ q₀'' f ≤ c₀' * N₀ f)
    (h₁ : ∀ f, N₁ f ≤ c₁ * A.approxNormDyadic s₁ q₁' f)
    (h₁' : ∀ f, A.approxNormDyadic s₁ q₁'' f ≤ c₁' * N₁ f) {f : X} :
    (⟨N₀, N₁⟩ : InterpCouple X).MemKMethod η q f ↔ A.MemApprox ((1 - η) * s₀ + η * s₁) q f :=
  ⟨fun hf => (memKMethod_approxCouple_iff hs₀ hs hη hη' hq₀'' hq₁'' hq).1
      (InterpCouple.MemKMethod.of_le (A := ⟨N₀, N₁⟩) (B := A.approxCouple s₀ q₀'' s₁ q₁'')
        hc₀' hc₁' h₀' h₁' hf),
    fun hf => InterpCouple.MemKMethod.of_le (A := A.approxCouple s₀ q₀' s₁ q₁') (B := ⟨N₀, N₁⟩)
      hc₀ hc₁ h₀ h₁ ((memKMethod_approxCouple_iff hs₀ hs hη hη' hq₀' hq₁' hq).2 hf)⟩

/-! ### Smoothness spaces -/

section SmoothnessSpace

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {ι : Y →L[ℝ] X} {C₁ C₂ : ℝ}

/-- **Jackson's inequality bounds `A^r_∞` by the quotient norm**: if `ι` satisfies Jackson's
inequality of order `r` with constant `C₁ ≥ 0`, then
`‖f‖_{A^r_∞} ≤ (1 + ‖ι‖ + C₁) inf {‖y‖ : ι y = f}`. -/
theorem approxNormDyadic_top_le_norm1_ofMap (hJ : JacksonBound ι A r C₁) (hC₁ : 0 ≤ C₁) (f : X) :
    A.approxNormDyadic r ∞ f ≤
      (1 + (‖ι‖ₑ + ENNReal.ofReal C₁)) * (InterpCouple.ofMap ι).norm1 f := by
  rw [InterpCouple.ofMap_norm1, ENNReal.mul_iInf_of_ne
    (by positivity)
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.add_ne_top.2 ⟨eNorm_ne_top,
      ENNReal.ofReal_ne_top⟩⟩)]
  refine le_iInf fun ⟨y, hy⟩ => ?_
  subst hy
  exact (approxNormDyadic_top_le_of_jackson hJ hC₁ y).trans (mul_le_mul_left le_add_self _)

/-- **Bernstein's inequality bounds the quotient norm by `A^r_1`**: if `Y` is complete and `ι`
satisfies a lifting bound of order `r ≥ 0` with constant `C₂ ≥ 0`, then
`inf {‖y‖ : ι y = f} ≤ (1 + 3 C₂ + 3 K) ‖f‖_{A^r_1}` with `K = liftConst C₂ r`
(`exists_preimage_of_liftBound`). -/
theorem norm1_ofMap_le_approxNormDyadic_one [CompleteSpace Y] (hB : LiftBound ι A r C₂)
    (hC₂ : 0 ≤ C₂) (hr : 0 ≤ r) (f : X) :
    (InterpCouple.ofMap ι).norm1 f ≤
      (1 + (3 * ENNReal.ofReal C₂ + 3 * liftConst C₂ r)) * A.approxNormDyadic r 1 f := by
  rcases lt_or_ge (lqNorm 1 (A.approxSeqDyadic r f)) ∞ with hf | hf
  · obtain ⟨y, hy, hyle⟩ := exists_preimage_of_liftBound hB hC₂ hr hf
    exact (InterpCouple.norm1_ofMap_le hy).trans (hyle.trans (mul_le_mul_left le_add_self _))
  · have h : A.approxNormDyadic r 1 f = ∞ := top_le_iff.1 (hf.trans le_add_self)
    rw [h, ENNReal.mul_top (by positivity)]
    exact le_top

/-- **The representation theorem through the sandwich principle**: if `Y` is complete and `ι`
satisfies Jackson's inequality and a lifting bound of order `r > 0`, then for `0 < θ < 1` and
`1 ≤ q ≤ ∞`, `(X, ι(Y))_{θ,q} = A^{θr}_q` for the couple `InterpCouple.ofMap ι`, since
`A^r_1 ⊆ ι(Y) ⊆ A^r_∞` with norms.  This is the representation theorem
`memApprox_iff_memKMethod` again, which holds for every normed space `Y`. -/
theorem memKMethod_ofMap_iff_memApprox [CompleteSpace Y] (hJ : JacksonBound ι A r C₁)
    (hC₁ : 0 ≤ C₁) (hB : LiftBound ι A r C₂) (hC₂ : 0 ≤ C₂) (hr : 0 < r) (hθ : 0 < θ)
    (hθ' : θ < 1) (hq : 1 ≤ q) {f : X} :
    (InterpCouple.ofMap ι).MemKMethod θ q f ↔ A.MemApprox (θ * r) q f :=
  memKMethod_iff_memApprox_of_sandwich (N₁ := (InterpCouple.ofMap ι).norm1)
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top
      (by norm_num) ENNReal.ofReal_ne_top, ENNReal.mul_ne_top (by norm_num)
        (liftConst_ne_top C₂ r)⟩⟩)
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.add_ne_top.2 ⟨eNorm_ne_top,
      ENNReal.ofReal_ne_top⟩⟩)
    le_rfl le_top hr hθ hθ' hq (norm1_ofMap_le_approxNormDyadic_one hB hC₂ hr.le)
    (approxNormDyadic_top_le_norm1_ofMap hJ hC₁)

end SmoothnessSpace

end ApproximationScheme
