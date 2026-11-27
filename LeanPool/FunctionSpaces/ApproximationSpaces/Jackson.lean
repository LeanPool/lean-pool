/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Lift

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Jackson and Bernstein inequalities, smoothness spaces

Let `ι : Y → X` be a bounded linear map; think of `Y` as a space of smooth elements of `X`
(a Sobolev space inside `L_p`).  Two inequalities relate `Y` to a scheme `A` in `X`:

* **Jackson's inequality** of order `r`: `E_n(ι y) ≤ C n^(-r) ‖y‖_Y` for `n ≥ 1`
  (`ApproximationScheme.JacksonBound`); smooth elements are well approximated;
* **Bernstein's inequality** of order `r`: every `a ∈ A n` is `ι y` with
  `‖y‖_Y ≤ C n^r ‖a‖_X` (`ApproximationScheme.LiftBound` with exponent `r`); approximants are
  smooth, with controlled norm.

Jackson's inequality gives `ι(Y) ⊆ A^r_∞` with `‖ι y‖_{A^r_∞} ≤ (‖ι‖ + C) ‖y‖`
(`approxNormDyadic_top_le_of_jackson`), and Bernstein's inequality gives `A^r_1 ⊆ ι(Y)`
(`exists_preimage_of_liftBound`).  So a space with both inequalities sits between the two
extreme approximation spaces of order `r`:

`A^r_1 ⊆ ι(Y) ⊆ A^r_∞`.

A **smoothness space** (`ApproximationScheme.SmoothnessSpace`) bundles `Y`, `ι`, the order and
the two inequalities.  These two inclusions are all that the embedding theorems for Sobolev
spaces use; they lose the fine index at both ends, which is why the limiting cases of the
Sobolev embedding are out of reach of this method.
-/

@[expose] public section

open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- **Jackson's inequality** of order `r` with constant `C`: `E_n(ι y) ≤ C n^(-r) ‖y‖` for all
`y ∈ Y` and `n ≥ 1`, stated for the real number `E_n(ι y)` (the error is finite). -/
def JacksonBound (ι : Y →L[ℝ] X) (A : ApproximationScheme X) (r C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ y : Y, (A.approxError (ι y) n).toReal ≤ C * (n : ℝ) ^ (-r) * ‖y‖

variable {ι : Y →L[ℝ] X} {A : ApproximationScheme X} {r C : ℝ}

/-- Jackson's inequality in `ℝ≥0∞`. -/
theorem JacksonBound.approxError_le (hJ : JacksonBound ι A r C) (hC : 0 ≤ C) {n : ℕ} (hn : 1 ≤ n)
    (y : Y) : A.approxError (ι y) n ≤ ENNReal.ofReal C * (n : ℝ≥0∞) ^ (-r) * ‖y‖ₑ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← ENNReal.ofReal_toReal (approxError_ne_top (ι y) n), ← ofReal_norm,
    ← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_pos hn0,
    ← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (hJ n hn y)

/-- **Jackson's inequality gives `ι(Y) ⊆ A^r_∞`**:
`‖ι y‖ + sup_k 2^(kr) E_{2^k}(ι y) ≤ (‖ι‖ + C) ‖y‖`. -/
theorem approxNormDyadic_top_le_of_jackson (hJ : JacksonBound ι A r C) (hC : 0 ≤ C) (y : Y) :
    A.approxNormDyadic r ∞ (ι y) ≤ (‖ι‖ₑ + ENNReal.ofReal C) * ‖y‖ₑ := by
  rw [approxNormDyadic, ENNReal.lqNorm_top, add_mul]
  refine add_le_add (ι.le_opENorm y) (iSup_le fun k => ?_)
  calc A.approxSeqDyadic r (ι y) k
      ≤ dyadicWeight r k * (ENNReal.ofReal C * ((2 ^ k : ℕ) : ℝ≥0∞) ^ (-r) * ‖y‖ₑ) := by
        rw [approxSeqDyadic]; gcongr; exact hJ.approxError_le hC Nat.one_le_two_pow y
    _ = ENNReal.ofReal C * ‖y‖ₑ := by
        rw [ENNReal.natCast_two_pow_rpow, mul_comm (ENNReal.ofReal C), mul_assoc, ← mul_assoc,
          ENNReal.dyadicWeight_mul_neg_self, one_mul]

/-- **Jackson's inequality gives `ι(Y) ⊆ A^r_∞`**, membership form. -/
theorem memApprox_top_of_jackson (hJ : JacksonBound ι A r C) (hC : 0 ≤ C) (hr : 0 ≤ r) (y : Y) :
    A.MemApprox r ∞ (ι y) := by
  rw [memApprox_iff_approxNormDyadic_lt_top le_top hr]
  exact (approxNormDyadic_top_le_of_jackson hJ hC y).trans_lt
    (ENNReal.mul_lt_top (ENNReal.add_lt_top.2 ⟨eNorm_lt_top, ENNReal.ofReal_lt_top⟩) eNorm_lt_top)

/-- A **smoothness space** of order `r` for the scheme `A`: a normed space `F` with an injective
bounded linear map `ι : F → E` satisfying Jackson's and Bernstein's inequalities of order `r`.
Sobolev spaces inside `L_p` are the motivating example. -/
structure SmoothnessSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ApproximationScheme E) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] where
  /-- The embedding `ι` of the smoothness space into `E`. -/
  incl : F →L[ℝ] E
  injective : Function.Injective incl
  /-- The order of smoothness. -/
  order : ℝ
  order_pos : 0 < order
  /-- The constant of Jackson's inequality. -/
  jacksonConst : ℝ
  jacksonConst_nonneg : 0 ≤ jacksonConst
  /-- The constant of Bernstein's inequality. -/
  bernsteinConst : ℝ
  bernsteinConst_nonneg : 0 ≤ bernsteinConst
  jackson : JacksonBound incl A order jacksonConst
  bernstein : LiftBound incl A order bernsteinConst

namespace SmoothnessSpace

variable (W : SmoothnessSpace A Y)

/-- **`W ⊆ A^r_∞`**, from Jackson's inequality. -/
theorem memApprox_top (y : Y) : A.MemApprox W.order ∞ (W.incl y) :=
  memApprox_top_of_jackson W.jackson W.jacksonConst_nonneg W.order_pos.le y

/-- **`A^r_1 ⊆ W`**, from Bernstein's inequality. -/
theorem exists_eq_of_memApprox_one [CompleteSpace Y] {f : X} (hf : A.MemApprox W.order 1 f) :
    ∃ y : Y, W.incl y = f ∧ ‖y‖ₑ ≤ (3 * ENNReal.ofReal W.bernsteinConst +
      3 * liftConst W.bernsteinConst W.order) * A.approxNormDyadic W.order 1 f :=
  exists_preimage_of_liftBound W.bernstein W.bernsteinConst_nonneg W.order_pos.le
    ((memApprox_iff_lqNorm_dyadic_lt_top le_rfl W.order_pos.le).1 hf)

/-- **`A^s_q ⊆ W` for `s > r`**: more smoothness in the approximation sense than the order of
`W` gives an element of `W`, for every fine index. -/
theorem exists_eq_of_lt [CompleteSpace Y] {s : ℝ} {q : ℝ≥0∞} (hs : W.order < s) (hq : 1 ≤ q)
    {f : X} (hf : A.MemApprox s q f) : ∃ y : Y, W.incl y = f :=
  let ⟨y, hy, _⟩ := W.exists_eq_of_memApprox_one (hf.of_lt hq le_rfl W.order_pos.le hs)
  ⟨y, hy⟩

/-- Transport of a smoothness space to an equal scheme, keeping the embedding, the order and
the constants. -/
def congr {B : ApproximationScheme X} (h : A = B) (W : SmoothnessSpace A Y) :
    SmoothnessSpace B Y where
  incl := W.incl
  injective := W.injective
  order := W.order
  order_pos := W.order_pos
  jacksonConst := W.jacksonConst
  jacksonConst_nonneg := W.jacksonConst_nonneg
  bernsteinConst := W.bernsteinConst
  bernsteinConst_nonneg := W.bernsteinConst_nonneg
  jackson := h ▸ W.jackson
  bernstein := h ▸ W.bernstein

end SmoothnessSpace

end ApproximationScheme
