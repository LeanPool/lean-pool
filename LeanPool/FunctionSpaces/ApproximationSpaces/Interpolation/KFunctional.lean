/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Jackson

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Peetre K-functional and real interpolation

For a bounded linear map `ι : Y → X` (think of `Y` as a space of smooth elements of `X`), the
**K-functional** of `f ∈ X` at `t ≥ 0` is

`K(t, f) = inf_{y ∈ Y} (‖f - ι y‖_X + t ‖y‖_Y)`   (`ApproximationScheme.kFunctional`),

a measure of how well `f` is approximated by elements of `Y` of controlled size.  It is
increasing in `t`, bounded by `‖f‖`, and subadditive in `f`.

The **real interpolation space** `(X, Y)_{θ,q}`, `0 < θ < 1`, consists of the `f` with

`‖f‖_{θ,q} = ‖f‖ + ‖(2^(kρθ) K(2^(-kρ), f))_{k ≥ 0}‖_{ℓ_q} < ∞`   (`interpNorm`, `MemInterp`).

The usual definition takes `ρ = 1` and all `k ∈ ℤ`; the terms with `k < 0` (that is `t > 1`)
are controlled by `‖f‖` since `K(t, f) ≤ ‖f‖`, which is why `‖f‖` appears here.  A scale
`ρ > 0` of the dyadic grid is allowed because the representation theorem produces the grid
`t = 2^(-kr)`.  So `MemInterp` is the **discrete K-method** on the grid `t = 2^(-kρ)`.  For
`θ > 0` it gives the same space for every `ρ > 0`, the space of the continuous K-method
`(∫_0^∞ (t^(-θ) K(t, f))^q dt/t)^(1/q)` (`ApproximationScheme.memInterp_iff_memKMethod` in
`ApproximationSpaces.Interpolation.KMethod`).
-/

@[expose] public section

open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The **Peetre K-functional** `K(t, f) = inf_y (‖f - ι y‖ + t ‖y‖)`. -/
noncomputable def kFunctional (ι : Y →L[ℝ] X) (t : ℝ≥0∞) (f : X) : ℝ≥0∞ :=
  ⨅ y : Y, ‖f - ι y‖ₑ + t * ‖y‖ₑ

variable {ι : Y →L[ℝ] X} {t u : ℝ≥0∞}

/-- Every `y ∈ Y` bounds the K-functional: `K(t, f) ≤ ‖f - ι y‖ + t ‖y‖`. -/
theorem kFunctional_le (y : Y) (f : X) : kFunctional ι t f ≤ ‖f - ι y‖ₑ + t * ‖y‖ₑ :=
  iInf_le (fun y => ‖f - ι y‖ₑ + t * ‖y‖ₑ) y

/-- `K(t, f) ≤ ‖f‖`, from `y = 0`. -/
theorem kFunctional_le_enorm (f : X) : kFunctional ι t f ≤ ‖f‖ₑ := by
  simpa using kFunctional_le (ι := ι) (t := t) 0 f

/-- `K(t, 0) = 0`. -/
@[simp]
theorem kFunctional_zero_right : kFunctional ι t 0 = 0 :=
  le_antisymm ((kFunctional_le_enorm 0).trans_eq eNorm_zero) bot_le

/-- The K-functional increases with `t`. -/
theorem kFunctional_mono (h : t ≤ u) (f : X) : kFunctional ι t f ≤ kFunctional ι u f :=
  iInf_mono fun y => by gcongr

/-- The K-functional `t ↦ K(t, f)` is monotone (the `Monotone` form of `kFunctional_mono`). -/
theorem monotone_kFunctional (f : X) : Monotone fun t => kFunctional ι t f :=
  fun _ _ h => kFunctional_mono h f

/-- **Subadditivity**: `K(t, f + g) ≤ K(t, f) + K(t, g)`. -/
theorem kFunctional_add_le (f g : X) :
    kFunctional ι t (f + g) ≤ kFunctional ι t f + kFunctional ι t g := by
  refine ENNReal.le_iInf_add_iInf fun y z => ?_
  calc kFunctional ι t (f + g) ≤ ‖f + g - ι (y + z)‖ₑ + t * ‖y + z‖ₑ := kFunctional_le _ _
    _ ≤ (‖f - ι y‖ₑ + ‖g - ι z‖ₑ) + t * (‖y‖ₑ + ‖z‖ₑ) := by
        rw [map_add, add_sub_add_comm]
        gcongr
        · exact eNorm_add_le _ _
        · exact eNorm_add_le _ _
    _ = (‖f - ι y‖ₑ + t * ‖y‖ₑ) + (‖g - ι z‖ₑ + t * ‖z‖ₑ) := by ring

/-- **Homogeneity**, one inequality: `K(t, c f) ≤ |c| K(t, f)`. -/
theorem kFunctional_smul_le (c : ℝ) (f : X) :
    kFunctional ι t (c • f) ≤ ‖c‖ₑ * kFunctional ι t f := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rw [show ‖c‖ₑ * kFunctional ι t f = ⨅ y, ‖c‖ₑ * (‖f - ι y‖ₑ + t * ‖y‖ₑ) from
    ENNReal.mul_iInf_of_ne (eNorm_ne_zero.2 hc) eNorm_ne_top]
  refine le_iInf fun y => ?_
  calc kFunctional ι t (c • f) ≤ ‖c • f - ι (c • y)‖ₑ + t * ‖c • y‖ₑ := kFunctional_le _ _
    _ = ‖c‖ₑ * (‖f - ι y‖ₑ + t * ‖y‖ₑ) := by
        rw [map_smul, ← smul_sub, eNorm_smul, eNorm_smul]; ring

/-- **Jackson's inequality controls the errors by the K-functional**:
`E_n(f) ≤ max(1, C) K(n^(-r), f)` for `n ≥ 1`. -/
theorem approxError_le_kFunctional_of_jackson {A : ApproximationScheme X} {r C : ℝ}
    (hJ : JacksonBound ι A r C) (hC : 0 ≤ C) {n : ℕ} (hn : 1 ≤ n) (f : X) :
    A.approxError f n ≤ max 1 (ENNReal.ofReal C) * kFunctional ι ((n : ℝ≥0∞) ^ (-r)) f := by
  have hM0 : max 1 (ENNReal.ofReal C) ≠ 0 := (zero_lt_one.trans_le (le_max_left _ _)).ne'
  have hMt : max 1 (ENNReal.ofReal C) ≠ ∞ := max_ne_top ENNReal.one_ne_top ENNReal.ofReal_ne_top
  rw [show max 1 (ENNReal.ofReal C) * kFunctional ι ((n : ℝ≥0∞) ^ (-r)) f =
      ⨅ y, max 1 (ENNReal.ofReal C) * (‖f - ι y‖ₑ + (n : ℝ≥0∞) ^ (-r) * ‖y‖ₑ) from
    ENNReal.mul_iInf_of_ne hM0 hMt]
  refine le_iInf fun y => ?_
  have h1 : A.approxError f n ≤ ‖f - ι y‖ₑ + A.approxError (ι y) n := by
    rw [add_comm]; exact approxError_le_approxError_add_enorm n f (ι y)
  calc A.approxError f n ≤ ‖f - ι y‖ₑ + ENNReal.ofReal C * (n : ℝ≥0∞) ^ (-r) * ‖y‖ₑ :=
        h1.trans (by gcongr; exact hJ.approxError_le hC hn y)
    _ ≤ max 1 (ENNReal.ofReal C) * ‖f - ι y‖ₑ +
          max 1 (ENNReal.ofReal C) * ((n : ℝ≥0∞) ^ (-r) * ‖y‖ₑ) := by
        rw [mul_assoc]
        gcongr
        · exact le_mul_of_one_le_left' (le_max_left _ _)
        · exact le_max_right _ _
    _ = _ := by rw [mul_add]

variable (ι) in
/-- The dyadic sequence of the interpolation norm, `2^(kρθ) K(2^(-kρ), f)`. -/
noncomputable def interpSeq (θ ρ : ℝ) (f : X) (k : ℕ) : ℝ≥0∞ :=
  dyadicWeight (ρ * θ) k * kFunctional ι (dyadicWeight (-ρ) k) f

variable (ι) in
/-- The norm of the **real interpolation space** `(X, Y)_{θ,q}` on the dyadic grid
`t = 2^(-kρ)`: `‖f‖ + ‖(2^(kρθ) K(2^(-kρ), f))_k‖_{ℓ_q}`. -/
noncomputable def interpNorm (θ ρ : ℝ) (q : ℝ≥0∞) (f : X) : ℝ≥0∞ :=
  ‖f‖ₑ + lqNorm q (interpSeq ι θ ρ f)

variable (ι) in
/-- `f` belongs to the **real interpolation space** `(X, Y)_{θ,q}` of the discrete K-method on
the grid `t = 2^(-kρ)`: `‖f‖ + ‖(2^(kρθ) K(2^(-kρ), f))_k‖_{ℓ_q} < ∞`. -/
def MemInterp (θ ρ : ℝ) (q : ℝ≥0∞) (f : X) : Prop := interpNorm ι θ ρ q f < ∞

variable {θ ρ : ℝ} {q : ℝ≥0∞}

/-- **The triangle inequality** for the interpolation norm. -/
theorem interpNorm_add_le (hq : 1 ≤ q) (f g : X) :
    interpNorm ι θ ρ q (f + g) ≤ interpNorm ι θ ρ q f + interpNorm ι θ ρ q g := by
  have hseq : lqNorm q (interpSeq ι θ ρ (f + g)) ≤
      lqNorm q (interpSeq ι θ ρ f) + lqNorm q (interpSeq ι θ ρ g) := by
    calc lqNorm q (interpSeq ι θ ρ (f + g))
        ≤ lqNorm q (fun k => interpSeq ι θ ρ f k + interpSeq ι θ ρ g k) :=
          ENNReal.lqNorm_mono fun k => by
            rw [interpSeq, interpSeq, interpSeq, ← mul_add]
            gcongr
            exact kFunctional_add_le f g
      _ ≤ _ := ENNReal.lqNorm_add_le hq _ _
  calc interpNorm ι θ ρ q (f + g) ≤ (‖f‖ₑ + ‖g‖ₑ) +
        (lqNorm q (interpSeq ι θ ρ f) + lqNorm q (interpSeq ι θ ρ g)) :=
      add_le_add (eNorm_add_le f g) hseq
    _ = _ := by rw [interpNorm, interpNorm]; ring

/-- The interpolation norm is homogeneous: `‖c f‖_{θ,q} ≤ |c| ‖f‖_{θ,q}`. -/
theorem interpNorm_smul_le (c : ℝ) (f : X) :
    interpNorm ι θ ρ q (c • f) ≤ ‖c‖ₑ * interpNorm ι θ ρ q f := by
  rw [interpNorm, interpNorm, mul_add, eNorm_smul, ← ENNReal.lqNorm_const_mul]
  gcongr
  refine ENNReal.lqNorm_mono fun k => ?_
  rw [interpSeq, interpSeq, mul_left_comm]
  gcongr
  exact kFunctional_smul_le c f

/-- `‖f‖ ≤ ‖f‖_{θ,q}`. -/
theorem enorm_le_interpNorm (f : X) : ‖f‖ₑ ≤ interpNorm ι θ ρ q f := le_self_add

variable (ι) in
/-- The **real interpolation space** `(X, Y)_{θ,q}` as a real subspace of `X`. -/
def interpSpace (θ ρ : ℝ) (q : ℝ≥0∞) (hq : 1 ≤ q) : Submodule ℝ X where
  carrier := {f | MemInterp ι θ ρ q f}
  zero_mem' := by
    change interpNorm ι θ ρ q 0 < ∞
    have : interpSeq ι θ ρ (0 : X) = fun _ => 0 := by funext k; simp [interpSeq]
    simp [interpNorm, this]
  add_mem' hf hg := (interpNorm_add_le hq _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hf, hg⟩)
  smul_mem' c _ hf := (interpNorm_smul_le c _).trans_lt (ENNReal.mul_lt_top eNorm_lt_top hf)

/-- Membership in the interpolation space as a submodule. -/
@[simp]
theorem mem_interpSpace {hq : 1 ≤ q} {f : X} :
    f ∈ interpSpace ι θ ρ q hq ↔ MemInterp ι θ ρ q f := Iff.rfl

end ApproximationScheme
