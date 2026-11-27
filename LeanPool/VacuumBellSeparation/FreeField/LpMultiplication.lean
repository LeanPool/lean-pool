/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Actual bounded multiplication on arbitrary complex L² spaces

No finite-measure hypothesis is imposed. Multiplication is constructed by
Hölder's map, and every algebraic or adjoint identity is proved on actual
almost-everywhere representatives.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- Continuous linear map for the ℓᵖ multiplication, of type `Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ`. -/
noncomputable def lpMultiplication (w : α → ℂ) (hw : MemLp w ⊤ μ) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL μ ⊤ 2 2 (hw.toLp w)

theorem lpMultiplication_ae (w : α → ℂ) (hw : MemLp w ⊤ μ) (f : Lp ℂ 2 μ) :
    lpMultiplication μ w hw f =ᵐ[μ] fun x => w x * f x := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (hw.toLp w) f
  filter_upwards [h, hw.coeFn_toLp] with x hx hxw
  simpa only [lpMultiplication, ContinuousLinearMap.holderL_apply_apply, hxw,
    ContinuousLinearMap.mul_apply'] using hx

theorem lpMultiplication_norm_le (w : α → ℂ) (hw : MemLp w ⊤ μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖w x‖ ≤ C) :
    ‖lpMultiplication μ w hw‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [lpMultiplication_ae μ w hw f, hb] with x hx hbx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hbx (norm_nonneg _)

theorem lpMultiplication_congr (w v : α → ℂ) (hw : MemLp w ⊤ μ) (hv : MemLp v ⊤ μ)
    (h : w =ᵐ[μ] v) : lpMultiplication μ w hw = lpMultiplication μ v hv := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [lpMultiplication_ae μ w hw f, lpMultiplication_ae μ v hv f, h] with x hx hy hxy
  rw [hx, hy, hxy]

theorem lpMultiplication_one :
    lpMultiplication μ (fun _ : α => 1) (memLp_top_const 1) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [lpMultiplication_ae μ (fun _ => 1) (memLp_top_const 1) f] with x hx
  simpa only [one_mul, one_apply_eq_self] using hx

theorem lpMultiplication_add (w v : α → ℂ) (hw : MemLp w ⊤ μ) (hv : MemLp v ⊤ μ) :
    lpMultiplication μ (w + v) (hw.add hv) = lpMultiplication μ w hw + lpMultiplication μ v hv := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [lpMultiplication_ae μ (w + v) (hw.add hv) f,
    lpMultiplication_ae μ w hw f, lpMultiplication_ae μ v hv f,
    Lp.coeFn_add (lpMultiplication μ w hw f) (lpMultiplication μ v hv f)] with x hx hwx hvx hsum
  change lpMultiplication μ (w + v) (hw.add hv) f x =
    (lpMultiplication μ w hw f + lpMultiplication μ v hv f) x
  simp only [hx, hsum, Pi.add_apply, hwx, hvx, add_mul]

theorem lpMultiplication_mul (w v : α → ℂ) (hw : MemLp w ⊤ μ) (hv : MemLp v ⊤ μ)
    (hwv : MemLp (w * v) ⊤ μ) :
    lpMultiplication μ (w * v) hwv = lpMultiplication μ w hw * lpMultiplication μ v hv := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [lpMultiplication_ae μ (w * v) hwv f,
    lpMultiplication_ae μ w hw (lpMultiplication μ v hv f),
    lpMultiplication_ae μ v hv f] with x hx hwx hvx
  change lpMultiplication μ (w * v) hwv f x =
    lpMultiplication μ w hw (lpMultiplication μ v hv f) x
  rw [hx, hwx, hvx, Pi.mul_apply, mul_assoc]

theorem lpMultiplication_isSelfAdjoint (w : α → ℂ) (hw : MemLp w ⊤ μ)
    (hreal : ∀ᵐ x ∂μ, conj (w x) = w x) : IsSelfAdjoint (lpMultiplication μ w hw) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lpMultiplication_ae μ w hw f, lpMultiplication_ae μ w hw g, hreal]
    with x hfx hgx hx
  change inner ℂ (lpMultiplication μ w hw f x) (g x) =
    inner ℂ (f x) (lpMultiplication μ w hw g x)
  simp only [hfx, hgx, RCLike.inner_apply, map_mul, hx]
  ring

theorem lpMultiplication_injective (w : α → ℂ) (hw : MemLp w ⊤ μ)
    (hzero : ∀ᵐ x ∂μ, w x ≠ 0) : Function.Injective (lpMultiplication μ w hw) := by
  intro f g hfg
  apply Lp.ext
  have he : (lpMultiplication μ w hw f : α → ℂ) =ᵐ[μ] lpMultiplication μ w hw g := by
    rw [hfg]
  filter_upwards [lpMultiplication_ae μ w hw f, lpMultiplication_ae μ w hw g, hzero, he]
    with x hfx hgx hx heq
  rw [hfx, hgx] at heq
  exact mul_left_cancel₀ hx heq

end VacuumBellSeparation
