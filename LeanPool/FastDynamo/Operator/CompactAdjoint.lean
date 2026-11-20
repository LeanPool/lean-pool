/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.AntiDual
public import LeanPool.FastDynamo.Operator.AssociatedForm
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Schauder's theorem on a Hilbert space, and the compact anti-dual pivot

Mathlib 4.35.0 closes the compact operators under composition with bounded maps, under sums
and under scalar multiples, but it contains no form of **Schauder's theorem**: nothing in
`Mathlib/Analysis/Normed/Operator/Compact/` concerns adjoints, and
`Mathlib/Analysis/InnerProductSpace/Adjoint.lean` never mentions `IsCompactOperator`.  This
module supplies the Hilbert-space case, which is all the paper needs.

The proof is the standard Hilbert-space shortcut, not the Arzelà-Ascoli argument of the
Banach-space statement.  Writing `S†` for `ContinuousLinearMap.adjoint S`,

`‖S†y‖² = re ⟪S†y, S†y⟫ = re ⟪y, S S† y⟫ ≤ ‖y‖ ‖S (S† y)‖`,

so a net of the totally bounded set `{S (S† y) : ‖y‖ < 1}` with centres *inside* that set
pulls back to a net of `{S† y : ‖y‖ < 1}`: if `‖S S† y - S S† y'‖ ≤ ε²/4` and `‖y - y'‖ ≤ 2`
then `‖S†y - S†y'‖² ≤ ε²/2 < ε²`.  Total boundedness plus completeness of the target gives
compact closure of the image of the unit ball, which is `IsCompactOperator`.

The second half transports the statement to the anti-dual pivot
`associatedFormPivot j f φ = ⟪j φ, f⟫` of `FastDynamo/Operator/AssociatedForm.lean`, through
the identity `associatedFormPivot j = complexToAntiDual ∘ j†`.  This is the exact ingredient
required by the compactness argument for `K_w` in §2.3 of the paper, where the terms of the
velocity form carrying a derivative on the *input* are said to factor through the adjoint of
the compact restriction `H¹(ℝ²) → L²(D)`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

section Schauder

variable {𝕜 V X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]

/-- The basic Hilbert-space inequality behind Schauder's theorem:
`‖S†y‖² ≤ ‖y‖ ‖S (S† y)‖`. -/
theorem norm_adjoint_apply_sq_le (S : V →L[𝕜] X) (y : X) :
    ‖ContinuousLinearMap.adjoint S y‖ ^ 2 ≤
      ‖y‖ * ‖S (ContinuousLinearMap.adjoint S y)‖ := by
  have hinner :
      (inner 𝕜 (ContinuousLinearMap.adjoint S y) (ContinuousLinearMap.adjoint S y) : 𝕜) =
        inner 𝕜 y (S (ContinuousLinearMap.adjoint S y)) :=
    ContinuousLinearMap.adjoint_inner_left S (ContinuousLinearMap.adjoint S y) y
  have hsq : ‖ContinuousLinearMap.adjoint S y‖ ^ 2 =
      RCLike.re (inner 𝕜 y (S (ContinuousLinearMap.adjoint S y)) : 𝕜) := by
    rw [← hinner, inner_self_eq_norm_sq]
  rw [hsq]
  calc
    RCLike.re (inner 𝕜 y (S (ContinuousLinearMap.adjoint S y)) : 𝕜)
        ≤ ‖(inner 𝕜 y (S (ContinuousLinearMap.adjoint S y)) : 𝕜)‖ := RCLike.re_le_norm _
    _ ≤ ‖y‖ * ‖S (ContinuousLinearMap.adjoint S y)‖ := norm_inner_le_norm _ _

/-- **Schauder's theorem** on Hilbert spaces: the adjoint of a compact operator between
complete inner product spaces is compact. -/
theorem isCompactOperator_adjoint (S : V →L[𝕜] X) (hS : IsCompactOperator S) :
    IsCompactOperator (ContinuousLinearMap.adjoint S) := by
  classical
  set T : X →L[𝕜] V := ContinuousLinearMap.adjoint S with hTdef
  have hSlin : IsCompactOperator ((S : V →ₗ[𝕜] X)) := hS
  have hKtb : TotallyBounded ((S : V →ₗ[𝕜] X) '' Metric.closedBall (0 : V) ‖T‖) :=
    (hSlin.isCompact_closure_image_closedBall ‖T‖).totallyBounded.subset subset_closure
  have hballnorm : ∀ y : X, y ∈ Metric.ball (0 : X) 1 → ‖y‖ ≤ 1 := by
    intro y hy
    have : ‖y‖ < 1 := by simpa [dist_zero_right] using hy
    exact this.le
  have hnormT : ∀ y : X, y ∈ Metric.ball (0 : X) 1 → ‖T y‖ ≤ ‖T‖ := by
    intro y hy
    calc
      ‖T y‖ ≤ ‖T‖ * ‖y‖ := T.le_opNorm y
      _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left (hballnorm y hy) (norm_nonneg T)
      _ = ‖T‖ := mul_one _
  have hBtb : TotallyBounded ((fun y : X => S (T y)) '' Metric.ball (0 : X) 1) := by
    refine hKtb.subset ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨T y, by simpa [Metric.mem_closedBall, dist_zero_right] using hnormT y hy, rfl⟩
  have hkey : ∀ y : X, ‖T y‖ ^ 2 ≤ ‖y‖ * ‖S (T y)‖ := norm_adjoint_apply_sq_le S
  have htb : TotallyBounded ((fun y : X => T y) '' Metric.ball (0 : X) 1) := by
    rw [Metric.totallyBounded_iff]
    intro eps heps
    obtain ⟨t, htB, htfin, htcov⟩ :=
      Metric.finite_approx_of_totallyBounded hBtb (eps ^ 2 / 4) (by positivity)
    have hchoice : ∀ c ∈ t, ∃ y : X, y ∈ Metric.ball (0 : X) 1 ∧ S (T y) = c := by
      intro c hc
      obtain ⟨y, hy, hyc⟩ := htB hc
      exact ⟨y, hy, hyc⟩
    choose! centre hcentre hcentreS using hchoice
    refine ⟨(fun c => T (centre c)) '' t, htfin.image _, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hxB : S (T x) ∈ (fun y : X => S (T y)) '' Metric.ball (0 : X) 1 := ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hball⟩ := Set.mem_iUnion₂.mp (htcov hxB)
    have hdist : ‖S (T x) - c‖ < eps ^ 2 / 4 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hball
    have hdiff : ‖T x - T (centre c)‖ ^ 2 ≤ ‖x - centre c‖ * ‖S (T x) - S (T (centre c))‖ := by
      have h := hkey (x - centre c)
      simpa [map_sub] using h
    have hnorm2 : ‖x - centre c‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by
        have h1 := hballnorm x hx
        have h2 := hballnorm _ (hcentre c hc)
        linarith)
    have hnormS : ‖S (T x) - S (T (centre c))‖ ≤ eps ^ 2 / 4 := by
      rw [hcentreS c hc]
      exact hdist.le
    have hquad : ‖T x - T (centre c)‖ ^ 2 ≤ 2 * (eps ^ 2 / 4) :=
      hdiff.trans (mul_le_mul hnorm2 hnormS (norm_nonneg _) (by norm_num))
    have hlt : ‖T x - T (centre c)‖ < eps := by
      refine lt_of_pow_lt_pow_left₀ 2 heps.le ?_
      have hpos : (0 : ℝ) < eps ^ 2 := by positivity
      linarith
    refine Set.mem_iUnion₂.mpr ⟨T (centre c), ⟨c, hc, rfl⟩, ?_⟩
    simpa [Metric.mem_ball, dist_eq_norm] using hlt
  rw [isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image]
  exact ⟨Metric.ball (0 : X) 1, Metric.ball_mem_nhds _ one_pos,
    htb.closure.isCompact_of_isClosed isClosed_closure⟩

end Schauder

/-! ## The anti-dual pivot -/

section Pivot

variable {V X : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- The pivot embedding `f ↦ (φ ↦ ⟪j φ, f⟫)` into the anti-dual is the anti-dual Riesz
isometry applied to the adjoint of `j`. -/
theorem associatedFormPivot_eq_adjoint (j : V →L[ℂ] X) :
    associatedFormPivot j =
      (complexToAntiDual (E := V)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.adjoint j) := by
  refine ContinuousLinearMap.ext fun f => ContinuousLinearMap.ext fun phi => ?_
  have hleft : associatedFormPivot j f phi = inner ℂ (j phi) f := rfl
  have hright :
      ((complexToAntiDual (E := V)).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (ContinuousLinearMap.adjoint j)) f phi =
        inner ℂ phi (ContinuousLinearMap.adjoint j f) :=
    complexToAntiDual_apply_apply _ _
  rw [hleft, hright, ContinuousLinearMap.adjoint_inner_right]

/-- Compactness of the anti-dual pivot of a compact embedding.  This is the exact form in
which the compactness argument for `K_w` in §2.3 of the paper uses Schauder's theorem: the
lower-order terms carrying a derivative on the input factor through the adjoint
`L²(D) → H⁻¹(ℝ²)` of the compact restriction `H¹(ℝ²) → L²(D)`. -/
theorem isCompactOperator_associatedFormPivot_of_compact (j : V →L[ℂ] X)
    (hj : IsCompactOperator j) : IsCompactOperator (associatedFormPivot j) := by
  have h := (isCompactOperator_adjoint j hj).clm_comp
    (complexToAntiDual (E := V)).toContinuousLinearEquiv.toContinuousLinearMap
  have h2 : IsCompactOperator
      ((complexToAntiDual (E := V)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.adjoint j) : X →L[ℂ] ComplexAntiDual V) := h
  rw [associatedFormPivot_eq_adjoint]
  exact h2

end Pivot

end

end FastDynamo
