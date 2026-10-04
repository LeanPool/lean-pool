/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.DifferenceQuotient
public import LeanPool.EllipticPDE.Sobolev.Basic
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.CompactOpen
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Integral.Prod


/-!
# Difference-quotient norm bounds

The two-directional bound of the difference-quotient method: a function with an
`L²` weak derivative has `L²`-bounded difference quotients (direction i), and a
uniform bound on the difference quotients yields a weak derivative (direction ii).
See Evans, *Partial Differential Equations* (2nd ed.), §5.8.2.

The direction-i bound is proved here for a smooth, compactly supported
representative `φ`, by the fundamental theorem of calculus along the segment
`t ↦ x + t • (h eₖ)`, a one-variable Cauchy-Schwarz bound on `[0, 1]`
(`MeasureTheory.sq_intervalIntegral_le`), a Tonelli swap of the order of
integration, and translation invariance of the Lebesgue integral.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- `g` has whole-space weak `k`-derivative `g'` in `L²`: for every smooth compactly
supported test function `φ`, `∫ g ∂ₖφ = -∫ g' φ`. -/
def HasWeakDeriv (k : Fin d) (g g' : EucL2 d) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∫ x, (g x) * (partialD k φ x) = - ∫ x, (g' x) * (φ x)

/-! ### Smooth compactly supported case -/

/-- The segment path `t ↦ φ (x + t • v)` has derivative `(fderiv ℝ φ (x + t • v)) v`
at every `t`, for `φ` smooth. -/
private theorem hasDerivAt_comp_segment {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x v : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (x + s • v)) ((fderiv ℝ φ (x + t • v)) v) t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hφ' : HasFDerivAt φ (fderiv ℝ φ (x + t • v)) (x + t • v) :=
    (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt
  exact hφ'.comp_hasDerivAt t hline

/-- Continuity of the segment derivative `t ↦ (fderiv ℝ φ (x + t • v)) v`. -/
private theorem continuous_segment_deriv {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x v : EuclideanSpace ℝ (Fin d)) :
    Continuous (fun t : ℝ => (fderiv ℝ φ (x + t • v)) v) :=
  ((hφ.continuous_fderiv (by simp)).comp (by fun_prop)).clm_apply continuous_const

/-- Joint continuity of `(x, t) ↦ ((fderiv ℝ φ (x + t • v)) v) ^ 2`. -/
private theorem continuous_uncurry_segment {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (v : EuclideanSpace ℝ (Fin d)) :
    Continuous (Function.uncurry fun (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) =>
        ((fderiv ℝ φ (x + t • v)) v) ^ 2) :=
  (((hφ.continuous_fderiv (by simp)).comp (by fun_prop : Continuous
    fun p : EuclideanSpace ℝ (Fin d) × ℝ => p.1 + p.2 • v)).clm_apply continuous_const).pow 2

/-- Fundamental theorem of calculus along the segment from `x` to `x + v`. -/
private theorem sub_translation_eq_integral {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x v : EuclideanSpace ℝ (Fin d)) :
    φ (x + v) - φ x = ∫ t in (0 : ℝ)..1, (fderiv ℝ φ (x + t • v)) v := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hasDerivAt_comp_segment hφ x v t)
        (continuous_segment_deriv hφ x v).continuousOn.intervalIntegrable]
  simp

/-- Pointwise square estimate: `(φ (x + v) - φ x) ^ 2` is at most the `[0, 1]`
integral of the squared segment derivative. -/
private theorem sq_sub_translation_le {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x v : EuclideanSpace ℝ (Fin d)) :
    (φ (x + v) - φ x) ^ 2 ≤ ∫ t in (0 : ℝ)..1, ((fderiv ℝ φ (x + t • v)) v) ^ 2 := by
  rw [sub_translation_eq_integral hφ x v]
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have := MeasureTheory.sq_intervalIntegral_le h01
    (continuous_segment_deriv hφ x v).continuousOn
  simpa using this

/-- The integrand `(x, t) ↦ ((fderiv ℝ φ (x + t • v)) v) ^ 2` is integrable for the
product of Lebesgue measure with the unit-interval slice. -/
private theorem integrable_uncurry_segment {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) (v : EuclideanSpace ℝ (Fin d)) :
    Integrable (Function.uncurry fun (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) =>
        ((fderiv ℝ φ (x + t • v)) v) ^ 2)
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  set g : EuclideanSpace ℝ (Fin d) × ℝ → ℝ :=
    Function.uncurry fun (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) =>
      ((fderiv ℝ φ (x + t • v)) v) ^ 2 with hg
  set ρ : Measure (EuclideanSpace ℝ (Fin d) × ℝ) :=
    volume.prod (volume.restrict (Ioc (0 : ℝ) 1)) with hρ
  have hcont : Continuous g := continuous_uncurry_segment hφ v
  obtain ⟨R, hR⟩ := (hcs.fderiv ℝ).isCompact.isBounded.subset_closedBall 0
  -- The joint support sits inside the compact slab `C`.
  set C : Set (EuclideanSpace ℝ (Fin d) × ℝ) := closedBall 0 (R + ‖v‖) ×ˢ Icc 0 1 with hC
  have hCcomp : IsCompact C := (isCompact_closedBall _ _).prod isCompact_Icc
  have hIntOn : IntegrableOn g C ρ := hcont.locallyIntegrable.integrableOn_isCompact hCcomp
  -- `g` vanishes off `C` on the support of `ρ` (where `t ∈ Ioc 0 1`).
  have hzero : ∀ p : EuclideanSpace ℝ (Fin d) × ℝ, p.2 ∈ Ioc (0 : ℝ) 1 → p ∉ C → g p = 0 := by
    rintro ⟨x, t⟩ ht hpC
    have hxball : x ∉ closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + ‖v‖) := by
      intro hx; exact hpC ⟨hx, ⟨le_of_lt ht.1, ht.2⟩⟩
    have hxt : x + t • v ∉ tsupport (fderiv ℝ φ) := by
      intro hmem
      apply hxball
      have hxK : ‖x + t • v‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hR hmem
      have htnorm : ‖t • v‖ ≤ ‖v‖ := by
        rw [norm_smul]
        have htle : ‖t‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_pos ht.1]; exact ht.2
        nlinarith [norm_nonneg v, htle]
      have hxle : ‖x‖ ≤ R + ‖v‖ := by
        calc ‖x‖ = ‖(x + t • v) - t • v‖ := by congr 1; abel
          _ ≤ ‖x + t • v‖ + ‖t • v‖ := norm_sub_le _ _
          _ ≤ R + ‖v‖ := by linarith
      simpa [mem_closedBall, dist_eq_norm] using hxle
    simp only [hg, Function.uncurry_apply_pair,
      image_eq_zero_of_notMem_tsupport hxt, _root_.zero_apply]
    norm_num
  -- Almost everywhere `t ∈ Ioc 0 1`, so `g =ᵐ[ρ] C.indicator g`.
  have htioc : ∀ᵐ p ∂ρ, p.2 ∈ Ioc (0 : ℝ) 1 := by
    rw [ae_iff]
    -- The bad set is a product with the (Lebesgue-null) complement of `Ioc 0 1`.
    have hset : {p : EuclideanSpace ℝ (Fin d) × ℝ | p.2 ∉ Ioc (0 : ℝ) 1}
        = univ ×ˢ (Ioc (0 : ℝ) 1)ᶜ := by ext p; simp
    rw [hset, hρ, Measure.prod_prod, Measure.restrict_apply' measurableSet_Ioc,
      compl_inter_self, measure_empty, mul_zero]
  have hae : g =ᵐ[ρ] C.indicator g := by
    filter_upwards [htioc] with p hp
    by_cases hpC : p ∈ C
    · rw [indicator_of_mem hpC]
    · rw [indicator_of_notMem hpC, hzero p hp hpC]
  rw [integrable_congr hae]
  exact (integrable_indicator_iff hCcomp.measurableSet).mpr hIntOn

/-- Squaring the pointwise identity `(fderiv ℝ φ x) (hshift k h) = h * ∂ₖφ x`, obtained
from linearity of `fderiv` and `hshift k h = h • single k 1`. -/
private theorem sq_fderiv_hshift {φ : EuclideanSpace ℝ (Fin d) → ℝ} (k : Fin d) (h : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ((fderiv ℝ φ x) (hshift k h)) ^ 2 = h ^ 2 * (partialD k φ x) ^ 2 := by
  have hfv : (fderiv ℝ φ x) (hshift k h) = h * partialD k φ x := by
    simp [hshift, partialD]
  rw [hfv]; ring

/-- **Difference-quotient bound in the smooth compactly supported case.** For `φ` smooth with
compact support, the `L²` norm of the difference quotient `Dₖʰφ` is bounded by the `L²`
norm of the `k`-th classical partial derivative: `‖Dₖʰφ‖ ≤ ‖∂ₖφ‖`. The argument is the
fundamental-theorem-of-calculus proof of Evans, *Partial Differential Equations* (2nd
ed.), §5.8.2, specialised to the single coordinate direction `k`, so no operator-norm
loss to the full gradient is incurred. -/
theorem norm_diffQuot_le_of_contDiff (k : Fin d) (h : ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    (hL2 : MemLp φ 2 volume) (hL2' : MemLp (partialD k φ) 2 volume) :
    ‖diffQuot k h (hL2.toLp φ)‖ ≤ ‖hL2'.toLp (partialD k φ)‖ := by
  rcases eq_or_ne h 0 with rfl | hh
  · rw [diffQuot_zero, _root_.zero_apply, norm_zero]
    exact norm_nonneg _
  set v : EuclideanSpace ℝ (Fin d) := hshift k h with hv
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hInt := integrable_uncurry_segment hφ hcs v
  -- The two sides of the pointwise square bound are integrable in `x`.
  have hLHS_int : Integrable (fun x => (φ (x + v) - φ x) ^ 2) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hφ.continuous.comp (by fun_prop)).sub hφ.continuous).pow 2
    · exact (((hcs.comp_homeomorph (Homeomorph.addRight v)).sub hcs).comp_left
        (g := fun r : ℝ => r ^ 2) (by simp))
  have hRHS_int : Integrable (fun x => ∫ t in (0 : ℝ)..1, ((fderiv ℝ φ (x + t • v)) v) ^ 2) := by
    simp_rw [intervalIntegral.integral_of_le h01]
    exact hInt.integral_prod_left
  -- Step A: integrate the pointwise square bound.
  have stepA : ∫ x, (φ (x + v) - φ x) ^ 2
      ≤ ∫ x, ∫ t in (0 : ℝ)..1, ((fderiv ℝ φ (x + t • v)) v) ^ 2 :=
    integral_mono hLHS_int hRHS_int (fun x => sq_sub_translation_le hφ x v)
  -- Step B: swap the order of integration (Tonelli).
  have stepB : (∫ x, ∫ t in (0 : ℝ)..1, ((fderiv ℝ φ (x + t • v)) v) ^ 2)
      = ∫ t in (0 : ℝ)..1, ∫ x, ((fderiv ℝ φ (x + t • v)) v) ^ 2 := by
    simp_rw [intervalIntegral.integral_of_le h01]
    exact integral_integral_swap hInt
  -- Step C: translation invariance collapses the inner integral, constant in `t`.
  have stepC : (∫ t in (0 : ℝ)..1, ∫ x, ((fderiv ℝ φ (x + t • v)) v) ^ 2)
      = ∫ x, ((fderiv ℝ φ x) v) ^ 2 := by
    have hI0 : ∀ t : ℝ, (∫ x, ((fderiv ℝ φ (x + t • v)) v) ^ 2) = ∫ x, ((fderiv ℝ φ x) v) ^ 2 :=
      fun t => integral_add_right_eq_self (fun x => ((fderiv ℝ φ x) v) ^ 2) (t • v)
    rw [intervalIntegral.integral_congr (g := fun _ => ∫ x, ((fderiv ℝ φ x) v) ^ 2)
        (fun t _ => hI0 t)]
    simp
  -- Step D: the exact (not lossy) collapse to the single partial derivative `∂ₖφ`.
  have stepD : (∫ x, ((fderiv ℝ φ x) v) ^ 2) = h ^ 2 * ∫ x, (partialD k φ x) ^ 2 := by
    rw [show (fun x => ((fderiv ℝ φ x) v) ^ 2)
          = fun x => h ^ 2 * (partialD k φ x) ^ 2 from funext fun x => sq_fderiv_hshift k h x]
    exact integral_const_mul _ _
  have hmain : ∫ x, (φ (x + v) - φ x) ^ 2 ≤ h ^ 2 * ∫ x, (partialD k φ x) ^ 2 := by
    rw [← stepD, ← stepC, ← stepB]; exact stepA
  -- Transport `hmain` back to the `L²` classes via the a.e. representative formulas.
  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving (· + v) volume volume :=
    (measurePreserving_add_right volume v).quasiMeasurePreserving
  have hshiftAE : (fun x => (hL2.toLp φ) (x + v)) =ᵐ[volume] (fun x => φ (x + v)) :=
    hqmp.ae_eq_comp hL2.coeFn_toLp
  have hcombine : (diffQuot k h (hL2.toLp φ) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume] fun x => (φ (x + v) - φ x) / h := by
    filter_upwards [coeFn_diffQuot k h (hL2.toLp φ), hL2.coeFn_toLp, hshiftAE]
      with x hx1 hx2 hx3
    rw [hx1, hx2, hx3]
  have hsq : ‖diffQuot k h (hL2.toLp φ)‖ ^ 2 ≤ ‖hL2'.toLp (partialD k φ)‖ ^ 2 := by
    rw [norm_sq_eq_integral_sq, norm_sq_eq_integral_sq]
    have hlhs : (∫ x, (diffQuot k h (hL2.toLp φ) x) ^ 2)
        = ∫ x, ((φ (x + v) - φ x) / h) ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [hcombine] with x hx
      rw [hx]
    have hrhs : (∫ x, (hL2'.toLp (partialD k φ) x) ^ 2) = ∫ x, (partialD k φ x) ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [hL2'.coeFn_toLp] with x hx
      rw [hx]
    rw [hlhs, hrhs]
    have hdiv : ∀ x, ((φ (x + v) - φ x) / h) ^ 2 = (φ (x + v) - φ x) ^ 2 / h ^ 2 := by
      intro x; rw [div_pow]
    rw [integral_congr_ae (Filter.Eventually.of_forall hdiv), integral_div]
    rw [div_le_iff₀ (by positivity)]
    calc (∫ x, (partialD k φ x) ^ 2) * h ^ 2 = h ^ 2 * ∫ x, (partialD k φ x) ^ 2 := by ring
      _ ≥ ∫ x, (φ (x + v) - φ x) ^ 2 := hmain
  have hnorm := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hnorm

/-! ### Strong `L²` convergence of the difference quotient to the derivative -/

/-- The translation `transL2 (0) ψ = ψ`. -/
private theorem transL2_zero_apply (ψ : EucL2 d) :
    transL2 (0 : EuclideanSpace ℝ (Fin d)) ψ = ψ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_transL2 (0 : EuclideanSpace ℝ (Fin d)) ψ] with x hx
  rw [hx]; simp

/-- **Continuity of translation in `L²`.** The map `w ↦ τ_w ψ` is continuous from the space of
shifts into `L²(ℝⁿ)`. This is the strong continuity of the translation group on `L²(ℝⁿ)`,
obtained from joint continuity of composition with a measure-preserving family (Evans,
*Partial Differential Equations* (2nd ed.), §5.8.2). -/
theorem continuous_transL2 (ψ : EucL2 d) :
    Continuous (fun w : EuclideanSpace ℝ (Fin d) => transL2 w ψ) := by
  set X := EuclideanSpace ℝ (Fin d) with hX
  -- The curried translation family `w ↦ (· + w)` is a continuous map into `C(X, X)`.
  have hcont : Continuous (fun p : X × X => p.2 + p.1) := by fun_prop
  set F : C(X × X, X) := ⟨fun p => p.2 + p.1, hcont⟩ with hF
  set G : C(X, C(X, X)) := F.curry with hG
  have hGw : ∀ w : X, (⇑(G w) : X → X) = fun x => x + w := fun w => rfl
  have hgm : ∀ w : X, MeasurePreserving (⇑(G w)) volume volume := by
    intro w
    rw [hGw w]; exact measurePreserving_add_right volume w
  -- Identify each composition term with `transL2 w ψ`.
  have hterm : ∀ w : X, Lp.compMeasurePreserving (⇑(G w)) (hgm w) ψ = transL2 w ψ := by
    intro w
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_compMeasurePreserving ψ (hgm w), coeFn_transL2 w ψ]
      with x hx1 hx2
    rw [hx1, hx2, hGw w]; rfl
  rw [continuous_iff_continuousAt]
  intro w₀
  have hcAt := ContinuousAt.compMeasurePreservingLp (μ := (volume : Measure X))
    (ν := (volume : Measure X)) (E := ℝ) (p := 2)
    (f := fun _ : X => ψ) (g := fun w => G w) (z := w₀)
    continuousAt_const G.continuous.continuousAt hgm (by norm_num)
  refine hcAt.congr ?_
  filter_upwards with w using hterm w

/-- **Strong `L²` continuity of translation at the origin.** As the shift `w → 0`, the
translated function `τ_w ψ` converges to `ψ` in `L²`. -/
theorem tendsto_transL2_zero (ψ : EucL2 d) :
    Filter.Tendsto (fun w : EuclideanSpace ℝ (Fin d) => transL2 w ψ)
      (nhds 0) (nhds ψ) :=
  (continuous_transL2 ψ).tendsto' 0 ψ (transL2_zero_apply ψ)

/-- The uncurried translate-difference `(x, t) ↦ (ψ (x + t v) - ψ x) ^ 2` is integrable for the
product of Lebesgue measure with the unit-interval slice, for `ψ` continuous with compact
support. Its joint support sits in the bounded slab `closedBall 0 (R + ‖v‖) × Icc 0 1`. -/
private theorem integrable_uncurry_transDiff {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (v : EuclideanSpace ℝ (Fin d)) :
    Integrable (Function.uncurry fun (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) =>
        (ψ (x + t • v) - ψ x) ^ 2)
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  set g : EuclideanSpace ℝ (Fin d) × ℝ → ℝ :=
    Function.uncurry fun (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) =>
      (ψ (x + t • v) - ψ x) ^ 2 with hg
  set ρ : Measure (EuclideanSpace ℝ (Fin d) × ℝ) :=
    volume.prod (volume.restrict (Ioc (0 : ℝ) 1)) with hρ
  have hcont : Continuous g :=
    ((hψc.comp (by fun_prop : Continuous fun p : EuclideanSpace ℝ (Fin d) × ℝ =>
      p.1 + p.2 • v)).sub (hψc.comp continuous_fst)).pow 2
  obtain ⟨R, hR⟩ := hψcs.isCompact.isBounded.subset_closedBall 0
  set C : Set (EuclideanSpace ℝ (Fin d) × ℝ) := closedBall 0 (R + ‖v‖) ×ˢ Icc 0 1 with hC
  have hCcomp : IsCompact C := (isCompact_closedBall _ _).prod isCompact_Icc
  have hIntOn : IntegrableOn g C ρ := hcont.locallyIntegrable.integrableOn_isCompact hCcomp
  have hzero : ∀ p : EuclideanSpace ℝ (Fin d) × ℝ, p.2 ∈ Ioc (0 : ℝ) 1 → p ∉ C → g p = 0 := by
    rintro ⟨x, t⟩ ht hpC
    have hxball : x ∉ closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + ‖v‖) := by
      intro hx; exact hpC ⟨hx, ⟨le_of_lt ht.1, ht.2⟩⟩
    have hxnorm : R + ‖v‖ < ‖x‖ :=
      lt_of_not_ge fun hle => hxball (by simpa [mem_closedBall, dist_eq_norm] using hle)
    have htnorm : ‖t • v‖ ≤ ‖v‖ := by
      rw [norm_smul]
      have htle : ‖t‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_pos ht.1]; exact ht.2
      nlinarith [norm_nonneg v, htle]
    have hψx : ψ x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have hle : ‖x‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hR hmem
      nlinarith [norm_nonneg v]
    have hψxv : ψ (x + t • v) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have hxvR : ‖x + t • v‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hR hmem
      have hxle : ‖x‖ ≤ R + ‖v‖ := by
        calc ‖x‖ = ‖(x + t • v) - t • v‖ := by congr 1; abel
          _ ≤ ‖x + t • v‖ + ‖t • v‖ := norm_sub_le _ _
          _ ≤ R + ‖v‖ := by linarith
      linarith
    simp only [hg, Function.uncurry_apply_pair, hψx, hψxv, sub_self]
    norm_num
  have htioc : ∀ᵐ p ∂ρ, p.2 ∈ Ioc (0 : ℝ) 1 := by
    rw [ae_iff]
    have hset : {p : EuclideanSpace ℝ (Fin d) × ℝ | p.2 ∉ Ioc (0 : ℝ) 1}
        = univ ×ˢ (Ioc (0 : ℝ) 1)ᶜ := by ext p; simp
    rw [hset, hρ, Measure.prod_prod, Measure.restrict_apply' measurableSet_Ioc,
      compl_inter_self, measure_empty, mul_zero]
  have hae : g =ᵐ[ρ] C.indicator g := by
    filter_upwards [htioc] with p hp
    by_cases hpC : p ∈ C
    · rw [indicator_of_mem hpC]
    · rw [indicator_of_notMem hpC, hzero p hp hpC]
  rw [integrable_congr hae]
  exact (integrable_indicator_iff hCcomp.measurableSet).mpr hIntOn

/-- **Squared `L²` bound on the difference-quotient defect.** For `φ` smooth with compact
support and `h ≠ 0`, the squared `L²` distance from the difference quotient `Dₖʰφ` to the
partial derivative `∂ₖφ` is bounded by the integral over `t ∈ [0, 1]` of the squared `L²`
translation defects `‖τ_{t h eₖ} ∂ₖφ - ∂ₖφ‖²`. This is the fundamental-theorem-of-calculus
representation `Dₖʰφ(x) - ∂ₖφ(x) = ∫₀¹ (∂ₖφ(x + t h eₖ) - ∂ₖφ(x)) dt` squared through the
one-variable Cauchy-Schwarz bound and integrated with a Tonelli swap (Evans, *Partial
Differential Equations* (2nd ed.), §5.8.2). -/
private theorem sq_norm_diffQuot_sub_le (k : Fin d) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    (hL2φ : MemLp φ 2 volume) (hL2p : MemLp (partialD k φ) 2 volume)
    (hψc : Continuous (partialD k φ)) (hψcs : HasCompactSupport (partialD k φ))
    {h : ℝ} (hh : h ≠ 0) :
    ‖diffQuot k h (hL2φ.toLp φ) - hL2p.toLp (partialD k φ)‖ ^ 2
      ≤ ∫ t in (0 : ℝ)..1,
          ‖transL2 (t • hshift k h) (hL2p.toLp (partialD k φ))
            - hL2p.toLp (partialD k φ)‖ ^ 2 := by
  set ψ := partialD k φ with hψdef
  set v : EuclideanSpace ℝ (Fin d) := hshift k h with hv
  set ψLp := hL2p.toLp (partialD k φ) with hψLp
  set φLp := hL2φ.toLp φ with hφLp
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hInt := integrable_uncurry_transDiff hψc hψcs v
  -- Pointwise directional derivative identity: `(fderiv φ y) v = h • ∂ₖφ y`.
  have hfv : ∀ y, (fderiv ℝ φ y) v = h * ψ y := fun y => by
    simp [hv, hshift, hψdef, partialD]
  -- Fundamental theorem of calculus, then division by `h`.
  have hHeq : ∀ x, (φ (x + v) - φ x) / h - ψ x
      = ∫ t in (0 : ℝ)..1, (ψ (x + t • v) - ψ x) := by
    intro x
    have hI1 : IntervalIntegrable (fun t => ψ (x + t • v)) volume 0 1 :=
      (hψc.comp (by fun_prop)).intervalIntegrable _ _
    have hI2 : IntervalIntegrable (fun _ : ℝ => ψ x) volume 0 1 := intervalIntegrable_const
    have hnum : φ (x + v) - φ x = h * ∫ t in (0 : ℝ)..1, ψ (x + t • v) := by
      rw [sub_translation_eq_integral hφ x v,
          show (fun t : ℝ => (fderiv ℝ φ (x + t • v)) v) = fun t => h * ψ (x + t • v) from
            funext fun t => hfv (x + t • v),
          intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_sub hI1 hI2, intervalIntegral.integral_const, hnum]
    rw [mul_comm h, mul_div_assoc, div_self hh, mul_one]
    simp
  -- Pointwise square bound via one-variable Cauchy-Schwarz on `[0, 1]`.
  have hsqle : ∀ x, ((φ (x + v) - φ x) / h - ψ x) ^ 2
      ≤ ∫ t in (0 : ℝ)..1, (ψ (x + t • v) - ψ x) ^ 2 := by
    intro x
    rw [hHeq x]
    have hcx : ContinuousOn (fun t : ℝ => ψ (x + t • v) - ψ x) (Set.uIcc 0 1) :=
      ((hψc.comp (by fun_prop)).sub continuous_const).continuousOn
    simpa using MeasureTheory.sq_intervalIntegral_le h01 hcx
  -- Integrability of the left- and right-hand integrands in `x`.
  have hHcont : Continuous (fun x => (φ (x + v) - φ x) / h - ψ x) :=
    (((hφ.continuous.comp (by fun_prop)).sub hφ.continuous).div_const h).sub hψc
  have hcs1 : HasCompactSupport (fun x => (φ (x + v) - φ x) / h) := by
    have hrw : (fun x => (φ (x + v) - φ x) / h)
        = (fun x => φ (x + v) - φ x) * (fun _ => h⁻¹) := by
      funext x; simp [div_eq_mul_inv]
    rw [hrw]
    exact ((hcs.comp_homeomorph (Homeomorph.addRight v)).sub hcs).mul_right
  have hHcs : HasCompactSupport (fun x => (φ (x + v) - φ x) / h - ψ x) := hcs1.sub hψcs
  have hLHS_int : Integrable (fun x => ((φ (x + v) - φ x) / h - ψ x) ^ 2) :=
    (hHcont.fun_pow 2).integrable_of_hasCompactSupport
      (by simpa only [Function.comp_def] using
        hHcs.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num))
  have hRHS_int : Integrable (fun x => ∫ t in (0 : ℝ)..1, (ψ (x + t • v) - ψ x) ^ 2) := by
    simp_rw [intervalIntegral.integral_of_le h01]
    exact hInt.integral_prod_left
  -- Integrate the pointwise bound and swap the order of integration.
  have hmono : ∫ x, ((φ (x + v) - φ x) / h - ψ x) ^ 2
      ≤ ∫ x, ∫ t in (0 : ℝ)..1, (ψ (x + t • v) - ψ x) ^ 2 :=
    integral_mono hLHS_int hRHS_int hsqle
  have hswap : (∫ x, ∫ t in (0 : ℝ)..1, (ψ (x + t • v) - ψ x) ^ 2)
      = ∫ t in (0 : ℝ)..1, ∫ x, (ψ (x + t • v) - ψ x) ^ 2 := by
    simp_rw [intervalIntegral.integral_of_le h01]
    exact integral_integral_swap hInt
  -- The inner `x`-integral is the squared `L²` translation defect.
  have hnormsq : ∀ t : ℝ, (∫ x, (ψ (x + t • v) - ψ x) ^ 2)
      = ‖transL2 (t • v) ψLp - ψLp‖ ^ 2 := by
    intro t
    rw [norm_sq_transL2_sub]
    refine integral_congr_ae ?_
    have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving (· + t • v) volume volume :=
      (measurePreserving_add_right volume (t • v)).quasiMeasurePreserving
    have hshiftAE : (fun x => ψLp (x + t • v)) =ᵐ[volume] fun x => ψ (x + t • v) :=
      hqmp.ae_eq_comp hL2p.coeFn_toLp
    filter_upwards [hL2p.coeFn_toLp, hshiftAE] with x hx1 hx2
    rw [hx2, hx1]
  -- Assemble.
  have hlhs : ‖diffQuot k h φLp - ψLp‖ ^ 2 = ∫ x, ((φ (x + v) - φ x) / h - ψ x) ^ 2 := by
    rw [norm_sq_eq_integral_sq]
    refine integral_congr_ae ?_
    have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving (· + v) volume volume :=
      (measurePreserving_add_right volume v).quasiMeasurePreserving
    have hshiftAE : (fun x => φLp (x + v)) =ᵐ[volume] fun x => φ (x + v) :=
      hqmp.ae_eq_comp hL2φ.coeFn_toLp
    filter_upwards [Lp.coeFn_sub (diffQuot k h φLp) ψLp, coeFn_diffQuot k h φLp,
      hL2φ.coeFn_toLp, hshiftAE, hL2p.coeFn_toLp] with x hx0 hx1 hx2 hx3 hx4
    rw [hx0, Pi.sub_apply, hx1, hx2, hx3, hx4]
  rw [hlhs]
  refine le_trans hmono ?_
  rw [hswap, intervalIntegral.integral_congr (g := fun t => ‖transL2 (t • v) ψLp - ψLp‖ ^ 2)
    (fun t _ => hnormsq t)]

/-- **Strong `L²` convergence of the difference quotient to the derivative.** For `φ` smooth
with compact support and a sequence of nonzero steps `η m → 0`, the difference quotients
`Dₖ^{η m} φ` converge in `L²` to the classical partial derivative `∂ₖφ`. This is the strong
convergence input passed to the limit in the weak-derivative identification (Evans, *Partial
Differential Equations* (2nd ed.), §5.8.2). -/
theorem tendsto_diffQuot_partialD (k : Fin d) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    (hL2φ : MemLp φ 2 volume) (hL2p : MemLp (partialD k φ) 2 volume)
    (η : ℕ → ℝ) (hη0 : ∀ m, η m ≠ 0) (hηlim : Filter.Tendsto η Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m => diffQuot k (η m) (hL2φ.toLp φ)) Filter.atTop
      (nhds (hL2p.toLp (partialD k φ))) := by
  set ψLp := hL2p.toLp (partialD k φ) with hψLp
  set φLp := hL2φ.toLp φ with hφLp
  have hψc : Continuous (partialD k φ) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψcs : HasCompactSupport (partialD k φ) :=
    hcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hfin : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  -- Dominated convergence: the integrated squared translation defects tend to `0`.
  set F : ℕ → ℝ → ℝ := fun m t => ‖transL2 (t • hshift k (η m)) ψLp - ψLp‖ ^ 2 with hF
  have hB : Filter.Tendsto (fun m => ∫ t, F m t ∂(volume.restrict (Ioc (0 : ℝ) 1)))
      Filter.atTop (nhds (∫ _t, (0 : ℝ) ∂(volume.restrict (Ioc (0 : ℝ) 1)))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (2 * ‖ψLp‖) ^ 2) ?_ ?_ ?_ ?_
    · intro m
      refine Continuous.aestronglyMeasurable ?_
      exact ((((continuous_transL2 ψLp).comp
        (by fun_prop : Continuous fun t : ℝ => t • hshift k (η m))).sub
          continuous_const).norm.pow 2)
    · exact integrable_const _
    · intro m
      refine Filter.Eventually.of_forall (fun t => ?_)
      have hb : ‖transL2 (t • hshift k (η m)) ψLp - ψLp‖ ≤ 2 * ‖ψLp‖ := by
        calc ‖transL2 (t • hshift k (η m)) ψLp - ψLp‖
            ≤ ‖transL2 (t • hshift k (η m)) ψLp‖ + ‖ψLp‖ := norm_sub_le _ _
          _ = ‖ψLp‖ + ‖ψLp‖ := by rw [(transL2 _).norm_map]
          _ = 2 * ‖ψLp‖ := by ring
      have hnormF : ‖F m t‖ = ‖transL2 (t • hshift k (η m)) ψLp - ψLp‖ ^ 2 := by
        rw [hF]; exact Real.norm_of_nonneg (sq_nonneg _)
      rw [hnormF]
      exact pow_le_pow_left₀ (norm_nonneg _) hb 2
    · refine Filter.Eventually.of_forall (fun t => ?_)
      have hsm : Filter.Tendsto (fun m => t • hshift k (η m)) Filter.atTop (nhds 0) := by
        have hc : Filter.Tendsto (fun m => (t * η m) • EuclideanSpace.single k (1 : ℝ))
            Filter.atTop (nhds ((0 : ℝ) • EuclideanSpace.single k (1 : ℝ))) :=
          Filter.Tendsto.smul_const (by simpa using hηlim.const_mul t) _
        simpa [hshift, smul_smul] using hc
      have hconv : Filter.Tendsto (fun m => transL2 (t • hshift k (η m)) ψLp)
          Filter.atTop (nhds ψLp) := (tendsto_transL2_zero ψLp).comp hsm
      have hsub : Filter.Tendsto (fun m => transL2 (t • hshift k (η m)) ψLp - ψLp)
          Filter.atTop (nhds 0) := by
        have hc : Filter.Tendsto (fun _ : ℕ => ψLp) Filter.atTop (nhds ψLp) := tendsto_const_nhds
        simpa using hconv.sub hc
      simpa [hF] using (hsub.norm.pow 2)
  -- Reduce to squared-norm convergence and squeeze.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Filter.Tendsto (fun m => ‖diffQuot k (η m) φLp - ψLp‖ ^ 2)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun m => sq_nonneg _) (fun m => ?_) (by simpa using hB)
    have hle := sq_norm_diffQuot_sub_le k hφ hcs hL2φ hL2p hψc hψcs (hη0 m)
    rwa [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hle
  have hfinal := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Real.sqrt_zero, Function.comp_def] at hfinal
  refine hfinal.congr (fun m => ?_)
  rw [Real.sqrt_sq (norm_nonneg _)]

/-! ### Weak sequential compactness and the converse -/

/-- **Weak sequential compactness of bounded sequences in `L²`.** A sequence bounded by `M` in
the separable Hilbert space `EucL2 d` has a subsequence converging weakly to a limit `g'` with
`‖g'‖ ≤ M`. Assembled from the sequential Banach-Alaoglu theorem on the weak dual
(`WeakDual.isSeqCompact_closedBall`), the Riesz self-duality of the Hilbert space
(`InnerProductSpace.toDual`), and the closed-ball membership of the weak-\* limit. -/
theorem exists_weak_limit_of_bounded {x : ℕ → EucL2 d} {M : ℝ} (hx : ∀ m, ‖x m‖ ≤ M) :
    ∃ (g' : EucL2 d) (σ : ℕ → ℕ), StrictMono σ ∧ ‖g'‖ ≤ M ∧
      ∀ y : EucL2 d, Filter.Tendsto (fun m => ⟪x (σ m), y⟫) Filter.atTop (nhds ⟪g', y⟫) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  set F : ℕ → WeakDual ℝ (EucL2 d) :=
    fun m => WeakDual.toStrongDual.symm (InnerProductSpace.toDual ℝ (EucL2 d) (x m)) with hFdef
  have hFtoS : ∀ m, WeakDual.toStrongDual (F m) = InnerProductSpace.toDual ℝ (EucL2 d) (x m) :=
    fun m => WeakDual.toStrongDual.apply_symm_apply _
  have hFmem : ∀ m, F m ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall
      (0 : StrongDual ℝ (EucL2 d)) M := by
    intro m
    simp only [Set.mem_preimage, hFtoS m, Metric.mem_closedBall, dist_zero_right]
    rw [(InnerProductSpace.toDual ℝ (EucL2 d)).norm_map]
    exact hx m
  obtain ⟨L, hLmem, σ, hσmono, hLtend⟩ :=
    WeakDual.isSeqCompact_closedBall ℝ (EucL2 d) 0 M hFmem
  refine ⟨(InnerProductSpace.toDual ℝ (EucL2 d)).symm (WeakDual.toStrongDual L), σ, hσmono, ?_, ?_⟩
  · rw [(InnerProductSpace.toDual ℝ (EucL2 d)).symm.norm_map]
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hLmem
  · intro y
    have heval := (tendsto_iff_forall_eval_tendsto_topDualPairing.mp hLtend) y
    have hL1 : ∀ m, topDualPairing ℝ (EucL2 d) (F (σ m)) y = ⟪x (σ m), y⟫ := by
      intro m
      change (F (σ m)) y = ⟪x (σ m), y⟫
      rw [show (F (σ m)) y = (InnerProductSpace.toDual ℝ (EucL2 d) (x (σ m))) y from rfl,
        InnerProductSpace.toDual_apply_apply]
    have hL2 : topDualPairing ℝ (EucL2 d) L y
        = ⟪(InnerProductSpace.toDual ℝ (EucL2 d)).symm (WeakDual.toStrongDual L), y⟫ := by
      change L y = ⟪(InnerProductSpace.toDual ℝ (EucL2 d)).symm (WeakDual.toStrongDual L), y⟫
      rw [InnerProductSpace.toDual_symm_apply]
      exact (WeakDual.toStrongDual_apply L y).symm
    rw [hL2] at heval
    exact heval.congr (fun m => hL1 m)

/-- **Difference-quotient weak-limit converse (Evans §5.8.2, direction ii).** If the
difference quotients `Dₖʰ g` are uniformly `L²`-bounded by `M` over all `h ≠ 0`, then `g` has a
weak `k`-derivative `g'` in `L²` with `‖g'‖ ≤ M`. The sequence `Dₖ^{1/(m+1)} g` is bounded, so
by weak sequential compactness a subsequence converges weakly to some `g'` with `‖g'‖ ≤ M`;
passing to the limit in the discrete integration-by-parts identity
`⟪Dₖʰ g, ζ⟫ = -⟪g, Dₖ^{-h} ζ⟫`, using the strong `L²` convergence `Dₖ^{-hₘ} ζ → ∂ₖζ` for a
test function `ζ`, identifies `g'` as the weak derivative (Evans, *Partial Differential
Equations* (2nd ed.), §5.8.2, Theorem 3). -/
theorem weakDeriv_of_diffQuot_bounded (k : Fin d) (g : EucL2 d) (M : ℝ)
    (hb : ∀ h : ℝ, h ≠ 0 → ‖diffQuot k h g‖ ≤ M) :
    ∃ g' : EucL2 d, HasWeakDeriv k g g' ∧ ‖g'‖ ≤ M := by
  set hseq : ℕ → ℝ := fun m => 1 / (m + 1) with hhseq
  have hseq_ne : ∀ m, hseq m ≠ 0 := fun m => by positivity
  have hseq_lim : Filter.Tendsto hseq Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  set X : ℕ → EucL2 d := fun m => diffQuot k (hseq m) g with hX
  have hXb : ∀ m, ‖X m‖ ≤ M := fun m => hb (hseq m) (hseq_ne m)
  obtain ⟨g', σ, hσmono, hg'norm, hg'weak⟩ := exists_weak_limit_of_bounded hXb
  refine ⟨g', ?_, hg'norm⟩
  intro ζ hζc hζcs
  -- `L²` classes of the test function and its `k`-th derivative.
  have hζMemLp : MemLp ζ 2 volume := hζc.continuous.memLp_of_hasCompactSupport (μ := volume) hζcs
  have hζpc : Continuous (partialD k ζ) :=
    (hζc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hζpcs : HasCompactSupport (partialD k ζ) :=
    hζcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hζpMemLp : MemLp (partialD k ζ) 2 volume :=
    hζpc.memLp_of_hasCompactSupport (μ := volume) hζpcs
  set ζLp := hζMemLp.toLp ζ with hζLp
  set ζpLp := hζpMemLp.toLp (partialD k ζ) with hζpLp
  -- The negated step sequence tends to `0` through nonzero values.
  have hη0 : ∀ m, -(hseq (σ m)) ≠ 0 := fun m => neg_ne_zero.mpr (hseq_ne (σ m))
  have hηlim : Filter.Tendsto (fun m => -(hseq (σ m))) Filter.atTop (nhds 0) := by
    simpa using (hseq_lim.comp hσmono.tendsto_atTop).neg
  -- Weak convergence along the subsequence, and strong convergence of the adjoint quotient.
  have hlimA : Filter.Tendsto (fun m => ⟪X (σ m), ζLp⟫) Filter.atTop (nhds ⟪g', ζLp⟫) :=
    hg'weak ζLp
  have hstrong : Filter.Tendsto (fun m => diffQuot k (-(hseq (σ m))) ζLp) Filter.atTop
      (nhds ζpLp) :=
    tendsto_diffQuot_partialD k hζc hζcs hζMemLp hζpMemLp _ hη0 hηlim
  have hinner : Filter.Tendsto (fun m => ⟪g, diffQuot k (-(hseq (σ m))) ζLp⟫) Filter.atTop
      (nhds ⟪g, ζpLp⟫) := tendsto_const_nhds.inner hstrong
  have hlimB : Filter.Tendsto (fun m => ⟪X (σ m), ζLp⟫) Filter.atTop (nhds (-⟪g, ζpLp⟫)) := by
    refine hinner.neg.congr (fun m => ?_)
    exact (diffQuot_inner_adjoint k (hseq (σ m)) g ζLp).symm
  have hkey : ⟪g', ζLp⟫ = -⟪g, ζpLp⟫ := tendsto_nhds_unique hlimA hlimB
  -- Translate the inner products back to integrals.
  have hinnerG' : ⟪g', ζLp⟫ = ∫ x, g' x * ζ x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hζMemLp.coeFn_toLp] with x hx
    rw [RCLike.inner_apply, conj_trivial, hx, mul_comm]
  have hinnerG : ⟪g, ζpLp⟫ = ∫ x, g x * partialD k ζ x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hζpMemLp.coeFn_toLp] with x hx
    rw [RCLike.inner_apply, conj_trivial, hx, mul_comm]
  rw [hinnerG', hinnerG] at hkey
  linarith [hkey]

/-! ### General weak-derivative direction-i bound -/

/-- The uncurried product `(x, t) ↦ g(x) · ψ(x - t v)` of an `L²` class `g` with a translate
of a continuous compactly supported `ψ` is integrable for the product of Lebesgue measure with
the unit-interval slice. Off the compact slab `closedBall 0 (R + ‖v‖) × Icc 0 1` the translate
`ψ(x - t v)` vanishes, and on the slab the `L²` factor `g` is locally integrable, so the product
is dominated by the integrable indicator `M · ‖g‖ · 1_ball` (Evans, *Partial Differential
Equations* (2nd ed.), §5.8.2). -/
private theorem integrable_uncurry_weak (g : EucL2 d) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (v : EuclideanSpace ℝ (Fin d)) :
    Integrable (Function.uncurry fun (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) => g x * ψ (x - t • v))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  set ρ : Measure (EuclideanSpace ℝ (Fin d) × ℝ) :=
    volume.prod (volume.restrict (Ioc (0 : ℝ) 1)) with hρ
  change Integrable (fun p : EuclideanSpace ℝ (Fin d) × ℝ => g p.1 * ψ (p.1 - p.2 • v)) ρ
  obtain ⟨M, hM⟩ := hψc.bounded_above_of_compact_support hψcs
  obtain ⟨R, hR⟩ := hψcs.isCompact.isBounded.subset_closedBall 0
  set B : Set (EuclideanSpace ℝ (Fin d)) := closedBall 0 (R + ‖v‖) with hB
  have hBfin : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  -- The `L²` factor is integrable on the ball.
  have hgB : Integrable (fun x => ‖g x‖) (volume.restrict B) := by
    have h1 : MemLp (⇑g) 1 (volume.restrict B) :=
      ((Lp.memLp g).restrict B).mono_exponent (by norm_num)
    exact (memLp_one_iff_integrable.mp h1).norm
  -- The dominating indicator function is integrable on the product.
  set Dx : EuclideanSpace ℝ (Fin d) → ℝ := B.indicator (fun x => M * ‖g x‖) with hDx
  have hDxint : Integrable Dx volume :=
    (integrable_indicator_iff measurableSet_closedBall).mpr (hgB.const_mul M)
  have hDint : Integrable (fun p : EuclideanSpace ℝ (Fin d) × ℝ => Dx p.1) ρ :=
    hDxint.comp_fst (volume.restrict (Ioc (0 : ℝ) 1))
  -- Joint measurability of the integrand.
  have haesm : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin d) × ℝ => g p.1 * ψ (p.1 - p.2 • v)) ρ := by
    refine (Lp.aestronglyMeasurable g).comp_fst.mul ?_
    exact (hψc.comp (by fun_prop : Continuous
      fun p : EuclideanSpace ℝ (Fin d) × ℝ => p.1 - p.2 • v)).aestronglyMeasurable
  -- Almost every point has `t ∈ Ioc 0 1`, where the slab support argument applies.
  have htioc : ∀ᵐ p ∂ρ, p.2 ∈ Ioc (0 : ℝ) 1 := by
    rw [ae_iff]
    have hset : {p : EuclideanSpace ℝ (Fin d) × ℝ | p.2 ∉ Ioc (0 : ℝ) 1}
        = univ ×ˢ (Ioc (0 : ℝ) 1)ᶜ := by ext p; simp
    rw [hset, hρ, Measure.prod_prod, Measure.restrict_apply' measurableSet_Ioc,
      compl_inter_self, measure_empty, mul_zero]
  refine Integrable.mono' hDint haesm ?_
  filter_upwards [htioc] with p hp
  by_cases hpB : p.1 ∈ B
  · rw [hDx, indicator_of_mem hpB]
    calc ‖g p.1 * ψ (p.1 - p.2 • v)‖ = ‖g p.1‖ * ‖ψ (p.1 - p.2 • v)‖ := norm_mul _ _
      _ ≤ ‖g p.1‖ * M := by gcongr; exact hM _
      _ = M * ‖g p.1‖ := by ring
  · rw [hDx, indicator_of_notMem hpB]
    have hzero : ψ (p.1 - p.2 • v) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      apply hpB
      have hxK : ‖p.1 - p.2 • v‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hR hmem
      have htnorm : ‖p.2 • v‖ ≤ ‖v‖ := by
        rw [norm_smul]
        have htle : ‖p.2‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_pos hp.1]; exact hp.2
        nlinarith [norm_nonneg v, htle]
      have hxle : ‖p.1‖ ≤ R + ‖v‖ := by
        calc ‖p.1‖ = ‖(p.1 - p.2 • v) + p.2 • v‖ := by congr 1; abel
          _ ≤ ‖p.1 - p.2 • v‖ + ‖p.2 • v‖ := norm_add_le _ _
          _ ≤ R + ‖v‖ := by linarith
      simpa [hB, mem_closedBall, dist_eq_norm] using hxle
    rw [hzero, mul_zero, norm_zero]

/-- **Segment-integral representation of the difference quotient (weak derivative).** For `g`
with `L²` weak `k`-derivative `g'` and a smooth compactly supported test function `ζ`, the inner
product of `Dₖʰ g` against `ζ` is the `[0, 1]` integral of the inner products of `g'` against the
translates `τ_{-t h eₖ} ζ`. This is the `L²`-tested form of the fundamental-theorem representation
`Dₖʰ g(x) = ∫₀¹ g'(x + t h eₖ) dt`, obtained by moving `Dₖʰ` onto `ζ` (discrete integration by
parts), the classical fundamental theorem of calculus along the segment, a Tonelli swap, and the
weak-derivative identity applied to each translated test function (Evans, *Partial Differential
Equations* (2nd ed.), §5.8.2). -/
private theorem inner_diffQuot_eq_integral_smooth (k : Fin d) (g g' : EucL2 d)
    (hg : HasWeakDeriv k g g') {h : ℝ} (hh : h ≠ 0)
    {ζ : EuclideanSpace ℝ (Fin d) → ℝ} (hζcd : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζcs : HasCompactSupport ζ) (hζ : MemLp ζ 2 volume) :
    ⟪diffQuot k h g, hζ.toLp ζ⟫
      = ∫ t in (0 : ℝ)..1, ⟪g', transL2 (-(t • hshift k h)) (hζ.toLp ζ)⟫ := by
  set v : EuclideanSpace ℝ (Fin d) := hshift k h with hv
  set ζLp := hζ.toLp ζ with hζLp
  have hψc : Continuous (partialD k ζ) :=
    (hζcd.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψcs : HasCompactSupport (partialD k ζ) :=
    hζcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  -- The directional derivative of `ζ` along `-v` is `(-h) · ∂ₖζ`.
  have hlin : ∀ y, (fderiv ℝ ζ y) (-v) = (-h) * partialD k ζ y := by
    intro y
    have hneg : (-v) = (-h) • EuclideanSpace.single k (1 : ℝ) := by
      rw [hv, hshift]; exact (neg_smul h _).symm
    rw [hneg, map_smul, smul_eq_mul]; rfl
  -- Fundamental theorem of calculus, divided by `-h`.
  have hFTC : ∀ x, (ζ (x + (-v)) - ζ x) / (-h)
      = ∫ t in (0 : ℝ)..1, partialD k ζ (x - t • v) := by
    intro x
    have h1 : ζ (x + (-v)) - ζ x = ∫ t in (0 : ℝ)..1, (-h) * partialD k ζ (x - t • v) := by
      rw [sub_translation_eq_integral hζcd x (-v)]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      rw [hlin (x + t • (-v))]
      congr 2
      rw [smul_neg, sub_eq_add_neg]
    rw [h1, intervalIntegral.integral_const_mul, mul_comm, mul_div_assoc,
      div_self (neg_ne_zero.mpr hh), mul_one]
  -- Move `Dₖʰ` onto `ζ` and expand the resulting inner product as an `x`-integral.
  have hshkneg : hshift k (-h) = -v := by rw [hshift_neg, hv]
  have hstep2 : ⟪g, diffQuot k (-h) ζLp⟫
      = ∫ x, g x * (∫ t in (0 : ℝ)..1, partialD k ζ (x - t • v)) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving (· + hshift k (-h)) volume volume :=
      (measurePreserving_add_right volume _).quasiMeasurePreserving
    have hshiftAE : (fun x => ζLp (x + hshift k (-h))) =ᵐ[volume]
        fun x => ζ (x + hshift k (-h)) := hqmp.ae_eq_comp hζ.coeFn_toLp
    filter_upwards [coeFn_diffQuot k (-h) ζLp, hζ.coeFn_toLp, hshiftAE] with x hx1 hx2 hx3
    rw [RCLike.inner_apply, conj_trivial, hx1, hx2, hx3, hshkneg, hFTC x]; ring
  -- Tonelli swap.
  have hswap : (∫ x, g x * (∫ t in (0 : ℝ)..1, partialD k ζ (x - t • v)))
      = ∫ t in (0 : ℝ)..1, ∫ x, g x * partialD k ζ (x - t • v) := by
    have hInt := integrable_uncurry_weak g hψc hψcs v
    simp_rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    rw [← integral_integral_swap hInt]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact (integral_const_mul _ _).symm
  -- The weak-derivative identity for each translated test function.
  have hpert : ∀ t : ℝ, (∫ x, g x * partialD k ζ (x - t • v))
      = -⟪g', transL2 (-(t • v)) ζLp⟫ := by
    intro t
    set φt : EuclideanSpace ℝ (Fin d) → ℝ := fun y => ζ (y - t • v) with hφt
    have hφtcd : ContDiff ℝ (⊤ : ℕ∞) φt :=
      hζcd.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
        fun y : EuclideanSpace ℝ (Fin d) => y - t • v)
    have hφtcs : HasCompactSupport φt := by
      simpa only [hφt, Function.comp_def, Homeomorph.coe_addRight, sub_eq_add_neg] using
        hζcs.comp_homeomorph (Homeomorph.addRight (-(t • v)))
    have hpd : ∀ x, partialD k φt x = partialD k ζ (x - t • v) := by
      intro x
      have hτ : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => y - t • v)
          (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) x := by
        simpa using (hasFDerivAt_id x).sub_const (t • v)
      have hcomp : HasFDerivAt φt
          ((fderiv ℝ ζ (x - t • v)).comp (ContinuousLinearMap.id ℝ _)) x :=
        ((hζcd.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x hτ
      simp only [partialD, hcomp.fderiv, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply]
    have hR : ⟪g', transL2 (-(t • v)) ζLp⟫ = ∫ x, g' x * ζ (x - t • v) := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving
          (· + (-(t • v))) volume volume :=
        (measurePreserving_add_right volume _).quasiMeasurePreserving
      have hae : (fun x => ζLp (x + (-(t • v)))) =ᵐ[volume]
          fun x => ζ (x + (-(t • v))) := hqmp.ae_eq_comp hζ.coeFn_toLp
      filter_upwards [coeFn_transL2 (-(t • v)) ζLp, hae] with x hx1 hx2
      rw [RCLike.inner_apply, conj_trivial, hx1, hx2, sub_eq_add_neg]; ring
    calc ∫ x, g x * partialD k ζ (x - t • v)
        = ∫ x, g x * partialD k φt x := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_)); simp only [hpd]
      _ = -∫ x, g' x * φt x := hg φt hφtcd hφtcs
      _ = -⟪g', transL2 (-(t • v)) ζLp⟫ := by rw [← hR]
  -- Assemble.
  rw [diffQuot_inner_adjoint k h g ζLp, hstep2, hswap,
    intervalIntegral.integral_congr
      (g := fun t => -⟪g', transL2 (-(t • v)) ζLp⟫) (fun t _ => hpert t),
    intervalIntegral.integral_neg, neg_neg]

/-- **Difference-quotient bound against a smooth compactly supported test element.** For `g` with
`L²` weak `k`-derivative `g'`, the inner product of `Dₖʰ g` against the `L²` class of a smooth
compactly supported `ζ` is bounded by `‖g'‖ · ‖ζ‖`. This follows from the segment-integral
representation by the Cauchy-Schwarz inequality and the translation isometry, integrated over the
unit interval (Evans, *Partial Differential Equations* (2nd ed.), §5.8.2). -/
private theorem inner_diffQuot_le_smooth (k : Fin d) (g g' : EucL2 d)
    (hg : HasWeakDeriv k g g') {h : ℝ} (hh : h ≠ 0)
    {ζ : EuclideanSpace ℝ (Fin d) → ℝ} (hζcd : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζcs : HasCompactSupport ζ) (hζ : MemLp ζ 2 volume) :
    ⟪diffQuot k h g, hζ.toLp ζ⟫ ≤ ‖g'‖ * ‖hζ.toLp ζ‖ := by
  set v : EuclideanSpace ℝ (Fin d) := hshift k h with hv
  set ζLp := hζ.toLp ζ with hζLp
  rw [inner_diffQuot_eq_integral_smooth k g g' hg hh hζcd hζcs hζ]
  have hcont : Continuous (fun t : ℝ => ⟪g', transL2 (-(t • v)) ζLp⟫) :=
    continuous_const.inner ((continuous_transL2 ζLp).comp (by fun_prop))
  have hbd : ∀ t ∈ Icc (0 : ℝ) 1, ⟪g', transL2 (-(t • v)) ζLp⟫ ≤ ‖g'‖ * ‖ζLp‖ := by
    intro t _
    calc ⟪g', transL2 (-(t • v)) ζLp⟫ ≤ ‖g'‖ * ‖transL2 (-(t • v)) ζLp‖ := real_inner_le_norm _ _
      _ = ‖g'‖ * ‖ζLp‖ := by rw [(transL2 _).norm_map]
  calc ∫ t in (0 : ℝ)..1, ⟪g', transL2 (-(t • v)) ζLp⟫
      ≤ ∫ _t in (0 : ℝ)..1, ‖g'‖ * ‖ζLp‖ :=
        intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable 0 1)
          intervalIntegrable_const hbd
    _ = ‖g'‖ * ‖ζLp‖ := by rw [intervalIntegral.integral_const]; simp

/-- **Weak-derivative difference-quotient bound (Evans §5.8.2, direction i).** A function `g`
with `L²` weak `k`-derivative `g'` has difference quotients bounded in `L²` by the derivative:
`‖Dₖʰ g‖ ≤ ‖g'‖`, uniformly in the step `h`. This is the general form of the tight single-direction
bound `norm_diffQuot_le_of_contDiff`, obtained by testing `Dₖʰ g` against the smooth compactly
supported functions (dense in `L²`), where the segment-integral representation gives the bound
`⟪Dₖʰ g, ζ⟫ ≤ ‖g'‖ · ‖ζ‖`, then passing to the limit along a smooth sequence converging to
`Dₖʰ g` itself (Evans, *Partial Differential Equations* (2nd ed.), §5.8.2, Theorem 3). -/
theorem norm_diffQuot_le_of_hasWeakDeriv (k : Fin d) (g g' : EucL2 d)
    (hg : HasWeakDeriv k g g') (h : ℝ) : ‖diffQuot k h g‖ ≤ ‖g'‖ := by
  rcases eq_or_ne h 0 with rfl | hh
  · rw [diffQuot_zero, _root_.zero_apply, norm_zero]
    exact norm_nonneg _
  -- Smooth compactly supported functions are dense in `L²`.
  set S : Set (EucL2 d) := {f : EucL2 d | ∃ ρ : EuclideanSpace ℝ (Fin d) → ℝ,
    f =ᵐ[volume] ρ ∧ HasCompactSupport ρ ∧ ContDiff ℝ (⊤ : ℕ∞) ρ} with hS
  have hdense : Dense S :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff
      (F := ℝ) (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (by norm_num)
  -- The inner-product bound is first proved against smooth compactly supported test elements.
  have hbound : ∀ f : EucL2 d, f ∈ S → ⟪diffQuot k h g, f⟫ ≤ ‖g'‖ * ‖f‖ := by
    rintro f ⟨ρ, hfρ, hρcs, hρcd⟩
    have hρL2 : MemLp ρ 2 volume := hρcd.continuous.memLp_of_hasCompactSupport hρcs
    have hfeq : f = hρL2.toLp ρ := Lp.ext (hfρ.trans hρL2.coeFn_toLp.symm)
    rw [hfeq]
    exact inner_diffQuot_le_smooth k g g' hg hh hρcd hρcs hρL2
  -- A smooth sequence converges to `Dₖʰ g`; pass the bound to the limit.
  have hmem : diffQuot k h g ∈ closure S := by rw [hdense.closure_eq]; trivial
  obtain ⟨u, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.mp hmem
  have h1 : Filter.Tendsto (fun n => ⟪diffQuot k h g, u n⟫) Filter.atTop
      (nhds ⟪diffQuot k h g, diffQuot k h g⟫) := tendsto_const_nhds.inner hu_lim
  have h2 : Filter.Tendsto (fun n => ‖g'‖ * ‖u n‖) Filter.atTop
      (nhds (‖g'‖ * ‖diffQuot k h g‖)) := hu_lim.norm.const_mul ‖g'‖
  have h3 : ⟪diffQuot k h g, diffQuot k h g⟫ ≤ ‖g'‖ * ‖diffQuot k h g‖ :=
    le_of_tendsto_of_tendsto' h1 h2 (fun n => hbound (u n) (hu_mem n))
  rw [real_inner_self_eq_norm_mul_norm] at h3
  rcases eq_or_lt_of_le (norm_nonneg (diffQuot k h g)) with hzero | hpos
  · rw [← hzero]; exact norm_nonneg _
  · exact le_of_mul_le_mul_right h3 hpos

end EllipticPdes.Regularity
