/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.MulIterated


/-!
# Cutoff transport of weak derivatives to the ambient domain

The induction of Guo, *Partial Differential Equations* (Course Lecture Notes), Theorem
VIII.3.2 (p. 65) runs on a pair `V ⋐ W ⋐ Ω`. The order-`k` conclusion is available on the
compact `W`, and the datum the induction hypothesis consumes needs its weak derivatives on all
of `Ω`. `EllipticPdes.Regularity.HasIteratedWeakDerivOn.restrict` moves a family the other way,
from `W` down to a smaller set, and is no help here.

Extension by zero is what closes the gap, and it needs the function to vanish near the boundary
of `W`. A cutoff supplies that: for a test function `χ` supported in `W`, the product `χ · p`
extended by zero to `Ω` has as many weak derivatives on `Ω` as `p` has on `W`.

## Keystone identity

Against a test function `φ` supported in `Ω`, the product `χ · φ` is a test function supported
in `tsupport χ ⊆ W`, so the weak derivative of `p` on `W` may be tested against it:

`∫_W p ∂_ℓ(χφ) = - ∫_W p' χφ`.

Expanding `∂_ℓ(χφ) = (∂_ℓχ)φ + χ(∂_ℓφ)` and moving the first summand across gives

`∫_W (χp) ∂_ℓφ = - ∫_W ((∂_ℓχ)p + χp') φ`,

and both sides may be read over `Ω` instead of `W`, since `χ` kills the integrand off `W`.
That is the statement that `(∂_ℓχ)p + χp'` is the weak `ℓ`-derivative of `χp` on `Ω`. Nothing
about `∂W` is needed, and no extension operator on Sobolev spaces appears: the cutoff does all
the work.

## Order-`k` family

The recursion is the one `EllipticPdes.Regularity.exists_iteratedWeakDeriv_mul` uses. The
`ℓ`-derivative of `χ·p` is `(∂_ℓχ)·p + χ·(∂_ℓp)`, and each summand is again a test function
supported in `W` against a function with `k` weak derivatives on `W`, so the statement recurses
on its own conclusion. Test functions are closed under `partialD`, which is what lets the weight
change at each step without leaving the hypothesis.

## Main declarations

* `isTestFn_partialD`: test functions are closed under a classical partial derivative.
* `setIntegral_mul_mulTest_partialD`: the integration by parts the cutoff makes admissible.
* `HasWeakDerivOn.extend_mulTest`: one weak derivative, from `W` to `Ω`, across a cutoff.
* `hasWeakDeriv_extend_mulTest`: the same, on the whole space.
* `exists_iteratedWeakDeriv_extend_mulTest`: the order-`k` family and its bound.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Test functions are closed under a partial derivative -/

/-- A classical partial derivative of a test function is a test function on the same set. -/
theorem isTestFn_partialD {W : Set (EuclideanSpace ℝ (Fin d))}
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn W χ) (ℓ : Fin d) :
    IsTestFn W (partialD ℓ χ) :=
  isTest_partialD hχ.1 hχ.2.1 hχ.2.2 ℓ

/-- An integral over `Ω` of an integrand vanishing off `W ⊆ Ω` is an integral over `W`. -/
private theorem setIntegral_shrink_of_forall_eq_zero
    {W Ω : Set (EuclideanSpace ℝ (Fin d))} (hWΩ : W ⊆ Ω)
    {F : EuclideanSpace ℝ (Fin d) → ℝ} (hF : ∀ x, x ∉ W → F x = 0) :
    ∫ x in Ω, F x = ∫ x in W, F x := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hF x (fun hc => hx (hWΩ hc))),
    setIntegral_eq_integral_of_forall_compl_eq_zero hF]

/-- The whole-space extension of an `L²(W)` class agrees with the class itself on `W`. -/
private theorem coeFn_extendL2_restrict {W : Set (EuclideanSpace ℝ (Fin d))}
    (hWm : MeasurableSet W) (p : L2D W) :
    (extendL2 hWm p : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict W] (p : EuclideanSpace ℝ (Fin d) → ℝ) := by
  filter_upwards [ae_restrict_of_ae (coeFn_extendL2 hWm p), ae_restrict_mem hWm] with x h1 h2
  rw [h1, Set.indicator_of_mem h2]

/-! ### Integration by parts the cutoff makes admissible -/

/-- **Integration by parts against a cut-off test function.** For `χ` supported in `W` and a
weak `ℓ`-derivative `p'` of `p` on `W`,

`∫_W p · (χ ∂_ℓφ) = - ∫_W ((∂_ℓχ)p + χp') · φ`

for every smooth `φ`, asking neither compact support nor a support condition of it. The product
`χφ` is compactly supported in `tsupport χ ⊆ W` whatever `φ` does, so it is admissible for the
weak derivative, and expanding `∂_ℓ(χφ)` moves the term where the derivative lands on the
cutoff across.

This is the one identity the cutoff gives, and everything else in this file and in Evans's step
3 is bookkeeping around it. -/
theorem setIntegral_mul_mulTest_partialD {W : Set (EuclideanSpace ℝ (Fin d))}
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn W χ) {ℓ : Fin d} {p p' : L2D W}
    (h : HasWeakDerivOn W ℓ p p') {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφc : ContDiff ℝ (⊤ : ℕ∞) φ) :
    (∫ x in W, (p x : ℝ) * (χ x * partialD ℓ φ x))
      = -∫ x in W, (partialD ℓ χ x * (p x : ℝ) + χ x * (p' x : ℝ)) * φ x := by
  have : ENNReal.HolderTriple (2 : ENNReal) 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  have hχd : Differentiable ℝ χ := hχ.1.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφc.differentiable (by simp)
  -- The three continuous compactly supported weights the identity is tested against.
  have hAc : Continuous fun x => χ x * partialD ℓ φ x :=
    hχ.continuous.mul (contDiff_partialD hφc ℓ).continuous
  have hBc : Continuous fun x => partialD ℓ χ x * φ x :=
    (hχ.continuous_partialD ℓ).mul hφc.continuous
  have hCc : Continuous fun x => χ x * φ x := hχ.continuous.mul hφc.continuous
  have hAcs : HasCompactSupport fun x => χ x * partialD ℓ φ x := hχ.2.1.mul_right
  have hBcs : HasCompactSupport fun x => partialD ℓ χ x * φ x :=
    (hχ.hasCompactSupport_partialD ℓ).mul_right
  have hCcs : HasCompactSupport fun x => χ x * φ x := hχ.2.1.mul_right
  have hAL : MemLp (fun x => χ x * partialD ℓ φ x) 2 (volume.restrict W) :=
    (hAc.memLp_of_hasCompactSupport (p := 2) (μ := volume) hAcs).restrict W
  have hBL : MemLp (fun x => partialD ℓ χ x * φ x) 2 (volume.restrict W) :=
    (hBc.memLp_of_hasCompactSupport (p := 2) (μ := volume) hBcs).restrict W
  have hCL : MemLp (fun x => χ x * φ x) 2 (volume.restrict W) :=
    (hCc.memLp_of_hasCompactSupport (p := 2) (μ := volume) hCcs).restrict W
  have iA : Integrable (fun x => (p x : ℝ) * (χ x * partialD ℓ φ x)) (volume.restrict W) :=
    (Lp.memLp p).integrable_mul hAL
  have iB : Integrable (fun x => (p x : ℝ) * (partialD ℓ χ x * φ x)) (volume.restrict W) :=
    (Lp.memLp p).integrable_mul hBL
  have iC : Integrable (fun x => (p' x : ℝ) * (χ x * φ x)) (volume.restrict W) :=
    (Lp.memLp p').integrable_mul hCL
  -- The derivative on `W`, tested against the admissible `χφ`.
  have key := h (fun x => χ x * φ x) (hχ.1.mul hφc) hCcs
    (tsupport_mul_subset_left.trans hχ.2.2)
  rw [partialD_mul hχd hφd ℓ] at key
  have hsplit : (∫ x in W, (p x : ℝ) * (χ x * partialD ℓ φ x + partialD ℓ χ x * φ x))
      = (∫ x in W, (p x : ℝ) * (χ x * partialD ℓ φ x))
        + ∫ x in W, (p x : ℝ) * (partialD ℓ χ x * φ x) := by
    rw [← integral_add iA iB]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hsplit] at key
  have hmerge : (∫ x in W, (partialD ℓ χ x * (p x : ℝ) + χ x * (p' x : ℝ)) * φ x)
      = (∫ x in W, (p x : ℝ) * (partialD ℓ χ x * φ x))
        + ∫ x in W, (p' x : ℝ) * (χ x * φ x) := by
    rw [← integral_add iB iC]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hmerge]
  linarith [key]

/-! ### One derivative across the cutoff -/

/-- **Transport of one weak derivative from `W` up to `Ω` by a cutoff.** For a test function `χ`
supported in `W ⊆ Ω` and a weak `ℓ`-derivative `p'` of `p` on `W`, any `L²(Ω)` class
representing `χ·p` has `(∂_ℓχ)·p + χ·p'` as its weak `ℓ`-derivative on `Ω`.

The classes are given through a.e. representations rather than as named products, matching
`EllipticPdes.Regularity.norm_le_of_ae_mul`, because the consumers assemble their own.

The proof tests the `W`-derivative against `χφ`, which is admissible because `χ` is supported
in `W`, and reads the Leibniz expansion of `∂_ℓ(χφ)` backwards. Each integral over `Ω` becomes
one over `W` because `χ` vanishes off its support. -/
theorem HasWeakDerivOn.extend_mulTest {W Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hWm : MeasurableSet W) (hWΩ : W ⊆ Ω)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn W χ) {ℓ : Fin d} {p p' : L2D W}
    (h : HasWeakDerivOn W ℓ p p') {q q' : L2D Ω}
    (hq : q =ᵐ[volume.restrict Ω] fun x => χ x * (extendL2 hWm p x : ℝ))
    (hq' : q' =ᵐ[volume.restrict Ω] fun x =>
      partialD ℓ χ x * (extendL2 hWm p x : ℝ) + χ x * (extendL2 hWm p' x : ℝ)) :
    HasWeakDerivOn Ω ℓ q q' := by
  intro φ hφc _hφcs _hφΩ
  have hEp := coeFn_extendL2_restrict hWm p
  have hEp' := coeFn_extendL2_restrict hWm p'
  -- The left-hand side, moved down to `W`.
  have hL : (∫ x in Ω, (q x : ℝ) * partialD ℓ φ x)
      = ∫ x in W, (p x : ℝ) * (χ x * partialD ℓ φ x) := by
    have e1 : (∫ x in Ω, (q x : ℝ) * partialD ℓ φ x)
        = ∫ x in Ω, χ x * (extendL2 hWm p x : ℝ) * partialD ℓ φ x := by
      refine integral_congr_ae ?_
      filter_upwards [hq] with x hx
      rw [hx]
    rw [e1, setIntegral_shrink_of_forall_eq_zero hWΩ (fun x hx => by
      rw [show χ x = 0 from image_eq_zero_of_notMem_tsupport (fun hc => hx (hχ.2.2 hc))]
      ring)]
    refine integral_congr_ae ?_
    filter_upwards [hEp] with x hx
    rw [hx]
    ring
  -- The right-hand side, moved down to `W`.
  have hR : (∫ x in Ω, (q' x : ℝ) * φ x)
      = ∫ x in W, (partialD ℓ χ x * (p x : ℝ) + χ x * (p' x : ℝ)) * φ x := by
    have e1 : (∫ x in Ω, (q' x : ℝ) * φ x)
        = ∫ x in Ω, (partialD ℓ χ x * (extendL2 hWm p x : ℝ)
            + χ x * (extendL2 hWm p' x : ℝ)) * φ x := by
      refine integral_congr_ae ?_
      filter_upwards [hq'] with x hx
      rw [hx]
    rw [e1, setIntegral_shrink_of_forall_eq_zero hWΩ (fun x hx => by
      rw [show χ x = 0 from image_eq_zero_of_notMem_tsupport (fun hc => hx (hχ.2.2 hc)),
        show partialD ℓ χ x = 0 from image_eq_zero_of_notMem_tsupport
          (fun hc => hx (hχ.2.2 (tsupport_partialD_subset ℓ χ hc)))]
      ring)]
    refine integral_congr_ae ?_
    filter_upwards [hEp, hEp'] with x h1 h2
    rw [h1, h2]
  rw [hL, hR]
  exact setIntegral_mul_mulTest_partialD hχ h hφc

/-- **Transport of one weak derivative from `W` up to the whole space by a cutoff.** The same
identity as `HasWeakDerivOn.extend_mulTest` with the ambient set taken to be everything, which is
the form `EllipticPdes.Regularity.HasWeakDeriv.unique` consumes.

Stated separately rather than instantiated, because `L²(univ)` and `L²(ℝᵈ)` are different types
and the conversion is longer than the proof. -/
theorem hasWeakDeriv_extend_mulTest {W : Set (EuclideanSpace ℝ (Fin d))}
    (hWm : MeasurableSet W) {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn W χ)
    {ℓ : Fin d} {p p' : L2D W} (h : HasWeakDerivOn W ℓ p p') {q q' : EucL2 d}
    (hq : q =ᵐ[volume] fun x => χ x * (extendL2 hWm p x : ℝ))
    (hq' : q' =ᵐ[volume] fun x =>
      partialD ℓ χ x * (extendL2 hWm p x : ℝ) + χ x * (extendL2 hWm p' x : ℝ)) :
    HasWeakDeriv ℓ q q' := by
  intro φ hφc _hφcs
  have hEp := coeFn_extendL2_restrict hWm p
  have hEp' := coeFn_extendL2_restrict hWm p'
  have hL : (∫ x, (q x : ℝ) * partialD ℓ φ x)
      = ∫ x in W, (p x : ℝ) * (χ x * partialD ℓ φ x) := by
    have e1 : (∫ x, (q x : ℝ) * partialD ℓ φ x)
        = ∫ x, χ x * (extendL2 hWm p x : ℝ) * partialD ℓ φ x := by
      refine integral_congr_ae ?_
      filter_upwards [hq] with x hx
      rw [hx]
    rw [e1, ← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [show χ x = 0 from image_eq_zero_of_notMem_tsupport (fun hc => hx (hχ.2.2 hc))]
      ring)]
    refine integral_congr_ae ?_
    filter_upwards [hEp] with x hx
    rw [hx]
    ring
  have hR : (∫ x, (q' x : ℝ) * φ x)
      = ∫ x in W, (partialD ℓ χ x * (p x : ℝ) + χ x * (p' x : ℝ)) * φ x := by
    have e1 : (∫ x, (q' x : ℝ) * φ x)
        = ∫ x, (partialD ℓ χ x * (extendL2 hWm p x : ℝ)
            + χ x * (extendL2 hWm p' x : ℝ)) * φ x := by
      refine integral_congr_ae ?_
      filter_upwards [hq'] with x hx
      rw [hx]
    rw [e1, ← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [show χ x = 0 from image_eq_zero_of_notMem_tsupport (fun hc => hx (hχ.2.2 hc)),
        show partialD ℓ χ x = 0 from image_eq_zero_of_notMem_tsupport
          (fun hc => hx (hχ.2.2 (tsupport_partialD_subset ℓ χ hc)))]
      ring)]
    refine integral_congr_ae ?_
    filter_upwards [hEp, hEp'] with x h1 h2
    rw [h1, h2]
  rw [hL, hR]
  exact setIntegral_mul_mulTest_partialD hχ h hφc

/-! ### Order-`k` family across the cutoff -/

/-- **Transport of `k` weak derivatives from `W` up to `Ω` by a cutoff.** For a test function `χ`
supported in `W ⊆ Ω` there is a constant `K`, depending on `χ` and `k` alone, such that whenever
`p` has weak derivatives to order `k` on `W` bounded by `M`, every `L²(Ω)` class representing
`χ·p` has weak derivatives to order `k` on `Ω` bounded by `K·M`.

The induction is on `k`, with the weight quantified inside so that it may change at each step.
`HasWeakDerivOn.extend_mulTest` supplies the single derivative
`∂_ℓ(χ·p) = (∂_ℓχ)·p + χ·(∂_ℓp)`, and the induction hypothesis covers each summand: the first
with the weight `∂_ℓχ`, again a test function supported in `W`, and the second with the
function `∂_ℓp`, whose order-`k` family is `HasIteratedWeakDerivOn.deriv`. -/
theorem exists_iteratedWeakDeriv_extend_mulTest {W Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hWm : MeasurableSet W) (hWΩ : W ⊆ Ω) :
    ∀ (k : ℕ) {χ : EuclideanSpace ℝ (Fin d) → ℝ}, IsTestFn W χ →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : L2D W} (hp : HasIteratedWeakDerivOn W k p) {q : L2D Ω},
        (q =ᵐ[volume.restrict Ω] fun x => χ x * (extendL2 hWm p x : ℝ)) → ∀ {M : ℝ},
        IteratedL2Bound hp M →
        ∃ H : HasIteratedWeakDerivOn Ω k q, IteratedL2Bound H (K * M) := by
  -- The order-zero bound, which both cases need: `‖χ·p‖ ≤ (sup |χ|) ‖p‖ ≤ (sup |χ|) M`.
  have base : ∀ {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn W χ) {p : L2D W} {q : L2D Ω},
      (q =ᵐ[volume.restrict Ω] fun x => χ x * (extendL2 hWm p x : ℝ)) →
      ‖q‖ ≤ (exists_abs_bound hχ).choose * ‖p‖ := by
    intro χ hχ p q hq
    have hag : q =ᵐ[volume.restrict Ω]
        fun x => χ x * ((restrictL2 (Ω := Ω) (extendL2 hWm p)) x : ℝ) := by
      filter_upwards [hq, coeFn_restrictL2 (Ω := Ω) (extendL2 hWm p)] with x h1 h2
      rw [h1, h2]
    refine (norm_le_of_ae_mul hχ.continuous.measurable
      (Filter.Eventually.of_forall (exists_abs_bound hχ).choose_spec) hag).trans ?_
    refine mul_le_mul_of_nonneg_left ?_
      (le_trans (abs_nonneg (χ 0)) ((exists_abs_bound hχ).choose_spec 0))
    refine (norm_restrictL2_le _).trans ?_
    rw [norm_extendL2]
  intro k
  induction k with
  | zero =>
    intro χ hχ
    refine ⟨(exists_abs_bound hχ).choose,
      le_trans (abs_nonneg (χ 0)) ((exists_abs_bound hχ).choose_spec 0), ?_⟩
    intro p hp q hq M hM
    exact ⟨HasIteratedWeakDerivOn.zero q, fun α _ =>
      (base hχ hq).trans (mul_le_mul_of_nonneg_left hM.norm_le
        (le_trans (abs_nonneg (χ 0)) ((exists_abs_bound hχ).choose_spec 0)))⟩
  | succ k ih =>
    intro χ hχ
    obtain ⟨K0, hK0, hP0⟩ := ih hχ
    choose K1 hK1 hP1 using fun ℓ : Fin d => ih (isTestFn_partialD hχ ℓ)
    have hCχ : (0 : ℝ) ≤ (exists_abs_bound hχ).choose :=
      le_trans (abs_nonneg (χ 0)) ((exists_abs_bound hχ).choose_spec 0)
    have hKsum : 0 ≤ ∑ ℓ : Fin d, K1 ℓ := Finset.sum_nonneg fun ℓ _ => hK1 ℓ
    refine ⟨(exists_abs_bound hχ).choose + K0 + ∑ ℓ, K1 ℓ, by linarith, ?_⟩
    intro p hp q hq M hM
    set K := (exists_abs_bound hχ).choose + K0 + ∑ ℓ : Fin d, K1 ℓ with hKdef
    have hM0 : 0 ≤ M := le_trans (norm_nonneg p) hM.norm_le
    -- One derivative of `χ·p` in each direction, with its own order-`k` family.
    have hstep : ∀ ℓ : Fin d, ∃ (dq : L2D Ω) (F : HasIteratedWeakDerivOn Ω k dq),
        HasWeakDerivOn Ω ℓ q dq ∧ IteratedL2Bound F (K * M) := by
      intro ℓ
      set q1 : L2D Ω := mulTest ((isTestFn_partialD hχ ℓ).mono hWΩ)
        (restrictL2 (Ω := Ω) (extendL2 hWm p)) with hq1def
      set q2 : L2D Ω := mulTest (hχ.mono hWΩ)
        (restrictL2 (Ω := Ω) (extendL2 hWm (hp.D [ℓ]))) with hq2def
      have hq1ae : q1 =ᵐ[volume.restrict Ω]
          fun x => partialD ℓ χ x * (extendL2 hWm p x : ℝ) := by
        filter_upwards [mulTest_coeFn ((isTestFn_partialD hχ ℓ).mono hWΩ)
            (restrictL2 (Ω := Ω) (extendL2 hWm p)),
          coeFn_restrictL2 (Ω := Ω) (extendL2 hWm p)] with x h1 h2
        rw [h1, h2]
      have hq2ae : q2 =ᵐ[volume.restrict Ω]
          fun x => χ x * (extendL2 hWm (hp.D [ℓ]) x : ℝ) := by
        filter_upwards [mulTest_coeFn (hχ.mono hWΩ)
            (restrictL2 (Ω := Ω) (extendL2 hWm (hp.D [ℓ]))),
          coeFn_restrictL2 (Ω := Ω) (extendL2 hWm (hp.D [ℓ]))] with x h1 h2
        rw [h1, h2]
      have hsum : (q1 + q2) =ᵐ[volume.restrict Ω] fun x =>
          partialD ℓ χ x * (extendL2 hWm p x : ℝ)
            + χ x * (extendL2 hWm (hp.D [ℓ]) x : ℝ) := by
        filter_upwards [Lp.coeFn_add q1 q2, hq1ae, hq2ae] with x hadd h1 h2
        simp only [hadd, Pi.add_apply, h1, h2]
      -- The bound on the family of `∂_ℓ p`, read off the family of `p`.
      have hMderiv : IteratedL2Bound (hp.deriv ℓ) M := by
        intro α hα
        exact hM (α ++ [ℓ]) (by simpa [List.length_append] using Nat.succ_le_succ hα)
      obtain ⟨H1, hH1⟩ := hP1 ℓ (hp.mono (Nat.le_succ k)) hq1ae
        (hM.mono_order (Nat.le_succ k))
      obtain ⟨H2, hH2⟩ := hP0 (hp.deriv ℓ) hq2ae hMderiv
      refine ⟨q1 + q2, H1.add H2, ?_, ?_⟩
      · exact HasWeakDerivOn.extend_mulTest hWm hWΩ hχ (hp.hasWeakDerivOn_D_singleton ℓ) hq hsum
      · intro α hα
        have hle : K1 ℓ ≤ ∑ ℓ' : Fin d, K1 ℓ' :=
          Finset.single_le_sum (fun i _ => hK1 i) (Finset.mem_univ ℓ)
        calc ‖(H1.add H2).D α‖ = ‖H1.D α + H2.D α‖ := rfl
          _ ≤ ‖H1.D α‖ + ‖H2.D α‖ := norm_add_le _ _
          _ ≤ K1 ℓ * M + K0 * M := add_le_add (hH1 α hα) (hH2 α hα)
          _ ≤ K * M := by
              rw [hKdef, ← add_mul]
              exact mul_le_mul_of_nonneg_right (by linarith) hM0
    choose dq F hleib hbnd using hstep
    have hq0 : ‖q‖ ≤ K * M := by
      refine (base hχ hq).trans ?_
      calc (exists_abs_bound hχ).choose * ‖p‖
          ≤ (exists_abs_bound hχ).choose * M := mul_le_mul_of_nonneg_left hM.norm_le hCχ
        _ ≤ K * M := by
            rw [hKdef]
            exact mul_le_mul_of_nonneg_right (by linarith) hM0
    exact ⟨HasIteratedWeakDerivOn.ofDeriv hleib F, IteratedL2Bound.ofDeriv hq0 hbnd⟩

end EllipticPdes.Regularity
