/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.Inverse
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SpectralGap.Curvature
public import LeanPool.KLS.FunctionalInequalities.L2.Components

/-!
# The centered inverse of the heat-model generator

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Lemma 2.1, operator-domain part. In the heat model
`ν = m.tilted (-U)` with `U ∈ C²`, the closed unit-gradient `Tbar` has the constants as kernel, so
`(ker Tbar)ᗮ` is the centered subspace of `L²(ν)`. If the literature Poincaré constant satisfies
`C_P(ν) ≤ C`, the generator `A = Tbar†Tbar = -ℒ` has, for every centered `g ∈ L²(ν)`, exactly one
centered preimage `u` in its operator domain, with `‖u‖ ≤ C ‖g‖`, `‖Tbaru‖² = ⟪g, u⟫ ≤ C ‖g‖²`
(BKL (20)) and the centered-gradient bound `‖∇₀u‖ ≤ √C ‖g‖` (BKL (24)). With `C = C_P(ν)` these are
the source's constants `λ⁻¹`, `λ⁻¹` and `λ^{-1/2}` (in dimension `0`, `C_P = 0` and every centered
function vanishes). For `G`-valued centered data the inverse lifts componentwise: in an orthonormal
basis of a finite-dimensional `G`, exactly one centered family `u_k` solves `A u_k = ⟪b k, g⟫`, with
`Σ_k ‖u_k‖² ≤ C² ‖g‖²` (the source's tensor version, operator-domain part). This is a restricted
counterpart of the source lemma: the polynomial-growth class `𝒜`, smooth representatives and the
pointwise equation are not proved here.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace
open MeasureTheory

namespace FunctionalInequalities.KLS.LogConcave

open Analysis.Semigroup Analysis.Semigroup.Generated

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)

include hνU hU in
/-- In the heat model `ν = m.tilted (-U)`, a form-domain vector is orthogonal to the kernel of the
closed unit gradient exactly when its mean vanishes (the kernel is the constants). -/
theorem orthogonal_ker_iff_mean_eq_zero
    (y : Lp ℝ 2 (ν : Measure V)) :
    (∀ k : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi k = 0 →
          ⟪y, (k : Lp ℝ 2 (ν : Measure V))⟫ = 0) ↔ L2.mean ν y = 0 := by
    have inner_const_eq_mean_mul :
        ∀ (f : Lp ℝ 2 (ν : Measure V)) (c : ℝ),
          ⟪f, L2.const ν c⟫ = c * L2.mean ν f := by
      intro f c
      rw [MeasureTheory.L2.inner_def, L2.mean_eq_integral]
      calc
        (∫ x, ⟪f x, (L2.const ν c) x⟫_ℝ ∂(ν : Measure V)) =
            ∫ x, f x * c ∂(ν : Measure V) := by
              apply integral_congr_ae
              filter_upwards [L2.const_coeFn ν c] with x hx
              rw [hx]
              simp
              ring
        _ = (∫ x, f x ∂(ν : Measure V)) * c := by
              rw [integral_mul_const]
        _ = c * ∫ x, f x ∂(ν : Measure V) := by
              ring
    constructor
    · intro hy
      let k :
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain :=
        ⟨L2.const ν 1,
          one_mem_domain_closedWeightedOperator
            (ν := ν) m (ContinuousLinearMap.id ℝ V) hν hi⟩
      have hk :
          hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi k = 0 := by
        simpa [k] using
          hν.closedWeightedOperator_one_eq_zero
            m (ContinuousLinearMap.id ℝ V) hi
      have hinner : ⟪y, (k : Lp ℝ 2 (ν : Measure V))⟫ = 0 :=
        hy k hk
      calc
        L2.mean ν y = 1 * L2.mean ν y := by ring
        _ = ⟪y, L2.const ν 1⟫ := by
          symm
          exact inner_const_eq_mean_mul y 1
        _ = ⟪y, (k : Lp ℝ 2 (ν : Measure V))⟫ := by
          rfl
        _ = 0 := hinner
    · intro hy k hk
      have hkeq :
          (k : Lp ℝ 2 (ν : Measure V)) =
            L2.const ν (L2.mean ν (k : Lp ℝ 2 (ν : Measure V))) :=
        (closedWeightedOperator_eq_zero_iff
          m hν hi hνU hU k).mp hk
      calc
        ⟪y, (k : Lp ℝ 2 (ν : Measure V))⟫ =
            ⟪y, L2.const ν (L2.mean ν (k : Lp ℝ 2 (ν : Measure V)))⟫ := by
              exact congrArg (fun z => ⟪y, z⟫) hkeq
        _ = L2.mean ν (k : Lp ℝ 2 (ν : Measure V)) * L2.mean ν y := by
              exact inner_const_eq_mean_mul y _
        _ = 0 := by
              rw [hy]
              simp

include hνU hU in
/--
**BKL Lemma 2.1, operator-domain part (existence and uniqueness).** If the literature Poincaré
constant of `ν` is at most `C`, then for every centered `g ∈ L²(ν)` there is exactly one centered
`u` in the domain of the generator `A = Tbar†Tbar` with `A u = g` (`A = -ℒ`). -/
theorem existsUnique_centered_adjointComp_eq {C : NNReal}
    (hC : Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ (C : ENNReal)) (g : Lp ℝ 2 (ν : Measure V))
    (hg : L2.mean ν g = 0) :
    ∃! u : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
      L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0 ∧
        adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u = g := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have hT : T.IsClosed := by
    simpa [T] using hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  have hd : Dense (T.domain : Set (Lp ℝ 2 (ν : Measure V))) := by
    simpa [T] using hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have hgap :
    ∀ y : T.domain,
      (∀ k : T.domain,
          T k = 0 → ⟪(y : Lp ℝ 2 (ν : Measure V)), (k : Lp ℝ 2 (ν : Measure V))⟫ = 0) →
        ‖(y : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤ (C : ℝ) * ‖T y‖ ^ 2 := by
    intro y hy
    have hmy : L2.mean ν (y : Lp ℝ 2 (ν : Measure V)) = 0 :=
      (orthogonal_ker_iff_mean_eq_zero m hν hi hνU hU (y : Lp ℝ 2 (ν : Measure V))).mp
        (by simpa [T] using hy)
    have h := hν.closedWeightedOperator_id_gap_of_literature_le m hi (C : NNReal) hC y
    simpa [T, L2.center, hmy] using h
  have hgorth : ∀ k : T.domain, T k = 0 → ⟪g, (k : Lp ℝ 2 (ν : Measure V))⟫ = 0 := by
    have h := (orthogonal_ker_iff_mean_eq_zero m hν hi hνU hU g).mpr hg
    simpa [T] using h
  obtain ⟨u, huorth, hueq⟩ := exists_adjointComp_eq_of_gap T hT hd hgap g hgorth
  refine ⟨u, ?_, ?_⟩
  · constructor
    · exact
        (orthogonal_ker_iff_mean_eq_zero m hν hi hνU hU (u : Lp ℝ 2 (ν : Measure V))).mp
          (by simpa [T] using huorth)
    · simpa [T] using hueq
  · intro v hv
    have hvorth :
      ∀ k : T.domain,
        T k = 0 → ⟪(v : Lp ℝ 2 (ν : Measure V)), (k : Lp ℝ 2 (ν : Measure V))⟫ = 0 := by
      have h :=
        (orthogonal_ker_iff_mean_eq_zero m hν hi hνU hU (v : Lp ℝ 2 (ν : Measure V))).mpr hv.1
      simpa [T] using h
    have hEq : adjointComp T v = adjointComp T u := by
      calc
        adjointComp T v = g := by simpa [T] using hv.2
        _ = adjointComp T u := hueq.symm
    have hvu : (v : Lp ℝ 2 (ν : Measure V)) = (u : Lp ℝ 2 (ν : Measure V)) :=
      eq_of_adjointComp_eq T hd v u hvorth huorth hEq
    exact Subtype.ext hvu

include hνU hU in
/-- **BKL Lemma 2.1, operator-domain part (bounds (20) and (24)).** With `C ≥ C_P(ν) = λ⁻¹`, a
centered `u` in the generator domain with `A u = g` satisfies `‖u‖ ≤ C ‖g‖`,
`‖Tbar u‖² = ⟪g, u⟫ ≤ C ‖g‖²` and `‖Tbar u‖ ≤ √C ‖g‖`. -/
theorem centered_adjointComp_bounds {C : NNReal}
    (hC : Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ (C : ENNReal))
    (u : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hu : L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0) :
    ‖(u : Lp ℝ 2 (ν : Measure V))‖ ≤
        (C : ℝ) *
          ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ ∧
      ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ ^
            2 =
          ⟪adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u,
            (u : Lp ℝ 2 (ν : Measure V))⟫ ∧
        ⟪adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u,
              (u : Lp ℝ 2 (ν : Measure V))⟫ ≤
            (C : ℝ) *
              ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ ^
                2 ∧
          ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ ≤
            Real.sqrt C *
              ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ := by
  have hd :
    Dense
      ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain :
        Set (Lp ℝ 2 (ν : Measure V))) :=
    hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have hgap :
    ∀ y : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
      (∀ k : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
          hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi k = 0 →
            ⟪(y : Lp ℝ 2 (ν : Measure V)), (k : Lp ℝ 2 (ν : Measure V))⟫ = 0) →
        ‖(y : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
          (C : ℝ) * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi y‖ ^ 2 := by
    intro y hy
    have hymean : L2.mean ν (y : Lp ℝ 2 (ν : Measure V)) = 0 :=
      (orthogonal_ker_iff_mean_eq_zero m hν hi hνU hU (y : Lp ℝ 2 (ν : Measure V))).mp hy
    have hcenter : L2.center ν (y : Lp ℝ 2 (ν : Measure V)) = (y : Lp ℝ 2 (ν : Measure V)) := by
      simp [L2.center, hymean]
    have h := hν.closedWeightedOperator_id_gap_of_literature_le m hi C hC y
    rw [hcenter] at h
    exact h
  have huorth :
    ∀ k : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi k = 0 →
        ⟪(u : Lp ℝ 2 (ν : Measure V)), (k : Lp ℝ 2 (ν : Measure V))⟫ = 0 :=
    (orthogonal_ker_iff_mean_eq_zero m hν hi hνU hU (u : Lp ℝ 2 (ν : Measure V))).mpr hu
  obtain ⟨hu₁, hu₂, hu₃⟩ :=
    norm_le_of_gap (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) hd hgap u
      huorth
  refine ⟨hu₁, hu₂, hu₃, ?_⟩
  have hsq :
    ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ ^
        2 ≤
      (C : ℝ) *
        ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ ^ 2 := by
    rw [hu₂]
    exact hu₃
  have hsqrt : (Real.sqrt (C : ℝ)) ^ 2 = (C : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt (C : ℝ) := Real.sqrt_nonneg _
  have hnorm₁ :
    0 ≤
      ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ :=
    norm_nonneg _
  have hnorm₂ :
    0 ≤ ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ :=
    norm_nonneg _
  by_contra hnot
  have hlt :
    Real.sqrt (C : ℝ) *
        ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ <
      ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ :=
    lt_of_not_ge hnot
  have hprod :
    0 ≤
      Real.sqrt (C : ℝ) *
        ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ :=
    mul_nonneg hsqrt_nonneg hnorm₂
  have hsum :
    0 <
      ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ +
        Real.sqrt (C : ℝ) *
          ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ := by
    linarith
  have hfac :
    0 <
      (‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ -
          Real.sqrt (C : ℝ) *
            ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖) *
        (‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ +
          Real.sqrt (C : ℝ) *
            ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖) :=
    mul_pos (sub_pos.mpr hlt) hsum
  have hsq' :
    (Real.sqrt (C : ℝ) *
          ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖) ^
        2 =
      (C : ℝ) *
        ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ ^ 2 := by
    rw [mul_pow, hsqrt]
  nlinarith [hfac, hsq, hsq']

omit [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- Subtracting the mean vector does not increase the `L²` norm: `‖w - ∫ w‖ ≤ ‖w‖` for vector-valued
`w ∈ L²(ν; V)` (BKL (23)). -/
private theorem norm_sub_const_integral_le (w : Lp V 2 (ν : Measure V)) :
    ‖w - Lp.const 2 (ν : Measure V) (∫ x, w x ∂(ν : Measure V))‖ ≤ ‖w‖ := by
    let c : V := ∫ x, w x ∂(ν : Measure V)
    let k : Lp V 2 (ν : Measure V) := Lp.const 2 (ν : Measure V) c
    have hw : Integrable (w : V → V) (ν : Measure V) :=
      (Lp.memLp w).integrable (by norm_num)
    have hconst : ∀ᵐ x ∂(ν : Measure V), k x = c := by
      simp [k]
    have hkw : ⟪w, k⟫_ℝ = ⟪c, c⟫_ℝ := by
      rw [MeasureTheory.L2.inner_def]
      calc
        (∫ x, ⟪w x, k x⟫_ℝ ∂(ν : Measure V)) =
            ∫ x, ⟪w x, c⟫_ℝ ∂(ν : Measure V) := by
              apply integral_congr_ae
              filter_upwards [hconst] with x hx
              rw [hx]
        _ = ∫ x, ⟪c, w x⟫_ℝ ∂(ν : Measure V) := by
              apply integral_congr_ae
              filter_upwards [] with x
              rw [real_inner_comm]
        _ = ⟪c, ∫ x, w x ∂(ν : Measure V)⟫_ℝ := by
              exact integral_inner hw c
        _ = ⟪c, c⟫_ℝ := by
              rfl
    have hkk : ⟪k, k⟫_ℝ = ⟪c, c⟫_ℝ := by
      rw [MeasureTheory.L2.inner_def]
      calc
        (∫ x, ⟪k x, k x⟫_ℝ ∂(ν : Measure V)) =
            ∫ x, ⟪c, c⟫_ℝ ∂(ν : Measure V) := by
              apply integral_congr_ae
              filter_upwards [hconst] with x hx
              rw [hx]
        _ = ⟪c, c⟫_ℝ := by
              simp
    have horth : ⟪w - k, k⟫_ℝ = 0 := by
      rw [inner_sub_left, hkw, hkk]
      ring
    have hadd := norm_add_sq_real (w - k) k
    rw [horth] at hadd
    have hsq : ‖w‖ ^ 2 = ‖w - k‖ ^ 2 + ‖k‖ ^ 2 := by
      simpa [sub_add_cancel] using hadd
    dsimp [c, k] at hsq ⊢
    nlinarith [
      norm_nonneg (w - Lp.const 2 (ν : Measure V)
        (∫ x, w x ∂(ν : Measure V))),
      norm_nonneg w,
      sq_nonneg ‖Lp.const 2 (ν : Measure V)
        (∫ x, w x ∂(ν : Measure V))‖
    ]

include hνU hU in
/--
**BKL (24)** in the operator-domain form: the centered gradient `∇₀u = Tbaru - ∫ Tbaru dν` of the
centered solution satisfies `‖∇₀ u‖ ≤ √C ‖A u‖`. -/
theorem norm_centered_gradient_le {C : NNReal}
    (hC : Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ (C : ENNReal))
    (u : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hu : L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0) :
    ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩ -
          Lp.const 2 (ν : Measure V)
            (∫ x,
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                    ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩ :
                  Lp V 2 (ν : Measure V))
                x ∂(ν : Measure V))‖ ≤
      Real.sqrt C *
        ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ := by
  refine
    le_trans
      (norm_sub_const_integral_le
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩))
      ?_
  exact (centered_adjointComp_bounds m hν hi hνU hU hC u hu).2.2.2

include hν hi hνU hU in
/-- Under the curvature bound `∇∇U ≥ ρ > 0` the hypotheses hold with `C = ρ⁻¹` (BGL Corollary
4.8.2): every centered `g` has a unique centered preimage `u` under `A`, and `‖u‖ ≤ ρ⁻¹ ‖g‖`. -/
theorem existsUnique_centered_adjointComp_eq_of_hessian {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (g : Lp ℝ 2 (ν : Measure V)) (hg : L2.mean ν g = 0) :
    ∃! u : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
      L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0 ∧
        adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u = g ∧
          ‖(u : Lp ℝ 2 (ν : Measure V))‖ ≤ ρ⁻¹ * ‖g‖ := by
    let C : NNReal := ⟨ρ⁻¹, (inv_pos.mpr hρ).le⟩
    have hCeq : ENNReal.ofReal ρ⁻¹ = (C : ENNReal) := by
      rw [ENNReal.ofReal_eq_coe_nnreal]
      rfl
    have hC : Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ (C : ENNReal) := by
      have h :=
        literatureConstant_le_inv m hν hi hνU hU hρ hH
      rw [hCeq] at h
      exact h
    obtain ⟨u, hu, huniq⟩ :=
      existsUnique_centered_adjointComp_eq m hν hi hνU hU hC g hg
    have hb :=
      (centered_adjointComp_bounds m hν hi hνU hU hC u hu.1).1
    rw [hu.2] at hb
    have hbound : ‖(u : Lp ℝ 2 (ν : Measure V))‖ ≤ ρ⁻¹ * ‖g‖ := by
      have hCval : (C : ℝ) = ρ⁻¹ := by
        rfl
      rw [hCval] at hb
      exact hb
    refine ⟨u, ⟨hu.1, hu.2, hbound⟩, ?_⟩
    intro v hv
    exact huniq v ⟨hv.1, hv.2.1⟩

section Components

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {ι : Type*} [Fintype ι]

include hνU hU in
/--
**BKL Lemma 2.1, operator-domain part, componentwise tensor lift.** If `C_P(ν) ≤ C`, then for
every centered `g ∈ L²(ν; G)` and orthonormal basis `b` of `G` there is exactly one family of
centered
`u_k` in the generator domain with `A u_k = ⟪b k, g⟫`, and `Σ_k ‖u_k‖² ≤ C² ‖g‖²`. -/
theorem existsUnique_centered_adjointComp_eq_components {C : NNReal}
    (hC : Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ (C : ENNReal)) (b : OrthonormalBasis ι ℝ G)
    (g : Lp G 2 (ν : Measure V)) (hg : ∫ x, g x ∂(ν : Measure V) = 0) :
    ∃! u :
      ι → (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
      (∀ k, L2.mean ν (u k : Lp ℝ 2 (ν : Measure V)) = 0) ∧
        (∀ k,
            adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (u k) =
              (innerSL ℝ (b k)).compLp g) ∧
          ∑ k, ‖(u k : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤ (C : ℝ) ^ 2 * ‖g‖ ^ 2 := by
  classical
  have hgk (k : ι) : L2.mean ν ((innerSL ℝ (b k)).compLp g) = 0 := by
    rw [L2.mean_compLp_innerSL, hg]
    simp
  have hs (k : ι) :
    ∃! u : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
      L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0 ∧
        adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u =
          (innerSL ℝ (b k)).compLp g :=
    existsUnique_centered_adjointComp_eq m hν hi hνU hU hC ((innerSL ℝ (b k)).compLp g) (hgk k)
  let u :
    ι → (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain :=
    fun k => Classical.choose ((hs k).exists)
  have hu (k : ι) :
    L2.mean ν (u k : Lp ℝ 2 (ν : Measure V)) = 0 ∧
      adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (u k) =
        (innerSL ℝ (b k)).compLp g :=
    Classical.choose_spec ((hs k).exists)
  have hbound (k : ι) :
    ‖(u k : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤ (C : ℝ) ^ 2 * ‖(innerSL ℝ (b k)).compLp g‖ ^ 2 := by
    have hk := (centered_adjointComp_bounds m hν hi hνU hU hC (u k) (hu k).1).1
    rw [(hu k).2] at hk
    calc
      ‖(u k : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤ ((C : ℝ) * ‖(innerSL ℝ (b k)).compLp g‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg C.2 (norm_nonneg _))).2 hk
      _ = (C : ℝ) ^ 2 * ‖(innerSL ℝ (b k)).compLp g‖ ^ 2 := mul_pow _ _ _
  refine ⟨u, ⟨fun k => (hu k).1, fun k => (hu k).2, ?_⟩, ?_⟩
  · calc
      ∑ k, ‖(u k : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
          ∑ k, (C : ℝ) ^ 2 * ‖(innerSL ℝ (b k)).compLp g‖ ^ 2 :=
        Finset.sum_le_sum (fun k _ => hbound k)
      _ = (C : ℝ) ^ 2 * ∑ k, ‖(innerSL ℝ (b k)).compLp g‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ = (C : ℝ) ^ 2 * ‖g‖ ^ 2 := by rw [L2.sum_norm_sq_compLp_innerSL b g]
  · intro v hv
    funext k
    exact (hs k).unique ⟨hv.1 k, hv.2.1 k⟩ (hu k)

include hν hi hνU hU in
/-- The componentwise lift under the curvature bound `∇∇U ≥ ρ > 0`, with `C = ρ⁻¹`. -/
theorem existsUnique_centered_adjointComp_eq_components_of_hessian {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (b : OrthonormalBasis ι ℝ G) (g : Lp G 2 (ν : Measure V))
    (hg : ∫ x, g x ∂(ν : Measure V) = 0) :
    ∃! u : ι → (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
      (∀ k, L2.mean ν (u k : Lp ℝ 2 (ν : Measure V)) = 0) ∧
        (∀ k, adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (u k) =
          (innerSL ℝ (b k)).compLp g) ∧
          ∑ k, ‖(u k : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤ ρ⁻¹ ^ 2 * ‖g‖ ^ 2 := by
  let C : NNReal := ⟨ρ⁻¹, (inv_pos.mpr hρ).le⟩
  have hCeq : ENNReal.ofReal ρ⁻¹ = (C : ENNReal) :=
    ENNReal.ofReal_eq_coe_nnreal (inv_pos.mpr hρ).le
  have hC : Poincare.LocalSlope.Intrinsic.optimalConstant ν ≤ (C : ENNReal) := by
    have h := literatureConstant_le_inv m hν hi hνU hU hρ hH
    rw [hCeq] at h
    exact h
  have hCval : (C : ℝ) = ρ⁻¹ := rfl
  simpa only [hCval] using
    (existsUnique_centered_adjointComp_eq_components
      (C := C) m hν hi hνU hU hC b g hg)

end Components

end FunctionalInequalities.KLS.LogConcave
