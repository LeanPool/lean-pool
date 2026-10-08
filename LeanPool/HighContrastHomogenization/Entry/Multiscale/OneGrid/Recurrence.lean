/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.OneGrid.HistoryMajorization

/-!
# High-contrast homogenization: Entry.Multiscale.OneGrid.Recurrence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Step 2 — the powered parent–child recurrence

Group E of the printed proof (`p.fixed.geometry.one.grid.propagation`), first part: the parent–child
recurrence as this decomposition consumes it, the bridge between the mixed Schatten norm and
the profile's printed moment, and the powered form `e.fixed.geometry.parent.child.powered`.

Part of the proof of `HCPoly/Entry/Statements/OneGridPropagation.lean`.
Conventions of the group:
`q = 𝒬(𝔪)` is `Geometry.explicitRoundedGrid jStar metric` at every loss, history, profile and drift;
`metric` (not `m`) names the positive matrix, because `m`, `n`, `m₀` are generations; the
source lower scale `e.source.lower.scale` is carried exactly by the
source-facing declaration `HCPoly/Entry/OneGridPropagation.lean`; this group's stronger internal
algebraic and history lemmas omit an unused threshold, and this group's generic
integration helpers take finiteness, integrability or measurability inputs that are proved
at their actual use sites, not extra premises of the printed proposition.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-! ## Group E. Step 2 — profile contraction (`p.fixed.geometry.one.grid.propagation`) -/

/-- The parent–child recurrence, `p.fixed.geometry.parent.child.recurrence`
(`p.fixed.geometry.parent.child.recurrence`), repeated here with the exact type of
`HCPolySupport.HighContrast.Entry.fixed_geometry_parent_child_recurrence`.

This bridge is discharged by one exact application of the
`Entry.fixed_geometry_parent_child_recurrence`; its elaborated type is identical to that
of the theorem it applies. -/
theorem parent_child_recurrence_input (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ)
        (_hP : IsProbabilityMeasure P) (_hstat : IsStationaryLaw P) (_hunit : IsUnitRangeLaw P)
        (_hell : CoarseEllipticityDagger P γ E Ψ K S)
        (N : ℕ) (_hN : 2 ≤ N) (_hNeven : Even N)
        (jStar : ℕ) (_hj : 2 * d ≤ 3 ^ jStar)
        (_hsrc : ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ))
        (m : Mat d) (_hm : m.PosDef)
        (j h : ℤ) (_hjgen : (jStar : ℤ) ≤ j) (_hh : 1 ≤ h),
        lqSchattenNorm P (N : ℝ)
            (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar m) (j + h)) ≤
          (N : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) * (1 + (2 * (d : ℝ)) ^ ((N : ℝ))⁻¹) *
                (3 : ℝ) ^ (-((d : ℝ) / 2) * (h : ℝ)) *
                Real.exp (detIncrement P (Geometry.explicitRoundedGrid jStar m) j (j + h)) *
              lqSchattenNorm P (N : ℝ)
                (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar m) j) +
            2 * (1 + (d : ℝ) ^ (1 - ((N : ℝ))⁻¹)) *
                Real.exp
                  ((1 - ((N : ℝ))⁻¹) *
                    detIncrement P (Geometry.explicitRoundedGrid jStar m) j (j + h)) *
                (Real.exp (detIncrement P (Geometry.explicitRoundedGrid jStar m) j (j + h)) - 1) ^
                  ((N : ℝ))⁻¹ := by
  exact HCPolySupport.HighContrast.Entry.fixed_geometry_parent_child_recurrence d hd γ hγ

/-- The bridge between the recurrence's mixed norm `‖·‖_{L^Q(S_Q)}` and the profile's printed
moment `E[|V^q_j|_{S_Q}^Q]`: the `Q`-th power of the first is the second.  The real Schatten
index and the natural outer power are exactly as `HCPoly/Entry/Setup/Profile.lean` records. -/
theorem lqSchattenNorm_pow_eq_integral (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ∀ (metric : Mat d), metric.PosDef →
          ∀ j : ℤ,
            lqSchattenNorm P (bigQ d γ : ℝ)
                (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar metric) j) ^
                bigQ d γ =
              ∫ a, absSchattenNorm (bigQ d γ : ℝ)
                  (normalizedFluctuationSelf P
                    (Geometry.explicitRoundedGrid jStar metric) j a) ^ bigQ d γ ∂P := by
  intro P E Ψ K S hprob hstat _hunit hdag jStar hjStar metric hmetric j
  let : IsProbabilityMeasure P := hprob
  have hN : (1 : ℝ) ≤ (bigQ d γ : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 2) (bigQ_two_le d γ hγ))
  have hmem : SchattenMemLp P (bigQ d γ : ℝ)
      (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar metric) j) := by
    simpa [normalizedFluctuationSelf] using!
      HCPolySupport.HighContrast.Annealed.memLqSchatten_normalizedFluctuation d hd P γ E Ψ K S
        hstat hdag
        jStar hjStar metric hmetric j j 0 (bigQ d γ : ℝ) hN
  unfold lqSchattenNorm
  rw [Real.rpow_inv_natCast_pow]
  · simp only [Real.rpow_natCast]
  · apply integral_nonneg_of_ae
    filter_upwards [hmem.symmetric] with a ha
    exact Real.rpow_nonneg
      (Analysis.absSchattenNorm_nonneg ((Analysis.toFullBlockMat_isHermitian_iff _).2 ha) hN)
      (bigQ d γ : ℝ)
  · exact ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) (bigQ_two_le d γ hγ))

private theorem averaging_term_power_bound (d Q : ℕ) (h : ℤ) (Δ a0 u M : ℝ)
    (hVj0 : 0 ≤ M) (hJeq : u ^ Q = M)
    (ha0def : a0 = (Q : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) *
      (1 + (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹) * (3 : ℝ) ^ (-((d : ℝ) / 2) * (h : ℝ)) *
        Real.exp Δ * u)
    (hbase_le : ((Q : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) *
      (1 + (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹)) ^ Q ≤
        ((3 : ℝ) ^ d * (Q : ℝ)) ^ Q) :
    a0 ^ Q ≤
      ((3 : ℝ) ^ d * (Q : ℝ)) ^ Q *
        ((3 : ℝ) ^ (-((Q : ℝ) * (d : ℝ) / 2) * (h : ℝ)) *
          (Real.exp ((Q : ℝ) * Δ) *
            M)) := by
  have e1 : ((3 : ℝ) ^ (-((d : ℝ) / 2) * (h : ℝ))) ^ Q =
      (3 : ℝ) ^ (-((Q : ℝ) * (d : ℝ) / 2) * (h : ℝ)) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-((d : ℝ) / 2) * (h : ℝ))) (Q),
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    congr 1
    ring
  have e2 : (Real.exp Δ) ^ Q = Real.exp ((Q : ℝ) * Δ) :=
    (Real.exp_nat_mul Δ (Q)).symm
  have hreassoc : a0 =
      ((Q : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) *
          (1 + (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹)) *
        ((3 : ℝ) ^ (-((d : ℝ) / 2) * (h : ℝ)) *
          (Real.exp Δ *
            u)) := by
    rw [ha0def]; ring
  have step1 :
      (((Q : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) *
            (1 + (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹)) *
          ((3 : ℝ) ^ (-((d : ℝ) / 2) * (h : ℝ)) *
            (Real.exp Δ *
              u))) ^
          Q =
        ((Q : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) *
            (1 + (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹)) ^ Q *
          ((3 : ℝ) ^ (-((d : ℝ) / 2) * (h : ℝ)) *
              (Real.exp Δ *
                u)) ^
            Q :=
    mul_pow _ _ _
  have step2 :
      ((3 : ℝ) ^ (-((d : ℝ) / 2) * (h : ℝ)) *
            (Real.exp Δ *
              u)) ^
          Q =
        ((3 : ℝ) ^ (-((d : ℝ) / 2) * (h : ℝ))) ^ Q *
          (Real.exp Δ *
              u) ^
            Q :=
    mul_pow _ _ _
  have step3 :
      (Real.exp Δ *
            u) ^
          Q =
        (Real.exp Δ) ^ Q *
          (u) ^
            Q :=
    mul_pow _ _ _
  have hstep : a0 ^ Q =
      ((Q : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) *
          (1 + (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹)) ^ Q *
        ((3 : ℝ) ^ (-((Q : ℝ) * (d : ℝ) / 2) * (h : ℝ)) *
          (Real.exp ((Q : ℝ) * Δ) *
            M)) := by
    rw [hreassoc, step1, step2, step3, e1, e2, hJeq]
  rw [hstep]
  exact mul_le_mul_of_nonneg_right hbase_le
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (mul_nonneg (Real.exp_pos _).le hVj0))

/-- `e.fixed.geometry.parent.child.powered` (`p.fixed.geometry.one.grid.propagation`): apply the
recurrence with
`N = Q`, raise to the `Q`-th power using `(a+b)^Q ≤ 2^{Q-1}(a^Q + b^Q)` and
`e^{(Q-1)t}(e^t-1) ≤ e^{Qt}-1`. -/
theorem parent_child_powered (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
            ∀ (metric : Mat d), metric.PosDef →
              ∀ j h : ℤ, (jStar : ℤ) ≤ j → 1 ≤ h →
                (∫ a, absSchattenNorm (bigQ d γ : ℝ)
                    (normalizedFluctuationSelf P
                      (Geometry.explicitRoundedGrid jStar metric) (j + h) a) ^ bigQ d γ ∂P) ≤
                  (2 : ℝ) ^ (bigQ d γ - 1) * ((3 : ℝ) ^ d * (bigQ d γ : ℝ)) ^ bigQ d γ *
                        (3 : ℝ) ^ (-((bigQ d γ : ℝ) * (d : ℝ) / 2) * (h : ℝ)) *
                        Real.exp ((bigQ d γ : ℝ) *
                          detIncrement P (Geometry.explicitRoundedGrid jStar metric) j (j + h)) *
                      (∫ a, absSchattenNorm (bigQ d γ : ℝ)
                        (normalizedFluctuationSelf P
                          (Geometry.explicitRoundedGrid jStar metric) j a) ^ bigQ d γ ∂P) +
                    (2 : ℝ) ^ (2 * bigQ d γ - 1) *
                        (1 + (d : ℝ) ^ (1 - ((bigQ d γ : ℝ))⁻¹)) ^ bigQ d γ *
                      (Real.exp ((bigQ d γ : ℝ) *
                        detIncrement P (Geometry.explicitRoundedGrid jStar metric) j (j + h)) -
                          1) := by
  obtain ⟨Csrc, hCsrc, hrec⟩ := parent_child_recurrence_input d hd γ hγ
  refine ⟨Csrc, hCsrc, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag jStar hjStar hsrc metric hmetric j h hj hh
  let := hP
  have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d γ hγ
  have hQ1 : 1 ≤ bigQ d γ := le_trans (by norm_num) hQ2
  have hQne : bigQ d γ ≠ 0 := bigQ_ne_zero d hd γ hγ
  have hrecQ := hrec P E Ψ K S hP hstat hunit hdag (bigQ d γ) hQ2 (bigQ_even d γ)
    jStar hjStar hsrc metric hmetric j h hj hh
  have hΔ : 0 ≤ detIncrement P (Geometry.explicitRoundedGrid jStar metric) j (j + h) :=
    Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
      j (j + h) hj (by omega)
  have hVj0 : 0 ≤ ∫ a, absSchattenNorm (bigQ d γ : ℝ)
      (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar metric) j a) ^ bigQ d γ ∂P :=
    integral_nonneg fun _ => (bigQ_even d γ).pow_nonneg _
  have hnormJ0 : 0 ≤ lqSchattenNorm P (bigQ d γ : ℝ)
      (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar metric) j) := by
    unfold lqSchattenNorm
    apply Real.rpow_nonneg
    apply integral_nonneg
    intro a
    simp only [Pi.zero_apply, Real.rpow_natCast]
    exact (bigQ_even d γ).pow_nonneg _
  have hnormJh0 : 0 ≤ lqSchattenNorm P (bigQ d γ : ℝ)
      (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar metric) (j + h)) := by
    unfold lqSchattenNorm
    apply Real.rpow_nonneg
    apply integral_nonneg
    intro a
    simp only [Pi.zero_apply, Real.rpow_natCast]
    exact (bigQ_even d γ).pow_nonneg _
  set Δ := detIncrement P (Geometry.explicitRoundedGrid jStar metric) j (j + h) with hΔdef
  set a0 : ℝ := (bigQ d γ : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) *
      (1 + (2 * (d : ℝ)) ^ ((bigQ d γ : ℝ))⁻¹) * (3 : ℝ) ^ (-((d : ℝ) / 2) * (h : ℝ)) *
      Real.exp Δ *
      lqSchattenNorm P (bigQ d γ : ℝ)
        (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar metric) j) with ha0def
  set b0 : ℝ := 2 * (1 + (d : ℝ) ^ (1 - ((bigQ d γ : ℝ))⁻¹)) *
      Real.exp ((1 - ((bigQ d γ : ℝ))⁻¹) * Δ) * (Real.exp Δ - 1) ^ ((bigQ d γ : ℝ))⁻¹ with hb0def
  have ha0nn : 0 ≤ a0 := by
    rw [ha0def]
    have h1 : (0:ℝ) ≤ (bigQ d γ : ℝ) := by positivity
    have h2 : (0:ℝ) ≤ (3 : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    have h3 : (0:ℝ) ≤ 1 + (2 * (d : ℝ)) ^ ((bigQ d γ : ℝ))⁻¹ := by
      have := Real.rpow_nonneg (show (0:ℝ) ≤ 2 * (d:ℝ) by positivity) ((bigQ d γ : ℝ))⁻¹
      linarith only [this]
    have h4 : (0:ℝ) ≤ (3 : ℝ) ^ (-((d : ℝ) / 2) * (h : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have h5 : (0:ℝ) ≤ Real.exp Δ := (Real.exp_pos _).le
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4) h5) hnormJ0
  have hb0nn : 0 ≤ b0 := by
    rw [hb0def]
    have h1 : (0:ℝ) ≤ 1 + (d : ℝ) ^ (1 - ((bigQ d γ : ℝ))⁻¹) := by
      have := Real.rpow_nonneg (show (0:ℝ) ≤ (d:ℝ) by positivity) (1 - ((bigQ d γ : ℝ))⁻¹)
      linarith only [this]
    have h2 : (0:ℝ) ≤ Real.exp ((1 - ((bigQ d γ : ℝ))⁻¹) * Δ) := (Real.exp_pos _).le
    have h3 : (0:ℝ) ≤ (Real.exp Δ - 1) ^ ((bigQ d γ : ℝ))⁻¹ :=
      Real.rpow_nonneg (by linarith only [Real.one_le_exp hΔ]) _
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2) h3
  have hpow0 : lqSchattenNorm P (bigQ d γ : ℝ)
      (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar metric) (j + h)) ^ bigQ d γ ≤
      (a0 + b0) ^ bigQ d γ :=
    pow_le_pow_left₀ hnormJh0 hrecQ (bigQ d γ)
  have hab : (a0 + b0) ^ bigQ d γ ≤ 2 ^ (bigQ d γ - 1) * (a0 ^ bigQ d γ + b0 ^ bigQ d γ) :=
    add_pow_le ha0nn hb0nn (bigQ d γ)
  have hAeq :
      lqSchattenNorm P (bigQ d γ : ℝ)
          (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar metric) (j + h)) ^
          bigQ d γ =
        ∫ a, absSchattenNorm (bigQ d γ : ℝ)
            (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar metric) (j + h) a) ^
              bigQ d γ ∂P :=
    lqSchattenNorm_pow_eq_integral d hd γ hγ P E Ψ K S hP hstat hunit hdag jStar hjStar
      metric hmetric (j + h)
  have hJeq :
      lqSchattenNorm P (bigQ d γ : ℝ)
          (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar metric) j) ^ bigQ d γ =
        ∫ a, absSchattenNorm (bigQ d γ : ℝ)
            (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar metric) j a) ^
              bigQ d γ ∂P :=
    lqSchattenNorm_pow_eq_integral d hd γ hγ P E Ψ K S hP hstat hunit hdag jStar hjStar
      metric hmetric j
  have hpow : ∫ a, absSchattenNorm (bigQ d γ : ℝ)
      (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar metric) (j + h) a) ^
        bigQ d γ ∂P ≤ (a0 + b0) ^ bigQ d γ := by
    rw [← hAeq]; exact hpow0
  have e3 : (Real.exp ((1 - ((bigQ d γ : ℝ))⁻¹) * Δ)) ^ bigQ d γ =
      Real.exp (((bigQ d γ : ℝ) - 1) * Δ) := by
    have hQR0 : (bigQ d γ : ℝ) ≠ 0 := by exact_mod_cast hQne
    rw [← Real.exp_nat_mul]
    congr 1
    rw [← mul_assoc, mul_sub, mul_one, mul_inv_cancel₀ hQR0]
  have e4 : ((Real.exp Δ - 1) ^ ((bigQ d γ : ℝ))⁻¹) ^ bigQ d γ = Real.exp Δ - 1 :=
    Real.rpow_inv_natCast_pow (by linarith only [Real.one_le_exp hΔ]) hQne
  -- hA : bound on a0 ^ Q, built via explicit `mul_pow` instantiations (never `rw [mul_pow]`,
  -- which is ambiguous once both sides contain products raised to the power `bigQ d γ`).
  have hbase_nn : (0:ℝ) ≤ (bigQ d γ : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) *
      (1 + (2 * (d : ℝ)) ^ ((bigQ d γ : ℝ))⁻¹) := by
    have h1 : (0:ℝ) ≤ (bigQ d γ : ℝ) := by positivity
    have h2 : (0:ℝ) ≤ (3 : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    have h3 : (0:ℝ) ≤ 1 + (2 * (d : ℝ)) ^ ((bigQ d γ : ℝ))⁻¹ := by
      have := Real.rpow_nonneg (show (0:ℝ) ≤ 2 * (d:ℝ) by positivity) ((bigQ d γ : ℝ))⁻¹
      linarith only [this]
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hbase_le : ((bigQ d γ : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) *
      (1 + (2 * (d : ℝ)) ^ ((bigQ d γ : ℝ))⁻¹)) ^ bigQ d γ ≤
      ((3 : ℝ) ^ d * (bigQ d γ : ℝ)) ^ bigQ d γ :=
    pow_le_pow_left₀ hbase_nn (averaging_coefficient_le d hd γ hγ) (bigQ d γ)
  have hA : a0 ^ bigQ d γ ≤
      ((3 : ℝ) ^ d * (bigQ d γ : ℝ)) ^ bigQ d γ *
        ((3 : ℝ) ^ (-((bigQ d γ : ℝ) * (d : ℝ) / 2) * (h : ℝ)) *
          (Real.exp ((bigQ d γ : ℝ) * Δ) *
            (∫ a, absSchattenNorm (bigQ d γ : ℝ)
                (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar metric) j a) ^
                  bigQ d γ ∂P))) :=
    averaging_term_power_bound d (bigQ d γ) h Δ a0 _ _ hVj0 hJeq ha0def hbase_le
  have hexpQ : Real.exp (((bigQ d γ : ℝ) - 1) * Δ) * (Real.exp Δ - 1) ≤
      Real.exp ((bigQ d γ : ℝ) * Δ) - 1 :=
    exp_pred_mul_sub_one_le (bigQ d γ) hQ1 Δ hΔ
  have hcoef_nn : (0:ℝ) ≤ (2:ℝ) ^ bigQ d γ *
      (1 + (d : ℝ) ^ (1 - ((bigQ d γ : ℝ))⁻¹)) ^ bigQ d γ := by
    apply mul_nonneg (by positivity)
    apply pow_nonneg
    have := Real.rpow_nonneg (show (0:ℝ) ≤ (d:ℝ) by positivity) (1 - ((bigQ d γ : ℝ))⁻¹)
    linarith only [this]
  have hB : b0 ^ bigQ d γ ≤
      (2:ℝ) ^ bigQ d γ * (1 + (d : ℝ) ^ (1 - ((bigQ d γ : ℝ))⁻¹)) ^ bigQ d γ *
        (Real.exp ((bigQ d γ : ℝ) * Δ) - 1) := by
    have hreassoc : b0 =
        (2 * (1 + (d : ℝ) ^ (1 - ((bigQ d γ : ℝ))⁻¹))) *
          (Real.exp ((1 - ((bigQ d γ : ℝ))⁻¹) * Δ) * (Real.exp Δ - 1) ^ ((bigQ d γ : ℝ))⁻¹) := by
      rw [hb0def]; ring
    have step1 :
        ((2 * (1 + (d : ℝ) ^ (1 - ((bigQ d γ : ℝ))⁻¹))) *
            (Real.exp ((1 - ((bigQ d γ : ℝ))⁻¹) * Δ) *
              (Real.exp Δ - 1) ^ ((bigQ d γ : ℝ))⁻¹)) ^ bigQ d γ =
          (2 * (1 + (d : ℝ) ^ (1 - ((bigQ d γ : ℝ))⁻¹))) ^ bigQ d γ *
            (Real.exp ((1 - ((bigQ d γ : ℝ))⁻¹) * Δ) *
                (Real.exp Δ - 1) ^ ((bigQ d γ : ℝ))⁻¹) ^ bigQ d γ :=
      mul_pow _ _ _
    have step2 :
        (2 * (1 + (d : ℝ) ^ (1 - ((bigQ d γ : ℝ))⁻¹))) ^ bigQ d γ =
          (2:ℝ) ^ bigQ d γ * (1 + (d : ℝ) ^ (1 - ((bigQ d γ : ℝ))⁻¹)) ^ bigQ d γ :=
      mul_pow _ _ _
    have step3 :
        (Real.exp ((1 - ((bigQ d γ : ℝ))⁻¹) * Δ) * (Real.exp Δ - 1) ^ ((bigQ d γ : ℝ))⁻¹) ^
            bigQ d γ =
          (Real.exp ((1 - ((bigQ d γ : ℝ))⁻¹) * Δ)) ^ bigQ d γ *
            ((Real.exp Δ - 1) ^ ((bigQ d γ : ℝ))⁻¹) ^ bigQ d γ :=
      mul_pow _ _ _
    have hstep : b0 ^ bigQ d γ =
        (2:ℝ) ^ bigQ d γ * (1 + (d : ℝ) ^ (1 - ((bigQ d γ : ℝ))⁻¹)) ^ bigQ d γ *
          (Real.exp (((bigQ d γ : ℝ) - 1) * Δ) * (Real.exp Δ - 1)) := by
      rw [hreassoc, step1, step2, step3, e3, e4]
    rw [hstep]
    exact mul_le_mul_of_nonneg_left hexpQ hcoef_nn
  have hsum := add_le_add hA hB
  have hfinal := mul_le_mul_of_nonneg_left hsum
    (show (0:ℝ) ≤ (2:ℝ) ^ (bigQ d γ - 1) by positivity)
  have h2pow : (2:ℝ) ^ (bigQ d γ - 1) * (2:ℝ) ^ bigQ d γ = (2:ℝ) ^ (2 * bigQ d γ - 1) := by
    rw [← pow_add]
    congr 1
    omega
  refine hpow.trans (hab.trans (hfinal.trans (le_of_eq ?_)))
  rw [← h2pow]
  ring

end

end HCPolySupport.HighContrast.Multiscale
