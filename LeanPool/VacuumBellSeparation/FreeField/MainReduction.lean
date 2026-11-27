/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.Theorem31
public import LeanPool.VacuumBellSeparation.Constants.Parameters
public import LeanPool.VacuumBellSeparation.FreeField.Existence
public import LeanPool.VacuumBellSeparation.FreeField.Statements
public import LeanPool.VacuumBellSeparation.FreeField.Dilation

/-!
# The proof of the main theorem as a conditional reduction (Section 8.4)

The "Proof of the main theorem" of the manuscript (Section 8.4), formalized as a
CONDITIONAL theorem: Theorem 1.1 follows from

* `Section8Estimates`: the regional estimates (8.11) and (8.13) for the double-cone algebras,
  uniformly in the mass (`ε₊(s) = A₊ s⁻²`, `ε₋(s) = A₋ s^{-γ}` as in (8.3));
* `Locality`: the local algebras of two unit double cones at centre distance `s > 2` commute
  (microcausality; a theorem about the model, proved in `FreeField/Microcausality/`, not an
  assumption);
* `Lemma_2_1` (dilation).

This is a reduction, NOT a proof of Theorem 1.1: `Section8Estimates` carries all analytic and
operator-algebraic content of Sections 2.2-8.2 other than Theorem 3.1 (Lemma 2.3 included), the
time-slice identity (2.3) of Section 2.1, Appendix A and the cited literature results; Theorem 3.1
is applied in `freeFieldBell_unit_eq_one`, and `Locality` and `Lemma_2_1` are separate hypotheses.

* `probExponent`, `cStar`: the numerator `X = 2 log 2/(ab) + ν₊ + ν₋` of the exponent `X/η` of
  `C_prob` in (8.16), and the separation ratio (8.17) (with `3` added to the maximum so that
  `C_* > 2`);
* `freeFieldBell_unit_eq_one`: for `s ≥ C_*` the hypotheses of Theorem 3.1 hold for the unit
  double cones and `β_μ(1, s) = 1`, for every mass `μ > 0`;
* `theorem_1_1_of_estimates : Section8Estimates → Locality → Lemma_2_1 → Theorem_1_1`.
* `theorem_1_1_of_section8 : Section8Estimates → Locality → Theorem_1_1`, using the proof
  `lemma_2_1` of Lemma 2.1 (`FreeField/Dilation.lean`).
-/

@[expose] public section

open scoped ENNReal

namespace VacuumBellSeparation

/-- Locality: the local algebras of two unit double cones at centre distance `s > 2` commute,
in every vacuum system of every mass. -/
def Locality : Prop :=
  ∀ μ s : ℝ, 0 < μ → 2 < s →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (V : FreeFieldVacuum μ H),
      Commuting (localAlgebra V (doubleCone 0 1)) (localAlgebra V (doubleCone (0, s • e₁) 1))

/-- The finite-separation estimates of Section 8 for unit double cones, uniform in the mass:
(8.11) `log K_{r₊,+} ≤ 8 r₊ ε₊(s)`, `log K_{r₋,-} ≤ (2 r₋ / a) ε₋(s)` and (8.13)
`|ω(AB) - ω(A)ω(B)| ≤ Q₀ / s`, with `ε₊(s) = A₊ s⁻²`, `ε₋(s) = A₋ s^{-γ}` (8.3), valid for
`s ≥ S_geo` whenever `ε₊(s) ≤ 1/(8 r₊)` and `ε₋(s) ≤ a/4` (the conditions used in the
manuscript's proof). -/
def Section8Estimates : Prop :=
  ∃ Ap Am Q0 Sgeo : ℝ, 0 < Ap ∧ 0 < Am ∧ 0 < Q0 ∧
    ∀ μ s : ℝ, 0 < μ → Sgeo ≤ s → 0 < s →
      Ap / s ^ 2 ≤ 1 / (8 * rPlus) → Am * s ^ (-gammaRev) ≤ aRev / 4 →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (V : FreeFieldVacuum μ H),
        eventConstPlus (vectorState V.vacuum V.vacuum_norm) (localAlgebra V (doubleCone 0 1))
            (localAlgebra V (doubleCone (0, s • e₁) 1)) rPlus
          ≤ ENNReal.ofReal (Real.exp (8 * rPlus * (Ap / s ^ 2))) ∧
        eventConstMinus (vectorState V.vacuum V.vacuum_norm) (localAlgebra V (doubleCone 0 1))
            (localAlgebra V (doubleCone (0, s • e₁) 1)) rMinus
          ≤ ENNReal.ofReal (Real.exp (2 * rMinus / aRev * (Am * s ^ (-gammaRev)))) ∧
        ∀ A ∈ saContractions (localAlgebra V (doubleCone 0 1)),
          ∀ B ∈ saContractions (localAlgebra V (doubleCone (0, s • e₁) 1)),
            ‖vectorState V.vacuum V.vacuum_norm (A * B)
              - vectorState V.vacuum V.vacuum_norm A * vectorState V.vacuum V.vacuum_norm B‖
              ≤ Q0 / s

/-- `X = 2 log 2/(ab) + ν₊ + ν₋`, the numerator of the exponent `X/η` of `C_prob` in (8.16). -/
noncomputable def probExponent : ℝ :=
  2 * Real.log 2 / (expA rMinus * expB rPlus) + nuPlus rPlus rMinus + nuMinus rMinus

/-- The sufficient separation ratio of (8.17) (with `3` added to the maximum so that `C_* > 2`). -/
noncomputable def cStar (Ap Am Q0 Sgeo : ℝ) : ℝ :=
  max 3 (max Sgeo (max (Real.sqrt (8 * rPlus * Ap))
    (max ((4 * Am / aRev) ^ (1 / gammaRev)) (Q0 * Real.exp (probExponent / expEta rPlus rMinus)))))

theorem nuPlus_pos : 0 < nuPlus rPlus rMinus := by
  rw [nuPlus_eq, expB_rPlus]; norm_num

theorem nuMinus_pos : 0 < nuMinus rMinus := by
  rw [nuMinus_eq]; norm_num

/-- Unit-ball step: for `s ≥ C_*`, the hypotheses of Theorem 3.1 hold and `β_μ(1, s) = 1`. -/
theorem freeFieldBell_unit_eq_one (h8 : Section8Estimates) (hloc : Locality) :
    ∃ C : ℝ, 2 < C ∧ ∀ μ s : ℝ, 0 < μ → C ≤ s →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (V : FreeFieldVacuum μ H), freeFieldBell V 1 s = 1 := by
  obtain ⟨Ap, Am, Q0, Sgeo, hAp, hAm, hQ0, hest⟩ := h8
  refine ⟨cStar Ap Am Q0 Sgeo, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro μ s hμ hs H _ _ _ V
  -- the five lower bounds packed in `cStar`
  -- (cStar = max 3 (max Sgeo (max √(8r₊A₊) (max (4A₋/a)^(1/γ) (Q₀ e^{X/η})))))
  have h3 : 3 ≤ s := le_trans (le_max_left _ _) hs
  have hspos : 0 < s := by linarith
  have hS : Sgeo ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hsq : Real.sqrt (8 * rPlus * Ap) ≤ s :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hs
  have hpow : (4 * Am / aRev) ^ (1 / gammaRev) ≤ s :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hs
  have hprob : Q0 * Real.exp (probExponent / expEta rPlus rMinus) ≤ s :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hs
  have hrp : 2 < rPlus := rPlus_ge.2
  have hrp0 : 0 < rPlus := by linarith
  have hrp_ne : rPlus ≠ 0 := hrp0.ne'
  have ha : 0 < aRev := aRev_pos_le.1
  have ha_ne : aRev ≠ 0 := ha.ne'
  have hγ : 0 < gammaRev := gammaRev_pos
  -- ε₊(s) ≤ 1/(8 r₊):  √(8 r₊ A₊) ≤ s  ⟹  8 r₊ A₊ ≤ s²
  have heps_p : Ap / s ^ 2 ≤ 1 / (8 * rPlus) := by
    have h0 : 0 ≤ 8 * rPlus * Ap :=
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 8) hrp0) hAp).le
    have h1 : 8 * rPlus * Ap ≤ s ^ 2 :=
      calc 8 * rPlus * Ap = Real.sqrt (8 * rPlus * Ap) ^ 2 := (Real.sq_sqrt h0).symm
        _ ≤ s ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
    rw [div_le_div_iff₀ (pow_pos hspos 2) (by linarith)]
    -- goal: `Ap * (8 * rPlus) ≤ 1 * s ^ 2`
    linarith
  -- ε₋(s) ≤ a/4:  (4A₋/a)^(1/γ) ≤ s  ⟹  4A₋/a ≤ s^γ
  have heps_m : Am * s ^ (-gammaRev) ≤ aRev / 4 := by
    have h1 : 4 * Am / aRev ≤ s ^ gammaRev := by
      have hb : 0 ≤ 4 * Am / aRev := div_nonneg (by linarith) ha.le
      calc 4 * Am / aRev = ((4 * Am / aRev) ^ (1 / gammaRev)) ^ gammaRev := by
            rw [← Real.rpow_mul hb, one_div, inv_mul_cancel₀ hγ.ne', Real.rpow_one]
        _ ≤ s ^ gammaRev := Real.rpow_le_rpow (Real.rpow_nonneg hb _) hpow hγ.le
    have hsγ : 0 < s ^ gammaRev := Real.rpow_pos_of_pos hspos _
    rw [Real.rpow_neg hspos.le, ← div_eq_mul_inv,
      div_le_div_iff₀ hsγ (by norm_num : (0 : ℝ) < 4)]
    -- goal: `Am * 4 ≤ aRev * s ^ gammaRev`
    rw [div_le_iff₀ ha] at h1
    -- h1: `4 * Am ≤ s ^ gammaRev * aRev`
    linarith
  obtain ⟨hKp, hKm, hcl⟩ := hest μ s hμ hS hspos heps_p heps_m H V
  -- the constants are at most `e`
  have hKp_le : (eventConstPlus (vectorState V.vacuum V.vacuum_norm)
      (localAlgebra V (doubleCone 0 1)) (localAlgebra V (doubleCone (0, s • e₁) 1)) rPlus).toReal
      ≤ Real.exp 1 := by
    refine ENNReal.toReal_le_of_le_ofReal (Real.exp_pos 1).le (hKp.trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)))
    calc 8 * rPlus * (Ap / s ^ 2) ≤ 8 * rPlus * (1 / (8 * rPlus)) :=
          mul_le_mul_of_nonneg_left heps_p (by linarith)
      _ = 1 := mul_one_div_cancel (mul_ne_zero (by norm_num) hrp_ne)
  have hKm_le : (eventConstMinus (vectorState V.vacuum V.vacuum_norm)
      (localAlgebra V (doubleCone 0 1)) (localAlgebra V (doubleCone (0, s • e₁) 1)) rMinus).toReal
      ≤ Real.exp 1 := by
    refine ENNReal.toReal_le_of_le_ofReal (Real.exp_pos 1).le (hKm.trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)))
    have hr := one_lt_rMinus_lt_two
    calc 2 * rMinus / aRev * (Am * s ^ (-gammaRev))
        ≤ 2 * rMinus / aRev * (aRev / 4) :=
          mul_le_mul_of_nonneg_left heps_m (div_nonneg (by linarith [hr.1]) ha.le)
      _ = rMinus / 2 * (aRev / aRev) := by ring
      _ = rMinus / 2 := by rw [div_self ha_ne, mul_one]
      _ ≤ 1 := by linarith [hr.2]
  -- finiteness
  have hKp_ne : eventConstPlus (vectorState V.vacuum V.vacuum_norm)
      (localAlgebra V (doubleCone 0 1)) (localAlgebra V (doubleCone (0, s • e₁) 1)) rPlus ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKp
  have hKm_ne : eventConstMinus (vectorState V.vacuum V.vacuum_norm)
      (localAlgebra V (doubleCone 0 1)) (localAlgebra V (doubleCone (0, s • e₁) 1)) rMinus ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKm
  -- the cutoff (3.5) with q = Q₀/s
  have hη := expEta_pos
  have hη_ne : expEta rPlus rMinus ≠ 0 := hη.ne'
  have hcut : (Q0 / s) ^ expEta rPlus rMinus *
      (eventConstPlus (vectorState V.vacuum V.vacuum_norm) (localAlgebra V (doubleCone 0 1))
        (localAlgebra V (doubleCone (0, s • e₁) 1)) rPlus).toReal ^ nuPlus rPlus rMinus *
      (eventConstMinus (vectorState V.vacuum V.vacuum_norm) (localAlgebra V (doubleCone 0 1))
        (localAlgebra V (doubleCone (0, s • e₁) 1)) rMinus).toReal ^ nuMinus rMinus
      ≤ (2 : ℝ) ^ (-(2 / (expA rMinus * expB rPlus))) := by
    have hq0 : 0 ≤ Q0 / s := div_nonneg hQ0.le hspos.le
    -- Q₀/s ≤ exp(-X/η), from Q₀ e^{X/η} ≤ s
    have hle : Q0 / s ≤ Real.exp (-(probExponent / expEta rPlus rMinus)) := by
      have hE : Real.exp (-(probExponent / expEta rPlus rMinus)) *
          Real.exp (probExponent / expEta rPlus rMinus) = 1 := by
        rw [← Real.exp_add]; simp
      rw [div_le_iff₀ hspos]
      calc Q0 = Real.exp (-(probExponent / expEta rPlus rMinus)) *
            (Q0 * Real.exp (probExponent / expEta rPlus rMinus)) := by
            rw [mul_left_comm, hE, mul_one]
        _ ≤ Real.exp (-(probExponent / expEta rPlus rMinus)) * s :=
            mul_le_mul_of_nonneg_left hprob (Real.exp_pos _).le
    -- (Q₀/s)^η ≤ exp(-X)
    have hq : (Q0 / s) ^ expEta rPlus rMinus ≤ Real.exp (-probExponent) := by
      calc (Q0 / s) ^ expEta rPlus rMinus
          ≤ (Real.exp (-(probExponent / expEta rPlus rMinus))) ^ expEta rPlus rMinus :=
            Real.rpow_le_rpow hq0 hle hη.le
        _ = Real.exp (-probExponent) := by
            rw [← Real.exp_mul, neg_mul, div_mul_cancel₀ _ hη_ne]
    -- K₊^{ν₊} ≤ e^{ν₊}, K₋^{ν₋} ≤ e^{ν₋}
    have hKp' := Real.rpow_le_rpow ENNReal.toReal_nonneg hKp_le nuPlus_pos.le
    have hKm' := Real.rpow_le_rpow ENNReal.toReal_nonneg hKm_le nuMinus_pos.le
    rw [← Real.exp_mul, one_mul] at hKp' hKm'
    have hB0 := Real.rpow_nonneg (ENNReal.toReal_nonneg (a := eventConstPlus
      (vectorState V.vacuum V.vacuum_norm) (localAlgebra V (doubleCone 0 1))
      (localAlgebra V (doubleCone (0, s • e₁) 1)) rPlus)) (nuPlus rPlus rMinus)
    have hC0 := Real.rpow_nonneg (ENNReal.toReal_nonneg (a := eventConstMinus
      (vectorState V.vacuum V.vacuum_norm) (localAlgebra V (doubleCone 0 1))
      (localAlgebra V (doubleCone (0, s • e₁) 1)) rMinus)) (nuMinus rMinus)
    -- 2^{-2/(ab)} = exp(-2 log 2/(ab))
    have hbase : (2 : ℝ) ^ (-(2 / (expA rMinus * expB rPlus)))
        = Real.exp (-(2 * Real.log 2 / (expA rMinus * expB rPlus))) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
    rw [hbase]
    -- e^{-X} e^{ν₊} e^{ν₋} = e^{-2 log 2/(ab)} since X = 2 log 2/(ab) + ν₊ + ν₋
    calc _ ≤ Real.exp (-probExponent) * Real.exp (nuPlus rPlus rMinus) *
          Real.exp (nuMinus rMinus) :=
          mul_le_mul (mul_le_mul hq hKp' hB0 (Real.exp_pos _).le) hKm' hC0 (by positivity)
      _ = Real.exp (-(2 * Real.log 2 / (expA rMinus * expB rPlus))) := by
          rw [← Real.exp_add, ← Real.exp_add]; unfold probExponent; congr 1; ring
  -- apply Theorem 3.1
  have hrm := one_lt_rMinus_lt_two
  exact probability_criterion (vectorState V.vacuum V.vacuum_norm) (hloc μ s hμ (by linarith) H V)
    hrp hrm.1 hrm.2 hη hKp_ne hKm_ne hcl hcut

/-- **Theorem 1.1, conditional form**: the finite-separation estimates of Section 8, locality and
Lemma 2.1 imply Theorem 1.1 (manuscript, Section 8.4). -/
theorem theorem_1_1_of_estimates (h8 : Section8Estimates) (hloc : Locality) (h21 : Lemma_2_1) :
    Theorem_1_1 := by
  obtain ⟨C, hC2, hC⟩ := freeFieldBell_unit_eq_one h8 hloc
  refine ⟨C, hC2, ?_⟩
  intro m R L hm hR hL H _ _ _ V
  -- L ≥ C R > 0
  have hL0 : 0 < L := lt_of_lt_of_le (mul_pos (by linarith) hR) hL
  obtain ⟨H', i1, i2, i3, ⟨V'⟩⟩ := freeFieldVacuum_exists (m * R) (mul_pos hm hR)
  -- β_m(R, L) = β_{mR}(1, L/R) (Lemma 2.1), and L/R ≥ C
  rw [h21 m R L hm hR hL0 H V H' V']
  exact hC (m * R) (L / R) (mul_pos hm hR) (by rw [le_div_iff₀ hR]; linarith) H' V'

/-- **Theorem 1.1, conditional form with Lemma 2.1 discharged**: the finite-separation estimates of
Section 8 and locality imply Theorem 1.1. -/
theorem theorem_1_1_of_section8 (h8 : Section8Estimates) (hloc : Locality) : Theorem_1_1 :=
  theorem_1_1_of_estimates h8 hloc lemma_2_1

end VacuumBellSeparation
