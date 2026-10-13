/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration.Bootstrap
public import Mathlib.Analysis.Real.Sqrt

/-!
# RecurrenceIntegration

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Integration of the approximate recurrence

The reported constant is one fixed numeral, independent of the sequence, of
`ν, c⋆, γ, E, F` and of the endpoint `m₀`: this is the manuscript's "there
exists a universal `C < ∞`" made explicit (see
`integrate_approx_recurrence_universal` for the literal existential form).

## No `c⋆ ≤ 1`

Neither the printed statement nor this formalization assumes any upper bound on
`c⋆`: the descent instead caps its step at `c = min{c⋆,1}`
(`Internal.adaptStep_le_cap`), and the resulting slack is absorbed into the
single universal constant `C`.

## References

* ABK26.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration

open scoped BigOperators
open Internal

noncomputable section

open scoped BigOperators

/-- `P_m = ν² + cstar γ⁻¹ 3^{2γm}`, the target the conclusion compares `s_m`
against (the `√·` argument in `e.concl.root.gamma.inv`). -/
noncomputable def targetProfileSq (ν cstar γ : ℝ) (m : ℤ) : ℝ :=
  ν ^ 2 + cstar * γ⁻¹ * geometricTerm γ m

section ComparatorVsTarget

variable {ν cstar γ : ℝ}

private lemma recurrenceComparator_pos
    (hν : 0 < ν) (hcstar : 0 < cstar) (hγ : 0 < γ) (m : ℤ) :
    0 < recurrenceComparator ν cstar γ m := by
  have hg := geometricTerm_pos γ m
  have hK : γ⁻¹ ≤ Stream.Kgamma γ := Stream.le_Kgamma hγ
  have hKpos : 0 < Stream.Kgamma γ := lt_of_lt_of_le (by positivity) hK
  rw [recurrenceComparator]; positivity

/-- `|T_m − (ν² + cstar γ⁻¹ 3^{2γm})| ≤ 4 γ T_m`. This is exactly the
`e.K.cgamma.ineq` estimate `0 ≤ K_γ − γ⁻¹ ≤ 4` transported through the
comparator, using `γ K_γ ≥ 1`. -/
private lemma recurrenceComparator_sub_targetProfileSq_le
    (_hν : 0 < ν) (hcstar : 0 < cstar) (hγ : 0 < γ) (m : ℤ) :
    |recurrenceComparator ν cstar γ m - targetProfileSq ν cstar γ m| ≤
      4 * γ * recurrenceComparator ν cstar γ m := by
  have hg := geometricTerm_pos γ m
  have hk0 : γ⁻¹ ≤ Stream.Kgamma γ := Stream.le_Kgamma hγ
  have hk4 : Stream.Kgamma γ ≤ γ⁻¹ + 4 := Stream.Kgamma_le hγ
  have hdiff : recurrenceComparator ν cstar γ m - targetProfileSq ν cstar γ m
      = cstar * (Stream.Kgamma γ - γ⁻¹) * geometricTerm γ m := by
    rw [recurrenceComparator, targetProfileSq]
    ring
  have hnn : 0 ≤ cstar * (Stream.Kgamma γ - γ⁻¹) * geometricTerm γ m :=
    mul_nonneg (mul_nonneg hcstar.le (by linarith only [hk0])) hg.le
  rw [hdiff, abs_of_nonneg hnn]
  -- γ K_γ ≥ 1
  have hγK : 1 ≤ γ * Stream.Kgamma γ := by
    have h1 : γ * γ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hγ)
    linarith only [mul_le_mul_of_nonneg_left hk0 hγ.le, h1]
  -- cstar * g ≤ γ * T
  have hcg : cstar * geometricTerm γ m ≤ γ * recurrenceComparator ν cstar γ m := by
    rw [recurrenceComparator]
    linarith only [mul_nonneg (mul_nonneg hcstar.le hg.le)
        (by linarith only [hγK] : (0:ℝ) ≤ γ * Stream.Kgamma γ - 1),
      mul_nonneg (sq_nonneg ν) hγ.le]
  linarith only [mul_nonneg (mul_nonneg
      (by linarith only [hk4] : (0:ℝ) ≤ 4 - (Stream.Kgamma γ - γ⁻¹)) hcstar.le) hg.le,
    hcg]

end ComparatorVsTarget

/-- The universal constant reported by `l.integrate.approx.recurrence`.

Any numeral at least `2·(2·(4·recurrenceDescentConstant²)+8) = 230400000016`
works: `4·recurrenceDescentConstant²` is the squared-deviation constant of
`Internal.sq_deviation_core_explicit`, the square-root reduction doubles it and
adds `8` for the `K_γ`-versus-`γ⁻¹` comparator gap, and the final factor `2`
pays for rewriting the internal capped bracket in terms of the printed one.
The fixed choice below is `2·(4·200000²)+8`.  It is independent of the
sequence, of `ν, c⋆, γ, E, F`, and of the endpoint `m₀`. -/
def recurrenceIntegrationConstant : ℝ := 320000000008

/-- The explicit numerical value of `recurrenceIntegrationConstant`. -/
theorem recurrenceIntegrationConstant_eq : recurrenceIntegrationConstant = 320000000008 := by
  norm_num [recurrenceIntegrationConstant]

/-- The square-root form of the squared bootstrap, reported against an
arbitrary bracket `B` dominating (a quarter of) the internal capped bracket
`1 + c⋆⁻²F + (c⋆·min{c⋆,1})⁻¹c⁺`.

This is a *proof-internal* interface only: both public forms below discharge
`hB1` and `hBle` at their application sites.  It exists so that the printed
bracket `1 + c⋆⁻²F` and the two-constant bracket
`1 + c⋆⁻²F + c⋆⁻²c⁺` are obtained from one and the same descent. -/
private theorem integrate_of_bracket
    {ν cstar cplus γ E F B : ℝ} {m₀ : ℤ} {s : ℤ → ℝ}
    (hν : 0 < ν) (hcstar : 0 < cstar) (hcc : cstar ≤ cplus) (hγ : 0 < γ)
    (hE : 1 ≤ E) (hF : 1 ≤ F)
    (hsmall : ∀ m : ℤ, ν ≤ s m ∧
      s m ≤ (1 + (ν ^ 2)⁻¹ * cplus * γ⁻¹ * (3 : ℝ) ^ (2 * γ * (m : ℝ))) * ν)
    (hupper : ∀ n m : ℤ, m ≤ m₀ → n ≤ m → (m : ℝ) ≤ (n : ℝ) + cstar * γ⁻¹ →
      s m ≤ (1 + E * γ) * s n + recurrenceIncrement cstar γ n m * (s n)⁻¹)
    (hlower : ∀ n m : ℤ, m ≤ m₀ → n ≤ m → (m : ℝ) ≤ (n : ℝ) + cstar * γ⁻¹ →
      (1 - E * γ) * s n + recurrenceIncrement cstar γ n m * ((s n)⁻¹) ^ 2 * s m
          - F * ((m : ℝ) - (n : ℝ)) ^ 2 * ((s n)⁻¹) ^ 4 * s m *
            (3 : ℝ) ^ (4 * γ * (m : ℝ))
        ≤ s m)
    (hB1 : 1 ≤ B)
    (hBle : 1 + (cstar ^ 2)⁻¹ * F + (cstar * min cstar 1)⁻¹ * cplus ≤ 4 * B) :
    γ ≤ (recurrenceIntegrationConstant * (E * B))⁻¹ →
      ∀ m : ℤ, m ≤ m₀ →
        |s m - Real.sqrt
            (ν ^ 2 + cstar * γ⁻¹ * (3 : ℝ) ^ (2 * γ * (m : ℝ)))|
          ≤ recurrenceIntegrationConstant * Real.sqrt (E * B * γ) * s m := by
  classical
  set C₀ : ℝ := 4 * recurrenceDescentConstant ^ 2 with hC₀
  have hC₀pos : 0 < C₀ := by rw [hC₀]; norm_num [recurrenceDescentConstant]
  have hpos : ∀ m, 0 < s m := fun m => lt_of_lt_of_le hν (hsmall m).1
  have hsmallInternal : ∀ m : ℤ, ν ≤ s m ∧
      s m ≤ (1 + (ν ^ 2)⁻¹ * cplus * γ⁻¹ * geometricTerm γ m) * ν := by
    intro m
    simpa only [geometricTerm] using hsmall m
  have hlowerInternal : ∀ n m : ℤ, m ≤ m₀ → n ≤ m →
      (m : ℝ) ≤ (n : ℝ) + cstar * γ⁻¹ →
      (1 - E * γ) * s n + recurrenceIncrement cstar γ n m * ((s n)⁻¹) ^ 2 * s m
          - F * ((m : ℝ) - (n : ℝ)) ^ 2 * ((s n)⁻¹) ^ 4 * s m *
            geometricTerm (2 * γ) m ≤ s m := by
    intro n m hm hnm hrange
    have h := hlower n m hm hnm hrange
    have hpow : (3 : ℝ) ^ (4 * γ * (m : ℝ)) = geometricTerm (2 * γ) m := by
      rw [geometricTerm]
      congr 1
      ring
    rw [hpow] at h
    exact h
  have hcore := sq_deviation_core_explicit hν hcstar hcc hγ hE hF hpos
    hsmallInternal hupper hlowerInternal
  -- internal capped bracket Θ = E (1 + c⋆⁻²F + (c⋆·min{c⋆,1})⁻¹c⁺)
  set Θ : ℝ := E * (1 + (cstar ^ 2)⁻¹ * F + (cstar * min cstar 1)⁻¹ * cplus) with hΘ
  have hcplus_pos : 0 < cplus := lt_of_lt_of_le hcstar hcc
  have hcbarpos : (0:ℝ) < cstar * min cstar 1 := mul_pos hcstar (lt_min hcstar one_pos)
  have hfac1 : 1 ≤ 1 + (cstar ^ 2)⁻¹ * F + (cstar * min cstar 1)⁻¹ * cplus := by
    have h1 : 0 ≤ (cstar ^ 2)⁻¹ * F := by positivity
    have h2 : 0 ≤ (cstar * min cstar 1)⁻¹ * cplus :=
      mul_nonneg (inv_nonneg.mpr hcbarpos.le) hcplus_pos.le
    linarith only [h1, h2]
  have hΘ1 : 1 ≤ Θ := by
    rw [hΘ]
    exact le_trans hfac1 (le_mul_of_one_le_left (by linarith only [hfac1]) hE)
  have hΘpos : 0 < Θ := lt_of_lt_of_le one_pos hΘ1
  -- Θ ≤ 4
  have hEBnn : (0:ℝ) ≤ E * B := mul_nonneg (by linarith only [hE]) (by linarith only [hB1])
  have hEB1 : (1:ℝ) ≤ E * B := le_trans hB1 (le_mul_of_one_le_left (by linarith only [hB1]) hE)
  have hΘle4 : Θ ≤ 4 * (E * B) := by
    rw [hΘ]
    have h := mul_le_mul_of_nonneg_left hBle (by linarith only [hE] : (0:ℝ) ≤ E)
    linarith only [h]
  -- make Θ opaque so downstream numeric tactics never zeta-unfold it into `⁻¹`
  clear_value Θ
  intro hsmallγ m hm
  -- convert the inverse-threshold to a product inequality
  have hCpos : (0:ℝ) < recurrenceIntegrationConstant := by
    rw [recurrenceIntegrationConstant_eq]; norm_num
  have hDpos : 0 < recurrenceIntegrationConstant * (E * B) := by
    apply mul_pos hCpos; linarith only [hEB1]
  have hprodle : γ * (recurrenceIntegrationConstant * (E * B)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hsmallγ hDpos.le
    rwa [inv_mul_cancel₀ (ne_of_gt hDpos)] at h
  -- core threshold  γ (C₀ Θ) ≤ 1
  have h4C₀ : 4 * C₀ ≤ recurrenceIntegrationConstant := by
    rw [hC₀, recurrenceIntegrationConstant_eq]; norm_num [recurrenceDescentConstant]
  have hthr_core : γ * (C₀ * Θ) ≤ 1 := by
    have hstep : C₀ * Θ ≤ recurrenceIntegrationConstant * (E * B) := by
      calc C₀ * Θ ≤ C₀ * (4 * (E * B)) := mul_le_mul_of_nonneg_left hΘle4 hC₀pos.le
        _ = (4 * C₀) * (E * B) := by ring
        _ ≤ recurrenceIntegrationConstant * (E * B) :=
            mul_le_mul_of_nonneg_right h4C₀ hEBnn
    have := mul_le_mul_of_nonneg_left hstep hγ.le
    linarith only [this, hprodle]
  -- Θ γ ≤ 1
  have hΘγ_le : Θ * γ ≤ 1 := by
    have h1 : Θ * γ ≤ 4 * (E * B) * γ := mul_le_mul_of_nonneg_right hΘle4 hγ.le
    have h2 : 4 * (E * B) * γ ≤ γ * (recurrenceIntegrationConstant * (E * B)) := by
      have hCge : (4:ℝ) ≤ recurrenceIntegrationConstant := by
        rw [recurrenceIntegrationConstant_eq]; norm_num
      linarith only [mul_le_mul_of_nonneg_right hCge (mul_nonneg hEBnn hγ.le)]
    linarith only [h1, h2, hprodle]
  -- unpack the core estimates
  obtain ⟨hsand, hdev⟩ := hcore hthr_core m hm
  -- pull back the comparator/target comparison, unfolding targetProfileSq
  have hTP0 := recurrenceComparator_sub_targetProfileSq_le hν hcstar hγ m
  rw [targetProfileSq] at hTP0
  change |recurrenceComparator ν cstar γ m -
      (ν ^ 2 + cstar * γ⁻¹ * (3 : ℝ) ^ (2 * γ * (m : ℝ)))| ≤
    4 * γ * recurrenceComparator ν cstar γ m at hTP0
  have hxpos0 : 0 < s m := hpos m
  have hTpos0 : 0 < recurrenceComparator ν cstar γ m := recurrenceComparator_pos hν hcstar hγ m
  -- discard the rpow-heavy hypotheses so `set` below does not attempt
  -- `isDefEq` matching against them (which would whnf into `rpow`), and the
  -- bracket bookkeeping so that the numeric tactics below stay small
  clear hcore hsmall hupper hlower hpos hsmallInternal hlowerInternal
  clear hthr_core hprodle hDpos h4C₀ hEB1 hB1 hBle hsmallγ hfac1 hcbarpos hcplus_pos hcc
    hE hF
  set x : ℝ := s m with hx_def
  set T : ℝ := recurrenceComparator ν cstar γ m with hT_def
  set P : ℝ := ν ^ 2 + cstar * γ⁻¹ *
    (3 : ℝ) ^ (2 * γ * (m : ℝ)) with hP_def
  set R : ℝ := Real.sqrt (Θ * γ) with hR_def
  set S : ℝ := Real.sqrt (E * B * γ) with hS_def
  -- positivity / basic facts, established while the `set` values are still available
  have hxpos : 0 < x := hxpos0
  have hTpos : 0 < T := hTpos0
  have hPpos : 0 < P := by
    rw [hP_def]
    have h1 : (0:ℝ) < ν ^ 2 := pow_pos hν 2
    have h2 : 0 < cstar * γ⁻¹ * (3 : ℝ) ^ (2 * γ * (m : ℝ)) :=
      mul_pos (mul_pos hcstar (inv_pos.mpr hγ))
        (Real.rpow_pos_of_pos (by norm_num) _)
    linarith only [h1, h2]
  have hRnn : 0 ≤ R := Real.sqrt_nonneg _
  have hSnn : 0 ≤ S := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = Θ * γ := by
    rw [hR_def, Real.sq_sqrt (le_of_lt (mul_pos hΘpos hγ))]
  have hR1 : R ≤ 1 := by
    rw [hR_def]
    calc Real.sqrt (Θ * γ) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hΘγ_le
      _ = 1 := Real.sqrt_one
  have hγ_le_R : γ ≤ R := by
    have hγR2 : γ ≤ R ^ 2 := by
      rw [hR2]
      linarith only [mul_nonneg (by linarith only [hΘ1] : (0:ℝ) ≤ Θ - 1) hγ.le]
    have hRR : R ^ 2 ≤ R := by
      linarith only [mul_nonneg hRnn (by linarith only [hR1] : (0:ℝ) ≤ 1 - R)]
    linarith only [hγR2, hRR]
  -- R ≤ 2 S, from Θ ≤ 4
  have hRle2S : R ≤ 2 * S := by
    have hmono : Real.sqrt (Θ * γ) ≤ Real.sqrt (2 ^ 2 * (E * B * γ)) := by
      apply Real.sqrt_le_sqrt
      have h1 : Θ * γ ≤ 4 * (E * B) * γ := mul_le_mul_of_nonneg_right hΘle4 hγ.le
      have h2 : 4 * (E * B) * γ = 2 ^ 2 * (E * B * γ) := by ring
      linarith only [h1, h2.le, h2.ge]
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ (2:ℝ) ^ 2),
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ (2:ℝ))] at hmono
    rw [hR_def, hS_def]
    exact hmono
  -- make x, T, P, R, S opaque so the numeric tactics never zeta-unfold into `rpow`
  clear_value x T P R S
  -- |x² − P| ≤ (C₀ R + 4γ) T
  have htri : |x ^ 2 - P| ≤ |x ^ 2 - T| + |T - P| := abs_sub_le _ _ _
  have hxP : |x ^ 2 - P| ≤ (C₀ * R + 4 * γ) * T := by
    calc |x ^ 2 - P| ≤ |x ^ 2 - T| + |T - P| := htri
      _ ≤ C₀ * R * T + 4 * γ * T := add_le_add hdev hTP0
      _ = (C₀ * R + 4 * γ) * T := by ring
  -- √P factorization
  have hsqrtPnn : 0 ≤ Real.sqrt P := Real.sqrt_nonneg _
  have hsqrtP : Real.sqrt P ^ 2 = P := Real.sq_sqrt hPpos.le
  have hxsP : 0 < x + Real.sqrt P := add_pos_of_pos_of_nonneg hxpos hsqrtPnn
  have hfactor : (x - Real.sqrt P) * (x + Real.sqrt P) = x ^ 2 - P := by
    have heq : (x - Real.sqrt P) * (x + Real.sqrt P) = x ^ 2 - Real.sqrt P ^ 2 := by ring
    rw [heq, hsqrtP]
  have hprod : |x - Real.sqrt P| * (x + Real.sqrt P) = |x ^ 2 - P| := by
    rw [← abs_of_pos hxsP, ← abs_mul, hfactor]
  -- |x²−P| ≤ 2(C₀R+4γ) x² ≤ (2C₀+8) R x² ≤ x²
  have hcoefRnn : 0 ≤ C₀ * R + 4 * γ := by
    have hC₀R : 0 ≤ C₀ * R := mul_nonneg hC₀pos.le hRnn
    linarith only [hC₀R, hγ.le]
  have hCS : (2 * C₀ + 8) * R ≤ recurrenceIntegrationConstant * S := by
    have h1 : (2 * C₀ + 8) * R ≤ (2 * C₀ + 8) * (2 * S) :=
      mul_le_mul_of_nonneg_left hRle2S (by linarith only [hC₀pos])
    have h2 : (2 * C₀ + 8) * (2 * S) ≤ recurrenceIntegrationConstant * S := by
      have hnum : (4 * C₀ + 16 : ℝ) ≤ recurrenceIntegrationConstant := by
        rw [hC₀, recurrenceIntegrationConstant_eq]; norm_num [recurrenceDescentConstant]
      linarith only [mul_le_mul_of_nonneg_right hnum hSnn]
    linarith only [h1, h2]
  have hxP2 : |x ^ 2 - P| ≤ recurrenceIntegrationConstant * S * x ^ 2 := by
    have hstep1 : (C₀ * R + 4 * γ) * T ≤ (C₀ * R + 4 * γ) * (2 * x ^ 2) :=
      mul_le_mul_of_nonneg_left hsand hcoefRnn
    have hstep2 : (C₀ * R + 4 * γ) * (2 * x ^ 2) ≤ (2 * C₀ + 8) * R * x ^ 2 := by
      have hnn : 0 ≤ 8 * ((R - γ) * x ^ 2) :=
        mul_nonneg (by norm_num) (mul_nonneg (by linarith only [hγ_le_R]) (sq_nonneg x))
      have hexp : (2 * C₀ + 8) * R * x ^ 2 - (C₀ * R + 4 * γ) * (2 * x ^ 2)
          = 8 * ((R - γ) * x ^ 2) := by ring
      linarith only [hnn, hexp]
    have hstep3 : (2 * C₀ + 8) * R * x ^ 2 ≤ recurrenceIntegrationConstant * S * x ^ 2 :=
      mul_le_mul_of_nonneg_right hCS (sq_nonneg x)
    exact le_trans hxP (le_trans hstep1 (le_trans hstep2 hstep3))
  -- conclude: |x − √P| ≤ x
  have hcoef : 0 ≤ recurrenceIntegrationConstant * S * x :=
    mul_nonneg (mul_nonneg hCpos.le hSnn) hxpos.le
  have hfinal : |x - Real.sqrt P| * (x + Real.sqrt P)
      ≤ (recurrenceIntegrationConstant * S * x) * (x + Real.sqrt P) := by
    rw [hprod]
    calc |x ^ 2 - P| ≤ recurrenceIntegrationConstant * S * x ^ 2 := hxP2
      _ ≤ (recurrenceIntegrationConstant * S * x) * (x + Real.sqrt P) := by
          have hnn : 0 ≤ (recurrenceIntegrationConstant * S * x) * Real.sqrt P :=
            mul_nonneg hcoef hsqrtPnn
          have hexp : (recurrenceIntegrationConstant * S * x) * (x + Real.sqrt P)
              - recurrenceIntegrationConstant * S * x ^ 2
              = (recurrenceIntegrationConstant * S * x) * Real.sqrt P := by ring
          linarith only [hnn, hexp]
  exact le_of_mul_le_mul_right hfinal hxsP

/-! ### `l.integrate.approx.recurrence` -/

/-- **Two-constant form of `l.integrate.approx.recurrence`**.

The manuscript denominates both the a-priori envelope `e.small.scale.bound` and
the fixed-point target `A_{n,m}` / `P_m` in the single constant `c⋆`.

Taking `c⁺ = c⋆` recovers `integrate_approx_recurrence` up to the universal
constant.  This is **not** a node statement: `l.integrate.approx.recurrence` is
`integrate_approx_recurrence` above. -/
theorem integrate_approx_recurrence_cstarPlus
    {ν cstar cstarPlus γ E F : ℝ} {m₀ : ℤ} {s : ℤ → ℝ}
    (hν : 0 < ν) (hcstar : 0 < cstar) (hcstar32 : cstar ≤ 3 / 2)
    (hcc : cstar ≤ cstarPlus) (hγ : 0 < γ) (hE : 1 ≤ E) (hF : 1 ≤ F)
    (hsmall : ∀ m : ℤ, ν ≤ s m ∧
      s m ≤ (1 + (ν ^ 2)⁻¹ * cstarPlus * γ⁻¹ * (3 : ℝ) ^ (2 * γ * (m : ℝ))) * ν)
    (hupper : ∀ n m : ℤ, m ≤ m₀ → n ≤ m → (m : ℝ) ≤ (n : ℝ) + cstar * γ⁻¹ →
      s m ≤ (1 + E * γ) * s n + recurrenceIncrement cstar γ n m * (s n)⁻¹)
    (hlower : ∀ n m : ℤ, m ≤ m₀ → n ≤ m → (m : ℝ) ≤ (n : ℝ) + cstar * γ⁻¹ →
      (1 - E * γ) * s n + recurrenceIncrement cstar γ n m * ((s n)⁻¹) ^ 2 * s m
          - F * ((m : ℝ) - (n : ℝ)) ^ 2 * ((s n)⁻¹) ^ 4 * s m *
            (3 : ℝ) ^ (4 * γ * (m : ℝ))
        ≤ s m) :
    γ ≤ (recurrenceIntegrationConstant
      * (E * (1 + (cstar ^ 2)⁻¹ * F + (cstar ^ 2)⁻¹ * cstarPlus)))⁻¹ →
      ∀ m : ℤ, m ≤ m₀ →
        |s m - Real.sqrt
            (ν ^ 2 + cstar * γ⁻¹ * (3 : ℝ) ^ (2 * γ * (m : ℝ)))|
          ≤ recurrenceIntegrationConstant
              * Real.sqrt (E * (1 + (cstar ^ 2)⁻¹ * F + (cstar ^ 2)⁻¹ * cstarPlus) * γ)
                * s m := by
  have hcstar2pos : (0:ℝ) < cstar ^ 2 := pow_pos hcstar 2
  have hcplus_pos : 0 < cstarPlus := lt_of_lt_of_le hcstar hcc
  have hFterm : (0:ℝ) ≤ (cstar ^ 2)⁻¹ * F :=
    mul_nonneg (inv_nonneg.mpr hcstar2pos.le) (by linarith only [hF])
  have hCterm : (0:ℝ) ≤ (cstar ^ 2)⁻¹ * cstarPlus :=
    mul_nonneg (inv_nonneg.mpr hcstar2pos.le) hcplus_pos.le
  have hB1 : (1:ℝ) ≤ 1 + (cstar ^ 2)⁻¹ * F + (cstar ^ 2)⁻¹ * cstarPlus := by
    linarith only [hFterm, hCterm]
  -- `(c⋆·min{c⋆,1})⁻¹ ≤ 4 (c⋆²)⁻¹`, i.e. `c⋆ ≤ 4·min{c⋆,1}`, from `c⋆ ≤ 3/2`
  have hcapinv : (cstar * min cstar 1)⁻¹ ≤ 4 * (cstar ^ 2)⁻¹ := by
    have hcbpos : (0:ℝ) < cstar * min cstar 1 := mul_pos hcstar (lt_min hcstar one_pos)
    have hkey : cstar ^ 2 ≤ 4 * (cstar * min cstar 1) := by
      rcases le_total cstar 1 with hc | hc
      · rw [min_eq_left hc]; linarith only [sq_nonneg cstar]
      · rw [min_eq_right hc]
        linarith only [mul_le_mul_of_nonneg_right hcstar32 hcstar.le, hcstar.le]
    have h1 : (1:ℝ) / (4 * (cstar * min cstar 1)) ≤ 1 / cstar ^ 2 :=
      one_div_le_one_div_of_le hcstar2pos hkey
    have h2 : (1:ℝ) / (4 * (cstar * min cstar 1)) = (1 / 4) * (cstar * min cstar 1)⁻¹ := by
      rw [one_div, mul_inv]; norm_num
    rw [h2] at h1
    simp only [one_div] at h1
    linarith only [h1, hcbpos]
  have hBle : 1 + (cstar ^ 2)⁻¹ * F + (cstar * min cstar 1)⁻¹ * cstarPlus
      ≤ 4 * (1 + (cstar ^ 2)⁻¹ * F + (cstar ^ 2)⁻¹ * cstarPlus) := by
    have hmul : (cstar * min cstar 1)⁻¹ * cstarPlus ≤ (4 * (cstar ^ 2)⁻¹) * cstarPlus :=
      mul_le_mul_of_nonneg_right hcapinv hcplus_pos.le
    linarith only [hFterm, hmul]
  exact integrate_of_bracket hν hcstar hcc hγ hE hF hsmall hupper hlower hB1 hBle

end

end Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration
