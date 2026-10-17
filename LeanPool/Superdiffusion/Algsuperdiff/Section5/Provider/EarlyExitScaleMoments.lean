/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.EarlyExitConfinementModel

/-!
# EarlyExitScaleMoments

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The confinement scale with its moment field and its restricted displacement tail

The quenched estimates at the random confinement scale are read by two further layers, and
both of them ask for more about the family of displacement scales than the early-exit
probability alone.

The annealed components of the superdiffusive bound need uniform bounds on the moments of
that family, of orders `4p` and `8p`, at one constant and over a range of exponents.  The
removal steps of the quenched composer need the displacement tail of the process at every
scale above the confinement scale, not only at the confinement scale itself.

Both are consequences of the same construction: the crossing scales of the percolation
estimate have an exponential tail, whose integration gives the moments; and the regime of
the chained early-exit estimate is met at every scale above the confinement scale, which
gives the tail there.  This module packages them with the data they must be read at — one
family, one confinement constant, one deterministic factor, hence one confinement scale.

## Main results

* `measureReal_exitEvent_confinementScale_le_pow_of_threshold`
  — the early-exit probability at the confinement scale together with the moment field of the
  displacement scales and the restricted displacement tail, at one and the same family.

## References

* ABK26, the early-exit estimate of Section 5.3 and the superdiffusive displacement bounds
  of Section 5.4.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3 Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open DivergenceFormProcess.Form DivergenceFormProcess.StoppedDirichlet
open HCPolySupport MarkovProcess MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem cubeSetAt_zero_eq_openCube (m : ℤ) :
    cubeSetAt (0 : Vec d) m = openCubeSet (originCube d m) := by
  ext z
  rw [cubeSetAt]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa only [zero_add] using ha
  · intro hz
    exact ⟨z, hz, by simp only [zero_add]⟩

/-- **The early-exit probability, the moment field and the restricted displacement tail at
one confinement scale, with uniform constants.**  Beside the early-exit probability at the
confinement scale, the family of displacement scales is returned with its measurability, its
nonnegativity and a uniform bound on its moments of order `4p` and `8p` for every exponent
`p` between `1` and the returned `pS`, at the single constant `CS`; and the process is
returned with its displacement tail at every scale above the confinement scale, in the form
carrying the two-branch minimum and in the form carrying the confinement radius, the latter
at both the returned rate and the uniform rate `cbar`, which is the shape the removal steps
read.

Four constants are returned before the model and the time, so that a caller whose own
constants are fixed at that level can use them: `Cscale`, which bounds the range of exponents
from below by `Cscale⁻¹ γ^{-1} |log γ|^{-6} ≤ pS`; `CSbar` and `Kbar`, which bound `CS` and
`K` from above; and `cbar`, which bounds the exponential rate from below.

Everything is stated at one and the same `S`, `K` and `L`, hence at one and the same
confinement scale, and the confinement constant is above the prescribed threshold `Kmin`, so
a consumer with a further lower bound on it can impose that bound here. -/
theorem measureReal_exitEvent_confinementScale_le_pow_of_threshold
    (d : ℕ) [NeZero d] (hdim : 2 ≤ d) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 Cscale CSbar Kbar cbar : ℝ,
      0 < gamma0 ∧ 1 ≤ Cscale ∧ 1 ≤ CSbar ∧ 1 ≤ Kbar ∧ 0 < cbar ∧ cbar ≤ 1 ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ t : ℝ, 0 < t → ∀ Kmin : ℝ,
        ∃ (S : ℤ → Cutoff.CutoffSample d → ℝ) (K L c CS pS : ℝ),
          1 ≤ K ∧ Kmin ≤ K ∧ 0 < c ∧ c ≤ 1 ∧ cbar ≤ c ∧
          L = K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t ∧
          (∃ (delta : ℝ) (Y : ℤ → Cutoff.CutoffSample d → ℕ),
            0 < delta ∧ delta ≤ 1 ∧ (∀ i : ℤ, Measurable (Y i)) ∧
            ∀ (i : ℤ) (omega : Cutoff.CutoffSample d),
              S i omega = displacementScale delta M.gamma (Y i omega)) ∧
          (∀ n : ℤ, Measurable (S n)) ∧
          (∀ (n : ℤ) (omega : Cutoff.CutoffSample d), 0 ≤ S n omega) ∧
          1 ≤ CS ∧ 1 ≤ pS ∧ CS ≤ CSbar ∧ K ≤ max Kbar Kmin ∧
          Cscale⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) ≤ pS ∧
          (∀ p : ℝ, 1 ≤ p → p ≤ pS →
            (∀ n : ℤ, (∫⁻ omega, ENNReal.ofReal (S n omega) ^ (4 * p)
                ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal CS ^ (4 * p)) ∧
            (∀ n : ℤ, (∫⁻ omega, ENNReal.ofReal (S n omega) ^ (8 * p)
                ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal CS ^ (8 * p))) ∧
          (∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
            IsConfinementScale (fun n => widenedScale (fun i => S i omega.1) n) L
              (confinementScale S L omega.1)) ∧
          (∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
            letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
            letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
            ((streamExhaustionTailInput M omega).wholeSpaceProcess
                ((0 : Vec d) : OnePoint (Vec d))
              (survivalEvent (((↑) : Vec d → OnePoint (Vec d)) ''
                cubeSetAt (0 : Vec d) (confinementScale S L omega.1))
                t.toNNReal)ᶜ).toReal ≤ M.gamma ^ (100 : ℕ)) ∧
          (∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
            letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
            letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
            ∀ k : ℤ, (3 : ℝ) ^ (confinementScale S L omega.1) ≤ (3 : ℝ) ^ k →
              (streamExhaustionTailInput M omega).wholeSpaceProcess
                  ((0 : Vec d) : OnePoint (Vec d))
                  {eta | (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤
                    ‖onePointRetract (0 : Vec d) (eta t.toNNReal)‖} ≤
                ENNReal.ofReal (Real.exp (-c *
                  displacementMinScale M.nu cstar M.gamma t k))) ∧
          (∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
            letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
            letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
            ∀ k : ℤ, (3 : ℝ) ^ (confinementScale S L omega.1) ≤ (3 : ℝ) ^ k →
              (streamProcess M omega ((0 : Vec d) : OnePoint (Vec d))).real
                  {eta | (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤
                    ‖onePointRetract (0 : Vec d) (eta t.toNNReal)‖} ≤
                Real.exp (-c * (((3 : ℝ) ^ k /
                  (3 : ℝ) ^ (confinementScale S L omega.1)) ^ (2 : ℕ)))) ∧
          ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
            letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
            letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
            ∀ k : ℤ, (3 : ℝ) ^ (confinementScale S L omega.1) ≤ (3 : ℝ) ^ k →
              (streamProcess M omega ((0 : Vec d) : OnePoint (Vec d))).real
                  {eta | (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤
                    ‖onePointRetract (0 : Vec d) (eta t.toNNReal)‖} ≤
                Real.exp (-cbar * (((3 : ℝ) ^ k /
                  (3 : ℝ) ^ (confinementScale S L omega.1)) ^ (2 : ℕ))) := by
  obtain ⟨gamma0, Cscale, CSbar, Kbar, cbar, hgamma0, hCscale1, hCSbar1, hKbar1, hcbarpos,
    hcbar1, hgcstar, hmain⟩ :=
    exists_ae_confinement_exitTime_bound_of_threshold
      d hdim cstar hcstar
  refine ⟨gamma0, Cscale, CSbar, Kbar, cbar, hgamma0, hCscale1, hCSbar1, hKbar1, hcbarpos,
    hcbar1, ?_⟩
  intro M hcs hgam t ht Kmin
  obtain ⟨S, K, L, c, CS, pS, hK, hKmin, hcpos, hc1, hcbarle, hcK, hLdef, hSform, hSmeas,
    hSnn, hCS, hpS1, hCSle, hKle, hpSrange, hSmom, hconf, hexitk⟩ :=
    hmain M hcs hgam t ht Kmin
  have hgc : M.gamma ≤ cstar := hgam.trans hgcstar
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hgamma4 : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  have hgamma1 : M.gamma < 1 := lt_of_le_of_lt hgamma4 (by norm_num)
  have hR : 0 < intrinsicScale M.nu cstar M.gamma t :=
    intrinsicScale_pos M.nu_pos hcstar hgamma ht
  have hs1 : 1 ≤ Real.sqrt |Real.log M.gamma| := one_le_sqrt_abs_log hgamma hgamma4
  have hKs : (1 : ℝ) ≤ K * Real.sqrt |Real.log M.gamma| := by nlinarith only [hK, hs1]
  have hRL : intrinsicScale M.nu cstar M.gamma t ≤ L := by
    rw [hLdef]
    nth_rewrite 1 [← one_mul (intrinsicScale M.nu cstar M.gamma t)]
    exact mul_le_mul_of_nonneg_right hKs hR.le
  -- the early-exit probability at the confinement scale
  have hearly :=
    measureReal_compl_survivalEvent_confinementScale_le_pow_of_exitTail_at_confinementScale
      M S hcstar hgc ht hK hcpos.le hcK (le_of_eq hLdef.symm) hconf
      (by filter_upwards [hexitk] with omega hmexit using hmexit _ le_rfl)
  -- the restricted displacement tail, in the two-branch form
  have hdispk : ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
      ∀ k : ℤ, (3 : ℝ) ^ (confinementScale S L omega.1) ≤ (3 : ℝ) ^ k →
        (streamExhaustionTailInput M omega).wholeSpaceProcess
            ((0 : Vec d) : OnePoint (Vec d))
            {eta | (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤
              ‖onePointRetract (0 : Vec d) (eta t.toNNReal)‖} ≤
          ENNReal.ofReal (Real.exp (-c *
            displacementMinScale M.nu cstar M.gamma t k)) := by
    filter_upwards [hexitk] with omega hmexit
    let := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
    let := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
    intro k hk3
    have hk : confinementScale S L omega.1 ≤ k :=
      (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hk3
    refine le_trans ?_ (hmexit k hk)
    rw [cubeSetAt_zero_eq_openCube]
    exact measure_norm_ge_le_measure_exitTime_le_retract
      ((streamExhaustionTailInput M omega).wholeSpaceProcess
        ((0 : Vec d) : OnePoint (Vec d)))
      ((↑) : Vec d → OnePoint (Vec d)) (onePointRetract (0 : Vec d))
      (onePointRetract_coe (0 : Vec d)) k t.toNNReal
  -- the restricted displacement tail, at the confinement radius
  have hdispR : ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
      ∀ k : ℤ, (3 : ℝ) ^ (confinementScale S L omega.1) ≤ (3 : ℝ) ^ k →
        (streamProcess M omega ((0 : Vec d) : OnePoint (Vec d))).real
            {eta | (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤
              ‖onePointRetract (0 : Vec d) (eta t.toNNReal)‖} ≤
          Real.exp (-c * (((3 : ℝ) ^ k /
            (3 : ℝ) ^ (confinementScale S L omega.1)) ^ (2 : ℕ))) := by
    filter_upwards [hconf, hdispk] with omega hmconf hmdisp
    let := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
    let := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
    intro k hk3
    have hRm : intrinsicScale M.nu cstar M.gamma t ≤
        (3 : ℝ) ^ (confinementScale S L omega.1) :=
      le_three_zpow_of_isConfinementScale' hRL hmconf
    have hRk : intrinsicScale M.nu cstar M.gamma t ≤ (3 : ℝ) ^ k := le_trans hRm hk3
    have hdiv : (3 : ℝ) ^ k / (3 : ℝ) ^ (confinementScale S L omega.1) ≤
        (3 : ℝ) ^ k / intrinsicScale M.nu cstar M.gamma t := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) <
        (3 : ℝ) ^ (confinementScale S L omega.1)) hR]
      exact mul_le_mul_of_nonneg_left hRm (by positivity)
    have hsq : ((3 : ℝ) ^ k / (3 : ℝ) ^ (confinementScale S L omega.1)) ^ (2 : ℕ) ≤
        ((3 : ℝ) ^ k / intrinsicScale M.nu cstar M.gamma t) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hdiv 2
    have hmin := sq_div_intrinsicScale_le_displacementMinScale M.nu_pos hcstar hgamma
      hgamma1 hgc ht hRk
    have hMk : ((3 : ℝ) ^ k / (3 : ℝ) ^ (confinementScale S L omega.1)) ^ (2 : ℕ) ≤
        displacementMinScale M.nu cstar M.gamma t k := by
      refine hsq.trans ?_
      rw [displacementMinScale]
      have hzp : ((3 : ℝ) ^ k) ^ (2 : ℕ) = (3 : ℝ) ^ (2 * k) := by
        rw [← zpow_natCast ((3 : ℝ) ^ k) 2, ← zpow_mul]
        congr 1
        push_cast
        ring
      rw [← hzp]
      exact hmin
    have hexp : Real.exp (-c * displacementMinScale M.nu cstar M.gamma t k) ≤
        Real.exp (-c * (((3 : ℝ) ^ k /
          (3 : ℝ) ^ (confinementScale S L omega.1)) ^ (2 : ℕ))) :=
      Real.exp_le_exp.2 (by nlinarith only [hMk, hcpos])
    refine le_trans ?_ hexp
    calc ((streamProcess M omega ((0 : Vec d) : OnePoint (Vec d)))
          {eta | (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤
            ‖onePointRetract (0 : Vec d) (eta t.toNNReal)‖}).toReal
        ≤ (ENNReal.ofReal (Real.exp (-c *
            displacementMinScale M.nu cstar M.gamma t k))).toReal :=
          ENNReal.toReal_mono (by finiteness) (hmdisp k hk3)
      _ = Real.exp (-c * displacementMinScale M.nu cstar M.gamma t k) :=
          ENNReal.toReal_ofReal (Real.exp_nonneg _)
  -- the same tail at the uniform rate
  have hdispRbar : ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
      ∀ k : ℤ, (3 : ℝ) ^ (confinementScale S L omega.1) ≤ (3 : ℝ) ^ k →
        (streamProcess M omega ((0 : Vec d) : OnePoint (Vec d))).real
            {eta | (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤
              ‖onePointRetract (0 : Vec d) (eta t.toNNReal)‖} ≤
          Real.exp (-cbar * (((3 : ℝ) ^ k /
            (3 : ℝ) ^ (confinementScale S L omega.1)) ^ (2 : ℕ))) := by
    filter_upwards [hdispR] with omega hmR
    let := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
    let := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
    intro k hk3
    refine le_trans (hmR k hk3) (Real.exp_le_exp.2 ?_)
    have hX : (0 : ℝ) ≤ ((3 : ℝ) ^ k /
        (3 : ℝ) ^ (confinementScale S L omega.1)) ^ (2 : ℕ) := by positivity
    nlinarith only [hcbarle, hX]
  exact ⟨S, K, L, c, CS, pS, hK, hKmin, hcpos, hc1, hcbarle, hLdef, hSform, hSmeas, hSnn,
    hCS, hpS1, hCSle, hKle, hpSrange, hSmom, hconf, hearly, hdispk, hdispR, hdispRbar⟩

end

end Algsuperdiff.Section5.Provider
