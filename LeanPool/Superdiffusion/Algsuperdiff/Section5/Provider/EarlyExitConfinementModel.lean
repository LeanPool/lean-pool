/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.EarlyExitModel
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.ExitTimeTailModel
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SigmaBarProfile

/-!
# EarlyExitConfinementModel

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The early-exit probability at the confinement scale, from the model alone

The early-exit estimate of the stream field holds at a pair of scales `n ≤ m` under a list
of conditions: an accuracy inside the window of the percolation estimate, the crossing scale
`Y_m` below `m - n`, the auxiliary-scale straddle at `n`, the comparison of the two time
scales at `n`, a smallness condition on the separation parameter, and a lower bound on
`m - n`.  Every one of them is met here at the random confinement scale `m_t`, once the
displacement scales are taken to be those of the crossing scales.

Two features of the confinement scale do the work.  The first is that the defining
inequality `L (1 + S_{m_t}) ≤ 3^{m_t}` bounds the displacement scale at `m_t` by the
two-branch minimum `M(t, m_t)`, which is the hypothesis of the auxiliary-scale comparison;
the deterministic factor `L = K |log γ|^{1/2} R(t)` leaves a margin of `K² |log γ|` in that
comparison, and choosing `K` with `3^k ≤ K²` converts the margin into `n ≤ m_t - Y - k`,
which is the lower bound on `m_t - n`.  The second is that the same margin makes the
exponential of `-c M(t, m_t)` at most `γ^{100}` once `100 ≤ c K²`.

The order of the choices is therefore: the constants of the chained estimate first, then the
separation parameter `δ` from the smallness condition, then the exponential rate
`c = earlyExitDecayConstant d γ δ κ`, and only then the constant `K` of the confinement
scale, which has to satisfy both `100 ≤ c K²` and `3^k ≤ K²`.

## Main results

* `displacementScale_add_le_displacementMinScale_of_isConfinementScale` — the displacement
  scale at a confinement scale, shifted by a triadic factor below `K²`.
*
`exists_ae_confinement_exitTime_bound_of_threshold`
  — the early-exit tail of the stream process at and above the random confinement scale,
  together with the moment field of the displacement scales, above a prescribed lower bound
  on the confinement constant.
* `measureReal_compl_survivalEvent_confinementScale_le_pow_of_exitTail_at_confinementScale`
  — the early-exit probability at the confinement scale, from that tail.

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

/-! ## 1. The displacement scale at a confinement scale, with a margin -/

private abbrev earlyExitConfinementModel_rates_statement : Prop :=
    ∀ (d : ℕ) [inst : NeZero d] (hdim : (2 : ℕ) ≤ d) (cstar : ℝ) (hcstar : (0 : ℝ) < cstar)
      (gammaT Cev Cfloor Cchain ctail csmall Creg : ℝ) (hCchain : (0 : ℝ) < Cchain) (gammaL gammaR : ℝ),
      let ep : ℝ := min (1 / 4 : ℝ) csmall;
      ∀ (hepdef : ep = min (1 / 4 : ℝ) csmall),
        let kappa : ℝ := earlyExitKappa Cchain.toNNReal Cchain⁻¹.toNNReal;
        ∀ (hkappa : (0 : ℝ) < kappa) (hkappa1 : kappa ≤ (1 : ℝ)),
          let costBar : ℝ := (3 : ℝ) + (3 : ℝ) * (max (1 : ℝ) √cstar * Real.exp (1 / 2 : ℝ));
          ∀ (hcostBardef : costBar = (3 : ℝ) + (3 : ℝ) * (max (1 : ℝ) √cstar * Real.exp (1 / 2 : ℝ))),
            let delta : ℝ := min (1 : ℝ) (Cchain * kappa / ((128 : ℝ) * (3 : ℝ) ^ d * costBar));
            ∀ (hdelta1 : delta ≤ (1 : ℝ)) (hdelta : (0 : ℝ) < delta)
              (hdeltaBar : (128 : ℝ) * (3 : ℝ) ^ d * delta * costBar ≤ Cchain * kappa),
              let jbase : ℕ := earlyExitBaseScale d;
              ∀
                (htail :
                  ∀ (M : ABKModel d),
                    Disorder.cstar M = cstar →
                      M.gamma ≤ gammaT →
                        Cfloor * √M.gamma * |Real.log M.gamma|.rpow (7 / 2 : ℝ) ≤ ep ∧
                          ∀ ep ∈ Set.Icc (Cfloor * √M.gamma * |Real.log M.gamma|.rpow (7 / 2 : ℝ)) (1 / 4 : ℝ),
                            ep ≤ csmall →
                              ∀ (m : ℤ),
                                ∃ (Y : Cutoff.CutoffSample d → ℕ),
                                  Measurable Y ∧
                                    (∀ (N : ℕ),
                                        (1 : ℕ) ≤ N →
                                          ((↑(fullSampleLaw M) : Measure (FullSample d M.gamma)) :
                                                (a : Set (FullSample d M.gamma)) → ℝ≥0∞)
                                              {omegaFull : FullSample d M.gamma |
                                                N ≤ Y (↑omegaFull : Cutoff.CutoffSample d)} ≤
                                            ENNReal.ofReal
                                              (Real.exp
                                                (-(ctail * ep ^ (2 : ℕ) * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) *
                                                    (3 : ℝ) ^ N)))) ∧
                                      ∀ᵐ (omegaFull :
                                        FullSample d M.gamma) ∂(↑(fullSampleLaw M) : Measure (FullSample d M.gamma)),
                                        ∀ n ≤ m - (↑(Y (↑omegaFull : Cutoff.CutoffSample d)) : ℤ),
                                          ∀ (_i : Fin d) (Good : Percolation.Site d → Prop) [DecidablePred Good],
                                            (∀ (z : Percolation.Site d),
                                                Good z ↔
                                                  (↑omegaFull : Cutoff.CutoffSample d) ∈
                                                    qEvent M Creg Cev n (rescaledLatticePoint n z) ep) →
                                              ∀ (delta : ℝ),
                                                (0 : ℝ) < delta →
                                                  delta ≤ (1 : ℝ) →
                                                    ∀ (t : ℝ≥0),
                                                      (0 : ℝ) < (↑t : ℝ) →
                                                        (3 : ℝ) ^ n ≤
                                                            auxiliaryScaleBound M.nu (Disorder.cstar M) M.gamma delta
                                                              (↑t : ℝ) m →
                                                          auxiliaryScaleBound M.nu (Disorder.cstar M) M.gamma delta (↑t : ℝ)
                                                                m <
                                                              (3 : ℝ) ^ (n + (1 : ℤ)) →
                                                            lengthTimeScale M.nu (Disorder.cstar M) M.gamma ((3 : ℝ) ^ n) ≤
                                                                (2 : ℝ) * exitTimeScale M n →
                                                              (128 : ℝ) * (3 : ℝ) ^ d * delta *
                                                                    earlyExitProfileCost (Disorder.cstar M) M.gamma ≤
                                                                  Cchain * kappa →
                                                                jbase ≤ (3 : ℕ) ^ (m - n).toNat →
                                                                  ∀
                                                                    x ∈
                                                                      Metric.closedBall (0 : Vec d)
                                                                        ((1 / 2 : ℝ) * (3 : ℝ) ^ (m - (1 : ℤ))),
                                                                    ((streamProcess M omegaFull :
                                                                              (a : OnePoint (Vec d)) →
                                                                                Measure (ContinuousPath (OnePoint (Vec d))))
                                                                            (↑x : OnePoint (Vec d)) :
                                                                          (a : Set (ContinuousPath (OnePoint (Vec d)))) →
                                                                            ℝ≥0∞)
                                                                        {eta : ContinuousPath (OnePoint (Vec d)) |
                                                                          ContinuousPath.exitTime
                                                                              (OnePoint.some ''
                                                                                openCubeSet (originCube d m))
                                                                              eta ≤
                                                                            (↑t : ℝ≥0∞)} ≤
                                                                      ENNReal.ofReal
                                                                        (Real.exp
                                                                          (-earlyExitDecayConstant d M.gamma delta kappa *
                                                                            displacementMinScale M.nu (Disorder.cstar M)
                                                                              M.gamma (↑t : ℝ) m))),
                let cbar : ℝ := kappa * delta ^ (2 : ℕ) / ((192 : ℝ) * (3 : ℝ) ^ d);
                ∀ (hcbardef : cbar = kappa * delta ^ (2 : ℕ) / ((192 : ℝ) * (3 : ℝ) ^ d)) (hcbarpos : (0 : ℝ) < cbar),
                  let Kbar : ℝ := max (max (1 : ℝ) √((100 : ℝ) / cbar)) √((3 : ℝ) ^ jbase);
                  ∀ (hKbardef : Kbar = max (max (1 : ℝ) √((100 : ℝ) / cbar)) √((3 : ℝ) ^ jbase)) (M : ABKModel d)
                    (hcs : Disorder.cstar M = cstar) (hgam : M.gamma ≤ min (min gammaT gammaL) (min gammaR cstar))
                    (Kmin : ℝ),
                    M.gamma ≤ gammaL ∧
                      M.gamma ≤ gammaR ∧
                        M.gamma ≤ cstar ∧
                          (0 : ℝ) < M.gamma ∧
                            M.gamma ≤ (1 / 4 : ℝ) ∧
                              M.gamma < (1 : ℝ) ∧
                                (0 : ℕ) < d ∧
                                  Cfloor * √M.gamma * |Real.log M.gamma|.rpow (7 / 2 : ℝ) ≤ ep ∧
                                    (∀ ep ∈ Set.Icc (Cfloor * √M.gamma * |Real.log M.gamma|.rpow (7 / 2 : ℝ)) (1 / 4 : ℝ),
                                        ep ≤ csmall →
                                          ∀ (m : ℤ),
                                            ∃ (Y : Cutoff.CutoffSample d → ℕ),
                                              Measurable Y ∧
                                                (∀ (N : ℕ),
                                                    (1 : ℕ) ≤ N →
                                                      ((↑(fullSampleLaw M) : Measure (FullSample d M.gamma)) :
                                                            (a : Set (FullSample d M.gamma)) → ℝ≥0∞)
                                                          {omegaFull : FullSample d M.gamma |
                                                            N ≤ Y (↑omegaFull : Cutoff.CutoffSample d)} ≤
                                                        ENNReal.ofReal
                                                          (Real.exp
                                                            (-(ctail * ep ^ (2 : ℕ) * M.gamma⁻¹ *
                                                                  |Real.log M.gamma| ^ (-6 : ℤ) *
                                                                (3 : ℝ) ^ N)))) ∧
                                                  ∀ᵐ (omegaFull :
                                                    FullSample d
                                                      M.gamma) ∂(↑(fullSampleLaw M) : Measure (FullSample d M.gamma)),
                                                    ∀ n ≤ m - (↑(Y (↑omegaFull : Cutoff.CutoffSample d)) : ℤ),
                                                      ∀ (_i : Fin d) (Good : Percolation.Site d → Prop)
                                                        [DecidablePred Good],
                                                        (∀ (z : Percolation.Site d),
                                                            Good z ↔
                                                              (↑omegaFull : Cutoff.CutoffSample d) ∈
                                                                qEvent M Creg Cev n (rescaledLatticePoint n z) ep) →
                                                          ∀ (delta : ℝ),
                                                            (0 : ℝ) < delta →
                                                              delta ≤ (1 : ℝ) →
                                                                ∀ (t : ℝ≥0),
                                                                  (0 : ℝ) < (↑t : ℝ) →
                                                                    (3 : ℝ) ^ n ≤
                                                                        auxiliaryScaleBound M.nu (Disorder.cstar M) M.gamma
                                                                          delta (↑t : ℝ) m →
                                                                      auxiliaryScaleBound M.nu (Disorder.cstar M) M.gamma
                                                                            delta (↑t : ℝ) m <
                                                                          (3 : ℝ) ^ (n + (1 : ℤ)) →
                                                                        lengthTimeScale M.nu (Disorder.cstar M) M.gamma
                                                                              ((3 : ℝ) ^ n) ≤
                                                                            (2 : ℝ) * exitTimeScale M n →
                                                                          (128 : ℝ) * (3 : ℝ) ^ d * delta *
                                                                                earlyExitProfileCost (Disorder.cstar M)
                                                                                  M.gamma ≤
                                                                              Cchain * kappa →
                                                                            jbase ≤ (3 : ℕ) ^ (m - n).toNat →
                                                                              ∀
                                                                                x ∈
                                                                                  Metric.closedBall (0 : Vec d)
                                                                                    ((1 / 2 : ℝ) * (3 : ℝ) ^ (m - (1 : ℤ))),
                                                                                ((streamProcess M omegaFull :
                                                                                          (a : OnePoint (Vec d)) →
                                                                                            Measure
                                                                                              (ContinuousPath
                                                                                                (OnePoint (Vec d))))
                                                                                        (↑x : OnePoint (Vec d)) :
                                                                                      (a :
                                                                                          Set
                                                                                            (ContinuousPath
                                                                                              (OnePoint (Vec d)))) →
                                                                                        ℝ≥0∞)
                                                                                    {eta :
                                                                                      ContinuousPath (OnePoint (Vec d)) |
                                                                                      ContinuousPath.exitTime
                                                                                          (OnePoint.some ''
                                                                                            openCubeSet (originCube d m))
                                                                                          eta ≤
                                                                                        (↑t : ℝ≥0∞)} ≤
                                                                                  ENNReal.ofReal
                                                                                    (Real.exp
                                                                                      (-earlyExitDecayConstant d M.gamma
                                                                                            delta kappa *
                                                                                        displacementMinScale M.nu
                                                                                          (Disorder.cstar M) M.gamma
                                                                                          (↑t : ℝ) m))) ∧
                                      ep ∈ Set.Icc (Cfloor * √M.gamma * |Real.log M.gamma|.rpow (7 / 2 : ℝ)) (1 / 4 : ℝ) ∧
                                        ep ≤ csmall ∧
                                          (128 : ℝ) * (3 : ℝ) ^ d * delta * earlyExitProfileCost cstar M.gamma ≤
                                              Cchain * kappa ∧
                                            earlyExitDecayConstant d M.gamma delta kappa =
                                                earlyExitDecayConstant d M.gamma delta kappa ∧
                                              ((1 : ℝ) - M.gamma)⁻¹ ≤ (2 : ℝ) ∧
                                                (0 : ℝ) < earlyExitDecayConstant d M.gamma delta kappa ∧
                                                  earlyExitDecayConstant d M.gamma delta kappa ≤ (1 : ℝ) ∧
                                                    cbar ≤ earlyExitDecayConstant d M.gamma delta kappa ∧
                                                      (1 : ℝ) ≤
                                                          max
                                                            (max
                                                              (max (1 : ℝ)
                                                                √((100 : ℝ) / earlyExitDecayConstant d M.gamma delta kappa))
                                                              √((3 : ℝ) ^ jbase))
                                                            Kmin ∧
                                                        Kmin ≤
                                                            max
                                                              (max
                                                                (max (1 : ℝ)
                                                                  √((100 : ℝ) /
                                                                      earlyExitDecayConstant d M.gamma delta kappa))
                                                                √((3 : ℝ) ^ jbase))
                                                              Kmin ∧
                                                          (100 : ℝ) ≤
                                                              earlyExitDecayConstant d M.gamma delta kappa *
                                                                max
                                                                    (max
                                                                      (max (1 : ℝ)
                                                                        √((100 : ℝ) /
                                                                            earlyExitDecayConstant d M.gamma delta kappa))
                                                                      √((3 : ℝ) ^ jbase))
                                                                    Kmin ^
                                                                  (2 : ℕ) ∧
                                                            (3 : ℝ) ^ jbase ≤
                                                                max
                                                                    (max
                                                                      (max (1 : ℝ)
                                                                        √((100 : ℝ) /
                                                                            earlyExitDecayConstant d M.gamma delta kappa))
                                                                      √((3 : ℝ) ^ jbase))
                                                                    Kmin ^
                                                                  (2 : ℕ) ∧
                                                              max
                                                                  (max
                                                                    (max (1 : ℝ)
                                                                      √((100 : ℝ) /
                                                                          earlyExitDecayConstant d M.gamma delta kappa))
                                                                    √((3 : ℝ) ^ jbase))
                                                                  Kmin ≤
                                                                max Kbar Kmin

private theorem three_zpow_pow_two (m : ℤ) :
    ((3 : ℝ) ^ m) ^ (2 : ℕ) = (3 : ℝ) ^ (2 * m) := by
  rw [← zpow_natCast ((3 : ℝ) ^ m) 2, ← zpow_mul]
  congr 1
  push_cast
  ring

/-- **The displacement scale at and above a confinement scale, with a triadic margin.**  The
defining inequality of the confinement scale bounds `L S_r 3^{-2(r - m)}` by `3^m` at every
scale `r` above the confinement scale `m`, so the ratio between the two-branch minimum
`M(t, r)` and the displacement scale at `r` is at least `K² |log γ| ≥ K²`.  Any triadic factor
below `K²` may therefore be absorbed into the comparison, uniformly in `r ≥ m`. -/
theorem displacementScale_add_le_displacementMinScale_of_isConfinementScale
    {nu cstar gamma delta t K : ℝ} {Y : ℤ → ℕ} {m r : ℤ} {j : ℕ}
    (hnu : 0 < nu) (hcstar : 0 < cstar) (hgamma : 0 < gamma) (hgamma4 : gamma ≤ 1 / 4)
    (hgc : gamma ≤ cstar) (hdelta : 0 < delta) (ht : 0 < t) (hK : 1 ≤ K)
    (hjK : (3 : ℝ) ^ j ≤ K ^ (2 : ℕ))
    (hm : IsConfinementScale
      (fun n => widenedScale (fun i => displacementScale delta gamma (Y i)) n)
      (K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t) m)
    (hmr : m ≤ r) :
    displacementScale delta gamma (Y r + j) ≤ displacementMinScale nu cstar gamma t r := by
  have hgamma1 : gamma < 1 := lt_of_le_of_lt hgamma4 (by norm_num)
  have hR : 0 < intrinsicScale nu cstar gamma t := intrinsicScale_pos hnu hcstar hgamma ht
  have hs1 : 1 ≤ Real.sqrt |Real.log gamma| := one_le_sqrt_abs_log hgamma hgamma4
  have hs0 : (0 : ℝ) < Real.sqrt |Real.log gamma| := lt_of_lt_of_le zero_lt_one hs1
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have hA : (0 : ℝ) < K * Real.sqrt |Real.log gamma| := by positivity
  have hA1 : (1 : ℝ) ≤ K * Real.sqrt |Real.log gamma| := by nlinarith only [hK, hs1]
  have hXm : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hX : (0 : ℝ) < (3 : ℝ) ^ r := zpow_pos (by norm_num) r
  have hSpos : 0 < displacementScale delta gamma (Y r) :=
    displacementScale_pos hdelta gamma (Y r)
  have hw : (0 : ℝ) < (3 : ℝ) ^ (-2 * (r - m)) := zpow_pos (by norm_num) _
  have hLpos : (0 : ℝ) < K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t := by
    positivity
  have htwo : K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t ≤
      (3 : ℝ) ^ m := le_three_zpow_of_isConfinementScale' le_rfl hm
  have hterm : ENNReal.ofReal (displacementScale delta gamma (Y r) *
      (3 : ℝ) ^ (-2 * (r - m))) ≤
      widenedScale (fun i => displacementScale delta gamma (Y i)) m :=
    le_iSup_of_le ⟨r, hmr⟩ (by rfl)
  have hprodE : ENNReal.ofReal (K * Real.sqrt |Real.log gamma| *
        intrinsicScale nu cstar gamma t) *
      ENNReal.ofReal (displacementScale delta gamma (Y r) * (3 : ℝ) ^ (-2 * (r - m))) ≤
      ENNReal.ofReal ((3 : ℝ) ^ m) := by
    refine le_trans ?_ hm.1
    gcongr
    exact le_trans hterm le_add_self
  have hone : (K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t) *
      (displacementScale delta gamma (Y r) * (3 : ℝ) ^ (-2 * (r - m))) ≤ (3 : ℝ) ^ m := by
    rw [← ENNReal.ofReal_mul hLpos.le] at hprodE
    exact (ENNReal.ofReal_le_ofReal_iff hXm.le).mp hprodE
  have hsqrt2 : Real.sqrt |Real.log gamma| ^ (2 : ℕ) = |Real.log gamma| :=
    Real.sq_sqrt (abs_nonneg _)
  have hlog1 : (1 : ℝ) ≤ |Real.log gamma| := by nlinarith only [hs1, hsqrt2]
  have hK2 : (0 : ℝ) < K ^ (2 : ℕ) := pow_pos hK0 2
  have hmargin : (3 : ℝ) ^ j ≤ (K * Real.sqrt |Real.log gamma|) ^ (2 : ℕ) := by
    have hexp : (K * Real.sqrt |Real.log gamma|) ^ (2 : ℕ) =
        K ^ (2 : ℕ) * |Real.log gamma| := by rw [mul_pow, hsqrt2]
    rw [hexp]
    nlinarith only [hjK, hlog1, hK2]
  have hwX : (3 : ℝ) ^ (-2 * (r - m)) * ((3 : ℝ) ^ r) ^ (2 : ℕ) =
      (3 : ℝ) ^ m * (3 : ℝ) ^ m := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
      ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    omega
  have hchain : (3 : ℝ) ^ (-2 * (r - m)) *
      ((K * Real.sqrt |Real.log gamma|) ^ (2 : ℕ) *
        intrinsicScale nu cstar gamma t ^ (2 : ℕ) * displacementScale delta gamma (Y r)) ≤
      (3 : ℝ) ^ (-2 * (r - m)) * ((3 : ℝ) ^ r) ^ (2 : ℕ) := by
    rw [hwX]
    calc (3 : ℝ) ^ (-2 * (r - m)) *
          ((K * Real.sqrt |Real.log gamma|) ^ (2 : ℕ) *
            intrinsicScale nu cstar gamma t ^ (2 : ℕ) * displacementScale delta gamma (Y r))
        = ((K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t) *
            (displacementScale delta gamma (Y r) * (3 : ℝ) ^ (-2 * (r - m)))) *
          (K * Real.sqrt |Real.log gamma| * intrinsicScale nu cstar gamma t) := by ring
      _ ≤ (3 : ℝ) ^ m * (3 : ℝ) ^ m := by
          refine mul_le_mul hone htwo hLpos.le hXm.le
  have hkey0 : (K * Real.sqrt |Real.log gamma|) ^ (2 : ℕ) *
      intrinsicScale nu cstar gamma t ^ (2 : ℕ) * displacementScale delta gamma (Y r) ≤
      ((3 : ℝ) ^ r) ^ (2 : ℕ) := le_of_mul_le_mul_left hchain hw
  have hkey : (3 : ℝ) ^ j * displacementScale delta gamma (Y r) ≤
      ((3 : ℝ) ^ r / intrinsicScale nu cstar gamma t) ^ (2 : ℕ) := by
    rw [div_pow, le_div_iff₀ (by positivity : (0 : ℝ) < intrinsicScale nu cstar gamma t ^ 2)]
    calc (3 : ℝ) ^ j * displacementScale delta gamma (Y r) *
          intrinsicScale nu cstar gamma t ^ 2
        ≤ (K * Real.sqrt |Real.log gamma|) ^ (2 : ℕ) *
            displacementScale delta gamma (Y r) *
            intrinsicScale nu cstar gamma t ^ 2 := by
          have hstep := mul_le_mul_of_nonneg_right hmargin hSpos.le
          exact mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (K * Real.sqrt |Real.log gamma|) ^ (2 : ℕ) *
          intrinsicScale nu cstar gamma t ^ (2 : ℕ) *
          displacementScale delta gamma (Y r) := by ring
      _ ≤ ((3 : ℝ) ^ r) ^ (2 : ℕ) := hkey0
  have hexpand : displacementScale delta gamma (Y r + j) =
      (3 : ℝ) ^ j * displacementScale delta gamma (Y r) := by
    simp only [displacementScale, pow_add]
    ring
  rw [hexpand]
  refine hkey.trans ?_
  have hXmX : (3 : ℝ) ^ m ≤ (3 : ℝ) ^ r :=
    (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).2 hmr
  have hRle : intrinsicScale nu cstar gamma t ≤ (3 : ℝ) ^ r := by
    nlinarith only [hA1, hR, htwo, hXmX]
  have hmin := sq_div_intrinsicScale_le_displacementMinScale hnu hcstar hgamma hgamma1 hgc ht
    hRle
  rw [displacementMinScale, ← three_zpow_pow_two]
  exact hmin

/-! ## 2. The rate of the crossing tail -/

private theorem le_percolationRate
    {ctail Cfloor gamma ep B : ℝ} (hctail : 0 < ctail) (hCfloor : 0 < Cfloor)
    (hgamma : 0 < gamma) (hgamma4 : gamma ≤ 1 / 4)
    (hep : Cfloor * Real.sqrt gamma * Real.rpow |Real.log gamma| (7 / 2) ≤ ep)
    (hrate : B ≤ ctail * Cfloor ^ (2 : ℕ) * |Real.log gamma|) :
    B ≤ ctail * ep ^ (2 : ℕ) * gamma⁻¹ * |Real.log gamma| ^ (-6 : ℤ) := by
  have hgamma1 : gamma < 1 := lt_of_le_of_lt hgamma4 (by norm_num)
  have hlogne : Real.log gamma ≠ 0 := ne_of_lt (Real.log_neg hgamma hgamma1)
  have hLpos : 0 < |Real.log gamma| := abs_pos.mpr hlogne
  have hg0 : gamma ≠ 0 := hgamma.ne'
  have hL0 : |Real.log gamma| ≠ 0 := hLpos.ne'
  have hlow : 0 < Cfloor * Real.sqrt gamma * Real.rpow |Real.log gamma| (7 / 2) := by
    have := Real.sqrt_pos.2 hgamma
    have := Real.rpow_pos_of_pos hLpos (7 / 2 : ℝ)
    positivity
  have hsq : (Cfloor * Real.sqrt gamma * Real.rpow |Real.log gamma| (7 / 2)) ^ (2 : ℕ) ≤
      ep ^ (2 : ℕ) := pow_le_pow_left₀ hlow.le hep 2
  have hrp : (Real.rpow |Real.log gamma| (7 / 2)) ^ (2 : ℕ) = |Real.log gamma| ^ (7 : ℕ) := by
    have hbase : Real.rpow |Real.log gamma| (7 / 2) = |Real.log gamma| ^ ((7 : ℝ) / 2) := rfl
    rw [hbase, ← Real.rpow_natCast (|Real.log gamma| ^ ((7 : ℝ) / 2)) 2,
      ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_natCast |Real.log gamma| 7]
    norm_num
  have hexpand : (Cfloor * Real.sqrt gamma * Real.rpow |Real.log gamma| (7 / 2)) ^ (2 : ℕ) =
      Cfloor ^ (2 : ℕ) * gamma * |Real.log gamma| ^ (7 : ℕ) := by
    have hring : (Cfloor * Real.sqrt gamma * Real.rpow |Real.log gamma| (7 / 2)) ^ (2 : ℕ) =
        Cfloor ^ (2 : ℕ) * (Real.sqrt gamma * Real.sqrt gamma) *
          (Real.rpow |Real.log gamma| (7 / 2)) ^ (2 : ℕ) := by ring
    rw [hring, Real.mul_self_sqrt hgamma.le, hrp]
  rw [hexpand] at hsq
  have hzpow : |Real.log gamma| ^ (-6 : ℤ) = (|Real.log gamma| ^ (6 : ℕ))⁻¹ := by
    rw [show (-6 : ℤ) = -(6 : ℕ) by norm_num, zpow_neg, zpow_natCast]
  have hfac : (0 : ℝ) < ctail * (gamma⁻¹ * (|Real.log gamma| ^ (6 : ℕ))⁻¹) := by
    have : (0 : ℝ) < |Real.log gamma| ^ (6 : ℕ) := by positivity
    positivity
  have hmul := mul_le_mul_of_nonneg_left hsq hfac.le
  have hlhs : ctail * (gamma⁻¹ * (|Real.log gamma| ^ (6 : ℕ))⁻¹) *
      (Cfloor ^ (2 : ℕ) * gamma * |Real.log gamma| ^ (7 : ℕ)) =
      ctail * Cfloor ^ (2 : ℕ) * |Real.log gamma| := by
    field_simp
  have hrhs : ctail * (gamma⁻¹ * (|Real.log gamma| ^ (6 : ℕ))⁻¹) * ep ^ (2 : ℕ) =
      ctail * ep ^ (2 : ℕ) * gamma⁻¹ * |Real.log gamma| ^ (-6 : ℤ) := by
    rw [hzpow]; ring
  rw [hlhs, hrhs] at hmul
  exact hrate.trans hmul

private theorem exists_gamma_rate_threshold {ctail Cfloor : ℝ} (hctail : 0 < ctail)
    (hCfloor : 0 < Cfloor) (B : ℝ) :
    ∃ g : ℝ, 0 < g ∧ ∀ gamma : ℝ, 0 < gamma → gamma ≤ g → gamma ≤ 1 / 4 →
      B ≤ ctail * Cfloor ^ (2 : ℕ) * |Real.log gamma| := by
  have hapos : (0 : ℝ) < ctail * Cfloor ^ (2 : ℕ) := by positivity
  refine ⟨Real.exp (-(B / (ctail * Cfloor ^ (2 : ℕ)))), Real.exp_pos _, ?_⟩
  intro gamma hgamma hle hg4
  have hgamma1 : gamma < 1 := lt_of_le_of_lt hg4 (by norm_num)
  have hlog : Real.log gamma ≤ -(B / (ctail * Cfloor ^ (2 : ℕ))) := by
    have hstep := Real.log_le_log hgamma hle
    rwa [Real.log_exp] at hstep
  have habs : |Real.log gamma| = -Real.log gamma :=
    abs_of_neg (Real.log_neg hgamma hgamma1)
  have hstep : B / (ctail * Cfloor ^ (2 : ℕ)) ≤ -Real.log gamma := by
    linarith only [hlog]
  have hmul := mul_le_mul_of_nonneg_left hstep hapos.le
  have hcalc : ctail * Cfloor ^ (2 : ℕ) *
      (B / (ctail * Cfloor ^ (2 : ℕ))) = B := by
    field_simp
  rw [hcalc] at hmul
  rw [habs]
  exact hmul

/-- For `u ∈ (0, 1]`, `u |log u| ≤ 1`, in the form `u (-log u) ≤ 1`. -/
private theorem mul_neg_log_le_one {gamma : ℝ} (hgamma : 0 < gamma) :
    gamma * (-Real.log gamma) ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < gamma⁻¹ by positivity)
  rw [Real.log_inv] at h
  have hmul := mul_le_mul_of_nonneg_left h hgamma.le
  rw [mul_sub, mul_inv_cancel₀ hgamma.ne', mul_one] at hmul
  linarith only [hmul, hgamma]

/-- **The profile cost is bounded uniformly in the disorder.**  In
`3 + 3 (c⋆ γ^{-1})^{γ/2}` the exponent tends to zero with `γ`, and the two factors of the
second term are bounded separately: `(c⋆^{1/2})^γ` by `max 1 (c⋆^{1/2})` because the exponent
is in `(0, 1]`, and `(γ^{-1/2})^γ = exp((γ/2)|log γ|)` by `e^{1/2}` because `γ |log γ| ≤ 1`.
The bound depends only on the ellipticity constant. -/
private theorem earlyExitProfileCost_le {cstar gamma : ℝ} (hcstar : 0 < cstar)
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1) :
    earlyExitProfileCost cstar gamma ≤
      3 + 3 * (max 1 (Real.sqrt cstar) * Real.exp (1 / 2)) := by
  have hg0 : (0 : ℝ) ≤ gamma := hgamma.le
  have hcs : (0 : ℝ) ≤ Real.sqrt cstar := Real.sqrt_nonneg _
  have hinv : (0 : ℝ) < gamma⁻¹ := by positivity
  have hsplit : Real.sqrt (cstar * gamma⁻¹) = Real.sqrt cstar * Real.sqrt gamma⁻¹ :=
    Real.sqrt_mul hcstar.le _
  have hprod : (Real.sqrt (cstar * gamma⁻¹)) ^ gamma =
      (Real.sqrt cstar) ^ gamma * (Real.sqrt gamma⁻¹) ^ gamma := by
    rw [hsplit, Real.mul_rpow hcs (Real.sqrt_nonneg _)]
  have hfirst : (Real.sqrt cstar) ^ gamma ≤ max 1 (Real.sqrt cstar) := by
    rcases le_total (Real.sqrt cstar) 1 with h | h
    · exact le_trans (Real.rpow_le_one hcs h hg0) (le_max_left _ _)
    · calc (Real.sqrt cstar) ^ gamma ≤ (Real.sqrt cstar) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h hgamma1
        _ = Real.sqrt cstar := Real.rpow_one _
        _ ≤ max 1 (Real.sqrt cstar) := le_max_right _ _
  have hsecond : (Real.sqrt gamma⁻¹) ^ gamma ≤ Real.exp (1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hinv.le, Real.rpow_def_of_pos hinv,
      Real.log_inv]
    refine Real.exp_le_exp.2 ?_
    have hgl := mul_neg_log_le_one hgamma
    nlinarith only [hgl]
  have hnn2 : (0 : ℝ) ≤ (Real.sqrt gamma⁻¹) ^ gamma :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hmax : (0 : ℝ) ≤ max 1 (Real.sqrt cstar) := le_trans zero_le_one (le_max_left _ _)
  have hmul : (Real.sqrt cstar) ^ gamma * (Real.sqrt gamma⁻¹) ^ gamma ≤
      max 1 (Real.sqrt cstar) * Real.exp (1 / 2) :=
    mul_le_mul hfirst hsecond hnn2 hmax
  rw [earlyExitProfileCost, hprod]
  linarith only [hmul]

/-! ## 3. The early-exit tail at the confinement scale -/

omit [NeZero d] in
private theorem cubeSetAt_zero_eq_originCube (m : ℤ) :
    cubeSetAt (0 : Vec d) m = openCubeSet (originCube d m) := by
  ext z
  rw [cubeSetAt]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa only [zero_add] using ha
  · intro hz
    exact ⟨z, hz, by simp only [zero_add]⟩

private theorem compl_survivalEvent_eq {alpha : Type*} [MetricSpace alpha] (U : Set alpha)
    (t : NNReal) :
    (survivalEvent U t)ᶜ = {eta | ContinuousPath.exitTime U eta ≤ (t : ℝ≥0∞)} := by
  ext eta
  simp only [Set.mem_compl_iff, survivalEvent, Set.mem_ofPred_eq, not_lt]

private theorem earlyExitConfinementModel_momentBounds1 :
    ∀ (d : ℕ) (cstar Cchain ctail csmall : ℝ) (hctail : (0 : ℝ) < ctail) (hcsmall : (0 : ℝ) < csmall)
      (hlog3 : (0 : ℝ) < Real.log (3 : ℝ)),
      let ep : ℝ := min (1 / 4 : ℝ) csmall;
      ∀ (heppos : (0 : ℝ) < ep),
        let Cscale : ℝ := max (1 : ℝ) ((16 : ℝ) * Real.log (3 : ℝ) / (ctail * ep ^ (2 : ℕ)));
        let kappa : ℝ := earlyExitKappa Cchain.toNNReal Cchain⁻¹.toNNReal;
        let costBar : ℝ := (3 : ℝ) + (3 : ℝ) * (max (1 : ℝ) √cstar * Real.exp (1 / 2 : ℝ));
        let delta : ℝ := min (1 : ℝ) (Cchain * kappa / ((128 : ℝ) * (3 : ℝ) ^ d * costBar));
        ∀ (hdelta : (0 : ℝ) < delta),
          let jbase : ℕ := earlyExitBaseScale d;
          ∀ (M : ABKModel d) (t Kmin : ℝ) (hgamma : (0 : ℝ) < M.gamma),
            let c : ℝ := earlyExitDecayConstant d M.gamma delta kappa;
            let K : ℝ := max (max (max (1 : ℝ) √((100 : ℝ) / c)) √((3 : ℝ) ^ jbase)) Kmin;
            let L : ℝ := K * √|Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t;
            ∀ (hL : (0 : ℝ) < L) (Yfam : (m : ℤ) → Cutoff.CutoffSample d → ℕ) (hYmeas : ∀ (m : ℤ), Measurable (Yfam m)),
              let S : ℤ → Cutoff.CutoffSample d → ℝ := fun (i : ℤ) (omega : Cutoff.CutoffSample d) =>
                displacementScale delta M.gamma (Yfam i omega);
              ∀ (hSmeas : ∀ (i : ℤ), Measurable (S i)),
                let a : ℝ := ctail * ep ^ (2 : ℕ) * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ);
                ∀
                  (hYtail :
                    ∀ (m : ℤ) (N : ℕ),
                      (1 : ℕ) ≤ N →
                        ((↑(fullSampleLaw M) : Measure (FullSample d M.gamma)) : (a : Set (FullSample d M.gamma)) → ℝ≥0∞)
                            {omegaFull : FullSample d M.gamma | N ≤ Yfam m (↑omegaFull : Cutoff.CutoffSample d)} ≤
                          ENNReal.ofReal (Real.exp (-(a * (3 : ℝ) ^ N))))
                  (hadef : a = ctail * ep ^ (2 : ℕ) * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ))
                  (ha16 : (16 : ℝ) * Real.log (3 : ℝ) ≤ a) (ha : (0 : ℝ) < a),
                  let Cmom : ℝ := delta ^ (-((1 : ℝ) - M.gamma)⁻¹) * ((1 : ℝ) - Real.exp (-(a / (2 : ℝ))))⁻¹;
                  let CS : ℝ := max (1 : ℝ) Cmom;
                  ∀ (hCS : (1 : ℝ) ≤ CS),
                    let pS : ℝ := a / ((16 : ℝ) * Real.log (3 : ℝ));
                    ∀ (hpSdef : pS = a / ((16 : ℝ) * Real.log (3 : ℝ))),
                      (1 : ℝ) ≤ pS ∧
                        Cscale⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) ≤ pS ∧
                          (∀ (p : ℝ),
                              (1 : ℝ) ≤ p →
                                p ≤ pS →
                                  (∀ (n : ℤ),
                                      ∫⁻ (omega : Cutoff.CutoffSample d),
                                          ENNReal.ofReal (S n omega) ^
                                            ((4 : ℝ) * p) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) ≤
                                        ENNReal.ofReal CS ^ ((4 : ℝ) * p)) ∧
                                    ∀ (n : ℤ),
                                      ∫⁻ (omega : Cutoff.CutoffSample d),
                                          ENNReal.ofReal (S n omega) ^
                                            ((8 : ℝ) * p) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) ≤
                                        ENNReal.ofReal CS ^ ((8 : ℝ) * p)) ∧
                            ∀ᵐ (omega : FullSample d M.gamma) ∂(↑(fullSampleLaw M) : Measure (FullSample d M.gamma)),
                              IsConfinementScale
                                (fun (n : ℤ) => widenedScale (fun (k : ℤ) => S k (↑omega : Cutoff.CutoffSample d)) n) L
                                (confinementScale S L (↑omega : Cutoff.CutoffSample d)) := by
  intro d cstar Cchain ctail csmall hctail hcsmall hlog3 ep heppos Cscale kappa costBar delta hdelta jbase M t Kmin hgamma c K L hL Yfam hYmeas S hSmeas a hYtail hadef ha16 ha Cmom CS hCS pS hpSdef
  have hpS1 : (1 : ℝ) ≤ pS := by
    rw [hpSdef, le_div_iff₀ (by positivity : (0 : ℝ) < 16 * Real.log 3)]
    linarith only [ha16]
  have hpSrange : Cscale⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) ≤ pS := by
    have hLg : (0 : ℝ) < |Real.log M.gamma| := abs_log_gamma_pos M
    have hnn : (0 : ℝ) ≤ M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) := by positivity
    have hden : (0 : ℝ) < ctail * ep ^ (2 : ℕ) := by positivity
    have hBpos' : (0 : ℝ) < 16 * Real.log 3 / (ctail * ep ^ (2 : ℕ)) := by positivity
    have hinv : Cscale⁻¹ ≤ ctail * ep ^ (2 : ℕ) / (16 * Real.log 3) := by
      have h := inv_anti₀ hBpos'
        (le_max_right (1 : ℝ) (16 * Real.log 3 / (ctail * ep ^ (2 : ℕ))))
      rwa [inv_div] at h
    have h16 : (16 : ℝ) * Real.log 3 ≠ 0 := by positivity
    calc Cscale⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ)
        = Cscale⁻¹ * (M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ)) := by ring
      _ ≤ (ctail * ep ^ (2 : ℕ) / (16 * Real.log 3)) *
            (M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ)) :=
          mul_le_mul_of_nonneg_right hinv hnn
      _ = pS := by rw [hpSdef, hadef]; field_simp
  have hcut : ∀ (i : ℤ) (N : ℕ), 1 ≤ N →
      (Cutoff.cutoffSampleLaw M).toMeasure {omega | N ≤ Yfam i omega} ≤
        ENNReal.ofReal (Real.exp (-(a * (3 : ℝ) ^ N))) := by
    intro i N hN
    have hSet : MeasurableSet {omega : Cutoff.CutoffSample d | N ≤ Yfam i omega} :=
      measurableSet_le measurable_const (hYmeas i)
    have hEq : (Cutoff.cutoffSampleLaw M).toMeasure {omega | N ≤ Yfam i omega} =
        (fullSampleLaw M).toMeasure {omegaFull | N ≤ Yfam i omegaFull.1} := by
      rw [← map_fullSampleLaw_val M, Measure.map_apply measurable_subtype_coe hSet]
      rfl
    rw [hEq]
    exact hYtail i N hN
  have hmomq : ∀ q : ℝ, 1 ≤ q → 2 * (q * Real.log 3) ≤ a → ∀ i : ℤ,
      (∫⁻ omega, ENNReal.ofReal (S i omega) ^ q
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal CS ^ q := by
    intro q hq hqa i
    refine (lintegral_ofReal_displacementScale_rpow_le (Cutoff.cutoffSampleLaw M).toMeasure
      (hYmeas i) hdelta ha hq hqa (hcut i)).trans ?_
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (le_max_right _ _))
      (le_trans zero_le_one hq)
  have hSmom : ∀ p : ℝ, 1 ≤ p → p ≤ pS →
      (∀ n : ℤ, (∫⁻ omega, ENNReal.ofReal (S n omega) ^ (4 * p)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal CS ^ (4 * p)) ∧
      (∀ n : ℤ, (∫⁻ omega, ENNReal.ofReal (S n omega) ^ (8 * p)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal CS ^ (8 * p)) := by
    intro p hp hpSle
    have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
    have hpl : (0 : ℝ) < p * Real.log 3 := mul_pos hp0 hlog3
    rw [hpSdef, le_div_iff₀ (by positivity : (0 : ℝ) < 16 * Real.log 3)] at hpSle
    exact ⟨hmomq (4 * p) (by linarith only [hp]) (by linarith only [hpSle, hpl]),
      hmomq (8 * p) (by linarith only [hp]) (by linarith only [hpSle])⟩
  have hmom : ∀ i : ℤ,
      (∫⁻ omega, ENNReal.ofReal (S i omega) ^ (1 : ℝ)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal CS ^ (1 : ℝ) :=
    hmomq 1 le_rfl (by linarith only [ha16, hlog3])
  have hconf := ae_isConfinementScale_confinementScale_fullSample M hSmeas
    (le_trans zero_le_one hCS) (le_refl (1 : ℝ)) hL hmom
  exact ⟨hpS1, hpSrange, hSmom, hconf⟩

private theorem earlyExitConfinementModel_rates : earlyExitConfinementModel_rates_statement := by
  classical
  intro d instance1 hdim cstar hcstar gammaT Cev Cfloor Cchain ctail csmall Creg hCchain gammaL gammaR ep hepdef kappa hkappa hkappa1 costBar hcostBardef delta hdelta1 hdelta hdeltaBar jbase htail cbar hcbardef hcbarpos Kbar hKbardef M hcs hgam Kmin
  have hgamT : M.gamma ≤ gammaT :=
    hgam.trans (le_trans (min_le_left _ _) (min_le_left _ _))
  have hgamL : M.gamma ≤ gammaL :=
    hgam.trans (le_trans (min_le_left _ _) (min_le_right _ _))
  have hgamR : M.gamma ≤ gammaR :=
    hgam.trans (le_trans (min_le_right _ _) (min_le_left _ _))
  have hgc : M.gamma ≤ cstar :=
    hgam.trans (le_trans (min_le_right _ _) (min_le_right _ _))
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hgamma4 : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  have hgamma1 : M.gamma < 1 := lt_of_le_of_lt hgamma4 (by norm_num)
  have hi : (0 : ℕ) < d := lt_of_lt_of_le (by norm_num) hdim
  obtain ⟨hwindow, hmain⟩ := htail M hcs hgamT
  have hepIcc : ep ∈ Set.Icc (Cfloor * Real.sqrt M.gamma *
      Real.rpow |Real.log M.gamma| (7 / 2)) (1 / 4) :=
    ⟨hwindow, by rw [hepdef]; exact min_le_left _ _⟩
  have hepsmall : ep ≤ csmall := by rw [hepdef]; exact min_le_right _ _
  -- the smallness of the separation parameter at this model
  have hcostM : earlyExitProfileCost cstar M.gamma ≤ costBar := by
    rw [hcostBardef]
    exact earlyExitProfileCost_le hcstar hgamma (by linarith only [hgamma4])
  have hdeltaSmall : 128 * (3 : ℝ) ^ d * delta *
      earlyExitProfileCost cstar M.gamma ≤ Cchain * kappa := by
    have hnn : (0 : ℝ) ≤ 128 * (3 : ℝ) ^ d * delta := by positivity
    calc 128 * (3 : ℝ) ^ d * delta * earlyExitProfileCost cstar M.gamma
        ≤ 128 * (3 : ℝ) ^ d * delta * costBar := mul_le_mul_of_nonneg_left hcostM hnn
      _ ≤ Cchain * kappa := hdeltaBar
  -- the exponential rate and the confinement constant
  set c : ℝ := earlyExitDecayConstant d M.gamma delta kappa with hcdef
  have hexpnn : (0 : ℝ) ≤ (1 - M.gamma)⁻¹ := by
    rw [inv_nonneg]; linarith only [hgamma1]
  have hexple : (1 - M.gamma)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith only [hgamma1]) (by norm_num)]
    linarith only [hgamma4]
  have hdpos : (0 : ℝ) < delta ^ (1 - M.gamma)⁻¹ := Real.rpow_pos_of_pos hdelta _
  have hcpos : 0 < c := by
    have h3 : (0 : ℝ) < 192 * (3 : ℝ) ^ d := by positivity
    rw [hcdef, earlyExitDecayConstant]
    exact div_pos (mul_pos hkappa hdpos) h3
  have hc1 : c ≤ 1 := by
    have hdle : delta ^ (1 - M.gamma)⁻¹ ≤ 1 :=
      Real.rpow_le_one hdelta.le hdelta1 hexpnn
    have h3d : (1 : ℝ) ≤ (3 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    have hnum : kappa * delta ^ (1 - M.gamma)⁻¹ ≤ 192 * (3 : ℝ) ^ d := by
      nlinarith only [hkappa1, hdle, hkappa, hdpos, h3d]
    rw [hcdef, earlyExitDecayConstant, div_le_one (by positivity)]
    exact hnum
  have hdge : delta ^ (2 : ℕ) ≤ delta ^ (1 - M.gamma)⁻¹ := by
    have hstep := Real.rpow_le_rpow_of_exponent_ge hdelta hdelta1 hexple
    rwa [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hstep
  have hcbarle : cbar ≤ c := by
    have h3 : (0 : ℝ) < 192 * (3 : ℝ) ^ d := by positivity
    have hnum : kappa * delta ^ (2 : ℕ) ≤ kappa * delta ^ (1 - M.gamma)⁻¹ :=
      mul_le_mul_of_nonneg_left hdge hkappa.le
    rw [hcbardef, hcdef, earlyExitDecayConstant, div_le_div_iff₀ h3 h3]
    exact mul_le_mul_of_nonneg_right hnum h3.le
  set K : ℝ :=
    max (max (max 1 (Real.sqrt (100 / c))) (Real.sqrt ((3 : ℝ) ^ jbase))) Kmin with hKdef
  have hK : 1 ≤ K :=
    le_trans (le_max_left (1 : ℝ) (Real.sqrt (100 / c)))
      (le_trans (le_max_left _ _) (le_max_left _ _))
  have hKmin : Kmin ≤ K := le_max_right _ _
  have hK0pos : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have hcK : (100 : ℝ) ≤ c * K ^ (2 : ℕ) := by
    have hsq : Real.sqrt (100 / c) ≤ K :=
      le_trans (le_max_right (1 : ℝ) (Real.sqrt (100 / c)))
        (le_trans (le_max_left _ _) (le_max_left _ _))
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg (100 / c)) hsq 2
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 100 / c), div_le_iff₀ hcpos] at h2
    linarith only [h2]
  have hkK : (3 : ℝ) ^ jbase ≤ K ^ (2 : ℕ) := by
    have h1 : Real.sqrt ((3 : ℝ) ^ jbase) ≤ K :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg ((3 : ℝ) ^ jbase)) h1 2
    rwa [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ jbase)] at h2
  have hKle : K ≤ max Kbar Kmin := by
    have hdivle : 100 / c ≤ 100 / cbar := by
      rw [div_le_div_iff₀ hcpos hcbarpos]
      linarith only [hcbarle]
    have hsqrtle : Real.sqrt (100 / c) ≤ Real.sqrt (100 / cbar) :=
      Real.sqrt_le_sqrt hdivle
    rw [hKdef, hKbardef]
    exact max_le_max (max_le_max (max_le_max (le_refl (1 : ℝ)) hsqrtle)
      (le_refl (Real.sqrt ((3 : ℝ) ^ jbase)))) (le_refl Kmin)
  exact ⟨hgamL, hgamR, hgc, hgamma, hgamma4, hgamma1, hi, hwindow, hmain, hepIcc, hepsmall, hdeltaSmall, hcdef, hexple, hcpos, hc1, hcbarle, hK, hKmin, hcK, hkK, hKle⟩

private theorem earlyExitConfinementModel_comparisonBounds1 :
    ∀ (d : ℕ) (cstar Cfloor Cchain ctail csmall : ℝ) (hCfloor : (0 : ℝ) < Cfloor) (hCchain : (0 : ℝ) < Cchain)
      (hctail : (0 : ℝ) < ctail) (hcsmall : (0 : ℝ) < csmall) (gammaR : ℝ)
      (hgrate :
        ∀ (gamma : ℝ),
          (0 : ℝ) < gamma →
            gamma ≤ gammaR →
              gamma ≤ (1 / 4 : ℝ) → (16 : ℝ) * Real.log (3 : ℝ) ≤ ctail * Cfloor ^ (2 : ℕ) * |Real.log gamma|)
      (hlog3 : (0 : ℝ) < Real.log (3 : ℝ)),
      let ep : ℝ := min (1 / 4 : ℝ) csmall;
      ∀ (heppos : (0 : ℝ) < ep),
        let Cscale : ℝ := max (1 : ℝ) ((16 : ℝ) * Real.log (3 : ℝ) / (ctail * ep ^ (2 : ℕ)));
        let kappa : ℝ := earlyExitKappa Cchain.toNNReal Cchain⁻¹.toNNReal;
        ∀ (hkappa : (0 : ℝ) < kappa),
          let costBar : ℝ := (3 : ℝ) + (3 : ℝ) * (max (1 : ℝ) √cstar * Real.exp (1 / 2 : ℝ));
          let delta : ℝ := min (1 : ℝ) (Cchain * kappa / ((128 : ℝ) * (3 : ℝ) ^ d * costBar));
          ∀ (hdelta1 : delta ≤ (1 : ℝ)) (hdelta : (0 : ℝ) < delta),
            let jbase : ℕ := earlyExitBaseScale d;
            let CSbar : ℝ := max (1 : ℝ) ((2 : ℝ) * delta⁻¹ ^ (2 : ℕ));
            ∀ (hCSbardef : CSbar = max (1 : ℝ) ((2 : ℝ) * delta⁻¹ ^ (2 : ℕ))) (M : ABKModel d) (t Kmin : ℝ)
              (hgamR : M.gamma ≤ gammaR) (hgamma : (0 : ℝ) < M.gamma) (hgamma4 : M.gamma ≤ (1 / 4 : ℝ))
              (hwindow : Cfloor * √M.gamma * |Real.log M.gamma|.rpow (7 / 2 : ℝ) ≤ min (1 / 4 : ℝ) csmall)
              (hexple : ((1 : ℝ) - M.gamma)⁻¹ ≤ (2 : ℝ)),
              let c : ℝ := earlyExitDecayConstant d M.gamma delta kappa;
              let K : ℝ := max (max (max (1 : ℝ) √((100 : ℝ) / c)) √((3 : ℝ) ^ jbase)) Kmin;
              let L : ℝ := K * √|Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t;
              ∀ (hL : (0 : ℝ) < L) (Yfam : (m : ℤ) → Cutoff.CutoffSample d → ℕ) (hYmeas : ∀ (m : ℤ), Measurable (Yfam m))
                (hYtail :
                  ∀ (m : ℤ) (N : ℕ),
                    (1 : ℕ) ≤ N →
                      ((↑(fullSampleLaw M) : Measure (FullSample d M.gamma)) : (a : Set (FullSample d M.gamma)) → ℝ≥0∞)
                          {omegaFull : FullSample d M.gamma | N ≤ Yfam m (↑omegaFull : Cutoff.CutoffSample d)} ≤
                        ENNReal.ofReal
                          (Real.exp (-(ctail * ep ^ (2 : ℕ) * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) * (3 : ℝ) ^ N)))),
                let S : ℤ → Cutoff.CutoffSample d → ℝ := fun (i : ℤ) (omega : Cutoff.CutoffSample d) =>
                  displacementScale delta M.gamma (Yfam i omega);
                (∀ (i : ℤ), Measurable (S i)) ∧
                  (∀ (i : ℤ) (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ S i omega) ∧
                    (1 : ℝ) ≤
                        max (1 : ℝ)
                          (delta ^ (-((1 : ℝ) - M.gamma)⁻¹) *
                            ((1 : ℝ) -
                                Real.exp
                                  (-(ctail * ep ^ (2 : ℕ) * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) / (2 : ℝ))))⁻¹) ∧
                      max (1 : ℝ)
                            (delta ^ (-((1 : ℝ) - M.gamma)⁻¹) *
                              ((1 : ℝ) -
                                  Real.exp
                                    (-(ctail * ep ^ (2 : ℕ) * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) / (2 : ℝ))))⁻¹) ≤
                          CSbar ∧
                        (1 : ℝ) ≤
                            ctail * ep ^ (2 : ℕ) * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) /
                              ((16 : ℝ) * Real.log (3 : ℝ)) ∧
                          Cscale⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) ≤
                              ctail * ep ^ (2 : ℕ) * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) /
                                ((16 : ℝ) * Real.log (3 : ℝ)) ∧
                            (∀ (p : ℝ),
                                (1 : ℝ) ≤ p →
                                  p ≤
                                      ctail * ep ^ (2 : ℕ) * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) /
                                        ((16 : ℝ) * Real.log (3 : ℝ)) →
                                    (∀ (n : ℤ),
                                        ∫⁻ (omega : Cutoff.CutoffSample d),
                                            ENNReal.ofReal (S n omega) ^
                                              ((4 : ℝ) *
                                                p) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) ≤
                                          ENNReal.ofReal
                                              (max (1 : ℝ)
                                                (delta ^ (-((1 : ℝ) - M.gamma)⁻¹) *
                                                  ((1 : ℝ) -
                                                      Real.exp
                                                        (-(ctail * ep ^ (2 : ℕ) * M.gamma⁻¹ *
                                                              |Real.log M.gamma| ^ (-6 : ℤ) /
                                                            (2 : ℝ))))⁻¹)) ^
                                            ((4 : ℝ) * p)) ∧
                                      ∀ (n : ℤ),
                                        ∫⁻ (omega : Cutoff.CutoffSample d),
                                            ENNReal.ofReal (S n omega) ^
                                              ((8 : ℝ) *
                                                p) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) ≤
                                          ENNReal.ofReal
                                              (max (1 : ℝ)
                                                (delta ^ (-((1 : ℝ) - M.gamma)⁻¹) *
                                                  ((1 : ℝ) -
                                                      Real.exp
                                                        (-(ctail * ep ^ (2 : ℕ) * M.gamma⁻¹ *
                                                              |Real.log M.gamma| ^ (-6 : ℤ) /
                                                            (2 : ℝ))))⁻¹)) ^
                                            ((8 : ℝ) * p)) ∧
                              ∀ᵐ (omega : FullSample d M.gamma) ∂(↑(fullSampleLaw M) : Measure (FullSample d M.gamma)),
                                IsConfinementScale
                                  (fun (n : ℤ) =>
                                    widenedScale
                                      (fun (k : ℤ) =>
                                        (fun (i : ℤ) (omega : Cutoff.CutoffSample d) =>
                                            displacementScale
                                              (min (1 : ℝ)
                                                (Cchain * earlyExitKappa Cchain.toNNReal Cchain⁻¹.toNNReal /
                                                  ((128 : ℝ) * (3 : ℝ) ^ d *
                                                    ((3 : ℝ) + (3 : ℝ) * (max (1 : ℝ) √cstar * Real.exp (1 / 2 : ℝ))))))
                                              M.gamma (Yfam i omega))
                                          k (↑omega : Cutoff.CutoffSample d))
                                      n)
                                  (max
                                        (max
                                          (max (1 : ℝ)
                                            √((100 : ℝ) /
                                                earlyExitDecayConstant d M.gamma
                                                  (min (1 : ℝ)
                                                    (Cchain * earlyExitKappa Cchain.toNNReal Cchain⁻¹.toNNReal /
                                                      ((128 : ℝ) * (3 : ℝ) ^ d *
                                                        ((3 : ℝ) + (3 : ℝ) * (max (1 : ℝ) √cstar * Real.exp (1 / 2 : ℝ))))))
                                                  (earlyExitKappa Cchain.toNNReal Cchain⁻¹.toNNReal)))
                                          √((3 : ℝ) ^ earlyExitBaseScale d))
                                        Kmin *
                                      √|Real.log M.gamma| *
                                    intrinsicScale M.nu cstar M.gamma t)
                                  (confinementScale
                                    (fun (i : ℤ) (omega : Cutoff.CutoffSample d) =>
                                      displacementScale
                                        (min (1 : ℝ)
                                          (Cchain * earlyExitKappa Cchain.toNNReal Cchain⁻¹.toNNReal /
                                            ((128 : ℝ) * (3 : ℝ) ^ d *
                                              ((3 : ℝ) + (3 : ℝ) * (max (1 : ℝ) √cstar * Real.exp (1 / 2 : ℝ))))))
                                        M.gamma (Yfam i omega))
                                    (max
                                          (max
                                            (max (1 : ℝ)
                                              √((100 : ℝ) /
                                                  earlyExitDecayConstant d M.gamma
                                                    (min (1 : ℝ)
                                                      (Cchain * earlyExitKappa Cchain.toNNReal Cchain⁻¹.toNNReal /
                                                        ((128 : ℝ) * (3 : ℝ) ^ d *
                                                          ((3 : ℝ) +
                                                            (3 : ℝ) * (max (1 : ℝ) √cstar * Real.exp (1 / 2 : ℝ))))))
                                                    (earlyExitKappa Cchain.toNNReal Cchain⁻¹.toNNReal)))
                                            √((3 : ℝ) ^ earlyExitBaseScale d))
                                          Kmin *
                                        √|Real.log M.gamma| *
                                      intrinsicScale M.nu cstar M.gamma t)
                                    (↑omega : Cutoff.CutoffSample d)) := by
  classical
  intro d cstar Cfloor Cchain ctail csmall hCfloor hCchain hctail hcsmall gammaR hgrate hlog3 ep heppos Cscale kappa hkappa costBar delta hdelta1 hdelta jbase CSbar hCSbardef M t Kmin hgamR hgamma hgamma4 hwindow hexple c K L hL Yfam hYmeas hYtail S
  have hSmeas : ∀ i, Measurable (S i) := fun i =>
    measurable_displacementScale (hYmeas i) delta M.gamma
  have hSnn : ∀ (i : ℤ) (omega : Cutoff.CutoffSample d), 0 ≤ S i omega := fun i omega =>
    (displacementScale_pos hdelta M.gamma (Yfam i omega)).le
  set a : ℝ := ctail * ep ^ (2 : ℕ) * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) with hadef
  have ha16 : 16 * Real.log 3 ≤ a := by
    rw [hadef]
    exact le_percolationRate hctail hCfloor hgamma hgamma4 hwindow
      (hgrate M.gamma hgamma hgamR hgamma4)
  have ha : 0 < a := lt_of_lt_of_le (by linarith only [hlog3]) ha16
  have hexpa : Real.exp (-(a / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith only [ha]
  have hexppos : (0 : ℝ) < 1 - Real.exp (-(a / 2)) := by linarith only [hexpa]
  set Cmom : ℝ := delta ^ (-(1 - M.gamma)⁻¹) * (1 - Real.exp (-(a / 2)))⁻¹ with hCmomdef
  set CS : ℝ := max 1 Cmom with hCSdef
  have hCS : (1 : ℝ) ≤ CS := le_max_left _ _
  have hCSle : CS ≤ CSbar := by
    have hdinv : (1 : ℝ) ≤ delta⁻¹ := (one_le_inv₀ hdelta).mpr hdelta1
    have hdrw : delta ^ (-(1 - M.gamma)⁻¹) = (delta⁻¹) ^ (1 - M.gamma)⁻¹ := by
      rw [Real.rpow_neg hdelta.le, ← Real.inv_rpow hdelta.le]
    have hd2 : (delta⁻¹) ^ (1 - M.gamma)⁻¹ ≤ (delta⁻¹) ^ (2 : ℕ) := by
      have hstep := Real.rpow_le_rpow_of_exponent_le hdinv hexple
      rwa [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hstep
    have hlog2 : Real.log 2 ≤ 8 * Real.log 3 := by
      have h23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
      linarith only [h23, hlog3]
    have hea : Real.exp (-(a / 2)) ≤ 1 / 2 := by
      have hle : -(a / 2) ≤ -Real.log 2 := by linarith only [ha16, hlog2]
      calc Real.exp (-(a / 2)) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 hle
        _ = (2 : ℝ)⁻¹ := by rw [Real.exp_neg, Real.exp_log (by norm_num)]
        _ = 1 / 2 := by norm_num
    have hinv2 : (1 - Real.exp (-(a / 2)))⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hexppos (by norm_num)]
      linarith only [hea]
    have hCmomle : Cmom ≤ 2 * (delta⁻¹) ^ (2 : ℕ) := by
      have hA : delta ^ (-(1 - M.gamma)⁻¹) ≤ (delta⁻¹) ^ (2 : ℕ) := by
        rw [hdrw]; exact hd2
      have hAnn : (0 : ℝ) ≤ delta ^ (-(1 - M.gamma)⁻¹) :=
        (Real.rpow_pos_of_pos hdelta _).le
      have hBnn : (0 : ℝ) ≤ (1 - Real.exp (-(a / 2)))⁻¹ := by positivity
      have hDnn : (0 : ℝ) ≤ (delta⁻¹) ^ (2 : ℕ) := by positivity
      rw [hCmomdef]
      calc delta ^ (-(1 - M.gamma)⁻¹) * (1 - Real.exp (-(a / 2)))⁻¹
          ≤ (delta⁻¹) ^ (2 : ℕ) * 2 := mul_le_mul hA hinv2 hBnn hDnn
        _ = 2 * (delta⁻¹) ^ (2 : ℕ) := by ring
    rw [hCSdef, hCSbardef]
    exact max_le_max (le_refl (1 : ℝ)) hCmomle
  set pS : ℝ := a / (16 * Real.log 3) with hpSdef
  obtain ⟨stage_hpS1, stage_hpSrange, stage_hSmom, stage_hconf⟩ :=
    @earlyExitConfinementModel_momentBounds1 (d) (cstar) (Cchain) (ctail) (csmall) (hctail) (hcsmall) (hlog3) (heppos) (hdelta) (M) (t) (Kmin) (hgamma) (hL) (Yfam) (hYmeas) (hSmeas) (hYtail) (hadef) (ha16) (ha) (hCS) (hpSdef)
  have hpS1 : (1 : ℝ) ≤ pS := stage_hpS1
  have hpSrange : Cscale⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) ≤ pS := stage_hpSrange
  have hSmom : ∀ p : ℝ, 1 ≤ p → p ≤ pS →
      (∀ n : ℤ, (∫⁻ omega, ENNReal.ofReal (S n omega) ^ (4 * p)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal CS ^ (4 * p)) ∧
      (∀ n : ℤ, (∫⁻ omega, ENNReal.ofReal (S n omega) ^ (8 * p)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal CS ^ (8 * p)) := stage_hSmom
  have hconf := stage_hconf
  exact ⟨hSmeas, hSnn, hCS, hCSle, hpS1, hpSrange, hSmom, hconf⟩

/-- **The early-exit tail of the stream process at and above the random confinement scale,
with uniform constants.**  The displacement scales of the crossing scales of the percolation
estimate determine a confinement scale, and at every scale above it each condition of the
chained early-exit estimate is met: the accuracy lies in the window, which the model form
shows nonempty; the crossing-scale condition and the lower bound on the scale gap come from
the defining inequality of the confinement scale through the auxiliary-scale comparison; the
auxiliary scale is the triadic scale straddling the quantity the estimate names; the
comparison of the two time scales is a theorem about the model; and the separation parameter
is chosen below the smallness threshold.

The returned exponential rate `c` and confinement constant `K` satisfy `100 ≤ c K²`, which
is what turns the tail into the bound `γ^{100}` at the confinement scale itself.  Every
requirement on `K` in the argument is a lower bound, so an arbitrary threshold `Kmin` may be
imposed on it at no cost; the returned `K` is above it.

The separation parameter is chosen against a bound for the profile cost that holds at every
admissible disorder, so it does not depend on the model; this is what makes the four
constants below uniform.  Three of them are returned before the model and the time:

* `Cscale`, with `Cscale⁻¹ γ^{-1} |log γ|^{-6} ≤ pS`, so that a caller whose range of
  exponents is prescribed in that shape can meet `p ≤ pS`.  The statement does not identify
  `pS`; it identifies a lower bound for it, which is all a caller consumes.
* `CSbar`, with `CS ≤ CSbar`, and `Kbar`, with `K ≤ max Kbar Kmin`.  A constant built from
  `CS` and `K` and increasing in both — the component constant of the annealed bound is one —
  can therefore be fixed before the model.
* `cbar`, with `0 < cbar ≤ c` and `cbar ≤ 1`: the exponential rate is bounded below by
  `κ δ² / (192 · 3^d)`, because `δ ≤ 1` and the exponent `1/(1-γ)` is at most `2`.  A caller
  that must fix the rate before the model can use `cbar` and weaken the tail to it.

The accuracy is taken at the top of its window rather than at the floor, so the rate of the
crossing tail is `c_tail ep² γ^{-1} |log γ|^{-6}` at a value of `ep` that does not shrink
with the disorder.  Integrating that tail bounds the moments of the displacement scales of
order at most `8 pS` by one constant `CS ≥ 1`, uniformly in the order and in the scale. -/
theorem exists_ae_confinement_exitTime_bound_of_threshold
    (d : ℕ) [NeZero d] (hdim : 2 ≤ d) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 Cscale CSbar Kbar cbar : ℝ,
      0 < gamma0 ∧ 1 ≤ Cscale ∧ 1 ≤ CSbar ∧ 1 ≤ Kbar ∧ 0 < cbar ∧ cbar ≤ 1 ∧
      gamma0 ≤ cstar ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ t : ℝ, 0 < t → ∀ Kmin : ℝ,
        ∃ (S : ℤ → Cutoff.CutoffSample d → ℝ) (K L c CS pS : ℝ),
          1 ≤ K ∧ Kmin ≤ K ∧ 0 < c ∧ c ≤ 1 ∧ cbar ≤ c ∧
          (100 : ℝ) ≤ c * K ^ (2 : ℕ) ∧
          L = K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t ∧
          (∃ (delta : ℝ) (Y : ℤ → Cutoff.CutoffSample d → ℕ),
            0 < delta ∧ delta ≤ 1 ∧ (∀ i : ℤ, Measurable (Y i)) ∧
            ∀ (i : ℤ) (omega : Cutoff.CutoffSample d),
              S i omega = displacementScale delta M.gamma (Y i omega)) ∧
          (∀ n : ℤ, Measurable (S n)) ∧ (∀ (n : ℤ) (omega : Cutoff.CutoffSample d),
            0 ≤ S n omega) ∧
          1 ≤ CS ∧ 1 ≤ pS ∧ CS ≤ CSbar ∧ K ≤ max Kbar Kmin ∧
          Cscale⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) ≤ pS ∧
          (∀ p : ℝ, 1 ≤ p → p ≤ pS →
            (∀ n : ℤ, (∫⁻ omega, ENNReal.ofReal (S n omega) ^ (4 * p)
                ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal CS ^ (4 * p)) ∧
            (∀ n : ℤ, (∫⁻ omega, ENNReal.ofReal (S n omega) ^ (8 * p)
                ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal CS ^ (8 * p))) ∧
          (∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
            IsConfinementScale (fun n => widenedScale (fun k => S k omega.1) n) L
              (confinementScale S L omega.1)) ∧
          ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
            letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
            letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
            ∀ k : ℤ, confinementScale S L omega.1 ≤ k →
              (streamExhaustionTailInput M omega).wholeSpaceProcess
                  ((0 : Vec d) : OnePoint (Vec d))
                  {eta | ContinuousPath.exitTime
                    (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) k) eta ≤
                      (t.toNNReal : ℝ≥0∞)} ≤
                ENNReal.ofReal (Real.exp (-c *
                  displacementMinScale M.nu cstar M.gamma t k)) := by
  classical
  obtain ⟨gammaT, Cev, Cfloor, Cchain, ctail, csmall, Creg,
    hgammaT, hCev, hCfloor, hCchain, hctail, hcsmall, hCreg, htail⟩ :=
    measure_exitTime_le_exp_neg_displacementMinScale_streamProcess_v2_of_model d hdim cstar
      hcstar
  obtain ⟨gammaL, hgammaL, hlen⟩ := exists_lengthTimeScale_conversions d cstar hcstar
  obtain ⟨gammaR, hgammaR, hgrate⟩ :=
    exists_gamma_rate_threshold hctail hCfloor (16 * Real.log 3)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  -- the accuracy, at the top of the window
  set ep : ℝ := min (1 / 4 : ℝ) csmall with hepdef
  have heppos : 0 < ep := by rw [hepdef]; exact lt_min (by norm_num) hcsmall
  -- the constant of the exponent range
  set Cscale : ℝ := max 1 (16 * Real.log 3 / (ctail * ep ^ (2 : ℕ))) with hCscaledef
  have hCscale1 : (1 : ℝ) ≤ Cscale := le_max_left _ _
  -- the separation parameter, chosen against a model-free bound for the profile cost
  set kappa : ℝ := earlyExitKappa (Real.toNNReal Cchain) (Real.toNNReal Cchain⁻¹) with hkdef
  have hkappa : 0 < kappa :=
    earlyExitKappa_pos (Real.toNNReal_pos.mpr hCchain)
      (Real.toNNReal_pos.mpr (inv_pos.mpr hCchain))
  have hkappa1 : kappa ≤ 1 := by
    rw [hkdef, earlyExitKappa]
    have hnn : (0 : ℝ) ≤ (oneStepLaplaceContraction (Real.toNNReal Cchain)
        (Real.toNNReal Cchain⁻¹)).toReal := ENNReal.toReal_nonneg
    linarith only [hnn]
  set costBar : ℝ := 3 + 3 * (max 1 (Real.sqrt cstar) * Real.exp (1 / 2)) with hcostBardef
  have hcostBar : 0 < costBar := by
    have h1 : (1 : ℝ) ≤ max 1 (Real.sqrt cstar) := le_max_left _ _
    have h2 : (0 : ℝ) < Real.exp (1 / 2) := Real.exp_pos _
    rw [hcostBardef]
    nlinarith only [h1, h2]
  have hBpos : (0 : ℝ) < 128 * (3 : ℝ) ^ d * costBar := by positivity
  set delta : ℝ := min 1 (Cchain * kappa / (128 * (3 : ℝ) ^ d * costBar)) with hddef
  have hdelta1 : delta ≤ 1 := min_le_left _ _
  have hdelta : 0 < delta := by
    rw [hddef]
    exact lt_min zero_lt_one (div_pos (mul_pos hCchain hkappa) hBpos)
  have hdeltaBar : 128 * (3 : ℝ) ^ d * delta * costBar ≤ Cchain * kappa := by
    have hle : delta ≤ Cchain * kappa / (128 * (3 : ℝ) ^ d * costBar) := by
      rw [hddef]; exact min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_left hle hBpos.le
    rw [mul_div_cancel₀ _ hBpos.ne'] at hmul
    calc 128 * (3 : ℝ) ^ d * delta * costBar
        = (128 * (3 : ℝ) ^ d * costBar) * delta := by ring
      _ ≤ Cchain * kappa := hmul
  set jbase : ℕ := earlyExitBaseScale d with hjbasedef
  have hk3 : earlyExitBaseScale d ≤ 3 ^ jbase := by
    rw [hjbasedef]
    exact (Nat.lt_pow_self (by norm_num)).le
  -- the two uniform bounds
  set CSbar : ℝ := max 1 (2 * (delta⁻¹) ^ (2 : ℕ)) with hCSbardef
  have hCSbar1 : (1 : ℝ) ≤ CSbar := le_max_left _ _
  set cbar : ℝ := kappa * delta ^ (2 : ℕ) / (192 * (3 : ℝ) ^ d) with hcbardef
  have hcbarpos : 0 < cbar := by
    rw [hcbardef]
    exact div_pos (mul_pos hkappa (pow_pos hdelta 2)) (by positivity)
  have hcbar1 : cbar ≤ 1 := by
    have h3d : (1 : ℝ) ≤ (3 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    have hd2 : delta ^ (2 : ℕ) ≤ 1 := pow_le_one₀ hdelta.le hdelta1
    have hd2pos : (0 : ℝ) < delta ^ (2 : ℕ) := pow_pos hdelta 2
    rw [hcbardef, div_le_one (by positivity)]
    nlinarith only [hkappa1, hd2, hkappa, h3d, hd2pos]
  set Kbar : ℝ :=
    max (max 1 (Real.sqrt (100 / cbar))) (Real.sqrt ((3 : ℝ) ^ jbase)) with hKbardef
  have hKbar1 : (1 : ℝ) ≤ Kbar := le_trans (le_max_left _ _) (le_max_left _ _)
  refine ⟨min (min gammaT gammaL) (min gammaR cstar), Cscale, CSbar, Kbar, cbar,
    lt_min (lt_min hgammaT hgammaL) (lt_min hgammaR hcstar), hCscale1, hCSbar1, hKbar1,
    hcbarpos, hcbar1, le_trans (min_le_right _ _) (min_le_right _ _), ?_⟩
  intro M hcs hgam t ht Kmin
  obtain ⟨hgamL, hgamR, hgc, hgamma, hgamma4, hgamma1, hi, hwindow, hmain, hepIcc, hepsmall, hdeltaSmall, hcdef, hexple, hcpos, hc1, hcbarle, hK, hKmin, hcK, hkK, hKle⟩ :=
    @earlyExitConfinementModel_rates (d) (by infer_instance) (hdim) (cstar) (hcstar) (gammaT) (Cev) (Cfloor) (Cchain) (ctail) (csmall) (Creg) (hCchain) (gammaL) (gammaR) (hepdef) (hkappa) (hkappa1) (hcostBardef) (hdelta1) (hdelta) (hdeltaBar) (htail) (hcbardef) (hcbarpos) (hKbardef) (M) (hcs) (hgam) (Kmin)
  set c : ℝ := earlyExitDecayConstant d M.gamma delta kappa with hcdef
  set K : ℝ :=
    max (max (max 1 (Real.sqrt (100 / c))) (Real.sqrt ((3 : ℝ) ^ jbase))) Kmin with hKdef
  have hR : 0 < intrinsicScale M.nu cstar M.gamma t :=
    intrinsicScale_pos M.nu_pos hcstar hgamma ht
  have hs1 : 1 ≤ Real.sqrt |Real.log M.gamma| := one_le_sqrt_abs_log hgamma hgamma4
  have hs0 : (0 : ℝ) < Real.sqrt |Real.log M.gamma| := lt_of_lt_of_le zero_lt_one hs1
  set L : ℝ := K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t
    with hLdef
  have hL : 0 < L := by rw [hLdef]; positivity
  -- the crossing scales, and the displacement scales they define
  choose Yfam hYmeas hYtail hYcross using hmain ep hepIcc hepsmall
  set S : ℤ → Cutoff.CutoffSample d → ℝ :=
    fun i omega => displacementScale delta M.gamma (Yfam i omega) with hSdef
  obtain ⟨hSmeas, hSnn, hCS, hCSle, hpS1, hpSrange, hSmom, hconf⟩ :=
    @earlyExitConfinementModel_comparisonBounds1 (d) (cstar) (Cfloor) (Cchain) (ctail) (csmall) (hCfloor) (hCchain) (hctail) (hcsmall) (gammaR) (hgrate) (hlog3) (heppos) (hkappa) (hdelta1) (hdelta) (hCSbardef) (M) (t) (Kmin) (hgamR) (hgamma) (hgamma4) (hwindow) (hexple) (hL) (Yfam) (hYmeas) (hYtail)
  set a : ℝ := ctail * ep ^ (2 : ℕ) * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) with hadef
  set Cmom : ℝ := delta ^ (-(1 - M.gamma)⁻¹) * (1 - Real.exp (-(a / 2)))⁻¹ with hCmomdef
  set CS : ℝ := max 1 Cmom with hCSdef
  set pS : ℝ := a / (16 * Real.log 3) with hpSdef
  refine ⟨S, K, L, c, CS, pS, hK, hKmin, hcpos, hc1, hcbarle, hcK, hLdef,
    ⟨delta, Yfam, hdelta, hdelta1, hYmeas, fun i omega => rfl⟩, hSmeas, hSnn, hCS, hpS1,
    hCSle, hKle, hpSrange, hSmom, hconf, ?_⟩
  filter_upwards [hconf, MeasureTheory.ae_all_iff.2 hYcross] with omega hmconf hmcross
  let _ := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
  let _ := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
  set m : ℤ := confinementScale S L omega.1 with hmdef
  set tN : NNReal := t.toNNReal with htNdef
  have htN : (tN : ℝ) = t := Real.coe_toNNReal t ht.le
  have htpos : 0 < (tN : ℝ) := by rw [htN]; exact ht
  have hmconf' : IsConfinementScale
      (fun i => widenedScale (fun l => displacementScale delta M.gamma (Yfam l omega.1)) i)
      (K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t) m := by
    rw [← hLdef]
    exact hmconf
  intro r hr
  -- the auxiliary scale at `r`
  obtain ⟨n, hnL, hnU⟩ := exists_auxiliaryScale
    (auxiliaryScaleBound_pos (nu := M.nu) (cstar := cstar) (gamma := M.gamma)
      (delta := delta) (t := t) M.nu_pos hdelta ht r)
  -- the crossing-scale condition and the lower bound on the scale gap
  have hdisp : displacementScale delta M.gamma (Yfam r omega.1 + jbase) ≤
      displacementMinScale M.nu cstar M.gamma t r :=
    displacementScale_add_le_displacementMinScale_of_isConfinementScale M.nu_pos hcstar
      hgamma hgamma4 hgc hdelta ht hK hkK hmconf' hr
  have hsub : n ≤ r - ((Yfam r omega.1 + jbase : ℕ) : ℤ) :=
    auxiliaryScale_le_sub_of_displacementScale_le M.nu_pos ht hdelta hdelta1 hcstar hgamma
      hgamma1 hnL hdisp
  push_cast at hsub
  have hnsub : n ≤ r - (Yfam r omega.1 : ℤ) := by omega
  have hjle : jbase ≤ (r - n).toNat := by omega
  have hlarge : earlyExitBaseScale d ≤ 3 ^ (r - n).toNat :=
    hk3.trans (Nat.pow_le_pow_right (by norm_num) hjle)
  -- the remaining conditions of the chained estimate
  have hnL' : (3 : ℝ) ^ n ≤
      auxiliaryScaleBound M.nu (Disorder.cstar M) M.gamma delta ((tN : ℝ)) r := by
    rw [hcs, htN]; exact hnL
  have hnU' : auxiliaryScaleBound M.nu (Disorder.cstar M) M.gamma delta ((tN : ℝ)) r <
      (3 : ℝ) ^ (n + 1) := by
    rw [hcs, htN]; exact hnU
  have hscale' : lengthTimeScale M.nu (Disorder.cstar M) M.gamma ((3 : ℝ) ^ n) ≤
      2 * exitTimeScale M n := by
    rw [hcs]; exact (hlen M hcs hgamL n).2.1
  have hdeltaSmall' : 128 * (3 : ℝ) ^ d * delta *
      earlyExitProfileCost (Disorder.cstar M) M.gamma ≤
      Cchain * earlyExitKappa (Real.toNNReal Cchain) (Real.toNNReal Cchain⁻¹) := by
    rw [hcs, ← hkdef]; exact hdeltaSmall
  set Good : Section5.Percolation.Site d → Prop :=
    fun z => omega.1 ∈ qEvent M Creg Cev n (rescaledLatticePoint n z) ep with hGooddef
  let instGood : DecidablePred Good := Classical.decPred Good
  have hGood : ∀ z, Good z ↔ omega.1 ∈ qEvent M Creg Cev n
      (rescaledLatticePoint n z) ep := fun z => Iff.rfl
  have hx : (0 : Vec d) ∈ Metric.closedBall (0 : Vec d) ((1 / 2 : ℝ) * (3 : ℝ) ^ (r - 1)) :=
    Metric.mem_closedBall_self (by positivity)
  have hinst := hmcross r n hnsub ⟨0, hi⟩ Good hGood delta hdelta hdelta1 tN htpos hnL' hnU'
    hscale' hdeltaSmall' hlarge (0 : Vec d) hx
  rw [hcs, htN, ← hcdef] at hinst
  rw [cubeSetAt_zero_eq_originCube]
  exact hinst

/-! ## 4. The early-exit probability at the confinement scale -/

/-- **The early-exit probability at the confinement scale, from the tail at that scale.**
The exit-time tail of the stream process read at the random confinement scale, together with
the confinement inequality, bounds the probability that the process started at the origin
has left `□_{m_t}` by time `t` by `γ^{100}`.

The tail is carried as the named hypothesis `hexitTail`, in the form the chained estimate
produces at the confinement scale: at the exponential rate `c` and the two-branch
displacement minimum, on the cube at the origin.  The only requirement on the constant `K`
of the deterministic factor is `100 ≤ c K²`. -/
theorem measureReal_compl_survivalEvent_confinementScale_le_pow_of_exitTail_at_confinementScale
    (M : ABKModel d) {cstar t K L c : ℝ} (S : ℤ → Cutoff.CutoffSample d → ℝ)
    (hcstar : 0 < cstar) (hgc : M.gamma ≤ cstar) (ht : 0 < t) (hK : 1 ≤ K) (hc : 0 ≤ c)
    (hcK : (100 : ℝ) ≤ c * K ^ (2 : ℕ))
    (hKL : K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t ≤ L)
    (hconf : ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
      IsConfinementScale (fun n => widenedScale (fun i => S i omega.1) n) L
        (confinementScale S L omega.1))
    (hexitTail : ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
      (streamExhaustionTailInput M omega).wholeSpaceProcess ((0 : Vec d) : OnePoint (Vec d))
          {eta | ContinuousPath.exitTime
            (((↑) : Vec d → OnePoint (Vec d)) ''
              cubeSetAt (0 : Vec d) (confinementScale S L omega.1)) eta ≤
              (t.toNNReal : ℝ≥0∞)} ≤
        ENNReal.ofReal (Real.exp (-c * displacementMinScale M.nu cstar M.gamma t
          (confinementScale S L omega.1)))) :
    ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
      ((streamExhaustionTailInput M omega).wholeSpaceProcess
          ((0 : Vec d) : OnePoint (Vec d))
        (survivalEvent (((↑) : Vec d → OnePoint (Vec d)) ''
          cubeSetAt (0 : Vec d) (confinementScale S L omega.1))
          t.toNNReal)ᶜ).toReal ≤ M.gamma ^ (100 : ℕ) := by
  filter_upwards [hconf, hexitTail] with omega hmconf hmexit
  let _ := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
  let _ := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
  have hexp := exp_neg_mul_displacementMinScale_le_pow_of_isConfinementScale
    M.nu_pos hcstar M.shellPrefix.gamma_pos M.shellPrefix.gamma_le_quarter hgc ht hK hc
    hcK hKL hmconf
  have hset := compl_survivalEvent_eq (((↑) : Vec d → OnePoint (Vec d)) ''
    cubeSetAt (0 : Vec d) (confinementScale S L omega.1)) t.toNNReal
  refine le_of_eq_of_le (congrArg (fun s ↦ (((streamExhaustionTailInput M omega
    ).wholeSpaceProcess ((0 : Vec d) : OnePoint (Vec d))) s).toReal) hset) ?_
  calc ((streamExhaustionTailInput M omega).wholeSpaceProcess
        ((0 : Vec d) : OnePoint (Vec d))
          {eta | ContinuousPath.exitTime
            (((↑) : Vec d → OnePoint (Vec d)) ''
              cubeSetAt (0 : Vec d) (confinementScale S L omega.1)) eta ≤
              (t.toNNReal : ℝ≥0∞)}).toReal ≤
      (ENNReal.ofReal (Real.exp (-c * displacementMinScale M.nu cstar M.gamma t
        (confinementScale S L omega.1)))).toReal :=
        ENNReal.toReal_mono (by finiteness) hmexit
    _ = Real.exp (-c * displacementMinScale M.nu cstar M.gamma t
        (confinementScale S L omega.1)) := ENNReal.toReal_ofReal (Real.exp_nonneg _)
    _ ≤ M.gamma ^ (100 : ℕ) := hexp

end

end Algsuperdiff.Section5.Provider
