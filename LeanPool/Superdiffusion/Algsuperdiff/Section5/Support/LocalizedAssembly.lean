/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.BallAverageRepresentative
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.DataApproximation
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.LocalizedGaugeMeasurable

/-!
# LocalizedAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The localized quantities are measurable functions of the sample

The two localized quantities of Section 5.1 are suprema over the whole
normalized forcing class, which is not countable, of quantities attached to
almost-everywhere classes of Sobolev functions.  They are nevertheless
measurable, with no regularity hypothesis at all.

Both inner quantities are countable suprema of ball averages: the `L^∞` norm of
a difference by the essential-supremum identification, and the Hölder seminorm
of the continuous representative by the identification that also reads `⊤` where
no continuous representative exists.  A ball average of the solution is a
measurable function of the sample, and it is continuous in the forcing field —
by the energy estimate, the zero-trace Poincaré inequality and Cauchy-Schwarz,
none of which sees any regularity — so each inner quantity is lower
semicontinuous in the datum and its supremum over the normalized class is
attained on the countable subclass that approximates that class uniformly.

## Main results

* `measurable_localizedRegularity`, `measurable_localizedError` — unconditional.
* `measurable_percolationScaleTotal` — the resulting measurability of the
  percolation scale.

## References

* ABK26, the localized error and regularity quantities and the chains of good
  cubes of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The inner quantities as ball-average gauges -/

theorem integrableOn_h1Function {y : Vec d} {n : ℤ} (u : H1Function (cubeSetAt y n)) :
    IntegrableOn u.toFun (cubeSetAt y n) volume := by
  have : IsFiniteMeasure (volumeMeasureOn (cubeSetAt y n)) :=
    (isOpenBoundedConvexDomain_cubeSetAt y n).isFiniteMeasure_restrict_volume
  exact u.memL2.integrable one_le_two

/-- **The infimum over the continuous representatives is the ball-average Hölder
gauge**, including the value `⊤` where no continuous representative exists. -/
theorem iInf_isCubeRepresentative_eq_ballAverageHolderOn [NeZero d] {y : Vec d} {n : ℤ}
    {D : Set (Vec d)} (hD : Dense D) (u : H1Function (cubeSetAt y n)) {c : ℝ≥0∞}
    (hc : c ≠ 0) :
    (⨅ uRep : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y n u uRep,
        c * holderSeminormOn (cubeSetAt y n) (1 / 2) uRep) =
      c * ballAverageHolderOn (cubeSetAt y n) D u.toFun := by
  have hInt : IntegrableOn u.toFun (cubeSetAt y n) volume := integrableOn_h1Function u
  by_cases hex : ∃ r : Vec d → ℝ, IsCubeRepresentative y n u r
  · obtain ⟨r, hr⟩ := hex
    rw [iInf_isCubeRepresentative_holderSeminormOn hr c,
      ballAverageHolderOn_eq_holderSeminormOn (isOpen_cubeSetAt y n) hD hInt hr.1 hr.2]
  · have hinf : (⨅ uRep : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y n u uRep,
        c * holderSeminormOn (cubeSetAt y n) (1 / 2) uRep) = ⊤ :=
      le_antisymm le_top (le_iInf fun r => le_iInf fun hr => absurd ⟨r, hr⟩ hex)
    have htop : ballAverageHolderOn (cubeSetAt y n) D u.toFun = ⊤ := by
      by_contra hcon
      obtain ⟨g, hae, hg⟩ := exists_continuousOn_of_ballAverageHolderOn_lt_top
        (isOpen_cubeSetAt y n) hD hInt (lt_top_iff_ne_top.2 hcon)
      exact hex ⟨g, hae, hg⟩
    rw [hinf, htop, ENNReal.mul_top hc]

/-- **The `L^∞` norm of the difference of two solutions is the ball-average
supremum gauge.** -/
theorem eLpNorm_top_sub_eq_ballAverageSupNormOn [NeZero d] {y : Vec d} {n : ℤ}
    {D : Set (Vec d)} (hD : Dense D) (u v : H1Function (cubeSetAt y n)) :
    eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict (cubeSetAt y n)) =
      ballAverageSupNormOn (cubeSetAt y n) D fun x => u.toFun x - v.toFun x :=
  eLpNorm_top_restrict_eq_ballAverageSupNormOn (isOpen_cubeSetAt y n) hD
    ((integrableOn_h1Function u).sub (integrableOn_h1Function v))

/-! ## 2. The localized regularity -/

/-- **The localized regularity is a measurable function of the sample.** -/
theorem measurable_localizedRegularity (M : ABKModel d) (n : ℤ) (y : Vec d) :
    Measurable (localizedRegularity M n y) := by
  have : NeZero d := Provider.Orlicz.neZero_of_model M
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Vec d)
  have hKn : (0 : ℝ) < Real.rpow 3 (-(n : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := Provider.Orlicz.sigmaBar_pos M n
  have hcX : ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact mul_pos hsig hKn
  obtain ⟨t, htc, htmem, htapprox⟩ := exists_countable_normalizedForceAt_approx y n
  have := htc.to_subtype
  have hGn : ∀ G : ↥t, HolderSeminormBoundOn (cubeSetAt y n) (1 / 2)
      (Real.rpow 3 (-(n : ℝ) / 2)) (extendVec y n (G : C(closedCubeAt y n, Vec d))) :=
    fun G => htmem _ G.2
  have hGL2 : ∀ G : ↥t,
      MemVectorL2 (cubeSetAt y n) (extendVec y n (G : C(closedCubeAt y n, Vec d))) :=
    fun G => memVectorL2_of_holderSeminormBoundOn_cubeSetAt hKn.le (by norm_num) (hGn G)
  have hEq : localizedRegularity M n y = fun omega =>
      ⨆ G : ↥t, ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
        ballAverageHolderOn (cubeSetAt y n) D (solutionAt M n n y omega (hGn G)).toFun := by
    funext omega
    refine le_antisymm ?_ ?_
    · refine localizedRegularity_le_iff.2 fun g hg u hu => ?_
      rw [iInf_isCubeRepresentative_eq_ballAverageHolderOn hDd u hcX]
      have hgL2 : MemVectorL2 (cubeSetAt y n) g :=
        memVectorL2_of_holderSeminormBoundOn_cubeSetAt hKn.le (by norm_num)
          (normalizedForceAt_def.1 hg)
      obtain ⟨Lam, hEll⟩ := exists_isEllipticFieldOn_cutoff M n n y omega
      have hkey : ballAverageHolderOn (cubeSetAt y n) D u.toFun ≤
          ⨆ G : ↥t, ballAverageHolderOn (cubeSetAt y n) D
            (solutionAt M n n y omega (hGn G)).toFun := by
        refine iSup_le fun x => iSup_le fun hxD => iSup_le fun z => iSup_le fun hzD =>
          iSup_le fun hne => iSup_le fun k => iSup_le fun hbx => iSup_le fun hbz => ?_
        refine ENNReal.le_of_forall_pos_le_add fun epsn hepsn _ => ?_
        have hNpos : (0 : ℝ) < ‖x - z‖ ^ (1 / 2 : ℝ) :=
          Real.rpow_pos_of_pos (by rw [norm_pos_iff]; exact sub_ne_zero.2 hne) _
        have hepsnR : (0 : ℝ) < (epsn : ℝ) := NNReal.coe_pos.2 hepsn
        have heps : (0 : ℝ) < (epsn : ℝ) * ‖x - z‖ ^ (1 / 2 : ℝ) / 2 := by
          have := mul_pos hepsnR hNpos
          linarith
        have hrpos : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
        obtain ⟨eta1, he1, hc1⟩ :=
          exists_eta_abs_setAverage_ball_sub_le hEll hrpos hbx heps
        obtain ⟨eta2, he2, hc2⟩ :=
          exists_eta_abs_setAverage_ball_sub_le hEll hrpos hbz heps
        obtain ⟨G0, hG0t, hG0close⟩ := htapprox g hg (min eta1 eta2) (lt_min he1 he2)
        obtain ⟨G, hGclose⟩ : ∃ G : ↥t, ∀ w ∈ cubeSetAt y n,
            ‖g w - extendVec y n (G : C(closedCubeAt y n, Vec d)) w‖ ≤ min eta1 eta2 :=
          ⟨⟨G0, hG0t⟩, hG0close⟩
        have hsol := isDirichletSolutionAt_solutionAt M n n y omega (hGn G)
        have hb1 := hc1 g (extendVec y n (G : C(closedCubeAt y n, Vec d))) hgL2 (hGL2 G)
          (fun w hw => (hGclose w hw).trans (min_le_left _ _)) u
          (solutionAt M n n y omega (hGn G)) hu hsol
        have hb2 := hc2 g (extendVec y n (G : C(closedCubeAt y n, Vec d))) hgL2 (hGL2 G)
          (fun w hw => (hGclose w hw).trans (min_le_right _ _)) u
          (solutionAt M n n y omega (hGn G)) hu hsol
        set Ax : ℝ := ⨍ w in Metric.ball x (1 / (k + 1 : ℝ)), u.toFun w ∂volume with hAxdef
        set Az : ℝ := ⨍ w in Metric.ball z (1 / (k + 1 : ℝ)), u.toFun w ∂volume with hAzdef
        set Bx : ℝ := ⨍ w in Metric.ball x (1 / (k + 1 : ℝ)),
          (solutionAt M n n y omega (hGn G)).toFun w ∂volume with hBxdef
        set Bz : ℝ := ⨍ w in Metric.ball z (1 / (k + 1 : ℝ)),
          (solutionAt M n n y omega (hGn G)).toFun w ∂volume with hBzdef
        have hbound : |Ax - Az| ≤ |Bx - Bz| + (epsn : ℝ) * ‖x - z‖ ^ (1 / 2 : ℝ) := by
          have hrw : Ax - Az = (Bx - Bz) + ((Ax - Bx) - (Az - Bz)) := by ring
          have h1 : |(Bx - Bz) + ((Ax - Bx) - (Az - Bz))| ≤
              |Bx - Bz| + |(Ax - Bx) - (Az - Bz)| := by
            simpa [Real.norm_eq_abs] using norm_add_le (Bx - Bz) ((Ax - Bx) - (Az - Bz))
          have h2 : |(Ax - Bx) - (Az - Bz)| ≤ |Ax - Bx| + |Az - Bz| := by
            simpa [Real.norm_eq_abs] using norm_sub_le (Ax - Bx) (Az - Bz)
          rw [hrw]
          linarith [hb1, hb2]
        calc ENNReal.ofReal (|Ax - Az| / ‖x - z‖ ^ (1 / 2 : ℝ))
            ≤ ENNReal.ofReal (|Bx - Bz| / ‖x - z‖ ^ (1 / 2 : ℝ) + (epsn : ℝ)) := by
              refine ENNReal.ofReal_le_ofReal ?_
              rw [div_le_iff₀ hNpos]
              have hexp : (|Bx - Bz| / ‖x - z‖ ^ (1 / 2 : ℝ) + (epsn : ℝ)) *
                  ‖x - z‖ ^ (1 / 2 : ℝ) =
                  |Bx - Bz| + (epsn : ℝ) * ‖x - z‖ ^ (1 / 2 : ℝ) := by field_simp
              rw [hexp]
              exact hbound
          _ = ENNReal.ofReal (|Bx - Bz| / ‖x - z‖ ^ (1 / 2 : ℝ)) +
              ENNReal.ofReal (epsn : ℝ) :=
              ENNReal.ofReal_add (div_nonneg (abs_nonneg _) hNpos.le) epsn.coe_nonneg
          _ ≤ (⨆ G : ↥t, ballAverageHolderOn (cubeSetAt y n) D
                (solutionAt M n n y omega (hGn G)).toFun) + (epsn : ℝ≥0∞) := by
              refine add_le_add ?_ (le_of_eq ENNReal.ofReal_coe_nnreal)
              exact le_trans (le_ballAverageHolderOn hxD hzD hne k hbx hbz)
                (le_iSup (fun G : ↥t => ballAverageHolderOn (cubeSetAt y n) D
                  (solutionAt M n n y omega (hGn G)).toFun) G)
      calc ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
            ballAverageHolderOn (cubeSetAt y n) D u.toFun
          ≤ ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
              ⨆ G : ↥t, ballAverageHolderOn (cubeSetAt y n) D
                (solutionAt M n n y omega (hGn G)).toFun := mul_le_mul' le_rfl hkey
        _ = _ := ENNReal.mul_iSup _ _
    · refine iSup_le fun G => ?_
      refine le_iSup_of_le (extendVec y n (G : C(closedCubeAt y n, Vec d)))
        (le_iSup_of_le (htmem _ G.2) (le_iSup_of_le (solutionAt M n n y omega (hGn G))
          (le_iSup_of_le (isDirichletSolutionAt_solutionAt M n n y omega (hGn G)) ?_)))
      exact (iInf_isCubeRepresentative_eq_ballAverageHolderOn hDd _ hcX).ge
  rw [hEq]
  exact Measurable.iSup fun G =>
    (measurable_ballAverageHolderOn_solution M n n y hKn.le (hGn G) hDc).const_mul _

/-! ## 3. The localized error -/

/-- **The localized error is a measurable function of the sample.** -/
theorem measurable_localizedError (M : ABKModel d) (n : ℤ) (y : Vec d) :
    Measurable (localizedError M n y) := by
  have : NeZero d := Provider.Orlicz.neZero_of_model M
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Vec d)
  have hKn : (0 : ℝ) < Real.rpow 3 (-(n : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨t, htc, htmem, htapprox⟩ := exists_countable_normalizedForceAt_approx y n
  have := htc.to_subtype
  have hGn : ∀ G : ↥t, HolderSeminormBoundOn (cubeSetAt y n) (1 / 2)
      (Real.rpow 3 (-(n : ℝ) / 2)) (extendVec y n (G : C(closedCubeAt y n, Vec d))) :=
    fun G => htmem _ G.2
  have hGL2 : ∀ G : ↥t,
      MemVectorL2 (cubeSetAt y n) (extendVec y n (G : C(closedCubeAt y n, Vec d))) :=
    fun G => memVectorL2_of_holderSeminormBoundOn_cubeSetAt hKn.le (by norm_num) (hGn G)
  have hVex : ∀ G : ↥t, ∃ v : H1Function (cubeSetAt y n),
      IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v
        (extendVec y n (G : C(closedCubeAt y n, Vec d))) := fun G =>
    exists_isDirichletSolutionAt_of_isEllipticFieldOn
      (isEllipticFieldOn_comparator M n y) hKn.le (hGn G)
  choose Vsol hVsol using hVex
  have hEq : localizedError M n y = fun omega =>
      ⨆ G : ↥t, ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
        ballAverageSupNormOn (cubeSetAt y n) D
          fun w => (solutionAt M n n y omega (hGn G)).toFun w - (Vsol G).toFun w := by
    funext omega
    refine le_antisymm ?_ ?_
    · refine localizedError_le_iff.2 fun g hg u hu v hv => ?_
      rw [eLpNorm_top_sub_eq_ballAverageSupNormOn hDd u v]
      have hgL2 : MemVectorL2 (cubeSetAt y n) g :=
        memVectorL2_of_holderSeminormBoundOn_cubeSetAt hKn.le (by norm_num)
          (normalizedForceAt_def.1 hg)
      obtain ⟨Lam, hEll⟩ := exists_isEllipticFieldOn_cutoff M n n y omega
      have hkey : ballAverageSupNormOn (cubeSetAt y n) D
            (fun w => u.toFun w - v.toFun w) ≤
          ⨆ G : ↥t, ballAverageSupNormOn (cubeSetAt y n) D
            fun w => (solutionAt M n n y omega (hGn G)).toFun w - (Vsol G).toFun w := by
        refine iSup_le fun x => iSup_le fun hxD => iSup_le fun k => iSup_le fun hbx => ?_
        refine ENNReal.le_of_forall_pos_le_add fun epsn hepsn _ => ?_
        have hepsnR : (0 : ℝ) < (epsn : ℝ) := NNReal.coe_pos.2 hepsn
        have hhalf : (0 : ℝ) < (epsn : ℝ) / 2 := by linarith
        have hrpos : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
        obtain ⟨eta1, he1, hc1⟩ :=
          exists_eta_abs_setAverage_ball_sub_le hEll hrpos hbx hhalf
        obtain ⟨eta2, he2, hc2⟩ := exists_eta_abs_setAverage_ball_sub_le
          (isEllipticFieldOn_comparator M n y) hrpos hbx hhalf
        obtain ⟨G0, hG0t, hG0close⟩ := htapprox g hg (min eta1 eta2) (lt_min he1 he2)
        obtain ⟨G, hGclose⟩ : ∃ G : ↥t, ∀ w ∈ cubeSetAt y n,
            ‖g w - extendVec y n (G : C(closedCubeAt y n, Vec d)) w‖ ≤ min eta1 eta2 :=
          ⟨⟨G0, hG0t⟩, hG0close⟩
        have hb1 := hc1 g (extendVec y n (G : C(closedCubeAt y n, Vec d))) hgL2 (hGL2 G)
          (fun w hw => (hGclose w hw).trans (min_le_left _ _)) u
          (solutionAt M n n y omega (hGn G)) hu
          (isDirichletSolutionAt_solutionAt M n n y omega (hGn G))
        have hb2 := hc2 g (extendVec y n (G : C(closedCubeAt y n, Vec d))) hgL2 (hGL2 G)
          (fun w hw => (hGclose w hw).trans (min_le_right _ _)) v (Vsol G) hv (hVsol G)
        have hGterm : ENNReal.ofReal
            |(⨍ w in Metric.ball x (1 / (k + 1 : ℝ)),
                (solutionAt M n n y omega (hGn G)).toFun w ∂volume) -
              ⨍ w in Metric.ball x (1 / (k + 1 : ℝ)), (Vsol G).toFun w ∂volume| ≤
            ⨆ G : ↥t, ballAverageSupNormOn (cubeSetAt y n) D
              fun w => (solutionAt M n n y omega (hGn G)).toFun w - (Vsol G).toFun w := by
          rw [← setAverage_ball_sub_of_h1 (solutionAt M n n y omega (hGn G)) (Vsol G) hbx]
          exact le_trans (le_ballAverageSupNormOn hxD k hbx)
            (le_iSup (fun G : ↥t => ballAverageSupNormOn (cubeSetAt y n) D
              fun w => (solutionAt M n n y omega (hGn G)).toFun w - (Vsol G).toFun w) G)
        rw [setAverage_ball_sub_of_h1 u v hbx]
        set Au : ℝ := ⨍ w in Metric.ball x (1 / (k + 1 : ℝ)), u.toFun w ∂volume with hAudef
        set Av : ℝ := ⨍ w in Metric.ball x (1 / (k + 1 : ℝ)), v.toFun w ∂volume with hAvdef
        set Bu : ℝ := ⨍ w in Metric.ball x (1 / (k + 1 : ℝ)),
          (solutionAt M n n y omega (hGn G)).toFun w ∂volume with hBudef
        set Bv : ℝ := ⨍ w in Metric.ball x (1 / (k + 1 : ℝ)),
          (Vsol G).toFun w ∂volume with hBvdef
        have hbound : |Au - Av| ≤ |Bu - Bv| + (epsn : ℝ) := by
          have hrw : Au - Av = (Bu - Bv) + ((Au - Bu) - (Av - Bv)) := by ring
          have h1 : |(Bu - Bv) + ((Au - Bu) - (Av - Bv))| ≤
              |Bu - Bv| + |(Au - Bu) - (Av - Bv)| := by
            simpa [Real.norm_eq_abs] using norm_add_le (Bu - Bv) ((Au - Bu) - (Av - Bv))
          have h2 : |(Au - Bu) - (Av - Bv)| ≤ |Au - Bu| + |Av - Bv| := by
            simpa [Real.norm_eq_abs] using norm_sub_le (Au - Bu) (Av - Bv)
          rw [hrw]
          linarith [hb1, hb2]
        calc ENNReal.ofReal |Au - Av|
            ≤ ENNReal.ofReal (|Bu - Bv| + (epsn : ℝ)) := ENNReal.ofReal_le_ofReal hbound
          _ = ENNReal.ofReal |Bu - Bv| + ENNReal.ofReal (epsn : ℝ) :=
              ENNReal.ofReal_add (abs_nonneg _) epsn.coe_nonneg
          _ ≤ (⨆ G : ↥t, ballAverageSupNormOn (cubeSetAt y n) D
                fun w => (solutionAt M n n y omega (hGn G)).toFun w - (Vsol G).toFun w) +
                (epsn : ℝ≥0∞) :=
              add_le_add hGterm (le_of_eq ENNReal.ofReal_coe_nnreal)
      calc ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
            ballAverageSupNormOn (cubeSetAt y n) D (fun w => u.toFun w - v.toFun w)
          ≤ ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
              ⨆ G : ↥t, ballAverageSupNormOn (cubeSetAt y n) D
                fun w => (solutionAt M n n y omega (hGn G)).toFun w -
                  (Vsol G).toFun w := mul_le_mul' le_rfl hkey
        _ = _ := ENNReal.mul_iSup _ _
    · refine iSup_le fun G => ?_
      rw [← eLpNorm_top_sub_eq_ballAverageSupNormOn hDd
        (solutionAt M n n y omega (hGn G)) (Vsol G)]
      exact le_localizedError M n y omega (htmem _ G.2)
        (isDirichletSolutionAt_solutionAt M n n y omega (hGn G)) (hVsol G)
  rw [hEq]
  exact Measurable.iSup fun G =>
    (measurable_ballAverageSupNormOn_solution_sub M n n y hKn.le (hGn G) hDc
      (Vsol G)).const_mul _

/-! ## 4. The chain to the percolation scale -/

/-- **The percolation scale is a measurable function of the sample**, with no
hypothesis beyond the model: the two localized quantities are measurable, hence
so are the good cube event, the event `Q`, and the least scale beyond which no
light crossing occurs. -/
theorem measurable_percolationScaleTotal_of_model (M : ABKModel d) (Creg Cinj : ℝ)
    (m : ℤ) (ep : ℝ) :
    Measurable (percolationScaleTotal M Creg Cinj m ep) :=
  measurable_percolationScaleTotal_of_measurable M Creg Cinj m ep
    (fun n z => measurable_localizedError M n z)
    (fun n z => measurable_localizedRegularity M n z)

end

end Algsuperdiff.Section5.Support
