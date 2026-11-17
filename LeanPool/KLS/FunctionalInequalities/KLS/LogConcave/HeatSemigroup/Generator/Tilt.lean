/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator.InteriorRegularity
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable

/-!
# The tilt identity and Lemma 3.6 on the generator domain

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), (48) and Lemma 3.6, extended from smooth compactly
supported functions to the operator domain `D(A)` of `A = Tbar†Tbar = -ℒ` in `L²(ν)`.

## What is proved

Write `ν = m.tilted (-U)` with a `C¹` potential `U` and all exponential moments, `Tbar` for the
closed unit-weight gradient and `A = Tbar†Tbar`. For every `F ∈ D(A)`, with the representatives of
the `L²` classes `A F ∈ L²(ν)` and `Tbar F ∈ L²(ν; V)`:

* `tiltAverage_adjointComp_eq`: **the tilt identity (48)**, `F_{A F}(z) = ⟪z, F_{Tbar F}(z)⟫` for
  every `z`;
* `taylorTensor_adjointComp_eq`: **Lemma 3.6**, `T_{d+1}(A F) = S_{d+1} T_d(Tbar F)` for every `d`.

The generic facts used here live in `Analysis/BakryEmery/Tilt/SquareIntegrable.lean`: for a finite
measure `μ` with all exponential moments, tilt averages and Taylor tensors only see a function
through its `μ`-class (`tiltAverage_congr_ae`, `taylorTensor_congr_ae`); `g ↦ F_g(z)` is
continuous on `L²(μ)`, being `(∫ e^{⟪z, x⟫} dμ)⁻¹ ⟪e^{⟪z, ·⟫}, g⟫` (`tiltAverage_Lp_eq_inner`);
`F_G` is smooth for every `G ∈ L²(μ; E)` (`contDiff_tiltAverage_Lp`); and the tensor identity
follows from the tilt identity (`taylorTensor_succ_of_eq_inner`). Graph convergence in `D(A)`
gives convergence of `Tbar` by `Analysis.Semigroup.tendsto_apply_of_tendsto_adjointComp`.

## The argument

`C_c^∞(V)` is an operator core of `A` (`exists_seq_smooth_tendsto_adjointComp`): there are
`fₙ ∈ C_c^∞(V)` with `[fₙ] → F` and `A [fₙ] = [-ℒfₙ] → A F`. Then `Tbar [fₙ] = [∇fₙ] → Tbar F`,
since `‖Tbar (xₙ - F)‖² = ⟪A (xₙ - F), xₙ - F⟫` (`tendsto_apply_of_tendsto_adjointComp`). For
smooth compactly supported functions (48) is `tiltAverage_neg_weightedLaplacian`; both sides of
(48) are continuous in the respective `L²` topologies (the right side through the scalar class
`⟪z, Tbar F⟫`), so (48) passes to the limit. Lemma 3.6 is then derived from (48) exactly as in the
smooth case: the tilt average of `A F` is `w ↦ ⟪w, F_{Tbar F}(w)⟫` with `F_{Tbar F}` smooth, and the
Leibniz rule with a linear factor and the symmetry of iterated derivatives give the tensor
identity (`taylorTensor_succ_of_eq_inner`).

## What this is not

No iterate of the source is constructed and Theorem 3.1 is neither stated nor proved here. The
identities are about `L²` classes; no pointwise regularity of `F` beyond membership in `D(A)` is
asserted, and the norm of `taylorTensor` is the multilinear operator norm.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ContDiff RealInnerProductSpace ENNReal

namespace FunctionalInequalities.KLS.LogConcave

section Generator

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- (48) for smooth compactly supported classes, read on the `L²` classes `A [f] = [-ℒf]` and
`Tbar [f] = [∇f]`. -/
private theorem tiltAverage_adjointComp_toLp_eq (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (z : V) :
    tiltAverage (ν : Measure V)
        (⇑(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩)) z =
      ⟪z, tiltAverage (ν : Measure V)
        (⇑(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩)) z⟫ := by
  rw [hν.adjointComp_toLp_eq m hi hνU hU hf hfc, hν.closedWeightedOperator_toLp_eq m hi hf hfc,
    tiltAverage_congr_ae _ (MemLp.coeFn_toLp _) z,
    tiltAverage_congr_ae _ (MemLp.coeFn_toLp _) z, hνU]
  exact tiltAverage_neg_weightedLaplacian m hU (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hfc z

/-- **BKL (48) on the generator domain**: for `ν = m.tilted (-U)` with `U ∈ C¹` and all
exponential moments, and `F ∈ D(A)`, `F_{A F}(z) = ⟪z, F_{Tbar F}(z)⟫` for every `z`. -/
theorem tiltAverage_adjointComp_eq (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (z : V) :
    tiltAverage (ν : Measure V)
        (⇑(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F)) z =
      ⟪z, tiltAverage (ν : Measure V)
        (⇑(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)) z⟫ := by
  obtain ⟨fn, hfn, hfnc, h0, h1⟩ := hν.exists_seq_smooth_tendsto_adjointComp m hi hνU hU F
  let x : ℕ → (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain :=
    fun n => ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n) (hfnc n)⟩
  have hx0 : Tendsto (fun n => (x n : Lp ℝ 2 (ν : Measure V))) atTop
      (𝓝 (F : Lp ℝ 2 (ν : Measure V))) := tendsto_iff_norm_sub_tendsto_zero.2 h0
  have hx1 : Tendsto
      (fun n => adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (x n))
      atTop (𝓝 (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F)) :=
    tendsto_iff_norm_sub_tendsto_zero.2 h1
  have hT := tendsto_apply_of_tendsto_adjointComp
    (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) hx0 hx1
  have hL := ((continuous_tiltAverage_Lp (ν : Measure V) hexp z).tendsto _).comp hx1
  have hR := (((continuous_tiltAverage_Lp (ν : Measure V) hexp z).comp
    ((innerSL ℝ z).compLpL 2 (ν : Measure V)).continuous).tendsto _).comp hT
  rw [inner_tiltAverage_Lp (ν : Measure V) hexp]
  refine tendsto_nhds_unique hL (hR.congr fun n => ?_)
  simp only [Function.comp_apply]
  rw [← inner_tiltAverage_Lp (ν : Measure V) hexp]
  exact (tiltAverage_adjointComp_toLp_eq m hν hi hνU hU (hfn n) (hfnc n) z).symm

/-- **BKL Lemma 3.6 on the generator domain**: for `ν = m.tilted (-U)` with `U ∈ C¹` and all
exponential moments, and `F ∈ D(A)`, `T_{d+1}(A F) = S_{d+1} T_d(Tbar F)` for every `d`, the
original index of `T_d(Tbar F)` placed after its `d` Taylor indices. -/
theorem taylorTensor_adjointComp_eq (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (d : ℕ) :
    taylorTensor (ν : Measure V)
        (⇑(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F))
        (d + 1) =
      symmetrizeML (appendInner (taylorTensor (ν : Measure V)
        (⇑(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)) d)) :=
  taylorTensor_succ_of_eq_inner (ν : Measure V) (contDiff_tiltAverage_Lp _ hexp _)
    (funext fun z => tiltAverage_adjointComp_eq m hν hi hνU hU hexp F z) d

end Generator

end FunctionalInequalities.KLS.LogConcave
