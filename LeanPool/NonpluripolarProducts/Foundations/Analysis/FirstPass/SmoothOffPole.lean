/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.NumericalRestrictedVolume
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.SmoothThetaCriterion
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicContDiff

/-!
# Smoothness outside the pole set

The local positivity argument for a current only evaluates its potential at a
point outside the pole set.  For that purpose, a smooth logarithmic remainder
is stronger than necessary: it suffices that each coordinate representative is
locally equal to a smooth real function at every non-polar point.

`SmoothOffPoleSet` records precisely this local condition.  Smooth analytic
singularities imply it, but the definition also accommodates regularizations
whose logarithmic expression is known to be smooth only away from its zero
set.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.FirstPass.AdmissibleCurrentFormPositivity

noncomputable section

open PositiveClasses NumericalRestrictedVolumeScaffold NumericalRestrictedVolume

variable {n : ℕ}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A global extended-real potential is smooth off its pole set when every
non-polar point has a chart neighbourhood on which the coordinate
representative agrees with a smooth real function. -/
def SmoothOffPoleSet (u : M → EReal) : Prop :=
  ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
    e.val.symm z ∉ poleSet u →
      ∃ g : ComplexModel n → ℝ, (∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ g y) ∧
        chartFunction u e =ᶠ[𝓝 z] fun y => (g y : EReal)

/-- **Off its poles, a potential with analytic singularities in the bounded-remainder convention is
still locally a smooth real function.**  This is the gateway the whole restricted-volume
pipeline goes through, and it needs nothing of the remainder at the pole itself: from
`u z \neq \bot` the generators do not all vanish at `z`, hence do not vanish on a
neighbourhood of `z`, and there the remainder is smooth by hypothesis.

The boundedness half of the convention is not used here at all; it is what keeps the
singularity TYPE under control. -/
theorem exists_smooth_eventuallyEq_of_hasAnalyticSingularitiesSmoothOffPoleAt
    {u : ComplexModel n → EReal} {z : ComplexModel n}
    (hu : HasAnalyticSingularitiesSmoothOffPoleAt u z) (hz : u z ≠ ⊥) :
    ∃ g : ComplexModel n → ℝ, (∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ g y) ∧
      u =ᶠ[𝓝 z] fun y => (g y : EReal) := by
  obtain ⟨c, m, f, hc, ⟨U, hU, hzU, hf⟩, b, -, hb, heq⟩ := hu
  have hsmoothSq : ContDiffOn ℝ ∞ (generatorNormSq f) U := by
    unfold generatorNormSq
    refine ContDiffOn.sum fun j _ => ?_
    have hj : ContDiffOn ℝ ∞ (f j) U := contDiffOn_real_of_differentiableOn_complex (hf j) hU
    exact (contDiff_norm_sq ℝ).comp_contDiffOn hj
  have hcont : ContinuousOn (generatorNormSq f) U := hsmoothSq.continuousOn
  have hlog (y : ComplexModel n) (hy : 0 < generatorNormSq f y) :
      generatorLog f y = (Real.log (generatorNormSq f y) : EReal) := by
    rw [generatorLog, logNormSq, generatorVector_norm_sq,
      ENNReal.log_ofReal_of_pos hy]
  have hpos : 0 < generatorNormSq f z := by
    rcases (generatorNormSq_nonneg f z).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hz
      rw [heq.eq_of_nhds]
      have hbot : generatorLog f z = ⊥ := by
        rw [generatorLog, logNormSq, generatorVector_norm_sq, ← h]
        simp
      rw [hbot, EReal.mul_bot_of_pos (by exact_mod_cast hc)]
      simp
  have hposNear : ∀ᶠ y in 𝓝 z, 0 < generatorNormSq f y :=
    (hcont.continuousAt (hU.mem_nhds hzU)).eventually (lt_mem_nhds hpos)
  refine ⟨fun y => c * Real.log (generatorNormSq f y) + b y, ?_, ?_⟩
  · filter_upwards [hb, hposNear, hU.mem_nhds hzU] with y hby hyp hyU
    have hsq : ContDiffAt ℝ ∞ (generatorNormSq f) y :=
      hsmoothSq.contDiffAt (hU.mem_nhds hyU)
    exact (contDiffAt_const.mul (hsq.log hyp.ne')).add (hby hyp.ne')
  · filter_upwards [heq, hposNear] with y hy hyp
    rw [hy, hlog y hyp]
    simp only [EReal.coe_add, EReal.coe_mul]

/-- Off its poles, a function with smooth analytic singularities is locally a
smooth real function. -/
theorem exists_smooth_eventuallyEq_of_hasSmoothAnalyticSingularitiesAt
    {u : ComplexModel n → EReal} {z : ComplexModel n}
    (hu : HasSmoothAnalyticSingularitiesAt u z) (hz : u z ≠ ⊥) :
    ∃ g : ComplexModel n → ℝ, (∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ g y) ∧
      u =ᶠ[𝓝 z] fun y => (g y : EReal) :=
  exists_smooth_eventuallyEq_of_hasAnalyticSingularitiesSmoothOffPoleAt hu.smoothOffPole hz

omit [IsComplexManifold n M] in
/-- Analytic singularities in the bounded-remainder convention imply local smoothness away from the
pole set. -/
theorem SmoothOffPoleSet.of_hasManifoldAnalyticSingularitiesSmoothOffPole
    {u : M → EReal} (hu : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) u) :
    SmoothOffPoleSet (n := n) u := by
  intro e z hz hpole
  exact exists_smooth_eventuallyEq_of_hasAnalyticSingularitiesSmoothOffPoleAt (hu e z hz) hpole

/- Smooth analytic singularities imply the weaker local smoothness condition
away from the pole set. -/
omit [IsComplexManifold n M] in
theorem SmoothOffPoleSet.of_hasManifoldSmoothAnalyticSingularities
    {u : M → EReal} (hu : HasManifoldSmoothAnalyticSingularities (n := n) u) :
    SmoothOffPoleSet (n := n) u := by
  intro e z hz hpole
  exact exists_smooth_eventuallyEq_of_hasSmoothAnalyticSingularitiesAt (hu e z hz) hpole

/-- Pointwise semipositivity of `θ + ddᶜu` at a point near which the `θ`-PSH
function `u` is a smooth real function in the chart. -/
theorem semipositive_add_smoothDDC_of_thetaPlurisubharmonic
    {θ : SmoothRealForm n M 2} {u : M → EReal} (hu : ThetaPlurisubharmonic θ u)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    {g : ComplexModel n → ℝ} (hg : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ g y)
    (hug : chartFunction u e =ᶠ[𝓝 z] fun y => (g y : EReal))
    (v : ComplexModel n) :
    0 ≤ θ.coeff e z ![v, Complex.I • v] + smoothDDC g z ![v, Complex.I • v] := by
  obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := hu e z hz
  have hmem : {y | ContDiffAt ℝ ∞ g y ∧ chartFunction u e y = (g y : EReal)} ∩ W ∈ 𝓝 z :=
    inter_mem (hg.and hug) (hρ.1.mem_nhds hzW)
  obtain ⟨V, hVsub, hV, hzV⟩ := mem_nhds_iff.mp hmem
  have hVW : V ⊆ W := fun y hy => (hVsub hy).2
  have hgV : ContDiffOn ℝ ∞ g V := fun y hy => (hVsub hy).1.1.contDiffWithinAt
  have hρV : ContDiffOn ℝ ∞ ρ V := hρ.2.2.1.mono hVW
  let f : ComplexModel n → ℝ := fun y => g y + ρ y
  have hfV : ContDiffOn ℝ ∞ f V := hgV.add hρV
  let Vopen : TopologicalSpace.Opens (ComplexModel n) := ⟨V, hV⟩
  have hpshV : PlurisubharmonicOn (fun y => (f y : EReal)) Vopen := by
    intro x hx
    apply (hpsh x (hVW hx)).congr
    filter_upwards [hV.mem_nhds hx] with y hy
    simp only [f, EReal.coe_add, (hVsub hy).1.2]
  have hlevi : 0 ≤ leviForm f z v :=
    leviForm_nonneg_of_contDiffOn_plurisubharmonicOn (U := Vopen) hfV hpshV hzV v
  have hf2 : ContDiffAt ℝ 2 f z :=
    ((hfV z hzV).contDiffAt (hV.mem_nhds hzV)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hdiag : 0 ≤ smoothDDC f z ![v, Complex.I • v] := by
    rw [smoothDDC_complexDiagonal_eq_leviForm hf2 v]
    exact div_nonneg hlevi Real.pi_pos.le
  rw [smoothDDC_add hV hgV hρV hzV, hρ.2.2.2 hzW] at hdiag
  simpa only [ContinuousAlternatingMap.add_apply, add_comm] using hdiag

/-- Off its poles, `θ + ddᶜu` is a semipositive `(1,1)`-form whenever the
`θ`-PSH potential is locally smooth there. -/
theorem isOneOne_and_semipositive_add_smoothDDC_of_smoothOffPoleSet
    (θ : ClosedRealOneOneForm n M) {u : M → EReal}
    (hpsh : ThetaPlurisubharmonic θ.val u)
    (hsmooth : SmoothOffPoleSet (n := n) u)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hpole : e.val.symm z ∉ poleSet u) :
    IsOneOne (θ.val.coeff e z + smoothDDC (fun y => (u (e.val.symm y)).toReal) z) ∧
      CoefficientSemipositive
        (θ.val.coeff e z + smoothDDC (fun y => (u (e.val.symm y)).toReal) z) := by
  obtain ⟨g, hg, hug⟩ := hsmooth e z hz hpole
  have hreal : (fun y => (u (e.val.symm y)).toReal) =ᶠ[𝓝 z] g := by
    filter_upwards [hug] with y hy
    change (chartFunction u e y).toReal = g y
    rw [hy, EReal.toReal_coe]
  have hddc : smoothDDC (fun y => (u (e.val.symm y)).toReal) z = smoothDDC g z :=
    smoothDDC_congr hreal
  have hg2 : ContDiffAt ℝ 2 g z :=
    hg.self_of_nhds.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  refine ⟨?_, ?_⟩
  · intro a b
    simp only [hddc, ContinuousAlternatingMap.add_apply]
    rw [θ.property.2 e z hz a b, MongeAmpere.smoothDDC_isOneOne hg2 a b]
  · intro v
    simp only [hddc, ContinuousAlternatingMap.add_apply]
    exact semipositive_add_smoothDDC_of_thetaPlurisubharmonic hpsh e hz hg hug v

end

end SGPT.Foundations.Analysis.FirstPass.AdmissibleCurrentFormPositivity
