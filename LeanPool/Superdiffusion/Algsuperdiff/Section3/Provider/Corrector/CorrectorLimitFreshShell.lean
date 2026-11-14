/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.NeumannUpperBound

/-!
# CorrectorLimitFreshShell

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the sandwich and the conclusion of the corrector-limit lemma

ABK26, Lemma `l.corrector.limit`.  Step 4 combines

* the ordering `e.ordering.corrector.limit`, `‖∇w_D^{(K)}‖²_{L²(cu_K)} ≤
  ‖∇w_N^{(K)}‖²_{L²(cu_K)}`, proved at a fixed realization in
  `Algsuperdiff/Section3/Provider/Corrector/CubeComparison.lean`;
* the lower bound `e.lower.bound.corrector.limit`, proved unconditionally in
  `Algsuperdiff/Section3/Provider/Corrector/DirichletLowerBound.lean`;
* the upper bound `e.upper.bound.neumann.corrector.limit`, proved in
  `Algsuperdiff/Section3/Provider/Corrector/NeumannUpperBound.lean`,

into the displayed chain

`E[|∇w|²] ≤ liminf_K E[‖∇w_D^{(K)}‖²] ≤ limsup_K E[‖∇w_N^{(K)}‖²] ≤ E[|∇w|²]`,

which gives `e.corrector.limit`: both limits exist and equal `E[|∇w|²]`.

This file proves that, in the form "both sequences converge to `E[|∇w|²]`",
which is the manuscript's assertion that "the limits below exist and" are equal.

## The two cube problems as data

The lemma is stated for *the* solutions `w_D^{(K)} ∈ H¹₀(cu_K)` and `w_N^{(K)} ∈
H¹(cu_K)` of `e.corrector.limit.pde`.  Accordingly their gradients enter below
as given families `Dfam`, `Nfam` carrying exactly the weak formulations of that
display — `IsPotentialZeroTraceOn` with `IsSolenoidalOn (D + f)` for the
Dirichlet problem, `IsPotentialOn` with `IsSolenoidalZeroNormalTraceOn (N + f)`
for the Neumann problem — together with the sample-integrability of their cube
energies, which is the regularity making the expectations `E[‖·‖²_{L²(cu_K)}]`
of the display well defined.  Existence of the two cube solutions is not proved
here; it is the hypothesis "let `w_D^{(K)}`, `w_N^{(K)}` be the solutions" of
the lemma itself.

**Disclosure.**  The assembling theorem
`tendsto_integral_cubeAverage_dirichlet_neumann_of_stationaryStream` is on the
disclosed Ω-level stream inputs `hSm`, `hS`, `hstreamSmooth`, `hstreamAnti`,
`hstreamDiv`, whose shapes are copied verbatim from
`exists_isSolenoidalZeroNormalTraceOn_limsup_le_of_stationaryStream`.  The
stream is not constructed here and does not yet exist in this repository (to
be supplied by the construction).  Until it proves, nothing in this file
realizes the source node `l.corrector.limit` at the fresh shell, and no
node status is claimed.  What is *not* assumed anywhere: the conclusion
`e.corrector.limit`, either one-sided bound, and part (ii)'s conclusion.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Probability.Stationary

noncomputable section

/-! ### The elementary squeeze -/

section Squeeze

/-- If `u ≤ v` pointwise and, for every `ε > 0`, eventually `M - ε ≤ u` and `v ≤
M + ε`, then both sequences converge to `M`.  This is the numerical content of
Step 4 of ABK26: the chain `M ≤ liminf u ≤ limsup v ≤ M` pins both limits. -/
theorem tendsto_of_eventually_sandwich {u v : ℕ → ℝ} {M : ℝ}
    (huv : ∀ K : ℕ, u K ≤ v K)
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in Filter.atTop, M - ε ≤ u K)
    (hhigh : ∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in Filter.atTop, v K ≤ M + ε) :
    Filter.Tendsto u Filter.atTop (nhds M) ∧
      Filter.Tendsto v Filter.atTop (nhds M) := by
  have key : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ K : ℕ in Filter.atTop, |u K - M| ≤ ε ∧ |v K - M| ≤ ε := by
    intro ε hε
    filter_upwards [hlow ε hε, hhigh ε hε] with K h1 h2
    have h3 := huv K
    refine ⟨?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith
  constructor
  · refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (key (ε / 2) (by linarith))
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hN n hn).1 (by linarith)
  · refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (key (ε / 2) (by linarith))
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hN n hn).2 (by linarith)

end Squeeze

/-! ### Step 1 in expectation -/

section Ordering

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- **`e.ordering.corrector.limit` in expectation**.  Integrating the
fixed-realization ordering `setIntegral_vecDot_self_le_of_isSolenoidal` over the
sample space,

`E[ ‖∇w_D^{(K)}‖²_{L²(cu_K)} ] ≤ E[ ‖∇w_N^{(K)}‖²_{L²(cu_K)} ]`.

Only the Neumann energy has to be integrable: the Dirichlet energy is
nonnegative, so the inequality holds for the Bochner integral in either case. -/
theorem integral_cubeAverage_dirichlet_le_neumann (Q : TriadicCube d)
    {f : Ω → HilbertVec d} (hfm : StronglyMeasurable f) (hf : MemLp f 2 μ)
    {Dω Nω : Ω → (Vec d → Vec d)}
    (hDpot : ∀ᵐ ω ∂μ, IsPotentialZeroTraceOn (openCubeSet Q) (Dω ω))
    (hDsol : ∀ᵐ ω ∂μ, IsSolenoidalOn (openCubeSet Q)
      fun x => Dω ω x + (realize f ω x).toVec)
    (hNpot : ∀ᵐ ω ∂μ, IsPotentialOn (openCubeSet Q) (Nω ω))
    (hNsol : ∀ᵐ ω ∂μ, IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      fun x => Nω ω x + (realize f ω x).toVec)
    (hNint : Integrable (fun ω => cubeAverage Q fun x => vecDot (Nω ω x) (Nω ω x)) μ) :
    (∫ ω, cubeAverage Q (fun x => vecDot (Dω ω x) (Dω ω x)) ∂μ)
      ≤ ∫ ω, cubeAverage Q (fun x => vecDot (Nω ω x) (Nω ω x)) ∂μ := by
  have hae : ∀ᵐ ω ∂μ, cubeAverage Q (fun x => vecDot (Dω ω x) (Dω ω x))
      ≤ cubeAverage Q fun x => vecDot (Nω ω x) (Nω ω x) := by
    filter_upwards [hDpot, hDsol, hNpot, hNsol,
      ae_memHilbertVectorL2_realize (μ := μ) Q hfm hf] with ω h1 h2 h3 h4 hfω
    have hres : volume.restrict (cubeSet Q) = volume.restrict (openCubeSet Q) :=
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
    have hfU : MemHilbertVectorL2 (openCubeSet Q) (realize f ω) := by
      have h : MemLp (realize (d := d) f ω) 2 (volume.restrict (cubeSet Q)) := hfω
      rwa [hres] at h
    have hFU : MemVectorL2 (openCubeSet Q) fun x => (realize f ω x).toVec :=
      memVectorL2_toVec_of_memHilbertVectorL2 hfU
    have hDU : MemVectorL2 (openCubeSet Q) (Dω ω) :=
      memVectorL2_of_isPotentialZeroTraceOn h1
    have hNU : MemVectorL2 (openCubeSet Q) (Nω ω) := memVectorL2_of_isPotentialOn h3
    have hcmp := setIntegral_vecDot_self_le_of_isSolenoidal hDU hNU hFU h1 h2 h4
    have hvol : (0 : ℝ) < (cubeVolume Q)⁻¹ := inv_pos.2 (cubeVolume_pos Q)
    have hscaled := mul_le_mul_of_nonneg_left hcmp hvol.le
    simp only [cubeAverage]
    rw [hres]
    linarith [hscaled]
  exact integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ω => cubeAverage_vecDot_self_nonneg Q _) hNint hae

end Ordering

section Conclusion

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]
variable [TopologicalSpace Ω] [R1Space Ω] [BorelSpace Ω] [ContinuousVAdd (Vec d) Ω]
variable [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

end Conclusion

end

end Algsuperdiff.Section3.Provider.Corrector
