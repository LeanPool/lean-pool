/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.ApproximationAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.CubeComparison
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.RealizationTransfer
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.StationaryCorrector
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.StationaryStrip

/-!
# DirichletLowerBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the Dirichlet lower bound of the corrector-limit proof

ABK26, Lemma `l.corrector.limit`, Step 2, proves

`liminf_{K→∞} E[ ‖∇w_D^{(K)}‖²_{L²(cu_K)} ] ≥ E[|∇w|²]`,

the display `e.lower.bound.corrector.limit`.

This file proves that display.  The only non-elementary input is part (i) of
`l.approximation.stationary.by.local`, which is available here unconditionally
as
`Algsuperdiff.Section3.Provider.Corrector.exists_isPotentialZeroTraceOn_limsup_le_of_mem_stationaryPotentialSubspace`,
so the results below are *not* conditional on the approximation lemma: they
consume the proved form of it.

The route differs from the manuscript's in one respect, recorded here.  The
paper reorganizes the three testing identities of
`e.testing.by.vKL.corrector.limit` and then applies Hölder to the resulting
cross term.  We instead use the *variational* form of the same step:
`∇w_D^{(K)}` minimizes `E_K` over `H¹₀(cu_K)`, so testing against the local
competitor `∇v_{K,L}` gives, after completing the square,

`⨍|∇w_D^{(K)}|² ≥ ⨍|f|² - ⨍|∇v_{K,L} + f|²`

(`Algsuperdiff/Section3/Provider/Corrector/CubeComparison.lean`).  The
right-hand side is then controlled by a pointwise Young split against the
stationary flux `j = f + ∇w`, which avoids any Cauchy-Schwarz inequality on the
product `Ω × cu_K` — a step that is not available here, because part (i)
supplies its competitor family with per-sample regularity only and no joint
measurability.  The two routes give the same conclusion; ours needs strictly
less measure theory.

**Disclosure.**  Nothing in this file realizes the source node
`l.corrector.limit`.  Step 3 of the manuscript proof, the Neumann *upper* bound
`e.upper.bound.neumann.corrector.limit`, consumes part (ii) of
`l.approximation.stationary.by.local` — the local solenoidal approximation
built from the JKO94 Chapter-7 stream potential of a stationary solenoidal
field — and no form of that input exists in this repository.  Without it the
sandwich of Step 4 cannot be closed, so only the lower half of
`e.corrector.limit` is proved here.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Probability.Stationary

noncomputable section

/-! ### Elementary carrier bridges -/

section Bridges

variable {d : ℕ}

/-- The squared Euclidean norm of a promoted vector is its dot square. -/
theorem norm_sq_ofVec (a : Vec d) : ‖HilbertVec.ofVec a‖ ^ 2 = vecDot a a := by
  rw [← real_inner_self_eq_norm_sq, HilbertVec.inner_def, HilbertVec.toVec_ofVec]

/-- Forgetting the Hilbert structure preserves square integrability. -/
theorem memVectorL2_toVec_of_memHilbertVectorL2 {U : Set (Vec d)}
    {g : Vec d → HilbertVec d} (hg : MemHilbertVectorL2 U g) :
    MemVectorL2 U fun x => (g x).toVec := by
  simpa using!
    ((HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap).comp_memLp' hg

/-- Promoting a plain vector field preserves square integrability. -/
theorem memHilbertVectorL2_ofVec_of_memVectorL2 {U : Set (Vec d)}
    {g : Vec d → Vec d} (hg : MemVectorL2 U g) :
    MemHilbertVectorL2 U fun x => HilbertVec.ofVec (g x) :=
  memHilbertVectorL2_hilbertifyVecField hg

/-- Square integrability of a zero-trace potential field. -/
theorem memVectorL2_of_isPotentialZeroTraceOn {U : Set (Vec d)} {v : Vec d → Vec d}
    (hv : IsPotentialZeroTraceOn U v) : MemVectorL2 U v := by
  obtain ⟨u, hu⟩ := hv
  simpa [hu] using u.toH1Function.grad_memVectorL2

/-- The normalized `L²` norm of a square-integrable field is the cube average of
its squared pointwise norm.  This is the computation used inside
`Algsuperdiff.Section3.Provider.Corrector.integral_cubeLpNorm_two_rpow_realize`,
isolated for reuse. -/
theorem cubeLpNorm_two_rpow_eq_cubeAverage_norm_sq {Q : TriadicCube d}
    {g : Vec d → HilbertVec d} (hg : MemHilbertVectorL2 (cubeSet Q) g) :
    cubeLpNorm Q 2 g ^ (2 : ℝ) = cubeAverage Q fun x => ‖g x‖ ^ 2 := by
  have h := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow Q 2 g (by norm_num) (by simp)
    (memLp_normalizedCubeMeasure_of_memHilbertVectorL2 hg)
  simpa [cubeAverage, Real.rpow_natCast] using h

end Bridges

/-! ### The per-sample Young split of the competitor flux -/

section Sample

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω}

omit [MeasurableSpace Ω] [AddAction (Vec d) Ω] in
/-- Promotion to the Euclidean Hilbert carrier is additive. -/
theorem ofVec_add' (a b : Vec d) :
    HilbertVec.ofVec (a + b) = HilbertVec.ofVec a + HilbertVec.ofVec b :=
  HilbertVec.ext fun _ => rfl

omit [MeasurableSpace Ω] in
/-- The competitor flux decomposes as the realized stationary flux plus the
approximation error: `∇v_{K,L} + f = (∇w + f) + (∇v_{K,L} - ∇w)`, pointwise in
space and in the sample. -/
theorem ofVec_add_realize_eq (f p : Ω → HilbertVec d) (v : Vec d → Vec d)
    (ω : Ω) (x : Vec d) :
    HilbertVec.ofVec (v x + (realize f ω x).toVec)
      = realize (fun ω' => p ω' + f ω') ω x
        + (HilbertVec.ofVec (v x) - realize p ω x) := by
  have h1 : HilbertVec.ofVec (v x + (realize f ω x).toVec)
      = HilbertVec.ofVec (v x) + realize f ω x := by
    rw [ofVec_add', HilbertVec.ofVec_toVec]
  have h2 : realize (fun ω' => p ω' + f ω') ω x
      = realize p ω x + realize f ω x := rfl
  rw [h1, h2]
  abel

omit [MeasurableSpace Ω] in
/-- **The Step-2 comparison after the Young split, at a fixed sample.**

For a Dirichlet gradient `D` on the cube, a zero-trace competitor `v`, and every
`δ > 0`,

`⨍|f|² - (1+δ) ⨍|∇w + f|² - (1+δ⁻¹) ⨍|v - ∇w|² ≤ ⨍|D|²`,

where all fields are the spatial realizations at the sample `ω`.  This is the
manuscript's Step 2 with the Hölder step replaced by a pointwise Young
inequality; see the module docstring. -/
theorem cubeAverage_vecDot_self_ge_young (Q : TriadicCube d) {δ : ℝ} (hδ : 0 < δ)
    {f p : Ω → HilbertVec d} {Dω vω : Vec d → Vec d} {ω : Ω}
    (hfω : MemHilbertVectorL2 (cubeSet Q) (realize f ω))
    (hpω : MemHilbertVectorL2 (cubeSet Q) (realize p ω))
    (hDpot : IsPotentialZeroTraceOn (openCubeSet Q) Dω)
    (hDsol : IsSolenoidalOn (openCubeSet Q)
      fun x => Dω x + (realize f ω x).toVec)
    (hvpot : IsPotentialZeroTraceOn (openCubeSet Q) vω) :
    cubeAverage Q (fun x => ‖realize f ω x‖ ^ 2)
        - (1 + δ) * cubeAverage Q
            (fun x => ‖realize (fun ω' => p ω' + f ω') ω x‖ ^ 2)
        - (1 + δ⁻¹) * cubeAverage Q
            (fun x => ‖HilbertVec.ofVec (vω x) - realize p ω x‖ ^ 2)
      ≤ cubeAverage Q fun x => vecDot (Dω x) (Dω x) := by
  classical
  set U : Set (Vec d) := openCubeSet Q with hU
  have hres : volume.restrict (cubeSet Q) = volume.restrict U :=
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
  -- Square integrability of every field involved, on the open cube.
  have hfU : MemHilbertVectorL2 U (realize f ω) := by
    have h : MemLp (realize (d := d) f ω) 2 (volume.restrict (cubeSet Q)) := hfω
    rwa [hres] at h
  have hpU : MemHilbertVectorL2 U (realize p ω) := by
    have h : MemLp (realize (d := d) p ω) 2 (volume.restrict (cubeSet Q)) := hpω
    rwa [hres] at h
  have hjU : MemHilbertVectorL2 U (realize (fun ω' => p ω' + f ω') ω) := by
    refine (hpU.add hfU).ae_eq ?_
    filter_upwards with x
    rfl
  have hFU : MemVectorL2 U fun x => (realize f ω x).toVec :=
    memVectorL2_toVec_of_memHilbertVectorL2 hfU
  have hDU : MemVectorL2 U Dω := memVectorL2_of_isPotentialZeroTraceOn hDpot
  have hvU : MemVectorL2 U vω := memVectorL2_of_isPotentialZeroTraceOn hvpot
  have hRU : MemHilbertVectorL2 U
      fun x => HilbertVec.ofVec (vω x) - realize p ω x :=
    (memHilbertVectorL2_ofVec_of_memVectorL2 hvU).sub hpU
  -- Step 2 in flux form on the open cube.
  have hflux := setIntegral_vecDot_flux_ge_of_isSolenoidalOn hDU hFU hvU hDsol hvpot
  -- Young split of the competitor flux.
  have hyoung : ∫ x in U, vecDot (vω x + (realize f ω x).toVec)
        (vω x + (realize f ω x).toVec)
      ≤ (1 + δ) * (∫ x in U, ‖realize (fun ω' => p ω' + f ω') ω x‖ ^ 2)
        + (1 + δ⁻¹) * ∫ x in U, ‖HilbertVec.ofVec (vω x) - realize p ω x‖ ^ 2 := by
    have hjint : IntegrableOn
        (fun x => ‖realize (fun ω' => p ω' + f ω') ω x‖ ^ 2) U :=
      (memLp_two_iff_integrable_sq_norm hjU.aestronglyMeasurable).1 hjU
    have hRint : IntegrableOn
        (fun x => ‖HilbertVec.ofVec (vω x) - realize p ω x‖ ^ 2) U :=
      (memLp_two_iff_integrable_sq_norm hRU.aestronglyMeasurable).1 hRU
    have hlhs : IntegrableOn (fun x => vecDot (vω x + (realize f ω x).toVec)
        (vω x + (realize f ω x).toVec)) U :=
      integrableOn_vecDot_of_memVectorL2 (hvU.add hFU) (hvU.add hFU)
    have hmono : ∫ x in U, vecDot (vω x + (realize f ω x).toVec)
          (vω x + (realize f ω x).toVec)
        ≤ ∫ x in U, ((1 + δ) * ‖realize (fun ω' => p ω' + f ω') ω x‖ ^ 2
            + (1 + δ⁻¹) * ‖HilbertVec.ofVec (vω x) - realize p ω x‖ ^ 2) := by
      refine integral_mono hlhs ((hjint.const_mul _).add (hRint.const_mul _)) ?_
      intro x
      show vecDot (vω x + (realize f ω x).toVec) (vω x + (realize f ω x).toVec)
          ≤ (1 + δ) * ‖realize (fun ω' => p ω' + f ω') ω x‖ ^ 2
            + (1 + δ⁻¹) * ‖HilbertVec.ofVec (vω x) - realize p ω x‖ ^ 2
      have hrw : vecDot (vω x + (realize f ω x).toVec)
          (vω x + (realize f ω x).toVec)
          = ‖realize (fun ω' => p ω' + f ω') ω x
              + (HilbertVec.ofVec (vω x) - realize p ω x)‖ ^ 2 := by
        rw [← norm_sq_ofVec, ofVec_add_realize_eq f p vω ω x]
      rw [hrw]
      exact normSq_add_le_young hδ _ _
    refine hmono.trans (le_of_eq ?_)
    rw [integral_add (hjint.const_mul _) (hRint.const_mul _), integral_const_mul,
      integral_const_mul]
  -- Convert the set integrals into cube averages.
  have hFsq : ∀ x : Vec d, vecDot (realize f ω x).toVec (realize f ω x).toVec
      = ‖realize f ω x‖ ^ 2 := fun x => by
    rw [← real_inner_self_eq_norm_sq, HilbertVec.inner_def]
  have hFF : ∫ x in U, vecDot (realize f ω x).toVec (realize f ω x).toVec
      = ∫ x in U, ‖realize f ω x‖ ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall hFsq)
  have hcombine : (∫ x in U, ‖realize f ω x‖ ^ 2)
        - (1 + δ) * (∫ x in U, ‖realize (fun ω' => p ω' + f ω') ω x‖ ^ 2)
        - (1 + δ⁻¹) * (∫ x in U, ‖HilbertVec.ofVec (vω x) - realize p ω x‖ ^ 2)
      ≤ ∫ x in U, vecDot (Dω x) (Dω x) := by
    rw [← hFF]
    linarith [hflux, hyoung]
  have hvol : (0 : ℝ) < (cubeVolume Q)⁻¹ := inv_pos.2 (cubeVolume_pos Q)
  have hscaled := mul_le_mul_of_nonneg_left hcombine hvol.le
  simp only [cubeAverage]
  rw [hres]
  linarith [hscaled]

end Sample

/-! ### The expected lower bound at a fixed scale -/

section Expectation

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- **The expected Step-2 comparison at a fixed cube.**  Integrating
`cubeAverage_vecDot_self_ge_young` over the sample space and applying the
stationary transfer turns the two realized cube averages into the expectations
`E[|f|²]` and `E[|∇w + f|²]`. -/
theorem integral_cubeAverage_vecDot_self_ge (Q : TriadicCube d) {δ : ℝ} (hδ : 0 < δ)
    {f p : Ω → HilbertVec d} (hfm : StronglyMeasurable f) (hf : MemLp f 2 μ)
    (hpm : StronglyMeasurable p) (hp : MemLp p 2 μ)
    {Dfam Vfam : Ω → (Vec d → Vec d)}
    (hDpot : ∀ᵐ ω ∂μ, IsPotentialZeroTraceOn (openCubeSet Q) (Dfam ω))
    (hDsol : ∀ᵐ ω ∂μ, IsSolenoidalOn (openCubeSet Q)
      fun x => Dfam ω x + (realize f ω x).toVec)
    (hVpot : ∀ᵐ ω ∂μ, IsPotentialZeroTraceOn (openCubeSet Q) (Vfam ω))
    (hDint : Integrable (fun ω => cubeAverage Q fun x => vecDot (Dfam ω x) (Dfam ω x)) μ)
    (hRint : Integrable (fun ω => cubeLpNorm Q 2
      (fun x => HilbertVec.ofVec (Vfam ω x) - realize p ω x) ^ (2 : ℝ)) μ) :
    (∫ ω, ‖f ω‖ ^ 2 ∂μ) - (1 + δ) * (∫ ω, ‖p ω + f ω‖ ^ 2 ∂μ)
        - (1 + δ⁻¹) * ∫ ω, cubeLpNorm Q 2
            (fun x => HilbertVec.ofVec (Vfam ω x) - realize p ω x) ^ (2 : ℝ) ∂μ
      ≤ ∫ ω, cubeAverage Q (fun x => vecDot (Dfam ω x) (Dfam ω x)) ∂μ := by
  classical
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  have hjm : StronglyMeasurable fun ω => p ω + f ω := hpm.add hfm
  have hj : MemLp (fun ω => p ω + f ω) 2 μ := hp.add hf
  -- The three sample-space integrands.
  set A : Ω → ℝ := fun ω => cubeAverage Q fun x => ‖realize f ω x‖ ^ 2 with hAdef
  set B : Ω → ℝ := fun ω => cubeAverage Q
    fun x => ‖realize (fun ω' => p ω' + f ω') ω x‖ ^ 2 with hBdef
  set C : Ω → ℝ := fun ω => cubeAverage Q
    fun x => ‖HilbertVec.ofVec (Vfam ω x) - realize p ω x‖ ^ 2 with hCdef
  have hAint : Integrable A μ := by
    have := (integrable_setIntegral_normSq_realize (μ := μ) hQfin hfm hf).const_mul
      (cubeVolume Q)⁻¹
    simpa [hAdef, cubeAverage] using this
  have hBint : Integrable B μ := by
    have := (integrable_setIntegral_normSq_realize (μ := μ) hQfin hjm hj).const_mul
      (cubeVolume Q)⁻¹
    simpa [hBdef, cubeAverage] using this
  -- The error term, in the two equivalent normalizations.
  have hCeq : ∀ᵐ ω ∂μ, cubeLpNorm Q 2
      (fun x => HilbertVec.ofVec (Vfam ω x) - realize p ω x) ^ (2 : ℝ) = C ω := by
    filter_upwards [hVpot, ae_memHilbertVectorL2_realize (μ := μ) Q hpm hp] with ω hv hpω
    have hres : volume.restrict (cubeSet Q) = volume.restrict (openCubeSet Q) :=
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
    have hvQ : MemVectorL2 (cubeSet Q) (Vfam ω) := by
      have h : MemLp (Vfam ω) 2 (volume.restrict (openCubeSet Q)) :=
        memVectorL2_of_isPotentialZeroTraceOn hv
      rwa [← hres] at h
    exact cubeLpNorm_two_rpow_eq_cubeAverage_norm_sq
      ((memHilbertVectorL2_ofVec_of_memVectorL2 hvQ).sub hpω)
  have hCint : Integrable C μ := hRint.congr hCeq
  -- The a.e. pointwise inequality supplied by the sample-level lemma.
  have hae : ∀ᵐ ω ∂μ, A ω - (1 + δ) * B ω - (1 + δ⁻¹) * C ω
      ≤ cubeAverage Q fun x => vecDot (Dfam ω x) (Dfam ω x) := by
    filter_upwards [hDpot, hDsol, hVpot,
      ae_memHilbertVectorL2_realize (μ := μ) Q hfm hf,
      ae_memHilbertVectorL2_realize (μ := μ) Q hpm hp] with ω hd hs hv hfω hpω
    exact cubeAverage_vecDot_self_ge_young Q hδ hfω hpω hd hs hv
  have hmono : ∫ ω, (A ω - (1 + δ) * B ω - (1 + δ⁻¹) * C ω) ∂μ
      ≤ ∫ ω, cubeAverage Q (fun x => vecDot (Dfam ω x) (Dfam ω x)) ∂μ :=
    integral_mono_ae
      ((hAint.sub (hBint.const_mul (1 + δ))).sub (hCint.const_mul (1 + δ⁻¹))) hDint hae
  have hLHS : ∫ ω, (A ω - (1 + δ) * B ω - (1 + δ⁻¹) * C ω) ∂μ
      = (∫ ω, A ω ∂μ) - (1 + δ) * (∫ ω, B ω ∂μ) - (1 + δ⁻¹) * ∫ ω, C ω ∂μ := by
    have e1 : ∫ ω, (A ω - (1 + δ) * B ω - (1 + δ⁻¹) * C ω) ∂μ
        = (∫ ω, (A ω - (1 + δ) * B ω) ∂μ) - ∫ ω, (1 + δ⁻¹) * C ω ∂μ :=
      integral_sub (hAint.sub (hBint.const_mul (1 + δ))) (hCint.const_mul (1 + δ⁻¹))
    have e2 : ∫ ω, (A ω - (1 + δ) * B ω) ∂μ
        = (∫ ω, A ω ∂μ) - ∫ ω, (1 + δ) * B ω ∂μ :=
      integral_sub hAint (hBint.const_mul (1 + δ))
    have e3 : ∫ ω, (1 + δ) * B ω ∂μ = (1 + δ) * ∫ ω, B ω ∂μ := integral_const_mul _ _
    have e4 : ∫ ω, (1 + δ⁻¹) * C ω ∂μ = (1 + δ⁻¹) * ∫ ω, C ω ∂μ := integral_const_mul _ _
    rw [e1, e2, e3, e4]
  rw [hLHS] at hmono
  have hA : ∫ ω, A ω ∂μ = ∫ ω, ‖f ω‖ ^ 2 ∂μ :=
    integral_cubeAverage_normSq_realize (μ := μ) Q hfm hf
  have hB : ∫ ω, B ω ∂μ = ∫ ω, ‖p ω + f ω‖ ^ 2 ∂μ :=
    integral_cubeAverage_normSq_realize (μ := μ) Q hjm hj
  have hC : ∫ ω, C ω ∂μ = ∫ ω, cubeLpNorm Q 2
      (fun x => HilbertVec.ofVec (Vfam ω x) - realize p ω x) ^ (2 : ℝ) ∂μ :=
    (integral_congr_ae hCeq).symm
  rw [hA, hB, hC] at hmono
  exact hmono

end Expectation

/-! ### The corrector-limit lower bound -/

section Assembly

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]
variable [TopologicalSpace Ω] [R1Space Ω] [BorelSpace Ω] [ContinuousVAdd (Vec d) Ω]
variable [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

omit [MeasurableSpace Ω] [AddAction (Vec d) Ω] [SFinite μ] [MeasurableConstVAdd (Vec d) Ω]
  [MeasurableVAdd₂ (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ] [TopologicalSpace Ω]
  [R1Space Ω] [BorelSpace Ω] [ContinuousVAdd (Vec d) Ω] [IsLocallyFiniteMeasure μ]
  [μ.InnerRegularCompactLTTop] in
/-- The localization error `C 3^{-L}` of part (i) of
`l.approximation.stationary.by.local` can be driven below any positive
threshold by taking `L` large. -/
theorem exists_three_zpow_neg_mul_le (D M c : ℝ) (hD : 0 ≤ D) (hM : 0 ≤ M) (hc : 0 < c) :
    ∃ L : ℕ, D * (3 : ℝ) ^ (-(L : ℤ)) * M ≤ c := by
  have hpos : (0 : ℝ) < D * M + 1 := by positivity
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < c / (D * M + 1) by positivity)
    (show (3 : ℝ)⁻¹ < 1 by norm_num)
  refine ⟨L, ?_⟩
  have hzp : (3 : ℝ) ^ (-(L : ℤ)) = ((3 : ℝ)⁻¹) ^ L := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  have h1 : D * (3 : ℝ) ^ (-(L : ℤ)) * M = D * M * ((3 : ℝ)⁻¹) ^ L := by
    rw [hzp]; ring
  have hDM : 0 ≤ D * M := mul_nonneg hD hM
  have h2 : D * M * ((3 : ℝ)⁻¹) ^ L ≤ D * M * (c / (D * M + 1)) :=
    mul_le_mul_of_nonneg_left hL.le hDM
  have h3 : D * M * (c / (D * M + 1)) ≤ c := by
    rw [mul_div_assoc', div_le_iff₀ hpos]
    nlinarith [hc.le, hDM]
  linarith

/-- **`e.lower.bound.corrector.limit`**, in the `ε`-form.

Let `f` be a stationary square-integrable forcing and let `∇w = p` be the
whole-space stationary corrector gradient of `l.corrector.limit`, i.e. the
element of `L²(Ω;ℝᵈ)` characterized by `∇w ∈ L²_pot(Ω)` (`hpmem`) and `f + ∇w ∈
L²_sol(Ω)` (`hflux`), which is the weak form of `-Δw = ∇·f` on `ℝᵈ`.  Let
`∇w_D^{(K)} = Dfam K` be the Dirichlet gradients of `e.corrector.limit.pde`.
Then for every `ε > 0`, eventually in `K`,

`E[|∇w|²] - ε ≤ E[ ‖∇w_D^{(K)}‖²_{L²(cu_K)} ]`.

The proof consumes part (i) of `l.approximation.stationary.by.local` in the
form `exists_family_bound`, the Step-2 comparison of
`Algsuperdiff/Section3/Provider/Corrector/CubeComparison.lean`, and the
stationary transfer.

**Disclosure.**  This is the lower half of `e.corrector.limit` only.  It is not
the source node `l.corrector.limit` and claims no node status; the matching
Neumann upper bound needs part (ii) of the approximation lemma, which does not
exist in this repository. -/
theorem eventually_integral_normSq_sub_le_integral_cubeAverage_dirichlet
    {f p : Ω → HilbertVec d}
    (hfm : StronglyMeasurable f) (hf : MemLp f 2 μ)
    (hpm : StronglyMeasurable p) (hp : MemLp p 2 μ)
    (hpmem : hp.toLp p ∈ stationaryPotentialSubspace (μ := μ) (d := d))
    (hflux : hf.toLp f + hp.toLp p ∈ stationarySolenoidalSubspace (μ := μ) (d := d))
    {Dfam : ℕ → Ω → (Vec d → Vec d)}
    (hDpot : ∀ K : ℕ, ∀ᵐ ω ∂μ,
      IsPotentialZeroTraceOn (openCubeSet (originCube d (K : ℤ))) (Dfam K ω))
    (hDsol : ∀ K : ℕ, ∀ᵐ ω ∂μ,
      IsSolenoidalOn (openCubeSet (originCube d (K : ℤ)))
        fun x => Dfam K ω x + (realize f ω x).toVec)
    (hDint : ∀ K : ℕ, Integrable (fun ω => cubeAverage (originCube d (K : ℤ))
      fun x => vecDot (Dfam K ω x) (Dfam K ω x)) μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℕ in Filter.atTop,
      (∫ ω, ‖p ω‖ ^ 2 ∂μ) - ε
        ≤ ∫ ω, cubeAverage (originCube d (K : ℤ))
            (fun x => vecDot (Dfam K ω x) (Dfam K ω x)) ∂μ := by
  classical
  set M : ℝ := ∫ ω, ‖p ω‖ ^ 2 ∂μ with hMdef
  set S : ℝ := ∫ ω, ‖p ω + f ω‖ ^ 2 ∂μ with hSdef
  have hM0 : 0 ≤ M := integral_nonneg fun ω => by positivity
  have hS0 : 0 ≤ S := integral_nonneg fun ω => by positivity
  -- The Helmholtz identity `E[|f|²] - E[|f + ∇w|²] = E[|∇w|²]`.
  have hkey : (∫ ω, ‖f ω‖ ^ 2 ∂μ) - S = M := by
    have hFP : inner ℝ (hp.toLp p) (hf.toLp f + hp.toLp p) = 0 :=
      inner_eq_zero_of_mem_potential_of_mem_solenoidal hpmem hflux
    have hinner : inner ℝ (hp.toLp p) (hf.toLp f) = -‖hp.toLp p‖ ^ 2 := by
      rw [inner_add_right, real_inner_self_eq_norm_sq] at hFP
      linarith
    have hexp : ‖hp.toLp p + hf.toLp f‖ ^ 2
        = ‖hp.toLp p‖ ^ 2 + 2 * inner ℝ (hp.toLp p) (hf.toLp f) + ‖hf.toLp f‖ ^ 2 :=
      norm_add_sq_real _ _
    have hS' : S = ‖hp.toLp p + hf.toLp f‖ ^ 2 := by
      rw [hSdef,
        show (∫ ω, ‖p ω + f ω‖ ^ 2 ∂μ) = ‖(hp.add hf).toLp (p + f)‖ ^ 2 from
          integral_normSq_eq_norm_sq_toLp (hp.add hf),
        MemLp.toLp_add]
    have hM' : M = ‖hp.toLp p‖ ^ 2 := integral_normSq_eq_norm_sq_toLp hp
    have hF' : ∫ ω, ‖f ω‖ ^ 2 ∂μ = ‖hf.toLp f‖ ^ 2 := integral_normSq_eq_norm_sq_toLp hf
    rw [hS', hM', hF', hexp, hinner]
    ring
  -- The Young parameter.
  set δ : ℝ := min 1 (ε / (2 * (S + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδS : δ * S ≤ ε / 2 := by
    have hδle : δ ≤ ε / (2 * (S + 1)) := min_le_right _ _
    have hstep : δ * S ≤ ε / (2 * (S + 1)) * S := mul_le_mul_of_nonneg_right hδle hS0
    have hfin : ε / (2 * (S + 1)) * S ≤ ε / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
      nlinarith [hε.le, hS0]
    linarith
  have hcoef : (0 : ℝ) < 1 + δ⁻¹ := by positivity
  set θ : ℝ := ε / (2 * (1 + δ⁻¹)) with hθdef
  have hθ0 : 0 < θ := by positivity
  have hθmul : (1 + δ⁻¹) * θ = ε / 2 := by
    rw [hθdef]
    field_simp
  -- The localization scale and the approximation family.
  obtain ⟨L, hL⟩ := exists_three_zpow_neg_mul_le (d : ℝ) M (θ / 2)
    (Nat.cast_nonneg d) hM0 (by linarith)
  obtain ⟨V, g, hg0, hgtend, hVpot, hVint, hVbd⟩ :=
    exists_family_bound (μ := μ) L (show (0 : ℝ) < θ / 4 by linarith) hpm hp hpmem
  have hgev : ∀ᶠ K : ℕ in Filter.atTop, g K < θ / 4 :=
    Filter.Tendsto.eventually_lt_const (show (0 : ℝ) < θ / 4 by linarith) hgtend
  filter_upwards [hgev] with K hgK
  have hmain := integral_cubeAverage_vecDot_self_ge (μ := μ) (originCube d (K : ℤ)) hδ0
    hfm hf hpm hp (hDpot K) (hDsol K) (hVpot K) (hDint K) (hVint K)
  have hbound : (∫ ω, cubeLpNorm (originCube d (K : ℤ)) 2
      (fun x => HilbertVec.ofVec (V K ω x) - realize p ω x) ^ (2 : ℝ) ∂μ) ≤ θ := by
    have h := hVbd K
    linarith
  have hscaled : (1 + δ⁻¹) * (∫ ω, cubeLpNorm (originCube d (K : ℤ)) 2
      (fun x => HilbertVec.ofVec (V K ω x) - realize p ω x) ^ (2 : ℝ) ∂μ)
      ≤ (1 + δ⁻¹) * θ := mul_le_mul_of_nonneg_left hbound hcoef.le
  linarith [hmain, hkey, hδS, hscaled, hθmul]

end Assembly

end

end Algsuperdiff.Section3.Provider.Corrector
