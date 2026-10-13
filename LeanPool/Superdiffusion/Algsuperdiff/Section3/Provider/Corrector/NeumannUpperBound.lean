/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.DirichletLowerBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.SolenoidalApproximation

/-!
# NeumannUpperBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the Neumann upper bound of the corrector-limit proof

ABK26, Lemma `l.corrector.limit`, Step 3, proves

`limsup_{K→∞} E[ ‖∇w_N^{(K)}‖²_{L²(cu_K)} ] ≤ E[|∇w|²]`,

the display `e.upper.bound.neumann.corrector.limit`.

This file proves that display, in the `ε`-form and in the printed `limsup`
form.  It is the exact mirror of
`Algsuperdiff/Section3/Provider/Corrector/DirichletLowerBound.lean`: the
Dirichlet class `H¹₀(cu_K)` is replaced by the Neumann class `H¹(cu_K)`
(CoarseGraining's `IsPotentialOn` together with the natural boundary condition
`IsSolenoidalZeroNormalTraceOn (∇w_N + f)`), and part (i) of
`l.approximation.stationary.by.local` is replaced by part (ii).

## The route

The manuscript reorganizes the testing identities, applies Hölder to the cross
term `⨍ (j − j_{K,L}) · ∇w_N`, and then absorbs `E[‖∇w_N‖²]^{1/2}` by Young's
inequality.  As in the Dirichlet half we use instead the *variational* form of
the same step, which keeps every estimate at a fixed sample and therefore needs
no Cauchy-Schwarz inequality on the product `Ω × cu_K`.  Writing `N =
∇w_N^{(K)}`, `F = f`, `J = j_{K,L}` at a fixed realization, the two weak
formulations give

`⨍ (N + F) · N = 0` (the natural boundary condition tested against `N ∈ H¹`) and
`⨍ J · N = 0` (`J ∈ L²_{sol,0}(cu_K)` tested against the same `N`),

hence `⨍ (J − F) · N = ⨍ |N|²`, and expanding `0 ≤ ⨍ |(J − F) − N|²` yields

`⨍ |∇w_N^{(K)}|² ≤ ⨍ |j_{K,L} − f|²`.

This is the Neumann companion of the Dirichlet flux comparison
`⨍|f|² − ⨍|∇v_{K,L} + f|² ≤ ⨍|∇w_D^{(K)}|²`
(`Algsuperdiff/Section3/Provider/Corrector/CubeComparison.lean`): in both cases
the competitor enters only through its flux.  Since `j = f + ∇w`, the
right-hand side is `⨍ |∇w + (j_{K,L} − j)|²`, and a pointwise Young split
against the approximation error finishes the fixed-cube estimate

`E[ ⨍ |∇w_N^{(K)}|² ] ≤ (1+δ) E[|∇w|²] + (1+δ⁻¹) E[ ‖j_{K,L} − j‖²_{L²(cu_K)} ]`,

which is the paper's display with `(1−δ)⁻¹, (4δ)⁻¹` replaced by `(1+δ),
(1+δ⁻¹)`.  Consequently the absorption lemma
`Algsuperdiff/Section3/Provider/Corrector/YoungAbsorption.lean` is not used:
the self-improving inequality never arises on this route.  The two routes give
the same conclusion, and this one needs strictly less measure theory — exactly
the divergence already recorded in the Dirichlet half.

## What is consumed, and how

Part (ii) of `l.approximation.stationary.by.local` is available in
`Algsuperdiff/Section3/Provider/Corrector/SolenoidalApproximation.lean`.  We
consume it through its *concrete* witness family `localStreamApprox` rather
than through the existential
`exists_isSolenoidalZeroNormalTraceOn_limsup_le_of_stationaryStream`, because
the existential's admissibility clause `IsSolenoidalZeroNormalTraceOn` carries
no per-sample square integrability of the error `j_{K,L} − j` (CoarseGraining's
predicate is orthogonality to `∇H¹(cu_K)` and nothing else), whereas the Young
split above needs it.  The concrete family supplies it as
`ae_memLp_localStreamApprox_sub`.  Nothing is assumed: the admissibility, the
integrability and the error estimate are all produced by that file from the
same three disclosed stream hypotheses.

**Disclosure.**  The results below are *conditional* on the Ω-level stream `S`
entering through `hSm`, `hS`, `hstreamSmooth`, `hstreamAnti`, `hstreamDiv`,
whose shapes are copied verbatim from
`exists_isSolenoidalZeroNormalTraceOn_limsup_le_of_stationaryStream`.  That
stream is not constructed here and does not yet exist in the repository (the
representation leg, to be supplied by the construction).  Nothing in this file
realizes a source node, and neither `e.upper.bound.neumann.corrector.limit` nor
`e.corrector.limit` is assumed anywhere: the conclusion is proved, not
disclosed.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

noncomputable section

/-! ### Elementary carrier lemmas -/

section Carrier

variable {d : ℕ}

/-- Left additivity of the Euclidean dot product under subtraction. -/
theorem vecDot_sub_left (a b c : Vec d) :
    vecDot (a - b) c = vecDot a c - vecDot b c := by
  simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- Promotion to the Euclidean Hilbert carrier commutes with subtraction. -/
theorem ofVec_sub' (a b : Vec d) :
    HilbertVec.ofVec (a - b) = HilbertVec.ofVec a - HilbertVec.ofVec b :=
  HilbertVec.ext fun _ => rfl

/-- Square integrability of a potential field, i.e. of the gradient of an
`H¹(U)` function.  This is the Neumann counterpart of
`Algsuperdiff.Section3.Provider.Corrector.memVectorL2_of_isPotentialZeroTraceOn`. -/
theorem memVectorL2_of_isPotentialOn {U : Set (Vec d)} {v : Vec d → Vec d}
    (hv : IsPotentialOn U v) : MemVectorL2 U v := by
  obtain ⟨u, hu⟩ := hv
  simpa [hu] using u.grad_memVectorL2

/-- The cube average of a squared field is nonnegative. -/
theorem cubeAverage_vecDot_self_nonneg (Q : TriadicCube d) (g : Vec d → Vec d) :
    0 ≤ cubeAverage Q fun x => vecDot (g x) (g x) := by
  simp only [cubeAverage]
  exact mul_nonneg (inv_nonneg.2 (cubeVolume_pos Q).le)
    (integral_nonneg fun x => vecDot_self_nonneg _)

end Carrier

/-! ### The Step-3 comparison at a fixed realization -/

section Comparison

variable {d : ℕ}

/-- **Step 3 of `l.corrector.limit` at a fixed realization**.

Let `N` be the gradient of the `H¹(U)` solution of `-Δw = ∇·F` with the natural
boundary condition, i.e. `N` is a potential field with `N + F` solenoidal with
vanishing normal trace, and let `J` be *any* admissible Neumann competitor,
`J ∈ L²_{sol,0}(U)`.  Then

`∫_U |N|² ≤ ∫_U |J - F|²`.

Equivalently, `N + F` is the projection of `F`-shifted admissible fluxes: the
Neumann energy is minimal among the fluxes of `L²_{sol,0}(U)`.  With
`J = j_{K,L}` and `F = f` the right-hand side is `∫_U |j_{K,L} - f|²`, which the
approximation lemma drives to `∫_U |∇w|²`.

The proof is the paper's, in variational form: the two weak formulations give
`∫_U (J - F) · N = ∫_U |N|²`, and the conclusion is `0 ≤ ∫_U |(J - F) - N|²`.
Only the weak formulations and square integrability are used; no boundary
regularity, no approximation lemma and no probability. -/
theorem setIntegral_vecDot_self_le_of_isSolenoidalZeroNormalTraceOn {U : Set (Vec d)}
    {N F J : Vec d → Vec d} (hN : MemVectorL2 U N) (hF : MemVectorL2 U F)
    (hJ : MemVectorL2 U J) (hNpot : IsPotentialOn U N)
    (hNsol : IsSolenoidalZeroNormalTraceOn U fun x => N x + F x)
    (hJsol : IsSolenoidalZeroNormalTraceOn U J) :
    (∫ x in U, vecDot (N x) (N x))
      ≤ ∫ x in U, vecDot (J x - F x) (J x - F x) := by
  have hW : MemVectorL2 U fun x => J x - F x := hJ.sub hF
  have hNN : IntegrableOn (fun x => vecDot (N x) (N x)) U :=
    integrableOn_vecDot_of_memVectorL2 hN hN
  have hFN : IntegrableOn (fun x => vecDot (F x) (N x)) U :=
    integrableOn_vecDot_of_memVectorL2 hF hN
  have hJN : IntegrableOn (fun x => vecDot (J x) (N x)) U :=
    integrableOn_vecDot_of_memVectorL2 hJ hN
  have hWN : IntegrableOn (fun x => vecDot (J x - F x) (N x)) U :=
    integrableOn_vecDot_of_memVectorL2 hW hN
  have hWW : IntegrableOn (fun x => vecDot (J x - F x) (J x - F x)) U :=
    integrableOn_vecDot_of_memVectorL2 hW hW
  -- `⨍ (N + F) · N = 0`: the natural boundary condition tested against `N`.
  have hNself : (∫ x in U, vecDot (N x) (N x)) + ∫ x in U, vecDot (F x) (N x) = 0 := by
    have hsplit : ∫ x in U, vecDot (N x + F x) (N x)
        = (∫ x in U, vecDot (N x) (N x)) + ∫ x in U, vecDot (F x) (N x) := by
      rw [← integral_add hNN hFN]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => vecDot_add_left _ _ _)
    rw [← hsplit]
    exact setIntegral_vecDot_eq_zero_of_isSolenoidalZeroNormalTraceOn hNsol hNpot
  -- `⨍ j_{K,L} · N = 0`: the competitor is admissible for the same test class.
  have hJzero : ∫ x in U, vecDot (J x) (N x) = 0 :=
    setIntegral_vecDot_eq_zero_of_isSolenoidalZeroNormalTraceOn hJsol hNpot
  have hWNval : ∫ x in U, vecDot (J x - F x) (N x) = ∫ x in U, vecDot (N x) (N x) := by
    have hsplit : ∫ x in U, vecDot (J x - F x) (N x)
        = (∫ x in U, vecDot (J x) (N x)) - ∫ x in U, vecDot (F x) (N x) := by
      rw [← integral_sub hJN hFN]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => vecDot_sub_left _ _ _)
    rw [hsplit, hJzero]
    linarith [hNself]
  -- Expand the squared distance between the Neumann gradient and the competitor flux.
  have hnn : 0 ≤ ∫ x in U, vecDot (J x - F x - N x) (J x - F x - N x) :=
    integral_nonneg fun x => vecDot_self_nonneg _
  have hexp : ∫ x in U, vecDot (J x - F x - N x) (J x - F x - N x)
      = (∫ x in U, vecDot (J x - F x) (J x - F x))
        - 2 * (∫ x in U, vecDot (J x - F x) (N x)) + ∫ x in U, vecDot (N x) (N x) := by
    have hpt : ∀ x, vecDot (J x - F x - N x) (J x - F x - N x)
        = vecDot (J x - F x) (J x - F x) - 2 * vecDot (J x - F x) (N x)
          + vecDot (N x) (N x) := fun x => vecDot_sub_self _ _
    have h1 : ∫ x in U, (vecDot (J x - F x) (J x - F x)
          - 2 * vecDot (J x - F x) (N x) + vecDot (N x) (N x))
        = (∫ x in U, (vecDot (J x - F x) (J x - F x)
            - 2 * vecDot (J x - F x) (N x))) + ∫ x in U, vecDot (N x) (N x) :=
      integral_add (hWW.sub (hWN.const_mul 2)) hNN
    have h2 : ∫ x in U, (vecDot (J x - F x) (J x - F x) - 2 * vecDot (J x - F x) (N x))
        = (∫ x in U, vecDot (J x - F x) (J x - F x))
          - ∫ x in U, 2 * vecDot (J x - F x) (N x) :=
      integral_sub hWW (hWN.const_mul 2)
    have h3 : ∫ x in U, 2 * vecDot (J x - F x) (N x)
        = 2 * ∫ x in U, vecDot (J x - F x) (N x) := integral_const_mul 2 _
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), h1, h2, h3]
  rw [hexp, hWNval] at hnn
  linarith

end Comparison

/-! ### The per-sample Young split of the Neumann energy -/

section Sample

variable {d : ℕ} {Ω : Type*} [AddAction (Vec d) Ω]

/-- **The Step-3 comparison after the Young split, at a fixed sample.**

For the Neumann gradient `N` on the cube, an admissible competitor
`J ∈ L²_{sol,0}(cu_K)`, and every `δ > 0`,

`⨍|N|² ≤ (1+δ) ⨍|∇w|² + (1+δ⁻¹) ⨍|J - j|²`,

where `j = ∇w + f` is the stationary flux and all fields are the spatial
realizations at the sample `ω`.  This is the manuscript's Step 3 with the Hölder
step and the subsequent absorption replaced by a pointwise Young inequality; see
the module docstring. -/
theorem cubeAverage_vecDot_self_le_young (Q : TriadicCube d) {δ : ℝ} (hδ : 0 < δ)
    {f p j : Ω → HilbertVec d} {Nω Jω : Vec d → Vec d} {ω : Ω}
    (hjdef : ∀ ω' : Ω, j ω' = p ω' + f ω')
    (hfω : MemHilbertVectorL2 (cubeSet Q) (realize f ω))
    (hpω : MemHilbertVectorL2 (cubeSet Q) (realize p ω))
    (hEω : MemHilbertVectorL2 (cubeSet Q)
      fun x => HilbertVec.ofVec (Jω x) - realize j ω x)
    (hNpot : IsPotentialOn (openCubeSet Q) Nω)
    (hNsol : IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      fun x => Nω x + (realize f ω x).toVec)
    (hJsol : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) Jω) :
    cubeAverage Q (fun x => vecDot (Nω x) (Nω x))
      ≤ (1 + δ) * cubeAverage Q (fun x => ‖realize p ω x‖ ^ 2)
        + (1 + δ⁻¹) * cubeAverage Q
            (fun x => ‖HilbertVec.ofVec (Jω x) - realize j ω x‖ ^ 2) := by
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
  have hEU : MemHilbertVectorL2 U
      fun x => HilbertVec.ofVec (Jω x) - realize j ω x := by
    have h : MemLp (fun x => HilbertVec.ofVec (Jω x) - realize j ω x) 2
        (volume.restrict (cubeSet Q)) := hEω
    rwa [hres] at h
  have hFU : MemVectorL2 U fun x => (realize f ω x).toVec :=
    memVectorL2_toVec_of_memHilbertVectorL2 hfU
  have hNU : MemVectorL2 U Nω := memVectorL2_of_isPotentialOn hNpot
  -- The competitor flux is the stationary corrector gradient plus the error.
  have hjr : ∀ x : Vec d, realize j ω x = realize p ω x + realize f ω x := fun x =>
    hjdef (x +ᵥ ω)
  have hpt : ∀ x : Vec d, HilbertVec.ofVec (Jω x - (realize f ω x).toVec)
      = realize p ω x + (HilbertVec.ofVec (Jω x) - realize j ω x) := by
    intro x
    rw [ofVec_sub', HilbertVec.ofVec_toVec, hjr x]
    abel
  have hWeq : (fun x => Jω x - (realize f ω x).toVec)
      = fun x => (realize p ω x + (HilbertVec.ofVec (Jω x) - realize j ω x)).toVec := by
    funext x
    rw [← hpt x, HilbertVec.toVec_ofVec]
  have hWU : MemVectorL2 U fun x => Jω x - (realize f ω x).toVec := by
    rw [hWeq]
    exact memVectorL2_toVec_of_memHilbertVectorL2 (hpU.add hEU)
  have hJU : MemVectorL2 U Jω := by
    have hEq : Jω = fun x => (Jω x - (realize f ω x).toVec) + (realize f ω x).toVec := by
      funext x
      abel
    rw [hEq]
    exact hWU.add hFU
  -- Step 3 in flux form on the open cube.
  have hcomp := setIntegral_vecDot_self_le_of_isSolenoidalZeroNormalTraceOn
    hNU hFU hJU hNpot hNsol hJsol
  -- Young split of the competitor flux.
  have hsq : ∀ x : Vec d,
      vecDot (Jω x - (realize f ω x).toVec) (Jω x - (realize f ω x).toVec)
        = ‖realize p ω x + (HilbertVec.ofVec (Jω x) - realize j ω x)‖ ^ 2 := by
    intro x
    rw [← norm_sq_ofVec, hpt x]
  have hyoung : ∫ x in U, vecDot (Jω x - (realize f ω x).toVec)
        (Jω x - (realize f ω x).toVec)
      ≤ (1 + δ) * (∫ x in U, ‖realize p ω x‖ ^ 2)
        + (1 + δ⁻¹) * ∫ x in U, ‖HilbertVec.ofVec (Jω x) - realize j ω x‖ ^ 2 := by
    have hlhs : IntegrableOn (fun x => vecDot (Jω x - (realize f ω x).toVec)
        (Jω x - (realize f ω x).toVec)) U :=
      integrableOn_vecDot_of_memVectorL2 hWU hWU
    have hPint : IntegrableOn (fun x => ‖realize p ω x‖ ^ 2) U :=
      (memLp_two_iff_integrable_sq_norm hpU.aestronglyMeasurable).1 hpU
    have hEint : IntegrableOn
        (fun x => ‖HilbertVec.ofVec (Jω x) - realize j ω x‖ ^ 2) U :=
      (memLp_two_iff_integrable_sq_norm hEU.aestronglyMeasurable).1 hEU
    have hmono : ∫ x in U, vecDot (Jω x - (realize f ω x).toVec)
          (Jω x - (realize f ω x).toVec)
        ≤ ∫ x in U, ((1 + δ) * ‖realize p ω x‖ ^ 2
            + (1 + δ⁻¹) * ‖HilbertVec.ofVec (Jω x) - realize j ω x‖ ^ 2) := by
      refine integral_mono hlhs ((hPint.const_mul _).add (hEint.const_mul _)) ?_
      intro x
      show vecDot (Jω x - (realize f ω x).toVec) (Jω x - (realize f ω x).toVec)
          ≤ (1 + δ) * ‖realize p ω x‖ ^ 2
            + (1 + δ⁻¹) * ‖HilbertVec.ofVec (Jω x) - realize j ω x‖ ^ 2
      rw [hsq x]
      exact normSq_add_le_young hδ _ _
    refine hmono.trans (le_of_eq ?_)
    rw [integral_add (hPint.const_mul _) (hEint.const_mul _), integral_const_mul,
      integral_const_mul]
  have hcombine : (∫ x in U, vecDot (Nω x) (Nω x))
      ≤ (1 + δ) * (∫ x in U, ‖realize p ω x‖ ^ 2)
        + (1 + δ⁻¹) * ∫ x in U, ‖HilbertVec.ofVec (Jω x) - realize j ω x‖ ^ 2 :=
    hcomp.trans hyoung
  have hvol : (0 : ℝ) < (cubeVolume Q)⁻¹ := inv_pos.2 (cubeVolume_pos Q)
  have hscaled := mul_le_mul_of_nonneg_left hcombine hvol.le
  simp only [cubeAverage]
  rw [hres]
  linarith [hscaled]

end Sample

/-! ### The expected Neumann energy at a fixed scale -/

section Expectation

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- **The expected Step-3 comparison at a fixed cube.**  Integrating
`cubeAverage_vecDot_self_le_young` over the sample space and applying the
stationary transfer turns the realized cube average of `|∇w|²` into the
expectation `E[|∇w|²]`.

`hNint` is the sample-integrability of the Neumann cube energy: it is what makes
the left-hand side the expectation of `e.corrector.limit` rather than the
Bochner junk value `0`.  It is the Neumann counterpart of the `hDint`
hypothesis of the Dirichlet half and is a regularity condition on the given
solution family, not a step of the proof. -/
theorem integral_cubeAverage_vecDot_self_le (Q : TriadicCube d) {δ : ℝ} (hδ : 0 < δ)
    {f p j : Ω → HilbertVec d} (hfm : StronglyMeasurable f) (hf : MemLp f 2 μ)
    (hpm : StronglyMeasurable p) (hp : MemLp p 2 μ)
    (hjdef : ∀ ω : Ω, j ω = p ω + f ω)
    {Nfam Jfam : Ω → (Vec d → Vec d)}
    (hNpot : ∀ᵐ ω ∂μ, IsPotentialOn (openCubeSet Q) (Nfam ω))
    (hNsol : ∀ᵐ ω ∂μ, IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      fun x => Nfam ω x + (realize f ω x).toVec)
    (hJsol : ∀ᵐ ω ∂μ, IsSolenoidalZeroNormalTraceOn (openCubeSet Q) (Jfam ω))
    (hJmem : ∀ᵐ ω ∂μ, MemLp (fun x => HilbertVec.ofVec (Jfam ω x) - realize j ω x) 2
      (volume.restrict (cubeSet Q)))
    (hNint : Integrable
      (fun ω => cubeAverage Q fun x => vecDot (Nfam ω x) (Nfam ω x)) μ)
    (hEint : Integrable (fun ω => cubeLpNorm Q 2
      (fun x => HilbertVec.ofVec (Jfam ω x) - realize j ω x) ^ (2 : ℝ)) μ) :
    (∫ ω, cubeAverage Q (fun x => vecDot (Nfam ω x) (Nfam ω x)) ∂μ)
      ≤ (1 + δ) * (∫ ω, ‖p ω‖ ^ 2 ∂μ)
        + (1 + δ⁻¹) * ∫ ω, cubeLpNorm Q 2
            (fun x => HilbertVec.ofVec (Jfam ω x) - realize j ω x) ^ (2 : ℝ) ∂μ := by
  classical
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  set A : Ω → ℝ := fun ω => cubeAverage Q fun x => ‖realize p ω x‖ ^ 2 with hAdef
  set C : Ω → ℝ := fun ω => cubeAverage Q
    fun x => ‖HilbertVec.ofVec (Jfam ω x) - realize j ω x‖ ^ 2 with hCdef
  have hAint : Integrable A μ := by
    have := (integrable_setIntegral_normSq_realize (μ := μ) hQfin hpm hp).const_mul
      (cubeVolume Q)⁻¹
    simpa [hAdef, cubeAverage] using this
  have hCeq : ∀ᵐ ω ∂μ, cubeLpNorm Q 2
      (fun x => HilbertVec.ofVec (Jfam ω x) - realize j ω x) ^ (2 : ℝ) = C ω := by
    filter_upwards [hJmem] with ω hω
    exact cubeLpNorm_two_rpow_eq_cubeAverage_norm_sq hω
  have hCint : Integrable C μ := hEint.congr hCeq
  have hae : ∀ᵐ ω ∂μ, cubeAverage Q (fun x => vecDot (Nfam ω x) (Nfam ω x))
      ≤ (1 + δ) * A ω + (1 + δ⁻¹) * C ω := by
    filter_upwards [hNpot, hNsol, hJsol, hJmem,
      ae_memHilbertVectorL2_realize (μ := μ) Q hfm hf,
      ae_memHilbertVectorL2_realize (μ := μ) Q hpm hp] with ω h1 h2 h3 h4 hfω hpω
    exact cubeAverage_vecDot_self_le_young Q hδ hjdef hfω hpω h4 h1 h2 h3
  have hmono : (∫ ω, cubeAverage Q (fun x => vecDot (Nfam ω x) (Nfam ω x)) ∂μ)
      ≤ ∫ ω, ((1 + δ) * A ω + (1 + δ⁻¹) * C ω) ∂μ :=
    integral_mono_ae hNint
      ((hAint.const_mul (1 + δ)).add (hCint.const_mul (1 + δ⁻¹))) hae
  have hRHS : ∫ ω, ((1 + δ) * A ω + (1 + δ⁻¹) * C ω) ∂μ
      = (1 + δ) * (∫ ω, A ω ∂μ) + (1 + δ⁻¹) * ∫ ω, C ω ∂μ := by
    rw [integral_add (hAint.const_mul (1 + δ)) (hCint.const_mul (1 + δ⁻¹)),
      integral_const_mul, integral_const_mul]
  have hA : ∫ ω, A ω ∂μ = ∫ ω, ‖p ω‖ ^ 2 ∂μ :=
    integral_cubeAverage_normSq_realize (μ := μ) Q hpm hp
  have hC : ∫ ω, C ω ∂μ = ∫ ω, cubeLpNorm Q 2
      (fun x => HilbertVec.ofVec (Jfam ω x) - realize j ω x) ^ (2 : ℝ) ∂μ :=
    (integral_congr_ae hCeq).symm
  rw [hRHS, hA, hC] at hmono
  exact hmono

end Expectation

section Assembly

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

end Assembly

end

end Algsuperdiff.Section3.Provider.Corrector
