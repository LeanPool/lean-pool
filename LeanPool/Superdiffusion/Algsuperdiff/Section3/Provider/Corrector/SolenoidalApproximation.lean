/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.PotentialApproximation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.SolenoidalStream

/-!
# SolenoidalApproximation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the cutoff core of the solenoidal half of the local-approximation lemma

This file builds the local approximants of part (ii) of
`l.approximation.stationary.by.local` and proves the approximation estimate

> **(ii) Solenoidal approximation.**  For every `L ∈ ℕ` there exists a family
> `{j_{K,L}}_{K ∈ ℕ}` with `j_{K,L} ∈ L²_{sol,0}(cu_K)` such that
> `limsup_{K→∞} E[ ‖j_{K,L} − j‖²_{L²(cu_K)} ] ≤ C 3^{−L} E[|j|²]`.

The proof is the structural mirror of the potential half
(`Algsuperdiff/Section3/Provider/Corrector/PotentialApproximation.lean`): the
same cutoff `η_{K,L}`, the same boundary strip `Σ_{K,L}`, the same
`e.boundary.strip.volume` bookkeeping and the same `3^{2(L−K)}` crush of the
second error term.  Only the competitor changes: the paper sets

`j_{K,L,i} := Σ_m ∂_m ( η_{K,L} (S_{im} − (S_{im})_{cu_K}) )`

for an antisymmetric stream tensor `S` with `j_i = Σ_m ∂_m S_{im}`, and expands

`j_{K,L} − j = (η_{K,L} − 1) j + Σ_m (S_{im} − (S_{im})_{cu_K}) ∂_m η_{K,L}`

The membership
`j_{K,L} ∈ L²_{sol,0}(cu_K)` and this error display are supplied unconditionally
by `Algsuperdiff/Section3/Provider/Corrector/SolenoidalStream.lean`
(`isSolenoidalZeroNormalTraceOn_cutoffStream`,
`streamDivergence_cutoffStream_apply`); what is proved here is the analytic
estimate on the two error terms.

**The stream is a disclosed input.**  Exactly as part (i) is proved here for a
*stationary square-integrable primitive* `φ` before being lifted to the whole
potential subspace in
`Algsuperdiff/Section3/Provider/Corrector/ApproximationAssembly.lean`, part (ii)
is proved here for a *stationary square-integrable stream* `S`, entered as three
explicitly named hypotheses `hstreamSmooth`, `hstreamAnti`, `hstreamDiv`.  The
Ω-level stream itself is not constructed in this file and does not yet exist in
the repository; the assembling theorem
`exists_isSolenoidalZeroNormalTraceOn_limsup_le_of_stationaryStream` is therefore
**conditional** and claims no node status.  What is *not* assumed anywhere below
is the conclusion: neither the approximation estimate nor membership in
`L²_{sol,0}(cu_K)` appears as a hypothesis.

For a stationary square-integrable stream no cube average has to be subtracted
and no sublinearity input is used: the paper's `(S)_{cu_K}` is taken to be `0`
and the second error term is bounded by `‖∇η_{K,L}‖²_∞ E[|S|²] ≍ 3^{2(L−K)}
E[|S|²]`, which already tends to `0` as `K → ∞` at fixed `L` because `E[|S|²]`
is finite.  The representation leg — the existence of such an `S` — is the hard
input recorded, and it is precisely what is disclosed rather than proved here.

A vanishing-invariant-part condition is therefore necessary.  Here it is *not*
a separate assumption: it is carried by `hstreamDiv` together with the
stationarity and square integrability of `S`, which force `E[j] = 0` and hence
are unsatisfiable for a nonzero constant `j`.  The mechanism is the one
displayed: pairing the divergence identity with a compactly supported test
function and using `∫ ∂_m ψ = 0` kills the mean.  The implication is stated but
**not proved** in this file; what is proved is its shadow at the competitors,
`setIntegral_coord_localStreamApprox_eq_zero`.  See the note on
`exists_isSolenoidalZeroNormalTraceOn_limsup_le_of_stationaryStream`.

**Disclosure.**  Nothing in this file realizes any source node.  The main
theorem is conditional on an Ω-level antisymmetric stream that the repository
does not yet provide.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

noncomputable section

/-! ### Coordinatewise sums in the Euclidean carrier -/

section SumApply

variable {d : ℕ}

/-- Coordinates of a finite sum in `HilbertVec d`.  The usual `Pi` lemma does not
fire on `PiLp`, whose algebraic operations are wrapped. -/
theorem hilbertVec_sum_apply {ι : Type*} (s : Finset ι) (f : ι → HilbertVec d) (i : Fin d) :
    (∑ m ∈ s, f m) i = ∑ m ∈ s, f m i := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a t ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]

end SumApply

/-! ### The stream tensor and its realization -/

section Realization

variable {d : ℕ} {Ω : Type*} [AddAction (Vec d) Ω]

/-- The spatial realization of an Ω-level stream tensor, in the index shape
`(i, m) ↦ (x ↦ S_{im}(x))` consumed by
`Algsuperdiff.Section3.Provider.Corrector.streamDivergence`.

The Ω-level carrier is `Ω → (Fin d → HilbertVec d)`: the value `S ω m` is the
`m`-th *column* of the stream matrix, so the entry `S_{im}` of ABK26 is `(S ω m)
i`.  This presentation keeps the paper's remainder `Σ_m (∂_m η) S_{im}` a finite
sum of scalar multiples of vectors of the Euclidean carrier, with no
coordinatewise repackaging. -/
def streamRealization (S : Ω → (Fin d → HilbertVec d)) (ω : Ω) :
    Fin d → Fin d → (Vec d → ℝ) :=
  fun i m x => realize S ω x m i

theorem streamRealization_apply (S : Ω → (Fin d → HilbertVec d)) (ω : Ω) (i m : Fin d)
    (x : Vec d) : streamRealization S ω i m x = realize S ω x m i := rfl

end Realization

/-! ### The local approximant and its error -/

section Approximant

variable {d : ℕ} {Ω : Type*} [AddAction (Vec d) Ω]

/-- The paper's remainder `r_{K,L}` of ABK26, i.e. the field `x ↦ (Σ_m (∂_m
η_{K,L})(x) S_{im}(x))_i`, written as a finite combination of the columns of the
stream. -/
def streamRemainder (Q : TriadicCube d) (L : ℕ) (S : Ω → (Fin d → HilbertVec d)) (ω : Ω)
    (x : Vec d) : HilbertVec d :=
  ∑ m : Fin d, fderiv ℝ (approxCutoff Q L).toFun x (basisVec m) • realize S ω x m

theorem streamRemainder_apply (Q : TriadicCube d) (L : ℕ)
    (S : Ω → (Fin d → HilbertVec d)) (ω : Ω) (x : Vec d) (i : Fin d) :
    streamRemainder Q L S ω x i
      = ∑ m : Fin d, fderiv ℝ (approxCutoff Q L).toFun x (basisVec m)
          * streamRealization S ω i m x := by
  rw [streamRemainder, hilbertVec_sum_apply]
  exact Finset.sum_congr rfl fun m _ => by
    rw [PiLp.smul_apply, smul_eq_mul, streamRealization_apply]

/-- The paper's local competitor
`j_{K,L,i} = Σ_m ∂_m ( η_{K,L} (S_{im} − (S_{im})_{cu_K}) )`, expanded by the
product rule with the cube average taken to be `0`.  It is defined by this
formula for *every* sample, so that it is jointly measurable without any
smoothness assumption; whenever the realization of `S` really is a smooth
antisymmetric stream for the realization of `j` it is an element of
`L²_{sol,0}(cu_K)` (`isSolenoidalZeroNormalTraceOn_localStreamApprox`). -/
def localStreamApprox (Q : TriadicCube d) (L : ℕ) (S : Ω → (Fin d → HilbertVec d))
    (j : Ω → HilbertVec d) (ω : Ω) : Vec d → Vec d :=
  fun x i => (approxCutoff Q L).toFun x * (realize j ω x).toVec i
    + streamRemainder Q L S ω x i

/-- **The error decomposition of part (ii)**, in the shape of the potential
display: `j_{K,L} − j = (η_{K,L} − 1) j + r_{K,L}`. -/
theorem ofVec_localStreamApprox_sub_realize (Q : TriadicCube d) (L : ℕ)
    (S : Ω → (Fin d → HilbertVec d)) (j : Ω → HilbertVec d) (ω : Ω) (x : Vec d) :
    HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x
      = ((approxCutoff Q L).toFun x - 1) • realize j ω x + streamRemainder Q L S ω x := by
  ext i
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    localStreamApprox, HilbertVec.toVec]
  ring

/-- Each coordinate derivative of the localization cutoff is bounded by the
gradient bound `C(d) 3^{L−K}`. -/
theorem abs_fderiv_approxCutoff_le (Q : TriadicCube d) (L : ℕ) (x : Vec d) (m : Fin d) :
    |fderiv ℝ (approxCutoff Q L).toFun x (basisVec m)| ≤ gradBound Q L := by
  have hcoord : |cutoffHilbertGrad Q L x m| ≤ ‖cutoffHilbertGrad Q L x‖ :=
    HilbertVec.abs_apply_le_norm _ m
  have hval : cutoffHilbertGrad Q L x m = fderiv ℝ (approxCutoff Q L).toFun x (basisVec m) := rfl
  rw [hval] at hcoord
  exact hcoord.trans (norm_cutoffHilbertGrad_le Q L x)

/-- **The gradient leg of the error bound.**  The paper's remainder obeys
`|r_{K,L}| ≤ d ‖∇η_{K,L}‖_∞ |S|` pointwise, which is the solenoidal analogue of
the second display of ABK26. -/
theorem norm_streamRemainder_le (Q : TriadicCube d) (L : ℕ)
    (S : Ω → (Fin d → HilbertVec d)) (ω : Ω) (x : Vec d) :
    ‖streamRemainder Q L S ω x‖ ≤ (d : ℝ) * gradBound Q L * ‖realize S ω x‖ := by
  classical
  have hterm : ∀ m : Fin d,
      ‖fderiv ℝ (approxCutoff Q L).toFun x (basisVec m) • realize S ω x m‖
        ≤ gradBound Q L * ‖realize S ω x‖ := by
    intro m
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (abs_fderiv_approxCutoff_le Q L x m)
      (norm_le_pi_norm (realize S ω x) m) (norm_nonneg _) (gradBound_nonneg Q L)
  calc ‖streamRemainder Q L S ω x‖
      ≤ ∑ m : Fin d, ‖fderiv ℝ (approxCutoff Q L).toFun x (basisVec m) • realize S ω x m‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _m : Fin d, gradBound Q L * ‖realize S ω x‖ :=
        Finset.sum_le_sum fun m _ => hterm m
    _ = (d : ℝ) * gradBound Q L * ‖realize S ω x‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **The competitor is admissible**: `j_{K,L} ∈ L²_{sol,0}(cu_K)`, by
`isSolenoidalZeroNormalTraceOn_cutoffStream` at the cube average `0`.

The three hypotheses are the disclosed per-sample stream data: smoothness,
antisymmetry `S_{im} = −S_{mi}`, and the representation `j_i = Σ_m ∂_m S_{im}`. -/
theorem isSolenoidalZeroNormalTraceOn_localStreamApprox (Q : TriadicCube d) (L : ℕ)
    {S : Ω → (Fin d → HilbertVec d)} {j : Ω → HilbertVec d} {ω : Ω}
    (hsmooth : ∀ i m, ContDiff ℝ (⊤ : ℕ∞) (streamRealization S ω i m))
    (hanti : ∀ i m, streamRealization S ω m i = -streamRealization S ω i m)
    (hdiv : ∀ x : Vec d, streamDivergence (streamRealization S ω) x = (realize j ω x).toVec) :
    IsSolenoidalZeroNormalTraceOn (openCubeSet Q) (localStreamApprox Q L S j ω) := by
  have hbase : IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (streamDivergence (cutoffStream (approxCutoff Q L).toFun (streamRealization S ω) 0)) :=
    isSolenoidalZeroNormalTraceOn_cutoffStream (approxCutoff Q L).smooth
      (approxCutoff Q L).hasCompactSupport (approxCutoff_tsupport_subset Q L)
      hsmooth hanti (fun i m => by simp)
  refine (show streamDivergence
      (cutoffStream (approxCutoff Q L).toFun (streamRealization S ω) 0)
      = localStreamApprox Q L S j ω from ?_) ▸ hbase
  funext x i
  have hη : DifferentiableAt ℝ (approxCutoff Q L).toFun x :=
    ((approxCutoff Q L).smooth.differentiable (by simp)).differentiableAt
  have hS : ∀ a b : Fin d, DifferentiableAt ℝ (streamRealization S ω a b) x := fun a b =>
    (((hsmooth a b).differentiable (by simp))).differentiableAt
  rw [streamDivergence_cutoffStream_apply hη hS i, hdiv x]
  simp only [localStreamApprox, streamRemainder_apply, Pi.zero_apply, sub_zero, coordDeriv]

/-- **Pointwise error bound.**  On the cube the local approximation error is
controlled by the boundary strip and by the stream, exactly as in the two
displays of ABK26 transported to part (ii). -/
theorem norm_sq_localStreamApprox_sub_le (Q : TriadicCube d) (L : ℕ)
    (S : Ω → (Fin d → HilbertVec d)) (j : Ω → HilbertVec d) (ω : Ω) {x : Vec d}
    (hx : x ∈ cubeSet Q) :
    ‖HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x‖ ^ 2
      ≤ 2 * (cubeSet Q \ scaledClosedCubeSet Q (cutoffInnerRatio L)).indicator
            (fun y => ‖realize j ω y‖ ^ 2) x
        + 2 * ((d : ℝ) * gradBound Q L) ^ 2 * ‖realize S ω x‖ ^ 2 := by
  have hdec := ofVec_localStreamApprox_sub_realize Q L S j ω x
  have hgb0 : (0 : ℝ) ≤ (d : ℝ) * gradBound Q L :=
    mul_nonneg (Nat.cast_nonneg d) (gradBound_nonneg Q L)
  have hsecond := norm_streamRemainder_le Q L S ω x
  by_cases hmem : x ∈ scaledClosedCubeSet Q (cutoffInnerRatio L)
  · have hone : (approxCutoff Q L).toFun x = 1 := (approxCutoff Q L).eq_one_on_inner x hmem
    have hind : (cubeSet Q \ scaledClosedCubeSet Q (cutoffInnerRatio L)).indicator
        (fun y => ‖realize j ω y‖ ^ 2) x = 0 :=
      Set.indicator_of_notMem (fun h => h.2 hmem) _
    have hle : ‖HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x‖
        ≤ (d : ℝ) * gradBound Q L * ‖realize S ω x‖ := by
      rw [hdec, hone]
      simpa using hsecond
    rw [hind]
    nlinarith [hle, norm_nonneg (HilbertVec.ofVec (localStreamApprox Q L S j ω x)
      - realize j ω x), mul_nonneg hgb0 (norm_nonneg (realize S ω x))]
  · have hxmem : x ∈ cubeSet Q \ scaledClosedCubeSet Q (cutoffInnerRatio L) :=
      Set.mem_sdiff_of_mem hx hmem
    have hind : (cubeSet Q \ scaledClosedCubeSet Q (cutoffInnerRatio L)).indicator
        (fun y => ‖realize j ω y‖ ^ 2) x = ‖realize j ω x‖ ^ 2 :=
      Set.indicator_of_mem hxmem _
    have hcut : ‖(approxCutoff Q L).toFun x - 1‖ ≤ 1 := by
      have h0 := (approxCutoff Q L).nonneg x
      have h1 := (approxCutoff Q L).le_one x
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hfirst : ‖((approxCutoff Q L).toFun x - 1) • realize j ω x‖ ≤ ‖realize j ω x‖ := by
      rw [norm_smul]
      calc ‖(approxCutoff Q L).toFun x - 1‖ * ‖realize j ω x‖
          ≤ 1 * ‖realize j ω x‖ := mul_le_mul_of_nonneg_right hcut (norm_nonneg _)
        _ = ‖realize j ω x‖ := one_mul _
    have hle : ‖HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x‖
        ≤ ‖realize j ω x‖ + (d : ℝ) * gradBound Q L * ‖realize S ω x‖ := by
      rw [hdec]
      exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)
    rw [hind]
    nlinarith [hle, norm_nonneg (HilbertVec.ofVec (localStreamApprox Q L S j ω x)
      - realize j ω x), mul_nonneg hgb0 (norm_nonneg (realize S ω x)),
      norm_nonneg (realize j ω x),
      sq_nonneg (‖realize j ω x‖ - (d : ℝ) * gradBound Q L * ‖realize S ω x‖)]

end Approximant

/-! ### Measurability of the competitor -/

section Measurability

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable [MeasurableVAdd₂ (Vec d) Ω]

/-- The paper's remainder is strongly measurable in space, for every sample. -/
theorem stronglyMeasurable_streamRemainder (Q : TriadicCube d) (L : ℕ)
    {S : Ω → (Fin d → HilbertVec d)} (hSm : StronglyMeasurable S) (ω : Ω) :
    StronglyMeasurable (streamRemainder Q L S ω) := by
  classical
  show StronglyMeasurable fun x : Vec d => ∑ m : Fin d,
    fderiv ℝ (approxCutoff Q L).toFun x (basisVec m) • realize S ω x m
  refine Finset.stronglyMeasurable_fun_sum _ fun m _ => ?_
  exact ((((approxCutoff Q L).smooth.continuous_fderiv (by simp)).clm_apply
      continuous_const).stronglyMeasurable).smul
    ((continuous_apply m).comp_stronglyMeasurable (stronglyMeasurable_realize hSm ω))

/-- The paper's remainder is jointly strongly measurable in the sample and in
space. -/
theorem stronglyMeasurable_uncurry_streamRemainder (Q : TriadicCube d) (L : ℕ)
    {S : Ω → (Fin d → HilbertVec d)} (hSm : StronglyMeasurable S) :
    StronglyMeasurable fun z : Ω × Vec d => streamRemainder Q L S z.1 z.2 := by
  classical
  show StronglyMeasurable fun z : Ω × Vec d => ∑ m : Fin d,
    fderiv ℝ (approxCutoff Q L).toFun z.2 (basisVec m) • realize S z.1 z.2 m
  refine Finset.stronglyMeasurable_fun_sum _ fun m _ => ?_
  exact (((((approxCutoff Q L).smooth.continuous_fderiv (by simp)).clm_apply
      continuous_const).stronglyMeasurable).comp_measurable measurable_snd).smul
    ((continuous_apply m).comp_stronglyMeasurable
      (stronglyMeasurable_uncurry_realize hSm))

/-- The approximation error is a strongly measurable field for every sample. -/
theorem stronglyMeasurable_localStreamApprox_sub (Q : TriadicCube d) (L : ℕ)
    {S : Ω → (Fin d → HilbertVec d)} {j : Ω → HilbertVec d}
    (hSm : StronglyMeasurable S) (hjm : StronglyMeasurable j) (ω : Ω) :
    StronglyMeasurable
      (fun x => HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x) := by
  have hrw : (fun x => HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x)
      = fun x => ((approxCutoff Q L).toFun x - 1) • realize j ω x
        + streamRemainder Q L S ω x :=
    funext fun x => ofVec_localStreamApprox_sub_realize Q L S j ω x
  rw [hrw]
  exact (((approxCutoff Q L).smooth.continuous.sub continuous_const).stronglyMeasurable.smul
    (stronglyMeasurable_realize hjm ω)).add (stronglyMeasurable_streamRemainder Q L hSm ω)

/-- The approximation error is jointly strongly measurable. -/
theorem stronglyMeasurable_uncurry_localStreamApprox_sub (Q : TriadicCube d) (L : ℕ)
    {S : Ω → (Fin d → HilbertVec d)} {j : Ω → HilbertVec d}
    (hSm : StronglyMeasurable S) (hjm : StronglyMeasurable j) :
    StronglyMeasurable fun z : Ω × Vec d =>
      HilbertVec.ofVec (localStreamApprox Q L S j z.1 z.2) - realize j z.1 z.2 := by
  have hrw : (fun z : Ω × Vec d =>
      HilbertVec.ofVec (localStreamApprox Q L S j z.1 z.2) - realize j z.1 z.2)
      = fun z : Ω × Vec d => ((approxCutoff Q L).toFun z.2 - 1) • realize j z.1 z.2
        + streamRemainder Q L S z.1 z.2 :=
    funext fun z => ofVec_localStreamApprox_sub_realize Q L S j z.1 z.2
  rw [hrw]
  refine StronglyMeasurable.add ?_ (stronglyMeasurable_uncurry_streamRemainder Q L hSm)
  exact ((((approxCutoff Q L).smooth.continuous.sub
    continuous_const).stronglyMeasurable).comp_measurable measurable_snd).smul
    (stronglyMeasurable_uncurry_realize hjm)

end Measurability

/-! ### The expected error at a fixed cube -/

section Estimate

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- The expected squared error over a fixed cube, before normalization. -/
theorem integral_setIntegral_normSq_localStreamApprox_sub_le (Q : TriadicCube d) (L : ℕ)
    {S : Ω → (Fin d → HilbertVec d)} {j : Ω → HilbertVec d}
    (hSm : StronglyMeasurable S) (hS : MemLp S 2 μ)
    (hjm : StronglyMeasurable j) (hj : MemLp j 2 μ) :
    ∫ ω, (∫ x in cubeSet Q,
        ‖HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x‖ ^ 2) ∂μ
      ≤ 2 * ((volume (boundaryStripSet Q L)).toReal * ∫ ω, ‖j ω‖ ^ 2 ∂μ)
        + 2 * ((d : ℝ) * gradBound Q L) ^ 2 * (cubeVolume Q * ∫ ω, ‖S ω‖ ^ 2 ∂μ) := by
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  have hSfin := volume_boundaryStripSet_ne_top Q L
  have hSmeas := measurableSet_boundaryStripSet Q L
  set G : ℝ := (d : ℝ) * gradBound Q L with hG
  have hdomint : Integrable (fun ω =>
      2 * (∫ x in boundaryStripSet Q L, ‖realize j ω x‖ ^ 2)
        + 2 * G ^ 2 * ∫ x in cubeSet Q, ‖realize S ω x‖ ^ 2) μ :=
    ((integrable_setIntegral_normSq_realize hSfin hjm hj).const_mul 2).add
      ((integrable_setIntegral_normSq_realize hQfin hSm hS).const_mul (2 * G ^ 2))
  have hmono : ∫ ω, (∫ x in cubeSet Q,
        ‖HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x‖ ^ 2) ∂μ
      ≤ ∫ ω, (2 * (∫ x in boundaryStripSet Q L, ‖realize j ω x‖ ^ 2)
        + 2 * G ^ 2 * ∫ x in cubeSet Q, ‖realize S ω x‖ ^ 2) ∂μ := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_) hdomint ?_
    · exact integral_nonneg fun x => by positivity
    filter_upwards [ae_memLp_two_realize (μ := μ) hSfin hjm hj,
      ae_memLp_two_realize (μ := μ) hQfin hSm hS] with ω hjS hSQ
    have hjSint : Integrable (fun x => ‖realize j ω x‖ ^ 2) (volume.restrict
        (boundaryStripSet Q L)) :=
      (memLp_two_iff_integrable_sq_norm
        (stronglyMeasurable_realize hjm ω).aestronglyMeasurable).1 hjS
    have hSQint : Integrable (fun x => ‖realize S ω x‖ ^ 2) (volume.restrict (cubeSet Q)) :=
      (memLp_two_iff_integrable_sq_norm
        (stronglyMeasurable_realize hSm ω).aestronglyMeasurable).1 hSQ
    have hindvol : Integrable ((boundaryStripSet Q L).indicator
        fun y => ‖realize j ω y‖ ^ 2) volume :=
      MeasureTheory.IntegrableOn.integrable_indicator hjSint hSmeas
    have hindint : Integrable ((boundaryStripSet Q L).indicator
        fun y => ‖realize j ω y‖ ^ 2) (volume.restrict (cubeSet Q)) :=
      hindvol.mono_measure Measure.restrict_le_self
    have hbound : Integrable (fun x =>
        2 * (boundaryStripSet Q L).indicator (fun y => ‖realize j ω y‖ ^ 2) x
          + 2 * G ^ 2 * ‖realize S ω x‖ ^ 2) (volume.restrict (cubeSet Q)) :=
      (hindint.const_mul 2).add (hSQint.const_mul (2 * G ^ 2))
    have hinner : (∫ x in cubeSet Q,
        ‖HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x‖ ^ 2)
        ≤ ∫ x in cubeSet Q,
            (2 * (boundaryStripSet Q L).indicator (fun y => ‖realize j ω y‖ ^ 2) x
              + 2 * G ^ 2 * ‖realize S ω x‖ ^ 2) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
        hbound ?_
      refine (ae_restrict_iff' (measurableSet_cubeSet Q)).2 ?_
      filter_upwards with x hx
      exact norm_sq_localStreamApprox_sub_le Q L S j ω hx
    refine hinner.trans (le_of_eq ?_)
    rw [integral_add (hindint.const_mul 2) (hSQint.const_mul (2 * G ^ 2)),
      integral_const_mul, integral_const_mul,
      setIntegral_indicator hSmeas,
      Set.inter_eq_self_of_subset_right (boundaryStripSet_subset_cubeSet Q L)]
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add ((integrable_setIntegral_normSq_realize hSfin hjm hj).const_mul 2)
      ((integrable_setIntegral_normSq_realize hQfin hSm hS).const_mul (2 * G ^ 2)),
    integral_const_mul, integral_const_mul,
    integral_setIntegral_normSq_realize hSfin hjm hj,
    integral_setIntegral_normSq_realize hQfin hSm hS, volume_cubeSet_toReal]

/-- For almost every sample the local approximation error is square integrable on
the cube. -/
theorem ae_memLp_localStreamApprox_sub (Q : TriadicCube d) (L : ℕ)
    {S : Ω → (Fin d → HilbertVec d)} {j : Ω → HilbertVec d}
    (hSm : StronglyMeasurable S) (hS : MemLp S 2 μ)
    (hjm : StronglyMeasurable j) (hj : MemLp j 2 μ) :
    ∀ᵐ ω ∂μ, MemLp (fun x => HilbertVec.ofVec (localStreamApprox Q L S j ω x)
      - realize j ω x) 2 (volume.restrict (cubeSet Q)) := by
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  filter_upwards [ae_memLp_two_realize (μ := μ) hQfin hjm hj,
    ae_memLp_two_realize (μ := μ) hQfin hSm hS] with ω hjω hSω
  refine MemLp.mono' (hjω.norm.add ((hSω.norm).const_mul ((d : ℝ) * gradBound Q L)))
    (stronglyMeasurable_localStreamApprox_sub Q L hSm hjm ω).aestronglyMeasurable ?_
  filter_upwards with x
  have hdec := ofVec_localStreamApprox_sub_realize Q L S j ω x
  have hcut : ‖(approxCutoff Q L).toFun x - 1‖ ≤ 1 := by
    have h0 := (approxCutoff Q L).nonneg x
    have h1 := (approxCutoff Q L).le_one x
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hfirst : ‖((approxCutoff Q L).toFun x - 1) • realize j ω x‖ ≤ ‖realize j ω x‖ := by
    rw [norm_smul]
    calc ‖(approxCutoff Q L).toFun x - 1‖ * ‖realize j ω x‖
        ≤ 1 * ‖realize j ω x‖ := mul_le_mul_of_nonneg_right hcut (norm_nonneg _)
      _ = ‖realize j ω x‖ := one_mul _
  have hbound := (norm_add_le _ _).trans
    (add_le_add hfirst (norm_streamRemainder_le Q L S ω x))
  rw [hdec]
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (realize j ω x)),
    abs_of_nonneg (norm_nonneg (realize S ω x)), mul_comm] using hbound

/-- **The expected normalized error at a fixed cube.**  This is the paper's
displayed estimate before the limit `K → ∞`, with the strip constant `C = d` and
with the second term carrying the cutoff gradient bound. -/
theorem integral_cubeLpNorm_localStreamApprox_sub_le (Q : TriadicCube d) (L : ℕ)
    {S : Ω → (Fin d → HilbertVec d)} {j : Ω → HilbertVec d}
    (hSm : StronglyMeasurable S) (hS : MemLp S 2 μ)
    (hjm : StronglyMeasurable j) (hj : MemLp j 2 μ) :
    ∫ ω, cubeLpNorm Q 2
        (fun x => HilbertVec.ofVec (localStreamApprox Q L S j ω x)
          - realize j ω x) ^ (2 : ℝ) ∂μ
      ≤ (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * (∫ ω, ‖j ω‖ ^ 2 ∂μ)
        + 2 * ((d : ℝ) * gradBound Q L) ^ 2 * ∫ ω, ‖S ω‖ ^ 2 ∂μ := by
  have hvolpos := cubeVolume_pos Q
  have hrepr : ∀ᵐ ω ∂μ, cubeLpNorm Q 2
      (fun x => HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x) ^ (2 : ℝ)
      = (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q,
          ‖HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x‖ ^ 2 := by
    filter_upwards [ae_memLp_localStreamApprox_sub (μ := μ) Q L hSm hS hjm hj] with ω hω
    have h := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow Q 2
      (fun x => HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x)
      (by norm_num) (by simp) (memLp_normalizedCubeMeasure_of_memHilbertVectorL2 hω)
    simpa [cubeAverage, Real.rpow_natCast] using h
  rw [integral_congr_ae hrepr, integral_const_mul]
  have hkey := integral_setIntegral_normSq_localStreamApprox_sub_le (μ := μ) Q L hSm hS hjm hj
  have hjnn : 0 ≤ ∫ ω, ‖j ω‖ ^ 2 ∂μ := integral_nonneg fun ω => by positivity
  have hstrip := volume_boundaryStripSet_toReal_le (d := d) Q L
  have hmul : (volume (boundaryStripSet Q L)).toReal * ∫ ω, ‖j ω‖ ^ 2 ∂μ
      ≤ (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) / 2 * cubeVolume Q * ∫ ω, ‖j ω‖ ^ 2 ∂μ :=
    mul_le_mul_of_nonneg_right hstrip hjnn
  have hinv : (0 : ℝ) < (cubeVolume Q)⁻¹ := inv_pos.2 hvolpos
  calc (cubeVolume Q)⁻¹ * ∫ ω, (∫ x in cubeSet Q,
        ‖HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x‖ ^ 2) ∂μ
      ≤ (cubeVolume Q)⁻¹ * (2 * ((volume (boundaryStripSet Q L)).toReal
            * ∫ ω, ‖j ω‖ ^ 2 ∂μ)
          + 2 * ((d : ℝ) * gradBound Q L) ^ 2 * (cubeVolume Q * ∫ ω, ‖S ω‖ ^ 2 ∂μ)) :=
        mul_le_mul_of_nonneg_left hkey hinv.le
    _ ≤ (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * (∫ ω, ‖j ω‖ ^ 2 ∂μ)
          + 2 * ((d : ℝ) * gradBound Q L) ^ 2 * ∫ ω, ‖S ω‖ ^ 2 ∂μ := by
        have h1 : (cubeVolume Q)⁻¹ * (2 * ((volume (boundaryStripSet Q L)).toReal
              * ∫ ω, ‖j ω‖ ^ 2 ∂μ))
            ≤ (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * ∫ ω, ‖j ω‖ ^ 2 ∂μ := by
          refine (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 2)) hinv.le).trans
            (le_of_eq ?_)
          field_simp
        have h2 : (cubeVolume Q)⁻¹ * (2 * ((d : ℝ) * gradBound Q L) ^ 2
              * (cubeVolume Q * ∫ ω, ‖S ω‖ ^ 2 ∂μ))
            = 2 * ((d : ℝ) * gradBound Q L) ^ 2 * ∫ ω, ‖S ω‖ ^ 2 ∂μ := by
          field_simp
        rw [mul_add, h2]
        exact add_le_add h1 le_rfl

/-- The squared normalized error is integrable in the sample.  Carrying this
clause in the existential below is what prevents a vacuous witness family whose
error is not integrable, on which the Bochner integral would degenerate to `0`
(the part-(i) convention of `ApproximationAssembly.lean`). -/
theorem integrable_cubeLpNorm_localStreamApprox_sub (Q : TriadicCube d) (L : ℕ)
    {S : Ω → (Fin d → HilbertVec d)} {j : Ω → HilbertVec d}
    (hSm : StronglyMeasurable S) (hS : MemLp S 2 μ)
    (hjm : StronglyMeasurable j) (hj : MemLp j 2 μ) :
    Integrable (fun ω => cubeLpNorm Q 2
      (fun x => HilbertVec.ofVec (localStreamApprox Q L S j ω x)
        - realize j ω x) ^ (2 : ℝ)) μ := by
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  have hmeas : StronglyMeasurable fun ω => ∫ x in cubeSet Q,
      ‖HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x‖ ^ 2 :=
    ((stronglyMeasurable_uncurry_localStreamApprox_sub Q L hSm hjm).norm.pow
      2).integral_prod_right'
  have hdom : Integrable (fun ω =>
      2 * (∫ x in cubeSet Q, ‖realize j ω x‖ ^ 2)
        + 2 * ((d : ℝ) * gradBound Q L) ^ 2 * ∫ x in cubeSet Q, ‖realize S ω x‖ ^ 2) μ :=
    ((integrable_setIntegral_normSq_realize hQfin hjm hj).const_mul 2).add
      ((integrable_setIntegral_normSq_realize hQfin hSm hS).const_mul
        (2 * ((d : ℝ) * gradBound Q L) ^ 2))
  have hI : Integrable (fun ω => ∫ x in cubeSet Q,
      ‖HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x‖ ^ 2) μ := by
    refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_memLp_two_realize (μ := μ) hQfin hjm hj,
      ae_memLp_two_realize (μ := μ) hQfin hSm hS] with ω hjω hSω
    have hji : Integrable (fun x => ‖realize j ω x‖ ^ 2) (volume.restrict (cubeSet Q)) :=
      (memLp_two_iff_integrable_sq_norm
        (stronglyMeasurable_realize hjm ω).aestronglyMeasurable).1 hjω
    have hSi : Integrable (fun x => ‖realize S ω x‖ ^ 2) (volume.restrict (cubeSet Q)) :=
      (memLp_two_iff_integrable_sq_norm
        (stronglyMeasurable_realize hSm ω).aestronglyMeasurable).1 hSω
    have hbound : ∫ x in cubeSet Q,
        ‖HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x‖ ^ 2
        ≤ ∫ x in cubeSet Q, (2 * ‖realize j ω x‖ ^ 2
          + 2 * ((d : ℝ) * gradBound Q L) ^ 2 * ‖realize S ω x‖ ^ 2) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
        ((hji.const_mul 2).add (hSi.const_mul (2 * ((d : ℝ) * gradBound Q L) ^ 2))) ?_
      filter_upwards with x
      have hdec := ofVec_localStreamApprox_sub_realize Q L S j ω x
      have hcut : ‖(approxCutoff Q L).toFun x - 1‖ ≤ 1 := by
        have h0 := (approxCutoff Q L).nonneg x
        have h1 := (approxCutoff Q L).le_one x
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith
      have hfirst : ‖((approxCutoff Q L).toFun x - 1) • realize j ω x‖ ≤ ‖realize j ω x‖ := by
        rw [norm_smul]
        calc ‖(approxCutoff Q L).toFun x - 1‖ * ‖realize j ω x‖
            ≤ 1 * ‖realize j ω x‖ := mul_le_mul_of_nonneg_right hcut (norm_nonneg _)
          _ = ‖realize j ω x‖ := one_mul _
      have hle : ‖HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x‖
          ≤ ‖realize j ω x‖ + (d : ℝ) * gradBound Q L * ‖realize S ω x‖ := by
        rw [hdec]
        exact (norm_add_le _ _).trans
          (add_le_add hfirst (norm_streamRemainder_le Q L S ω x))
      have hgb0 : (0 : ℝ) ≤ (d : ℝ) * gradBound Q L :=
        mul_nonneg (Nat.cast_nonneg d) (gradBound_nonneg Q L)
      nlinarith [hle, norm_nonneg (HilbertVec.ofVec (localStreamApprox Q L S j ω x)
        - realize j ω x), norm_nonneg (realize j ω x),
        mul_nonneg hgb0 (norm_nonneg (realize S ω x)),
        sq_nonneg (‖realize j ω x‖ - (d : ℝ) * gradBound Q L * ‖realize S ω x‖)]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => by positivity)]
    refine hbound.trans (le_of_eq ?_)
    rw [integral_add (hji.const_mul 2)
      (hSi.const_mul (2 * ((d : ℝ) * gradBound Q L) ^ 2)),
      integral_const_mul, integral_const_mul]
  have hrepr : ∀ᵐ ω ∂μ, cubeLpNorm Q 2
      (fun x => HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x) ^ (2 : ℝ)
      = (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q,
          ‖HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x‖ ^ 2 := by
    filter_upwards [ae_memLp_localStreamApprox_sub (μ := μ) Q L hSm hS hjm hj] with ω hω
    have h := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow Q 2
      (fun x => HilbertVec.ofVec (localStreamApprox Q L S j ω x) - realize j ω x)
      (by norm_num) (by simp) (memLp_normalizedCubeMeasure_of_memHilbertVectorL2 hω)
    simpa [cubeAverage, Real.rpow_natCast] using h
  exact ((hI.const_mul (cubeVolume Q)⁻¹).congr
    (by filter_upwards [hrepr] with ω h; exact h.symm))

end Estimate

section Main

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

end Main

end

end Algsuperdiff.Section3.Provider.Corrector
