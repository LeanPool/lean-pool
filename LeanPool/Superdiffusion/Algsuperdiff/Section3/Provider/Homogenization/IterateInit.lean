/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.AmplitudeBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.CombineIntegerDownscale

/-!
# IterateInit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The initialization data of the finite-corridor iterate (`e.iter.init`)

ABK26, proof of `p.homogenization.step`.  After the fourth moment display, the
manuscript writes

```text
E[J(cu_n, shom_L^{-1/2} e, shom_L^{1/2} e; a_L)] <= C E^2 gamma
    for all L, n in Z with L <= min{m-1, n},                    (e.iter.init)
```

obtained from that display "by subadditivity".  In the `A.4` reindexing, with

```text
F t = E[J(cu_{L+t}, shom_L^{-1/2} e, shom_L^{1/2} e; a_L)],    t in N,
```

the engine's two remaining slots are `hFnonneg : ∀ t, 0 ≤ F t` and
`hcrude : ∀ t, F t ≤ K₀ * delta`.  This module supplies both, at `K₀ = 1` and
`delta = delta_1`: `integral_cutoffResponseJ_nonneg_and_le_amplitude` is the
pair, and the engine's `hcrude` slot is its second component read through
`one_mul`.  The engine's third slot `hrec`, the `A.4` finite recurrence, is not
touched here, and no iteration depth (`j₀`, `k₁`) is mentioned by any statement
below.

The last theorem, `exists_integral_cutoffResponseJ_le_iterateInitDisplay`, is
the same crude bound in the verified consumer contract shape: one
dimension-only coefficient `K0 >= 0` selected before the model, the cutoff and
the direction, and the conclusion `F t <= K0 * delta_1` on the corridor horizon
`L + t <= m`.  Its witness is `K0 = 1`, the printed constant, and its horizon
hypothesis is not used --- the bound above the cutoff is horizon-free here,
because the route descends to the diagonal `n = L`, where the preceding-error
clause lives, instead of transporting the clause up to the observation scale.

## The route

The two components are separate source facts and have separate proofs.

* *Nonnegativity* is `J >= 0` (`e.Jenergyv.nosymm`) in the mean.  It is not
  part of the `A.4` display and is not derived from `e.iter.init`; it is the
  proved almost-sure nonnegativity
  `Observable.ae_forall_cutoffResponseJ_nonneg` integrated.  Almost-sure, not
  pointwise, because the carrier is the common measurable representative of the
  coarse block.

* *The crude bound* is the printed derivation, in two steps.  At the diagonal
  `n = L` it is the proved one-cube bound
  `coefficientCutoffLaw_annealedResponseJAtScale_le_of_moment_bound`
  (`Provider/Homogenization/CombineIntegerDownscale.lean`): the pathwise
  domination `J(cu_L; a_L) <= mathcal E_{s,infinity,2}(cu_L; a_L, shom_L)^2`
  followed by Cauchy--Schwarz against the diagonal fourth moment, whose
  universal constant is `1`.  Above the diagonal it is subadditivity in
  expectation, in the proved unconditional all-scales form
  `coefficientCutoffLaw_annealedResponseJAtScale_antitone` (`ibid.:430`).  Both
  are stated on the pushforward coefficient law `Cutoff.coefficientCutoffLaw M
  L`, so the only mathematical content of this module that is new *in this
  repository* is the carrier bridge to the sample-law integral of the
  source-facing observable `Observable.cutoffResponseJ`, which is the shape the
  iterate consumer and the frozen surface use.

The diagonal fourth moment itself is the proved amplitude bridge
`amplitude_mem_Ioc_and_lintegral_pow_four_le`
(`Provider/Homogenization/AmplitudeBridge.lean`), consumed here at `s = 1/4`
exactly as it is stated; this module re-derives none of it and chooses no
window.

## What this module does *not* do

No recurrence, no iteration, no selection of `j₀`, `k₁`, `A`, `C`, or of the
geometric weight `r`, and no instantiation of the iteration engine: the engine
is not even imported.  Nothing is stated about the union over cutoffs, about
concentration, or about any scale below the cutoff: every statement below has
`L <= n`, and the packaged form is indexed by `t : ℕ` at `n = L + t`.  The
excluded cutoff `L = m - 1` is not excluded here --- the premise is the full
`L <= m - 1` of the amplitude bridge.

## References

* ABK26, `e.iter.init`, `p.homogenization.step`, the premises `epsilon in
  (0,1/2]` and `e.gamma.condition.homog`, `e.Jenergyv.nosymm`,
  `e.subaddJ.nosymm`, the one-cube bound.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.IndependentSums
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The standing nonnegativity of the response mean -/

omit [NeZero d] in
/-- **The response mean is nonnegative** (`e.Jenergyv.nosymm`, in the mean), at
every cube scale, every coefficient cutoff scale and every direction.  This is
the engine slot `hFnonneg` of `exists_finiteCorridor_weightedDefect_decay`; it
is a separate source fact and is not part of the `A.4` display.

Almost-sure rather than pointwise: the source-facing observable is the common
measurable representative of the coarse block, whose nonnegativity is the
proved `Observable.ae_forall_cutoffResponseJ_nonneg`. -/
theorem integral_cutoffResponseJ_nonneg (M : ABKModel d) (n L : ℤ) (e : Vec d) :
    0 ≤ ∫ omega, Observable.cutoffResponseJ M n L e omega
      ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [Observable.ae_forall_cutoffResponseJ_nonneg M n L] with omega homega
  exact homega e

/-! ## The carrier bridge -/

/-- The annealed response of the genuine coefficient cutoff, read on the
cutoff-sample carrier.  The coefficient law is the pushforward of the sample law
along the genuine coefficient cutoff, so no new hypothesis enters. -/
private theorem annealedResponseJAtScale_eq_integral_cutoffSampleLaw
    (M : ABKModel d) (n L : ℤ) (p q : Vec d) :
    Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) n p q =
      ∫ omega, Ch04.restrictionResponseJObservableCubeSet (originCube d n) p q
          (Cutoff.coefficientCutoff M.nu L omega)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  have hmeas : AEStronglyMeasurable
      (Ch04.restrictionResponseJObservableCubeSet (originCube d n) p q)
      (Cutoff.coefficientCutoffLaw M L) :=
    ((Cutoff.coefficientCutoffLaw_lawCarrier M
        L).aemeasurable_restrictionResponseJObservableCubeSet
      (originCube d n) p q).aestronglyMeasurable
  change ∫ a, Ch04.restrictionResponseJObservableCubeSet (originCube d n) p q a
      ∂(Cutoff.coefficientCutoffLaw M L) = _
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hmeas ⊢
  exact integral_map (Cutoff.measurable_coefficientCutoff M.nu L).aemeasurable hmeas

/-- **The carrier bridge.**  The sample-law mean of the source-facing response
observable at cube scale `n`, coefficient cutoff scale `L` and direction `e` is
the annealed response of the pushforward coefficient law at the manuscript loads
`shom_L^{-1/2} e , shom_L^{1/2} e`.

One null set is spent, the literal identification
`Observable.ae_forall_cutoffResponseJ_eq_literal`; the change of variables is
the pushforward identity `Cutoff.coefficientCutoffLaw_eq_map`.  This is the
transport that lets the Step-2 lane of
`Provider/Homogenization/CombineIntegerDownscale.lean`, which is stated on the
coefficient law, be read at the observable the iterate consumer and the frozen
surface use. -/
theorem integral_cutoffResponseJ_eq_annealedResponseJAtScale (M : ABKModel d)
    (n L : ℤ) (e : Vec d) :
    ∫ omega, Observable.cutoffResponseJ M n L e omega
        ∂(Cutoff.cutoffSampleLaw M).toMeasure =
      Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) n
        (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
        (Observable.sqrtLoad (Annealed.sigmaBar M L) e) := by
  rw [annealedResponseJAtScale_eq_integral_cutoffSampleLaw M n L]
  refine integral_congr_ae ?_
  filter_upwards [Observable.ae_forall_cutoffResponseJ_eq_literal M n L] with omega homega
  exact homega e

/-! ## The crude bound of `e.iter.init` -/

/-- **`e.iter.init` at the amplitude-bridge conclusion**.  Under the diagonal
fourth-moment bound at amplitude `delta1 ^ 2` and the printed normalization
`|e| = 1`, the response mean at every cube scale `n >= L` above the coefficient
cutoff is at most `delta1`.

The two printed steps are the two proved inputs, in this order: the ascent
`E[J(cu_n; a_L)] <= E[J(cu_L; a_L)]` for `L <= n`
(`CombineIntegerDownscale.lean`, response subadditivity in the mean), and the
one-cube bound `E[J(cu_L; a_L)] <= delta1` (`ibid.:577`, the pathwise domination
by the squared error followed by Cauchy--Schwarz), whose universal constant is
`1`.  The only work done here is the carrier bridge and the identification of
the manuscript loads: `q = shom_L p` and `|q|^2 = shom_L` for `p = shom_L^{-1/2}
e`, `q = shom_L^{1/2} e`.

`hdelta1` and `hmoment` are the two conclusions of the proved amplitude bridge
and are conditional A inputs of this statement; the next public discharges them
by bare application.  The upper half `delta1 <= 1/2` of `hdelta1` is required
by the binder of the proved one-cube bound, whose proof uses only `0 <= delta1`
--- the binder occurs there exactly once, as `hdelta1.1.le`
(`CombineIntegerDownscale.lean`). -/
theorem integral_cutoffResponseJ_le_of_lintegral_pow_four_le (M : ABKModel d)
    {L n : ℤ} (hLn : L ≤ n) {s : ℝ} (hs : 0 < s) {delta1 : ℝ}
    (hdelta1 : delta1 ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hmoment : ∫⁻ omega, ENNReal.ofReal
        (Observable.cutoffHomogenizationErrorRepresentative M L L hs
          (Annealed.sigmaBar M L) omega ^ 4)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (delta1 ^ 2))
    {e : Vec d} (he : Ch02.vecNorm e = 1) :
    ∫ omega, Observable.cutoffResponseJ M n L e omega
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ delta1 := by
  have hsigma : (0 : ℝ) < (Annealed.sigmaBar M L : ℝ) := (Annealed.sigmaBar M L).property
  have hroot : (0 : ℝ) < Real.sqrt (Annealed.sigmaBar M L : ℝ) := Real.sqrt_pos.2 hsigma
  have hrootsq : Real.sqrt (Annealed.sigmaBar M L : ℝ) ^ 2 =
      (Annealed.sigmaBar M L : ℝ) := Real.sq_sqrt hsigma.le
  have hesq : vecNormSq e = 1 := by
    rw [← Ch02.vecNorm_sq_eq_vecNormSq, he, one_pow]
  have hpq : Observable.sqrtLoad (Annealed.sigmaBar M L) e =
      (Annealed.sigmaBar M L : ℝ) •
        Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e := by
    rw [Observable.sqrtLoad, Observable.inverseSqrtLoad, smul_smul]
    congr 1
    rw [inv_eq_one_div, mul_one_div, eq_div_iff (ne_of_gt hroot)]
    exact Real.mul_self_sqrt hsigma.le
  have hqnorm : vecNormSq (Observable.sqrtLoad (Annealed.sigmaBar M L) e) =
      (Annealed.sigmaBar M L : ℝ) := by
    rw [Observable.sqrtLoad, vecNormSq_smul, hesq, mul_one, hrootsq]
  rw [integral_cutoffResponseJ_eq_annealedResponseJAtScale]
  exact (coefficientCutoffLaw_annealedResponseJAtScale_antitone M L hLn _ _).trans
    (coefficientCutoffLaw_annealedResponseJAtScale_le_of_moment_bound M L hs hdelta1
      hmoment hpq hqnorm)

/-- **`e.iter.init`** at the repository amplitude `delta_1 = 10^9 E^2 gamma` of
`A.3`: under the frozen regime binders, the preceding-error clause and the
proposition's own smallness gate, for every cutoff `L <= m - 1`, every unit
direction and every cube scale `n >= L`,

```text
E[J(cu_n, shom_L^{-1/2} e, shom_L^{1/2} e; a_L)] <= 10^9 E^2 gamma .
```

The premise block is the proved amplitude bridge's, verbatim; the bridge is
applied at `s = 1/4` and its two conclusions are passed to the previous public
unchanged.  The printed constant `C` is `10^9` here, and the printed range `L
<= min{m-1, n}` is the pair `hL`, `hLn`. -/
theorem integral_cutoffResponseJ_le_amplitude_of_precedingError (M : ABKModel d)
    {m : ℤ} {E : {E : ℝ // 1 ≤ E}} {Chom epsilon : ℝ}
    (hChom : (10 : ℝ) ^ 9 ≤ Chom)
    (hEfloor : 15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hregime : M.gamma ≤ ((E : ℝ)⁻¹) ^ 10)
    (hLower : ∀ k : ℤ, k ≤ m - 1 →
      ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
        Probability.IsTwoTermBigOWith
          (Cutoff.cutoffSampleLaw M).toMeasure
          (gammaSigma 2) (gammaSigma (1 / 2))
          (Observable.cutoffHomogenizationError M k
            ⟨s,
              (mul_pos (by norm_num : (0 : ℝ) < 8)
                M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
          ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
          ((s⁻¹) ^ 2 *
            Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))))
    (hepsilon : epsilon ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hgate : M.gamma ≤ Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon)
    {L : ℤ} (hL : L ≤ m - 1) {e : Vec d} (he : Ch02.vecNorm e = 1)
    (n : ℤ) (hLn : L ≤ n) :
    ∫ omega, Observable.cutoffResponseJ M n L e omega
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      10 ^ 9 * (E : ℝ) ^ 2 * M.gamma := by
  have hs : (0 : ℝ) < 1 / 4 := by norm_num
  obtain ⟨hrange, hmoment⟩ :=
    amplitude_mem_Ioc_and_lintegral_pow_four_le M hChom hEfloor hregime hLower
      hepsilon hgate hs
  exact integral_cutoffResponseJ_le_of_lintegral_pow_four_le M hLn hs hrange
    (hmoment L hL) he

/-- ```text
F t = E[J(cu_{L+t}, shom_L^{-1/2} e, shom_L^{1/2} e; a_L)] ,
```

the two components are the two remaining input slots of the proved iteration
engine `exists_finiteCorridor_weightedDefect_decay`
(`Provider/Homogenization/FiniteCorridorIteration.lean`): the first is its
`hFnonneg`, and the second is its `hcrude` at the crude coefficient `K₀ = 1`
and the amplitude `delta = 10^9 E^2 gamma`, read through `one_mul`.  The
engine's remaining slot `hrec` --- the `A.4` finite recurrence --- is not
supplied here, and neither is the selection of `j₀`, `k₁`, `A`, `C` or `r`.
The consumer contract shape of the second component, with the crude coefficient
existentially quantified in front and the corridor horizon bound, is the next
and last theorem.

This is a local Provider theorem and makes no source-node status claim. -/
theorem integral_cutoffResponseJ_nonneg_and_le_amplitude (M : ABKModel d)
    {m : ℤ} {E : {E : ℝ // 1 ≤ E}} {Chom epsilon : ℝ}
    (hChom : (10 : ℝ) ^ 9 ≤ Chom)
    (hEfloor : 15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hregime : M.gamma ≤ ((E : ℝ)⁻¹) ^ 10)
    (hLower : ∀ k : ℤ, k ≤ m - 1 →
      ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
        Probability.IsTwoTermBigOWith
          (Cutoff.cutoffSampleLaw M).toMeasure
          (gammaSigma 2) (gammaSigma (1 / 2))
          (Observable.cutoffHomogenizationError M k
            ⟨s,
              (mul_pos (by norm_num : (0 : ℝ) < 8)
                M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
          ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
          ((s⁻¹) ^ 2 *
            Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))))
    (hepsilon : epsilon ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hgate : M.gamma ≤ Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon)
    {L : ℤ} (hL : L ≤ m - 1) {e : Vec d} (he : Ch02.vecNorm e = 1) :
    (∀ t : ℕ, 0 ≤ ∫ omega, Observable.cutoffResponseJ M (L + (t : ℤ)) L e omega
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ∧
      ∀ t : ℕ, ∫ omega, Observable.cutoffResponseJ M (L + (t : ℤ)) L e omega
          ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        10 ^ 9 * (E : ℝ) ^ 2 * M.gamma :=
  ⟨fun t => integral_cutoffResponseJ_nonneg M (L + (t : ℤ)) L e,
    fun t =>
      integral_cutoffResponseJ_le_amplitude_of_precedingError M hChom hEfloor
        hregime hLower hepsilon hgate hL he (L + (t : ℤ)) (by omega)⟩

end

end Algsuperdiff.Section3.Provider.Homogenization
