/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseBudgetWire
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseIndepAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.FreshShellExistence

/-!
# PrincipalResponseGoodEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The principal good-event energy display, consumer-closed up to the `Ccg` gate

Conditional Provider module: the direct successor of
`PrincipalResponseBudgetWire.exists_smallCoupling_principalEnergy_bound_of_centering`,
with thirteen previously caller-supplied inputs internalized (`n`, `highScale`,
`hle`, `wD`, `wN`, `hwD`, `hwN`, `hmeasR`, `hintR`, `hgoodInt`, `hcubeInt`,
`hindep`, `hbudget`).  The correctors are produced existentially on the
conclusion side together with their `e.def.w` (label) weak-solution properties
-- never assumed.  The scales are instantiated at `n = ((originCube d K).scale)
- j` and `highScale = m`; no uniqueness is claimed for that scale bridge.

The complement leg's per-cube integrability -- the integrability of
`switchCubeEnergy` against the complement indicator of the per-cube bad event --
is produced on the conclusion side too, at the very correctors and event
constant the inequality is stated at.  It is an internal consequence of the
almost-sure good-event domination used to prove the display, not a new
hypothesis, and a direct consumer needs it to recombine the two legs.

The ONE non-standing conditional gate is `hccg : 2 * d ^ 6 ≤ Ccg *
sensitivityConstMax d ^ 2`, quantified over the event constant `Ccg`.  The
planned internal discharge (same-constant route, supervisor-ruled) selects a
floor-normalized coarse-ellipticity constant `Cbase ≥ d ^ 6` B the bad-event
application and consumes the bad-event companion at event constant `2 * Cbase`,
matching how the frozen `bad_event_estimate` on current main states its event
at twice its coarse constant.  No event monotonicity is used or assumed
anywhere.

Besides the display endpoint
`exists_smallCoupling_principalEnergy_bound_of_gate`,
the fourth-order load integrability
`exists_gamma0_integrable_switchEllipLoad_principalPz_sq` and the energy's
sample measurability `aestronglyMeasurable_switchCubeEnergy` are exposed,
because the same-witness recombination in `PrincipalResponseTerminal` has to
rebuild the bad-event half's well-definedness binders at the very correctors
this module produces.  Everything else below is private.

`Frozen.Section3.stream_increment_lp_large_cube_bound` is reached too but is
**proved** here, so it contributes nothing either.
`aestronglyMeasurable_switchCubeEnergy` reaches neither.  All internal helpers
below are otherwise sorry-free, and none of the five forbidden circular anchors
is reached.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}


private theorem transport_shellSeq_integral (M : ABKModel d) (f : ShellSeq d → ℝ) :
    (∫ omega : ShellSeq d, f omega ∂M.P.toMeasure) =
      ∫ w : CutoffSample d, f w.val ∂(cutoffSampleLaw M).toMeasure := by
  rw [← map_cutoffSampleLaw_val M]
  exact (MeasurableEmbedding.subtype_coe (measurableSet_lowerTailGoodSet d)).integral_map f

private theorem gaugeRatio_self' (sigma : PositiveScalar) : gaugeRatio sigma sigma = 1 := by
  rw [gaugeRatio, div_self (ne_of_gt sigma.2), max_self]

private theorem annealedSqrtNormSq_eq_switchEllipLoad' (sigma : PositiveScalar)
    (X : BlockVec d) : annealedSqrtNormSq sigma X = switchEllipLoad ((sigma : ℝ)) X := rfl

private theorem le_card_mul_descendantsAverage' {Q : TriadicCube d} {jd : ℕ}
    {F : TriadicCube d → ℝ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth Q jd)
    (hF : ∀ S ∈ descendantsAtDepth Q jd, 0 ≤ F S) :
    F R ≤ ((descendantsAtDepth Q jd).card : ℝ) * descendantsAverage Q jd F := by
  classical
  have hcard : (0 : ℝ) < ((descendantsAtDepth Q jd).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨R, hR⟩
  have hsum : F R ≤ ∑ S ∈ descendantsAtDepth Q jd, F S := Finset.single_le_sum hF hR
  have hdef : descendantsAverage Q jd F =
      ((descendantsAtDepth Q jd).card : ℝ)⁻¹ * ∑ S ∈ descendantsAtDepth Q jd, F S := rfl
  rw [hdef, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcard), one_mul]
  exact hsum

private theorem exists_kappa_switchEllipLoad_sq_le (K : ℤ) (jd : ℕ)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d K) jd)
    (sigma : PositiveScalar) (L Hi : ℤ) {e e' : Vec d}
    (he : Ch02.vecNorm e ≤ 1) (he' : Ch02.vecNorm e' ≤ 1) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ (omega : Cutoff.ShellSeq d)
        (wD : H10Function (openCubeSet (originCube d K)))
        (wN : H1MeanZeroFunction (openCubeSet (originCube d K))),
        MemLp wD.toH1Function.grad (8 : ℝ≥0∞)
            (normalizedCubeMeasure (originCube d K)) →
        MemLp wN.toH1Function.grad (8 : ℝ≥0∞)
            (normalizedCubeMeasure (originCube d K)) →
        |switchEllipLoad ((sigma : ℝ))
              (principalPz sigma omega L Hi e e' R wD wN) ^ (2 : ℕ)| ≤
          kappa *
            (1 +
              cubeEuclideanLpNorm (originCube d K) 8 wD.toH1Function.grad ^ (2 : ℕ) +
              cubeEuclideanLpNorm (originCube d K) 8 wN.toH1Function.grad ^ (2 : ℕ) +
              Provider.Stream.streamIncrementLpNorm 8 K L Hi omega ^ (2 : ℕ)) ^ (2 : ℕ) := by
  classical
  have hsi : (0 : ℝ) < (sigma : ℝ) := sigma.2
  have hsiInv : (0 : ℝ) < ((sigma : ℝ))⁻¹ := inv_pos.2 hsi
  set crd : ℝ := ((descendantsAtDepth (originCube d K) jd).card : ℝ) with hcrd
  have hcrd0 : (0 : ℝ) ≤ crd := by rw [hcrd]; positivity
  clear_value crd
  set c0 : ℝ := 3 + 2 * ((sigma : ℝ))⁻¹ ^ (2 : ℕ) with hc0
  have hc00 : (0 : ℝ) ≤ c0 := by rw [hc0]; positivity
  have hesq : vecNormSq e ≤ 1 := by
    have h := Ch02.vecNorm_sq_eq_vecNormSq e
    have h0 := Ch02.vecNorm_nonneg e
    nlinarith
  have hesq' : vecNormSq e' ≤ 1 := by
    have h := Ch02.vecNorm_sq_eq_vecNormSq e'
    have h0 := Ch02.vecNorm_nonneg e'
    nlinarith
  have he4 : vecNormSq e' ^ (2 : ℕ) + vecNormSq e ^ (2 : ℕ) ≤ 2 := by
    have h1 : vecNormSq e' ^ (2 : ℕ) ≤ 1 := by
      simpa using pow_le_pow_left₀ (vecNormSq_nonneg e') hesq' 2
    have h2 : vecNormSq e ^ (2 : ℕ) ≤ 1 := by
      simpa using pow_le_pow_left₀ (vecNormSq_nonneg e) hesq 2
    linarith
  refine ⟨crd * (32 + 16 * c0 ^ (2 : ℕ)) + 1, by positivity, ?_⟩
  intro omega wD wN hD hN
  have hpath := pathwise_descendantsAverage_sq_annealedSqrtNormSq_le sigma sigma omega
    L Hi e e' (originCube d K) jd wD wN hD hN
  simp only [gaugeRatio_self', one_pow, mul_one] at hpath
  have hcube := le_card_mul_descendantsAverage' (Q := originCube d K) (jd := jd)
    (F := fun S => annealedSqrtNormSq sigma
      (principalPz sigma omega L Hi e e' S wD wN) ^ (2 : ℕ)) hR
    (fun _ _ => sq_nonneg _)
  rw [← hcrd] at hcube
  have hgrid := hcube.trans (mul_le_mul_of_nonneg_left hpath hcrd0)
  simp only [annealedSqrtNormSq_eq_switchEllipLoad'] at hgrid
  set ND : ℝ := cubeEuclideanLpNorm (originCube d K) 8 wD.toH1Function.grad with hND
  set NN : ℝ := cubeEuclideanLpNorm (originCube d K) 8 wN.toH1Function.grad with hNN
  set St : ℝ := Provider.Stream.streamIncrementLpNorm 8 K L Hi omega with hSt
  set FN : ℝ := cubeEuclideanLpNorm (originCube d K) 8
    (streamForcing ((sigma : ℝ))⁻¹ omega L Hi e') with hFN
  have hND0 : (0 : ℝ) ≤ ND := by rw [hND]; exact cubeEuclideanLpNorm_nonneg _ _ _
  have hNN0 : (0 : ℝ) ≤ NN := by rw [hNN]; exact cubeEuclideanLpNorm_nonneg _ _ _
  have hFN0 : (0 : ℝ) ≤ FN := by rw [hFN]; exact cubeEuclideanLpNorm_nonneg _ _ _
  have hFle : FN ≤ ((sigma : ℝ))⁻¹ * St := by
    rw [hFN, hSt]
    exact cubeEuclideanLpNorm_streamForcing_le hsiInv.le K L Hi omega he'
  clear_value ND NN St FN
  set Wl : ℝ := 1 + ND ^ (2 : ℕ) + NN ^ (2 : ℕ) + St ^ (2 : ℕ) with hWl
  have hWl1 : (1 : ℝ) ≤ Wl := by
    rw [hWl]; linarith [sq_nonneg ND, sq_nonneg NN, sq_nonneg St]
  have hWlND : ND ^ (2 : ℕ) ≤ Wl := by
    rw [hWl]; linarith [sq_nonneg NN, sq_nonneg St]
  have hWlNN : NN ^ (2 : ℕ) ≤ Wl := by
    rw [hWl]; linarith [sq_nonneg ND, sq_nonneg St]
  have hWlSt : St ^ (2 : ℕ) ≤ Wl := by
    rw [hWl]; linarith [sq_nonneg ND, sq_nonneg NN]
  clear_value Wl
  have hFNsq : FN ^ (2 : ℕ) ≤ ((sigma : ℝ))⁻¹ ^ (2 : ℕ) * Wl := by
    have h1 : FN ^ (2 : ℕ) ≤ (((sigma : ℝ))⁻¹ * St) ^ (2 : ℕ) :=
      pow_le_pow_left₀ hFN0 hFle 2
    have h2 : (((sigma : ℝ))⁻¹ * St) ^ (2 : ℕ) =
        ((sigma : ℝ))⁻¹ ^ (2 : ℕ) * St ^ (2 : ℕ) := by ring
    have h3 : ((sigma : ℝ))⁻¹ ^ (2 : ℕ) * St ^ (2 : ℕ) ≤
        ((sigma : ℝ))⁻¹ ^ (2 : ℕ) * Wl :=
      mul_le_mul_of_nonneg_left hWlSt (by positivity)
    linarith [h1, h2 ▸ h1]
  have hSinner0 : (0 : ℝ) ≤ ND ^ (2 : ℕ) + 2 * NN ^ (2 : ℕ) + 2 * FN ^ (2 : ℕ) := by
    positivity
  have hSinnerle : ND ^ (2 : ℕ) + 2 * NN ^ (2 : ℕ) + 2 * FN ^ (2 : ℕ) ≤ c0 * Wl := by
    rw [hc0]
    linarith [hWlND, hWlNN, hFNsq]
  have hSq : (ND ^ (2 : ℕ) + 2 * NN ^ (2 : ℕ) + 2 * FN ^ (2 : ℕ)) ^ (2 : ℕ) ≤
      c0 ^ (2 : ℕ) * Wl ^ (2 : ℕ) := by
    have h := pow_le_pow_left₀ hSinner0 hSinnerle 2
    have h2 : (c0 * Wl) ^ (2 : ℕ) = c0 ^ (2 : ℕ) * Wl ^ (2 : ℕ) := by ring
    linarith [h2 ▸ h]
  have hWlsq1 : (1 : ℝ) ≤ Wl ^ (2 : ℕ) := one_le_pow₀ hWl1
  refine le_trans (le_of_eq (abs_of_nonneg (sq_nonneg _))) (hgrid.trans ?_)
  have hstep : 16 * (vecNormSq e' ^ (2 : ℕ) + vecNormSq e ^ (2 : ℕ)) +
      16 * (ND ^ (2 : ℕ) + 2 * NN ^ (2 : ℕ) + 2 * FN ^ (2 : ℕ)) ^ (2 : ℕ) ≤
      (32 + 16 * c0 ^ (2 : ℕ)) * Wl ^ (2 : ℕ) := by
    linarith [he4, hSq, hWlsq1]
  calc crd * (16 * (vecNormSq e' ^ (2 : ℕ) + vecNormSq e ^ (2 : ℕ)) +
        16 * (ND ^ (2 : ℕ) + 2 * NN ^ (2 : ℕ) + 2 * FN ^ (2 : ℕ)) ^ (2 : ℕ))
      ≤ crd * ((32 + 16 * c0 ^ (2 : ℕ)) * Wl ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hstep hcrd0
    _ ≤ (crd * (32 + 16 * c0 ^ (2 : ℕ)) + 1) * Wl ^ (2 : ℕ) := by
        linarith [hWlsq1]


/-! ## The measurable-proxy integrability device -/

private theorem isBigOWith_posPart' {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {Psi : ℝ → ℝ} {Y : Omega → ℝ} {A : ℝ} (hA : 0 < A)
    (hY : IndependentSums.IsBigOWith mu Psi Y A) :
    IndependentSums.IsBigOWith mu Psi (fun omega => max (Y omega) 0) A := by
  intro t ht
  have hAt : (0 : ℝ) < A * t := mul_pos hA (lt_of_lt_of_le zero_lt_one ht)
  have hset :
      IndependentSums.upperTailEvent (fun omega => max (Y omega) 0) (A * t) =
        IndependentSums.upperTailEvent Y (A * t) := by
    ext omega
    simp only [IndependentSums.mem_upperTailEvent, lt_max_iff]
    constructor
    · rintro (hlt | hlt)
      · exact hlt
      · exact absurd hlt (not_lt.2 hAt.le)
    · exact fun hlt => Or.inl hlt
  rw [hset]
  exact hY ht

private theorem rpow_two_eq_pow' (y : ℝ) : y ^ (2 : ℝ) = y ^ (2 : ℕ) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

private theorem integrable_of_abs_le_shift_add_kappa_sq' {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {f W Y : Omega → ℝ}
    {B kappa b A sigma : ℝ}
    (hsigma : 0 < sigma) (hA : 0 < A) (hb : 0 ≤ b) (hkappa : 0 < kappa)
    (hfm : Measurable f) (hWnn : ∀ omega, 0 ≤ W omega)
    (hfW : ∀ omega, |f omega| ≤ B + kappa * W omega ^ (2 : ℕ))
    (hWY : ∀ omega, W omega ≤ b + Y omega)
    (hY : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) Y A) :
    Integrable f mu := by
  classical
  set P : Omega → ℝ := fun omega => max (|f omega| - B) 0 with hPdef
  have hPnn : ∀ omega, 0 ≤ P omega := fun omega => le_max_right _ _
  set W0 : Omega → ℝ := fun omega => Real.sqrt (P omega / kappa) with hW0def
  have hW0nn : ∀ omega, 0 ≤ W0 omega := fun omega => Real.sqrt_nonneg _
  have hW0m : Measurable W0 :=
    Real.continuous_sqrt.measurable.comp
      ((((continuous_abs.measurable.comp hfm).sub measurable_const).max
        measurable_const).div measurable_const)
  have hW0sq : ∀ omega, kappa * W0 omega ^ (2 : ℕ) = P omega := by
    intro omega
    rw [hW0def]
    have hnn : (0 : ℝ) ≤ P omega / kappa := div_nonneg (hPnn omega) hkappa.le
    rw [Real.sq_sqrt hnn]
    field_simp
  have hXle : ∀ omega, |f omega| ≤ B + kappa * W0 omega ^ (2 : ℕ) := by
    intro omega
    rw [hW0sq omega, hPdef]
    have h : |f omega| - B ≤ max (|f omega| - B) 0 := le_max_left _ _
    simp only
    linarith
  have hW0leW : ∀ omega, W0 omega ≤ W omega := by
    intro omega
    have hP : P omega ≤ kappa * W omega ^ (2 : ℕ) := by
      rw [hPdef]
      refine max_le ?_ (by positivity)
      linarith [hfW omega]
    have hsq : W0 omega ^ (2 : ℕ) ≤ W omega ^ (2 : ℕ) := by
      have := hW0sq omega
      nlinarith [hP, hkappa]
    exact le_of_sq_le_sq hsq (hWnn omega)
  set Yt : Omega → ℝ := fun omega => W0 omega - b with hYtdef
  have hYtm : Measurable Yt := hW0m.sub measurable_const
  have hYt : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) Yt A :=
    hY.of_le fun omega => by
      have h1 := hW0leW omega
      have h2 := hWY omega
      rw [hYtdef]
      simp only
      linarith
  have hmax := isBigOWith_posPart' hA hYt
  have hIY : Integrable (fun omega => max (Yt omega) 0 ^ (2 : ℕ)) mu := by
    have h := IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
      (p := (2 : ℝ)) hsigma hA (by norm_num) (fun omega => le_max_right _ _)
      (hYtm.max measurable_const).aemeasurable hmax
    simpa only [rpow_two_eq_pow'] using h
  have hdom2 : ∀ omega,
      W0 omega ^ (2 : ℕ) ≤ 2 * b ^ (2 : ℕ) + 2 * max (Yt omega) 0 ^ (2 : ℕ) := by
    intro omega
    have hle : W0 omega ≤ b + max (Yt omega) 0 := by
      have hm : Yt omega ≤ max (Yt omega) 0 := le_max_left _ _
      rw [hYtdef] at hm
      simp only at hm
      linarith
    have hnn : (0 : ℝ) ≤ max (Yt omega) 0 := le_max_right _ _
    nlinarith [hW0nn omega, hle, hnn, hb, sq_nonneg (b - max (Yt omega) 0)]
  have hIW0 : Integrable (fun omega => W0 omega ^ (2 : ℕ)) mu := by
    refine Integrable.mono'
      ((integrable_const (2 * b ^ (2 : ℕ))).add (hIY.const_mul 2))
      ((hW0m.pow_const 2).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun omega => ?_
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ W0 omega ^ (2 : ℕ))]
    exact hdom2 omega
  refine Integrable.mono'
    ((integrable_const B).add (hIW0.const_mul kappa))
    hfm.aestronglyMeasurable (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_eq_abs]
  exact hXle omega

/-! ## Measurability of the ellipticity load in the sample -/

private theorem measurable_vecNormSq_comp {Omega : Type*} [MeasurableSpace Omega]
    {f : Omega → Vec d} (hf : Measurable f) :
    Measurable fun omega => vecNormSq (f omega) := by
  have hEq : (fun omega => vecNormSq (f omega)) =
      fun omega => ∑ i, f omega i * f omega i := rfl
  rw [hEq]
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hf).mul ((measurable_pi_apply i).comp hf)

private theorem measurable_switchEllipLoad_comp {Omega : Type*} [MeasurableSpace Omega]
    (S : ℝ) {X : Omega → BlockVec d} (hX : Measurable X) :
    Measurable fun omega => switchEllipLoad S (X omega) := by
  have hEq : (fun omega => switchEllipLoad S (X omega)) =
      fun omega => S * vecNormSq (X omega).1 + S⁻¹ * vecNormSq (X omega).2 := rfl
  rw [hEq]
  exact (measurable_const.mul (measurable_vecNormSq_comp hX.fst)).add
    (measurable_const.mul (measurable_vecNormSq_comp hX.snd))


/-! ## The `L^8` membership of the two corrector gradients -/

private theorem memLp_eight_grad_dirichlet' (hd : 2 ≤ d)
    (Q : TriadicCube d) (f : Vec d → Vec d) (hf : Continuous f)
    (w : H10Function (openCubeSet Q))
    (hw : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) w
      (fun x => -f x)) :
    MemLp w.toH1Function.grad (8 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  obtain ⟨_, _, hCZ⟩ := Algsuperdiff.Frozen.External.calderon_zygmund (d := d) hd
    (8 : ℝ≥0∞) (by norm_num) (by norm_num)
  exact ((hCZ Q f (memLp_normalizedCubeMeasure_of_continuous Q _ hf)).1 w hw).1

private theorem memLp_eight_grad_neumann' (hd : 2 ≤ d)
    (Q : TriadicCube d) (f : Vec d → Vec d) (hf : Continuous f)
    (w : H1MeanZeroFunction (openCubeSet Q))
    (hw : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) w
      (fun x => -f x)) :
    MemLp w.toH1Function.grad (8 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  obtain ⟨_, _, hCZ⟩ := Algsuperdiff.Frozen.External.calderon_zygmund (d := d) hd
    (8 : ℝ≥0∞) (by norm_num) (by norm_num)
  exact ((hCZ Q f (memLp_normalizedCubeMeasure_of_continuous Q _ hf)).2 w hw).1

/-! ## The fourth-order integrability of the ellipticity load -/

theorem exists_gamma0_integrable_switchEllipLoad_principalPz_sq (d : ℕ) (hd : 2 ≤ d) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
        ∀ (m0 : ℤ) (Eind : {E : ℝ // 1 ≤ E}),
          Algsuperdiff.Frozen.Section3.inductionState M m0 Eind →
          ∀ (m K : ℤ) (hgap : ℕ), 0 < hgap → m - (hgap : ℤ) ≤ m0 →
            (hgap : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
            (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (K : ℝ) - (m : ℝ) →
            ∀ e e' : Vec d, Ch02.vecNorm e ≤ 1 → Ch02.vecNorm e' ≤ 1 →
              ∀ (jd : ℕ) (R : TriadicCube d),
                R ∈ descendantsAtDepth (originCube d K) jd →
                ∀ (wD : Cutoff.ShellSeq d →
                    H10Function (openCubeSet (originCube d K)))
                  (wN : Cutoff.ShellSeq d →
                    H1MeanZeroFunction (openCubeSet (originCube d K))),
                  (∀ omega : Cutoff.ShellSeq d,
                    IsZeroTraceDirichletRhsWeakSolution
                      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                      (openCubeSet (originCube d K)) (wD omega)
                      (fun x => -streamForcing
                        ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ omega
                        (m - (hgap : ℤ)) m e x)) →
                  (∀ omega : Cutoff.ShellSeq d,
                    IsMeanZeroNeumannRhsWeakSolution
                      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                      (openCubeSet (originCube d K)) (wN omega)
                      (fun x => -streamForcing
                        ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ omega
                        (m - (hgap : ℤ)) m e' x)) →
                  Integrable
                    (fun omega : Cutoff.ShellSeq d =>
                      switchEllipLoad
                          ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))
                          (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ)))
                            omega (m - (hgap : ℤ)) m e e' R (wD omega)
                            (wN omega)) ^ (2 : ℕ))
                    M.P.toMeasure := by
  classical
  obtain ⟨Chead, hChead0, gamma0, hg0pos, hg0quarter, hL8⟩ :=
    exists_cubeEuclideanL8_gradient_sq_sum_le_const_add_gammaPow d hd
  obtain ⟨Clp, hClp0, hLP⟩ := exists_streamIncrementLpNormSq_head_tail d
  refine ⟨gamma0, hg0pos, hg0quarter, ?_⟩
  intro M hMgamma m0 Eind hstate m K hgap hhpos hm hh hK e e' he he' jd R hR wD wN
    hwD hwN
  have : NeZero d := ⟨by omega⟩
  have hgamma : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hnm : m - (hgap : ℤ) < m := by omega
  have hmK : m ≤ K := by
    have hpos : (0 : ℝ) < (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ := by positivity
    have hle : (m : ℝ) ≤ (K : ℝ) := by linarith
    exact_mod_cast hle
  obtain ⟨Tfl, hTfl0, hTfltail, hTflbd⟩ :=
    hL8 M hMgamma m0 Eind hstate m K hgap hhpos hm hh hK e e' he he'
  obtain ⟨T, hT0, hTbd, hTtail⟩ := hLP M K (m - (hgap : ℤ)) m hnm hmK
  obtain ⟨kappa, hkappa0, hkappa⟩ := exists_kappa_switchEllipLoad_sq_le K jd hR
    (Annealed.sigmaBar M (m - (hgap : ℤ))) (m - (hgap : ℤ)) m he he'
  have hDmem : ∀ omega : Cutoff.ShellSeq d,
      MemLp (wD omega).toH1Function.grad (8 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d K)) := fun omega =>
    memLp_eight_grad_dirichlet' hd (originCube d K) _
      (continuous_streamForcing _ _ _ _ _) (wD omega) (hwD omega)
  have hNmem : ∀ omega : Cutoff.ShellSeq d,
      MemLp (wN omega).toH1Function.grad (8 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d K)) := fun omega =>
    memLp_eight_grad_neumann' hd (originCube d K) _
      (continuous_streamForcing _ _ _ _ _) (wN omega) (hwN omega)
  have hPzmeas : Measurable (fun omega : Cutoff.ShellSeq d =>
      principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) omega (m - (hgap : ℤ)) m
        e e' R (wD omega) (wN omega)) :=
    (measurable_shellIndexSigma_principalPz hR
      (Annealed.sigmaBar M (m - (hgap : ℤ)))
      ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹
      ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹
      (m - (hgap : ℤ)) m e e' e e' wD wN hwD hwN).mono
      (Cutoff.shellIndexSigma_le_borel _) le_rfl
  have hfmeas : Measurable (fun omega : Cutoff.ShellSeq d =>
      switchEllipLoad ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))
        (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) omega
          (m - (hgap : ℤ)) m e e' R (wD omega) (wN omega)) ^ (2 : ℕ)) :=
    (measurable_switchEllipLoad_comp _ hPzmeas).pow_const 2
  have hcast : (m : ℝ) - ((m - (hgap : ℤ) : ℤ) : ℝ) = (hgap : ℝ) := by push_cast; ring
  have hhgapR : (0 : ℝ) < (hgap : ℝ) := by exact_mod_cast hhpos
  set A0 : ℝ := min M.gamma⁻¹ ((m : ℝ) - ((m - (hgap : ℤ) : ℤ) : ℝ)) *
    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) with hA0
  have hA0pos : (0 : ℝ) < A0 := by
    rw [hA0, hcast]
    exact mul_pos (lt_min (inv_pos.2 hgamma) hhgapR)
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hAmp0 : (0 : ℝ) ≤ Clp * A0 *
      (3 : ℝ) ^ (-((d : ℝ) / 8) * ((K : ℝ) - (m : ℝ))) :=
    mul_nonneg (mul_nonneg hClp0.le hA0pos.le)
      (Real.rpow_pos_of_pos (by norm_num) _).le
  have hApos : (0 : ℝ) < 2 * (M.gamma ^ (100 : ℕ) + Clp * A0 *
      (3 : ℝ) ^ (-((d : ℝ) / 8) * ((K : ℝ) - (m : ℝ)))) := by
    have h1 : (0 : ℝ) < M.gamma ^ (100 : ℕ) := pow_pos hgamma 100
    linarith
  refine integrable_of_abs_le_shift_add_kappa_sq' (B := 0)
    (W := fun omega : Cutoff.ShellSeq d => 1 +
      cubeEuclideanLpNorm (originCube d K) 8 (wD omega).toH1Function.grad ^ (2 : ℕ) +
      cubeEuclideanLpNorm (originCube d K) 8 (wN omega).toH1Function.grad ^ (2 : ℕ) +
      Provider.Stream.streamIncrementLpNorm 8 K (m - (hgap : ℤ)) m omega ^ (2 : ℕ))
    (b := 1 + Chead + Clp * A0) one_pos hApos
    (by have h := mul_nonneg hClp0.le hA0pos.le; linarith) hkappa0 hfmeas
    (fun omega => by positivity) (fun omega => ?_) (fun omega => ?_)
    (isBigOWith_gammaSigma_one_add hTfltail hTtail)
  · rw [zero_add]
    exact hkappa omega (wD omega) (wN omega) (hDmem omega) (hNmem omega)
  · have h1 := hTflbd omega (wD omega) (hwD omega) (wN omega) (hwN omega)
    have h2 := hTbd omega
    linarith


/-! ## The integrability of the conjugated quadratic form -/

open ProbabilityTheory in
private theorem toFullBlockMat_eq_blockMatEntry' (A : BlockMat d) (a b : BlockCoord d) :
    toFullBlockMat A a b = blockMatEntry A a b := by
  cases a <;> cases b <;> rfl

private theorem blockQuadratic_eq_sum_entry' (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul A X) =
      ∑ a : BlockCoord d, ∑ b : BlockCoord d,
        blockMatEntry A a b * (toFullBlockVec X a * toFullBlockVec X b) := by
  rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [toFullBlockMat_eq_blockMatEntry']
  ring

private theorem measurable_toFullBlockVec_apply' {Omega : Type*}
    {mo : MeasurableSpace Omega} {W : Omega → BlockVec d}
    (hW : Measurable[mo] W) (a : BlockCoord d) :
    Measurable[mo] fun omega => toFullBlockVec (W omega) a := by
  cases a with
  | inl i => exact (measurable_pi_apply i).comp hW.fst
  | inr i => exact (measurable_pi_apply i).comp hW.snd

open ProbabilityTheory in
private theorem integrable_blockQuadratic_shellSplit (M : ABKModel d) {L n m : ℤ}
    (hLn : L ≤ n) (U : Set (Vec d)) {W : Cutoff.ShellSeq d → BlockVec d}
    {B : Cutoff.ShellSeq d → BlockMat d}
    (hBmeas : ∀ a b : BlockCoord d,
      Measurable[Cutoff.lowerShellLocalCompletion M L U]
        fun omega => blockMatEntry (B omega) a b)
    (hWmeas : Measurable[Cutoff.shellIndexSigma (Set.Ioc n m)] W)
    (hB : ∀ a b : BlockCoord d,
      Integrable (fun omega => blockMatEntry (B omega) a b) M.P.toMeasure)
    (hW : ∀ a b : BlockCoord d,
      Integrable
        (fun omega => toFullBlockVec (W omega) a * toFullBlockVec (W omega) b)
        M.P.toMeasure) :
    Integrable
      (fun omega => blockVecDot (W omega) (blockMatVecMul (B omega) (W omega)))
      M.P.toMeasure := by
  classical
  have hindep := Cutoff.indep_lowerShellLocalCompletion_shellIndexSigma_Ioc M (m := m) hLn U
  have hfun : ∀ a b : BlockCoord d,
      IndepFun (fun omega => blockMatEntry (B omega) a b)
        (fun omega => toFullBlockVec (W omega) a * toFullBlockVec (W omega) b)
        M.P.toMeasure := by
    intro a b
    have hWab : Measurable[Cutoff.shellIndexSigma (Set.Ioc n m)]
        fun omega => toFullBlockVec (W omega) a * toFullBlockVec (W omega) b :=
      (measurable_toFullBlockVec_apply' hWmeas a).mul
        (measurable_toFullBlockVec_apply' hWmeas b)
    exact (IndepFun_iff_Indep _ _ M.P.toMeasure).mpr
      (indep_of_indep_of_le_right
        (indep_of_indep_of_le_left hindep (hBmeas a b).comap_le) hWab.comap_le)
  have hprod : ∀ a b : BlockCoord d,
      Integrable (fun omega => blockMatEntry (B omega) a b *
        (toFullBlockVec (W omega) a * toFullBlockVec (W omega) b)) M.P.toMeasure :=
    fun a b => (hfun a b).integrable_mul (hB a b) (hW a b)
  have hEq : (fun omega =>
        blockVecDot (W omega) (blockMatVecMul (B omega) (W omega))) =
      fun omega => ∑ a : BlockCoord d, ∑ b : BlockCoord d,
        blockMatEntry (B omega) a b *
          (toFullBlockVec (W omega) a * toFullBlockVec (W omega) b) := by
    funext omega
    exact blockQuadratic_eq_sum_entry' _ _
  rw [hEq]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hprod a b

/-! ## Sample measurability of the coarse matrix and of the good-event energy -/

private theorem aestronglyMeasurable_blockMatEntry_switchCubeMatrix [NeZero d]
    (M : ABKModel d) (scale : ℤ) (R : TriadicCube d) (alpha beta : BlockCoord d) :
    AEStronglyMeasurable
      (fun w : CutoffSample d => blockMatEntry (switchCubeMatrix M scale R w) alpha beta)
      (cutoffSampleLaw M).toMeasure := by
  have hmeas : AEStronglyMeasurable
      (fun a : RegCoeffField d =>
        blockMatEntry (HCPolySupport.coarseBlockMatrix (cubeSet R) a.toFun) alpha beta)
      (Measure.map (coefficientCutoff M.nu scale) (cutoffSampleLaw M).toMeasure) := by
    rw [← coefficientCutoffLaw_eq_map M scale]
    exact Provider.Annealed.aestronglyMeasurable_blockMatEntry_coarseBlockMatrix_cubeSet
      (coefficientCutoffLaw_lawCarrier M scale) R alpha beta
  refine (hmeas.comp_aemeasurable
    (measurable_coefficientCutoff M.nu scale).aemeasurable).congr
    (Filter.Eventually.of_forall fun w => ?_)
  exact congrArg (fun A => blockMatEntry A alpha beta)
    (coarseBlockMatrix_cubeSet_coefficientCutoff_eq M scale w R)

theorem aestronglyMeasurable_switchCubeEnergy [NeZero d] (M : ABKModel d)
    (scale : ℤ) (R : TriadicCube d) {X : CutoffSample d → BlockVec d}
    (hX : Measurable X) :
    AEStronglyMeasurable
      (fun w : CutoffSample d => switchCubeEnergy M scale R (X w) w)
      (cutoffSampleLaw M).toMeasure := by
  have hEq : (fun w : CutoffSample d => switchCubeEnergy M scale R (X w) w) =
      fun w : CutoffSample d => ∑ alpha : BlockCoord d, ∑ beta : BlockCoord d,
        blockMatEntry (switchCubeMatrix M scale R w) alpha beta *
          (toFullBlockVec (X w) alpha * toFullBlockVec (X w) beta) := by
    funext w
    exact blockQuadratic_eq_sum_entry' (switchCubeMatrix M scale R w) (X w)
  rw [hEq]
  refine Finset.aestronglyMeasurable_fun_sum _ fun alpha _ => ?_
  refine Finset.aestronglyMeasurable_fun_sum _ fun beta _ => ?_
  exact (aestronglyMeasurable_blockMatEntry_switchCubeMatrix M scale R alpha beta).mul
    (((measurable_toFullBlockVec_apply' hX alpha).mul
      (measurable_toFullBlockVec_apply' hX beta)).aestronglyMeasurable)

private theorem switchCubeEnergy_nonneg' (M : ABKModel d) (scale : ℤ)
    (R : TriadicCube d) (X : BlockVec d) (w : CutoffSample d) :
    0 ≤ switchCubeEnergy M scale R X w :=
  blockVecDot_coarseBlockMatrix_nonneg _ _ _

/-! ## The per-cube switch with the shell size taken almost surely -/

private theorem switchCubeEnergy_indicator_le_ae' (dimension : 2 ≤ d) [NeZero d]
    (M : ABKModel d) (Ccg : ℝ) (Q : TriadicCube d) (jj : ℕ)
    {lowScale highScale : ℤ} (hle : lowScale ≤ highScale)
    (P : TriadicCube d → CutoffSample d → BlockVec d) {S : ℝ} (hS0 : 0 < S)
    (hshell : ∀ R ∈ descendantsAtDepth Q jj,
      ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
        omega ∈ Provider.BadEvents.goodLocalEvent M Ccg R lowScale →
          (centeredFreshShellUnitCube M R hle omega).w1Infinity ^ 2 ≤
            gridSwitchDiscount Q jj lowScale ^ 2 * S *
              Ch02.lambdaSq R (3 / 8) (.finite 2)
                (coefficientCutoffTriadicCoeffFamily M lowScale omega)) :
    ∀ R ∈ descendantsAtDepth Q jj,
      ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
        switchCubeEnergy M highScale R (P R omega) omega *
            (principalBadEvent M Ccg R lowScale)ᶜ.indicator
              (fun _ => (1 : ℝ)) omega ≤
          (1 + (3 / 2 : ℝ) * gridSwitchDiscount Q jj lowScale) *
              switchCubeQuad M lowScale highScale R (P R omega) omega +
            principalSwitchLoadConst d *
                ((3 / 2 : ℝ) * gridSwitchDiscount Q jj lowScale) *
              switchEllipLoad S (P R omega) := by
  classical
  intro R hR
  filter_upwards
    [responseSensitivityConst_mul_gradientW1Infinity_centeredFreshShell_le_ae
      M Ccg R hle (highScale := highScale), hshell R hR] with omega hgate hsh
  have hquad0 : (0 : ℝ) ≤ switchCubeQuad M lowScale highScale R (P R omega) omega :=
    switchCubeQuad_nonneg M lowScale highScale R (P R omega) omega
  have hload0 : (0 : ℝ) ≤ switchEllipLoad S (P R omega) :=
    switchEllipLoad_nonneg hS0 (P R omega)
  have hCload : 0 < principalSwitchLoadConst d :=
    principalSwitchLoadConst_pos dimension
  have hD0 : 0 < gridSwitchDiscount Q jj lowScale := gridSwitchDiscount_pos Q jj lowScale
  by_cases hmem : omega ∈ Provider.BadEvents.goodLocalEvent M Ccg R lowScale
  · have hmem' : omega ∈ (principalBadEvent M Ccg R lowScale)ᶜ := by
      rwa [compl_principalBadEvent]
    rw [Set.indicator_of_mem hmem', mul_one]
    have hgrad : Provider.BadEvents.responseSensitivityConst d *
        (centeredFreshShellUnitCube M R hle omega).gradientW1Infinity ≤
        gridSwitchDiscount Q jj lowScale *
          Ch02.lambdaSq R (3 / 8) (.finite 2)
            (coefficientCutoffTriadicCoeffFamily M lowScale omega) := by
      have h := hgate hmem
      rwa [gridSwitchDiscount_eq_of_mem Q jj lowScale hR] at h
    exact blockVecDot_coarseBlockMatrix_le_switch_absorbed_cube dimension M R
      lowScale highScale omega (centeredFreshShellUnitCube M R hle omega)
      (freshShellCubeAverage_skew R omega.1 lowScale highScale)
      (centeredFreshShellUnitCube_shift M R hle omega)
      hD0 (gridSwitchDiscount_le_one Q jj lowScale) hS0
      (lambdaSq_coefficientCutoffTriadicCoeffFamily_pos M R lowScale omega) hgrad
      (hsh hmem) (P R omega)
  · have hmem' : omega ∉ (principalBadEvent M Ccg R lowScale)ᶜ := by
      rwa [compl_principalBadEvent]
    rw [Set.indicator_of_notMem hmem', mul_zero]
    have h1 : (0 : ℝ) ≤ (1 + (3 / 2 : ℝ) * gridSwitchDiscount Q jj lowScale) *
        switchCubeQuad M lowScale highScale R (P R omega) omega :=
      mul_nonneg (by linarith) hquad0
    have h2 : (0 : ℝ) ≤ principalSwitchLoadConst d *
        ((3 / 2 : ℝ) * gridSwitchDiscount Q jj lowScale) *
          switchEllipLoad S (P R omega) :=
      mul_nonneg (mul_nonneg hCload.le (by linarith)) hload0
    linarith

private theorem ccg_pos_of_gate' [NeZero d] {Ccg : ℝ}
    (hccg : 2 * (d : ℝ) ^ 6 ≤ Ccg * Provider.BadEvents.sensitivityConstMax d ^ 2) :
    0 < Ccg := by
  have hCsq : (0 : ℝ) < Provider.BadEvents.sensitivityConstMax d ^ 2 :=
    pow_pos (Provider.BadEvents.sensitivityConstMax_pos d) 2
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hd6 : (1 : ℝ) ≤ (d : ℝ) ^ 6 := one_le_pow₀ hd1
  by_contra hcon
  push Not at hcon
  nlinarith [mul_nonneg (neg_nonneg.2 hcon) hCsq.le]


/-! ## The consumer-closed successor -/

private theorem principalEnergy_scaleSum_independent_bound :
    ∀ (d : ℕ) (g2 : ℝ),
      (∀ (M : ABKModel d),
          M.gamma ≤ g2 →
            ∀ (m0 : ℤ) (Eind : { E : ℝ // (1 : ℝ) ≤ E }),
              Frozen.Section3.inductionState M m0 Eind →
                ∀ (m K : ℤ) (hgap : ℕ),
                  (0 : ℕ) < hgap →
                    m - (↑hgap : ℤ) ≤ m0 →
                      (↑hgap : ℝ) ≤ (6 : ℝ) * Disorder.cstar M * M.gamma⁻¹ →
                        (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (↑K : ℝ) - (↑m : ℝ) →
                          ∀ (e e' : Vec d),
                            Ch02.vecNorm e ≤ (1 : ℝ) →
                              Ch02.vecNorm e' ≤ (1 : ℝ) →
                                ∀ (jd : ℕ),
                                  ∀ R ∈ descendantsAtDepth (originCube d K) jd,
                                    ∀ (wD : ShellSeq d → H10Function (openCubeSet (originCube d K)))
                                      (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet
                                        (originCube d K))),
                                      (∀ (omega : ShellSeq d),
                                          IsZeroTraceDirichletRhsWeakSolution
                                            (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
                                            (openCubeSet (originCube d K)) (wD omega) fun (x : Vec
                                              d) =>
                                            -streamForcing (↑(Annealed.sigmaBar M (m - (↑hgap :
                                              ℤ))) : ℝ)⁻¹ omega
                                                (m - (↑hgap : ℤ)) m e x) →
                                        (∀ (omega : ShellSeq d),
                                            IsMeanZeroNeumannRhsWeakSolution
                                              (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
                                              (openCubeSet (originCube d K)) (wN omega) fun (x :
                                                Vec d) =>
                                              -streamForcing (↑(Annealed.sigmaBar M (m - (↑hgap :
                                                ℤ))) : ℝ)⁻¹ omega
                                                  (m - (↑hgap : ℤ)) m e' x) →
                                          ∀ (alpha beta : BlockCoord d),
                                            Integrable
                                              (fun (omega : ShellSeq d) =>
                                                toFullBlockVec
                                                    (gaugedPrincipalLoadShell (Annealed.sigmaBar M
                                                      (m - (↑hgap : ℤ))) R
                                                      (m - (↑hgap : ℤ)) m e e' wD wN omega)
                                                    alpha *
                                                  toFullBlockVec
                                                    (gaugedPrincipalLoadShell (Annealed.sigmaBar M
                                                      (m - (↑hgap : ℤ))) R
                                                      (m - (↑hgap : ℤ)) m e e' wD wN omega)
                                                    beta)
                                              (↑M.P : Measure (ℤ → Frozen.Assumptions.ShellField
                                                d))) →
        ∀ (M : ABKModel d) (m0 : ℤ) (Eind : { E : ℝ // (1 : ℝ) ≤ E }),
          Frozen.Section3.inductionState M m0 Eind →
            ∀ (m K : ℤ) (hgap : ℕ),
              (0 : ℕ) < hgap →
                m - (↑hgap : ℤ) ≤ m0 →
                  (↑hgap : ℝ) ≤ (6 : ℝ) * Disorder.cstar M * M.gamma⁻¹ →
                    (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (↑K : ℝ) - (↑m : ℝ) →
                      ∀ (e e' : Vec d),
                        Ch02.vecNorm e ≤ (1 : ℝ) →
                          Ch02.vecNorm e' ≤ (1 : ℝ) →
                            ∀ (j : ℕ),
                              NeZero d →
                                M.gamma ≤ g2 →
                                  ∀ (wD : ShellSeq d → H10Function (openCubeSet (originCube d K))),
                                    (∀ (omega : ShellSeq d),
                                        IsZeroTraceDirichletRhsWeakSolution
                                          (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
                                            (openCubeSet (originCube d K))
                                          (wD omega) fun (x : Vec d) =>
                                          -streamForcing (↑(Annealed.sigmaBar M (m - (↑hgap : ℤ)))
                                            : ℝ)⁻¹ omega
                                              (m - (↑hgap : ℤ)) m e x) →
                                      ∀ (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet
                                        (originCube d K))),
                                        (∀ (omega : ShellSeq d),
                                            IsMeanZeroNeumannRhsWeakSolution
                                              (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
                                              (openCubeSet (originCube d K)) (wN omega) fun (x :
                                                Vec d) =>
                                              -streamForcing (↑(Annealed.sigmaBar M (m - (↑hgap :
                                                ℤ))) : ℝ)⁻¹ omega
                                                  (m - (↑hgap : ℤ)) m e' x) →
                                          ∀ R ∈ descendantsAtDepth (originCube d K) j,
                                            ∫ (omega : CutoffSample d),
                                                switchCubeQuad M (m - (↑hgap : ℤ)) m R
                                                  (principalPz (Annealed.sigmaBar M (m - (↑hgap :
                                                    ℤ))) (↑omega : ShellSeq d)
                                                    (m - (↑hgap : ℤ)) m e e' R (wD (↑omega :
                                                      ShellSeq d))
                                                    (wN (↑omega : ShellSeq d)))
                                                  omega ∂(↑(cutoffSampleLaw M) : Measure
                                                    (CutoffSample d)) =
                                              ∫ (omega : CutoffSample d),
                                                blockVecDot
                                                  (gaugedPrincipalLoadShell (Annealed.sigmaBar M
                                                    (m - (↑hgap : ℤ))) R
                                                    (m - (↑hgap : ℤ)) m e e' wD wN (↑omega :
                                                      ShellSeq d))
                                                  (blockMatVecMul
                                                    (Ch04.annealedBlockMatrixAtScale
                                                      (coefficientCutoffLaw M (m - (↑hgap : ℤ)))
                                                      ((originCube d K).scale - (↑j : ℤ)))
                                                    (gaugedPrincipalLoadShell (Annealed.sigmaBar M
                                                      (m - (↑hgap : ℤ))) R
                                                      (m - (↑hgap : ℤ)) m e e' wD wN
                                                      (↑omega :
                                                        ShellSeq d))) ∂(↑(cutoffSampleLaw M) :
                                                          Measure (CutoffSample d)) := by
  intro d _ hWint M m0 Eind hstate m K hgap hhpos hm hh hK e e' he he' j _ h2 wD hwD wN hwN R hR
  obtain ⟨B, hBmeas, hBrep⟩ :=
    exists_measurable_representative_switchCubeMatrix M (m - (hgap : ℤ)) R
      (subset_refl (cubeSet R))
  have key := integral_blockQuadratic_shellSplit_eq_gaugedPrincipalLoadShell M
    (Annealed.sigmaBar M (m - (hgap : ℤ))) (le_refl (m - (hgap : ℤ))) hR hBmeas hBrep
    ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹
    ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ e e' e e' wD wN hwD hwN
    (fun alpha beta => hWint M h2 m0 Eind hstate m K hgap hhpos hm hh hK e e' he he'
      j R hR wD wN hwD hwN alpha beta)
  rw [transport_shellSeq_integral M
      (fun omega : Cutoff.ShellSeq d =>
        blockVecDot (gaugedPrincipalLoadShell
            (Annealed.sigmaBar M (m - (hgap : ℤ))) R (m - (hgap : ℤ)) m e e' wD wN omega)
          (blockMatVecMul (B omega)
            (gaugedPrincipalLoadShell
              (Annealed.sigmaBar M (m - (hgap : ℤ))) R (m - (hgap : ℤ)) m e e' wD wN omega))),
    transport_shellSeq_integral M
      (fun omega : Cutoff.ShellSeq d =>
        blockVecDot (gaugedPrincipalLoadShell
            (Annealed.sigmaBar M (m - (hgap : ℤ))) R (m - (hgap : ℤ)) m e e' wD wN omega)
          (blockMatVecMul
            (Ch04.annealedBlockMatrixAtScale
              (Cutoff.coefficientCutoffLaw M (m - (hgap : ℤ)))
              (((originCube d K).scale : ℤ) - (j : ℤ)))
            (gaugedPrincipalLoadShell
              (Annealed.sigmaBar M (m - (hgap : ℤ))) R (m - (hgap : ℤ)) m e e' wD wN omega)))]
    at key
  rw [← key]
  refine integral_congr_ae ?_
  filter_upwards [hBrep] with w hw
  rw [switchCubeQuad_eq_blockVecDot_gaugedSwitchLoad,
    ← gaugedPrincipalLoadShell_val (Annealed.sigmaBar M (m - (hgap : ℤ))) R
      (m - (hgap : ℤ)) m e e' wD wN w, hw]

theorem exists_smallCoupling_principalEnergy_bound_of_gate
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
        ∀ (m0 : ℤ) (Eind : {E : ℝ // 1 ≤ E}),
          Algsuperdiff.Frozen.Section3.inductionState M m0 Eind →
          ∀ (m K : ℤ) (hgap : ℕ), 0 < hgap → m - (hgap : ℤ) ≤ m0 →
            (hgap : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
            (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (K : ℝ) - (m : ℝ) →
            ∀ e e' : Vec d, Ch02.vecNorm e ≤ 1 → Ch02.vecNorm e' ≤ 1 →
              ∀ (j a : ℕ), recurrenceGapMultiplierFloor ≤ a →
                ((originCube d K).scale : ℤ) - (j : ℤ) =
                  recurrenceMesoScale a M.gamma m (hgap : ℤ) →
                ∀ Ccg : ℝ,
                  2 * (d : ℝ) ^ 6 ≤
                    Ccg * Provider.BadEvents.sensitivityConstMax d ^ 2 →
                  ∃ (wD : Cutoff.ShellSeq d →
                      H10Function (openCubeSet (originCube d K)))
                    (wN : Cutoff.ShellSeq d →
                      H1MeanZeroFunction (openCubeSet (originCube d K))),
                    (∀ omega : Cutoff.ShellSeq d,
                      IsZeroTraceDirichletRhsWeakSolution
                        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                        (openCubeSet (originCube d K)) (wD omega)
                        (fun x => -streamForcing
                          ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ omega
                          (m - (hgap : ℤ)) m e x)) ∧
                    (∀ omega : Cutoff.ShellSeq d,
                      IsMeanZeroNeumannRhsWeakSolution
                        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                        (openCubeSet (originCube d K)) (wN omega)
                        (fun x => -streamForcing
                          ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ omega
                          (m - (hgap : ℤ)) m e' x)) ∧
                    (∀ R ∈ descendantsAtDepth (originCube d K) j,
                      Integrable (fun omega : Cutoff.CutoffSample d =>
                        switchCubeEnergy M m R
                            (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ)))
                              omega.val (m - (hgap : ℤ)) m e e' R
                              (wD omega.val) (wN omega.val)) omega *
                          (principalBadEvent M Ccg R
                            (m - (hgap : ℤ)))ᶜ.indicator (fun _ => (1 : ℝ)) omega)
                        (Cutoff.cutoffSampleLaw M).toMeasure) ∧
                    descendantsAverage (originCube d K) j
                        (fun R => ∫ omega : Cutoff.CutoffSample d,
                          switchCubeEnergy M m R
                              (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ)))
                                omega.val (m - (hgap : ℤ)) m e e' R
                                (wD omega.val) (wN omega.val)) omega *
                            (principalBadEvent M Ccg R
                              (m - (hgap : ℤ)))ᶜ.indicator (fun _ => (1 : ℝ)) omega
                          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                      (1 + M.gamma ^ (6 : ℕ)) *
                          descendantsAverage (originCube d K) j
                            (fun R => ∫ omega : Cutoff.CutoffSample d,
                              blockVecDot
                                (gaugedPrincipalLoadShell
                                  (Annealed.sigmaBar M (m - (hgap : ℤ))) R
                                  (m - (hgap : ℤ)) m e e' wD wN omega.val)
                                (blockMatVecMul
                                  (Ch04.annealedBlockMatrixAtScale
                                    (Cutoff.coefficientCutoffLaw M (m - (hgap : ℤ)))
                                    (((originCube d K).scale : ℤ) - (j : ℤ)))
                                  (gaugedPrincipalLoadShell
                                    (Annealed.sigmaBar M (m - (hgap : ℤ))) R
                                    (m - (hgap : ℤ)) m e e' wD wN omega.val))
                              ∂(Cutoff.cutoffSampleLaw M).toMeasure) +
                        M.gamma ^ (6 : ℕ) / 2 := by
  classical
  obtain ⟨g1, hg1p, hg1q, hbud⟩ :=
    exists_smallCoupling_principalEnergy_bound_of_centering
      d hd
  obtain ⟨g2, hg2p, hg2q, hWint⟩ :=
    exists_gamma0_integrable_toFullBlockVec_gaugedPrincipalLoadShell_mul d hd
  obtain ⟨g3, hg3p, hg3q, hSqInt⟩ :=
    exists_gamma0_integrable_switchEllipLoad_principalPz_sq d hd
  refine ⟨min g1 (min g2 g3), lt_min hg1p (lt_min hg2p hg3p),
    le_trans (min_le_left _ _) hg1q, ?_⟩
  intro M hMgamma m0 Eind hstate m K hgap hhpos hm hh hK e e' he he' j a ha hscale
    Ccg hccg
  have : NeZero d := ⟨by omega⟩
  have h1 : M.gamma ≤ g1 := le_trans hMgamma (min_le_left _ _)
  have h2 : M.gamma ≤ g2 :=
    le_trans hMgamma (le_trans (min_le_right _ _) (min_le_left _ _))
  have h3 : M.gamma ≤ g3 :=
    le_trans hMgamma (le_trans (min_le_right _ _) (min_le_right _ _))
  have hle : m - (hgap : ℤ) ≤ m := by omega
  obtain ⟨wD, hwD⟩ : ∃ wD : Cutoff.ShellSeq d →
      H10Function (openCubeSet (originCube d K)),
      ∀ omega : Cutoff.ShellSeq d,
        IsZeroTraceDirichletRhsWeakSolution
          (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
          (openCubeSet (originCube d K)) (wD omega)
          (fun x => -streamForcing
            ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ omega
            (m - (hgap : ℤ)) m e x) :=
    ⟨fun omega => Classical.choose
      (exists_isZeroTraceDirichletRhsWeakSolution_streamForcing (originCube d K)
        ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ omega (m - (hgap : ℤ)) m e),
     fun omega => Classical.choose_spec
      (exists_isZeroTraceDirichletRhsWeakSolution_streamForcing (originCube d K)
        ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ omega (m - (hgap : ℤ)) m e)⟩
  obtain ⟨wN, hwN⟩ : ∃ wN : Cutoff.ShellSeq d →
      H1MeanZeroFunction (openCubeSet (originCube d K)),
      ∀ omega : Cutoff.ShellSeq d,
        IsMeanZeroNeumannRhsWeakSolution
          (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
          (openCubeSet (originCube d K)) (wN omega)
          (fun x => -streamForcing
            ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ omega
            (m - (hgap : ℤ)) m e' x) :=
    ⟨fun omega => Classical.choose
      (exists_isMeanZeroNeumannRhsWeakSolution_streamForcing (originCube d K)
        ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ omega (m - (hgap : ℤ)) m e'),
     fun omega => Classical.choose_spec
      (exists_isMeanZeroNeumannRhsWeakSolution_streamForcing (originCube d K)
        ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ omega (m - (hgap : ℤ)) m e')⟩
  refine ⟨wD, wN, hwD, hwN, ?_⟩
  have hemb : MeasurableEmbedding (Subtype.val : CutoffSample d → ShellSeq d) :=
    MeasurableEmbedding.subtype_coe (measurableSet_lowerTailGoodSet d)
  -- sample measurability of the load, cube by cube
  have hPzmeas : ∀ R ∈ descendantsAtDepth (originCube d K) j,
      Measurable (fun z : Cutoff.CutoffSample d =>
        principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val (m - (hgap : ℤ)) m
          e e' R (wD z.val) (wN z.val)) := by
    intro R hR
    exact ((measurable_shellIndexSigma_principalPz hR
      (Annealed.sigmaBar M (m - (hgap : ℤ)))
      ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹
      ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹
      (m - (hgap : ℤ)) m e e' e e' wD wN hwD hwN).mono
      (Cutoff.shellIndexSigma_le_borel _) le_rfl).comp measurable_subtype_coe
  have hmeasR : ∀ R ∈ descendantsAtDepth (originCube d K) j,
      Measurable (fun z : Cutoff.CutoffSample d =>
        switchEllipLoad ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))
          (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
            (m - (hgap : ℤ)) m e e' R (wD z.val) (wN z.val))) :=
    fun R hR => measurable_switchEllipLoad_comp _ (hPzmeas R hR)
  have hintR : ∀ R ∈ descendantsAtDepth (originCube d K) j,
      Integrable (fun z : Cutoff.CutoffSample d =>
        switchEllipLoad ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))
            (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
              (m - (hgap : ℤ)) m e e' R (wD z.val) (wN z.val)) ^ (2 : ℕ))
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    intro R hR
    have hsh := hSqInt M h3 m0 Eind hstate m K hgap hhpos hm hh hK e e' he he' j R hR
      wD wN hwD hwN
    rw [← map_cutoffSampleLaw_val M, hemb.integrable_map_iff] at hsh
    exact hsh
  have hellipInt : ∀ R ∈ descendantsAtDepth (originCube d K) j,
      Integrable (fun z : Cutoff.CutoffSample d =>
        switchEllipLoad ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))
          (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
            (m - (hgap : ℤ)) m e e' R (wD z.val) (wN z.val)))
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    intro R hR
    refine ((integrable_const ((1 : ℝ) / 2)).add
      ((hintR R hR).const_mul ((1 : ℝ) / 2))).mono'
      (hmeasR R hR).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    have h0 : (0 : ℝ) ≤ switchEllipLoad
        ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))
        (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
          (m - (hgap : ℤ)) m e e' R (wD z.val) (wN z.val)) :=
      switchEllipLoad_nonneg (Annealed.sigmaBar M (m - (hgap : ℤ))).2 _
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg h0]
    nlinarith [sq_nonneg (switchEllipLoad
      ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))
      (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
        (m - (hgap : ℤ)) m e e' R (wD z.val) (wN z.val)) - 1)]
  -- the representative of the coarse matrix, and the two consequences
  have hcubeInt : ∀ R ∈ descendantsAtDepth (originCube d K) j,
      Integrable (fun omega : Cutoff.CutoffSample d =>
        switchCubeQuad M (m - (hgap : ℤ)) m R
          (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) omega.val
            (m - (hgap : ℤ)) m e e' R (wD omega.val) (wN omega.val)) omega)
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    intro R hR
    obtain ⟨B, hBmeas, hBrep⟩ :=
      exists_measurable_representative_switchCubeMatrix M (m - (hgap : ℤ)) R
        (subset_refl (cubeSet R))
    have hInt := integrable_blockQuadratic_shellSplit M
      (le_refl (m - (hgap : ℤ))) (cubeSet R) hBmeas
      (measurable_shellIndexSigma_gaugedPrincipalLoadShell hR
        (Annealed.sigmaBar M (m - (hgap : ℤ)))
        ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹
        ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹
        (m - (hgap : ℤ)) m e e' e e' wD wN hwD hwN)
      (fun alpha beta =>
        integrable_blockMatEntry_of_representative M (m - (hgap : ℤ)) R hBrep alpha beta)
      (fun alpha beta => hWint M h2 m0 Eind hstate m K hgap hhpos hm hh hK e e' he he'
        j R hR wD wN hwD hwN alpha beta)
    rw [← map_cutoffSampleLaw_val M, hemb.integrable_map_iff] at hInt
    refine hInt.congr ?_
    filter_upwards [hBrep] with w hw
    rw [Function.comp_apply, hw,
      gaugedPrincipalLoadShell_val (Annealed.sigmaBar M (m - (hgap : ℤ))) R
        (m - (hgap : ℤ)) m e e' wD wN w,
      ← switchCubeQuad_eq_blockVecDot_gaugedSwitchLoad M (m - (hgap : ℤ)) m R
        (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) w.val (m - (hgap : ℤ)) m
          e e' R (wD w.val) (wN w.val)) w]
  have hshell := shell_hypothesis_of_centeringConst_ae M (ccg_pos_of_gate' hccg)
    (originCube d K) j hle
    (shellSizeThreshold_centeringConst_le_sigmaBar M hstate hm hccg)
  have hdom := switchCubeEnergy_indicator_le_ae' hd M Ccg (originCube d K) j hle
    (fun R z => principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
      (m - (hgap : ℤ)) m e e' R (wD z.val) (wN z.val))
    (Annealed.sigmaBar M (m - (hgap : ℤ))).2 hshell
  have hgoodInt : ∀ R ∈ descendantsAtDepth (originCube d K) j,
      Integrable (fun omega : Cutoff.CutoffSample d =>
        switchCubeEnergy M m R
            (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) omega.val
              (m - (hgap : ℤ)) m e e' R (wD omega.val) (wN omega.val)) omega *
          (principalBadEvent M Ccg R (m - (hgap : ℤ)))ᶜ.indicator
            (fun _ => (1 : ℝ)) omega)
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    intro R hR
    have hind : Measurable
        ((principalBadEvent M Ccg R (m - (hgap : ℤ)))ᶜ.indicator
          (fun _ : Cutoff.CutoffSample d => (1 : ℝ))) :=
      measurable_one.indicator (measurableSet_principalBadEvent M Ccg R
        (m - (hgap : ℤ))).compl
    refine Integrable.mono'
      (((hcubeInt R hR).const_mul
          (1 + (3 / 2 : ℝ) * gridSwitchDiscount (originCube d K) j
            (m - (hgap : ℤ)))).add
        ((hellipInt R hR).const_mul (principalSwitchLoadConst d *
          ((3 / 2 : ℝ) * gridSwitchDiscount (originCube d K) j (m - (hgap : ℤ))))))
      ((aestronglyMeasurable_switchCubeEnergy M m R (hPzmeas R hR)).mul
        hind.aestronglyMeasurable) ?_
    filter_upwards [hdom R hR] with omega homega
    have hnn : (0 : ℝ) ≤ switchCubeEnergy M m R
        (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) omega.val
          (m - (hgap : ℤ)) m e e' R (wD omega.val) (wN omega.val)) omega *
        (principalBadEvent M Ccg R (m - (hgap : ℤ)))ᶜ.indicator
          (fun _ => (1 : ℝ)) omega := by
      refine mul_nonneg (switchCubeEnergy_nonneg' M m R _ omega) ?_
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) omega
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg hnn]
    exact homega
  -- the independence factorization at the chosen families
  have hindep := @principalEnergy_scaleSum_independent_bound (d) (g2) (hWint) (M) (m0) (Eind)
    (hstate) (m) (K) (hgap) (hhpos) (hm) (hh) (hK) (e) (e') (he) (he') (j) (this) (h2) (wD) (hwD)
      (wN) (hwN)
  exact ⟨hgoodInt, hbud M h1 m0 Eind hstate m K hgap hhpos hm hh hK e e' he he' j a ha hscale
    Ccg hccg (((originCube d K).scale : ℤ) - (j : ℤ)) m hle
    (fun z : Cutoff.CutoffSample d => wD z.val)
    (fun z : Cutoff.CutoffSample d => wN z.val)
    (fun z => hwD z.val) (fun z => hwN z.val) hmeasR hintR hgoodInt hcubeInt
    (fun R omega => gaugedPrincipalLoadShell
      (Annealed.sigmaBar M (m - (hgap : ℤ))) R (m - (hgap : ℤ)) m e e' wD wN omega.val)
    hindep⟩


end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
