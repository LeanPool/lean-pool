/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseBudget

/-!
# PrincipalResponseComposeAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the assembly of `e.lower.bound.principal.one`

Target display, `e.lower.bound.principal.one`, in ABK26 (block):

```
  avsum_{z in 3^n Zd cap cu_K} E[ P_z . bfA_m(z+cu_n) P_z ]
    <= (1 + C E^2 |log cgamma|^2 cgamma)
         avsum_z E[ G_{-(h)_{z+cu_n}} P_z . bfAhom_{m-h} G_{-(h)_{z+cu_n}} P_z ]
       + cgamma^6 .
```

The manuscript derives it in one sentence: "Combining the above two displays
with `e.lower.bound.principal.one.pre` leads to `e.lower.bound.principal.one`."
The three inputs of that sentence are

* `e.lower.bound.principal.one.pre`, the **good-event** half, which reads
  `avsum_z E[ P_z. bfA_m(z+cu_n) P_z 1_{Q_z} ] <= (1 + cgamma^6) avsum_z E[ G
  P_z. bfAhom_{m-h}(z+cu_n) G P_z ] + cgamma^6/2`;
* `e.use.also.for.the.upper.bound`, the passage from the finite-cube annealed
  matrix `bfAhom_{m-h}(cu_n)` to the infinite-volume `bfAhom_{m-h}`, at the
  factor `1 +^2 |log cgamma|^2 cgamma`.

This module performs exactly that combination.

## What is supplied and what is assumed

* The **indicator split** `E[X] = E[X 1_{Q}] + E[X 1_{not Q}]` at the grid
  (`integral_indicator_split`, `descendantsAverage_add_real`).  The two
  integrability side conditions are its only cost.
* The **cube-to-limit step** is *not* assumed.  It is produced from the proved
  leg (v): `annealedCubeBlockQuadratic_le_annealedLimitBlockQuadratic`
  (`e.use.also.for.the.upper.bound` in Loewner form) integrated and
  grid-averaged in `descendantsAverage_integral_annealedCubeBlockQuadratic_le`,
  together with `cubeAnnealedProbeDefect_le_logSq_budget`, which is the
  manuscript's own budget at `t = |log cgamma|^{-1}`.  So the printed factor
  `C E^2 |log cgamma|^2 cgamma` appears here as the *named* quantity
  `principalResponseSwitchBudget`, with `C` the proved
  `principalResponseBudgetConst` and the scale-gap factor `3^{2K}` visible.
* The **good-event half** `hgood` is a named binder: it is the source display
  `e.lower.bound.principal.one.pre`, whose proof combines the `l.J.sensitivity`
  gauge switch of sub-step (i), the ellipticity budget of sub-step (ii) and the
  independence step of sub-step (iii).  It is a conclusion of the manuscript at
  a `\label`ed display, not a step of the combination performed here.
* The **bad-event half** `hbad` is likewise a named binder.  Its analytic
  content is the bad-event leg at the grid average,
  `PrincipalComplementEnergy.exists_const_descendantsAverage_integral_switchCubeEnergy_badEvent_le`;
  bringing that estimate's exponential tail below the half-budget shape used
  here is the caller's step, not one performed in this module.

## Other divergences

* **The scale gap is free.**  It enters only through the free real `K` of
  `cubeAnnealedProbeDefect_le_logSq_budget`'s own gate `|log cgamma|^{-1}(L -
  n) <= K`.  The printed buffer `16` of `e.recurrence.params` is not used and
  the localization depth `j` is free.

## Binders

Every theorem below is conditional except `descendantsAverage_add_real`, which
is an unconditional identity.  None of them is a frozen declaration.  What the
caller must supply, plainly:

* `integral_indicator_split` asks for integrability of the two halves;
* `descendantsAverage_integral_annealedCubeBlockQuadratic_le` asks for the unit
  normalization `hEv` of the probe direction and integrability of the two
  quadratic forms;

`hgood` and `hbad` are `\label`ed displays of the manuscript, supplied
elsewhere; every step *between* them and the target display is performed here
rather than assumed.

## Module boundary

This module does **not** import or consume
`Provider.BadEvents.BadEventLemmaUmbrella`.  The bad-event half enters only as
the abstract binder `hbad`, so the transitional umbrella consumption described
in `PrincipalResponseComposeBadEvent` is confined to that single file and does
not leak here.

## References

* ABK26, `l.approximate.recurrence.formula`, Step 3;
  `e.lower.bound.principal.one`, `e.lower.bound.principal.one.pre`,
  `e.use.also.for.the.upper.bound`, the budget chain; `e.good.local.events`;
  `e.cgamma.constraints`; `e.recurrence.params`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Grid arithmetic -/

/-- A uniform per-cube bound with a constant factor passes to the grid average.

: this statement holds only under the propositions supplied by its binders; it
is a provider A, not a source-facing frozen declaration. -/
theorem descendantsAverage_le_mul_of_le (Q : TriadicCube d) (j : ℕ)
    {f g : TriadicCube d → ℝ} {c : ℝ}
    (h : ∀ R ∈ descendantsAtDepth Q j, f R ≤ c * g R) :
    descendantsAverage Q j f ≤ c * descendantsAverage Q j g := by
  refine le_trans (descendantsAverage_le_descendantsAverage Q j h) ?_
  exact le_of_eq (descendantsAverage_mul_left Q j c g)

/-- The grid average is additive.

Unconditional: no caller-supplied proposition enters. -/
theorem descendantsAverage_add_real (Q : TriadicCube d) (j : ℕ)
    (f g : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => f R + g R) =
      descendantsAverage Q j f + descendantsAverage Q j g := by
  classical
  change ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtDepth Q j, (f R + g R) = _
  rw [Finset.sum_add_distrib, mul_add]
  rfl

/-! ## The fold, with its excess pinned -/

/-- **The combination, with the product left exact.**

Splitting the energy over the good and bad events, applying the good-event
display at factor `1 + delta`, the bad-event budget, and the cube-to-limit step
at factor `1 + kappa`, one gets the target with the **exact** product `(1 +
delta)(1 + kappa)`.  Nothing is absorbed: a formalization must name its
constants, and this statement names them.

: this statement holds only under the propositions supplied by its binders; it
is a provider A, not a source-facing frozen declaration. -/
theorem principalResponse_fold_exact
    {total good bad cubeEnergy limEnergy delta kappa budget : ℝ}
    (hsplit : total = good + bad)
    (hgood : good ≤ (1 + delta) * cubeEnergy + budget / 2)
    (hbad : bad ≤ budget / 2)
    (hcube : cubeEnergy ≤ (1 + kappa) * limEnergy)
    (hdelta0 : 0 ≤ delta) :
    total ≤ (1 + delta) * (1 + kappa) * limEnergy + budget := by
  have h1 : (1 + delta) * cubeEnergy ≤ (1 + delta) * ((1 + kappa) * limEnergy) :=
    mul_le_mul_of_nonneg_left hcube (by linarith)
  rw [hsplit]
  nlinarith [h1, hgood, hbad]

/-- **The rename, at the visible price `C -> 3C`.**  If the good-event excess
`delta` is below the cube-to-limit budget `kappa` and below `1`, the exact
product collapses into a single factor with the constant tripled.

: this statement holds only under the propositions supplied by its binders; it
is a provider A, not a source-facing frozen declaration. -/
theorem one_add_mul_one_add_le_one_add_three_mul {delta kappa : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ kappa) (hdelta1 : delta ≤ 1) :
    (1 + delta) * (1 + kappa) ≤ 1 + 3 * kappa := by
  have hkappa0 : 0 ≤ kappa := le_trans hdelta0 hdelta
  nlinarith [hdelta0, hdelta, hdelta1, hkappa0]

/-- **The combination in the manuscript's printed shape**, with the constant
renamed rather than silently reused.

: this statement holds only under the propositions supplied by its binders; it
is a provider A, not a source-facing frozen declaration. -/
theorem principalResponse_fold_renamed
    {total good bad cubeEnergy limEnergy delta kappa budget : ℝ}
    (hsplit : total = good + bad)
    (hgood : good ≤ (1 + delta) * cubeEnergy + budget / 2)
    (hbad : bad ≤ budget / 2)
    (hcube : cubeEnergy ≤ (1 + kappa) * limEnergy)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ kappa) (hdelta1 : delta ≤ 1)
    (hlim0 : 0 ≤ limEnergy) :
    total ≤ (1 + 3 * kappa) * limEnergy + budget := by
  refine le_trans
    (principalResponse_fold_exact hsplit hgood hbad hcube hdelta0) ?_
  have hstep := mul_le_mul_of_nonneg_right
    (one_add_mul_one_add_le_one_add_three_mul hdelta0 hdelta hdelta1) hlim0
  linarith

/-! ## The indicator split -/

section Split

variable {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}

/-- The good/bad split of the energy under the expectation, against.

: this statement holds only under the propositions supplied by its binders; it
is a provider A, not a source-facing frozen declaration. -/
theorem integral_indicator_split {f : Omega → ℝ} {Ebad : Set Omega}
    (h1 : Integrable (fun omega =>
      f omega * Ebadᶜ.indicator (fun _ => (1 : ℝ)) omega) mu)
    (h2 : Integrable (fun omega =>
      f omega * Ebad.indicator (fun _ => (1 : ℝ)) omega) mu) :
    ∫ omega, f omega ∂mu =
      ∫ omega, f omega * Ebadᶜ.indicator (fun _ => (1 : ℝ)) omega ∂mu +
        ∫ omega, f omega * Ebad.indicator (fun _ => (1 : ℝ)) omega ∂mu := by
  rw [← integral_add h1 h2]
  congr 1
  funext omega
  by_cases homega : omega ∈ Ebad
  · rw [Set.indicator_of_mem homega,
      Set.indicator_of_notMem (by simpa using homega)]
    ring
  · rw [Set.indicator_of_notMem homega, Set.indicator_of_mem homega]
    ring

end Split

/-! ## Leg (v) at the grid -/

section LegFive

variable {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}

/-- **`e.use.also.for.the.upper.bound` integrated and grid-averaged.**  The proved
Loewner domination of the finite-cube annealed matrix by `(1 + delta)` times
the infinite-volume one, with `delta` the defect, passes through the
expectation and the grid average.

: this statement holds only under the propositions supplied by its binders; it
is a provider A, not a source-facing frozen declaration. -/
theorem descendantsAverage_integral_annealedCubeBlockQuadratic_le [NeZero d]
    (M : ABKModel d) (L n : ℤ) {Ev : BlockVec d} (hEv : blockVecDot Ev Ev = 1)
    (Q : TriadicCube d) (j : ℕ) (W : TriadicCube d → Omega → BlockVec d)
    (hcubeInt : ∀ R ∈ descendantsAtDepth Q j,
      Integrable (fun omega => blockVecDot (W R omega)
        (blockMatVecMul
          (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
          (W R omega))) mu)
    (hlimInt : ∀ R ∈ descendantsAtDepth Q j,
      Integrable (fun omega => blockVecDot (W R omega)
        (blockMatVecMul
          (Ch02.blockDiag ((Annealed.sigmaBar M L : ℝ) • (1 : Mat d))
            (((Annealed.sigmaBar M L : ℝ))⁻¹ • (1 : Mat d)))
          (W R omega))) mu) :
    descendantsAverage Q j (fun R => ∫ omega, blockVecDot (W R omega)
        (blockMatVecMul
          (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
          (W R omega)) ∂mu) ≤
      (1 + cubeAnnealedProbeDefect M L n Ev) *
        descendantsAverage Q j (fun R => ∫ omega, blockVecDot (W R omega)
          (blockMatVecMul
            (Ch02.blockDiag ((Annealed.sigmaBar M L : ℝ) • (1 : Mat d))
              (((Annealed.sigmaBar M L : ℝ))⁻¹ • (1 : Mat d)))
            (W R omega)) ∂mu) := by
  refine descendantsAverage_le_mul_of_le Q j ?_
  intro R hR
  have hmono := integral_mono (hcubeInt R hR)
    ((hlimInt R hR).const_mul (1 + cubeAnnealedProbeDefect M L n Ev))
    (fun omega => annealedCubeBlockQuadratic_le_annealedLimitBlockQuadratic M L n
      hEv (W R omega))
  rwa [integral_const_mul] at hmono

end LegFive

/-! ## The target display -/

section Assembly

variable {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}

/-- **The printed switch budget**^{2K} E^2 |log cgamma|^2 cgamma`, with the proved
absolute constant and the scale-gap factor both visible.  This is the quantity
the manuscript writes as^2 |log cgamma|^2 cgamma`. -/
def principalResponseSwitchBudget (M : ABKModel d) (Ec : {E : ℝ // 1 ≤ E})
    (K : ℝ) : ℝ :=
  principalResponseBudgetConst * (3 : ℝ) ^ (2 * K) *
    ((Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2 * M.gamma)

/-- **`e.lower.bound.principal.one`, assembled.**

At the field index `L` (the manuscript's `m - h`), the cube scale `n`, the
localization cube `Q` and depth `j`, for every energy observable `energy` and
every gauged doubled load `W`:

```
  avsum_R E[ energy_R ]
    <= (1 + 3 principalResponseSwitchBudget)
         avsum_R E[ W_R . bfAhom_L W_R ]
       + cgamma^6 ,
```

given the good-event display `e.lower.bound.principal.one.pre` (`hgood`), the
bad-event budget (`hbad`), and the rename gate `hrename`.  The passage from
`bfAhom_L(cu_n)` to `bfAhom_L` -- the manuscript's third input,
`e.use.also.for.the.upper.bound` -- is **not** assumed: it is produced from the
proved leg (v) and its budget.

The bad event is indexed by the grid cube, `Ebad : TriadicCube d → Set Omega`,
as the manuscript's own `Q_z` are: each cube of the depth-`j` grid carries its
own event, and the split below is performed cube by cube.  Taking `Ebad`
constant recovers the single-event reading, so nothing is lost by the indexing.

`hgood` and `hbad` are named binders: they are the manuscript's own two
`\label`ed displays, and this theorem asserts nothing about their
satisfiability.

The statement therefore holds only under the propositions supplied by its
binders; it is a conditional result, not a frozen declaration. -/
theorem descendantsAverage_integral_principalEnergy_le_annealedLimit [NeZero d]
    (M : ABKModel d) {m0 L n : ℤ} {Ec : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ec)
    (hL : L ≤ m0) (hn : n ≤ L) (hE6 : 6 ≤ (Ec : ℝ))
    (hgamE : M.gamma ≤ ((Ec : ℝ) ^ 5)⁻¹)
    (hsw : |Real.log M.gamma|⁻¹ ∈ Set.Icc (8 * M.gamma) 1)
    {Ev : BlockVec d} (hEv : blockVecDot Ev Ev = 1)
    {K : ℝ} (hgapK : |Real.log M.gamma|⁻¹ * ((Int.toNat (L - n) : ℕ) : ℝ) ≤ K)
    (Q : TriadicCube d) (j : ℕ)
    (energy : TriadicCube d → Omega → ℝ)
    (W : TriadicCube d → Omega → BlockVec d) {Ebad : TriadicCube d → Set Omega}
    (hgoodInt : ∀ R ∈ descendantsAtDepth Q j,
      Integrable (fun omega =>
        energy R omega * (Ebad R)ᶜ.indicator (fun _ => (1 : ℝ)) omega) mu)
    (hbadInt : ∀ R ∈ descendantsAtDepth Q j,
      Integrable (fun omega =>
        energy R omega * (Ebad R).indicator (fun _ => (1 : ℝ)) omega) mu)
    (hcubeInt : ∀ R ∈ descendantsAtDepth Q j,
      Integrable (fun omega => blockVecDot (W R omega)
        (blockMatVecMul
          (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
          (W R omega))) mu)
    (hlimInt : ∀ R ∈ descendantsAtDepth Q j,
      Integrable (fun omega => blockVecDot (W R omega)
        (blockMatVecMul
          (Ch02.blockDiag ((Annealed.sigmaBar M L : ℝ) • (1 : Mat d))
            (((Annealed.sigmaBar M L : ℝ))⁻¹ • (1 : Mat d)))
          (W R omega))) mu)
    (hgood : descendantsAverage Q j
        (fun R => ∫ omega,
          energy R omega * (Ebad R)ᶜ.indicator (fun _ => (1 : ℝ)) omega ∂mu) ≤
      (1 + M.gamma ^ (6 : ℕ)) *
          descendantsAverage Q j (fun R => ∫ omega, blockVecDot (W R omega)
            (blockMatVecMul
              (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
              (W R omega)) ∂mu) +
        M.gamma ^ (6 : ℕ) / 2)
    (hbad : descendantsAverage Q j
        (fun R => ∫ omega,
          energy R omega * (Ebad R).indicator (fun _ => (1 : ℝ)) omega ∂mu) ≤
      M.gamma ^ (6 : ℕ) / 2)
    (hrename : M.gamma ^ (6 : ℕ) ≤ principalResponseSwitchBudget M Ec K) :
    descendantsAverage Q j (fun R => ∫ omega, energy R omega ∂mu) ≤
      (1 + 3 * principalResponseSwitchBudget M Ec K) *
          descendantsAverage Q j (fun R => ∫ omega, blockVecDot (W R omega)
            (blockMatVecMul
              (Ch02.blockDiag ((Annealed.sigmaBar M L : ℝ) • (1 : Mat d))
                (((Annealed.sigmaBar M L : ℝ))⁻¹ • (1 : Mat d)))
              (W R omega)) ∂mu) +
        M.gamma ^ (6 : ℕ) := by
  classical
  have hgamma : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hquarter : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  have hlimpt : ∀ (R : TriadicCube d) (omega : Omega),
      0 ≤ blockVecDot (W R omega)
        (blockMatVecMul
          (Ch02.blockDiag ((Annealed.sigmaBar M L : ℝ) • (1 : Mat d))
            (((Annealed.sigmaBar M L : ℝ))⁻¹ • (1 : Mat d)))
          (W R omega)) := by
    intro R omega
    rw [blockVecDot_blockDiag_smul_one_vecDot]
    have h1 : (0 : ℝ) ≤ vecDot (W R omega).1 (W R omega).1 :=
      vecNormSq_nonneg (W R omega).1
    have h2 : (0 : ℝ) ≤ vecDot (W R omega).2 (W R omega).2 :=
      vecNormSq_nonneg (W R omega).2
    have h3 : (0 : ℝ) < (Annealed.sigmaBar M L : ℝ) := (Annealed.sigmaBar M L).2
    have h4 : (0 : ℝ) ≤ ((Annealed.sigmaBar M L : ℝ))⁻¹ := (inv_pos.2 h3).le
    positivity
  have hlim0 : 0 ≤ descendantsAverage Q j (fun R => ∫ omega, blockVecDot (W R omega)
      (blockMatVecMul
        (Ch02.blockDiag ((Annealed.sigmaBar M L : ℝ) • (1 : Mat d))
          (((Annealed.sigmaBar M L : ℝ))⁻¹ • (1 : Mat d)))
        (W R omega)) ∂mu) :=
    descendantsAverage_nonneg Q j _ fun R _ => integral_nonneg (hlimpt R)
  have hdefect := cubeAnnealedProbeDefect_le_logSq_budget M hS hL hn hE6 hgamE hsw
    hEv hgapK
  have hcubeLeg := descendantsAverage_integral_annealedCubeBlockQuadratic_le M L n
    hEv Q j W hcubeInt hlimInt
  have hcube : descendantsAverage Q j (fun R => ∫ omega, blockVecDot (W R omega)
        (blockMatVecMul
          (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
          (W R omega)) ∂mu) ≤
      (1 + principalResponseSwitchBudget M Ec K) *
        descendantsAverage Q j (fun R => ∫ omega, blockVecDot (W R omega)
          (blockMatVecMul
            (Ch02.blockDiag ((Annealed.sigmaBar M L : ℝ) • (1 : Mat d))
              (((Annealed.sigmaBar M L : ℝ))⁻¹ • (1 : Mat d)))
            (W R omega)) ∂mu) := by
    refine hcubeLeg.trans (mul_le_mul_of_nonneg_right ?_ hlim0)
    rw [principalResponseSwitchBudget]
    linarith [hdefect]
  have hcongr : descendantsAverage Q j (fun R => ∫ omega, energy R omega ∂mu) =
      descendantsAverage Q j (fun R =>
        (∫ omega, energy R omega * (Ebad R)ᶜ.indicator (fun _ => (1 : ℝ)) omega ∂mu) +
          ∫ omega,
            energy R omega * (Ebad R).indicator (fun _ => (1 : ℝ)) omega ∂mu) := by
    change ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, _ = ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, _
    congr 1
    exact Finset.sum_congr rfl fun R hR =>
      integral_indicator_split (hgoodInt R hR) (hbadInt R hR)
  have hsplit := hcongr.trans (descendantsAverage_add_real Q j _ _)
  refine principalResponse_fold_renamed hsplit hgood hbad hcube (by positivity)
    hrename ?_ hlim0
  have hgpow : M.gamma ^ (6 : ℕ) ≤ (1 / 4 : ℝ) ^ (6 : ℕ) :=
    pow_le_pow_left₀ hgamma.le hquarter 6
  norm_num at hgpow ⊢
  linarith

end Assembly

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
