/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusBackgroundParameters
public import LeanPool.FastDynamo.Operator.HorizontalSectorBasic
public import LeanPool.FastDynamo.Operator.CompactBaseInjectiveResolvent
public import LeanPool.FastDynamo.Operator.PointwiseResolvent

/-!
# The uniform background resolvent

This module proves `prop:background-resolvent`:
under the parameter choices collected in `BackgroundParameters`, the translated region
`cG_tau` lies in the resolvent set of the background operator `A^bg_{eps,n}`, and

`‖(z - A^bg_{eps,n})^{-1} f‖₂ + sqrt(eps) ‖∇_⊥ (z - A^bg_{eps,n})^{-1} f‖₂ ≤ C ‖f‖₂`

with `C = backgroundResolventConstant (g_*/2)` independent of `n`, of the diffusivity, of `z`
and of the final enlargement of `K_0` (`eq:bg-resolvent`).

## Route

**This is the paper's own route** (the end of the proof of `prop:background-resolvent`): the
paper uses the coercivity only for *injectivity* of the pencil and takes surjectivity from
`lem:torus-sector-basic`, where the pencil is Fredholm of index zero, so that injective implies
boundedly invertible with a domain-valued inverse.  The chain is:

* `BackgroundCoercivity.pencil_injective` — the kernel of `z - A^bg` is trivial on `cG_tau`;
* `exists_positiveReal_compactStateResolvent_horizontalInductionOperator` — one base point with
  a compact state resolvent, from `lem:torus-sector-basic`;
* `DomainOperator.hasResolventAt_of_compactStateResolvent_of_pencil_injective` — injective plus
  compact base gives a two-sided inverse at each `z`;
* `DomainOperator.hasResolventOnOfPointwiseTwoSidedInverses` — the pointwise inverses are
  assembled into one continuous family on `cG_tau`.

No elliptic-regularity theorem is needed: the domain of the operator is `H^2` by construction
and the Fredholm step produces a domain-valued inverse directly.

## Deviations from the statement of `prop:background-resolvent`

* The proposition says nothing about the dependence of the resolvent on `z`.  `resolvent` and
  `backgroundResolventData` record, in addition, continuity of the resolvent family on
  `cG_tau` (the `continuousOn` field of `HasResolventOn`), which is what the contour argument
  of §7 consumes.  Holomorphy, which the paper does not state, is proved separately, as
  `BackgroundParameters.exists_isOpen_hasResolventOn_analyticOnNhd`
  (`FastDynamo/Global/TorusBackgroundResolventHolomorphic.lean`): the resolvent extends to the
  intrinsic resolvent set of the operator, an open set containing `cG_tau`, on which it is
  analytic in operator norm.
* `tau ≥ tau_0` and "all sufficiently large `K_0`" enter as the explicit hypotheses of
  `BackgroundParameters`: `tau` above `max (2M^2/g_*) (2(C_0+1)/c_q^2)`, and
  `C_1 delta_+ ell_0 ≤ g_*/4` with `C_1 = 18 ‖vartheta'‖_inf^2`.  The constant of
  `eq:bg-resolvent` is the explicit `backgroundResolventConstant (g_*/2)`.

## Main results

* `BackgroundParameters.resolvent` — `HasResolventOn (A^bg_{eps,n}) cG_tau`.
* `BackgroundParameters.boundaryResolvent` — its restriction to the contour `Gamma_tau`.
* `BackgroundParameters.norm_resolvent_le`,
  `BackgroundParameters.sqrt_eps_mul_sqrt_gradientEnergy_resolvent_le`,
  `BackgroundParameters.sqrt_eps_mul_norm_deriv_resolvent_le` — `eq:bg-resolvent`.
* `TorusBackgroundResolventData` — the bundled interface (resolvent family, right-inverse identity,
  norm bound, gradient bound) consumed by the two-summand parametrix of §7.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Set

/--
**The background resolvent interface.**

This is the record that the two-summand parametrix of `prop:global-spectral-transfer` (§7)
consumes: a chosen resolvent family on a parameter set, together with the two uniform bounds of
`eq:bg-resolvent`.
The right-inverse identity `(z - A) R(z) = 1` is the `right_inv` field of the stored
`HasResolventOn`, and the left-inverse identity `R(z)(z - A) = 1` is its `left_inv` field.
-/
structure TorusBackgroundResolventData (A : DomainOperator TransverseC2L2 TransverseC2H2)
    (S : Set ℂ) (epsilon bound : ℝ) where
  /-- The chosen domain-valued resolvent family `R(z) : L² → H²` on `S`. -/
  resolvent : HasResolventOn A S
  /-- `‖R(z) f‖₂ ≤ C ‖f‖₂`, the `L²` half of `eq:bg-resolvent`. -/
  norm_le : ∀ z ∈ S, ∀ f : TransverseC2L2,
    ‖transverseH2Embedding (resolvent.inv z f)‖ ≤ bound * ‖f‖
  /-- `sqrt(eps) ‖∇_⊥ R(z) f‖₂ ≤ C ‖f‖₂`, the gradient half of `eq:bg-resolvent`. -/
  sqrt_eps_gradient_le : ∀ z ∈ S, ∀ f : TransverseC2L2,
    Real.sqrt epsilon *
        Real.sqrt (transverseGradientEnergy (resolvent.inv z f)) ≤ bound * ‖f‖

namespace TorusBackgroundResolventData

variable {A : DomainOperator TransverseC2L2 TransverseC2H2} {S : Set ℂ} {epsilon bound : ℝ}

/-- Restrict the interface to a smaller parameter set, for instance from the closed region
`cG_tau` to the contour `Gamma_tau`. -/
def mono (D : TorusBackgroundResolventData A S epsilon bound) {T : Set ℂ} (hTS : T ⊆ S) :
    TorusBackgroundResolventData A T epsilon bound where
  resolvent := D.resolvent.mono hTS
  norm_le z hz f := D.norm_le z (hTS hz) f
  sqrt_eps_gradient_le z hz f := D.sqrt_eps_gradient_le z (hTS hz) f

end TorusBackgroundResolventData

namespace ScaleFamily.TorusCellPlacement

namespace BackgroundParameters

variable {p : LocalSeedParameters} {r : ScaleRatios p}
  {hw : PonomarenkoSmoothingWidth} {P : TorusCellPlacement (r := r) (1 + (hw : ℝ))}
  {angularSpeed axialSpeed : ℝ}

/-! ## Existence of the resolvent on `cG_tau` -/

/--
**`cG_tau ⊆ rho(A^bg_{eps,n})`** (statement of `prop:background-resolvent`).

The coercivity of `eq:background-coercivity` makes the pencil injective at every `z` of the
translated region; `lem:torus-sector-basic` supplies a base point with compact state resolvent;
the Fredholm alternative then yields a two-sided inverse at each such `z`, and the pointwise
inverses are assembled into a single continuous family.
-/
theorem exists_hasResolventOn_shiftedRegion
    (B : BackgroundParameters hw P angularSpeed axialSpeed) (n : ℕ) {ε : ℝ}
    (heps : 0 < ε) (hlow : B.diffusivityLower * P.scaleFamily.ell n ^ 2 ≤ ε)
    (hupp : ε ≤ B.diffusivityUpper * P.scaleFamily.ell n ^ 2) :
    Nonempty (HasResolventOn (B.operator ε n) B.shiftedRegion) := by
  obtain ⟨t, h₀, hcompact⟩ :=
    exists_positiveReal_compactStateResolvent_horizontalInductionOperator
      (B.velocity n) ε (B.fourierIndex n) heps
  have hbase : ((Real.exp t : ℝ) : ℂ) ∈ ({((Real.exp t : ℝ) : ℂ)} : Set ℂ) := rfl
  refine ⟨DomainOperator.hasResolventOnOfPointwiseTwoSidedInverses (B.operator ε n)
    ((Real.exp t : ℝ) : ℂ) (h₀.inv _) (h₀.left_inv _ hbase) (h₀.right_inv _ hbase)
    B.shiftedRegion ?_⟩
  intro z hz
  obtain ⟨hres⟩ :=
    DomainOperator.hasResolventAt_of_compactStateResolvent_of_pencil_injective
      (B.operator ε n) h₀ hcompact (B.pencil_injective n heps hlow hupp hz)
  exact ⟨hres.inv z, hres.left_inv z rfl, hres.right_inv z rfl⟩

/-- The chosen background resolvent family `R_bg(z)` on `cG_tau`. -/
def resolvent (B : BackgroundParameters hw P angularSpeed axialSpeed) (n : ℕ) {ε : ℝ}
    (heps : 0 < ε) (hlow : B.diffusivityLower * P.scaleFamily.ell n ^ 2 ≤ ε)
    (hupp : ε ≤ B.diffusivityUpper * P.scaleFamily.ell n ^ 2) :
    HasResolventOn (B.operator ε n) B.shiftedRegion :=
  (B.exists_hasResolventOn_shiftedRegion n heps hlow hupp).some

/-- The same family read on the contour `Gamma_tau` only; this is the input of the contour
integral of §7. -/
def boundaryResolvent (B : BackgroundParameters hw P angularSpeed axialSpeed) (n : ℕ) {ε : ℝ}
    (heps : 0 < ε) (hlow : B.diffusivityLower * P.scaleFamily.ell n ^ 2 ≤ ε)
    (hupp : ε ≤ B.diffusivityUpper * P.scaleFamily.ell n ^ 2) :
    HasResolventOn (B.operator ε n) B.shiftedBoundary :=
  (B.resolvent n heps hlow hupp).mono B.shiftedBoundary_subset_shiftedRegion

/-- The resolvent on the contour is the restriction of the resolvent on the region, with the
same stored inverse. -/
@[simp] theorem boundaryResolvent_inv
    (B : BackgroundParameters hw P angularSpeed axialSpeed) (n : ℕ) {ε : ℝ}
    (heps : 0 < ε) (hlow : B.diffusivityLower * P.scaleFamily.ell n ^ 2 ≤ ε)
    (hupp : ε ≤ B.diffusivityUpper * P.scaleFamily.ell n ^ 2) :
    (B.boundaryResolvent n heps hlow hupp).inv = (B.resolvent n heps hlow hupp).inv :=
  rfl

/-! ## The uniform bounds `eq:bg-resolvent` -/

/-- `(z - A^bg_{eps,n}) R_bg(z) f = f` on `cG_tau`. -/
theorem pencil_resolvent_apply (B : BackgroundParameters hw P angularSpeed axialSpeed) (n : ℕ)
    {ε : ℝ} (heps : 0 < ε) (hlow : B.diffusivityLower * P.scaleFamily.ell n ^ 2 ≤ ε)
    (hupp : ε ≤ B.diffusivityUpper * P.scaleFamily.ell n ^ 2)
    {z : ℂ} (hz : z ∈ B.shiftedRegion) (f : TransverseC2L2) :
    (B.operator ε n).pencil z ((B.resolvent n heps hlow hupp).inv z f) = f := by
  have h := DFunLike.congr_fun ((B.resolvent n heps hlow hupp).right_inv z hz) f
  simpa using h

/-- **`eq:bg-resolvent`**, combined form:
`‖R_bg(z) f‖₂ + sqrt(eps) ‖∇_⊥ R_bg(z) f‖₂ ≤ C ‖f‖₂` with
`C = backgroundResolventConstant (g_*/2)`. -/
theorem norm_add_sqrt_eps_gradientEnergy_resolvent_le
    (B : BackgroundParameters hw P angularSpeed axialSpeed) (n : ℕ) {ε : ℝ}
    (heps : 0 < ε) (hlow : B.diffusivityLower * P.scaleFamily.ell n ^ 2 ≤ ε)
    (hupp : ε ≤ B.diffusivityUpper * P.scaleFamily.ell n ^ 2)
    {z : ℂ} (hz : z ∈ B.shiftedRegion) (f : TransverseC2L2) :
    ‖transverseH2Embedding ((B.resolvent n heps hlow hupp).inv z f)‖ +
        Real.sqrt (ε * transverseGradientEnergy
          ((B.resolvent n heps hlow hupp).inv z f)) ≤
      BackgroundCoercivity.backgroundResolventConstant (B.contour.growthFloor / 2) * ‖f‖ := by
  have hbound := B.norm_add_sqrt_eps_gradientEnergy_le n heps hlow hupp hz
    ((B.resolvent n heps hlow hupp).inv z f)
  rwa [B.pencil_resolvent_apply n heps hlow hupp hz f] at hbound

/-- **The `L²` half of `eq:bg-resolvent`**: `‖R_bg(z) f‖₂ ≤ C ‖f‖₂`. -/
theorem norm_resolvent_le (B : BackgroundParameters hw P angularSpeed axialSpeed) (n : ℕ)
    {ε : ℝ} (heps : 0 < ε) (hlow : B.diffusivityLower * P.scaleFamily.ell n ^ 2 ≤ ε)
    (hupp : ε ≤ B.diffusivityUpper * P.scaleFamily.ell n ^ 2)
    {z : ℂ} (hz : z ∈ B.shiftedRegion) (f : TransverseC2L2) :
    ‖transverseH2Embedding ((B.resolvent n heps hlow hupp).inv z f)‖ ≤
      BackgroundCoercivity.backgroundResolventConstant (B.contour.growthFloor / 2) * ‖f‖ := by
  have hmain := B.norm_add_sqrt_eps_gradientEnergy_resolvent_le n heps hlow hupp hz f
  have hsqrt : (0 : ℝ) ≤ Real.sqrt (ε * transverseGradientEnergy
      ((B.resolvent n heps hlow hupp).inv z f)) := Real.sqrt_nonneg _
  linarith

/-- **The gradient half of `eq:bg-resolvent`**:
`sqrt(eps) ‖∇_⊥ R_bg(z) f‖₂ ≤ C ‖f‖₂`, where `‖∇_⊥ h‖₂² = transverseGradientEnergy h`. -/
theorem sqrt_eps_mul_sqrt_gradientEnergy_resolvent_le
    (B : BackgroundParameters hw P angularSpeed axialSpeed) (n : ℕ) {ε : ℝ}
    (heps : 0 < ε) (hlow : B.diffusivityLower * P.scaleFamily.ell n ^ 2 ≤ ε)
    (hupp : ε ≤ B.diffusivityUpper * P.scaleFamily.ell n ^ 2)
    {z : ℂ} (hz : z ∈ B.shiftedRegion) (f : TransverseC2L2) :
    Real.sqrt ε *
        Real.sqrt (transverseGradientEnergy ((B.resolvent n heps hlow hupp).inv z f)) ≤
      BackgroundCoercivity.backgroundResolventConstant (B.contour.growthFloor / 2) * ‖f‖ := by
  have hmain := B.norm_add_sqrt_eps_gradientEnergy_resolvent_le n heps hlow hupp hz f
  have hnorm : (0 : ℝ) ≤
      ‖transverseH2Embedding ((B.resolvent n heps hlow hupp).inv z f)‖ := norm_nonneg _
  rw [Real.sqrt_mul heps.le] at hmain
  linarith

/-- The gradient half, per transverse coordinate:
`sqrt(eps) ‖∂_j R_bg(z) f‖₂ ≤ C ‖f‖₂`. -/
theorem sqrt_eps_mul_norm_deriv_resolvent_le
    (B : BackgroundParameters hw P angularSpeed axialSpeed) (n : ℕ) {ε : ℝ}
    (heps : 0 < ε) (hlow : B.diffusivityLower * P.scaleFamily.ell n ^ 2 ≤ ε)
    (hupp : ε ≤ B.diffusivityUpper * P.scaleFamily.ell n ^ 2)
    {z : ℂ} (hz : z ∈ B.shiftedRegion) (f : TransverseC2L2) (j : Fin 2) :
    Real.sqrt ε * ‖transverseVecDerivFromH2 (Fin 2) j
        ((B.resolvent n heps hlow hupp).inv z f)‖ ≤
      BackgroundCoercivity.backgroundResolventConstant (B.contour.growthFloor / 2) * ‖f‖ := by
  have hmain := B.sqrt_eps_mul_sqrt_gradientEnergy_resolvent_le n heps hlow hupp hz f
  have hsingle : ‖transverseVecDerivFromH2 (Fin 2) j
      ((B.resolvent n heps hlow hupp).inv z f)‖ ^ 2 ≤
      transverseGradientEnergy ((B.resolvent n heps hlow hupp).inv z f) :=
    Finset.single_le_sum (f := fun i : Fin 2 ↦ ‖transverseVecDerivFromH2 (Fin 2) i
      ((B.resolvent n heps hlow hupp).inv z f)‖ ^ 2)
      (fun i _ ↦ sq_nonneg _) (Finset.mem_univ j)
  have hle : ‖transverseVecDerivFromH2 (Fin 2) j
      ((B.resolvent n heps hlow hupp).inv z f)‖ ≤
      Real.sqrt (transverseGradientEnergy ((B.resolvent n heps hlow hupp).inv z f)) := by
    rw [show ‖transverseVecDerivFromH2 (Fin 2) j
        ((B.resolvent n heps hlow hupp).inv z f)‖ =
      Real.sqrt (‖transverseVecDerivFromH2 (Fin 2) j
        ((B.resolvent n heps hlow hupp).inv z f)‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hsingle
  have hstep : Real.sqrt ε * ‖transverseVecDerivFromH2 (Fin 2) j
      ((B.resolvent n heps hlow hupp).inv z f)‖ ≤
      Real.sqrt ε *
        Real.sqrt (transverseGradientEnergy ((B.resolvent n heps hlow hupp).inv z f)) :=
    mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)
  linarith

/-- The constant of `eq:bg-resolvent` is nonnegative, the positivity field of the parametrix
interface. -/
theorem backgroundResolventConstant_nonneg
    (B : BackgroundParameters hw P angularSpeed axialSpeed) :
    0 ≤ BackgroundCoercivity.backgroundResolventConstant (B.contour.growthFloor / 2) := by
  have hg : 0 < B.contour.growthFloor / 2 := by linarith [B.growthFloor_pos]
  have hs : 0 < Real.sqrt (B.contour.growthFloor / 2) := Real.sqrt_pos.mpr hg
  rw [BackgroundCoercivity.backgroundResolventConstant]
  positivity

/-! ## The bundled interface -/

/--
**`prop:background-resolvent`** in the bundled form consumed by the parametrix of §7 (holomorphy,
which the paper does not state, is
`BackgroundParameters.exists_isOpen_hasResolventOn_analyticOnNhd`): the resolvent family on
`cG_tau`, its two inverse identities and the two uniform bounds of `eq:bg-resolvent`.
-/
def backgroundResolventData (B : BackgroundParameters hw P angularSpeed axialSpeed) (n : ℕ)
    {ε : ℝ} (heps : 0 < ε) (hlow : B.diffusivityLower * P.scaleFamily.ell n ^ 2 ≤ ε)
    (hupp : ε ≤ B.diffusivityUpper * P.scaleFamily.ell n ^ 2) :
    TorusBackgroundResolventData (B.operator ε n) B.shiftedRegion ε
      (BackgroundCoercivity.backgroundResolventConstant (B.contour.growthFloor / 2)) where
  resolvent := B.resolvent n heps hlow hupp
  norm_le _z hz f := B.norm_resolvent_le n heps hlow hupp hz f
  sqrt_eps_gradient_le _z hz f :=
    B.sqrt_eps_mul_sqrt_gradientEnergy_resolvent_le n heps hlow hupp hz f

/-- The same interface on the contour `Gamma_tau`. -/
def boundaryResolventData (B : BackgroundParameters hw P angularSpeed axialSpeed) (n : ℕ)
    {ε : ℝ} (heps : 0 < ε) (hlow : B.diffusivityLower * P.scaleFamily.ell n ^ 2 ≤ ε)
    (hupp : ε ≤ B.diffusivityUpper * P.scaleFamily.ell n ^ 2) :
    TorusBackgroundResolventData (B.operator ε n) B.shiftedBoundary ε
      (BackgroundCoercivity.backgroundResolventConstant (B.contour.growthFloor / 2)) :=
  (B.backgroundResolventData n heps hlow hupp).mono B.shiftedBoundary_subset_shiftedRegion

end BackgroundParameters

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
