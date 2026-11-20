/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.LocalSeedC2Concrete
public import LeanPool.FastDynamo.Global.TorusSelectedCellParametrixData

/-!
# A concrete parameter choice for the proof

§3.1-§3.3 of the paper and the paragraph collecting the parameter choices at the end of §7.2.
`Global/GlobalParameterChoice.lean` contains the abstract chain
`(v, I, Gamma, cG, g_*, f_*, L_*, q, vartheta) -> tau -> K_0` for an arbitrary seed interface
and an arbitrary pair `(errorConstant, errorTarget)` of `eq:error-small`; this module

* instantiates the seed interface with the concrete two-component seed
  `HorizontalMode.globalSeedInterface` of `Local/LocalSeedC2Concrete.lean`;
* computes `errorConstant` from §7: `parametrixErrorConstant C_bg C_loc (1 + delta_+)` with
  `C_bg = backgroundResolventConstant (g_*/2)` the constant of `eq:bg-resolvent` and `C_loc` a
  cell-uniform majorant of the transported selected bound `selectedTransportedBound` of
  `eq:local-gradient`;
* fixes `errorTarget` small enough both for the Neumann series of `lem:global-contour-resolvent`
  (`‖E_n‖ < 1`) and for the projection error of `lem:global-riesz-nonzero`
  (`eq:global-projection-error`, `< 1/4`);
* chooses the chain `Theta` once and for all, above `K_0 ≥ k_*`, and records the numeric fact
  `eps_0 = delta_+/K_0²` (the concrete seed has `k_* = 1`).  The growth-floor bound
  `g_* ≥ (3/4)(448 - 4 pi²)` of the concrete seed is recorded in
  `Global/ParameterChainWitnesses.lean`.

The constants `C_bg`, `C_loc`, `C_app` and `eta_*` below are explicit values chosen by the
formalisation; the paper only asserts that such constants exist.  The chain is chosen with
`Classical.choose`, hence noncomputable and opaque; only the exported facts are available
downstream, just as the paper only chooses `K_0` "sufficiently large".
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

namespace GlobalSeedInterface

open ParametrixExplicitCutoff
open TorusChartC2Transfer
open TorusParametrixError

variable (S : GlobalSeedInterface)

/-! ## The two constants of `eq:error-small` -/

/-- **`C_bg`, the constant of `eq:bg-resolvent`** at the retained growth rate
`g_*/2`: `sqrt 2/g + 2/sqrt g` with `g = g_*/2`. -/
def backgroundConstant : ℝ :=
  BackgroundCoercivity.backgroundResolventConstant (S.growthFloor / 2)

/-- The background resolvent constant is nonnegative. -/
theorem backgroundConstant_nonneg : 0 ≤ S.backgroundConstant := by
  have hg : 0 < S.growthFloor / 2 := by
    have := S.growthFloor_pos
    linarith
  unfold backgroundConstant BackgroundCoercivity.backgroundResolventConstant
  have h1 : 0 ≤ Real.sqrt 2 / (S.growthFloor / 2) :=
    div_nonneg (Real.sqrt_nonneg 2) hg.le
  have h2 : 0 ≤ 2 / Real.sqrt (S.growthFloor / 2) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  linarith

/-- **`C_loc`, a cell-uniform majorant of the transported selected bound** of
`eq:local-gradient`.  The transported bound at the cell `n` is
`L_* (1 + sqrt 2 (C_1/(3R_n/2) sqrt(eps) + sqrt(delta_+)))`; at the paper's scaling
`sqrt(eps)/R_n = sqrt(delta_n) sqrt(ell_n) ≤ sqrt(delta_+)` once `ell_n ≤ 1`, so the displayed
number bounds it for every cell and every admissible diffusivity. -/
def selectedConstant : ℝ :=
  S.resolventBound * (1 + Real.sqrt 2 *
    (2 / 3 * firstDerivativeConstant * Real.sqrt S.parameters.deltaPlus +
      Real.sqrt S.parameters.deltaPlus))

/-- The cell-uniform selected constant is nonnegative. -/
theorem selectedConstant_nonneg : 0 ≤ S.selectedConstant := by
  have hfac : 0 ≤ 2 / 3 * firstDerivativeConstant * Real.sqrt S.parameters.deltaPlus :=
    mul_nonneg (mul_nonneg (by norm_num) firstDerivativeConstant_pos.le) (Real.sqrt_nonneg _)
  have hroot : 0 ≤ Real.sqrt S.parameters.deltaPlus := Real.sqrt_nonneg _
  have hsqrt2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  refine mul_nonneg S.resolventBound_nonneg ?_
  nlinarith

/-- The transported selected bound at a cell is dominated by the cell-uniform constant, as soon
as the scaled ratio `sqrt(eps)/R` stays below `sqrt(delta_+)`. -/
theorem selectedTransportedBound_le_selectedConstant {R epsilon : ℝ} (hR : 0 < R)
    (hratio : Real.sqrt epsilon / R ≤ Real.sqrt S.parameters.deltaPlus) :
    selectedTransportedBound R epsilon S.parameters.deltaPlus S.resolventBound ≤
      S.selectedConstant := by
  have hC : 0 < firstDerivativeConstant := firstDerivativeConstant_pos
  have haux : auxOutputRadius R = 3 * R / 2 := rfl
  have hkey : firstDerivativeConstant / auxOutputRadius R * Real.sqrt epsilon ≤
      2 / 3 * firstDerivativeConstant * Real.sqrt S.parameters.deltaPlus := by
    have hstep : firstDerivativeConstant / auxOutputRadius R * Real.sqrt epsilon =
        2 / 3 * firstDerivativeConstant * (Real.sqrt epsilon / R) := by
      rw [haux]
      field_simp
    rw [hstep]
    exact mul_le_mul_of_nonneg_left hratio
      (mul_nonneg (by norm_num) hC.le)
  unfold selectedTransportedBound selectedConstant
  refine mul_le_mul_of_nonneg_left ?_ S.resolventBound_nonneg
  have hsqrt2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

/-! ## The two parameters of `eq:error-small` -/

/-- **The constant of `eq:error-small`** at this seed: the error constant of
`eq:explicit-error` scaled by the crude factor `1 + delta_+` of
`scaleErrorMajorant_scaled_le`. -/
def errorConstant : ℝ :=
  parametrixErrorConstant S.backgroundConstant S.selectedConstant * (1 + S.parameters.deltaPlus)

/-- The constant of `eq:error-small` is nonnegative. -/
theorem errorConstant_nonneg : 0 ≤ S.errorConstant := by
  have h := parametrixErrorConstant_nonneg S.backgroundConstant_nonneg S.selectedConstant_nonneg
  have hd := S.parameters.deltaPlus_pos
  exact mul_nonneg h (by linarith)

/-- The uniform bound `C_app = C_bg + C_loc` on the approximate inverse
(`eq:parametrix-uniform-bound`).  The background input of `eq:Rapp` carries the
sharp `‖1 - φ_n‖ ≤ 1`, so no factor `2` appears. -/
def approximateInverseConstant : ℝ := S.backgroundConstant + S.selectedConstant

/-- The approximate-inverse constant is nonnegative. -/
theorem approximateInverseConstant_nonneg : 0 ≤ S.approximateInverseConstant := by
  have h1 := S.backgroundConstant_nonneg
  have h2 := S.selectedConstant_nonneg
  unfold approximateInverseConstant
  linarith

/-- The constant in front of the Neumann remainder in `eq:global-projection-error`,
generously rounded up: `length(Gamma)/(2 pi) = radius` times `C_app`, plus one on each factor so
that the bound is insensitive to the exact normalisation of the contour integral. -/
def projectionConstant : ℝ :=
  (1 + S.contour.radius) * (1 + S.approximateInverseConstant)

/-- The projection constant is at least one. -/
theorem one_le_projectionConstant : 1 ≤ S.projectionConstant := by
  have h1 : (1 : ℝ) ≤ 1 + S.contour.radius := by
    have := S.contour.radius_pos
    linarith
  have h2 : (1 : ℝ) ≤ 1 + S.approximateInverseConstant := by
    have := S.approximateInverseConstant_nonneg
    linarith
  unfold projectionConstant
  nlinarith

/-- The projection constant is nonnegative. -/
theorem projectionConstant_nonneg : 0 ≤ S.projectionConstant := by
  have := S.one_le_projectionConstant
  linarith

/-- **The target of `eq:error-small`**, the paper's `eta_*` (proof of
`lem:global-contour-resolvent`): small enough
for the Neumann series (`eta_* ≤ 1/2 < 1`) and small enough for the projection error
`eq:global-projection-error` to stay below `1/4`. -/
def errorTarget : ℝ := min (1 / 2) (1 / (100 * (1 + S.projectionConstant)))

/-- The target of `eq:error-small` is positive. -/
theorem errorTarget_pos : 0 < S.errorTarget := by
  refine lt_min (by norm_num) ?_
  have := S.projectionConstant_nonneg
  positivity

/-- The target of `eq:error-small` is at most one half. -/
theorem errorTarget_le_half : S.errorTarget ≤ 1 / 2 := min_le_left _ _

/-- The target of `eq:error-small` is at most one, so `eq:error-small` implies `‖E_n‖ < 1`. -/
theorem errorTarget_le_one : S.errorTarget ≤ 1 := by
  have := S.errorTarget_le_half
  linarith

/-- **The projection-error threshold** (`eq:global-projection-error`): with
`eta_* = errorTarget` the Neumann remainder `eta_*/(1 - eta_*)` multiplied by any constant of
the size of the contour-integral prefactor stays strictly below `1/4`.  The admissible range
`A ≤ 10 * projectionConstant` covers the prefactor `length(Gamma)/(2 pi) * C_app` and any
re-normalisation of it by a factor at most `2 pi`. -/
theorem mul_errorTarget_div_lt_quarter {A : ℝ} (hA : 0 ≤ A)
    (hle : A ≤ 10 * S.projectionConstant) :
    A * (S.errorTarget / (1 - S.errorTarget)) < 1 / 4 := by
  set K : ℝ := S.projectionConstant with hK
  have hK1 : 1 ≤ K := S.one_le_projectionConstant
  have hden : (0 : ℝ) < 100 * (1 + K) := by linarith
  have hsmall : S.errorTarget ≤ 1 / (100 * (1 + K)) := min_le_right _ _
  have hhalf : S.errorTarget ≤ 1 / 2 := S.errorTarget_le_half
  have hpos : 0 < S.errorTarget := S.errorTarget_pos
  have hone : (0 : ℝ) < 1 - S.errorTarget := by linarith
  have hratio : S.errorTarget / (1 - S.errorTarget) ≤ 2 * S.errorTarget := by
    rw [div_le_iff₀ hone]
    nlinarith
  have hchain : A * (S.errorTarget / (1 - S.errorTarget)) ≤ 10 * K * (2 * S.errorTarget) := by
    refine le_trans (mul_le_mul_of_nonneg_left hratio hA) ?_
    refine mul_le_mul_of_nonneg_right hle ?_
    linarith
  have hfinal : 10 * K * (2 * S.errorTarget) < 1 / 4 := by
    have h20 : 20 * K * S.errorTarget ≤ 20 * K * (1 / (100 * (1 + K))) := by
      refine mul_le_mul_of_nonneg_left hsmall ?_
      linarith
    have hexp : 20 * K * (1 / (100 * (1 + K))) = K / (5 * (1 + K)) := by
      field_simp
      ring
    have hlt : K / (5 * (1 + K)) < 1 / 4 := by
      rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
      linarith
    nlinarith
  linarith

end GlobalSeedInterface

/-! ## The concrete chain -/

namespace HorizontalMode

open GlobalSeedInterface
open TorusChartC2Transfer
open TorusParametrixError

/-- **The parameter chain at the concrete seed** exists above `K_0 ≥ k_*`, the lower
bound that makes every transverse scale satisfy `ell_n ≤ 1`. -/
theorem exists_mainParameterChoice :
    ∃ Theta : GlobalParameterChoice globalSeedInterface globalSeedInterface.errorConstant
      globalSeedInterface.errorTarget,
      globalSeedInterface.parameters.kStar ≤ Theta.baseIndex :=
  exists_globalParameterChoice globalSeedInterface globalSeedInterface.errorConstant_nonneg
    globalSeedInterface.errorTarget_pos globalSeedInterface.parameters.kStar

/-- **The parameter chain of the proof**: one value of `(q, tau, K_0)` for the concrete
two-component seed, fixed once and for all (the final choice of `K_0` at the end of §7.2). -/
def mainParameterChoice :
    GlobalParameterChoice globalSeedInterface globalSeedInterface.errorConstant
      globalSeedInterface.errorTarget :=
  Classical.choose exists_mainParameterChoice

/-- The chosen base Fourier index is at least `k_*`. -/
theorem kStar_le_mainParameterChoice_baseIndex :
    globalSeedInterface.parameters.kStar ≤ mainParameterChoice.baseIndex :=
  Classical.choose_spec exists_mainParameterChoice

end HorizontalMode

/-! ## Consequences of `K_0 ≥ k_*` -/

namespace GlobalParameterChoice

open GlobalSeedInterface
open TorusChartC2Transfer
open TorusParametrixError

variable {S : GlobalSeedInterface} {errorConstant errorTarget : ℝ}
  (Theta : GlobalParameterChoice S errorConstant errorTarget)

/-- Above the base bound `K_0 ≥ k_*` every transverse scale is at most one. -/
theorem ell_le_one (hbase : S.parameters.kStar ≤ Theta.baseIndex) (n : ℕ) :
    Theta.scaleFamily.ell n ≤ 1 := by
  refine le_trans (Theta.scaleFamily.ell_le_ell_zero n) ?_
  rw [ScaleFamily.ell_formula, ScaleFamily.fourierIndex_zero]
  have hK0 : 0 < (Theta.scaleFamily.K0 : ℝ) :=
    Nat.cast_pos.2 Theta.scaleFamily.K0_pos
  rw [div_le_one hK0]
  exact_mod_cast hbase

/-- Above the base bound the buffer radii are at most one as well. -/
theorem bufferRadius_le_one (hbase : S.parameters.kStar ≤ Theta.baseIndex) (n : ℕ) :
    Theta.scaleFamily.bufferRadius n ≤ 1 := by
  have hle := Theta.ell_le_one hbase n
  have h := Real.sqrt_le_sqrt hle
  simpa [ScaleFamily.bufferRadius, Real.sqrt_one] using h

/-- At the paper's scaling the ratio `sqrt(eps)/R_n` stays below `sqrt(delta_+)`, which is
what makes the transported selected bound cell-uniform. -/
theorem sqrt_epsilon_div_bufferRadius_le (hbase : S.parameters.kStar ≤ Theta.baseIndex)
    {epsilon : ℝ} (c : ScaleFamily.MatchingCell Theta.scaleFamily epsilon) :
    Real.sqrt epsilon / Theta.scaleFamily.bufferRadius c.index ≤
      Real.sqrt S.parameters.deltaPlus := by
  have hell : 0 < Theta.scaleFamily.ell c.index := Theta.scaleFamily.ell_pos c.index
  have hR : Theta.scaleFamily.bufferRadius c.index = Real.sqrt (Theta.scaleFamily.ell c.index) :=
    rfl
  have hRpos : 0 < Theta.scaleFamily.bufferRadius c.index :=
    Theta.scaleFamily.bufferRadius_pos c.index
  have heps : epsilon = c.delta * Theta.scaleFamily.ell c.index ^ 2 :=
    c.epsilon_eq_delta_mul_ell_sq
  have hsqrt : Real.sqrt epsilon =
      Real.sqrt c.delta * Theta.scaleFamily.ell c.index := by
    have hstep := congrArg Real.sqrt heps
    rwa [Real.sqrt_mul c.delta_pos.le, Real.sqrt_sq hell.le] at hstep
  have hdiv : Real.sqrt epsilon / Theta.scaleFamily.bufferRadius c.index =
      Real.sqrt c.delta * Theta.scaleFamily.bufferRadius c.index := by
    rw [hsqrt, hR, mul_div_assoc, Real.div_sqrt]
  rw [hdiv]
  have hstep : Real.sqrt c.delta * Theta.scaleFamily.bufferRadius c.index ≤
      Real.sqrt c.delta :=
    by nlinarith [Real.sqrt_nonneg c.delta, Theta.bufferRadius_le_one hbase c.index,
      Theta.scaleFamily.bufferRadius_pos c.index]
  refine hstep.trans ?_
  exact Real.sqrt_le_sqrt c.admissible.2

/-- The transported selected bound of a matching cell is dominated by the cell-uniform constant
`C_loc`. -/
theorem selectedTransportedBound_le (hbase : S.parameters.kStar ≤ Theta.baseIndex)
    {epsilon : ℝ} (c : ScaleFamily.MatchingCell Theta.scaleFamily epsilon) :
    selectedTransportedBound (Theta.scaleFamily.bufferRadius c.index) epsilon
        S.parameters.deltaPlus S.resolventBound ≤
      S.selectedConstant :=
  S.selectedTransportedBound_le_selectedConstant
    (Theta.scaleFamily.bufferRadius_pos c.index)
    (Theta.sqrt_epsilon_div_bufferRadius_le hbase c)

end GlobalParameterChoice

namespace GlobalParameterChoice

open GlobalSeedInterface
open TorusChartC2Transfer
open TorusParametrixError

variable {S : GlobalSeedInterface}

/-- **`eq:error-small` at a selected cell, in the exact shape `lem:global-contour-resolvent`
consumes it**: the parametrix error majorant of the selected cell stays below the
target `eta_*`, hence in particular below `1`. -/
theorem scaleErrorMajorant_lt_errorTarget
    (Theta : GlobalParameterChoice S S.errorConstant S.errorTarget)
    (hbase : S.parameters.kStar ≤ Theta.baseIndex)
    {epsilon : ℝ} (c : ScaleFamily.MatchingCell Theta.scaleFamily epsilon) :
    scaleErrorMajorant
        (parametrixErrorConstant S.backgroundConstant
          (selectedTransportedBound (Theta.scaleFamily.bufferRadius c.index) epsilon
            S.parameters.deltaPlus S.resolventBound))
        epsilon (Theta.scaleFamily.bufferRadius c.index) < S.errorTarget := by
  have hell : 0 < Theta.scaleFamily.ell c.index := Theta.scaleFamily.ell_pos c.index
  have hR : Theta.scaleFamily.bufferRadius c.index =
      Real.sqrt (Theta.scaleFamily.ell c.index) := rfl
  have hRpos : 0 < Theta.scaleFamily.bufferRadius c.index :=
    Theta.scaleFamily.bufferRadius_pos c.index
  have hepsnn : 0 ≤ epsilon := by
    rw [c.epsilon_eq_delta_mul_ell_sq]
    exact le_of_lt (mul_pos c.delta_pos (pow_pos hell 2))
  -- replace the cell constant by the cell-uniform one
  have hloc := Theta.selectedTransportedBound_le hbase c
  have hmono : parametrixErrorConstant S.backgroundConstant
        (selectedTransportedBound (Theta.scaleFamily.bufferRadius c.index) epsilon
          S.parameters.deltaPlus S.resolventBound) ≤
      parametrixErrorConstant S.backgroundConstant S.selectedConstant := by
    unfold parametrixErrorConstant
    refine mul_le_mul_of_nonneg_left (by linarith) ?_
    exact commutatorErrorConstant_nonneg ParametrixCutoffs.cutoffFirstDerivativeConstant_pos.le
      ParametrixCutoffs.cutoffSecondDerivativeConstant_pos.le
  have hfactor : 0 ≤ Real.sqrt epsilon / Theta.scaleFamily.bufferRadius c.index +
      epsilon / Theta.scaleFamily.bufferRadius c.index ^ 2 := by
    have h1 : 0 ≤ Real.sqrt epsilon / Theta.scaleFamily.bufferRadius c.index :=
      div_nonneg (Real.sqrt_nonneg _) hRpos.le
    have h2 : 0 ≤ epsilon / Theta.scaleFamily.bufferRadius c.index ^ 2 :=
      div_nonneg hepsnn (by positivity)
    linarith
  have hstep1 : scaleErrorMajorant
        (parametrixErrorConstant S.backgroundConstant
          (selectedTransportedBound (Theta.scaleFamily.bufferRadius c.index) epsilon
            S.parameters.deltaPlus S.resolventBound))
        epsilon (Theta.scaleFamily.bufferRadius c.index) ≤
      scaleErrorMajorant (parametrixErrorConstant S.backgroundConstant S.selectedConstant)
        epsilon (Theta.scaleFamily.bufferRadius c.index) := by
    unfold scaleErrorMajorant
    exact mul_le_mul_of_nonneg_right hmono hfactor
  -- unfold the paper scaling `eps = delta ell²`, `R = sqrt(ell)`
  have hscaled : scaleErrorMajorant
        (parametrixErrorConstant S.backgroundConstant S.selectedConstant) epsilon
        (Theta.scaleFamily.bufferRadius c.index) =
      scaleErrorMajorant (parametrixErrorConstant S.backgroundConstant S.selectedConstant)
        (c.delta * Theta.scaleFamily.ell c.index ^ 2)
        (Real.sqrt (Theta.scaleFamily.ell c.index)) := by
    rw [← c.epsilon_eq_delta_mul_ell_sq, hR]
  have hstep2 := scaleErrorMajorant_scaled_le
    (C := parametrixErrorConstant S.backgroundConstant S.selectedConstant)
    (δ := c.delta) (ℓ := Theta.scaleFamily.ell c.index)
    (δplus := S.parameters.deltaPlus)
    (parametrixErrorConstant_nonneg S.backgroundConstant_nonneg S.selectedConstant_nonneg)
    c.delta_pos.le c.admissible.2 hell
  have hstep3 : parametrixErrorConstant S.backgroundConstant S.selectedConstant *
        (1 + S.parameters.deltaPlus) *
        (Real.sqrt (Theta.scaleFamily.ell c.index) + Theta.scaleFamily.ell c.index) <
      S.errorTarget :=
    Theta.errorSmall_cell S.errorConstant_nonneg c.index
  rw [hscaled] at hstep1
  linarith

end GlobalParameterChoice

/-! ## The numeric facts of the concrete chain -/

namespace HorizontalMode

open GlobalSeedInterface

/-- The chain's diffusivity threshold is the paper's `eps_0 = delta_+/K_0²` (§3.2): the
concrete seed has `k_* = 1`. -/
theorem mainParameterChoice_eps0_formula :
    mainParameterChoice.eps0 =
      globalSeedInterface.parameters.deltaPlus /
        (mainParameterChoice.baseIndex : ℝ) ^ 2 := by
  have hk : globalSeedInterface.parameters.kStar = 1 := localSeedC2_kStar
  rw [mainParameterChoice.eps0_formula, hk]
  norm_num

end HorizontalMode

end

end FastDynamo
