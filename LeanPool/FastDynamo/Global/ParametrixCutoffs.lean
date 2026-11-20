/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.TransverseVecCutoffMultiplier
public import LeanPool.FastDynamo.Global.ParametrixExplicitCutoffDerivatives

/-!
# The three parametrix cut-offs of Section 7

The paper (§7.1, `sec:parametrix`) uses
three smooth scalar cut-offs around the selected cell centre `p_n`, at the reserved radius
`R_n`:

* `φ_n = 1` on `D(p_n, R_n/5)`, `supp φ_n ⊂ D(p_n, R_n/4)`;
* `ψ_n = 1` on `D(p_n, R_n/3)`, `supp ψ_n ⊂ D(p_n, R_n/2)`;
* `χ_n = 0` on `D(p_n, R_n/10)`, `χ_n = 1` outside `D(p_n, R_n/6)`.

The first two are the cut-offs of `FastDynamo/Global/ParametrixExplicitCutoffDerivatives.lean`
and are reused verbatim.  The third one, `χ_n`, is the output
cut-off of the *background* summand, and it is what makes the full and background coefficients
agree identically wherever the background resolvent is used.  It is built here as `1 - b`, where
`b` is a `ContDiffBump` of inner radius `R/10` and outer radius `R/6`, by the same affine
rescaling of a fixed unit-scale reference bump, so that

`‖D^jφ_n‖_∞ + ‖D^jψ_n‖_∞ + ‖D^jχ_n‖_∞ ≤ C R_n^{-j}`, `j = 1, 2`,

with radius-independent constants.  The paper's `eq:parametrix-cutoff-bounds`
is the two-term display over `ψ_n` and `χ_n` only — `φ_n` divides the forcing and needs no
derivative bound — so what is proved here is the stronger three-term sum, of which the
paper's display is the `ψ_n`/`χ_n` part.  The consumed interface
`HorizontalParametrixCutoffs` stores exactly the paper's four derivative bounds.

The two exact identities

`χ_n(1 - φ_n) = 1 - φ_n`, `ψ_nφ_n = φ_n`
(`eq:parametrix-cutoff-identities`)

are proved pointwise on the plane, together with the partition
`χ_n(1 - φ_n) + ψ_nφ_n = 1` behind `eq:Rapp`: as in the paper, the background summand carries
an output cut-off.

The module closes with the multiplier layer these cut-offs are used through.  A
`TransverseVecSecondOrderCutoff` is the fibre-generic form of the second-order periodic
multiplier interface of `FastDynamo/Global/PeriodicSecondOrderCutoffs.lean`: a periodic
scalar cut-off together with its bounded multiplication on the transverse `H²` Fourier
graph and the first- and second-order Leibniz identities.  A `HorizontalParametrixCutoffs R`
bundles the three placed multipliers at a cell of reserved radius `R`, their scale bounds and
the two identities, read at the two-component fibre `TransverseC2H2`/`TransverseC2L2` of the
paper.

The centre of the cell never enters the bundle, only its reserved radius: in the concrete
instance of a `ScaleFamily.TorusCellPlacement` cell `n` the parameters are
`p = pairToWholePlane (P.scaleFamily.cellCenter n)` and `R = P.scaleFamily.bufferRadius n`
(whose positivity is `ScaleFamily.bufferRadius_pos`), and the placement's own `supportFit` field
`supportRadius * ℓ_n < R_n/10` is exactly the paper's `supp u_n^loc ⊂ D(p_n, R_n/10)`,
i.e. the containment that makes `χ_n` kill the local velocity.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open scoped ENNReal NNReal

namespace ParametrixCutoffs

open ConstantCoefficientBackground ParametrixExplicitCutoff

/-! ## The background output bump `χ` -/

/-- The paper's background output cut-off, as a bump to be subtracted from one:
it is one on `D(p, R/10)` and supported in `D(p, R/6)` (§7.1). -/
def backgroundBump (p : WholePlane) (R : ℝ) (hR : 0 < R) : ContDiffBump p where
  rIn := R / 10
  rOut := R / 6
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- Fixed reference for the background bump.  Its outer-to-inner radius ratio is `5 / 3`. -/
def unitBackgroundBump : ContDiffBump (0 : WholePlane) where
  rIn := 1
  rOut := 5 / 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The background output cut-off `χ`: zero on `D(p, R/10)` and one outside `D(p, R/6)`
(§7.1). -/
def backgroundCutoff (p : WholePlane) (R : ℝ) (hR : 0 < R) : WholePlane → ℝ :=
  fun x ↦ 1 - backgroundBump p R hR x

/-- The background bump at centre `p` and radius `R` is the fixed unit bump precomposed with the
dilation `x ↦ (10 / R) • (x - p)`. -/
theorem backgroundBump_eq_unit_rescale
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    (backgroundBump p R hR) x = unitBackgroundBump ((10 / R) • (x - p)) := by
  have hR0 : R ≠ 0 := ne_of_gt hR
  change (someContDiffBumpBase WholePlane).toFun
      ((R / 6) / (R / 10)) ((R / 10)⁻¹ • (x - p)) =
    (someContDiffBumpBase WholePlane).toFun
      ((5 / 3) / 1) (1⁻¹ • ((10 / R) • (x - p) - 0))
  have hratio : (R / 6) / (R / 10) = (5 / 3 : ℝ) / 1 := by
    field_simp
    ring
  have hscale : (R / 10)⁻¹ = 10 / R := by
    field_simp
  rw [hratio, hscale]
  simp

/-- The background bump is smooth. -/
theorem backgroundBump_contDiff (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    ContDiff ℝ (⊤ : ℕ∞) ((backgroundBump p R hR : WholePlane → ℝ)) :=
  (backgroundBump p R hR).contDiff

/-- `χ = 0` on the closed disk of radius `R/10`: the first half of the paper's defining
property of the background cut-off (§7.1). -/
theorem backgroundCutoff_eq_zero_of_dist_le
    (p : WholePlane) (R : ℝ) (hR : 0 < R) {x : WholePlane}
    (hx : dist x p ≤ R / 10) : backgroundCutoff p R hR x = 0 := by
  have hone : (backgroundBump p R hR) x = 1 := by
    apply (backgroundBump p R hR).one_of_mem_closedBall
    simpa [Metric.mem_closedBall, dist_comm, backgroundBump] using hx
  rw [backgroundCutoff, hone, sub_self]

/-- `χ = 1` outside the open disk of radius `R/6`: the second half of the paper's defining
property of the background cut-off (§7.1). -/
theorem backgroundCutoff_eq_one_of_radius_le_dist
    (p : WholePlane) (R : ℝ) (hR : 0 < R) {x : WholePlane}
    (hx : R / 6 ≤ dist x p) : backgroundCutoff p R hR x = 1 := by
  have hzero : (backgroundBump p R hR) x = 0 :=
    (backgroundBump p R hR).zero_of_le_dist hx
  rw [backgroundCutoff, hzero, sub_zero]

/-- The background cut-off takes values in `[0, 1]`. -/
theorem backgroundCutoff_mem_Icc
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    backgroundCutoff p R hR x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · have := (backgroundBump p R hR).le_one (x := x)
    simp only [backgroundCutoff]
    linarith
  · have := (backgroundBump p R hR).nonneg (x := x)
    simp only [backgroundCutoff]
    linarith

/-! ## First derivative scaling of `χ` -/

/-- Lipschitz constant of the fixed unit-scale background bump. -/
def unitBackgroundLipschitzConstant : NNReal :=
  contDiffBumpLipschitzConstant unitBackgroundBump

/-- The fixed unit background bump is Lipschitz with `unitBackgroundLipschitzConstant`. -/
theorem unitBackground_lipschitzWith :
    LipschitzWith unitBackgroundLipschitzConstant
      (unitBackgroundBump : WholePlane → ℝ) :=
  contDiffBump_lipschitzWith unitBackgroundBump

/-- Lipschitz constant of the radius-`R` background affine dilation. -/
def backgroundDilationConstant (R : ℝ) (hR : 0 < R) : NNReal :=
  ⟨10 / R, by positivity⟩

/-- The dilation `x ↦ (10 / R) • (x - p)` is Lipschitz with constant `10 / R`. -/
theorem backgroundAffine_lipschitzWith
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    LipschitzWith (backgroundDilationConstant R hR)
      (fun x : WholePlane ↦ (10 / R) • (x - p)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist ((10 / R) • (x - p)) ((10 / R) • (y - p)) ≤ (10 / R) * dist x y
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos (by norm_num) hR), dist_eq_norm]
  rw [show x - p - (y - p) = x - y by abel]

/-- The background bump is Lipschitz with the product constant
`unitBackgroundLipschitzConstant * (10 / R)`, exhibiting the `1 / R` scaling. -/
theorem backgroundBump_lipschitzWith_explicit
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    LipschitzWith
      (unitBackgroundLipschitzConstant * backgroundDilationConstant R hR)
      ((backgroundBump p R hR : WholePlane → ℝ)) := by
  have hcomp := unitBackground_lipschitzWith.comp
    (backgroundAffine_lipschitzWith p R hR)
  intro x y
  rw [backgroundBump_eq_unit_rescale p R hR x,
    backgroundBump_eq_unit_rescale p R hR y]
  simpa only [Function.comp_apply] using hcomp x y

/-- Subtracting from the constant `1` does not change the Lipschitz constant, so the background
cut-off has the same explicit `1 / R` Lipschitz bound as the bump it is built from. -/
theorem backgroundCutoff_lipschitzWith_explicit
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    LipschitzWith
      (unitBackgroundLipschitzConstant * backgroundDilationConstant R hR)
      (backgroundCutoff p R hR) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (backgroundBump_lipschitzWith_explicit p R hR).dist_le_mul x y
  simp only [backgroundCutoff, Real.dist_eq] at h ⊢
  rw [show 1 - (backgroundBump p R hR) x - (1 - (backgroundBump p R hR) y) =
    -((backgroundBump p R hR) x - (backgroundBump p R hR) y) by ring, abs_neg]
  exact h

/-- A radius-independent first derivative constant for the background cut-off. -/
def backgroundFirstDerivativeConstant : ℝ :=
  1 + 10 * (unitBackgroundLipschitzConstant : ℝ)

/-- The background first-derivative constant is strictly positive. -/
theorem backgroundFirstDerivativeConstant_pos : 0 < backgroundFirstDerivativeConstant := by
  unfold backgroundFirstDerivativeConstant
  positivity

/-- Every coordinate derivative of the background cut-off is bounded by
`backgroundFirstDerivativeConstant / R`: the `j = 1` half of `eq:parametrix-cutoff-bounds`
for `χ`. -/
theorem norm_backgroundCutoff_coordinateDerivative_le
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (j : Fin 2) (x : WholePlane) :
    ‖realProfileCoordinateDerivative (backgroundCutoff p R hR) j x‖ ≤
      backgroundFirstDerivativeConstant / R := by
  have h := norm_realProfileCoordinateDerivative_le_of_lipschitz
    (backgroundCutoff_lipschitzWith_explicit p R hR) j x
  calc
    ‖realProfileCoordinateDerivative (backgroundCutoff p R hR) j x‖ ≤
        ((unitBackgroundLipschitzConstant *
          backgroundDilationConstant R hR : NNReal) : ℝ) := h
    _ = (10 * (unitBackgroundLipschitzConstant : ℝ)) / R := by
      change (unitBackgroundLipschitzConstant : ℝ) * (10 / R) = _
      ring
    _ ≤ backgroundFirstDerivativeConstant / R := by
      apply (div_le_div_iff_of_pos_right hR).2
      unfold backgroundFirstDerivativeConstant
      nlinarith [NNReal.coe_nonneg unitBackgroundLipschitzConstant]

/-! ## Second derivative scaling of `χ` -/

/-- The second iterated Fréchet derivative of the fixed unit background bump is globally bounded,
being continuous with compact support. -/
theorem exists_unitBackground_secondDerivative_bound :
    ∃ C : ℝ, ∀ x : WholePlane,
      ‖iteratedFDeriv ℝ 2 (unitBackgroundBump : WholePlane → ℝ) x‖ ≤ C := by
  have hcont : Continuous (fun x : WholePlane ↦
      iteratedFDeriv ℝ 2 (unitBackgroundBump : WholePlane → ℝ) x) :=
    (unitBackgroundBump.contDiff : ContDiff ℝ 2
      (unitBackgroundBump : WholePlane → ℝ)).continuous_iteratedFDeriv le_rfl
  have hsupp : HasCompactSupport (iteratedFDeriv ℝ 2
      (unitBackgroundBump : WholePlane → ℝ)) :=
    unitBackgroundBump.hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) 2
  exact hcont.bounded_above_of_compact_support hsupp

/-- A nonnegative global Hessian bound for the fixed background reference bump. -/
def unitBackgroundSecondDerivativeConstant : ℝ :=
  max 0 (Classical.choose exists_unitBackground_secondDerivative_bound)

/-- The chosen unit-scale background Hessian constant is nonnegative. -/
theorem unitBackgroundSecondDerivativeConstant_nonneg :
    0 ≤ unitBackgroundSecondDerivativeConstant :=
  le_max_left _ _

/-- The second iterated derivative of the unit background bump is bounded everywhere by
`unitBackgroundSecondDerivativeConstant`. -/
theorem unitBackground_secondDerivative_le (x : WholePlane) :
    ‖iteratedFDeriv ℝ 2 (unitBackgroundBump : WholePlane → ℝ) x‖ ≤
      unitBackgroundSecondDerivativeConstant :=
  (Classical.choose_spec exists_unitBackground_secondDerivative_bound x).trans
    (le_max_right _ _)

/-- Exact scaling of the background bump's second derivative: it is `(10 / R) ^ 2` times the unit
bump's second derivative at the dilated point. -/
theorem backgroundBump_iteratedFDeriv_two_eq
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    iteratedFDeriv ℝ 2 ((backgroundBump p R hR : WholePlane → ℝ)) x =
      (10 / R) ^ 2 • iteratedFDeriv ℝ 2
        (unitBackgroundBump : WholePlane → ℝ) ((10 / R) • (x - p)) := by
  rw [show ((backgroundBump p R hR : WholePlane → ℝ)) =
      (fun z ↦ unitBackgroundBump ((10 / R) • (z - p))) by
    funext z
    exact backgroundBump_eq_unit_rescale p R hR z]
  exact iteratedFDeriv_two_affine_dilation
    (unitBackgroundBump : WholePlane → ℝ)
      (unitBackgroundBump.contDiff : ContDiff ℝ 2
        (unitBackgroundBump : WholePlane → ℝ)) (10 / R) p x

/-- Subtracting from the constant `1` flips the sign of the second derivative and changes nothing
else. -/
theorem backgroundCutoff_iteratedFDeriv_two_eq
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    iteratedFDeriv ℝ 2 (backgroundCutoff p R hR) x =
      -iteratedFDeriv ℝ 2 ((backgroundBump p R hR : WholePlane → ℝ)) x := by
  have hsplit : backgroundCutoff p R hR =
      (fun _ : WholePlane ↦ (1 : ℝ)) - ((backgroundBump p R hR : WholePlane → ℝ)) := by
    funext z
    rfl
  have hconst : ContDiffAt ℝ 2 (fun _ : WholePlane ↦ (1 : ℝ)) x := contDiffAt_const
  have hbump : ContDiffAt ℝ 2 ((backgroundBump p R hR : WholePlane → ℝ)) x :=
    ((backgroundBump p R hR).contDiff : ContDiff ℝ 2 _).contDiffAt
  rw [hsplit, iteratedFDeriv_sub_apply hconst hbump,
    iteratedFDeriv_const_of_ne (by norm_num) (1 : ℝ)]
  simp

/-- A radius-independent second derivative constant for the background cut-off. -/
def backgroundSecondDerivativeConstant : ℝ :=
  1 + 100 * unitBackgroundSecondDerivativeConstant

/-- The background second-derivative constant is strictly positive. -/
theorem backgroundSecondDerivativeConstant_pos : 0 < backgroundSecondDerivativeConstant := by
  unfold backgroundSecondDerivativeConstant
  nlinarith [unitBackgroundSecondDerivativeConstant_nonneg]

/-- The background cut-off's second derivative is bounded by
`backgroundSecondDerivativeConstant / R ^ 2`: the `j = 2` half of `eq:parametrix-cutoff-bounds`
for `χ`. -/
theorem norm_backgroundCutoff_iteratedFDeriv_two_le
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    ‖iteratedFDeriv ℝ 2 (backgroundCutoff p R hR) x‖ ≤
      backgroundSecondDerivativeConstant / R ^ 2 := by
  rw [backgroundCutoff_iteratedFDeriv_two_eq p R hR x, norm_neg,
    backgroundBump_iteratedFDeriv_two_eq p R hR x, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (10 / R))]
  calc
    (10 / R) ^ 2 *
        ‖iteratedFDeriv ℝ 2 (unitBackgroundBump : WholePlane → ℝ)
          ((10 / R) • (x - p))‖ ≤
        (10 / R) ^ 2 * unitBackgroundSecondDerivativeConstant :=
      mul_le_mul_of_nonneg_left
        (unitBackground_secondDerivative_le ((10 / R) • (x - p))) (sq_nonneg _)
    _ = (100 * unitBackgroundSecondDerivativeConstant) / R ^ 2 := by ring
    _ ≤ backgroundSecondDerivativeConstant / R ^ 2 := by
      apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hR)).2
      unfold backgroundSecondDerivativeConstant
      nlinarith [unitBackgroundSecondDerivativeConstant_nonneg]

/-! ## `eq:parametrix-cutoff-bounds` for the three cut-offs together -/

/-- The common radius-independent first-derivative constant of the three cut-offs. -/
def cutoffFirstDerivativeConstant : ℝ :=
  2 * firstDerivativeConstant + backgroundFirstDerivativeConstant

/-- The common radius-independent second-derivative constant of the three cut-offs. -/
def cutoffSecondDerivativeConstant : ℝ :=
  2 * secondDerivativeConstant + backgroundSecondDerivativeConstant

/-- The common first-derivative constant is strictly positive. -/
theorem cutoffFirstDerivativeConstant_pos : 0 < cutoffFirstDerivativeConstant := by
  unfold cutoffFirstDerivativeConstant
  nlinarith [firstDerivativeConstant_pos, backgroundFirstDerivativeConstant_pos]

/-- The common second-derivative constant is strictly positive. -/
theorem cutoffSecondDerivativeConstant_pos : 0 < cutoffSecondDerivativeConstant := by
  unfold cutoffSecondDerivativeConstant
  nlinarith [secondDerivativeConstant_pos, backgroundSecondDerivativeConstant_pos]

/-- **The three-term first-derivative bound**: `‖Dφ‖_∞ + ‖Dψ‖_∞ + ‖Dχ‖_∞ ≤ C/R`, with `C`
independent of the radius and of the centre.  Its `ψ`/`χ` part is the `j = 1` half of the
paper's `eq:parametrix-cutoff-bounds`; the `φ` summand is a by-product of the
construction and is never read. -/
theorem norm_cutoff_coordinateDerivative_sum_le
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (j : Fin 2) (x : WholePlane) :
    ‖realProfileCoordinateDerivative (inputCutoff p R hR) j x‖ +
        ‖realProfileCoordinateDerivative (outputCutoff p R hR) j x‖ +
        ‖realProfileCoordinateDerivative (backgroundCutoff p R hR) j x‖ ≤
      cutoffFirstDerivativeConstant / R := by
  have h1 := norm_inputCutoff_coordinateDerivative_le p R hR j x
  have h2 := norm_outputCutoff_coordinateDerivative_le p R hR j x
  have h3 := norm_backgroundCutoff_coordinateDerivative_le p R hR j x
  have hsum : firstDerivativeConstant / R + firstDerivativeConstant / R +
      backgroundFirstDerivativeConstant / R = cutoffFirstDerivativeConstant / R := by
    unfold cutoffFirstDerivativeConstant
    ring
  calc
    _ ≤ firstDerivativeConstant / R + firstDerivativeConstant / R +
        backgroundFirstDerivativeConstant / R := by
      gcongr
    _ = cutoffFirstDerivativeConstant / R := hsum

/-- **The three-term second-derivative bound**: `‖D²φ‖_∞ + ‖D²ψ‖_∞ + ‖D²χ‖_∞ ≤ C/R²`, with `C`
independent of the radius and of the centre.  Its `ψ`/`χ` part is the `j = 2` half of the
paper's `eq:parametrix-cutoff-bounds`. -/
theorem norm_cutoff_iteratedFDeriv_two_sum_le
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    ‖iteratedFDeriv ℝ 2 (inputCutoff p R hR) x‖ +
        ‖iteratedFDeriv ℝ 2 (outputCutoff p R hR) x‖ +
        ‖iteratedFDeriv ℝ 2 (backgroundCutoff p R hR) x‖ ≤
      cutoffSecondDerivativeConstant / R ^ 2 := by
  have h1 := norm_inputCutoff_iteratedFDeriv_two_le p R hR x
  have h2 := norm_outputCutoff_iteratedFDeriv_two_le p R hR x
  have h3 := norm_backgroundCutoff_iteratedFDeriv_two_le p R hR x
  have hsum : secondDerivativeConstant / R ^ 2 + secondDerivativeConstant / R ^ 2 +
      backgroundSecondDerivativeConstant / R ^ 2 =
      cutoffSecondDerivativeConstant / R ^ 2 := by
    unfold cutoffSecondDerivativeConstant
    ring
  calc
    _ ≤ secondDerivativeConstant / R ^ 2 + secondDerivativeConstant / R ^ 2 +
        backgroundSecondDerivativeConstant / R ^ 2 := by
      gcongr
    _ = cutoffSecondDerivativeConstant / R ^ 2 := hsum

/-! ## `eq:parametrix-cutoff-identities` -/

/-- **The `χ` half of `eq:parametrix-cutoff-identities`**: `χ(1 - φ) = 1 - φ`.  Where `φ ≠ 1`
the distance to the centre exceeds `R/5`, hence exceeds `R/6`, so `χ = 1` there. -/
theorem backgroundCutoff_mul_one_sub_inputCutoff
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    backgroundCutoff p R hR x * (1 - inputCutoff p R hR x) =
      1 - inputCutoff p R hR x := by
  by_cases hx : inputCutoff p R hR x = 1
  · rw [hx]
    ring
  · have hdist : R / 5 < dist x p := by
      by_contra hcon
      exact hx (inputCutoff_eq_one_of_dist_le p R hR (not_lt.mp hcon))
    have hone : backgroundCutoff p R hR x = 1 :=
      backgroundCutoff_eq_one_of_radius_le_dist p R hR (by linarith)
    rw [hone, one_mul]

/-- **The `ψ` half of `eq:parametrix-cutoff-identities`**: `ψφ = φ`.  This is
`inputCutoff_mul_outputCutoff` in the paper's order. -/
theorem outputCutoff_mul_inputCutoff
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    outputCutoff p R hR x * inputCutoff p R hR x = inputCutoff p R hR x := by
  rw [mul_comm]
  exact inputCutoff_mul_outputCutoff p R hR x

/-- The partition underlying the two-summand parametrix:
`χ(1 - φ) + ψφ = 1`.  The background summand carries an output cut-off. -/
theorem cutoff_partition
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    backgroundCutoff p R hR x * (1 - inputCutoff p R hR x) +
        outputCutoff p R hR x * inputCutoff p R hR x = 1 := by
  rw [backgroundCutoff_mul_one_sub_inputCutoff p R hR x,
    outputCutoff_mul_inputCutoff p R hR x]
  ring

end ParametrixCutoffs

/-! ## The three placed cut-offs of one cell

The fibre-generic multiplier interface `TransverseVecSecondOrderCutoff` these cut-offs are
built from is in `Analysis/TransverseVecCutoffMultiplier.lean`. -/

namespace ParametrixCutoffs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The three placed parametrix cut-offs at a cell of reserved radius `R`, as
two-component periodic multipliers, together with `eq:parametrix-cutoff-bounds` and
`eq:parametrix-cutoff-identities` in the form the parametrix algebra consumes.

The two output cut-offs `ψ_n` and `χ_n` are the only ones whose derivatives are estimated: they
are the ones that produce the commutators in `lem:parametrix-error`.  The identities are stated
at the level of the `L²` multipliers, which is where the partition of the two-summand parametrix
lives. -/
structure HorizontalParametrixCutoffs (R : ℝ) where
  /-- The reserved radius `R_n` is positive. -/
  radius_pos : 0 < R
  /-- The smaller input cut-off `φ_n` (`= 1` on `D(p_n,R_n/5)`, supported in `D(p_n,R_n/4)`). -/
  input : TransverseVecSecondOrderCutoff (Fin 2)
  /-- The selected output cut-off `ψ_n` (`= 1` on `D(p_n,R_n/3)`, supported in
  `D(p_n,R_n/2)`). -/
  output : TransverseVecSecondOrderCutoff (Fin 2)
  /-- The background output cut-off `χ_n` (`= 0` on `D(p_n,R_n/10)`, `= 1` off
  `D(p_n,R_n/6)`). -/
  background : TransverseVecSecondOrderCutoff (Fin 2)
  /-- `|φ_n| ≤ 1`. -/
  norm_input_value_le_one : ‖input.value‖ ≤ 1
  /-- `‖1 - φ_n‖ ≤ 1`: because `0 ≤ φ_n ≤ 1` holds pointwise, the input complement of
  `eq:Rapp` is again a contraction of `L²`, not merely bounded by the triangle inequality.
  The `[0, 1]`-valuedness of the three cut-offs is required in §7.1;
  the scale bound `eq:parametrix-cutoff-bounds` carries no `φ_n` summand. -/
  norm_inputComplement_le_one :
    ‖ContinuousLinearMap.id ℂ TransverseC2L2 - input.stateMul‖ ≤ 1
  /-- `|ψ_n| ≤ 1`. -/
  norm_output_value_le_one : ‖output.value‖ ≤ 1
  /-- `|χ_n| ≤ 1`. -/
  norm_background_value_le_one : ‖background.value‖ ≤ 1
  /-- `‖∂_jψ_n‖_∞ ≤ C₁/R_n` (`eq:parametrix-cutoff-bounds`). -/
  norm_output_gradient_le : ∀ j,
    ‖output.gradient j‖ ≤ cutoffFirstDerivativeConstant / R
  /-- `‖Δψ_n‖_∞ ≤ 2C₂/R_n²` (`eq:parametrix-cutoff-bounds`). -/
  norm_output_laplacian_le :
    ‖output.laplacian‖ ≤ 2 * cutoffSecondDerivativeConstant / R ^ 2
  /-- `‖∂_jχ_n‖_∞ ≤ C₁/R_n` (`eq:parametrix-cutoff-bounds`). -/
  norm_background_gradient_le : ∀ j,
    ‖background.gradient j‖ ≤ cutoffFirstDerivativeConstant / R
  /-- `‖Δχ_n‖_∞ ≤ 2C₂/R_n²` (`eq:parametrix-cutoff-bounds`). -/
  norm_background_laplacian_le :
    ‖background.laplacian‖ ≤ 2 * cutoffSecondDerivativeConstant / R ^ 2
  /-- `χ_n(1 - φ_n) = 1 - φ_n` (`eq:parametrix-cutoff-identities`). -/
  background_mul_inputComplement :
    background.stateMul.comp
        (ContinuousLinearMap.id ℂ TransverseC2L2 - input.stateMul) =
      ContinuousLinearMap.id ℂ TransverseC2L2 - input.stateMul
  /-- `ψ_nφ_n = φ_n` (`eq:parametrix-cutoff-identities`). -/
  output_mul_input : output.stateMul.comp input.stateMul = input.stateMul

namespace HorizontalParametrixCutoffs

variable {R : ℝ}

/-- The input complement `1 - φ_n`, the state-space restriction feeding the background
summand of `eq:Rapp`. -/
def inputComplement (C : HorizontalParametrixCutoffs R) :
    TransverseC2L2 →L[ℂ] TransverseC2L2 :=
  ContinuousLinearMap.id ℂ TransverseC2L2 - C.input.stateMul

/-- `‖1 - φ_n‖ ≤ 1`: the sharp bound that the parametrix error estimate uses on the input side
of the background summand.  It is the structure field `norm_inputComplement_le_one`, which the
placed cut-off discharges from `0 ≤ φ_n ≤ 1`, the paper's choice of the three cut-offs
with values in `[0, 1]` (§7.1); the triangle inequality
would only give `2`. -/
theorem norm_inputComplement_le (C : HorizontalParametrixCutoffs R) :
    ‖C.inputComplement‖ ≤ 1 :=
  C.norm_inputComplement_le_one

/-- **The partition behind the two-summand parametrix**: `χ_n(1 - φ_n) + ψ_nφ_n = 1`, the exact
hypothesis `hpartition` of the two-summand assembly.  It follows from the two identities of
`eq:parametrix-cutoff-identities` alone. -/
theorem partition (C : HorizontalParametrixCutoffs R) :
    C.background.stateMul.comp C.inputComplement +
        C.output.stateMul.comp C.input.stateMul =
      ContinuousLinearMap.id ℂ TransverseC2L2 := by
  rw [inputComplement, C.background_mul_inputComplement, C.output_mul_input]
  abel

end HorizontalParametrixCutoffs

end ParametrixCutoffs

end

end FastDynamo
