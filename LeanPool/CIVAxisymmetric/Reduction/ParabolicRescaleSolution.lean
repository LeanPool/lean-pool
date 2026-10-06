/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.MeridionalPartial
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import LeanPool.CIVAxisymmetric.Reduction.AnalyticPredicates
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingQuantities
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceBasic
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The Navier–Stokes scaling transports a classical solution

The scaling `u ↦ R u(R·, R²·)`, `π ↦ R² π(R·, R²·)`, `f ↦ R³ f(R·, R²·)` — the rescaled
fields `CKN.rescaleVelocity`, `CKN.rescalePressure`, `CKN.rescaleForce` of the parabolic
dilation `CKN.scalingParabolic` — carries a classical solution of `eq:nse:forced` on a
space-time set `S` to a classical solution on the preimage of `S`.

The three derivative identities behind it are unconditional: for every scalar `c` and every
dilation parameter `μ`,

* `∂_i (c · g ∘ T) = c μ (∂_i g) ∘ T`,
* `∂_t (c · g ∘ T) = c μ² (∂_t g) ∘ T`,
* `∂_j ∂_i (c · g ∘ T) = c μ² (∂_j ∂_i g) ∘ T`,

where `T = CKN.scalingParabolic μ z₀`. No smoothness is needed for them: the spatial and
temporal slices of `g ∘ T` are reparametrisations of the slices of `g` by an affine map, and
the composition rules `fderiv_comp_smul`, `fderiv_comp_add_left` and `fderiv_const_smul_field`
that they use hold with no differentiability hypothesis. Every term of the momentum equation
therefore picks up the same factor `μ³`, and the divergence picks up `μ²`.

The same rule iterated gives the meridional derivatives of `eq:interior:mean:bounds`: a
derivative of order `(a, b)` of the rescaled velocity carries the factor `μ^(1+a+b)`, which is
exactly the prefactor that `CIV.rpow_scaled_le_of_radialAnisoBound` and
`CIV.rpow_scaled_le_of_swirlVerticalAnisoBound` convert into the rescaled constants.

The last theorem is the form used in `cor:interior:nonanalytic`: for `0 < R ≤ R'` and
`R² ≤ δ'`, the scaling carries a classical solution on `B(R') × (-δ', 0)` to one on the unit
parabolic cylinder `CIV.unitCylinder`, which is the cylinder the hypotheses of `thm:main`
are read on.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-! ### Derivatives under an affine reparametrisation -/

/-- The chain rule for a constant multiple of a function precomposed with the affine map
`y ↦ a + μ y`. It holds for every `c` and every `μ`, with no differentiability hypothesis,
because each of its three steps — the constant multiple, the dilation and the translation —
is an unconditional identity of Fréchet derivatives. -/
private theorem fderiv_apply_const_mul_affine {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c μ : ℝ) (a : E) (G : E → ℝ) (x v : E) :
    fderiv ℝ (fun y : E => c * G (a + μ • y)) x v = c * μ * fderiv ℝ G (a + μ • x) v := by
  have e1 : (fun y : E => c * G (a + μ • y)) = c • fun y : E => G (a + μ • y) := by
    funext y
    simp
  have e2 : fderiv ℝ (fun y : E => G (a + μ • y)) x
      = μ • fderiv ℝ (fun y : E => G (a + y)) (μ • x) :=
    fderiv_comp_smul (f := fun y : E => G (a + y)) (x := x) μ
  have e3 : fderiv ℝ (fun y : E => G (a + y)) (μ • x) = fderiv ℝ G (a + μ • x) :=
    fderiv_comp_add_left (f := G) (x := μ • x) a
  rw [e1, fderiv_const_smul_field, Pi.smul_apply, e2, e3, smul_smul]
  simp [mul_assoc]

/-! ### Derivatives under the parabolic rescaling -/

/-- A spatial derivative of `c · g ∘ T`, for `T` the parabolic dilation of ratio `μ` at `z₀`,
is `c μ` times the same derivative of `g` at the dilated point. -/
theorem spatialPartial_const_mul_comp_scalingParabolic (c μ : ℝ) (z₀ : ParabolicPoint)
    (g : ParabolicPoint → ℝ) (i : Fin 3) (z : ParabolicPoint) :
    spatialPartial (fun w : ParabolicPoint => c * g (scalingParabolic μ z₀ w)) i z
      = c * μ * spatialPartial g i (scalingParabolic μ z₀ z) := by
  show fderiv ℝ (fun x : Vec3 => c * g (z₀.1 + μ • x, z₀.2 + μ ^ 2 * z.2)) z.1 (basisVec i)
      = c * μ *
        fderiv ℝ (fun x : Vec3 => g (x, z₀.2 + μ ^ 2 * z.2)) (z₀.1 + μ • z.1) (basisVec i)
  exact fderiv_apply_const_mul_affine c μ z₀.1 (fun y : Vec3 => g (y, z₀.2 + μ ^ 2 * z.2))
    z.1 (basisVec i)

/-- The time derivative of `c · g ∘ T`, for `T` the parabolic dilation of ratio `μ` at `z₀`,
is `c μ²` times the time derivative of `g` at the dilated point. -/
theorem timePartial_const_mul_comp_scalingParabolic (c μ : ℝ) (z₀ : ParabolicPoint)
    (g : ParabolicPoint → ℝ) (z : ParabolicPoint) :
    timePartial (fun w : ParabolicPoint => c * g (scalingParabolic μ z₀ w)) z
      = c * μ ^ 2 * timePartial g (scalingParabolic μ z₀ z) := by
  show fderiv ℝ (fun s : ℝ => c * g (z₀.1 + μ • z.1, z₀.2 + μ ^ 2 * s)) z.2 1
      = c * μ ^ 2 * fderiv ℝ (fun s : ℝ => g (z₀.1 + μ • z.1, s)) (z₀.2 + μ ^ 2 * z.2) 1
  exact fderiv_apply_const_mul_affine c (μ ^ 2) z₀.2
    (fun s : ℝ => g (z₀.1 + μ • z.1, s)) z.2 1

/-- A second spatial derivative of `c · g ∘ T`, for `T` the parabolic dilation of ratio `μ`
at `z₀`, is `c μ²` times the same derivative of `g` at the dilated point: the first
derivative already has the shape to which the first-order rule applies again. -/
theorem spatialSecondPartial_const_mul_comp_scalingParabolic (c μ : ℝ) (z₀ : ParabolicPoint)
    (g : ParabolicPoint → ℝ) (i j : Fin 3) (z : ParabolicPoint) :
    spatialSecondPartial (fun w : ParabolicPoint => c * g (scalingParabolic μ z₀ w)) i j z
      = c * μ ^ 2 * spatialSecondPartial g i j (scalingParabolic μ z₀ z) := by
  have h1 : (fun w : ParabolicPoint =>
        spatialPartial (fun w' : ParabolicPoint => c * g (scalingParabolic μ z₀ w')) i w)
      = fun w : ParabolicPoint => c * μ * spatialPartial g i (scalingParabolic μ z₀ w) :=
    funext fun w => spatialPartial_const_mul_comp_scalingParabolic c μ z₀ g i w
  have h2 : spatialPartial (fun w : ParabolicPoint =>
        c * μ * spatialPartial g i (scalingParabolic μ z₀ w)) j z
      = c * μ * μ * spatialPartial (fun w : ParabolicPoint => spatialPartial g i w) j
          (scalingParabolic μ z₀ z) :=
    spatialPartial_const_mul_comp_scalingParabolic (c * μ) μ z₀
      (fun w : ParabolicPoint => spatialPartial g i w) j z
  calc spatialSecondPartial (fun w : ParabolicPoint => c * g (scalingParabolic μ z₀ w)) i j z
      = spatialPartial (fun w : ParabolicPoint =>
          c * μ * spatialPartial g i (scalingParabolic μ z₀ w)) j z := by
        rw [← h1]; rfl
    _ = c * μ * μ * spatialPartial (fun w : ParabolicPoint => spatialPartial g i w) j
          (scalingParabolic μ z₀ z) := h2
    _ = c * μ ^ 2 * spatialSecondPartial g i j (scalingParabolic μ z₀ z) := by
        show c * μ * μ * spatialPartial (fun w : ParabolicPoint => spatialPartial g i w) j
            (scalingParabolic μ z₀ z)
          = c * μ ^ 2 * spatialPartial (fun w : ParabolicPoint => spatialPartial g i w) j
            (scalingParabolic μ z₀ z)
        ring

/-! ### Meridional derivatives under the parabolic rescaling -/

/-- Iterating a single spatial direction: `n` derivatives in the direction `i` of
`c · g ∘ T` are `c μⁿ` times the same `n` derivatives of `g` at the dilated point. -/
private theorem iterate_spatialPartial_const_mul_comp (μ : ℝ) (z₀ : ParabolicPoint)
    (i : Fin 3) :
    ∀ (n : ℕ) (c : ℝ) (g : ParabolicPoint → ℝ),
      (fun k => spatialPartial k i)^[n] (fun w : ParabolicPoint => c * g (scalingParabolic μ z₀ w))
        = fun w : ParabolicPoint =>
            c * μ ^ n * (fun k => spatialPartial k i)^[n] g (scalingParabolic μ z₀ w) := by
  intro n
  induction n with
  | zero =>
      intro c g
      funext w
      simp
  | succ n ih =>
      intro c g
      have hstep : spatialPartial (fun w : ParabolicPoint => c * g (scalingParabolic μ z₀ w)) i
          = fun w : ParabolicPoint =>
              c * μ * spatialPartial g i (scalingParabolic μ z₀ w) :=
        funext fun w => spatialPartial_const_mul_comp_scalingParabolic c μ z₀ g i w
      rw [Function.iterate_succ_apply, hstep, ih (c * μ) (spatialPartial g i),
        Function.iterate_succ_apply]
      funext w
      ring

/-- The meridional derivative `∂_r^a ∂_z^b` of `c · g ∘ T` is `c μ^(a+b)` times the same
derivative of `g` at the dilated point, for all orders `a` and `b`. -/
theorem meridionalPartial_const_mul_comp_scalingParabolic (c μ : ℝ) (z₀ : ParabolicPoint)
    (g : ParabolicPoint → ℝ) (a b : ℕ) (z : ParabolicPoint) :
    meridionalPartial (fun w : ParabolicPoint => c * g (scalingParabolic μ z₀ w)) a b z
      = c * μ ^ (a + b) * meridionalPartial g a b (scalingParabolic μ z₀ z) := by
  have hb := iterate_spatialPartial_const_mul_comp μ z₀ 2 b c g
  have ha := iterate_spatialPartial_const_mul_comp μ z₀ 0 a (c * μ ^ b)
      ((fun k => spatialPartial k 2)^[b] g)
  show ((fun k => spatialPartial k 0)^[a] ((fun k => spatialPartial k 2)^[b]
      (fun w : ParabolicPoint => c * g (scalingParabolic μ z₀ w)))) z
      = c * μ ^ (a + b) *
        ((fun k => spatialPartial k 0)^[a] ((fun k => spatialPartial k 2)^[b] g))
          (scalingParabolic μ z₀ z)
  rw [hb, ha]
  ring

/-- The prefactor of the rescaled anisotropic bounds `eq:interior:mean:bounds`: a meridional
derivative of order `(a, b)` of the rescaled velocity is `μ^(1+a+b)` times the same derivative
of the velocity at the dilated point. This is the left-hand factor `R^(1+a+b)` of
`CIV.rpow_scaled_le_of_radialAnisoBound` and of
`CIV.rpow_scaled_le_of_swirlVerticalAnisoBound`, which convert it into the rescaled
constants. -/
theorem meridionalPartial_rescaleVelocity (μ : ℝ) (z₀ : ParabolicPoint)
    (u : ParabolicPoint → Vec3) (i : Fin 3) (a b : ℕ) (z : ParabolicPoint) :
    meridionalPartial (fun w : ParabolicPoint => rescaleVelocity μ z₀ u w i) a b z
      = μ ^ (1 + a + b) * meridionalPartial (fun w : ParabolicPoint => u w i) a b
          (scalingParabolic μ z₀ z) := by
  have h : meridionalPartial (fun w : ParabolicPoint => rescaleVelocity μ z₀ u w i) a b z
      = μ * μ ^ (a + b) * meridionalPartial (fun w : ParabolicPoint => u w i) a b
          (scalingParabolic μ z₀ z) :=
    meridionalPartial_const_mul_comp_scalingParabolic μ μ z₀
      (fun w : ParabolicPoint => u w i) a b z
  rw [h]
  ring

/-! ### The transport of `eq:nse:forced` -/

/-- The parabolic dilation `z ↦ (x₀ + μ y, t₀ + μ² s)` is smooth on the product carrier. -/
private theorem contDiff_scalingParabolic (μ : ℝ) (z₀ : ParabolicPoint) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => (z₀.1 + μ • z.1, z₀.2 + μ ^ 2 * z.2)) :=
  (contDiff_const.add (contDiff_fst.const_smul μ)).prodMk
    (contDiff_const.add (contDiff_const.mul contDiff_snd))

/-- The Navier–Stokes scaling of the footnote to `eq:nse:forced`, `u ↦ R u(R·, R²·)`,
`π ↦ R² π(R·, R²·)`, `f ↦ R³ f(R·, R²·)` based at `z₀`, carries a classical solution on `S`
to a classical solution on the preimage of `S` under the dilation. Every term of the momentum
equation is multiplied by `μ³` and the divergence by `μ²`, so both equations are preserved
exactly; the identity therefore needs no restriction on `μ`, and the case used in
`cor:interior:nonanalytic` is `0 < R ≤ 1`. -/
theorem isClassicalSolutionOn_parabolicRescale (μ : ℝ) (z₀ : ParabolicPoint)
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {S : Set ParabolicPoint} (h : IsClassicalSolutionOn u p f S) :
    IsClassicalSolutionOn (rescaleVelocity μ z₀ u) (rescalePressure μ z₀ p)
      (rescaleForce μ z₀ f) (scalingParabolic μ z₀ ⁻¹' S) := by
  have hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => (z₀.1 + μ • z.1, z₀.2 + μ ^ 2 * z.2))
      (scalingParabolic μ z₀ ⁻¹' S) := (contDiff_scalingParabolic μ z₀).contDiffOn
  have hmaps : MapsTo (fun z : Vec3 × ℝ => ((z₀.1 + μ • z.1, z₀.2 + μ ^ 2 * z.2) : Vec3 × ℝ))
      (scalingParabolic μ z₀ ⁻¹' S) S := fun z hz => hz
  refine ⟨(h.1.comp hT hmaps).const_smul μ, (h.2.1.comp hT hmaps).const_smul (μ ^ 2),
    (h.2.2.1.comp hT hmaps).const_smul (μ ^ 3), ?_, ?_⟩
  · intro z hz i
    have heq := h.2.2.2.1 (scalingParabolic μ z₀ z) hz i
    have hA : timePartial (fun w : ParabolicPoint => rescaleVelocity μ z₀ u w i) z
        = μ * μ ^ 2 * timePartial (fun w : ParabolicPoint => u w i)
            (scalingParabolic μ z₀ z) :=
      timePartial_const_mul_comp_scalingParabolic μ μ z₀ (fun w : ParabolicPoint => u w i) z
    have hB : ∀ j : Fin 3,
        spatialPartial (fun w : ParabolicPoint => rescaleVelocity μ z₀ u w i) j z
          = μ * μ * spatialPartial (fun w : ParabolicPoint => u w i) j
              (scalingParabolic μ z₀ z) := fun j =>
      spatialPartial_const_mul_comp_scalingParabolic μ μ z₀ (fun w : ParabolicPoint => u w i) j z
    have hC : ∀ j : Fin 3,
        spatialSecondPartial (fun w : ParabolicPoint => rescaleVelocity μ z₀ u w i) j j z
          = μ * μ ^ 2 * spatialSecondPartial (fun w : ParabolicPoint => u w i) j j
              (scalingParabolic μ z₀ z) := fun j =>
      spatialSecondPartial_const_mul_comp_scalingParabolic μ μ z₀
        (fun w : ParabolicPoint => u w i) j j z
    have hD : spatialPartial (rescalePressure μ z₀ p) i z
        = μ ^ 2 * μ * spatialPartial p i (scalingParabolic μ z₀ z) :=
      spatialPartial_const_mul_comp_scalingParabolic (μ ^ 2) μ z₀ p i z
    have hF : rescaleForce μ z₀ f z i = μ ^ 3 * f (scalingParabolic μ z₀ z) i := rfl
    have hS1 : ∑ j, rescaleVelocity μ z₀ u z j *
          spatialPartial (fun w : ParabolicPoint => rescaleVelocity μ z₀ u w i) j z
        = μ ^ 3 * ∑ j, u (scalingParabolic μ z₀ z) j *
            spatialPartial (fun w : ParabolicPoint => u w i) j (scalingParabolic μ z₀ z) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hB j]
      show μ * u (scalingParabolic μ z₀ z) j *
          (μ * μ * spatialPartial (fun w : ParabolicPoint => u w i) j (scalingParabolic μ z₀ z))
        = μ ^ 3 * (u (scalingParabolic μ z₀ z) j *
            spatialPartial (fun w : ParabolicPoint => u w i) j (scalingParabolic μ z₀ z))
      ring
    have hS2 : ∑ j, spatialSecondPartial
          (fun w : ParabolicPoint => rescaleVelocity μ z₀ u w i) j j z
        = μ ^ 3 * ∑ j, spatialSecondPartial (fun w : ParabolicPoint => u w i) j j
            (scalingParabolic μ z₀ z) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hC j]
      ring
    rw [hA, hS1, hS2, hD, hF]
    linear_combination (μ ^ 3) * heq
  · intro z hz
    have hdiv := h.2.2.2.2 (scalingParabolic μ z₀ z) hz
    have hsum : ∑ j, spatialPartial (fun w : ParabolicPoint => rescaleVelocity μ z₀ u w j) j z
        = μ * μ * ∑ j, spatialPartial (fun w : ParabolicPoint => u w j) j
            (scalingParabolic μ z₀ z) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ =>
        spatialPartial_const_mul_comp_scalingParabolic μ μ z₀
          (fun w : ParabolicPoint => u w j) j z
    rw [hsum, hdiv, mul_zero]

/-- The form of the scaling used in `cor:interior:nonanalytic`: a classical solution of
`eq:nse:forced` on `B(R') × (-δ', 0)` is carried to a classical solution on the unit parabolic
cylinder by the dilation of ratio `R`, for every `0 < R ≤ R'` with `R² ≤ δ'`. -/
theorem isClassicalSolutionOn_unitCylinder_of_parabolicRescale {R R' δ' : ℝ} (hR : 0 < R)
    (hRR' : R ≤ R') (hRδ : R ^ 2 ≤ δ') {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3}
    (h : IsClassicalSolutionOn u p f (spaceTimeSet (vec3Ball 0 R') (Ioo (-δ') 0))) :
    IsClassicalSolutionOn (rescaleVelocity R ((0 : Vec3), (0 : ℝ)) u)
      (rescalePressure R ((0 : Vec3), (0 : ℝ)) p) (rescaleForce R ((0 : Vec3), (0 : ℝ)) f)
      unitCylinder := by
  have hsub : unitCylinder ⊆ scalingParabolic R ((0 : Vec3), (0 : ℝ)) ⁻¹'
      spaceTimeSet (vec3Ball 0 R') (Ioo (-δ') 0) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have hxnorm : vec3EuclideanNorm x < 1 := by
      simpa using hx
    have hspace : vec3EuclideanNorm (((0 : Vec3) + R • x) - 0) < R' := by
      have hR0 : ((0 : Vec3) + R • x) - 0 = R • x := by
        rw [zero_add, sub_zero]
      rw [hR0, vec3EuclideanNorm_smul, abs_of_pos hR]
      calc R * vec3EuclideanNorm x < R * 1 := mul_lt_mul_of_pos_left hxnorm hR
        _ = R := mul_one R
        _ ≤ R' := hRR'
    have htime : (0 : ℝ) + R ^ 2 * t ∈ Ioo (-δ') 0 := by
      have hR2 : (0 : ℝ) < R ^ 2 := pow_pos hR 2
      constructor
      · have : -(R ^ 2) < R ^ 2 * t := by
          have := mul_lt_mul_of_pos_left ht.1 hR2
          linarith only [this]
        linarith only [this, hRδ]
      · have := mul_neg_of_pos_of_neg hR2 ht.2
        linarith only [this]
    exact ⟨hspace, htime⟩
  exact (isClassicalSolutionOn_parabolicRescale R _ h).mono hsub

end CIV
