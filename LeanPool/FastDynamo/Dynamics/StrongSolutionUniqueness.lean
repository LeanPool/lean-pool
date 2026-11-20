/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.StronglyContinuousSemigroup
public import LeanPool.FastDynamo.Global.ReducedInductionEnergyIdentity
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Uniqueness and the a priori energy bound for forward strong solutions

This module proves uniqueness of strong solutions of the induction equation in a fixed axial
sector, which `FastDynamo/Main.lean` does not state.

The analytic input is a half-plane bound for the numerical range.  If a `DomainOperator`
`A : DomainOperator X D` on a complex inner-product space `X` satisfies

`Re ⟪ι d, A d⟫ ≤ M ‖ι d‖²`  for every domain element `d`

(`ι` the domain-to-ambient embedding), then along any forward strong solution `B` the
squared ambient energy `φ(t) = ‖ι B(t)‖²` obeys `φ' ≤ 2 M φ` on `(0, ∞)` — that is where
the one-sided derivative of `IsForwardStrongSolution` upgrades to a two-sided one — hence
`e^{-2Mt} φ(t)` is antitone on `[0, ∞)` and

`‖ι B(t)‖ ≤ e^{M t} ‖ι B(0)‖`.

This is the operator-level form of the paper's (formal) energy competition
`eq:energy-competition`, for complex fields through the real part of the pairing: the
stretching term contributes at most
`‖∇⊥ u‖_∞ ‖B‖²`, diffusion contributes a nonpositive term, and transport contributes
nothing.
Applied to the difference of two forward strong solutions with the same initial ambient state
it gives uniqueness, i.e. the uniqueness half of an energy well-posedness statement that
the paper does not make, for the reduced fixed-sector
operator, at `H²` regularity and for an autonomous velocity.  The statement of
Theorem 1.2 does not contain it; in the Lean proof its all-frequency form
`productInductionOperator_forwardStrongSolutionsUnique` identifies the semigroup orbit of an
eigenvector with the exponential trajectory.

The half-plane bound itself is available for `reducedInductionOperator u ε K`: it is
the exact energy identity `re_inner_reducedInductionAction_eq` together with the stretching
estimate `re_inner_reducedInductionStretching_le` of
`FastDynamo/Global/ReducedInductionEnergyIdentity.lean`, with
`M = ‖transverseStretchingCoefficient u‖` independent of `ε` and of the axial index `K`.
Consequently `reducedInductionOperator_forwardStrongSolutionsUnique` holds for every
divergence-free `u`, every `ε ≥ 0` and every `K`.

No semigroup is constructed here; generation is the business of
`FastDynamo/Dynamics/HilleYosida/` and `FastDynamo/Dynamics/Assembly/ProductSemigroup.lean`.

The Grönwall step is carried out by hand through
`antitoneOn_of_hasDerivWithinAt_nonpos` rather than through
`Mathlib.Analysis.ODE.Gronwall`: the exponential-multiplier argument needs no import beyond
the mean-value theory.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Set

universe u v

namespace DomainOperator

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

/-- At a strictly positive time the embedded curve of a forward strong solution is
differentiable, with derivative the operator applied to the current state.  The nonnegative
half-line of the definition of `IsForwardStrongSolution` is a neighbourhood of every positive
time, so the one-sided derivative upgrades to a two-sided one. -/
theorem hasDerivAt_embedding_of_isForwardStrongSolution
    (A : DomainOperator X D) {trajectory : ℝ → D}
    (h : A.IsForwardStrongSolution trajectory) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ ↦ A.embedding (trajectory s)) (A.op (trajectory t)) t :=
  (h t ht.le).hasDerivAt (Ici_mem_nhds ht)

/-- The squared ambient energy of a forward strong solution is continuous on `[0, ∞)`, being
the squared norm of a curve that is one-sidedly differentiable there. -/
theorem continuousOn_norm_embedding_sq_of_isForwardStrongSolution
    (A : DomainOperator X D) {trajectory : ℝ → D}
    (h : A.IsForwardStrongSolution trajectory) :
    ContinuousOn (fun s : ℝ ↦ ‖A.embedding (trajectory s)‖ ^ 2) (Ici 0) := fun s hs ↦
  (((h s hs).continuousWithinAt).norm).pow 2

/-- Differentiation of the energy along a curve whose ambient embedding is differentiable at `t`
with derivative the operator applied to the current state: the squared ambient norm has derivative
`2 Re ⟪ι B(t), A B(t)⟫`. -/
theorem hasDerivAt_norm_embedding_sq_of_hasDerivAt_embedding
    (A : DomainOperator X D) {trajectory : ℝ → D} {t : ℝ}
    (hcurve : HasDerivAt (fun s : ℝ ↦ A.embedding (trajectory s))
      (A.op (trajectory t)) t) :
    HasDerivAt (fun s : ℝ ↦ ‖A.embedding (trajectory s)‖ ^ 2)
      (2 * (inner ℂ (A.embedding (trajectory t)) (A.op (trajectory t))).re) t := by
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hcurve.inner ℂ hcurve)
  have hconj : inner ℂ (A.op (trajectory t)) (A.embedding (trajectory t))
      = (starRingEnd ℂ) (inner ℂ (A.embedding (trajectory t)) (A.op (trajectory t))) :=
    (inner_conj_symm _ _).symm
  have hself : (fun s : ℝ ↦
        (inner ℂ (A.embedding (trajectory s)) (A.embedding (trajectory s))).re)
      = fun s : ℝ ↦ ‖A.embedding (trajectory s)‖ ^ 2 :=
    funext fun s ↦ inner_self_eq_norm_sq (𝕜 := ℂ) _
  simp only [Function.comp_def, Complex.reCLM_apply, Complex.add_re, hconj,
    Complex.conj_re, hself] at hre
  rw [two_mul]
  exact hre

/-- Differentiation of the energy at a positive time: the squared ambient norm of a forward
strong solution has derivative `2 Re ⟪ι B(t), A B(t)⟫`.  This is the exact statement of the
paper's energy identity `eq:energy-competition` before any estimate of the
right-hand side. -/
theorem hasDerivAt_norm_embedding_sq_of_isForwardStrongSolution
    (A : DomainOperator X D) {trajectory : ℝ → D}
    (h : A.IsForwardStrongSolution trajectory) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ ↦ ‖A.embedding (trajectory s)‖ ^ 2)
      (2 * (inner ℂ (A.embedding (trajectory t)) (A.op (trajectory t))).re) t :=
  A.hasDerivAt_norm_embedding_sq_of_hasDerivAt_embedding
    (A.hasDerivAt_embedding_of_isForwardStrongSolution h ht)

/-- The difference of two forward strong solutions is again a forward strong solution, by
linearity of the domain-to-ambient embedding and of the operator. -/
theorem isForwardStrongSolution_sub
    (A : DomainOperator X D) {trajectory₁ trajectory₂ : ℝ → D}
    (h₁ : A.IsForwardStrongSolution trajectory₁)
    (h₂ : A.IsForwardStrongSolution trajectory₂) :
    A.IsForwardStrongSolution fun s : ℝ ↦ trajectory₁ s - trajectory₂ s := by
  intro t ht
  simpa only [map_sub] using (h₁ t ht).fun_sub (h₂ t ht)

/-- **A priori energy estimate, squared form.**  If the numerical range of `A` lies in the
half-plane `{Re z ≤ M}`, measured through the domain-to-ambient embedding, then along every
forward strong solution the squared ambient energy grows at most like `e^{2Mt}`.

The proof is the exponential-multiplier form of Grönwall's lemma: the energy
`φ(t) = ‖ι B(t)‖²` satisfies `φ'(t) = 2 Re ⟪ι B(t), A B(t)⟫ ≤ 2 M φ(t)` at every
positive time, so `e^{-2Mt} φ(t)` has nonpositive derivative and is antitone on every
`[0, T]`. -/
theorem norm_embedding_sq_le_exp_of_isForwardStrongSolution
    (A : DomainOperator X D) (M : ℝ)
    (hM : ∀ d : D, (inner ℂ (A.embedding d) (A.op d)).re ≤ M * ‖A.embedding d‖ ^ 2)
    {trajectory : ℝ → D} (h : A.IsForwardStrongSolution trajectory)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖A.embedding (trajectory t)‖ ^ 2 ≤
      Real.exp (2 * M * t) * ‖A.embedding (trajectory 0)‖ ^ 2 := by
  have hcont : ContinuousOn
      (fun s : ℝ ↦ Real.exp (-(2 * M) * s) * ‖A.embedding (trajectory s)‖ ^ 2)
      (Icc 0 t) := by
    refine ContinuousOn.mul ?_
      ((A.continuousOn_norm_embedding_sq_of_isForwardStrongSolution h).mono
        Icc_subset_Ici_self)
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun s : ℝ ↦
      -(2 * M) * Real.exp (-(2 * M) * s) * ‖A.embedding (trajectory s)‖ ^ 2 +
        Real.exp (-(2 * M) * s) *
          (2 * (inner ℂ (A.embedding (trajectory s)) (A.op (trajectory s))).re))
    (convex_Icc 0 t) hcont ?_ ?_
  · have hle := hanti (left_mem_Icc.2 ht) (right_mem_Icc.2 ht) ht
    simp only [mul_zero, Real.exp_zero, one_mul] at hle
    have hmul : Real.exp (2 * M * t) * Real.exp (-(2 * M) * t) = 1 := by
      rw [← Real.exp_add, show 2 * M * t + -(2 * M) * t = 0 by ring, Real.exp_zero]
    calc ‖A.embedding (trajectory t)‖ ^ 2
        = Real.exp (2 * M * t) *
            (Real.exp (-(2 * M) * t) * ‖A.embedding (trajectory t)‖ ^ 2) := by
          rw [← mul_assoc, hmul, one_mul]
      _ ≤ Real.exp (2 * M * t) * ‖A.embedding (trajectory 0)‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
  · intro x hx
    rw [interior_Icc] at hx ⊢
    have hexp : HasDerivAt (fun s : ℝ ↦ Real.exp (-(2 * M) * s))
        (-(2 * M) * Real.exp (-(2 * M) * x)) x := by
      simpa [mul_comm] using ((hasDerivAt_id x).const_mul (-(2 * M))).exp
    exact (hexp.mul
      (A.hasDerivAt_norm_embedding_sq_of_isForwardStrongSolution h hx.1)).hasDerivWithinAt
  · intro x _
    have hpos : (0 : ℝ) < Real.exp (-(2 * M) * x) := Real.exp_pos _
    have hbound := hM (trajectory x)
    nlinarith [hpos]

/-- **A priori energy estimate.**  If the numerical range of `A` lies in the half-plane
`{Re z ≤ M}`, every forward strong solution obeys `‖ι B(t)‖ ≤ e^{M t} ‖ι B(0)‖` for
`t ≥ 0`.

This is the growth ceiling attached to the paper's energy competition
`eq:energy-competition`; for the reduced induction operator `M` is the
`L^∞` norm of the transverse velocity gradient, so the ceiling is uniform in the
diffusivity `ε` and in the axial index `K`. -/
theorem norm_embedding_le_exp_of_isForwardStrongSolution
    (A : DomainOperator X D) (M : ℝ)
    (hM : ∀ d : D, (inner ℂ (A.embedding d) (A.op d)).re ≤ M * ‖A.embedding d‖ ^ 2)
    {trajectory : ℝ → D} (h : A.IsForwardStrongSolution trajectory)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖A.embedding (trajectory t)‖ ≤
      Real.exp (M * t) * ‖A.embedding (trajectory 0)‖ := by
  have hsq := A.norm_embedding_sq_le_exp_of_isForwardStrongSolution M hM h ht
  have hexp : Real.exp (M * t) ^ 2 = Real.exp (2 * M * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsquared : ‖A.embedding (trajectory t)‖ ^ 2 ≤
      (Real.exp (M * t) * ‖A.embedding (trajectory 0)‖) ^ 2 := by
    rw [mul_pow, hexp]
    exact hsq
  have hroot := Real.sqrt_le_sqrt hsquared
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at hroot

/-- **Uniqueness of forward strong solutions from a half-plane numerical range.**  If
`Re ⟪ι d, A d⟫ ≤ M ‖ι d‖²` for every domain element `d`, then two forward strong solutions
of `A` with the same initial ambient state have the same ambient state at every
nonnegative time.

The difference of the two solutions is again a forward strong solution, with vanishing initial
ambient state, so the a priori energy estimate
`norm_embedding_le_exp_of_isForwardStrongSolution` forces its ambient curve to vanish
identically.  This is the uniqueness half of an energy well-posedness statement
(see the module docstring), stated at the regularity of the bundled operator domain. -/
theorem forwardStrongSolutionsUnique_of_re_inner_le
    (A : DomainOperator X D) (M : ℝ)
    (hM : ∀ d : D, (inner ℂ (A.embedding d) (A.op d)).re ≤ M * ‖A.embedding d‖ ^ 2) :
    A.ForwardStrongSolutionsUnique := by
  intro trajectory₁ trajectory₂ h₁ h₂ hinitial t ht
  have hdiff : A.IsForwardStrongSolution fun s : ℝ ↦ trajectory₁ s - trajectory₂ s :=
    A.isForwardStrongSolution_sub h₁ h₂
  have hzero : ‖A.embedding (trajectory₁ 0 - trajectory₂ 0)‖ = 0 := by
    rw [map_sub, hinitial, sub_self, norm_zero]
  have hbound : ‖A.embedding (trajectory₁ t - trajectory₂ t)‖ ≤
      Real.exp (M * t) * ‖A.embedding (trajectory₁ 0 - trajectory₂ 0)‖ :=
    A.norm_embedding_le_exp_of_isForwardStrongSolution M hM hdiff ht
  rw [hzero, mul_zero] at hbound
  have hvanish : A.embedding (trajectory₁ t - trajectory₂ t) = 0 :=
    norm_le_zero_iff.mp hbound
  rw [map_sub, sub_eq_zero] at hvanish
  exact hvanish

end DomainOperator

/-! ## The reduced fixed-sector induction operator -/

/-- **Half-plane numerical range of the reduced induction operator.**  For a
divergence-free transverse velocity and a nonnegative diffusivity, the real part of the
energy pairing of the reduced induction action is bounded by `‖∇⊥ u‖_∞ ‖b‖²`, uniformly
in the axial index `K`.

This is the exact energy identity `re_inner_reducedInductionAction_eq` — transport is
skew and contributes nothing, diffusion contributes `-ε (‖∇⊥ b‖² + (2πK)² ‖b‖²) ≤ 0` —
combined with the stretching estimate `re_inner_reducedInductionStretching_le`.  It is
the operator form of the paper's energy competition `eq:energy-competition`. -/
theorem re_inner_reducedInductionAction_le
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (hε : 0 ≤ ε) (K : ℤ) (b : TransverseC3H2) :
    (inner ℂ (transverseH2Embedding b) (reducedInductionAction u ε K b)).re ≤
      ‖transverseStretchingCoefficient u‖ * ‖transverseH2Embedding b‖ ^ 2 := by
  have hreal := re_inner_reducedInductionAction_eq u hu ε K b
  have hstretch := re_inner_reducedInductionStretching_le u b
  have haxial : (0 : ℝ) ≤ (2 * Real.pi * (K : ℝ)) ^ 2 := sq_nonneg _
  have hgrad := reducedTransverseGradientEnergy_nonneg b
  have hnorm : (0 : ℝ) ≤ ‖transverseH2Embedding b‖ ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hε hgrad, mul_nonneg (mul_nonneg hε haxial) hnorm]

/-- **Uniqueness of forward strong solutions of the reduced induction equation.**  For every
divergence-free transverse velocity, every nonnegative diffusivity and every axial index, two
forward strong solutions of `reducedInductionOperator u ε K` with the same initial `L²` state
agree in `L²` at every nonnegative time.

This needs no further hypothesis: the half-plane numerical-range bound
`re_inner_reducedInductionAction_le` supplies the hypothesis of
`DomainOperator.forwardStrongSolutionsUnique_of_re_inner_le` with
`M = ‖transverseStretchingCoefficient u‖`.  It discharges the
`ForwardStrongSolutionsUnique` hypothesis of
`FastDynamo/Dynamics/StronglyContinuousSemigroup.lean` for the fixed-sector operator, and is
the uniqueness half of an energy well-posedness statement (see the module
docstring). -/
theorem reducedInductionOperator_forwardStrongSolutionsUnique
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (hε : 0 ≤ ε) (K : ℤ) :
    (reducedInductionOperator u ε K).ForwardStrongSolutionsUnique :=
  DomainOperator.forwardStrongSolutionsUnique_of_re_inner_le _
    ‖transverseStretchingCoefficient u‖
    (fun b ↦ re_inner_reducedInductionAction_le u hu ε hε K b)

/-- **A priori energy bound for the reduced induction equation.**  Every forward strong
solution of `reducedInductionOperator u ε K` obeys
`‖B(t)‖ ≤ e^{‖∇⊥ u‖_∞ t} ‖B(0)‖` in `L²` for `t ≥ 0`, with a growth ceiling independent
of the diffusivity `ε` and of the axial index `K`.

This is the paper's `eq:energy-competition` in integrated form; it is
the companion of the growth floor produced by the spectral half of Theorem 1.2.  Fed to
`DomainOperator.strongSolutionGrowthFloor_le_of_norm_le` it caps the growth floor of the
reduced operator; see `FastDynamo/Dynamics/MainGrowthFloor.lean`. -/
theorem reducedInductionOperator_norm_embedding_le_exp
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (hε : 0 ≤ ε) (K : ℤ) {trajectory : ℝ → TransverseC3H2}
    (h : (reducedInductionOperator u ε K).IsForwardStrongSolution trajectory)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖transverseH2Embedding (trajectory t)‖ ≤
      Real.exp (‖transverseStretchingCoefficient u‖ * t) *
        ‖transverseH2Embedding (trajectory 0)‖ :=
  DomainOperator.norm_embedding_le_exp_of_isForwardStrongSolution _
    ‖transverseStretchingCoefficient u‖
    (fun b ↦ re_inner_reducedInductionAction_le u hu ε hε K b) h ht

end

end FastDynamo
