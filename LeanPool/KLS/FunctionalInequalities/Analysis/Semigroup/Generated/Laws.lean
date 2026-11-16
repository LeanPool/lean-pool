/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Exponential.Limit
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Yosida.Laws

/-!
# Semigroup laws for the strong Yosida limit

For a closed densely defined operator `T` between real Hilbert spaces,
`Generated.apply T hT hd t` is the strong limit of the exponentials approximating `exp (-t T†T)`.
On nonnegative times it is linear, contractive, symmetric and strongly continuous;
`zero_time` and `add_time` give the identity and semigroup laws.

`Generated.operator` packages the limit as a bounded linear operator.
Its norm bound and composition law are `norm_operator_le_one` and `operator_add_time`.
The generator and Markov properties are proved in `Generated/Generator.lean`
and `Generated/Markov.lean`.
-/

@[expose] public section

noncomputable section

open InnerProductSpace

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]

/-! ### Two real-analysis squeezes

Both are used to turn "smaller than every `ε > 0`" into an equality. -/

/-- A nonnegative real that is smaller than every positive real is `0`. -/
theorem eq_zero_of_forall_pos_lt {a : ℝ} (ha : 0 ≤ a) (h : ∀ ε : ℝ, 0 < ε → a < ε) : a = 0 :=
  le_antisymm (le_of_forall_pos_le_add fun ε hε => by simpa using (h ε hε).le) ha

/-- A nonnegative real bounded by `ε * C` for every `ε > 0` (with `C` a fixed real, of any sign)
is `0`. -/
theorem eq_zero_of_forall_le_mul {a C : ℝ} (ha : 0 ≤ a) (h : ∀ ε : ℝ, 0 < ε → a ≤ ε * C) :
    a = 0 := by
  refine le_antisymm (le_of_forall_pos_le_add fun η hη => ?_) ha
  have hC : (0 : ℝ) < |C| + 1 := by positivity
  have h1 := h (η / (|C| + 1)) (by positivity)
  have h2 : η / (|C| + 1) * C ≤ η := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hC]
    exact mul_le_mul_of_nonneg_left (by linarith [le_abs_self C]) hη.le
  linarith

/-! ### Operator-level ingredients -/

/-- `exp (-(t + u) • A) f = exp (-t • A) (exp (-u • A) f)` for a bounded operator `A`: the two
scalar multiples of `A` commute, so `NormedSpace.exp` turns the sum into a product. -/
theorem exp_neg_add_smul_apply (A : H₀ →L[ℝ] H₀) (t u : ℝ) (f : H₀) :
    NormedSpace.exp (-(t + u) • A) f
      = NormedSpace.exp (-t • A) (NormedSpace.exp (-u • A) f) := by
  have hc : Commute (-t • A) (-u • A) := ((Commute.refl A).smul_left (-t)).smul_right (-u)
  have hsplit : NormedSpace.exp (-t • A + -u • A)
      = NormedSpace.exp (-t • A) * NormedSpace.exp (-u • A) :=
    NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hc
      ((NormedSpace.expSeries_radius_eq_top ℝ (H₀ →L[ℝ] H₀)).symm ▸ edist_lt_top _ _)
      ((NormedSpace.expSeries_radius_eq_top ℝ (H₀ →L[ℝ] H₀)).symm ▸ edist_lt_top _ _)
  rw [show -(t + u) • A = -t • A + -u • A by rw [← add_smul]; ring_nf, hsplit]
  rfl

/-- `‖exp (-t • L_s) f - f‖ ≤ t ‖L_s f‖`: this is `norm_exp_neg_smul_sub_le` with the second
operator taken to be `0`, whose exponential is the identity. -/
theorem norm_exp_neg_smul_yosida_sub_le (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s)
    {t : ℝ} (ht : 0 ≤ t) (f : H₀) :
    ‖NormedSpace.exp (-t • yosida T hT hs) f - f‖ ≤ t * ‖yosida T hT hs f‖ := by
  have h := norm_exp_neg_smul_sub_le (yosida T hT hs) 0 (yosida_nonneg T hT hs) (by simp)
    (by simp) ht f
  rwa [smul_zero, NormedSpace.exp_zero, zero_apply, sub_zero,
    show (1 : H₀ →L[ℝ] H₀) f = f from rfl] at h

/-! ### Laws of the generated semigroup -/

namespace Generated

/-- **Uniqueness of the limit**: the limit defining `P_t` is unique.  If `exp (-t • L_s) f → g`
as `s ↓ 0`, then
`g = P_t f`.  The triangle inequality against `Generated.yosida_limit` gives `‖g - P_t f‖ < ε` for
every `ε > 0`. -/
theorem eq_apply_of_tendsto (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {t : ℝ} (ht : 0 ≤ t) (f g : H₀)
    (hg : ∀ {ε : ℝ}, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ} (hs : 0 < s), s < δ →
      ‖NormedSpace.exp (-t • yosida T hT hs) f - g‖ < ε) :
    g = Generated.apply T hT hd t f := by
  have key : ∀ ε : ℝ, 0 < ε → ‖g - Generated.apply T hT hd t f‖ < ε := by
    intro ε hε
    obtain ⟨δ₁, hδ₁, h₁⟩ := hg (half_pos hε)
    obtain ⟨δ₂, hδ₂, h₂⟩ := Generated.yosida_limit T hT hd ht f (half_pos hε)
    have hmpos : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
    have hs : 0 < min δ₁ δ₂ / 2 := by linarith
    have hsm : min δ₁ δ₂ / 2 < min δ₁ δ₂ := by linarith
    have e1 := h₁ hs (lt_of_lt_of_le hsm (min_le_left _ _))
    have e2 := h₂ hs (lt_of_lt_of_le hsm (min_le_right _ _))
    have hrw : g - Generated.apply T hT hd t f =
        (NormedSpace.exp (-t • yosida T hT hs) f - Generated.apply T hT hd t f)
          - (NormedSpace.exp (-t • yosida T hT hs) f - g) := by abel
    have htri : ‖g - Generated.apply T hT hd t f‖
        ≤ ‖NormedSpace.exp (-t • yosida T hT hs) f - Generated.apply T hT hd t f‖
          + ‖NormedSpace.exp (-t • yosida T hT hs) f - g‖ := by
      rw [hrw]; exact norm_sub_le _ _
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (eq_zero_of_forall_pos_lt (norm_nonneg _) key))

/--
**contraction**: `P_t` is a contraction, `‖P_t f‖ ≤ ‖f‖`.  The exponential bound
(`norm_exp_neg_smul_apply_le` applied
to the nonnegative operator `L_s`) passes to the limit. -/
theorem norm_apply_le (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
    {t : ℝ} (ht : 0 ≤ t) (f : H₀) : ‖Generated.apply T hT hd t f‖ ≤ ‖f‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ, h⟩ := Generated.yosida_limit T hT hd ht f hε
  have hs : 0 < δ / 2 := by linarith
  have e1 := h hs (by linarith : δ / 2 < δ)
  have e2 := norm_exp_neg_smul_apply_le (yosida T hT hs) (yosida_nonneg T hT hs) ht f
  have e3 :=
    norm_sub_norm_le (Generated.apply T hT hd t f) (NormedSpace.exp (-t • yosida T hT hs) f)
  rw [norm_sub_rev] at e3
  linarith

/-- **Linearity**: `P_t` is linear, `P_t (a • f + g) = a • P_t f + P_t g`.  The candidate
`a • P_t f + P_t g` satisfies the defining convergence, so `Generated.eq_apply_of_tendsto`
identifies it. -/
theorem map_smul_add (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {t : ℝ} (ht : 0 ≤ t) (a : ℝ) (f g : H₀) :
    Generated.apply T hT hd t (a • f + g) =
      a • Generated.apply T hT hd t f + Generated.apply T hT hd t g := by
  refine (Generated.eq_apply_of_tendsto T hT hd ht (a • f + g) _ ?_).symm
  intro ε hε
  have hA : (0 : ℝ) < |a| + 1 := by positivity
  have hpos : 0 < ε / (2 * (|a| + 1)) := by positivity
  obtain ⟨δ₁, hδ₁, h₁⟩ := Generated.yosida_limit T hT hd ht f hpos
  obtain ⟨δ₂, hδ₂, h₂⟩ := Generated.yosida_limit T hT hd ht g (half_pos hε)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro s hs hsm
  have e1 := h₁ hs (lt_of_lt_of_le hsm (min_le_left _ _))
  have e2 := h₂ hs (lt_of_lt_of_le hsm (min_le_right _ _))
  have hrw : NormedSpace.exp (-t • yosida T hT hs) (a • f + g)
        - (a • Generated.apply T hT hd t f + Generated.apply T hT hd t g)
      = a • (NormedSpace.exp (-t • yosida T hT hs) f - Generated.apply T hT hd t f)
        + (NormedSpace.exp (-t • yosida T hT hs) g - Generated.apply T hT hd t g) := by
    rw [map_add, map_smul]; module
  have hsplit : ‖NormedSpace.exp (-t • yosida T hT hs) (a • f + g)
        - (a • Generated.apply T hT hd t f + Generated.apply T hT hd t g)‖
      ≤ |a| * ‖NormedSpace.exp (-t • yosida T hT hs) f - Generated.apply T hT hd t f‖
        + ‖NormedSpace.exp (-t • yosida T hT hs) g - Generated.apply T hT hd t g‖ := by
    rw [hrw]
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_smul, Real.norm_eq_abs]
  have hbound : |a| * ‖NormedSpace.exp (-t • yosida T hT hs) f - Generated.apply T hT hd t f‖
      ≤ |a| * (ε / (2 * (|a| + 1))) :=
    mul_le_mul_of_nonneg_left e1.le (abs_nonneg a)
  have hfield : (|a| + 1) * (ε / (2 * (|a| + 1))) = ε / 2 := by
    field_simp
  have hmono : |a| * (ε / (2 * (|a| + 1))) ≤ (|a| + 1) * (ε / (2 * (|a| + 1))) :=
    mul_le_mul_of_nonneg_right (by linarith) hpos.le
  linarith

/-- `P_t` respects differences: `P_t (f - g) = P_t f - P_t g`.  This is
`Generated.map_smul_add` with `a = -1`. -/
theorem map_sub (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {t : ℝ} (ht : 0 ≤ t) (f g : H₀) :
    Generated.apply T hT hd t (f - g) =
      Generated.apply T hT hd t f - Generated.apply T hT hd t g := by
  have h := Generated.map_smul_add T hT hd ht (-1) g f
  rw [show (-1 : ℝ) • g + f = f - g by module] at h
  rw [h]; module

/-- `P_t 0 = 0`, from `Generated.map_sub` with `f = g`. -/
theorem map_zero (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {t : ℝ} (ht : 0 ≤ t) :
    Generated.apply T hT hd t (0 : H₀) = 0 := by
  have h := Generated.map_sub T hT hd ht (0 : H₀) 0
  simpa using h

/-- `P_t (a • f) = a • P_t f`, from `Generated.map_smul_add` with `g = 0`. -/
theorem map_smul (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {t : ℝ} (ht : 0 ≤ t) (a : ℝ) (f : H₀) :
    Generated.apply T hT hd t (a • f) = a • Generated.apply T hT hd t f := by
  have h := Generated.map_smul_add T hT hd ht a f 0
  rwa [add_zero, Generated.map_zero T hT hd ht, add_zero] at h

/-- `P_t (f + g) = P_t f + P_t g`, from `Generated.map_smul_add` with `a = 1`. -/
theorem map_add (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {t : ℝ} (ht : 0 ≤ t) (f g : H₀) :
    Generated.apply T hT hd t (f + g) =
      Generated.apply T hT hd t f + Generated.apply T hT hd t g := by
  have h := Generated.map_smul_add T hT hd ht 1 f g
  rwa [one_smul, one_smul] at h

/-- `P_t` packaged as a `ContinuousLinearMap` of operator norm at most `1`, using linearity and
contraction.
`Generated.operator_apply` identifies it with `Generated.apply`. -/
def operator (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) {t : ℝ}
    (ht : 0 ≤ t) : H₀ →L[ℝ] H₀ :=
  LinearMap.mkContinuous
    { toFun := Generated.apply T hT hd t
      map_add' := Generated.map_add T hT hd ht
      map_smul' := fun a f => Generated.map_smul T hT hd ht a f }
    1 fun f => by simpa using Generated.norm_apply_le T hT hd ht f

/-- `Generated.operator` applies as `Generated.apply`. -/
@[simp]
theorem operator_apply (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
    {t : ℝ} (ht : 0 ≤ t) (f : H₀) :
    Generated.operator T hT hd ht f = Generated.apply T hT hd t f := rfl

end Generated

/-- `exp (-t • L_s)` is self-adjoint: `L_s` is symmetric (`yosida_symm`), hence self-adjoint as a
bounded operator, hence so is `-t • L_s` and therefore its exponential. -/
theorem isSelfAdjoint_exp_neg_smul_yosida (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ}
    (hs : 0 < s) (t : ℝ) : IsSelfAdjoint (NormedSpace.exp (-t • yosida T hT hs)) :=
  (IsSelfAdjoint.smul (show IsSelfAdjoint (-t) from star_trivial _)
    (LinearMap.IsSymmetric.isSelfAdjoint (yosida_symm T hT hs))).exp

/-- `⟪exp (-t • L_s) f, g⟫ = ⟪f, exp (-t • L_s) g⟫`, the pointwise form of
`isSelfAdjoint_exp_neg_smul_yosida`. -/
theorem inner_exp_neg_smul_yosida (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s)
    (t : ℝ) (f g : H₀) :
    ⟪NormedSpace.exp (-t • yosida T hT hs) f, g⟫
      = ⟪f, NormedSpace.exp (-t • yosida T hT hs) g⟫ := by
  have h := isSelfAdjoint_exp_neg_smul_yosida T hT hs t
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at h
  conv_lhs => rw [← h]
  rw [ContinuousLinearMap.adjoint_inner_left]

namespace Generated

/--
**symmetry**: `P_t` is symmetric, `⟪P_t f, g⟫ = ⟪f, P_t g⟫`.  Each `exp (-t • L_s)` is symmetric,
and the defect `⟪P_t f, g⟫ - ⟪f, P_t g⟫` is bounded by `ε * (‖g‖ + ‖f‖)` for every `ε > 0`. -/
theorem symmetric (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) {t : ℝ}
    (ht : 0 ≤ t) (f g : H₀) :
    ⟪Generated.apply T hT hd t f, g⟫ = ⟪f, Generated.apply T hT hd t g⟫ := by
  have key :
    ∀ ε : ℝ,
      0 < ε →
        |⟪Generated.apply T hT hd t f, g⟫ - ⟪f, Generated.apply T hT hd t g⟫| ≤
          ε * (‖g‖ + ‖f‖) := by
    intro ε hε
    obtain ⟨δ₁, hδ₁, h₁⟩ := Generated.yosida_limit T hT hd ht f hε
    obtain ⟨δ₂, hδ₂, h₂⟩ := Generated.yosida_limit T hT hd ht g hε
    have hmpos : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
    have hs : 0 < min δ₁ δ₂ / 2 := by linarith
    have hsm : min δ₁ δ₂ / 2 < min δ₁ δ₂ := by linarith
    have e1 := h₁ hs (lt_of_lt_of_le hsm (min_le_left _ _))
    have e2 := h₂ hs (lt_of_lt_of_le hsm (min_le_right _ _))
    have hdec :
      ⟪Generated.apply T hT hd t f, g⟫ - ⟪f, Generated.apply T hT hd t g⟫ =
        ⟪Generated.apply T hT hd t f - NormedSpace.exp (-t • yosida T hT hs) f, g⟫ +
          ⟪f, NormedSpace.exp (-t • yosida T hT hs) g - Generated.apply T hT hd t g⟫ := by
      rw [inner_sub_left, inner_sub_right, inner_exp_neg_smul_yosida T hT hs t f g]
      ring
    have b1 :
      |⟪Generated.apply T hT hd t f - NormedSpace.exp (-t • yosida T hT hs) f, g⟫| ≤
        ‖Generated.apply T hT hd t f - NormedSpace.exp (-t • yosida T hT hs) f‖ * ‖g‖ :=
      abs_real_inner_le_norm _ _
    have b2 :
      |⟪f, NormedSpace.exp (-t • yosida T hT hs) g - Generated.apply T hT hd t g⟫| ≤
        ‖f‖ * ‖NormedSpace.exp (-t • yosida T hT hs) g - Generated.apply T hT hd t g‖ :=
      abs_real_inner_le_norm _ _
    have hrev :
      ‖Generated.apply T hT hd t f - NormedSpace.exp (-t • yosida T hT hs) f‖ =
        ‖NormedSpace.exp (-t • yosida T hT hs) f - Generated.apply T hT hd t f‖ :=
      norm_sub_rev _ _
    have hm1 :
      ‖Generated.apply T hT hd t f - NormedSpace.exp (-t • yosida T hT hs) f‖ * ‖g‖ ≤ ε * ‖g‖ := by
      rw [hrev]; exact mul_le_mul_of_nonneg_right e1.le (norm_nonneg g)
    have hm2 :
      ‖f‖ * ‖NormedSpace.exp (-t • yosida T hT hs) g - Generated.apply T hT hd t g‖ ≤ ‖f‖ * ε :=
      mul_le_mul_of_nonneg_left e2.le (norm_nonneg f)
    have habs :=
      abs_add_le (⟪Generated.apply T hT hd t f - NormedSpace.exp (-t • yosida T hT hs) f, g⟫)
        (⟪f, NormedSpace.exp (-t • yosida T hT hs) g - Generated.apply T hT hd t g⟫)
    rw [hdec]
    nlinarith
  exact sub_eq_zero.mp (abs_eq_zero.mp (eq_zero_of_forall_le_mul (abs_nonneg _) key))

/-- **Identity at time zero**: `P_0 = 1`.  `exp (-0 • L_s) = 1`, so the constant family `f`
converges to `f`; `Generated.eq_apply_of_tendsto` identifies the limit.  No hypothesis `0 ≤ t`
occurs here. -/
theorem zero_time (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) (f : H₀) : Generated.apply T hT hd 0 f = f := by
  refine (Generated.eq_apply_of_tendsto T hT hd le_rfl f f ?_).symm
  intro ε hε
  refine ⟨1, one_pos, ?_⟩
  intro s hs _
  have hid : NormedSpace.exp (-(0 : ℝ) • yosida T hT hs) f = f := by
    rw [neg_zero, zero_smul, NormedSpace.exp_zero]
    rfl
  rw [hid, sub_self, norm_zero]
  exact hε

/-- **The semigroup law** `P_{t + u} = P_t ∘ P_u`.  `exp (-(t+u) • L_s)` factors as
`exp (-t • L_s) ∘ exp (-u • L_s)` (`exp_neg_add_smul_apply`); the error splits as
`‖exp (-u • L_s) f - P_u f‖` (after the contraction bound `norm_exp_neg_smul_apply_le`) plus
`‖exp (-t • L_s) (P_u f) - P_t (P_u f)‖`, and `Generated.eq_apply_of_tendsto` identifies the
limit. -/
theorem add_time (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) (f : H₀) :
    Generated.apply T hT hd (t + u) f =
      Generated.apply T hT hd t (Generated.apply T hT hd u f) := by
  refine (Generated.eq_apply_of_tendsto T hT hd (by linarith) f _ ?_).symm
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := Generated.yosida_limit T hT hd hu f (half_pos hε)
  obtain ⟨δ₂, hδ₂, h₂⟩ :=
    Generated.yosida_limit T hT hd ht (Generated.apply T hT hd u f) (half_pos hε)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro s hs hsm
  have e1 := h₁ hs (lt_of_lt_of_le hsm (min_le_left _ _))
  have e2 := h₂ hs (lt_of_lt_of_le hsm (min_le_right _ _))
  rw [exp_neg_add_smul_apply]
  have hcontr : ‖NormedSpace.exp (-t • yosida T hT hs)
        (NormedSpace.exp (-u • yosida T hT hs) f)
      - NormedSpace.exp (-t • yosida T hT hs) (Generated.apply T hT hd u f)‖
      ≤ ‖NormedSpace.exp (-u • yosida T hT hs) f - Generated.apply T hT hd u f‖ := by
    rw [← _root_.map_sub]
    exact norm_exp_neg_smul_apply_le _ (yosida_nonneg T hT hs) ht _
  have hrw : NormedSpace.exp (-t • yosida T hT hs) (NormedSpace.exp (-u • yosida T hT hs) f)
        - Generated.apply T hT hd t (Generated.apply T hT hd u f)
      = (NormedSpace.exp (-t • yosida T hT hs) (NormedSpace.exp (-u • yosida T hT hs) f)
          - NormedSpace.exp (-t • yosida T hT hs) (Generated.apply T hT hd u f))
        + (NormedSpace.exp (-t • yosida T hT hs) (Generated.apply T hT hd u f)
          - Generated.apply T hT hd t (Generated.apply T hT hd u f)) := by abel
  have htri : ‖NormedSpace.exp (-t • yosida T hT hs)
        (NormedSpace.exp (-u • yosida T hT hs) f)
      - Generated.apply T hT hd t (Generated.apply T hT hd u f)‖
      ≤ ‖NormedSpace.exp (-t • yosida T hT hs) (NormedSpace.exp (-u • yosida T hT hs) f)
          - NormedSpace.exp (-t • yosida T hT hs) (Generated.apply T hT hd u f)‖
        + ‖NormedSpace.exp (-t • yosida T hT hs) (Generated.apply T hT hd u f)
          - Generated.apply T hT hd t (Generated.apply T hT hd u f)‖ := by
    rw [hrw]; exact norm_add_le _ _
  linarith

/-- On `D(T†T)` the semigroup moves at a bounded speed: `‖P_t f - f‖ ≤ t (‖T†T f‖ + 1)`.
`norm_exp_neg_smul_sub_le` with `B = 0` gives `‖exp (-t • L_s) f - f‖ ≤ t ‖L_s f‖`, and
`exists_delta_norm_yosida_sub_adjointComp_lt` with `ε = 1` gives
`‖L_s f‖ ≤ ‖T†T f‖ + 1` for `s` small; then let `s ↓ 0`. -/
theorem displacement_le (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t) :
    ‖Generated.apply T hT hd t (f : H₀) - (f : H₀)‖ ≤ t * (‖adjointComp T f‖ + 1) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_delta_norm_yosida_sub_adjointComp_lt T hT hd f one_pos
  obtain ⟨δ₂, hδ₂, h₂⟩ := Generated.yosida_limit T hT hd ht (f : H₀) hε
  have hmpos : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hs : 0 < min δ₁ δ₂ / 2 := by linarith
  have hsm : min δ₁ δ₂ / 2 < min δ₁ δ₂ := by linarith
  have e1 := h₁ hs (lt_of_lt_of_le hsm (min_le_left _ _))
  have e2 := h₂ hs (lt_of_lt_of_le hsm (min_le_right _ _))
  have e3 := norm_exp_neg_smul_yosida_sub_le T hT hs ht (f : H₀)
  have e4 : ‖yosida T hT hs (f : H₀)‖ ≤ ‖adjointComp T f‖ + 1 := by
    have h := norm_sub_norm_le (yosida T hT hs (f : H₀)) (adjointComp T f)
    linarith
  have e5 : t * ‖yosida T hT hs (f : H₀)‖ ≤ t * (‖adjointComp T f‖ + 1) :=
    mul_le_mul_of_nonneg_left e4 ht
  have hrw : Generated.apply T hT hd t (f : H₀) - (f : H₀)
      = (Generated.apply T hT hd t (f : H₀)
          - NormedSpace.exp (-t • yosida T hT hs) (f : H₀))
        + (NormedSpace.exp (-t • yosida T hT hs) (f : H₀) - (f : H₀)) := by abel
  have htri : ‖Generated.apply T hT hd t (f : H₀) - (f : H₀)‖
      ≤ ‖Generated.apply T hT hd t (f : H₀)
          - NormedSpace.exp (-t • yosida T hT hs) (f : H₀)‖
        + ‖NormedSpace.exp (-t • yosida T hT hs) (f : H₀) - (f : H₀)‖ := by
    rw [hrw]; exact norm_add_le _ _
  have hrev : ‖Generated.apply T hT hd t (f : H₀)
      - NormedSpace.exp (-t • yosida T hT hs) (f : H₀)‖
      = ‖NormedSpace.exp (-t • yosida T hT hs) (f : H₀) - Generated.apply T hT hd t (f : H₀)‖ :=
    norm_sub_rev _ _
  rw [hrev] at htri
  linarith

/-- **Strong continuity at `0`.**  For `f ∈ D(T†T)` this is
`Generated.displacement_le`; a general `f` is approximated within `ε/3` by some
`g ∈ D(T†T)` (`dense_adjointComp_domain`), and the contraction
`Generated.norm_apply_le` together with linearity transfers the bound. -/
theorem continuous_at_zero (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) (f : H₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 ≤ t → t < δ → ‖Generated.apply T hT hd t f - f‖ < ε := by
  obtain ⟨b, hb, hlt⟩ := Metric.mem_closure_iff.mp (dense_adjointComp_domain T hT hd f) (ε / 3)
    (by positivity)
  have hfb : ‖f - b‖ < ε / 3 := by simpa [dist_eq_norm] using hlt
  set g : (adjointComp T).domain := ⟨b, hb⟩ with hg
  have hgb : (g : H₀) = b := rfl
  have hC : (0 : ℝ) < ‖adjointComp T g‖ + 1 := by positivity
  refine ⟨ε / (3 * (‖adjointComp T g‖ + 1)), by positivity, ?_⟩
  intro t ht htδ
  have h1 : ‖Generated.apply T hT hd t b - b‖ ≤ t * (‖adjointComp T g‖ + 1) := by
    have h := Generated.displacement_le T hT hd g ht
    rwa [hgb] at h
  have h2 : t * (‖adjointComp T g‖ + 1) < ε / 3 := by
    rw [← lt_div_iff₀ hC]
    calc t < ε / (3 * (‖adjointComp T g‖ + 1)) := htδ
      _ = ε / 3 / (‖adjointComp T g‖ + 1) := by rw [div_div]
  have h3 : ‖Generated.apply T hT hd t f - Generated.apply T hT hd t b‖ ≤ ‖f - b‖ := by
    rw [← Generated.map_sub T hT hd ht]
    exact Generated.norm_apply_le T hT hd ht _
  have hrw : Generated.apply T hT hd t f - f
      = (Generated.apply T hT hd t f - Generated.apply T hT hd t b)
        + (Generated.apply T hT hd t b - b) + (b - f) := by abel
  have htri : ‖Generated.apply T hT hd t f - f‖
      ≤ ‖Generated.apply T hT hd t f - Generated.apply T hT hd t b‖
        + ‖Generated.apply T hT hd t b - b‖ + ‖b - f‖ := by
    rw [hrw]
    exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
  have hrev : ‖b - f‖ = ‖f - b‖ := norm_sub_rev _ _
  rw [hrev] at htri
  linarith

/-- **Strong continuity**: `t ↦ P_t f` is continuous on `[0, ∞)`.  For `t₀ ≤ t` the semigroup
law gives `P_t f - P_{t₀} f = P_{t₀} (P_{t - t₀} f - f)`, which the contraction
`Generated.norm_apply_le` bounds by `‖P_{t - t₀} f - f‖`; for `t ≤ t₀` exchange the roles.  Then
apply `Generated.continuous_at_zero`. -/
theorem continuousOn (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) (f : H₀) :
    ContinuousOn (fun t : ℝ => Generated.apply T hT hd t f) (Set.Ici 0) := by
  rw [Metric.continuousOn_iff]
  intro t₀ ht₀ ε hε
  obtain ⟨δ, hδ, h⟩ := Generated.continuous_at_zero T hT hd f hε
  refine ⟨δ, hδ, ?_⟩
  intro t ht hdist
  simp only [Set.mem_Ici] at ht ht₀
  rw [Real.dist_eq] at hdist
  obtain ⟨hlow, hhigh⟩ := abs_lt.mp hdist
  simp only [dist_eq_norm]
  rcases le_total t₀ t with hle | hle
  · have hsum : t₀ + (t - t₀) = t := by ring
    have hsplit : Generated.apply T hT hd t f
        = Generated.apply T hT hd t₀ (Generated.apply T hT hd (t - t₀) f) := by
      rw [← Generated.add_time T hT hd ht₀ (by linarith : (0 : ℝ) ≤ t - t₀), hsum]
    rw [hsplit, ← Generated.map_sub T hT hd ht₀]
    exact lt_of_le_of_lt (Generated.norm_apply_le T hT hd ht₀ _)
      (h (t - t₀) (by linarith) (by linarith))
  · have hsum : t + (t₀ - t) = t₀ := by ring
    have hsplit : Generated.apply T hT hd t₀ f
        = Generated.apply T hT hd t (Generated.apply T hT hd (t₀ - t) f) := by
      rw [← Generated.add_time T hT hd ht (by linarith : (0 : ℝ) ≤ t₀ - t), hsum]
    rw [hsplit, ← Generated.map_sub T hT hd ht]
    refine lt_of_le_of_lt (Generated.norm_apply_le T hT hd ht _) ?_
    rw [norm_sub_rev]
    exact h (t₀ - t) (by linarith) (by linarith)

end Generated

end FunctionalInequalities.Analysis.Semigroup

namespace FunctionalInequalities.Analysis.Semigroup.Generated

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]

/-- The generated bounded operator is a contraction in operator norm. -/
theorem norm_operator_le_one (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {t : ℝ} (ht : 0 ≤ t) :
    ‖operator T hT hd ht‖ ≤ 1 := by
  apply (operator T hT hd ht).opNorm_le_bound (by norm_num)
  intro f
  simpa only [operator_apply, one_mul] using norm_apply_le T hT hd ht f

/-- The semigroup law as an equality of bounded linear operators. -/
theorem operator_add_time (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    operator T hT hd (add_nonneg ht hu) = (operator T hT hd ht).comp (operator T hT hd hu) := by
  ext f
  simp only [operator_apply, ContinuousLinearMap.comp_apply]
  exact add_time T hT hd ht hu f

end FunctionalInequalities.Analysis.Semigroup.Generated
