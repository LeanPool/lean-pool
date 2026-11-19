/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.PicardSpaceDiscrete
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The Bielecki β-weighted pseudo-edist between bounded processes

Pointwise Euclidean Minkowski on `Fin n → ℝ` lifts, through `L²`-Minkowski over `Ω`,
multiplication by the weight `exp (-β * t)` and sup-subadditivity over `t ∈ [0, T]`, to
subadditivity of the Bielecki β-norm `bieleckiNorm β T X = ⨆ t ∈ [0, T], exp (-β * t) *
(E‖X t‖²)^(1/2)`. Evaluating that norm on the pointwise path difference of two
`SBoundedProcess`es gives `bieleckiEDist`, which vanishes on the diagonal and is symmetric;
two processes whose paths agree P-a.s. at every `t` are at Bielecki distance zero, so it is a
pseudo-edist rather than an edist.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

/-! ### Pointwise Euclidean Minkowski on `Fin n → ℝ`

The Bielecki β-norm has the inner part `(∑ i, ‖X t ω i‖₊²)^(1/2)` which
is the **Euclidean** norm of `X t ω : Fin n → ℝ` (NOT the sup-norm that
Mathlib's default `Pi.instNorm` provides). The triangle inequality
requires `(∑ i, (a_i + b_i)²)^(1/2) ≤ (∑ i, a_i²)^(1/2) + (∑ i, b_i²)^(1/2)`,
which is `NNReal.Lp_add_le` at `p = 2`. -/

/-- **Pointwise Euclidean Minkowski (ENNReal form).** For NNReal-valued
`a, b : Fin n → NNReal`,
  `(∑ i, ((a i + b i) : ℝ≥0∞)²)^(1/2) ≤ (∑ i, a i²)^(1/2) + (∑ i, b i²)^(1/2)`.

This is the cast-to-`ℝ≥0∞` version of `NNReal.Lp_add_le` at `p = 2`. -/
lemma sum_sq_nnreal_add_le (n : ℕ) (a b : Fin n → NNReal) :
    (∑ i, ((a i + b i : NNReal) : ℝ≥0∞) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ (∑ i, ((a i : NNReal) : ℝ≥0∞) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        + (∑ i, ((b i : NNReal) : ℝ≥0∞) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
  ENNReal.Lp_add_le Finset.univ
    (fun i => ((a i : NNReal) : ℝ≥0∞)) (fun i => ((b i : NNReal) : ℝ≥0∞))
    (by norm_num : (1:ℝ) ≤ 2)

/-! ### Bielecki edist between `SBoundedProcess`es

Defined as `bieleckiNorm β T (X.X - Y.X)`. The path map difference is
just pointwise subtraction. -/

/-- **Pointwise difference of path maps.** Subtraction of two
`SBoundedProcess`'s underlying path maps is pointwise subtraction in
`Fin n → ℝ` at each `(t, ω)`. -/
@[simp] noncomputable def SBoundedProcess.pathDiff
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (X Y : SBoundedProcess (n := n) P ℱ T) : ℝ → Ω → (Fin n → ℝ) :=
  fun t ω => X.X t ω - Y.X t ω

/-- **The Bielecki β-weighted edist between two `SBoundedProcess`es.**

  `bieleckiEDist β T X Y := bieleckiNorm β T (X.X - Y.X)`,

i.e., `⨆_{t ∈ [0, T]} e^{-βt} · (E[‖X_t - Y_t‖²])^(1/2)`.

This is a **pseudo-edist** on `SBoundedProcess`: two structures with
P-a.s. equal paths at every `t` have `bieleckiEDist = 0` but are not
structurally equal as `SBoundedProcess`es. The genuine `MetricSpace` is
on the AE-quotient (`SBoundedProcess.AEQuot`); this pseudo-edist
descends to a genuine edist on the quotient. -/
noncomputable def bieleckiEDist
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (β T : ℝ) (X Y : SBoundedProcess (n := n) P ℱ T) : ℝ≥0∞ :=
  bieleckiNorm (P := P) β T (SBoundedProcess.pathDiff X Y)

/-! ### Pseudo-edist axioms for `bieleckiEDist` -/

@[simp] lemma bieleckiEDist_self
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {β T : ℝ}
    (X : SBoundedProcess (n := n) P ℱ T) : bieleckiEDist β T X X = 0 := by
  unfold bieleckiEDist bieleckiNorm SBoundedProcess.pathDiff
  -- The path-difference is identically zero, so the L² norm is zero.
  refine le_antisymm ?_ bot_le
  refine iSup_le (fun t => ?_)
  refine iSup_le (fun _ => ?_)
  -- The integrand is pointwise zero (`X.X t ω - X.X t ω = 0`), so the
  -- lintegral is zero, hence the (1/2)-rpow is zero, multiplying gives zero.
  have h_integrand_zero :
      (fun ω : Ω => ∑ i, ((‖(X.X t ω - X.X t ω) i‖₊ : ℝ≥0∞)) ^ 2)
        = fun _ => 0 := by
    funext ω
    simp
  rw [h_integrand_zero]
  simp

lemma bieleckiEDist_comm
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {β T : ℝ}
    (X Y : SBoundedProcess (n := n) P ℱ T) :
    bieleckiEDist β T X Y = bieleckiEDist β T Y X := by
  -- It suffices to show, per-`(t, ω, i)`, that the inner summands agree.
  -- ‖X t ω i - Y t ω i‖₊ = ‖-(Y t ω i - X t ω i)‖₊ = ‖Y t ω i - X t ω i‖₊
  -- (by `nnNorm_neg`).
  unfold bieleckiEDist bieleckiNorm SBoundedProcess.pathDiff
  -- The integrand pointwise equality:
  have h_pw : ∀ t : ℝ, ∀ ω : Ω,
      ∑ i, (‖(X.X t ω - Y.X t ω) i‖₊ : ℝ≥0∞) ^ 2
        = ∑ i, (‖(Y.X t ω - X.X t ω) i‖₊ : ℝ≥0∞) ^ 2 := by
    intro t ω
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 2
    rw [show (X.X t ω - Y.X t ω) i = -((Y.X t ω - X.X t ω) i) by
      simp [Pi.sub_apply]]
    exact nnNorm_neg _
  -- Lift to lintegral, then to (1/2)-rpow, then to multiplication, then to sup.
  refine iSup_congr (fun t => ?_)
  refine iSup_congr (fun _ => ?_)
  congr 1
  congr 1
  exact lintegral_congr_ae (Filter.Eventually.of_forall (fun ω => h_pw t ω))

/-! ### Bielecki triangle inequality

The key analytic content: `bieleckiNorm β T ((X - Y) + (Y - Z)) ≤
bieleckiNorm β T (X - Y) + bieleckiNorm β T (Y - Z)`.

This decomposes as:
1. Pointwise (in `t, ω`) Euclidean Minkowski (`sum_sq_nnreal_add_le`).
2. L² Minkowski over `ω` (`ENNReal.lintegral_Lp_add_le`).
3. Multiplication by `ENNReal.ofReal (Real.exp (-β·t))` preserves the
   inequality (left-multiplication by a non-negative constant in ℝ≥0∞).
4. Sup-subadditivity (`iSup₂_add_le`).
-/

/-- **Bielecki β-norm subadditivity.** For any two path maps `Y₁, Y₂`,
  `bieleckiNorm β T (Y₁ + Y₂) ≤ bieleckiNorm β T Y₁ + bieleckiNorm β T Y₂`.

The proof chains four steps:
* Pointwise (in `t, ω`) Euclidean Minkowski on `Fin n → ℝ`.
* L² Minkowski over `ω` (`ENNReal.lintegral_Lp_add_le`).
* Multiplication by the (constant in `ω`) Bielecki weight `e^{-βt}`.
* Sup-subadditivity over `t ∈ [0, T]`. -/
lemma bieleckiNorm_add_le
    {n : ℕ} {P : Measure Ω} (β T : ℝ)
    (Y₁ Y₂ : ℝ → Ω → (Fin n → ℝ))
    (hY₁_meas : ∀ t : ℝ, AEMeasurable
      (fun ω => (∑ i, (‖Y₁ t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)) P)
    (hY₂_meas : ∀ t : ℝ, AEMeasurable
      (fun ω => (∑ i, (‖Y₂ t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)) P) :
    bieleckiNorm (P := P) β T (fun t ω => Y₁ t ω + Y₂ t ω)
      ≤ bieleckiNorm (P := P) β T Y₁ + bieleckiNorm (P := P) β T Y₂ := by
  unfold bieleckiNorm
  refine iSup_le (fun t => ?_)
  refine iSup_le (fun ht => ?_)
  -- At fixed `t`, show the per-`t` term of the LHS is bounded by the
  -- sum of the per-`t` terms.
  -- Outline:
  --   ofReal(e^{-βt}) · (∫⁻ ω, ∑ i, ‖(Y₁+Y₂) t ω i‖²)^(1/2)
  -- ≤ ofReal(e^{-βt}) · ((∫⁻ ω, ∑ i, ‖Y₁ t ω i‖²)^(1/2)
  --                     + (∫⁻ ω, ∑ i, ‖Y₂ t ω i‖²)^(1/2))
  -- = ofReal(e^{-βt}) · (∫⁻ ω, ∑ i, ‖Y₁ t ω i‖²)^(1/2)
  --   + ofReal(e^{-βt}) · (∫⁻ ω, ∑ i, ‖Y₂ t ω i‖²)^(1/2)
  have h_step :
      (∫⁻ ω, ∑ i, (‖(Y₁ t ω + Y₂ t ω) i‖₊ : ℝ≥0∞) ^ 2 ∂P)
        ^ ((1 : ℝ) / 2)
        ≤ (∫⁻ ω, ∑ i, (‖Y₁ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
          + (∫⁻ ω, ∑ i, (‖Y₂ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2) := by
    -- Apply L² Minkowski via ENNReal.lintegral_Lp_add_le. To do so we
    -- need the pointwise (in ω) bound
    --   (∑ i, ‖(Y₁+Y₂) t ω i‖²)^(1/2) ≤ (∑ i, ‖Y₁ t ω i‖²)^(1/2)
    --                                  + (∑ i, ‖Y₂ t ω i‖²)^(1/2),
    -- after which the L² Minkowski on the RHS-as-a-function-of-ω
    -- closes the gap.
    have h_pw : ∀ ω,
        (∑ i, (‖(Y₁ t ω + Y₂ t ω) i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)
          ≤ (∑ i, (‖Y₁ t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)
            + (∑ i, (‖Y₂ t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2) := by
      intro ω
      -- Apply `sum_sq_nnreal_add_le` after bounding the L¹ summand pointwise.
      have h_pw_nn : ∀ i,
          (‖(Y₁ t ω + Y₂ t ω) i‖₊ : ℝ≥0∞)
            ≤ (‖Y₁ t ω i‖₊ : ℝ≥0∞) + (‖Y₂ t ω i‖₊ : ℝ≥0∞) := by
        intro i
        rw [show (Y₁ t ω + Y₂ t ω) i = Y₁ t ω i + Y₂ t ω i from rfl]
        exact_mod_cast nnNorm_add_le _ _
      -- Convert sums to the ℝ-power form, apply Minkowski, convert back.
      -- The Bielecki defn uses `^ (2 : ℕ)` but `sum_sq_nnreal_add_le`
      -- and `ENNReal.Lp_add_le` use `^ (2 : ℝ)`. Convert via
      -- `ENNReal.rpow_two = pow_two`.
      have h_conv : ∀ (x : ℝ≥0∞), x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
        intro x
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
      have h_step_A :
          (∑ i, (‖(Y₁ t ω + Y₂ t ω) i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)
            ≤ (∑ i,
                (((‖Y₁ t ω i‖₊ + ‖Y₂ t ω i‖₊ : NNReal) : ℝ≥0∞)) ^ (2 : ℕ))
                ^ ((1 : ℝ) / 2) := by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num : (0:ℝ) ≤ 1/2)
        refine Finset.sum_le_sum (fun i _ => ?_)
        push_cast
        gcongr
        exact h_pw_nn i
      -- Step B: apply the Euclidean Minkowski, converting ℕ ↔ ℝ exponents.
      refine le_trans h_step_A ?_
      have hMink :=
        sum_sq_nnreal_add_le n (fun i => ‖Y₁ t ω i‖₊) (fun i => ‖Y₂ t ω i‖₊)
      -- Convert all `^ (2 : ℝ)` to `^ (2 : ℕ)` to match the goal shape.
      have h_eq_a :
          (∑ i,
            (((‖Y₁ t ω i‖₊ + ‖Y₂ t ω i‖₊ : NNReal) : ℝ≥0∞)) ^ (2 : ℕ))
          = (∑ i,
            (((‖Y₁ t ω i‖₊ + ‖Y₂ t ω i‖₊ : NNReal) : ℝ≥0∞)) ^ (2 : ℝ))
            := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [h_conv]
      have h_eq_b : (∑ i, ((‖Y₁ t ω i‖₊ : NNReal) : ℝ≥0∞) ^ (2 : ℝ))
          = (∑ i, ((‖Y₁ t ω i‖₊ : ℝ≥0∞)) ^ 2) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [h_conv]
      have h_eq_c : (∑ i, ((‖Y₂ t ω i‖₊ : NNReal) : ℝ≥0∞) ^ (2 : ℝ))
          = (∑ i, ((‖Y₂ t ω i‖₊ : ℝ≥0∞)) ^ 2) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [h_conv]
      rw [h_eq_a]
      rw [h_eq_b, h_eq_c] at hMink
      exact hMink
    -- Now apply L² Minkowski (`ENNReal.lintegral_Lp_add_le`) to the
    -- functions `f₁ ω := (∑ i, ‖Y₁ t ω i‖²)^(1/2)` and similarly for `f₂`.
    -- The bound `h_pw` says the function `ω ↦ (∑ i, ‖(Y₁+Y₂) t ω i‖²)^(1/2)`
    -- is pointwise ≤ `f₁ ω + f₂ ω`. Then squaring is monotone on the
    -- pointwise-NN values, then integration is monotone, then taking
    -- the (1/2)-rpow of both sides preserves the inequality.
    -- Setup: define
    --   F  ω := (∑ i, ‖(Y₁+Y₂) t ω i‖²)^(1/2)
    --   f₁ ω := (∑ i, ‖Y₁ t ω i‖²)^(1/2)
    --   f₂ ω := (∑ i, ‖Y₂ t ω i‖²)^(1/2)
    -- Show:   (∫⁻ ω, F ω ^ 2)^(1/2) ≤ (∫⁻ ω, f₁ ω ^ 2)^(1/2)
    --                                  + (∫⁻ ω, f₂ ω ^ 2)^(1/2)
    -- via the chain  (∫⁻ ω, F ω ^ 2)^(1/2)
    --             ≤ (∫⁻ ω, (f₁ ω + f₂ ω) ^ 2)^(1/2)
    --               [monotonicity in F ≤ f₁+f₂]
    --             ≤ (∫⁻ ω, f₁²)^(1/2) + (∫⁻ ω, f₂²)^(1/2) [L² Minkowski]
    set F : Ω → ℝ≥0∞ :=
      fun ω => (∑ i,
        (‖(Y₁ t ω + Y₂ t ω) i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)
    set f₁ : Ω → ℝ≥0∞ :=
      fun ω => (∑ i, (‖Y₁ t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)
    set f₂ : Ω → ℝ≥0∞ :=
      fun ω => (∑ i, (‖Y₂ t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)
    -- The (∫⁻ ω, ∑ i, ‖·‖²) expressions equal (∫⁻ ω, F²),
    --   (∫⁻ ω, f₁²), (∫⁻ ω, f₂²)
    -- via the rpow-cancellation `((x)^(1/2))^2 = x`.
    have h_rpow_half_sq : ∀ (x : ℝ≥0∞), (x ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = x := by
      intro x
      rw [← ENNReal.rpow_mul]
      norm_num
    have h_F_sq :
        ∀ ω, F ω ^ (2 : ℝ) = ∑ i, (‖(Y₁ t ω + Y₂ t ω) i‖₊ : ℝ≥0∞) ^ 2 :=
      fun ω => h_rpow_half_sq _
    have h_f₁_sq : ∀ ω, f₁ ω ^ (2 : ℝ) = ∑ i, (‖Y₁ t ω i‖₊ : ℝ≥0∞) ^ 2 :=
      fun ω => h_rpow_half_sq _
    have h_f₂_sq : ∀ ω, f₂ ω ^ (2 : ℝ) = ∑ i, (‖Y₂ t ω i‖₊ : ℝ≥0∞) ^ 2 :=
      fun ω => h_rpow_half_sq _
    -- Rewrite LHS and RHS in terms of F, f₁, f₂.
    have h_LHS_eq :
        (∫⁻ ω, ∑ i, (‖(Y₁ t ω + Y₂ t ω) i‖₊ : ℝ≥0∞) ^ 2 ∂P)
            ^ ((1 : ℝ) / 2)
          = (∫⁻ ω, F ω ^ (2 : ℝ) ∂P) ^ ((1 : ℝ) / 2) := by
      congr 1
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      exact (h_F_sq ω).symm
    have h_RHS₁_eq :
        (∫⁻ ω, ∑ i, (‖Y₁ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
          = (∫⁻ ω, f₁ ω ^ (2 : ℝ) ∂P) ^ ((1 : ℝ) / 2) := by
      congr 1
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      exact (h_f₁_sq ω).symm
    have h_RHS₂_eq :
        (∫⁻ ω, ∑ i, (‖Y₂ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
          = (∫⁻ ω, f₂ ω ^ (2 : ℝ) ∂P) ^ ((1 : ℝ) / 2) := by
      congr 1
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      exact (h_f₂_sq ω).symm
    rw [h_LHS_eq, h_RHS₁_eq, h_RHS₂_eq]
    -- Step 1: bound (∫⁻ F²)^(1/2) ≤ (∫⁻ (f₁+f₂)²)^(1/2) via
    --   monotonicity of LHS in F.
    have h_step1 : (∫⁻ ω, F ω ^ (2 : ℝ) ∂P) ^ ((1 : ℝ) / 2)
        ≤ (∫⁻ ω, (f₁ ω + f₂ ω) ^ (2 : ℝ) ∂P) ^ ((1 : ℝ) / 2) := by
      refine ENNReal.rpow_le_rpow ?_ (by norm_num : (0:ℝ) ≤ 1/2)
      refine lintegral_mono (fun ω => ?_)
      -- F ω ≤ f₁ ω + f₂ ω by h_pw, so F ω ^ 2 ≤ (f₁+f₂) ω ^ 2.
      have h_F_le : F ω ≤ f₁ ω + f₂ ω := h_pw ω
      exact ENNReal.rpow_le_rpow h_F_le (by norm_num : (0:ℝ) ≤ 2)
    -- Step 2: apply L² Minkowski `ENNReal.lintegral_Lp_add_le`.
    -- Need AEMeasurable f₁, f₂.
    have hf₁_meas : AEMeasurable f₁ P := hY₁_meas t
    have hf₂_meas : AEMeasurable f₂ P := hY₂_meas t
    have h_step2 := ENNReal.lintegral_Lp_add_le hf₁_meas hf₂_meas (by norm_num : (1:ℝ) ≤ 2)
    -- h_step2 : (∫⁻ ω, (f₁+f₂)(ω)^2 ∂P)^(1/2)
    --   ≤ (∫⁻ f₁²)^(1/2) + (∫⁻ f₂²)^(1/2)
    -- The `(f₁+f₂) ω` in the lintegral is `Pi.add_apply`-applied;
    -- the goal expression is `(f₁ ω + f₂ ω)`. These are defeq.
    exact le_trans h_step1 h_step2
  -- Multiply by the Bielecki weight `ofReal (e^{-βt})` and split.
  calc ENNReal.ofReal (Real.exp (-β * t)) *
      (∫⁻ ω, ∑ i,
          (‖(fun t ω => Y₁ t ω + Y₂ t ω) t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
        ^ ((1 : ℝ) / 2)
      = ENNReal.ofReal (Real.exp (-β * t)) *
          (∫⁻ ω, ∑ i, (‖(Y₁ t ω + Y₂ t ω) i‖₊ : ℝ≥0∞) ^ 2 ∂P)
            ^ ((1 : ℝ) / 2) := rfl
    _ ≤ ENNReal.ofReal (Real.exp (-β * t)) *
          ((∫⁻ ω, ∑ i, (‖Y₁ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
            + (∫⁻ ω, ∑ i, (‖Y₂ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
                ^ ((1 : ℝ) / 2)) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (-β * t)) *
            (∫⁻ ω, ∑ i, (‖Y₁ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
        + ENNReal.ofReal (Real.exp (-β * t)) *
            (∫⁻ ω, ∑ i, (‖Y₂ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2) := by
        rw [mul_add]
    _ ≤ (⨆ s ∈ Set.Icc (0 : ℝ) T,
            ENNReal.ofReal (Real.exp (-β * s)) *
              (∫⁻ ω, ∑ i, (‖Y₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2))
        + ⨆ s ∈ Set.Icc (0 : ℝ) T,
            ENNReal.ofReal (Real.exp (-β * s)) *
              (∫⁻ ω, ∑ i, (‖Y₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
                ^ ((1 : ℝ) / 2) := by
        gcongr
        · refine le_iSup₂ (f := fun s (_ : s ∈ Set.Icc (0:ℝ) T) =>
            ENNReal.ofReal (Real.exp (-β * s)) *
              (∫⁻ ω, ∑ i, (‖Y₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
                ^ ((1 : ℝ) / 2)) t ht
        · refine le_iSup₂ (f := fun s (_ : s ∈ Set.Icc (0:ℝ) T) =>
            ENNReal.ofReal (Real.exp (-β * s)) *
              (∫⁻ ω, ∑ i, (‖Y₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
                ^ ((1 : ℝ) / 2)) t ht

end LevyStochCalc.Ito.Picard
