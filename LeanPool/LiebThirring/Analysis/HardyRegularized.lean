/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import LeanPool.LiebThirring.Defs.Coulomb
/-!
# Regularized Hardy inequality

The regularized inverse-square weight is a valid Schwartz multiplier.

Each component of the regularized Hardy field has temperate growth.
-/
public section
open MeasureTheory
open scoped RealInnerProductSpace SchwartzMap
namespace LiebThirring

/-- The regularized inverse-square weight is a valid Schwartz multiplier. -/
theorem hasTemperateGrowth_hardy_weight {ε : ℝ} (hε : 0 < ε) (c : Position) :
    (fun x : Position => (‖x - c‖ ^ 2 + ε ^ 2)⁻¹).HasTemperateGrowth := by
  have ha : (fun x : Position => ε⁻¹ • (x - c)).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const ε⁻¹).smul
      (Function.HasTemperateGrowth.id'.sub (Function.HasTemperateGrowth.const c))
  have hh := (Function.hasTemperateGrowth_one_add_norm_sq_rpow Position (-1)).comp ha
  have he : (fun x : Position => (‖x - c‖ ^ 2 + ε ^ 2)⁻¹) =
      (fun x : Position => (ε ^ 2)⁻¹ * (1 + ‖ε⁻¹ • (x - c)‖ ^ 2) ^ (-1 : ℝ)) := by
    funext x
    rw [Real.rpow_neg_one, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
    field_simp
    ring
  rw [he]
  exact (Function.HasTemperateGrowth.const _).mul hh

/-- Each component of the regularized Hardy field has temperate growth. -/
theorem hasTemperateGrowth_hardy_component {ε : ℝ} (hε : 0 < ε) (c v : Position) :
    (fun x : Position => inner ℝ (x - c) v / (‖x - c‖ ^ 2 + ε ^ 2)).HasTemperateGrowth := by
  have hi := (Function.hasTemperateGrowth_inner_left v).comp
    (Function.HasTemperateGrowth.id'.sub (Function.HasTemperateGrowth.const c))
  exact hi.mul (hasTemperateGrowth_hardy_weight hε c)

/-- Directional derivative of the regularized Hardy field component. -/
theorem fderiv_hardy_component {ε : ℝ} (hε : 0 < ε) (c x v w : Position) :
    fderiv ℝ (fun y : Position => inner ℝ (y - c) v / (‖y - c‖ ^ 2 + ε ^ 2)) x w =
      inner ℝ w v / (‖x - c‖ ^ 2 + ε ^ 2) -
        2 * inner ℝ (x - c) v * inner ℝ (x - c) w / (‖x - c‖ ^ 2 + ε ^ 2) ^ 2 := by
  have hs := (((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c).norm_sq).add_const (ε ^ 2)
  have hn : ‖x - c‖ ^ 2 + ε ^ 2 ≠ 0 :=
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)).ne'
  have hi := ((innerSL ℝ v).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const c))
  have hi' : HasFDerivAt (fun y : Position => inner ℝ (y - c) v)
      (innerSL ℝ v) x := by
    simpa only [Function.comp_def, id_eq, coe_innerSL_apply, real_inner_comm,
      ContinuousLinearMap.comp_id] using hi
  have hd := hi'.fun_mul ((hasDerivAt_inv hn).comp_hasFDerivAt x hs)
  change fderiv ℝ (fun y : Position => inner ℝ (y - c) v * (‖y - c‖ ^ 2 + ε ^ 2)⁻¹) x w = _
  simp only [Function.comp_def, id_eq] at hd
  rw [hd.fderiv]
  simp only [smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul]
  rw [real_inner_comm v w]
  ring

/-- The coordinate trace of the regularized Hardy field in dimension three. -/
theorem sum_fderiv_hardy_component {ε : ℝ} (hε : 0 < ε) (c x : Position) :
    (∑ i : Fin 3, fderiv ℝ
      (fun y : Position => inner ℝ (y - c) (EuclideanSpace.basisFun (Fin 3) ℝ i) /
        (‖y - c‖ ^ 2 + ε ^ 2)) x (EuclideanSpace.basisFun (Fin 3) ℝ i)) =
      (‖x - c‖ ^ 2 + 3 * ε ^ 2) / (‖x - c‖ ^ 2 + ε ^ 2) ^ 2 := by
  simp_rw [fderiv_hardy_component hε, EuclideanSpace.inner_basisFun_real,
    EuclideanSpace.basisFun_apply, PiLp.single_apply, ite_true]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  simp_rw [show ∀ i : Fin 3, 2 * (x - c) i * (x - c) i = 2 * ((x - c) i) ^ 2
    from fun i => by ring]
  rw [← Finset.sum_div, ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
  have hn : ‖x - c‖ ^ 2 + ε ^ 2 ≠ 0 :=
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)).ne'
  field_simp
  ring

/-- The field derivative is also a valid Schwartz multiplier. -/
theorem hasTemperateGrowth_fderiv_hardy_component {ε : ℝ} (hε : 0 < ε)
    (c v w : Position) :
    (fun x : Position => fderiv ℝ
      (fun y : Position => inner ℝ (y - c) v / (‖y - c‖ ^ 2 + ε ^ 2)) x w).HasTemperateGrowth := by
  simp_rw [fderiv_hardy_component hε]
  have hi (z : Position) := (Function.hasTemperateGrowth_inner_left z).comp
    (Function.HasTemperateGrowth.id'.sub (Function.HasTemperateGrowth.const c))
  have hw := hasTemperateGrowth_hardy_weight hε c
  have h₁ := (Function.HasTemperateGrowth.const (inner ℝ w v)).mul hw
  have h₂ := (((Function.HasTemperateGrowth.const (2 : ℝ)).mul (hi v)).mul (hi w)).mul
    (hw.pow 2)
  convert h₁.sub h₂ using 1
  funext x
  simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply, Pi.pow_apply, inv_pow]
  rfl

/-- A temperate multiplier times a scalar Schwartz test is integrable. -/
theorem integrable_temperate_mul_schwartz {a : Position → ℝ}
    (ha : a.HasTemperateGrowth) (g : 𝓢(Position, ℝ)) :
    Integrable (fun x => a x * g x) (volume : Measure Position) := by
  have hh := (SchwartzMap.smulLeftCLM ℝ a g).integrable (μ := (volume : Measure Position))
  convert hh using 1
  funext x
  exact (SchwartzMap.smulLeftCLM_apply_apply ha g x).symm

/-- Integration by parts against one component of the regularized field. -/
theorem integral_hardy_component_mul_fderiv {ε : ℝ} (hε : 0 < ε)
    (c v : Position) (g : 𝓢(Position, ℝ)) :
    (∫ x, (inner ℝ (x - c) v / (‖x - c‖ ^ 2 + ε ^ 2)) * fderiv ℝ g x v) =
      -∫ x, fderiv ℝ
        (fun y : Position => inner ℝ (y - c) v / (‖y - c‖ ^ 2 + ε ^ 2)) x v * g x := by
  have hv := hasTemperateGrowth_hardy_component hε c v
  have hd := hasTemperateGrowth_fderiv_hardy_component hε c v v
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact integrable_temperate_mul_schwartz hd g
  · exact integrable_temperate_mul_schwartz hv (LineDeriv.lineDerivOp v g)
  · exact integrable_temperate_mul_schwartz hv g
  · exact fun x _ => hv.1.differentiable (by simp) x
  · exact fun x _ => g.differentiableAt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The derivative of the squared Hilbert norm, evaluated in one direction. -/
theorem fderiv_schwartz_norm_sq (f : 𝓢(Position, E)) (x v : Position) :
    fderiv ℝ (fun y => ‖f y‖ ^ 2) x v = 2 * inner ℝ (f x) (fderiv ℝ f x v) := by
  rw [(f.hasFDerivAt x).norm_sq.fderiv]
  simp only [two_smul, add_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  ring

/-- Integration by parts against the squared norm of a Hilbert-valued Schwartz map. -/
theorem integral_hardy_component_norm_sq {ε : ℝ} (hε : 0 < ε)
    (c v : Position) (f : 𝓢(Position, E)) :
    (∫ x, fderiv ℝ
      (fun y : Position => inner ℝ (y - c) v / (‖y - c‖ ^ 2 + ε ^ 2)) x v * ‖f x‖ ^ 2) =
      -2 * ∫ x, (inner ℝ (x - c) v / (‖x - c‖ ^ 2 + ε ^ 2)) *
        inner ℝ (f x) (fderiv ℝ f x v) := by
  let g := SchwartzMap.pairing (innerSL ℝ) f f
  have hg : (g : Position → ℝ) = (fun x => ‖f x‖ ^ 2) := by
    funext x
    exact real_inner_self_eq_norm_sq (f x)
  have hh := integral_hardy_component_mul_fderiv hε c v g
  rw [hg] at hh
  simp_rw [fderiv_schwartz_norm_sq] at hh
  have he : (fun x => (inner ℝ (x - c) v / (‖x - c‖ ^ 2 + ε ^ 2)) *
      (2 * inner ℝ (f x) (fderiv ℝ f x v))) =
      (fun x => 2 * ((inner ℝ (x - c) v / (‖x - c‖ ^ 2 + ε ^ 2)) *
      inner ℝ (f x) (fderiv ℝ f x v))) := by funext x; ring
  rw [he, integral_const_mul] at hh
  linarith only [hh]

/-- The pointwise square estimate used to absorb half the weighted mass. -/
theorem hardy_component_young (a : ℝ) (u v : E) :
    -2 * a * inner ℝ u v ≤ (a ^ 2 * ‖u‖ ^ 2) / 2 + 2 * ‖v‖ ^ 2 := by
  have hh := sq_nonneg ‖(a / 2) • u + v‖
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left] at hh
  nlinarith only [hh]

/-- A temperate multiplier times the squared Schwartz norm is integrable. -/
theorem integrable_temperate_mul_norm_sq {a : Position → ℝ}
    (ha : a.HasTemperateGrowth) (f : 𝓢(Position, E)) :
    Integrable (fun x => a x * ‖f x‖ ^ 2) (volume : Measure Position) := by
  convert integrable_temperate_mul_schwartz ha (SchwartzMap.pairing (innerSL ℝ) f f) using 1
  funext x
  rw [SchwartzMap.pairing_apply_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq]

/-- The regularized Hardy estimate with constant four, uniform in the pole and scale. -/
theorem integral_hardy_regularized_le {ε : ℝ} (hε : 0 < ε)
    (c : Position) (f : 𝓢(Position, E)) :
    (∫ x, (‖x - c‖ ^ 2 + ε ^ 2)⁻¹ * ‖f x‖ ^ 2) ≤
      4 * ∑ i : Fin 3, ∫ x, ‖fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i)‖ ^ 2 := by
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  let a := fun (i : Fin 3) (x : Position) => inner ℝ (x - c) (e i) / (‖x - c‖ ^ 2 + ε ^ 2)
  let b := fun (i : Fin 3) (x : Position) => fderiv ℝ (a i) x (e i)
  let g := fun (i : Fin 3) (x : Position) => fderiv ℝ f x (e i)
  have hiA := integrable_temperate_mul_norm_sq (hasTemperateGrowth_hardy_weight hε c) f
  have hiB (i : Fin 3) : Integrable (fun x => b i x * ‖f x‖ ^ 2) :=
    integrable_temperate_mul_norm_sq (hasTemperateGrowth_fderiv_hardy_component hε c (e i) (e i)) f
  have hiG (i : Fin 3) : Integrable (fun x => ‖g i x‖ ^ 2) := by
    simpa only [one_mul, SchwartzMap.lineDerivOp_apply_eq_fderiv, g] using
      integrable_temperate_mul_norm_sq
      (Function.HasTemperateGrowth.const (1 : ℝ)) (LineDeriv.lineDerivOp (e i) f)
  have hiC (i : Fin 3) : Integrable (fun x => -2 * a i x * inner ℝ (f x) (g i x)) := by
    have hh := (integrable_temperate_mul_schwartz (hasTemperateGrowth_hardy_component hε c (e i))
      (SchwartzMap.pairing (innerSL ℝ) f (LineDeriv.lineDerivOp (e i) f))).const_mul (-2)
    convert hh using 1
    funext x
    simp only [a, g, SchwartzMap.pairing_apply_apply,
      SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change -2 * (inner ℝ (x - c) (e i) / (‖x - c‖ ^ 2 + ε ^ 2)) *
      inner ℝ (f x) (fderiv ℝ f x (e i)) =
      -2 * ((inner ℝ (x - c) (e i) / (‖x - c‖ ^ 2 + ε ^ 2)) *
        inner ℝ (f x) (fderiv ℝ f x (e i)))
    ring
  have hdiv (x : Position) : (‖x - c‖ ^ 2 + ε ^ 2)⁻¹ ≤ ∑ i, b i x := by
    rw [show (∑ i, b i x) = (‖x - c‖ ^ 2 + 3 * ε ^ 2) /
      (‖x - c‖ ^ 2 + ε ^ 2) ^ 2 from sum_fderiv_hardy_component hε c x]
    have hp := add_pos_of_nonneg_of_pos (sq_nonneg ‖x - c‖) (sq_pos_of_pos hε)
    apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
    rw [show (‖x - c‖ ^ 2 + ε ^ 2)⁻¹ * (‖x - c‖ ^ 2 + ε ^ 2) ^ 2 =
      ‖x - c‖ ^ 2 + ε ^ 2 by
        calc
          _ = (‖x - c‖ ^ 2 + ε ^ 2)⁻¹ *
            ((‖x - c‖ ^ 2 + ε ^ 2) * (‖x - c‖ ^ 2 + ε ^ 2)) := by ring
          _ = _ := inv_mul_cancel_left₀ hp.ne' _]
    nlinarith only [sq_nonneg ε]
  have ha (x : Position) : (∑ i, a i x ^ 2) ≤ (‖x - c‖ ^ 2 + ε ^ 2)⁻¹ := by
    change (∑ i : Fin 3, (inner ℝ (x - c) (e i) / (‖x - c‖ ^ 2 + ε ^ 2)) ^ 2) ≤ _
    dsimp [e]
    simp_rw [div_pow, EuclideanSpace.inner_basisFun_real]
    rw [← Finset.sum_div, ← EuclideanSpace.real_norm_sq_eq]
    have hp := add_pos_of_nonneg_of_pos (sq_nonneg ‖x - c‖) (sq_pos_of_pos hε)
    apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
    rw [show (‖x - c‖ ^ 2 + ε ^ 2)⁻¹ * (‖x - c‖ ^ 2 + ε ^ 2) ^ 2 =
      ‖x - c‖ ^ 2 + ε ^ 2 by
        calc
          _ = (‖x - c‖ ^ 2 + ε ^ 2)⁻¹ *
            ((‖x - c‖ ^ 2 + ε ^ 2) * (‖x - c‖ ^ 2 + ε ^ 2)) := by ring
          _ = _ := inv_mul_cancel_left₀ hp.ne' _]
    exact le_add_of_nonneg_right (sq_nonneg ε)
  have hy (x : Position) :
      (∑ i, -2 * a i x * inner ℝ (f x) (g i x)) ≤
        ((‖x - c‖ ^ 2 + ε ^ 2)⁻¹ * ‖f x‖ ^ 2) / 2 + 2 * ∑ i, ‖g i x‖ ^ 2 := by
    calc
      _ ≤ ∑ i, ((a i x ^ 2 * ‖f x‖ ^ 2) / 2 + 2 * ‖g i x‖ ^ 2) :=
        Finset.sum_le_sum (fun i _ => hardy_component_young (a i x) (f x) (g i x))
      _ = ((∑ i, a i x ^ 2) * ‖f x‖ ^ 2) / 2 + 2 * ∑ i, ‖g i x‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ _ := by gcongr; exact ha x
  have he : (∫ x, ∑ i, b i x * ‖f x‖ ^ 2) =
      ∫ x, ∑ i, -2 * a i x * inner ℝ (f x) (g i x) := by
    rw [integral_finsetSum _ (fun i _ => hiB i), integral_finsetSum _ (fun i _ => hiC i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_hardy_component_norm_sq hε c (e i) f]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by dsimp [a, g]; ring)
  have h₁ : (∫ x, (‖x - c‖ ^ 2 + ε ^ 2)⁻¹ * ‖f x‖ ^ 2) ≤
      ∫ x, ∑ i, b i x * ‖f x‖ ^ 2 := by
    apply integral_mono hiA (integrable_finsetSum _ (fun i _ => hiB i))
    intro x
    dsimp only
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hdiv x) (sq_nonneg _)
  have h₂ := integral_mono (integrable_finsetSum _ (fun i _ => hiC i))
    ((hiA.div_const 2).add ((integrable_finsetSum _ (fun i _ => hiG i)).const_mul 2)) hy
  simp only [Pi.add_apply] at h₂
  rw [integral_add (hiA.div_const 2) ((integrable_finsetSum _ (fun i _ => hiG i)).const_mul 2),
    integral_div, integral_const_mul, integral_finsetSum _ (fun i _ => hiG i)] at h₂
  rw [← he] at h₂
  linarith only [h₁, h₂]

end LiebThirring
end
