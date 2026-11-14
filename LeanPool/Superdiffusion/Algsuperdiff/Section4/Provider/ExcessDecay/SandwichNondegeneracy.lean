/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CubeMoments

/-!
# SandwichNondegeneracy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The affine geometry of a sandwiched window

`l.iteration.lemma` never assumes its windows are cubes.  Its only stated
geometry is the **sandwich** `x + □_{j-2} ⊆ U_j ⊆ y + □_j` (hypothesis (iii),
scoped to `j ≤ m` per the binding).  This module transports the exact cube
second moment of `CubeMoments.lean` to such a window, producing the two
window-geometry facts on which every §4.3 producer rests:

* the **inverse (Bernstein) inequality** `hnd`
  `c₀ |W|^{1/d} |g| ≤ ‖c + g·x‖_{L²(W)}` (`normalizedL2On_affineEval_ge_of_sandwich`), with
  `c₀ = ndConst d θ = √(θ^d)·θ/(2√3)` for a sandwich of aspect ratio `θ = Lin/Lout`;
* the **direct (diameter) inequality** `haffosc`
  `‖ℓ − (ℓ)_W‖_{L²(W)} ≤ K |W|^{1/d} |∇ℓ|`
  (`normalizedL2On_affineEval_sub_average_le_of_sandwich`), with
  `K = oscConst d θ = 1/(√(θ^d)·θ·2√3)`.

They are the *opposite* halves of the same geometry, and they are exactly what
the two endpoint comparisons of Step 3 need.  Note `ndConst d θ · oscConst d θ = 1/12`,
so on an exact cube (`θ = 1`) both constants are `1/(2√3)` and both
inequalities are equalities.

For the paper's triadic sandwich the aspect ratio is `θ = 3^{-2} = 1/9` at *every* scale, giving
the scale-free constants `c₀ = 3^{-d-2}/(2√3)` and `K = 3^{d+2}/(2√3)`
(`ndConst_one_ninth`, `oscConst_one_ninth`).  Both are explicit definitions of `d` alone: no
existential constant appears anywhere in this module.

## What is assumed and what is proved

Nothing about `W` is assumed beyond the sandwich itself and `0 < Lin`, `0 < Lout`: positivity and
finiteness of `|W|`, square-integrability of the affine competitors, and the two inequalities are
all **derived**.  In particular the nondegeneracy that `AffineMinimizerExistence.lean` had to
carry as a hypothesis (`hlb`/`hub`) becomes a theorem here --- see
`SandwichNondegeneracyAttainment.lean`.

## References

* ABK26, `e.grad.stability`; `l.iteration.lemma`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport (Vec vecDot vecNormSq volumeAverage axisCube openCubeSet TriadicCube
  cubeCenter cubeScaleFactor)
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ### The two sandwich constants -/

/-- The **nondegeneracy constant** of a sandwich of aspect ratio `θ = Lin/Lout`:
`c₀(θ) = √(θ^d)·θ/(2√3)`.  For the triadic sandwich `x + □_{j-2} ⊆ U_j ⊆ y + □_j` the ratio is
`θ = 3^{-2}` and `c₀ = 3^{-d-2}/(2√3)`. -/
def ndConst (d : ℕ) (θ : ℝ) : ℝ :=
  Real.sqrt (θ ^ d) * θ / (2 * Real.sqrt 3)

/-- The **affine-oscillation (diameter) constant** of a sandwich of aspect ratio `θ`:
`K(θ) = 1/(√(θ^d)·θ·2√3)`.  Note `ndConst d θ · oscConst d θ = 1/12`, so on an exact cube
(`θ = 1`) both are `1/(2√3)`. -/
def oscConst (d : ℕ) (θ : ℝ) : ℝ :=
  1 / (Real.sqrt (θ ^ d) * θ * (2 * Real.sqrt 3))

theorem ndConst_pos {θ : ℝ} (hθ : 0 < θ) : 0 < ndConst d θ := by
  have h : 0 < Real.sqrt (θ ^ d) := Real.sqrt_pos.2 (pow_pos hθ d)
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [ndConst]
  positivity

theorem oscConst_pos {θ : ℝ} (hθ : 0 < θ) : 0 < oscConst d θ := by
  have h : 0 < Real.sqrt (θ ^ d) := Real.sqrt_pos.2 (pow_pos hθ d)
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [oscConst]
  positivity

/-- `ndConst` is monotone in the aspect ratio: a fatter sandwich is a better window. -/
theorem ndConst_mono {θ θ' : ℝ} (hθ : 0 < θ) (hle : θ ≤ θ') :
    ndConst d θ ≤ ndConst d θ' := by
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs : Real.sqrt (θ ^ d) ≤ Real.sqrt (θ' ^ d) :=
    Real.sqrt_le_sqrt (pow_le_pow_left₀ hθ.le hle d)
  have hs0 : 0 ≤ Real.sqrt (θ ^ d) := Real.sqrt_nonneg _
  rw [ndConst, ndConst]
  exact div_le_div_of_nonneg_right
    (mul_le_mul hs hle hθ.le (Real.sqrt_nonneg _)) (by positivity)

/-- `oscConst` is antitone in the aspect ratio. -/
theorem oscConst_anti {θ θ' : ℝ} (hθ : 0 < θ) (hle : θ ≤ θ') :
    oscConst d θ' ≤ oscConst d θ := by
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hθ' : 0 < θ' := lt_of_lt_of_le hθ hle
  have hs : Real.sqrt (θ ^ d) ≤ Real.sqrt (θ' ^ d) :=
    Real.sqrt_le_sqrt (pow_le_pow_left₀ hθ.le hle d)
  have hs0 : 0 < Real.sqrt (θ ^ d) := Real.sqrt_pos.2 (pow_pos hθ d)
  rw [oscConst, oscConst]
  exact div_le_div_of_nonneg_left zero_le_one
    (mul_pos (mul_pos hs0 hθ) (by positivity))
    (mul_le_mul_of_nonneg_right (mul_le_mul hs hle hθ.le (Real.sqrt_nonneg _))
      (by positivity))

/-! ### Volume bookkeeping for a sandwich -/

theorem volume_ne_top_of_sandwich {W : Set (Vec d)} {zout : Vec d} {Lout : ℝ}
    (hout : W ⊆ axisCube zout Lout) : volume W ≠ ⊤ :=
  ne_top_of_le_ne_top (volume_axisCube_ne_top zout Lout) (measure_mono hout)

theorem pow_le_volume_toReal_of_sandwich {W : Set (Vec d)} {zin zout : Vec d} {Lin Lout : ℝ}
    (hLin : 0 ≤ Lin) (hin : axisCube zin Lin ⊆ W) (hout : W ⊆ axisCube zout Lout) :
    Lin ^ d ≤ (volume W).toReal := by
  rw [← volume_axisCube_toReal zin hLin]
  exact ENNReal.toReal_mono (volume_ne_top_of_sandwich hout) (measure_mono hin)

theorem volume_toReal_le_pow_of_sandwich {W : Set (Vec d)} {zout : Vec d} {Lout : ℝ}
    (hLout : 0 ≤ Lout) (hout : W ⊆ axisCube zout Lout) :
    (volume W).toReal ≤ Lout ^ d := by
  rw [← volume_axisCube_toReal zout hLout]
  exact ENNReal.toReal_mono (volume_axisCube_ne_top zout Lout) (measure_mono hout)

theorem volume_toReal_pos_of_sandwich {W : Set (Vec d)} {zin zout : Vec d} {Lin Lout : ℝ}
    (hLin : 0 < Lin) (hin : axisCube zin Lin ⊆ W) (hout : W ⊆ axisCube zout Lout) :
    0 < (volume W).toReal :=
  lt_of_lt_of_le (pow_pos hLin d) (pow_le_volume_toReal_of_sandwich hLin.le hin hout)

private theorem rpow_inv_natCast_pow (hd : 0 < d) {x : ℝ} (hx : 0 ≤ x) :
    (x ^ d) ^ ((d : ℝ)⁻¹) = x := by
  have hdne : ((d : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [← Real.rpow_natCast x d, ← Real.rpow_mul hx, mul_inv_cancel₀ hdne, Real.rpow_one]

/-- `Lin ≤ |W|^{1/d} ≤ Lout` for a sandwiched window. -/
theorem rpow_volume_bounds_of_sandwich {W : Set (Vec d)} {zin zout : Vec d} {Lin Lout : ℝ}
    (hd : 0 < d) (hLin : 0 < Lin) (hLout : 0 < Lout)
    (hin : axisCube zin Lin ⊆ W) (hout : W ⊆ axisCube zout Lout) :
    Lin ≤ ((volume W).toReal) ^ ((d : ℝ)⁻¹)
      ∧ ((volume W).toReal) ^ ((d : ℝ)⁻¹) ≤ Lout := by
  refine ⟨?_, ?_⟩
  · calc Lin = ((Lin ^ d : ℝ)) ^ ((d : ℝ)⁻¹) := (rpow_inv_natCast_pow hd hLin.le).symm
      _ ≤ ((volume W).toReal) ^ ((d : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) (pow_le_volume_toReal_of_sandwich hLin.le hin hout)
          (by positivity)
  · calc ((volume W).toReal) ^ ((d : ℝ)⁻¹)
        ≤ ((Lout ^ d : ℝ)) ^ ((d : ℝ)⁻¹) :=
        Real.rpow_le_rpow ENNReal.toReal_nonneg
          (volume_toReal_le_pow_of_sandwich hLout.le hout) (by positivity)
      _ = Lout := rpow_inv_natCast_pow hd hLout.le

/-! ### Square-integrability of the affine competitors -/

theorem integrableOn_affineEval_sq_of_sandwich {W : Set (Vec d)} {zout : Vec d} {Lout : ℝ}
    (hout : W ⊆ axisCube zout Lout) (c : ℝ) (g : Vec d) :
    IntegrableOn (fun x => affineEval c g x ^ 2) W :=
  (integrableOn_axisCube_of_continuous ((continuous_affineEval c g).pow 2) zout Lout).mono_set hout

theorem integrableOn_affineEval_of_sandwich {W : Set (Vec d)} {zout : Vec d} {Lout : ℝ}
    (hout : W ⊆ axisCube zout Lout) (c : ℝ) (g : Vec d) :
    IntegrableOn (affineEval c g) W :=
  (integrableOn_axisCube_of_continuous (continuous_affineEval c g) zout Lout).mono_set hout

/-! ### The volume ratio of a sandwich -/

/-- The inner-cube volume ratio: `(|W|/|□in|)^{1/2} ≤ (√(θ^d))⁻¹` for `θ = Lin/Lout`.  Only the
outer inclusion is used: the inner cube enters through its volume `Lin^d` alone. -/
theorem sqrt_volume_ratio_inner_le {W : Set (Vec d)} {zin zout : Vec d} {Lin Lout : ℝ}
    (hLin : 0 < Lin) (hLout : 0 < Lout) (hout : W ⊆ axisCube zout Lout) :
    Real.sqrt ((volume W).toReal / (volume (axisCube zin Lin)).toReal)
      ≤ (Real.sqrt ((Lin / Lout) ^ d))⁻¹ := by
  have hb : (0 : ℝ) < Lin ^ d := pow_pos hLin d
  have hle : (volume W).toReal / (volume (axisCube zin Lin)).toReal ≤ ((Lin / Lout) ^ d)⁻¹ := by
    rw [volume_axisCube_toReal zin hLin.le, div_pow, inv_div]
    exact div_le_div_of_nonneg_right
      (volume_toReal_le_pow_of_sandwich hLout.le hout) hb.le
  calc Real.sqrt ((volume W).toReal / (volume (axisCube zin Lin)).toReal)
      ≤ Real.sqrt (((Lin / Lout) ^ d)⁻¹) := Real.sqrt_le_sqrt hle
    _ = (Real.sqrt ((Lin / Lout) ^ d))⁻¹ := Real.sqrt_inv _

/-- The outer-cube volume ratio: `(|□out|/|W|)^{1/2} ≤ (√(θ^d))⁻¹` for `θ = Lin/Lout`. -/
private theorem sqrt_ratio_outer_le {W : Set (Vec d)} {zin zout : Vec d} {Lin Lout : ℝ}
    (hLin : 0 < Lin) (hLout : 0 < Lout) (hin : axisCube zin Lin ⊆ W)
    (hout : W ⊆ axisCube zout Lout) :
    Real.sqrt ((volume (axisCube zout Lout)).toReal / (volume W).toReal)
      ≤ (Real.sqrt ((Lin / Lout) ^ d))⁻¹ := by
  have hb : (0 : ℝ) < Lin ^ d := pow_pos hLin d
  have hout0 : (0 : ℝ) ≤ Lout ^ d := by positivity
  have hle : (volume (axisCube zout Lout)).toReal / (volume W).toReal
      ≤ ((Lin / Lout) ^ d)⁻¹ := by
    rw [volume_axisCube_toReal zout hLout.le, div_pow, inv_div]
    exact div_le_div_of_nonneg_left hout0 hb
      (pow_le_volume_toReal_of_sandwich hLin.le hin hout)
  calc Real.sqrt ((volume (axisCube zout Lout)).toReal / (volume W).toReal)
      ≤ Real.sqrt (((Lin / Lout) ^ d)⁻¹) := Real.sqrt_le_sqrt hle
    _ = (Real.sqrt ((Lin / Lout) ^ d))⁻¹ := Real.sqrt_inv _

/-! ### `hnd`: the inverse (Bernstein) inequality on a sandwiched window -/

/-- The arithmetic identity behind `hnd`'s constant, over abstract reals. -/
private theorem ndConst_mul_mul (d : ℕ) (t Lout S : ℝ) :
    ndConst d t * Lout * S = Real.sqrt (t ^ d) * (t * Lout / (2 * Real.sqrt 3) * S) := by
  rw [ndConst]
  ring

/-- **`hnd` at the sandwich's own aspect ratio.**  On a window sandwiched between two
axis-parallel cubes, `c₀ |W|^{1/d} |g| ≤ ‖c + g·x‖_{L²(W)}` with `c₀ = ndConst d (Lin/Lout)`. -/
theorem normalizedL2On_affineEval_ge_of_sandwich_aux {W : Set (Vec d)} {zin zout : Vec d}
    {Lin Lout : ℝ} (hd : 0 < d) (hLin : 0 < Lin) (hLout : 0 < Lout)
    (hin : axisCube zin Lin ⊆ W) (hout : W ⊆ axisCube zout Lout) (c : ℝ) (g : Vec d) :
    ndConst d (Lin / Lout) * ((volume W).toReal) ^ ((d : ℝ)⁻¹) * slopeMagnitude g
      ≤ normalizedL2On W (affineEval c g) := by
  have hS : 0 ≤ slopeMagnitude g := slopeMagnitude_nonneg g
  have hVpos : 0 < (volume W).toReal := volume_toReal_pos_of_sandwich hLin hin hout
  have hQinpos : 0 < (volume (axisCube zin Lin)).toReal := volume_axisCube_toReal_pos zin hLin
  have hr : 0 < Real.sqrt ((Lin / Lout) ^ d) := Real.sqrt_pos.2 (pow_pos (div_pos hLin hLout) d)
  have hN : 0 ≤ normalizedL2On W (affineEval c g) := normalizedL2On_nonneg _ _
  -- Step 1: the exact cube lower bound on the inner cube.
  have h1 : Lin / (2 * Real.sqrt 3) * slopeMagnitude g
      ≤ normalizedL2On (axisCube zin Lin) (affineEval c g) :=
    normalizedL2On_axisCube_affineEval_ge zin hLin c g
  -- Step 2: pass from the inner cube to `W`, at the sandwich volume ratio.
  have h2 : normalizedL2On (axisCube zin Lin) (affineEval c g)
      ≤ Real.sqrt ((volume W).toReal / (volume (axisCube zin Lin)).toReal)
        * normalizedL2On W (affineEval c g) :=
    normalizedL2On_le_of_subset hin hVpos hQinpos (integrableOn_affineEval_sq_of_sandwich hout c g)
  have h3 := sqrt_volume_ratio_inner_le (zin := zin) hLin hLout hout
  have hchain : Lin / (2 * Real.sqrt 3) * slopeMagnitude g
      ≤ (Real.sqrt ((Lin / Lout) ^ d))⁻¹ * normalizedL2On W (affineEval c g) :=
    h1.trans (h2.trans (mul_le_mul_of_nonneg_right h3 hN))
  -- Step 3: clear the volume ratio.
  have hcancel : Real.sqrt ((Lin / Lout) ^ d)
      * ((Real.sqrt ((Lin / Lout) ^ d))⁻¹ * normalizedL2On W (affineEval c g))
      = normalizedL2On W (affineEval c g) := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hr), one_mul]
  have hmul : Real.sqrt ((Lin / Lout) ^ d) * (Lin / (2 * Real.sqrt 3) * slopeMagnitude g)
      ≤ normalizedL2On W (affineEval c g) := by
    refine le_trans (mul_le_mul_of_nonneg_left hchain hr.le) ?_
    rw [hcancel]
  -- Step 4: `|W|^{1/d} ≤ Lout`, and the constant arithmetic.
  obtain ⟨_, hup⟩ := rpow_volume_bounds_of_sandwich hd hLin hLout hin hout
  have hc0 : 0 < ndConst d (Lin / Lout) := ndConst_pos (div_pos hLin hLout)
  have hstep : ndConst d (Lin / Lout) * ((volume W).toReal) ^ ((d : ℝ)⁻¹) * slopeMagnitude g
      ≤ ndConst d (Lin / Lout) * Lout * slopeMagnitude g :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hup hc0.le) hS
  have hLinEq : Lin / Lout * Lout = Lin := by
    rw [div_mul_eq_mul_div, mul_div_assoc, div_self (ne_of_gt hLout), mul_one]
  refine hstep.trans (le_trans (le_of_eq ?_) hmul)
  rw [ndConst_mul_mul, hLinEq]

/-- **`hnd` at a uniform aspect ratio.**  If `θ · Lout ≤ Lin` then
`ndConst d θ · |W|^{1/d} · |g| ≤ ‖c + g·x‖_{L²(W)}`.  This is the form the §4.3 producers need:
one constant for a whole family of windows. -/
theorem normalizedL2On_affineEval_ge_of_sandwich {W : Set (Vec d)} {zin zout : Vec d}
    {Lin Lout θ : ℝ} (hd : 0 < d) (hLin : 0 < Lin) (hLout : 0 < Lout) (hθ0 : 0 < θ)
    (hθ : θ * Lout ≤ Lin) (hin : axisCube zin Lin ⊆ W) (hout : W ⊆ axisCube zout Lout)
    (c : ℝ) (g : Vec d) :
    ndConst d θ * ((volume W).toReal) ^ ((d : ℝ)⁻¹) * slopeMagnitude g
      ≤ normalizedL2On W (affineEval c g) := by
  refine le_trans ?_ (normalizedL2On_affineEval_ge_of_sandwich_aux hd hLin hLout hin hout c g)
  have hle : θ ≤ Lin / Lout := (le_div_iff₀ hLout).2 hθ
  have h1 : (0 : ℝ) ≤ ((volume W).toReal) ^ ((d : ℝ)⁻¹) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (ndConst_mono hθ0 hle) h1) (slopeMagnitude_nonneg g)

/-! ### The mean minimizes the `L²` deviation -/

/-- The volume average of a constant is that constant, on a window of positive finite volume. -/
theorem volumeAverage_const_of_pos {W : Set (Vec d)} (hW : 0 < (volume W).toReal)
    (a : ℝ) : volumeAverage W (fun _ => a) = a := by
  unfold volumeAverage
  rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (ne_of_gt hW), one_mul]

/-- Expansion of the average of `(f − a)²`. -/
theorem volumeAverage_sub_const_sq {W : Set (Vec d)} (hWm : MeasurableSet W)
    (hW : 0 < (volume W).toReal) (hfin : volume W ≠ ⊤) {f : Vec d → ℝ}
    (hf : IntegrableOn f W) (hf2 : IntegrableOn (fun x => f x ^ 2) W) (a : ℝ) :
    volumeAverage W (fun x => (f x - a) ^ 2)
      = volumeAverage W (fun x => f x ^ 2) - 2 * a * volumeAverage W f + a ^ 2 := by
  have hB : IntegrableOn (fun x => -(2 * a) * f x) W := hf.const_mul _
  have hAB : IntegrableOn (fun x => f x ^ 2 + -(2 * a) * f x) W := hf2.add hB
  have hC : IntegrableOn (fun _ : Vec d => a ^ 2) W := integrableOn_const hfin
  have hcongr : (∫ x in W, (f x - a) ^ 2)
      = ∫ x in W, (f x ^ 2 + -(2 * a) * f x + a ^ 2) :=
    MeasureTheory.setIntegral_congr_fun hWm (fun x _ => by ring)
  have hVne : (volume W).toReal ≠ 0 := ne_of_gt hW
  unfold volumeAverage
  rw [hcongr, MeasureTheory.integral_add hAB hC, MeasureTheory.integral_add hf2 hB,
    MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_const,
    MeasureTheory.measureReal_def, smul_eq_mul]
  field_simp
  ring

/-- **The mean minimizes the `L²` deviation**: `‖f − (f)_W‖_{L²(W)} ≤ ‖f − a‖_{L²(W)}` for every
constant `a`.  This is what transfers the affine-oscillation bound from the outer cube to `W`. -/
theorem normalizedL2On_sub_volumeAverage_le {W : Set (Vec d)} (hWm : MeasurableSet W)
    (hW : 0 < (volume W).toReal) (hfin : volume W ≠ ⊤) {f : Vec d → ℝ}
    (hf : IntegrableOn f W) (hf2 : IntegrableOn (fun x => f x ^ 2) W) (a : ℝ) :
    normalizedL2On W (fun x => f x - volumeAverage W f)
      ≤ normalizedL2On W (fun x => f x - a) := by
  have h1 := volumeAverage_sub_const_sq hWm hW hfin hf hf2 (volumeAverage W f)
  have h2 := volumeAverage_sub_const_sq hWm hW hfin hf hf2 a
  have hsq : (0 : ℝ) ≤ (a - volumeAverage W f) ^ 2 := sq_nonneg _
  have hexp : (a - volumeAverage W f) ^ 2
      = a ^ 2 - 2 * a * volumeAverage W f + volumeAverage W f ^ 2 := by ring
  unfold normalizedL2On
  refine Real.sqrt_le_sqrt ?_
  rw [h1, h2]
  linarith only [hsq, hexp]

/-! ### `haffosc`: the direct (diameter) inequality on a sandwiched window -/

/-- The arithmetic identity behind `haffosc`'s constant, over abstract reals. -/
private theorem oscConst_mul_mul {t Lin Lout S : ℝ} (ht : Real.sqrt (t ^ d) ≠ 0) (ht' : t ≠ 0)
    (h3 : Real.sqrt 3 ≠ 0) (hLin : Lin = t * Lout) :
    (Real.sqrt (t ^ d))⁻¹ * (Lout / (2 * Real.sqrt 3) * S) = oscConst d t * Lin * S := by
  rw [oscConst, hLin]
  field_simp

/-- **`haffosc` at the sandwich's own aspect ratio.**  On a sandwiched window,
`‖ℓ − (ℓ)_W‖_{L²(W)} ≤ K |W|^{1/d} |∇ℓ|` with `K = oscConst d (Lin/Lout)`.

On an exact cube (`Lin = Lout`) the constant is `1/(2√3)` and the inequality is the *equality*
`normalizedL2On_axisCube_affineEval_sub_average`. -/
theorem normalizedL2On_affineEval_sub_average_le_of_sandwich_aux {W : Set (Vec d)}
    {zin zout : Vec d} {Lin Lout : ℝ} (hd : 0 < d) (hLin : 0 < Lin) (hLout : 0 < Lout)
    (hWm : MeasurableSet W) (hin : axisCube zin Lin ⊆ W) (hout : W ⊆ axisCube zout Lout)
    (c : ℝ) (g : Vec d) :
    normalizedL2On W (fun x => affineEval c g x - volumeAverage W (affineEval c g))
      ≤ oscConst d (Lin / Lout) * ((volume W).toReal) ^ ((d : ℝ)⁻¹) * slopeMagnitude g := by
  have hS : 0 ≤ slopeMagnitude g := slopeMagnitude_nonneg g
  have hVpos : 0 < (volume W).toReal := volume_toReal_pos_of_sandwich hLin hin hout
  have hfin : volume W ≠ ⊤ := volume_ne_top_of_sandwich hout
  have hQoutpos : 0 < (volume (axisCube zout Lout)).toReal :=
    volume_axisCube_toReal_pos zout hLout
  have hr : 0 < Real.sqrt ((Lin / Lout) ^ d) := Real.sqrt_pos.2 (pow_pos (div_pos hLin hLout) d)
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  -- Step 1: the mean minimizes, so we may recentre at the *outer* cube's centre.
  have h1 : normalizedL2On W (fun x => affineEval c g x - volumeAverage W (affineEval c g))
      ≤ normalizedL2On W
          (fun x => affineEval c g x - affineEval c g (axisCubeCenter zout Lout)) :=
    normalizedL2On_sub_volumeAverage_le hWm hVpos hfin
      (integrableOn_affineEval_of_sandwich hout c g)
      (integrableOn_affineEval_sq_of_sandwich hout c g) _
  -- Step 2: pass to the outer cube, at the sandwich volume ratio.
  have hsqint : IntegrableOn
      (fun x => (affineEval c g x - affineEval c g (axisCubeCenter zout Lout)) ^ 2)
      (axisCube zout Lout) :=
    integrableOn_axisCube_of_continuous
      (((continuous_affineEval c g).sub continuous_const).pow 2) zout Lout
  have h2 : normalizedL2On W
        (fun x => affineEval c g x - affineEval c g (axisCubeCenter zout Lout))
      ≤ Real.sqrt ((volume (axisCube zout Lout)).toReal / (volume W).toReal)
        * normalizedL2On (axisCube zout Lout)
            (fun x => affineEval c g x - affineEval c g (axisCubeCenter zout Lout)) :=
    normalizedL2On_le_of_subset hout hQoutpos hVpos hsqint
  -- Step 3: the exact cube identity on the outer cube.
  have h3' : normalizedL2On (axisCube zout Lout)
        (fun x => affineEval c g x - affineEval c g (axisCubeCenter zout Lout))
      = Lout / (2 * Real.sqrt 3) * slopeMagnitude g := by
    rw [← volumeAverage_axisCube_affineEval zout hLout c g]
    exact normalizedL2On_axisCube_affineEval_sub_average zout hLout c g
  have h4 := sqrt_ratio_outer_le hLin hLout hin hout
  have hbound : normalizedL2On W (fun x => affineEval c g x - volumeAverage W (affineEval c g))
      ≤ (Real.sqrt ((Lin / Lout) ^ d))⁻¹ * (Lout / (2 * Real.sqrt 3) * slopeMagnitude g) := by
    refine h1.trans (h2.trans ?_)
    rw [h3']
    exact mul_le_mul_of_nonneg_right h4 (by positivity)
  -- Step 4: `Lin ≤ |W|^{1/d}`, and the constant arithmetic.
  obtain ⟨hlow, _⟩ := rpow_volume_bounds_of_sandwich hd hLin hLout hin hout
  have hK : 0 < oscConst d (Lin / Lout) := oscConst_pos (div_pos hLin hLout)
  have hLinEq : Lin = Lin / Lout * Lout := by
    rw [div_mul_eq_mul_div, mul_div_assoc, div_self (ne_of_gt hLout), mul_one]
  have hstep : oscConst d (Lin / Lout) * Lin * slopeMagnitude g
      ≤ oscConst d (Lin / Lout) * ((volume W).toReal) ^ ((d : ℝ)⁻¹) * slopeMagnitude g :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlow hK.le) hS
  refine hbound.trans (le_trans (le_of_eq ?_) hstep)
  exact oscConst_mul_mul (ne_of_gt hr) (ne_of_gt (div_pos hLin hLout)) (ne_of_gt h3) hLinEq

/-- **`haffosc` at a uniform aspect ratio.**  If `θ · Lout ≤ Lin` then
`‖ℓ − (ℓ)_W‖_{L²(W)} ≤ oscConst d θ · |W|^{1/d} · |∇ℓ|`. -/
theorem normalizedL2On_affineEval_sub_average_le_of_sandwich {W : Set (Vec d)}
    {zin zout : Vec d} {Lin Lout θ : ℝ} (hd : 0 < d) (hLin : 0 < Lin) (hLout : 0 < Lout)
    (hθ0 : 0 < θ) (hθ : θ * Lout ≤ Lin) (hWm : MeasurableSet W)
    (hin : axisCube zin Lin ⊆ W) (hout : W ⊆ axisCube zout Lout) (c : ℝ) (g : Vec d) :
    normalizedL2On W (fun x => affineEval c g x - volumeAverage W (affineEval c g))
      ≤ oscConst d θ * ((volume W).toReal) ^ ((d : ℝ)⁻¹) * slopeMagnitude g := by
  refine le_trans
    (normalizedL2On_affineEval_sub_average_le_of_sandwich_aux hd hLin hLout hWm hin hout c g) ?_
  have hle : θ ≤ Lin / Lout := (le_div_iff₀ hLout).2 hθ
  have h1 : (0 : ℝ) ≤ ((volume W).toReal) ^ ((d : ℝ)⁻¹) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (oscConst_anti hθ0 hle) h1) (slopeMagnitude_nonneg g)

/-! ### The triadic instance: aspect ratio `1/9` at every scale -/

/-- The triadic sandwich has aspect ratio exactly `1/9`: `3^{j-2} = 3^j/9`. -/
theorem triadic_aspect (j : ℤ) : (1 / 9 : ℝ) * (3 : ℝ) ^ j = (3 : ℝ) ^ (j - 2) := by
  rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
  rw [show ((3 : ℝ) ^ (2 : ℤ)) = 9 by norm_num]
  ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
