/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.AffineMinimizerExistence
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SandwichNondegeneracy

/-!
# SandwichNondegeneracyAttainment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Attainment of the affine minimum on the §4.3 consumption class

`AffineMinimizerExistence.lean` proves attainment of `ℓ(u,W) = argmin_{ℓ ∈ 𝕃}
‖u − ℓ‖_{L²(W)}` on every window carrying the two-sided **parameter-space**
nondegeneracy

```
c₀ ‖(c,g)‖ ≤ ‖c + g·x‖_{L²(W)} ≤ K ‖(c,g)‖        (hlb / hub),      c₀ > 0 ,
```

It also records the residual: the §4.3 consumption sites are the truncated
windows `U_j = (x + □_j) ∩ □_m`, whose only stated geometry is the sandwich `x
+ □_{j-2} ⊆ U_j ⊆ y + □_j`, and on such a window `hlb`/`hub` are *theorems* ---
reachable only through the exact cube second moment.

This module closes that residual.  `hub` is the crude sup bound on the outer cube; `hlb` combines

* the exact cube second moment on the *inner* cube (`CubeMoments.lean`), which gives both
  `|c + g·x| ≤ ‖c + g·x‖_{L²(□in)}` and `(Lin/(2√3))|g| ≤ ‖c + g·x‖_{L²(□in)}`,
* the volume-ratio transfer `normalizedL2On_le_of_subset` from `□in` to `W`, and
* the recentring `|c| ≤ |c + g·x| + |x||g|`, which converts the two cube bounds into a bound on
  the parameter norm `‖(c,g)‖ = max(|c|, ‖g‖_∞)`.

The outcome is `exists_isAffineMinimizer_of_cubeSandwich`: attainment is **unconditional** on the
consumption class, with the explicit constants `lbConst` and `ubConst`.

## Scope, honestly

Attainment needs only that `W` is sandwiched between *some* two axis-parallel (resp. triadic)
cubes of positive side; the scale relation `Lin = 3^{-2} Lout` of the paper's sandwich is **not**
used here and is therefore not a hypothesis.  It *is* used by `SandwichNondegeneracy.lean`, whose
constants must be scale-free across the window family.  Note also that `lbConst` and `ubConst` are
**not** scale invariant: they involve the position of the window (`‖zout‖`, `|x|`), because the
parameter norm `‖(c,g)‖` adds an intercept to a slope.  That is intrinsic to the direct method's
coercivity hypothesis, not a defect; the scale-invariant form is `hnd`.

## References

* ABK26, `e.excess.def` (the `min`/`argmin`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport (Vec vecDot vecNormSq volumeAverage axisCube openCubeSet TriadicCube
  cubeScaleFactor)
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ### Euclidean versus sup norm on `Vec d` -/

/-- The ambient (sup) norm of a slope is dominated by its Euclidean norm. -/
theorem norm_le_slopeMagnitude (g : Vec d) : ‖g‖ ≤ slopeMagnitude g := by
  refine (pi_norm_le_iff_of_nonneg (slopeMagnitude_nonneg g)).2 fun i => ?_
  rw [Real.norm_eq_abs, slopeMagnitude]
  have hsum : g i * g i ≤ ∑ j, g j * g j :=
    Finset.single_le_sum (f := fun j => g j * g j) (fun j _ => mul_self_nonneg (g j))
      (Finset.mem_univ i)
  have hv : |g i| ^ 2 ≤ vecNormSq g := by
    rw [sq_abs, pow_two, vecNormSq, vecDot]
    exact hsum
  exact (Real.le_sqrt (abs_nonneg _) (HCPolySupport.vecNormSq_nonneg g)).2 hv

/-- Cauchy--Schwarz in the Euclidean norm of `Vec d`. -/
theorem abs_vecDot_le_slopeMagnitude_mul (x y : Vec d) :
    |vecDot x y| ≤ slopeMagnitude x * slopeMagnitude y := by
  have hcs := HCPolySupport.sq_vecDot_le_vecNormSq_mul_vecNormSq x y
  calc |vecDot x y| = Real.sqrt (vecDot x y ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (vecNormSq x * vecNormSq y) := Real.sqrt_le_sqrt hcs
    _ = slopeMagnitude x * slopeMagnitude y :=
        Real.sqrt_mul (HCPolySupport.vecNormSq_nonneg x) _

/-! ### A pointwise bound bounds the normalized seminorm -/

/-- If `|f| ≤ M` on `W` then `‖f‖_{L²(W)} ≤ M`. -/
theorem normalizedL2On_le_of_abs_le {W : Set (Vec d)} (hWm : MeasurableSet W)
    (hW : 0 < (volume W).toReal) (hfin : volume W ≠ ⊤) {f : Vec d → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hf2 : IntegrableOn (fun x => f x ^ 2) W) (hle : ∀ x ∈ W, |f x| ≤ M) :
    normalizedL2On W f ≤ M := by
  have hint : (∫ x in W, f x ^ 2) ≤ ∫ _x in W, M ^ 2 := by
    refine MeasureTheory.setIntegral_mono_on hf2 (integrableOn_const hfin) hWm ?_
    intro x hx
    have h2 : |f x| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hle x hx) 2
    rw [sq_abs] at h2
    exact h2
  rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, smul_eq_mul] at hint
  refine normalizedL2On_le_of_sq_le hM ?_
  unfold volumeAverage
  calc ((volume W).toReal)⁻¹ * ∫ x in W, f x ^ 2
      ≤ ((volume W).toReal)⁻¹ * ((volume W).toReal * M ^ 2) :=
        mul_le_mul_of_nonneg_left hint (le_of_lt (inv_pos.2 hW))
    _ = M ^ 2 := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hW), one_mul]

/-- An affine function is bounded on an axis-parallel cube, with an explicit bound. -/
theorem abs_affineEval_le_of_mem_axisCube {zout : Vec d} {Lout : ℝ} (hLout : 0 < Lout)
    (c : ℝ) (g : Vec d) {x : Vec d} (hx : x ∈ axisCube zout Lout) :
    |affineEval c g x| ≤ |c| + (d : ℝ) * (‖g‖ * (‖zout‖ + Lout)) := by
  have hxb : ∀ i, |x i| ≤ ‖zout‖ + Lout := by
    intro i
    have hmem := hx i (Set.mem_univ i)
    have hz : |zout i| ≤ ‖zout‖ := by
      have h := norm_le_pi_norm zout i
      rw [Real.norm_eq_abs] at h
      exact h
    obtain ⟨hz1, hz2⟩ := abs_le.1 hz
    rw [abs_le]
    exact ⟨by linarith only [hmem.1, hz1, hLout], by linarith only [hmem.2, hz2]⟩
  have hsum : |∑ i, g i * x i| ≤ (d : ℝ) * (‖g‖ * (‖zout‖ + Lout)) := by
    calc |∑ i, g i * x i| ≤ ∑ i, |g i * x i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, ‖g‖ * (‖zout‖ + Lout) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          have hgi : |g i| ≤ ‖g‖ := by
            have h := norm_le_pi_norm g i
            rw [Real.norm_eq_abs] at h
            exact h
          exact mul_le_mul hgi (hxb i) (abs_nonneg _) (norm_nonneg _)
      _ = (d : ℝ) * (‖g‖ * (‖zout‖ + Lout)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have heq : affineEval c g x = c + ∑ i, g i * x i := by
    rw [affineEval, vecDot]
  rw [heq]
  calc |c + ∑ i, g i * x i| ≤ |c| + |∑ i, g i * x i| := abs_add_le c _
    _ ≤ |c| + (d : ℝ) * (‖g‖ * (‖zout‖ + Lout)) := by linarith only [hsum]

/-- **`haff`: the affine functions are square-integrable on a bounded window.**  On a window
contained in a bounded cube every affine function is bounded, hence in `L²`.  This discharges the
`haff` hypothesis of `exists_isAffineMinimizer_of_nondegenerate`. -/
theorem memLp_affineEval_of_sandwich {W : Set (Vec d)} {zout : Vec d} {Lout : ℝ}
    (hLout : 0 < Lout) (hWm : MeasurableSet W) (hout : W ⊆ axisCube zout Lout)
    (c : ℝ) (g : Vec d) :
    MemLp (affineEval c g) 2 (volume.restrict W) := by
  have hfin : volume W ≠ ⊤ := volume_ne_top_of_sandwich hout
  have : IsFiniteMeasure (volume.restrict W) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hfin
  refine MemLp.of_bound (continuous_affineEval c g).aestronglyMeasurable
    (|c| + (d : ℝ) * (‖g‖ * (‖zout‖ + Lout))) ?_
  refine (ae_restrict_iff' hWm).2 (Filter.Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs]
  exact abs_affineEval_le_of_mem_axisCube hLout c g (hout hx)

/-! ### The two parameter-space constants -/

/-- The `hub` constant of a sandwich: `K = 1 + d(‖y‖ + Lout)` for the outer cube `y + □(Lout)`. -/
def ubConst (d : ℕ) (zout : Vec d) (Lout : ℝ) : ℝ := 1 + (d : ℝ) * (‖zout‖ + Lout)

/-- The `hlb` constant of a sandwich:
`c₀ = √((Lin/Lout)^d) · min(1, Lin/(2√3)) / (2(1 + |xin|))`, with `xin` the centre of the inner
cube.  Every factor is explicit: the volume ratio of the sandwich, the sharp cube constant
`1/(2√3)` from the second moment, and the recentring loss `1 + |xin|`. -/
def lbConst (d : ℕ) (zin : Vec d) (Lin Lout : ℝ) : ℝ :=
  Real.sqrt ((Lin / Lout) ^ d) * min 1 (Lin / (2 * Real.sqrt 3))
    / (2 * (1 + slopeMagnitude (axisCubeCenter zin Lin)))

theorem ubConst_nonneg {zout : Vec d} {Lout : ℝ} (hLout : 0 ≤ Lout) :
    0 ≤ ubConst d zout Lout := by
  have hz : (0 : ℝ) ≤ ‖zout‖ := norm_nonneg _
  rw [ubConst]
  positivity

theorem lbConst_pos {zin : Vec d} {Lin Lout : ℝ} (hLin : 0 < Lin) (hLout : 0 < Lout) :
    0 < lbConst d zin Lin Lout := by
  have hr : 0 < Real.sqrt ((Lin / Lout) ^ d) := Real.sqrt_pos.2 (pow_pos (div_pos hLin hLout) d)
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hm : 0 < min 1 (Lin / (2 * Real.sqrt 3)) := lt_min one_pos (by positivity)
  have hrho : 0 ≤ slopeMagnitude (axisCubeCenter zin Lin) := slopeMagnitude_nonneg _
  rw [lbConst]
  positivity

/-! ### `hub`: the affine evaluation map is bounded -/

/-- **`hub`.**  `‖c + g·x‖_{L²(W)} ≤ (1 + d(‖y‖ + Lout))·‖(c,g)‖` on a window
contained in the cube `y + □(Lout)` and containing a cube of positive side. -/
theorem normalizedL2On_affineEval_le_of_sandwich {W : Set (Vec d)} {zin zout : Vec d}
    {Lin Lout : ℝ} (hLin : 0 < Lin) (hLout : 0 < Lout) (hWm : MeasurableSet W)
    (hin : axisCube zin Lin ⊆ W) (hout : W ⊆ axisCube zout Lout) (c : ℝ) (g : Vec d) :
    normalizedL2On W (affineEval c g) ≤ ubConst d zout Lout * ‖((c, g) : ℝ × Vec d)‖ := by
  have hVpos : 0 < (volume W).toReal := volume_toReal_pos_of_sandwich hLin hin hout
  have hfin : volume W ≠ ⊤ := volume_ne_top_of_sandwich hout
  have hnormdef : ‖((c, g) : ℝ × Vec d)‖ = max |c| ‖g‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs]
  have hcn : |c| ≤ ‖((c, g) : ℝ × Vec d)‖ := by
    rw [hnormdef]
    exact le_max_left _ _
  have hgn : ‖g‖ ≤ ‖((c, g) : ℝ × Vec d)‖ := by
    rw [hnormdef]
    exact le_max_right _ _
  have hnn : 0 ≤ ‖((c, g) : ℝ × Vec d)‖ := norm_nonneg _
  have hR : (0 : ℝ) ≤ ‖zout‖ + Lout := by
    have hz : (0 : ℝ) ≤ ‖zout‖ := norm_nonneg _
    linarith only [hz, hLout]
  refine normalizedL2On_le_of_abs_le hWm hVpos hfin
    (mul_nonneg (ubConst_nonneg hLout.le) hnn)
    (integrableOn_affineEval_sq_of_sandwich hout c g) ?_
  intro x hx
  have hval : |affineEval c g x| ≤ |c| + (d : ℝ) * (‖g‖ * (‖zout‖ + Lout)) :=
    abs_affineEval_le_of_mem_axisCube hLout c g (hout hx)
  have hkey : (d : ℝ) * (‖g‖ * (‖zout‖ + Lout))
      ≤ (d : ℝ) * ((‖zout‖ + Lout) * ‖((c, g) : ℝ × Vec d)‖) := by
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
    rw [mul_comm ‖g‖]
    exact mul_le_mul_of_nonneg_left hgn hR
  have hexp : ubConst d zout Lout * ‖((c, g) : ℝ × Vec d)‖
      = ‖((c, g) : ℝ × Vec d)‖ + (d : ℝ) * ((‖zout‖ + Lout) * ‖((c, g) : ℝ × Vec d)‖) := by
    rw [ubConst]
    ring
  rw [hexp]
  linarith only [hval, hcn, hkey]

/-! ### `hlb`: the affine evaluation map is bounded below -/

/-- **`hlb`.**  `c₀ ‖(c,g)‖ ≤ ‖c + g·x‖_{L²(W)}` on a sandwiched window, with `c₀
= lbConst d zin Lin Lout > 0`.  Together with `hub` this says the affine
evaluation map is a linear isomorphism onto its image --- the nondegeneracy the
direct method needs.

Both cube inputs come from the exact second moment: `|c + g·x| ≤ ‖c + g·x‖_{L²(□in)}` and
`(Lin/(2√3))|g| ≤ ‖c + g·x‖_{L²(□in)}`. -/
theorem normalizedL2On_affineEval_ge_norm_of_sandwich {W : Set (Vec d)} {zin zout : Vec d}
    {Lin Lout : ℝ} (hLin : 0 < Lin) (hLout : 0 < Lout)
    (hin : axisCube zin Lin ⊆ W) (hout : W ⊆ axisCube zout Lout) (c : ℝ) (g : Vec d) :
    lbConst d zin Lin Lout * ‖((c, g) : ℝ × Vec d)‖ ≤ normalizedL2On W (affineEval c g) := by
  have hVpos : 0 < (volume W).toReal := volume_toReal_pos_of_sandwich hLin hin hout
  have hQinpos : 0 < (volume (axisCube zin Lin)).toReal := volume_axisCube_toReal_pos zin hLin
  have hr : 0 < Real.sqrt ((Lin / Lout) ^ d) := Real.sqrt_pos.2 (pow_pos (div_pos hLin hLout) d)
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  set xb : Vec d := axisCubeCenter zin Lin with hxb
  set A : ℝ := affineEval c g xb with hA
  set S : ℝ := slopeMagnitude g with hSdef
  set rho : ℝ := slopeMagnitude xb with hrho
  set NW : ℝ := normalizedL2On W (affineEval c g) with hNW
  set Nin : ℝ := normalizedL2On (axisCube zin Lin) (affineEval c g) with hNin
  set mc : ℝ := min 1 (Lin / (2 * Real.sqrt 3)) with hmc
  have hS0 : 0 ≤ S := slopeMagnitude_nonneg g
  have hrho0 : 0 ≤ rho := slopeMagnitude_nonneg _
  have hNW0 : 0 ≤ NW := normalizedL2On_nonneg _ _
  -- the two exact-cube lower bounds on the inner cube
  have hb1 : |A| ≤ Nin := abs_le_normalizedL2On_axisCube_affineEval zin hLin c g
  have hb2 : Lin / (2 * Real.sqrt 3) * S ≤ Nin :=
    normalizedL2On_axisCube_affineEval_ge zin hLin c g
  -- the parameter norm is controlled by `|A|` and `S`
  have hnormdef : ‖((c, g) : ℝ × Vec d)‖ = max |c| ‖g‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs]
  have hcA : |c| ≤ |A| + rho * S := by
    have hc : c = A - vecDot g xb := by
      rw [hA, affineEval]
      ring
    have hdot : |vecDot g xb| ≤ S * rho := abs_vecDot_le_slopeMagnitude_mul g xb
    rw [hc]
    calc |A - vecDot g xb| = |A + -vecDot g xb| := by rw [sub_eq_add_neg]
      _ ≤ |A| + |-vecDot g xb| := abs_add_le _ _
      _ = |A| + |vecDot g xb| := by rw [abs_neg]
      _ ≤ |A| + rho * S := by
          rw [mul_comm rho S]
          linarith only [hdot]
  have hgS : ‖g‖ ≤ S := norm_le_slopeMagnitude g
  have hnorm : ‖((c, g) : ℝ × Vec d)‖ ≤ (1 + rho) * (|A| + S) := by
    have hprod : 0 ≤ rho * |A| := mul_nonneg hrho0 (abs_nonneg A)
    have hprod2 : 0 ≤ rho * S := mul_nonneg hrho0 hS0
    have hA0 : 0 ≤ |A| := abs_nonneg A
    have hexp : (1 + rho) * (|A| + S) = |A| + S + rho * |A| + rho * S := by ring
    have h1 : |c| ≤ |A| + S + rho * |A| + rho * S := by
      linarith only [hcA, hprod, hS0]
    have h2 : ‖g‖ ≤ |A| + S + rho * |A| + rho * S := by
      linarith only [hgS, hprod, hprod2, hA0]
    rw [hnormdef, hexp]
    exact max_le h1 h2
  -- the two cube bounds combine into a bound on `|A| + S`
  have hmin1 : mc ≤ 1 := min_le_left _ _
  have hmin2 : mc ≤ Lin / (2 * Real.sqrt 3) := min_le_right _ _
  have hmin0 : 0 < mc := lt_min one_pos (by positivity)
  have hcube : mc * (|A| + S) ≤ 2 * Nin := by
    have ha1 : mc * |A| ≤ 1 * |A| := mul_le_mul_of_nonneg_right hmin1 (abs_nonneg A)
    have ha2 : mc * S ≤ Lin / (2 * Real.sqrt 3) * S := mul_le_mul_of_nonneg_right hmin2 hS0
    have hexp : mc * (|A| + S) = mc * |A| + mc * S := by ring
    rw [hexp]
    linarith only [ha1, ha2, hb1, hb2]
  -- transfer from the inner cube to `W`
  have hchain : Nin ≤ (Real.sqrt ((Lin / Lout) ^ d))⁻¹ * NW := by
    have hsub : Nin ≤ Real.sqrt ((volume W).toReal / (volume (axisCube zin Lin)).toReal) * NW :=
      normalizedL2On_le_of_subset hin hVpos hQinpos
        (integrableOn_affineEval_sq_of_sandwich hout c g)
    have hratio : Real.sqrt ((volume W).toReal / (volume (axisCube zin Lin)).toReal)
        ≤ (Real.sqrt ((Lin / Lout) ^ d))⁻¹ :=
      sqrt_volume_ratio_inner_le (zin := zin) hLin hLout hout
    exact hsub.trans (mul_le_mul_of_nonneg_right hratio hNW0)
  -- assemble
  have hkey : mc * ‖((c, g) : ℝ × Vec d)‖
      ≤ 2 * (1 + rho) * ((Real.sqrt ((Lin / Lout) ^ d))⁻¹ * NW) := by
    calc mc * ‖((c, g) : ℝ × Vec d)‖
        ≤ mc * ((1 + rho) * (|A| + S)) := mul_le_mul_of_nonneg_left hnorm hmin0.le
      _ = (1 + rho) * (mc * (|A| + S)) := by ring
      _ ≤ (1 + rho) * (2 * Nin) :=
          mul_le_mul_of_nonneg_left hcube (by linarith only [hrho0])
      _ ≤ (1 + rho) * (2 * ((Real.sqrt ((Lin / Lout) ^ d))⁻¹ * NW)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hchain (by norm_num)) (by linarith only [hrho0])
      _ = 2 * (1 + rho) * ((Real.sqrt ((Lin / Lout) ^ d))⁻¹ * NW) := by ring
  have hpos : 0 < 2 * (1 + rho) := by linarith only [hrho0]
  have hid : Real.sqrt ((Lin / Lout) ^ d)
      * (2 * (1 + rho) * ((Real.sqrt ((Lin / Lout) ^ d))⁻¹ * NW))
      = NW * (2 * (1 + rho)) := by
    rw [show Real.sqrt ((Lin / Lout) ^ d)
        * (2 * (1 + rho) * ((Real.sqrt ((Lin / Lout) ^ d))⁻¹ * NW))
        = (Real.sqrt ((Lin / Lout) ^ d) * (Real.sqrt ((Lin / Lout) ^ d))⁻¹)
            * (2 * (1 + rho) * NW) by ring,
      mul_inv_cancel₀ (ne_of_gt hr), one_mul]
    ring
  rw [lbConst, ← hxb, ← hrho, ← hmc, div_mul_eq_mul_div, div_le_iff₀ hpos]
  calc Real.sqrt ((Lin / Lout) ^ d) * mc * ‖((c, g) : ℝ × Vec d)‖
      = Real.sqrt ((Lin / Lout) ^ d) * (mc * ‖((c, g) : ℝ × Vec d)‖) := by ring
    _ ≤ Real.sqrt ((Lin / Lout) ^ d)
        * (2 * (1 + rho) * ((Real.sqrt ((Lin / Lout) ^ d))⁻¹ * NW)) :=
          mul_le_mul_of_nonneg_left hkey hr.le
    _ = NW * (2 * (1 + rho)) := hid

/-! ### Attainment on the consumption class -/

/-- **Attainment on a window sandwiched between two axis-parallel cubes.**  The infimum defining
`affineExcessRaw W u` is a minimum: some affine parameter pair is an `IsAffineMinimizer`.

This is `exists_isAffineMinimizer_of_nondegenerate` with all three of its analytic inputs
discharged from the sandwich geometry, at the explicit constants `lbConst` and `ubConst`. -/
theorem exists_isAffineMinimizer_of_axisCubeSandwich {W : Set (Vec d)} {zin zout : Vec d}
    {Lin Lout : ℝ} (hLin : 0 < Lin) (hLout : 0 < Lout) (hWm : MeasurableSet W)
    (hin : axisCube zin Lin ⊆ W) (hout : W ⊆ axisCube zout Lout)
    (u : Vec d → ℝ) (hu : MemLp u 2 (volume.restrict W)) :
    ∃ (c : ℝ) (g : Vec d), IsAffineMinimizer W u c g :=
  exists_isAffineMinimizer_of_nondegenerate (c₀ := lbConst d zin Lin Lout)
    (K := ubConst d zout Lout) (lbConst_pos hLin hLout)
    (fun c g => memLp_affineEval_of_sandwich hLout hWm hout c g)
    (fun c g => normalizedL2On_affineEval_ge_norm_of_sandwich hLin hLout hin hout c g)
    (fun c g => normalizedL2On_affineEval_le_of_sandwich hLin hLout hWm hin hout c g) u hu

end

end Algsuperdiff.Section4.Provider.ExcessDecay
