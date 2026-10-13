/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryLaneWindows
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.AffineExcess
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ClassicalGradient
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# AffineSplitLift

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The affine lift `ℓ_h` of the boundary datum, and its residual

The boundary lane of §4.3 replaces the printed odd-reflection Schauder step by
the *affine split* `v = v₀ + w + ℓ_h` of the replacement draft's item 2
(`l.comparison.reduction`).  The affine lift is

```text
  ∇ℓ_h := (∇h)_{W_0} ,     ℓ_h(x) = h(x) ,        W_0 := (x + □_n) ∩ □_m ,
```

and the whole point of the device is that the residual `h - ℓ_h` is controlled
on `W_0` by the **`C^{0,1/2}` seminorm of `∇h`** — the leg the frozen theorem's
general clause keeps (`e.data.residual` of the draft):

```text
  ‖h - ℓ_h‖_{L^∞(W_0)} ≤ diam(W_0) · osc_{W_0} ∇h ≤ C(d) 3^{3n/2} [∇h]_{C^{0,1/2}(W_0)} .
```

This module proves that display, with `C(d) = 2d` at the sup-metric diameter,
together with the `H¹` realization of `ℓ_h` and the two elementary inputs (the
slope functional and the deviation of a volume average from a pointwise value).

## The dimensional constant, honestly

`Vec d` carries the **supremum** norm, so a slope `A` acts as a functional of
operator norm `∑_i |A_i| ≤ d ‖A‖`.  That is the only source of the factor `d`
in `abs_sub_affineLift_le`, and it is exactly the sup-vs-`ℓ¹` conversion the
manuscript hides in its `C(d)`.

## What is not done here

* No maximum principle: the passage from `‖h - ℓ_h‖_{L^∞(∂V ∩ ∂□_m)}` to
  `‖w‖_{L^∞(V)}` is a separate obligation (draft item 2(ii), first inequality).
* No harmonic function of any kind appears.
* `HasGradientOn` (now `Algsuperdiff.Section4.Support.HasGradientOn`, imported
  from `Support/ClassicalGradient.lean`) is the **classical** `C^1` half of the
  source hypothesis `h ∈ C^{1,1/2}(□_m)`; it is a genuine premise of the pinned
  statement, not a proof step promoted to a hypothesis.

## References

* ABK26, `l.excess.decay.good.scales`, (datum).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The slope functional

`slopeCLM` and its `@[simp]` application lemma now live in
`Algsuperdiff/Section4/Support/ClassicalGradient.lean` (the Support-layer home
a frozen root anchor can bind); this module consumes them through `open
Algsuperdiff.Section4.Support`.  Only the norm estimates specific to the
affine-split lane stay here. -/

theorem slopeCLM_sub (A B : Vec d) : slopeCLM A - slopeCLM B = slopeCLM (A - B) := by
  ext v
  simp only [sub_apply, slopeCLM_apply, vecDot, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The operator norm of the slope functional is at most `d ‖A‖`: the sup-norm
of `Vec d` dualizes to `ℓ¹`. -/
theorem norm_slopeCLM_le (A : Vec d) : ‖slopeCLM A‖ ≤ (d : ℝ) * ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Nat.cast_nonneg d) (norm_nonneg A)) fun v => ?_
  rw [slopeCLM_apply, Real.norm_eq_abs, vecDot]
  calc
    |∑ i : Fin d, A i * v i| ≤ ∑ i : Fin d, |A i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖A‖ * ‖v‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (by simpa using norm_le_pi_norm A i)
          (by simpa using norm_le_pi_norm v i) (abs_nonneg _) (norm_nonneg A)
    _ = (d : ℝ) * ‖A‖ * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem norm_slopeCLM_sub_le {G A : Vec d} {K : ℝ} (h : ‖G - A‖ ≤ K) :
    ‖slopeCLM G - slopeCLM A‖ ≤ (d : ℝ) * K := by
  rw [slopeCLM_sub]
  refine (norm_slopeCLM_le (G - A)).trans ?_
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg d)

/-! ## 2. The affine lift -/

/-- **The affine lift** `ℓ(y) = c + A · (y - x)`: the affine function with slope
`A` taking the value `c` at `x`.  With `c = h(x)` and `A = (∇h)_{W_0}` this is
`ℓ_h` of the draft's `e.data.affine`. -/
def affineLift (x : Vec d) (c : ℝ) (A : Vec d) : Vec d → ℝ :=
  fun y => c + vecDot A (y - x)

theorem vecDot_sub_right (A y x : Vec d) :
    vecDot A (y - x) = vecDot A y - vecDot A x := by
  simp only [vecDot, Pi.sub_apply]
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The affine lift is an affine function in the sense of `Support.AffineExcess`:
it is `affineEval` at intercept `c - A · x` and slope `A`. -/
theorem affineLift_eq_affineEval (x : Vec d) (c : ℝ) (A : Vec d) :
    affineLift x c A = affineEval (c - vecDot A x) A := by
  funext y
  rw [affineLift, affineEval, vecDot_sub_right]
  ring

@[simp] theorem affineLift_self (x : Vec d) (c : ℝ) (A : Vec d) :
    affineLift x c A x = c := by
  rw [affineLift, sub_self]
  simp [vecDot]

/-- The `H¹` realization of the affine lift on a Sobolev-regular domain. -/
def affineLiftH1 {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U) (x : Vec d) (c : ℝ) (A : Vec d) :
    H1Function U :=
  (H1Function.affineOnIsSobolevRegularDomain hU A).addConst (c - vecDot A x)

@[simp] theorem affineLiftH1_toFun {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] (hU : IsSobolevRegularDomain U)
    (x : Vec d) (c : ℝ) (A : Vec d) :
    (affineLiftH1 hU x c A).toFun = affineLift x c A := by
  funext y
  rw [affineLift, affineLiftH1]
  show (H1Function.affineOnIsSobolevRegularDomain hU A) y + (c - vecDot A x) = _
  rw [H1Function.affineOnIsSobolevRegularDomain_apply, vecDot_sub_right]
  show (∑ i : Fin d, A i * y i) + (c - vecDot A x) = c + (vecDot A y - vecDot A x)
  rw [show vecDot A y = ∑ i : Fin d, A i * y i from rfl]
  ring

@[simp] theorem affineLiftH1_grad {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] (hU : IsSobolevRegularDomain U)
    (x : Vec d) (c : ℝ) (A : Vec d) (y : Vec d) :
    (affineLiftH1 hU x c A).grad y = A := by
  rw [affineLiftH1, H1Function.grad_addConst,
    H1Function.affineOnIsSobolevRegularDomain_grad]

/-! ## 3. The classical `C¹` carrier

`HasGradientOn` — the classical `C¹` half of the source hypothesis `h ∈
C^{1,1/2}(□_m)`, written against `Vec d`'s sup-norm through `slopeCLM` — now lives
in `Algsuperdiff/Section4/Support/ClassicalGradient.lean` and is used here
through `open Algsuperdiff.Section4.Support`. -/

/-! ## 4. The mean-value residual -/

/-- **The affine-lift residual, at an arbitrary slope.**

If `f` is differentiable on the convex window `W` with gradient field `G`, and
`G` stays within `K` of the slope `A` on `W`, then `f` differs from its affine
lift at `x` by at most `d·K·r` on a window of sup-radius `r` around `x`.  This
is the mean-value inequality of the draft's `e.data.residual` computation. -/
theorem abs_sub_affineLift_le {W : Set (Vec d)} {f : Vec d → ℝ} {G : Vec d → Vec d}
    {A : Vec d} {K r : ℝ} {x y : Vec d} (hW : Convex ℝ W) (hx : x ∈ W) (hy : y ∈ W)
    (hK : 0 ≤ K) (hf : HasGradientOn W f G) (hG : ∀ p ∈ W, ‖G p - A‖ ≤ K)
    (hr : ‖y - x‖ ≤ r) :
    |f y - affineLift x (f x) A y| ≤ (d : ℝ) * K * r := by
  have hmv : ‖f y - f x - slopeCLM A (y - x)‖ ≤ (d : ℝ) * K * ‖y - x‖ :=
    hW.norm_image_sub_le_of_norm_hasFDerivWithin_le' hf
      (fun p hp => norm_slopeCLM_sub_le (hG p hp)) hx hy
  have hdK : (0 : ℝ) ≤ (d : ℝ) * K := mul_nonneg (Nat.cast_nonneg d) hK
  have heq : f y - affineLift x (f x) A y = f y - f x - slopeCLM A (y - x) := by
    rw [affineLift, slopeCLM_apply]
    ring
  rw [heq, ← Real.norm_eq_abs]
  exact hmv.trans (mul_le_mul_of_nonneg_left hr hdK)

/-! ## 5. The volume average as a slope -/

/-- Gradient coordinates of an `H¹` function are integrable on the domain. -/
theorem integrableOn_grad_coord {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] (u : H1Function U) (i : Fin d) :
    IntegrableOn (fun y => u.grad y i) U volume := by
  simpa [IntegrableOn, volumeMeasureOn] using
    (u.gradMemL2 i).integrable (by norm_num : (1 : ENNReal) ≤ 2)

/-- **The average slope is an admissible base point.**

If `G` stays within `K` of a vector `A` on a window of positive finite volume,
then so does its volume average.  With `A = G x` this is the step
`|(∇h)_{W_0} - ∇h(x)| ≤ osc_{W_0} ∇h` of the draft's residual computation. -/
theorem norm_volumeAverageVec_sub_le {W : Set (Vec d)} {G : Vec d → Vec d}
    {A : Vec d} {K : ℝ} (hvolpos : 0 < volume W) (hvoltop : volume W < ⊤)
    (hint : ∀ i, IntegrableOn (fun y => G y i) W volume) (hK : 0 ≤ K)
    (hG : ∀ y ∈ W, ‖G y - A‖ ≤ K) :
    ‖volumeAverageVec W G - A‖ ≤ K := by
  have hvolreal : 0 < (volume W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hvolpos) (ne_of_lt hvoltop)
  refine (pi_norm_le_iff_of_nonneg hK).2 fun i => ?_
  have hIA : IntegrableOn (fun _ : Vec d => A i) W volume := by
    have : IsFiniteMeasure (volume.restrict W) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hvoltop⟩
    exact integrable_const _
  have hsplit : ∫ y in W, (G y i - A i) ∂volume =
      (∫ y in W, G y i ∂volume) - (volume W).toReal * A i := by
    rw [integral_sub (hint i) hIA, setIntegral_const, smul_eq_mul, measureReal_def]
  have hbound : ‖∫ y in W, (G y i - A i) ∂volume‖ ≤ K * (volume W).toReal := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := W)
      (f := fun y => G y i - A i) (C := K) hvoltop ?_
    · simpa [measureReal_def] using this
    · intro y hy
      refine le_trans ?_ (hG y hy)
      simpa using norm_le_pi_norm (G y - A) i
  rw [hsplit] at hbound
  have hcoord : (volumeAverageVec W G - A) i =
      (volume W).toReal⁻¹ * ((∫ y in W, G y i ∂volume) - (volume W).toReal * A i) := by
    show volumeAverage W (fun y => G y i) - A i = _
    rw [volumeAverage]
    field_simp
  rw [hcoord, Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_of_lt (inv_pos.2 hvolreal))]
  rw [← Real.norm_eq_abs]
  calc
    (volume W).toReal⁻¹ * ‖(∫ y in W, G y i ∂volume) - (volume W).toReal * A i‖
        ≤ (volume W).toReal⁻¹ * (K * (volume W).toReal) :=
          mul_le_mul_of_nonneg_left hbound (le_of_lt (inv_pos.2 hvolreal))
    _ = K := by field_simp

/-! ## 6. The residual of the boundary datum's affine lift -/

private theorem rpow_half_mul_self {r : ℝ} (hr : 0 ≤ r) :
    r ^ (1 / 2 : ℝ) * r = r ^ (3 / 2 : ℝ) := by
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · rw [← hr0, Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num), mul_zero]
  · calc
      r ^ (1 / 2 : ℝ) * r = r ^ (1 / 2 : ℝ) * r ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = r ^ ((1 / 2 : ℝ) + (1 : ℝ)) := (Real.rpow_add hrpos _ _).symm
      _ = r ^ (3 / 2 : ℝ) := by norm_num

/-- **The residual bound `e.data.residual`.**

On a convex window `W` of sup-radius `r` around `x`, with `f = h` of class
`C^{1,1/2}` (gradient field `G`, Hölder constant `K`), the affine lift at the
**average slope** `(∇h)_W` satisfies

```text
  |h(y) - ℓ_h(y)| ≤ 2 d K r^{3/2}      for every y ∈ W .
```

At `W = (x+□_n) ∩ □_m` and `r = 3^n/2` this is the draft's `‖h -
ℓ_h‖_{L^∞(W_0)} ≤ C(d) 3^{3n/2} [∇h]_{C^{0,1/2}(W_0)}`, and it is the leg that
the frozen theorem's general clause pays through its `‖(∇h)_W‖` slot. -/
theorem abs_sub_affineLift_volumeAverage_le {W : Set (Vec d)} {f : Vec d → ℝ}
    {G : Vec d → Vec d} {K r : ℝ} {x y : Vec d} (hW : Convex ℝ W) (hx : x ∈ W)
    (hy : y ∈ W) (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hvolpos : 0 < volume W)
    (hvoltop : volume W < ⊤) (hint : ∀ i, IntegrableOn (fun p => G p i) W volume)
    (hf : HasGradientOn W f G) (hG : HolderSeminormBoundOn W (1 / 2 : ℝ) K G)
    (hdiam : ∀ p ∈ W, ‖p - x‖ ≤ r) :
    |f y - affineLift x (f x) (volumeAverageVec W G) y| ≤
      2 * (d : ℝ) * K * r ^ (3 / 2 : ℝ) := by
  have hKr : 0 ≤ K * r ^ (1 / 2 : ℝ) :=
    mul_nonneg hK (Real.rpow_nonneg hr0 _)
  have hbase : ∀ p ∈ W, ‖G p - G x‖ ≤ K * r ^ (1 / 2 : ℝ) := by
    intro p hp
    refine (hG p hp x hx).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (hdiam p hp) (by norm_num)) hK
  have havg : ‖volumeAverageVec W G - G x‖ ≤ K * r ^ (1 / 2 : ℝ) :=
    norm_volumeAverageVec_sub_le hvolpos hvoltop hint hKr hbase
  have hslope : ∀ p ∈ W, ‖G p - volumeAverageVec W G‖ ≤ 2 * (K * r ^ (1 / 2 : ℝ)) := by
    intro p hp
    have htri : ‖G p - volumeAverageVec W G‖ ≤
        ‖G p - G x‖ + ‖G x - volumeAverageVec W G‖ := by
      simpa using norm_sub_le_norm_sub_add_norm_sub (G p) (G x) (volumeAverageVec W G)
    have hsymm : ‖G x - volumeAverageVec W G‖ = ‖volumeAverageVec W G - G x‖ :=
      norm_sub_rev _ _
    rw [hsymm] at htri
    linarith only [htri, hbase p hp, havg]
  have hmain := abs_sub_affineLift_le (f := f) (G := G)
    (A := volumeAverageVec W G) hW hx hy (by linarith only [hKr] : (0:ℝ) ≤ 2 * (K * r ^ (1/2:ℝ)))
    hf hslope (hdiam y hy)
  refine hmain.trans (le_of_eq ?_)
  rw [← rpow_half_mul_self hr0]
  ring

/-! ## 7. The window instantiation -/

/-- Points of a truncated window are within sup-distance `3^k/2` of its centre. -/
theorem norm_sub_le_of_mem_truncatedWindow {x p : Vec d} {m k : ℤ}
    (hp : p ∈ truncatedWindow x m k) : ‖p - x‖ ≤ (3 : ℝ) ^ k / 2 := by
  obtain ⟨y, hy, hpy⟩ := hp.1
  have hpx : p - x = y := by
    rw [← hpy]
    exact add_sub_cancel_left x y
  rw [hpx]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [mem_openCubeSet_originCube_iff] at hy
  have h := hy i
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith only [h.1, h.2]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
