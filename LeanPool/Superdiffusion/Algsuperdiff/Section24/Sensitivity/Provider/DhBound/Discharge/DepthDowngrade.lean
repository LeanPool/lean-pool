/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Besov.Perturbation
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.MultiscalePoincare
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarseCaccioppoliRHS.ZeroTraceValue
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.CutoffProduct.PositiveSeminorms.Bounds
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfacesComponentwise

/-!
# DepthDowngrade

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# From the `ℓ^∞`-over-depths multiscale Poincaré estimate to the `ℓ²` one

Source: ABK26 (`l.Besov.grad.to.function`,
`e.v.in.Bpps.vs.nabla.v.in.B.pp.minus.t`) as consumed at `e.split.besov.stuff`
inside the proof of `l.Dh.bound`.

CoarseGraining proves the function-from-gradient comparison with an
`ℓ^∞`-over-depths left hand side,
`Book.Ch01.Legacy.h1_fluctuation_partialNormTop_two_le_sum_grad_circNorm`:

```
‖ fluct u ‖_{B^{s}_{2,∞}(Q), M} ≤ C(d,Q) ∑_i [∂_i u]^{circ}_{B^{-(1-s)}_{2,1}(Q)} .
```

The Besov product estimate of `Provider.DhBound.Besov.Product` consumes instead
the `ℓ²`-over-depths seminorm `[u]_{B^{3/8}_{2,2}(Q), N}`.  The two are related
by summing a geometric series: at any two exponents `s < t`,

```
[u]^{+}_{B^{s}_{2,2}(Q), N} ≤ (1 - 3^{-2(t-s)})^{-1/2} 3^{t·scale} ‖u‖_{B^{t}_{2,∞}(Q), N},
```

because the depth-`j` contributions at the two exponents differ exactly by the
factor `3^{(s-t)j}`.

The consuming instance is `s = 3/8`, `t = 1/2`; the gradient side then sits at
`-(1 - 1/2) = -1/2`, which is downgraded to the gauge exponent `-3/8` by the
CoarseGraining circ comparison
`cubeBesovCircNorm_two_one_component_le_scaleWeight_neg_mul_gap_geometric_of_bddAbove`
(gap `1/2 - 3/8 = 1/8 > 0`).

The depth-level extraction step (`3^{-t·scale} [u]^{+}_{depth j, t} ≤
‖u‖_{B^{t}_{2,∞}, M}` for `j ≤ M`) exists in CoarseGraining only as a `private`
lemma of `Book/Ch01/Theorems/CutoffProduct.lean`; it is re-proved here from the
public
`cubeBesovPositiveScalarDepthSeminorm_eq_scaleWeight_neg_mul_cubeBesovDepthSeminorm_two`
and `Finset.le_sup'`.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Besov
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- CoarseGraining writes the triadic weights with explicit `Real.rpow`; Mathlib's
`^`-notation lemmas do not rewrite against it. -/
private theorem rpow_eq_pow (x y : ℝ) : Real.rpow x y = x ^ y := rfl

/-! ## Exponent conversion at a fixed depth -/

/-- Exact depthwise conversion between two positive-Besov exponents. -/
theorem cubeBesovPositiveScalarDepthSeminorm_eq_gap_mul (Q : TriadicCube d)
    (a b : ℝ) (v : Vec d → ℝ) (j : ℕ) :
    cubeBesovPositiveScalarDepthSeminorm Q a v j =
      Real.rpow (3 : ℝ) ((a - b) * (j : ℝ)) *
        cubeBesovPositiveScalarDepthSeminorm Q b v j := by
  unfold cubeBesovPositiveScalarDepthSeminorm
  rw [← mul_assoc]
  congr 1
  simp only [rpow_eq_pow]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-! ## Depth-level extraction from the `ℓ^∞` norm -/

theorem cubeBesovPartialNormTop_nonneg (Q : TriadicCube d) (s : ℝ) (M : ℕ)
    (v : Vec d → ℝ) :
    0 ≤ cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M v := by
  unfold cubeBesovPartialNormTop cubeBesovPartialSeminormTop
  refine add_nonneg ?_ (mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (norm_nonneg _))
  refine le_trans (cubeBesovDepthSeminorm_nonneg Q s (2 : ℝ≥0∞) v 0) ?_
  exact Finset.le_sup' (f := fun k => cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v k)
    (by simp)

/-- **Depth-level extraction.**  Local re-proof of the CoarseGraining private lemma
`Book.Ch01.Legacy.cubeBesovScaleWeight_mul_positiveScalarDepthSeminorm_le_partialNormTop`,
in the divided form used below. -/
theorem cubeBesovPositiveScalarDepthSeminorm_le_scaleWeight_neg_mul_partialNormTop
    (Q : TriadicCube d) (s : ℝ) (M j : ℕ) (v : Vec d → ℝ)
    (hj : j ∈ Finset.range (M + 1)) :
    cubeBesovPositiveScalarDepthSeminorm Q s v j ≤
      cubeBesovScaleWeight (-s) Q * cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M v := by
  rw [cubeBesovPositiveScalarDepthSeminorm_eq_scaleWeight_neg_mul_cubeBesovDepthSeminorm_two]
  refine mul_le_mul_of_nonneg_left ?_ (cubeBesovScaleWeight_nonneg (-s) Q)
  calc
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v j
        ≤ cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) M v := by
          unfold cubeBesovPartialSeminormTop
          exact Finset.le_sup'
            (f := fun k => cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v k) hj
    _ ≤ cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M v := by
          unfold cubeBesovPartialNormTop
          exact le_add_of_nonneg_right
            (mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (norm_nonneg _))

/-! ## The `ℓ^∞ → ℓ²` downgrade -/

/-- **The `ℓ^∞`-to-`ℓ²` positive Besov downgrade.**  At any two exponents
`s < t`, the finite-depth `ℓ²` positive seminorm at `s` is controlled by the
finite-depth `ℓ^∞` norm at `t`, with the geometric loss of the exponent gap. -/
theorem cubeBesovPositiveScalarPartialSeminormTwo_le_gap_geometric_mul_partialNormTop
    (Q : TriadicCube d) {s t : ℝ} (hst : s < t) (M : ℕ) (v : Vec d → ℝ) :
    cubeBesovPositiveScalarPartialSeminormTwo Q s M v ≤
      Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * (t - s)))⁻¹) *
        (cubeBesovScaleWeight (-t) Q *
          cubeBesovPartialNormTop Q t (2 : ℝ≥0∞) M v) := by
  classical
  set T : ℝ := cubeBesovScaleWeight (-t) Q *
    cubeBesovPartialNormTop Q t (2 : ℝ≥0∞) M v with hT
  have hTnn : 0 ≤ T := by
    rw [hT]
    exact mul_nonneg (cubeBesovScaleWeight_nonneg (-t) Q)
      (cubeBesovPartialNormTop_nonneg Q t M v)
  -- the geometric sum
  have hgeom :
      (∑ j ∈ Finset.range (M + 1),
          (Real.rpow (3 : ℝ) ((s - t) * (j : ℝ))) ^ 2) ≤
        (1 - Real.rpow (3 : ℝ) (-2 * (t - s)))⁻¹ := by
    have hrewrite :
        (∑ j ∈ Finset.range (M + 1),
            (Real.rpow (3 : ℝ) ((s - t) * (j : ℝ))) ^ 2) =
          ∑ j ∈ Finset.range (M + 1),
            Real.rpow (3 : ℝ) (-(2 * (t - s)) * (j : ℝ)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [rpow_eq_pow]
      rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    rw [hrewrite]
    simpa using
      (sum_filter_triadicDepthWeight_le_geometric_inv (2 * (t - s)) M
        (fun _ : ℕ => True) (by linarith))
  -- the depthwise bound
  have hdepth : ∀ j ∈ Finset.range (M + 1),
      (cubeBesovPositiveScalarDepthSeminorm Q s v j) ^ 2 ≤
        (Real.rpow (3 : ℝ) ((s - t) * (j : ℝ))) ^ 2 * T ^ 2 := by
    intro j hj
    have hw : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((s - t) * (j : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hb : cubeBesovPositiveScalarDepthSeminorm Q t v j ≤ T :=
      cubeBesovPositiveScalarDepthSeminorm_le_scaleWeight_neg_mul_partialNormTop
        Q t M j v hj
    have hbnn : 0 ≤ cubeBesovPositiveScalarDepthSeminorm Q t v j :=
      cubeBesovPositiveScalarDepthSeminorm_nonneg Q t v j
    have heq := cubeBesovPositiveScalarDepthSeminorm_eq_gap_mul Q s t v j
    rw [heq, mul_pow]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (pow_nonneg hw 2)
  have hsum :
      (∑ j ∈ Finset.range (M + 1),
          (cubeBesovPositiveScalarDepthSeminorm Q s v j) ^ 2) ≤
        (1 - Real.rpow (3 : ℝ) (-2 * (t - s)))⁻¹ * T ^ 2 := by
    calc
      (∑ j ∈ Finset.range (M + 1),
            (cubeBesovPositiveScalarDepthSeminorm Q s v j) ^ 2)
          ≤ ∑ j ∈ Finset.range (M + 1),
              (Real.rpow (3 : ℝ) ((s - t) * (j : ℝ))) ^ 2 * T ^ 2 :=
            Finset.sum_le_sum hdepth
      _ = (∑ j ∈ Finset.range (M + 1),
              (Real.rpow (3 : ℝ) ((s - t) * (j : ℝ))) ^ 2) * T ^ 2 := by
            rw [Finset.sum_mul]
      _ ≤ (1 - Real.rpow (3 : ℝ) (-2 * (t - s)))⁻¹ * T ^ 2 :=
            mul_le_mul_of_nonneg_right hgeom (sq_nonneg T)
  have hGnn : (0 : ℝ) ≤ (1 - Real.rpow (3 : ℝ) (-2 * (t - s)))⁻¹ := by
    have hlt : Real.rpow (3 : ℝ) (-2 * (t - s)) < 1 := by
      simp only [rpow_eq_pow]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact le_of_lt (inv_pos.mpr (by linarith))
  unfold cubeBesovPositiveScalarPartialSeminormTwo
  refine (Real.sqrt_le_sqrt hsum).trans (le_of_eq ?_)
  rw [Real.sqrt_mul hGnn, Real.sqrt_sq hTnn]

/-! ## The origin-cube consumer at the sensitivity exponents -/

/-- The geometric loss of the `1/2 → 3/8` exponent gap. -/
def sensitivityGapConst : ℝ :=
  Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 3 / 8)))⁻¹)

theorem sensitivityGapConst_nonneg : 0 ≤ sensitivityGapConst :=
  Real.sqrt_nonneg _

/-- The explicit constant of the origin-cube function-from-gradient estimate at
the sensitivity exponents. -/
def depthDowngradeConst (d : ℕ) : ℝ :=
  sensitivityGapConst *
    ((Ch01.Legacy.fullVectorPoincareConstant (originCube d 0) * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((d : ℝ) * sensitivityGapConst))

/-- The componentwise circ norm of the gradient, at the exponent produced by the
multiscale Poincaré estimate, is controlled by the gauge-exponent negative
seminorm of the full gradient. -/
theorem cubeBesovCircNorm_half_grad_originCube_le
    (G : Vec d → Vec d) (i : Fin d)
    (hBdd : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo (originCube d 0) (3 / 8) N G)) :
    cubeBesovCircNorm (originCube d 0) (1 / 2 : ℝ) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => G x i) ≤
      sensitivityGapConst *
        cubeBesovNegativeVectorSeminormTwo (originCube d 0) (3 / 8) G := by
  have h :=
    cubeBesovCircNorm_two_one_component_le_scaleWeight_neg_mul_gap_geometric_of_bddAbove
      (Q := originCube d 0) (a := (1 / 2 : ℝ)) (b := (3 / 8 : ℝ)) (by norm_num)
      G i hBdd
  rwa [cubeBesovScaleWeight_originCube_zero, one_mul] at h

/-- **The origin-cube function-from-gradient estimate in the `ℓ²` form.** -/
theorem cubeBesovPositiveScalarPartialSeminormTwo_h1_originCube_le [NeZero d]
    (M : ℕ) (u : H1Function (openCubeSet (originCube d 0)))
    (hBdd : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo (originCube d 0) (3 / 8) N
        (fun x => u.grad x))) :
    cubeBesovPositiveScalarPartialSeminormTwo (originCube d 0) (3 / 8) M
        (fun x => u x) ≤
      depthDowngradeConst d *
        cubeBesovNegativeVectorSeminormTwo (originCube d 0) (3 / 8)
          (fun x => u.grad x) := by
  classical
  -- Step 1: the `ℓ∞ → ℓ²` downgrade for the fluctuation
  have hdown :=
    cubeBesovPositiveScalarPartialSeminormTwo_le_gap_geometric_mul_partialNormTop
      (originCube d 0) (s := (3 / 8 : ℝ)) (t := (1 / 2 : ℝ)) (by norm_num) M
      (cubeFluctuation (originCube d 0) (fun x => u x))
  rw [cubeBesovScaleWeight_originCube_zero, one_mul] at hdown
  -- Step 2: the fluctuation has the same positive seminorm
  have hmem : ∀ j ∈ Finset.range (M + 1),
      ∀ R ∈ descendantsAtDepth (originCube d 0) j,
      MemLp (fun x => u x) (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
    intro j _ R hR
    exact memLp_on_descendant_of_memLp_generic hR u.memL2_normalizedCubeMeasure
  have hfluct :
      cubeBesovPositiveScalarPartialSeminormTwo (originCube d 0) (3 / 8) M
          (cubeFluctuation (originCube d 0) (fun x => u x)) =
        cubeBesovPositiveScalarPartialSeminormTwo (originCube d 0) (3 / 8) M
          (fun x => u x) :=
    cubeBesovPositiveScalarPartialSeminormTwo_sub_const (originCube d 0) (3 / 8) M
      (fun x => u x) (cubeAverage (originCube d 0) (fun x => u x)) hmem
  rw [hfluct] at hdown
  -- Step 3: the multiscale Poincaré estimate at `t = 1/2`
  have hpoincare :=
    Ch01.Legacy.h1_fluctuation_partialNormTop_two_le_sum_grad_circNorm
      (originCube d 0) (1 / 2 : ℝ) M u (by norm_num) (by norm_num)
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hhalf] at hpoincare
  -- Step 4: the componentwise circ comparison
  have hsum :
      (∑ i : Fin d,
          cubeBesovCircNorm (originCube d 0) (1 / 2 : ℝ) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i)) ≤
        (d : ℝ) * (sensitivityGapConst *
          cubeBesovNegativeVectorSeminormTwo (originCube d 0) (3 / 8)
            (fun x => u.grad x)) := by
    calc
      (∑ i : Fin d,
          cubeBesovCircNorm (originCube d 0) (1 / 2 : ℝ) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i))
          ≤ ∑ _i : Fin d, sensitivityGapConst *
              cubeBesovNegativeVectorSeminormTwo (originCube d 0) (3 / 8)
                (fun x => u.grad x) :=
            Finset.sum_le_sum fun i _ =>
              cubeBesovCircNorm_half_grad_originCube_le (fun x => u.grad x) i hBdd
      _ = (d : ℝ) * (sensitivityGapConst *
            cubeBesovNegativeVectorSeminormTwo (originCube d 0) (3 / 8)
              (fun x => u.grad x)) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- assembly
  have hPnn : (0 : ℝ) ≤ Ch01.Legacy.fullVectorPoincareConstant (originCube d 0) *
      (3 : ℝ) ^ ((d : ℝ) + 1) :=
    mul_nonneg (Ch01.Legacy.fullVectorPoincareConstant_nonneg (originCube d 0))
      (Real.rpow_nonneg (by norm_num) _)
  have hstep :
      cubeBesovPartialNormTop (originCube d 0) (1 / 2 : ℝ) (2 : ℝ≥0∞) M
          (cubeFluctuation (originCube d 0) (fun x => u x)) ≤
        (Ch01.Legacy.fullVectorPoincareConstant (originCube d 0) *
            (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((d : ℝ) * (sensitivityGapConst *
            cubeBesovNegativeVectorSeminormTwo (originCube d 0) (3 / 8)
              (fun x => u.grad x))) :=
    hpoincare.trans (mul_le_mul_of_nonneg_left hsum hPnn)
  refine hdown.trans ?_
  refine (mul_le_mul_of_nonneg_left hstep sensitivityGapConst_nonneg).trans
    (le_of_eq ?_)
  unfold depthDowngradeConst
  ring

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
