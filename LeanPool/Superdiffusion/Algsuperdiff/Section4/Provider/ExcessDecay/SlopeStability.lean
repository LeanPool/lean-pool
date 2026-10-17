/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SandwichNondegeneracyAttainment

/-!
# SlopeStability

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Gradient stability of consecutive best-affine approximations (`e.grad.stability`)

```
|∇ℓ_k − ∇ℓ_{k−1}| ≤ C 3^{−k} ‖ℓ_k − ℓ_{k−1}‖_{L²(U_{k−1})} ≤ C (E_k + E_{k−1}) .
```

Both inequalities are proved here on the lemma's own window family.

* The **second** inequality is Minkowski for `‖·‖_{L²}` plus the volume-ratio comparison on the
  nested windows `U_{k−1} ⊆ U_k`, together with the two minimizing properties: this is
  `normalizedL2On_affineEval_sub_le`.
* The **first** inequality is the *inverse (Bernstein) inequality for affine
  functions*, which the tex attributes to "the triangle inequality".  It is
  supplied here by `normalizedL2On_affineEval_ge_of_sandwich`, i.e. by the
  exact cube second moment transported along the sandwich `x + □_{k−3} ⊆
  U_{k−1} ⊆ y + □_{k−1}` that `l.iteration.lemma` already assumes.  This is a
  **change of proof attribution, not of statement**: nothing is added to the
  source hypotheses.

## The constant chase

Write `A = |U_k|`, `B = |U_{k−1}|`, `e = 1/d`, `S = |∇ℓ_k − ∇ℓ_{k−1}|`:

```
c₀ B^e S  ≤  ‖ℓ_k − ℓ_{k−1}‖_{L²(U_{k−1})}                            (hnd)
          ≤  ‖u − ℓ_{k−1}‖_{L²(U_{k−1})} + ‖u − ℓ_k‖_{L²(U_{k−1})}   (Minkowski)
          ≤  B^e E_{k−1} + (A/B)^{1/2} A^e E_k                          (minimality + ratio)
          =  B^e (E_{k−1} + (A/B)^{e+1/2} E_k) ,
```

so with `κ` the volume-ratio constant `(A/B)^{1/d+1/2} ≤ κ` (and `1 ≤ κ` *derived* from
nestedness, `one_le_volumeRatioConst_of_nested`),

```
Cstab = slopeStabilityConst d θ κ = κ / ndConst d θ .
```

Under the paper's sandwich `θ = 3^{−2}`, so `c₀ = 3^{−d−2}/(2√3)` and `Cstab =
C(d)`, matching the tex's `C` in `e.grad.stability`; the tex's `C 3^{−k}` normalizer
is the Lean `|U_{k−1}|^{−1/d}` up to the same bounded volume ratio.

## Scalar versus vector form

The tex's Step 2 runs the Grönwall argument on the *vector* sequence `∇ℓ_{b−l}
− ∇ℓ_b`, while the proved §4.3 iteration engine (`IterationLemma.lean`,
hypothesis `hstab`) runs on the *scalar* sequence `p_k = |∇ℓ_k|`.  records that
the two Grönwall arguments are therefore not literally the same argument.  The
bridge is the reverse triangle inequality
`abs_slopeMagnitude_sub_slopeMagnitude_le`, proved below; the scalar statement
is *weaker* than the vector one, so nothing is smuggled by using it.

## References

* ABK26, `e.grad.stability`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport (Vec vecDot vecNormSq volumeAverage axisCube openCubeSet TriadicCube
  cubeScaleFactor)
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ### The slope magnitude is a Euclidean norm -/

private theorem vecNormSq_add_expand (x y : Vec d) :
    vecNormSq (x + y) = vecNormSq x + 2 * vecDot x y + vecNormSq y := by
  simp only [vecNormSq, vecDot, Pi.add_apply]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    show (x i + y i) * (x i + y i) = x i * x i + 2 * (x i * y i) + y i * y i from by ring)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem vecNormSq_sub_comm (x y : Vec d) : vecNormSq (x - y) = vecNormSq (y - x) := by
  simp only [vecNormSq, vecDot, Pi.sub_apply]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- **Triangle inequality for the slope magnitude** `|g|₂ = (∑ᵢ gᵢ²)^{1/2}`.  The ambient norm on
`Vec d = Fin d → ℝ` is the sup norm, so this is not available from the `Pi` instance. -/
theorem slopeMagnitude_add_le (x y : Vec d) :
    slopeMagnitude (x + y) ≤ slopeMagnitude x + slopeMagnitude y := by
  have hx : 0 ≤ vecNormSq x := HCPolySupport.vecNormSq_nonneg x
  have hy : 0 ≤ vecNormSq y := HCPolySupport.vecNormSq_nonneg y
  have hsx : Real.sqrt (vecNormSq x) ^ 2 = vecNormSq x := Real.sq_sqrt hx
  have hsy : Real.sqrt (vecNormSq y) ^ 2 = vecNormSq y := Real.sq_sqrt hy
  have hcs : vecDot x y ≤ Real.sqrt (vecNormSq x) * Real.sqrt (vecNormSq y) := by
    have h1 : vecDot x y ≤ |vecDot x y| := le_abs_self _
    have h2 : |vecDot x y| ≤ slopeMagnitude x * slopeMagnitude y :=
      abs_vecDot_le_slopeMagnitude_mul x y
    rw [slopeMagnitude, slopeMagnitude] at h2
    linarith only [h1, h2]
  have hexp : (Real.sqrt (vecNormSq x) + Real.sqrt (vecNormSq y)) ^ 2
      = vecNormSq x + 2 * (Real.sqrt (vecNormSq x) * Real.sqrt (vecNormSq y))
        + vecNormSq y := by
    rw [add_sq, hsx, hsy]
    ring
  have hsq : vecNormSq (x + y)
      ≤ (Real.sqrt (vecNormSq x) + Real.sqrt (vecNormSq y)) ^ 2 := by
    rw [vecNormSq_add_expand, hexp]
    linarith only [hcs]
  calc slopeMagnitude (x + y) = Real.sqrt (vecNormSq (x + y)) := rfl
    _ ≤ Real.sqrt ((Real.sqrt (vecNormSq x) + Real.sqrt (vecNormSq y)) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (vecNormSq x) + Real.sqrt (vecNormSq y) := Real.sqrt_sq (by positivity)
    _ = slopeMagnitude x + slopeMagnitude y := rfl

theorem slopeMagnitude_sub_comm (x y : Vec d) :
    slopeMagnitude (x - y) = slopeMagnitude (y - x) := by
  rw [slopeMagnitude, slopeMagnitude, vecNormSq_sub_comm]

/-- **Reverse triangle inequality** for the slope magnitude: the difference of the
*magnitudes* is controlled by the magnitude of the *difference*. -/
theorem abs_slopeMagnitude_sub_slopeMagnitude_le (x y : Vec d) :
    |slopeMagnitude x - slopeMagnitude y| ≤ slopeMagnitude (x - y) := by
  have h1 : slopeMagnitude x ≤ slopeMagnitude y + slopeMagnitude (x - y) := by
    have h := slopeMagnitude_add_le y (x - y)
    have hxy : y + (x - y) = x := by abel
    rw [hxy] at h
    exact h
  have h2 : slopeMagnitude y ≤ slopeMagnitude x + slopeMagnitude (x - y) := by
    have h := slopeMagnitude_add_le x (y - x)
    have hxy : x + (y - x) = y := by abel
    rw [hxy, slopeMagnitude_sub_comm y x] at h
    exact h
  rw [abs_le]
  exact ⟨by linarith only [h1, h2], by linarith only [h1, h2]⟩

/-! ### Undoing the excess normalizer -/

/-- `min_ℓ ‖u − ℓ‖_{L²(W)} = |W|^{1/d} · E(u,W)` --- the `|W|^{−1/d}` normalizer of
`affineExcess` undone on a window of positive volume. -/
theorem affineExcessRaw_eq_rpow_mul_affineExcess {W : Set (Vec d)}
    (hW : 0 < (volume W).toReal) (u : Vec d → ℝ) :
    affineExcessRaw W u = ((volume W).toReal) ^ ((d : ℝ)⁻¹) * affineExcess W u := by
  have hne : ((volume W).toReal) ^ ((d : ℝ)⁻¹) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hW _)
  rw [affineExcess, Real.rpow_neg hW.le, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-! ### The second inequality of `e.grad.stability` -/

/-- **The `L²` comparison of two affine minimizers on nested windows** (the second inequality of
`e.grad.stability`).  If `(c,g)` minimizes on `W` and `(c',g')` minimizes on `W' ⊆ W`, then

`‖ℓ − ℓ'‖_{L²(W')} ≤ min_ℓ ‖u − ℓ‖_{L²(W')} + (|W|/|W'|)^{1/2} · min_ℓ ‖u −
ℓ‖_{L²(W)}`.

Minkowski on `ℓ − ℓ' = (u − ℓ') + (ℓ − u)`, then the volume-ratio comparison on the second term. -/
theorem normalizedL2On_affineEval_sub_le {W W' : Set (Vec d)} {u : Vec d → ℝ} {c c' : ℝ}
    {g g' : Vec d} (hsub : W' ⊆ W) (hW : 0 < (volume W).toReal) (hW' : 0 < (volume W').toReal)
    (hu' : MemLp u 2 (volume.restrict W'))
    (haff' : ∀ (a : ℝ) (b : Vec d), MemLp (affineEval a b) 2 (volume.restrict W'))
    (hint : IntegrableOn (fun x => (u x - affineEval c g x) ^ 2) W)
    (hmin : IsAffineMinimizer W u c g) (hmin' : IsAffineMinimizer W' u c' g') :
    normalizedL2On W' (affineEval (c - c') (g - g'))
      ≤ affineExcessRaw W' u
        + Real.sqrt ((volume W).toReal / (volume W').toReal) * affineExcessRaw W u := by
  have hpt : affineEval (c - c') (g - g')
      = fun x => (u x - affineEval c' g' x) + (affineEval c g x - u x) := by
    funext x
    rw [← affineEval_sub]
    ring
  have h1 : MemLp (fun x => u x - affineEval c' g' x) 2 (volume.restrict W') :=
    hu'.sub (haff' c' g')
  have h2 : MemLp (fun x => affineEval c g x - u x) 2 (volume.restrict W') :=
    (haff' c g).sub hu'
  have hmink : normalizedL2On W'
        (fun x => (u x - affineEval c' g' x) + (affineEval c g x - u x))
      ≤ normalizedL2On W' (fun x => u x - affineEval c' g' x)
        + normalizedL2On W' (fun x => affineEval c g x - u x) :=
    normalizedL2On_add_le h1 h2
  have hterm1 : normalizedL2On W' (fun x => u x - affineEval c' g' x) = affineExcessRaw W' u :=
    hmin'
  have hsym : normalizedL2On W' (fun x => affineEval c g x - u x)
      = normalizedL2On W' (fun x => u x - affineEval c g x) :=
    normalizedL2On_sub_comm W' (affineEval c g) u
  have hcmp : normalizedL2On W' (fun x => u x - affineEval c g x)
      ≤ Real.sqrt ((volume W).toReal / (volume W').toReal)
        * normalizedL2On W (fun x => u x - affineEval c g x) :=
    normalizedL2On_le_of_subset hsub hW hW' hint
  have hminW : normalizedL2On W (fun x => u x - affineEval c g x) = affineExcessRaw W u := hmin
  rw [hterm1, hsym] at hmink
  rw [hminW] at hcmp
  rw [hpt]
  linarith only [hmink, hcmp]

/-! ### The constant, and the arithmetic of the chase -/

/-- The **slope-stability constant** of a window family: `Cstab = κ / c₀(θ)`, with `κ` the
volume-ratio constant of the nesting and `c₀(θ) = ndConst d θ` the nondegeneracy constant of the
sandwich.  Explicitly a function of `(d, θ, κ)`; no existential. -/
def slopeStabilityConst (d : ℕ) (θ κ : ℝ) : ℝ := κ / ndConst d θ

theorem slopeStabilityConst_nonneg {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 ≤ κ) :
    0 ≤ slopeStabilityConst d θ κ :=
  div_nonneg hκ (ndConst_pos hθ).le

/-- The `rpow` bookkeeping of the chase, over abstract positive reals. -/
private theorem rpow_slope_identity {A B e : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Real.sqrt (A / B) * A ^ e = (A / B) ^ (e + 1 / 2) * B ^ e := by
  have hAB : (0 : ℝ) < A / B := div_pos hA hB
  have hBe : B ^ e ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hB e)
  rw [Real.sqrt_eq_rpow, Real.rpow_add hAB e (1 / 2), Real.div_rpow hA.le hB.le e]
  field_simp

/-- The pure-algebra core of the chase, over abstract reals: no `rpow`, no `sqrt`. -/
private theorem slope_algebra {c₀ κ S Ek Ek1 Be r : ℝ}
    (hc₀ : 0 < c₀) (hBe : 0 < Be) (hκ : 1 ≤ κ) (hr : r ≤ κ)
    (hEk : 0 ≤ Ek) (hEk1 : 0 ≤ Ek1)
    (hmain : c₀ * Be * S ≤ Be * Ek1 + r * Be * Ek) :
    S ≤ κ / c₀ * (Ek + Ek1) := by
  have h1 : c₀ * S ≤ Ek1 + r * Ek :=
    le_of_mul_le_mul_left (by linarith only [hmain]) hBe
  have h2 : r * Ek ≤ κ * Ek := mul_le_mul_of_nonneg_right hr hEk
  have h3 : Ek1 ≤ κ * Ek1 := le_mul_of_one_le_left hEk1 hκ
  have h4 : c₀ * S ≤ κ * (Ek + Ek1) := by linarith only [h1, h2, h3]
  rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
  linarith only [h4]

/-- `1 ≤ κ` is **derived** from nestedness, not assumed: a nested family has volume ratio at least
one, and the exponent `1/d + 1/2` is nonnegative. -/
theorem one_le_volumeRatioConst_of_nested {U : ℤ → Set (Vec d)} {κ : ℝ}
    (hvol : ∀ k : ℤ, 0 < (volume (U k)).toReal) (hnest : ∀ k : ℤ, U k ⊆ U (k + 1))
    (hratio : ∀ k : ℤ,
      ((volume (U (k + 1))).toReal / (volume (U k)).toReal) ^ ((d : ℝ)⁻¹ + 1 / 2) ≤ κ) :
    (1 : ℝ) ≤ κ := by
  have hexp0 : (0 : ℝ) ≤ (d : ℝ)⁻¹ + 1 / 2 := by positivity
  have hne : volume (U (0 + 1)) ≠ ⊤ := by
    intro htop
    have h := hvol (0 + 1)
    rw [htop] at h
    rw [ENNReal.toReal_top] at h
    exact absurd h (lt_irrefl 0)
  have hle : (volume (U 0)).toReal ≤ (volume (U (0 + 1))).toReal :=
    ENNReal.toReal_mono hne (measure_mono (hnest 0))
  have hr1 : (1 : ℝ) ≤ (volume (U (0 + 1))).toReal / (volume (U 0)).toReal :=
    (one_le_div (hvol 0)).2 hle
  have h := Real.rpow_le_rpow zero_le_one hr1 hexp0
  rw [Real.one_rpow] at h
  exact le_trans h (hratio 0)

/-- The **volume-ratio constant of the triadic sandwich family**:
`κ(d) = (3^{3d})^{1/d + 1/2}`, i.e. `27 · 3^{3d/2}`.  On the family
`x + □_{k−2} ⊆ U_k ⊆ y + □_k` the ratio `|U_{k+1}|/|U_k|` is at most
`3^{(k+1)d}/3^{(k−2)d} = 3^{3d}`, so this value works at every scale.  Explicitly a function of
`d`; no existential. -/
def volumeRatioConstTriadic (d : ℕ) : ℝ := ((3 : ℝ) ^ (3 * d)) ^ ((d : ℝ)⁻¹ + 1 / 2)

theorem one_le_volumeRatioConstTriadic (d : ℕ) : (1 : ℝ) ≤ volumeRatioConstTriadic d := by
  have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (3 * d) := one_le_pow₀ (by norm_num)
  have hexp : (0 : ℝ) ≤ (d : ℝ)⁻¹ + 1 / 2 := by positivity
  have h := Real.rpow_le_rpow zero_le_one h1 hexp
  rw [Real.one_rpow] at h
  exact h

/-! ### The producer -/

/-- **Gradient stability (`e.grad.stability`) on the sandwich class.**

For a nested family `U : ℤ → Set (Vec d)` whose members are sandwiched between axis-parallel cubes
of aspect ratio at least `θ`, with `u` square-integrable on each window and `(cc k, gg k)` a chosen
affine minimizer on `U k`, the minimizer slopes on adjacent scales satisfy

```
| |∇ℓ_k| − |∇ℓ_{k−1}| | ≤ (κ / c₀(θ)) · (E_k + E_{k−1}) ,
```

exactly the shape `IterationLemma.iterationSlopeBound` consumes as `hstab`, with the explicit
`Cstab = slopeStabilityConst d θ κ`.

Neither is `1 ≤ κ`, which `one_le_volumeRatioConst_of_nested` derives. -/
theorem slopeStability_of_axisCubeSandwich (U : ℤ → Set (Vec d)) (u : Vec d → ℝ)
    (cc : ℤ → ℝ) (gg : ℤ → Vec d) {κ θ : ℝ} {zin zout : ℤ → Vec d} {Lin Lout : ℤ → ℝ}
    (hd : 0 < d) (hLin : ∀ k : ℤ, 0 < Lin k) (hLout : ∀ k : ℤ, 0 < Lout k)
    (hθ0 : 0 < θ) (hθ : ∀ k : ℤ, θ * Lout k ≤ Lin k)
    (hin : ∀ k : ℤ, axisCube (zin k) (Lin k) ⊆ U k)
    (hout : ∀ k : ℤ, U k ⊆ axisCube (zout k) (Lout k))
    (hmeas : ∀ k : ℤ, MeasurableSet (U k)) (hnest : ∀ k : ℤ, U k ⊆ U (k + 1))
    (hu : ∀ k : ℤ, MemLp u 2 (volume.restrict (U k)))
    (hmin : ∀ k : ℤ, IsAffineMinimizer (U k) u (cc k) (gg k))
    (hratio : ∀ k : ℤ,
      ((volume (U (k + 1))).toReal / (volume (U k)).toReal) ^ ((d : ℝ)⁻¹ + 1 / 2) ≤ κ) :
    ∀ k : ℤ, |slopeMagnitude (gg k) - slopeMagnitude (gg (k - 1))|
      ≤ slopeStabilityConst d θ κ * (affineExcess (U k) u + affineExcess (U (k - 1)) u) := by
  have hvol : ∀ k : ℤ, 0 < (volume (U k)).toReal :=
    fun k => volume_toReal_pos_of_sandwich (hLin k) (hin k) (hout k)
  have haff : ∀ (k : ℤ) (c : ℝ) (g : Vec d),
      MemLp (affineEval c g) 2 (volume.restrict (U k)) :=
    fun k c g => memLp_affineEval_of_sandwich (hLout k) (hmeas k) (hout k) c g
  have hc₀ : 0 < ndConst d θ := ndConst_pos hθ0
  have hnd : ∀ (k : ℤ) (c : ℝ) (g : Vec d),
      ndConst d θ * ((volume (U k)).toReal) ^ ((d : ℝ)⁻¹) * slopeMagnitude g
        ≤ normalizedL2On (U k) (affineEval c g) :=
    fun k c g => normalizedL2On_affineEval_ge_of_sandwich hd (hLin k) (hLout k) hθ0 (hθ k)
      (hin k) (hout k) c g
  have hone : (1 : ℝ) ≤ κ := one_le_volumeRatioConst_of_nested hvol hnest hratio
  intro k
  have hsub : U (k - 1) ⊆ U k := by
    have h := hnest (k - 1)
    rw [sub_add_cancel] at h
    exact h
  have hA : 0 < (volume (U k)).toReal := hvol k
  have hB : 0 < (volume (U (k - 1))).toReal := hvol (k - 1)
  have hrk : ((volume (U k)).toReal / (volume (U (k - 1))).toReal) ^ ((d : ℝ)⁻¹ + 1 / 2) ≤ κ := by
    have h := hratio (k - 1)
    rw [sub_add_cancel] at h
    exact h
  have hmemk : MemLp (fun x => u x - affineEval (cc k) (gg k) x) 2 (volume.restrict (U k)) :=
    (hu k).sub (haff k (cc k) (gg k))
  have hint : IntegrableOn (fun x => (u x - affineEval (cc k) (gg k) x) ^ 2) (U k) :=
    (memLp_two_iff_integrable_sq hmemk.aestronglyMeasurable).1 hmemk
  -- Step A: the `L²(U_{k−1})` comparison of the two minimizers.
  have hcore := normalizedL2On_affineEval_sub_le hsub hA hB (hu (k - 1))
    (haff (k - 1)) hint (hmin k) (hmin (k - 1))
  -- Step B: nondegeneracy converts it into a slope bound.
  have hnk := hnd (k - 1) (cc k - cc (k - 1)) (gg k - gg (k - 1))
  -- Step C: restore the excess normalizers and identify the volume ratio.
  have hrawB := affineExcessRaw_eq_rpow_mul_affineExcess hB u
  have hrawA := affineExcessRaw_eq_rpow_mul_affineExcess hA u
  have hid := rpow_slope_identity (e := (d : ℝ)⁻¹) hA hB
  have hchain : ndConst d θ * ((volume (U (k - 1))).toReal) ^ ((d : ℝ)⁻¹)
        * slopeMagnitude (gg k - gg (k - 1))
      ≤ ((volume (U (k - 1))).toReal) ^ ((d : ℝ)⁻¹) * affineExcess (U (k - 1)) u
        + (((volume (U k)).toReal / (volume (U (k - 1))).toReal) ^ ((d : ℝ)⁻¹ + 1 / 2)
            * ((volume (U (k - 1))).toReal) ^ ((d : ℝ)⁻¹)) * affineExcess (U k) u := by
    have h := le_trans hnk hcore
    rw [hrawB, hrawA] at h
    calc ndConst d θ * ((volume (U (k - 1))).toReal) ^ ((d : ℝ)⁻¹)
          * slopeMagnitude (gg k - gg (k - 1))
        ≤ ((volume (U (k - 1))).toReal) ^ ((d : ℝ)⁻¹) * affineExcess (U (k - 1)) u
          + Real.sqrt ((volume (U k)).toReal / (volume (U (k - 1))).toReal)
            * (((volume (U k)).toReal) ^ ((d : ℝ)⁻¹) * affineExcess (U k) u) := h
      _ = ((volume (U (k - 1))).toReal) ^ ((d : ℝ)⁻¹) * affineExcess (U (k - 1)) u
          + (Real.sqrt ((volume (U k)).toReal / (volume (U (k - 1))).toReal)
              * ((volume (U k)).toReal) ^ ((d : ℝ)⁻¹)) * affineExcess (U k) u := by ring
      _ = ((volume (U (k - 1))).toReal) ^ ((d : ℝ)⁻¹) * affineExcess (U (k - 1)) u
          + (((volume (U k)).toReal / (volume (U (k - 1))).toReal) ^ ((d : ℝ)⁻¹ + 1 / 2)
              * ((volume (U (k - 1))).toReal) ^ ((d : ℝ)⁻¹)) * affineExcess (U k) u := by
          rw [hid]
  -- Step D: pure algebra, then the reverse triangle inequality.
  have hslope : slopeMagnitude (gg k - gg (k - 1))
      ≤ slopeStabilityConst d θ κ * (affineExcess (U k) u + affineExcess (U (k - 1)) u) :=
    slope_algebra hc₀ (Real.rpow_pos_of_pos hB _) hone hrk
      (affineExcess_nonneg _ _) (affineExcess_nonneg _ _) hchain
  exact le_trans (abs_slopeMagnitude_sub_slopeMagnitude_le (gg k) (gg (k - 1))) hslope

end

end Algsuperdiff.Section4.Provider.ExcessDecay
