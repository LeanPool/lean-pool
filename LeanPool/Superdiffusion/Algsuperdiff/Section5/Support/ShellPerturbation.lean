/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.HolderCalculus
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.Translation
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.VecGauge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.ShellSum

/-!
# ShellPerturbation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The stream increment `k_m - k_n` as a perturbation on `y + □_n`

Section 5.1 compares the localized Dirichlet problems for `a_n` and for `a_m`,
`m ≥ n`, by treating `k_m - k_n` as a perturbation of the coefficient field on
the cube `y + □_n`.  The whole size input for that comparison is the large-scale
event `𝒥(y + □_n, θ)` of `Translation.lean`, which caps the tail sum

```text
  Σ_{k ≥ n} 3^{(2-γ) n} ‖∇ j_k‖_{W^{1,∞}(y+□_n)} ≤ θ .
```

Because the weight is fixed at the cube scale `n`, a bound on the whole tail is
in particular a bound on the block `k ∈ (n, m]`, uniformly in `m`.  Unfolding
the volume-normalized gauge `‖∇ j‖_{W^{1,∞}(y+□_n)} = max(‖∇²j‖_{L^∞(y+□_n)},
3^{-n} ‖∇ j‖_{L^∞(y+□_n)})` therefore gives, with **no constant at all**,

```text
  Σ_{k ∈ (n,m]} ‖∇² j_k‖_{L^∞(y+□_n)} ≤ θ 3^{(γ-2) n} ,
  Σ_{k ∈ (n,m]} ‖∇  j_k‖_{L^∞(y+□_n)} ≤ θ 3^{(γ-1) n} ,
```

which are the two displayed bounds of the perturbation step.  The `1/2`-Hölder
bound follows by the mean value inequality on the convex cube together with the
interpolation `[F]_{1/2} ≤ (2 ‖F‖_∞ ‖∇F‖_∞)^{1/2}` of `HolderCalculus.lean`.

## The two metrics, and where the dimensional constants come from

The shell gauges of `Section4/Support/ShellNorms.lean` are built from the exact
*Euclidean-induced* sizes `matrixDerivativeNorm` and `matrixSecondDerivativeNorm`
of the stored derivatives, whereas `supNormOn` and `holderSeminormOn` use the
ambient norm of the derivative carriers `Vec d →L[ℝ] Mat d` and
`Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)`, whose source is `Vec d` in the *supremum*
norm and whose target `Mat d` carries the entrywise supremum norm.  Converting
one into the other costs `√d` per differentiation, since `‖v‖_∞ ≤ |v|_2 ≤ √d
‖v‖_∞` and the entrywise supremum norm of a matrix is at most its Euclidean
operator norm.  That is the entire source of the constants below: the exact
Euclidean statements carry the constant `1`, the ambient statements carry `√d`
for the gradient, `d` for the Hessian and `√2 · d` for the Hölder seminorm.

## References

* ABK26, the large-scale good event of Section 5.1 and the perturbation step of
  the injection estimate.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Stream
open scoped Matrix.Norms.Elementwise ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-- `Real.rpow` written with the power notation, so that the `Real.rpow_*`
rewriting API applies to the spellings used in the statements. -/
private theorem rpow_eq_hpow (a b : ℝ) : Real.rpow a b = a ^ b := rfl

/-! ## 1. The Euclidean gauges versus the ambient norms -/

/-- The entrywise supremum norm of a matrix is at most its Euclidean operator
norm. -/
theorem norm_le_matrixOperatorNorm (A : Mat d) : ‖A‖ ≤ matrixOperatorNorm A := by
  refine (Matrix.norm_le_iff (matrixOperatorNorm_nonneg A)).2 fun i j => ?_
  simpa only [Real.norm_eq_abs] using abs_entry_le_matrixOperatorNorm A i j

/-- On a vector of positive ambient norm the rescaling by `(√d ‖v‖)⁻¹` lands in
the Euclidean unit ball, and the rescaling factor is positive. -/
private theorem exists_unit_rescale {v : Vec d} (hv : 0 < ‖v‖) :
    0 < Real.sqrt d ∧ vecNorm ((Real.sqrt d * ‖v‖)⁻¹ • v) ≤ 1 := by
  have hle : ‖v‖ ≤ Real.sqrt d * ‖v‖ :=
    (ShellField.norm_vec_le_vecNorm v).trans (vecNorm_le_sqrt_dim_mul_norm v)
  have hs : 0 < Real.sqrt d := by
    rcases lt_or_ge 0 (Real.sqrt d) with h | h
    · exact h
    · have hnp : Real.sqrt d * ‖v‖ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hv.le
      linarith only [hnp, hle, hv]
  refine ⟨hs, ?_⟩
  have hpos : 0 < Real.sqrt d * ‖v‖ := mul_pos hs hv
  rw [vecNorm_smul, abs_of_pos (inv_pos.2 hpos), inv_mul_le_one₀ hpos]
  exact vecNorm_le_sqrt_dim_mul_norm v

/-- **The gradient conversion**: the ambient norm of a stored first derivative is
at most `√d` times its exact Euclidean induced norm. -/
theorem norm_le_sqrt_dim_mul_matrixDerivativeNorm (D : ShellField.MatrixDerivative d) :
    ‖D‖ ≤ Real.sqrt d * ShellField.matrixDerivativeNorm D := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Real.sqrt_nonneg _) (ShellField.matrixDerivativeNorm_nonneg D)) fun v => ?_
  rcases eq_or_lt_of_le (norm_nonneg v) with hv | hv
  · have hv0 : v = 0 := by rwa [eq_comm, norm_eq_zero] at hv
    subst hv0
    show ‖D 0‖ ≤ Real.sqrt d * ShellField.matrixDerivativeNorm D * ‖(0 : Vec d)‖
    have hD0 : D 0 = 0 := map_zero D
    simp only [hD0, norm_zero, mul_zero, le_refl]
  · obtain ⟨hs, hunit⟩ := exists_unit_rescale hv
    have hpos : 0 < Real.sqrt d * ‖v‖ := mul_pos hs hv
    set c : ℝ := (Real.sqrt d * ‖v‖)⁻¹ with hc
    have hkey : ‖D (c • v)‖ ≤ ShellField.matrixDerivativeNorm D :=
      (norm_le_matrixOperatorNorm _).trans
        (ShellField.matrixOperatorNorm_apply_le_matrixDerivativeNorm D (c • v) hunit)
    rw [map_smul, norm_smul, hc, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos),
      inv_mul_le_iff₀ hpos] at hkey
    calc ‖D v‖ ≤ Real.sqrt d * ‖v‖ * ShellField.matrixDerivativeNorm D := hkey
      _ = Real.sqrt d * ShellField.matrixDerivativeNorm D * ‖v‖ := by ring

/-- `√d ≤ d`, the step from the sharp gradient conversion to the packaged one. -/
theorem sqrt_dim_le_dim (d : ℕ) : Real.sqrt d ≤ (d : ℝ) := by
  have hle : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      norm_num
    · have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      calc (d : ℝ) = 1 * (d : ℝ) := (one_mul _).symm
        _ ≤ (d : ℝ) * (d : ℝ) := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg d)
        _ = (d : ℝ) ^ 2 := (pow_two _).symm
  calc Real.sqrt d ≤ Real.sqrt ((d : ℝ) ^ 2) := Real.sqrt_le_sqrt hle
    _ = (d : ℝ) := Real.sqrt_sq (Nat.cast_nonneg d)

/-- The packaged gradient conversion, with the same constant `d` as the Hessian
conversion below. -/
theorem norm_le_dim_mul_matrixDerivativeNorm (D : ShellField.MatrixDerivative d) :
    ‖D‖ ≤ (d : ℝ) * ShellField.matrixDerivativeNorm D :=
  (norm_le_sqrt_dim_mul_matrixDerivativeNorm D).trans
    (mul_le_mul_of_nonneg_right (sqrt_dim_le_dim d)
      (ShellField.matrixDerivativeNorm_nonneg D))

/-- **The Hessian conversion**: the ambient norm of a stored second derivative is
at most `d` times its exact twice-induced Euclidean norm. -/
theorem norm_le_dim_mul_matrixSecondDerivativeNorm
    (H : ShellField.MatrixSecondDerivative d) :
    ‖H‖ ≤ (d : ℝ) * ShellField.matrixSecondDerivativeNorm H := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Nat.cast_nonneg d) (ShellField.matrixSecondDerivativeNorm_nonneg H)) fun v => ?_
  rcases eq_or_lt_of_le (norm_nonneg v) with hv | hv
  · have hv0 : v = 0 := by rwa [eq_comm, norm_eq_zero] at hv
    subst hv0
    show ‖H 0‖ ≤ (d : ℝ) * ShellField.matrixSecondDerivativeNorm H * ‖(0 : Vec d)‖
    have hH0 : H 0 = 0 := map_zero H
    simp only [hH0, norm_zero, mul_zero, le_refl]
  · obtain ⟨hs, hunit⟩ := exists_unit_rescale hv
    have hpos : 0 < Real.sqrt d * ‖v‖ := mul_pos hs hv
    set c : ℝ := (Real.sqrt d * ‖v‖)⁻¹ with hc
    have hsq : Real.sqrt d * Real.sqrt d = (d : ℝ) := Real.mul_self_sqrt (by positivity)
    have hkey : ‖H (c • v)‖ ≤ Real.sqrt d * ShellField.matrixSecondDerivativeNorm H :=
      (norm_le_sqrt_dim_mul_matrixDerivativeNorm _).trans
        (by
          gcongr
          exact ShellField.matrixDerivativeNorm_apply_le_matrixSecondDerivativeNorm
            H (c • v) hunit)
    rw [map_smul, norm_smul, hc, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos),
      inv_mul_le_iff₀ hpos] at hkey
    calc ‖H v‖ ≤ Real.sqrt d * ‖v‖ * (Real.sqrt d * ShellField.matrixSecondDerivativeNorm H) :=
          hkey
      _ = Real.sqrt d * Real.sqrt d * ShellField.matrixSecondDerivativeNorm H * ‖v‖ := by ring
      _ = (d : ℝ) * ShellField.matrixSecondDerivativeNorm H * ‖v‖ := by rw [hsq]

/-! ## 2. The mean value step on a convex set -/

/-- **The mean value inequality as a Lipschitz (exponent-one Hölder) bound.**
On a convex set a uniform bound on the Fréchet derivative is exactly the
two-point bound `HolderSeminormBoundOn U 1 L F`.  The dimensional cost of
converting the derivative bound into the ambient operator norm `‖F' x‖` is
carried by the caller; for the shell carriers it is the factor `d` of
`norm_le_dim_mul_matrixSecondDerivativeNorm`. -/
theorem holderSeminormBoundOn_one_of_hasFDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set (Vec d)} (hU : Convex ℝ U) {F : Vec d → E}
    {F' : Vec d → (Vec d →L[ℝ] E)} (hF : ∀ x ∈ U, HasFDerivAt F (F' x) x)
    {L : ℝ} (hL : ∀ x ∈ U, ‖F' x‖ ≤ L) :
    Section4.Support.HolderSeminormBoundOn U 1 L F := by
  intro x hx z hz
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := F) (f' := F') (s := U) (C := L)
    (fun w hw => (hF w hw).hasFDerivWithinAt) hL hU hz hx
  rwa [Real.rpow_one]

/-! ## 3. The shell gauges on the translated cube -/

/-- The exact Euclidean size of `∇ j` at a point of `y + □_n` is controlled by
the `L^∞(y + □_n)` gauge of the translated shell. -/
theorem matrixDerivativeNorm_deriv_le_localCubeDerivNorm_at
    (y : Vec d) (n : ℤ) (j : ShellField d) {x : Vec d} (hx : x ∈ cubeSetAt y n) :
    ShellField.matrixDerivativeNorm (ShellField.deriv j x)
      ≤ localCubeDerivNorm n (ShellField.translate y j) := by
  have hx' : x - y ∈ openCubeSet (originCube d n) := mem_cubeSetAt_iff.1 hx
  have h := matrixDerivativeNorm_deriv_le_localCubeDerivNorm n
    (ShellField.translate y j) hx'
  rwa [ShellField.translate_deriv, sub_add_cancel] at h

/-- The exact Euclidean size of `∇² j` at a point of `y + □_n` is controlled by
the `L^∞(y + □_n)` gauge of the translated shell. -/
theorem matrixSecondDerivativeNorm_secondDeriv_le_localCubeSecondDerivNorm_at
    (y : Vec d) (n : ℤ) (j : ShellField d) {x : Vec d} (hx : x ∈ cubeSetAt y n) :
    ShellField.matrixSecondDerivativeNorm (ShellField.secondDeriv j x)
      ≤ localCubeSecondDerivNorm n (ShellField.translate y j) := by
  have hx' : x - y ∈ openCubeSet (originCube d n) := mem_cubeSetAt_iff.1 hx
  have h := matrixSecondDerivativeNorm_secondDeriv_le_localCubeSecondDerivNorm n
    (ShellField.translate y j) hx'
  rwa [ShellField.translate_secondDeriv, sub_add_cancel] at h

/-- Triangle inequality for the exact Euclidean gradient size over a finite sum
of shell fields. -/
theorem matrixDerivativeNorm_deriv_sum_le {iota : Type*} (s : Finset iota)
    (f : iota → ShellField d) (x : Vec d) :
    ShellField.matrixDerivativeNorm (ShellField.deriv (ShellField.sum s f) x)
      ≤ ∑ i ∈ s, ShellField.matrixDerivativeNorm (ShellField.deriv (f i) x) := by
  have hzero : ShellField.matrixDerivativeNorm (0 : ShellField.MatrixDerivative d) ≤ 0 := by
    simpa only [norm_zero, mul_zero] using
      ShellField.matrixDerivativeNorm_le_sq_mul_norm (0 : ShellField.MatrixDerivative d)
  exact Finset.le_sum_of_subadditive (ShellField.matrixDerivativeNorm (d := d)) hzero
    ShellField.matrixDerivativeNorm_add_le s (fun i => ShellField.deriv (f i) x)

/-- Triangle inequality for the exact Euclidean Hessian size over a finite sum
of shell fields. -/
theorem matrixSecondDerivativeNorm_secondDeriv_sum_le {iota : Type*} (s : Finset iota)
    (f : iota → ShellField d) (x : Vec d) :
    ShellField.matrixSecondDerivativeNorm (ShellField.secondDeriv (ShellField.sum s f) x)
      ≤ ∑ i ∈ s, ShellField.matrixSecondDerivativeNorm (ShellField.secondDeriv (f i) x) := by
  have hzero :
      ShellField.matrixSecondDerivativeNorm (0 : ShellField.MatrixSecondDerivative d) ≤ 0 := by
    rw [ShellField.matrixSecondDerivativeNorm_le_iff]
    refine ⟨le_rfl, fun u _ => ?_⟩
    simpa only [zero_apply, norm_zero, mul_zero] using
      ShellField.matrixDerivativeNorm_le_sq_mul_norm (0 : ShellField.MatrixDerivative d)
  exact Finset.le_sum_of_subadditive (ShellField.matrixSecondDerivativeNorm (d := d)) hzero
    ShellField.matrixSecondDerivativeNorm_add_le s (fun i => ShellField.secondDeriv (f i) x)

/-! ## 4. Reading the large-scale event on a block of shells

The weight `3^{(2-γ) n}` of `largeScaleEventBase` does not run with the
summation index, so a bound on the whole tail `k ≥ n` restricts to a bound on
any finite block of shells, with no loss and in particular uniformly in the
upper endpoint. -/

private theorem shellW1InfGradNorm_sum_le_of_mem_largeScaleEventBase
    {M : ABKModel d} {n : ℤ} {theta : ℝ} {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ largeScaleEventBase M n theta) (htheta : 0 ≤ theta)
    (s : Finset ℤ) (hs : ∀ k ∈ s, n ≤ k) :
    ∑ k ∈ s, Section4.Support.shellW1InfGradNorm n (omega.1 k)
      ≤ theta * Real.rpow 3 ((M.gamma - 2) * (n : ℝ)) := by
  classical
  have hwpos : (0 : ℝ) < Real.rpow 3 ((2 - M.gamma) * (n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hmem' : ∑' k : {k : ℤ // n ≤ k},
      ENNReal.ofReal (Real.rpow 3 ((2 - M.gamma) * (n : ℝ)) *
        Section4.Support.shellW1InfGradNorm n (omega.1 k.1)) ≤ ENNReal.ofReal theta := hmem
  have hsub := ENNReal.sum_le_tsum (f := fun k : {k : ℤ // n ≤ k} =>
      ENNReal.ofReal (Real.rpow 3 ((2 - M.gamma) * (n : ℝ)) *
        Section4.Support.shellW1InfGradNorm n (omega.1 k.1)))
    (s.subtype (fun k => n ≤ k))
  have hfil : ∑ i ∈ s.subtype (fun k => n ≤ k),
        ENNReal.ofReal (Real.rpow 3 ((2 - M.gamma) * (n : ℝ)) *
          Section4.Support.shellW1InfGradNorm n (omega.1 i.1))
      = ∑ k ∈ s, ENNReal.ofReal (Real.rpow 3 ((2 - M.gamma) * (n : ℝ)) *
          Section4.Support.shellW1InfGradNorm n (omega.1 k)) := by
    rw [Finset.sum_subtype_eq_sum_filter
        (fun k : ℤ => ENNReal.ofReal (Real.rpow 3 ((2 - M.gamma) * (n : ℝ)) *
          Section4.Support.shellW1InfGradNorm n (omega.1 k))),
      Finset.filter_true_of_mem hs]
  have hle : ENNReal.ofReal (∑ k ∈ s, Real.rpow 3 ((2 - M.gamma) * (n : ℝ)) *
        Section4.Support.shellW1InfGradNorm n (omega.1 k)) ≤ ENNReal.ofReal theta := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ =>
      mul_nonneg hwpos.le (Section4.Support.shellW1InfGradNorm_nonneg n _), ← hfil]
    exact hsub.trans hmem'
  have hreal := (ENNReal.ofReal_le_ofReal_iff htheta).1 hle
  rw [← Finset.mul_sum] at hreal
  have hfinal : ∑ k ∈ s, Section4.Support.shellW1InfGradNorm n (omega.1 k)
      ≤ theta / Real.rpow 3 ((2 - M.gamma) * (n : ℝ)) := (le_div_iff₀' hwpos).2 hreal
  have hinv : Real.rpow 3 ((M.gamma - 2) * (n : ℝ))
      = (Real.rpow 3 ((2 - M.gamma) * (n : ℝ)))⁻¹ := by
    simp only [rpow_eq_hpow]
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  rw [hinv, ← div_eq_mul_inv]
  exact hfinal

/-- **The block form of the large-scale event on `y + □_n`.**  On
`𝒥(y + □_n, θ)` the volume-normalized gauges of any finite block of shells
`k ≥ n` sum to at most `θ 3^{(γ-2) n}`. -/
theorem shellW1InfGradNorm_translate_sum_le_of_mem_largeScaleEvent
    {M : ABKModel d} {n : ℤ} {y : Vec d} {theta : ℝ} {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ largeScaleEvent M n y theta) (htheta : 0 ≤ theta)
    (s : Finset ℤ) (hs : ∀ k ∈ s, n ≤ k) :
    ∑ k ∈ s, Section4.Support.shellW1InfGradNorm n (ShellField.translate y (omega.1 k))
      ≤ theta * Real.rpow 3 ((M.gamma - 2) * (n : ℝ)) := by
  have h := shellW1InfGradNorm_sum_le_of_mem_largeScaleEventBase
    ((mem_largeScaleEvent_iff M n y theta omega).1 hmem) htheta s hs
  simpa only [Cutoff.translateCutoffSample_val, ShellField.translateSequence_apply] using h

/-- The Hessian leg of the block bound: `Σ ‖∇² j_k‖_{L^∞(y+□_n)} ≤ θ 3^{(γ-2) n}`. -/
theorem localCubeSecondDerivNorm_sum_le_of_mem_largeScaleEvent
    {M : ABKModel d} {n : ℤ} {y : Vec d} {theta : ℝ} {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ largeScaleEvent M n y theta) (htheta : 0 ≤ theta)
    (s : Finset ℤ) (hs : ∀ k ∈ s, n ≤ k) :
    ∑ k ∈ s, localCubeSecondDerivNorm n (ShellField.translate y (omega.1 k))
      ≤ theta * Real.rpow 3 ((M.gamma - 2) * (n : ℝ)) :=
  (Finset.sum_le_sum fun _ _ =>
      Section4.Support.localCubeSecondDerivNorm_le_shellW1InfGradNorm n _).trans
    (shellW1InfGradNorm_translate_sum_le_of_mem_largeScaleEvent hmem htheta s hs)

/-- The gradient leg of the block bound: `Σ ‖∇ j_k‖_{L^∞(y+□_n)} ≤ θ 3^{(γ-1) n}`.
The extra factor `3^n` is the volume normalization `|□_n|^{-1/d} = 3^{-n}` that
the gauge divides out of the first-derivative leg. -/
theorem localCubeDerivNorm_sum_le_of_mem_largeScaleEvent
    {M : ABKModel d} {n : ℤ} {y : Vec d} {theta : ℝ} {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ largeScaleEvent M n y theta) (htheta : 0 ≤ theta)
    (s : Finset ℤ) (hs : ∀ k ∈ s, n ≤ k) :
    ∑ k ∈ s, localCubeDerivNorm n (ShellField.translate y (omega.1 k))
      ≤ theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hstep : ∀ k ∈ s, localCubeDerivNorm n (ShellField.translate y (omega.1 k))
      ≤ (3 : ℝ) ^ n *
        Section4.Support.shellW1InfGradNorm n (ShellField.translate y (omega.1 k)) := by
    intro k _
    have h := Section4.Support.three_zpow_mul_localCubeDerivNorm_le_shellW1InfGradNorm n
      (ShellField.translate y (omega.1 k))
    calc localCubeDerivNorm n (ShellField.translate y (omega.1 k))
        = (3 : ℝ) ^ n *
            ((3 : ℝ) ^ (-n) * localCubeDerivNorm n (ShellField.translate y (omega.1 k))) := by
          rw [← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), add_neg_cancel,
            zpow_zero, one_mul]
      _ ≤ (3 : ℝ) ^ n *
            Section4.Support.shellW1InfGradNorm n (ShellField.translate y (omega.1 k)) :=
          mul_le_mul_of_nonneg_left h h3.le
  have hzpow : (3 : ℝ) ^ n = Real.rpow 3 (n : ℝ) := (Real.rpow_intCast 3 n).symm
  have hadd : Real.rpow 3 (n : ℝ) * Real.rpow 3 ((M.gamma - 2) * (n : ℝ))
      = Real.rpow 3 ((M.gamma - 1) * (n : ℝ)) := by
    simp only [rpow_eq_hpow]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hpow : (3 : ℝ) ^ n * (theta * Real.rpow 3 ((M.gamma - 2) * (n : ℝ)))
      = theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)) := by
    rw [hzpow, ← hadd]
    ring
  calc ∑ k ∈ s, localCubeDerivNorm n (ShellField.translate y (omega.1 k))
      ≤ ∑ k ∈ s, (3 : ℝ) ^ n *
          Section4.Support.shellW1InfGradNorm n (ShellField.translate y (omega.1 k)) :=
        Finset.sum_le_sum hstep
    _ = (3 : ℝ) ^ n *
          ∑ k ∈ s, Section4.Support.shellW1InfGradNorm n
            (ShellField.translate y (omega.1 k)) := (Finset.mul_sum _ _ _).symm
    _ ≤ (3 : ℝ) ^ n * (theta * Real.rpow 3 ((M.gamma - 2) * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (shellW1InfGradNorm_translate_sum_le_of_mem_largeScaleEvent hmem htheta s hs) h3.le
    _ = theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)) := hpow

/-! ## 5. The perturbation bounds on `y + □_n` -/

private theorem shellIncrement_eq_sum (omega : Cutoff.ShellSeq d) (n m : ℤ) :
    shellIncrement omega n m = ShellField.sum (Finset.Ioc n m) omega := rfl

private theorem mem_Ioc_le (n m : ℤ) : ∀ k ∈ Finset.Ioc n m, n ≤ k :=
  fun _ hk => le_of_lt (Finset.mem_Ioc.1 hk).1

/-- **The increment shell field carries the derivative of `k_m - k_n`.**  Its
values are `k_m x - k_n x`, and the stored first derivative is the genuine
Fréchet derivative of that map, so the bounds below are bounds on
`∇(k_m - k_n)`. -/
theorem hasFDerivAt_cutoff_sub (omega : Cutoff.CutoffSample d) {n m : ℤ} (hnm : n ≤ m)
    (x : Vec d) :
    HasFDerivAt (fun z : Vec d => Cutoff.cutoff m omega z - Cutoff.cutoff n omega z)
      (ShellField.deriv (shellIncrement omega.1 n m) x) x :=
  ((shellIncrement omega.1 n m).hasFDerivAt x).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun z =>
      (shellIncrement_apply_eq_cutoff_sub omega hnm z).symm)

/-- **The gradient bound**, in the exact Euclidean induced norm and with the
constant `1`: `‖Σ_{k ∈ (n,m]} ∇ j_k‖_{L^∞(y+□_n)} ≤ θ 3^{(γ-1) n}`, uniformly in
`m`.  The block is empty for `m ≤ n`, and for `n ≤ m` the field it sums to is
`∇(k_m - k_n)` by `hasFDerivAt_cutoff_sub`. -/
theorem matrixDerivativeNorm_deriv_shellIncrement_le
    {M : ABKModel d} {n m : ℤ} {y : Vec d} {theta : ℝ} {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ largeScaleEvent M n y theta) (htheta : 0 ≤ theta)
    {x : Vec d} (hx : x ∈ cubeSetAt y n) :
    ShellField.matrixDerivativeNorm (ShellField.deriv (shellIncrement omega.1 n m) x)
      ≤ theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)) := by
  rw [shellIncrement_eq_sum]
  calc ShellField.matrixDerivativeNorm
        (ShellField.deriv (ShellField.sum (Finset.Ioc n m) omega.1) x)
      ≤ ∑ k ∈ Finset.Ioc n m,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega.1 k) x) :=
        matrixDerivativeNorm_deriv_sum_le _ _ _
    _ ≤ ∑ k ∈ Finset.Ioc n m,
          localCubeDerivNorm n (ShellField.translate y (omega.1 k)) :=
        Finset.sum_le_sum fun k _ =>
          matrixDerivativeNorm_deriv_le_localCubeDerivNorm_at y n _ hx
    _ ≤ theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)) :=
        localCubeDerivNorm_sum_le_of_mem_largeScaleEvent hmem htheta _ (mem_Ioc_le n m)

/-- **The Hessian bound**, in the exact twice-induced Euclidean norm and with
the constant `1`: `‖Σ_{k ∈ (n,m]} ∇² j_k‖_{L^∞(y+□_n)} ≤ θ 3^{(γ-2) n}`,
uniformly in `m`.  The block is empty for `m ≤ n`, and for `n ≤ m` the field it
sums to is `∇²(k_m - k_n)`. -/
theorem matrixSecondDerivativeNorm_secondDeriv_shellIncrement_le
    {M : ABKModel d} {n m : ℤ} {y : Vec d} {theta : ℝ} {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ largeScaleEvent M n y theta) (htheta : 0 ≤ theta)
    {x : Vec d} (hx : x ∈ cubeSetAt y n) :
    ShellField.matrixSecondDerivativeNorm
        (ShellField.secondDeriv (shellIncrement omega.1 n m) x)
      ≤ theta * Real.rpow 3 ((M.gamma - 2) * (n : ℝ)) := by
  rw [shellIncrement_eq_sum]
  calc ShellField.matrixSecondDerivativeNorm
        (ShellField.secondDeriv (ShellField.sum (Finset.Ioc n m) omega.1) x)
      ≤ ∑ k ∈ Finset.Ioc n m,
          ShellField.matrixSecondDerivativeNorm (ShellField.secondDeriv (omega.1 k) x) :=
        matrixSecondDerivativeNorm_secondDeriv_sum_le _ _ _
    _ ≤ ∑ k ∈ Finset.Ioc n m,
          localCubeSecondDerivNorm n (ShellField.translate y (omega.1 k)) :=
        Finset.sum_le_sum fun k _ =>
          matrixSecondDerivativeNorm_secondDeriv_le_localCubeSecondDerivNorm_at y n _ hx
    _ ≤ theta * Real.rpow 3 ((M.gamma - 2) * (n : ℝ)) :=
        localCubeSecondDerivNorm_sum_le_of_mem_largeScaleEvent hmem htheta _ (mem_Ioc_le n m)

/-- The gradient bound in the ambient gauge of `HolderGauge.lean`, with the
dimensional cost `√d` of the change of metric. -/
theorem supNormOn_deriv_shellIncrement_le
    {M : ABKModel d} {n m : ℤ} {y : Vec d} {theta : ℝ} {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ largeScaleEvent M n y theta) (htheta : 0 ≤ theta) :
    supNormOn (cubeSetAt y n) (fun x => ShellField.deriv (shellIncrement omega.1 n m) x)
      ≤ ENNReal.ofReal
          (Real.sqrt d * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)))) := by
  have hnn : (0 : ℝ) ≤ Real.sqrt d * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ))) :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg htheta (Real.rpow_pos_of_pos (by norm_num) _).le)
  refine (supNormOn_le_ofReal_iff hnn).2 fun x hx => ?_
  exact (norm_le_sqrt_dim_mul_matrixDerivativeNorm _).trans
    (mul_le_mul_of_nonneg_left
      (matrixDerivativeNorm_deriv_shellIncrement_le hmem htheta hx) (Real.sqrt_nonneg _))

/-- **The mean value step on the cube**: `Σ_{k ∈ (n,m]} ∇ j_k`, which is
`∇(k_m - k_n)` for `n ≤ m`, is Lipschitz on `y + □_n` with constant
`d · θ · 3^{(γ-2) n}`. -/
theorem holderSeminormBoundOn_one_deriv_shellIncrement
    {M : ABKModel d} {n m : ℤ} {y : Vec d} {theta : ℝ} {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ largeScaleEvent M n y theta) (htheta : 0 ≤ theta) :
    Section4.Support.HolderSeminormBoundOn (cubeSetAt y n) 1
      ((d : ℝ) * (theta * Real.rpow 3 ((M.gamma - 2) * (n : ℝ))))
      (fun x => ShellField.deriv (shellIncrement omega.1 n m) x) := by
  refine holderSeminormBoundOn_one_of_hasFDerivAt (convex_cubeSetAt y n)
    (F' := fun x => ShellField.secondDeriv (shellIncrement omega.1 n m) x)
    (fun x _ => (shellIncrement omega.1 n m).deriv_hasFDerivAt x) fun x hx => ?_
  exact (norm_le_dim_mul_matrixSecondDerivativeNorm _).trans
    (mul_le_mul_of_nonneg_left
      (matrixSecondDerivativeNorm_secondDeriv_shellIncrement_le hmem htheta hx)
      (Nat.cast_nonneg d))

/-- **The `1/2`-Hölder bound of the perturbation step**:
`[Σ_{k ∈ (n,m]} ∇ j_k]_{C^{0,1/2}(y+□_n)} ≤ √2 · d · θ · 3^{(γ - 3/2) n}`,
uniformly in `m`; for `n ≤ m` the field is `∇(k_m - k_n)`.  The exponent is the
printed one; the constant is the interpolation constant `√2` times the
dimensional cost `d` of the change of metric. -/
theorem holderSeminormBoundOn_half_deriv_shellIncrement
    {M : ABKModel d} {n m : ℤ} {y : Vec d} {theta : ℝ} {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ largeScaleEvent M n y theta) (htheta : 0 ≤ theta) :
    Section4.Support.HolderSeminormBoundOn (cubeSetAt y n) (1 / 2)
      (Real.sqrt 2 * ((d : ℝ) * (theta * Real.rpow 3 ((M.gamma - 3 / 2) * (n : ℝ)))))
      (fun x => ShellField.deriv (shellIncrement omega.1 n m) x) := by
  have hS : ∀ x ∈ cubeSetAt y n,
      ‖ShellField.deriv (shellIncrement omega.1 n m) x‖
        ≤ (d : ℝ) * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ))) := by
    intro x hx
    exact (norm_le_dim_mul_matrixDerivativeNorm _).trans
      (mul_le_mul_of_nonneg_left
        (matrixDerivativeNorm_deriv_shellIncrement_le hmem htheta hx) (Nat.cast_nonneg d))
  have hL := holderSeminormBoundOn_one_deriv_shellIncrement hmem htheta (m := m)
  have hX : (0 : ℝ) ≤ (d : ℝ) * (theta * Real.rpow 3 ((M.gamma - 3 / 2) * (n : ℝ))) :=
    mul_nonneg (Nat.cast_nonneg d)
      (mul_nonneg htheta (Real.rpow_pos_of_pos (by norm_num) _).le)
  have hAB : Real.rpow 3 ((M.gamma - 1) * (n : ℝ)) * Real.rpow 3 ((M.gamma - 2) * (n : ℝ))
      = Real.rpow 3 ((M.gamma - 3 / 2) * (n : ℝ)) *
        Real.rpow 3 ((M.gamma - 3 / 2) * (n : ℝ)) := by
    simp only [rpow_eq_hpow]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hconst : Real.sqrt
        (2 * ((d : ℝ) * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)))) *
          ((d : ℝ) * (theta * Real.rpow 3 ((M.gamma - 2) * (n : ℝ)))))
      = Real.sqrt 2 * ((d : ℝ) * (theta * Real.rpow 3 ((M.gamma - 3 / 2) * (n : ℝ)))) := by
    have hEq : 2 * ((d : ℝ) * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)))) *
          ((d : ℝ) * (theta * Real.rpow 3 ((M.gamma - 2) * (n : ℝ))))
        = 2 * (((d : ℝ) * (theta * Real.rpow 3 ((M.gamma - 3 / 2) * (n : ℝ)))) *
            ((d : ℝ) * (theta * Real.rpow 3 ((M.gamma - 3 / 2) * (n : ℝ))))) := by
      calc 2 * ((d : ℝ) * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)))) *
            ((d : ℝ) * (theta * Real.rpow 3 ((M.gamma - 2) * (n : ℝ))))
          = 2 * ((d : ℝ) * (d : ℝ) * (theta * theta)) *
              (Real.rpow 3 ((M.gamma - 1) * (n : ℝ)) *
                Real.rpow 3 ((M.gamma - 2) * (n : ℝ))) := by ring
        _ = 2 * ((d : ℝ) * (d : ℝ) * (theta * theta)) *
              (Real.rpow 3 ((M.gamma - 3 / 2) * (n : ℝ)) *
                Real.rpow 3 ((M.gamma - 3 / 2) * (n : ℝ))) := by rw [hAB]
        _ = 2 * (((d : ℝ) * (theta * Real.rpow 3 ((M.gamma - 3 / 2) * (n : ℝ)))) *
              ((d : ℝ) * (theta * Real.rpow 3 ((M.gamma - 3 / 2) * (n : ℝ))))) := by ring
    rw [hEq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul_self hX]
  have h := holderSeminormBoundOn_half_of_supNorm_of_lipschitz hS hL
  rwa [hconst] at h

end

end Algsuperdiff.Section5.Support
