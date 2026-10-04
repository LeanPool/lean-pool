/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Existence.ClassicalMaximum


/-!
# Hopf's lemma and the strong maximum principle

Hopf's lemma: a `C²` subsolution on a ball, continuous on the closed ball, that is strictly
below its value at a boundary point `x₀` throughout the ball, has positive outward normal
derivative at `x₀`. The barrier `v = exp(-λ|x - y|²) - exp(-λ r²)` is a subsolution on the
annulus `r/2 < |x - y| < r` for `λ` large, vanishes on the outer sphere and is positive on the
inner one, so `u + ε v - u(x₀)` is nonpositive on the boundary of the annulus for `ε` small and,
by the weak maximum principle, on the annulus. Along the inward radius through `x₀` the
function `u + ε v` is therefore at most its value at `x₀`, and its one-sided derivative there,
which is `-∂_ν u(x₀) + ε ∂_ν(-v)(x₀)`, is nonpositive. The normal derivative of `v` is negative,
which gives the strict inequality.

The strong maximum principle: a `C²` subsolution on a connected open set that attains its
maximum at an interior point is constant. If not, the set where the function is below the
maximum is open, nonempty, and has a frontier point inside the set; a small ball about a
nearby point of it, of radius the distance to the level set of the maximum, lies in it and
touches the level set at a point where Hopf's lemma gives a nonzero gradient, though the point
is an interior maximum.

## Main declarations

* `EllipticPdes.Classical.hopf_lemma_ball`: Hopf's lemma on a ball.
* `EllipticPdes.Classical.hopf_lemma`: Hopf's lemma at a boundary point with the interior
  ball condition.
* `EllipticPdes.Classical.strong_maximum_principle`: the strong maximum principle.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.4.2 Lemma (Hopf's Lemma, p. 347)
and Theorem 3 (p. 349);
D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§3.2 Lemma 3.4 (p. 34) and Theorem 3.5 (p. 35).
-/

@[expose] public section

open Set Filter Topology Metric

noncomputable section

namespace EllipticPdes.Classical

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-! ### The barrier -/

/-- The squared distance to `y` as a sum of squares. -/
def sqDist (y x : EuclideanSpace ℝ (Fin d)) : ℝ := ∑ i, (x i - y i) ^ 2

/-- The squared distance is the squared norm of the difference. -/
theorem sqDist_eq (y x : EuclideanSpace ℝ (Fin d)) : sqDist y x = ‖x - y‖ ^ 2 := by
  rw [sqDist, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]

/-- The derivative of the squared distance. -/
theorem hasFDerivAt_sqDist (y x : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (sqDist y)
      (∑ i, (2 * (x i - y i)) • (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) x := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => (z i - y i) ^ 2)
        ((2 * (x i - y i)) • (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) x := by
    intro i _
    have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => z i - y i)
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) x :=
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).hasFDerivAt.sub_const (y i)
    have h2 := h1.pow 2
    refine h2.congr_fderiv ?_
    simp only [Nat.add_one_sub_one, pow_one, nsmul_eq_mul, Nat.cast_ofNat]
  refine (HasFDerivAt.sum h).congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  simp [sqDist, Finset.sum_apply]

/-- The barrier's exponential part `exp (-λ |x - y|²)`. -/
def barrierExp (lam : ℝ) (y x : EuclideanSpace ℝ (Fin d)) : ℝ := Real.exp (-lam * sqDist y x)

/-- The exponential part is positive. -/
theorem barrierExp_pos (lam : ℝ) (y x : EuclideanSpace ℝ (Fin d)) : 0 < barrierExp lam y x :=
  Real.exp_pos _

/-- The derivative of the exponential part. -/
theorem hasFDerivAt_barrierExp (lam : ℝ) (y x : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (barrierExp lam y)
      (barrierExp lam y x • ((-lam) • ∑ i, (2 * (x i - y i))
        • (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))) x := by
  have h1 := (hasFDerivAt_sqDist y x).const_mul (-lam)
  exact (Real.hasDerivAt_exp (-lam * sqDist y x)).comp_hasFDerivAt x h1

/-- The value of the derivative of the exponential part on a vector. -/
theorem fderiv_barrierExp_apply (lam : ℝ) (y x ξ : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (barrierExp lam y) x ξ
      = barrierExp lam y x * (-lam * ∑ i, 2 * (x i - y i) * ξ i) := by
  rw [(hasFDerivAt_barrierExp lam y x).fderiv]
  simp only [_root_.smul_apply, _root_.sum_apply, smul_eq_mul,
    proj_apply', Finset.mul_sum]

/-- The first partials of the exponential part. -/
theorem partialD_barrierExp (lam : ℝ) (y : EuclideanSpace ℝ (Fin d)) (i : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    partialD i (barrierExp lam y) x = -2 * lam * (x i - y i) * barrierExp lam y x := by
  simp only [partialD, fderiv_barrierExp_apply, PiLp.single_apply]
  classical
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    ring
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The first partials of the exponential part, as functions. -/
theorem partialD_barrierExp_eq (lam : ℝ) (y : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    partialD i (barrierExp lam y) = fun x => (-2 * lam) * ((x i - y i) * barrierExp lam y x) := by
  funext x
  rw [partialD_barrierExp]
  ring

/-- The second partials of the exponential part. -/
theorem partialD_partialD_barrierExp (lam : ℝ) (y : EuclideanSpace ℝ (Fin d)) (i j : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    partialD i (partialD j (barrierExp lam y)) x
      = (-2 * lam * (if j = i then 1 else 0)
          + 4 * lam ^ 2 * (x j - y j) * (x i - y i)) * barrierExp lam y x := by
  rw [partialD_barrierExp_eq]
  simp only [partialD]
  have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => z j - y j)
      (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).hasFDerivAt.sub_const (y j)
  have h2 : HasFDerivAt
      (fun z : EuclideanSpace ℝ (Fin d) => -2 * lam * ((z j - y j) * barrierExp lam y z))
      ((-2 * lam) • ((x j - y j) • (barrierExp lam y x • ((-lam) • ∑ i, (2 * (x i - y i))
        • (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)))
        + barrierExp lam y x • (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))) x :=
    (h1.mul (hasFDerivAt_barrierExp lam y x)).const_mul (-2 * lam)
  rw [h2.fderiv]
  simp only [_root_.smul_apply, _root_.add_apply, smul_eq_mul,
    proj_apply', _root_.sum_apply, PiLp.single_apply]
  classical
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    ring
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The barrier `exp (-λ |x - y|²) - exp (-λ r²)`. -/
def barrier (lam r : ℝ) (y x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  barrierExp lam y x - Real.exp (-lam * r ^ 2)

/-- The barrier is smooth. -/
theorem contDiff_barrier (lam r : ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    ContDiff ℝ 2 (barrier lam r y) := by
  have hq : ContDiff ℝ 2 (sqDist y) := by
    unfold sqDist
    exact ContDiff.sum fun i _ =>
      ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff.sub
        contDiff_const).pow 2
  have he : ContDiff ℝ 2 (barrierExp lam y) :=
    Real.contDiff_exp.comp (contDiff_const.mul hq)
  exact he.sub contDiff_const

/-- The partials of the barrier are those of its exponential part. -/
theorem partialD_barrier (lam r : ℝ) (y : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    partialD i (barrier lam r y) = partialD i (barrierExp lam y) := by
  funext x
  have e : barrier lam r y = fun z => barrierExp lam y z - Real.exp (-lam * r ^ 2) := rfl
  simp only [partialD]
  rw [e, fderiv_sub_const]

/-- **Operator on the barrier.** -/
theorem nondivOp_barrier (a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d) → ℝ) (lam r : ℝ)
    (y x : EuclideanSpace ℝ (Fin d)) :
    nondivOp a b c (barrier lam r y) x
      = barrierExp lam y x * (2 * lam * ∑ i, a x i i
          - 4 * lam ^ 2 * ∑ i, ∑ j, a x i j * (x i - y i) * (x j - y j)
          - 2 * lam * ∑ i, b x i * (x i - y i)) + c x * barrier lam r y x := by
  classical
  unfold nondivOp
  simp only [partialD_barrier, partialD_partialD_barrierExp, partialD_barrierExp]
  set w : ℝ := barrierExp lam y x with hw
  have hterm : ∀ i j, a x i j * ((-2 * lam * (if j = i then 1 else 0)
      + 4 * lam ^ 2 * (x j - y j) * (x i - y i)) * w)
      = (if j = i then -2 * lam * w * a x i i else 0)
        + 4 * lam ^ 2 * w * (a x i j * (x i - y i) * (x j - y j)) := by
    intro i j
    split_ifs with h
    · subst h
      ring
    · ring
  have hdiag : ∑ i, ∑ j, a x i j * ((-2 * lam * (if j = i then 1 else 0)
      + 4 * lam ^ 2 * (x j - y j) * (x i - y i)) * w)
      = -2 * lam * w * ∑ i, a x i i
        + 4 * lam ^ 2 * w * ∑ i, ∑ j, a x i j * (x i - y i) * (x j - y j) := by
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.mul_sum]
  have hbsum : ∑ i, b x i * (-2 * lam * (x i - y i) * w)
      = -2 * lam * w * ∑ i, b x i * (x i - y i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hdiag, hbsum]
  ring

/-- **Barrier as a subsolution on the annulus** for `λ` large: with the bounds on the
coefficients and `r²/4 ≤ |x - y|² ≤ r²`. -/
theorem nondivOp_barrier_nonpos (hd : 0 < d)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ}
    {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ} {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ A B C : ℝ} (hθ : 0 < θ) {x y : EuclideanSpace ℝ (Fin d)}
    (hell : ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ i j, |a x i j| ≤ A) (hb : ∀ i, |b x i| ≤ B) (hc0 : 0 ≤ c x) (hcC : c x ≤ C)
    {r : ℝ} (hr : 0 < r) (hq1 : r ^ 2 / 4 ≤ sqDist y x) (hq2 : sqDist y x ≤ r ^ 2) {lam : ℝ}
    (hlam : (2 * d * A + B * (d + r ^ 2) + C) / (θ * r ^ 2) + 1 ≤ lam) :
    nondivOp a b c (barrier lam r y) x ≤ 0 := by
  rw [nondivOp_barrier]
  have hw := barrierExp_pos lam y x
  set i₀ : Fin d := ⟨0, hd⟩ with hi₀
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (ha i₀ i₀)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hb i₀)
  have hC0 : 0 ≤ C := hc0.trans hcC
  have hq0 : 0 ≤ sqDist y x := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- the three sums
  have hS1 : ∑ i, a x i i ≤ d * A := by
    calc ∑ i, a x i i ≤ ∑ _i : Fin d, A :=
          Finset.sum_le_sum fun i _ => (le_abs_self _).trans (ha i i)
      _ = d * A := by simp
  have hS2 : θ * sqDist y x ≤ ∑ i, ∑ j, a x i j * (x i - y i) * (x j - y j) := by
    have := hell fun i => x i - y i
    simpa [sqDist] using this
  have hS3 : -(B * (d + sqDist y x) / 2) ≤ ∑ i, b x i * (x i - y i) := by
    have hterm : ∀ i, -(B * (1 + (x i - y i) ^ 2) / 2) ≤ b x i * (x i - y i) := by
      intro i
      have h1 : |b x i * (x i - y i)| ≤ B * |x i - y i| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hb i) (abs_nonneg _)
      have h2 : |x i - y i| ≤ (1 + (x i - y i) ^ 2) / 2 := by
        nlinarith [sq_nonneg (|x i - y i| - 1), sq_abs (x i - y i)]
      have h3 := neg_abs_le (b x i * (x i - y i))
      nlinarith
    have hsum : ∑ i, -(B * (1 + (x i - y i) ^ 2) / 2) = -(B * (d + sqDist y x) / 2) := by
      simp only [sqDist, Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.mul_sum,
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
    rw [← hsum]
    exact Finset.sum_le_sum fun i _ => hterm i
  -- the choice of `λ`
  have hθr : 0 < θ * r ^ 2 := by positivity
  have hlam0 : 0 ≤ (2 * d * A + B * (d + r ^ 2) + C) / (θ * r ^ 2) :=
    div_nonneg (add_nonneg (add_nonneg (mul_nonneg (by positivity) hA0)
      (mul_nonneg hB0 (by positivity))) hC0) hθr.le
  have hlam1 : 1 ≤ lam := by linarith
  have hlam_pos : 0 < lam := by linarith
  have hkey : (2 * d * A + B * (d + r ^ 2) + C) / (θ * r ^ 2) * (θ * r ^ 2)
      = 2 * d * A + B * (d + r ^ 2) + C := div_mul_cancel₀ _ hθr.ne'
  have hbr : lam * (2 * d * A + B * (d + sqDist y x)) + C - 4 * lam ^ 2 * θ * sqDist y x ≤ 0 := by
    have h1 : lam * θ * r ^ 2 ≥ 2 * d * A + B * (d + r ^ 2) + C + θ * r ^ 2 := by
      have := mul_le_mul_of_nonneg_right hlam hθr.le
      nlinarith
    have h2 : 4 * lam * θ * sqDist y x ≥ lam * θ * r ^ 2 := by
      have := mul_le_mul_of_nonneg_left hq1 (by positivity : 0 ≤ 4 * lam * θ)
      nlinarith
    have h3 : B * (d + sqDist y x) ≤ B * (d + r ^ 2) := by
      exact mul_le_mul_of_nonneg_left (by linarith) hB0
    have h4 : lam * (4 * lam * θ * sqDist y x) ≥ lam * (lam * θ * r ^ 2) :=
      mul_le_mul_of_nonneg_left h2 hlam_pos.le
    have h5 : lam * (lam * θ * r ^ 2) ≥ lam * (2 * d * A + B * (d + r ^ 2) + C + θ * r ^ 2) :=
      mul_le_mul_of_nonneg_left h1 hlam_pos.le
    have h6 : lam * C ≥ C := by nlinarith
    nlinarith
  -- the zeroth-order term is at most `C` times the exponential part
  have hbar_nonneg : 0 ≤ barrier lam r y x := by
    simp only [barrier, barrierExp, sub_nonneg]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hbar_le : barrier lam r y x ≤ barrierExp lam y x := by
    simp only [barrier, barrierExp]
    linarith [Real.exp_pos (-lam * r ^ 2)]
  have hcv : c x * barrier lam r y x ≤ C * barrierExp lam y x :=
    (mul_le_mul_of_nonneg_right hcC hbar_nonneg).trans (mul_le_mul_of_nonneg_left hbar_le hC0)
  have hX : 2 * lam * ∑ i, a x i i
      - 4 * lam ^ 2 * ∑ i, ∑ j, a x i j * (x i - y i) * (x j - y j)
      - 2 * lam * ∑ i, b x i * (x i - y i) + C ≤ 0 := by
    have e1 : 2 * lam * ∑ i, a x i i ≤ 2 * lam * (d * A) :=
      mul_le_mul_of_nonneg_left hS1 (by positivity)
    have e2 : 4 * lam ^ 2 * (θ * sqDist y x)
        ≤ 4 * lam ^ 2 * ∑ i, ∑ j, a x i j * (x i - y i) * (x j - y j) :=
      mul_le_mul_of_nonneg_left hS2 (by positivity)
    have e3 : 2 * lam * (-(B * (d + sqDist y x) / 2)) ≤ 2 * lam * ∑ i, b x i * (x i - y i) :=
      mul_le_mul_of_nonneg_left hS3 (by positivity)
    nlinarith only [hbr, e1, e2, e3]
  calc barrierExp lam y x * (2 * lam * ∑ i, a x i i
        - 4 * lam ^ 2 * ∑ i, ∑ j, a x i j * (x i - y i) * (x j - y j)
        - 2 * lam * ∑ i, b x i * (x i - y i)) + c x * barrier lam r y x
      ≤ barrierExp lam y x * (2 * lam * ∑ i, a x i i
        - 4 * lam ^ 2 * ∑ i, ∑ j, a x i j * (x i - y i) * (x j - y j)
        - 2 * lam * ∑ i, b x i * (x i - y i)) + C * barrierExp lam y x := by linarith
    _ = barrierExp lam y x * (2 * lam * ∑ i, a x i i
        - 4 * lam ^ 2 * ∑ i, ∑ j, a x i j * (x i - y i) * (x j - y j)
        - 2 * lam * ∑ i, b x i * (x i - y i) + C) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw.le hX

/-! ### Hopf's lemma -/

/-- **One-sided derivative at a right-sided maximum.** -/
theorem deriv_nonpos_of_le_on_Ioo {φ : ℝ → ℝ} {φ' δ : ℝ} (hδ : 0 < δ) (hφ : HasDerivAt φ φ' 0)
    (hle : ∀ t ∈ Ioo (0 : ℝ) δ, φ t ≤ φ 0) : φ' ≤ 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero] at hφ
  have h := tendsto_nhdsWithin_mono_left
    (fun t (ht : t ∈ Ioi (0 : ℝ)) => Set.mem_compl_singleton_iff.mpr (ne_of_gt ht)) hφ
  refine le_of_tendsto h ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
  simp only [zero_add, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.1.le) (by linarith [hle t ht])

/-- **Hopf's lemma on a ball** (Evans §6.4.2 Lemma, Gilbarg and Trudinger Lemma 3.4). A
subsolution on a ball, continuous on the closed ball, strictly below its value at a point
`x₀` of the sphere throughout the ball, and differentiable at `x₀`, has positive derivative
at `x₀` in the outward radial direction `x₀ - y`. The zeroth-order coefficient is nonnegative
and bounded, and `c u(x₀) ≥ 0`, which covers the clause `c = 0` and the clause `c ≥ 0` with
`u(x₀) ≥ 0`. -/
theorem hopf_lemma_ball (hd : 0 < d) {y : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 < r)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ A B C : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ ball y r, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ ball y r, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ ball y r, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ ball y r, ∀ i, |b x i| ≤ B)
    (hc0 : ∀ x ∈ ball y r, 0 ≤ c x) (hcC : ∀ x ∈ ball y r, c x ≤ C)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u (ball y r))
    (huc : ContinuousOn u (closedBall y r))
    (hsub : ∀ x ∈ ball y r, nondivOp a b c u x ≤ 0)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : dist x₀ y = r) (hlt : ∀ x ∈ ball y r, u x < u x₀)
    (hcu : ∀ x ∈ ball y r, 0 ≤ c x * u x₀) (hdiff : DifferentiableAt ℝ u x₀) :
    0 < fderiv ℝ u x₀ (x₀ - y) := by
  classical
  set i₀ : Fin d := ⟨0, hd⟩ with hi₀
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (ha y (mem_ball_self hr) i₀ i₀)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hb y (mem_ball_self hr) i₀)
  have hC0 : 0 ≤ C := (hc0 y (mem_ball_self hr)).trans (hcC y (mem_ball_self hr))
  -- the annulus
  set R : Set (EuclideanSpace ℝ (Fin d)) := ball y r \ closedBall y (r / 2) with hRdef
  have hRo : IsOpen R := isOpen_ball.sdiff isClosed_closedBall
  have hRb : Bornology.IsBounded R := isBounded_ball.subset sdiff_subset
  have hRsub : R ⊆ ball y r := sdiff_subset
  have hnorm : ∀ c : ℝ, 0 < c → dist (y + c • e i₀) y = c := by
    intro c hc
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, PiLp.norm_single, norm_one, mul_one,
      Real.norm_eq_abs, abs_of_pos hc]
  have hRne : R.Nonempty := by
    refine ⟨y + (3 * r / 4) • e i₀, ?_, ?_⟩
    · rw [mem_ball, hnorm _ (by positivity)]
      linarith
    · rw [mem_closedBall, not_le, hnorm _ (by positivity)]
      linarith
  have hclR : closure R ⊆ closedBall y r := by
    refine (closure_mono hRsub).trans ?_
    rw [closure_ball y hr.ne']
  have hclR' : closure R ⊆ (ball y (r / 2))ᶜ := by
    have h1 : R ⊆ (closedBall y (r / 2))ᶜ := fun z hz => hz.2
    refine (closure_mono h1).trans ?_
    rw [closure_compl, interior_closedBall y (by positivity)]
  have hfrR : ∀ z ∈ frontier R, dist z y = r ∨ dist z y = r / 2 := by
    intro z hz
    have h1 : z ∈ closure R := frontier_subset_closure hz
    have h2 : z ∉ R := by
      rw [← hRo.interior_eq]
      exact hz.2
    have h3 : dist z y ≤ r := hclR h1
    have h4 : r / 2 ≤ dist z y := by
      have := hclR' h1
      rw [mem_compl_iff, mem_ball, not_lt] at this
      exact this
    rcases lt_or_eq_of_le h3 with h3' | h3'
    · rcases lt_or_eq_of_le h4 with h4' | h4'
      · exact absurd ⟨mem_ball.mpr h3', fun h => absurd (mem_closedBall.mp h) (not_le.mpr h4')⟩ h2
      · exact Or.inr h4'.symm
    · exact Or.inl h3'
  -- the inner sphere: `u` is below `u x₀` by a margin `δ`
  have hsph : IsCompact (sphere y (r / 2)) := isCompact_sphere y (r / 2)
  have hsphne : (sphere y (r / 2)).Nonempty :=
    ⟨y + (r / 2) • e i₀, by rw [mem_sphere, hnorm _ (by positivity)]⟩
  have hsphsub : sphere y (r / 2) ⊆ closedBall y r :=
    sphere_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  obtain ⟨s, hs, hsmax⟩ := hsph.exists_isMaxOn hsphne (huc.mono hsphsub)
  have hsball : s ∈ ball y r := by
    rw [mem_sphere] at hs
    rw [mem_ball, hs]
    linarith
  set δ : ℝ := u x₀ - u s with hδ
  have hδpos : 0 < δ := by linarith [hlt s hsball]
  -- the barrier constants
  set lam : ℝ := (2 * d * A + B * (d + r ^ 2) + C) / (θ * r ^ 2) + 1 with hlam
  have hlam_pos : 0 < lam := by
    have : 0 ≤ (2 * d * A + B * (d + r ^ 2) + C) / (θ * r ^ 2) :=
      div_nonneg (add_nonneg (add_nonneg (mul_nonneg (by positivity) hA0)
        (mul_nonneg hB0 (by positivity))) hC0) (by positivity)
    linarith
  set vmax : ℝ := Real.exp (-lam * (r / 2) ^ 2) - Real.exp (-lam * r ^ 2) with hvmax
  have hvmax_pos : 0 < vmax := by
    rw [hvmax, sub_pos]
    apply Real.exp_lt_exp.mpr
    have hsq : (r / 2) ^ 2 < r ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left hsq hlam_pos]
  set ε : ℝ := δ / (2 * vmax) with hε
  have hεpos : 0 < ε := by positivity
  have hv_outer : ∀ z, dist z y = r → barrier lam r y z = 0 := by
    intro z hz
    simp only [barrier, barrierExp, sqDist_eq]
    rw [← dist_eq_norm, hz, sub_self]
  have hv_le : ∀ z, r / 2 ≤ dist z y → barrier lam r y z ≤ vmax := by
    intro z hz
    simp only [barrier, barrierExp, sqDist_eq, hvmax]
    rw [← dist_eq_norm]
    have : -lam * dist z y ^ 2 ≤ -lam * (r / 2) ^ 2 := by
      have h1 : (r / 2) ^ 2 ≤ dist z y ^ 2 := by nlinarith [dist_nonneg (x := z) (y := y)]
      nlinarith
    linarith [Real.exp_le_exp.mpr this]
  -- `u + ε v` is a subsolution on the annulus
  have hvC : ContDiff ℝ 2 (barrier lam r y) := contDiff_barrier lam r y
  have hgC2 : ContDiffOn ℝ 2 (fun x => u x + ε * barrier lam r y x) R :=
    (hu.mono hRsub).add (contDiffOn_const.mul hvC.contDiffOn)
  have hgsub : ∀ z ∈ R,
      nondivOp a b c (fun x => u x + ε * barrier lam r y x - u x₀) z ≤ 0 := by
    intro z hz
    have hzb := hRsub hz
    rw [nondivOp_sub_const hRo hgC2 a b c (u x₀) hz,
      nondivOp_add_smul hRo (hu.mono hRsub) hvC.contDiffOn a b c ε hz]
    have h1 := hsub z hzb
    have h0 := hcu z hzb
    have h2 : nondivOp a b c (barrier lam r y) z ≤ 0 := by
      refine nondivOp_barrier_nonpos hd hθ (hell z hzb) (ha z hzb) (hb z hzb) (hc0 z hzb)
        (hcC z hzb) hr ?_ ?_ le_rfl
      · rw [sqDist_eq, ← dist_eq_norm]
        have := hz.2
        rw [mem_closedBall, not_le] at this
        nlinarith
      · rw [sqDist_eq, ← dist_eq_norm]
        have := hz.1
        rw [mem_ball] at this
        nlinarith [dist_nonneg (x := z) (y := y)]
    nlinarith
  -- the weak maximum principle on the annulus
  have hgc : ContinuousOn (fun x => u x + ε * barrier lam r y x - u x₀) (closure R) :=
    ((huc.mono hclR).add (continuousOn_const.mul hvC.continuous.continuousOn)).sub
      continuousOn_const
  have hgC2' : ContDiffOn ℝ 2 (fun x => u x + ε * barrier lam r y x - u x₀) R :=
    hgC2.sub contDiffOn_const
  obtain ⟨z, hzfr, hzmax⟩ := weak_maximum_principle_of_nonneg hd hRo hRb hRne hθ
    (fun x hx => hsymm x (hRsub hx)) (fun x hx => hell x (hRsub hx))
    (fun x hx => hb x (hRsub hx)) (fun x hx => hc0 x (hRsub hx)) hgC2' hgc hgsub
  have hgbound : ∀ x ∈ closure R, u x + ε * barrier lam r y x ≤ u x₀ := by
    intro x hx
    have hx' := hzmax x hx
    have hz' : u z + ε * barrier lam r y z - u x₀ ≤ 0 := by
      rcases hfrR z hzfr with hz | hz
      · have huz : u z ≤ u x₀ := by
          have hzcl : z ∈ closure (ball y r) := by
            rw [closure_ball y hr.ne']
            exact mem_closedBall.mpr hz.le
          obtain ⟨w, hw, hwz⟩ := mem_closure_iff_seq_limit.mp hzcl
          have h1 : Tendsto w atTop (𝓝[closedBall y r] z) :=
            tendsto_nhdsWithin_iff.mpr
              ⟨hwz, Eventually.of_forall fun n => ball_subset_closedBall (hw n)⟩
          have hcont : Tendsto (fun n => u (w n)) atTop (𝓝 (u z)) :=
            (huc z (mem_closedBall.mpr hz.le)).tendsto.comp h1
          exact le_of_tendsto' hcont fun n => (hlt (w n) (hw n)).le
        rw [hv_outer z hz, mul_zero, add_zero]
        linarith
      · have h1 : u z ≤ u s := hsmax (mem_sphere.mpr hz)
        have h2 : barrier lam r y z ≤ vmax := hv_le z hz.ge
        have h3 : ε * barrier lam r y z ≤ δ / 2 := by
          calc ε * barrier lam r y z ≤ ε * vmax := mul_le_mul_of_nonneg_left h2 hεpos.le
            _ = δ / 2 := by
                rw [hε]
                field_simp
        linarith
    rw [max_eq_right hz'] at hx'
    linarith
  -- the one-sided derivative along the inward radius
  set ξ : EuclideanSpace ℝ (Fin d) := y - x₀ with hξ
  have hpt : ∀ t ∈ Ioo (0 : ℝ) (1 / 2), x₀ + t • ξ ∈ R := by
    intro t ht
    have hdist : dist (x₀ + t • ξ) y = (1 - t) * r := by
      rw [dist_eq_norm, hξ]
      have e : x₀ + t • (y - x₀) - y = (1 - t) • (x₀ - y) := by
        simp only [sub_smul, one_smul, smul_sub]
        abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [ht.2]), ← dist_eq_norm, hx₀]
    constructor
    · rw [mem_ball, hdist]
      nlinarith [ht.1]
    · rw [mem_closedBall, not_le, hdist]
      nlinarith [ht.2]
  have hφ : HasDerivAt (fun t : ℝ => u (x₀ + t • ξ) + ε * barrier lam r y (x₀ + t • ξ))
      (fderiv ℝ u x₀ ξ + ε * fderiv ℝ (barrier lam r y) x₀ ξ) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => u (x₀ + t • ξ)) (fderiv ℝ u (x₀ + (0 : ℝ) • ξ) ξ) 0 :=
      hasDerivAt_line (by simpa using hdiff)
    have h2 : HasDerivAt (fun t : ℝ => barrier lam r y (x₀ + t • ξ))
        (fderiv ℝ (barrier lam r y) (x₀ + (0 : ℝ) • ξ) ξ) 0 :=
      hasDerivAt_line (hvC.differentiable (by simp) _)
    have := h1.add (h2.const_mul ε)
    simp only [zero_smul, add_zero] at this
    exact this
  have hle : ∀ t ∈ Ioo (0 : ℝ) (1 / 2),
      (fun t : ℝ => u (x₀ + t • ξ) + ε * barrier lam r y (x₀ + t • ξ)) t
        ≤ (fun t : ℝ => u (x₀ + t • ξ) + ε * barrier lam r y (x₀ + t • ξ)) 0 := by
    intro t ht
    have := hgbound _ (subset_closure (hpt t ht))
    simp only [zero_smul, add_zero]
    rw [hv_outer x₀ hx₀, mul_zero, add_zero]
    exact this
  have hder := deriv_nonpos_of_le_on_Ioo (by norm_num : (0 : ℝ) < 1 / 2) hφ hle
  -- the derivative of the barrier at `x₀` along `ξ`
  have hvder : fderiv ℝ (barrier lam r y) x₀ ξ = 2 * lam * r ^ 2 * barrierExp lam y x₀ := by
    have hfv : fderiv ℝ (barrier lam r y) x₀ = fderiv ℝ (barrierExp lam y) x₀ := by
      have e : barrier lam r y = fun z => barrierExp lam y z - Real.exp (-lam * r ^ 2) := rfl
      rw [e]
      exact fderiv_sub_const _
    rw [hfv, fderiv_barrierExp_apply, hξ]
    have hsq : ∑ i, (x₀ i - y i) ^ 2 = r ^ 2 := by
      have := sqDist_eq y x₀
      rw [sqDist, ← dist_eq_norm, hx₀] at this
      exact this
    have hsum : ∑ i, 2 * (x₀ i - y i) * (y - x₀) i = -2 * r ^ 2 := by
      calc ∑ i, 2 * (x₀ i - y i) * (y - x₀) i = ∑ i, -2 * (x₀ i - y i) ^ 2 :=
            Finset.sum_congr rfl fun i _ => by rw [PiLp.sub_apply]; ring
        _ = -2 * r ^ 2 := by rw [← Finset.mul_sum, hsq]
    rw [hsum]
    ring
  have hexp := barrierExp_pos lam y x₀
  have hfu : fderiv ℝ u x₀ ξ = -fderiv ℝ u x₀ (x₀ - y) := by
    rw [hξ, ← neg_sub, map_neg]
  rw [hfu, hvder] at hder
  have hpos : 0 < ε * (2 * lam * r ^ 2 * barrierExp lam y x₀) := by positivity
  linarith

/-- **Hopf's lemma** (Evans §6.4.2 Lemma, Gilbarg and Trudinger Lemma 3.4). A subsolution on
an open set, continuous on its closure, strictly below its value at a point `x₀` throughout the
set, and differentiable at `x₀`, has positive derivative at `x₀` in the outward direction of any
ball inside the set whose sphere passes through `x₀`. The zeroth-order coefficient is
nonnegative and bounded with `c u(x₀) ≥ 0`, which covers both clauses of the sources. -/
theorem hopf_lemma (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {θ A B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    {c : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} (hc0 : ∀ x ∈ U, 0 ≤ c x) (hcC : ∀ x ∈ U, c x ≤ C)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, nondivOp a b c u x ≤ 0)
    {x₀ y : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 < r) (hball : ball y r ⊆ U)
    (hx₀ : dist x₀ y = r) (hlt : ∀ x ∈ U, u x < u x₀) (hcu : ∀ x ∈ U, 0 ≤ c x * u x₀)
    (hdiff : DifferentiableAt ℝ u x₀) :
    0 < fderiv ℝ u x₀ (x₀ - y) := by
  have hcl : closedBall y r ⊆ closure U := by
    rw [← closure_ball y hr.ne']
    exact closure_mono hball
  exact hopf_lemma_ball hd hr hθ (fun x hx => hsymm x (hball hx)) (fun x hx => hell x (hball hx))
    (fun x hx => ha x (hball hx)) (fun x hx => hb x (hball hx)) (fun x hx => hc0 x (hball hx))
    (fun x hx => hcC x (hball hx)) (hu.mono hball) (huc.mono hcl)
    (fun x hx => hsub x (hball hx)) hx₀ (fun x hx => hlt x (hball hx))
    (fun x hx => hcu x (hball hx)) hdiff

/-! ### The strong maximum principle -/

/-- **Strong maximum principle** (Evans §6.4.2 Theorem 3, Gilbarg and Trudinger Theorem 3.5).
A subsolution, `C²` on a connected open set, that attains its maximum over the set at an
interior point is constant on the set. The zeroth-order coefficient is nonnegative and bounded
with `c` times the maximum nonnegative, which covers the clause `c = 0` and the clause `c ≥ 0`
with a nonnegative maximum. -/
theorem strong_maximum_principle (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ A B C : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    (hc0 : ∀ x ∈ U, 0 ≤ c x) (hcC : ∀ x ∈ U, c x ≤ C)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hsub : ∀ x ∈ U, nondivOp a b c u x ≤ 0)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : x₀ ∈ U) (hmax : ∀ x ∈ U, u x ≤ u x₀)
    (hcu : ∀ x ∈ U, 0 ≤ c x * u x₀) :
    ∀ x ∈ U, u x = u x₀ := by
  classical
  by_contra hne
  simp only [not_forall, exists_prop] at hne
  obtain ⟨x₁, hx₁U, hx₁⟩ := hne
  -- the set where `u` is below the maximum
  set V : Set (EuclideanSpace ℝ (Fin d)) := U ∩ u ⁻¹' Iio (u x₀) with hVdef
  have hVo : IsOpen V := hu.continuousOn.isOpen_inter_preimage hU isOpen_Iio
  have hVU : V ⊆ U := inter_subset_left
  have hx₁V : x₁ ∈ V := ⟨hx₁U, lt_of_le_of_ne (hmax x₁ hx₁U) hx₁⟩
  -- a point of the set on the frontier of `V`
  have hnot : ¬ U ⊆ V := fun h => by
    have : u x₀ < u x₀ := (h hx₀).2
    exact lt_irrefl _ this
  have hex : ∃ z ∈ U, z ∈ closure V ∧ z ∉ V := by
    by_contra hcon
    apply hnot
    refine hUc.subset_of_closure_inter_subset hVo ⟨x₁, hx₁U, hx₁V⟩ fun z hz => ?_
    by_contra hzV
    exact hcon ⟨z, hz.2, hz.1, hzV⟩
  obtain ⟨z, hzU, hzcl, hzV⟩ := hex
  have hzM : u z = u x₀ := le_antisymm (hmax z hzU) (not_lt.mp fun h => hzV ⟨hzU, h⟩)
  -- a ball about `z` in the set, and a point of `V` near `z`
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU z hzU
  obtain ⟨y, hyV, hyz⟩ := Metric.mem_closure_iff.mp hzcl (ρ / 2) (by positivity)
  have hyM : u y < u x₀ := hyV.2
  have hcb : closedBall y (ρ / 2) ⊆ U :=
    (closedBall_subset_ball' (by rw [dist_comm]; linarith)).trans hρU
  -- the level set of the maximum near `y`
  set K : Set (EuclideanSpace ℝ (Fin d)) := closedBall y (ρ / 2) ∩ u ⁻¹' {u x₀} with hKdef
  have hKclosed : IsClosed K :=
    (hu.continuousOn.mono hcb).preimage_isClosed_of_isClosed isClosed_closedBall
      isClosed_singleton
  have hKc : IsCompact K :=
    (isCompact_closedBall y (ρ / 2)).of_isClosed_subset hKclosed inter_subset_left
  have hzy : dist z y ≤ ρ / 2 := hyz.le
  have hKne : K.Nonempty := ⟨z, mem_closedBall.mpr hzy, hzM⟩
  obtain ⟨x₂, hx₂K, hx₂d⟩ := hKc.exists_infDist_eq_dist hKne y
  set r : ℝ := infDist y K with hr
  have hyK : y ∉ K := fun h => hyM.ne h.2
  have hzK : z ∈ K := ⟨mem_closedBall.mpr hzy, hzM⟩
  have hrpos : 0 < r := by
    rw [hr]
    refine (infDist_pos_iff_notMem_closure hKne).mp ?_
    rw [hKclosed.closure_eq]
    exact hyK
  have hrle : r ≤ ρ / 2 := by
    rw [hr]
    exact (infDist_le_dist_of_mem hzK).trans (by rw [dist_comm]; exact hzy)
  -- the ball of radius `r` about `y` lies below the maximum
  have hballU : ball y r ⊆ U :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hrle)).trans hcb
  have hballV : ∀ x ∈ ball y r, u x < u x₀ := by
    intro x hx
    have hxU : x ∈ U := hballU hx
    rcases lt_or_eq_of_le (hmax x hxU) with h | h
    · exact h
    · exfalso
      have hxK : x ∈ K := ⟨mem_closedBall.mpr ((mem_ball.mp hx).le.trans hrle), h⟩
      have : infDist y K ≤ dist y x := infDist_le_dist_of_mem hxK
      rw [← hr, dist_comm] at this
      exact absurd (mem_ball.mp hx) (not_lt.mpr this)
  -- Hopf's lemma at the touching point
  have hx₂dist : dist x₂ y = r := by
    rw [dist_comm]
    exact hx₂d.symm
  have hx₂M : u x₂ = u x₀ := hx₂K.2
  have hx₂U : x₂ ∈ U := hcb hx₂K.1
  have hdiff : DifferentiableAt ℝ u x₂ :=
    (hu.contDiffAt (hU.mem_nhds hx₂U)).differentiableAt (by simp)
  have hhopf := hopf_lemma_ball hd hrpos hθ (fun x hx => hsymm x (hballU hx))
    (fun x hx => hell x (hballU hx)) (fun x hx => ha x (hballU hx))
    (fun x hx => hb x (hballU hx)) (fun x hx => hc0 x (hballU hx))
    (fun x hx => hcC x (hballU hx)) (hu.mono hballU)
    (hu.continuousOn.mono ((closedBall_subset_closedBall hrle).trans hcb))
    (fun x hx => hsub x (hballU hx)) hx₂dist (fun x hx => by rw [hx₂M]; exact hballV x hx)
    (fun x hx => by rw [hx₂M]; exact hcu x (hballU hx)) hdiff
  -- but `x₂` is an interior maximum, so the gradient vanishes there
  have hloc : IsLocalMax u x₂ := by
    have hmax' : IsMaxOn u U x₂ := fun x hx => by
      rw [hx₂M]
      exact hmax x hx
    exact hmax'.isLocalMax (hU.mem_nhds hx₂U)
  rw [hloc.fderiv_eq_zero] at hhopf
  simp at hhopf

/-- **Strong maximum principle with nonnegative zeroth-order coefficient** (Evans §6.4.2
Theorem 3(ii)). With `c ≥ 0`, a subsolution that attains a nonnegative maximum at an interior
point of a connected open set is constant on the set. -/
theorem strong_maximum_principle_of_nonneg (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ A B C : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    (hc0 : ∀ x ∈ U, 0 ≤ c x) (hcC : ∀ x ∈ U, c x ≤ C)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hsub : ∀ x ∈ U, nondivOp a b c u x ≤ 0)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : x₀ ∈ U) (hmax : ∀ x ∈ U, u x ≤ u x₀)
    (hu0 : 0 ≤ u x₀) : ∀ x ∈ U, u x = u x₀ :=
  strong_maximum_principle hd hU hUc hθ hsymm hell ha hb hc0 hcC hu hsub hx₀ hmax
    fun x hx => mul_nonneg (hc0 x hx) hu0

end EllipticPdes.Classical
