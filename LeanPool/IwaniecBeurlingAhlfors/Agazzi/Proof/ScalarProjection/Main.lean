/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Proof.ScalarProjection.Existence
public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Minors.Periodic
public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.ZeroSet
public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.FDeriv
public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.FundamentalDomain
public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.Periodize

/-!
# §2: the scalar projection lemma (Lemma 4)

For `K ⊂ ℝ²` nonempty, compact and convex, `p ∈ K` and `η ∈ W^{1,∞}_per (Q)`, let
`v (x) = p · x + η (x)` and let `ζ` be the `L² (Q)`-projection of `η` on
`𝒞 = {ξ ∈ W^{1,∞}_per (Q) : p + Dξ ∈ K a.e.}`. Then `w (x) = p · x + ζ (x)` satisfies `Dw = Dv` or
`Dw ∈ ∂K` almost everywhere, and `∫_Q Dw · (Dv − Dw) ≥ 0` (`(eq:projection-integral-sign)`).

The objects and the representation choices are in `Agazzi.Proof.ScalarProjection.Defs`; the
existence of the projection and the variational inequality in
`Agazzi.Proof.ScalarProjection.Existence`.

The proof (TeX lines 417–443) in steps, with `h = η − ζ`:

* `lemma4_step1`: `Dw = Dv` a.e. on `{h = 0}` (the gradient of the Lipschitz `h` vanishes a.e. on
  its zero set);
* `lemma4_step2`: `Dw (x₀) ∉ int K` where `h (x₀) ≠ 0` and `w` is differentiable at `x₀`, by the
  competitor `ζ + (c − w)_+` with the cone `c (x) = w (x₀) + ε − H (x₀ − x)`
  (`lemma4_step2_core`); then the first assertion, `lemma4_first`;
* `lemma4_step3_diff`, `lemma4_step3_partial`, `lemma4_step3`: the second differences of the
  variational inequality, `∫_Q ∂_i h ∂_i ζ ≥ 0`, and `(eq:projection-integral-sign)`.

Norms on `ℝ² = Fin 2 → ℝ` are Mathlib's sup norm, and balls are sup-norm balls: the paper's
Euclidean `|y|` and `B_ρ (b₀)` become `‖y‖` and sup-norm balls, the argument being the same for
any norm.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology CalculusOfVariations

namespace Agazzi

variable {K : Set (Fin 2 → ℝ)} {p : Fin 2 → ℝ}

/-! ### Preliminaries: the gradient `sgrad`, the unit square -/

private lemma lem4_unitSquare_eq : unitSquare = CalculusOfVariations.unitCube 2 := rfl

private lemma lem4_measurableSet_unitSquare : MeasurableSet unitSquare :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

private lemma lem4_isOpen_unitSquare : IsOpen unitSquare :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

private lemma lem4_volume_unitSquare : volume unitSquare = 1 := by
  simp [unitSquare, Real.volume_pi_Ioo]

private lemma lem4_integrableOn_of_continuous {f : (Fin 2 → ℝ) → ℝ} (hf : Continuous f) :
    IntegrableOn f unitSquare :=
  (hf.integrableOn_Icc (a := 0) (b := 1)).mono_set fun _ hx =>
    ⟨fun i => (hx i (Set.mem_univ i)).1.le, fun i => (hx i (Set.mem_univ i)).2.le⟩

/-- A measurable function bounded by `C` is integrable on the unit square. -/
private lemma lem4_integrableOn_of_bound {f : (Fin 2 → ℝ) → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) : IntegrableOn f unitSquare :=
  IntegrableOn.of_bound (by rw [lem4_volume_unitSquare]; exact ENNReal.one_lt_top)
    hf.aestronglyMeasurable C (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

/-- `|∂_v f| ≤ C ‖v‖` for a `C`-Lipschitz `f`. -/
private lemma lem4_abs_fderiv_le {f : (Fin 2 → ℝ) → ℝ} {C : NNReal} (hf : LipschitzWith C f)
    (x v : Fin 2 → ℝ) : |fderiv ℝ f x v| ≤ C * ‖v‖ := by
  rw [← Real.norm_eq_abs]
  exact ((fderiv ℝ f x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg v))

/-- `y ↦ p · y` as a continuous linear map. -/
private def lem4Dot (p : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ∑ j, p j • ContinuousLinearMap.proj j

private lemma lem4Dot_apply (p y : Fin 2 → ℝ) : lem4Dot p y = p ⬝ᵥ y := by
  simp [lem4Dot, dotProduct]

/-- A linear functional is the dot product with its gradient. -/
private lemma lem4_apply_eq_dotProduct (L : (Fin 2 → ℝ) →L[ℝ] ℝ) (y : Fin 2 → ℝ) :
    L y = (fun j => L (Pi.single j 1)) ⬝ᵥ y := by
  conv_lhs => rw [← Finset.univ_sum_single y]
  simp only [map_sum, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (Pi.single j (y j) : Fin 2 → ℝ) = y j • Pi.single j 1 by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]

private lemma lem4_fderiv_apply_eq (f : (Fin 2 → ℝ) → ℝ) (x y : Fin 2 → ℝ) :
    fderiv ℝ f x y = sgrad f x ⬝ᵥ y :=
  lem4_apply_eq_dotProduct _ y

private lemma sgrad_congr {f g : (Fin 2 → ℝ) → ℝ} {x : Fin 2 → ℝ} (h : f =ᶠ[𝓝 x] g) :
    sgrad f x = sgrad g x := by
  unfold sgrad; rw [h.fderiv_eq]

private lemma sgrad_comp_add (f : (Fin 2 → ℝ) → ℝ) (a x : Fin 2 → ℝ) :
    sgrad (fun y => f (y + a)) x = sgrad f (x + a) := by
  unfold sgrad; rw [fderiv_comp_add_right]

private lemma sgrad_add_const (f : (Fin 2 → ℝ) → ℝ) (c : ℝ) (x : Fin 2 → ℝ) :
    sgrad (fun y => f y + c) x = sgrad f x := by
  unfold sgrad; rw [fderiv_add_const]

private lemma sgrad_const_mul {f : (Fin 2 → ℝ) → ℝ} {x : Fin 2 → ℝ}
    (hf : DifferentiableAt ℝ f x) (s : ℝ) : sgrad (fun y => s * f y) x = s • sgrad f x := by
  ext j; simp [sgrad, fderiv_const_mul hf s]

private lemma hasFDerivAt_dot_add {f : (Fin 2 → ℝ) → ℝ} {x : Fin 2 → ℝ}
    (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (fun y => p ⬝ᵥ y + f y) (lem4Dot p + fderiv ℝ f x) x := by
  refine ((lem4Dot p).hasFDerivAt.add hf.hasFDerivAt).congr_of_eventuallyEq
    (Eventually.of_forall fun y => ?_)
  simp [lem4Dot_apply]

/-- `D (p · y + f) = p + D f` where `f` is differentiable. -/
private lemma sgrad_dot_add {f : (Fin 2 → ℝ) → ℝ} {x : Fin 2 → ℝ}
    (hf : DifferentiableAt ℝ f x) : sgrad (fun y => p ⬝ᵥ y + f y) x = p + sgrad f x := by
  ext j
  simp only [sgrad, Pi.add_apply]
  rw [(hasFDerivAt_dot_add hf).fderiv, add_apply, lem4Dot_apply,
    dotProduct_single, mul_one]

private lemma sgrad_periodic {f : (Fin 2 → ℝ) → ℝ} (hf : IsPeriodic f) (x : Fin 2 → ℝ)
    (k : Fin 2 → ℤ) : sgrad f (x + fun i => (k i : ℝ)) = sgrad f x := by
  rw [← sgrad_comp_add]
  congr 1
  funext y
  exact hf y k

private lemma lem4_lipschitz_dot_add {f : (Fin 2 → ℝ) → ℝ} {C : NNReal} (hf : LipschitzWith C f) :
    ∃ C', LipschitzWith C' (fun y => p ⬝ᵥ y + f y) :=
  ⟨_, by simpa only [lem4Dot_apply] using (lem4Dot p).lipschitzWith.add hf⟩

/-- The constraint of `𝒞` holds almost everywhere on `ℝ²`, not only on the unit square: it is a
periodic property. -/
private lemma lemma4_ae_constraint {ξ : (Fin 2 → ℝ) → ℝ} (hξ : ξ ∈ constraintSet K p) :
    ∀ᵐ x ∂(volume : Measure (Fin 2 → ℝ)), p + sgrad ξ x ∈ K :=
  ae_of_ae_restrict_unitCube_of_periodic (fun x k h => by rwa [sgrad_periodic hξ.1.2] at h) hξ.2

/-! ### Step 1: `Dw = Dv` almost everywhere on `{h = 0}` -/

/-- **Step 1** (TeX line 417). With `h = η − ζ`, `Dw = Dv` almost everywhere on `{h = 0}`: the
gradient of the Lipschitz `h = v − w` vanishes almost everywhere on its zero set. -/
private lemma lemma4_step1 {η ζ : (Fin 2 → ℝ) → ℝ} (hη : LipPer η) (hζ : LipPer ζ) :
    ∀ᵐ x ∂(volume : Measure (Fin 2 → ℝ)), η x - ζ x = 0 →
      sgrad (fun y => p ⬝ᵥ y + ζ y) x = sgrad (fun y => p ⬝ᵥ y + η y) x := by
  obtain ⟨Cη, hηL⟩ := hη.1
  obtain ⟨Cζ, hζL⟩ := hζ.1
  filter_upwards [ae_fderiv_eq_zero_of_eq_zero (hηL.sub hζL), hηL.ae_differentiableAt,
    hζL.ae_differentiableAt] with x h0 hηd hζd hx
  have h1 := h0 hx
  rw [fderiv_fun_sub hηd hζd, sub_eq_zero] at h1
  rw [sgrad_dot_add hζd, sgrad_dot_add hηd]
  ext j
  simp [sgrad, h1]

/-! ### Step 2: `Dw ∈ ∂K` almost everywhere on `{h ≠ 0}` -/

/-- TeX lines 422–425: if `B_δ (b₀) ⊂ K`, then `H (y) ≥ b₀ · y + ρ ‖y‖` with `ρ = δ / 2`. -/
private lemma lemma4_choose_rho (hKc : IsCompact K) {b₀ : Fin 2 → ℝ} (hb : b₀ ∈ interior K) :
    ∃ ρ > 0, ∀ y, b₀ ⬝ᵥ y + ρ * ‖y‖ ≤ supportFun K y := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hb)
  refine ⟨δ / 2, by positivity, fun y => ?_⟩
  set u : Fin 2 → ℝ := fun j => if 0 ≤ y j then 1 else -1 with hu_def
  have hu : ‖u‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by
    simp only [hu_def]; split_ifs <;> simp
  have huy : ∀ j, u j * y j = |y j| := fun j => by
    simp only [hu_def]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (not_le.1 h)]
  have hmem : b₀ + (δ / 2) • u ∈ K := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    nlinarith [norm_nonneg u])
  have h1 := dotProduct_le_supportFun hKc hmem y
  have h2 : (b₀ + (δ / 2) • u) ⬝ᵥ y = b₀ ⬝ᵥ y + δ / 2 * (|y 0| + |y 1|) := by
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
    simp only [dotProduct, Fin.sum_univ_two, huy]
  have h3 : ‖y‖ ≤ |y 0| + |y 1| := (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => by
    fin_cases j <;> simp [Real.norm_eq_abs]
  nlinarith

/-- TeX lines 426–429: a radius `r < 1/2` with `h > 0` on `closedBall x₀ r` and
`|w (x) − w (x₀) − b₀ · (x − x₀)| ≤ (ρ/2) ‖x − x₀‖` there (`b₀ = Dw (x₀)`). The bound `r < 1/2`
makes the ball embed in the torus; the paper leaves it implicit. -/
private lemma lemma4_choose_r {w h : (Fin 2 → ℝ) → ℝ} {x₀ : Fin 2 → ℝ}
    (hw : DifferentiableAt ℝ w x₀) (hh : Continuous h) (hh0 : 0 < h x₀) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r, 0 < r ∧ r < 1 / 2 ∧ (∀ x, ‖x - x₀‖ ≤ r → 0 < h x) ∧
      ∀ x, ‖x - x₀‖ ≤ r → |w x - w x₀ - sgrad w x₀ ⬝ᵥ (x - x₀)| ≤ ρ / 2 * ‖x - x₀‖ := by
  have h1 := hw.hasFDerivAt.isLittleO.def (show 0 < ρ / 2 by positivity)
  have h2 : ∀ᶠ x in 𝓝 x₀, 0 < h x := (hh.tendsto x₀).eventually (lt_mem_nhds hh0)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (h1.and h2)
  have hlt : ∀ x, ‖x - x₀‖ ≤ min (δ / 2) (1 / 4) → dist x x₀ < δ := fun x hx => by
    rw [dist_eq_norm]; linarith [min_le_left (δ / 2) (1 / 4)]
  refine ⟨min (δ / 2) (1 / 4), by positivity, by linarith [min_le_right (δ / 2) (1 / 4)],
    fun x hx => (hδ' (hlt x hx)).2, fun x hx => ?_⟩
  have := (hδ' (hlt x hx)).1
  rwa [Real.norm_eq_abs, lem4_fderiv_apply_eq] at this

/-- The cone `c (x) = A − s H (s (x₀ − x))` is Lipschitz. -/
private lemma lemma4_cone_lipschitz (hKne : K.Nonempty) (hKc : IsCompact K) {s : ℝ}
    (hs : |s| = 1) (A : ℝ) (x₀ : Fin 2 → ℝ) :
    ∃ C, LipschitzWith C (fun x => A - s * supportFun K (s • (x₀ - x))) := by
  obtain ⟨C, hC⟩ := lipschitzWith_supportFun hKc hKne
  refine ⟨C, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [Real.dist_eq, show A - s * supportFun K (s • (x₀ - x)) - (A - s * supportFun K (s • (x₀ - y)))
    = -(s * (supportFun K (s • (x₀ - x)) - supportFun K (s • (x₀ - y)))) by ring, abs_neg,
    abs_mul, hs, one_mul, ← Real.dist_eq]
  calc dist (supportFun K (s • (x₀ - x))) (supportFun K (s • (x₀ - y)))
      ≤ C * dist (s • (x₀ - x)) (s • (x₀ - y)) := hC.dist_le_mul _ _
    _ = C * dist x y := by
      rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, hs, one_mul,
        show x₀ - x - (x₀ - y) = -(x - y) by abel, norm_neg]

/-- TeX line 433: the cone `c (x) = A − s H (s (x₀ − x))` (`s = ±1`) has gradient in `K`
wherever it is differentiable: `Dc (z) = DH (s (x₀ − z))`. -/
private lemma lemma4_cone_sgrad_mem (hKne : K.Nonempty) (hKc : IsCompact K) (hKcv : Convex ℝ K)
    {s : ℝ} (hs2 : s * s = 1) (A : ℝ) (x₀ : Fin 2 → ℝ) {z : Fin 2 → ℝ}
    (hz : DifferentiableAt ℝ (fun x => A - s * supportFun K (s • (x₀ - x))) z) :
    sgrad (fun x => A - s * supportFun K (s • (x₀ - x))) z ∈ K := by
  set c := fun x => A - s * supportFun K (s • (x₀ - x)) with hc_def
  set u₀ := s • (x₀ - z) with hu₀
  have hH_eq : supportFun K = fun u => s * (A - c (x₀ - s • u)) := by
    funext u
    simp only [hc_def, sub_sub_cancel, smul_smul, hs2, one_smul]
    rw [← mul_assoc, hs2, one_mul]
  have hHd : DifferentiableAt ℝ (supportFun K) u₀ := by
    rw [hH_eq]
    have hin : DifferentiableAt ℝ (fun u : Fin 2 → ℝ => x₀ - s • u) u₀ :=
      (differentiableAt_const _).sub ((differentiableAt_id).const_smul s)
    have hz' : DifferentiableAt ℝ c (x₀ - s • u₀) := by
      rw [hu₀, smul_smul, hs2, one_smul, sub_sub_cancel]; exact hz
    exact ((hz'.comp u₀ hin).const_sub A).const_mul s
  have hmem := gradient_supportFun_mem hKc hKne hKcv hHd
  have hin : HasFDerivAt (fun x : Fin 2 → ℝ => s • (x₀ - x))
      (s • -(ContinuousLinearMap.id ℝ (Fin 2 → ℝ))) z :=
    ((hasFDerivAt_id z).const_sub x₀).const_smul s
  have hcomp : HasFDerivAt (fun x => supportFun K (s • (x₀ - x)))
      ((fderiv ℝ (supportFun K) u₀).comp (s • -(ContinuousLinearMap.id ℝ (Fin 2 → ℝ)))) z :=
    HasFDerivAt.comp (g := supportFun K) (f := fun x : Fin 2 → ℝ => s • (x₀ - x)) z
      hHd.hasFDerivAt hin
  have hcd : HasFDerivAt c (-(s • ((fderiv ℝ (supportFun K) u₀).comp
      (s • -(ContinuousLinearMap.id ℝ (Fin 2 → ℝ)))))) z :=
    (hcomp.const_mul s).const_sub A
  convert hmem using 1
  ext j
  simp only [sgrad, hcd.fderiv]
  simp only [neg_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_neg, map_smul, smul_eq_mul]
  linear_combination (fderiv ℝ (supportFun K) u₀ (Pi.single j 1)) * hs2

/-- TeX lines 432–434: `s (c − w) ≤ ε − (ρ/2) ‖x − x₀‖` on `closedBall x₀ r`, for
`c (x) = w (x₀) + s ε − s H (s (x₀ − x))`. Hence `c < w` on `∂B_r (x₀)` (for `s = 1`) when
`ε < ρ r / 2`. -/
private lemma lemma4_cone_bound {b₀ : Fin 2 → ℝ} {ρ : ℝ}
    (hHρ : ∀ y, b₀ ⬝ᵥ y + ρ * ‖y‖ ≤ supportFun K y) {s : ℝ} (hs : s = 1 ∨ s = -1)
    {w : (Fin 2 → ℝ) → ℝ} {x₀ x : Fin 2 → ℝ} (ε : ℝ)
    (hw : |w x - w x₀ - b₀ ⬝ᵥ (x - x₀)| ≤ ρ / 2 * ‖x - x₀‖) :
    s * ((w x₀ + s * ε - s * supportFun K (s • (x₀ - x))) - w x) ≤ ε - ρ / 2 * ‖x - x₀‖ := by
  have hH := hHρ (s • (x₀ - x))
  have hn : ‖x₀ - x‖ = ‖x - x₀‖ := norm_sub_rev _ _
  have hd : b₀ ⬝ᵥ (x₀ - x) = -(b₀ ⬝ᵥ (x - x₀)) := by
    rw [← dotProduct_neg, neg_sub]
  have habs := abs_le.1 hw
  rcases hs with rfl | rfl
  · simp only [one_smul, one_mul, hn, hd] at hH ⊢
    linarith
  · simp only [neg_smul, one_smul, dotProduct_neg, norm_neg, hn, hd, neg_mul, one_mul,
      neg_neg] at hH ⊢
    linarith

/-- TeX line 434: `s (c (x₀) − w (x₀)) = ε`. -/
private lemma lemma4_cone_center (hKne : K.Nonempty) (hKc : IsCompact K) {s : ℝ}
    (hs2 : s * s = 1) (A ε : ℝ) (x₀ : Fin 2 → ℝ) :
    s * ((A + s * ε - s * supportFun K (s • (x₀ - x₀))) - A) = ε := by
  rw [sub_self, smul_zero, supportFun_zero hKc hKne]
  linear_combination ε * hs2

/-- TeX line 434: `(F)_+` on the ball `B_r (x₀)`, extended by zero outside (the paper's
`(c − w)_+` for `F = c − w`). -/
private def lem4Cutoff (F : (Fin 2 → ℝ) → ℝ) (x₀ : Fin 2 → ℝ) (r : ℝ) : (Fin 2 → ℝ) → ℝ :=
  Set.indicator (Metric.ball x₀ r) fun x => max (F x) 0

/-- `(F)_+` on `B_r (x₀)`, extended by zero, is `min (F_+, (ε − (ρ/2) ‖x − x₀‖)_+)` when
`F ≤ ε − (ρ/2) ‖x − x₀‖` on `closedBall x₀ r` and `2ε < ρ r`: a formula that shows it is
Lipschitz. -/
private lemma lem4Cutoff_eq_min {F : (Fin 2 → ℝ) → ℝ} {x₀ : Fin 2 → ℝ} {r ρ ε : ℝ} (hρ : 0 < ρ)
    (hερ : 2 * ε < ρ * r) (hF : ∀ x, ‖x - x₀‖ ≤ r → F x ≤ ε - ρ / 2 * ‖x - x₀‖)
    (x : Fin 2 → ℝ) :
    lem4Cutoff F x₀ r x = min (max (F x) 0) (max (ε - ρ / 2 * ‖x - x₀‖) 0) := by
  unfold lem4Cutoff
  by_cases hx : x ∈ Metric.ball x₀ r
  · rw [Set.indicator_of_mem hx]
    have : ‖x - x₀‖ ≤ r := by rw [Metric.mem_ball, dist_eq_norm] at hx; exact hx.le
    exact (min_eq_left (max_le_max (hF x this) le_rfl)).symm
  · rw [Set.indicator_of_notMem hx]
    have : r ≤ ‖x - x₀‖ := by rw [Metric.mem_ball, dist_eq_norm, not_lt] at hx; exact hx
    have h2 : ε - ρ / 2 * ‖x - x₀‖ ≤ 0 := by nlinarith
    rw [max_eq_right h2, min_eq_right (le_max_right _ _)]

private lemma lem4Cutoff_nonneg (F : (Fin 2 → ℝ) → ℝ) (x₀ : Fin 2 → ℝ) (r : ℝ) (x : Fin 2 → ℝ) :
    0 ≤ lem4Cutoff F x₀ r x :=
  Set.indicator_nonneg (fun _ _ => le_max_right _ _) x

private lemma lem4Cutoff_le {F : (Fin 2 → ℝ) → ℝ} {x₀ : Fin 2 → ℝ} {r ρ ε : ℝ} (hρ : 0 < ρ)
    (hε : 0 < ε) (hερ : 2 * ε < ρ * r) (hF : ∀ x, ‖x - x₀‖ ≤ r → F x ≤ ε - ρ / 2 * ‖x - x₀‖)
    (x : Fin 2 → ℝ) : lem4Cutoff F x₀ r x ≤ ε := by
  rw [lem4Cutoff_eq_min hρ hερ hF]
  exact (min_le_right _ _).trans (max_le (by nlinarith [norm_nonneg (x - x₀)]) hε.le)

/-- The cut-off vanishes outside `B_{2ε/ρ} (x₀)`. -/
private lemma lem4Cutoff_eq_zero {F : (Fin 2 → ℝ) → ℝ} {x₀ : Fin 2 → ℝ} {r ρ ε : ℝ} (hρ : 0 < ρ)
    (hερ : 2 * ε < ρ * r) (hF : ∀ x, ‖x - x₀‖ ≤ r → F x ≤ ε - ρ / 2 * ‖x - x₀‖)
    {x : Fin 2 → ℝ} (hx : 2 * ε < ρ * ‖x - x₀‖) : lem4Cutoff F x₀ r x = 0 := by
  rw [lem4Cutoff_eq_min hρ hερ hF, max_eq_right (by linarith : ε - ρ / 2 * ‖x - x₀‖ ≤ 0)]
  exact min_eq_right (le_max_right _ _)

private lemma lem4Cutoff_eventuallyEq_zero {F : (Fin 2 → ℝ) → ℝ} {x₀ : Fin 2 → ℝ} {r ρ ε : ℝ}
    (hρ : 0 < ρ) (hερ : 2 * ε < ρ * r) (hF : ∀ x, ‖x - x₀‖ ≤ r → F x ≤ ε - ρ / 2 * ‖x - x₀‖)
    {z : Fin 2 → ℝ} (hz : 2 * ε < ρ * ‖z - x₀‖) : lem4Cutoff F x₀ r =ᶠ[𝓝 z] fun _ => 0 := by
  have hopen : IsOpen {x : Fin 2 → ℝ | 2 * ε < ρ * ‖x - x₀‖} :=
    isOpen_lt continuous_const (continuous_const.mul (continuous_id.sub continuous_const).norm)
  filter_upwards [hopen.mem_nhds hz] with x hx
  exact lem4Cutoff_eq_zero hρ hερ hF hx

private lemma lem4Cutoff_eventuallyEq_ball (F : (Fin 2 → ℝ) → ℝ) {x₀ : Fin 2 → ℝ} {r : ℝ}
    {z : Fin 2 → ℝ} (hz : z ∈ Metric.ball x₀ r) :
    lem4Cutoff F x₀ r =ᶠ[𝓝 z] fun x => max (F x) 0 := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with x hx
  exact Set.indicator_of_mem hx _

private lemma lem4Cutoff_lipschitz {F : (Fin 2 → ℝ) → ℝ} {CF : NNReal} (hFL : LipschitzWith CF F)
    {x₀ : Fin 2 → ℝ} {r ρ ε : ℝ} (hρ : 0 < ρ) (hερ : 2 * ε < ρ * r)
    (hF : ∀ x, ‖x - x₀‖ ≤ r → F x ≤ ε - ρ / 2 * ‖x - x₀‖) :
    ∃ C, LipschitzWith C (lem4Cutoff F x₀ r) := by
  have hd : LipschitzWith (Real.toNNReal (ρ / 2)) (fun x : Fin 2 → ℝ => ε - ρ / 2 * ‖x - x₀‖) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h1 : |‖x - x₀‖ - ‖y - x₀‖| ≤ ‖x - y‖ := by
      calc |‖x - x₀‖ - ‖y - x₀‖| ≤ ‖(x - x₀) - (y - x₀)‖ := abs_norm_sub_norm_le _ _
        _ = ‖x - y‖ := by rw [sub_sub_sub_cancel_right]
    have h2 : dist (ε - ρ / 2 * ‖x - x₀‖) (ε - ρ / 2 * ‖y - x₀‖) =
        ρ / 2 * |‖x - x₀‖ - ‖y - x₀‖| := by
      rw [Real.dist_eq, show ε - ρ / 2 * ‖x - x₀‖ - (ε - ρ / 2 * ‖y - x₀‖) =
        -(ρ / 2 * (‖x - x₀‖ - ‖y - x₀‖)) by ring, abs_neg, abs_mul,
        abs_of_pos (by positivity : 0 < ρ / 2)]
    rw [h2, Real.coe_toNNReal _ (by positivity), dist_eq_norm]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  rw [show lem4Cutoff F x₀ r = fun x => min (max (F x) 0) (max (ε - ρ / 2 * ‖x - x₀‖) 0) from
    funext (lem4Cutoff_eq_min hρ hερ hF)]
  exact ⟨_, (hFL.max (LipschitzWith.const 0)).min (hd.max (LipschitzWith.const 0))⟩

private lemma lem4_lipschitz_const_mul {f : (Fin 2 → ℝ) → ℝ} {C : NNReal} (hf : LipschitzWith C f)
    (s : ℝ) : LipschitzWith (‖s‖₊ * C) (fun x => s * f x) :=
  (lipschitzWith_smul s).comp hf

/-- **The competitor lies in `𝒞`** (TeX line 434). For the cone `c` (Lipschitz, gradient in `K`
where differentiable) and the cut-off `g = (s (c − w))_+` on `B_r (x₀)`, extended by zero
(`lem4Cutoff`), the function `ξ = ζ + s ĝ`, with `ĝ` the `ℤ²`-periodization of `g`, lies in `𝒞`.
Near a point of `B_r (x₀)` (up to an integer translation), `p · x + ξ = s max {s c, s w}` (that
is, `max {w, c}` for `s = 1` and `min {w, c}` for `s = −1`), whose gradient is a.e. `Dc ∈ K` or
`Dw ∈ K` (`ae_fderiv_max_eq_or`); away from `B_{2ε/ρ} (x₀)`, `ξ = ζ` up to translation. -/
private lemma lemma4_competitor_mem {ζ w c : (Fin 2 → ℝ) → ℝ} (hζ : ζ ∈ constraintSet K p)
    (hw : w = fun y => p ⬝ᵥ y + ζ y) {Cc : NNReal} (hcL : LipschitzWith Cc c)
    (hcK : ∀ z, DifferentiableAt ℝ c z → sgrad c z ∈ K) {s : ℝ} (hs2 : s * s = 1)
    {x₀ : Fin 2 → ℝ} {r ρ ε : ℝ} (hr : r < 1 / 2) (hρ : 0 < ρ) (hε : 0 < ε)
    (hερ : 2 * ε < ρ * r) (hF : ∀ x, ‖x - x₀‖ ≤ r → s * (c x - w x) ≤ ε - ρ / 2 * ‖x - x₀‖) :
    (fun x => ζ x + s * supPeriodize (lem4Cutoff (fun x => s * (c x - w x)) x₀ r) x) ∈
      constraintSet K p := by
  have hζK := lemma4_ae_constraint hζ
  obtain ⟨⟨⟨Cζ, hζL⟩, hζper⟩, -⟩ := hζ
  obtain ⟨Cw, hwL⟩ := lem4_lipschitz_dot_add (p := p) hζL
  rw [← hw] at hwL
  have hsupp : ∀ x, r ≤ ‖x - x₀‖ → lem4Cutoff (fun x => s * (c x - w x)) x₀ r x = 0 :=
    fun x hx => lem4Cutoff_eq_zero hρ hερ hF (by nlinarith)
  obtain ⟨Cg, hgL⟩ := lem4Cutoff_lipschitz (lem4_lipschitz_const_mul (hcL.sub hwL) s) hρ hερ hF
  have hφL := lipschitzWith_supPeriodize hgL (lem4Cutoff_le hρ hε hερ hF)
  set g := lem4Cutoff (fun x => s * (c x - w x)) x₀ r with hg_def
  set φ := supPeriodize g with hφ_def
  have hξL : LipschitzWith _ (fun x => ζ x + s * φ x) := hζL.add (lem4_lipschitz_const_mul hφL s)
  refine ⟨⟨⟨_, hξL⟩, fun x k => ?_⟩, ae_restrict_of_ae ?_⟩
  · -- periodicity
    simp only [hφ_def]
    rw [hζper x k, supPeriodize_periodic]
  -- the gradient constraint, almost everywhere on `ℝ²`
  have hML := (lem4_lipschitz_const_mul hcL s).max (lem4_lipschitz_const_mul hwL s)
  have hgood : ∀ᵐ z ∂(volume : Measure (Fin 2 → ℝ)), DifferentiableAt ℝ ζ z ∧
      p + sgrad ζ z ∈ K ∧ DifferentiableAt ℝ c z ∧
      DifferentiableAt ℝ (fun u => max (s * c u) (s * w u)) z ∧
      (fderiv ℝ (fun u => max (s * c u) (s * w u)) z = fderiv ℝ (fun u => s * c u) z ∨
        fderiv ℝ (fun u => max (s * c u) (s * w u)) z = fderiv ℝ (fun u => s * w u) z) := by
    filter_upwards [hζL.ae_differentiableAt, hζK, hcL.ae_differentiableAt, hML.ae_differentiableAt,
      ae_fderiv_max_eq_or (lem4_lipschitz_const_mul hcL s) (lem4_lipschitz_const_mul hwL s)]
      with z h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  have hgood' := ae_all_iff.2 fun k : Fin 2 → ℤ => QuasiMeasurePreserving.ae
    (measurePreserving_add_right volume fun i => (k i : ℝ)).quasiMeasurePreserving hgood
  filter_upwards [hgood', hξL.ae_differentiableAt] with x hx hξd
  obtain ⟨k, hk⟩ := exists_norm_add_intVec_sub_le_half x₀ x
  obtain ⟨hζd, hζK', hcd, hMd, hmax⟩ := hx k
  set z := x + fun i => (k i : ℝ) with hz
  have hwd : DifferentiableAt ℝ w z := by rw [hw]; exact (hasFDerivAt_dot_add hζd).differentiableAt
  have hwg : sgrad w z = p + sgrad ζ z := by rw [hw]; exact sgrad_dot_add hζd
  -- near `x`, `p · y + ξ (y) = (w + s g) (y + k) − p · k`
  have hW : (fun y => p ⬝ᵥ y + (ζ y + s * φ y)) =ᶠ[𝓝 x]
      fun y => (fun u => w u + s * g u) (y + fun i => (k i : ℝ)) + -(p ⬝ᵥ fun i => (k i : ℝ)) := by
    filter_upwards [supPeriodize_eventuallyEq (lem4Cutoff_nonneg _ x₀ r) hsupp hr hk] with y hy
    have hy' : φ y = g (y + fun i => (k i : ℝ)) := hy
    simp only [hy', hw, hζper y k, dotProduct_add]
    ring
  have key : p + sgrad (fun y => ζ y + s * φ y) x = sgrad (fun u => w u + s * g u) z := by
    rw [← sgrad_dot_add hξd, sgrad_congr hW, sgrad_add_const]
    exact sgrad_comp_add (fun u => w u + s * g u) _ x
  rw [key]
  by_cases hzr : z ∈ Metric.ball x₀ r
  · -- near `z`, `w + s g = s max {s c, s w}`
    have hloc : (fun u => w u + s * g u) =ᶠ[𝓝 z] fun u => s * max (s * c u) (s * w u) := by
      filter_upwards [lem4Cutoff_eventuallyEq_ball _ hzr] with u hu
      rw [hg_def, hu, show s * (c u - w u) = s * c u - s * w u by ring,
        show (0 : ℝ) = s * w u - s * w u by ring, max_sub_sub_right]
      linear_combination (-(w u)) * hs2
    rw [sgrad_congr hloc, sgrad_const_mul hMd]
    rcases hmax with h | h
    · have : sgrad (fun u => max (s * c u) (s * w u)) z = s • sgrad c z := by
        ext j; simp [sgrad, h, fderiv_const_mul hcd]
      rw [this, smul_smul, hs2, one_smul]
      exact hcK z hcd
    · have : sgrad (fun u => max (s * c u) (s * w u)) z = s • sgrad w z := by
        ext j; simp [sgrad, h, fderiv_const_mul hwd]
      rw [this, smul_smul, hs2, one_smul, hwg]
      exact hζK'
  · -- away from `B_{2ε/ρ} (x₀)`, `w + s g = w` near `z`
    have hzr' : 2 * ε < ρ * ‖z - x₀‖ := by
      rw [Metric.mem_ball, dist_eq_norm, not_lt] at hzr; nlinarith
    have hloc : (fun u => w u + s * g u) =ᶠ[𝓝 z] w := by
      filter_upwards [lem4Cutoff_eventuallyEq_zero hρ hερ hF hzr'] with u hu
      rw [hg_def, hu, mul_zero, add_zero]
    rw [sgrad_congr hloc, hwg]
    exact hζK'

/-- **The competitor increases the integral** (TeX line 436): `∫_Q h (ξ − ζ) > 0`, as `s h > 0`
where the periodized cut-off is positive, and `s h (x₀) ĝ (x₀) = s h (x₀) ε > 0`. -/
private lemma lemma4_competitor_integral_pos {η ζ w c : (Fin 2 → ℝ) → ℝ} (hη : LipPer η)
    (hζ : LipPer ζ) (hw : w = fun y => p ⬝ᵥ y + ζ y) {Cc : NNReal} (hcL : LipschitzWith Cc c)
    {s : ℝ} {x₀ : Fin 2 → ℝ} (hx₀ : x₀ ∈ unitSquare) {r ρ ε : ℝ} (hr : r < 1 / 2) (hρ : 0 < ρ)
    (hε : 0 < ε) (hερ : 2 * ε < ρ * r)
    (hF : ∀ x, ‖x - x₀‖ ≤ r → s * (c x - w x) ≤ ε - ρ / 2 * ‖x - x₀‖)
    (hFx₀ : s * (c x₀ - w x₀) = ε) (hh : ∀ x, ‖x - x₀‖ ≤ r → 0 < s * (η x - ζ x)) :
    0 < ∫ x in unitSquare, (η x - ζ x) *
      ((ζ x + s * supPeriodize (lem4Cutoff (fun x => s * (c x - w x)) x₀ r) x) - ζ x) := by
  obtain ⟨⟨Cη, hηL⟩, hηper⟩ := hη
  obtain ⟨⟨Cζ, hζL⟩, hζper⟩ := hζ
  obtain ⟨Cw, hwL⟩ := lem4_lipschitz_dot_add (p := p) hζL
  rw [← hw] at hwL
  have hr0 : 0 < r := by nlinarith
  have hsupp : ∀ x, r ≤ ‖x - x₀‖ → lem4Cutoff (fun x => s * (c x - w x)) x₀ r x = 0 :=
    fun x hx => lem4Cutoff_eq_zero hρ hερ hF (by nlinarith)
  obtain ⟨Cg, hgL⟩ := lem4Cutoff_lipschitz (lem4_lipschitz_const_mul (hcL.sub hwL) s) hρ hερ hF
  have hφc := (lipschitzWith_supPeriodize hgL (lem4Cutoff_le hρ hε hερ hF)).continuous
  set g := lem4Cutoff (fun x => s * (c x - w x)) x₀ r with hg_def
  set φ := supPeriodize g with hφ_def
  have hηc := hηL.continuous
  have hζc := hζL.continuous
  have hGc : Continuous fun x => (η x - ζ x) * ((ζ x + s * φ x) - ζ x) := by fun_prop
  have hGeq : ∀ x, (η x - ζ x) * ((ζ x + s * φ x) - ζ x) = s * (η x - ζ x) * φ x := fun x => by
    ring
  -- `s h ĝ ≥ 0`: where `ĝ (x) = g (x + k) > 0`, `x + k ∈ B_r (x₀)` and `s h (x + k) > 0`
  have hG0 : ∀ x, 0 ≤ (η x - ζ x) * ((ζ x + s * φ x) - ζ x) := by
    intro x
    obtain ⟨k, hk⟩ := exists_norm_add_intVec_sub_le_half x₀ x
    rw [hGeq, hφ_def, supPeriodize_eq (lem4Cutoff_nonneg _ x₀ r) hsupp hr hk]
    rcases (lem4Cutoff_nonneg (fun x => s * (c x - w x)) x₀ r
      (x + fun i => (k i : ℝ))).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
    · have hxk : ‖x + (fun i => (k i : ℝ)) - x₀‖ ≤ r := by
        by_contra hcon
        exact hpos.ne' (lem4Cutoff_eq_zero hρ hερ hF (by nlinarith))
      have := hh _ hxk
      rw [hηper x k, hζper x k] at this
      exact mul_nonneg this.le hpos.le
  -- `s h (x₀) ĝ (x₀) = s h (x₀) ε > 0`
  have hGx₀ : 0 < (η x₀ - ζ x₀) * ((ζ x₀ + s * φ x₀) - ζ x₀) := by
    have hk0 : ‖x₀ + (fun i => ((0 : Fin 2 → ℤ) i : ℝ)) - x₀‖ ≤ 1 / 2 := by simp
    have h0 : (fun i => ((0 : Fin 2 → ℤ) i : ℝ)) = 0 := by ext; simp
    rw [hGeq, hφ_def, supPeriodize_eq (lem4Cutoff_nonneg _ x₀ r) hsupp hr hk0, h0, add_zero,
      lem4Cutoff, Set.indicator_of_mem (Metric.mem_ball_self hr0), hFx₀,
      max_eq_left hε.le]
    exact mul_pos (hh x₀ (by rw [sub_self, norm_zero]; exact hr0.le)) hε
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hG0)
    (lem4_integrableOn_of_continuous hGc)]
  exact (hGc.isOpen_support.inter lem4_isOpen_unitSquare).measure_pos volume
    ⟨x₀, hGx₀.ne', hx₀⟩

/-- **Step 2, the contradiction** (TeX lines 422–436), for `s h (x₀) > 0` with `s = ±1`. The
case `s = 1` is the paper's; `s = −1` is the paper's "by changing signs" made explicit: the mirror
cone `c (x) = w (x₀) − ε + H (x − x₀)`, `min {w, c}` and the competitor `ζ − (w − c)_+`. -/
private lemma lemma4_step2_core (hKne : K.Nonempty) (hKc : IsCompact K) (hKcv : Convex ℝ K)
    {η ζ : (Fin 2 → ℝ) → ℝ} (hη : LipPer η) (hζ : IsL2Projection (constraintSet K p) η ζ)
    {x₀ : Fin 2 → ℝ} (hx₀ : x₀ ∈ unitSquare) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hsh : 0 < s * (η x₀ - ζ x₀)) (hdiff : DifferentiableAt ℝ (fun y => p ⬝ᵥ y + ζ y) x₀)
    (hint : sgrad (fun y => p ⬝ᵥ y + ζ y) x₀ ∈ interior K) : False := by
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hs1 : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  obtain ⟨Cη, hηL⟩ := hη.1
  obtain ⟨Cζ, hζL⟩ := hζ.1.1.1
  -- `ρ` with `B_ρ (b₀) ⊂ K`, so that `H (y) ≥ b₀ · y + ρ ‖y‖`
  obtain ⟨ρ, hρ, hHρ⟩ := lemma4_choose_rho hKc hint
  -- the ball `closedBall x₀ r`
  obtain ⟨r, hr0, hr, hrh, hrw⟩ := lemma4_choose_r hdiff
    (continuous_const.mul (hηL.continuous.sub hζL.continuous)) hsh hρ
  -- `0 < ε < ρ r / 2`
  set ε := ρ * r / 4 with hε_def
  have hε : 0 < ε := by positivity
  have hερ : 2 * ε < ρ * r := by rw [hε_def]; nlinarith
  -- the cone `c (x) = w (x₀) + s ε − s H (s (x₀ − x))`
  obtain ⟨Cc, hcL⟩ := lemma4_cone_lipschitz hKne hKc hs1 (p ⬝ᵥ x₀ + ζ x₀ + s * ε) x₀
  have hcK := fun z hz => lemma4_cone_sgrad_mem hKne hKc hKcv hs2 (p ⬝ᵥ x₀ + ζ x₀ + s * ε) x₀
    (z := z) hz
  have hF : ∀ x, ‖x - x₀‖ ≤ r → s * ((p ⬝ᵥ x₀ + ζ x₀ + s * ε -
      s * supportFun K (s • (x₀ - x))) - (p ⬝ᵥ x + ζ x)) ≤ ε - ρ / 2 * ‖x - x₀‖ :=
    fun x hx => lemma4_cone_bound hHρ hs (w := fun y => p ⬝ᵥ y + ζ y) ε (hrw x hx)
  have hFx₀ := lemma4_cone_center hKne hKc hs2 (p ⬝ᵥ x₀ + ζ x₀) ε x₀
  -- the competitor `ξ = ζ + s (s (c − w))_+` lies in `𝒞` and `∫_Q h (ξ − ζ) > 0`
  have hξ := lemma4_competitor_mem hζ.1 rfl hcL hcK hs2 hr hρ hε hερ hF
  have hpos := lemma4_competitor_integral_pos hη hζ.1.1 rfl hcL hx₀ hr hρ hε hερ hF hFx₀ hrh
  -- contradicting `(eq:projection-variational-inequality)`
  have := lemma4_variationalInequality hKcv hη hζ _ hξ
  linarith

/-- **Step 2** (TeX lines 422–436): where `h (x₀) ≠ 0` and `w` is differentiable at `x₀`,
`Dw (x₀) ∉ int K`. "By changing signs, we may assume `h (x₀) > 0`": made explicit by `s = ±1` in
`lemma4_step2_core`. -/
private lemma lemma4_step2 (hKne : K.Nonempty) (hKc : IsCompact K) (hKcv : Convex ℝ K)
    {η ζ : (Fin 2 → ℝ) → ℝ} (hη : LipPer η) (hζ : IsL2Projection (constraintSet K p) η ζ)
    {x₀ : Fin 2 → ℝ} (hx₀ : x₀ ∈ unitSquare) (hh : η x₀ - ζ x₀ ≠ 0)
    (hdiff : DifferentiableAt ℝ (fun y => p ⬝ᵥ y + ζ y) x₀) :
    sgrad (fun y => p ⬝ᵥ y + ζ y) x₀ ∉ interior K := by
  intro hint
  rcases lt_or_gt_of_ne hh with hneg | hpos
  · exact lemma4_step2_core hKne hKc hKcv hη hζ hx₀ (Or.inr rfl) (by linarith) hdiff hint
  · exact lemma4_step2_core hKne hKc hKcv hη hζ hx₀ (Or.inl rfl) (by linarith) hdiff hint

/-- **The first assertion** (TeX lines 417–436): `Dw = Dv` or `Dw ∈ ∂K` almost everywhere. -/
private lemma lemma4_first (hKne : K.Nonempty) (hKc : IsCompact K) (hKcv : Convex ℝ K)
    {η ζ : (Fin 2 → ℝ) → ℝ} (hη : LipPer η) (hζ : IsL2Projection (constraintSet K p) η ζ) :
    ∀ᵐ x ∂(volume.restrict unitSquare),
      sgrad (fun y => p ⬝ᵥ y + ζ y) x = sgrad (fun y => p ⬝ᵥ y + η y) x ∨
        sgrad (fun y => p ⬝ᵥ y + ζ y) x ∈ frontier K := by
  obtain ⟨Cζ, hζL⟩ := hζ.1.1.1
  filter_upwards [ae_restrict_mem lem4_measurableSet_unitSquare, hζ.1.2,
    ae_restrict_of_ae (lemma4_step1 (p := p) hη hζ.1.1), ae_restrict_of_ae hζL.ae_differentiableAt]
    with x hx hxK h1 hζd
  by_cases h0 : η x - ζ x = 0
  · exact Or.inl (h1 h0)
  right
  have hwK : sgrad (fun y => p ⬝ᵥ y + ζ y) x ∈ K := by rw [sgrad_dot_add hζd]; exact hxK
  rw [hKc.isClosed.frontier_eq]
  -- if `K` has empty interior, `∂K = K`; otherwise Step 2
  by_cases hint : interior K = ∅
  · rw [hint, Set.sdiff_empty]; exact hwK
  · exact ⟨hwK, lemma4_step2 hKne hKc hKcv hη hζ hx h0 (hasFDerivAt_dot_add hζd).differentiableAt⟩

/-! ### Step 3: `(eq:projection-integral-sign)` -/

/-- TeX line 438: translates `ζ (· + a)` of `ζ ∈ 𝒞` lie in `𝒞`. -/
private lemma lemma4_translate_mem {ζ : (Fin 2 → ℝ) → ℝ} (hζ : ζ ∈ constraintSet K p)
    (a : Fin 2 → ℝ) : (fun x => ζ (x + a)) ∈ constraintSet K p := by
  have hae := lemma4_ae_constraint hζ
  obtain ⟨⟨⟨C, hC⟩, hper⟩, -⟩ := hζ
  refine ⟨⟨⟨C, LipschitzWith.of_dist_le_mul fun x y => ?_⟩, fun x k => ?_⟩, ?_⟩
  · have := hC.dist_le_mul (x + a) (y + a)
    rwa [dist_eq_norm (x + a), add_sub_add_right_eq_sub, ← dist_eq_norm] at this
  · simp only
    rw [show x + (fun i => (k i : ℝ)) + a = x + a + fun i => (k i : ℝ) by abel]
    exact hper _ k
  · refine ae_restrict_of_ae ?_
    filter_upwards [QuasiMeasurePreserving.ae
      (measurePreserving_add_right volume a).quasiMeasurePreserving hae] with x hx
    rwa [sgrad_comp_add]

/-- **Step 3, the second differences** (TeX lines 438–442): adding the variational inequalities
for `ζ (· ± t e) ∈ 𝒞` and changing variables,
`0 ≥ ∫_Q h (x) [ζ (x + t e) + ζ (x − t e) − 2 ζ (x)] = −∫_Q [h (x + t e) − h (x)]
[ζ (x + t e) − ζ (x)]`. -/
private lemma lemma4_step3_diff (hKcv : Convex ℝ K) {η ζ : (Fin 2 → ℝ) → ℝ} (hη : LipPer η)
    (hζ : IsL2Projection (constraintSet K p) η ζ) (e : Fin 2 → ℝ) (t : ℝ) :
    0 ≤ ∫ x in unitSquare, ((η (x + t • e) - ζ (x + t • e)) - (η x - ζ x)) *
      (ζ (x + t • e) - ζ x) := by
  obtain ⟨⟨Cη, hηL⟩, hηper⟩ := hη
  obtain ⟨⟨Cζ, hζL⟩, hζper⟩ := hζ.1.1
  have hηc := hηL.continuous
  have hζc := hζL.continuous
  -- the variational inequalities for `ζ (· + t e)` and `ζ (· − t e)`
  have hplus := lemma4_variationalInequality hKcv ⟨⟨Cη, hηL⟩, hηper⟩ hζ _
    (lemma4_translate_mem hζ.1 (t • e))
  have hminus := lemma4_variationalInequality hKcv ⟨⟨Cη, hηL⟩, hηper⟩ hζ _
    (lemma4_translate_mem hζ.1 (-(t • e)))
  beta_reduce at hplus hminus
  have hiplus : IntegrableOn (fun x => (η x - ζ x) * (ζ (x + t • e) - ζ x)) unitSquare :=
    lem4_integrableOn_of_continuous (by fun_prop)
  have himinus : IntegrableOn (fun x => (η x - ζ x) * (ζ (x + -(t • e)) - ζ x)) unitSquare :=
    lem4_integrableOn_of_continuous (by fun_prop)
  have hi₂ : IntegrableOn
      (fun x => (η (x + t • e) - ζ (x + t • e)) * (ζ x - ζ (x + t • e))) unitSquare :=
    lem4_integrableOn_of_continuous (by fun_prop)
  have hsplit : ∫ x in unitSquare, (η x - ζ x) * (ζ (x + t • e) + ζ (x + -(t • e)) - 2 * ζ x) =
      (∫ x in unitSquare, (η x - ζ x) * (ζ (x + t • e) - ζ x)) +
        ∫ x in unitSquare, (η x - ζ x) * (ζ (x + -(t • e)) - ζ x) := by
    rw [← integral_add hiplus himinus]
    congr 1
    funext x
    ring
  -- adding them: `0 ≥ ∫_Q h (x) [ζ (x + t e) + ζ (x − t e) − 2 ζ (x)]`
  have hsum :
      ∫ x in unitSquare, (η x - ζ x) * (ζ (x + t • e) + ζ (x + -(t • e)) - 2 * ζ x) ≤ 0 := by
    rw [hsplit]; linarith
  -- changing variables: `∫_Q h (x) [ζ (x − t e) − ζ (x)] = ∫_Q h (x + t e) [ζ (x) − ζ (x + t e)]`
  have hcv : ∫ x in unitSquare, (η x - ζ x) * (ζ (x + -(t • e)) - ζ x) =
      ∫ x in unitSquare, (η (x + t • e) - ζ (x + t • e)) * (ζ x - ζ (x + t • e)) := by
    have hper : ∀ (x : Fin 2 → ℝ) (k : Fin 2 → ℤ),
        (fun x => (η x - ζ x) * (ζ (x + -(t • e)) - ζ x)) (x + fun i => (k i : ℝ)) =
          (fun x => (η x - ζ x) * (ζ (x + -(t • e)) - ζ x)) x := fun x k => by
      simp only
      rw [hηper x k, hζper x k, show x + (fun i => (k i : ℝ)) + -(t • e) =
        x + -(t • e) + fun i => (k i : ℝ) by abel, hζper _ k]
    have := setIntegral_unitCube_comp_add
      (f := fun x => (η x - ζ x) * (ζ (x + -(t • e)) - ζ x)) hper (t • e)
    rw [← lem4_unitSquare_eq] at this
    rw [← this]
    congr 1
    funext x
    rw [add_neg_cancel_right]
  -- `= −∫_Q [h (x + t e) − h (x)] [ζ (x + t e) − ζ (x)]`
  have heq : ∫ x in unitSquare, (η x - ζ x) * (ζ (x + t • e) + ζ (x + -(t • e)) - 2 * ζ x) =
      -∫ x in unitSquare, ((η (x + t • e) - ζ (x + t • e)) - (η x - ζ x)) *
        (ζ (x + t • e) - ζ x) := by
    rw [hsplit, hcv, ← integral_add hiplus hi₂, ← integral_neg]
    congr 1
    funext x
    ring
  linarith

/-- **Step 3, the limit** (TeX line 443): dividing by `t²` and letting `t → 0`,
`∫_Q ∂_e h ∂_e ζ ≥ 0`. -/
private lemma lemma4_step3_partial (hKcv : Convex ℝ K) {η ζ : (Fin 2 → ℝ) → ℝ} (hη : LipPer η)
    (hζ : IsL2Projection (constraintSet K p) η ζ) (e : Fin 2 → ℝ) :
    0 ≤ ∫ x in unitSquare, fderiv ℝ (fun y => η y - ζ y) x e * fderiv ℝ ζ x e := by
  obtain ⟨Cη, hηL⟩ := hη.1
  obtain ⟨Cζ, hζL⟩ := hζ.1.1.1
  have hlim := tendsto_setIntegral_slope_mul (hηL.sub hζL) hζL e
    (s := unitSquare) (by rw [lem4_volume_unitSquare]; exact ENNReal.one_ne_top)
  refine ge_of_tendsto hlim (Eventually.of_forall fun t => ?_)
  have h := lemma4_step3_diff hKcv hη hζ e t
  calc (0 : ℝ) ≤ t⁻¹ * t⁻¹ * ∫ x in unitSquare, ((η (x + t • e) - ζ (x + t • e)) - (η x - ζ x)) *
        (ζ (x + t • e) - ζ x) := mul_nonneg (mul_self_nonneg _) h
    _ = _ := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring

/-- **Step 3** (TeX line 443): summing over `i`, with `Dw = p + Dζ`, `Dv − Dw = Dh` and
`∫_Q Dh = 0`, `∫_Q Dw · (Dv − Dw) ≥ 0`. -/
private lemma lemma4_step3 (hKcv : Convex ℝ K) {η ζ : (Fin 2 → ℝ) → ℝ} (hη : LipPer η)
    (hζ : IsL2Projection (constraintSet K p) η ζ) :
    0 ≤ ∫ x in unitSquare, sgrad (fun y => p ⬝ᵥ y + ζ y) x ⬝ᵥ
      (sgrad (fun y => p ⬝ᵥ y + η y) x - sgrad (fun y => p ⬝ᵥ y + ζ y) x) := by
  obtain ⟨⟨Cη, hηL⟩, hηper⟩ := hη
  obtain ⟨⟨Cζ, hζL⟩, hζper⟩ := hζ.1.1
  have hhL := hηL.sub hζL
  have hhper : ∀ (x : Fin 2 → ℝ) (k : Fin 2 → ℤ),
      (fun y => η y - ζ y) (x + fun i => (k i : ℝ)) = (fun y => η y - ζ y) x := fun x k => by
    simp only [hηper x k, hζper x k]
  -- `Dw = p + Dζ` and `Dv − Dw = Dh` almost everywhere
  have hae : (fun x => sgrad (fun y => p ⬝ᵥ y + ζ y) x ⬝ᵥ
      (sgrad (fun y => p ⬝ᵥ y + η y) x - sgrad (fun y => p ⬝ᵥ y + ζ y) x))
      =ᵐ[volume.restrict unitSquare] fun x =>
        ∑ j, (p j * fderiv ℝ (fun y => η y - ζ y) x (Pi.single j 1) +
          fderiv ℝ ζ x (Pi.single j 1) * fderiv ℝ (fun y => η y - ζ y) x (Pi.single j 1)) := by
    filter_upwards [ae_restrict_of_ae hηL.ae_differentiableAt,
      ae_restrict_of_ae hζL.ae_differentiableAt] with x hηd hζd
    rw [sgrad_dot_add hηd, sgrad_dot_add hζd, fderiv_fun_sub hηd hζd]
    simp only [dotProduct, sgrad, Pi.add_apply, Pi.sub_apply, sub_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint1 : ∀ j : Fin 2, IntegrableOn
      (fun x => p j * fderiv ℝ (fun y => η y - ζ y) x (Pi.single j 1)) unitSquare := fun j =>
    lem4_integrableOn_of_bound
      (measurable_const.mul (measurable_fderiv_apply_const ℝ _ _)) (|p j| * ((Cη + Cζ) * 1))
      fun x => by
        rw [abs_mul]
        gcongr
        simpa [Pi.norm_single] using lem4_abs_fderiv_le hhL x (Pi.single j 1)
  have hint2 : ∀ j : Fin 2, IntegrableOn (fun x => fderiv ℝ ζ x (Pi.single j 1) *
      fderiv ℝ (fun y => η y - ζ y) x (Pi.single j 1)) unitSquare := fun j =>
    lem4_integrableOn_of_bound
      ((measurable_fderiv_apply_const ℝ _ _).mul (measurable_fderiv_apply_const ℝ _ _))
      (Cζ * (Cη + Cζ)) fun x => by
        rw [abs_mul]
        have h1 := lem4_abs_fderiv_le hζL x (Pi.single j 1)
        have h2 := lem4_abs_fderiv_le hhL x (Pi.single j 1)
        simp only [Pi.norm_single, norm_one, mul_one] at h1 h2
        exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  rw [integral_congr_ae hae, integral_finsetSum (f := fun j x =>
    p j * fderiv ℝ (fun y => η y - ζ y) x (Pi.single j 1) +
      fderiv ℝ ζ x (Pi.single j 1) * fderiv ℝ (fun y => η y - ζ y) x (Pi.single j 1))
    Finset.univ fun j _ => (hint1 j).add (hint2 j)]
  refine Finset.sum_nonneg fun j _ => ?_
  rw [integral_add (hint1 j) (hint2 j), integral_const_mul]
  -- `∫_Q ∂_j h = 0` by periodicity, and `∫_Q ∂_j ζ ∂_j h ≥ 0`
  have h0 := setIntegral_unitCube_fderiv_eq_zero hhL hhper (Pi.single j 1)
  rw [← lem4_unitSquare_eq] at h0
  rw [h0, mul_zero, zero_add]
  have := lemma4_step3_partial hKcv ⟨⟨Cη, hηL⟩, hηper⟩ hζ (Pi.single j 1)
  calc (0 : ℝ) ≤ _ := this
    _ = _ := by congr 1; funext x; ring

-- The hypothesis `p ∈ K` is not used here: it makes `𝒞` nonempty (`0 ∈ 𝒞`), which the projection
-- hypothesis `hζ` already gives (`ζ ∈ 𝒞`); it is used for the existence of `ζ` (`lemma4_exists`).
/-- **Lemma 4** (`lem:scalar-projection`). Let `K ⊂ ℝ²` be nonempty, compact and convex, `p ∈ K`,
`η ∈ W^{1,∞}_per (Q)`, `v (x) = p · x + η (x)`, and let `ζ` be the `L² (Q)`-projection of `η` on
`𝒞 = {ξ ∈ W^{1,∞}_per (Q) : p + Dξ ∈ K a.e.}`. Then `w (x) = p · x + ζ (x)` satisfies `Dw = Dv` or
`Dw ∈ ∂K` almost everywhere, and `∫_Q Dw · (Dv − Dw) ≥ 0` (`(eq:projection-integral-sign)`).

The proof is the paper's (TeX lines 411–443), in the steps `lemma4_step1`, `lemma4_step2`
(with `lemma4_first`) and `lemma4_step3`. Remarks on the paper's argument:

* the ball `B_r (x₀)` of the competitor is taken with `r < 1/2`, so that it embeds in the torus
  (its integer translates are disjoint) and `(c − w)_+`, extended by zero, extends to a
  `ℤ²`-periodic function (`supPeriodize`); the paper leaves this implicit;
* "by changing signs, we may assume `h (x₀) > 0`" is made explicit: for `h (x₀) < 0` the mirror
  cone `c (x) = w (x₀) − ε + H (x − x₀)`, `min {w, c}` and `ζ − (w − c)_+` (`s = −1` in
  `lemma4_step2_core`);
* norms and balls in `ℝ²` are those of the sup norm (Mathlib's norm on `Fin 2 → ℝ`), in place of
  the Euclidean ones; the argument does not depend on the norm. -/
theorem lemma4 (hKne : K.Nonempty) (hKc : IsCompact K) (hKcv : Convex ℝ K) (_hp : p ∈ K)
    {η ζ : (Fin 2 → ℝ) → ℝ} (hη : LipPer η) (hζ : IsL2Projection (constraintSet K p) η ζ) :
    (∀ᵐ x ∂(volume.restrict unitSquare),
      sgrad (fun y => p ⬝ᵥ y + ζ y) x = sgrad (fun y => p ⬝ᵥ y + η y) x ∨
        sgrad (fun y => p ⬝ᵥ y + ζ y) x ∈ frontier K) ∧
    0 ≤ ∫ x in unitSquare, sgrad (fun y => p ⬝ᵥ y + ζ y) x ⬝ᵥ
      (sgrad (fun y => p ⬝ᵥ y + η y) x - sgrad (fun y => p ⬝ᵥ y + ζ y) x) :=
  ⟨lemma4_first hKne hKc hKcv hη hζ, lemma4_step3 hKcv hη hζ⟩

end Agazzi
