/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.Periodic
public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.Rescale
public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Quasiconvex.Cutoff
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Hessians: periodic and compactly supported test functions

For a Borel, locally bounded `f : ℝ^{m×m} → ℝ` and a matrix `A`, the inequality
`∫ [f (A + D²u) − f (A)] ≥ 0` holds for every `ℤ^m`-periodic `u ∈ C^∞ (ℝ^m)`, integrated over the
unit cube `Q = (0, 1)^m`, if and only if it holds for every `u ∈ C_c^∞ (ℝ^m)`, integrated over
`ℝ^m` (`CalculusOfVariations.hessian_periodic_iff_hasCompactSupport`). This is the second-order
form of B. Dacorogna, *Direct Methods in the Calculus of Variations*, 2nd ed., Springer, 2008,
Proposition 5.13, with the argument of its proof (as in `CalculusOfVariations.Quasiconvex.Periodic`
for first-order test maps):

* "⇐" (`CalculusOfVariations.integral_hessian_nonneg_of_periodic`): a `u ∈ C_c^∞` with support in
  `closedBall 0 R` is rescaled and translated, `v (x) = λ² u ((x − c) / λ)` with `λ = 1/(4R)` and
  `c` the centre of `Q`, so that `D²v (x) = D²u ((x − c) / λ)` and `v` vanishes off `[1/4, 3/4]^m`.
  Its periodic extension `x ↦ v (fract x)` agrees near every point with an integer translate of
  `v`, so it is smooth and periodic, with the Hessian of `v` on `Q`. The change of variables
  `x = c + λ y` gives `∫_Q [f (A + D²v) − f (A)] = λ^m ∫_{ℝ^m} [f (A + D²u) − f (A)]`, since the
  integrand vanishes off `Q`. This direction uses neither the measurability nor the local
  boundedness of `f`.
* "⇒" (`CalculusOfVariations.setIntegral_unitCube_hessian_nonneg_of_hasCompactSupport`): for a
  periodic `u`, the functions `ψ_ν (x) = ν⁻² u (ν x)`, `ν ∈ ℕ`, have `D²ψ_ν (x) = D²u (ν x)`, so the
  same integral over `Q` by periodicity, while `|ψ_ν| ≤ ν⁻² sup |u|` and `|Dψ_ν| ≤ ν⁻¹ sup |Du|`.
  The cut-off `η_j` is a smooth bump function for the sup norm (Mathlib's `ContDiffBump`, whose
  balls are cubes), equal to `1` on `(1/j, 1 − 1/j)^m` and with compact support in `Q`; its first
  and second derivatives are bounded by some `C_j`. For `ν ≥ C_j`, the Hessian
  `D² (η_j ψ_ν) = η_j D²ψ_ν + Dη_j ⊗ Dψ_ν + Dψ_ν ⊗ Dη_j + ψ_ν D²η_j` of the test function
  `η_j ψ_ν ∈ C_c^∞` is bounded independently of `j`, and equal to `D²ψ_ν` on `(1/j, 1 − 1/j)^m`.
  As `f` is locally bounded, the two integrals over `Q` differ by at most a constant times the
  measure `1 − (1 − 2/j)^m` of the boundary layer; let `j → ∞`. As in
  `CalculusOfVariations.Quasiconvex.Cutoff`, the width `1/j` of the layer and the frequency `ν` are
  chosen separately, so that no bound of the derivatives of `η_j` in terms of `j` is needed.

`CalculusOfVariations.hessian u x` is the matrix `(∂_j ∂_i u (x))`, the derivative matrix
(`CalculusOfVariations.grad`) of the gradient `y ↦ (∂_i u (y))_i`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ContDiff

namespace CalculusOfVariations

variable {m : ℕ}

/-- The Hessian matrix of `u : ℝ^m → ℝ` at `x`: the entries `∂_j ∂_i u (x)`, that is, the derivative
matrix of the gradient `y ↦ (∂_i u (y))_i`. -/
def hessian (u : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  grad (fun y i => fderiv ℝ u y (Pi.single i 1)) x

/-! ### Calculus of Hessians -/

/-- The entries of the Hessian: `(D²u (x))_{ik} = ∂_k ∂_i u (x)`. -/
private lemma hess_apply (u : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ) (i k : Fin m) :
    hessian u x i k = fderiv ℝ (fun y => fderiv ℝ u y (Pi.single i 1)) x (Pi.single k 1) := rfl

/-- The directional derivatives of a smooth function are smooth. -/
private lemma hess_contDiff_fderiv {g : (Fin m → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    (v : Fin m → ℝ) : ContDiff ℝ ∞ fun y => fderiv ℝ g y v :=
  (contDiff_infty_iff_fderiv.1 hg).2.clm_apply contDiff_const

/-- A smooth function is differentiable. -/
private lemma hess_differentiable {g : (Fin m → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) :
    Differentiable ℝ g :=
  hg.differentiable (by simp)

/-- `D (y ↦ c g (a y)) (x) = c a Dg (a x)`. -/
private lemma hess_fderiv_comp_smul (g : (Fin m → ℝ) → ℝ) (c a : ℝ) (x : Fin m → ℝ) :
    fderiv ℝ (fun y => c * g (a • y)) x = (c * a) • fderiv ℝ g (a • x) := by
  have e : (fun y => c * g (a • y)) = c • fun y => g (a • y) := rfl
  rw [e, fderiv_const_smul_field, Pi.smul_apply, fderiv_comp_smul (f := g), smul_smul]

/-- `D² (y ↦ c g (a y)) (x) = c a² D²g (a x)`. -/
private lemma hess_hessian_comp_smul (g : (Fin m → ℝ) → ℝ) (c a : ℝ) (x : Fin m → ℝ) :
    hessian (fun y => c * g (a • y)) x = (c * a ^ 2) • hessian g (a • x) := by
  ext i k
  have e : (fun y => fderiv ℝ (fun y => c * g (a • y)) y (Pi.single i 1)) =
      fun y => (c * a) * fderiv ℝ g (a • y) (Pi.single i 1) := by
    funext y
    rw [hess_fderiv_comp_smul]
    rfl
  rw [Matrix.smul_apply, hess_apply, hess_apply, e]
  refine (congrArg (fun L => L (Pi.single k 1))
    (hess_fderiv_comp_smul (fun z => fderiv ℝ g z (Pi.single i 1)) (c * a) a x)).trans ?_
  simp only [smul_apply, smul_eq_mul]
  ring

/-- `D² (y ↦ g (y − b)) (x) = D²g (x − b)`. -/
private lemma hess_hessian_comp_sub (g : (Fin m → ℝ) → ℝ) (b x : Fin m → ℝ) :
    hessian (fun y => g (y - b)) x = hessian g (x - b) := by
  ext i k
  have e : (fun y => fderiv ℝ (fun y => g (y - b)) y (Pi.single i 1)) =
      fun y => fderiv ℝ g (y - b) (Pi.single i 1) := by
    funext y
    rw [fderiv_comp_sub]
  rw [hess_apply, hess_apply, e]
  exact congrArg (fun L => L (Pi.single k 1))
    (fderiv_comp_sub (𝕜 := ℝ) (f := fun z => fderiv ℝ g z (Pi.single i 1)) b)

/-- The Hessian at `x` only depends on the function near `x`. -/
private lemma hess_hessian_congr {u v : (Fin m → ℝ) → ℝ} {x : Fin m → ℝ} (h : u =ᶠ[𝓝 x] v) :
    hessian u x = hessian v x := by
  unfold hessian
  refine cv_grad_congr ?_
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  rw [hy]

/-- The Hessian vanishes off the closed support. -/
private lemma hess_hessian_eq_zero {u : (Fin m → ℝ) → ℝ} {x : Fin m → ℝ} (hx : x ∉ tsupport u) :
    hessian u x = 0 := by
  rw [hess_hessian_congr (notMem_tsupport_iff_eventuallyEq.1 hx)]
  ext i k
  simp [hess_apply]

/-- The Hessian of a product: `D² (η ψ) = η D²ψ + ψ D²η + Dη ⊗ Dψ + Dψ ⊗ Dη`. -/
private lemma hess_hessian_mul {η ψ : (Fin m → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η)
    (hψ : ContDiff ℝ ∞ ψ) (x : Fin m → ℝ) (i k : Fin m) :
    hessian (fun y => η y * ψ y) x i k = η x * hessian ψ x i k + ψ x * hessian η x i k +
      fderiv ℝ η x (Pi.single k 1) * fderiv ℝ ψ x (Pi.single i 1) +
      fderiv ℝ η x (Pi.single i 1) * fderiv ℝ ψ x (Pi.single k 1) := by
  have dη := hess_differentiable hη
  have dψ := hess_differentiable hψ
  have dηi := hess_differentiable (hess_contDiff_fderiv hη (Pi.single i 1))
  have dψi := hess_differentiable (hess_contDiff_fderiv hψ (Pi.single i 1))
  have e : (fun y => fderiv ℝ (fun y => η y * ψ y) y (Pi.single i 1)) = fun y =>
      η y * fderiv ℝ ψ y (Pi.single i 1) + ψ y * fderiv ℝ η y (Pi.single i 1) := by
    funext y
    rw [fderiv_fun_mul (dη y) (dψ y)]
    simp
  rw [hess_apply, e, fderiv_fun_add ((dη x).fun_mul (dψi x)) ((dψ x).fun_mul (dηi x)),
    fderiv_fun_mul (dη x) (dψi x), fderiv_fun_mul (dψ x) (dηi x), hess_apply, hess_apply]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- `x ↦ A + D²u (x)` is measurable, for every `u`. -/
private lemma hess_measurable_add (A : Matrix (Fin m) (Fin m) ℝ) (u : (Fin m → ℝ) → ℝ) :
    Measurable fun x => A + hessian u x :=
  rd_measurable_add_grad A _

/-! ### Bounds -/

/-- The derivatives of a `ℤ^m`-periodic function are periodic. -/
private lemma hess_fderiv_periodic {g : (Fin m → ℝ) → ℝ}
    (hper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), g (x + fun i => (z i : ℝ)) = g x)
    (v x : Fin m → ℝ) (z : Fin m → ℤ) :
    fderiv ℝ g (x + fun i => (z i : ℝ)) v = fderiv ℝ g x v := by
  rw [← fderiv_comp_add_right]
  congr 2
  funext y
  exact hper y z

/-- The Hessian of a `ℤ^m`-periodic function is periodic. -/
private lemma hess_hessian_periodic {u : (Fin m → ℝ) → ℝ}
    (hper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), u (x + fun i => (z i : ℝ)) = u x)
    (x : Fin m → ℝ) (z : Fin m → ℤ) : hessian u (x + fun i => (z i : ℝ)) = hessian u x := by
  ext i k
  rw [hess_apply, hess_apply,
    hess_fderiv_periodic (fun y z => hess_fderiv_periodic hper (Pi.single i 1) y z)]

/-- A continuous `ℤ^m`-periodic function is bounded: it takes all its values on `[0, 1]^m`. -/
private lemma hess_bdd_of_periodic {g : (Fin m → ℝ) → ℝ} (hg : Continuous g)
    (hper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), g (x + fun i => (z i : ℝ)) = g x) :
    ∃ C, ∀ x, |g x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ_pi fun _ =>
    isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, fun x => ?_⟩
  have hx : (x + fun i => ((-⌊x i⌋ : ℤ) : ℝ)) ∈ Set.pi Set.univ fun _ => Set.Icc (0:ℝ) 1 := by
    intro i _
    simp only [Pi.add_apply, Int.cast_neg]
    constructor
    · linarith [Int.floor_le (x i)]
    · linarith [Int.lt_floor_add_one (x i)]
  rw [← hper x (fun i => -⌊x i⌋), ← Real.norm_eq_abs]
  exact hC _ hx

/-- Uniform bounds for a smooth `u` and its first and second derivatives, when the smooth functions
of a class `P` closed under directional derivatives are bounded. -/
private lemma hess_bounds {P : ((Fin m → ℝ) → ℝ) → Prop}
    (hb : ∀ g, ContDiff ℝ ∞ g → P g → ∃ C, ∀ x, |g x| ≤ C)
    (hd : ∀ g v, P g → P fun y => fderiv ℝ g y v) {u : (Fin m → ℝ) → ℝ}
    (hu : ContDiff ℝ ∞ u) (hP : P u) :
    ∃ B, 0 ≤ B ∧ (∀ x, |u x| ≤ B) ∧ (∀ i x, |fderiv ℝ u x (Pi.single i 1)| ≤ B) ∧
      ∀ i k x, |hessian u x i k| ≤ B := by
  obtain ⟨B0, h0⟩ := hb u hu hP
  choose B1 h1 using fun i : Fin m => hb _ (hess_contDiff_fderiv hu (Pi.single i 1)) (hd u _ hP)
  choose B2 h2 using fun p : Fin m × Fin m =>
    hb _ (hess_contDiff_fderiv (hess_contDiff_fderiv hu (Pi.single p.1 1)) (Pi.single p.2 1))
      (hd _ _ (hd u _ hP))
  obtain ⟨D1, hD1⟩ := Finite.bddAbove_range B1
  obtain ⟨D2, hD2⟩ := Finite.bddAbove_range B2
  refine ⟨max (max B0 0) (max D1 D2), le_max_of_le_left (le_max_right _ _),
    fun x => (h0 x).trans (le_max_of_le_left (le_max_left _ _)), fun i x => ?_, fun i k x => ?_⟩
  · exact (h1 i x).trans ((hD1 ⟨i, rfl⟩).trans (le_max_of_le_right (le_max_left _ _)))
  · exact (h2 (i, k) x).trans ((hD2 ⟨(i, k), rfl⟩).trans (le_max_of_le_right (le_max_right _ _)))

/-- `|a − b| ≤ 2 M` if `|a| ≤ M` and `|b| ≤ M`. -/
private lemma hess_abs_sub_le {a b M : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M) : |a - b| ≤ 2 * M := by
  rw [abs_le] at *
  constructor <;> linarith

/-! ### Periodic extension and cut-offs -/

/-- The periodic extension `x ↦ v (fract x)` of a function `v` vanishing off `[δ, 1 − δ]^m` agrees
near every `x` with the translate `v (· − ⌊x⌋)`. -/
private lemma hess_fract_eventuallyEq {v : (Fin m → ℝ) → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hv : ∀ y : Fin m → ℝ, (∃ i, y i < δ ∨ 1 - δ < y i) → v y = 0) (x : Fin m → ℝ) :
    (fun y => v fun i => Int.fract (y i)) =ᶠ[𝓝 x] fun y => v (y - fun i => (⌊x i⌋ : ℝ)) := by
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  by_cases hfl : ∀ i, ⌊y i⌋ = ⌊x i⌋
  · congr 1
    funext i
    rw [Pi.sub_apply, ← hfl i, Int.self_sub_floor]
  · push Not at hfl
    obtain ⟨i, hi⟩ := hfl
    have hyx : |y i - x i| < δ := by
      rw [← Real.dist_eq]; exact (dist_le_pi_dist y x i).trans_lt hy
    have a1 := Int.floor_le (y i)
    have a2 := Int.lt_floor_add_one (y i)
    have b1 := Int.floor_le (x i)
    have b2 := Int.lt_floor_add_one (x i)
    obtain ⟨c1, c2⟩ := abs_lt.1 hyx
    rcases lt_or_gt_of_ne hi with h | h
    · have h' : (⌊y i⌋ : ℝ) + 1 ≤ ⌊x i⌋ := by
        have : ⌊y i⌋ + 1 ≤ ⌊x i⌋ := h
        exact_mod_cast this
      have f1 : 1 - δ < Int.fract (y i) := by rw [← Int.self_sub_floor]; linarith
      have f2 : (y - fun i => (⌊x i⌋ : ℝ)) i < δ := by rw [Pi.sub_apply]; linarith
      rw [hv (fun i => Int.fract (y i)) ⟨i, Or.inr f1⟩,
        hv (y - fun i => (⌊x i⌋ : ℝ)) ⟨i, Or.inl f2⟩]
    · have h' : (⌊x i⌋ : ℝ) + 1 ≤ ⌊y i⌋ := by
        have : ⌊x i⌋ + 1 ≤ ⌊y i⌋ := h
        exact_mod_cast this
      have f1 : Int.fract (y i) < δ := by rw [← Int.self_sub_floor]; linarith
      have f2 : 1 - δ < (y - fun i => (⌊x i⌋ : ℝ)) i := by rw [Pi.sub_apply]; linarith
      rw [hv (fun i => Int.fract (y i)) ⟨i, Or.inl f1⟩,
        hv (y - fun i => (⌊x i⌋ : ℝ)) ⟨i, Or.inr f2⟩]

/-- A smooth cut-off: `1` on the inner cube `(δ, 1 − δ)^m`, with values in `[0, 1]`, and with
compact support in the open unit cube (a bump function for the sup norm, centred at the centre of
the cube). -/
private lemma hess_exists_cutoff {δ : ℝ} (hδ : 0 < δ) (hδ2 : 2 * δ < 1) :
    ∃ η : (Fin m → ℝ) → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ unitCube m ∧
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧ ∀ x ∈ innerCube δ, η x = 1 := by
  let b : ContDiffBump (fun _ : Fin m => (1 / 2 : ℝ)) :=
    ⟨1 / 2 - δ, 1 / 2 - δ / 2, by linarith, by linarith⟩
  have hIn : b.rIn = 1 / 2 - δ := rfl
  have hOut : b.rOut = 1 / 2 - δ / 2 := rfl
  refine ⟨b, b.contDiff, b.hasCompactSupport, ?_, fun x => ⟨b.nonneg, b.le_one⟩,
    fun x hx => b.one_of_mem_closedBall ?_⟩
  · rw [b.tsupport_eq, hOut]
    intro x hx i _
    have h := (dist_le_pi_dist x _ i).trans (mem_closedBall.1 hx)
    rw [Real.dist_eq] at h
    have h' := abs_le.1 h
    constructor <;> linarith [h'.1, h'.2]
  · rw [hIn, mem_closedBall, dist_pi_le_iff (by linarith)]
    intro i
    have := hx i (mem_univ i)
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [this.1, this.2]

/-! ### The two implications -/

/-- **Compactly supported test functions give periodic ones** (Dacorogna, Prop. 5.13, "⇒", for
Hessians): if `∫_{ℝ^m} [f (A + D²v) − f (A)] ≥ 0` for every `v ∈ C_c^∞ (ℝ^m)`, then
`∫_Q [f (A + D²u) − f (A)] ≥ 0` for every `ℤ^m`-periodic `u ∈ C^∞ (ℝ^m)`. -/
theorem setIntegral_unitCube_hessian_nonneg_of_hasCompactSupport
    {f : Matrix (Fin m) (Fin m) ℝ → ℝ} (hf : Measurable f) (hbdd : IsLocallyBounded f)
    (A : Matrix (Fin m) (Fin m) ℝ)
    (h : ∀ v : (Fin m → ℝ) → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v →
      0 ≤ ∫ x, (f (A + hessian v x) - f A))
    {u : (Fin m → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u)
    (hper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), u (x + fun i => (z i : ℝ)) = u x) :
    0 ≤ ∫ x in unitCube m, (f (A + hessian u x) - f A) := by
  have hQm : MeasurableSet (unitCube m) := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hQfin : volume (unitCube m) < ⊤ := by rw [rd_volume_unitCube]; exact ENNReal.one_lt_top
  -- bounds of `u` and of its first and second derivatives
  obtain ⟨B, hB0, hBu, hBd, hBh⟩ := hess_bounds
    (P := fun g => ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), g (x + fun i => (z i : ℝ)) = g x)
    (fun g hg hp => hess_bdd_of_periodic hg.continuous hp)
    (fun g v hp => hess_fderiv_periodic hp v) hu hper
  -- a bound of `f` near `A`
  obtain ⟨M, hM0, hM⟩ := rd_bound_near hbdd A (4 * B)
  have hfA : |f A| ≤ M := by
    simpa using hM 0 fun _ _ => by
      simp only [Matrix.zero_apply, abs_zero, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
      positivity
  have hGm : Measurable fun x => f (A + hessian u x) - f A :=
    (hf.comp (hess_measurable_add A u)).sub measurable_const
  have hGb : ∀ x, |f (A + hessian u x) - f A| ≤ 2 * M := fun x =>
    hess_abs_sub_le (hM _ fun i k => (hBh i k x).trans (by linarith)) hfA
  have hGp : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ),
      f (A + hessian u (x + fun i => (z i : ℝ))) - f A = f (A + hessian u x) - f A :=
    fun x z => by rw [hess_hessian_periodic hper]
  -- the inequality up to the measure of a boundary layer of width `1/j`
  have key : ∀ j : ℕ, 3 ≤ j → -(2 * M * (1 - (1 - 2 * (1 / (j : ℝ))) ^ m)) ≤
      ∫ x in unitCube m, (f (A + hessian u x) - f A) := by
    intro j hj
    have hj' : (3 : ℝ) ≤ j := by exact_mod_cast hj
    set δ : ℝ := 1 / j with hδdef
    have hδ : 0 < δ := by positivity
    have hδ2 : 2 * δ < 1 := by
      rw [hδdef, mul_one_div, div_lt_one (by linarith)]; linarith
    -- the cut-off `η` and the bounds of its derivatives
    obtain ⟨η, hηs, hηc, hηQ, hη01, hη1⟩ := hess_exists_cutoff (m := m) hδ hδ2
    obtain ⟨C, hC0, -, hCd, hCh⟩ := hess_bounds (P := HasCompactSupport)
      (fun g hg hc => by
        obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hc
        exact ⟨C, fun x => by rw [← Real.norm_eq_abs]; exact hC x⟩)
      (fun g v hc => hc.fderiv_apply (𝕜 := ℝ) v) hηs hηc
    -- the frequency `ν ≥ C`
    set ν : ℕ := ⌈C⌉₊ + 1 with hνdef
    have hν : 0 < ν := Nat.succ_pos _
    have hν1 : (1 : ℝ) ≤ ν := by exact_mod_cast hν
    have hνC : C ≤ ν := by rw [hνdef]; push_cast; linarith [Nat.le_ceil C]
    set a : ℝ := (ν : ℝ)⁻¹ with hadef
    have ha0 : 0 < a := by positivity
    have ha1 : a ≤ 1 := inv_le_one_of_one_le₀ hν1
    have haC : a * C ≤ 1 := by
      rw [hadef, inv_mul_le_iff₀ (by positivity)]; linarith
    -- `ψ (x) = ν⁻² u (ν x)`
    set ψ : (Fin m → ℝ) → ℝ := fun y => ((ν : ℝ) ^ 2)⁻¹ * u ((ν : ℝ) • y) with hψdef
    have hψs : ContDiff ℝ ∞ ψ := contDiff_const.mul (hu.comp (contDiff_id.const_smul _))
    have hψ : ∀ x, |ψ x| ≤ a ^ 2 * B := fun x => by
      rw [hψdef, abs_mul, abs_of_pos (by positivity), hadef, inv_pow]
      exact mul_le_mul_of_nonneg_left (hBu _) (by positivity)
    have hψd : ∀ x i, |fderiv ℝ ψ x (Pi.single i 1)| ≤ a * B := fun x i => by
      rw [hψdef, hess_fderiv_comp_smul, smul_apply, smul_eq_mul, abs_mul,
        abs_of_pos (by positivity)]
      have e : ((ν : ℝ) ^ 2)⁻¹ * ν = a := by rw [hadef]; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (hBd _ _) ha0.le
    have hψh : ∀ x, hessian ψ x = hessian u ((ν : ℝ) • x) := fun x => by
      rw [hψdef, hess_hessian_comp_smul, inv_mul_cancel₀ (by positivity), one_smul]
    -- the test function `w = η ψ`
    set w : (Fin m → ℝ) → ℝ := fun y => η y * ψ y with hwdef
    have hws : ContDiff ℝ ∞ w := hηs.mul hψs
    have hwc : HasCompactSupport w := hηc.mul_right
    have hwb : ∀ x i k, |hessian w x i k| ≤ 4 * B := fun x i k => by
      rw [hwdef, hess_hessian_mul hηs hψs, hψh]
      have t1 : |η x * hessian u ((ν : ℝ) • x) i k| ≤ B := by
        rw [abs_mul, abs_of_nonneg (hη01 x).1]
        exact (mul_le_of_le_one_left (abs_nonneg _) (hη01 x).2).trans (hBh i k _)
      have t2 : |ψ x * hessian η x i k| ≤ B := by
        rw [abs_mul]
        calc |ψ x| * |hessian η x i k| ≤ (a ^ 2 * B) * C :=
              mul_le_mul (hψ x) (hCh i k x) (abs_nonneg _) (by positivity)
          _ = (a * C) * a * B := by ring
          _ ≤ 1 * 1 * B := by gcongr
          _ = B := by ring
      have t3 : ∀ p q, |fderiv ℝ η x (Pi.single p 1) * fderiv ℝ ψ x (Pi.single q 1)| ≤ B :=
        fun p q => by
          rw [abs_mul]
          calc |fderiv ℝ η x (Pi.single p 1)| * |fderiv ℝ ψ x (Pi.single q 1)| ≤ C * (a * B) :=
                mul_le_mul (hCd p x) (hψd x q) (abs_nonneg _) hC0
            _ = (a * C) * B := by ring
            _ ≤ 1 * B := by gcongr
            _ = B := one_mul B
      have s1 := abs_add_le (η x * hessian u ((ν : ℝ) • x) i k + ψ x * hessian η x i k +
        fderiv ℝ η x (Pi.single k 1) * fderiv ℝ ψ x (Pi.single i 1))
        (fderiv ℝ η x (Pi.single i 1) * fderiv ℝ ψ x (Pi.single k 1))
      have s2 := abs_add_le (η x * hessian u ((ν : ℝ) • x) i k + ψ x * hessian η x i k)
        (fderiv ℝ η x (Pi.single k 1) * fderiv ℝ ψ x (Pi.single i 1))
      have s3 := abs_add_le (η x * hessian u ((ν : ℝ) • x) i k) (ψ x * hessian η x i k)
      linarith [t3 k i, t3 i k]
    have hwQ : ∀ x ∉ unitCube m, hessian w x = 0 := fun x hx =>
      hess_hessian_eq_zero fun h => hx (hηQ (tsupport_mul_subset_left h))
    have hwi : ∀ x ∈ innerCube δ, hessian w x = hessian ψ x := fun x hx =>
      hess_hessian_congr (by
        filter_upwards [(rd_inner_isOpen δ).mem_nhds hx] with y hy
        simp only [hwdef, hη1 y hy, one_mul])
    -- the hypothesis, as an integral over `Q`
    have h0 := h w hws hwc
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := unitCube m)
      fun x hx => by rw [hwQ x hx, add_zero, sub_self]] at h0
    -- periodicity: `∫_Q f (A + D²ψ) = ∫_Q f (A + D²u)`
    have hperQ : ∫ x in unitCube m, (f (A + hessian ψ x) - f A) =
        ∫ x in unitCube m, (f (A + hessian u x) - f A) := by
      simp_rw [hψh]
      exact rd_setIntegral_comp_nsmul (G := fun x => f (A + hessian u x) - f A) hGm hGb hGp hν
    -- the two integrands agree on the inner cube
    have hb1 : ∀ x, |f (A + hessian w x)| ≤ M := fun x => hM _ (hwb x)
    have hb2 : ∀ x, |f (A + hessian ψ x)| ≤ M := fun x => by
      rw [hψh]; exact hM _ fun i k => (hBh i k _).trans (by linarith)
    have hint : ∀ φ : (Fin m → ℝ) → ℝ, (∀ x, |f (A + hessian φ x)| ≤ M) →
        IntegrableOn (fun x => f (A + hessian φ x) - f A) (unitCube m) := fun φ hφ =>
      IntegrableOn.of_bound hQfin
        ((hf.comp (hess_measurable_add A φ)).sub measurable_const).aestronglyMeasurable (2 * M)
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hess_abs_sub_le (hφ x) hfA)
    have hdiff : ∫ x in unitCube m, ((f (A + hessian w x) - f A) - (f (A + hessian ψ x) - f A)) =
        ∫ x in unitCube m \ innerCube δ,
          ((f (A + hessian w x) - f A) - (f (A + hessian ψ x) - f A)) := by
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQm sdiff_subset fun x hx => ?_
      have hx' : x ∈ innerCube δ := by_contra fun h => hx.2 ⟨hx.1, h⟩
      rw [hwi x hx', sub_self]
    have hbd := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := unitCube m \ innerCube (m := m) δ) ((measure_mono sdiff_subset).trans_lt hQfin)
      (f := fun x => (f (A + hessian w x) - f A) - (f (A + hessian ψ x) - f A)) (C := 2 * M)
      fun x _ => by
        rw [Real.norm_eq_abs, sub_sub_sub_cancel_right]; exact hess_abs_sub_le (hb1 x) (hb2 x)
    rw [← hdiff, integral_sub (hint w hb1) (hint ψ hb2), hperQ, Real.norm_eq_abs,
      rd_volume_real_layer hδ.le hδ2.le] at hbd
    have hle : (∫ x in unitCube m, (f (A + hessian w x) - f A)) -
        ∫ x in unitCube m, (f (A + hessian u x) - f A) ≤ 2 * M * (1 - (1 - 2 * δ) ^ m) :=
      (abs_le.1 hbd).2
    linarith
  -- the limit `j → ∞`
  have hlim : Tendsto (fun j : ℕ => -(2 * M * (1 - (1 - 2 * (1 / (j : ℝ))) ^ m))) atTop
      (𝓝 (-(2 * M * (1 - (1 - 2 * 0) ^ m)))) :=
    (tendsto_const_nhds.mul (tendsto_const_nhds.sub
      ((tendsto_const_nhds.sub (tendsto_const_nhds.mul
        tendsto_one_div_atTop_nhds_zero_nat)).pow m))).neg
  simp only [mul_zero, sub_zero, one_pow, sub_self, neg_zero] at hlim
  exact le_of_tendsto hlim ((eventually_ge_atTop 3).mono key)

/-- **Periodic test functions give compactly supported ones** (Dacorogna, Prop. 5.13, "⇐", for
Hessians): if `∫_Q [f (A + D²v) − f (A)] ≥ 0` for every `ℤ^m`-periodic `v ∈ C^∞ (ℝ^m)`, then
`∫_{ℝ^m} [f (A + D²u) − f (A)] ≥ 0` for every `u ∈ C_c^∞ (ℝ^m)`. -/
theorem integral_hessian_nonneg_of_periodic {f : Matrix (Fin m) (Fin m) ℝ → ℝ}
    (A : Matrix (Fin m) (Fin m) ℝ)
    (h : ∀ v : (Fin m → ℝ) → ℝ, ContDiff ℝ ∞ v →
      (∀ (x : Fin m → ℝ) (z : Fin m → ℤ), v (x + fun i => (z i : ℝ)) = v x) →
      0 ≤ ∫ x in unitCube m, (f (A + hessian v x) - f A))
    {u : (Fin m → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    0 ≤ ∫ x, (f (A + hessian u x) - f A) := by
  have hQm : MeasurableSet (unitCube m) := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  -- a ball `closedBall 0 R` containing the support, and the scale `s = λ = 1/(4R)`
  obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Fin m → ℝ)
  set R : ℝ := max r 1
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR : tsupport u ⊆ closedBall 0 R :=
    hr.trans (closedBall_subset_closedBall (le_max_left _ _))
  set s : ℝ := (4 * R)⁻¹
  have hs : 0 < s := by positivity
  have hsinv : s⁻¹ = 4 * R := inv_inv _
  set c : Fin m → ℝ := fun _ => 1 / 2
  -- the points at distance `> 1/4` from the centre `c` are sent outside the support
  have hout : ∀ (y : Fin m → ℝ) (i : Fin m), 1 / 4 < |y i - 1 / 2| →
      s⁻¹ • (y - c) ∉ tsupport u := by
    intro y i hi hy
    have h1 := mem_closedBall_zero_iff.1 (hR hy)
    have h2 := norm_le_pi_norm (s⁻¹ • (y - c)) i
    have hci : c i = 1 / 2 := rfl
    rw [hsinv] at h1 h2
    rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, hci,
      abs_of_pos (by positivity : (0:ℝ) < 4 * R)] at h2
    nlinarith
  -- the rescaled copy `v (x) = s² u ((x − c) / s)`, supported in `[1/4, 3/4]^m`
  set v : (Fin m → ℝ) → ℝ := fun y => s ^ 2 * u (s⁻¹ • (y - c)) with hvdef
  have hvs : ContDiff ℝ ∞ v :=
    contDiff_const.mul (hu.comp ((contDiff_id.sub contDiff_const).const_smul _))
  have hv0 : ∀ y : Fin m → ℝ, (∃ i, y i < 1 / 4 ∨ 1 - 1 / 4 < y i) → v y = 0 := by
    rintro y ⟨i, hi⟩
    rw [hvdef]
    dsimp only
    rw [image_eq_zero_of_notMem_tsupport (hout y i ?_), mul_zero]
    rcases hi with hi | hi
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hvh : ∀ x, hessian v x = hessian u (s⁻¹ • (x - c)) := fun x => by
    have h1 := hess_hessian_comp_sub (fun z => s ^ 2 * u (s⁻¹ • z)) c x
    have hs2 : s ^ 2 * s⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hs.ne', one_pow]
    rw [hess_hessian_comp_smul, hs2, one_smul] at h1
    exact h1
  -- its periodic extension `vp (x) = v (fract x)`
  set vp : (Fin m → ℝ) → ℝ := fun y => v fun i => Int.fract (y i) with hvpdef
  have hvps : ContDiff ℝ ∞ vp := contDiff_iff_contDiffAt.2 fun x =>
    (hvs.comp (contDiff_id.sub contDiff_const)).contDiffAt.congr_of_eventuallyEq
      (hess_fract_eventuallyEq (by norm_num) hv0 x)
  have hvpp : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), vp (x + fun i => (z i : ℝ)) = vp x :=
    fun x z => by simp only [hvpdef, Pi.add_apply, Int.fract_add_intCast]
  have hvpQ : ∀ x ∈ unitCube m, hessian vp x = hessian u (s⁻¹ • (x - c)) := fun x hx => by
    rw [← hvh]
    refine hess_hessian_congr ?_
    filter_upwards [(isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo).mem_nhds hx] with y hy
    simp only [hvpdef]
    congr 1
    funext i
    exact Int.fract_eq_self.2 ⟨(hy i (mem_univ i)).1.le, (hy i (mem_univ i)).2⟩
  -- off the cube, the integrand vanishes
  have hzero : ∀ x ∉ unitCube m, f (A + hessian u (s⁻¹ • (x - c))) - f A = 0 := by
    intro x hx
    simp only [unitCube, Set.mem_pi, mem_univ, true_implies, mem_Ioo, not_forall, not_and_or,
      not_lt] at hx
    obtain ⟨i, hi⟩ := hx
    rw [hess_hessian_eq_zero (hout x i ?_), add_zero, sub_self]
    rcases hi with hi | hi
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  -- the change of variables `x = c + λ y`
  have key := h vp hvps hvpp
  have e1 : ∫ x in unitCube m, (f (A + hessian vp x) - f A) =
      ∫ x in unitCube m, (f (A + hessian u (s⁻¹ • (x - c))) - f A) :=
    setIntegral_congr_fun hQm fun x hx => by simp only [hvpQ x hx]
  have e2 := cv_integral_comp_affine (fun y => f (A + hessian u y) - f A) c hs
  rw [e1, setIntegral_eq_integral_of_forall_compl_eq_zero hzero, e2] at key
  exact (mul_nonneg_iff_of_pos_left (pow_pos hs m)).1 key

/-- **The periodic and the compactly supported Hessian inequalities are equivalent** at every
matrix `A`, for a Borel, locally bounded `f` (Dacorogna, Prop. 5.13, for Hessians). -/
theorem hessian_periodic_iff_hasCompactSupport
    {f : Matrix (Fin m) (Fin m) ℝ → ℝ} (hf : Measurable f) (hbdd : IsLocallyBounded f)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    (∀ u : (Fin m → ℝ) → ℝ, ContDiff ℝ ∞ u →
      (∀ (x : Fin m → ℝ) (z : Fin m → ℤ), u (x + fun i => (z i : ℝ)) = u x) →
      0 ≤ ∫ x in unitCube m, (f (A + hessian u x) - f A)) ↔
    ∀ u : (Fin m → ℝ) → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u →
      0 ≤ ∫ x, (f (A + hessian u x) - f A) :=
  ⟨fun h _ hu hc => integral_hessian_nonneg_of_periodic A h hu hc,
    fun h _ hu hper => setIntegral_unitCube_hessian_nonneg_of_hasCompactSupport hf hbdd A h hu hper⟩

end CalculusOfVariations
