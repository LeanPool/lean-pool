/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.Mollify
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Minors of order at most three are null Lagrangians

For Lipschitz maps vanishing outside a compact set, the integrals of the `2 × 2` and `3 × 3` minors
of the gradient vanish (`nl_null2`, `nl_null3`): for smooth compactly supported maps by the
divergence identities (`∂_a u ∂_b v − ∂_b u ∂_a v = ∂_a (u ∂_b v) − ∂_b (u ∂_a v)`, and the
cofactor identity for `3 × 3` minors), and for Lipschitz maps by mollification
(`Lipschitz.Mollify`) and dominated convergence (`nl_lipschitz_limit`). This is the argument of
C. B. Morrey, *Quasi-convexity and the lower semicontinuity of multiple integrals*, Pacific J. Math.
2 (1952), Lemma 5.1 (mollify, then Green's theorem), and of B. Dacorogna, *Direct Methods in the
Calculus of Variations*, 2nd ed., Springer, 2008, Theorems 8.33 and 8.35 (minors as divergences, and
density), which cover minors of every order (`Minors.AllOrders`); here orders `2` and `3`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff Pointwise

namespace CalculusOfVariations

variable {m : ℕ}

/-- The partial derivative `∂_a g`. -/
noncomputable def nlD (a : Fin m) (g : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ) : ℝ :=
  fderiv ℝ g x (Pi.single a 1)

theorem nl_D_contDiff {g : (Fin m → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (a : Fin m) :
    ContDiff ℝ ∞ (nlD a g) :=
  (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem nl_D_mul {g h : (Fin m → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (a : Fin m) : nlD a (fun x => g x * h x) = fun x => nlD a g x * h x + g x * nlD a h x := by
  funext x
  simp only [nlD]
  rw [fderiv_fun_mul ((hg.differentiable (by simp)) x) ((hh.differentiable (by simp)) x)]
  simp [smul_eq_mul]
  ring

theorem nl_D_sub {g h : (Fin m → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (a : Fin m) : nlD a (fun x => g x - h x) = fun x => nlD a g x - nlD a h x := by
  funext x
  simp only [nlD]
  rw [fderiv_fun_sub ((hg.differentiable (by simp)) x) ((hh.differentiable (by simp)) x)]
  rfl

theorem nl_D_add {g h : (Fin m → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (a : Fin m) : nlD a (fun x => g x + h x) = fun x => nlD a g x + nlD a h x := by
  funext x
  simp only [nlD]
  rw [fderiv_fun_add ((hg.differentiable (by simp)) x) ((hh.differentiable (by simp)) x)]
  rfl

/-- Symmetry of second derivatives: `∂_a ∂_b g = ∂_b ∂_a g`. -/
theorem nl_D_comm {g : (Fin m → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (a b : Fin m) :
    nlD a (nlD b g) = nlD b (nlD a g) := by
  funext x
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  have hsymm := (hg.contDiffAt (x := x)).isSymmSndFDerivAt (n := ∞) (by simp)
  change fderiv ℝ (fun y => fderiv ℝ g y (Pi.single b 1)) x (Pi.single a 1) =
    fderiv ℝ (fun y => fderiv ℝ g y (Pi.single a 1)) x (Pi.single b 1)
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd
      (differentiableAt_const _)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact hsymm _ _

/-- `∫ ∂_a w = 0` for smooth compactly supported `w`. -/
theorem nl_integral_D_eq_zero {w : (Fin m → ℝ) → ℝ} (hw : ContDiff ℝ ∞ w)
    (hwc : HasCompactSupport w) (a : Fin m) : ∫ x, nlD a w x = 0 := by
  obtain ⟨K, hK⟩ := hw.lipschitzWith_of_hasCompactSupport hwc (by simp) (𝕂 := ℝ)
  exact plancherel_integral_fderiv_eq_zero hK hwc _

theorem nl_hasCompactSupport_D {g : (Fin m → ℝ) → ℝ} (hgc : HasCompactSupport g) (a : Fin m) :
    HasCompactSupport (nlD a g) :=
  (hgc.fderiv ℝ).comp_left (g := fun L : (Fin m → ℝ) →L[ℝ] ℝ => L (Pi.single a 1)) rfl

theorem nl_integrable_of_smooth {g : (Fin m → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) : Integrable g :=
  hg.continuous.integrable_of_hasCompactSupport hgc

/-- **`2 × 2` minors, smooth case**: `∫ (∂_a u ∂_b v − ∂_b u ∂_a v) = 0`. -/
theorem nl_null2_smooth {u v : (Fin m → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (huc : HasCompactSupport u) (a b : Fin m) :
    ∫ x, (nlD a u x * nlD b v x - nlD b u x * nlD a v x) = 0 := by
  have hDv := fun c => nl_D_contDiff hv c
  have e : (fun x => nlD a u x * nlD b v x - nlD b u x * nlD a v x) =
      fun x => nlD a (fun y => u y * nlD b v y) x - nlD b (fun y => u y * nlD a v y) x := by
    rw [nl_D_mul hu (hDv b), nl_D_mul hu (hDv a), nl_D_comm hv a b]
    funext x; ring
  rw [e]
  have hw1 : ContDiff ℝ ∞ fun y => u y * nlD b v y := hu.mul (hDv b)
  have hw2 : ContDiff ℝ ∞ fun y => u y * nlD a v y := hu.mul (hDv a)
  have hc1 : HasCompactSupport fun y => u y * nlD b v y := huc.mul_right
  have hc2 : HasCompactSupport fun y => u y * nlD a v y := huc.mul_right
  rw [integral_sub (nl_integrable_of_smooth (nl_D_contDiff hw1 a) (nl_hasCompactSupport_D hc1 a))
    (nl_integrable_of_smooth (nl_D_contDiff hw2 b) (nl_hasCompactSupport_D hc2 b)),
    nl_integral_D_eq_zero hw1 hc1, nl_integral_D_eq_zero hw2 hc2, sub_zero]

/-- The `3 × 3` minor `det [∂_{a_j} u_i]`. -/
noncomputable def nlDet3 (u₀ u₁ u₂ : (Fin m → ℝ) → ℝ) (a₀ a₁ a₂ : Fin m) (x : Fin m → ℝ) : ℝ :=
  nlD a₀ u₀ x * (nlD a₁ u₁ x * nlD a₂ u₂ x - nlD a₂ u₁ x * nlD a₁ u₂ x) -
    nlD a₁ u₀ x * (nlD a₀ u₁ x * nlD a₂ u₂ x - nlD a₂ u₁ x * nlD a₀ u₂ x) +
    nlD a₂ u₀ x * (nlD a₀ u₁ x * nlD a₁ u₂ x - nlD a₁ u₁ x * nlD a₀ u₂ x)

/-- **`3 × 3` minors, smooth case**: `∫ det [∂_{a_j} u_i] = 0`, by
`det = Σ_j ∂_{a_j} (u₀ C_j)` with the cofactors `C_j` of the first row, whose divergence
`Σ_j ∂_{a_j} C_j` vanishes (Piola). -/
theorem nl_null3_smooth {u₀ u₁ u₂ : (Fin m → ℝ) → ℝ} (h₀ : ContDiff ℝ ∞ u₀)
    (h₁ : ContDiff ℝ ∞ u₁) (h₂ : ContDiff ℝ ∞ u₂) (hc : HasCompactSupport u₀)
    (a₀ a₁ a₂ : Fin m) : ∫ x, nlDet3 u₀ u₁ u₂ a₀ a₁ a₂ x = 0 := by
  have D1 := fun c => nl_D_contDiff h₁ c
  have D2 := fun c => nl_D_contDiff h₂ c
  -- the cofactors of the first row
  set C₀ : (Fin m → ℝ) → ℝ := fun x => nlD a₁ u₁ x * nlD a₂ u₂ x - nlD a₂ u₁ x * nlD a₁ u₂ x
  set C₁ : (Fin m → ℝ) → ℝ := fun x => nlD a₀ u₁ x * nlD a₂ u₂ x - nlD a₂ u₁ x * nlD a₀ u₂ x
  set C₂ : (Fin m → ℝ) → ℝ := fun x => nlD a₀ u₁ x * nlD a₁ u₂ x - nlD a₁ u₁ x * nlD a₀ u₂ x
  have hC₀ : ContDiff ℝ ∞ C₀ := ((D1 a₁).mul (D2 a₂)).sub ((D1 a₂).mul (D2 a₁))
  have hC₁ : ContDiff ℝ ∞ C₁ := ((D1 a₀).mul (D2 a₂)).sub ((D1 a₂).mul (D2 a₀))
  have hC₂ : ContDiff ℝ ∞ C₂ := ((D1 a₀).mul (D2 a₁)).sub ((D1 a₁).mul (D2 a₀))
  -- the Piola identity
  have hP : ∀ x, nlD a₀ C₀ x - nlD a₁ C₁ x + nlD a₂ C₂ x = 0 := by
    intro x
    simp only [C₀, C₁, C₂]
    rw [nl_D_sub ((D1 a₁).mul (D2 a₂)) ((D1 a₂).mul (D2 a₁)),
      nl_D_sub ((D1 a₀).mul (D2 a₂)) ((D1 a₂).mul (D2 a₀)),
      nl_D_sub ((D1 a₀).mul (D2 a₁)) ((D1 a₁).mul (D2 a₀))]
    simp only
    rw [nl_D_mul (D1 a₁) (D2 a₂), nl_D_mul (D1 a₂) (D2 a₁), nl_D_mul (D1 a₀) (D2 a₂),
      nl_D_mul (D1 a₂) (D2 a₀), nl_D_mul (D1 a₀) (D2 a₁), nl_D_mul (D1 a₁) (D2 a₀)]
    simp only
    rw [nl_D_comm h₁ a₀ a₁, nl_D_comm h₁ a₀ a₂, nl_D_comm h₁ a₁ a₂,
      nl_D_comm h₂ a₀ a₁, nl_D_comm h₂ a₀ a₂, nl_D_comm h₂ a₁ a₂]
    ring
  have e : nlDet3 u₀ u₁ u₂ a₀ a₁ a₂ = fun x =>
      nlD a₀ (fun y => u₀ y * C₀ y) x - nlD a₁ (fun y => u₀ y * C₁ y) x +
        nlD a₂ (fun y => u₀ y * C₂ y) x := by
    rw [nl_D_mul h₀ hC₀, nl_D_mul h₀ hC₁, nl_D_mul h₀ hC₂]
    funext x
    have := hP x
    simp only [nlDet3]
    linear_combination (-(u₀ x)) * this
  rw [e]
  have w0 : ContDiff ℝ ∞ fun y => u₀ y * C₀ y := h₀.mul hC₀
  have w1 : ContDiff ℝ ∞ fun y => u₀ y * C₁ y := h₀.mul hC₁
  have w2 : ContDiff ℝ ∞ fun y => u₀ y * C₂ y := h₀.mul hC₂
  have c0 : HasCompactSupport fun y => u₀ y * C₀ y := hc.mul_right
  have c1 : HasCompactSupport fun y => u₀ y * C₁ y := hc.mul_right
  have c2 : HasCompactSupport fun y => u₀ y * C₂ y := hc.mul_right
  have i0 := nl_integrable_of_smooth (nl_D_contDiff w0 a₀) (nl_hasCompactSupport_D c0 a₀)
  have i1 := nl_integrable_of_smooth (nl_D_contDiff w1 a₁) (nl_hasCompactSupport_D c1 a₁)
  have i2 := nl_integrable_of_smooth (nl_D_contDiff w2 a₂) (nl_hasCompactSupport_D c2 a₂)
  beta_reduce
  rw [integral_add (f := fun x => nlD a₀ (fun y => u₀ y * C₀ y) x -
      nlD a₁ (fun y => u₀ y * C₁ y) x) (i0.sub i1) i2,
    integral_sub i0 i1, nl_integral_D_eq_zero w0 c0,
    nl_integral_D_eq_zero w1 c1, nl_integral_D_eq_zero w2 c2]
  ring

/-- **Mollification**: an identity `∫ Φ (∇ψ) = 0`, valid for smooth compactly supported `ψ`,
passes to compactly supported Lipschitz maps, for continuous `Φ` with `Φ (0) = 0` (the
mollifications `ρ_n ⋆ u_i` are smooth with compact support, and their derivatives are bounded,
supported in a fixed compact set and converge almost everywhere). -/
theorem nl_lipschitz_limit {k : ℕ} (u : Fin k → (Fin m → ℝ) → ℝ) (K : Fin k → NNReal)
    (hu : ∀ i, LipschitzWith (K i) (u i)) (huc : ∀ i, HasCompactSupport (u i))
    (Φ : (Fin k → Fin m → ℝ) → ℝ) (hΦ : Continuous Φ) (hΦ0 : Φ 0 = 0)
    (hsmooth : ∀ ψ : Fin k → (Fin m → ℝ) → ℝ, (∀ i, ContDiff ℝ ∞ (ψ i)) →
      (∀ i, HasCompactSupport (ψ i)) → ∫ x, Φ (fun i a => nlD a (ψ i) x) = 0) :
    ∫ x, Φ (fun i a => fderiv ℝ (u i) x (Pi.single a 1)) = 0 := by
  set ψ : ℕ → Fin k → (Fin m → ℝ) → ℝ :=
    fun n i => plancherelMollify volume (plancherelBump m n)
      (u i) with hψ
  have hψs : ∀ n i, ContDiff ℝ ∞ (ψ n i) := fun n i =>
    plancherelMollify_contDiff _ (hu i).continuous
  have hψc : ∀ n i, HasCompactSupport (ψ n i) := fun n i =>
    plancherelMollify_hasCompactSupport _ (huc i)
  have hn : ∀ n, ∫ x, Φ (fun i a => nlD a (ψ n i) x) = 0 := fun n => hsmooth _ (hψs n) (hψc n)
  have hbd : ∀ n i (v : Fin m → ℝ) x, |fderiv ℝ (ψ n i) x v| ≤ K i * ‖v‖ := by
    intro n i v x
    rw [plancherelMollify_fderiv _ (hu i)]
    exact plancherelMollify_abs_le _ (fun y => by
      simpa [Real.norm_eq_abs] using norm_lineDeriv_le_of_lipschitz ℝ (hu i) (x₀ := y) (v := v)) x
  set S := ⋃ i, Metric.closedBall (0 : Fin m → ℝ) 1 + tsupport (u i) with hS
  have hSc : IsCompact S := isCompact_iUnion fun i => (isCompact_closedBall _ _).add (huc i)
  have hsupp : ∀ n i (v : Fin m → ℝ) x, x ∉ S → fderiv ℝ (ψ n i) x v = 0 := by
    intro n i v x hx
    rw [plancherelMollify_fderiv _ (hu i)]
    exact plancherelMollify_eq_zero _
      (plancherelBump_rOut_le m n)
      (fun y hy => plancherel_lineDeriv_eq_zero_of_notMem hy v)
      (fun h => hx (Set.mem_iUnion.mpr ⟨i, h⟩))
  -- a bound for `Φ` on the box of admissible gradients
  set B : Set (Fin k → Fin m → ℝ) :=
    Set.pi Set.univ fun i => Set.pi Set.univ fun a =>
      Set.Icc (-(K i * ‖(Pi.single a 1 : Fin m → ℝ)‖)) (K i * ‖(Pi.single a 1 : Fin m → ℝ)‖)
  have hBc : IsCompact B := isCompact_univ_pi fun i => isCompact_univ_pi fun a => isCompact_Icc
  obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn hΦ.continuousOn
  have hmem : ∀ n x, (fun i a => nlD a (ψ n i) x) ∈ B := by
    intro n x i _ a _
    exact abs_le.mp (hbd n i _ x)
  have hlim : Tendsto (fun n => ∫ x, Φ (fun i a => nlD a (ψ n i) x)) atTop
      (𝓝 (∫ x, Φ (fun i a => fderiv ℝ (u i) x (Pi.single a 1)))) := by
    refine tendsto_integral_of_dominated_convergence (S.indicator fun _ => M) (fun n => ?_) ?_
      (fun n => ?_) ?_
    · have : Continuous fun x => (fun i a => nlD a (ψ n i) x) :=
        continuous_pi fun i => continuous_pi fun a => (nl_D_contDiff (hψs n i) a).continuous
      exact (hΦ.comp this).aestronglyMeasurable
    · exact (integrable_indicator_iff hSc.measurableSet).2
        (integrableOn_const hSc.measure_lt_top.ne)
    · filter_upwards with x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]
        exact hM _ (hmem n x)
      · rw [Set.indicator_of_notMem hx]
        have : (fun i a => nlD a (ψ n i) x) = 0 := by
          funext i a; exact hsupp n i _ x hx
        rw [this, hΦ0, norm_zero]
    · have hae : ∀ᵐ x, ∀ i : Fin k, ∀ a : Fin m, Tendsto
          (fun n => fderiv ℝ (ψ n i) x (Pi.single a 1)) atTop
          (𝓝 (fderiv ℝ (u i) x (Pi.single a 1))) := by
        rw [ae_all_iff]; intro i
        rw [ae_all_iff]; intro a
        exact plancherel_ae_tendsto (hu i) _
      filter_upwards [hae] with x hx
      exact (hΦ.tendsto _).comp (tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun a => hx i a)
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun n => (hn n).symm) hlim |>.symm

/-- **`2 × 2` minors are null Lagrangians** (Lipschitz, compact support). -/
theorem nl_null2 {u v : (Fin m → ℝ) → ℝ} {Ku Kv : NNReal} (hu : LipschitzWith Ku u)
    (hv : LipschitzWith Kv v) (huc : HasCompactSupport u) (hvc : HasCompactSupport v)
    (a b : Fin m) :
    ∫ x, (fderiv ℝ u x (Pi.single a 1) * fderiv ℝ v x (Pi.single b 1) -
      fderiv ℝ u x (Pi.single b 1) * fderiv ℝ v x (Pi.single a 1)) = 0 := by
  have := nl_lipschitz_limit ![u, v] ![Ku, Kv]
    (fun i => by fin_cases i <;> simpa) (fun i => by fin_cases i <;> simpa)
    (fun G => G 0 a * G 1 b - G 0 b * G 1 a) (by fun_prop) (by simp)
    (fun ψ hψ hψc => nl_null2_smooth (hψ 0) (hψ 1) (hψc 0) a b)
  simpa using this

/-- **`3 × 3` minors are null Lagrangians** (Lipschitz, compact support). -/
theorem nl_null3 {u₀ u₁ u₂ : (Fin m → ℝ) → ℝ} {K₀ K₁ K₂ : NNReal} (h₀ : LipschitzWith K₀ u₀)
    (h₁ : LipschitzWith K₁ u₁) (h₂ : LipschitzWith K₂ u₂) (c₀ : HasCompactSupport u₀)
    (c₁ : HasCompactSupport u₁) (c₂ : HasCompactSupport u₂) (a₀ a₁ a₂ : Fin m) :
    ∫ x, (fderiv ℝ u₀ x (Pi.single a₀ 1) * (fderiv ℝ u₁ x (Pi.single a₁ 1) *
        fderiv ℝ u₂ x (Pi.single a₂ 1) - fderiv ℝ u₁ x (Pi.single a₂ 1) *
        fderiv ℝ u₂ x (Pi.single a₁ 1)) -
      fderiv ℝ u₀ x (Pi.single a₁ 1) * (fderiv ℝ u₁ x (Pi.single a₀ 1) *
        fderiv ℝ u₂ x (Pi.single a₂ 1) - fderiv ℝ u₁ x (Pi.single a₂ 1) *
        fderiv ℝ u₂ x (Pi.single a₀ 1)) +
      fderiv ℝ u₀ x (Pi.single a₂ 1) * (fderiv ℝ u₁ x (Pi.single a₀ 1) *
        fderiv ℝ u₂ x (Pi.single a₁ 1) - fderiv ℝ u₁ x (Pi.single a₁ 1) *
        fderiv ℝ u₂ x (Pi.single a₀ 1))) = 0 := by
  have := nl_lipschitz_limit ![u₀, u₁, u₂] ![K₀, K₁, K₂]
    (fun i => by fin_cases i <;> simpa) (fun i => by fin_cases i <;> simpa)
    (fun G => G 0 a₀ * (G 1 a₁ * G 2 a₂ - G 1 a₂ * G 2 a₁) -
      G 0 a₁ * (G 1 a₀ * G 2 a₂ - G 1 a₂ * G 2 a₀) +
      G 0 a₂ * (G 1 a₀ * G 2 a₁ - G 1 a₁ * G 2 a₀)) (by fun_prop) (by simp)
    (fun ψ hψ hψc => nl_null3_smooth (hψ 0) (hψ 1) (hψ 2) (hψc 0) a₀ a₁ a₂)
  simpa using this

end CalculusOfVariations
