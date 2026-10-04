/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Extension.Shear
public import LeanPool.EllipticPDE.Embedding.GagliardoNirenberg


/-!
# Weak gradient through a shear

Flattening a `C¹` boundary is a shear, and a Sobolev class has to travel through it. The test
function travels the other way, and a smooth test function pulled back through a `C¹` shear is
`C¹` and no better, which is the class `hasWeakGradOn_contDiffOne` integrates by parts against.

One term of the chain rule asks for more. The pull-back multiplies the test function by a
partial derivative of the chart, which for a `C¹` chart is continuous and no better, so the
product sits outside the `C¹` class. That factor does not depend on the `j`-th coordinate,
mollification preserves that independence, and a mollified factor is smooth, so the product rule
in the `j`-th direction leaves only the term the weak gradient names. Dominated convergence
returns the identity as the mollification shrinks.

## Main declarations

* `EllipticPdes.Extension.fderiv_eq_of_indepCoord`: the derivative of a chart independent of the
  `j`-th coordinate is itself independent of it.
* `EllipticPdes.Extension.indepCoord_partialD`: the same for a partial derivative.
* `EllipticPdes.Extension.indepCoord_convolution`: mollification preserves that independence.
* `EllipticPdes.Extension.integral_mul_indepCoord`: the identity of a weak gradient in the
  `j`-th direction, against a test function scaled by such a factor.
* `EllipticPdes.Extension.hasWeakGradOn_comp_shear`: the weak gradient of a class composed with
  a shear, the transpose of the shear's derivative applied to the gradient.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4 Theorem 1.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal Convolution Pointwise

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn partialD_mul)
open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

local notation "Lsm" => ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)

/-! ### Independence of a coordinate, under differentiation and under mollification -/

/-- **Independence of the `j`-th coordinate passes to a partial derivative.** Translating along
`eⱼ` leaves the chart alone, so it leaves the derivative alone. -/
theorem fderiv_eq_of_indepCoord {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) (y : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    fderiv ℝ γ (y + t • EuclideanSpace.single j (1 : ℝ)) = fderiv ℝ γ y := by
  set c : EuclideanSpace ℝ (Fin d) := t • EuclideanSpace.single j (1 : ℝ) with hc
  have hfun : (fun z => γ (z + c)) = γ := funext fun z => hind z t
  have h1 : HasFDerivAt (fun z => γ (z + c)) (fderiv ℝ γ (y + c)) y := by
    have h := (hγ (y + c)).hasFDerivAt.comp y ((hasFDerivAt_id y).add_const c)
    simpa [Function.comp_def] using h
  rw [hfun] at h1
  exact h1.fderiv.symm

theorem indepCoord_partialD {j k : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) : IndepCoord j (partialD k γ) := by
  intro y t
  simp only [partialD, fderiv_eq_of_indepCoord hγ hind y t]

/-- **Mollification preserves independence of a coordinate.** The convolution averages the
factor over translations, each of which leaves it alone. -/
theorem indepCoord_convolution {j : Fin d} {c : EuclideanSpace ℝ (Fin d) → ℝ}
    (hind : IndepCoord j c) (ρ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))) :
    IndepCoord j (ρ.normed volume ⋆[Lsm, volume] c) := by
  intro y t
  simp only [convolution_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  dsimp only
  have hshift : y + t • EuclideanSpace.single j (1 : ℝ) - s
      = (y - s) + t • EuclideanSpace.single j (1 : ℝ) := by abel
  rw [hshift, hind (y - s) t]

/-- **Bound on a mollification of a bounded factor.** The normed bump is a probability density,
so the convolution is an average and inherits the bound with no compact support to lean on. -/
theorem norm_convolution_normed_le_of_bound (ρ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hc : Continuous h) {M : ℝ} (hM : ∀ y, ‖h y‖ ≤ M)
    (x : EuclideanSpace ℝ (Fin d)) : ‖(ρ.normed volume ⋆[Lsm, volume] h) x‖ ≤ M := by
  have hρc : Continuous (ρ.normed volume) :=
    (ρ.contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) _).continuous
  have hρint : Integrable (ρ.normed volume) volume := ρ.integrable_normed
  have hex : ConvolutionExistsAt (ρ.normed volume) h x Lsm volume :=
    ρ.hasCompactSupport_normed.convolutionExists_left (L := Lsm) hρc hc.locallyIntegrable x
  rw [convolution_def]
  calc ‖∫ t, (Lsm (ρ.normed volume t)) (h (x - t))‖
      ≤ ∫ t, ‖(Lsm (ρ.normed volume t)) (h (x - t))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, ρ.normed volume t * M := by
        refine integral_mono hex.norm (hρint.mul_const M) fun t => ?_
        simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg (ρ.nonneg_normed t)]
        exact mul_le_mul_of_nonneg_left (hM _) (ρ.nonneg_normed t)
    _ = M := by rw [integral_mul_const, ρ.integral_normed, one_mul]

/-! ### Integration by parts against a scaled test function -/

/-- **Integration by parts against a bounded factor independent of the `j`-th coordinate.** The
identity of a weak gradient in the `j`-th direction survives multiplication of the test function
by such a factor, which need only be continuous. Mollification makes the factor smooth and
leaves it independent of the `j`-th coordinate, so the product rule contributes nothing beyond
the term the identity names, and dominated convergence takes the mollification away. -/
theorem integral_mul_indepCoord {B : Set (EuclideanSpace ℝ (Fin d))} (hBopen : IsOpen B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u B volume) (hgi : ∀ k, IntegrableOn (g k) B volume)
    (hwg : HasWeakGradOn B u g) {j : Fin d} {c : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : Continuous c) (hcind : IndepCoord j c) {M : ℝ} (hcb : ∀ y, ‖c y‖ ≤ M)
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ B) :
    ∫ x in B, u x * (c x * partialD j ψ x) = - ∫ x in B, g j x * (c x * ψ x) := by
  classical
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg (c 0)) (hcb 0)
  have hψc : Continuous ψ := hψ.continuous
  have hdc : Continuous (partialD j ψ) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdcs : HasCompactSupport (partialD j ψ) :=
    (hψcs.fderiv ℝ).comp_left (g := fun T : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ =>
      T (EuclideanSpace.single j (1 : ℝ))) (by simp)
  obtain ⟨P, hP⟩ := hψcs.exists_bound_of_continuous hψc
  obtain ⟨N, hN⟩ := hdcs.exists_bound_of_continuous hdc
  have hN0 : (0 : ℝ) ≤ N := le_trans (norm_nonneg _) (hN 0)
  have hP0 : (0 : ℝ) ≤ P := le_trans (norm_nonneg _) (hP 0)
  -- the mollifier family
  set ρ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := fun n =>
    { rIn := 1 / (n + 1) / 2
      rOut := 1 / (n + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := half_lt_self (by positivity) } with hρdef
  have hrOut : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat
  have hcnsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) ((ρ n).normed volume ⋆[Lsm, volume] c) := fun n =>
    (ρ n).hasCompactSupport_normed.contDiff_convolution_left (L := Lsm) (ρ n).contDiff_normed
      hc.locallyIntegrable
  have hcndiff : ∀ n, Differentiable ℝ ((ρ n).normed volume ⋆[Lsm, volume] c) := fun n =>
    (hcnsmooth n).differentiable (by simp)
  have hcnind : ∀ n, IndepCoord j ((ρ n).normed volume ⋆[Lsm, volume] c) := fun n =>
    indepCoord_convolution hcind (ρ n)
  have hcnb : ∀ n x, ‖((ρ n).normed volume ⋆[Lsm, volume] c) x‖ ≤ M := fun n x =>
    norm_convolution_normed_le_of_bound (ρ n) hc hcb x
  have hcnconv : ∀ x, Tendsto (fun n => ((ρ n).normed volume ⋆[Lsm, volume] c) x) atTop
      (𝓝 (c x)) := fun x =>
    ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hrOut hc x
  -- the mollified test functions
  have hθC1 : ∀ n, ContDiff ℝ 1
      (fun z => ((ρ n).normed volume ⋆[Lsm, volume] c) z * ψ z) := fun n =>
    ((hcnsmooth n).of_le (by exact_mod_cast le_top)).mul hψ
  have hθcs : ∀ n, HasCompactSupport
      (fun z => ((ρ n).normed volume ⋆[Lsm, volume] c) z * ψ z) := fun n => hψcs.mul_left
  have hθs : ∀ n, tsupport (fun z => ((ρ n).normed volume ⋆[Lsm, volume] c) z * ψ z) ⊆ B := by
    intro n
    refine subset_trans (closure_mono ?_) hψs
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h
    exact hx (by rw [h, mul_zero])
  have hθd : ∀ n x, partialD j (fun z => ((ρ n).normed volume ⋆[Lsm, volume] c) z * ψ z) x
      = ((ρ n).normed volume ⋆[Lsm, volume] c) x * partialD j ψ x := by
    intro n x
    have hzero : partialD j ((ρ n).normed volume ⋆[Lsm, volume] c) x = 0 :=
      partialD_eq_zero_of_indepCoord (hcndiff n) (hcnind n) x
    rw [partialD_mul j (hcndiff n x) (hψ.differentiable (by simp) x), hzero, zero_mul, zero_add]
  -- the identity, at every mollification
  have hid : ∀ n, ∫ x in B, u x * (((ρ n).normed volume ⋆[Lsm, volume] c) x * partialD j ψ x)
      = - ∫ x in B, g j x * (((ρ n).normed volume ⋆[Lsm, volume] c) x * ψ x) := by
    intro n
    have h := hasWeakGradOn_contDiffOne hBopen hu hgi hwg (hθC1 n) (hθcs n) (hθs n) j
    have hleft : ∫ x in B,
          u x * partialD j (fun z => ((ρ n).normed volume ⋆[Lsm, volume] c) z * ψ z) x
        = ∫ x in B, u x * (((ρ n).normed volume ⋆[Lsm, volume] c) x * partialD j ψ x) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by dsimp only; rw [hθd n x])
    rw [← hleft]
    exact h
  -- both sides converge, by dominated convergence on `B`
  have hL : Tendsto (fun n => ∫ x in B,
        u x * (((ρ n).normed volume ⋆[Lsm, volume] c) x * partialD j ψ x)) atTop
      (𝓝 (∫ x in B, u x * (c x * partialD j ψ x))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => M * N * ‖u x‖) ?_ ?_ ?_ ?_
    · exact fun n => hu.1.mul (((hcnsmooth n).continuous.mul hdc)).aestronglyMeasurable
    · exact hu.norm.const_mul (M * N)
    · intro n
      filter_upwards with x
      have hb : ‖((ρ n).normed volume ⋆[Lsm, volume] c) x * partialD j ψ x‖ ≤ M * N := by
        rw [norm_mul]
        exact mul_le_mul (hcnb n x) (hN x) (norm_nonneg _) hM0
      calc ‖u x * (((ρ n).normed volume ⋆[Lsm, volume] c) x * partialD j ψ x)‖
          = ‖u x‖ * ‖((ρ n).normed volume ⋆[Lsm, volume] c) x * partialD j ψ x‖ := norm_mul _ _
        _ ≤ ‖u x‖ * (M * N) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = M * N * ‖u x‖ := by ring
    · filter_upwards with x using ((hcnconv x).mul_const (partialD j ψ x)).const_mul (u x)
  have hR : Tendsto (fun n => ∫ x in B,
        g j x * (((ρ n).normed volume ⋆[Lsm, volume] c) x * ψ x)) atTop
      (𝓝 (∫ x in B, g j x * (c x * ψ x))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => M * P * ‖g j x‖) ?_ ?_ ?_ ?_
    · exact fun n => (hgi j).1.mul (((hcnsmooth n).continuous.mul hψc)).aestronglyMeasurable
    · exact (hgi j).norm.const_mul (M * P)
    · intro n
      filter_upwards with x
      have hb : ‖((ρ n).normed volume ⋆[Lsm, volume] c) x * ψ x‖ ≤ M * P := by
        rw [norm_mul]
        exact mul_le_mul (hcnb n x) (hP x) (norm_nonneg _) hM0
      calc ‖g j x * (((ρ n).normed volume ⋆[Lsm, volume] c) x * ψ x)‖
          = ‖g j x‖ * ‖((ρ n).normed volume ⋆[Lsm, volume] c) x * ψ x‖ := norm_mul _ _
        _ ≤ ‖g j x‖ * (M * P) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = M * P * ‖g j x‖ := by ring
    · filter_upwards with x using ((hcnconv x).mul_const (ψ x)).const_mul (g j x)
  exact tendsto_nhds_unique hL (by simpa only [hid] using hR.neg)

/-! ### The weak gradient of a composition with a shear -/

/-- **Weak gradient through a shear.** If `u` has weak gradient `g` on `B`, then `u ∘ S` has
weak gradient `k ↦ gₖ ∘ S + (g_j ∘ S) ∂ₖγ` on the preimage of `B`, which is the transpose of the
shear's derivative applied to the gradient.

A smooth test function pulled back through the inverse shear is `C¹`, and the chain rule splits
the identity in two. The first half is the weak gradient tested against that pull-back. The
second has the chart's `k`-th partial as a factor on the test function, and that factor is
independent of the `j`-th coordinate, which is what `integral_mul_indepCoord` asks of it. -/
theorem hasWeakGradOn_comp_shear {B : Set (EuclideanSpace ℝ (Fin d))} (hBopen : IsOpen B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u B volume) (hgi : ∀ k, IntegrableOn (g k) B volume)
    (hwg : HasWeakGradOn B u g) {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hind : IndepCoord j γ) {M : ℝ}
    (hγb : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k γ y‖ ≤ M) :
    HasWeakGradOn (shear j γ ⁻¹' B) (fun y => u (shear j γ y))
      (fun k y => g k (shear j γ y) + g j (shear j γ y) * partialD k γ y) := by
  classical
  intro φ hφ hφcs hφs k
  have hγd : Differentiable ℝ γ := hγ.differentiable (by simp)
  have hnegC1 : ContDiff ℝ 1 fun z => -γ z := hγ.neg
  have hnegcont : Continuous fun z => -γ z := hnegC1.continuous
  have hckc : Continuous (partialD k γ) :=
    (hγ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hckind : IndepCoord j (partialD k γ) := indepCoord_partialD hγd hind
  -- the chart's partial derivative sees no change along the shear
  have hckS : ∀ (m : Fin d) (y : EuclideanSpace ℝ (Fin d)),
      partialD m γ (shear j γ y) = partialD m γ y := fun m y =>
    indepCoord_partialD (k := m) hγd hind y (γ y)
  -- the test function, pulled back through the inverse shear
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ, Ψ = fun x => φ (shear j (fun z => -γ z) x) := ⟨_, rfl⟩
  have hΨC1 : ContDiff ℝ 1 Ψ := by
    rw [hΨ]
    exact (hφ.of_le (by exact_mod_cast le_top)).comp (contDiff_shear hnegC1)
  have hΨcs : HasCompactSupport Ψ := by
    rw [hΨ]
    exact hφcs.comp_homeomorph (shearHomeomorph hnegcont hind.neg)
  have hΨS : ∀ y, Ψ (shear j γ y) = φ y := by
    intro y
    simp only [hΨ]
    rw [shear_shear_neg hind y]
  have hΨs : tsupport Ψ ⊆ B := by
    have hsub1 : tsupport Ψ ⊆ shear j (fun z => -γ z) ⁻¹' tsupport φ := by
      refine closure_minimal ?_ (IsClosed.preimage (continuous_shear hnegcont) isClosed_closure)
      intro x hx
      refine Set.mem_preimage.mpr (subset_tsupport φ ?_)
      simp only [hΨ, Function.mem_support] at hx
      exact hx
    intro x hx
    have h2 := hφs (hsub1 hx)
    simp only [Set.mem_preimage] at h2
    rwa [shear_neg_shear hind x] at h2
  -- the chain rule for the smooth test function
  have hchain : ∀ y, partialD k φ y
      = partialD k Ψ (shear j γ y) + partialD j Ψ (shear j γ y) * partialD k γ y := by
    intro y
    have hΨd : Differentiable ℝ Ψ := hΨC1.differentiable (by simp)
    have hcomp := partialD_comp_shear (j := j) (γ := γ) (φ := Ψ) hγd hΨd k y
    have hfun : (fun z => Ψ (shear j γ z)) = φ := funext hΨS
    rwa [hfun] at hcomp
  -- the change of variables, in both directions
  have hmp : MeasurePreserving (shear j γ) volume volume := measurePreserving_shear hγd hind
  have hme : MeasurableEmbedding (shear j γ) := measurableEmbedding_shear hγd.continuous hind
  have hcv : ∀ F : EuclideanSpace ℝ (Fin d) → ℝ,
      ∫ y in shear j γ ⁻¹' B, F (shear j γ y) = ∫ x in B, F x :=
    fun F => hmp.setIntegral_preimage_emb hme F B
  -- bounds and integrability of the four pieces
  have hΨc : Continuous Ψ := hΨC1.continuous
  have hdkc : Continuous (partialD k Ψ) :=
    (hΨC1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdjc : Continuous (partialD j Ψ) :=
    (hΨC1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdkcs : HasCompactSupport (partialD k Ψ) :=
    (hΨcs.fderiv ℝ).comp_left (g := fun T : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ =>
      T (EuclideanSpace.single k (1 : ℝ))) (by simp)
  have hdjcs : HasCompactSupport (partialD j Ψ) :=
    (hΨcs.fderiv ℝ).comp_left (g := fun T : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ =>
      T (EuclideanSpace.single j (1 : ℝ))) (by simp)
  obtain ⟨Pk, hPk⟩ := hdkcs.exists_bound_of_continuous hdkc
  obtain ⟨Pj, hPj⟩ := hdjcs.exists_bound_of_continuous hdjc
  obtain ⟨PΨ, hPΨ⟩ := hΨcs.exists_bound_of_continuous hΨc
  have hmul : ∀ {w h : EuclideanSpace ℝ (Fin d) → ℝ}, IntegrableOn w B volume →
      Continuous h → ∀ {C : ℝ}, (∀ x, ‖h x‖ ≤ C) → IntegrableOn (fun x => w x * h x) B volume := by
    intro w h hw hcont C hC
    have hbd := hw.bdd_mul (f := h) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
    exact hbd.congr (Filter.Eventually.of_forall fun x => mul_comm (h x) (w x))
  have hi1 : IntegrableOn (fun x => u x * partialD k Ψ x) B volume := hmul hu hdkc hPk
  have hi2 : IntegrableOn (fun x => u x * (partialD k γ x * partialD j Ψ x)) B volume :=
    hmul hu (hckc.mul hdjc) (fun x => by
      rw [norm_mul]; exact mul_le_mul (hγb k x) (hPj x) (norm_nonneg _)
        (le_trans (norm_nonneg _) (hγb k 0)))
  have hi3 : IntegrableOn (fun x => g k x * Ψ x) B volume := hmul (hgi k) hΨc hPΨ
  have hi4 : IntegrableOn (fun x => g j x * (partialD k γ x * Ψ x)) B volume :=
    hmul (hgi j) (hckc.mul hΨc) (fun x => by
      rw [norm_mul]; exact mul_le_mul (hγb k x) (hPΨ x) (norm_nonneg _)
        (le_trans (norm_nonneg _) (hγb k 0)))
  -- both sides, moved onto `B`
  have hLeq : ∫ y in shear j γ ⁻¹' B, u (shear j γ y) * partialD k φ y
      = ∫ x in B, u x * (partialD k Ψ x + partialD j Ψ x * partialD k γ x) := by
    rw [← hcv fun x => u x * (partialD k Ψ x + partialD j Ψ x * partialD k γ x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [hchain y, hckS k y]
  have hReq : ∫ y in shear j γ ⁻¹' B,
        (g k (shear j γ y) + g j (shear j γ y) * partialD k γ y) * φ y
      = ∫ x in B, (g k x + g j x * partialD k γ x) * Ψ x := by
    rw [← hcv fun x => (g k x + g j x * partialD k γ x) * Ψ x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [hckS k y, hΨS y]
  have hsplitL : ∫ x in B, u x * (partialD k Ψ x + partialD j Ψ x * partialD k γ x)
      = (∫ x in B, u x * partialD k Ψ x)
        + ∫ x in B, u x * (partialD k γ x * partialD j Ψ x) := by
    rw [← integral_add hi1 hi2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hsplitR : ∫ x in B, (g k x + g j x * partialD k γ x) * Ψ x
      = (∫ x in B, g k x * Ψ x) + ∫ x in B, g j x * (partialD k γ x * Ψ x) := by
    rw [← integral_add hi3 hi4]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hLeq, hsplitL, hReq, hsplitR,
    hasWeakGradOn_contDiffOne hBopen hu hgi hwg hΨC1 hΨcs hΨs k,
    integral_mul_indepCoord hBopen hu hgi hwg hckc hckind (hγb k) hΨC1 hΨcs hΨs]
  ring

end EllipticPdes.Extension
