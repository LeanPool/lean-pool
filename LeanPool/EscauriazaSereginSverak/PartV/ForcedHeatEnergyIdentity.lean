/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatEnergyCore

/-!
# The whole-space entropy identity for the smooth forced heat response

At each time, integrating by parts in space turns the entropy production
`∑_i T_i(Z) ∂_t Z_i` of the forced heat response into
`-∑_{i,j} ∂_j[T_i(Z)] (∂_j Z_i + g_ij)`. Combined with the time integration of
`entropy_integral_eq_window_integral`, this is the identity behind the energy
and critical estimates of `lem:pv-stokes`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The spatial derivative of a time slice of a differentiable space-time
function is the joint derivative in the corresponding spatial direction. -/
theorem fderiv_slice_apply {F : Vec3 × ℝ → ℝ} (hF : Differentiable ℝ F)
    (x : Vec3) (t : ℝ) (v : Vec3) :
    fderiv ℝ (fun y : Vec3 => F (y, t)) x v = fderiv ℝ F (x, t) (v, 0) := by
  have hinner : HasFDerivAt (fun y : Vec3 => ((y, t) : Vec3 × ℝ))
      ((ContinuousLinearMap.id ℝ Vec3).prod 0) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
  have hcomp := (hF (x, t)).hasFDerivAt.comp x hinner
  rw [show (fun y : Vec3 => F (y, t)) = F ∘ (fun y : Vec3 => ((y, t) : Vec3 × ℝ)) from rfl,
    hcomp.fderiv]
  rfl

/-- Chain rule for a map applied to a time slice of a smooth vector field. -/
theorem fderiv_comp_slice_apply {T : Vec3 → Vec3} (hT : Differentiable ℝ T)
    {U : Fin 3 → Vec3 × ℝ → ℝ} (hU : ∀ k, Differentiable ℝ (U k))
    (x : Vec3) (t : ℝ) (v : Vec3) (i : Fin 3) :
    fderiv ℝ (fun y : Vec3 => T (fun k => U k (y, t)) i) x v =
      fderiv ℝ T (fun k => U k (x, t)) (fun k => fderiv ℝ (U k) (x, t) (v, 0)) i := by
  have hslice (k : Fin 3) : Differentiable ℝ (fun y : Vec3 => U k (y, t)) :=
    (hU k).comp (differentiable_id.prodMk (differentiable_const t))
  have hZ : HasFDerivAt (fun y : Vec3 => fun k => U k (y, t))
      (ContinuousLinearMap.pi fun k => fderiv ℝ (fun y : Vec3 => U k (y, t)) x) x :=
    hasFDerivAt_pi.2 fun k => (hslice k x).hasFDerivAt
  have hcomp := (hT (fun k => U k (x, t))).hasFDerivAt.comp x hZ
  have hi := (hasFDerivAt_pi'.1 hcomp i).fderiv
  change fderiv ℝ (fun y => (T ∘ fun y : Vec3 => fun k => U k (y, t)) y i) x v = _
  rw [hi]
  change fderiv ℝ T (fun k => U k (x, t))
      ((ContinuousLinearMap.pi fun k => fderiv ℝ (fun y : Vec3 => U k (y, t)) x) v) i = _
  have hvec : (ContinuousLinearMap.pi fun k => fderiv ℝ (fun y : Vec3 => U k (y, t)) x) v =
      fun k => fderiv ℝ (U k) (x, t) (v, 0) := by
    funext k
    exact fderiv_slice_apply (hU k) x t v
  rw [hvec]

/-- Integration by parts on Vec3 for continuously differentiable functions
with `(1 + |x|)^{-3}` decay together with their derivatives. -/
theorem integral_mul_fderiv_of_decay {f k : Vec3 → ℝ} (hf : ContDiff ℝ 1 f)
    (hk : ContDiff ℝ 1 k) {A : ℝ} (hA : 0 ≤ A) (v : Vec3)
    (hfb : ∀ x, |f x| ≤ A / (1 + vec3EuclideanNorm x) ^ 3)
    (hDfb : ∀ x, |fderiv ℝ f x v| ≤ A / (1 + vec3EuclideanNorm x) ^ 3)
    (hkb : ∀ x, |k x| ≤ A / (1 + vec3EuclideanNorm x) ^ 3)
    (hDkb : ∀ x, |fderiv ℝ k x v| ≤ A / (1 + vec3EuclideanNorm x) ^ 3) :
    ∫ x, f x * fderiv ℝ k x v = -∫ x, fderiv ℝ f x v * k x := by
  have hDf : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDk : Continuous (fun x => fderiv ℝ k x v) :=
    (hk.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_of_decay hDf.aestronglyMeasurable hk.continuous.aestronglyMeasurable
      hA hA hDfb hkb)
    (integrable_mul_of_decay hf.continuous.aestronglyMeasurable hDk.aestronglyMeasurable
      hA hA hfb hDkb)
    (integrable_mul_of_decay hf.continuous.aestronglyMeasurable
      hk.continuous.aestronglyMeasurable hA hA hfb hkb)
    (fun x _ => hf.differentiable one_ne_zero x) (fun x _ => hk.differentiable one_ne_zero x)

/-- At each time, the entropy production of the forced heat response
integrates by parts to `-∑_{i,j} ∫ ∂_j[T_i(Z)] (∂_j Z_i + g_ij)`. -/
theorem response_production_identity {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j))
    {T : Vec3 → Vec3} (hT : ContDiff ℝ 1 T) (hT0 : T 0 = 0) (t : ℝ) :
    ∫ x, ∑ i : Fin 3, T (responseVec g (x, t)) i *
        fderiv ℝ (causalHeatConv (vecTimeDiv g i)) (x, t) (0, 1) =
      -∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ T (responseVec g (x, t)) (responseGrad g j (x, t)) i *
          (responseGrad g j (x, t) i + g i j (x, t)) := by
  let U : Fin 3 → Vec3 × ℝ → ℝ := fun i => causalHeatConv (vecTimeDiv g i)
  have hU (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (U i) :=
    causalHeatConv_contDiff (vecTimeDiv_contDiff hg i) (vecTimeDiv_hasCompactSupport hgc i)
  have hUd (i : Fin 3) : Differentiable ℝ (U i) := (hU i).differentiable (by simp)
  obtain ⟨M, hM, hdec⟩ := vecTimeDiv_response_decay hg hgc
  obtain ⟨L, hL, hLb⟩ := exists_linear_bound_of_contDiff hT hT0 M
  let e : Fin 3 → Vec3 := fun j => CKN.basisVec j
  let f : Fin 3 → Vec3 → ℝ := fun i y => T (fun k => U k (y, t)) i
  let k : Fin 3 → Fin 3 → Vec3 → ℝ := fun i j y => fderiv ℝ (U i) (y, t) (e j, 0)
  let s : Fin 3 → Fin 3 → Vec3 → ℝ := fun i j y => g i j (y, t)
  have hsl : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => ((y, t) : Vec3 × ℝ)) :=
    contDiff_id.prodMk contDiff_const
  have hZs : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => fun k => U k (y, t)) :=
    contDiff_pi.2 fun k => (hU k).comp hsl
  have hf (i : Fin 3) : ContDiff ℝ 1 (f i) :=
    (contDiff_apply ℝ ℝ i).comp (hT.comp (hZs.of_le (by simp)))
  have hk (i j : Fin 3) : ContDiff ℝ 1 (k i j) :=
    ((contDiff_fderiv_apply_const (hU i) (e j, 0)).comp hsl).of_le (by simp)
  have hs (i j : Fin 3) : ContDiff ℝ 1 (s i j) := ((hg i j).comp hsl).of_le (by simp)
  have hDf (i j : Fin 3) (y : Vec3) : fderiv ℝ (f i) y (e j) =
      fderiv ℝ T (responseVec g (y, t)) (responseGrad g j (y, t)) i :=
    fderiv_comp_slice_apply (hT.differentiable one_ne_zero) hUd y t (e j) i
  have hDk (i j : Fin 3) (y : Vec3) : fderiv ℝ (k i j) y (e j) =
      fderiv ℝ (fun p => fderiv ℝ (U i) p (e j, 0)) (y, t) (e j, 0) :=
    fderiv_slice_apply ((contDiff_fderiv_apply_const (hU i) (e j, 0)).differentiable
      (by simp)) y t (e j)
  have hDs (i j : Fin 3) (y : Vec3) : fderiv ℝ (s i j) y (e j) =
      fderiv ℝ (g i j) (y, t) (e j, 0) :=
    fderiv_slice_apply ((hg i j).differentiable (by simp)) y t (e j)
  -- pointwise bounds
  let w : Vec3 → ℝ := fun y => (1 + vec3EuclideanNorm y) ^ 3
  have hw (y : Vec3) : 1 ≤ w y := one_le_pow₀ (by
    have := vec3EuclideanNorm_nonneg y
    linarith only [this])
  have hwpos (y : Vec3) : 0 < w y := lt_of_lt_of_le zero_lt_one (hw y)
  have hdivle (y : Vec3) : M / w y ≤ M := div_le_self hM (hw y)
  have hZnorm (y : Vec3) : ‖responseVec g (y, t)‖ ≤ M / w y :=
    (pi_norm_le_iff_of_nonneg (div_nonneg hM (hwpos y).le)).2 fun k => by
      rw [Real.norm_eq_abs]
      exact (hdec k k k (y, t)).1
  have hGnorm (j : Fin 3) (y : Vec3) : ‖responseGrad g j (y, t)‖ ≤ M / w y :=
    (pi_norm_le_iff_of_nonneg (div_nonneg hM (hwpos y).le)).2 fun k => by
      rw [Real.norm_eq_abs]
      exact (hdec k j j (y, t)).2.1
  let A : ℝ := L * M + M
  have hA : 0 ≤ A := by positivity
  have hLMA : L * (M / w 0) ≤ A := by
    have := hdivle 0
    nlinarith only [this, hL, hM]
  have hfb (i : Fin 3) (y : Vec3) : |f i y| ≤ A / w y := by
    have h1 : |f i y| ≤ ‖T (responseVec g (y, t))‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm (T (responseVec g (y, t))) i
    have h2 := (hLb _ ((hZnorm y).trans (hdivle y))).1
    calc
      |f i y| ≤ L * ‖responseVec g (y, t)‖ := h1.trans h2
      _ ≤ L * (M / w y) := mul_le_mul_of_nonneg_left (hZnorm y) hL
      _ ≤ A / w y := by
        rw [mul_div_assoc']
        exact div_le_div_of_nonneg_right (by linarith only [hM]) (hwpos y).le
  have hDfb (i j : Fin 3) (y : Vec3) : |fderiv ℝ (f i) y (e j)| ≤ A / w y := by
    rw [hDf]
    have h1 : |fderiv ℝ T (responseVec g (y, t)) (responseGrad g j (y, t)) i| ≤
        ‖fderiv ℝ T (responseVec g (y, t))‖ * ‖responseGrad g j (y, t)‖ := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm _ i).trans (ContinuousLinearMap.le_opNorm _ _)
    have h2 := (hLb _ ((hZnorm y).trans (hdivle y))).2
    calc
      _ ≤ ‖fderiv ℝ T (responseVec g (y, t))‖ * ‖responseGrad g j (y, t)‖ := h1
      _ ≤ L * (M / w y) := mul_le_mul h2 (hGnorm j y) (norm_nonneg _) hL
      _ ≤ A / w y := by
        rw [mul_div_assoc']
        exact div_le_div_of_nonneg_right (by linarith only [hM]) (hwpos y).le
  have hMA : M ≤ A := by
    have : 0 ≤ L * M := mul_nonneg hL hM
    linarith only [this]
  have hkb (i j : Fin 3) (y : Vec3) : |k i j y| ≤ A / w y :=
    (hdec i j j (y, t)).2.1.trans (div_le_div_of_nonneg_right hMA (hwpos y).le)
  have hDkb (i j : Fin 3) (y : Vec3) : |fderiv ℝ (k i j) y (e j)| ≤ A / w y := by
    rw [hDk]
    exact (hdec i j j (y, t)).2.2.1.trans (div_le_div_of_nonneg_right hMA (hwpos y).le)
  have hsb (i j : Fin 3) (y : Vec3) : |s i j y| ≤ A / w y :=
    (hdec i j j (y, t)).2.2.2.2.1.trans (div_le_div_of_nonneg_right hMA (hwpos y).le)
  have hDsb (i j : Fin 3) (y : Vec3) : |fderiv ℝ (s i j) y (e j)| ≤ A / w y := by
    rw [hDs]
    exact (hdec i j j (y, t)).2.2.2.2.2.trans (div_le_div_of_nonneg_right hMA (hwpos y).le)
  -- measurability
  have hcf (i : Fin 3) := (hf i).continuous
  have hcDf (i j : Fin 3) : Continuous (fun y => fderiv ℝ (f i) y (e j)) :=
    ((hf i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcDk (i j : Fin 3) : Continuous (fun y => fderiv ℝ (k i j) y (e j)) :=
    ((hk i j).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcDs (i j : Fin 3) : Continuous (fun y => fderiv ℝ (s i j) y (e j)) :=
    ((hs i j).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint1 (i j : Fin 3) : Integrable (fun y => f i y * fderiv ℝ (k i j) y (e j)) :=
    integrable_mul_of_decay (hcf i).aestronglyMeasurable (hcDk i j).aestronglyMeasurable
      hA hA (hfb i) (hDkb i j)
  have hint2 (i j : Fin 3) : Integrable (fun y => f i y * fderiv ℝ (s i j) y (e j)) :=
    integrable_mul_of_decay (hcf i).aestronglyMeasurable (hcDs i j).aestronglyMeasurable
      hA hA (hfb i) (hDsb i j)
  have hint3 (i j : Fin 3) : Integrable (fun y => fderiv ℝ (f i) y (e j) * k i j y) :=
    integrable_mul_of_decay (hcDf i j).aestronglyMeasurable
      (hk i j).continuous.aestronglyMeasurable hA hA (hDfb i j) (hkb i j)
  have hint4 (i j : Fin 3) : Integrable (fun y => fderiv ℝ (f i) y (e j) * s i j y) :=
    integrable_mul_of_decay (hcDf i j).aestronglyMeasurable
      (hs i j).continuous.aestronglyMeasurable hA hA (hDfb i j) (hsb i j)
  have hkey (i j : Fin 3) :
      ∫ y, (f i y * fderiv ℝ (k i j) y (e j) + f i y * fderiv ℝ (s i j) y (e j)) =
        -∫ y, fderiv ℝ (f i) y (e j) * (k i j y + s i j y) := by
    rw [integral_add (hint1 i j) (hint2 i j),
      integral_mul_fderiv_of_decay (hf i) (hk i j) hA (e j) (hfb i) (hDfb i j) (hkb i j)
        (hDkb i j),
      integral_mul_fderiv_of_decay (hf i) (hs i j) hA (e j) (hfb i) (hDfb i j) (hsb i j)
        (hDsb i j), ← neg_add, ← integral_add (hint3 i j) (hint4 i j)]
    congr 2
    funext y
    ring
  -- rewrite both integrands
  have hleft : (fun x : Vec3 => ∑ i : Fin 3, T (responseVec g (x, t)) i *
      fderiv ℝ (causalHeatConv (vecTimeDiv g i)) (x, t) (0, 1)) =
      fun x => ∑ i : Fin 3, ∑ j : Fin 3,
        (f i x * fderiv ℝ (k i j) x (e j) + f i x * fderiv ℝ (s i j) x (e j)) := by
    funext x
    apply Finset.sum_congr rfl
    intro i _
    have hheat := causalHeatConv_heat_equation (vecTimeDiv_contDiff hg i)
      (vecTimeDiv_hasCompactSupport hgc i) (x, t)
    have htime : fderiv ℝ (causalHeatConv (vecTimeDiv g i)) (x, t) (0, 1) =
        ∑ j : Fin 3, (fderiv ℝ (k i j) x (e j) + fderiv ℝ (s i j) x (e j)) := by
      rw [Finset.sum_add_distrib]
      simp only [hDk, hDs]
      simp only [vecTimeDiv] at hheat
      linarith only [hheat]
    rw [htime, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hfx : f i x = T (responseVec g (x, t)) i := rfl
    rw [hfx]
    ring
  have hright : (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ T (responseVec g (x, t)) (responseGrad g j (x, t)) i *
        (responseGrad g j (x, t) i + g i j (x, t))) =
      fun x => ∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ (f i) x (e j) * (k i j x + s i j x) := by
    funext x
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hDf]
    rfl
  rw [hleft, hright]
  have hint12 (i j : Fin 3) : Integrable (fun x =>
      f i x * fderiv ℝ (k i j) x (e j) + f i x * fderiv ℝ (s i j) x (e j)) :=
    (hint1 i j).add (hint2 i j)
  have hsumint (i : Fin 3) : Integrable (fun x => ∑ j : Fin 3,
      (f i x * fderiv ℝ (k i j) x (e j) + f i x * fderiv ℝ (s i j) x (e j))) :=
    integrable_finsetSum _ fun j _ => hint12 i j
  have hint34 (i j : Fin 3) : Integrable (fun x =>
      fderiv ℝ (f i) x (e j) * (k i j x + s i j x)) := by
    simp only [mul_add]
    exact (hint3 i j).add (hint4 i j)
  have hsumint' (i : Fin 3) : Integrable (fun x => ∑ j : Fin 3,
      fderiv ℝ (f i) x (e j) * (k i j x + s i j x)) :=
    integrable_finsetSum _ fun j _ => hint34 i j
  rw [integral_finsetSum _ fun i _ => hsumint i, integral_finsetSum _ fun i _ => hsumint' i,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ fun j _ => hint12 i j,
    integral_finsetSum _ fun j _ => hint34 i j,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => hkey i j

/-- The divergence of a tensor supported in positive times vanishes at
nonpositive times. -/
theorem vecTimeDiv_eq_zero_of_nonpos {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hgpos : ∀ i j, tsupport (g i j) ⊆ {p | 0 < p.2}) (i : Fin 3) (p : Vec3 × ℝ)
    (hp : vecTimeDiv g i p ≠ 0) : 0 < p.2 := by
  by_contra hneg
  apply hp
  apply Finset.sum_eq_zero
  intro j _
  have hnot : p ∉ tsupport (g i j) := fun hmem => hneg (hgpos i j hmem)
  have hzero : fderiv ℝ (g i j) p = 0 := by
    by_contra hne
    exact hnot (support_fderiv_subset (𝕜 := ℝ) hne)
  rw [hzero]
  rfl

/-- Pointwise `(1 + |x|)^{-6}` bounds for the entropy production and the
dissipation integrand of the forced heat response. -/
theorem response_entropy_bounds {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j))
    {T : Vec3 → Vec3} (hT : ContDiff ℝ 1 T) (hT0 : T 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Vec3 × ℝ,
      |∑ i : Fin 3, T (responseVec g p) i *
        fderiv ℝ (causalHeatConv (vecTimeDiv g i)) p (0, 1)| ≤
          C / (1 + vec3EuclideanNorm p.1) ^ 6 ∧
      |∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ T (responseVec g p) (responseGrad g j p) i *
        (responseGrad g j p i + g i j p)| ≤ C / (1 + vec3EuclideanNorm p.1) ^ 6 := by
  obtain ⟨M, hM, hdec⟩ := vecTimeDiv_response_decay hg hgc
  obtain ⟨L, hL, hLb⟩ := exists_linear_bound_of_contDiff hT hT0 M
  refine ⟨9 * (L * M) * (2 * M), by positivity, fun p => ?_⟩
  let w : ℝ := (1 + vec3EuclideanNorm p.1) ^ 3
  have hw : 1 ≤ w := one_le_pow₀ (by
    have := vec3EuclideanNorm_nonneg p.1
    linarith only [this])
  have hwpos : 0 < w := lt_of_lt_of_le zero_lt_one hw
  have hw6 : (1 + vec3EuclideanNorm p.1) ^ 6 = w * w := by
    simp only [w]
    ring
  have hZnorm : ‖responseVec g p‖ ≤ M / w :=
    (pi_norm_le_iff_of_nonneg (div_nonneg hM hwpos.le)).2 fun k => by
      rw [Real.norm_eq_abs]
      exact (hdec k k k p).1
  have hZle : ‖responseVec g p‖ ≤ M := hZnorm.trans (div_le_self hM hw)
  have hGnorm (j : Fin 3) : ‖responseGrad g j p‖ ≤ M / w :=
    (pi_norm_le_iff_of_nonneg (div_nonneg hM hwpos.le)).2 fun k => by
      rw [Real.norm_eq_abs]
      exact (hdec k j j p).2.1
  have hT1 (i : Fin 3) : |T (responseVec g p) i| ≤ L * M / w := by
    rw [← Real.norm_eq_abs, mul_div_assoc]
    exact (norm_le_pi_norm _ i).trans ((hLb _ hZle).1.trans
      (mul_le_mul_of_nonneg_left hZnorm hL))
  have hDT (i j : Fin 3) :
      |fderiv ℝ T (responseVec g p) (responseGrad g j p) i| ≤ L * M / w := by
    rw [← Real.norm_eq_abs, mul_div_assoc]
    exact (norm_le_pi_norm _ i).trans ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hLb _ hZle).2 (hGnorm j) (norm_nonneg _) hL))
  have hsum (i j : Fin 3) : |responseGrad g j p i + g i j p| ≤ 2 * M / w := by
    have h1 := (hdec i j j p).2.1
    have h2 := (hdec i j j p).2.2.2.2.1
    calc
      |responseGrad g j p i + g i j p| ≤ |responseGrad g j p i| + |g i j p| := abs_add_le _ _
      _ ≤ M / w + M / w := add_le_add h1 h2
      _ = 2 * M / w := by ring
  have hprod {a b A B : ℝ} (ha : |a| ≤ A / w) (hb : |b| ≤ B / w) (hA : 0 ≤ A) :
      |a * b| ≤ A * B / (w * w) := by
    rw [abs_mul, ← div_mul_div_comm]
    exact mul_le_mul ha hb (abs_nonneg _) (div_nonneg hA hwpos.le)
  have hMw : (M / w) ≤ 2 * M / w := div_le_div_of_nonneg_right (by linarith only [hM]) hwpos.le
  constructor
  · rw [hw6]
    calc
      _ ≤ ∑ i : Fin 3, |T (responseVec g p) i *
          fderiv ℝ (causalHeatConv (vecTimeDiv g i)) p (0, 1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, (L * M) * (2 * M) / (w * w) := by
        apply Finset.sum_le_sum
        intro i _
        exact hprod (hT1 i) (((hdec i i i p).2.2.2.1).trans hMw) (by positivity)
      _ ≤ 9 * (L * M) * (2 * M) / (w * w) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hX : 0 ≤ L * M * (2 * M) / (w * w) := by positivity
        rw [show (9 : ℝ) * (L * M) * (2 * M) / (w * w) = 9 * (L * M * (2 * M) / (w * w)) by
          ring]
        push_cast
        linarith only [hX]
  · rw [hw6]
    calc
      _ ≤ ∑ i : Fin 3, |∑ j : Fin 3, fderiv ℝ T (responseVec g p) (responseGrad g j p) i *
          (responseGrad g j p i + g i j p)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, (L * M) * (2 * M) / (w * w) := by
        apply Finset.sum_le_sum
        intro i _
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        apply Finset.sum_le_sum
        intro j _
        exact hprod (hDT i j) (hsum i j) (by positivity)
      _ = 9 * (L * M) * (2 * M) / (w * w) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- The whole-space entropy identity for the forced heat response: for a
convex entropy `Φ` with gradient `T` and every `t₁ ≥ 0`,
`∫ Φ(Z(t₁)) = -∫_{Vec3 × (0,t₁]} ∑_{i,j} ∂_j[T_i(Z)] (∂_j Z_i + g_ij)`. -/
theorem response_entropy_identity {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j))
    (hgpos : ∀ i j, tsupport (g i j) ⊆ {p | 0 < p.2})
    {Φ : Vec3 → ℝ} {T : Vec3 → Vec3} (hΦ : ContDiff ℝ 1 Φ) (hT : ContDiff ℝ 1 T)
    (hΦT : ∀ v w : Vec3, fderiv ℝ Φ v w = ∑ i : Fin 3, T v i * w i) (hΦ0 : Φ 0 = 0)
    (hT0 : T 0 = 0) {t₁ : ℝ} (ht₁ : 0 ≤ t₁) :
    ∫ x, Φ (responseVec g (x, t₁)) =
      -∫ p, ∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ T (responseVec g p) (responseGrad g j p) i *
          (responseGrad g j p i + g i j p)
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 t₁))) := by
  let U : Fin 3 → Vec3 × ℝ → ℝ := fun i => causalHeatConv (vecTimeDiv g i)
  have hU (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (U i) :=
    causalHeatConv_contDiff (vecTimeDiv_contDiff hg i) (vecTimeDiv_hasCompactSupport hgc i)
  have hU0 (i : Fin 3) (x : Vec3) : U i (x, 0) = 0 :=
    causalHeatConv_eq_zero_of_nonpos (vecTimeDiv_eq_zero_of_nonpos hgpos i) le_rfl
  obtain ⟨C, hC, hb⟩ := response_entropy_bounds hg hgc hT hT0
  have hwin := entropy_integral_eq_window_integral hΦ hT.continuous hΦT hΦ0
    (U := U) (fun i => (hU i).of_le (by simp)) hU0 ht₁ hC (fun x t _ => (hb (x, t)).1)
  change ∫ x, Φ (fun i => U i (x, t₁)) = _
  rw [hwin]
  have hslice (t : ℝ) : ∫ x, ∑ i : Fin 3, T (fun k => U k (x, t)) i *
      fderiv ℝ (U i) (x, t) (0, 1) = -∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ T (responseVec g (x, t)) (responseGrad g j (x, t)) i *
          (responseGrad g j (x, t) i + g i j (x, t)) :=
    response_production_identity hg hgc hT hT0 t
  simp_rw [hslice]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_of_le ht₁]
  congr 1
  have hcont : Continuous (fun p : Vec3 × ℝ => ∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ T (responseVec g p) (responseGrad g j p) i *
        (responseGrad g j p i + g i j p)) := by
    have hZ : Continuous (responseVec g) := continuous_pi fun k => (hU k).continuous
    have hGr (j : Fin 3) : Continuous (responseGrad g j) := continuous_pi fun k =>
      ((hU k).continuous_fderiv (by simp)).clm_apply continuous_const
    have hDT : Continuous (fun v => fderiv ℝ T v) := hT.continuous_fderiv one_ne_zero
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact ((continuous_apply i).comp ((hDT.comp hZ).clm_apply (hGr j))).mul
      (((continuous_apply i).comp (hGr j)).add (hg i j).continuous)
  have hint := integrable_window_of_decay (a := 0) (b := t₁) hcont hC
    (fun x t _ => (hb (x, t)).2)
  exact (integral_prod_symm _ hint).symm

end ESS

end
