/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Convex.SupportFunction
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.FundamentalDomain
import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.Mollify
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.Measurable

/-!
# A gradient constraint `p + Dξ ∈ K` on Lipschitz `ℤ^m`-periodic functions

For `ξ : ℝ^m → ℝ` Lipschitz and `ℤ^m`-periodic, `p ∈ ℝ^m` and `K ⊂ ℝ^m` compact, the constraint
"`p + Dξ ∈ K` almost everywhere on the unit cube `(0, 1)^m`" is equivalent to the slope bound
`ξ (y) − ξ (x) + p · (y − x) ≤ H_K (y − x)` for all `x, y` (`H_K = supportFun K`), when `K` is also
convex and nonempty. These facts are standard.

* `sub_add_dotProduct_le_supportFun_of_ae_mem`: the constraint implies the slope bound. The
  constraint holds almost everywhere on `ℝ^m` by periodicity
  (`ae_of_ae_restrict_unitCube_of_periodic`); the mollifications `ρ_n ⋆ ξ` are smooth with
  `D (ρ_n ⋆ ξ) v = ρ_n ⋆ ∂_v ξ ≤ H_K (v) − p · v` (`plancherelMollify_fderiv`), hence satisfy the
  slope bound by the mean value theorem, and converge to `ξ` pointwise.
* `add_fderiv_mem_of_sub_add_dotProduct_le_supportFun`: for `K` also convex and nonempty, the
  slope bound implies `p + Dξ (x) ∈ K` at every point of differentiability
  (`mem_of_forall_dotProduct_le_supportFun`).
* `exists_lipschitzWith_of_sub_add_dotProduct_le_supportFun`: the slope bound implies a Lipschitz
  bound that depends only on `K` and `p`.
* `exists_tendsto_of_ae_restrict_unitCube_tendsto`: an equi-Lipschitz sequence of `ℤ^m`-periodic
  functions that converges almost everywhere on the unit cube converges everywhere.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace CalculusOfVariations

variable {m : ℕ}

/-- The derivative of a `ℤ^m`-periodic function is `ℤ^m`-periodic. -/
private theorem gc_fderiv_periodic {ξ : (Fin m → ℝ) → ℝ}
    (hper : ∀ x (k : Fin m → ℤ), ξ (x + fun i => (k i : ℝ)) = ξ x) (x : Fin m → ℝ)
    (k : Fin m → ℤ) : fderiv ℝ ξ (x + fun i => (k i : ℝ)) = fderiv ℝ ξ x := by
  rw [← fderiv_comp_add_right]
  congr 1
  funext y
  exact hper y k

/-- If `p + Dξ ∈ K` almost everywhere on `ℝ^m`, then `D (ρ ⋆ ξ) (x) v ≤ H_K (v) − p · v`. -/
private theorem gc_fderiv_mollify_le {K : Set (Fin m → ℝ)} (hKc : IsCompact K) {p : Fin m → ℝ}
    {ξ : (Fin m → ℝ) → ℝ} {C : NNReal} (hξ : LipschitzWith C ξ)
    (hall : ∀ᵐ z, DifferentiableAt ℝ ξ z ∧ p + (fun j => fderiv ℝ ξ z (Pi.single j 1)) ∈ K)
    (ρ : ContDiffBump (0 : Fin m → ℝ)) (x v : Fin m → ℝ) :
    fderiv ℝ (plancherelMollify volume ρ ξ) x v ≤ supportFun K v - p ⬝ᵥ v := by
  have hline : ∀ᵐ z, lineDeriv ℝ ξ z v ≤ supportFun K v - p ⬝ᵥ v := by
    filter_upwards [hall] with z ⟨hd, hz⟩
    rw [hd.lineDeriv_eq_fderiv, continuousLinearMap_apply_eq_dotProduct]
    have := dotProduct_le_supportFun hKc hz v
    rw [add_dotProduct] at this
    linarith
  have hline' : ∀ᵐ t, lineDeriv ℝ ξ (x - t) v ≤ supportFun K v - p ⬝ᵥ v :=
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae hline
  rw [plancherelMollify_fderiv ρ hξ, plancherelMollify, convolution_lsmul]
  have hρi : Integrable (ρ.normed volume) volume :=
    ρ.continuous_normed.integrable_of_hasCompactSupport ρ.hasCompactSupport_normed
  have hi : Integrable (fun t => ρ.normed volume t • lineDeriv ℝ ξ (x - t) v) volume := by
    have := hρi.bdd_mul (f := fun t => lineDeriv ℝ ξ (x - t) v) (c := C * ‖v‖)
      ((measurable_lineDeriv (𝕜 := ℝ) (v := v) hξ.continuous).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun t => norm_lineDeriv_le_of_lipschitz ℝ hξ)
    simpa [smul_eq_mul, mul_comm] using this
  calc ∫ t, ρ.normed volume t • lineDeriv ℝ ξ (x - t) v
      ≤ ∫ t, ρ.normed volume t * (supportFun K v - p ⬝ᵥ v) :=
        integral_mono_ae hi (hρi.mul_const _) (hline'.mono fun t ht =>
          mul_le_mul_of_nonneg_left ht (ρ.nonneg_normed t))
    _ = supportFun K v - p ⬝ᵥ v := by rw [integral_mul_const, ρ.integral_normed, one_mul]

/-- The mean value theorem along the segment `[x, y]`: if `D f (z) v ≤ G (v)` for all `z, v`, then
`f (y) − f (x) ≤ G (y − x)`. -/
private theorem gc_sub_le_of_fderiv_le {f : (Fin m → ℝ) → ℝ} (hf : Differentiable ℝ f)
    {G : (Fin m → ℝ) → ℝ} (h : ∀ z v, fderiv ℝ f z v ≤ G v) (x y : Fin m → ℝ) :
    f y - f x ≤ G (y - x) := by
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (x + t • (y - x)))
      (fderiv ℝ f (x + t • (y - x)) (y - x)) t := by
    intro t
    have := (hf (x + t • (y - x))).hasFDerivAt.comp_hasDerivAt_of_eq (x := t)
      (((hasDerivAt_id t).smul_const (y - x)).const_add x) (by simp)
    simpa [Function.comp_def] using this
  have := image_sub_le_mul_sub_of_deriv_le (f := fun t : ℝ => f (x + t • (y - x)))
    (fun t => (hg t).differentiableAt) (C := G (y - x))
    (fun t => by rw [(hg t).deriv]; exact h _ _) zero_le_one
  simpa using this

/-- **The slope bound.** For `ξ` Lipschitz and `ℤ^m`-periodic with `p + Dξ ∈ K` almost everywhere
on `(0, 1)^m`, `K` compact: `ξ (y) − ξ (x) + p · (y − x) ≤ H_K (y − x)` for all `x, y`. -/
theorem sub_add_dotProduct_le_supportFun_of_ae_mem {K : Set (Fin m → ℝ)} (hKc : IsCompact K)
    {p : Fin m → ℝ} {ξ : (Fin m → ℝ) → ℝ} {C : NNReal} (hξ : LipschitzWith C ξ)
    (hper : ∀ x (k : Fin m → ℤ), ξ (x + fun i => (k i : ℝ)) = ξ x)
    (hK : ∀ᵐ x ∂(volume.restrict (Set.pi Set.univ fun _ : Fin m => Set.Ioo (0 : ℝ) 1)),
      p + (fun j => fderiv ℝ ξ x (Pi.single j 1)) ∈ K) (x y : Fin m → ℝ) :
    ξ y - ξ x + p ⬝ᵥ (y - x) ≤ supportFun K (y - x) := by
  have hK' : ∀ᵐ z, p + (fun j => fderiv ℝ ξ z (Pi.single j 1)) ∈ K :=
    ae_of_ae_restrict_unitCube_of_periodic (fun z k hz => by rwa [gc_fderiv_periodic hper] at hz) hK
  have hall := hξ.ae_differentiableAt.and hK'
  have hn : ∀ n : ℕ,
      plancherelMollify volume (plancherelBump m n) ξ y -
        plancherelMollify volume (plancherelBump m n) ξ x
        ≤ supportFun K (y - x) - p ⬝ᵥ (y - x) := fun n =>
    gc_sub_le_of_fderiv_le
      ((plancherelMollify_contDiff _ hξ.continuous).differentiable (by simp))
      (fun z v => gc_fderiv_mollify_le hKc hξ hall _ z v) x y
  have hlim : ∀ z, Tendsto (fun n : ℕ => plancherelMollify volume (plancherelBump m n) ξ z) atTop
      (𝓝 (ξ z)) := fun z =>
    ContDiffBump.convolution_tendsto_right_of_continuous (plancherelBump_tendsto m)
      hξ.continuous z
  have := le_of_tendsto' ((hlim y).sub (hlim x)) hn
  linarith

/-- **The converse.** For `K` compact, convex and nonempty, if `ξ` satisfies the slope bound
`ξ (y) − ξ (x) + p · (y − x) ≤ H_K (y − x)`, then `p + Dξ (x) ∈ K` wherever `ξ` is differentiable:
`Dξ (x) v = lim_{t → 0⁺} (ξ (x + t v) − ξ (x)) / t ≤ H_K (v) − p · v`. -/
theorem add_fderiv_mem_of_sub_add_dotProduct_le_supportFun {K : Set (Fin m → ℝ)}
    (hKc : IsCompact K) (hKne : K.Nonempty) (hKcv : Convex ℝ K) {p : Fin m → ℝ}
    {ξ : (Fin m → ℝ) → ℝ}
    (h : ∀ x y, ξ y - ξ x + p ⬝ᵥ (y - x) ≤ supportFun K (y - x)) {x : Fin m → ℝ}
    (hx : DifferentiableAt ℝ ξ x) : p + (fun j => fderiv ℝ ξ x (Pi.single j 1)) ∈ K := by
  apply mem_of_forall_dotProduct_le_supportFun hKc hKne hKcv
  intro v
  rw [add_dotProduct, ← continuousLinearMap_apply_eq_dotProduct]
  have hd : HasDerivAt (fun t : ℝ => ξ (x + t • v)) (fderiv ℝ ξ x v) 0 := by
    have := hx.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ))
      (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x) (by simp)
    simpa [Function.comp_def] using this
  have : fderiv ℝ ξ x v ≤ supportFun K v - p ⬝ᵥ v := by
    refine le_of_tendsto hd.tendsto_slope_zero_right ?_
    filter_upwards [self_mem_nhdsWithin] with t (htpos : 0 < t)
    simp only [zero_smul, add_zero, smul_eq_mul, zero_add]
    rw [inv_mul_le_iff₀ htpos]
    have := h x (x + t • v)
    rw [add_sub_cancel_left, supportFun_smul hKc hKne htpos.le, dotProduct_smul,
      smul_eq_mul] at this
    linarith
  linarith

/-- The slope bound implies a Lipschitz bound `L` that depends only on `K` and `p` (`K` compact and
nonempty). -/
theorem exists_lipschitzWith_of_sub_add_dotProduct_le_supportFun {K : Set (Fin m → ℝ)}
    (hKc : IsCompact K) (hKne : K.Nonempty) (p : Fin m → ℝ) :
    ∃ L : NNReal, ∀ ξ : (Fin m → ℝ) → ℝ,
      (∀ x y, ξ y - ξ x + p ⬝ᵥ (y - x) ≤ supportFun K (y - x)) → LipschitzWith L ξ := by
  obtain ⟨C, hC⟩ := lipschitzWith_supportFun hKc hKne
  refine ⟨C + Real.toNNReal (m * ‖p‖), fun ξ h => LipschitzWith.of_le_add_mul _ fun y x => ?_⟩
  have h1 := h x y
  have h2 : supportFun K (y - x) ≤ C * dist y x := by
    have := hC.dist_le_mul (y - x) 0
    rw [supportFun_zero hKc hKne, Real.dist_eq, sub_zero, dist_zero_right, ← dist_eq_norm] at this
    exact (le_abs_self _).trans this
  have h3 : -(p ⬝ᵥ (y - x)) ≤ m * ‖p‖ * dist y x := by
    have := dotProduct_le_mul_norm_mul_norm (-p) (y - x)
    rw [neg_dotProduct, norm_neg, ← dist_eq_norm] at this
    linarith
  have h4 : (m * ‖p‖ : ℝ) * dist y x ≤ Real.toNNReal (m * ‖p‖) * dist y x :=
    mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) dist_nonneg
  push_cast
  linarith

/-- An equi-Lipschitz sequence of `ℤ^m`-periodic functions that converges almost everywhere on the
unit cube converges everywhere: the points of convergence are dense in `ℝ^m` (by periodicity they
have full measure), and the equicontinuity makes the sequence Cauchy at every point. -/
theorem exists_tendsto_of_ae_restrict_unitCube_tendsto {F : ℕ → (Fin m → ℝ) → ℝ} {L : NNReal}
    (hF : ∀ k, LipschitzWith L (F k))
    (hper : ∀ k x (z : Fin m → ℤ), F k (x + fun i => (z i : ℝ)) = F k x)
    {u : (Fin m → ℝ) → ℝ}
    (h : ∀ᵐ x ∂(volume.restrict (Set.pi Set.univ fun _ : Fin m => Set.Ioo (0 : ℝ) 1)),
      Tendsto (fun k => F k x) atTop (𝓝 (u x))) :
    ∃ ξ : (Fin m → ℝ) → ℝ, ∀ x, Tendsto (fun k => F k x) atTop (𝓝 (ξ x)) := by
  have hall : ∀ᵐ x, CauchySeq fun k => F k x :=
    ae_of_ae_restrict_unitCube_of_periodic (P := fun x => CauchySeq fun k => F k x)
      (fun x z hx => by simpa only [hper] using hx) (h.mono fun x hx => hx.cauchySeq)
  have hdense := Measure.dense_of_ae hall
  have hcs : ∀ x, CauchySeq fun k => F k x := by
    intro x
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hδ : 0 < ε / (3 * (L + 1)) := by positivity
    obtain ⟨y, hxy, hy⟩ := Metric.dense_iff.1 hdense x _ hδ
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hy (ε / 3) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have hd : dist x y < ε / (3 * (L + 1)) := by rw [dist_comm]; exact hxy
    have e1 : dist (F n x) (F n y) ≤ L * dist x y := (hF n).dist_le_mul x y
    have e2 : dist (F N y) (F N x) ≤ L * dist x y := by
      rw [dist_comm x y]; exact (hF N).dist_le_mul y x
    have e3 := hN n hn
    have hL : (L : ℝ) * dist x y ≤ ε / 3 := by
      calc (L : ℝ) * dist x y ≤ (L + 1) * (ε / (3 * (L + 1))) :=
            mul_le_mul (by linarith) hd.le dist_nonneg (by positivity)
        _ = ε / 3 := by field_simp
    calc dist (F n x) (F N x)
        ≤ dist (F n x) (F n y) + dist (F n y) (F N y) + dist (F N y) (F N x) :=
          dist_triangle4 _ _ _ _
      _ < ε := by linarith
  exact ⟨fun x => limUnder atTop fun k => F k x, fun x => (hcs x).tendsto_limUnder⟩

end CalculusOfVariations
