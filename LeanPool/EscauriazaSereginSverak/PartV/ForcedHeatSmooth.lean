/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatKernel
public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatDecay

/-!
# Smooth-data calculus for the forced heat response

For a smooth compactly supported tensor source supported in positive times,
the forced heat response and its first and second spatial derivatives and its
time derivative decay like `|x|^{-3}` uniformly in time; the response solves
the heat equation with divergence source and vanishes at time zero. These are
the facts used by the energy estimates of `lem:pv-stokes`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A continuous compactly supported space-time function is bounded by a
multiple of `(1 + |x|)^{-3}`. -/
theorem abs_le_decay_of_hasCompactSupport {f : Vec3 × ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q : Vec3 × ℝ, |f q| ≤ M / (1 + vec3EuclideanNorm q.1) ^ 3 := by
  obtain ⟨R, hRone, hRball⟩ :=
    hfc.isCompact.isBounded.subset_closedBall_lt 1 (0 : Vec3 × ℝ)
  have hBdd : BddAbove (Set.range (fun p : Vec3 × ℝ => ‖f p‖)) :=
    hf.norm.bddAbove_range_of_hasCompactSupport hfc.norm
  let B : ℝ := ⨆ p : Vec3 × ℝ, ‖f p‖
  have hB (p : Vec3 × ℝ) : ‖f p‖ ≤ B := le_ciSup hBdd p
  have hBnonneg : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨B * (1 + 2 * R) ^ 3, by positivity, ?_⟩
  intro q
  have hden : 0 < (1 + vec3EuclideanNorm q.1) ^ 3 := by
    have := vec3EuclideanNorm_nonneg q.1
    positivity
  rw [le_div_iff₀ hden]
  by_cases hq : f q = 0
  · rw [hq, abs_zero, zero_mul]
    positivity
  · have hmem := hRball (subset_tsupport f hq)
    have hnorm : ‖q‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hmem
    have hspace : ‖q.1‖ ≤ R := (norm_fst_le q).trans hnorm
    have heucl : vec3EuclideanNorm q.1 ≤ 2 * R := by
      calc
        vec3EuclideanNorm q.1 ≤ Real.sqrt 3 * ‖q.1‖ :=
          vec3EuclideanNorm_le_sqrt_three_mul_norm _
        _ ≤ 2 * R := by
          have hsqrt : Real.sqrt 3 ≤ 2 := by
            nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
              Real.sqrt_nonneg 3]
          exact mul_le_mul hsqrt hspace (norm_nonneg _) (by norm_num)
    have hpow : (1 + vec3EuclideanNorm q.1) ^ 3 ≤ (1 + 2 * R) ^ 3 :=
      pow_le_pow_left₀ (by have := vec3EuclideanNorm_nonneg q.1; positivity)
        (by linarith only [heucl]) 3
    rw [← Real.norm_eq_abs]
    exact mul_le_mul (hB q) hpow hden.le hBnonneg

/-- A finite family of functions with `(1 + |x|)^{-3}` decay has a common
decay constant. -/
theorem exists_common_decay_constant {ι : Type*} [Finite ι] (f : ι → Vec3 × ℝ → ℝ)
    (hf : ∀ a, ∃ M : ℝ, 0 ≤ M ∧ ∀ q : Vec3 × ℝ,
      |f a q| ≤ M / (1 + vec3EuclideanNorm q.1) ^ 3) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a q, |f a q| ≤ M / (1 + vec3EuclideanNorm q.1) ^ 3 := by
  let _ := Fintype.ofFinite ι
  choose M hM hbound using hf
  refine ⟨∑ a, M a, Finset.sum_nonneg fun a _ => hM a, ?_⟩
  intro a q
  have hden : 0 ≤ (1 + vec3EuclideanNorm q.1) ^ 3 := by
    have := vec3EuclideanNorm_nonneg q.1
    positivity
  exact (hbound a q).trans (div_le_div_of_nonneg_right
    (Finset.single_le_sum (fun b _ => hM b) (Finset.mem_univ a)) hden)

/-- The divergence `∑_j ∂_j g_ij` of a space-time tensor on `Vec3 × ℝ`, with
spatial derivatives written as directional derivatives. -/
@[expose] def vecTimeDiv (g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (i : Fin 3) (q : Vec3 × ℝ) : ℝ :=
  ∑ j : Fin 3, fderiv ℝ (g i j) q (CKN.basisVec j, 0)

/-- For a smooth compactly supported tensor, the forced heat response is the
causal heat potential of `vecTimeDiv`. -/
theorem forcedHeat_eq_causalHeatConv_vecTimeDiv {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => G i j p))
    (hGc : ∀ i j, HasCompactSupport (fun p : Vec3 × ℝ => G i j p))
    (i : Fin 3) (z : ParabolicPoint) :
    forcedHeat G z i =
      causalHeatConv (vecTimeDiv (fun i j (p : Vec3 × ℝ) => G i j p) i) z := by
  have hfun := congrFun (forcedHeat_eq_causalHeatConv hG hGc i) z
  refine hfun.trans ?_
  congr 1
  funext q
  exact Finset.sum_congr rfl fun j _ => spatialPartial_eq_fderiv_apply (hG i j) j q.1 q.2

/-- The divergence of a smooth tensor is smooth. -/
theorem vecTimeDiv_contDiff {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (vecTimeDiv g i) :=
  ContDiff.sum fun j _ => contDiff_fderiv_apply_const (hg i j) _

/-- The divergence of a compactly supported smooth tensor has compact support. -/
theorem vecTimeDiv_hasCompactSupport {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hgc : ∀ i j, HasCompactSupport (g i j)) (i : Fin 3) :
    HasCompactSupport (vecTimeDiv g i) := by
  have hsum := HasCompactSupport.finset_sum (s := Finset.univ)
    (f := fun j (q : Vec3 × ℝ) => fderiv ℝ (g i j) q (CKN.basisVec j, 0))
    (fun j _ => (hgc i j).fderiv_apply (𝕜 := ℝ) _)
  convert hsum using 1
  funext q
  simp only [vecTimeDiv, Finset.sum_apply]

/-- The response `causalHeatConv (vecTimeDiv g i)`, its first and second
spatial derivatives, its time derivative, and the tensor with its spatial
derivatives all decay like `(1 + |x|)^{-3}` with a common constant. -/
theorem vecTimeDiv_response_decay {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (i j k : Fin 3) (q : Vec3 × ℝ),
      |causalHeatConv (vecTimeDiv g i) q| ≤ M / (1 + vec3EuclideanNorm q.1) ^ 3 ∧
      |fderiv ℝ (causalHeatConv (vecTimeDiv g i)) q (CKN.basisVec j, 0)| ≤
        M / (1 + vec3EuclideanNorm q.1) ^ 3 ∧
      |fderiv ℝ (fun p => fderiv ℝ (causalHeatConv (vecTimeDiv g i)) p
        (CKN.basisVec j, 0)) q (CKN.basisVec k, 0)| ≤
        M / (1 + vec3EuclideanNorm q.1) ^ 3 ∧
      |fderiv ℝ (causalHeatConv (vecTimeDiv g i)) q (0, 1)| ≤
        M / (1 + vec3EuclideanNorm q.1) ^ 3 ∧
      |g i j q| ≤ M / (1 + vec3EuclideanNorm q.1) ^ 3 ∧
      |fderiv ℝ (g i j) q (CKN.basisVec k, 0)| ≤ M / (1 + vec3EuclideanNorm q.1) ^ 3 := by
  let h : Fin 3 → Vec3 × ℝ → ℝ := vecTimeDiv g
  have hh (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (h i) := vecTimeDiv_contDiff hg i
  have hhc (i : Fin 3) : HasCompactSupport (h i) := vecTimeDiv_hasCompactSupport hgc i
  have hD (i : Fin 3) (w : Vec3 × ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun q => fderiv ℝ (h i) q w) :=
    contDiff_fderiv_apply_const (hh i) w
  have hDc (i : Fin 3) (w : Vec3 × ℝ) : HasCompactSupport (fun q => fderiv ℝ (h i) q w) :=
    (hhc i).fderiv_apply (𝕜 := ℝ) w
  have hdec (f : Vec3 × ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
      (F : Vec3 × ℝ → ℝ) (hF : ∀ q, F q = causalHeatConv f q) :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ q : Vec3 × ℝ, |F q| ≤ M / (1 + vec3EuclideanNorm q.1) ^ 3 := by
    obtain ⟨M, hM, hb⟩ := causalHeatConv_abs_le_decay hf.continuous hfc
    exact ⟨M, hM, fun q => (hF q).symm ▸ hb q⟩
  have hfirst (i : Fin 3) (w : Vec3 × ℝ) :
      (fun p => fderiv ℝ (causalHeatConv (h i)) p w) =
        causalHeatConv (fun q => fderiv ℝ (h i) q w) := by
    funext p
    exact causalHeatConv_fderiv_apply (hh i) (hhc i) p w
  obtain ⟨M₁, hM₁, h₁⟩ := exists_common_decay_constant
    (fun (a : Fin 3) q => causalHeatConv (h a) q) fun a =>
      hdec _ (hh a) (hhc a) _ fun q => rfl
  obtain ⟨M₂, hM₂, h₂⟩ := exists_common_decay_constant
    (fun (a : Fin 3 × Fin 3) q => fderiv ℝ (causalHeatConv (h a.1)) q
      (CKN.basisVec a.2, 0)) fun a =>
      hdec _ (hD a.1 _) (hDc a.1 _) _ fun q => congrFun (hfirst a.1 _) q
  obtain ⟨M₃, hM₃, h₃⟩ := exists_common_decay_constant
    (fun (a : Fin 3 × Fin 3 × Fin 3) q => fderiv ℝ (fun p =>
      fderiv ℝ (causalHeatConv (h a.1)) p (CKN.basisVec a.2.1, 0)) q
        (CKN.basisVec a.2.2, 0)) fun a => by
      refine hdec _ (contDiff_fderiv_apply_const (hD a.1 (CKN.basisVec a.2.1, 0))
        (CKN.basisVec a.2.2, 0))
        ((hDc a.1 (CKN.basisVec a.2.1, 0)).fderiv_apply (𝕜 := ℝ) (CKN.basisVec a.2.2, 0))
        _ fun q => ?_
      rw [hfirst]
      exact causalHeatConv_fderiv_apply (hD a.1 _) (hDc a.1 _) q _
  obtain ⟨M₄, hM₄, h₄⟩ := exists_common_decay_constant
    (fun (a : Fin 3) q => fderiv ℝ (causalHeatConv (h a)) q (0, 1)) fun a =>
      hdec _ (hD a _) (hDc a _) _ fun q => congrFun (hfirst a _) q
  obtain ⟨M₅, hM₅, h₅⟩ := exists_common_decay_constant
    (fun (a : Fin 3 × Fin 3) (q : Vec3 × ℝ) => g a.1 a.2 q) fun a =>
      abs_le_decay_of_hasCompactSupport (hg a.1 a.2).continuous (hgc a.1 a.2)
  obtain ⟨M₆, hM₆, h₆⟩ := exists_common_decay_constant
    (fun (a : Fin 3 × Fin 3 × Fin 3) (q : Vec3 × ℝ) =>
      fderiv ℝ (g a.1 a.2.1) q (CKN.basisVec a.2.2, 0)) fun a =>
      abs_le_decay_of_hasCompactSupport
        (contDiff_fderiv_apply_const (hg a.1 a.2.1) _).continuous
        ((hgc a.1 a.2.1).fderiv_apply (𝕜 := ℝ) _)
  refine ⟨M₁ + M₂ + M₃ + M₄ + M₅ + M₆, by positivity, ?_⟩
  intro i j k q
  have hden : 0 ≤ (1 + vec3EuclideanNorm q.1) ^ 3 := by
    have := vec3EuclideanNorm_nonneg q.1
    positivity
  have hmono {a b : ℝ} (hab : a ≤ b) (x : ℝ) (hx : |x| ≤ a / (1 + vec3EuclideanNorm q.1) ^ 3) :
      |x| ≤ b / (1 + vec3EuclideanNorm q.1) ^ 3 :=
    hx.trans (div_le_div_of_nonneg_right hab hden)
  refine ⟨hmono ?_ _ (h₁ i q), hmono ?_ _ (h₂ (i, j) q), hmono ?_ _ (h₃ (i, j, k) q),
    hmono ?_ _ (h₄ i q), hmono ?_ _ (h₅ (i, j) q), hmono ?_ _ (h₆ (i, j, k) q)⟩ <;>
    linarith only [hM₁, hM₂, hM₃, hM₄, hM₅, hM₆]

end ESS

end
