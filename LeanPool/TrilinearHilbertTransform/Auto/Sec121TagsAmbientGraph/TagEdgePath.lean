/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec121TagsAmbientGraph.Setup

/-!
# Trilinear Hilbert transform: tagEdge_path
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

open scoped Classical in
private def TagEdgePathHedgeBStatement : Prop :=
  ∀ (B : ℝ)
    (r : ℝ)
    (_ : (2 : ℝ) ≤ B)
    (L : ℕ)
    (dB : ℕ)
    (_ : (1 : ℕ) ≤ L)
    (v : Fin (L + (1 : ℕ)) → ChartTag)
    (_ : ∀ (i : Fin (L + (1 : ℕ))) (a b : Fin (v i).dim), (↑(rationalHeight ((v i).C a b)) :
      ℝ) ≤ B)
    (U : (j : Fin L) → Submodule ℝ (EuclideanSpace ℝ (Fin ((v j.castSucc).dim + (v
      j.succ).dim))))
    (Q : (j : Fin L) → Matrix (Fin ((v j.castSucc).dim + (v j.succ).dim)) (Fin ((v
      j.castSucc).dim + (v j.succ).dim)) ℚ)
    (_ : ∀ (j : Fin L), ∀ x ∈ U j, ∀ y ∈ U j, chartAltForm (tagDiffC (v j.castSucc) (v
      j.succ)) y.ofLp x.ofLp = (0 : ℝ))
    (_ : ∀ (j : Fin L), ‖((U j) ᗮ.starProjection : EuclideanSpace ℝ (Fin ((v j.castSucc).dim
      + (v j.succ).dim)) → EuclideanSpace ℝ (Fin ((v j.castSucc).dim + (v j.succ).dim)))
      (WithLp.toLp (2 : ℝ≥0∞) fun (i : Fin ((v j.castSucc).dim + (v j.succ).dim)) =>
      tagDiffV r (v j.castSucc) (v j.succ) i (0 : Fin (1 : ℕ)))‖ ≤ B)
    (_ : ∀ (j : Fin L), |(tagDiffΛ r (v j.castSucc) (v j.succ) (0 : Fin (1 : ℕ)) (0 : Fin (1
      : ℕ)) + (1 / 2 : ℝ) * chartMatrixPhase (tagDiffC (v j.castSucc) (v j.succ)) (fun
      (i : Fin ((v j.castSucc).dim + (v j.succ).dim)) => tagDiffV r (v j.castSucc) (v
      j.succ) i (0 : Fin (1 : ℕ))) fun (i : Fin ((v j.castSucc).dim + (v j.succ).dim))
      => tagDiffV r (v j.castSucc) (v j.succ) i (0 : Fin (1 : ℕ))) + (1 / 2 : ℝ) *
      chartAltForm (tagDiffC (v j.castSucc) (v j.succ)) (((U j).starProjection :
      EuclideanSpace ℝ (Fin ((v j.castSucc).dim + (v j.succ).dim)) → EuclideanSpace ℝ
      (Fin ((v j.castSucc).dim + (v j.succ).dim))) (WithLp.toLp (2 : ℝ≥0∞) fun (i : Fin
      ((v j.castSucc).dim + (v j.succ).dim)) => tagDiffV r (v j.castSucc) (v j.succ) i
      (0 : Fin (1 : ℕ)))).ofLp fun (i : Fin ((v j.castSucc).dim + (v j.succ).dim)) =>
      tagDiffV r (v j.castSucc) (v j.succ) i (0 : Fin (1 : ℕ))| ≤ B),
  let N : ℕ :=
    ∑ i : Fin (L + (1 : ℕ)), (v i).dim
  let t : EuclideanSpace ℝ (Fin (∑ i : Fin (L + (1 : ℕ)), (v i).dim)) :=
    pathVector r v
  let s : Fin L → ℕ :=
    fun (j : Fin L) => (v j.castSucc).dim + (v j.succ).dim
  let σ : (j : Fin L) → Fin (s j) → Fin N :=
    fun (j : Fin L) => pathPair v j.castSucc j.succ
  ∀ (_ : ∀ (j : Fin L), Function.Injective (σ j))
    (_ : (0 : ℝ) ≤ B),
  let M : Matrix (Fin (∑ j : Fin L, s j)) (Fin N) ℚ :=
    stackedConstraint s σ Q
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin N)) :=
    rationalRealRowSpace M
  let y : EuclideanSpace ℝ (Fin N) :=
    (K ᗮ.starProjection : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) t
  ∀ (_ : ∀ (j : Fin L), (WithLp.toLp (2 : ℝ≥0∞) fun (b : Fin (s j)) => y.ofLp (σ j b)) ∈ U j),
  let D : ℝ :=
    ‖t - y‖
  ∀ (_ : D = ‖t - y‖)
    (_ : ∀ (j : Fin L), (fun (c : Fin ((v j.castSucc).dim + (v j.succ).dim)) => tagDiffV r (v
      j.castSucc) (v j.succ) c (0 : Fin (1 : ℕ))) = fun (b : Fin (s j)) => t.ofLp (σ j
      b)),
  let X : ℝ :=
    ((↑L : ℝ) + (1 : ℝ)) * ((↑dB : ℝ) + (1 : ℝ))
  ∀ (_ : (1 : ℝ) ≤ X)
    (_ : ∀ (j : Fin L), (↑(s j) : ℝ) ≤ (2 : ℝ) * X),
  let ψ : Fin (L + (1 : ℕ)) → ℝ :=
    fun (i : Fin (L + (1 : ℕ))) => r ^ (2 : ℕ) * (v i).lam + (1 / 2 : ℝ) *
      chartMatrixPhase (v i).C (pathNode v t i) (pathNode v t i) + (1 / 2 : ℝ) *
      chartAltForm (v i).C (pathNode v y i) (pathNode v t i)
  ∀ (_ : ψ = fun (i : Fin (L + (1 : ℕ))) => r ^ (2 : ℕ) * (v i).lam + (1 / 2 : ℝ) *
      chartMatrixPhase (v i).C (pathNode v t i) (pathNode v t i) + (1 / 2 : ℝ) *
      chartAltForm (v i).C (pathNode v y i) (pathNode v t i)),
  ∀ (j : Fin L), |ψ j.castSucc - ψ j.succ| ≤ B + ((2 : ℝ) * X) ^ (2 : ℕ) * B ^ (2 : ℕ)
    * (D + B)


open scoped Classical in
private def TagEdgePathStage1Statement : Prop :=
  ∀ (B : ℝ)
    (r : ℝ)
    (_ : (2 : ℝ) ≤ B)
    (L : ℕ)
    (dB : ℕ)
    (_ : (1 : ℕ) ≤ L)
    (v : Fin (L + (1 : ℕ)) → ChartTag)
    (_ : ∀ (i : Fin (L + (1 : ℕ))) (a b : Fin (v i).dim), (↑(rationalHeight ((v i).C a b)) :
      ℝ) ≤ B)
    (U : (j : Fin L) → Submodule ℝ (EuclideanSpace ℝ (Fin ((v j.castSucc).dim + (v
      j.succ).dim))))
    (Q : (j : Fin L) → Matrix (Fin ((v j.castSucc).dim + (v j.succ).dim)) (Fin ((v
      j.castSucc).dim + (v j.succ).dim)) ℚ)
    (_ : ∀ (j : Fin L), realMatrixOperator ((Q j).map fun (q : ℚ) => (↑q : ℝ)) = (U j)
      ᗮ.starProjection)
    (_ : ∀ (j : Fin L), ∀ x ∈ U j, ∀ y ∈ U j, chartAltForm (tagDiffC (v j.castSucc) (v
      j.succ)) y.ofLp x.ofLp = (0 : ℝ)),
  let N : ℕ :=
    ∑ i : Fin (L + (1 : ℕ)), (v i).dim
  let t : EuclideanSpace ℝ (Fin (∑ i : Fin (L + (1 : ℕ)), (v i).dim)) :=
    pathVector r v
  let s : Fin L → ℕ :=
    fun (j : Fin L) => (v j.castSucc).dim + (v j.succ).dim
  let σ : (j : Fin L) → Fin (s j) → Fin N :=
    fun (j : Fin L) => pathPair v j.castSucc j.succ
  ∀ (_ : σ = fun (j : Fin L) => pathPair v j.castSucc j.succ)
    (_ : (0 : ℝ) ≤ B),
  let M : Matrix (Fin (∑ j : Fin L, s j)) (Fin N) ℚ :=
    stackedConstraint s σ Q
  ∀ (_ : ∀ (p : Fin (∑ j : Fin L, s j)) (q : Fin N), (↑(rationalHeight (M p q)) : ℝ) ≤ B),
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin N)) :=
    rationalRealRowSpace M
  let y : EuclideanSpace ℝ (Fin N) :=
    (K ᗮ.starProjection : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) t
  ∀ (_ : y ∈ K ᗮ),
  let D : ℝ :=
    ‖t - y‖
  ∀ (_ : D = ‖t - y‖)
    (_ : (0 : ℝ) ≤ D)
    (_ : D ≤ Real.exp ((4 : ℝ) * ((↑(∑ j : Fin L, s j) : ℝ) + (↑N : ℝ) + (1 : ℝ)) ^ (4 : ℕ) *
      Real.log ((2 : ℝ) * B)) * ((↑(∑ j : Fin L, s j) : ℝ) * B)),
  let X : ℝ :=
    ((↑L : ℝ) + (1 : ℝ)) * ((↑dB : ℝ) + (1 : ℝ))
  ∀ (_ : X = ((↑L : ℝ) + (1 : ℝ)) * ((↑dB : ℝ) + (1 : ℝ)))
    (_ : (1 : ℝ) ≤ X)
    (_ : ∀ (i : Fin (L + (1 : ℕ))), (↑(v i).dim : ℝ) ≤ X)
    (_ : (↑L : ℝ) ≤ X)
    (_ : (↑N : ℝ) ≤ X)
    (_ : (↑(∑ j : Fin L, s j) : ℝ) ≤ (2 : ℝ) * X),
  let ψ : Fin (L + (1 : ℕ)) → ℝ :=
    fun (i : Fin (L + (1 : ℕ))) => r ^ (2 : ℕ) * (v i).lam + (1 / 2 : ℝ) *
      chartMatrixPhase (v i).C (pathNode v t i) (pathNode v t i) + (1 / 2 : ℝ) *
      chartAltForm (v i).C (pathNode v y i) (pathNode v t i)
  ∀ (_ : ψ = fun (i : Fin (L + (1 : ℕ))) => r ^ (2 : ℕ) * (v i).lam + (1 / 2 : ℝ) *
      chartMatrixPhase (v i).C (pathNode v t i) (pathNode v t i) + (1 / 2 : ℝ) *
      chartAltForm (v i).C (pathNode v y i) (pathNode v t i))
    (_ : ∀ (j : Fin L), |ψ j.castSucc - ψ j.succ| ≤ B + ((2 : ℝ) * X) ^ (2 : ℕ) * B ^ (2 : ℕ)
      * (D + B)),
  tagEdge (Real.exp ((100000 : ℝ) * X ^ (8 : ℕ) * Real.log ((2 : ℝ) * B))) r (v (0 :
    Fin (L + (1 : ℕ)))) (v (Fin.last L))




private theorem tagEdge_path_hedgeB : TagEdgePathHedgeBStatement := by
  classical
  intro B r hB L dB hL v hC U Q hiso hdist heff N t s σ hσi hB0 M K y hyU D hD hVcol X hX1 hsX ψ
    hψ j
  have h1 := heff j
  have h2 := hdist j
  rw [hVcol j] at h1 h2
  set Vj : EuclideanSpace ℝ (Fin (s j)) := WithLp.toLp 2 (fun b => t (σ j b)) with hVj
  set! Gj : EuclideanSpace ℝ (Fin (s j)) := WithLp.toLp 2 (fun b => y (σ j b)) with hGj
  set Fj := (U j).starProjection Vj with hFj
  have hFU : Fj ∈ U j := (U j).starProjection_apply_mem Vj
  have hGF : Gj - Fj ∈ U j := sub_mem (hyU j) hFU
  have hcorr : chartAltForm (tagDiffC (v j.castSucc) (v j.succ)) Gj.ofLp Vj.ofLp -
      chartAltForm (tagDiffC (v j.castSucc) (v j.succ)) Fj.ofLp Vj.ofLp =
      chartAltForm (tagDiffC (v j.castSucc) (v j.succ)) (Gj - Fj).ofLp (Vj - Fj).ofLp := by
    have hz := hiso j Fj hFU (Gj - Fj) hGF
    rw [WithLp.ofLp_sub] at hz
    rw [WithLp.ofLp_sub, WithLp.ofLp_sub, chartAltForm_sub_right, hz, sub_zero,
      chartAltForm_sub_left]
  have hVF : ‖Vj - Fj‖ ≤ B := by
    rw [hFj, ← Submodule.starProjection_orthogonal_val]; exact h2
  have hGV : ‖Gj - Vj‖ ≤ D := by
    have : Gj - Vj = WithLp.toLp 2 (fun b => (y - t) (σ j b)) := by ext b; simp [hGj, hVj]
    rw [this, hD, norm_sub_rev]; exact norm_toLp_comp_le (hσi j) _
  have hGF' : ‖Gj - Fj‖ ≤ D + B := by
    calc ‖Gj - Fj‖ = ‖(Gj - Vj) + (Vj - Fj)‖ := by congr 1; abel
      _ ≤ ‖Gj - Vj‖ + ‖Vj - Fj‖ := norm_add_le _ _
      _ ≤ D + B := add_le_add hGV hVF
  have hbd := abs_chartAltForm_le (tagDiffC (v j.castSucc) (v j.succ)) hB0
    (abs_tagDiffC_le hB0 (hC _) (hC _)) (Gj - Fj) (Vj - Fj)
  have hs2 : ((s j : ℕ) : ℝ) * (s j : ℕ) ≤ (2 * X) ^ 2 := by
    have := hsX j; have : (0 : ℝ) ≤ s j := Nat.cast_nonneg _; nlinarith
  have hc : |chartAltForm (tagDiffC (v j.castSucc) (v j.succ)) (Gj - Fj).ofLp (Vj - Fj).ofLp| ≤
      2 * ((2 * X) ^ 2 * B) * (D + B) * B := by
    refine hbd.trans ?_
    have : ((s j : ℕ) : ℝ) * (s j : ℕ) * B ≤ (2 * X) ^ 2 * B := by gcongr
    gcongr
  have hid : ψ j.castSucc - ψ j.succ =
      (tagDiffΛ r (v j.castSucc) (v j.succ) 0 0 +
        1 / 2 * chartMatrixPhase (tagDiffC (v j.castSucc) (v j.succ)) (fun b => t (σ j b))
          (fun b => t (σ j b)) +
        1 / 2 * chartAltForm (tagDiffC (v j.castSucc) (v j.succ)) Fj.ofLp
          (fun b => t (σ j b))) +
      1 / 2 * chartAltForm (tagDiffC (v j.castSucc) (v j.succ)) (Gj - Fj).ofLp
          (Vj - Fj).ofLp := by
    rw [← hcorr]
    rw [show chartMatrixPhase (tagDiffC (v j.castSucc) (v j.succ)) (fun b => t (σ j b))
        (fun b => t (σ j b)) = _ from chartMatrixPhase_pathPair v _ _ t t]
    rw [show chartAltForm (tagDiffC (v j.castSucc) (v j.succ)) Gj.ofLp Vj.ofLp = _ from
        chartAltForm_pathPair v _ _ y t]
    simp only [hψ, tagDiffΛ, hVj]
    ring
  rw [hid]
  calc _ ≤ |tagDiffΛ r (v j.castSucc) (v j.succ) 0 0 +
        1 / 2 * chartMatrixPhase (tagDiffC (v j.castSucc) (v j.succ)) (fun b => t (σ j b))
          (fun b => t (σ j b)) +
        1 / 2 * chartAltForm (tagDiffC (v j.castSucc) (v j.succ)) Fj.ofLp
          (fun b => t (σ j b))| +
      |1 / 2 * chartAltForm (tagDiffC (v j.castSucc) (v j.succ)) (Gj - Fj).ofLp
          (Vj - Fj).ofLp| := abs_add_le _ _
    _ ≤ B + 1 / 2 * (2 * ((2 * X) ^ 2 * B) * (D + B) * B) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        gcongr
    _ = B + (2 * X) ^ 2 * B ^ 2 * (D + B) := by ring



private theorem tagEdge_path_stage_1 : TagEdgePathStage1Statement := by
  classical
  intro B r hB L dB hL v hC U Q hQ1 hiso N t s σ hσ hB0 M hMh K y hyW D hD hD0 hDle X hX hX1 hdimX
    hLX hNX hmX ψ hψ hedgeB
  have htel : |ψ 0 - ψ (Fin.last L)| ≤ X * (B + (2 * X) ^ 2 * B ^ 2 * (D + B)) := by
    rw [← sum_castSucc_sub_succ ψ]
    calc _ ≤ ∑ j : Fin L, |ψ j.castSucc - ψ j.succ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin L, (B + (2 * X) ^ 2 * B ^ 2 * (D + B)) :=
          Finset.sum_le_sum (fun j _ => hedgeB j)
      _ = L * (B + (2 * X) ^ 2 * B ^ 2 * (D + B)) := by simp; ring
      _ ≤ _ := by gcongr
  -- the endpoint subspace
  obtain ⟨P, -, hP2, -, hP4, -, -⟩ := rationalMatrix_projection_bounds (d := N) le_rfl hB M hMh
  set E₁ := Real.exp (8 * (N + 1 : ℝ) ^ 4 * Real.log (2 * B)) with hE₁
  have hlog0 : 0 ≤ Real.log (2 * B) := Real.log_nonneg (by linarith)
  have hE₁2 : 2 ≤ E₁ := by
    have h1 : (1 : ℝ) ≤ 8 * (N + 1 : ℝ) ^ 4 := by
      have : (1 : ℝ) ≤ (N + 1 : ℝ) ^ 4 := one_le_pow₀ (by
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
        linarith)
      linarith
    calc (2 : ℝ) ≤ 2 * B := by linarith
      _ = Real.exp (Real.log (2 * B)) := (Real.exp_log (by linarith)).symm
      _ ≤ E₁ := Real.exp_le_exp.mpr (by nlinarith only [hlog0, h1])
  set! τ := pathPair v 0 (Fin.last L) with hτ
  have hτi : Function.Injective τ := pathPair_injective v (by
    rw [Ne, Fin.ext_iff]; simp; omega)
  obtain ⟨W', Q', h1', h2', h3', h4', hin, hout⟩ :=
    rational_restrict_subspace hE₁2 P Kᗮ hP2 hP4 τ
  have hTcol : (fun c => tagDiffV r (v 0) (v (Fin.last L)) c 0) = fun c => t (τ c) :=
    (pathVector_pair r v _ _).symm
  set! T : EuclideanSpace ℝ (Fin ((v 0).dim + (v (Fin.last L)).dim)) :=
    WithLp.toLp 2 (fun c => t (τ c)) with hT
  set! u : EuclideanSpace ℝ (Fin ((v 0).dim + (v (Fin.last L)).dim)) :=
    WithLp.toLp 2 (fun c => y (τ c)) with hu
  have huW : u ∈ W' := hin y hyW
  have iso' : ∀ x ∈ W', ∀ x₂ ∈ W',
      chartAltForm (tagDiffC (v 0) (v (Fin.last L))) x₂.ofLp x.ofLp = 0 := by
    intro x hx x₂ hx₂
    obtain ⟨z, hz, rfl⟩ := hout x hx
    obtain ⟨z₂, hz₂, rfl⟩ := hout x₂ hx₂
    have hzU := (mem_stackedConstraint_kernel s σ Q U hQ1 z).mp hz
    have hz₂U := (mem_stackedConstraint_kernel s σ Q U hQ1 z₂).mp hz₂
    rw [show chartAltForm (tagDiffC (v 0) (v (Fin.last L))) (WithLp.toLp 2 fun c => z₂ (τ c)).ofLp
        (WithLp.toLp 2 fun c => z (τ c)).ofLp = _ from chartAltForm_pathPair v _ _ z₂ z]
    rw [← sum_castSucc_sub_succ (fun i => chartAltForm (v i).C (pathNode v z₂ i) (pathNode v z i))]
    apply Finset.sum_eq_zero
    intro j _
    have h := hiso j _ (hzU j) _ (hz₂U j)
    simp only [hσ] at h
    rw [chartAltForm_pathPair] at h
    exact h
  have hTu : T - u = WithLp.toLp 2 (fun c => (t - y) (τ c)) := by ext c; simp [hT, hu]
  have hTuD : ‖T - u‖ ≤ D := by rw [hTu, hD]; exact norm_toLp_comp_le hτi _
  have dist' : ‖W'ᗮ.starProjection T‖ ≤ D := by
    have h0 : W'ᗮ.starProjection u = 0 := Submodule.starProjection_orthogonal_apply_eq_zero huW
    calc ‖W'ᗮ.starProjection T‖ = ‖W'ᗮ.starProjection (T - u)‖ := by
          rw [map_sub, h0, sub_zero]
      _ ≤ ‖T - u‖ := Submodule.norm_starProjection_apply_le _ _
      _ ≤ D := hTuD
  set! F' := W'.starProjection T with hF'
  have hF'W : F' ∈ W' := W'.starProjection_apply_mem T
  have hFu : F' - u ∈ W' := sub_mem hF'W huW
  have hTF : ‖T - F'‖ ≤ D := by
    rw [hF', ← Submodule.starProjection_orthogonal_val]; exact dist'
  have hFuD : ‖F' - u‖ ≤ 2 * D := by
    calc ‖F' - u‖ = ‖(T - u) - (T - F')‖ := by congr 1; abel
      _ ≤ ‖T - u‖ + ‖T - F'‖ := norm_sub_le _ _
      _ ≤ 2 * D := by linarith
  have hcorr' : chartAltForm (tagDiffC (v 0) (v (Fin.last L))) F'.ofLp T.ofLp -
      chartAltForm (tagDiffC (v 0) (v (Fin.last L))) u.ofLp T.ofLp =
      chartAltForm (tagDiffC (v 0) (v (Fin.last L))) (F' - u).ofLp (T - u).ofLp := by
    have hz := iso' u huW (F' - u) hFu
    rw [WithLp.ofLp_sub] at hz
    rw [WithLp.ofLp_sub, WithLp.ofLp_sub, chartAltForm_sub_right, hz, sub_zero,
      chartAltForm_sub_left]
  have hn'X : (((v 0).dim + (v (Fin.last L)).dim : ℕ) : ℝ) ≤ 2 * X := by
    have := hdimX 0; have := hdimX (Fin.last L); push_cast; linarith
  have hc' : |chartAltForm (tagDiffC (v 0) (v (Fin.last L))) (F' - u).ofLp (T - u).ofLp| ≤
      2 * ((2 * X) ^ 2 * B) * (2 * D) * D := by
    refine (abs_chartAltForm_le _ hB0 (abs_tagDiffC_le hB0 (hC _) (hC _)) _ _).trans ?_
    have h0 : (0 : ℝ) ≤ (((v 0).dim + (v (Fin.last L)).dim : ℕ) : ℝ) := Nat.cast_nonneg _
    have : (((v 0).dim + (v (Fin.last L)).dim : ℕ) : ℝ) *
        (((v 0).dim + (v (Fin.last L)).dim : ℕ) : ℝ) * B ≤ (2 * X) ^ 2 * B := by
      gcongr; nlinarith only [hn'X]
    gcongr
  have hid' : tagDiffΛ r (v 0) (v (Fin.last L)) 0 0 +
      1 / 2 * chartMatrixPhase (tagDiffC (v 0) (v (Fin.last L))) T.ofLp T.ofLp +
      1 / 2 * chartAltForm (tagDiffC (v 0) (v (Fin.last L))) F'.ofLp T.ofLp =
      (ψ 0 - ψ (Fin.last L)) +
        1 / 2 * chartAltForm (tagDiffC (v 0) (v (Fin.last L))) (F' - u).ofLp (T - u).ofLp := by
    rw [← hcorr']
    rw [show chartMatrixPhase (tagDiffC (v 0) (v (Fin.last L))) T.ofLp T.ofLp = _ from
      chartMatrixPhase_pathPair v _ _ t t]
    rw [show chartAltForm (tagDiffC (v 0) (v (Fin.last L))) u.ofLp T.ofLp = _ from
      chartAltForm_pathPair v _ _ y t]
    simp only [hψ, tagDiffΛ]
    ring
  have eff' : |tagDiffΛ r (v 0) (v (Fin.last L)) 0 0 +
      1 / 2 * chartMatrixPhase (tagDiffC (v 0) (v (Fin.last L))) T.ofLp T.ofLp +
      1 / 2 * chartAltForm (tagDiffC (v 0) (v (Fin.last L))) F'.ofLp T.ofLp| ≤
      X * (B + (2 * X) ^ 2 * B ^ 2 * (D + B)) + (2 * X) ^ 2 * B * 2 * D ^ 2 := by
    rw [hid']
    calc _ ≤ |ψ 0 - ψ (Fin.last L)| + |1 / 2 * chartAltForm (tagDiffC (v 0) (v (Fin.last L)))
          (F' - u).ofLp (T - u).ofLp| := abs_add_le _ _
      _ ≤ X * (B + (2 * X) ^ 2 * B ^ 2 * (D + B)) +
          1 / 2 * (2 * ((2 * X) ^ 2 * B) * (2 * D) * D) := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          gcongr
      _ = _ := by ring
  -- the quasipolynomial budget
  have hDX : D ≤ Real.exp (4 * (4 * X) ^ 4 * Real.log (2 * B)) * (2 * X * B) := by
    refine hDle.trans ?_
    have h4 : ((∑ j, s j : ℕ) + N + 1 : ℝ) ≤ 4 * X := by linarith
    have h0 : (0 : ℝ) ≤ ((∑ j, s j : ℕ) + N + 1 : ℝ) := by positivity
    gcongr
  obtain ⟨b1, b2, b3⟩ := shortPath_budget hX1 hB hDX hD0
  have hheight : Real.exp (8 * ((((v 0).dim + (v (Fin.last L)).dim : ℕ) : ℝ) + 1) ^ 4 *
      Real.log (2 * E₁)) ≤ Real.exp (100000 * X ^ 8 * Real.log (2 * B)) := by
    refine le_trans ?_ b3
    apply Real.exp_le_exp.mpr
    have hl : Real.log (2 * E₁) ≤ Real.log (2 * Real.exp (8 * (X + 1) ^ 4 * Real.log (2 * B))) := by
      apply Real.log_le_log (by linarith)
      rw [hE₁]
      gcongr
    have hl0 : 0 ≤ Real.log (2 * E₁) := Real.log_nonneg (by linarith)
    have h0 : (0 : ℝ) ≤ (((v 0).dim + (v (Fin.last L)).dim : ℕ) : ℝ) := Nat.cast_nonneg _
    gcongr
  have hgoal : (Real.exp (100000 * ((L + 1) * (dB + 1) : ℝ) ^ 8 * Real.log (2 * B))) =
      Real.exp (100000 * X ^ 8 * Real.log (2 * B)) := by rw [hX]
  rw [hgoal]
  apply (weylSplitData_iff _ _ _).mpr
  rw [hTcol]
  refine ⟨W', Q', h1', h2', iso', fun i j => (h3' i j).trans ?_, fun i j => (h4' i j).trans ?_,
    dist'.trans b1, eff'.trans b2⟩
  · push_cast at hheight ⊢; exact hheight
  · push_cast at hheight ⊢; exact hheight


/-- Blueprint lem:graph, short paths (proof line 1704): if `v_0, …, v_L` are joined
consecutively by edges at length `r` with heights and sizes at most `B`, then the endpoints are
joined by an edge with logarithmic height and size polynomial in `L`, the dimensions and
`log B`. -/
theorem tagEdge_path {B r : ℝ} (hB : 2 ≤ B) {L dB : ℕ} (hL : 1 ≤ L)
    (v : Fin (L + 1) → ChartTag) (hdim : ∀ i, (v i).dim ≤ dB)
    (hC : ∀ i a b, (rationalHeight ((v i).C a b) : ℝ) ≤ B)
    (hedge : ∀ j : Fin L, tagEdge B r (v j.castSucc) (v j.succ)) :
    tagEdge (Real.exp (100000 * ((L + 1) * (dB + 1) : ℝ) ^ 8 * Real.log (2 * B))) r
      (v 0) (v (Fin.last L)) := by
  classical
  choose U Q hQ1 hQ2 hiso hh1 hh2 hdist heff using
    fun j => (weylSplitData_iff _ _ _).mp (hedge j)
  set! N := ∑ i, (v i).dim with hN
  set! t := pathVector r v with ht
  set! s : Fin L → ℕ := fun j => (v j.castSucc).dim + (v j.succ).dim with hs
  set! σ : (j : Fin L) → Fin (s j) → Fin N := fun j => pathPair v j.castSucc j.succ with hσ
  have hσi : ∀ j, Function.Injective (σ j) := fun j =>
    pathPair_injective v (show j.castSucc < j.succ from Fin.castSucc_lt_succ).ne
  have hB0 : (0 : ℝ) ≤ B := by linarith only [hB]
  set! M := stackedConstraint s σ Q with hM
  have hMh : ∀ p q, (rationalHeight (M p q) : ℝ) ≤ B :=
    stackedConstraint_height (by linarith) s σ hσi Q hh1
  set! K := rationalRealRowSpace M with hK
  set! y := Kᗮ.starProjection t with hy
  have hyW : y ∈ Kᗮ := Kᗮ.starProjection_apply_mem t
  have hyU : ∀ j, WithLp.toLp 2 (fun b => y (σ j b)) ∈ U j :=
    (mem_stackedConstraint_kernel s σ Q U hQ1 y).mp hyW
  set! D := ‖t - y‖ with hD
  have hD0 : 0 ≤ D := norm_nonneg _
  -- the edge vectors are restrictions of the concatenated vector
  have hVcol : ∀ j : Fin L, (fun c => tagDiffV r (v j.castSucc) (v j.succ) c 0) =
      fun b => t (σ j b) := fun j => (pathVector_pair r v _ _).symm
  -- the defect of the concatenated vector
  have hMt : ‖realMatrixOperator (M.map (fun q => (q : ℝ))) t‖ ≤ ((∑ j, s j : ℕ) : ℝ) * B := by
    calc _ ≤ ∑ p, ‖realMatrixOperator (M.map (fun q => (q : ℝ))) t p‖ :=
          euclidean_norm_le_sum_coordinates _
      _ = ∑ k : (j : Fin L) × Fin (s j),
            ‖realMatrixOperator (M.map (fun q => (q : ℝ))) t (finSigmaFinEquiv k)‖ :=
          (Equiv.sum_comp finSigmaFinEquiv _).symm
      _ = ∑ j, ∑ c : Fin (s j),
            ‖realMatrixOperator (M.map (fun q => (q : ℝ))) t (finSigmaFinEquiv ⟨j, c⟩)‖ :=
          Fintype.sum_sigma _
      _ ≤ ∑ j, ∑ c : Fin (s j), B := by
          apply Finset.sum_le_sum; intro j _; apply Finset.sum_le_sum; intro c _
          have e1 : realMatrixOperator (M.map (fun q => (q : ℝ))) t (finSigmaFinEquiv ⟨j, c⟩) =
              (U j)ᗮ.starProjection (WithLp.toLp 2 (fun b => t (σ j b))) c := by
            rw [← hQ1]
            simp only [realMatrixOperator_apply]
            exact stackedConstraint_mulVec s σ Q t.ofLp j c
          rw [e1]
          have h2 := hdist j
          rw [hVcol j] at h2
          exact (PiLp.norm_apply_le _ c).trans h2
      _ = ((∑ j, s j : ℕ) : ℝ) * B := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; rw [Finset.sum_mul]
  have hDle : D ≤ Real.exp (4 * ((∑ j, s j : ℕ) + N + 1 : ℝ) ^ 4 * Real.log (2 * B)) *
      (((∑ j, s j : ℕ) : ℝ) * B) := by
    have h1 : t - y = K.starProjection t := by
      rw [hy, Submodule.starProjection_orthogonal_val]; abel
    rw [hD, h1]
    refine (rational_rowSpace_projection_le hB M hMh t).trans ?_
    gcongr
  -- dimension bookkeeping
  set X : ℝ := ((L : ℝ) + 1) * ((dB : ℝ) + 1) with hX
  have hX1 : 1 ≤ X := by
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ dB := Nat.cast_nonneg _
    rw [hX]; nlinarith only
  have hdimX : ∀ i, ((v i).dim : ℝ) ≤ X := by
    intro i
    have : ((v i).dim : ℝ) ≤ dB := by exact_mod_cast hdim i
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ dB := Nat.cast_nonneg _
    rw [hX]; nlinarith
  have hLX : (L : ℝ) ≤ X := by
    have : (0 : ℝ) ≤ dB := Nat.cast_nonneg _
    rw [hX]; nlinarith only
  have hNX : (N : ℝ) ≤ X := by
    have h1 : N ≤ (L + 1) * dB := by
      calc N = ∑ i, (v i).dim := rfl
        _ ≤ ∑ _i : Fin (L + 1), dB := Finset.sum_le_sum (fun i _ => hdim i)
        _ = (L + 1) * dB := by simp
    have h2 : ((L + 1) * dB : ℕ) ≤ ((L : ℝ) + 1) * ((dB : ℝ) + 1) := by
      push_cast; have : (0 : ℝ) ≤ L := Nat.cast_nonneg _; nlinarith only
    calc (N : ℝ) ≤ ((L + 1) * dB : ℕ) := by exact_mod_cast h1
      _ ≤ X := h2
  have hsX : ∀ j, (s j : ℝ) ≤ 2 * X := by
    intro j
    have := hdimX j.castSucc; have := hdimX j.succ
    simp only [hs]; push_cast; linarith
  have hmX : ((∑ j, s j : ℕ) : ℝ) ≤ 2 * X := by
    have h1 : ∑ j, s j ≤ L * (2 * dB) := by
      calc ∑ j, s j ≤ ∑ _j : Fin L, 2 * dB := Finset.sum_le_sum (fun j _ => by
            simp only [hs]; have := hdim j.castSucc; have := hdim j.succ; omega)
        _ = L * (2 * dB) := by simp
    have h2 : ((L * (2 * dB) : ℕ) : ℝ) ≤ 2 * X := by
      push_cast; have : (0 : ℝ) ≤ L := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ dB := Nat.cast_nonneg _
      rw [hX]; nlinarith only
    calc ((∑ j, s j : ℕ) : ℝ) ≤ ((L * (2 * dB) : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ 2 * X := h2
  -- the node potentials
  set! ψ : Fin (L + 1) → ℝ := fun i => r ^ 2 * (v i).lam +
    1 / 2 * chartMatrixPhase (v i).C (pathNode v t i) (pathNode v t i) +
    1 / 2 * chartAltForm (v i).C (pathNode v y i) (pathNode v t i) with hψ
  have hedgeB : ∀ j : Fin L, |ψ j.castSucc - ψ j.succ| ≤ B + (2 * X) ^ 2 * B ^ 2 * (D + B) := by
    expose_names
    exact @tagEdge_path_hedgeB B r hB L dB hL v hC U Q hiso hdist heff hσi hB0 hyU hD hVcol hX1
      hsX hψ
  expose_names
  exact @tagEdge_path_stage_1 B r hB L dB hL v hC U Q hQ1 hiso hσ hB0 hMh hyW hD hD0 hDle hX hX1
    hdimX hLX hNX hmX hψ hedgeB

theorem tagEdge_mono {B B' r : ℝ} {v w : ChartTag} (h : tagEdge B r v w) (hB : B ≤ B') :
    tagEdge B' r v w := WeylSplitData.mono h hB

theorem qpoly_exponent_mono {D₁ D : ℕ} (h : D₁ ≤ D) {Y : ℝ} (hY : 1 ≤ Y) :
    Real.exp (D₁ * Y ^ D₁) ≤ Real.exp (D * Y ^ D) := by
  apply Real.exp_le_exp.mpr
  have h1 : Y ^ D₁ ≤ Y ^ D := pow_le_pow_right₀ hY h
  have h2 : (D₁ : ℝ) ≤ D := by exact_mod_cast h
  have h3 : (0 : ℝ) ≤ Y ^ D₁ := by positivity
  have h4 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  calc (D₁ : ℝ) * Y ^ D₁ ≤ D * Y ^ D₁ := by gcongr
    _ ≤ D * Y ^ D := by gcongr

/-- Blueprint lem:graph (Declaration graph, `THT.Localization.curvatureGraph`): one choice
`H_ed = exp(D (1 + log H + log τ₂⁻¹)^D)` of the edge threshold gives same-slot separation
(normalized inner product at most `τ₂` on every interval of length `r`) and distinct-slot
separation (form norm at most `τ₂` against arbitrary normalized `L²` spectators) for tags not
joined by an edge, and paths of edges give endpoint edges with logarithmic height and size
polynomial in the path length, the dimensions and the logarithm of the edge threshold. -/
theorem curvatureGraph (κ : LocalKernelClass) (c₀ : ℕ) (hc : 1 ≤ c₀) :
    ∃ D : ℕ, 1 ≤ D ∧
    (∀ (H τ : ℝ), Real.exp 2 ≤ H → 0 < τ → τ ≤ 1 →
      ∀ (v w : ChartTag) (c : ℤ), c ≠ 0 →
      ∀ (A : QuadraticChartData v.dim) (B : QuadraticChartData w.dim),
      QuadraticChartComplexity c₀ H A → QuadraticChartComplexity c₀ H B →
      IsBoundedQuadraticChart A → IsBoundedQuadraticChart B →
      A.horizontal = v.θ → A.matrix = (c : ℚ) • v.C → A.quadratic = c * v.lam →
      B.horizontal = w.θ → B.matrix = (c : ℚ) • w.C → B.quadratic = c * w.lam →
      ∀ (a₀ r : ℝ), 0 < r →
      ¬ tagEdge (Real.exp (D * (1 + Real.log H + Real.log τ⁻¹) ^ D)) r v w →
      ‖∫ y, quadraticChartAtom A y * star (quadraticChartAtom B y)
        ∂(normalizedIntervalMeasure a₀ r)‖ ≤ τ) ∧
    (∀ (H τ : ℝ), Real.exp 2 ≤ H → 0 < τ → τ ≤ 1 →
      ∀ (v w : ChartTag) {a i k b : Fin 4}, a ≠ i → a ≠ k → a ≠ b → i ≠ k → i ≠ b → k ≠ b →
      1 ≤ v.dim → 1 ≤ w.dim →
      ∀ (A : QuadraticChartData v.dim) (A' : QuadraticChartData w.dim),
      QuadraticChartComplexity c₀ H A → QuadraticChartComplexity c₀ H A' →
      IsBoundedQuadraticChart A → IsBoundedQuadraticChart A' →
      A.horizontal = v.θ → A.matrix = (slotCoeff i : ℚ) • v.C →
      A.quadratic = slotCoeff i * v.lam →
      A'.horizontal = w.θ → A'.matrix = (slotCoeff k : ℚ) • w.C →
      A'.quadratic = slotCoeff k * w.lam →
      ∀ {a₀ r : ℝ}, 0 < r → ∀ {wI : ℝ × ℝ → ℂ}, IsAdmissibleLocalKernel κ a₀ r wI →
      ¬ tagEdge (Real.exp (D * (1 + Real.log H + Real.log τ⁻¹) ^ D)) r v w →
      PairSmall a₀ r wI i k (quadraticChartAtom A) (quadraticChartAtom A') τ) ∧
    (∀ {B r : ℝ}, 2 ≤ B → ∀ {L dB : ℕ}, 1 ≤ L →
      ∀ (v : Fin (L + 1) → ChartTag), (∀ i, (v i).dim ≤ dB) →
      (∀ i a b, (rationalHeight ((v i).C a b) : ℝ) ≤ B) →
      (∀ j : Fin L, tagEdge B r (v j.castSucc) (v j.succ)) →
      tagEdge (Real.exp (100000 * ((L + 1) * (dB + 1) : ℝ) ^ 8 * Real.log (2 * B))) r
        (v 0) (v (Fin.last L))) := by
  obtain ⟨D₁, hD₁, hsame⟩ := graph_sameSlot_tag c₀ hc
  obtain ⟨D₂, hD₂, hdist⟩ := graph_distinctSlot_tag κ c₀ hc
  refine ⟨max D₁ D₂, le_max_of_le_left hD₁, ?_, ?_, fun {_ _} hB {_ _} hL v hdim hC he =>
    tagEdge_path hB hL v hdim hC he⟩
  · intro H τ hH hτ hτ1 v w c hc0 A B hA hB hAb hBb hAh hAm hAq hBh hBm hBq a₀ r hr hne
    refine hsame H τ hH hτ hτ1 v w c hc0 A B hA hB hAb hBb hAh hAm hAq hBh hBm hBq a₀ r hr
      (fun he => hne (tagEdge_mono he (qpoly_exponent_mono (le_max_left _ _) ?_)))
    have hlogH : 0 ≤ Real.log H := Real.log_nonneg (le_trans (by
      have := Real.add_one_le_exp (2 : ℝ); linarith only [this]) hH)
    have hlτ : 0 ≤ Real.log τ⁻¹ := Real.log_nonneg (one_le_inv₀ hτ |>.mpr hτ1)
    linarith
  · intro H τ hH hτ hτ1 v w a i k b hai hak hab hik hib hkb hv hw A A' hA hA' hAb hA'b hAh hAm
      hAq hA'h hA'm hA'q a₀ r hr wI hwI hne
    refine hdist H τ hH hτ hτ1 v w hai hak hab hik hib hkb hv hw A A' hA hA' hAb hA'b hAh hAm
      hAq hA'h hA'm hA'q hr hwI
      (fun he => hne (tagEdge_mono he (qpoly_exponent_mono (le_max_right _ _) ?_)))
    have hlogH : 0 ≤ Real.log H := Real.log_nonneg (le_trans (by
      have := Real.add_one_le_exp (2 : ℝ); linarith) hH)
    have hlτ : 0 ≤ Real.log τ⁻¹ := Real.log_nonneg (one_le_inv₀ hτ |>.mpr hτ1)
    linarith

section Rounds
variable {V : Type*}

/-! ### Decreasing colors (blueprint §12.2, lines 1712-1755)

The deterministic part of the coloring.  A *round* is a present list `X` with integer scores; it
is *marked* if it has a unique winner whose score exceeds every rival score by at least five.
The *round potential* `2·top + [unmarked]` is monotone when the list grows and scores increase,
and it determines the marking and the winner. -/

open Classical in
/-- The top score of a round (`0` on an empty list). -/
noncomputable def roundTop (X : Finset V) (sc : V → ℤ) : ℤ :=
  if h : X.Nonempty then X.sup' h sc else 0

/-- `z` is the marked winner of the round: its score is the top score and every rival is at
least five below. -/
def RoundWinner (X : Finset V) (sc : V → ℤ) (z : V) : Prop :=
  z ∈ X ∧ sc z = roundTop X sc ∧ ∀ z' ∈ X, z' ≠ z → sc z' + 5 ≤ roundTop X sc

/-- A finite scored family with a winning round. -/
def RoundMarked (X : Finset V) (sc : V → ℤ) : Prop := ∃ z, RoundWinner X sc z

open Classical in
/-- The round potential `2·top + [unmarked]`. -/
noncomputable def roundPot (X : Finset V) (sc : V → ℤ) : ℤ :=
  2 * roundTop X sc + if RoundMarked X sc then 0 else 1

theorem le_roundTop {X : Finset V} {sc : V → ℤ} {z : V} (hz : z ∈ X) : sc z ≤ roundTop X sc := by
  have h : X.Nonempty := ⟨z, hz⟩
  simp only [roundTop, h, dite_true]; exact Finset.le_sup' sc hz

theorem roundTop_mem {X : Finset V} (hX : X.Nonempty) (sc : V → ℤ) :
    ∃ z ∈ X, sc z = roundTop X sc := by
  simp only [roundTop, hX, dite_true]
  obtain ⟨z, hz, h⟩ := Finset.exists_mem_eq_sup' hX sc
  exact ⟨z, hz, h.symm⟩

theorem roundTop_le {X : Finset V} (hX : X.Nonempty) {sc : V → ℤ} {c : ℤ}
    (h : ∀ z ∈ X, sc z ≤ c) : roundTop X sc ≤ c := by
  obtain ⟨z, hz, he⟩ := roundTop_mem hX sc
  rw [← he]; exact h z hz

theorem RoundWinner.unique {X : Finset V} {sc : V → ℤ} {z z' : V} (h : RoundWinner X sc z)
    (h' : RoundWinner X sc z') : z = z' := by
  by_contra hne
  have := h.2.2 z' h'.1 (Ne.symm hne)
  rw [h'.2.1] at this
  linarith

theorem roundTop_mono {X X' : Finset V} (hX : X.Nonempty) (hXX : X ⊆ X') {sc sc' : V → ℤ}
    (hsc : ∀ z ∈ X, sc z ≤ sc' z) : roundTop X sc ≤ roundTop X' sc' := by
  obtain ⟨z, hz, he⟩ := roundTop_mem hX sc
  rw [← he]
  exact (hsc z hz).trans (le_roundTop (hXX hz))

/-- At an unchanged top score, a winner of the later round was already the winner. -/
theorem RoundWinner.of_later {X X' : Finset V} (hX : X.Nonempty) (hXX : X ⊆ X')
    {sc sc' : V → ℤ} (hsc : ∀ z ∈ X, sc z ≤ sc' z) (htop : roundTop X sc = roundTop X' sc')
    {z : V} (hz : RoundWinner X' sc' z) : RoundWinner X sc z := by
  obtain ⟨z₀, hz₀, he⟩ := roundTop_mem hX sc
  have hz₀z : z₀ = z := by
    by_contra hne
    have h1 := hz.2.2 z₀ (hXX hz₀) hne
    have h2 := hsc z₀ hz₀
    linarith
  subst hz₀z
  refine ⟨hz₀, he, fun z' hz' hne => ?_⟩
  have := hz.2.2 z' (hXX hz') hne
  have := hsc z' hz'
  linarith

theorem roundPot_mono {X X' : Finset V} (hX : X.Nonempty) (hXX : X ⊆ X') {sc sc' : V → ℤ}
    (hsc : ∀ z ∈ X, sc z ≤ sc' z) : roundPot X sc ≤ roundPot X' sc' := by
  have ht := roundTop_mono hX hXX hsc
  rcases ht.lt_or_eq with hlt | heq
  · unfold roundPot; split_ifs <;> omega
  · unfold roundPot
    by_cases hm' : RoundMarked X' sc'
    · obtain ⟨z, hz⟩ := hm'
      have : RoundMarked X sc := ⟨z, hz.of_later hX hXX hsc heq⟩
      have h2 : RoundMarked X' sc' := ⟨z, hz⟩
      simp only [this, h2, ite_true]; omega
    · simp only [hm', ite_false]; split_ifs <;> omega

/-- Equal round potentials force equal top scores, markings and winners. -/
theorem roundPot_eq {X X' : Finset V} (hX : X.Nonempty) (hXX : X ⊆ X') {sc sc' : V → ℤ}
    (hsc : ∀ z ∈ X, sc z ≤ sc' z) (he : roundPot X sc = roundPot X' sc') :
    roundTop X sc = roundTop X' sc' ∧ ∀ z, RoundWinner X sc z ↔ RoundWinner X' sc' z := by
  have ht := roundTop_mono hX hXX hsc
  have htop : roundTop X sc = roundTop X' sc' := by
    rcases ht.lt_or_eq with hlt | heq
    · exfalso; unfold roundPot at he; split_ifs at he <;> omega
    · exact heq
  refine ⟨htop, fun z => ⟨fun hz => ?_, fun hz => hz.of_later hX hXX hsc htop⟩⟩
  have hm : RoundMarked X' sc' := by
    by_contra hm'
    unfold roundPot at he
    have h1 : RoundMarked X sc := ⟨z, hz⟩
    simp only [h1, hm', ite_true, ite_false, htop] at he
    omega
  obtain ⟨z', hz'⟩ := hm
  rwa [hz.unique (hz'.of_later hX hXX hsc htop)]

end Rounds

/-! Dyadic cohorts: the separating level of admission indices `i ≤ j` (0-based) is the bit length
of `i xor j`; the frozen prefix ends at the end of the lower half of the block. -/

/-- The separating level of `i ≤ j`: `0` for the equality cohort. -/
def cohortLevel (i j : ℕ) : ℕ := Nat.size (i ^^^ j)

/-- The length of the frozen prefix of the cohort of the winner index `i` at level `m`. -/
def cohortPrefix (i m : ℕ) : ℕ := if m = 0 then i + 1 else (i / 2 ^ (m - 1) + 1) * 2 ^ (m - 1)

theorem nat_xor_eq_zero_iff {a b : ℕ} : a ^^^ b = 0 ↔ a = b := by
  refine ⟨fun h => Nat.eq_of_testBit_eq fun i => ?_, fun h => h ▸ Nat.xor_self a⟩
  have := congrArg (fun n => n.testBit i) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at this
  revert this; cases a.testBit i <;> cases b.testBit i <;> simp

theorem cohortLevel_le_iff (i j m : ℕ) : cohortLevel i j ≤ m ↔ i / 2 ^ m = j / 2 ^ m := by
  rw [cohortLevel, Nat.size_le, ← nat_xor_eq_zero_iff, ← Nat.xor_div_two_pow,
    Nat.div_eq_zero_iff]
  simp

theorem cohortLevel_mono {i j₁ j₂ : ℕ} (h₁ : i ≤ j₁) (h₂ : j₁ ≤ j₂) :
    cohortLevel i j₁ ≤ cohortLevel i j₂ := by
  rw [cohortLevel_le_iff]
  have h := (cohortLevel_le_iff i j₂ (cohortLevel i j₂)).mp le_rfl
  have a1 := Nat.div_le_div_right (c := 2 ^ cohortLevel i j₂) h₁
  have a2 := Nat.div_le_div_right (c := 2 ^ cohortLevel i j₂) h₂
  omega

/-- At a positive level `m`, the indices sit in the lower and upper half of one block. -/
theorem cohortLevel_halves {i j m : ℕ} (hij : i ≤ j) (hm : cohortLevel i j = m) (hm0 : m ≠ 0) :
    i / 2 ^ (m - 1) = 2 * (i / 2 ^ m) ∧ j / 2 ^ (m - 1) = 2 * (i / 2 ^ m) + 1 := by
  have hp : 2 ^ m = 2 ^ (m - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  have h1 := (cohortLevel_le_iff i j m).mp hm.le
  have h2 : ¬ i / 2 ^ (m - 1) = j / 2 ^ (m - 1) := by
    rw [← cohortLevel_le_iff]; omega
  have hi : i / 2 ^ m = i / 2 ^ (m - 1) / 2 := by rw [hp, Nat.div_div_eq_div_mul]
  have hj : j / 2 ^ m = j / 2 ^ (m - 1) / 2 := by rw [hp, Nat.div_div_eq_div_mul]
  have a1 := Nat.div_le_div_right (c := 2 ^ (m - 1)) hij
  omega

theorem cohortPrefix_le {i j m : ℕ} (hij : i ≤ j) (hm : cohortLevel i j = m) :
    cohortPrefix i m ≤ j + 1 := by
  unfold cohortPrefix
  split_ifs with h0
  · subst h0
    have := (cohortLevel_le_iff i j 0).mp hm.le
    simp at this; omega
  · obtain ⟨-, hj⟩ := cohortLevel_halves hij hm h0
    have h1 := Nat.div_mul_le_self j (2 ^ (m - 1))
    rw [hj] at h1
    have h2 : i / 2 ^ (m - 1) + 1 = 2 * (i / 2 ^ m) + 1 := by
      rw [(cohortLevel_halves hij hm h0).1]
    rw [h2]; omega

/-- The separation of cohorts at a common level along an admission path: the earlier winner
lies in the later frozen prefix. -/
theorem lt_cohortPrefix_of_le {i i' j j' m : ℕ} (hij : i ≤ j) (hi'j' : i' ≤ j') (hjj : j ≤ j')
    (hm : cohortLevel i j = m) (hm' : cohortLevel i' j' = m) : i < cohortPrefix i' m := by
  unfold cohortPrefix
  split_ifs with h0
  · subst h0
    have h1 := (cohortLevel_le_iff i j 0).mp hm.le
    have h2 := (cohortLevel_le_iff i' j' 0).mp hm'.le
    simp at h1 h2; omega
  · obtain ⟨hi, -⟩ := cohortLevel_halves hij hm h0
    obtain ⟨hi', -⟩ := cohortLevel_halves hi'j' hm' h0
    have e1 := (cohortLevel_le_iff i j m).mp hm.le
    have e2 := (cohortLevel_le_iff i' j' m).mp hm'.le
    have a1 := Nat.div_le_div_right (c := 2 ^ m) hjj
    have hlt : i / 2 ^ (m - 1) < i' / 2 ^ (m - 1) + 1 := by omega
    have hp : 0 < 2 ^ (m - 1) := Nat.two_pow_pos _
    have := (Nat.div_lt_iff_lt_mul hp).mp hlt
    linarith only [this]

/-- Graph distances `d_s` on the original vertices (blueprint lines 1682-1686): a pseudometric at
every depth, with values in `ℕ∞`, decreasing with depth. -/
structure DepthDistance (V : Type*) where
  /-- Extended-natural graph distance at each integer depth. -/
  d : ℤ → V → V → ℕ∞
  self : ∀ s v, d s v v = 0
  symm : ∀ s v w, d s v w = d s w v
  triangle : ∀ s u v w, d s u w ≤ d s u v + d s v w
  anti : ∀ {s s'}, s ≤ s' → ∀ v w, d s' v w ≤ d s v w

/-- Capped quotient `min(⌊x/b⌋, c)` of an extended natural (`c` at `∞`). -/
noncomputable def capDiv (x : ℕ∞) (b c : ℕ) : ℕ := if x = ⊤ then c else min (x.toNat / b) c

theorem capDiv_le (x : ℕ∞) (b c : ℕ) : capDiv x b c ≤ c := by
  unfold capDiv; split_ifs <;> simp

theorem capDiv_mono {x y : ℕ∞} (h : x ≤ y) (b c : ℕ) : capDiv x b c ≤ capDiv y b c := by
  unfold capDiv
  by_cases hy : y = ⊤
  · simp only [hy, ite_true]; split_ifs <;> simp
  · have hx : x ≠ ⊤ := ne_top_of_le_ne_top hy h
    simp only [hx, hy, ite_false]
    have : x.toNat ≤ y.toNat := ENat.toNat_le_toNat h hy
    exact min_le_min (Nat.div_le_div_right this) le_rfl

theorem capDiv_zero (b c : ℕ) : capDiv 0 b c = 0 := by simp [capDiv]

/-- If the capped quotient is below the cap, it is the true quotient. -/
theorem capDiv_lt_cap {x : ℕ∞} {b c : ℕ} (h : capDiv x b c < c) :
    x ≠ ⊤ ∧ capDiv x b c = x.toNat / b := by
  unfold capDiv at h ⊢
  by_cases hx : x = ⊤
  · simp [hx] at h
  · simp only [hx, ite_false] at h ⊢
    have := (min_lt_iff.mp h).resolve_right (lt_irrefl c)
    exact ⟨hx, min_eq_left this.le⟩

/-- The integer clipping `min(U, max(T, x))` extended by `T` at `-∞`. -/
noncomputable def clipW (T U : ℝ) : WithBot ℤ → ℝ
  | none => T
  | some n => min U (max T n)

theorem clipW_mem {T U : ℝ} (hTU : T ≤ U) (x : WithBot ℤ) : T ≤ clipW T U x ∧ clipW T U x ≤ U := by
  cases x with
  | bot => exact ⟨le_rfl, hTU⟩
  | coe n => exact ⟨le_min hTU (le_max_left _ _), min_le_left _ _⟩

theorem clipW_coe (T U : ℝ) (n : ℤ) : clipW T U (n : WithBot ℤ) = min U (max T n) := rfl

theorem clipW_bot (T U : ℝ) : clipW T U ⊥ = T := rfl

/-- A clipped value strictly below the top equals the clipping from below only. -/
theorem clipW_le_of_le {T U : ℝ} {x : WithBot ℤ} {c : ℝ} (hc : T ≤ c)
    (h : ∀ n : ℤ, x = n → (n : ℝ) ≤ c) : clipW T U x ≤ c := by
  cases x with
  | bot => exact hc
  | coe n => exact (min_le_right _ _).trans (max_le hc (h n rfl))

theorem nat_mul_two_pow_le_three_pow : ∀ n : ℕ, n * 2 ^ n ≤ 3 ^ n
  | 0 => by norm_num
  | 1 => by norm_num
  | 2 => by norm_num
  | n + 3 => by
    have h := nat_mul_two_pow_le_three_pow (n + 2)
    calc (n + 3) * 2 ^ (n + 3) = (2 * n + 6) * 2 ^ (n + 2) := by ring
      _ ≤ (3 * n + 6) * 2 ^ (n + 2) := Nat.mul_le_mul_right _ (by omega)
      _ = 3 * ((n + 2) * 2 ^ (n + 2)) := by ring
      _ ≤ 3 * 3 ^ (n + 2) := Nat.mul_le_mul_left _ h
      _ = 3 ^ (n + 3) := by ring

/-- `⌊log_{3/2} n⌋` for `n ≥ 1` (and `0` at `0`). -/
def flog32 (n : ℕ) : ℕ := Nat.findGreatest (fun k => 3 ^ k ≤ n * 2 ^ k) n

theorem flog32_mono {n m : ℕ} (h : n ≤ m) : flog32 n ≤ flog32 m := by
  unfold flog32
  apply Nat.findGreatest_mono _ h
  intro k hk
  exact hk.trans (Nat.mul_le_mul_right _ h)

theorem flog32_le (n : ℕ) : flog32 n ≤ n := Nat.findGreatest_le n

/-- The floor-logarithm certificate: `(3/2)^{flog32 n} ≤ n` for `n ≥ 1`. -/
theorem pow_flog32_le {n : ℕ} (hn : 1 ≤ n) : 3 ^ flog32 n ≤ n * 2 ^ flog32 n :=
  Nat.findGreatest_spec (P := fun k => 3 ^ k ≤ n * 2 ^ k) (Nat.zero_le n) (by simpa using hn)

/-- The floor-logarithm is maximal: `n < (3/2)^{flog32 n + 1}`. -/
theorem lt_pow_flog32_succ (n : ℕ) : n * 2 ^ (flog32 n + 1) < 3 ^ (flog32 n + 1) := by
  unfold flog32
  set k := Nat.findGreatest (fun k => 3 ^ k ≤ n * 2 ^ k) n with hk
  by_cases hkn : k + 1 ≤ n
  · have := Nat.findGreatest_is_greatest (P := fun k => 3 ^ k ≤ n * 2 ^ k) (n := n)
      (k := k + 1) (by omega) hkn
    omega
  · -- `k = n`, and `n·2^(n+1) < 3^(n+1)` fails only for small `n`; use `k ≥ n`
    have hk' : k = n := le_antisymm (Nat.findGreatest_le n) (by omega)
    rw [hk']
    have := nat_mul_two_pow_le_three_pow n
    have h3 : 0 < 3 ^ n := by positivity
    rw [pow_succ, pow_succ]; nlinarith

/-- An admission state along a path: a depth, the present list and its admission positions. -/
structure AdmState (V : Type*) where
  /-- Integer depth of an admissible catalog state. -/
  s : ℤ
  /-- Finite set of labels present in the admissible state. -/
  X : Finset V
  /-- Position assigned to each label in the current finite list. -/
  pos : V → ℕ

/-- Well-formed states: positions enumerate the present list. -/
def AdmState.WF {V : Type*} (A : AdmState V) : Prop :=
  (∀ v ∈ A.X, A.pos v < A.X.card) ∧ Set.InjOn A.pos A.X

/-- `A'` is a later state on the same path: deeper, with a longer list extending `A`. -/
def AdmState.Le {V : Type*} (A A' : AdmState V) : Prop :=
  A.s ≤ A'.s ∧ A.X ⊆ A'.X ∧ ∀ v ∈ A.X, A'.pos v = A.pos v

theorem AdmState.Le.refl {V : Type*} (A : AdmState V) : A.Le A := ⟨le_rfl, subset_rfl, fun _ _ =>
    rfl⟩

theorem AdmState.Le.trans {V : Type*} {A B C : AdmState V} (h : A.Le B) (h' : B.Le C) : A.Le C :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, fun v hv => (h'.2.2 v (h.2.1 hv)).trans (h.2.2 v hv)⟩

/-- In a later state, the vertices at positions below the earlier list length are exactly the
earlier vertices. -/
theorem AdmState.Le.mem_of_pos_lt {V : Type*} {A A' : AdmState V} (hA : A.WF)
    (hA' : A'.WF) (h : A.Le A') {w : V} (hw : w ∈ A'.X) (hp : A'.pos w < A.X.card) : w ∈ A.X := by
  classical
  by_contra hwA
  have himg : A.X.image A.pos = Finset.range A.X.card := by
    apply Finset.eq_of_subset_of_card_le
    · intro n hn
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_range.mpr (hA.1 u hu)
    · rw [Finset.card_range, Finset.card_image_of_injOn hA.2]
  have : A'.pos w ∈ A.X.image A.pos := by rw [himg]; exact Finset.mem_range.mpr hp
  obtain ⟨u, hu, hpu⟩ := Finset.mem_image.mp this
  have hu' : A'.pos u = A'.pos w := (h.2.2 u hu).trans hpu
  have := hA'.2 (h.2.1 hu) hw hu'
  exact hwA (this ▸ hu)

/-- The separating level of the cohort of the winner `z` at a state. -/
def admLevel {V : Type*} (A : AdmState V) (z : V) : ℕ := cohortLevel (A.pos z) (A.X.card - 1)

/-- The frozen prefix `W` of the cohort of `z`. -/
def admFrozen {V : Type*} (A : AdmState V) (z : V) : Finset V :=
  A.X.filter (fun w => A.pos w < cohortPrefix (A.pos z) (admLevel A z))

/-! ### Refinement of the tag graph (blueprint lines 1685-1686) -/

theorem chartMatrixPhase_smul {d : ℕ} (C : Matrix (Fin d) (Fin d) ℚ) (t : ℝ) (z w : Fin d → ℝ) :
    chartMatrixPhase C (t • z) (t • w) = t ^ 2 * chartMatrixPhase C z w := by
  simp only [chartMatrixPhase, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem chartAltForm_smul {d : ℕ} (C : Matrix (Fin d) (Fin d) ℚ) (t : ℝ) (z w : Fin d → ℝ) :
    chartAltForm C (t • z) (t • w) = t ^ 2 * chartAltForm C z w := by
  simp only [chartAltForm, chartMatrixPhase_smul]; ring

/-- Blueprint lines 1685-1686: the edge relation persists under refinement: at a smaller length
`r' ≤ r` the difference data `V` and `Λ` are scaled by `r'/r` and `(r'/r)²`, and the same
splitting works. Hence graph distances decrease with depth. -/
theorem tagEdge_refine {B r r' : ℝ} {v w : ChartTag} (h : tagEdge B r v w) (hr' : 0 ≤ r')
    (hrr : r' ≤ r) : tagEdge B r' v w := by
  rcases eq_or_lt_of_le (hr'.trans hrr) with hr0 | hr0
  · have : r' = r := le_antisymm hrr (hr0 ▸ hr')
    rwa [this]
  set t := r' / r
  have ht0 : 0 ≤ t := div_nonneg hr' hr0.le
  have ht1 : t ≤ 1 := (div_le_one hr0).mpr hrr
  unfold tagEdge at h ⊢
  rw [weylSplitData_iff] at h ⊢
  obtain ⟨U, Q, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hB0 : 0 ≤ B := (norm_nonneg _).trans h6
  have hV : (fun i => tagDiffV r' v w i 0) = t • (fun i => tagDiffV r v w i 0) := by
    funext i; simp only [tagDiffV, Pi.smul_apply, smul_eq_mul, t]; field_simp
  have hΛ : tagDiffΛ r' v w 0 0 = t ^ 2 * tagDiffΛ r v w 0 0 := by
    simp only [tagDiffΛ, t]; field_simp
  refine ⟨U, Q, h1, h2, h3, h4, h5, ?_, ?_⟩
  · rw [hV, WithLp.toLp_smul, map_smul, norm_smul, Real.norm_of_nonneg ht0]
    calc t * ‖Uᗮ.starProjection (WithLp.toLp 2 fun i => tagDiffV r v w i 0)‖ ≤ 1 * B :=
          mul_le_mul ht1 h6 (norm_nonneg _) zero_le_one
      _ = B := one_mul B
  · rw [hV, hΛ, WithLp.toLp_smul, map_smul, WithLp.ofLp_smul, chartMatrixPhase_smul,
      chartAltForm_smul]
    have e : t ^ 2 * tagDiffΛ r v w 0 0 +
        1 / 2 * (t ^ 2 * chartMatrixPhase (tagDiffC v w) (fun i => tagDiffV r v w i 0)
          (fun i => tagDiffV r v w i 0)) +
        1 / 2 * (t ^ 2 * chartAltForm (tagDiffC v w)
          (U.starProjection (WithLp.toLp 2 fun i => tagDiffV r v w i 0)).ofLp
          (fun i => tagDiffV r v w i 0)) =
        t ^ 2 * (tagDiffΛ r v w 0 0 +
          1 / 2 * chartMatrixPhase (tagDiffC v w) (fun i => tagDiffV r v w i 0)
            (fun i => tagDiffV r v w i 0) +
          1 / 2 * chartAltForm (tagDiffC v w)
            (U.starProjection (WithLp.toLp 2 fun i => tagDiffV r v w i 0)).ofLp
            (fun i => tagDiffV r v w i 0)) := by ring
    rw [e, abs_mul, abs_of_nonneg (sq_nonneg t)]
    have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
    calc t ^ 2 * _ ≤ 1 * B := mul_le_mul ht2 h7 (abs_nonneg _) zero_le_one
      _ = B := one_mul B

theorem chartMatrixPhase_reindex {n m : ℕ} (e : Fin n ≃ Fin m) (C : Matrix (Fin n) (Fin n) ℚ)
    (z w : Fin n → ℝ) :
    chartMatrixPhase (C.submatrix e.symm e.symm) (fun i => z (e.symm i)) (fun i => w (e.symm i)) =
      chartMatrixPhase C z w := by
  unfold chartMatrixPhase
  simp only [Matrix.submatrix_apply]
  exact (e.symm.sum_comp (fun i => ∑ j, z i * (C i (e.symm j) : ℝ) * w (e.symm j))).trans
    (Finset.sum_congr rfl fun i _ => e.symm.sum_comp (fun j => z i * (C i j : ℝ) * w j))

theorem chartAltForm_reindex {n m : ℕ} (e : Fin n ≃ Fin m) (C : Matrix (Fin n) (Fin n) ℚ)
    (z w : Fin n → ℝ) :
    chartAltForm (C.submatrix e.symm e.symm) (fun i => z (e.symm i)) (fun i => w (e.symm i)) =
      chartAltForm C z w := by
  simp only [chartAltForm, chartMatrixPhase_reindex]

/-- `eq:weyl-splitting` is invariant under reindexing the coordinates. -/
theorem WeylSplitData.reindex {B : ℝ} {n m : ℕ} (e : Fin n ≃ Fin m) {V : Matrix (Fin n) (Fin 1) ℝ}
    {C : Matrix (Fin n) (Fin n) ℚ} {Λ : Matrix (Fin 1) (Fin 1) ℝ} (h : WeylSplitData B V C Λ) :
    WeylSplitData B (V.submatrix e.symm id) (C.submatrix e.symm e.symm) Λ := by
  rw [weylSplitData_iff] at h ⊢
  obtain ⟨U, Q, h1, h2, h3, h4, h5, h6, h7⟩ := h
  set! P := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  have hP : ∀ x : EuclideanSpace ℝ (Fin n), (P x).ofLp = fun i => x.ofLp (e.symm i) := by
    intro x; funext i; simp [P, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]
  have hPs : ∀ x : EuclideanSpace ℝ (Fin m), (P.symm x).ofLp = fun i => x.ofLp (e i) := by
    intro x; funext i
    simp [P, LinearIsometryEquiv.piLpCongrLeft_symm, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft'_apply]
  set! U' := U.map (P.toLinearEquiv : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
  have hproj : ∀ x, U'.starProjection x = P (U.starProjection (P.symm x)) := fun x =>
    Submodule.starProjection_map_apply P U x
  -- the conjugated operators
  have hop : ∀ (A : Matrix (Fin n) (Fin n) ℚ) (x : EuclideanSpace ℝ (Fin m)),
      realMatrixOperator ((A.submatrix e.symm e.symm).map (fun q => (q : ℝ))) x =
        P (realMatrixOperator (A.map (fun q => (q : ℝ))) (P.symm x)) := by
    intro A x
    apply WithLp.ofLp_injective
    rw [realMatrixOperator_apply, hP, realMatrixOperator_apply, hPs]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.submatrix_apply]
    rw [← e.symm.sum_comp (fun j => (A (e.symm i) j : ℝ) * x.ofLp (e j))]
    simp only [Equiv.apply_symm_apply]
  have hv : (WithLp.toLp 2 fun i => (V.submatrix e.symm id) i 0 :
      EuclideanSpace ℝ (Fin m)) = P (WithLp.toLp 2 fun i => V i 0) := by
    apply WithLp.ofLp_injective
    rw [hP]; rfl
  have e1 : (1 - Q.submatrix e.symm e.symm) = (1 - Q).submatrix e.symm e.symm := by
    ext i j
    simp [Matrix.sub_apply, Matrix.one_apply]
  refine ⟨U', Q.submatrix e.symm e.symm, ?_, ?_, ?_, fun i j => h4 _ _, ?_, ?_, ?_⟩
  · ext1 x
    rw [hop, h1, Submodule.starProjection_orthogonal_val, Submodule.starProjection_orthogonal_val,
      hproj, map_sub, LinearIsometryEquiv.apply_symm_apply]
  · ext1 x
    rw [e1, hop, h2, hproj]
  · intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨y₀, hy₀, rfl⟩ := Submodule.mem_map.mp hy
    change chartAltForm _ (P y₀).ofLp (P x₀).ofLp = 0
    rw [hP, hP, chartAltForm_reindex]
    exact h3 x₀ hx₀ y₀ hy₀
  · intro i j
    rw [e1]; exact h5 _ _
  · rw [hv, Submodule.starProjection_orthogonal_val, hproj, LinearIsometryEquiv.symm_apply_apply,
      ← map_sub, LinearIsometryEquiv.norm_map, ← Submodule.starProjection_orthogonal_val]
    exact h6
  · rw [hv, hproj, LinearIsometryEquiv.symm_apply_apply, hP]
    have k1 := chartMatrixPhase_reindex e C (fun j => V j 0) (fun j => V j 0)
    have k2 := chartAltForm_reindex e C
      (fun j => (U.starProjection (WithLp.toLp 2 fun i => V i 0)).ofLp j) (fun j => V j 0)
    simp only [Matrix.submatrix_apply, id] at k1 k2 ⊢
    rw [k1, k2]
    exact h7

theorem chartAltForm_neg {d : ℕ} (C : Matrix (Fin d) (Fin d) ℚ) (z w : Fin d → ℝ) :
    chartAltForm (-C) z w = -chartAltForm C z w := by
  simp only [chartAltForm, chartMatrixPhase_neg]; ring

/-- `eq:weyl-splitting` is invariant under negating the matrix and the quadratic. -/
theorem WeylSplitData.neg {B : ℝ} {d : ℕ} {V : Matrix (Fin d) (Fin 1) ℝ}
    {C : Matrix (Fin d) (Fin d) ℚ} {Λ : Matrix (Fin 1) (Fin 1) ℝ} (h : WeylSplitData B V C Λ) :
    WeylSplitData B V (-C) (-Λ) := by
  rw [weylSplitData_iff] at h ⊢
  obtain ⟨U, Q, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨U, Q, h1, h2, fun x hx y hy => ?_, h4, h5, h6, ?_⟩
  · rw [chartAltForm_neg, h3 x hx y hy, neg_zero]
  · rw [Matrix.neg_apply, chartMatrixPhase_neg, chartAltForm_neg]
    have e : -Λ 0 0 + 1 / 2 * -chartMatrixPhase C (fun i => V i 0) (fun i => V i 0) +
        1 / 2 * -chartAltForm C (U.starProjection (WithLp.toLp 2 fun i => V i 0)).ofLp
          (fun i => V i 0) =
        -(Λ 0 0 + 1 / 2 * chartMatrixPhase C (fun i => V i 0) (fun i => V i 0) +
          1 / 2 * chartAltForm C (U.starProjection (WithLp.toLp 2 fun i => V i 0)).ofLp
            (fun i => V i 0)) := by ring
    rw [e, abs_neg]
    exact h7

/-- The block swap of the coordinates of a pair of tags. -/
def tagSwap (v w : ChartTag) : Fin (v.dim + w.dim) ≃ Fin (w.dim + v.dim) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm _ _).trans finSumFinEquiv)

/-- Blueprint lines 1682-1684: the edge relation of the tag graph is symmetric (swap the two
blocks and negate the difference matrix and quadratic). -/
theorem tagEdge_symm {B r : ℝ} {v w : ChartTag} (h : tagEdge B r v w) : tagEdge B r w v := by
  have hV : tagDiffV r w v = (tagDiffV r v w).submatrix (tagSwap v w).symm id := by
    ext i j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
      simp [tagDiffV, tagSwap, Fin.append_left, Fin.append_right]
  have hC : tagDiffC w v = -((tagDiffC v w).submatrix (tagSwap v w).symm (tagSwap v w).symm) := by
    ext i j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
      refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>
      simp [tagDiffC, tagSwap, chartBlockMatrix]
  have hΛ : tagDiffΛ r w v = -tagDiffΛ r v w := by
    ext i j; simp [tagDiffΛ]; ring
  unfold tagEdge at h ⊢
  rw [hV, hC, hΛ]
  exact (h.reindex (tagSwap v w)).neg

section GraphDistance
variable {V : Type*} (edge : ℤ → V → V → Prop)

/-! ### Graph distances of depth-dependent edge relations (blueprint lines 1682-1686) -/

/-- Walks of length `n` in the graph of `edge s`. -/
def reachIn (s : ℤ) : ℕ → V → V → Prop
  | 0, v, w => v = w
  | n + 1, v, w => ∃ u, reachIn s n v u ∧ edge s u w

/-- The graph distance at depth `s` (infinite without a connecting walk). -/
noncomputable def graphDist (s : ℤ) (v w : V) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : reachIn edge s n v w), (n : ℕ∞)

variable {edge}

theorem graphDist_le_of_reach {s : ℤ} {n : ℕ} {v w : V} (h : reachIn edge s n v w) :
    graphDist edge s v w ≤ n :=
  iInf₂_le n h

theorem reachIn_append {s : ℤ} {n m : ℕ} {u v w : V} (h₁ : reachIn edge s n u v)
    (h₂ : reachIn edge s m v w) : reachIn edge s (n + m) u w := by
  induction m generalizing w with
  | zero => simp only [reachIn] at h₂; subst h₂; simpa using h₁
  | succ m ih =>
    obtain ⟨x, hx, hxw⟩ := h₂
    exact ⟨x, ih hx, hxw⟩

theorem reachIn_succ_left {s : ℤ} {n : ℕ} {u v w : V} (h₁ : edge s u v)
    (h₂ : reachIn edge s n v w) : reachIn edge s (n + 1) u w := by
  have h₁' : reachIn edge s 1 u v := ⟨u, rfl, h₁⟩
  simpa [add_comm] using reachIn_append h₁' h₂

theorem reachIn_symm (hsymm : ∀ s v w, edge s v w → edge s w v) {s : ℤ} {n : ℕ} {v w : V}
    (h : reachIn edge s n v w) : reachIn edge s n w v := by
  induction n generalizing w with
  | zero => exact (h : v = w).symm
  | succ n ih =>
    obtain ⟨u, hu, huw⟩ := h
    exact reachIn_succ_left (hsymm s u w huw) (ih hu)

theorem reachIn_mono (hmono : ∀ {s s'}, s ≤ s' → ∀ v w, edge s v w → edge s' v w)
    {s s' : ℤ} (hss : s ≤ s') {n : ℕ} {v w : V} (h : reachIn edge s n v w) :
    reachIn edge s' n v w := by
  induction n generalizing w with
  | zero => exact h
  | succ n ih =>
    obtain ⟨u, hu, huw⟩ := h
    exact ⟨u, ih hu, hmono hss u w huw⟩

/-- A finite graph distance is attained by a walk. -/
theorem exists_reachIn_of_graphDist_eq {s : ℤ} {v w : V} {k : ℕ}
    (h : graphDist edge s v w = k) : reachIn edge s k v w := by
  classical
  by_contra hk
  have hne : ∃ n, reachIn edge s n v w := by
    by_contra hno
    push Not at hno
    have : graphDist edge s v w = ⊤ := by
      unfold graphDist
      simp only [iInf_eq_top]
      intro n hn; exact absurd hn (hno n)
    rw [this] at h; exact ENat.top_ne_natCast k h
  set n₀ := Nat.find hne
  have hn₀ : reachIn edge s n₀ v w := Nat.find_spec hne
  have hle : graphDist edge s v w ≤ n₀ := graphDist_le_of_reach hn₀
  have hge : (n₀ : ℕ∞) ≤ graphDist edge s v w := by
    unfold graphDist
    refine le_iInf₂ fun n hn => ?_
    exact_mod_cast Nat.find_min' hne hn
  have heq : graphDist edge s v w = n₀ := le_antisymm hle hge
  rw [heq] at h
  have : n₀ = k := by exact_mod_cast h
  exact hk (this ▸ hn₀)

/-- The depth distance of a symmetric edge relation that persists under refinement. -/
noncomputable def DepthDistance.ofEdges (edge : ℤ → V → V → Prop)
    (hsymm : ∀ s v w, edge s v w → edge s w v)
    (hmono : ∀ {s s'}, s ≤ s' → ∀ v w, edge s v w → edge s' v w) : DepthDistance V where
  d := graphDist edge
  self := fun s v => le_antisymm (graphDist_le_of_reach (n := 0) rfl) zero_le
  symm := fun s v w => le_antisymm
    (le_iInf₂ fun n hn => graphDist_le_of_reach (reachIn_symm hsymm hn))
    (le_iInf₂ fun n hn => graphDist_le_of_reach (reachIn_symm hsymm hn))
  triangle := fun s u v w => by
    rcases eq_top_or_lt_top (graphDist edge s u v) with h₁ | h₁
    · rw [h₁, top_add]; exact le_top
    rcases eq_top_or_lt_top (graphDist edge s v w) with h₂ | h₂
    · rw [h₂, add_top]; exact le_top
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp h₁.ne
    obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp h₂.ne
    have r₁ := exists_reachIn_of_graphDist_eq ha.symm
    have r₂ := exists_reachIn_of_graphDist_eq hb.symm
    rw [← ha, ← hb]
    exact_mod_cast graphDist_le_of_reach (reachIn_append r₁ r₂)
  anti := fun {s s'} hss v w =>
    le_iInf₂ fun n hn => graphDist_le_of_reach (reachIn_mono hmono hss hn)

theorem graphDist_le_one_of_edge {s : ℤ} {v w : V} (h : edge s v w) : graphDist edge s v w ≤ 1 :=
  graphDist_le_of_reach (n := 1) ⟨v, rfl, h⟩

end GraphDistance

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

/-! ### Binary split trees -/

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

/-- The physical coordinate of an augmented vector is measurable. -/
theorem columnPhys_measurable {V : Type*} [Fintype V] (x : ColumnL2 V) :
    Measurable fun y => (x : ℝ → ColumnHilbert V) y none := by
  have hev : Continuous fun x : ColumnHilbert V => x.ofLp none :=
    (continuous_apply none).comp (PiLp.continuous_ofLp 2 _)
  exact hev.measurable.comp (Lp.stronglyMeasurable _).measurable

theorem columnPhys_memLp_normalized {V : Type*} [Fintype V] (x : ColumnL2 V) (a₀ r : ℝ) :
    MemLp (fun y => (x : ℝ → ColumnHilbert V) y none) 2 (normalizedIntervalMeasure a₀ r) :=
  ((memLp_column_coord x none).restrict _).smul_measure ENNReal.ofReal_ne_top

/-! ### The cell form on augmented inputs -/

/-- The progression coordinates pull null sets back to null sets of the plane. -/
theorem realProgressionCoordinate_preimage_null (j : Fin 4) {N : Set ℝ} (hN : volume N = 0) :
    (volume : Measure (ℝ × ℝ)) (realProgressionCoordinate j ⁻¹' N) = 0 := by
  obtain ⟨N', hNN', hN'm, hN'0⟩ := exists_measurable_superset_of_null hN
  refine measure_mono_null (Set.preimage_mono hNN') ?_
  have hm : MeasurableSet (realProgressionCoordinate j ⁻¹' N') :=
    (continuous_realProgressionCoordinate j).measurable hN'm
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hm]
  by_cases hj : (j : ℝ) = 0
  · -- the slice is all of `ℝ` over `N'` and empty elsewhere
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hN'0] with x hx
    have : Prod.mk x ⁻¹' (realProgressionCoordinate j ⁻¹' N') = ∅ := by
      ext t
      simp only [Set.mem_preimage, realProgressionCoordinate, hj, zero_mul, add_zero,
        Set.mem_empty_iff_false, iff_false]
      exact hx
    simp only [this, measure_empty, Pi.zero_apply]
  · refine Filter.Eventually.of_forall fun x => ?_
    have : Prod.mk x ⁻¹' (realProgressionCoordinate j ⁻¹' N') =
        (fun t => (j : ℝ) * t) ⁻¹' ((fun u => u + x) ⁻¹' N') := by
      ext t
      simp only [Set.mem_preimage, realProgressionCoordinate]
      rw [add_comm]
    change volume (Prod.mk x ⁻¹' (realProgressionCoordinate j ⁻¹' N')) = 0
    rw [this, Real.volume_preimage_mul_left hj, measure_preimage_add_right]
    simp [hN'0]

/-- The local form depends only on the almost-everywhere classes of its inputs. -/
theorem localProgressionForm_congr_ae (r : ℝ) (w : ℝ × ℝ → ℂ) {f g : Fin 4 → ℝ → ℂ}
    (h : ∀ j, f j =ᵐ[volume] g j) : localProgressionForm r w f = localProgressionForm r w g := by
  unfold localProgressionForm
  congr 1
  refine integral_congr_ae ?_
  have hj : ∀ j, ∀ᵐ z : ℝ × ℝ ∂volume,
      f j (realProgressionCoordinate j z) = g j (realProgressionCoordinate j z) := by
    intro j
    have hN := (h j)
    rw [Filter.EventuallyEq, ae_iff] at hN
    rw [ae_iff]
    exact realProgressionCoordinate_preimage_null j hN
  filter_upwards [ae_all_iff.mpr hj] with z hz
  simp only [hz]

/-- The physical coordinate of an augmented vector. -/
noncomputable def augPhys {V : Type*} [Fintype V] (x : ColumnL2 V) : ℝ → ℂ :=
  fun y => (x : ℝ → ColumnHilbert V) y none

theorem augPhys_add {V : Type*} [Fintype V] (x x' : ColumnL2 V) :
    augPhys (x + x') =ᵐ[volume] augPhys x + augPhys x' := by
  filter_upwards [Lp.coeFn_add x x'] with y hy
  simp only [augPhys, hy, Pi.add_apply, PiLp.add_apply]

theorem augPhys_smul {V : Type*} [Fintype V] (c : ℂ) (x : ColumnL2 V) :
    augPhys (c • x) =ᵐ[volume] c • augPhys x := by
  filter_upwards [Lp.coeFn_smul c x] with y hy
  simp only [augPhys, hy, Pi.smul_apply, PiLp.smul_apply]

theorem apply_update_augPhys {V : Type*} [Fintype V] (x : Fin 4 → ColumnL2 V) (k : Fin 4)
    (a : ColumnL2 V) (l : Fin 4) :
    augPhys (Function.update x k a l) = Function.update (fun l => augPhys (x l)) k (augPhys a) l :=
  by by_cases h : l = k <;> simp [Function.update, h]

/-- Blueprint eq:local on a cell, as a multilinear form on augmented inputs (only physical
coordinates enter). -/
noncomputable def cellForm {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r) {w : ℝ × ℝ → ℂ}
    (hw : IsAdmissibleLocalKernel κ a₀ r w) (V : Type*) [Fintype V] :
    MultilinearMap ℂ (fun _ : Fin 4 => ColumnL2 V) ℂ where
  toFun x := localProgressionForm r w (fun l => augPhys (x l))
  map_update_add' := by
    intro inst x k a b
    obtain rfl : inst = instDecidableEqFin 4 := Subsingleton.elim _ _
    have hm : ∀ l, Measurable (augPhys (x l)) := fun l => columnPhys_measurable (x l)
    have hfin : ∀ l, eLpNorm (augPhys (x l)) 2 (normalizedIntervalMeasure a₀ r) ≠ ⊤ :=
      fun l => (columnPhys_memLp_normalized (x l) a₀ r).eLpNorm_ne_top
    have e : localProgressionForm r w (fun l => augPhys (Function.update x k (a + b) l)) =
        localProgressionForm r w
          (Function.update (fun l => augPhys (x l)) k (augPhys a + augPhys b)) := by
      refine localProgressionForm_congr_ae r w fun l => ?_
      rw [apply_update_augPhys]
      by_cases h : l = k
      · subst h; simp only [Function.update_self]; exact augPhys_add a b
      · simp only [Function.update_of_ne h]; rfl
    have hadd := localProgressionForm_update_add_two (g₁ := augPhys a) (g₂ := augPhys b) hr hw
      hm hfin k (columnPhys_measurable a) (columnPhys_measurable b)
      (columnPhys_memLp_normalized a a₀ r).eLpNorm_ne_top
      (columnPhys_memLp_normalized b a₀ r).eLpNorm_ne_top
    rw [e, hadd]
    congr 1
    · congr 1; funext l; rw [apply_update_augPhys]
    · congr 1; funext l; rw [apply_update_augPhys]
  map_update_smul' := by
    intro inst x k c a
    obtain rfl : inst = instDecidableEqFin 4 := Subsingleton.elim _ _
    have e : localProgressionForm r w (fun l => augPhys (Function.update x k (c • a) l)) =
        localProgressionForm r w (Function.update (fun l => augPhys (x l)) k (c • augPhys a)) := by
      refine localProgressionForm_congr_ae r w fun l => ?_
      rw [apply_update_augPhys]
      by_cases h : l = k
      · subst h; simp only [Function.update_self]; exact augPhys_smul c a
      · simp only [Function.update_of_ne h]; rfl
    rw [e, localProgressionForm_update_const_smul, smul_eq_mul]
    congr 2
    funext l; rw [apply_update_augPhys]

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

/-! ### Equal tags are joined (blueprint line 1684: the tag graph contains equal tags) -/

/-- The folding of the doubled coordinates. -/
def foldIdx (d : ℕ) : Fin (d + d) → Fin d := Fin.addCases (motive := fun _ => Fin d) id id

/-- Column functions supported on pairwise disjoint sets are orthogonal: the squared norm of
their sum is the sum of squared norms. -/
theorem columnL2_norm_sq_sum_disjoint {V ι : Type*} [Fintype V] (s : Finset ι)
    (v : ι → ColumnL2 V) (J : ι → Set ℝ) (hJ : Set.PairwiseDisjoint (s : Set ι) J)
    (hv : ∀ i, ∀ᵐ y ∂volume, y ∉ J i → (v i : ℝ → ColumnHilbert V) y = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  have horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℂ (v i) (v j) = 0 := by
    intro i hi j hj hij
    rw [L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hv i, hv j] with y h1 h2
    by_cases hy : y ∈ J i
    · have : y ∉ J j := fun hyj => Set.disjoint_left.mp (hJ hi hj hij) hy hyj
      rw [h2 this, inner_zero_right]; rfl
    · rw [h1 hy, inner_zero_left]; rfl
  clear hv hJ
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h0 : inner ℂ (v a) (∑ i ∈ s, v i) = 0 := by
      rw [inner_sum]
      exact Finset.sum_eq_zero fun j hj => horth a (Finset.mem_insert_self a s) j
        (Finset.mem_insert_of_mem hj) (fun h => ha (h ▸ hj))
    rw [← ih fun i hi j hj hij =>
      horth i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij]
    simp only [sq]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

section RestrictionUnions
variable {V : Type*} [Fintype V]

/-- The restriction to a finite disjoint union of cells is the sum of the cell restrictions. -/
theorem columnL2Restriction_biUnion {κ : Type*} (S : Finset κ) (J : κ → Set ℝ)
    (hJ : ∀ i, MeasurableSet (J i)) (hdis : Set.PairwiseDisjoint (S : Set κ) J) :
    columnL2Restriction (V := V) (⋃ i ∈ S, J i)
        (Finset.measurableSet_biUnion S fun i _ => hJ i) =
      ∑ i ∈ S, columnL2Restriction (J i) (hJ i) := by
  refine ContinuousLinearMap.ext fun w => Lp.ext ?_
  rw [sum_apply]
  change (columnL2Indicator _ (Finset.measurableSet_biUnion S fun i _ => hJ i) w :
    ℝ → ColumnHilbert V) =ᵐ[volume] _
  have hall : ∀ᵐ y ∂volume, ∀ i ∈ S, (columnL2Restriction (J i) (hJ i) w :
      ℝ → ColumnHilbert V) y = (J i).indicator (w : ℝ → ColumnHilbert V) y := by
    rw [Filter.eventually_all_finset]
    exact fun i _ => columnL2Indicator_coeFn _ (hJ i) w
  filter_upwards [columnL2Indicator_coeFn _ (Finset.measurableSet_biUnion S fun i _ => hJ i) w,
    hall, Lp.coeFn_fun_finsetSum S (fun i => columnL2Restriction (J i) (hJ i) w)]
    with y h1 h2 h3
  rw [h1, h3, Finset.sum_congr rfl h2, Finset.indicator_biUnion_apply _ _ hdis]

end RestrictionUnions

/-- Squared restrictions to disjoint cells add up to at most the squared norm. -/
theorem sum_norm_sq_restrict_le {V : Type*} [Fintype V] (Gd : RealDyadicGrid)
    (C : Finset (ℤ × ℤ))
    (hC : Set.PairwiseDisjoint (C : Set (ℤ × ℤ)) fun I => dyadicGridCell Gd I.1 I.2)
    (v : ColumnL2 V) :
    ∑ I ∈ C, ‖columnL2Restriction (dyadicGridCell Gd I.1 I.2)
      (dyadicGridCell_measurable Gd I.1 I.2) v‖ ^ 2 =
      ‖columnL2Restriction (⋃ I ∈ C, dyadicGridCell Gd I.1 I.2)
        (Finset.measurableSet_biUnion C fun I _ => dyadicGridCell_measurable Gd I.1 I.2) v‖ ^ 2 :=
      by
  rw [columnL2Restriction_biUnion C (fun I => dyadicGridCell Gd I.1 I.2)
    (fun I => dyadicGridCell_measurable Gd I.1 I.2) hC, sum_apply]
  refine (columnL2_norm_sq_sum_disjoint C _ (fun I => dyadicGridCell Gd I.1 I.2) hC
    fun I => ?_).symm
  filter_upwards [columnL2Indicator_coeFn _ (dyadicGridCell_measurable Gd I.1 I.2) v]
    with y hy hyI
  change (columnL2Indicator _ (dyadicGridCell_measurable Gd I.1 I.2) v :
    ℝ → ColumnHilbert V) y = 0
  rw [hy, Set.indicator_of_notMem hyI]

open Classical in
/-- Path caps integrate to square budgets: `Σ_{I ∋ x} a_I ≤ C` everywhere gives
`Σ_I |I| a_I ≤ C |R|` (blueprint `eq:path`). -/
theorem integrated_cap_le (G : RealDyadicGrid) (S : Finset (ℤ × ℤ)) (a : ℤ × ℤ → ℝ)
    (root : ℤ × ℤ) (hR : ∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G root.1 root.2)
    {C : ℝ} (hC : ∀ x, ∑ I ∈ S.filter (fun I => x ∈ dyadicGridCell G I.1 I.2), a I ≤ C) :
    ∑ I ∈ S, dyadicGridLength G I.1 * a I ≤ C * dyadicGridLength G root.1 := by
  set f : ℝ → ℝ := fun x => ∑ I ∈ S, (dyadicGridCell G I.1 I.2).indicator (fun _ => a I) x
  rw [dyadicPathIntegral_real G S _ (dyadicGridCell G root.1 root.2) hR]
  have hpt : ∀ x, f x ≤ C := by
    intro x
    have hfx : f x = ∑ I ∈ S.filter (fun I => x ∈ dyadicGridCell G I.1 I.2), a I := by
      simp only [f, Finset.sum_filter, Set.indicator_apply]
    rw [hfx]; exact hC x
  have hint : IntegrableOn f (dyadicGridCell G root.1 root.2) := by
    refine integrable_finsetSum _ fun I hI => ?_
    apply (integrable_indicator_iff (dyadicGridCell_measurable G I.1 I.2)).mpr
    change Integrable _ ((volume.restrict _).restrict (dyadicGridCell G I.1 I.2))
    rw [Measure.restrict_restrict_of_subset (hR I hI)]
    exact integrableOn_const (by rw [dyadicGridCell_volume]; exact ENNReal.ofReal_ne_top)
  calc ∫ x in dyadicGridCell G root.1 root.2, f x ≤ ∫ _x in dyadicGridCell G root.1 root.2, C :=
        setIntegral_mono_on hint (integrableOn_const (by
          rw [dyadicGridCell_volume]; exact ENNReal.ofReal_ne_top))
          (dyadicGridCell_measurable G root.1 root.2) fun x _ => hpt x
    _ = _ := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, dyadicGridCell_volume,
          ENNReal.toReal_ofReal (dyadicGridLength_pos G root.1).le]
        ring

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

namespace ActiveSetup
variable {κ' : LocalKernelClass} {c₀ : ℕ} (A : ActiveSetup κ' c₀)

/-- The `L²` energy of a basic side on a cell is its length times its normalized square norm. -/
theorem U_cell_energy (l : Fin 4) (I : ℤ × ℤ) :
    ∫ y in dyadicGridCell A.G I.1 I.2, ‖A.U l I y‖ ^ 2 =
      dyadicGridLength A.G I.1 * (eLpNorm (A.U l I) 2 (A.μ I)).toReal ^ 2 := by
  have hr := dyadicGridLength_pos A.G I.1
  rw [eLpNorm_normalized_toReal_sq hr (A.U_L2 l I), ← mul_assoc, mul_inv_cancel₀ hr.ne',
    one_mul]
  rfl

end ActiveSetup

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

/-! ### Basic leaf inputs as differences of current projections (blueprint line 1611) -/

end TrilinearHT.Auto

end
