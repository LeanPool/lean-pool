/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Global.ScalarLemmas

/-!
# High-contrast homogenization: Entry.Multiscale.Global.FiniteRun

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The generic finite run and the projective metric

The generic stopping and telescoping facts for a potential with a per-step charge
(`p.global.selection`, `e.global.selection.count`), the elementary identities of
`detIncrement` and `synchCharge`, and the projective-metric layer
(`e.scale.selection.canonical.metric`, `e.global.selection.metric.loss`,
`e.global.selection.metric.comparison`): positive definiteness of the canonical metric,
symmetry and the triangle inequality, and the two canonical-metric comparisons
(log-determinant and Loewner sandwich).
-/

open HCPolySupport.HighContrast (blockLogDet blockScale specBound specBound_le specBound_nonneg)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## §B Generic finite run (`p.global.selection`) -/

/-- `e.global.selection.count`-`p.global.selection`, abstract: a nonnegative potential decreasing
by `c` per continuing step up to
a charge whose running sum is bounded by `Bud` stops within `⌈(Φ 0 + Bud)/c⌉₊` steps. -/
theorem exists_stop_of_potential (Φ charge : ℕ → ℝ) (stop : ℕ → Prop) (c Bud : ℝ) (hc : 0 < c)
    (hΦ : ∀ i, 0 ≤ Φ i)
    (hstep : ∀ i, (∀ j, j ≤ i → ¬ stop j) → Φ (i + 1) - Φ i ≤ -c + charge i)
    (hbud : ∀ M, (∀ j, j < M → ¬ stop j) → ∑ i ∈ Finset.range M, charge i ≤ Bud) :
    ∃ i, i ≤ ⌈(Φ 0 + Bud) / c⌉₊ ∧ stop i := by
  by_contra hcon
  push Not at hcon
  set M₀ := ⌈(Φ 0 + Bud) / c⌉₊ with hM₀def
  have key : ∀ M, M ≤ M₀ + 1 → Φ M ≤ Φ 0 - c * M + ∑ i ∈ Finset.range M, charge i := by
    intro M
    induction M with
    | zero =>
        intro _
        simp only [Nat.cast_zero, mul_zero, sub_zero, Finset.sum_range_zero, add_zero, le_refl]
    | succ n ih =>
        intro hn
        have hnle : n ≤ M₀ := Nat.le_of_succ_le_succ hn
        have hn1 : n ≤ M₀ + 1 := le_trans hnle (Nat.le_succ M₀)
        have ihn := ih hn1
        have hstepn : Φ (n + 1) - Φ n ≤ -c + charge n := by
          apply hstep
          intro j hj
          exact hcon j (le_trans hj hnle)
        have hcast : c * ((n : ℝ) + 1) = c * (n : ℝ) + c := by ring
        rw [Finset.sum_range_succ]
        push_cast
        linarith only [ihn, hstepn, hcast]
  have hkey' := key (M₀ + 1) (le_refl _)
  have hbudget : ∑ i ∈ Finset.range (M₀ + 1), charge i ≤ Bud := by
    apply hbud
    intro j hj
    exact hcon j (by omega)
  have hnonneg : 0 ≤ Φ (M₀ + 1) := hΦ (M₀ + 1)
  have hle : (Φ 0 + Bud) / c ≤ (M₀ : ℝ) := by
    rw [hM₀def]
    exact Nat.le_ceil _
  rw [div_le_iff₀ hc] at hle
  push_cast at hkey'
  have hcast2 : c * ((M₀ : ℝ) + 1) = c * (M₀ : ℝ) + c := by ring
  have hcomm : c * (M₀ : ℝ) = (M₀ : ℝ) * c := by ring
  linarith only [hkey', hbudget, hnonneg, hle, hcast2, hcomm, hc]

/-! ## §C Matrix geometry (`p.global.selection`) -/

/-- `explicitCanonicalMetric F` is positive definite for a symmetric positive block `F`
(`e.scale.selection.canonical.metric`); specialises
`Geometry.explicitCanonicalMetric_posDef`, trivial for `d = 0`. -/
theorem explicitCanonicalMetric_posDef {d : ℕ} (F : BlockMat d) (hFs : IsSymmetricBlockMat F)
    (hF : Book.Ch02.BlockPosDef F) : (explicitCanonicalMetric F).PosDef := by
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · subst h0
    refine ⟨Subsingleton.elim _ _, ?_⟩
    intro x hx
    exact absurd (Subsingleton.elim x 0) hx
  · have : NeZero d := ⟨hpos.ne'⟩
    exact HCPolySupport.HighContrast.Geometry.explicitCanonicalMetric_posDef hFs hF

/-- Triangle inequality for `projectiveDistance` on positive definite matrices
(`p.global.selection`). -/
theorem projectiveDistance_triangle {d : ℕ} (m₀ m₁ m₂ : Mat d) (h₀ : m₀.PosDef) (h₁ : m₁.PosDef)
    (h₂ : m₂.PosDef) :
    projectiveDistance m₀ m₂ ≤ projectiveDistance m₀ m₁ + projectiveDistance m₁ m₂ := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have e1 : m₀ = m₁ := Subsingleton.elim _ _
    have e2 : m₁ = m₂ := Subsingleton.elim _ _
    subst e1
    subst e2
    have hconst : ∀ (t : ℝ) (A : Mat 0), t • A = A := fun t A => Subsingleton.elim _ _
    have hgen : ∀ (Q : Prop), sInf {t : ℝ | 0 ≤ t ∧ Q} = 0 := by
      intro Q
      rcases Classical.em Q with hQ | hQ
      · have hset : {t : ℝ | 0 ≤ t ∧ Q} = Set.Ici (0 : ℝ) := by
          ext t
          simp [hQ]
        rw [hset]
        apply le_antisymm
        · exact csInf_le ⟨0, fun x hx => hx⟩ (le_refl (0 : ℝ))
        · exact le_csInf ⟨0, le_refl (0 : ℝ)⟩ (fun x hx => hx)
      · have hset : {t : ℝ | 0 ≤ t ∧ Q} = (∅ : Set ℝ) := by
          ext t
          simp [hQ]
        rw [hset]
        exact Real.sInf_empty
    have hval : HCPolySupport.HighContrast.projectiveDistance m₀ m₀ = 0 := by
      simp [HCPolySupport.HighContrast.projectiveDistance, HCPolySupport.HighContrast.specBound,
        HCPolySupport.HighContrast.specMin, HCPolySupport.HighContrast.normalizedMat, hconst, hgen,
        Real.log_zero]
    linarith only [hval]
  · have : NeZero d := ⟨hd.ne'⟩
    exact HCPolySupport.HighContrast.Geometry.projectiveDistance_triangle h₀ h₁ h₂

/-- `e.global.selection.metric.loss`: for positive blocks `G ≤ F`,
`d_pr([m(F)],[m(G)]) ≤ ½ log (det F / det G)`. Monotonicity and homogeneity of the matrix
geometric mean in `explicitCanonicalMetric`, and the `2d` eigenvalues of `G^{-1/2} F G^{-1/2}`. -/
theorem explicitCanonicalMetric_projectiveDistance_le_logDet {d : ℕ} (F G : BlockMat d)
    (hFs : IsSymmetricBlockMat F) (hF : Book.Ch02.BlockPosDef F)
    (hGs : IsSymmetricBlockMat G) (hG : Book.Ch02.BlockPosDef G) (hGF : BlockMatLoewnerLE G F) :
    projectiveDistance (explicitCanonicalMetric F) (explicitCanonicalMetric G) ≤
      1 / 2 * (blockLogDet F - blockLogDet G) := by
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    have htriv : ∀ A B : Mat 0, MatLoewnerLE A B := by
      intro A B x
      simp [vecDot]
    have hb : specBound (normalizedMat (explicitCanonicalMetric F) (explicitCanonicalMetric G)) = 0 :=
      le_antisymm (specBound_le le_rfl (htriv _ _)) (specBound_nonneg _)
    have hs : specMin (normalizedMat (explicitCanonicalMetric F) (explicitCanonicalMetric G)) = 0 := by
      have hset : {t : ℝ | MatLoewnerLE (t • (1 : Mat 0))
          (normalizedMat (explicitCanonicalMetric F) (explicitCanonicalMetric G))} = Set.univ :=
        Set.eq_univ_of_forall fun t => htriv _ _
      simp only [specMin, hset, Real.sSup_univ]
    have hpd : projectiveDistance (explicitCanonicalMetric F) (explicitCanonicalMetric G) = 0 := by
      simp only [projectiveDistance, hb, hs]
      norm_num
    have : IsEmpty (BlockCoord 0) :=
      ⟨fun x => Sum.elim (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0) x⟩
    have hdetF : blockLogDet F = 0 := by
      simp only [blockLogDet, Matrix.det_isEmpty, Real.log_one]
    have hdetG : blockLogDet G = 0 := by
      simp only [blockLogDet, Matrix.det_isEmpty, Real.log_one]
    rw [hpd, hdetF, hdetG]
    norm_num
  · have : NeZero d := ⟨hdpos.ne'⟩
    obtain ⟨hhi, hloss⟩ :=
      BlockGeometricMean.explicitCanonicalMetric_projectiveDistance_le_logDet_aux_upper F G hFs hF hGs hG hGF
    have hκ1 : (1 : ℝ) ≤ Real.exp (blockLogDet F - blockLogDet G) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr hloss
    have hlo : BlockMatLoewnerLE (blockScale (1 : ℝ) G) F :=
      BlockGeometricMean.explicitCanonicalMetric_projectiveDistance_le_logDet_aux_scale_one_le G F hGs hG hFs hF hGF
    have hhi' : BlockMatLoewnerLE F
        (blockScale (Real.exp (blockLogDet F - blockLogDet G) * 1) G) := by
      rw [mul_one]
      exact hhi
    have hmain := BlockGeometricMean.sandwich F G
      hFs hF hGs hG 1 (Real.exp (blockLogDet F - blockLogDet G)) zero_lt_one hκ1 hlo hhi'
    rwa [Real.log_exp] at hmain

/-- `e.global.selection.metric.comparison`: a `δ`-sandwich moves the canonical metric by
at most `½ log((1+δ)/(1-δ))`; same statement as
`explicitCanonicalMetric_projectiveDistance_le_of_sandwich`
in `HCPoly/Entry/InitialFixedGridScale.lean`, proved here from `BlockGeometricMean.sandwich`. -/
theorem explicitCanonicalMetric_projectiveDistance_le_of_deltaSandwich {d : ℕ} (F G : BlockMat d) (δ : ℝ)
    (hδ : δ ∈ Set.Ico (0 : ℝ) 1) (hFs : IsSymmetricBlockMat F) (hF : Book.Ch02.BlockPosDef F)
    (hGs : IsSymmetricBlockMat G) (hG : Book.Ch02.BlockPosDef G)
    (h₁ : BlockMatLoewnerLE (blockScale (1 - δ) F) G) (h₂ : BlockMatLoewnerLE G (blockScale (1 + δ) F)) :
    projectiveDistance (explicitCanonicalMetric F) (explicitCanonicalMetric G) ≤
      1 / 2 * Real.log ((1 + δ) / (1 - δ)) := by
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hcpos : (0:ℝ) < 1 - δ := by linarith only [hδ0, hδ1]
  have hκ1 : (1:ℝ) ≤ (1 + δ) / (1 - δ) := by
    rw [le_div_iff₀ hcpos]; linarith only [hδ0]
  have hlog : 0 ≤ 1 / 2 * Real.log ((1 + δ) / (1 - δ)) := by
    have h := Real.log_nonneg hκ1
    linarith only [h]
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    have htriv : ∀ A B : Mat 0, MatLoewnerLE A B := by
      intro A B x
      simp [vecDot]
    have hb : specBound (normalizedMat (explicitCanonicalMetric F) (explicitCanonicalMetric G)) = 0 :=
      le_antisymm (specBound_le le_rfl (htriv _ _)) (specBound_nonneg _)
    have hs : specMin (normalizedMat (explicitCanonicalMetric F) (explicitCanonicalMetric G)) = 0 := by
      have hset : {t : ℝ | MatLoewnerLE (t • (1 : Mat 0))
          (normalizedMat (explicitCanonicalMetric F) (explicitCanonicalMetric G))} = Set.univ :=
        Set.eq_univ_of_forall fun t => htriv _ _
      simp only [specMin, hset, Real.sSup_univ]
    have hpd : projectiveDistance (explicitCanonicalMetric F) (explicitCanonicalMetric G) = 0 := by
      simp only [projectiveDistance, hb, hs]
      norm_num
    rw [hpd]
    exact hlog
  · have : NeZero d := ⟨hdpos.ne'⟩
    have hmul : (1 + δ) / (1 - δ) * (1 - δ) = 1 + δ := by field_simp
    have h := BlockGeometricMean.sandwich G F hGs hG hFs hF
      (1 - δ) ((1 + δ) / (1 - δ)) hcpos hκ1 h₁ (by rw [hmul]; exact h₂)
    rwa [Geometry.projectiveDistance_symm (Geometry.explicitCanonicalMetric_posDef hGs hG)
      (Geometry.explicitCanonicalMetric_posDef hFs hF)] at h

/-- `p.global.selection`: `G ≤ (1+δ) F` raises the log-determinant by at most `2d log(1+δ)`. -/
theorem blockLogDet_le_of_sandwich {d : ℕ} (F G : BlockMat d) (δ : ℝ) (hδ : 0 ≤ δ)
    (hFs : IsSymmetricBlockMat F) (hF : Book.Ch02.BlockPosDef F)
    (hGs : IsSymmetricBlockMat G) (hG : Book.Ch02.BlockPosDef G)
    (h₂ : BlockMatLoewnerLE G (blockScale (1 + δ) F)) :
    blockLogDet G ≤ blockLogDet F + 2 * (d : ℝ) * Real.log (1 + δ) := by
  have hc : (0 : ℝ) < 1 + δ := by linarith only [hδ]
  have hFfull : (toFullBlockMat F).PosDef := posDef_toFullBlockMat hFs hF
  have hGfull : (toFullBlockMat G).PosDef := posDef_toFullBlockMat hGs hG
  have hscale : toFullBlockMat (blockScale (1 + δ) F) = (1 + δ) • toFullBlockMat F :=
    HCPolySupport.HighContrast.toFullBlockMat_blockScale _ _
  have hSfull : (toFullBlockMat (blockScale (1 + δ) F)).PosDef := by
    rw [hscale]
    exact hFfull.smul hc
  have hstep := (Annealed.normalizedBlock_order_consequences 0 (blockScale (1 + δ) F) G
    hSfull hGfull h₂).2.1
  have hdetF : 0 < (toFullBlockMat F).det := hFfull.det_pos
  have hkey : blockLogDet (blockScale (1 + δ) F)
      = blockLogDet F + 2 * (d : ℝ) * Real.log (1 + δ) := by
    simp only [blockLogDet]
    rw [hscale, Matrix.det_smul,
      Real.log_mul (pow_ne_zero _ (ne_of_gt hc)) (ne_of_gt hdetF), Real.log_pow]
    simp only [Fintype.card_sum, Fintype.card_fin]
    push_cast
    ring
  rw [hkey] at hstep
  linarith only [hstep]

end

end HCPolySupport.HighContrast.Multiscale
