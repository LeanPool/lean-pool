/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec112bFiniteBaseDataPairs.Setup

/-!
# Trilinear Hilbert transform: lowDelayedReplacement
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

open scoped Classical in
private def LowDelayedReplacementHpairStatement : Prop :=
  ∀ (κ : LocalKernelClass)
    (a : Fin (4 : ℕ))
    (i : Fin (4 : ℕ))
    (k : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (_ : a ≠ i)
    (_ : a ≠ k)
    (_ : a ≠ b)
    (_ : i ≠ k)
    (_ : i ≠ b)
    (_ : k ≠ b)
    (B : ℝ)
    (Dl : ℝ)
    (ε : ℝ)
    (_ : (0 : ℝ) ≤ Dl)
    (G : RealDyadicGrid)
    (J : ℤ × ℤ)
    (N : ℕ)
    (V : Type)
    [Fintype V]
    (P : PathColumnSystem G J N V)
    (R : ℤ × ℤ)
    (hR : R ∈ dyadicFiniteTree G J N)
    (c₀ : ℕ)
    (H : ℝ)
    (Xi : LowList G J N R c₀ H)
    (Xk : LowList G J N R c₀ H)
    (_ : ∀ (I : ℤ × ℤ) (li : Xi.Λ) (lk : Xk.Λ), Xi.coef I li ≠ (0 : ℂ) → Xk.coef I lk ≠ (0 :
      ℂ) → PredictorCover κ P a i k b B Dl ε (Xi.chart (Xi.birth I li) li) (Xk.chart
      (Xk.birth I lk) lk) (jointBirth Xi Xk I li lk))
    (f : ↥(Lp ℂ (2 : ℝ≥0∞) volume))
    (K₀ : ℕ)
    (S : Finset (ℤ × ℤ))
    (_ : ∀ I ∈ S, I ∈ pathBelow G J N R)
    (_ : ∀ I ∈ S, I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ))
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (_ : ∀ I ∈ S, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G
      I.1) (w I))
    (Fb : ℝ → ℂ)
    (zb : ℤ × ℤ → ℝ → ℂ)
    (Kb : ℝ)
    (_ : (0 : ℝ) ≤ Kb)
    (_ : ∀ J' ∈ dyadicFiniteTree G J N, dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2
      → IsAdmissibleOpponent G J' Fb zb Kb ∧ HasDepthEnergy G J' Fb zb Kb)
    (_ : ∀ (I : ℤ × ℤ), Measurable (zb I))
    (_ : ∀ (I : ℤ × ℤ), MemLp (zb I) (2 : ℝ≥0∞) (volume.restrict (dyadicGridCell G I.1 I.2)))
    (_ : IntegrableOn (fun (y : ℝ) => ‖Fb y‖ ^ (2 : ℕ)) (dyadicGridCell G R.1 R.2) volume),
  let Err : ℝ :=
    (2 : ℝ) * Real.exp (-B) * ((2 : ℝ) * (compressionOneConst (P.rooted R) + (↑K₀ : ℝ))
      + (1 : ℝ)) * Kb + Dl ^ (2 : ℕ) * (delayConst κ * ((2 : ℝ)⁻¹ ^ K₀ + ((1 : ℝ) + (↑K₀
      : ℝ)) * √ε) * ((1 : ℝ) + Dl) ^ (4 : ℕ) * Kb)
  ∀ (_ : (0 : ℝ) ≤ Err),
  let Ψ : ColumnDepthFamily V :=
    P.family R hR
  let r : ℤ × ℤ → ℝ :=
    fun (I : ℤ × ℤ) => dyadicGridLength G I.1
  let D₁ : ℤ × ℤ → Xi.Λ → Xk.Λ → ℂ :=
    fun (I : ℤ × ℤ) (li : Xi.Λ) (lk : Xk.Λ) => localProgressionForm (r I) (w I) (slots4
      a i k (↑(↑f : ℝ →ₘ[volume] ℂ) : ℝ → ℂ) (Xi.atom I li) (Xk.atom I lk) (zb I))
  let D₂ : ℤ × ℤ → Xi.Λ → Xk.Λ → ℂ :=
    fun (I : ℤ × ℤ) (li : Xi.Λ) (lk : Xk.Λ) => localProgressionForm (r I) (w I) (slots4
      a i k (Ψ.delayed f K₀ I) (Xi.atom I li) (Xk.atom I lk) (zb I))
  ∀ (li : Xi.Λ) (lk : Xk.Λ), ∑ I ∈ S, r I * (‖Xi.coef I li * Xk.coef I lk‖ * ‖D₁ I li
    lk - D₂ I li lk‖) ≤ Err * √(∫ (y : ℝ) in dyadicGridCell G R.1 R.2, ‖(↑(↑f : ℝ
    →ₘ[volume] ℂ) : ℝ → ℂ) y‖ ^ (2 : ℕ)) * √(∫ (y : ℝ) in dyadicGridCell G R.1 R.2,
    ‖Fb y‖ ^ (2 : ℕ))




private theorem lowDelayedReplacement_hpair : LowDelayedReplacementHpairStatement := by
  classical
  intro κ a i k b hai hak hab hik hib hkb B Dl ε hDl G J N V inst P R hR c₀ H Xi Xk hcov f K₀ S hS
    hK₀ w hw Fb zb Kb hKb hzbJ hzbm hzb2 hFb Err hErr Ψ r D₁ D₂ li lk
  set! S₀ := S.filter (fun I => Xi.coef I li ≠ 0 ∧ Xk.coef I lk ≠ 0)
  set! jb : ℤ × ℤ → ℤ × ℤ := fun I => jointBirth Xi Xk I li lk
  set! T := S₀.image jb
  have hS₀ : ∑ I ∈ S, r I * (‖Xi.coef I li * Xk.coef I lk‖ * ‖D₁ I li lk - D₂ I li lk‖) =
      ∑ I ∈ S₀, r I * (‖Xi.coef I li * Xk.coef I lk‖ * ‖D₁ I li lk - D₂ I li lk‖) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs with h
    · rfl
    · rcases not_and_or.mp h with h | h <;> simp [not_not.mp h]
  rw [hS₀, ← Finset.sum_fiberwise_of_maps_to (g := jb) (t := T)
    (fun I hI => Finset.mem_image_of_mem jb hI)]
  -- each fiber is a group with a fixed chart pair
  have hgroup : ∀ J' ∈ T, ∑ I ∈ S₀.filter (fun I => jb I = J'),
      r I * (‖Xi.coef I li * Xk.coef I lk‖ * ‖D₁ I li lk - D₂ I li lk‖) ≤
        Err * Real.sqrt (∫ y in dyadicGridCell G J'.1 J'.2, ‖(f : ℝ → ℂ) y‖ ^ 2) *
          Real.sqrt (∫ y in dyadicGridCell G J'.1 J'.2, ‖Fb y‖ ^ 2) := by
    intro J' hJ'T
    obtain ⟨I₀, hI₀, hjb₀⟩ := Finset.mem_image.mp hJ'T
    obtain ⟨hI₀S, hci₀, hck₀⟩ := Finset.mem_filter.mp hI₀
    obtain ⟨-, hJ'tree, hJ'i, hJ'k⟩ := jointBirth_spec Xi Xk hci₀ hck₀
    rw [show jointBirth Xi Xk I₀ li lk = J' from hjb₀] at hJ'tree hJ'i hJ'k
    have hJ'R : dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2 :=
      hJ'i.trans (Xi.birth_sub I₀ li hci₀).2.2
    obtain ⟨ι, L, ψa, ψb, lam, coef, p, hP, hcard, hcoef, hlam, hbdd, hp, hε⟩ :=
      hcov I₀ li lk hci₀ hck₀
    rw [show jointBirth Xi Xk I₀ li lk = J' from hjb₀] at hp
    obtain ⟨hzbA, hzbD⟩ := hzbJ J' hJ'tree hJ'R
    -- the group cells
    set S' := S₀.filter (fun I => jb I = J')
    have hmem : ∀ I ∈ S', I ∈ S ∧ Xi.coef I li ≠ 0 ∧ Xk.coef I lk ≠ 0 ∧ jb I = J' :=
      fun I hI => by
        obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hI
        obtain ⟨h3, h4, h5⟩ := Finset.mem_filter.mp h1
        exact ⟨h3, h4, h5, h2⟩
    have hbirth : ∀ I ∈ S', Xi.birth I li = Xi.birth I₀ li ∧ Xk.birth I lk = Xk.birth I₀ lk := by
      intro I hI
      obtain ⟨-, hci, hck, hjb⟩ := hmem I hI
      refine jointBirth_canon Xi Xk hci hck hci₀ hck₀ ?_
      rw [show jointBirth Xi Xk I li lk = J' from hjb,
        show jointBirth Xi Xk I₀ li lk = J' from hjb₀]
      rw [Set.not_disjoint_iff]
      exact ⟨_, dyadicGridCell_left_mem G J'.1 J'.2, dyadicGridCell_left_mem G J'.1 J'.2⟩
    have hS'below : ∀ I ∈ S', I ∈ pathBelow G J N J' := by
      intro I hI
      obtain ⟨hIS, hci, hck, hjb⟩ := hmem I hI
      have hIT := ((PathColumnSystem.below_mem_iff hR I).mp (hS I hIS)).1
      refine (PathColumnSystem.below_mem_iff hJ'tree I).mpr ⟨hIT, ?_⟩
      have := (jointBirth_spec Xi Xk hci hck).1
      rwa [show jointBirth Xi Xk I li lk = J' from hjb] at this
    have hgl := predictorDelay_group κ hai hak hab hik hib hkb hP hDl hcard hcoef hlam hbdd P
      hJ'tree p (fun ℓ hℓ => (hp ℓ hℓ).1) (fun ℓ hℓ => (hp ℓ hℓ).2) hε f K₀ S' hS'below
      (fun I hI => hK₀ I (hmem I hI).1) w (fun I hI => hw I (hmem I hI).1) hKb hzbA hzbD hzbm
      hzb2 (fun I => Xi.coef I li * Xk.coef I lk) (fun I => by
        rw [norm_mul]
        exact (mul_le_mul (Xi.coef_le I li) (Xk.coef_le I lk) (norm_nonneg _)
          zero_le_one).trans (by norm_num))
    have hcc : compressionOneConst (P.rooted J') = compressionOneConst (P.rooted R) := rfl
    rw [hcc] at hgl
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun I hI => ?_)) hgl
    obtain ⟨hIS, hci, hck, hjb⟩ := hmem I hI
    have hat : Xi.atom I li = quadraticChartAtom (Xi.chart (Xi.birth I₀ li) li) := by
      unfold LowList.atom; rw [(hbirth I hI).1]
    have hat' : Xk.atom I lk = quadraticChartAtom (Xk.chart (Xk.birth I₀ lk) lk) := by
      unfold LowList.atom; rw [(hbirth I hI).2]
    -- the delayed opponents of the two roots agree on `I`
    have hIR := hS I hIS
    have hIJ := hS'below I hI
    have hae := P.delayed_ae hR hJ'tree f K₀ hIR hIJ (hK₀ I hIS)
    have hr := dyadicGridLength_pos G I.1
    have hwI := hw I hIS
    have hD : D₂ I li lk = localProgressionForm (dyadicGridLength G I.1) (w I)
        (slots4 a i k ((P.family J' hJ'tree).delayed f K₀ I)
          (quadraticChartAtom (Xi.chart (Xi.birth I₀ li) li))
          (quadraticChartAtom (Xk.chart (Xk.birth I₀ lk) lk)) (zb I)) := by
      simp only [D₂, r]
      rw [hat, hat', slots4_update_a, slots4_update_a (za := (P.family J' hJ'tree).delayed f K₀
          I)]
      have hbase : ∀ l, FinL2 (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)
          (slots4 a i k 0 (quadraticChartAtom (Xi.chart (Xi.birth I₀ li) li))
            (quadraticChartAtom (Xk.chart (Xk.birth I₀ lk) lk)) (zb I) l) := by
        intro l
        unfold slots4
        split_ifs
        · exact FinL2.zero
        · exact FinL2.of_bound hr (quadraticChartAtom_measurable _) (Xi.bounded _ _)
        · exact FinL2.of_bound hr (quadraticChartAtom_measurable _) (Xk.bounded _ _)
        · exact finL2_of_memLp_cell (hzbm I) (hzb2 I)
      refine localProgressionForm_update_congr_ae hr hwI (fun l => (hbase l).1)
        (fun l => (hbase l).2) hai hak hab hik hib hkb (measurable_column_coord _ none)
        (measurable_column_coord _ none)
        (finL2_of_memLp_cell (G := G) (I := I) (measurable_column_coord _ none)
          (ColumnDepthFamily.memLp_coord_restrict _ _)).2
        (finL2_of_memLp_cell (G := G) (I := I) (measurable_column_coord _ none)
          (ColumnDepthFamily.memLp_coord_restrict _ _)).2 ?_
      exact ae_normalized_of_cell hae
    have hD1 : D₁ I li lk = localProgressionForm (dyadicGridLength G I.1) (w I)
        (slots4 a i k (f : ℝ → ℂ) (quadraticChartAtom (Xi.chart (Xi.birth I₀ li) li))
          (quadraticChartAtom (Xk.chart (Xk.birth I₀ lk) lk)) (zb I)) := by
      simp only [D₁, r]; rw [hat, hat']
    rw [hD1, hD]
  -- sum over the disjoint group roots
  have hTdisj : (T : Set (ℤ × ℤ)).PairwiseDisjoint (fun c => dyadicGridCell G c.1 c.2) := by
    intro J₁ hJ₁ J₂ hJ₂ hne
    obtain ⟨I₁, hI₁, rfl⟩ := Finset.mem_image.mp hJ₁
    obtain ⟨I₂, hI₂, rfl⟩ := Finset.mem_image.mp hJ₂
    obtain ⟨-, h1i, h1k⟩ := Finset.mem_filter.mp hI₁
    obtain ⟨-, h2i, h2k⟩ := Finset.mem_filter.mp hI₂
    by_contra hnd
    exact hne (jointBirth_eq_of Xi Xk (jointBirth_canon Xi Xk h1i h1k h2i h2k hnd))
  have hTR : ∀ c ∈ T, dyadicGridCell G c.1 c.2 ⊆ dyadicGridCell G R.1 R.2 := by
    intro c hc
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨-, hci, hck⟩ := Finset.mem_filter.mp hI
    exact (jointBirth_spec Xi Xk hci hck).2.2.1.trans (Xi.birth_sub I li hci).2.2
  calc ∑ J' ∈ T, ∑ I ∈ S₀.filter (fun I => jb I = J'),
        r I * (‖Xi.coef I li * Xk.coef I lk‖ * ‖D₁ I li lk - D₂ I li lk‖)
      ≤ ∑ J' ∈ T, Err * (Real.sqrt (∫ y in dyadicGridCell G J'.1 J'.2, ‖(f : ℝ → ℂ) y‖ ^ 2) *
          Real.sqrt (∫ y in dyadicGridCell G J'.1 J'.2, ‖Fb y‖ ^ 2)) :=
        Finset.sum_le_sum fun J' hJ' => (hgroup J' hJ').trans (le_of_eq (by ring))
    _ = Err * ∑ J' ∈ T, Real.sqrt (∫ y in dyadicGridCell G J'.1 J'.2, ‖(f : ℝ → ℂ) y‖ ^ 2) *
          Real.sqrt (∫ y in dyadicGridCell G J'.1 J'.2, ‖Fb y‖ ^ 2) := by rw [Finset.mul_sum]
    _ ≤ Err * (Real.sqrt (∫ y in dyadicGridCell G R.1 R.2, ‖(f : ℝ → ℂ) y‖ ^ 2) *
          Real.sqrt (∫ y in dyadicGridCell G R.1 R.2, ‖Fb y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (sum_sqrt_energy_le T hTdisj hTR
          ((Lp.memLp f).integrable_norm_pow two_ne_zero).integrableOn hFb) hErr
    _ = _ := by ring
-- assemble


/-- Blueprint prop:base, proof lines 1626-1632: inserting the conjugate predictors of every
low pair at its joint birth cell, the delayed replacement of the input in slot `a` (against the
low arguments in slots `i, k` and an admissible opponent in slot `b`) has absolute scale-sum
error controlled by the number of low label pairs, the predictor accuracy `e^{-B}`, and the
delay error `2^{-K₀} + (1 + K₀)√ε`. -/
theorem lowDelayedReplacement (κ : LocalKernelClass) {a i k b : Fin 4}
    (hai : a ≠ i) (hak : a ≠ k) (hab : a ≠ b) (hik : i ≠ k) (hib : i ≠ b) (hkb : k ≠ b)
    {B Dl ε : ℝ} (hDl : 0 ≤ Dl) {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {V : Type}
    [Fintype V] (P : PathColumnSystem G J N V) {R : ℤ × ℤ} (hR : R ∈ dyadicFiniteTree G J N)
    {c₀ : ℕ} {H : ℝ} (Xi Xk : LowList G J N R c₀ H)
    (hcov : ∀ I li lk, Xi.coef I li ≠ 0 → Xk.coef I lk ≠ 0 →
      PredictorCover κ P a i k b B Dl ε (Xi.chart (Xi.birth I li) li)
        (Xk.chart (Xk.birth I lk) lk) (jointBirth Xi Xk I li lk))
    (f : Lp ℂ 2 (volume : Measure ℝ)) (K₀ : ℕ) (S : Finset (ℤ × ℤ))
    (hS : ∀ I ∈ S, I ∈ pathBelow G J N R) (hK₀ : ∀ I ∈ S, I.1 + K₀ ≤ J.1 + N)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ) (hw : ∀ I ∈ S, IsAdmissibleLocalKernel κ
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I))
    {Fb : ℝ → ℂ} {zb : ℤ × ℤ → ℝ → ℂ} {Kb : ℝ} (hKb : 0 ≤ Kb)
    (hzbJ : ∀ J' ∈ dyadicFiniteTree G J N, dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2 →
      IsAdmissibleOpponent G J' Fb zb Kb ∧ HasDepthEnergy G J' Fb zb Kb)
    (hzbm : ∀ I, Measurable (zb I))
    (hzb2 : ∀ I, MemLp (zb I) 2 (volume.restrict (dyadicGridCell G I.1 I.2)))
    (hFb : IntegrableOn (fun y => ‖Fb y‖ ^ 2) (dyadicGridCell G R.1 R.2)) :
    ∑ I ∈ S, dyadicGridLength G I.1 *
      ‖localProgressionForm (dyadicGridLength G I.1) (w I)
          (slots4 a i k (f : ℝ → ℂ) (Xi.val I) (Xk.val I) (zb I)) -
        localProgressionForm (dyadicGridLength G I.1) (w I)
          (slots4 a i k ((P.family R hR).delayed f K₀ I) (Xi.val I) (Xk.val I) (zb I))‖ ≤
      (Fintype.card Xi.Λ * Fintype.card Xk.Λ) *
        (2 * Real.exp (-B) * (2 * (compressionOneConst (P.rooted R) + K₀) + 1) * Kb +
          Dl ^ 2 * (delayConst κ * ((2 : ℝ)⁻¹ ^ K₀ + (1 + K₀) * Real.sqrt ε) *
            (1 + Dl) ^ 4 * Kb)) *
        Real.sqrt (∫ y in dyadicGridCell G R.1 R.2, ‖(f : ℝ → ℂ) y‖ ^ 2) *
        Real.sqrt (∫ y in dyadicGridCell G R.1 R.2, ‖Fb y‖ ^ 2) := by
  classical
  set Err := 2 * Real.exp (-B) * (2 * (compressionOneConst (P.rooted R) + K₀) + 1) * Kb +
    Dl ^ 2 * (delayConst κ * ((2 : ℝ)⁻¹ ^ K₀ + (1 + K₀) * Real.sqrt ε) * (1 + Dl) ^ 4 * Kb)
  have hErr : 0 ≤ Err := by
    have := delayConst_nonneg κ
    have hcc : 0 ≤ compressionOneConst (P.rooted R) := by
      unfold compressionOneConst
      exact pow_nonneg (mul_nonneg (by positivity)
        (Real.log_nonneg (by linarith [(P.rooted R).two_le_budget]))) _
    positivity
  set Ψ := P.family R hR
  set! r : ℤ × ℤ → ℝ := fun I => dyadicGridLength G I.1
  set! D₁ : ℤ × ℤ → Xi.Λ → Xk.Λ → ℂ := fun I li lk =>
    localProgressionForm (r I) (w I) (slots4 a i k (f : ℝ → ℂ) (Xi.atom I li) (Xk.atom I lk) (zb I))
  set! D₂ : ℤ × ℤ → Xi.Λ → Xk.Λ → ℂ := fun I li lk =>
    localProgressionForm (r I) (w I)
      (slots4 a i k (Ψ.delayed f K₀ I) (Xi.atom I li) (Xk.atom I lk) (zb I))
  have hfm : Measurable (f : ℝ → ℂ) := (Lp.stronglyMeasurable f).measurable
  -- step 1: bilinear expansion on each cell
  have hexp : ∀ I ∈ S, localProgressionForm (r I) (w I)
        (slots4 a i k (f : ℝ → ℂ) (Xi.val I) (Xk.val I) (zb I)) -
      localProgressionForm (r I) (w I)
        (slots4 a i k (Ψ.delayed f K₀ I) (Xi.val I) (Xk.val I) (zb I)) =
      ∑ li, ∑ lk, Xi.coef I li * Xk.coef I lk * (D₁ I li lk - D₂ I li lk) := by
    intro I hI
    have hr := dyadicGridLength_pos G I.1
    have hwI := hw I hI
    have hat : ∀ (X : LowList G J N R c₀ H) l,
        FinL2 (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (X.atom I l) :=
      fun X l => FinL2.of_bound hr (X.atom_measurable I l) (X.atom_bound I l)
    have hf2 := finL2_of_memLp_cell hfm ((Lp.memLp f).restrict (dyadicGridCell G I.1 I.2))
    have hd2 : FinL2 (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (Ψ.delayed f K₀ I) :=
      finL2_of_memLp_cell (measurable_column_coord (Ψ.proj (I.1 + K₀) (physicalColumnInput f)) none)
        (ColumnDepthFamily.memLp_coord_restrict (Ψ.proj (I.1 + K₀) (physicalColumnInput f)) _)
    have hb2 := finL2_of_memLp_cell (hzbm I) (hzb2 I)
    rw [show Xi.val I = fun y => ∑ l, Xi.coef I l * Xi.atom I l y from rfl,
      show Xk.val I = fun y => ∑ l, Xk.coef I l * Xk.atom I l y from rfl,
      localProgressionForm_slots4_expand hr hwI hai hak hik hf2 hb2 (Xi.coef I) (Xk.coef I)
        (Xi.atom I) (Xk.atom I) (hat Xi) (hat Xk),
      localProgressionForm_slots4_expand hr hwI hai hak hik hd2 hb2 (Xi.coef I) (Xk.coef I)
        (Xi.atom I) (Xk.atom I) (hat Xi) (hat Xk),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun li _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun lk _ => ?_
    simp only [D₁, D₂, r]
    ring
  -- step 4: the bound for one label pair
  have hpair : ∀ (li : Xi.Λ) (lk : Xk.Λ), ∑ I ∈ S, r I *
      (‖Xi.coef I li * Xk.coef I lk‖ * ‖D₁ I li lk - D₂ I li lk‖) ≤
      Err * Real.sqrt (∫ y in dyadicGridCell G R.1 R.2, ‖(f : ℝ → ℂ) y‖ ^ 2) *
        Real.sqrt (∫ y in dyadicGridCell G R.1 R.2, ‖Fb y‖ ^ 2) := by
    expose_names
    exact @lowDelayedReplacement_hpair κ a i k b hai hak hab hik hib hkb B Dl ε hDl G J N V inst P
      R hR c₀ H Xi Xk hcov f K₀ S hS hK₀ w hw Fb zb Kb hKb hzbJ hzbm hzb2 hFb hErr
  calc ∑ I ∈ S, dyadicGridLength G I.1 *
        ‖localProgressionForm (dyadicGridLength G I.1) (w I)
            (slots4 a i k (f : ℝ → ℂ) (Xi.val I) (Xk.val I) (zb I)) -
          localProgressionForm (dyadicGridLength G I.1) (w I)
            (slots4 a i k (Ψ.delayed f K₀ I) (Xi.val I) (Xk.val I) (zb I))‖
      ≤ ∑ I ∈ S, r I * ∑ li, ∑ lk,
          ‖Xi.coef I li * Xk.coef I lk‖ * ‖D₁ I li lk - D₂ I li lk‖ := by
        refine Finset.sum_le_sum fun I hI => ?_
        rw [hexp I hI]
        refine mul_le_mul_of_nonneg_left ?_ (dyadicGridLength_pos G I.1).le
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun li _ => ?_)
        refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun lk _ => ?_))
        rw [norm_mul]
    _ = ∑ li, ∑ lk, ∑ I ∈ S, r I *
          (‖Xi.coef I li * Xk.coef I lk‖ * ‖D₁ I li lk - D₂ I li lk‖) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun li _ => ?_
        rw [Finset.sum_comm]
    _ ≤ ∑ _li : Xi.Λ, ∑ _lk : Xk.Λ,
          Err * Real.sqrt (∫ y in dyadicGridCell G R.1 R.2, ‖(f : ℝ → ℂ) y‖ ^ 2) *
            Real.sqrt (∫ y in dyadicGridCell G R.1 R.2, ‖Fb y‖ ^ 2) :=
        Finset.sum_le_sum fun li _ => Finset.sum_le_sum fun lk _ => hpair li lk
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

namespace LowList
variable {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {R : ℤ × ℤ} {c₀ : ℕ} {H : ℝ}

/-- Births of a label available at two nested tree cells agree. -/
theorem birth_eq_of_le (X : LowList G J N R c₀ H) {c d : ℤ × ℤ} {l : X.Λ}
    (hc : X.avail c l) (hd : X.avail d l)
    (hcd : dyadicGridCell G c.1 c.2 ⊆ dyadicGridCell G d.1 d.2) : X.birth c l = X.birth d l := by
  refine X.birth_canon' c d l hc hd (Set.not_disjoint_iff.mpr ?_)
  have hy := dyadicGridCell_left_mem G c.1 c.2
  exact ⟨_, (X.birth_spec c l hc).1 hy, (X.birth_spec d l hd).1 (hcd hy)⟩

end LowList

section PredSystem
variable (κ : LocalKernelClass) {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {R : ℤ × ℤ} {c₀ c₁ : ℕ}
  {H : ℝ} (Xi Xk : LowList G J N R c₀ H) (a i k b : Fin 4) (B D : ℝ)
  (pkg : ∀ (K K' : ℤ × ℤ) (li : Xi.Λ) (lk : Xk.Λ),
    PredictorPackage κ (Xi.chart K li) (Xk.chart K' lk) a i k b B D c₁)

/-- Predictor availability: both low labels available and the index within the list. -/
def PredAvail (c : ℤ × ℤ) (v : Xi.Λ × Xk.Λ × Fin (⌊D⌋₊)) : Prop :=
  c ∈ dyadicFiniteTree G J N ∧ Xi.avail c v.1 ∧ Xk.avail c v.2.1 ∧
    (v.2.2 : ℕ) < (pkg (Xi.birth c v.1) (Xk.birth c v.2.1) v.1 v.2.1).L.card

open scoped Classical in
/-- The conjugate predictor with index `v.2.2` of the pair `(v.1, v.2.1)` born at `(K, K')`. -/
noncomputable def predScalarB (K K' : ℤ × ℤ) (v : Xi.Λ × Xk.Λ × Fin (⌊D⌋₊)) (y : ℝ) : ℂ :=
  if h : (v.2.2 : ℕ) < (pkg K K' v.1 v.2.1).L.card then
    conj (quadraticChartAtom ((pkg K K' v.1 v.2.1).ψa
      ((pkg K K' v.1 v.2.1).L.equivFin.symm ⟨v.2.2, h⟩).1) y)
  else 0

open scoped Classical in
/-- The scalar of a predictor label at a cell. -/
noncomputable def predScalar (c : ℤ × ℤ) (v : Xi.Λ × Xk.Λ × Fin (⌊D⌋₊)) (y : ℝ) : ℂ :=
  if PredAvail κ Xi Xk a i k b B D pkg c v then
    predScalarB κ Xi Xk a i k b B D pkg (Xi.birth c v.1) (Xk.birth c v.2.1) v y
  else 0

theorem predAvail_mono {c d : ℤ × ℤ} (hc : c ∈ dyadicFiniteTree G J N)
    (hcd : dyadicGridCell G c.1 c.2 ⊆ dyadicGridCell G d.1 d.2) {v : Xi.Λ × Xk.Λ × Fin (⌊D⌋₊)}
    (h : PredAvail κ Xi Xk a i k b B D pkg d v) : PredAvail κ Xi Xk a i k b B D pkg c v := by
  obtain ⟨hd, hi, hk, hm⟩ := h
  have hi' := Xi.avail_mono c d v.1 hc hd hcd hi
  have hk' := Xk.avail_mono c d v.2.1 hc hd hcd hk
  refine ⟨hc, hi', hk', ?_⟩
  rw [Xi.birth_eq_of_le hi' hi hcd, Xk.birth_eq_of_le hk' hk hcd]
  exact hm

theorem predScalar_eq {c d : ℤ × ℤ} (hc : c ∈ dyadicFiniteTree G J N)
    (hcd : dyadicGridCell G c.1 c.2 ⊆ dyadicGridCell G d.1 d.2) {v : Xi.Λ × Xk.Λ × Fin (⌊D⌋₊)}
    (h : PredAvail κ Xi Xk a i k b B D pkg d v) :
    predScalar κ Xi Xk a i k b B D pkg c v = predScalar κ Xi Xk a i k b B D pkg d v := by
  classical
  have hc' := predAvail_mono κ Xi Xk a i k b B D pkg hc hcd h
  funext y
  unfold predScalar
  simp only [hc', h, ↓reduceIte]
  rw [Xi.birth_eq_of_le hc'.2.1 h.2.1 hcd, Xk.birth_eq_of_le hc'.2.2.1 h.2.2.1 hcd]

theorem predScalar_measurable (c : ℤ × ℤ) (v : Xi.Λ × Xk.Λ × Fin (⌊D⌋₊)) :
    Measurable (predScalar κ Xi Xk a i k b B D pkg c v) := by
  classical
  unfold predScalar predScalarB
  split_ifs
  · exact Complex.continuous_conj.measurable.comp (quadraticChartAtom_measurable _)
  · exact measurable_const
  · exact measurable_const

theorem predScalar_bound (c : ℤ × ℤ) (v : Xi.Λ × Xk.Λ × Fin (⌊D⌋₊)) (y : ℝ) :
    ‖predScalar κ Xi Xk a i k b B D pkg c v y‖ ≤ 1 := by
  classical
  unfold predScalar predScalarB
  split_ifs with h1 h2
  · rw [Complex.norm_conj]
    exact ((pkg _ _ _ _).bdd _ ((pkg _ _ _ _).L.equivFin.symm ⟨v.2.2, h2⟩).2).1 y
  · simp
  · simp

open scoped Classical in
/-- The predictor high system of a pair of low lists (blueprint prop:base, line 1626): one
label for each low label pair and predictor index, available below the pair's joint birth, with
scalar the conjugate predictor and private weight `ε`. -/
noncomputable def predSystem {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    PathColumnSystem G J N (Xi.Λ × Xk.Λ × Fin (⌊D⌋₊)) where
  avail := fun c => Finset.univ.filter (PredAvail κ Xi Xk a i k b B D pkg c)
  scalarAt := predScalar κ Xi Xk a i k b B D pkg
  weight := fun _ => ε
  weight_pos := fun _ => hε0
  weight_le := fun _ => hε1
  scalar_meas := predScalar_measurable κ Xi Xk a i k b B D pkg
  scalar_bound := predScalar_bound κ Xi Xk a i k b B D pkg
  avail_mono := fun c d hc _ hcd v hv => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact predAvail_mono κ Xi Xk a i k b B D pkg hc hcd hv
  consistent := fun c d hc _ hcd v hv y _ => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rw [predScalar_eq κ Xi Xk a i k b B D pkg hc hcd hv]

end PredSystem

section PredCover
variable (κ : LocalKernelClass) {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {R : ℤ × ℤ} {c₀ c₁ : ℕ}
  {H : ℝ} (Xi Xk : LowList G J N R c₀ H) (a i k b : Fin 4) (B D : ℝ)
  (pkg : ∀ (K K' : ℤ × ℤ) (li : Xi.Λ) (lk : Xk.Λ),
    PredictorPackage κ (Xi.chart K li) (Xk.chart K' lk) a i k b B D c₁)

/-- Blueprint prop:base, line 1626: the predictor system covers every low pair at its joint
birth cell. -/
theorem predSystem_cover {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hD1 : 1 ≤ D) {I : ℤ × ℤ}
    {li : Xi.Λ} {lk : Xk.Λ} (hci : Xi.coef I li ≠ 0) (hck : Xk.coef I lk ≠ 0) :
    PredictorCover κ (predSystem κ Xi Xk a i k b B D pkg hε0 hε1) a i k b B D ε
      (Xi.chart (Xi.birth I li) li) (Xk.chart (Xk.birth I lk) lk) (jointBirth Xi Xk I li lk) := by
  classical
  set P := pkg (Xi.birth I li) (Xk.birth I lk) li lk with hPdef
  have hpos : 0 < ⌊D⌋₊ := Nat.floor_pos.mpr hD1
  have hcardD : P.L.card ≤ ⌊D⌋₊ := Nat.le_floor P.card_le
  set! m : P.ι → Fin (⌊D⌋₊) := fun ℓ => if h : ℓ ∈ P.L then
    ⟨(P.L.equivFin ⟨ℓ, h⟩ : ℕ), lt_of_lt_of_le (P.L.equivFin ⟨ℓ, h⟩).2 hcardD⟩ else ⟨0, hpos⟩
  obtain ⟨hIJ', hJ'T, hJ'i, hJ'k⟩ := jointBirth_spec Xi Xk hci hck
  set J' := jointBirth Xi Xk I li lk
  have hai : Xi.avail I li := Xi.coef_avail I li hci
  have hak : Xk.avail I lk := Xk.coef_avail I lk hck
  have hbi := Xi.birth_spec I li hai
  have hbk := Xk.birth_spec I lk hak
  have hJ'ai : Xi.avail J' li :=
    Xi.avail_mono J' _ li hJ'T hbi.2.1 hJ'i (Xi.avail_birth I li hai)
  have hJ'ak : Xk.avail J' lk :=
    Xk.avail_mono J' _ lk hJ'T hbk.2.1 hJ'k (Xk.avail_birth I lk hak)
  have hbe1 : Xi.birth J' li = Xi.birth I li := (Xi.birth_eq_of_le hai hJ'ai hIJ').symm
  have hbe2 : Xk.birth J' lk = Xk.birth I lk := (Xk.birth_eq_of_le hak hJ'ak hIJ').symm
  have hmval : ∀ ℓ (hℓ : ℓ ∈ P.L), ((m ℓ : Fin (⌊D⌋₊)) : ℕ) = (P.L.equivFin ⟨ℓ, hℓ⟩ : ℕ) := by
    intro ℓ hℓ; simp [m, hℓ]
  have havail : ∀ ℓ ∈ P.L, PredAvail κ Xi Xk a i k b B D pkg J' (li, lk, m ℓ) := by
    intro ℓ hℓ
    refine ⟨hJ'T, hJ'ai, hJ'ak, ?_⟩
    simp only
    rw [hbe1, hbe2, hmval ℓ hℓ]
    exact (P.L.equivFin ⟨ℓ, hℓ⟩).2
  refine ⟨P.ι, P.L, P.ψa, P.ψb, P.lam, P.coef, fun ℓ => (li, lk, m ℓ), P.approx, P.card_le,
    P.coef_le, P.lam_le, fun ℓ hℓ => ⟨(P.bdd ℓ hℓ).1, (P.bdd ℓ hℓ).2.1⟩, fun ℓ hℓ => ⟨?_, ?_⟩,
    fun ℓ _ => le_rfl⟩
  · simp only [predSystem, Finset.mem_filter, Finset.mem_univ, true_and]
    exact havail ℓ hℓ
  · intro y
    simp only [predSystem, predScalar]
    simp only [havail ℓ hℓ, ↓reduceIte]
    rw [hbe1, hbe2]
    unfold predScalarB
    have hlt : ((m ℓ : Fin (⌊D⌋₊)) : ℕ) < P.L.card := by
      rw [hmval ℓ hℓ]; exact (P.L.equivFin ⟨ℓ, hℓ⟩).2
    rw [show pkg (Xi.birth I li) (Xk.birth I lk) li lk = P from rfl]
    simp only [hlt, ↓reduceDIte]
    have he : P.L.equivFin.symm ⟨(m ℓ : ℕ), hlt⟩ = ⟨ℓ, hℓ⟩ := by
      rw [Equiv.symm_apply_eq]; ext; exact hmval ℓ hℓ
    rw [he]

end PredCover

/-! ### Low lists from the adaptive fits -/

/-- The ancestor of `I` at depth `d`. -/
noncomputable def ancAt (G : RealDyadicGrid) (I : ℤ × ℤ) (d : ℤ) : ℤ × ℤ :=
  (d, dyadicIndex G d (dyadicGridLeft G I.1 I.2))

theorem ancAt_self (G : RealDyadicGrid) (I : ℤ × ℤ) : ancAt G I I.1 = I := by
  unfold ancAt; rw [dyadicIndex_eq (dyadicGridCell_left_mem G I.1 I.2)]

theorem subset_ancAt (G : RealDyadicGrid) (I : ℤ × ℤ) {d : ℤ} (hd : d ≤ I.1) :
    dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G (ancAt G I d).1 (ancAt G I d).2 :=
  dyadicGridCell_subset_of_common_point G (dyadicGridCell_left_mem G I.1 I.2)
    (mem_dyadicIndex G d _) hd

theorem ancAt_subset {G : RealDyadicGrid} {I R : ℤ × ℤ}
    (hIR : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2) {d : ℤ} (hd : R.1 ≤ d) :
    dyadicGridCell G (ancAt G I d).1 (ancAt G I d).2 ⊆ dyadicGridCell G R.1 R.2 :=
  dyadicGridCell_subset_of_common_point G (mem_dyadicIndex G d _)
    (hIR (dyadicGridCell_left_mem G I.1 I.2)) hd

/-- A cell containing `I` at depth `d` is the ancestor of `I` at depth `d`. -/
theorem ancAt_eq_of_subset {G : RealDyadicGrid} {I c : ℤ × ℤ}
    (h : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G c.1 c.2) : ancAt G I c.1 = c := by
  unfold ancAt; rw [dyadicIndex_eq (h (dyadicGridCell_left_mem G I.1 I.2))]

namespace LowList
variable {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {R : ℤ × ℤ} {c₀ : ℕ} {H : ℝ}

/-- The difference of two low lists. -/
noncomputable def sub (X Y : LowList G J N R c₀ H) : LowList G J N R c₀ H where
  Λ := X.Λ ⊕ Y.Λ
  coef := fun I l => Sum.elim (X.coef I) (fun m => -Y.coef I m) l
  coef_le := fun I l => by
    cases l with
    | inl l => exact X.coef_le I l
    | inr l => simpa using Y.coef_le I l
  avail := fun I l => Sum.elim (X.avail I) (Y.avail I) l
  coef_avail := fun I l h => by
    cases l with
    | inl l => exact X.coef_avail I l h
    | inr l => exact Y.coef_avail I l (by simpa using h)
  avail_mono := fun c d l hc hd hcd h => by
    cases l with
    | inl l => exact X.avail_mono c d l hc hd hcd h
    | inr l => exact Y.avail_mono c d l hc hd hcd h
  birth := fun I l => Sum.elim (X.birth I) (Y.birth I) l
  dim := fun K l => Sum.elim (X.dim K) (Y.dim K) l
  chart := fun K l => match l with
    | .inl l => X.chart K l
    | .inr l => Y.chart K l
  birth_spec := fun I l h => by
    cases l with
    | inl l => exact X.birth_spec I l h
    | inr l => exact Y.birth_spec I l h
  avail_birth := fun I l h => by
    cases l with
    | inl l => exact X.avail_birth I l h
    | inr l => exact Y.avail_birth I l h
  birth_canon' := fun I₁ I₂ l h₁ h₂ hnd => by
    cases l with
    | inl l => exact X.birth_canon' I₁ I₂ l h₁ h₂ hnd
    | inr l => exact Y.birth_canon' I₁ I₂ l h₁ h₂ hnd
  one_le_dim := fun K l => by
    cases l with
    | inl l => exact X.one_le_dim K l
    | inr l => exact Y.one_le_dim K l
  complexity := fun K l => by
    cases l with
    | inl l => exact X.complexity K l
    | inr l => exact Y.complexity K l
  bounded := fun K l => by
    cases l with
    | inl l => exact X.bounded K l
    | inr l => exact Y.bounded K l

theorem sub_val (X Y : LowList G J N R c₀ H) (I : ℤ × ℤ) (y : ℝ) :
    (X.sub Y).val I y = X.val I y - Y.val I y := by
  unfold val
  change ∑ l : X.Λ ⊕ Y.Λ, _ = _
  rw [Fintype.sum_sum_type]
  simp only [atom, sub, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib]
  ring

end LowList

section FitLow
variable {c₂ : ℕ} {B : ℝ} {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ}
  {w : ℤ × ℤ → ℝ × ℝ → ℂ} {j : Fin 4} {q : ℝ} {f : ℝ → ℂ} {k : ℕ} {M : ℕ}
  {roots : Finset (ℤ × ℤ)} {seg : ℤ × ℤ → ℤ × ℤ} {n : ℤ × ℤ → ℕ}
  {a : ℤ × ℤ → ℕ → ℝ → ℂ} {g : ℤ × ℤ → ℝ → ℂ} {cnt : ℤ × ℤ → ℤ × ℤ → ℕ}
  {atm : ℤ × ℤ → ℤ × ℤ → ℕ → ℝ → ℂ}

open scoped Classical in
/-- The coefficients of a fit at a cell. -/
noncomputable def fitCoef (hF : IsAdaptiveFit c₂ B G J N w j q f k M roots seg n a g)
    (I : ℤ × ℤ) : Fin M → ℂ :=
  if h : I ∈ dyadicFiniteTree G J N ∧ kernelHull G J N w I then
    Classical.choose ((hF.2.2.2.2 I h.1).2.2.2.2.2.1 h.2) else 0

theorem fitCoef_spec (hF : IsAdaptiveFit c₂ B G J N w j q f k M roots seg n a g) {I : ℤ × ℤ}
    (hI : I ∈ dyadicFiniteTree G J N) (hIT : kernelHull G J N w I) :
    ∑ m, ‖fitCoef hF I m‖ ^ 2 ≤ 1 ∧ (∀ m : Fin M, n I ≤ m → fitCoef hF I m = 0) ∧
      ∀ y, g I y = ∑ m, fitCoef hF I m * a I m y := by
  classical
  unfold fitCoef
  simp only [hI, hIT, and_self, ↓reduceDIte]
  exact Classical.choose_spec ((hF.2.2.2.2 I hI).2.2.2.2.2.1 hIT)

theorem fitCoef_le (hF : IsAdaptiveFit c₂ B G J N w j q f k M roots seg n a g) (I : ℤ × ℤ)
    (m : Fin M) : ‖fitCoef hF I m‖ ≤ 1 := by
  classical
  by_cases hI : I ∈ dyadicFiniteTree G J N ∧ kernelHull G J N w I
  · have h := (fitCoef_spec hF hI.1 hI.2).1
    have h1 : ‖fitCoef hF I m‖ ^ 2 ≤ 1 :=
      (Finset.single_le_sum (f := fun m => ‖fitCoef hF I m‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ m)).trans h
    nlinarith [norm_nonneg (fitCoef hF I m)]
  · unfold fitCoef; simp [hI]

theorem kernelHull_of_fitCoef_ne (hF : IsAdaptiveFit c₂ B G J N w j q f k M roots seg n a g)
    {I : ℤ × ℤ} {m : Fin M} (h : fitCoef hF I m ≠ 0) : kernelHull G J N w I := by
  classical
  by_contra hT
  apply h
  unfold fitCoef
  simp [hT]

variable (hF : IsAdaptiveFit c₂ B G J N w j q f k M roots seg n a g)
  (hA : IsAttemptData c₂ B G J N M roots seg n a cnt atm)
  {R K : ℤ × ℤ} (hR : R ∈ dyadicFiniteTree G J N) (hK : K ∈ roots)
  (hRK : dyadicGridCell G R.1 R.2 ⊆ dyadicGridCell G K.1 K.2) {c₀ : ℕ} {H : ℝ}
  (hpad : ∀ (b : ℤ × ℤ) (m : Fin M), b ∈ dyadicFiniteTree G J N ∧
    dyadicGridCell G b.1 b.2 ⊆ dyadicGridCell G K.1 K.2 ∧ (m : ℕ) < cnt K b →
    ∃ (d : ℕ) (Φ : QuadraticChartData d), 1 ≤ d ∧ QuadraticChartComplexity c₀ H Φ ∧
      IsBoundedQuadraticChart Φ ∧ ∀ y, quadraticChartAtom Φ y = atm K b m y)
  (hdef : ∃ (d : ℕ) (Φ : QuadraticChartData d), 1 ≤ d ∧
    QuadraticChartComplexity c₀ H Φ ∧ IsBoundedQuadraticChart Φ)

/-- Availability of fit label `m` at `I` below `R` in the attempt rooted at `K`. -/
def fitAvail (cnt : ℤ × ℤ → ℤ × ℤ → ℕ) (G : RealDyadicGrid) (J : ℤ × ℤ) (N : ℕ) (R K I : ℤ × ℤ)
    {M : ℕ} (m : Fin M) : Prop :=
  I ∈ dyadicFiniteTree G J N ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2 ∧
    (m : ℕ) < cnt K I

theorem fitAvail_exists {I : ℤ × ℤ} {m : Fin M} (h : fitAvail cnt G J N R K I m) :
    ∃ e : ℕ, (m : ℕ) < cnt K (ancAt G I (R.1 + e)) := by
  have hle := dyadicGridCell_depth_le_of_subset G I R h.2.1
  refine ⟨(I.1 - R.1).toNat, ?_⟩
  rw [show R.1 + ((I.1 - R.1).toNat : ℤ) = I.1 by omega, ancAt_self]
  exact h.2.2

open scoped Classical in
/-- The birth cell: the shallowest ancestor of `I` below `R` where the label is available. -/
noncomputable def fitBirth (I : ℤ × ℤ) (m : Fin M) : ℤ × ℤ :=
  if h : fitAvail cnt G J N R K I m then ancAt G I (R.1 + Nat.find (fitAvail_exists h)) else R

include hR in
theorem fitBirth_spec {I : ℤ × ℤ} {m : Fin M} (h : fitAvail cnt G J N R K I m) :
    dyadicGridCell G I.1 I.2 ⊆
        dyadicGridCell G (fitBirth (cnt := cnt) (G := G) (J := J) (N := N) (R := R) (K := K) I m).1
          (fitBirth (cnt := cnt) (G := G) (J := J) (N := N) (R := R) (K := K) I m).2 ∧
      fitAvail cnt G J N R K (fitBirth (cnt := cnt) (G := G) (J := J) (N := N) (R := R) (K := K)
        I m) m := by
  classical
  have hle := dyadicGridCell_depth_le_of_subset G I R h.2.1
  have hmin := Nat.find_min' (fitAvail_exists h) (show (m : ℕ) < cnt K
    (ancAt G I (R.1 + ((I.1 - R.1).toNat : ℕ))) by
      rw [show R.1 + ((I.1 - R.1).toNat : ℤ) = I.1 by omega, ancAt_self]; exact h.2.2)
  have hd1 : R.1 + (Nat.find (fitAvail_exists h) : ℤ) ≤ I.1 := by omega
  unfold fitBirth
  simp only [h, ↓reduceDIte]
  have hsub := subset_ancAt G I hd1
  have hsubR := ancAt_subset h.2.1 (d := R.1 + Nat.find (fitAvail_exists h)) (by omega)
  refine ⟨hsub, ?_, hsubR, Nat.find_spec (fitAvail_exists h)⟩
  have hRT := (dyadicFiniteTree_mem_iff G J R N).mp hR
  have hIT := (dyadicFiniteTree_mem_iff G J I N).mp h.1
  refine (dyadicFiniteTree_mem_iff G J _ N).mpr ⟨hsubR.trans hRT.1, ?_⟩
  exact hd1.trans hIT.2

theorem fitBirth_depth_le {I c : ℤ × ℤ} {m : Fin M} (h : fitAvail cnt G J N R K I m)
    (hIc : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G c.1 c.2)
    (hcR : dyadicGridCell G c.1 c.2 ⊆ dyadicGridCell G R.1 R.2) (hmc : (m : ℕ) < cnt K c) :
    (fitBirth (cnt := cnt) (G := G) (J := J) (N := N) (R := R) (K := K) I m).1 ≤ c.1 := by
  classical
  have hle := dyadicGridCell_depth_le_of_subset G c R hcR
  unfold fitBirth
  simp only [h, ↓reduceDIte, ancAt]
  have hc' : R.1 + ((c.1 - R.1).toNat : ℤ) = c.1 := by omega
  refine le_trans ((add_le_add_iff_left R.1).mpr (Nat.cast_le.mpr (Nat.find_min' _ ?_)))
    (le_of_eq hc')
  rw [hc', show ((c.1, dyadicIndex G c.1 (dyadicGridLeft G I.1 I.2)) : ℤ × ℤ) = c from
    ancAt_eq_of_subset hIc]
  exact hmc

include hR in
theorem fitBirth_canon {I₁ I₂ : ℤ × ℤ} {m : Fin M} (h₁ : fitAvail cnt G J N R K I₁ m)
    (h₂ : fitAvail cnt G J N R K I₂ m)
    (hnd : ¬ Disjoint
      (dyadicGridCell G (fitBirth (cnt := cnt) (G := G) (J := J) (N := N) (R := R) (K := K)
        I₁ m).1 (fitBirth (cnt := cnt) (G := G) (J := J) (N := N) (R := R) (K := K) I₁ m).2)
      (dyadicGridCell G (fitBirth (cnt := cnt) (G := G) (J := J) (N := N) (R := R) (K := K)
        I₂ m).1 (fitBirth (cnt := cnt) (G := G) (J := J) (N := N) (R := R) (K := K) I₂ m).2)) :
    fitBirth (cnt := cnt) (G := G) (J := J) (N := N) (R := R) (K := K) I₁ m =
      fitBirth (cnt := cnt) (G := G) (J := J) (N := N) (R := R) (K := K) I₂ m := by
  set b₁ := fitBirth (cnt := cnt) (G := G) (J := J) (N := N) (R := R) (K := K) I₁ m
  set b₂ := fitBirth (cnt := cnt) (G := G) (J := J) (N := N) (R := R) (K := K) I₂ m
  obtain ⟨hI₁, hb₁⟩ := fitBirth_spec hR h₁
  obtain ⟨hI₂, hb₂⟩ := fitBirth_spec hR h₂
  obtain ⟨y, hy₁, hy₂⟩ := Set.not_disjoint_iff.mp hnd
  rcases le_total b₁.1 b₂.1 with hle | hle
  · have hsub : dyadicGridCell G b₂.1 b₂.2 ⊆ dyadicGridCell G b₁.1 b₁.2 :=
      dyadicGridCell_subset_of_common_point G hy₂ hy₁ hle
    have h2 : b₂.1 ≤ b₁.1 := fitBirth_depth_le h₂ (hI₂.trans hsub) hb₁.2.1 hb₁.2.2
    exact (dyadicGridCell_eq_of_common_point G hy₁ hy₂ (by omega))
  · have hsub : dyadicGridCell G b₁.1 b₁.2 ⊆ dyadicGridCell G b₂.1 b₂.2 :=
      dyadicGridCell_subset_of_common_point G hy₁ hy₂ hle
    have h2 : b₁.1 ≤ b₂.1 := fitBirth_depth_le h₁ (hI₁.trans hsub) hb₂.2.1 hb₂.2.2
    exact (dyadicGridCell_eq_of_common_point G hy₁ hy₂ (by omega))

open scoped Classical in
/-- The chart of label `m` at the birth cell `b` (padded to positive dimension). -/
noncomputable def fitChartData (b : ℤ × ℤ) (m : Fin M) : Σ d, QuadraticChartData d :=
  if h : b ∈ dyadicFiniteTree G J N ∧
      dyadicGridCell G b.1 b.2 ⊆ dyadicGridCell G K.1 K.2 ∧ (m : ℕ) < cnt K b then
    ⟨Classical.choose (hpad b m h), Classical.choose (Classical.choose_spec (hpad b m h))⟩
  else ⟨Classical.choose hdef, Classical.choose (Classical.choose_spec hdef)⟩

theorem fitChartData_spec (b : ℤ × ℤ) (m : Fin M) :
    1 ≤ (fitChartData hpad hdef b m).1 ∧
      QuadraticChartComplexity c₀ H (fitChartData hpad hdef b m).2 ∧
      IsBoundedQuadraticChart (fitChartData hpad hdef b m).2 := by
  classical
  unfold fitChartData
  by_cases h : b ∈ dyadicFiniteTree G J N ∧
      dyadicGridCell G b.1 b.2 ⊆ dyadicGridCell G K.1 K.2 ∧ (m : ℕ) < cnt K b
  · rw [dite_eq_left_of_eq_true (eq_true h)]
    have hs := Classical.choose_spec (Classical.choose_spec (hpad b m h))
    exact ⟨hs.1, hs.2.1, hs.2.2.1⟩
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    exact Classical.choose_spec (Classical.choose_spec hdef)

theorem fitChartData_atom {b : ℤ × ℤ} {m : Fin M} (h : b ∈ dyadicFiniteTree G J N ∧
    dyadicGridCell G b.1 b.2 ⊆ dyadicGridCell G K.1 K.2 ∧ (m : ℕ) < cnt K b) (y : ℝ) :
    quadraticChartAtom (fitChartData hpad hdef b m).2 y = atm K b m y := by
  classical
  unfold fitChartData
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact (Classical.choose_spec (Classical.choose_spec (hpad b m h))).2.2.2 y

open scoped Classical in
/-- The low list of one adaptive fit on the tree below `R`, in the attempt rooted at
`K ⊇ R` (blueprint prop:base, lines 1626-1630). -/
noncomputable def fitLowList : LowList G J N R c₀ H where
  Λ := Fin M
  coef := fun I m => if I ∈ dyadicFiniteTree G J N ∧
    dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2 ∧ seg I = K then fitCoef hF I m else 0
  coef_le := fun I m => by
    split_ifs
    · exact fitCoef_le hF I m
    · simp
  avail := fun I m => fitAvail cnt G J N R K I m
  coef_avail := fun I m hc => by
    split_ifs at hc with hs
    · refine ⟨hs.1, hs.2.1, ?_⟩
      have hn := (fitCoef_spec hF hs.1 (kernelHull_of_fitCoef_ne hF hc)).2.1 m
      have : (m : ℕ) < n I := by
        by_contra hlt; exact hc (hn (by omega))
      rw [← hs.2.2, (hA.1 I hs.1).1]; exact this
    · exact absurd rfl hc
  avail_mono := fun c d m hc hd hcd h => ⟨hc, hcd.trans h.2.1,
    lt_of_lt_of_le h.2.2 (hA.2.1 K hK c hc d hd hcd (h.2.1.trans hRK)).1⟩
  birth := fun I m => fitBirth (cnt := cnt) (G := G) (J := J) (N := N) (R := R) (K := K) I m
  dim := fun b m => (fitChartData hpad hdef b m).1
  chart := fun b m => (fitChartData hpad hdef b m).2
  birth_spec := fun I m h => ⟨(fitBirth_spec hR h).1, (fitBirth_spec hR h).2.1,
    (fitBirth_spec hR h).2.2.1⟩
  avail_birth := fun I m h => (fitBirth_spec hR h).2
  birth_canon' := fun I₁ I₂ m h₁ h₂ hnd => fitBirth_canon hR h₁ h₂ hnd
  one_le_dim := fun b m => (fitChartData_spec hpad hdef b m).1
  complexity := fun b m => (fitChartData_spec hpad hdef b m).2.1
  bounded := fun b m => (fitChartData_spec hpad hdef b m).2.2

/-- On the cells of the segment of `K` below `R`, the low list is the fit. -/
theorem fitLowList_val {I : ℤ × ℤ} (hI : I ∈ dyadicFiniteTree G J N)
    (hIR : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2) (hseg : seg I = K)
    (hIT : kernelHull G J N w I) (y : ℝ) :
    (fitLowList hF hA hR hK hRK hpad hdef).val I y = g I y := by
  classical
  rw [(fitCoef_spec hF hI hIT).2.2 y]
  unfold LowList.val LowList.atom
  change ∑ m : Fin M, _ = ∑ m : Fin M, _
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [fitLowList, hI, hIR, hseg, and_self, ↓reduceIte]
  by_cases hc : fitCoef hF I m = 0
  · rw [hc, zero_mul, zero_mul]
  · have hav : fitAvail cnt G J N R K I m := by
      have hn := (fitCoef_spec hF hI hIT).2.1 m
      have : (m : ℕ) < n I := by by_contra hlt; exact hc (hn (by omega))
      refine ⟨hI, hIR, ?_⟩
      rw [← hseg, (hA.1 I hI).1]; exact this
    obtain ⟨hIb, hb⟩ := fitBirth_spec hR hav
    set b := fitBirth (cnt := cnt) (G := G) (J := J) (N := N) (R := R) (K := K) I m
    congr 1
    rw [fitChartData_atom hpad hdef ⟨hb.1, hb.2.1.trans hRK, hb.2.2⟩ y]
    have hpre := (hA.2.1 K hK I hI b hb.1 hIb (hb.2.1.trans hRK)).2 m hb.2.2
    rw [← hpre, ← hseg, (hA.1 I hI).2]

end FitLow

section ColRange
variable {V : Type} [Fintype V]

/-! ### Column ranges at one cell -/

/-- Admissible data for the column of label `v` on the set `s`. -/
def ColOK (s : Set ℝ) (sc : V → ℝ → ℂ) (wt : V → ℝ) (v : V) : Prop :=
  MeasurableSet s ∧ volume s < ⊤ ∧ Measurable (sc v) ∧ (∀ y, ‖sc v y‖ ≤ 1) ∧ 0 ≤ wt v ∧
    wt v ≤ 1

theorem norm_privateColumnValue_le_two {sc : V → ℝ → ℂ} {wt : V → ℝ} {v : V}
    (hb : ∀ y, ‖sc v y‖ ≤ 1) (hw0 : 0 ≤ wt v) (hw1 : wt v ≤ 1) (y : ℝ) :
    ‖privateColumnValue sc wt v y‖ ≤ 2 := by
  have h2 := norm_privateColumnValue_sq sc wt v y hw0
  have hle : ‖privateColumnValue sc wt v y‖ ^ 2 ≤ 2 ^ 2 := by
    rw [h2]; nlinarith [norm_nonneg (sc v y), hb y]
  exact (abs_le_of_sq_le_sq' hle (by norm_num)).2

theorem ColOK.memLp {s : Set ℝ} {sc : V → ℝ → ℂ} {wt : V → ℝ} {v : V} (h : ColOK s sc wt v) :
    MemLp (s.indicator (privateColumnValue sc wt v)) 2 volume := by
  obtain ⟨hs, hsv, hm, hb, hw0, hw1⟩ := h
  refine (memLp_indicator_iff_restrict hs).mpr ?_
  have : IsFiniteMeasure (volume.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hsv⟩
  exact MemLp.of_bound (privateColumnValue_measurable sc wt v hm).aestronglyMeasurable 2
    (Filter.Eventually.of_forall (norm_privateColumnValue_le_two hb hw0 hw1))

open scoped Classical in
/-- The column `1_s (φ_v, √(w_v) e_v)`. -/
noncomputable def col (s : Set ℝ) (sc : V → ℝ → ℂ) (wt : V → ℝ) (v : V) : ColumnL2 V :=
  if h : ColOK s sc wt v then h.memLp.toLp _ else 0

theorem col_coeFn {s : Set ℝ} {sc : V → ℝ → ℂ} {wt : V → ℝ} {v : V} (h : ColOK s sc wt v) :
    (col s sc wt v : ℝ → ColumnHilbert V) =ᵐ[volume] s.indicator (privateColumnValue sc wt v) := by
  classical
  unfold col
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact MemLp.coeFn_toLp _

theorem col_of_not {s : Set ℝ} {sc : V → ℝ → ℂ} {wt : V → ℝ} {v : V} (h : ¬ ColOK s sc wt v) :
    col s sc wt v = 0 := by
  classical
  unfold col
  rw [dite_eq_right_of_eq_false (eq_false h)]

/-- The range of the columns of the labels in `A` on `s`. -/
noncomputable def colRange (s : Set ℝ) (sc : V → ℝ → ℂ) (wt : V → ℝ) (A : Finset V) :
    Submodule ℂ (ColumnL2 V) :=
  Submodule.span ℂ (col s sc wt '' (A : Set V))

instance (s : Set ℝ) (sc : V → ℝ → ℂ) (wt : V → ℝ) (A : Finset V) :
    FiniteDimensional ℂ (colRange s sc wt A) :=
  FiniteDimensional.span_of_finite ℂ (A.finite_toSet.image _)

theorem colRange_insert [DecidableEq V] (s : Set ℝ) (sc : V → ℝ → ℂ) (wt : V → ℝ) (A : Finset V)
    (v : V) :
    colRange s sc wt (insert v A) = colRange s sc wt A ⊔ Submodule.span ℂ {col s sc wt v} := by
  unfold colRange
  rw [Finset.coe_insert, Set.image_insert_eq, Submodule.span_insert, sup_comm]

/-- Elements of a column range vanish in the private coordinates of absent labels. -/
theorem colRange_fresh_zero {s : Set ℝ} {sc : V → ℝ → ℂ} {wt : V → ℝ} {A : Finset V} {v : V}
    (hv : v ∉ A) {x : ColumnL2 V} (hx : x ∈ colRange s sc wt A) :
    ∀ᵐ y ∂volume, (x : ℝ → ColumnHilbert V) y (some v) = 0 := by
  refine Submodule.span_induction (R := ℂ) (M := ColumnL2 V) (p := fun x _ =>
    ∀ᵐ y ∂volume, (x : ℝ → ColumnHilbert V) y (some v) = 0) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨u, hu, rfl⟩
    by_cases h : ColOK s sc wt u
    · filter_upwards [col_coeFn h] with y hy
      rw [hy]
      have hne : v ≠ u := fun e => hv (e ▸ hu)
      by_cases hys : y ∈ s
      · rw [Set.indicator_of_mem hys, privateColumnValue_private]
        simp [hne]
      · rw [Set.indicator_of_notMem hys]; rfl
    · rw [col_of_not h]
      filter_upwards [Lp.coeFn_zero (ColumnHilbert V) 2 volume] with y hy
      rw [hy]; rfl
  · filter_upwards [Lp.coeFn_zero (ColumnHilbert V) 2 volume] with y hy
    rw [hy]; rfl
  · intro x y _ _ hx hy
    filter_upwards [hx, hy, Lp.coeFn_add x y] with z hx hy hz
    rw [hz, Pi.add_apply, PiLp.add_apply, hx, hy, add_zero]
  · intro c x _ hx
    filter_upwards [hx, Lp.coeFn_smul c x] with z hx hz
    rw [hz, Pi.smul_apply, PiLp.smul_apply, hx, smul_zero]

/-- Elements of a column range on `s` vanish off `s`. -/
theorem colRange_ae_zero_off {s : Set ℝ} {sc : V → ℝ → ℂ} {wt : V → ℝ} {A : Finset V}
    {x : ColumnL2 V} (hx : x ∈ colRange s sc wt A) :
    ∀ᵐ y ∂volume, y ∉ s → (x : ℝ → ColumnHilbert V) y = 0 := by
  refine Submodule.span_induction (R := ℂ) (M := ColumnL2 V) (p := fun x _ =>
    ∀ᵐ y ∂volume, y ∉ s → (x : ℝ → ColumnHilbert V) y = 0) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨u, hu, rfl⟩
    by_cases h : ColOK s sc wt u
    · filter_upwards [col_coeFn h] with y hy hys
      rw [hy, Set.indicator_of_notMem hys]
    · rw [col_of_not h]
      filter_upwards [Lp.coeFn_zero (ColumnHilbert V) 2 volume] with y hy _
      rw [hy]; rfl
  · filter_upwards [Lp.coeFn_zero (ColumnHilbert V) 2 volume] with y hy _
    rw [hy]; rfl
  · intro x y _ _ hx hy
    filter_upwards [hx, hy, Lp.coeFn_add x y] with z hx hy hz hzs
    rw [hz, Pi.add_apply, hx hzs, hy hzs, add_zero]
  · intro c x _ hx
    filter_upwards [hx, Lp.coeFn_smul c x] with z hx hz hzs
    rw [hz, Pi.smul_apply, hx hzs, smul_zero]

/-- The inner product of a column with a residual vanishing in its private coordinate. -/
theorem inner_col {s : Set ℝ} {sc : V → ℝ → ℂ} {wt : V → ℝ} {v : V} (h : ColOK s sc wt v)
    (r : ColumnL2 V) (hr : ∀ᵐ y ∂volume, (r : ℝ → ColumnHilbert V) y (some v) = 0) :
    inner ℂ (col s sc wt v) r = ∫ y in s, conj (sc v y) * (r : ℝ → ColumnHilbert V) y none := by
  rw [MeasureTheory.L2.inner_def, ← integral_indicator h.1]
  refine integral_congr_ae ?_
  filter_upwards [col_coeFn h, hr] with y hy hry
  rw [hy]
  by_cases hys : y ∈ s
  · rw [Set.indicator_of_mem hys, Set.indicator_of_mem hys, privateColumnValue_inner, hry]
    simp
  · rw [Set.indicator_of_notMem hys, Set.indicator_of_notMem hys]
    simp

theorem norm_col_sq_le {s : Set ℝ} {sc : V → ℝ → ℂ} {wt : V → ℝ} {v : V} (h : ColOK s sc wt v) :
    ‖col s sc wt v‖ ^ 2 ≤ 4 * volume.real s := by
  rw [columnInput_norm_sq_integral]
  have hs := h.1
  have : IsFiniteMeasure (volume.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact h.2.1⟩
  calc ∫ y, ‖(col s sc wt v : ℝ → ColumnHilbert V) y‖ ^ 2
      = ∫ y, s.indicator (fun y => ‖privateColumnValue sc wt v y‖ ^ 2) y := by
        refine integral_congr_ae ?_
        filter_upwards [col_coeFn h] with y hy
        rw [hy]
        by_cases hys : y ∈ s
        · rw [Set.indicator_of_mem hys, Set.indicator_of_mem hys]
        · rw [Set.indicator_of_notMem hys, Set.indicator_of_notMem hys]; simp
    _ = ∫ y in s, ‖privateColumnValue sc wt v y‖ ^ 2 := integral_indicator hs
    _ ≤ ∫ y in s, (4 : ℝ) := by
        refine setIntegral_mono_on ?_ (integrableOn_const h.2.1.ne) hs fun y _ => ?_
        · exact (MemLp.of_bound (privateColumnValue_measurable sc wt v h.2.2.1).aestronglyMeasurable
            2 (Filter.Eventually.of_forall
              (norm_privateColumnValue_le_two h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2))
            ).integrable_norm_pow two_ne_zero
        · have := norm_privateColumnValue_le_two h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 y
          nlinarith [norm_nonneg (privateColumnValue sc wt v y)]
    _ = 4 * volume.real s := by rw [setIntegral_const, smul_eq_mul, mul_comm]

/-- Inserting a fresh column gains at least `|∫_s conj(φ_v) (z - P z)_phys|² / (4|s|)` of
projection energy (blueprint §11.2, line 1577 and prop:base, proof line 1637). -/
theorem colRange_gain [DecidableEq V] {s : Set ℝ} {sc : V → ℝ → ℂ} {wt : V → ℝ} {A : Finset V} {v
    : V}
    (hv : v ∉ A) (h : ColOK s sc wt v) (z : ColumnL2 V)
    (hz : ∀ᵐ y ∂volume, (z : ℝ → ColumnHilbert V) y (some v) = 0) :
    ‖(colRange s sc wt A).starProjection z‖ ^ 2 +
        ‖∫ y in s, conj (sc v y) *
          ((z - (colRange s sc wt A).starProjection z : ColumnL2 V) : ℝ → ColumnHilbert V) y
            none‖ ^ 2 / (4 * volume.real s) ≤
      ‖(colRange s sc wt (insert v A)).starProjection z‖ ^ 2 := by
  set! U := colRange s sc wt A
  set! u := col s sc wt v
  set r := z - U.starProjection z
  have hr : ∀ᵐ y ∂volume, (r : ℝ → ColumnHilbert V) y (some v) = 0 := by
    filter_upwards [hz, colRange_fresh_zero hv (Submodule.starProjection_apply_mem U z),
      Lp.coeFn_sub z (U.starProjection z)] with y h1 h2 h3
    rw [h3, Pi.sub_apply, PiLp.sub_apply, h1, h2, sub_zero]
  have hgain := starProjection_sup_span_gain U u z
  have hins : colRange s sc wt (insert v A) = U ⊔ Submodule.span ℂ {u} := colRange_insert _ _ _ _ _
  have hcongr := starProjection_congr hins z
  rw [hcongr]
  have hinner : inner ℂ u r = ∫ y in s, conj (sc v y) * (r : ℝ → ColumnHilbert V) y none :=
    inner_col h r hr
  rw [← hinner]
  have hu := norm_col_sq_le h
  rcases eq_or_lt_of_le (sq_nonneg ‖u‖) with h0 | hpos
  · have hu0 : u = 0 := by
      have : ‖u‖ = 0 := by nlinarith only [norm_nonneg u, h0]
      exact norm_eq_zero.mp this
    have hi : inner ℂ u r = 0 := by rw [hu0, inner_zero_left]
    rw [hi] at hgain ⊢
    simpa using hgain
  · have hs : 0 < volume.real s := by linarith
    calc ‖U.starProjection z‖ ^ 2 + ‖inner ℂ u r‖ ^ 2 / (4 * volume.real s)
        ≤ ‖U.starProjection z‖ ^ 2 + ‖inner ℂ u r‖ ^ 2 / ‖u‖ ^ 2 := by
          gcongr
      _ ≤ _ := hgain

end ColRange

section ColRange2
variable {V : Type} [Fintype V]

omit [Fintype V] in
theorem ColData.ok {sc : V → ℝ → ℂ} {wt : V → ℝ} (h : ColData sc wt) {s : Set ℝ}
    (hs : MeasurableSet s) (hsv : volume s < ⊤) (v : V) : ColOK s sc wt v :=
  ⟨hs, hsv, (h v).1, (h v).2.1, (h v).2.2.1, (h v).2.2.2⟩

theorem col_union {s₁ s₂ : Set ℝ} (hs₁ : MeasurableSet s₁) (hs₁v : volume s₁ < ⊤)
    (hs₂ : MeasurableSet s₂) (hs₂v : volume s₂ < ⊤) (hd : Disjoint s₁ s₂)
    {sc : V → ℝ → ℂ} {wt : V → ℝ} (h : ColData sc wt) (v : V) :
    col (s₁ ∪ s₂) sc wt v = col s₁ sc wt v + col s₂ sc wt v := by
  have hsv : volume (s₁ ∪ s₂) < ⊤ := (measure_union_le s₁ s₂).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hs₁v, hs₂v⟩)
  refine Lp.ext ?_
  filter_upwards [col_coeFn (h.ok (hs₁.union hs₂) hsv v), col_coeFn (h.ok hs₁ hs₁v v),
    col_coeFn (h.ok hs₂ hs₂v v), Lp.coeFn_add (col s₁ sc wt v) (col s₂ sc wt v)] with y hy h1 h2 h3
  rw [hy, h3, Pi.add_apply, h1, h2, Set.indicator_union_of_disjoint hd]

theorem col_congr {s : Set ℝ} (hs : MeasurableSet s) (hsv : volume s < ⊤)
    {sc sc' : V → ℝ → ℂ} {wt : V → ℝ} (h : ColData sc wt) (h' : ColData sc' wt) {v : V}
    (hv : ∀ y ∈ s, sc v y = sc' v y) : col s sc wt v = col s sc' wt v := by
  refine Lp.ext ?_
  filter_upwards [col_coeFn (h.ok hs hsv v), col_coeFn (h'.ok hs hsv v)] with y h1 h2
  rw [h1, h2]
  by_cases hy : y ∈ s
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    simp only [privateColumnValue, hv y hy]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]

/-- Refinement: the range on a union of two cells lies in the sum of the ranges on the cells
with inherited labels and consistent scalars. -/
theorem colRange_le_sup {s₁ s₂ : Set ℝ} (hs₁ : MeasurableSet s₁) (hs₁v : volume s₁ < ⊤)
    (hs₂ : MeasurableSet s₂) (hs₂v : volume s₂ < ⊤) (hd : Disjoint s₁ s₂)
    {sc sc₁ sc₂ : V → ℝ → ℂ} {wt : V → ℝ} (h : ColData sc wt) (h₁ : ColData sc₁ wt)
    (h₂ : ColData sc₂ wt) {A A₁ A₂ : Finset V} (hA₁ : A ⊆ A₁) (hA₂ : A ⊆ A₂)
    (hc₁ : ∀ v ∈ A, ∀ y ∈ s₁, sc v y = sc₁ v y) (hc₂ : ∀ v ∈ A, ∀ y ∈ s₂, sc v y = sc₂ v y) :
    colRange (s₁ ∪ s₂) sc wt A ≤ colRange s₁ sc₁ wt A₁ ⊔ colRange s₂ sc₂ wt A₂ := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨v, hv, rfl⟩
  rw [col_union hs₁ hs₁v hs₂ hs₂v hd h v, col_congr hs₁ hs₁v h h₁ (hc₁ v hv),
    col_congr hs₂ hs₂v h h₂ (hc₂ v hv)]
  exact Submodule.add_mem_sup (Submodule.subset_span ⟨v, hA₁ hv, rfl⟩)
    (Submodule.subset_span ⟨v, hA₂ hv, rfl⟩)

/-- Ranges on disjoint sets are orthogonal. -/
theorem colRange_isOrtho {s₁ s₂ : Set ℝ} (hd : Disjoint s₁ s₂) (sc₁ sc₂ : V → ℝ → ℂ)
    (wt : V → ℝ) (A₁ A₂ : Finset V) : colRange s₁ sc₁ wt A₁ ⟂ colRange s₂ sc₂ wt A₂ := by
  unfold colRange
  refine Submodule.isOrtho_span.mpr ?_
  rintro _ ⟨u, -, rfl⟩ _ ⟨u', -, rfl⟩
  by_cases h₁ : ColOK s₁ sc₁ wt u
  · by_cases h₂ : ColOK s₂ sc₂ wt u'
    · rw [MeasureTheory.L2.inner_def]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [col_coeFn h₁, col_coeFn h₂] with y hy1 hy2
      rw [hy1, hy2]
      by_cases hy : y ∈ s₁
      · have hy' : y ∉ s₂ := Set.disjoint_left.mp hd hy
        rw [Set.indicator_of_notMem hy', inner_zero_right]; rfl
      · rw [Set.indicator_of_notMem hy, inner_zero_left]; rfl
    · rw [col_of_not h₂, inner_zero_right]
  · rw [col_of_not h₁, inner_zero_left]

theorem colRange_energy_split {s₁ s₂ : Set ℝ} (hs₁ : MeasurableSet s₁) (hs₁v : volume s₁ < ⊤)
    (hs₂ : MeasurableSet s₂) (hs₂v : volume s₂ < ⊤) (hd : Disjoint s₁ s₂)
    {sc sc₁ sc₂ : V → ℝ → ℂ} {wt : V → ℝ} (h : ColData sc wt) (h₁ : ColData sc₁ wt)
    (h₂ : ColData sc₂ wt) {A A₁ A₂ : Finset V} (hA₁ : A ⊆ A₁) (hA₂ : A ⊆ A₂)
    (hc₁ : ∀ v ∈ A, ∀ y ∈ s₁, sc v y = sc₁ v y) (hc₂ : ∀ v ∈ A, ∀ y ∈ s₂, sc v y = sc₂ v y)
    (z : ColumnL2 V) :
    ‖(colRange (s₁ ∪ s₂) sc wt A).starProjection z‖ ^ 2 ≤
      ‖(colRange s₁ sc₁ wt A₁).starProjection z‖ ^ 2 +
        ‖(colRange s₂ sc₂ wt A₂).starProjection z‖ ^ 2 :=
  starProjection_energy_le_of_le_sup
    (colRange_le_sup hs₁ hs₁v hs₂ hs₂v hd h h₁ h₂ hA₁ hA₂ hc₁ hc₂)
    (colRange_isOrtho hd sc₁ sc₂ wt A₁ A₂) z

/-- The projection only sees the input on its cell. -/
theorem colRange_proj_restrict {s : Set ℝ} (hs : MeasurableSet s) (sc : V → ℝ → ℂ)
    (wt : V → ℝ) (A : Finset V) (z : ColumnL2 V) :
    (colRange s sc wt A).starProjection (columnL2Restriction s hs z) =
      (colRange s sc wt A).starProjection z := by
  set! U := colRange s sc wt A
  have e : columnL2Restriction s hs z = columnL2Indicator s hs z := rfl
  have hw : z - columnL2Restriction s hs z ∈ Uᗮ := by
    rw [e]
    refine (Submodule.mem_orthogonal' U _).mpr fun u hu => ?_
    rw [MeasureTheory.L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [colRange_ae_zero_off hu, Lp.coeFn_sub z (columnL2Indicator s hs z),
      columnL2Indicator_coeFn s hs z] with y hu hy hr
    rw [hy, Pi.sub_apply, hr]
    by_cases hys : y ∈ s
    · rw [Set.indicator_of_mem hys, sub_self, inner_zero_left]; rfl
    · rw [hu hys, inner_zero_right]; rfl
  calc U.starProjection (columnL2Restriction s hs z)
      = U.starProjection (columnL2Restriction s hs z) +
          U.starProjection (z - columnL2Restriction s hs z) := by
        rw [(Submodule.starProjection_apply_eq_zero_iff U).mpr hw, add_zero]
    _ = U.starProjection z := by rw [← map_add]; congr 1; abel

/-- Contraction on the cell. -/
theorem colRange_energy_le {s : Set ℝ} (hs : MeasurableSet s) (sc : V → ℝ → ℂ) (wt : V → ℝ)
    (A : Finset V) (z : ColumnL2 V) :
    ‖(colRange s sc wt A).starProjection z‖ ^ 2 ≤
      ∫ y in s, ‖(z : ℝ → ColumnHilbert V) y‖ ^ 2 := by
  rw [← colRange_proj_restrict hs, ← columnL2Restriction_norm_sq s hs z]
  have h1 := ContinuousLinearMap.le_opNorm (colRange s sc wt A).starProjection
    (columnL2Restriction s hs z)
  have h2 : ‖(colRange s sc wt A).starProjection‖ ≤ 1 := Submodule.starProjection_norm_le _
  have h3 : ‖(colRange s sc wt A).starProjection (columnL2Restriction s hs z)‖ ≤
      ‖columnL2Restriction s hs z‖ :=
    h1.trans (by simpa using mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
  exact pow_le_pow_left₀ (norm_nonneg _) h3 2

theorem colRange_exists_coeff {s : Set ℝ} {sc : V → ℝ → ℂ} {wt : V → ℝ} {A : Finset V}
    {x : ColumnL2 V} (hx : x ∈ colRange s sc wt A) :
    ∃ c : V → ℂ, x = ∑ v ∈ A, c v • col s sc wt v := by
  classical
  refine Submodule.span_induction (R := ℂ) (M := ColumnL2 V) (p := fun x _ =>
    ∃ c : V → ℂ, x = ∑ v ∈ A, c v • col s sc wt v) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨u, hu, rfl⟩
    refine ⟨Pi.single u (1 : ℂ), ?_⟩
    rw [Finset.sum_eq_single u]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd hu h
  · exact ⟨0, by simp⟩
  · rintro x y _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
    exact ⟨c + d, by simp [add_smul, Finset.sum_add_distrib]⟩
  · rintro r x _ ⟨c, rfl⟩
    exact ⟨r • c, by simp [Finset.smul_sum, smul_smul]⟩

/-- Coefficients of the projection in the columns. -/
noncomputable def colCoeff (s : Set ℝ) (sc : V → ℝ → ℂ) (wt : V → ℝ) (A : Finset V)
    (z : ColumnL2 V) : V → ℂ :=
  Classical.choose (colRange_exists_coeff
    (Submodule.starProjection_apply_mem (colRange s sc wt A) z))

theorem colCoeff_spec (s : Set ℝ) (sc : V → ℝ → ℂ) (wt : V → ℝ) (A : Finset V)
    (z : ColumnL2 V) :
    (colRange s sc wt A).starProjection z = ∑ v ∈ A, colCoeff s sc wt A z v • col s sc wt v :=
  Classical.choose_spec (colRange_exists_coeff
    (Submodule.starProjection_apply_mem (colRange s sc wt A) z))

open scoped Classical in
/-- The pointwise physical part of the projection: `∑ c_v φ_v` over admissible labels. -/
noncomputable def colPhys (s : Set ℝ) (sc : V → ℝ → ℂ) (wt : V → ℝ) (A : Finset V)
    (z : ColumnL2 V) (y : ℝ) : ℂ :=
  ∑ v ∈ A, if ColOK s sc wt v then colCoeff s sc wt A z v * sc v y else 0

open scoped Classical in
theorem colProj_coeFn {s : Set ℝ} (sc : V → ℝ → ℂ) (wt : V → ℝ) (A : Finset V)
    (z : ColumnL2 V) :
    ∀ᵐ y ∂volume, y ∈ s → ((colRange s sc wt A).starProjection z : ℝ → ColumnHilbert V) y =
      ∑ v ∈ A, if ColOK s sc wt v then
        colCoeff s sc wt A z v • privateColumnValue sc wt v y else 0 := by
  have hcol : ∀ v : V, ∀ᵐ y ∂volume, y ∈ s →
      ((colCoeff s sc wt A z v • col s sc wt v : ColumnL2 V) : ℝ → ColumnHilbert V) y =
        if ColOK s sc wt v then colCoeff s sc wt A z v • privateColumnValue sc wt v y else 0 := by
    intro v
    by_cases h : ColOK s sc wt v
    · filter_upwards [Lp.coeFn_smul (colCoeff s sc wt A z v) (col s sc wt v), col_coeFn h]
        with y h1 h2 hys
      rw [h1, Pi.smul_apply, h2, Set.indicator_of_mem hys]
      simp only [h, ↓reduceIte]
    · filter_upwards [Lp.coeFn_zero (ColumnHilbert V) 2 volume] with y hy _
      rw [col_of_not h, smul_zero, hy]
      simp only [h, ↓reduceIte]; rfl
  have hall : ∀ᵐ y ∂volume, ∀ v ∈ A, y ∈ s →
      ((colCoeff s sc wt A z v • col s sc wt v : ColumnL2 V) : ℝ → ColumnHilbert V) y =
        if ColOK s sc wt v then colCoeff s sc wt A z v • privateColumnValue sc wt v y else 0 :=
    (Filter.eventually_all_finset _).mpr fun v _ => hcol v
  filter_upwards [hall, Lp.coeFn_fun_finsetSum A
    (fun v => colCoeff s sc wt A z v • col s sc wt v)] with y hy hsum hys
  rw [colCoeff_spec, hsum]
  exact Finset.sum_congr rfl fun v hv => hy v hv hys

open scoped Classical in
theorem colProj_none {s : Set ℝ} (sc : V → ℝ → ℂ) (wt : V → ℝ) (A : Finset V)
    (z : ColumnL2 V) :
    ∀ᵐ y ∂volume, y ∈ s → ((colRange s sc wt A).starProjection z : ℝ → ColumnHilbert V) y none =
      colPhys s sc wt A z y := by
  filter_upwards [colProj_coeFn (s := s) sc wt A z] with y hy hys
  rw [hy hys, colPhys, columnHilbert_sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs
  · simp [privateColumnValue_physical, smul_eq_mul]
  · rfl

open scoped Classical in
theorem colProj_some {s : Set ℝ} (sc : V → ℝ → ℂ) (wt : V → ℝ) (A : Finset V)
    (z : ColumnL2 V) (u : V) :
    ∀ᵐ y ∂volume, y ∈ s →
      ((colRange s sc wt A).starProjection z : ℝ → ColumnHilbert V) y (some u) =
        if u ∈ A ∧ ColOK s sc wt u then colCoeff s sc wt A z u * (Real.sqrt (wt u) : ℂ)
        else 0 := by
  filter_upwards [colProj_coeFn (s := s) sc wt A z] with y hy hys
  rw [hy hys, columnHilbert_sum_apply]
  by_cases hu : u ∈ A
  · rw [Finset.sum_eq_single u]
    · by_cases h1 : ColOK s sc wt u
      · simp [h1, hu, privateColumnValue_private, smul_eq_mul]
      · simp only [h1, ↓reduceIte, and_false]; rfl
    · intro b _ hb
      split_ifs
      · simp [privateColumnValue_private, Ne.symm hb]
      · rfl
    · intro h; exact absurd hu h
  · simp only [hu, false_and, ↓reduceIte]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hb' : u ≠ b := fun h => hu (h ▸ hb)
    split_ifs
    · simp [privateColumnValue_private, hb']
    · rfl

theorem colPhys_measurable (s : Set ℝ) (sc : V → ℝ → ℂ) (wt : V → ℝ) (A : Finset V)
    (z : ColumnL2 V) : Measurable (colPhys s sc wt A z) := by
  classical
  unfold colPhys
  refine Finset.measurable_sum _ fun v _ => ?_
  split_ifs with h
  · exact measurable_const.mul h.2.2.1
  · exact measurable_const

/-- Private-coordinate recovery: `|c_v|² w_v |s| ≤ ∫_s ‖P z‖²`. -/
theorem colCoeff_recovery {s : Set ℝ} (sc : V → ℝ → ℂ) (wt : V → ℝ) (A : Finset V)
    (z : ColumnL2 V) {u : V} (hu : u ∈ A) (h : ColOK s sc wt u) :
    ‖colCoeff s sc wt A z u‖ ^ 2 * wt u * volume.real s ≤
      ∫ y in s, ‖((colRange s sc wt A).starProjection z : ℝ → ColumnHilbert V) y‖ ^ 2 := by
  classical
  have : IsFiniteMeasure (volume.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact h.2.1⟩
  have hpt : ∀ᵐ y ∂volume.restrict s, ‖colCoeff s sc wt A z u‖ ^ 2 * wt u ≤
      ‖((colRange s sc wt A).starProjection z : ℝ → ColumnHilbert V) y‖ ^ 2 := by
    rw [ae_restrict_iff' h.1]
    filter_upwards [colProj_some (s := s) sc wt A z u] with y hy hys
    have hc := norm_coord_le
      (((colRange s sc wt A).starProjection z : ℝ → ColumnHilbert V) y) (some u)
    rw [hy hys] at hc
    simp only [hu, h, and_self, ↓reduceIte, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] at hc
    have hw := Real.sq_sqrt h.2.2.2.2.1
    calc ‖colCoeff s sc wt A z u‖ ^ 2 * wt u
        = (‖colCoeff s sc wt A z u‖ * Real.sqrt (wt u)) ^ 2 := by rw [mul_pow, hw]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hc 2
  calc ‖colCoeff s sc wt A z u‖ ^ 2 * wt u * volume.real s
      = ∫ _ in s, ‖colCoeff s sc wt A z u‖ ^ 2 * wt u := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ _ := integral_mono_ae (integrable_const _) (integrableOn_norm_sq_Lp _ s) hpt

end ColRange2

/-- The data of the accurate high fits of one input (blueprint prop:base, proof lines
1634-1641): a predictor system, the delay `K₀`, coarse cells tested at depth `+K₀`, fit labels
`Fin M` with private weight one, the input `f` in slot `e` at accuracy `e^{-k}`. -/
structure AccSetup where
  /-- Dyadic grid used for the accurate high-fit construction. -/
  G : RealDyadicGrid
  /-- Root cell for the accurate high-fit construction. -/
  J : ℤ × ℤ
  /-- Number of fine-grid generations below the root. -/
  N : ℕ
  /-- Delay between coarse fitting cells and their fine descendants. -/
  K₀ : ℕ
  /-- Finite label type of the predictor column system. -/
  V₀ : Type
  [fin₀ : Fintype V₀]
  /-- Predictor columns available along the dyadic paths. -/
  P₀ : PathColumnSystem G J N V₀
  /-- Maximum number of additional fit labels. -/
  M : ℕ
  /-- Input function fitted in the selected high slot. -/
  f : ℝ → ℂ
  /-- Admissible local kernels assigned to the fitting cells. -/
  w : ℤ × ℤ → ℝ × ℝ → ℂ
  /-- High slot occupied by the input being fitted. -/
  e : Fin 4
  /-- Integrability exponent used in the high-fit residual estimates. -/
  q : ℝ
  /-- Accuracy exponent specifying the high-fit error threshold. -/
  k : ℕ
  /-- Complexity exponent supplied to the high-fit oracle. -/
  c₂ : ℕ
  /-- Complexity budget supplied to the high-fit oracle. -/
  B : ℝ

attribute [instance] AccSetup.fin₀

namespace AccSetup
variable (S : AccSetup)

/-- The combined labels: predictors and fit labels. -/
abbrev W : Type := S.V₀ ⊕ Fin S.M

/-- The cell of an index. -/
noncomputable abbrev cell (c : ℤ × ℤ) : Set ℝ := dyadicGridCell S.G c.1 c.2

/-- The depth of the coarse tree. -/
def Nc : ℕ := S.N - S.K₀

/-- The fine cells of a coarse cell. -/
noncomputable def fine (I : ℤ × ℤ) : Finset (ℤ × ℤ) := dyadicGeneration S.G I S.K₀

open scoped Classical in
/-- The input `1_J f` as an `L²` class. -/
noncomputable def input : Lp ℂ 2 (volume : Measure ℝ) :=
  if h : MemLp ((S.cell S.J).indicator S.f) 2 volume then h.toLp _ else 0

/-- The column input. -/
noncomputable def Z : ColumnL2 S.W := physicalColumnInput S.input

/-- Scalars at a fine cell for the fit list `a`. -/
noncomputable def sc (Q : ℤ × ℤ) (a : ℕ → ℝ → ℂ) : S.W → ℝ → ℂ :=
  Sum.elim (S.P₀.scalarAt Q) (fun m => a m)

/-- Private weights: `ε` for predictors, one for fits. -/
noncomputable def wt : S.W → ℝ := Sum.elim S.P₀.weight (fun _ => 1)

/-- The labels available at a fine cell with `n` fit labels. -/
noncomputable def lab (Q : ℤ × ℤ) (n : ℕ) : Finset S.W := (S.P₀.avail Q).disjSum (fitLabels S.M n)

/-- The projection at a fine cell. -/
noncomputable def proj (Q : ℤ × ℤ) (a : ℕ → ℝ → ℂ) (n : ℕ) : ColumnL2 S.W →L[ℂ] ColumnL2 S.W :=
  (colRange (S.cell Q) (S.sc Q a) S.wt (S.lab Q n)).starProjection

/-- The pointwise physical part of the fine projections on a coarse cell. -/
noncomputable def phys (I : ℤ × ℤ) (a : ℕ → ℝ → ℂ) (n : ℕ) (y : ℝ) : ℂ :=
  ∑ Q ∈ S.fine I, (S.cell Q).indicator
    (colPhys (S.cell Q) (S.sc Q a) S.wt (S.lab Q n) S.Z) y

/-- The coarse residual `f - (P_{s+K₀} F)_phys`. -/
noncomputable def res (I : ℤ × ℤ) (a : ℕ → ℝ → ℂ) (n : ℕ) (y : ℝ) : ℂ := S.f y - S.phys I a n y

/-- The stopping predicate on coarse cells. -/
def P (I : ℤ × ℤ) (a : ℕ → ℝ → ℂ) (n : ℕ) : Prop :=
  I ∉ dyadicFiniteTree S.G S.J S.Nc ∨
    FormSmall (dyadicGridLeft S.G I.1 I.2) (dyadicGridLength S.G I.1) (S.w I) S.e S.q
      (S.res I a n) (Real.exp (-(S.k : ℝ)))

/-- The oracle. -/
noncomputable def O (I : ℤ × ℤ) (a : ℕ → ℝ → ℂ) (n : ℕ) : ℝ → ℂ :=
  fitOracleAtom S.c₂ S.B (dyadicGridLeft S.G I.1 I.2) (dyadicGridLength S.G I.1) (S.res I a n)

/-- The fine energy of a coarse cell. -/
noncomputable def energy (I : ℤ × ℤ) (a : ℕ → ℝ → ℂ) (n : ℕ) : ℝ :=
  ∑ Q ∈ S.fine I, ‖S.proj Q a n S.Z‖ ^ 2

/-- The greedy attempt structure of the accurate fits. -/
noncomputable def tree : GreedyTree := ⟨S.G, S.J, S.Nc, S.M, S.P, S.O, 4 * S.B ^ 2⟩

/-- Hypotheses on the data. -/
structure Hyp : Prop where
  f_meas : Measurable S.f
  f_norm_root : eLpNorm S.f 2
    (normalizedIntervalMeasure (dyadicGridLeft S.G S.J.1 S.J.2) (dyadicGridLength S.G S.J.1)) ≤ 1
  f_norm : ∀ c ∈ dyadicFiniteTree S.G S.J S.N, kernelHull S.G S.J S.N S.w c → eLpNorm S.f 2
    (normalizedIntervalMeasure (dyadicGridLeft S.G c.1 c.2) (dyadicGridLength S.G c.1)) ≤ 1
  B_pos : 0 < S.B
  K₀_le : S.K₀ ≤ S.N
  detect : ∀ I a n, I ∈ dyadicFiniteTree S.G S.J S.Nc → Measurable (S.res I a n) →
    eLpNorm (S.res I a n) 2 (normalizedIntervalMeasure (dyadicGridLeft S.G I.1 I.2)
      (dyadicGridLength S.G I.1)) ≤ ENNReal.ofReal 2 →
    ¬ FormSmall (dyadicGridLeft S.G I.1 I.2) (dyadicGridLength S.G I.1) (S.w I) S.e S.q
      (S.res I a n) (Real.exp (-(S.k : ℝ))) →
    ∃ p, FitChartGood S.c₂ S.B (dyadicGridLeft S.G I.1 I.2) (dyadicGridLength S.G I.1)
      (S.res I a n) p

variable {S}

theorem coarse_fine {I Q : ℤ × ℤ} (hI : I ∈ dyadicFiniteTree S.G S.J S.Nc) (hQ : Q ∈ S.fine I)
    (h : S.Hyp) : Q ∈ dyadicFiniteTree S.G S.J S.N := by
  have hIm := (dyadicFiniteTree_mem_iff S.G S.J I S.Nc).mp hI
  refine (dyadicFiniteTree_mem_iff S.G S.J Q S.N).mpr
    ⟨(dyadicGeneration_subset S.G I S.K₀ hQ).trans hIm.1, ?_⟩
  have := dyadicGeneration_depth S.G I S.K₀ hQ
  have := h.K₀_le
  have h2 := hIm.2
  simp only [Nc] at h2
  omega

theorem coarse_tree {I : ℤ × ℤ} (h : S.Hyp) (hI : I ∈ dyadicFiniteTree S.G S.J S.Nc) :
    I ∈ dyadicFiniteTree S.G S.J S.N := by
  have hIm := (dyadicFiniteTree_mem_iff S.G S.J I S.Nc).mp hI
  refine (dyadicFiniteTree_mem_iff S.G S.J I S.N).mpr ⟨hIm.1, ?_⟩
  have := h.K₀_le
  have h2 := hIm.2
  simp only [Nc] at h2
  omega

theorem wt_pos (v : S.W) : 0 < S.wt v := by
  cases v with
  | inl v => exact S.P₀.weight_pos v
  | inr m => exact one_pos

theorem wt_le (v : S.W) : S.wt v ≤ 1 := by
  cases v with
  | inl v => exact S.P₀.weight_le v
  | inr m => exact le_rfl

/-- Column data at a fine cell for a list of bounded measurable atoms. -/
theorem colData (Q : ℤ × ℤ) {a : ℕ → ℝ → ℂ} (ha : ∀ i, Measurable (a i) ∧ ∀ y, ‖a i y‖ ≤ 1) :
    ColData (S.sc Q a) S.wt := by
  intro v
  cases v with
  | inl v => exact ⟨S.P₀.scalar_meas Q v, S.P₀.scalar_bound Q v, (S.P₀.weight_pos v).le,
      S.P₀.weight_le v⟩
  | inr m => exact ⟨(ha m).1, (ha m).2, zero_le_one, le_rfl⟩

open scoped Classical in
theorem lab_succ (Q : ℤ × ℤ) {n : ℕ} (hn : n < S.M) :
    S.lab Q (n + 1) = insert (Sum.inr (⟨n, hn⟩ : Fin S.M)) (S.lab Q n) := by
  ext v
  cases v with
  | inl v => simp [lab, Finset.inl_mem_disjSum]
  | inr m =>
    simp only [lab, Finset.mem_insert, Finset.inr_mem_disjSum, fitLabels, Finset.mem_filter,
      Finset.mem_univ, true_and, Sum.inr.injEq]
    constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (h | h)
      · subst h; simp
      · omega

theorem not_mem_lab (Q : ℤ × ℤ) {n : ℕ} (hn : n < S.M) :
    (Sum.inr (⟨n, hn⟩ : Fin S.M)) ∉ S.lab Q n := by
  simp [lab, fitLabels]

end AccSetup

theorem setIntegral_cell_eq_sum_generation_complex (G : RealDyadicGrid) (I : ℤ × ℤ) (n : ℕ)
    {F : ℝ → ℂ} (hF : IntegrableOn F (dyadicGridCell G I.1 I.2)) :
    ∫ y in dyadicGridCell G I.1 I.2, F y =
      ∑ Q ∈ dyadicGeneration G I n, ∫ y in dyadicGridCell G Q.1 Q.2, F y := by
  rw [← integral_biUnion_finset (dyadicGeneration G I n)
    (fun Q _ => dyadicGridCell_measurable G Q.1 Q.2) (dyadicGeneration_pairwiseDisjoint G I n)
    (fun Q hQ => hF.mono_set (dyadicGeneration_subset G I n hQ)), dyadicGeneration_union]

theorem col_congr_sc {V : Type} [Fintype V] {s : Set ℝ} {sc sc' : V → ℝ → ℂ} {wt : V → ℝ}
    {v : V} (h : sc v = sc' v) : col s sc wt v = col s sc' wt v := by
  classical
  unfold col ColOK privateColumnValue
  simp only [h]
  split_ifs <;> rfl

theorem colRange_congr_sc {V : Type} [Fintype V] {s : Set ℝ} {sc sc' : V → ℝ → ℂ}
    {wt : V → ℝ} {A : Finset V} (h : ∀ v ∈ A, sc v = sc' v) :
    colRange s sc wt A = colRange s sc' wt A := by
  unfold colRange
  congr 1
  exact Set.image_congr fun v hv => col_congr_sc (h v hv)

namespace AccSetup
variable {S : AccSetup}

theorem Hyp.memLp (h : S.Hyp) : MemLp ((S.cell S.J).indicator S.f) 2 volume := by
  refine (memLp_indicator_iff_restrict (dyadicGridCell_measurable _ _ _)).mpr ?_
  exact memLp_Ico_of_normalized (dyadicGridLength_pos S.G S.J.1)
    (ne_top_of_le_ne_top ENNReal.one_ne_top h.f_norm_root)

theorem Hyp.input_ae (h : S.Hyp) :
    (S.input : ℝ → ℂ) =ᵐ[volume] (S.cell S.J).indicator S.f := by
  unfold input
  rw [dite_eq_left_of_eq_true (eq_true h.memLp)]
  exact MemLp.coeFn_toLp _

theorem Z_private (u : S.V₀ ⊕ Fin S.M) :
    ∀ᵐ y ∂volume, (S.Z : ℝ → ColumnHilbert S.W) y (some u) = 0 := by
  classical
  filter_upwards [physicalColumnInput_coeFn (V := S.W) S.input] with y hy
  rw [Z, hy]
  simp

theorem Z_none : ∀ᵐ y ∂volume, (S.Z : ℝ → ColumnHilbert S.W) y none = (S.input : ℝ → ℂ) y := by
  classical
  filter_upwards [physicalColumnInput_coeFn (V := S.W) S.input] with y hy
  rw [Z, hy]
  simp

theorem Hyp.Z_none_cell (h : S.Hyp) {c : ℤ × ℤ} (hc : c ∈ dyadicFiniteTree S.G S.J S.N) :
    ∀ᵐ y ∂volume, y ∈ S.cell c → (S.Z : ℝ → ColumnHilbert S.W) y none = S.f y := by
  have hcJ := ((dyadicFiniteTree_mem_iff S.G S.J c S.N).mp hc).1
  filter_upwards [Z_none (S := S), h.input_ae] with y h1 h2 hy
  rw [h1, h2, Set.indicator_of_mem (hcJ hy)]

/-- The input energy on a fine-tree cell is at most its length. -/
theorem Hyp.energy_cell_le (h : S.Hyp) {c : ℤ × ℤ} (hc : c ∈ dyadicFiniteTree S.G S.J S.N)
    (hT : kernelHull S.G S.J S.N S.w c) :
    ∫ y in S.cell c, ‖(S.Z : ℝ → ColumnHilbert S.W) y‖ ^ 2 ≤ dyadicGridLength S.G c.1 := by
  have hs := dyadicGridCell_measurable S.G c.1 c.2
  have hr := dyadicGridLength_pos S.G c.1
  have heq : ∫ y in S.cell c, ‖(S.Z : ℝ → ColumnHilbert S.W) y‖ ^ 2 =
      ∫ y in S.cell c, ‖S.f y‖ ^ 2 := by
    refine setIntegral_congr_ae hs ?_
    have hcJ := ((dyadicFiniteTree_mem_iff S.G S.J c S.N).mp hc).1
    filter_upwards [physicalColumnInput_coeFn (V := S.W) S.input, h.input_ae] with y h1 h2 hy
    rw [Z, h1, h2, Set.indicator_of_mem (hcJ hy)]
    simp [norm_smul]
  have hn := h.f_norm c hc hT
  rw [← ENNReal.ofReal_one] at hn
  have hsq := sqrt_normalized_le_of_eLpNorm hr zero_le_one hn
  rw [Real.sqrt_le_iff] at hsq
  have h2 := hsq.2
  rw [one_pow, inv_mul_le_iff₀ hr, mul_one] at h2
  rw [heq]
  exact h2

theorem phys_eq_on {I Q : ℤ × ℤ} (hQ : Q ∈ S.fine I) {y : ℝ} (hy : y ∈ S.cell Q)
    (a : ℕ → ℝ → ℂ) (n : ℕ) :
    S.phys I a n y = colPhys (S.cell Q) (S.sc Q a) S.wt (S.lab Q n) S.Z y := by
  unfold phys
  rw [Finset.sum_eq_single Q]
  · rw [Set.indicator_of_mem hy]
  · intro Q' hQ' hne
    have hd := dyadicGeneration_pairwiseDisjoint S.G I S.K₀ hQ' hQ hne
    rw [Set.indicator_of_notMem (Set.disjoint_right.mp hd hy)]
  · intro h; exact absurd hQ h

/-- On a fine cell, the residual is the physical coordinate of `Z - P Z`. -/
theorem Hyp.res_ae (h : S.Hyp) {I Q : ℤ × ℤ} (hI : I ∈ dyadicFiniteTree S.G S.J S.Nc)
    (hQ : Q ∈ S.fine I) (a : ℕ → ℝ → ℂ) (n : ℕ) :
    ∀ᵐ y ∂volume, y ∈ S.cell Q → S.res I a n y =
      ((S.Z - S.proj Q a n S.Z : ColumnL2 S.W) : ℝ → ColumnHilbert S.W) y none := by
  have hQT := coarse_fine hI hQ h
  filter_upwards [h.Z_none_cell hQT, colProj_none (s := S.cell Q) (S.sc Q a) S.wt (S.lab Q n) S.Z,
    Lp.coeFn_sub S.Z (S.proj Q a n S.Z)] with y h1 h2 h3 hy
  rw [h3, Pi.sub_apply, PiLp.sub_apply, h1 hy]
  unfold res
  rw [phys_eq_on hQ hy, proj, h2 hy]

theorem phys_measurable (I : ℤ × ℤ) (a : ℕ → ℝ → ℂ) (n : ℕ) : Measurable (S.phys I a n) :=
  Finset.measurable_sum _ fun _ _ =>
    (colPhys_measurable _ _ _ _ _).indicator (dyadicGridCell_measurable _ _ _)

theorem Hyp.res_measurable (h : S.Hyp) (I : ℤ × ℤ) (a : ℕ → ℝ → ℂ) (n : ℕ) :
    Measurable (S.res I a n) :=
  h.f_meas.sub (phys_measurable I a n)

end AccSetup

theorem colPhys_bound {V : Type} [Fintype V] (s : Set ℝ) (sc : V → ℝ → ℂ) (wt : V → ℝ)
    (A : Finset V) (z : ColumnL2 V) (y : ℝ) :
    ‖colPhys s sc wt A z y‖ ≤ ∑ v ∈ A, ‖colCoeff s sc wt A z v‖ := by
  classical
  unfold colPhys
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  split_ifs with h
  · rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (h.2.2.2.1 y)
  · simp

namespace AccSetup
variable {S : AccSetup}

theorem phys_bound (I : ℤ × ℤ) (a : ℕ → ℝ → ℂ) (n : ℕ) :
    ∃ C, ∀ y, ‖S.phys I a n y‖ ≤ C := by
  refine ⟨∑ Q ∈ S.fine I, ∑ v ∈ S.lab Q n,
    ‖colCoeff (S.cell Q) (S.sc Q a) S.wt (S.lab Q n) S.Z v‖, fun y => ?_⟩
  unfold phys
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun Q _ => ?_)
  by_cases hy : y ∈ S.cell Q
  · rw [Set.indicator_of_mem hy]; exact colPhys_bound _ _ _ _ _ _
  · rw [Set.indicator_of_notMem hy, norm_zero]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- The fine projections on a coarse cell have physical `L²(I)` energy at most `|I|`. -/
theorem Hyp.phys_sq_le (h : S.Hyp) {I : ℤ × ℤ} (hI : I ∈ dyadicFiniteTree S.G S.J S.Nc)
    (hT : kernelHull S.G S.J S.N S.w I)
    (a : ℕ → ℝ → ℂ) (n : ℕ) :
    ∫ y in S.cell I, ‖S.phys I a n y‖ ^ 2 ≤ dyadicGridLength S.G I.1 := by
  obtain ⟨C, hC⟩ := phys_bound (S := S) I a n
  have := cell_isFiniteMeasure S.G I.1 I.2
  have hint : IntegrableOn (fun y => ‖S.phys I a n y‖ ^ 2) (S.cell I) :=
    Integrable.of_bound (C := C ^ 2) ((phys_measurable I a n).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC y) 2)
  rw [setIntegral_cell_eq_sum_generation_real S.G I S.K₀ hint]
  calc ∑ Q ∈ dyadicGeneration S.G I S.K₀, ∫ y in S.cell Q, ‖S.phys I a n y‖ ^ 2
      ≤ ∑ Q ∈ dyadicGeneration S.G I S.K₀, ∫ y in S.cell Q,
          ‖(S.Z : ℝ → ColumnHilbert S.W) y‖ ^ 2 := by
        refine Finset.sum_le_sum fun Q hQ => ?_
        have hs := dyadicGridCell_measurable S.G Q.1 Q.2
        calc ∫ y in S.cell Q, ‖S.phys I a n y‖ ^ 2
            ≤ ∫ y in S.cell Q, ‖(S.proj Q a n S.Z : ℝ → ColumnHilbert S.W) y‖ ^ 2 := by
              refine integral_mono_ae (hint.mono_set (dyadicGeneration_subset S.G I S.K₀ hQ))
                (integrableOn_norm_sq_Lp _ _) ?_
              rw [Filter.EventuallyLE, ae_restrict_iff' hs]
              filter_upwards [colProj_none (s := S.cell Q) (S.sc Q a) S.wt (S.lab Q n) S.Z]
                with y hy hyQ
              rw [phys_eq_on hQ hyQ, ← hy hyQ]
              exact pow_le_pow_left₀ (norm_nonneg _) (norm_coord_le _ _) 2
          _ ≤ ‖S.proj Q a n S.Z‖ ^ 2 := by
              rw [columnInput_norm_sq_integral]
              exact setIntegral_le_integral ((Lp.memLp _).integrable_norm_pow two_ne_zero)
                (Filter.Eventually.of_forall fun _ => by positivity)
          _ ≤ _ := colRange_energy_le hs _ _ _ _
    _ = ∫ y in S.cell I, ‖(S.Z : ℝ → ColumnHilbert S.W) y‖ ^ 2 :=
        (setIntegral_cell_eq_sum_generation_real S.G I S.K₀ (integrableOn_norm_sq_Lp _ _)).symm
    _ ≤ _ := h.energy_cell_le (coarse_tree h hI) hT

/-- The coarse residual has normalized `L²` norm at most two. -/
theorem Hyp.res_eLpNorm_le (h : S.Hyp) {I : ℤ × ℤ} (hI : I ∈ dyadicFiniteTree S.G S.J S.Nc)
    (hT : kernelHull S.G S.J S.N S.w I) (a : ℕ → ℝ → ℂ) (n : ℕ) :
    eLpNorm (S.res I a n) 2 (normalizedIntervalMeasure (dyadicGridLeft S.G I.1 I.2)
      (dyadicGridLength S.G I.1)) ≤ ENNReal.ofReal 2 := by
  have hr := dyadicGridLength_pos S.G I.1
  have h1 : eLpNorm S.f 2 (normalizedIntervalMeasure (dyadicGridLeft S.G I.1 I.2)
      (dyadicGridLength S.G I.1)) ≤ ENNReal.ofReal 1 := by
    rw [ENNReal.ofReal_one]; exact h.f_norm I (coarse_tree h hI) hT
  obtain ⟨C, hC⟩ := phys_bound (S := S) I a n
  have hmem : MemLp (S.phys I a n) 2 (volume.restrict (Set.Ico (dyadicGridLeft S.G I.1 I.2)
      (dyadicGridLeft S.G I.1 I.2 + dyadicGridLength S.G I.1))) := by
    have := cell_isFiniteMeasure S.G I.1 I.2
    exact MemLp.of_bound (phys_measurable I a n).aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)
  have h2 : eLpNorm (S.phys I a n) 2 (normalizedIntervalMeasure (dyadicGridLeft S.G I.1 I.2)
      (dyadicGridLength S.G I.1)) ≤ ENNReal.ofReal 1 :=
    eLpNorm_normalized_le_of_integral hr hmem zero_le_one (by
      have := h.phys_sq_le hI hT a n
      simpa only [one_pow, one_mul, cell, dyadicGridCell] using this)
  calc eLpNorm (S.res I a n) 2 _ ≤ eLpNorm S.f 2 _ + eLpNorm (S.phys I a n) 2 _ :=
        eLpNorm_sub_le (by norm_num)
    _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal 1 := add_le_add h1 h2
    _ = ENNReal.ofReal 2 := by
        rw [← ENNReal.ofReal_add zero_le_one zero_le_one]; norm_num

theorem sum_fine_length (I : ℤ × ℤ) :
    ∑ Q ∈ S.fine I, dyadicGridLength S.G Q.1 = dyadicGridLength S.G I.1 := by
  have := cell_isFiniteMeasure S.G I.1 I.2
  have h := setIntegral_cell_eq_sum_generation_real S.G I S.K₀ (F := fun _ => (1 : ℝ))
    (integrableOn_const (by rw [dyadicGridCell_volume]; exact ENNReal.ofReal_ne_top))
  simp only [setIntegral_const, smul_eq_mul, mul_one, volume_real_cell] at h
  exact h.symm

/-- Blueprint prop:base, proof lines 1634-1637: inserting the detection atom with a fresh label
on all fine subcells of a failing coarse cell increases the fine energy by `B⁻²|I|/4`. -/
theorem Hyp.gain (h : S.Hyp) {I : ℤ × ℤ} (hI : I ∈ dyadicFiniteTree S.G S.J S.Nc)
    {a : ℕ → ℝ → ℂ} {n : ℕ} (hn : n < S.M) (hP : ¬ S.P I a n) :
    S.energy I a n + (S.B⁻¹) ^ 2 * dyadicGridLength S.G I.1 / 4 ≤
      S.energy I (Function.update a n (S.O I a n)) (n + 1) := by
  classical
  simp only [P, not_or, not_not] at hP
  obtain ⟨hIt, hns⟩ := hP
  have hIT := kernelHull_of_not_formSmall (coarse_tree h hIt) hns
  obtain ⟨p, hgood, hO⟩ := fitOracleAtom_good
    (h.detect I a n hIt (h.res_measurable I a n)
      (h.res_eLpNorm_le hIt hIT a n) hns)
  set φ := S.O I a n with hφdef
  have hφe : φ = quadraticChartAtom p.2 := hO
  have hφm : Measurable φ := fitOracleAtom_measurable _ _ _ _ _
  have hφb : ∀ y, ‖φ y‖ ≤ 1 := fitOracleAtom_bound _ _ _ _ _
  set a' := Function.update a n φ
  set v : S.W := Sum.inr ⟨n, hn⟩
  have hr := dyadicGridLength_pos S.G I.1
  -- per fine cell
  set m : ℤ × ℤ → ℂ := fun Q => ∫ y in S.cell Q, conj (φ y) * S.res I a n y
  have hcell : ∀ Q ∈ S.fine I, ‖S.proj Q a n S.Z‖ ^ 2 +
      ‖m Q‖ ^ 2 / (4 * dyadicGridLength S.G Q.1) ≤ ‖S.proj Q a' (n + 1) S.Z‖ ^ 2 := by
    intro Q hQ
    have hs := dyadicGridCell_measurable S.G Q.1 Q.2
    have hsv : volume (S.cell Q) < ⊤ := by
      rw [dyadicGridCell_volume]; exact ENNReal.ofReal_lt_top
    have hcong : colRange (S.cell Q) (S.sc Q a) S.wt (S.lab Q n) =
        colRange (S.cell Q) (S.sc Q a') S.wt (S.lab Q n) := by
      refine colRange_congr_sc fun u hu => ?_
      cases u with
      | inl u => rfl
      | inr i =>
        have hi : (i : ℕ) < n := by
          simpa [lab, fitLabels] using hu
        simp only [sc, Sum.elim_inr, a', Function.update_of_ne (show (i : ℕ) ≠ n by omega)]
    have hok : ColOK (S.cell Q) (S.sc Q a') S.wt v := by
      refine ⟨hs, hsv, ?_, fun y => ?_, zero_le_one, le_rfl⟩
      · simp only [sc, Sum.elim_inr, a', v, Function.update_self]; exact hφm
      · simp only [sc, Sum.elim_inr, a', v, Function.update_self]; exact hφb y
    have hg := colRange_gain (not_mem_lab Q hn) hok S.Z (Z_private v)
    have hins : colRange (S.cell Q) (S.sc Q a') S.wt (insert v (S.lab Q n)) =
        colRange (S.cell Q) (S.sc Q a') S.wt (S.lab Q (n + 1)) := by rw [lab_succ Q hn]
    rw [starProjection_congr hins] at hg
    have hPeq : (colRange (S.cell Q) (S.sc Q a) S.wt (S.lab Q n)).starProjection S.Z =
        (colRange (S.cell Q) (S.sc Q a') S.wt (S.lab Q n)).starProjection S.Z :=
      starProjection_congr hcong S.Z
    have hmQ : ∫ y in S.cell Q, conj (S.sc Q a' v y) *
        ((S.Z - (colRange (S.cell Q) (S.sc Q a') S.wt (S.lab Q n)).starProjection S.Z :
          ColumnL2 S.W) : ℝ → ColumnHilbert S.W) y none = m Q := by
      rw [← hPeq]
      refine setIntegral_congr_ae hs ?_
      filter_upwards [h.res_ae hIt hQ a n] with y hy hyQ
      rw [hy hyQ]
      simp only [sc, Sum.elim_inr, a', Function.update_self, v, proj]
    rw [hmQ, volume_real_cell] at hg
    change ‖(colRange (S.cell Q) (S.sc Q a) S.wt (S.lab Q n)).starProjection S.Z‖ ^ 2 + _ ≤ _
    rw [hPeq]
    exact hg
  -- sum over the fine cells
  have hsum : S.energy I a n + ∑ Q ∈ S.fine I, ‖m Q‖ ^ 2 / (4 * dyadicGridLength S.G Q.1) ≤
      S.energy I a' (n + 1) := by
    unfold energy
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hcell
  -- Cauchy-Schwarz over the fine cells
  have hint : IntegrableOn (fun y => conj (φ y) * S.res I a n y) (S.cell I) := by
    have := cell_isFiniteMeasure S.G I.1 I.2
    obtain ⟨C, hC⟩ := phys_bound (S := S) I a n
    have hf : MemLp S.f 2 (volume.restrict (S.cell I)) :=
      memLp_Ico_of_normalized hr (ne_top_of_le_ne_top ENNReal.one_ne_top
        (h.f_norm I (coarse_tree h hI) hIT))
    have hph : MemLp (S.phys I a n) 2 (volume.restrict (S.cell I)) :=
      MemLp.of_bound (phys_measurable I a n).aestronglyMeasurable C
        (Filter.Eventually.of_forall hC)
    have hres : IntegrableOn (S.res I a n) (S.cell I) := (hf.sub hph).integrable one_le_two
    exact hres.bdd_mul (c := 1) (Complex.continuous_conj.measurable.comp hφm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa using hφb y)
  have hm_sum : ∑ Q ∈ S.fine I, m Q = ∫ y in S.cell I, conj (φ y) * S.res I a n y :=
    (setIntegral_cell_eq_sum_generation_complex S.G I S.K₀ hint).symm
  have hcorr : S.B⁻¹ * dyadicGridLength S.G I.1 ≤ ‖∫ y in S.cell I, conj (φ y) * S.res I a n y‖ :=
      by
    have hc := hgood.2.2
    rw [intervalIntegral_eq_cell hr.le] at hc
    rw [le_inv_mul_iff₀ hr] at hc
    have heq : ∫ x in Set.Ico (dyadicGridLeft S.G I.1 I.2)
        (dyadicGridLeft S.G I.1 I.2 + dyadicGridLength S.G I.1),
          S.res I a n x * conj (quadraticChartAtom p.2 x) =
        ∫ y in S.cell I, conj (φ y) * S.res I a n y := by
      refine setIntegral_congr_fun (dyadicGridCell_measurable _ _ _) fun y _ => ?_
      rw [hφe, mul_comm]
    rw [heq] at hc
    linarith
  have hlen := sum_fine_length (S := S) I
  have hsed := Finset.sq_sum_div_le_sum_sq_div (S.fine I) (fun Q => ‖m Q‖)
    (g := fun Q => 4 * dyadicGridLength S.G Q.1)
    (fun Q _ => by have := dyadicGridLength_pos S.G Q.1; positivity)
  have hden : ∑ Q ∈ S.fine I, 4 * dyadicGridLength S.G Q.1 = 4 * dyadicGridLength S.G I.1 := by
    rw [← Finset.mul_sum, hlen]
  rw [hden] at hsed
  have htri : ‖∫ y in S.cell I, conj (φ y) * S.res I a n y‖ ≤ ∑ Q ∈ S.fine I, ‖m Q‖ := by
    rw [← hm_sum]; exact norm_sum_le _ _
  have hlow : (S.B⁻¹) ^ 2 * dyadicGridLength S.G I.1 / 4 ≤
      (∑ Q ∈ S.fine I, ‖m Q‖) ^ 2 / (4 * dyadicGridLength S.G I.1) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : S.B⁻¹ * dyadicGridLength S.G I.1 ≤ ∑ Q ∈ S.fine I, ‖m Q‖ := hcorr.trans htri
    have h0 : 0 ≤ S.B⁻¹ * dyadicGridLength S.G I.1 :=
      mul_nonneg (inv_nonneg.mpr h.B_pos.le) hr.le
    have := pow_le_pow_left₀ h0 h1 2
    nlinarith only [hcorr, htri, h0]
  linarith

end AccSetup

theorem dyadicGeneration_one (G : RealDyadicGrid) (I : ℤ × ℤ) :
    dyadicGeneration G I 1 = dyadicChildren G I := by
  simp [dyadicGeneration]

/-- Generations below `I` regrouped by the children of `I`. -/
theorem dyadicGeneration_succ_eq_biUnion (G : RealDyadicGrid) (I : ℤ × ℤ) (n : ℕ) :
    dyadicGeneration G I (n + 1) =
      (dyadicChildren G I).biUnion (fun I' => dyadicGeneration G I' n) := by
  ext c
  simp only [Finset.mem_biUnion, dyadicGeneration_mem_iff]
  constructor
  · rintro ⟨hd, hc⟩
    refine ⟨ancAt G c (I.1 + 1), ?_, ?_, subset_ancAt G c (by push_cast at hd; omega)⟩
    · rw [← dyadicGeneration_one, dyadicGeneration_mem_iff]
      refine ⟨by simp [ancAt], ?_⟩
      exact dyadicGridCell_subset_of_common_point G (mem_dyadicIndex G _ _)
        (hc (dyadicGridCell_left_mem G c.1 c.2)) (by simp [ancAt])
    · simp only [ancAt]; push_cast at hd ⊢; omega
  · rintro ⟨I', hI', hd, hc⟩
    have h1 := dyadicChildren_depth G I I' hI'
    have h2 := dyadicChildren_subset G I I' hI'
    exact ⟨by push_cast; omega, hc.trans h2⟩

theorem dyadicChildren_generation_disjoint (G : RealDyadicGrid) (I : ℤ × ℤ) (n : ℕ) :
    ((dyadicChildren G I : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)).PairwiseDisjoint
      (fun I' => dyadicGeneration G I' n) := by
  intro I₁ h₁ I₂ h₂ hne
  refine Finset.disjoint_left.mpr fun c hc₁ hc₂ => hne ?_
  have e₁ := dyadicChildren_depth G I I₁ h₁
  have e₂ := dyadicChildren_depth G I I₂ h₂
  have s₁ := dyadicGeneration_subset G I₁ n hc₁
  have s₂ := dyadicGeneration_subset G I₂ n hc₂
  have hy := dyadicGridCell_left_mem G c.1 c.2
  exact dyadicGridCell_eq_of_common_point G (s₁ hy) (s₂ hy) (by omega)

namespace AccSetup
variable {S : AccSetup}

/-- Blueprint prop:base, line 1639 (orthogonal energy of the chronological fitting sequence):
with the same fit list, the fine energy of a coarse cell is at most the fine energies of its
children at the next stage. -/
theorem Hyp.energy_children (h : S.Hyp) {I : ℤ × ℤ} (hI : I ∈ dyadicFiniteTree S.G S.J S.Nc)
    (hIN : I.1 + 1 ≤ S.J.1 + S.Nc) {a : ℕ → ℝ → ℂ}
    (ha : ∀ i, Measurable (a i) ∧ ∀ y, ‖a i y‖ ≤ 1) (n : ℕ) :
    S.energy I a n ≤ ∑ I' ∈ dyadicChildren S.G I, S.energy I' a n := by
  classical
  have hQT : ∀ Q ∈ S.fine I, Q ∈ dyadicFiniteTree S.G S.J S.N := fun Q hQ => coarse_fine hI hQ h
  have hIm := (dyadicFiniteTree_mem_iff S.G S.J I S.Nc).mp hI
  have hchildT : ∀ Q ∈ S.fine I, ∀ Q' ∈ dyadicChildren S.G Q,
      Q' ∈ dyadicFiniteTree S.G S.J S.N := by
    intro Q hQ Q' hQ'
    have hQm := (dyadicFiniteTree_mem_iff S.G S.J Q S.N).mp (hQT Q hQ)
    refine (dyadicFiniteTree_mem_iff S.G S.J Q' S.N).mpr
      ⟨(dyadicChildren_subset S.G Q Q' hQ').trans hQm.1, ?_⟩
    have := dyadicChildren_depth S.G Q Q' hQ'
    have := dyadicGeneration_depth S.G I S.K₀ hQ
    have := h.K₀_le
    simp only [Nc] at hIN
    omega
  have hstep : ∀ Q ∈ S.fine I, ‖S.proj Q a n S.Z‖ ^ 2 ≤
      ∑ Q' ∈ dyadicChildren S.G Q, ‖S.proj Q' a n S.Z‖ ^ 2 := by
    intro Q hQ
    set! m := Classical.choose (dyadicGridCell_children S.G Q.1 Q.2)
    have hm := Classical.choose_spec (dyadicGridCell_children S.G Q.1 Q.2)
    have hch : dyadicChildren S.G Q = {(Q.1 + 1, m), (Q.1 + 1, m + 1)} := rfl
    have hne : ((Q.1 + 1, m) : ℤ × ℤ) ≠ (Q.1 + 1, m + 1) := by simp
    have hc₁ : ((Q.1 + 1, m) : ℤ × ℤ) ∈ dyadicChildren S.G Q := by rw [hch]; simp
    have hc₂ : ((Q.1 + 1, m + 1) : ℤ × ℤ) ∈ dyadicChildren S.G Q := by rw [hch]; simp
    rw [hch, Finset.sum_pair hne]
    have hd : Disjoint (dyadicGridCell S.G (Q.1 + 1) m) (dyadicGridCell S.G (Q.1 + 1) (m + 1)) :=
      dyadicGridCell_pairwiseDisjoint S.G (Q.1 + 1) (by omega)
    have hfin : ∀ c : ℤ × ℤ, volume (dyadicGridCell S.G c.1 c.2) < ⊤ := fun c => by
      rw [dyadicGridCell_volume]; exact ENNReal.ofReal_lt_top
    have hsub : ∀ c ∈ dyadicChildren S.G Q,
        dyadicGridCell S.G c.1 c.2 ⊆ dyadicGridCell S.G Q.1 Q.2 :=
      fun c hc => dyadicChildren_subset S.G Q c hc
    have hlab : ∀ c ∈ dyadicChildren S.G Q, S.lab Q n ⊆ S.lab c n := by
      intro c hc v hv
      cases v with
      | inl v =>
        simp only [lab, Finset.inl_mem_disjSum] at hv ⊢
        exact S.P₀.avail_mono c Q (hchildT Q hQ c hc) (hQT Q hQ) (hsub c hc) hv
      | inr i => simpa [lab] using hv
    have hcons : ∀ c ∈ dyadicChildren S.G Q, ∀ v ∈ S.lab Q n,
        ∀ y ∈ dyadicGridCell S.G c.1 c.2, S.sc Q a v y = S.sc c a v y := by
      intro c hc v hv y hy
      cases v with
      | inl v =>
        simp only [lab, Finset.inl_mem_disjSum] at hv
        simp only [sc, Sum.elim_inl]
        exact (S.P₀.consistent c Q (hchildT Q hQ c hc) (hQT Q hQ) (hsub c hc) v hv y hy).symm
      | inr i => rfl
    have := colRange_energy_split (dyadicGridCell_measurable S.G (Q.1 + 1) m) (hfin (Q.1 + 1, m))
      (dyadicGridCell_measurable S.G (Q.1 + 1) (m + 1)) (hfin (Q.1 + 1, m + 1)) hd (colData Q ha)
      (colData (Q.1 + 1, m) ha) (colData (Q.1 + 1, m + 1) ha) (hlab _ hc₁) (hlab _ hc₂)
      (hcons _ hc₁) (hcons _ hc₂) S.Z (A := S.lab Q n)
    unfold proj
    have hU : colRange (S.cell Q) (S.sc Q a) S.wt (S.lab Q n) =
        colRange (dyadicGridCell S.G (Q.1 + 1) m ∪ dyadicGridCell S.G (Q.1 + 1) (m + 1))
          (S.sc Q a) S.wt (S.lab Q n) :=
      congrArg (fun s => colRange s (S.sc Q a) S.wt (S.lab Q n)) hm
    rw [starProjection_congr hU S.Z]
    exact this
  calc S.energy I a n ≤ ∑ Q ∈ S.fine I, ∑ Q' ∈ dyadicChildren S.G Q, ‖S.proj Q' a n S.Z‖ ^ 2 :=
        Finset.sum_le_sum hstep
    _ = ∑ Q' ∈ dyadicGeneration S.G I (S.K₀ + 1), ‖S.proj Q' a n S.Z‖ ^ 2 := by
        rw [show dyadicGeneration S.G I (S.K₀ + 1) =
          (dyadicGeneration S.G I S.K₀).biUnion (dyadicChildren S.G) from rfl,
          Finset.sum_biUnion (dyadicGeneration_children_disjoint S.G I S.K₀)]
        rfl
    _ = ∑ I' ∈ dyadicChildren S.G I, S.energy I' a n := by
        rw [dyadicGeneration_succ_eq_biUnion,
          Finset.sum_biUnion (dyadicChildren_generation_disjoint S.G I S.K₀)]
        rfl

/-- Contraction: the fine energy of a coarse cell is at most the input energy on it. -/
theorem energy_le (I : ℤ × ℤ) (a : ℕ → ℝ → ℂ) (n : ℕ) :
    S.energy I a n ≤ ∫ y in S.cell I, ‖(S.Z : ℝ → ColumnHilbert S.W) y‖ ^ 2 := by
  rw [setIntegral_cell_eq_sum_generation_real S.G I S.K₀ (integrableOn_norm_sq_Lp _ _)]
  exact Finset.sum_le_sum fun Q _ => colRange_energy_le (dyadicGridCell_measurable _ _ _) _ _ _ _

theorem state_atoms (d : ℕ) (c : ℤ × ℤ) :
    ∀ i, Measurable ((fitState S.G S.M S.P S.O d c).1 i) ∧
      ∀ y, ‖(fitState S.G S.M S.P S.O d c).1 i y‖ ≤ 1 :=
  fitState_inv_all S.G S.M S.P S.O (fun φ => Measurable φ ∧ ∀ y, ‖φ y‖ ≤ 1)
    ⟨measurable_const, fun y => by simp⟩
    (fun _ _ _ => ⟨fitOracleAtom_measurable _ _ _ _ _, fitOracleAtom_bound _ _ _ _ _⟩) d c

theorem Hyp.cell_gain (h : S.Hyp) (d : ℕ) (c : ℤ × ℤ) :
    S.energy c (fitInherited S.G S.M S.P S.O d c).1 (fitInherited S.G S.M S.P S.O d c).2 +
        (S.B⁻¹) ^ 2 * dyadicGridLength S.G c.1 / 4 * fitNew S.G S.M S.P S.O d c ≤
      S.energy c (fitState S.G S.M S.P S.O d c).1 (fitState S.G S.M S.P S.O d c).2 := by
  have hg := fitGreedy_energy (M := S.M) (P := S.P c) (O := S.O c)
    (fun a n => S.energy c a n) (g := (S.B⁻¹) ^ 2 * dyadicGridLength S.G c.1 / 4)
    (fun a n hn hP => by
      have hIt : c ∈ dyadicFiniteTree S.G S.J S.Nc := by
        by_contra hc; exact hP (Or.inl hc)
      exact h.gain hIt hn hP) (fitInherited S.G S.M S.P S.O d c)
  rw [← fitState_eq_greedy] at hg
  have hc := (fitGreedy_count (P := S.P c) (O := S.O c) (fitInherited S.G S.M S.P S.O d c)
    (fitInherited_count_le S.G S.M S.P S.O d c)).1
  rw [← fitState_eq_greedy] at hc
  have hnew : ((fitState S.G S.M S.P S.O d c).2 - (fitInherited S.G S.M S.P S.O d c).2 : ℝ) =
      (fitNew S.G S.M S.P S.O d c : ℝ) := by
    unfold fitNew; rw [Nat.cast_sub hc]
  rw [hnew] at hg
  exact hg

/-- Blueprint prop:base, line 1639: the insertion gains of all coarse cells down to generation
`L` are at most the fine energy of that generation. -/
theorem Hyp.telescope (h : S.Hyp) {K : ℤ × ℤ} (hK : K ∈ dyadicFiniteTree S.G S.J S.Nc) :
    ∀ L : ℕ, K.1 + L ≤ S.J.1 + S.Nc →
      ∑ k ∈ Finset.range (L + 1), ∑ c ∈ dyadicGeneration S.G K k,
          (S.B⁻¹) ^ 2 * dyadicGridLength S.G c.1 / 4 * fitNew S.G S.M S.P S.O k c ≤
        ∑ c ∈ dyadicGeneration S.G K L,
          S.energy c (fitState S.G S.M S.P S.O L c).1 (fitState S.G S.M S.P S.O L c).2 := by
  intro L
  induction L with
  | zero =>
    intro _
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    refine Finset.sum_le_sum fun c _ => ?_
    have hg := h.cell_gain 0 c
    have h0 : 0 ≤ S.energy c (fitInherited S.G S.M S.P S.O 0 c).1
        (fitInherited S.G S.M S.P S.O 0 c).2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    linarith
  | succ d ih =>
    intro hd
    have hKm := (dyadicFiniteTree_mem_iff S.G S.J K S.Nc).mp hK
    rw [Finset.sum_range_succ]
    have hgen : dyadicGeneration S.G K (d + 1) =
        (dyadicGeneration S.G K d).biUnion (dyadicChildren S.G) := rfl
    have hstep := Finset.sum_le_sum fun c (_ : c ∈ dyadicGeneration S.G K (d + 1)) =>
      h.cell_gain (d + 1) c
    have hinh : ∑ p ∈ dyadicGeneration S.G K d,
        S.energy p (fitState S.G S.M S.P S.O d p).1 (fitState S.G S.M S.P S.O d p).2 ≤
        ∑ c ∈ dyadicGeneration S.G K (d + 1),
          S.energy c (fitInherited S.G S.M S.P S.O (d + 1) c).1
            (fitInherited S.G S.M S.P S.O (d + 1) c).2 := by
      rw [hgen, Finset.sum_biUnion (dyadicGeneration_children_disjoint S.G K d)]
      refine Finset.sum_le_sum fun p hp => ?_
      have hpd := dyadicGeneration_depth S.G K d hp
      have hpT : p ∈ dyadicFiniteTree S.G S.J S.Nc :=
        (dyadicFiniteTree_mem_iff S.G S.J p S.Nc).mpr
          ⟨(dyadicGeneration_subset S.G K d hp).trans hKm.1, by omega⟩
      refine (h.energy_children hpT (by omega) (state_atoms d p) _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun c hc => ?_
      simp only [fitInherited, dyadicParent_of_mem_children S.G hc]
    rw [Finset.sum_add_distrib] at hstep
    have := ih (by omega)
    linarith

/-- The insertion mass of the attempt rooted at `K` is at most `4 B² |K|`. -/
theorem Hyp.mass_le (h : S.Hyp) {K : ℤ × ℤ} (hK : K ∈ dyadicFiniteTree S.G S.J S.Nc) :
    dyadicWeightedMass S.G (S.tree.sub K) (S.tree.newAt K) ≤
      4 * S.B ^ 2 * dyadicGridLength S.G K.1 := by
  by_cases hKT : ¬ kernelHull S.G S.J S.N S.w K
  · have h0 : dyadicWeightedMass S.G (S.tree.sub K) (S.tree.newAt K) = 0 := by
      unfold dyadicWeightedMass
      refine Finset.sum_eq_zero fun c hc => ?_
      have hc' := (GreedyTree.sub_mem_iff (S := S.tree) hK c).mp hc
      have hP : ∀ a n, S.P c a n := fun a n => by
        by_cases hct : c ∈ dyadicFiniteTree S.G S.J S.Nc
        · refine Or.inr ?_
          rw [eq_zero_of_not_kernelHull (coarse_tree h hct) fun hc'' => hKT (hc''.mono hc'.2)]
          exact formSmall_zero_kernel (Real.exp_pos _).le
        · exact Or.inl hct
      simp only [GreedyTree.newAt, tree]
      rw [fitNew_eq_zero_of_P S.G S.M S.P S.O _ c hP]; simp
    rw [h0]; have := dyadicGridLength_pos S.G K.1; have := h.B_pos; positivity
  push Not at hKT
  set L := dyadicRemainingDepth S.J S.Nc K
  have hend := dyadicRemainingDepth_endpoint S.G S.J S.Nc hK
  have hdisj : ((Finset.range (L + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (dyadicGeneration S.G K) := by
    intro k _ k' _ hkk
    refine Finset.disjoint_left.mpr fun c hc hc' => hkk ?_
    have h1 := dyadicGeneration_depth S.G K k hc
    have h2 := dyadicGeneration_depth S.G K k' hc'
    omega
  have hmass : (S.B⁻¹) ^ 2 / 4 * dyadicWeightedMass S.G (S.tree.sub K) (S.tree.newAt K) =
      ∑ k ∈ Finset.range (L + 1), ∑ c ∈ dyadicGeneration S.G K k,
        (S.B⁻¹) ^ 2 * dyadicGridLength S.G c.1 / 4 * fitNew S.G S.M S.P S.O k c := by
    unfold dyadicWeightedMass GreedyTree.sub dyadicFiniteTree
    change (S.B⁻¹) ^ 2 / 4 * ∑ c ∈ (Finset.range (L + 1)).biUnion (dyadicGeneration S.G K),
      dyadicGridLength S.G c.1 * S.tree.newAt K c = _
    rw [Finset.sum_biUnion hdisj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    have h1 := dyadicGeneration_depth S.G K k hc
    have : (c.1 - K.1).toNat = k := by omega
    simp only [GreedyTree.newAt, tree, this]; ring
  have htel := h.telescope hK L (by omega)
  have hen : ∑ c ∈ dyadicGeneration S.G K L,
      S.energy c (fitState S.G S.M S.P S.O L c).1 (fitState S.G S.M S.P S.O L c).2 ≤
        dyadicGridLength S.G K.1 := by
    calc _ ≤ ∑ c ∈ dyadicGeneration S.G K L,
          ∫ y in S.cell c, ‖(S.Z : ℝ → ColumnHilbert S.W) y‖ ^ 2 :=
          Finset.sum_le_sum fun c _ => energy_le c _ _
      _ = ∫ y in S.cell K, ‖(S.Z : ℝ → ColumnHilbert S.W) y‖ ^ 2 :=
          (setIntegral_cell_eq_sum_generation_real S.G K L (integrableOn_norm_sq_Lp _ _)).symm
      _ ≤ _ := h.energy_cell_le (coarse_tree h hK) hKT
  have hB := h.B_pos
  set W := dyadicWeightedMass S.G (S.tree.sub K) (S.tree.newAt K)
  have h1 : (S.B⁻¹) ^ 2 / 4 * W ≤ dyadicGridLength S.G K.1 := by linarith
  have h2 : W = 4 * S.B ^ 2 * ((S.B⁻¹) ^ 2 / 4 * W) := by field_simp
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- The accurate fits satisfy the hypotheses of the restart structure. -/
theorem Hyp.treeHyp (h : S.Hyp) : S.tree.Hyp where
  A_nonneg := by simp only [tree]; positivity
  mass := fun K hK => h.mass_le hK
  escape := fun _ _ _ hc => Or.inl hc

end AccSetup

namespace AccSetup
variable (S : AccSetup)

/-- The coarse ancestor of a fine cell. -/
noncomputable def coarse (c : ℤ × ℤ) : ℤ × ℤ := ancAt S.G c (c.1 - S.K₀)

open scoped Classical in
/-- The number of fit labels at a fine cell in the attempt rooted at `K`. -/
noncomputable def fcount (K c : ℤ × ℤ) : ℕ :=
  if c ∈ dyadicFiniteTree S.G S.J S.N ∧ S.cell c ⊆ S.cell K ∧ K.1 + S.K₀ ≤ c.1 then
    (fitState S.G S.M S.P S.O (c.1 - S.K₀ - K.1).toNat (S.coarse c)).2
  else 0

/-- The fit atoms at a fine cell in the attempt rooted at `K`. -/
noncomputable def fatoms (K c : ℤ × ℤ) : ℕ → ℝ → ℂ :=
  (fitState S.G S.M S.P S.O (c.1 - S.K₀ - K.1).toNat (S.coarse c)).1

variable {S}

theorem coarse_spec {c : ℤ × ℤ} :
    S.cell c ⊆ S.cell (S.coarse c) ∧ (S.coarse c).1 = c.1 - S.K₀ :=
  ⟨subset_ancAt S.G c (by omega), rfl⟩

theorem coarse_eq {I Q : ℤ × ℤ} (hQ : Q ∈ S.fine I) : S.coarse Q = I := by
  have hd := dyadicGeneration_depth S.G I S.K₀ hQ
  have hs := dyadicGeneration_subset S.G I S.K₀ hQ
  unfold coarse
  rw [show Q.1 - S.K₀ = I.1 by omega]
  exact ancAt_eq_of_subset hs

/-- Along a path inside the attempt rooted at `K`, coarse lists extend. -/
theorem fit_prefix {K c d : ℤ × ℤ} (hcd : S.cell c ⊆ S.cell d)
    (hdK : K.1 + S.K₀ ≤ d.1) :
    FitPrefix (fitState S.G S.M S.P S.O (c.1 - S.K₀ - K.1).toNat (S.coarse c))
      (fitState S.G S.M S.P S.O (d.1 - S.K₀ - K.1).toNat (S.coarse d)) := by
  have hdc := dyadicGridCell_depth_le_of_subset S.G c d hcd
  have hsub : S.cell (S.coarse c) ⊆ S.cell (S.coarse d) :=
    dyadicGridCell_subset_of_common_point S.G (coarse_spec.1 (dyadicGridCell_left_mem S.G c.1 c.2))
      (coarse_spec.1 (hcd (dyadicGridCell_left_mem S.G c.1 c.2)))
      (by simp only [coarse, ancAt]; omega)
  have hpre := fitState_fitPrefix S.G S.M S.P S.O (d.1 - S.K₀ - K.1).toNat (S.coarse d)
    (c.1 - d.1).toNat (S.coarse c) hsub (by simp only [coarse, ancAt]; omega)
  rw [show (d.1 - S.K₀ - K.1).toNat + (c.1 - d.1).toNat = (c.1 - S.K₀ - K.1).toNat by omega]
    at hpre
  exact hpre

variable (S)

open scoped Classical in
/-- The high column system of the attempt rooted at `K`: predictors and fit labels. -/
noncomputable def system (K : ℤ × ℤ) : PathColumnSystem S.G S.J S.N S.W where
  avail := fun c => (S.P₀.avail c).disjSum (fitLabels S.M (S.fcount K c))
  scalarAt := fun c => S.sc c (S.fatoms K c)
  weight := S.wt
  weight_pos := wt_pos
  weight_le := wt_le
  scalar_meas := fun c v => (colData c (state_atoms (S := S) _ _) v).1
  scalar_bound := fun c v => (colData c (state_atoms (S := S) _ _) v).2.1
  avail_mono := fun c d hc hd hcd v hv => by
    cases v with
    | inl v =>
      simp only [Finset.inl_mem_disjSum] at hv ⊢
      exact S.P₀.avail_mono c d hc hd hcd hv
    | inr m =>
      simp only [Finset.inr_mem_disjSum, fitLabels, Finset.mem_filter, Finset.mem_univ,
        true_and] at hv ⊢
      unfold fcount at hv ⊢
      split_ifs at hv with hdc
      · have hcc : c ∈ dyadicFiniteTree S.G S.J S.N ∧ S.cell c ⊆ S.cell K ∧ K.1 + S.K₀ ≤ c.1 :=
          ⟨hc, hcd.trans hdc.2.1, le_trans hdc.2.2
            (dyadicGridCell_depth_le_of_subset S.G c d hcd)⟩
        simp only [hcc.1, hcc.2.1, hcc.2.2, and_self, ↓reduceIte]
        exact lt_of_lt_of_le hv (fit_prefix hcd hdc.2.2).1
      · omega
  consistent := fun c d hc hd hcd v hv y hy => by
    cases v with
    | inl v =>
      simp only [Finset.inl_mem_disjSum] at hv
      simp only [sc, Sum.elim_inl]
      exact S.P₀.consistent c d hc hd hcd v hv y hy
    | inr m =>
      simp only [Finset.inr_mem_disjSum, fitLabels, Finset.mem_filter, Finset.mem_univ,
        true_and] at hv
      unfold fcount at hv
      split_ifs at hv with hdc
      · simp only [sc, Sum.elim_inr, fatoms]
        rw [(fit_prefix hcd hdc.2.2).2 m hv]
      · omega

variable {S}

/-- The cell projections of the attempt system are the accurate-fit projections with the
coarse state of the attempt. -/
theorem system_proj {K I Q : ℤ × ℤ} (hQ : Q ∈ S.fine I) (hQT : Q ∈ dyadicFiniteTree S.G S.J S.N)
    (hIK : S.cell I ⊆ S.cell K) (hKI : K.1 ≤ I.1) :
    (S.system K).proj Q =
      S.proj Q (fitState S.G S.M S.P S.O (I.1 - K.1).toNat I).1
        (fitState S.G S.M S.P S.O (I.1 - K.1).toNat I).2 := by
  classical
  have hd := dyadicGeneration_depth S.G I S.K₀ hQ
  have hs := dyadicGeneration_subset S.G I S.K₀ hQ
  have hco := coarse_eq hQ
  have hidx : (Q.1 - S.K₀ - K.1).toNat = (I.1 - K.1).toNat := by omega
  have hcount : S.fcount K Q = (fitState S.G S.M S.P S.O (I.1 - K.1).toNat I).2 := by
    unfold fcount
    have hcnd : Q ∈ dyadicFiniteTree S.G S.J S.N ∧ S.cell Q ⊆ S.cell K ∧ K.1 + S.K₀ ≤ Q.1 :=
      ⟨hQT, hs.trans hIK, by omega⟩
    simp only [hcnd.1, hcnd.2.1, hcnd.2.2, and_self, ↓reduceIte]
    rw [hco, hidx]
  have hatoms : S.fatoms K Q = (fitState S.G S.M S.P S.O (I.1 - K.1).toNat I).1 := by
    unfold fatoms; rw [hco, hidx]
  have hrange : (S.system K).range Q = colRange (S.cell Q)
      (S.sc Q (fitState S.G S.M S.P S.O (I.1 - K.1).toNat I).1) S.wt
      (S.lab Q (fitState S.G S.M S.P S.O (I.1 - K.1).toNat I).2) := by
    unfold PathColumnSystem.range colRange
    have hav : (S.system K).avail Q = S.lab Q (fitState S.G S.M S.P S.O (I.1 - K.1).toNat I).2 := by
      simp only [system, lab, hcount]
    rw [hav]
    congr 1
    refine Set.image_congr fun v _ => ?_
    have hok : ColOK (S.cell Q) (S.sc Q (fitState S.G S.M S.P S.O (I.1 - K.1).toNat I).1) S.wt v :=
      (colData Q (state_atoms (S := S) _ _)).ok (dyadicGridCell_measurable _ _ _)
        (by rw [dyadicGridCell_volume]; exact ENNReal.ofReal_lt_top) v
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp ((S.system K).column_memLp Q v), col_coeFn hok] with y h1 h2
    rw [PathColumnSystem.column, h1, h2]
    simp only [system, hatoms]
  unfold PathColumnSystem.proj proj
  ext z : 1
  exact starProjection_congr hrange z

end AccSetup

namespace AccSetup
variable {S : AccSetup}

/-- The delayed opponent of the attempt system rooted at a cell `R` is, on a coarse cell `I`,
the physical part of its fine projections. -/
theorem Hyp.system_delayed_ae (h : S.Hyp) {K R I : ℤ × ℤ}
    (hR : R ∈ dyadicFiniteTree S.G S.J S.N) (hIR : I ∈ pathBelow S.G S.J S.N R)
    (hIc : I ∈ dyadicFiniteTree S.G S.J S.Nc) (hIK : S.cell I ⊆ S.cell K) (hKI : K.1 ≤ I.1) :
    ∀ᵐ y ∂volume, y ∈ S.cell I →
      ((S.system K).family R hR).delayed S.input S.K₀ I y =
        S.phys I (fitState S.G S.M S.P S.O (I.1 - K.1).toNat I).1
          (fitState S.G S.M S.P S.O (I.1 - K.1).toNat I).2 y := by
  classical
  set a := (fitState S.G S.M S.P S.O (I.1 - K.1).toNat I).1
  set n := (fitState S.G S.M S.P S.O (I.1 - K.1).toNat I).2
  set Ψ := (S.system K).family R hR
  have hIRm := (PathColumnSystem.below_mem_iff hR I).mp hIR
  have hRl := dyadicGridCell_depth_le_of_subset S.G I R hIRm.2
  have hIcm := (dyadicFiniteTree_mem_iff S.G S.J I S.Nc).mp hIc
  have hpart : ∀ Q ∈ S.fine I, Q ∈ (Ψ.partition (I.1 + S.K₀)).cells := by
    intro Q hQ
    refine (Ψ.mem_partition _ Q).mpr ⟨?_, (dyadicGeneration_subset S.G I S.K₀ hQ).trans hIRm.2⟩
    have := dyadicGeneration_depth S.G I S.K₀ hQ
    have := h.K₀_le
    simp only [Nc] at hIcm
    simp only [ColumnDepthFamily.depth, Ψ, PathColumnSystem.family, PathColumnSystem.rooted]
    omega
  have hall : ∀ᵐ y ∂volume, ∀ Q ∈ S.fine I, y ∈ S.cell Q →
      (Ψ.proj (I.1 + S.K₀) S.Z : ℝ → ColumnHilbert S.W) y none = S.phys I a n y := by
    refine (Filter.eventually_all_finset (S.fine I)).mpr fun Q hQ => ?_
    have h1 := (S.system K).family_proj_ae hR _ (hpart Q hQ) S.Z
    rw [system_proj hQ (coarse_fine hIc hQ h) hIK hKI] at h1
    rw [Filter.EventuallyEq, ae_restrict_iff' (dyadicGridCell_measurable _ _ _)] at h1
    filter_upwards [h1, colProj_none (s := S.cell Q) (S.sc Q a) S.wt (S.lab Q n) S.Z]
      with y hy1 hy2 hyQ
    rw [hy1 hyQ, phys_eq_on hQ hyQ]
    exact hy2 hyQ
  filter_upwards [hall] with y hy hyI
  obtain ⟨Q, hQ, hyQ⟩ := dyadicGeneration_cover S.G I S.K₀ hyI
  exact hy Q hQ hyQ

/-- Private-coordinate recovery bounds the physical part of the fine projections on a coarse
cell (blueprint prop:base, line 1641). -/
theorem Hyp.phys_sup (h : S.Hyp) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hwε : ∀ v, ε ≤ S.P₀.weight v)
    {I : ℤ × ℤ} (hIc : I ∈ dyadicFiniteTree S.G S.J S.Nc) (hIT : kernelHull S.G S.J S.N S.w I)
    {a : ℕ → ℝ → ℂ} (ha : ∀ i, Measurable (a i) ∧ ∀ y, ‖a i y‖ ≤ 1) (n : ℕ) (y : ℝ) :
    ‖S.phys I a n y‖ ≤ Fintype.card S.W * Real.sqrt (2 ^ S.K₀ / ε) := by
  classical
  have hX : 0 ≤ (Fintype.card S.W : ℝ) * Real.sqrt (2 ^ S.K₀ / ε) := by positivity
  by_cases hyI : y ∈ S.cell I
  · obtain ⟨Q, hQ, hyQ⟩ := dyadicGeneration_cover S.G I S.K₀ hyI
    rw [phys_eq_on hQ hyQ]
    refine (colPhys_bound _ _ _ _ _ _).trans ?_
    have hQd := dyadicGeneration_depth S.G I S.K₀ hQ
    have hlen : dyadicGridLength S.G I.1 = 2 ^ S.K₀ * dyadicGridLength S.G Q.1 := by
      rw [hQd, dyadicGridLength_add_nat, mul_comm, mul_assoc, ← mul_pow]; norm_num
    have hQpos := dyadicGridLength_pos S.G Q.1
    have hcoef : ∀ v ∈ S.lab Q n, ‖colCoeff (S.cell Q) (S.sc Q a) S.wt (S.lab Q n) S.Z v‖ ≤
        Real.sqrt (2 ^ S.K₀ / ε) := by
      intro v hv
      have hok := (colData Q ha).ok (dyadicGridCell_measurable S.G Q.1 Q.2)
        (by rw [dyadicGridCell_volume]; exact ENNReal.ofReal_lt_top) v
      have hrec := colCoeff_recovery (s := S.cell Q) (S.sc Q a) S.wt (S.lab Q n) S.Z hv hok
      have hE : ∫ y in S.cell Q, ‖((colRange (S.cell Q) (S.sc Q a) S.wt (S.lab Q n)).starProjection
          S.Z : ℝ → ColumnHilbert S.W) y‖ ^ 2 ≤ dyadicGridLength S.G I.1 := by
        calc _ ≤ ‖(colRange (S.cell Q) (S.sc Q a) S.wt (S.lab Q n)).starProjection S.Z‖ ^ 2 := by
              rw [columnInput_norm_sq_integral]
              exact setIntegral_le_integral ((Lp.memLp _).integrable_norm_pow two_ne_zero)
                (Filter.Eventually.of_forall fun _ => by positivity)
          _ ≤ ∫ y in S.cell Q, ‖(S.Z : ℝ → ColumnHilbert S.W) y‖ ^ 2 :=
              colRange_energy_le (dyadicGridCell_measurable _ _ _) _ _ _ _
          _ ≤ ∫ y in S.cell I, ‖(S.Z : ℝ → ColumnHilbert S.W) y‖ ^ 2 :=
              setIntegral_mono_set (integrableOn_norm_sq_Lp _ _)
                (Filter.Eventually.of_forall fun _ => by positivity)
                (Filter.Eventually.of_forall (dyadicGeneration_subset S.G I S.K₀ hQ))
          _ ≤ _ := h.energy_cell_le (coarse_tree h hIc) hIT
      rw [volume_real_cell] at hrec
      have hw : ε ≤ S.wt v := by
        cases v with
        | inl v => exact hwε v
        | inr m => exact hε1
      have hwpos : 0 < S.wt v := lt_of_lt_of_le hε hw
      refine Real.le_sqrt_of_sq_le ?_
      rw [le_div_iff₀ hε]
      have h1 : ‖colCoeff (S.cell Q) (S.sc Q a) S.wt (S.lab Q n) S.Z v‖ ^ 2 * S.wt v *
          dyadicGridLength S.G Q.1 ≤ 2 ^ S.K₀ * dyadicGridLength S.G Q.1 := by linarith
      have h2 : ‖colCoeff (S.cell Q) (S.sc Q a) S.wt (S.lab Q n) S.Z v‖ ^ 2 * S.wt v ≤
          2 ^ S.K₀ := le_of_mul_le_mul_right (by linarith) hQpos
      have h3 : ‖colCoeff (S.cell Q) (S.sc Q a) S.wt (S.lab Q n) S.Z v‖ ^ 2 * ε ≤
          ‖colCoeff (S.cell Q) (S.sc Q a) S.wt (S.lab Q n) S.Z v‖ ^ 2 * S.wt v :=
        mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      linarith
    calc ∑ v ∈ S.lab Q n, ‖colCoeff (S.cell Q) (S.sc Q a) S.wt (S.lab Q n) S.Z v‖
        ≤ ∑ _v ∈ S.lab Q n, Real.sqrt (2 ^ S.K₀ / ε) := Finset.sum_le_sum hcoef
      _ = (S.lab Q n).card * Real.sqrt (2 ^ S.K₀ / ε) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
          gcongr
          exact_mod_cast Finset.card_le_univ _
  · have h0 : S.phys I a n y = 0 := by
      unfold phys
      refine Finset.sum_eq_zero fun Q hQ => Set.indicator_of_notMem
        (fun hyQ => hyI (dyadicGeneration_subset S.G I S.K₀ hQ hyQ)) _
    rw [h0, norm_zero]; exact hX

end AccSetup

/-! ### Pair control for the replaced tuple -/

/-- Residual smallness against an `L^q` input of size at most `C`. -/
theorem FormSmall.apply_pair_Lq {a₀ r : ℝ} {w : ℝ × ℝ → ℂ} {p p' : Fin 4} (hpp : p ≠ p') {q : ℝ}
    {R : ℝ → ℂ} {η : ℝ}
    (h : FormSmall a₀ r w p q R η) (hR : Measurable R) {V : ℝ → ℂ} (hV : Measurable V) {C : ℝ}
    (hC : 0 < C) (hVq : eLpNorm V (ENNReal.ofReal q) (normalizedIntervalMeasure a₀ r) ≤
      ENNReal.ofReal C) {z : Fin 4 → ℝ → ℂ} (hz : ∀ l, Measurable (z l))
    (hz2 : ∀ l, l ≠ p → l ≠ p' → eLpNorm (z l) 2 (normalizedIntervalMeasure a₀ r) ≤ 1) :
    ‖localProgressionForm r w (slotPair z p p' R V)‖ ≤ C * η := by
  have hV' : Measurable ((C⁻¹ : ℂ) • V) := hV.const_smul _
  have hVq' : eLpNorm ((C⁻¹ : ℂ) • V) (ENNReal.ofReal q) (normalizedIntervalMeasure a₀ r) ≤ 1 := by
    rw [eLpNorm_const_smul]
    calc ‖((C : ℂ))⁻¹‖ₑ * eLpNorm V (ENNReal.ofReal q) (normalizedIntervalMeasure a₀ r)
        ≤ ENNReal.ofReal C⁻¹ * ENNReal.ofReal C := by
          gcongr
          rw [← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
      _ = 1 := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hC.le), inv_mul_cancel₀ hC.ne',
            ENNReal.ofReal_one]
  have h1 := h.apply_pair hpp hR hV' hVq' hz hz2
  have he : V = (C : ℂ) • ((C⁻¹ : ℂ) • V) := by
    rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hC.ne'), one_smul]
  rw [he, slotPair_const_smul_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
  exact mul_le_mul_of_nonneg_left h1 hC.le

/-- The data of the replaced tuple at one cell (blueprint prop:base, eq:Y and proof lines
1641-1642): low arguments bounded by `S`, high arguments `X_e = f_e - g_e` and their
replacements `Y_e = P_e - g_e` with `d_{e,I}(f_e - P_e) ≤ δ_e`. -/
structure YCell (κ : LocalKernelClass) where
  /-- Left endpoint of the cell in the tuple-replacement estimate. -/
  a₀ : ℝ
  /-- Positive length of the cell in the tuple-replacement estimate. -/
  r : ℝ
  /-- Admissible kernel used by the tuple-replacement local form. -/
  w : ℝ × ℝ → ℂ
  /-- Integrability exponent of the normalized original inputs. -/
  q : ℝ
  /-- First low slot, whose input is uniformly bounded. -/
  i : Fin 4
  /-- Second low slot, distinct from the first low slot. -/
  j : Fin 4
  /-- First high slot, replaced using the approximation `Pa`. -/
  a : Fin 4
  /-- Second high slot, replaced using the approximation `Pb`. -/
  b : Fin 4
  /-- Tuple before replacement, with high entries represented as residuals. -/
  X : Fin 4 → ℝ → ℂ
  /-- Original normalized input functions in the high-slot residuals. -/
  f : Fin 4 → ℝ → ℂ
  /-- Projected approximations subtracted from the original inputs. -/
  g : Fin 4 → ℝ → ℂ
  /-- Accurate approximation replacing the first high-slot input. -/
  Pa : ℝ → ℂ
  /-- Accurate approximation replacing the second high-slot input. -/
  Pb : ℝ → ℂ
  /-- Uniform norm bound for the low inputs and the subtracted projections. -/
  S : ℝ
  /-- Uniform norm bound for the first accurate high-slot approximation. -/
  Sa : ℝ
  /-- Uniform norm bound for the second accurate high-slot approximation. -/
  Sb : ℝ
  /-- Pair-smallness threshold for distinct entries of the original tuple. -/
  η₀ : ℝ
  /-- Residual-smallness tolerance for the first high-slot replacement. -/
  δa : ℝ
  /-- Residual-smallness tolerance for the second high-slot replacement. -/
  δb : ℝ
  r_pos : 0 < r
  adm : IsAdmissibleLocalKernel κ a₀ r w
  two_le_q : 2 ≤ q
  hij : i ≠ j
  hia : i ≠ a
  hib : i ≠ b
  hja : j ≠ a
  hjb : j ≠ b
  hab : a ≠ b
  X_meas : ∀ l, Measurable (X l)
  low_bound : ∀ y, ‖X i y‖ ≤ S ∧ ‖X j y‖ ≤ S
  f_meas : ∀ l, Measurable (f l)
  f_norm : ∀ l, eLpNorm (f l) (ENNReal.ofReal q) (normalizedIntervalMeasure a₀ r) ≤ 1
  g_meas : ∀ l, Measurable (g l)
  g_bound : ∀ y, ‖g a y‖ ≤ S ∧ ‖g b y‖ ≤ S
  Xa : X a = f a - g a
  Xb : X b = f b - g b
  Pa_meas : Measurable Pa
  Pb_meas : Measurable Pb
  Pa_bound : ∀ y, ‖Pa y‖ ≤ Sa
  Pb_bound : ∀ y, ‖Pb y‖ ≤ Sb
  S_pos : 0 < S
  Sa_pos : 0 < Sa
  δa_nonneg : 0 ≤ δa
  δb_nonneg : 0 ≤ δb
  small_a : FormSmall a₀ r w a q (f a - Pa) δa
  small_b : FormSmall a₀ r w b q (f b - Pb) δb
  pairs : ∀ s s', s ≠ s' → PairSmall a₀ r w s s' (X s) (X s') η₀

namespace YCell
variable {κ : LocalKernelClass} (C : YCell κ)

/-- The normalized measure of the cell. -/
noncomputable abbrev μ : Measure ℝ := normalizedIntervalMeasure C.a₀ C.r

/-- The local form. -/
noncomputable abbrev H (F : Fin 4 → ℝ → ℂ) : ℂ := localProgressionForm C.r C.w F

open scoped Classical in
/-- The replaced tuple `Y` (blueprint eq:Y). -/
noncomputable def Y (l : Fin 4) : ℝ → ℂ :=
  if l = C.a then C.Pa - C.g C.a else if l = C.b then C.Pb - C.g C.b else C.X l

/-- The residual of a high argument. -/
noncomputable def Rres (l : Fin 4) : ℝ → ℂ := if l = C.a then C.f C.a - C.Pa else C.f C.b - C.Pb

theorem Y_a : C.Y C.a = C.X C.a - C.Rres C.a := by
  funext y; simp [Y, Rres, C.Xa]

theorem Y_b : C.Y C.b = C.X C.b - C.Rres C.b := by
  funext y; simp [Y, Rres, C.Xb, Ne.symm C.hab]

theorem Y_low {l : Fin 4} (ha : l ≠ C.a) (hb : l ≠ C.b) : C.Y l = C.X l := by
  simp [Y, ha, hb]

theorem f_L2 (l : Fin 4) : FinL2 C.a₀ C.r (C.f l) := by
  have : IsProbabilityMeasure C.μ := normalizedIntervalMeasure_probability C.a₀ C.r_pos
  refine ⟨C.f_meas l, ne_top_of_le_ne_top ENNReal.one_ne_top
    (le_trans (eLpNorm_le_eLpNorm_of_exponent_le ?_) (C.f_norm l))⟩
  rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num]
  exact ENNReal.ofReal_le_ofReal C.two_le_q

theorem low_L2 {l : Fin 4} (hl : l = C.i ∨ l = C.j) : FinL2 C.a₀ C.r (C.X l) := by
  rcases hl with rfl | rfl
  · exact FinL2.of_bound C.r_pos (C.X_meas _) fun y => (C.low_bound y).1
  · exact FinL2.of_bound C.r_pos (C.X_meas _) fun y => (C.low_bound y).2

theorem high_L2 {l : Fin 4} (hl : l = C.a ∨ l = C.b) : FinL2 C.a₀ C.r (C.X l) := by
  rcases hl with rfl | rfl
  · rw [C.Xa]; exact (C.f_L2 _).sub (FinL2.of_bound C.r_pos (C.g_meas _) fun y => (C.g_bound y).1)
  · rw [C.Xb]; exact (C.f_L2 _).sub (FinL2.of_bound C.r_pos (C.g_meas _) fun y => (C.g_bound y).2)

theorem R_L2 {l : Fin 4} (hl : l = C.a ∨ l = C.b) : FinL2 C.a₀ C.r (C.Rres l) := by
  rcases hl with rfl | rfl
  · simp only [Rres, ↓reduceIte]
    exact (C.f_L2 _).sub (FinL2.of_bound C.r_pos C.Pa_meas C.Pa_bound)
  · simp only [Rres, Ne.symm C.hab, ↓reduceIte]
    exact (C.f_L2 _).sub (FinL2.of_bound C.r_pos C.Pb_meas C.Pb_bound)

theorem R_small {l : Fin 4} (hl : l = C.a ∨ l = C.b) :
    FormSmall C.a₀ C.r C.w l C.q (C.Rres l) (if l = C.a then C.δa else C.δb) ∧
      Measurable (C.Rres l) := by
  rcases hl with rfl | rfl
  · simp only [Rres, ↓reduceIte]
    exact ⟨C.small_a, (C.f_meas _).sub C.Pa_meas⟩
  · simp only [Rres, Ne.symm C.hab, ↓reduceIte]
    exact ⟨C.small_b, (C.f_meas _).sub C.Pb_meas⟩

theorem high_Lq {l : Fin 4} (hl : l = C.a ∨ l = C.b) :
    eLpNorm (C.X l) (ENNReal.ofReal C.q) C.μ ≤ ENNReal.ofReal (1 + C.S) := by
  have : IsProbabilityMeasure C.μ := normalizedIntervalMeasure_probability C.a₀ C.r_pos
  have hq1 : (1 : ENNReal) ≤ ENNReal.ofReal C.q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith [C.two_le_q])
  have hg : ∀ {g : ℝ → ℂ}, Measurable g → (∀ y, ‖g y‖ ≤ C.S) →
      eLpNorm g (ENNReal.ofReal C.q) C.μ ≤ ENNReal.ofReal C.S := fun hgm hgb =>
    (eLpNorm_le_of_ae_bound hgm.aestronglyMeasurable
      (Filter.Eventually.of_forall hgb)).trans (by simp)
  have key : ∀ {fl gl : ℝ → ℂ}, eLpNorm fl (ENNReal.ofReal C.q) C.μ ≤ 1 →
      eLpNorm gl (ENNReal.ofReal C.q) C.μ ≤ ENNReal.ofReal C.S →
      eLpNorm (fl - gl) (ENNReal.ofReal C.q) C.μ ≤ ENNReal.ofReal (1 + C.S) := by
    intro fl gl h1 h2
    refine (eLpNorm_sub_le hq1).trans ?_
    rw [ENNReal.ofReal_add zero_le_one C.S_pos.le, ENNReal.ofReal_one]
    exact add_le_add h1 h2
  rcases hl with rfl | rfl
  · rw [C.Xa]; exact key (C.f_norm _) (hg (C.g_meas _) fun y => (C.g_bound y).1)
  · rw [C.Xb]; exact key (C.f_norm _) (hg (C.g_meas _) fun y => (C.g_bound y).2)

/-- Normalized spectators for the slots `p, p'`. -/
def Spect (z : Fin 4 → ℝ → ℂ) (p p' : Fin 4) : Prop :=
  (∀ l, Measurable (z l)) ∧ ∀ l, l ≠ p → l ≠ p' → eLpNorm (z l) 2 C.μ ≤ 1

theorem Spect.flip {C : YCell κ} {z : Fin 4 → ℝ → ℂ} {p p' : Fin 4} (h : C.Spect z p p') :
    C.Spect z p' p := ⟨h.1, fun l h1 h2 => h.2 l h2 h1⟩

theorem Spect.ok {C : YCell κ} {z : Fin 4 → ℝ → ℂ} {p p' : Fin 4} (h : C.Spect z p p') :
    SpectatorOK C.a₀ C.r z p p' :=
  ⟨h.1, fun l h1 h2 => ne_top_of_le_ne_top ENNReal.one_ne_top (h.2 l h1 h2)⟩

theorem H_comm (z : Fin 4 → ℝ → ℂ) {p p' : Fin 4} (h : p ≠ p') (X Y : ℝ → ℂ) :
    C.H (slotPair z p p' X Y) = C.H (slotPair z p' p Y X) := by
  rw [slotPair_comm z h]

/-- The `ε`-bound of a high residual. -/
noncomputable def δ (e : Fin 4) : ℝ := if e = C.a then C.δa else C.δb

theorem δ_le (e : Fin 4) : C.δ e ≤ C.δa + C.δb := by
  unfold δ; split_ifs <;> linarith [C.δa_nonneg, C.δb_nonneg]

theorem low_bound' {s : Fin 4} (hs : s = C.i ∨ s = C.j) (y : ℝ) : ‖C.X s y‖ ≤ C.S := by
  rcases hs with rfl | rfl
  · exact (C.low_bound y).1
  · exact (C.low_bound y).2

/-- A low argument against a high residual. -/
theorem low_res {s e : Fin 4} (hs : s = C.i ∨ s = C.j) (he : e = C.a ∨ e = C.b) (hse : s ≠ e)
    {z : Fin 4 → ℝ → ℂ} (hz : C.Spect z s e) :
    ‖C.H (slotPair z s e (C.X s) (C.Rres e))‖ ≤ C.S * C.δ e := by
  obtain ⟨hsm, hRm⟩ := C.R_small he
  rw [C.H_comm z hse]
  exact hsm.apply_pair_bounded C.r_pos (Ne.symm hse) hRm (C.X_meas s) C.S_pos (C.low_bound' hs)
    hz.flip.1 hz.flip.2

/-- A low argument against a replaced high argument. -/
theorem low_high {s e : Fin 4} (hs : s = C.i ∨ s = C.j) (he : e = C.a ∨ e = C.b) (hse : s ≠ e)
    {z : Fin 4 → ℝ → ℂ} (hz : C.Spect z s e) :
    ‖C.H (slotPair z s e (C.X s) (C.X e - C.Rres e))‖ ≤ C.η₀ + C.S * C.δ e := by
  have h := slotPair_sub_right C.r_pos C.adm hz.ok (C.low_L2 hs) (C.high_L2 he) (C.R_L2 he)
  change C.H _ = C.H _ - C.H _ at h
  rw [h]
  refine (norm_sub_le _ _).trans (add_le_add ?_ (C.low_res hs he hse hz))
  exact C.pairs s e hse z hz.1 hz.2

theorem Y_high {e : Fin 4} (he : e = C.a ∨ e = C.b) : C.Y e = C.X e - C.Rres e := by
  rcases he with rfl | rfl
  · exact C.Y_a
  · exact C.Y_b

/-- The two replaced high arguments. -/
theorem a_b {z : Fin 4 → ℝ → ℂ} (hz : C.Spect z C.a C.b) :
    ‖C.H (slotPair z C.a C.b (C.X C.a - C.Rres C.a) (C.X C.b - C.Rres C.b))‖ ≤
      C.η₀ + (1 + C.S) * C.δb + (1 + C.S) * C.δa + (1 + C.Sa) * C.δb := by
  have hA := C.high_L2 (Or.inl rfl)
  have hB := C.high_L2 (Or.inr rfl)
  have hRA := C.R_L2 (Or.inl rfl)
  have hRB := C.R_L2 (Or.inr rfl)
  have e1 := slotPair_sub_left C.r_pos C.adm C.hab hz.ok hA hRA (hB.sub hRB)
  have e2 := slotPair_sub_right C.r_pos C.adm hz.ok hA hB hRB
  have e3 := slotPair_sub_right C.r_pos C.adm hz.ok hRA hB hRB
  change C.H _ = C.H _ - C.H _ at e1 e2 e3
  rw [e1, e2, e3]
  obtain ⟨hsa, hRam⟩ := C.R_small (Or.inl rfl)
  obtain ⟨hsb, hRbm⟩ := C.R_small (Or.inr rfl)
  simp only [↓reduceIte, Ne.symm C.hab] at hsa hsb
  -- the four terms
  have t1 : ‖C.H (slotPair z C.a C.b (C.X C.a) (C.X C.b))‖ ≤ C.η₀ :=
    C.pairs C.a C.b C.hab z hz.1 hz.2
  have t2 : ‖C.H (slotPair z C.a C.b (C.X C.a) (C.Rres C.b))‖ ≤ (1 + C.S) * C.δb := by
    rw [C.H_comm z C.hab]
    exact hsb.apply_pair_Lq (Ne.symm C.hab) hRbm (C.X_meas _) (by linarith [C.S_pos])
      (C.high_Lq (Or.inl rfl)) hz.flip.1 hz.flip.2
  have t3 : ‖C.H (slotPair z C.a C.b (C.Rres C.a) (C.X C.b))‖ ≤ (1 + C.S) * C.δa :=
    hsa.apply_pair_Lq C.hab hRam (C.X_meas _) (by linarith [C.S_pos])
      (C.high_Lq (Or.inr rfl)) hz.1 hz.2
  have t4 : ‖C.H (slotPair z C.a C.b (C.Rres C.a) (C.Rres C.b))‖ ≤ (1 + C.Sa) * C.δb := by
    have hRa : C.Rres C.a = C.f C.a - C.Pa := by simp [Rres]
    rw [hRa]
    change ‖localProgressionForm C.r C.w (slotPair z C.a C.b (C.f C.a - C.Pa) (C.Rres C.b))‖ ≤ _
    rw [slotPair_sub_left C.r_pos C.adm C.hab hz.ok (C.f_L2 _)
      (FinL2.of_bound C.r_pos C.Pa_meas C.Pa_bound) hRB]
    change ‖C.H _ - C.H _‖ ≤ _
    rw [C.H_comm z C.hab, C.H_comm z C.hab]
    have u1 := hsb.apply_pair (Ne.symm C.hab) hRbm (C.f_meas C.a) (C.f_norm C.a) hz.flip.1 hz.flip.2
    have u2 := hsb.apply_pair_bounded C.r_pos (Ne.symm C.hab) hRbm C.Pa_meas C.Sa_pos
      C.Pa_bound hz.flip.1 hz.flip.2
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ C.δb + C.Sa * C.δb := add_le_add u1 u2
      _ = (1 + C.Sa) * C.δb := by ring
  calc _ ≤ ‖C.H (slotPair z C.a C.b (C.X C.a) (C.X C.b)) -
          C.H (slotPair z C.a C.b (C.X C.a) (C.Rres C.b))‖ +
        ‖C.H (slotPair z C.a C.b (C.Rres C.a) (C.X C.b)) -
          C.H (slotPair z C.a C.b (C.Rres C.a) (C.Rres C.b))‖ := norm_sub_le _ _
    _ ≤ (C.η₀ + (1 + C.S) * C.δb) + ((1 + C.S) * C.δa + (1 + C.Sa) * C.δb) :=
        add_le_add ((norm_sub_le _ _).trans (add_le_add t1 t2))
          ((norm_sub_le _ _).trans (add_le_add t3 t4))
    _ = _ := by ring

/-- The pair bound for the replaced tuple: the supremum `S_a` of the first new catalog only
multiplies the second precision `δ_b` (blueprint prop:base, line 1640). -/
noncomputable def ηY : ℝ := C.η₀ + (2 + 2 * C.S) * (C.δa + C.δb) + (1 + C.Sa) * C.δb

/-- Blueprint prop:base, proof lines 1641-1642: every pair of the replaced tuple `Y` has
bilinear norm at most `η₀ + (2 + 2S)(δ_a + δ_b) + (1 + S_a) δ_b`. -/
theorem Y_pairSmall {s s' : Fin 4} (hss : s ≠ s') :
    PairSmall C.a₀ C.r C.w s s' (C.Y s) (C.Y s') C.ηY := by
  intro z hzm hz2
  have hz : C.Spect z s s' := ⟨hzm, hz2⟩
  change ‖C.H (slotPair z s s' _ _)‖ ≤ _
  have hS := C.S_pos.le
  have hSa := C.Sa_pos.le
  have hδ := add_nonneg C.δa_nonneg C.δb_nonneg
  have hSaδ : 0 ≤ (1 + C.Sa) * C.δb := mul_nonneg (by linarith) C.δb_nonneg
  have hcov := fin_four_cover C.hij C.hia C.hib C.hja C.hjb C.hab
  have hlowY : ∀ l, l = C.i ∨ l = C.j → C.Y l = C.X l := by
    rintro l (rfl | rfl)
    · exact C.Y_low C.hia C.hib
    · exact C.Y_low C.hja C.hjb
  have hbig : ∀ e, C.S * C.δ e ≤ (2 + 2 * C.S) * (C.δa + C.δb) := by
    intro e
    have := C.δ_le e
    have := C.δa_nonneg; have := C.δb_nonneg
    unfold δ; split_ifs <;> nlinarith
  rcases hcov s with hs | hs | hs | hs <;> rcases hcov s' with hs' | hs' | hs' | hs'
  all_goals try exact absurd (hs.trans hs'.symm) hss
  -- low / low
  · rw [hlowY s (Or.inl hs), hlowY s' (Or.inr hs')]
    exact (C.pairs s s' hss z hzm hz2).trans (by unfold ηY; nlinarith)
  · rw [hlowY s (Or.inl hs), C.Y_high (Or.inl hs')]
    exact (C.low_high (Or.inl hs) (Or.inl hs') hss hz).trans (by unfold ηY; linarith [hbig s'])
  · rw [hlowY s (Or.inl hs), C.Y_high (Or.inr hs')]
    exact (C.low_high (Or.inl hs) (Or.inr hs') hss hz).trans (by unfold ηY; linarith [hbig s'])
  · rw [hlowY s (Or.inr hs), hlowY s' (Or.inl hs')]
    exact (C.pairs s s' hss z hzm hz2).trans (by unfold ηY; nlinarith)
  · rw [hlowY s (Or.inr hs), C.Y_high (Or.inl hs')]
    exact (C.low_high (Or.inr hs) (Or.inl hs') hss hz).trans (by unfold ηY; linarith [hbig s'])
  · rw [hlowY s (Or.inr hs), C.Y_high (Or.inr hs')]
    exact (C.low_high (Or.inr hs) (Or.inr hs') hss hz).trans (by unfold ηY; linarith [hbig s'])
  · rw [C.Y_high (Or.inl hs), hlowY s' (Or.inl hs'), C.H_comm z hss]
    exact (C.low_high (Or.inl hs') (Or.inl hs) (Ne.symm hss) hz.flip).trans
      (by unfold ηY; linarith [hbig s])
  · rw [C.Y_high (Or.inl hs), hlowY s' (Or.inr hs'), C.H_comm z hss]
    exact (C.low_high (Or.inr hs') (Or.inl hs) (Ne.symm hss) hz.flip).trans
      (by unfold ηY; linarith [hbig s])
  · subst hs hs'
    rw [C.Y_a, C.Y_b]
    exact (C.a_b hz).trans (by unfold ηY; nlinarith [C.δa_nonneg, C.δb_nonneg])
  · rw [C.Y_high (Or.inr hs), hlowY s' (Or.inl hs'), C.H_comm z hss]
    exact (C.low_high (Or.inl hs') (Or.inr hs) (Ne.symm hss) hz.flip).trans
      (by unfold ηY; linarith [hbig s])
  · rw [C.Y_high (Or.inr hs), hlowY s' (Or.inr hs'), C.H_comm z hss]
    exact (C.low_high (Or.inr hs') (Or.inr hs) (Ne.symm hss) hz.flip).trans
      (by unfold ηY; linarith [hbig s])
  · subst hs hs'
    rw [C.Y_a, C.Y_b, C.H_comm z hss]
    exact (C.a_b hz.flip).trans (by unfold ηY; nlinarith [C.δa_nonneg, C.δb_nonneg])

end YCell

/-! ### Local sizes, the basic side and the two-`U` term -/

/-- Scaling one spectator slot of a local form. -/
theorem localProgressionForm_scale_slot (r : ℝ) (w : ℝ × ℝ → ℂ) (F : Fin 4 → ℝ → ℂ) (l : Fin 4)
    (c : ℂ) : localProgressionForm r w (Function.update F l (c • F l)) =
      c * localProgressionForm r w F := by
  rw [localProgressionForm_update_const_smul, Function.update_eq_self]

/-- A pair estimate against spectators of arbitrary normalized `L²` size:
`|H(X, Y, z_a, z_b)| ≤ η ‖z_a‖ ‖z_b‖`. -/
theorem PairSmall.le_mul {a₀ r : ℝ} {w : ℝ × ℝ → ℂ} {p p' : Fin 4}
    (hpp : p ≠ p') {X Y : ℝ → ℂ} {η : ℝ}
    (h : PairSmall a₀ r w p p' X Y η) {F : Fin 4 → ℝ → ℂ} (hF : ∀ l, Measurable (F l))
    {a b : Fin 4} (hab : a ≠ b) (hap : a ≠ p) (hap' : a ≠ p') (hbp : b ≠ p) (hbp' : b ≠ p')
    {ca cb : ℝ} (hca : 0 < ca) (hcb : 0 < cb)
    (hFa : eLpNorm (F a) 2 (normalizedIntervalMeasure a₀ r) ≤ ENNReal.ofReal ca)
    (hFb : eLpNorm (F b) 2 (normalizedIntervalMeasure a₀ r) ≤ ENNReal.ofReal cb) :
    ‖localProgressionForm r w (slotPair F p p' X Y)‖ ≤ ca * cb * η := by
  have hcov := fin_four_cover hpp (Ne.symm hap) (Ne.symm hbp) (Ne.symm hap') (Ne.symm hbp') hab
  set z : Fin 4 → ℝ → ℂ := fun l =>
    if l = a then ((ca : ℂ)⁻¹) • F a else if l = b then ((cb : ℂ)⁻¹) • F b else F l with hz
  have hca0 : (ca : ℂ) ≠ 0 := by exact_mod_cast hca.ne'
  have hcb0 : (cb : ℂ) ≠ 0 := by exact_mod_cast hcb.ne'
  have hzm : ∀ l, Measurable (z l) := by
    intro l; simp only [hz]; split_ifs
    · exact (hF a).const_smul _
    · exact (hF b).const_smul _
    · exact hF l
  have hscale : ∀ {c : ℝ}, 0 < c → ∀ {g : ℝ → ℂ},
      eLpNorm g 2 (normalizedIntervalMeasure a₀ r) ≤ ENNReal.ofReal c →
      eLpNorm (((c : ℂ)⁻¹) • g) 2 (normalizedIntervalMeasure a₀ r) ≤ 1 := by
    intro c hc g hg
    rw [eLpNorm_const_smul]
    calc ‖((c : ℂ))⁻¹‖ₑ * eLpNorm g 2 (normalizedIntervalMeasure a₀ r)
        ≤ ENNReal.ofReal c⁻¹ * ENNReal.ofReal c := by
          gcongr
          rw [← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      _ = 1 := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), inv_mul_cancel₀ hc.ne',
            ENNReal.ofReal_one]
  have hz2 : ∀ l, l ≠ p → l ≠ p' → eLpNorm (z l) 2 (normalizedIntervalMeasure a₀ r) ≤ 1 := by
    intro l h1 h2
    rcases hcov l with rfl | rfl | rfl | rfl
    · exact absurd rfl h1
    · exact absurd rfl h2
    · simp only [hz, ↓reduceIte]; exact hscale hca hFa
    · simp only [hz, hab.symm, ↓reduceIte]; exact hscale hcb hFb
  have hsmall := h z hzm hz2
  set Gz := slotPair z p p' X Y
  have he : slotPair F p p' X Y = Function.update (Function.update Gz a ((ca : ℂ) • Gz a)) b
      ((cb : ℂ) • (Function.update Gz a ((ca : ℂ) • Gz a)) b) := by
    funext l
    have hGa : Gz a = z a := slotPair_other hap hap' X Y
    have hGb : Gz b = z b := slotPair_other hbp hbp' X Y
    rcases hcov l with rfl | rfl | rfl | rfl
    · simp [Gz, slotPair_left hpp, Function.update_of_ne hap.symm, Function.update_of_ne hbp.symm]
    · simp [Gz, slotPair_right, Function.update_of_ne hap'.symm, Function.update_of_ne hbp'.symm]
    · rw [Function.update_of_ne hab, Function.update_self, hGa, hz]
      simp only [↓reduceIte, smul_smul, mul_inv_cancel₀ hca0, one_smul]
      exact slotPair_other hap hap' X Y
    · rw [Function.update_self, Function.update_of_ne hab.symm, hGb, hz]
      simp only [hab.symm, ↓reduceIte, smul_smul, mul_inv_cancel₀ hcb0, one_smul]
      exact slotPair_other hbp hbp' X Y
  rw [he, localProgressionForm_scale_slot, localProgressionForm_scale_slot, norm_mul, norm_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hca,
    abs_of_pos hcb]
  have : 0 ≤ ca * cb := by positivity
  nlinarith [norm_nonneg (localProgressionForm r w Gz)]

/-- The pair estimate with the spectators' exact normalized sizes. -/
theorem PairSmall.le_norm_mul {a₀ r : ℝ} {w : ℝ × ℝ → ℂ} {p p' : Fin 4}
    (hpp : p ≠ p') {X Y : ℝ → ℂ} {η : ℝ} (hη : 0 ≤ η)
    (h : PairSmall a₀ r w p p' X Y η) {F : Fin 4 → ℝ → ℂ} (hF : ∀ l, Measurable (F l))
    {a b : Fin 4} (hab : a ≠ b) (hap : a ≠ p) (hap' : a ≠ p') (hbp : b ≠ p) (hbp' : b ≠ p')
    (hfa : eLpNorm (F a) 2 (normalizedIntervalMeasure a₀ r) ≠ ⊤)
    (hfb : eLpNorm (F b) 2 (normalizedIntervalMeasure a₀ r) ≠ ⊤) :
    ‖localProgressionForm r w (slotPair F p p' X Y)‖ ≤
      (eLpNorm (F a) 2 (normalizedIntervalMeasure a₀ r)).toReal *
        (eLpNorm (F b) 2 (normalizedIntervalMeasure a₀ r)).toReal * η := by
  set na := (eLpNorm (F a) 2 (normalizedIntervalMeasure a₀ r)).toReal
  set nb := (eLpNorm (F b) 2 (normalizedIntervalMeasure a₀ r)).toReal
  have hna : 0 ≤ na := ENNReal.toReal_nonneg
  have hnb : 0 ≤ nb := ENNReal.toReal_nonneg
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set! t := min 1 (ε / (2 * ((na + nb + 1) * (η + 1))))
  have ht : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have hbound := h.le_mul hpp hF hab hap hap' hbp hbp' (ca := na + t) (cb := nb + t)
    (by linarith) (by linarith)
    (by rw [← ENNReal.ofReal_toReal hfa]; exact ENNReal.ofReal_le_ofReal (by linarith))
    (by rw [← ENNReal.ofReal_toReal hfb]; exact ENNReal.ofReal_le_ofReal (by linarith))
  have hte : t * ((na + nb + 1) * (η + 1)) ≤ ε / 2 := by
    have := min_le_right 1 (ε / (2 * ((na + nb + 1) * (η + 1))))
    calc t * ((na + nb + 1) * (η + 1)) ≤ ε / (2 * ((na + nb + 1) * (η + 1))) *
          ((na + nb + 1) * (η + 1)) := by gcongr
      _ = ε / 2 := by field_simp
  have : (na + t) * (nb + t) * η ≤ na * nb * η + t * ((na + nb + 1) * (η + 1)) := by
    have : t * t ≤ t := by nlinarith
    nlinarith [mul_nonneg hna hη, mul_nonneg hnb hη]
  calc _ ≤ (na + t) * (nb + t) * η := hbound
    _ ≤ na * nb * η + t * ((na + nb + 1) * (η + 1)) := this
    _ ≤ na * nb * η + ε / 2 := by linarith
    _ < na * nb * η + ε := by linarith

/-! ### Several-variable charts from one-variable charts (blueprint lines 642-660) -/

/-- The lift of a one-variable chart along a linear functional `ℓ` on `ℝ^k`:
`z ↦ φ(ℓ · z)`. -/
noncomputable def liftChart {d k : ℕ} (B : QuadraticChartData d) (ℓ : Fin k → ℝ) :
    MultivariableQuadraticChartData k d where
  horizontal := fun i j => B.horizontal i * ℓ j
  quadratic := fun i j => B.quadratic * ℓ i * ℓ j
  symmetric := Matrix.IsSymm.ext fun i j => by ring
  linear := fun j => B.linear * ℓ j
  matrix := B.matrix
  amplitude := B.amplitude
  smooth := B.smooth
  compact := B.compact

theorem liftChart_alongLine {d k : ℕ} (B : QuadraticChartData d) (ℓ z : Fin k → ℝ) :
    multivariableChartAlongLine (liftChart B ℓ) z = dilateQuadraticChart (ℓ ⬝ᵥ z) B := by
  cases B
  simp only [multivariableChartAlongLine, liftChart, dilateQuadraticChart, dotProduct,
    QuadraticChartData.mk.injEq]
  refine ⟨?_, ?_, ?_, trivial, trivial⟩
  · funext i
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · simp only [Finset.mul_sum, Finset.sum_mul, pow_two]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem liftChart_atom {d k : ℕ} (B : QuadraticChartData d) (ℓ z : Fin k → ℝ) :
    multivariableQuadraticChartAtom (liftChart B ℓ) z = quadraticChartAtom B (ℓ ⬝ᵥ z) := by
  have h := multivariableChartAlongLine_atom (liftChart B ℓ) z 1
  rw [one_smul, liftChart_alongLine, dilateQuadraticChart_atom, mul_one] at h
  exact h.symm

theorem liftChart_complexity {d k c₀ : ℕ} {H : ℝ} {B : QuadraticChartData d}
    (hB : QuadraticChartComplexity c₀ H B) (ℓ : Fin k → ℝ) :
    MultivariableQuadraticChartComplexity c₀ H (liftChart B ℓ) := by
  unfold MultivariableQuadraticChartComplexity
  rw [liftChart_alongLine]
  exact dilateQuadraticChart_complexity hB _

/-- The product of two several-variable charts in the same variables. -/
noncomputable def mvProductChart {k d e : ℕ} (M : MultivariableQuadraticChartData k d)
    (N : MultivariableQuadraticChartData k e) : MultivariableQuadraticChartData k (d + e) where
  horizontal := Fin.append M.horizontal N.horizontal
  quadratic := M.quadratic + N.quadratic
  symmetric := M.symmetric.add N.symmetric
  linear := M.linear + N.linear
  matrix := chartBlockMatrix M.matrix N.matrix
  amplitude := productChartAmplitude (multivariableChartAlongLine M 0)
    (multivariableChartAlongLine N 0)
  smooth := productChartAmplitude_smooth _ _
  compact := productChartAmplitude_compact _ _

theorem mvProductChart_alongLine {k d e : ℕ} (M : MultivariableQuadraticChartData k d)
    (N : MultivariableQuadraticChartData k e) (v : Fin k → ℝ) :
    multivariableChartAlongLine (mvProductChart M N) v =
      productQuadraticChart (multivariableChartAlongLine M v)
        (multivariableChartAlongLine N v) := by
  simp only [multivariableChartAlongLine, mvProductChart, productQuadraticChart,
    QuadraticChartData.mk.injEq]
  refine ⟨?_, ?_, ?_, trivial, ?_⟩
  · funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Matrix.mulVec]
      rw [Fin.append_left]
      exact congrArg (· ⬝ᵥ v) (Fin.append_left M.horizontal N.horizontal i)
    · simp only [Matrix.mulVec]
      rw [Fin.append_right]
      exact congrArg (· ⬝ᵥ v) (Fin.append_right M.horizontal N.horizontal i)
  · simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  · rfl

theorem mvProductChart_atom {k d e : ℕ} (M : MultivariableQuadraticChartData k d)
    (N : MultivariableQuadraticChartData k e) (z : Fin k → ℝ) :
    multivariableQuadraticChartAtom (mvProductChart M N) z =
      multivariableQuadraticChartAtom M z * multivariableQuadraticChartAtom N z := by
  have h := multivariableChartAlongLine_atom (mvProductChart M N) z 1
  have hM := multivariableChartAlongLine_atom M z 1
  have hN := multivariableChartAlongLine_atom N z 1
  rw [one_smul] at h hM hN
  rw [← h, ← hM, ← hN, mvProductChart_alongLine, productQuadraticChart_atom]

theorem mvProductChart_complexity {k d e c₀ : ℕ} {H : ℝ}
    {M : MultivariableQuadraticChartData k d} {N : MultivariableQuadraticChartData k e}
    (hM : MultivariableQuadraticChartComplexity c₀ H M)
    (hN : MultivariableQuadraticChartComplexity c₀ H N) (hc : 1 ≤ c₀) :
    MultivariableQuadraticChartComplexity c₀ (H ^ 6) (mvProductChart M N) := by
  unfold MultivariableQuadraticChartComplexity at *
  rw [mvProductChart_alongLine]
  exact productQuadraticChart_complexity hM hN hc

/-- Dilation of a several-variable chart: `z ↦ Q(a z)`. -/
noncomputable def mvDilateChart {k d : ℕ} (a : ℝ) (A : MultivariableQuadraticChartData k d) :
    MultivariableQuadraticChartData k d where
  horizontal := fun i j => A.horizontal i j * a
  quadratic := fun i j => A.quadratic i j * a ^ 2
  symmetric := Matrix.IsSymm.ext fun i j => by
    rw [A.symmetric.apply i j]
  linear := fun j => A.linear j * a
  matrix := A.matrix
  amplitude := A.amplitude
  smooth := A.smooth
  compact := A.compact

theorem mvDilateChart_alongLine {k d : ℕ} (a : ℝ) (A : MultivariableQuadraticChartData k d)
    (v : Fin k → ℝ) :
    multivariableChartAlongLine (mvDilateChart a A) v =
      multivariableChartAlongLine A (a • v) := by
  simp only [multivariableChartAlongLine, mvDilateChart, QuadraticChartData.mk.injEq,
    Pi.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, trivial, trivial⟩
  · funext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · exact Finset.sum_congr rfl fun j _ => by ring

theorem mvDilateChart_atom {k d : ℕ} (a : ℝ) (A : MultivariableQuadraticChartData k d)
    (z : Fin k → ℝ) :
    multivariableQuadraticChartAtom (mvDilateChart a A) z =
      multivariableQuadraticChartAtom A (a • z) := by
  have h := multivariableChartAlongLine_atom (mvDilateChart a A) z 1
  have h' := multivariableChartAlongLine_atom A (a • z) 1
  rw [one_smul] at h h'
  rw [← h, ← h', mvDilateChart_alongLine]

theorem mvDilateChart_complexity {k d c₀ : ℕ} {H : ℝ}
    {A : MultivariableQuadraticChartData k d}
    (hA : MultivariableQuadraticChartComplexity c₀ H A) (a : ℝ) :
    MultivariableQuadraticChartComplexity c₀ H (mvDilateChart a A) := by
  unfold MultivariableQuadraticChartComplexity at *
  rw [mvDilateChart_alongLine, smul_zero]
  exact hA

/-- The effective quadratic form of a several-variable chart for a rational matrix `M`,
symmetrized: `Λ + sym(Vᵀ M V)`. -/
noncomputable def mvEffQuad {k d : ℕ} (A : MultivariableQuadraticChartData k d)
    (M : Matrix (Fin d) (Fin d) ℚ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => A.quadratic i j + (1 / 2 : ℝ) * ∑ a, ∑ b, (M a b : ℝ) *
    (A.horizontal a i * A.horizontal b j + A.horizontal a j * A.horizontal b i)

theorem effectiveReturnQuadratic_eq_sym {d k : ℕ} (C : Matrix (Fin d) (Fin d) ℝ)
    (Λ : Matrix (Fin k) (Fin k) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (Qr : Matrix (Fin d) (Fin d) ℝ) :
    effectiveReturnQuadratic C Λ V ((1 - Qr) * V) (Qr * V) =
      Λ + realSymmetricPart (V.transpose *
        ((1 / 2 : ℝ) • realSymmetricPart C + (1 - Qr).transpose * realSkewPart C * Qr) * V) := by
  simp only [effectiveReturnQuadratic, realSymmetricPart, realSkewPart, Matrix.transpose_add,
    Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_transpose, Matrix.transpose_one, Matrix.add_mul, Matrix.mul_add,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
    Matrix.one_mul]
  module

theorem effectiveReturnQuadratic_eq_mvEffQuad {k d : ℕ}
    (A : MultivariableQuadraticChartData k d) (Q : Matrix (Fin d) (Fin d) ℚ) :
    effectiveReturnQuadratic (A.matrix.map (fun q => (q : ℝ))) A.quadratic A.horizontal
      ((1 - Q.map (fun q => (q : ℝ))) * A.horizontal) (Q.map (fun q => (q : ℝ)) * A.horizontal) =
      mvEffQuad A (separatedPhaseMatrix A.matrix Q) := by
  rw [effectiveReturnQuadratic_eq_sym, ← separatedPhaseMatrix_cast]
  ext i j
  simp only [mvEffQuad, Matrix.of_apply, Matrix.add_apply, realSymmetricPart, Matrix.smul_apply,
    Matrix.transpose_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul]
  congr 1
  simp only [Finset.sum_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun x y => _ * (A.horizontal y i * _ * A.horizontal x j)),
    Finset.sum_comm (f := fun x y => _ * (A.horizontal y j * _ * A.horizontal x i))]
  congr 1 <;> refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- Blueprint lem:separation in up to three variables: lemmas `lem:weyl` and
`lem:chartfourier` combined. If the Fourier supremum of `θ Q` is at least `δ`, then on the box
`Q(z) = e(zᵀΛ_* z + b·z) Σ a_ℓ e(σ_ℓ·Vz)` exactly and absolutely, with
`Λ_* = Λ + sym(Vᵀ M V)` for a rational matrix `M` of bounded height and bounded entries. -/
theorem mvSeparatedPhase (c₀ : ℕ) (hc : 1 ≤ c₀) (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (R : ℝ)
    (hR : 0 ≤ R) :
    ∃ D : ℕ, 1 ≤ D ∧ ∃ DJ : ℕ → ℕ, ∀ {d : ℕ} (H δ : ℝ) (A : MultivariableQuadraticChartData k d),
      MultivariableQuadraticChartComplexity c₀ H A →
      ∀ θ : (Fin k → ℝ) → ℂ, Measurable θ → (∀ z, ‖θ z‖ ≤ H) →
      (∀ x y, ‖θ y - θ x‖ ≤ H * ‖y - x‖) → (∀ z, θ z ≠ 0 → ∀ i, |z i| ≤ R) → 0 < δ →
      (∀ t < δ, ∃ ξ : EuclideanSpace ℝ (Fin k), t < ‖𝓕 (fun z : EuclideanSpace ℝ (Fin k) =>
        θ z.ofLp * multivariableQuadraticChartAtom A z.ofLp) ξ‖) →
      let X := 1 + Real.log H + Real.log (max 1 δ⁻¹)
      ∃ M : Matrix (Fin d) (Fin d) ℚ,
        (∀ i j, (rationalHeight (M i j) : ℝ) ≤ Real.exp (D * X ^ D)) ∧
        (∀ i j, |mvEffQuad A M i j| ≤ Real.exp (D * X ^ D)) ∧
        ∃ (ι : Type) (_ : Fintype ι) (σ : ι × (Fin (d + d) → ℤ) → Fin d → ℚ),
          (Fintype.card ι : ℝ) ≤ Real.exp (D * X ^ D) ∧
          (∀ p i, (rationalHeight (σ p i) : ℝ) ≤
            Real.exp (D * X ^ D) * (1 + frequencyLength p.2)) ∧
          ∃ a : ι × (Fin (d + d) → ℤ) → ℂ,
            (∀ z : Fin k → ℝ, (∀ i, |z i| ≤ R) →
              HasSum (fun p => a p * (Real.fourierChar (dotProduct (fun i => (σ p i : ℝ))
                  (A.horizontal.mulVec z)) : ℂ))
                ((Real.fourierChar (-(dotProduct z ((mvEffQuad A M).mulVec z) +
                    dotProduct A.linear z)) : ℂ) * multivariableQuadraticChartAtom A z)) ∧
            Summable (fun p => ‖a p‖) ∧ (∑' p, ‖a p‖) ≤ Real.exp (D * X ^ D) ∧
            ∀ J : ℕ,
              (∀ p, ‖a p‖ * (1 + frequencyLength p.2) ^ (J * (d + 1) ^ 2) ≤
                Real.exp (DJ J * X ^ DJ J)) ∧
              ∀ T : ℝ, 1 ≤ T →
                (∑ f : ι, ∑ v ∈ frequencyShell (d + d) T, ‖a (f, v)‖) *
                    T ^ (J * (d + 1) ^ 2) ≤ Real.exp (DJ J * X ^ DJ J) := by
  obtain ⟨Dw, hDw, hweyl⟩ := weylSplitting c₀ hc R hR
  obtain ⟨Ds, hDs, DJs, hsplit⟩ := splitFourierExpansion c₀ hc k R hR
  set Dm : ℕ := 12 * (1 + Dw) + Ds * (1 + Dw) ^ Ds + Dw * Ds + Dw + 3 with hDm
  have hDm1 : Dw * Ds ≤ Dm := by
    rw [hDm]; generalize Ds * (1 + Dw) ^ Ds = x; generalize Dw * Ds = y; omega
  have hDm2 : Dw + 2 ≤ Dm := by
    rw [hDm]; generalize Ds * (1 + Dw) ^ Ds = x; generalize Dw * Ds = y; omega
  have hDm3 : Dw ≤ Dm := by omega
  refine ⟨Dm, by omega, fun J => DJs J * (1 + Dw) ^ (DJs J) + Dw * DJs J + 1, ?_⟩
  intro d H δ A hA θ hθm hθb hθL hθs hδ hF X
  obtain ⟨U, Q, hQU, hPU, hiso, hQh, hPh, hVs, hΛ⟩ :=
    hweyl hk1 hk3 H A hA θ hθm hθb hθL hθs δ hδ hF
  set B := Real.exp ((Dw : ℝ) * (1 + Real.log H + Real.log (max 1 δ⁻¹)) ^ Dw) with hBdef
  have hH1 : 1 ≤ H := by linarith [hA.lower, Real.add_one_le_exp (2 : ℝ)]
  have hlogH : 2 ≤ Real.log H := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) hA.lower
  have hlogδ : 0 ≤ Real.log (max 1 δ⁻¹) := Real.log_nonneg (le_max_left _ _)
  have hX3 : 3 ≤ X := by simp only [X]; linarith
  have hX1 : 1 ≤ X := by linarith
  have hXD : 1 ≤ (Dw : ℝ) * X ^ Dw := by
    have : (1 : ℝ) ≤ X ^ Dw := one_le_pow₀ hX1
    have : (1 : ℝ) ≤ Dw := by exact_mod_cast hDw
    nlinarith
  have hB2 : 2 ≤ B := by
    have : Real.exp 1 ≤ B := Real.exp_le_exp.mpr hXD
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hQs : Q.IsSymm := isSymm_of_realMatrixOperator_starProjection hQU
  have hiso' := isotropy_matrix_of_starProjection hPU hiso
  obtain ⟨ι, hι, σ, hcard, hσ, hrest⟩ := hsplit (d := d) H B hA.lower hA.dimension hB2
    A.matrix Q (fun i j => hA.height i j) hQs hQh hiso'
  obtain ⟨a, hexp, hsumm, htot, hJ⟩ := hrest A rfl hA hVs
  set! M := separatedPhaseMatrix A.matrix Q with hMdef
  have hΛe := effectiveReturnQuadratic_eq_mvEffQuad A Q
  have hX0 : 0 ≤ 1 + Real.log H + Real.log B := by
    have : 0 ≤ Real.log B := Real.log_nonneg (by linarith); linarith
  have hXs : 1 + Real.log H + Real.log B ≤ (1 + Dw) * X ^ Dw := by
    rw [hBdef, Real.log_exp]
    have h1 : X ≤ X ^ Dw := le_self_pow₀ hX1 (by omega)
    have h2 : 1 + Real.log H ≤ X := by simp only [X]; linarith
    change 1 + Real.log H + (Dw : ℝ) * X ^ Dw ≤ (1 + Dw) * X ^ Dw
    nlinarith only [hlogδ, h1]
  have hcomp := exp_compose_budget (Ds := Ds) hX0 hXs
  have hDsm : Real.exp (((Ds : ℝ) * (1 + Dw) ^ Ds) * X ^ (Dw * Ds)) ≤
      Real.exp (Dm * X ^ Dm) :=
    exp_poly_le hX1 hDm1 (by
      rw [hDm]; push_cast
      have : (0 : ℝ) ≤ Dw * Ds := by positivity
      linarith)
  have hmain : ∀ {y : ℝ}, y ≤ Real.exp (Ds * (1 + Real.log H + Real.log B) ^ Ds) →
      y ≤ Real.exp (Dm * X ^ Dm) := fun h => (h.trans hcomp).trans hDsm
  refine ⟨M, ?_, ?_, ι, hι, σ, hmain hcard, fun p i => (hσ p i).trans
    (mul_le_mul_of_nonneg_right (hmain le_rfl) (by
      have := frequencyLength_nonneg p.2; linarith)), a, ?_, hsumm, hmain htot, ?_⟩
  · intro i j
    have h := separatedPhaseMatrix_height (H := H) (B := B) hH1 (by linarith) A.matrix Q
      (fun i j => hA.height i j) hQh i j
    have hdX : (d : ℝ) ≤ X := by
      have := hA.dimension; simp only [X]; linarith
    have hb := phase_height_budget (Dw := Dw) hDw hH1 (by simp only [X]; linarith) hX3 hdX
    refine h.trans (hb.trans (exp_poly_le hX1 hDm2 (by
      rw [hDm]; push_cast
      have : (0 : ℝ) ≤ Ds * (1 + Dw) ^ Ds + Dw * Ds := by positivity
      linarith)))
  · intro i j
    have h := realMatrix_abs_entry_le_norm (mvEffQuad A M) i j
    have hΛ' := hΛ
    rw [one_sub_map_cast, hΛe] at hΛ'
    refine (h.trans hΛ').trans (exp_poly_le hX1 hDm3 (by
      rw [hDm]; push_cast
      have : (0 : ℝ) ≤ Ds * (1 + Dw) ^ Ds + Dw * Ds := by positivity
      linarith))
  · intro z hz
    have h := hexp z hz
    rw [hΛe] at h
    exact h
  · intro J
    have hcompJ := exp_compose_budget (Ds := DJs J) hX0 hXs
    have hJm : Real.exp (((DJs J : ℝ) * (1 + Dw) ^ DJs J) * X ^ (Dw * DJs J)) ≤
        Real.exp (((DJs J * (1 + Dw) ^ DJs J + Dw * DJs J + 1 : ℕ) : ℝ) *
          X ^ (DJs J * (1 + Dw) ^ DJs J + Dw * DJs J + 1)) :=
      exp_poly_le hX1 (by omega) (by
        push_cast
        have : (0 : ℝ) ≤ Dw * DJs J := by positivity
        linarith)
    obtain ⟨hp, hs⟩ := hJ J
    exact ⟨fun p => ((hp p).trans hcompJ).trans hJm,
      fun T hT => ((hs T hT).trans hcompJ).trans hJm⟩

/-! ### One-dimensional Fourier estimates for a kernel slice -/

theorem fourierChar_add_half_div (ν x : ℝ) (hν : ν ≠ 0) :
    (Real.fourierChar (ν * (x + 1 / (2 * ν))) : ℂ) = -(Real.fourierChar (ν * x) : ℂ) := by
  have e : ν * (x + 1 / (2 * ν)) = ν * x + 1 / 2 := by field_simp
  rw [e, AddChar.map_add_eq_mul, Circle.coe_mul]
  have h2 : (Real.fourierChar (1 / 2) : ℂ) = -1 := by
    rw [Real.fourierChar_apply]
    rw [show (2 * Real.pi * (1 / 2 : ℝ) : ℝ) = Real.pi by ring]
    rw [Complex.exp_pi_mul_I]
  rw [h2]; ring

theorem continuous_fourierChar_mul (ν : ℝ) :
    Continuous fun x : ℝ => (Real.fourierChar (ν * x) : ℂ) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_const.mul
      continuous_id))

theorem hasCompactSupport_of_abs_le {f : ℝ → ℂ} {R : ℝ} (hs : ∀ x, R < |x| → f x = 0) :
    HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_closedBall 0 R) fun x hx => hs x (by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hx; linarith [not_le.mp hx])

/-- Fourier decay of a Lipschitz function of compact support, by the half-period shift. -/
theorem lipschitz_fourier_decay {f : ℝ → ℂ} {L R : ℝ} (hR : 0 ≤ R) (hf : Continuous f)
    (hL : ∀ x y, ‖f x - f y‖ ≤ L * |x - y|) (hs : ∀ x, R < |x| → f x = 0) {ν : ℝ}
    (hν : 1 ≤ |ν|) :
    ‖∫ x, f x * (Real.fourierChar (ν * x) : ℂ)‖ ≤ L * (R + 1) / |ν| := by
  have hν0 : ν ≠ 0 := by intro h; rw [h, abs_zero] at hν; linarith
  have hνp : 0 < |ν| := abs_pos.mpr hν0
  set h := 1 / (2 * ν) with hh
  have hha : |h| = 1 / (2 * |ν|) := by rw [hh, abs_div, abs_mul]; norm_num
  have hh1 : |h| ≤ 1 / 2 := by
    rw [hha, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hfc := hasCompactSupport_of_abs_le hs
  have hcont : Continuous fun x => f x * (Real.fourierChar (ν * x) : ℂ) :=
    hf.mul (continuous_fourierChar_mul ν)
  have hint : Integrable fun x => f x * (Real.fourierChar (ν * x) : ℂ) :=
    hcont.integrable_of_hasCompactSupport (hfc.mul_right)
  have hcont' : Continuous fun x => f (x + h) * (Real.fourierChar (ν * x) : ℂ) :=
    (hf.comp (continuous_id.add continuous_const)).mul
      (continuous_fourierChar_mul ν)
  have hint' : Integrable fun x => f (x + h) * (Real.fourierChar (ν * x) : ℂ) :=
    hcont'.integrable_of_hasCompactSupport ((hfc.comp_homeomorph (Homeomorph.addRight h)).mul_right)
  have hshift : (∫ x, f x * (Real.fourierChar (ν * x) : ℂ)) =
      -∫ x, f (x + h) * (Real.fourierChar (ν * x) : ℂ) := by
    rw [← integral_add_right_eq_self (fun x => f x * (Real.fourierChar (ν * x) : ℂ)) h,
      ← integral_neg]
    congr 1; funext x
    rw [fourierChar_add_half_div ν x hν0]; ring
  have h2 : 2 * (∫ x, f x * (Real.fourierChar (ν * x) : ℂ)) =
      ∫ x, (f x - f (x + h)) * (Real.fourierChar (ν * x) : ℂ) := by
    have : (∫ x, (f x - f (x + h)) * (Real.fourierChar (ν * x) : ℂ)) =
        (∫ x, f x * (Real.fourierChar (ν * x) : ℂ)) -
          ∫ x, f (x + h) * (Real.fourierChar (ν * x) : ℂ) := by
      rw [← integral_sub hint hint']; congr 1; funext x; ring
    rw [this]
    linear_combination hshift
  have hbound : ∀ x, ‖(f x - f (x + h)) * (Real.fourierChar (ν * x) : ℂ)‖ ≤
      Set.indicator (Set.Icc (-(R + 1)) (R + 1)) (fun _ => L * |h|) x := by
    intro x
    rw [norm_mul, Circle.norm_coe, mul_one]
    by_cases hx : x ∈ Set.Icc (-(R + 1)) (R + 1)
    · rw [Set.indicator_of_mem hx]
      have := hL x (x + h)
      rwa [show x - (x + h) = -h by ring, abs_neg] at this
    · rw [Set.indicator_of_notMem hx]
      have hx' : R + 1 < |x| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have hxh : R < |x + h| := by
        have := abs_add_le (x + h) (-h)
        rw [add_neg_cancel_right, abs_neg] at this
        linarith
      rw [hs x (by linarith), hs (x + h) hxh, sub_zero, norm_zero]
  have hL0 : 0 ≤ L := by
    have := hL 0 1
    have h0 : 0 ≤ ‖f 0 - f 1‖ := norm_nonneg _
    norm_num at this; linarith
  have hI : ‖∫ x, (f x - f (x + h)) * (Real.fourierChar (ν * x) : ℂ)‖ ≤ L * |h| * (2 * (R + 1)) :=
      by
    calc _ ≤ ∫ x, Set.indicator (Set.Icc (-(R + 1)) (R + 1)) (fun _ => L * |h|) x :=
          norm_integral_le_of_norm_le
            ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc)
            (Filter.Eventually.of_forall hbound)
      _ = L * |h| * (2 * (R + 1)) := by
          rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc, smul_eq_mul]
          rw [max_eq_left (by linarith)]; ring
  have h2n : ‖2 * (∫ x, f x * (Real.fourierChar (ν * x) : ℂ))‖ =
      2 * ‖∫ x, f x * (Real.fourierChar (ν * x) : ℂ)‖ := by
    rw [norm_mul]; norm_num
  have key : 2 * ‖∫ x, f x * (Real.fourierChar (ν * x) : ℂ)‖ ≤ L * |h| * (2 * (R + 1)) := by
    rw [← h2n, h2]; exact hI
  have e : L * |h| * (2 * (R + 1)) = 2 * (L * (R + 1) / |ν|) / 2 := by
    rw [hha]; field_simp
  rw [e] at key
  have : 0 ≤ L * (R + 1) / |ν| := by positivity
  linarith [norm_nonneg (∫ x, f x * (Real.fourierChar (ν * x) : ℂ))]

/-- A function with vanishing integral against a low frequency. -/
theorem zero_mean_fourier_small {f : ℝ → ℂ} {K R : ℝ} (hR : 0 ≤ R) (hf : Continuous f)
    (hK : ∀ x, ‖f x‖ ≤ K) (hs : ∀ x, R < |x| → f x = 0) (h0 : ∫ x, f x = 0) (ν : ℝ) :
    ‖∫ x, f x * (Real.fourierChar (ν * x) : ℂ)‖ ≤ 2 * Real.pi * K * |ν| * R * (2 * R) := by
  have hfc := hasCompactSupport_of_abs_le hs
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfc
  have hcont : Continuous fun x => f x * (Real.fourierChar (ν * x) : ℂ) :=
    hf.mul (continuous_fourierChar_mul ν)
  have hint : Integrable fun x => f x * (Real.fourierChar (ν * x) : ℂ) :=
    hcont.integrable_of_hasCompactSupport (hfc.mul_right)
  have he : (∫ x, f x * (Real.fourierChar (ν * x) : ℂ)) =
      ∫ x, f x * ((Real.fourierChar (ν * x) : ℂ) - 1) := by
    rw [show (fun x => f x * ((Real.fourierChar (ν * x) : ℂ) - 1)) =
      fun x => f x * (Real.fourierChar (ν * x) : ℂ) - f x by funext x; ring,
      integral_sub hint hfi, h0, sub_zero]
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hbound : ∀ x, ‖f x * ((Real.fourierChar (ν * x) : ℂ) - 1)‖ ≤
      Set.indicator (Set.Icc (-R) R) (fun _ => K * (2 * Real.pi * (|ν| * R))) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (-R) R
    · rw [Set.indicator_of_mem hx, norm_mul]
      refine mul_le_mul (hK x) ((chart_fourierChar_sub_one_norm_le _).trans ?_) (norm_nonneg _)
        hK0
      rw [abs_mul]
      gcongr
      exact abs_le.mpr hx
    · rw [Set.indicator_of_notMem hx]
      have hx' : R < |x| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [hs x hx', zero_mul, norm_zero]
  rw [he]
  calc _ ≤ ∫ x, Set.indicator (Set.Icc (-R) R) (fun _ => K * (2 * Real.pi * (|ν| * R))) x :=
        norm_integral_le_of_norm_le ((continuous_const.integrableOn_Icc).integrable_indicator
            measurableSet_Icc)
          (Filter.Eventually.of_forall hbound)
    _ = _ := by
        rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc, smul_eq_mul,
          max_eq_left (by linarith)]
        ring

/-! ### The doubled kernel in three variables -/

/-- The doubled kernel `θ(u, τ, τ') = W(u, τ) conj W(u, τ')` (blueprint prop:base, line 1645). -/
noncomputable def sixTheta (W : ℝ × ℝ → ℂ) (z : Fin 3 → ℝ) : ℂ :=
  W (z 0, z 1) * conj (W (z 0, z 2))

theorem integral_fin_three (F : (Fin 3 → ℝ) → ℂ) :
    ∫ z, F z = ∫ p : ℝ × (Fin 2 → ℝ), F (Fin.insertNth 0 p.1 p.2) := by
  rw [← (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm.integral_comp']
  rfl

theorem integral_fin_two (F : (Fin 2 → ℝ) → ℂ) :
    ∫ y, F y = ∫ q : ℝ × ℝ, F ![q.1, q.2] := by
  rw [← (volume_preserving_finTwoArrow ℝ).symm.integral_comp']
  rfl

/-- The `τ`-integral controls the Fourier coefficients of the doubled kernel. -/
theorem sixTheta_fourier_bound {W : ℝ × ℝ → ℂ} {K R S : ℝ} (hR : 0 ≤ R) (hW : Continuous W)
    (hK : ∀ p, ‖W p‖ ≤ K) (hs : ∀ p, W p ≠ 0 → |p.1| ≤ R ∧ |p.2| ≤ R) (ν : Fin 3 → ℝ)
    (hS : ∀ u, ‖∫ τ, W (u, τ) * (Real.fourierChar (ν 1 * τ) : ℂ)‖ ≤ S) :
    ‖∫ z, sixTheta W z * (Real.fourierChar (ν ⬝ᵥ z) : ℂ)‖ ≤ 2 * R * (S * (2 * R * K)) := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0)
  set F : ℝ × (Fin 2 → ℝ) → ℂ := fun p =>
    sixTheta W (Fin.insertNth 0 p.1 p.2) *
      (Real.fourierChar (ν ⬝ᵥ (Fin.insertNth 0 p.1 p.2 : Fin 3 → ℝ)) : ℂ) with hF
  have hFe : ∀ a (y : Fin 2 → ℝ), F (a, y) = (Real.fourierChar (ν 0 * a) : ℂ) *
      ((W (a, y 0) * (Real.fourierChar (ν 1 * y 0) : ℂ)) *
        (conj (W (a, y 1)) * (Real.fourierChar (ν 2 * y 1) : ℂ))) := by
    intro a y
    simp only [hF, sixTheta, dotProduct, Fin.sum_univ_three]
    have e0 : (Fin.insertNth 0 a y : Fin 3 → ℝ) 0 = a := Fin.insertNth_apply_same _ _ _
    have e1 : (Fin.insertNth 0 a y : Fin 3 → ℝ) 1 = y 0 := by
      change (Fin.insertNth 0 a y : Fin 3 → ℝ) (Fin.succAbove 0 0) = y 0
      exact Fin.insertNth_apply_succAbove (α := fun _ => ℝ) (0 : Fin 3) a y 0
    have e2 : (Fin.insertNth 0 a y : Fin 3 → ℝ) 2 = y 1 := by
      change (Fin.insertNth 0 a y : Fin 3 → ℝ) (Fin.succAbove 0 1) = y 1
      exact Fin.insertNth_apply_succAbove (α := fun _ => ℝ) (0 : Fin 3) a y 1
    rw [e0, e1, e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, Circle.coe_mul,
      Circle.coe_mul]
    ring
  have hWc : HasCompactSupport W := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × ℝ) R) fun p hp => ?_
    by_contra h
    obtain ⟨h1, h2⟩ := hs p h
    apply hp
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, Real.norm_eq_abs,
      Real.norm_eq_abs]
    exact ⟨h1, h2⟩
  have hcont : Continuous F := by
    have hins : Continuous fun p : ℝ × (Fin 2 → ℝ) => (Fin.insertNth 0 p.1 p.2 : Fin 3 → ℝ) :=
      Continuous.finInsertNth (A := fun _ : Fin 3 => ℝ) 0 continuous_fst continuous_snd
    refine Continuous.mul ?_ (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp ((continuous_const.dotProduct continuous_id).comp hins)))
    simp only [sixTheta]
    exact (hW.comp (((continuous_apply 0).comp hins).prodMk ((continuous_apply 1).comp hins))).mul
      (Complex.continuous_conj.comp
        (hW.comp (((continuous_apply 0).comp hins).prodMk ((continuous_apply 2).comp hins))))
  have hFc : HasCompactSupport F := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × (Fin 2 → ℝ)) R) fun p hp => ?_
    obtain ⟨a, y⟩ := p
    rw [hFe]
    by_contra h
    have h1 : W (a, y 0) ≠ 0 := fun h0 => h (by rw [h0]; ring)
    have h2 : W (a, y 1) ≠ 0 := fun h0 => h (by rw [h0]; simp)
    apply hp
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, Real.norm_eq_abs]
    refine ⟨(hs _ h1).1, (pi_norm_le_iff_of_nonneg hR).mpr fun i => ?_⟩
    rw [Real.norm_eq_abs]
    fin_cases i
    · exact (hs _ h1).2
    · exact (hs _ h2).2
  have hFi : Integrable F := hcont.integrable_of_hasCompactSupport hFc
  rw [integral_fin_three, Measure.volume_eq_prod, integral_prod _ hFi]
  have hinner : ∀ a, ‖∫ y, F (a, y)‖ ≤
      Set.indicator (Set.Icc (-R) R) (fun _ => S * (2 * R * K)) a := by
    intro a
    rw [integral_fin_two]
    simp only [hFe, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [integral_const_mul, Measure.volume_eq_prod, integral_prod_mul (fun b => W (a, b) *
        (Real.fourierChar (ν 1 * b) : ℂ))
      (fun c => conj (W (a, c)) * (Real.fourierChar (ν 2 * c) : ℂ)), norm_mul, Circle.norm_coe,
      one_mul, norm_mul]
    by_cases ha : a ∈ Set.Icc (-R) R
    · rw [Set.indicator_of_mem ha]
      refine mul_le_mul (hS a) ?_ (norm_nonneg _) hS0
      have hb : ∀ c, ‖conj (W (a, c)) * (Real.fourierChar (ν 2 * c) : ℂ)‖ ≤
          Set.indicator (Set.Icc (-R) R) (fun _ => K) c := by
        intro c
        rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_conj]
        by_cases hc : c ∈ Set.Icc (-R) R
        · rw [Set.indicator_of_mem hc]; exact hK _
        · rw [Set.indicator_of_notMem hc]
          by_contra hne
          have hW0 : W (a, c) ≠ 0 := fun h0 => hne (by rw [h0, norm_zero])
          exact hc (abs_le.mp (hs _ hW0).2)
      calc _ ≤ ∫ c, Set.indicator (Set.Icc (-R) R) (fun _ => K) c :=
            norm_integral_le_of_norm_le
              ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc)
              (Filter.Eventually.of_forall hb)
        _ = 2 * R * K := by
            rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc, smul_eq_mul,
              max_eq_left (by linarith)]
            ring
    · rw [Set.indicator_of_notMem ha]
      have hz : ∀ b, W (a, b) = 0 := by
        intro b
        by_contra hne
        exact ha (abs_le.mp (hs _ hne).1)
      simp [hz]
  calc _ ≤ ∫ a, Set.indicator (Set.Icc (-R) R) (fun _ => S * (2 * R * K)) a :=
        norm_integral_le_of_norm_le
          ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc)
          (Filter.Eventually.of_forall hinner)
    _ = _ := by
        rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc, smul_eq_mul,
          max_eq_left (by linarith)]
        ring

/-- Coefficient mass beyond a frequency truncation, for coefficients indexed by a finite family
times a frequency lattice. -/
theorem fintype_prod_tail {ι : Type*} [Fintype ι] {D k : ℕ} (hD : 1 ≤ D) (hk : D < k)
    (a : ι × (Fin D → ℤ) → ℂ) {E : ℝ} (hE : 0 ≤ E)
    (ha : ∀ p, ‖a p‖ * (1 + frequencyLength p.2) ^ k ≤ E) (K₀ : ℕ) :
    (∑' p, if p.2 ∈ frequencyTruncationSet D K₀ then 0 else ‖a p‖) ≤
      Fintype.card ι * (E * (2 * 7 ^ D * (2 * Real.pi) ^ k / 2 ^ K₀)) := by
  classical
  obtain ⟨hws, hwt⟩ := lattice_weight_tail hD hk K₀
  set w : (Fin D → ℤ) → ℝ := fun v => if v ≠ 0 ∧ (2 : ℝ) ^ K₀ ≤ 1 + frequencyLength v then
      ((1 + frequencyLength v) ^ k)⁻¹ else 0 with hw
  have hw0 : ∀ v, 0 ≤ w v := fun v => by
    have := frequencyLength_nonneg v
    simp only [hw]; split_ifs <;> positivity
  set g : ι × (Fin D → ℤ) → ℝ := fun p => E * w p.2 with hg
  have hg0 : 0 ≤ g := fun p => mul_nonneg hE (hw0 _)
  have hgs : Summable g := (summable_prod_of_nonneg hg0).mpr
    ⟨fun _ => hws.mul_left E, Summable.of_finite⟩
  have hle : ∀ p, (if p.2 ∈ frequencyTruncationSet D K₀ then 0 else ‖a p‖) ≤ g p := by
    intro p
    split_ifs with hp
    · exact hg0 p
    · rw [mem_frequencyTruncationSet, not_or, not_lt] at hp
      have hpos : 0 < (1 + frequencyLength p.2) ^ k := by
        have := frequencyLength_nonneg p.2; positivity
      simp only [hg, hw, ne_eq, hp.1, not_false_eq_true, hp.2, and_self, ↓reduceIte]
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]
      exact ha p
  have hfs : Summable fun p : ι × (Fin D → ℤ) =>
      if p.2 ∈ frequencyTruncationSet D K₀ then 0 else ‖a p‖ :=
    Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity) hle hgs
  calc _ ≤ ∑' p, g p := hfs.tsum_le_tsum hle hgs
    _ = ∑' i : ι, ∑' v, g (i, v) := hgs.tsum_prod' fun _ => hws.mul_left E
    _ = Fintype.card ι * (E * ∑' v, w v) := by
        rw [tsum_fintype]
        simp only [hg, tsum_mul_left, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := by gcongr

/-- The volume of the box `[-1,1]³`. -/
theorem volume_real_box_three :
    volume.real (Set.Icc (fun _ : Fin 3 => (-1 : ℝ)) fun _ => 1) = 8 := by
  rw [measureReal_def, Real.volume_Icc_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num)]
  norm_num

theorem integral_box_three_le {F : (Fin 3 → ℝ) → ℂ} {c : ℝ}
    (hF : ∀ z, ‖F z‖ ≤ Set.indicator (Set.Icc (fun _ : Fin 3 => (-1 : ℝ)) fun _ => 1)
      (fun _ => c) z) : ‖∫ z, F z‖ ≤ 8 * c := by
  calc _ ≤ ∫ z, Set.indicator (Set.Icc (fun _ : Fin 3 => (-1 : ℝ)) fun _ => 1) (fun _ => c) z :=
        norm_integral_le_of_norm_le
          ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc)
          (Filter.Eventually.of_forall hF)
    _ = 8 * c := by
        rw [integral_indicator_const _ measurableSet_Icc, volume_real_box_three, smul_eq_mul]

theorem sixTheta_continuous {W : ℝ × ℝ → ℂ} (hW : Continuous W) : Continuous (sixTheta W) :=
  (hW.comp ((continuous_apply 0).prodMk (continuous_apply 1))).mul
    (Complex.continuous_conj.comp (hW.comp ((continuous_apply 0).prodMk (continuous_apply 2))))

theorem sixTheta_norm_le {W : ℝ × ℝ → ℂ} {K : ℝ} (hK : ∀ p, ‖W p‖ ≤ K) (z : Fin 3 → ℝ) :
    ‖sixTheta W z‖ ≤ K ^ 2 := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  rw [sixTheta, norm_mul, Complex.norm_conj, sq]
  exact mul_le_mul (hK _) (hK _) (norm_nonneg _) hK0

theorem sixTheta_support {W : ℝ × ℝ → ℂ} (hs : ∀ p, W p ≠ 0 → |p.1| ≤ 1 ∧ |p.2| ≤ 1)
    {z : Fin 3 → ℝ} (hz : sixTheta W z ≠ 0) : ∀ i, |z i| ≤ 1 := by
  rw [sixTheta, mul_ne_zero_iff] at hz
  have h1 := hs _ hz.1
  have h2 := hs _ (fun h => hz.2 (by rw [h, map_zero]))
  intro i
  fin_cases i
  · exact h1.1
  · exact h1.2
  · exact h2.2

theorem sixTheta_mem_box {W : ℝ × ℝ → ℂ} (hs : ∀ p, W p ≠ 0 → |p.1| ≤ 1 ∧ |p.2| ≤ 1)
    {z : Fin 3 → ℝ} (hz : sixTheta W z ≠ 0) :
    z ∈ Set.Icc (fun _ : Fin 3 => (-1 : ℝ)) fun _ => 1 :=
  ⟨fun i => (abs_le.mp (sixTheta_support hs hz i)).1,
    fun i => (abs_le.mp (sixTheta_support hs hz i)).2⟩

theorem sixTheta_hasCompactSupport {W : ℝ × ℝ → ℂ}
    (hs : ∀ p, W p ≠ 0 → |p.1| ≤ 1 ∧ |p.2| ≤ 1) : HasCompactSupport (sixTheta W) :=
  HasCompactSupport.intro isCompact_Icc fun z hz => by
    by_contra h; exact hz (sixTheta_mem_box hs h)

/-- Bound by `K²` times an indicator of the box. -/
theorem sixTheta_mul_norm_le {W : ℝ × ℝ → ℂ} {K c : ℝ} (hK : ∀ p, ‖W p‖ ≤ K)
    (hs : ∀ p, W p ≠ 0 → |p.1| ≤ 1 ∧ |p.2| ≤ 1) {g : (Fin 3 → ℝ) → ℂ}
    (hg : ∀ z, (∀ i, |z i| ≤ 1) → ‖g z‖ ≤ c) (z : Fin 3 → ℝ) :
    ‖sixTheta W z * g z‖ ≤
      Set.indicator (Set.Icc (fun _ : Fin 3 => (-1 : ℝ)) fun _ => 1) (fun _ => K ^ 2 * c) z := by
  by_cases h : sixTheta W z = 0
  · rw [h, zero_mul, norm_zero]
    by_cases hz : z ∈ Set.Icc (fun _ : Fin 3 => (-1 : ℝ)) fun _ => 1
    · rw [Set.indicator_of_mem hz]
      have := hg z fun i => abs_le.mpr ⟨hz.1 i, hz.2 i⟩
      have := sixTheta_norm_le hK z
      have : 0 ≤ c := (norm_nonneg _).trans (hg z fun i => abs_le.mpr ⟨hz.1 i, hz.2 i⟩)
      positivity
    · rw [Set.indicator_of_notMem hz]
  · rw [Set.indicator_of_mem (sixTheta_mem_box hs h), norm_mul]
    exact mul_le_mul (sixTheta_norm_le hK z) (hg z (sixTheta_support hs h)) (norm_nonneg _)
      (sq_nonneg _)

/-- The quadratic phase on the box is bounded by the entries. -/
theorem quadForm_box_le {N : Matrix (Fin 3) (Fin 3) ℝ} {α : ℝ} (hN : ∀ i j, |N i j| ≤ α)
    {z : Fin 3 → ℝ} (hz : ∀ i, |z i| ≤ 1) : |z ⬝ᵥ N.mulVec z| ≤ 9 * α := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  calc |∑ i, ∑ j, z i * (N i j * z j)| ≤ ∑ i : Fin 3, ∑ j : Fin 3, α := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_))
        rw [abs_mul, abs_mul]
        have h1 := hz i; have h2 := hz j; have h3 := hN i j
        have : 0 ≤ |N i j| := abs_nonneg _
        calc |z i| * (|N i j| * |z j|) ≤ 1 * (|N i j| * 1) := by gcongr
          _ ≤ α := by linarith
    _ = 9 * α := by simp; ring

/-- The `τ`-integral of a kernel slice against a tiny or a large frequency. -/
theorem slice_fourier_le {W : ℝ × ℝ → ℂ} {K L : ℝ} (hW : Continuous W) (hK : ∀ p, ‖W p‖ ≤ K)
    (hL : ∀ p q, ‖W p - W q‖ ≤ L * ‖p - q‖) (hs : ∀ p, W p ≠ 0 → |p.1| ≤ 1 ∧ |p.2| ≤ 1)
    (hm : ∀ u, ∫ τ, W (u, τ) = 0) (hL0 : 0 ≤ L) {ν α₁ β₁ : ℝ} (hα₁ : 0 ≤ α₁) (hβ₁ : 1 ≤ β₁)
    (hν : |ν| ≤ α₁ ∨ β₁ ≤ |ν|) (u : ℝ) :
    ‖∫ τ, W (u, τ) * (Real.fourierChar (ν * τ) : ℂ)‖ ≤
      4 * Real.pi * K * α₁ + 2 * L / β₁ := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hc : Continuous fun τ => W (u, τ) := hW.comp (continuous_const.prodMk continuous_id)
  have hsu : ∀ τ, 1 < |τ| → W (u, τ) = 0 := fun τ hτ => by
    by_contra h; have := (hs _ h).2; linarith
  rcases hν with hν | hν
  · have h := zero_mean_fourier_small zero_le_one hc (fun τ => hK _) hsu (hm u) ν
    have h2 : 2 * Real.pi * K * |ν| * 1 * (2 * 1) ≤ 4 * Real.pi * K * α₁ := by
      have := mul_le_mul_of_nonneg_left hν (by positivity : (0 : ℝ) ≤ 4 * Real.pi * K)
      nlinarith
    have : 0 ≤ 2 * L / β₁ := by positivity
    linarith
  · have hLip : ∀ x y, ‖W (u, x) - W (u, y)‖ ≤ L * |x - y| := fun x y => by
      have := hL (u, x) (u, y)
      rwa [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero, Real.norm_eq_abs,
        max_eq_right (abs_nonneg _)] at this
    have h := lipschitz_fourier_decay zero_le_one hc hLip hsu (hβ₁.trans hν)
    have h2 : L * (1 + 1) / |ν| ≤ 2 * L / β₁ := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have : 0 ≤ 4 * Real.pi * K * α₁ := by positivity
    linarith

open scoped Classical in
/-- Blueprint prop:base, proof line 1651: the doubled-kernel integral of an expanded chart.
At a scale where every effective quadratic entry is tiny and every retained `τ`-frequency is
tiny or large, the integral is bounded by the tiny/large errors and the truncation tail. -/
theorem sixTheta_expansion_bound {W : ℝ × ℝ → ℂ} {K L : ℝ} (hW : Continuous W)
    (hK : ∀ p, ‖W p‖ ≤ K) (hL : ∀ p q, ‖W p - W q‖ ≤ L * ‖p - q‖)
    (hs : ∀ p, W p ≠ 0 → |p.1| ≤ 1 ∧ |p.2| ≤ 1) (hm : ∀ u, ∫ τ, W (u, τ) = 0) (hL0 : 0 ≤ L)
    {τt : Type*} (Φ : (Fin 3 → ℝ) → ℂ) (N : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ) {d : ℕ}
    (V : Matrix (Fin d) (Fin 3) ℝ) (σ : τt → Fin d → ℝ) (a : τt → ℂ)
    (hsum : Summable fun p => ‖a p‖)
    (hexp : ∀ z : Fin 3 → ℝ, (∀ i, |z i| ≤ 1) →
      HasSum (fun p => a p * (Real.fourierChar (σ p ⬝ᵥ V.mulVec z) : ℂ))
        ((Real.fourierChar (-(z ⬝ᵥ N.mulVec z + b ⬝ᵥ z)) : ℂ) * Φ z))
    {α α₁ β₁ : ℝ} (hα : ∀ i j, |N i j| ≤ α) (hα₁ : 0 ≤ α₁) (hβ₁ : 1 ≤ β₁) (F : Finset τt)
    (hF : ∀ p ∈ F, |b 1 + ∑ i, σ p i * V i 1| ≤ α₁ ∨ β₁ ≤ |b 1 + ∑ i, σ p i * V i 1|) :
    ‖∫ z, sixTheta W z * Φ z‖ ≤
      (∑ p ∈ F, ‖a p‖) * (4 * K * (4 * Real.pi * K * α₁ + 2 * L / β₁) +
        8 * (K ^ 2 * (2 * Real.pi * (9 * α)))) +
      8 * (K ^ 2 * ∑' p, if p ∈ F then 0 else ‖a p‖) := by
  classical
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  set tailF := ∑' p, if p ∈ F then 0 else ‖a p‖ with htailF
  have htail0 : 0 ≤ tailF := tsum_nonneg fun p => by split_ifs <;> positivity
  set! ν : τt → Fin 3 → ℝ := fun p i => b i + ∑ j, σ p j * V j i with hνdef
  have hν : ∀ p z, ν p ⬝ᵥ z = b ⬝ᵥ z + σ p ⬝ᵥ V.mulVec z := by
    intro p z
    simp only [hνdef, dotProduct, Matrix.mulVec, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  set! e2 : (Fin 3 → ℝ) → ℂ := fun z => (Real.fourierChar (z ⬝ᵥ N.mulVec z) : ℂ) with he2
  set! ph : τt → (Fin 3 → ℝ) → ℂ := fun p z => (Real.fourierChar (ν p ⬝ᵥ z) : ℂ) with hph
  -- pointwise remainder
  have hpt : ∀ z : Fin 3 → ℝ, (∀ i, |z i| ≤ 1) →
      ‖Φ z - ∑ p ∈ F, a p * (e2 z * ph p z)‖ ≤ tailF := by
    intro z hz
    set! X := z ⬝ᵥ N.mulVec z + b ⬝ᵥ z with hX
    set! f : τt → ℂ := fun p => a p * (Real.fourierChar (σ p ⬝ᵥ V.mulVec z) : ℂ) with hf
    have hS := hexp z hz
    have hF' : HasSum (fun p => if p ∈ F then f p else 0) (∑ p ∈ F, f p) := by
      have h0 : HasSum (fun p => if p ∈ F then f p else 0)
          (∑ p ∈ F, if p ∈ F then f p else 0) :=
        hasSum_sum_of_ne_finset_zero (fun p hp => by simp [hp])
      convert h0 using 1
      exact Finset.sum_congr rfl fun p hp => by simp [hp]
    have hdiff := hS.sub hF'
    have hfn : ∀ p, ‖f p - (if p ∈ F then f p else 0)‖ = if p ∈ F then 0 else ‖a p‖ := by
      intro p
      split_ifs with hp
      · simp
      · rw [sub_zero, hf, norm_mul, Circle.norm_coe, mul_one]
    have hsn : Summable fun p => ‖f p - (if p ∈ F then f p else 0)‖ := by
      simp only [hfn]
      exact Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity)
        (fun p => by split_ifs <;> simp) hsum
    have hnorm : ‖(Real.fourierChar (-X) : ℂ) * Φ z - ∑ p ∈ F, f p‖ ≤ tailF := by
      rw [← hdiff.tsum_eq]
      refine (norm_tsum_le_tsum_norm hsn).trans (le_of_eq ?_)
      simp only [hfn, htailF]
    have he : Φ z - ∑ p ∈ F, a p * (e2 z * ph p z) =
        (Real.fourierChar X : ℂ) * ((Real.fourierChar (-X) : ℂ) * Φ z - ∑ p ∈ F, f p) := by
      rw [mul_sub, ← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_neg_cancel,
        AddChar.map_zero_eq_one, Circle.coe_one, one_mul, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [hf, he2, hph, hν, hX]
      rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, Circle.coe_mul, Circle.coe_mul]
      ring
    rw [he, norm_mul, Circle.norm_coe, one_mul]
    exact hnorm
  -- each retained term
  have hterm : ∀ p ∈ F, ‖∫ z, sixTheta W z * (e2 z * ph p z)‖ ≤
      4 * K * (4 * Real.pi * K * α₁ + 2 * L / β₁) + 8 * (K ^ 2 * (2 * Real.pi * (9 * α))) := by
    intro p hp
    have hcont1 : Continuous fun z => sixTheta W z * ph p z :=
      (sixTheta_continuous hW).mul (continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp (continuous_const.dotProduct continuous_id)))
    have hcont2 : Continuous fun z => sixTheta W z * ((e2 z - 1) * ph p z) := by
      refine (sixTheta_continuous hW).mul ((Continuous.sub ?_ continuous_const).mul
        (continuous_subtype_val.comp
          (Real.continuous_fourierChar.comp (continuous_const.dotProduct continuous_id))))
      exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (continuous_id.dotProduct ((continuous_const.matrix_mulVec continuous_id))))
    have hcs := sixTheta_hasCompactSupport hs
    have hi1 : Integrable fun z => sixTheta W z * ph p z :=
      hcont1.integrable_of_hasCompactSupport hcs.mul_right
    have hi2 : Integrable fun z => sixTheta W z * ((e2 z - 1) * ph p z) :=
      hcont2.integrable_of_hasCompactSupport hcs.mul_right
    have hsplit : (∫ z, sixTheta W z * (e2 z * ph p z)) =
        (∫ z, sixTheta W z * ph p z) + ∫ z, sixTheta W z * ((e2 z - 1) * ph p z) := by
      rw [← integral_add hi1 hi2]; congr 1; funext z; ring
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · have hS := slice_fourier_le hW hK hL hs hm hL0 hα₁ hβ₁ (hF p hp)
      have h := sixTheta_fourier_bound zero_le_one hW hK
        (fun q hq => hs q hq) (ν p) (S := 4 * Real.pi * K * α₁ + 2 * L / β₁) (fun u => hS u)
      calc _ ≤ 2 * 1 * ((4 * Real.pi * K * α₁ + 2 * L / β₁) * (2 * 1 * K)) := h
        _ = _ := by ring
    · refine integral_box_three_le fun z =>
        sixTheta_mul_norm_le (g := fun z => (e2 z - 1) * ph p z) hK hs (fun z hz => ?_) z
      rw [norm_mul, hph, Circle.norm_coe, mul_one, he2]
      refine (chart_fourierChar_sub_one_norm_le _).trans ?_
      have := quadForm_box_le hα hz
      have : 0 ≤ 2 * Real.pi := by positivity
      nlinarith
  -- assemble
  by_cases hint : Integrable fun z => sixTheta W z * Φ z
  · have hcs := sixTheta_hasCompactSupport hs
    have hiF : ∀ p ∈ F, Integrable fun z => sixTheta W z * (a p * (e2 z * ph p z)) := by
      intro p _
      refine Continuous.integrable_of_hasCompactSupport ?_ hcs.mul_right
      refine (sixTheta_continuous hW).mul (continuous_const.mul ((continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp (continuous_id.dotProduct
          (continuous_const.matrix_mulVec continuous_id)))).mul
        (continuous_subtype_val.comp
          (Real.continuous_fourierChar.comp (continuous_const.dotProduct continuous_id)))))
    have hsumI : Integrable fun z => ∑ p ∈ F, sixTheta W z * (a p * (e2 z * ph p z)) :=
      integrable_finsetSum F hiF
    have hdec : (∫ z, sixTheta W z * Φ z) =
        (∑ p ∈ F, a p * ∫ z, sixTheta W z * (e2 z * ph p z)) +
          ∫ z, sixTheta W z * (Φ z - ∑ p ∈ F, a p * (e2 z * ph p z)) := by
      have h1 : (∫ z, sixTheta W z * (Φ z - ∑ p ∈ F, a p * (e2 z * ph p z))) =
          (∫ z, sixTheta W z * Φ z) -
            ∫ z, ∑ p ∈ F, sixTheta W z * (a p * (e2 z * ph p z)) := by
        rw [← integral_sub hint hsumI]; congr 1; funext z; rw [mul_sub, Finset.mul_sum]
      rw [h1, integral_finsetSum F hiF]
      have h2 : ∀ p ∈ F, (∫ z, sixTheta W z * (a p * (e2 z * ph p z))) =
          a p * ∫ z, sixTheta W z * (e2 z * ph p z) := fun p _ => by
        rw [← integral_const_mul]; congr 1; funext z; ring
      rw [Finset.sum_congr rfl h2]; ring
    rw [hdec]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun p hp => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hterm p hp) (norm_nonneg _)
    · exact integral_box_three_le fun z => sixTheta_mul_norm_le hK hs (fun z hz => hpt z hz) z
  · rw [integral_undef hint, norm_zero]
    have h0 : 0 ≤ 4 * K * (4 * Real.pi * K * α₁ + 2 * L / β₁) +
        8 * (K ^ 2 * (2 * Real.pi * (9 * α))) := by
      have := (hterm)
      by_cases hFe : F.Nonempty
      · obtain ⟨p, hp⟩ := hFe
        exact (norm_nonneg _).trans (hterm p hp)
      · have : (0 : ℝ) ≤ |N 0 0| := abs_nonneg _
        have := hα 0 0
        have : 0 ≤ α := by linarith
        have : 0 ≤ 2 * L / β₁ := by positivity
        positivity
    have : 0 ≤ ∑ p ∈ F, ‖a p‖ := Finset.sum_nonneg fun p _ => norm_nonneg _
    exact add_nonneg (mul_nonneg this h0) (mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg K)
        htail0))

theorem fourier_euclidean_zero {k : ℕ} (g : (Fin k → ℝ) → ℂ) :
    𝓕 (fun z : EuclideanSpace ℝ (Fin k) => g z.ofLp) 0 = ∫ z, g z := by
  rw [Real.fourier_eq]
  have hp : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin k) => x.ofLp) := by
    convert! PiLp.volume_preserving_ofLp (Fin k)
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
  convert! hp.integral_comp (MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm.measurableEmbedding g

theorem mvDilateChart_effQuad {k d : ℕ} (r : ℝ) (A : MultivariableQuadraticChartData k d)
    (M : Matrix (Fin d) (Fin d) ℚ) (i j : Fin k) :
    mvEffQuad (mvDilateChart r A) M i j = r ^ 2 * mvEffQuad A M i j := by
  have h : ∀ a b, (M a b : ℝ) * (A.horizontal a i * r * (A.horizontal b j * r) +
      A.horizontal a j * r * (A.horizontal b i * r)) =
      r ^ 2 * ((M a b : ℝ) * (A.horizontal a i * A.horizontal b j +
        A.horizontal a j * A.horizontal b i)) := fun a b => by ring
  simp only [mvEffQuad, mvDilateChart, Matrix.of_apply, h, ← Finset.mul_sum]
  ring

/-- The fixed real parameters of an effective quadratic entry. -/
noncomputable def effQuadVector {k d : ℕ} (A : MultivariableQuadraticChartData k d)
    (i j : Fin k) : Fin (d * d + 1) → ℝ :=
  Fin.cons (A.quadratic i j) fun x => (1 / 2 : ℝ) *
    (A.horizontal (finProdFinEquiv.symm x).1 i * A.horizontal (finProdFinEquiv.symm x).2 j +
      A.horizontal (finProdFinEquiv.symm x).1 j * A.horizontal (finProdFinEquiv.symm x).2 i)

theorem effQuad_eval {k d : ℕ} (A : MultivariableQuadraticChartData k d)
    (M : Matrix (Fin d) (Fin d) ℚ) (i j : Fin k) :
    ∑ l, ((Fin.cons (1 : ℚ) (fun x => M (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2) :
      Fin (d * d + 1) → ℚ) l : ℝ) * effQuadVector A i j l = mvEffQuad A M i j := by
  rw [Fin.sum_univ_succ, Fin.cons_zero]
  have h0 : effQuadVector A i j 0 = A.quadratic i j := by
    unfold effQuadVector; rw [Fin.cons_zero]
  have hs : ∀ x : Fin (d * d), ((Fin.cons (1 : ℚ) (fun x => M (finProdFinEquiv.symm x).1
      (finProdFinEquiv.symm x).2) : Fin (d * d + 1) → ℚ) x.succ : ℝ) *
        effQuadVector A i j x.succ =
      (fun p : Fin d × Fin d => (1 / 2 : ℝ) * ((M p.1 p.2 : ℝ) *
        (A.horizontal p.1 i * A.horizontal p.2 j + A.horizontal p.1 j * A.horizontal p.2 i)))
        (finProdFinEquiv.symm x) := by
    intro x
    unfold effQuadVector
    rw [Fin.cons_succ, Fin.cons_succ]; ring
  rw [h0, Rat.cast_one, one_mul, Finset.sum_congr rfl (fun x _ => hs x),
    Equiv.sum_comp finProdFinEquiv.symm (fun p : Fin d × Fin d => (1 / 2 : ℝ) *
      ((M p.1 p.2 : ℝ) * (A.horizontal p.1 i * A.horizontal p.2 j +
        A.horizontal p.1 j * A.horizontal p.2 i))), Fintype.sum_prod_type]
  simp only [mvEffQuad, Matrix.of_apply, Finset.mul_sum]

/-- The fixed real parameters of a `τ`-frequency. -/
noncomputable def freqVector {k d : ℕ} (A : MultivariableQuadraticChartData k d) (j : Fin k) :
    Fin (d + 1) → ℝ :=
  Fin.cons (A.linear j) fun i => A.horizontal i j

theorem freq_eval {k d : ℕ} (r : ℝ) (A : MultivariableQuadraticChartData k d) (j : Fin k)
    (σ : Fin d → ℚ) :
    (mvDilateChart r A).linear j + ∑ i, (σ i : ℝ) * (mvDilateChart r A).horizontal i j =
      r * ∑ l, ((Fin.cons (1 : ℚ) σ : Fin (d + 1) → ℚ) l : ℝ) * freqVector A j l := by
  rw [Fin.sum_univ_succ]
  simp only [freqVector, Fin.cons_zero, Fin.cons_succ, mvDilateChart, Rat.cast_one, one_mul,
    mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _ => by ring

theorem cons_one_height {d : ℕ} {σ : Fin d → ℚ} {B : ℝ} (hB : 1 ≤ B)
    (hσ : ∀ i, (rationalHeight (σ i) : ℝ) ≤ B) (l : Fin (d + 1)) :
    (rationalHeight ((Fin.cons (1 : ℚ) σ : Fin (d + 1) → ℚ) l) : ℝ) ≤ B := by
  refine Fin.cases ?_ (fun x => ?_) l
  · rw [Fin.cons_zero, show rationalHeight (1 : ℚ) = 1 by decide]; push_cast; exact hB
  · rw [Fin.cons_succ]; exact hσ x

theorem sixTheta_lipschitz {W : ℝ × ℝ → ℂ} {K : ℝ} (hK : ∀ p, ‖W p‖ ≤ K)
    (hL : ∀ p q, ‖W p - W q‖ ≤ K * ‖p - q‖) (x y : Fin 3 → ℝ) :
    ‖sixTheta W y - sixTheta W x‖ ≤ 2 * K ^ 2 * ‖y - x‖ := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hpair : ∀ i : Fin 3, ‖(y 0, y i) - (x 0, x i)‖ ≤ ‖y - x‖ := fun i => by
    rw [Prod.mk_sub_mk, Prod.norm_def, max_le_iff]
    exact ⟨by simpa using norm_le_pi_norm (y - x) 0, by simpa using norm_le_pi_norm (y - x) i⟩
  have he : sixTheta W y - sixTheta W x = (W (y 0, y 1) - W (x 0, x 1)) * conj (W (y 0, y 2)) +
      W (x 0, x 1) * conj (W (y 0, y 2) - W (x 0, x 2)) := by
    simp only [sixTheta, map_sub]; ring
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
  have h1 := (hL (y 0, y 1) (x 0, x 1)).trans (mul_le_mul_of_nonneg_left (hpair 1) hK0)
  have h2 := (hL (y 0, y 2) (x 0, x 2)).trans (mul_le_mul_of_nonneg_left (hpair 2) hK0)
  have h3 := hK (y 0, y 2)
  have h4 := hK (x 0, x 1)
  calc _ ≤ K * ‖y - x‖ * K + K * (K * ‖y - x‖) :=
        add_le_add (mul_le_mul h1 h3 (norm_nonneg _) (by positivity))
          (mul_le_mul h4 h2 (norm_nonneg _) hK0)
    _ = 2 * K ^ 2 * ‖y - x‖ := by ring

/-- Blueprint prop:base, proof lines 1647-1651, with explicit thresholds: the number of
scales at which the doubled-kernel integral of a fixed three-variable chart exceeds `ε`
is at most the number of intermediate scales of the effective quadratic entries and of the
retained `τ`-frequencies (lem:height). -/
theorem sixTheta_count_thresholds (c₀ : ℕ) (hc : 1 ≤ c₀) :
    ∃ D : ℕ, 1 ≤ D ∧ ∃ DJ : ℕ → ℕ, ∀ {d : ℕ} (H K ε r₀ : ℝ)
      (A : MultivariableQuadraticChartData 3 d), MultivariableQuadraticChartComplexity c₀ H A →
      1 ≤ K → 0 < ε → 0 < r₀ →
      ∀ (T : Finset ℤ) (W : ℤ → ℝ × ℝ → ℂ), (∀ n, Continuous (W n)) →
      (∀ n p, ‖W n p‖ ≤ K) → (∀ n p q, ‖W n p - W n q‖ ≤ K * ‖p - q‖) →
      (∀ n p, W n p ≠ 0 → |p.1| ≤ 1 ∧ |p.2| ≤ 1) → (∀ n u, ∫ τ, W n (u, τ) = 0) →
      (∀ n ∈ T, ε < ‖∫ z, sixTheta (W n) z *
        multivariableQuadraticChartAtom A ((r₀ * (2 : ℝ) ^ (-n)) • z)‖) →
      ∀ (α α₁ β₁ : ℝ) (K₀ : ℕ),
      let X := 1 + Real.log (2 * H * K ^ 2) + Real.log (max 1 ε⁻¹)
      let E := Real.exp (D * X ^ D)
      let E₁ := Real.exp (DJ 1 * X ^ DJ 1)
      0 < α → α ≤ E → 0 < α₁ → α₁ ≤ β₁ → 1 ≤ β₁ →
      E * (4 * K * (4 * Real.pi * K * α₁ + 2 * K / β₁) + 8 * (K ^ 2 * (2 * Real.pi * (9 * α)))) +
        8 * (K ^ 2 * (E * (E₁ * (2 * 7 ^ (d + d) * (2 * Real.pi) ^ ((d + 1) ^ 2) / 2 ^ K₀))))
        ≤ ε →
      (T.card : ℝ) ≤ 9 * (32 * (((d * d + 1 : ℕ) : ℝ) + 1) ^ 4 *
          (Real.log (2 * E) + Real.log (2 * E / α))) +
        32 * (((d + 1 : ℕ) : ℝ) + 1) ^ 4 *
          (Real.log (2 * (E * (1 + 2 ^ K₀))) + Real.log (2 * β₁ / α₁)) := by
  obtain ⟨D, hD, DJ, hsep⟩ := mvSeparatedPhase c₀ hc 3 (by norm_num) le_rfl 1 zero_le_one
  refine ⟨D, hD, DJ, ?_⟩
  intro d H K ε r₀ A hA hK1 hε hr₀ T W hWc hWb hWL hWs hWm hT α α₁ β₁ K₀ X E E₁ hα hαE hα₁ hαβ hβ₁
    herr
  classical
  have hH1 : 1 ≤ H := by linarith [hA.lower, Real.add_one_le_exp (2 : ℝ)]
  have hK0 : 0 ≤ K := by linarith
  set! H' := 2 * H * K ^ 2 with hH'
  have hK2 : (1 : ℝ) ≤ K ^ 2 := one_le_pow₀ hK1
  have hHH' : H ≤ H' := by rw [hH']; nlinarith only [hH1, hK2]
  have hA' : MultivariableQuadraticChartComplexity c₀ H' A :=
    quadraticChartComplexity_mono hA hHH'
  have hX1 : 1 ≤ X := by
    have : 0 ≤ Real.log H' := Real.log_nonneg (by rw [hH']; nlinarith only [hK1, hH1])
    have : 0 ≤ Real.log (max 1 ε⁻¹) := Real.log_nonneg (le_max_left _ _)
    simp only [X]; linarith
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hE2 : 2 ≤ E := by
    have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have : 1 ≤ (D : ℝ) * X ^ D := by nlinarith only [one_le_pow₀ (n := D) hX1, hD1]
    have := Real.add_one_le_exp (1 : ℝ)
    have : Real.exp 1 ≤ E := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hE₁0 : 0 ≤ E₁ := (Real.exp_pos _).le
  -- the exceptional sets
  have hq := fun ij : Fin 3 × Fin 3 => rational_frequency_scale_count (d := d * d + 1) (u := 2)
    hE2 (by norm_num) hα hαE (effQuadVector A ij.1 ij.2) r₀
  choose X1 hX1 hX1c using hq
  have hB₂ : 2 ≤ E * (1 + 2 ^ K₀) := by
    have : (1 : ℝ) ≤ 2 ^ K₀ := one_le_pow₀ (by norm_num)
    nlinarith only [hE1, this]
  obtain ⟨X2, hX2, hX2c⟩ := rational_frequency_scale_count (d := d + 1) (u := 1) hB₂ le_rfl hα₁
    hαβ (freqVector A 1) r₀
  have hsub : T ⊆ (Finset.univ.biUnion X1) ∪ X2 := by
    intro n hn
    by_contra hnX
    have hn1 : ∀ ij, n ∉ X1 ij := fun ij h =>
      hnX (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨ij, Finset.mem_univ _, h⟩))
    have hn2 : n ∉ X2 := fun h => hnX (Finset.mem_union_right _ h)
    set! r := r₀ * (2 : ℝ) ^ (-n) with hr
    set! A' := mvDilateChart r A with hA'def
    have hA'c : MultivariableQuadraticChartComplexity c₀ H' A' :=
      mvDilateChart_complexity hA' r
    have hθb : ∀ z, ‖sixTheta (W n) z‖ ≤ H' := fun z =>
      (sixTheta_norm_le (hWb n) z).trans (by nlinarith only [hH1])
    have hθL : ∀ x y, ‖sixTheta (W n) y - sixTheta (W n) x‖ ≤ H' * ‖y - x‖ := fun x y =>
      (sixTheta_lipschitz (hWb n) (hWL n) x y).trans
        (mul_le_mul_of_nonneg_right (by nlinarith only [hH1]) (norm_nonneg _))
    have hF : ∀ t < ε, ∃ ξ : EuclideanSpace ℝ (Fin 3), t < ‖𝓕 (fun z : EuclideanSpace ℝ (Fin 3) =>
        sixTheta (W n) z.ofLp * multivariableQuadraticChartAtom A' z.ofLp) ξ‖ := by
      intro t ht
      refine ⟨0, ?_⟩
      rw [fourier_euclidean_zero (fun z => sixTheta (W n) z * multivariableQuadraticChartAtom A' z)]
      simp only [hA'def, mvDilateChart_atom]
      exact ht.trans (hT n hn)
    obtain ⟨M, hMh, hMb, ι, hι, σ, hcard, hσ, a, hexp, hsumm, htot, hJ⟩ :=
      hsep H' ε A' hA'c (sixTheta (W n)) (sixTheta_continuous (hWc n)).measurable hθb hθL
        (fun z hz => sixTheta_support (hWs n) hz) hε hF
    -- tiny quadratic entries
    have htiny : ∀ i j, |mvEffQuad A' M i j| ≤ α := by
      intro i j
      have hev := effQuad_eval A M i j
      have hmem := (hX1 (i, j) n).not.mp (hn1 (i, j))
      push Not at hmem
      have h := hmem _ (quadraticParam_height M hE1 hMh)
      rw [hev] at h
      have hb := hMb i j
      rw [hA'def, mvDilateChart_effQuad, abs_mul, abs_of_nonneg (sq_nonneg r)] at hb ⊢
      by_contra hlt
      push Not at hlt
      exact absurd (h hlt.le) (not_lt.mpr hb)
    -- frequencies: tiny or large on the truncation
    set! F : Finset (ι × (Fin (d + d) → ℤ)) := Finset.univ ×ˢ frequencyTruncationSet (d + d) K₀
      with hFdef
    have hfreq : ∀ p ∈ F, |A'.linear 1 + ∑ i, (σ p i : ℝ) * A'.horizontal i 1| ≤ α₁ ∨
        β₁ ≤ |A'.linear 1 + ∑ i, (σ p i : ℝ) * A'.horizontal i 1| := by
      intro p hp
      have hpℓ : p.2 ∈ frequencyTruncationSet (d + d) K₀ := (Finset.mem_product.mp hp).2
      have hlen : frequencyLength p.2 ≤ 2 ^ K₀ := by
        rcases mem_frequencyTruncationSet.mp hpℓ with h0 | h0
        · rw [h0]; simp [frequencyLength]
        · linarith
      have hσB : ∀ i, (rationalHeight (σ p i) : ℝ) ≤ E * (1 + 2 ^ K₀) := fun i =>
        (hσ p i).trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
      have hmem := (hX2 n).not.mp hn2
      push Not at hmem
      have h := hmem _ (cons_one_height (by linarith) hσB)
      rw [hA'def, freq_eval, abs_mul, abs_of_pos (by rw [hr]; positivity : (0 : ℝ) < r)]
      by_cases h1 : α₁ ≤ r * |∑ l, ((Fin.cons (1 : ℚ) (σ p) : Fin (d + 1) → ℚ) l : ℝ) *
          freqVector A 1 l|
      · right
        have h2 := h (by rw [pow_one]; exact h1)
        rw [pow_one] at h2
        exact h2.le
      · left; push Not at h1; exact h1.le
    -- the bound at this scale
    have hbound := sixTheta_expansion_bound (hWc n) (hWb n) (hWL n) (hWs n) (hWm n) hK0
      (multivariableQuadraticChartAtom A') (mvEffQuad A' M) A'.linear A'.horizontal
      (fun p i => (σ p i : ℝ)) a hsumm hexp htiny hα₁.le hβ₁ F hfreq
    have hsumF : ∑ p ∈ F, ‖a p‖ ≤ E := (hsumm.sum_le_tsum F (fun p _ => norm_nonneg _)).trans htot
    have htail : (∑' p, if p ∈ F then 0 else ‖a p‖) ≤
        E * (E₁ * (2 * 7 ^ (d + d) * (2 * Real.pi) ^ ((d + 1) ^ 2) / 2 ^ K₀)) := by
      have hmemF : ∀ p, p ∈ F ↔ p.2 ∈ frequencyTruncationSet (d + d) K₀ := fun p => by
        simp [hFdef]
      simp only [hmemF]
      rcases Nat.eq_zero_or_pos d with hd | hd
      · subst hd
        have : ∀ p : ι × (Fin (0 + 0) → ℤ), p.2 ∈ frequencyTruncationSet (0 + 0) K₀ := fun p =>
          mem_frequencyTruncationSet.mpr (Or.inl (funext fun i => absurd i.2 (by omega)))
        simp only [this, ↓reduceIte, tsum_zero]
        positivity
      · have h := fintype_prod_tail (D := d + d) (k := (d + 1) ^ 2) (by omega) (by nlinarith only) a
          hE₁0 (fun p => by simpa only [one_mul] using (hJ 1).1 p) K₀
        refine h.trans ?_
        have : (Fintype.card ι : ℝ) ≤ E := hcard
        gcongr
    have hc1 : 0 ≤ 4 * K * (4 * Real.pi * K * α₁ + 2 * K / β₁) +
        8 * (K ^ 2 * (2 * Real.pi * (9 * α))) := by positivity
    have : ‖∫ z, sixTheta (W n) z * multivariableQuadraticChartAtom A' z‖ ≤ ε := by
      refine hbound.trans (le_trans (add_le_add (mul_le_mul_of_nonneg_right hsumF hc1)
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by convert htail) (sq_nonneg K))
          (by norm_num))) herr)
    have hT' := hT n hn
    simp only [hA'def, mvDilateChart_atom] at this
    linarith
  -- counting
  have hc1 : (T.card : ℝ) ≤ ((Finset.univ.biUnion X1) ∪ X2).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hc2 : (((Finset.univ.biUnion X1) ∪ X2).card : ℝ) ≤
      ∑ ij : Fin 3 × Fin 3, ((X1 ij).card : ℝ) + X2.card := by
    have h1 := Finset.card_union_le (Finset.univ.biUnion X1) X2
    have h2 := Finset.card_biUnion_le (s := Finset.univ) (t := X1)
    have h1' : (((Finset.univ.biUnion X1) ∪ X2).card : ℝ) ≤
        ((Finset.univ.biUnion X1).card : ℝ) + X2.card := by exact_mod_cast h1
    have h2' : ((Finset.univ.biUnion X1).card : ℝ) ≤ ∑ ij : Fin 3 × Fin 3, ((X1 ij).card : ℝ) := by
      exact_mod_cast h2
    linarith
  refine hc1.trans (hc2.trans (add_le_add ?_ ?_))
  · calc ∑ ij : Fin 3 × Fin 3, ((X1 ij).card : ℝ) ≤ ∑ _ij : Fin 3 × Fin 3,
          32 * (((d * d + 1 : ℕ) : ℝ) + 1) ^ 4 * (Real.log (2 * E) + Real.log (2 * E / α)) :=
          Finset.sum_le_sum fun ij _ => hX1c ij
      _ = _ := by simp
  · simpa using hX2c

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith

theorem exp_two_ge_seven : (7.38 : ℝ) ≤ Real.exp 2 := by
  have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have h := Real.exp_one_gt_d9
  have : (2.7182818283 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := by gcongr
  rw [e]; norm_num at this ⊢; linarith

theorem log_seven_le_two : Real.log 7 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]; linarith [exp_two_ge_seven]

theorem log_two_pi_le_two : Real.log (2 * Real.pi) ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by positivity)]; linarith [exp_two_ge_seven, Real.pi_lt_d2]

theorem le_exp_seven : (1008 : ℝ) ≤ Real.exp 7 := by
  have e7 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
  have h := Real.exp_one_gt_d9
  have : (2.7 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := by gcongr; linarith
  rw [e7]; norm_num at this ⊢; linarith

theorem log_lattice_const_le {d : ℕ} {Z : ℝ} (hZ1 : 1 ≤ Z) (hdZ : (d : ℝ) ≤ Z) :
    Real.log (2 * 7 ^ (d + d) * (2 * Real.pi) ^ ((d + 1) ^ 2)) ≤ 13 * Z ^ 2 := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_pow, Real.log_pow]
  have h2 := log_two_le_one
  have h7 := log_seven_le_two
  have hπ := log_two_pi_le_two
  have h70 : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
  have hπ0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  push_cast
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have a1 : ((d : ℝ) + d) * Real.log 7 ≤ (Z + Z) * 2 := mul_le_mul (by linarith) h7 h70 (by
      linarith)
  have a2 : ((d : ℝ) + 1) ^ 2 * Real.log (2 * Real.pi) ≤ 2 * Z ^ 2 + 4 * Z + 2 := by
    calc _ ≤ (Z + 1) ^ 2 * 2 := mul_le_mul (by gcongr) hπ hπ0 (by positivity)
      _ = _ := by ring
  have hZZ : Z ≤ Z ^ 2 := by rw [sq]; exact le_mul_of_one_le_left (by linarith) hZ1
  have hZ1' : 1 ≤ Z ^ 2 := one_le_pow₀ hZ1
  linarith

/-- The threshold that dominates all errors of the scale estimate. -/
theorem count_threshold_big {K E E₁ G ε Z a : ℝ} {m : ℕ} (hK : 1 ≤ K) (hE : 1 ≤ E)
    (hE₁ : 1 ≤ E₁) (hG : 1 ≤ G) (hε : 0 < ε) (hZ1 : 1 ≤ Z) (hZm : Z ≤ Z ^ m)
    (hZ2m : Z ^ 2 ≤ Z ^ m) (hlK : Real.log K ≤ Z) (hlε : Real.log ε⁻¹ ≤ Z)
    (hlG : Real.log G ≤ 13 * Z ^ 2) (hlE : Real.log E ≤ a * Z ^ m)
    (hlE₁ : Real.log E₁ ≤ a * Z ^ m) :
    (1000 + 8 * G * E₁) * K ^ 2 * E / ε ≤ Real.exp ((2 * a + 23) * Z ^ m) := by
  have hK0 : 0 < K := by linarith
  have hE0 : 0 < E := by linarith
  have hGE : 1 ≤ G * E₁ := one_le_mul_of_one_le_of_one_le hG hE₁
  have hpos : 0 < (1000 + 8 * G * E₁) * K ^ 2 * E / ε := by
    have : 0 < 1000 + 8 * G * E₁ := by nlinarith only [hE₁, hG]
    positivity
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  have h1 : Real.log (1000 + 8 * G * E₁) ≤ 7 + Real.log G + Real.log E₁ := by
    have : 1000 + 8 * G * E₁ ≤ Real.exp 7 * (G * E₁) := by
      have := mul_le_mul_of_nonneg_right le_exp_seven (by linarith : (0 : ℝ) ≤ G * E₁)
      linarith
    calc Real.log (1000 + 8 * G * E₁) ≤ Real.log (Real.exp 7 * (G * E₁)) :=
          Real.log_le_log (by linarith) this
      _ = 7 + Real.log G + Real.log E₁ := by
          rw [Real.log_mul (by positivity) (by linarith), Real.log_exp,
            Real.log_mul (by linarith) (by linarith)]; ring
  have h1000 : (0 : ℝ) < 1000 + 8 * G * E₁ := by linarith
  rw [div_eq_mul_inv, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) hE0.ne', Real.log_mul h1000.ne' (by positivity),
    Real.log_pow]
  have hZm1 : 1 ≤ Z ^ m := hZ1.trans hZm
  have he : (2 * a + 23) * Z ^ m = 2 * (a * Z ^ m) + 23 * Z ^ m := by ring
  rw [he]
  push_cast
  linarith

/-- The thresholds `α = α₁ = e^{-Y}`, `β₁ = e^Y`, `2^{K₀} ≈ e^Y` make the errors at most `ε`. -/
theorem count_threshold_err {K E E₁ G ε Y : ℝ} (hK : 1 ≤ K) (hE : 1 ≤ E) (hE₁ : 1 ≤ E₁)
    (hG : 1 ≤ G) (hY : 0 < Y) (hbig : (1000 + 8 * G * E₁) * K ^ 2 * E / ε ≤ Real.exp Y)
    (hε : 0 < ε) :
    E * (4 * K * (4 * Real.pi * K * Real.exp (-Y) + 2 * K / Real.exp Y) +
      8 * (K ^ 2 * (2 * Real.pi * (9 * Real.exp (-Y))))) +
      8 * (K ^ 2 * (E * (E₁ * (G / 2 ^ ⌈Y / Real.log 2⌉₊)))) ≤ ε ∧
    Real.exp Y ≤ 2 ^ ⌈Y / Real.log 2⌉₊ ∧ (2 : ℝ) ^ ⌈Y / Real.log 2⌉₊ ≤ 2 * Real.exp Y := by
  set K₀ := ⌈Y / Real.log 2⌉₊ with hK₀
  set α := Real.exp (-Y) with hα
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2K : Real.exp Y ≤ 2 ^ K₀ := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
    apply Real.exp_le_exp.mpr
    have := Nat.le_ceil (Y / Real.log 2)
    rw [div_le_iff₀ hlog2] at this
    linarith
  have h2K' : (2 : ℝ) ^ K₀ ≤ 2 * Real.exp Y := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
    have hY0 : 0 ≤ Y / Real.log 2 := by positivity
    have := Nat.ceil_lt_add_one hY0
    rw [show (2 : ℝ) * Real.exp Y = Real.exp (Real.log 2 + Y) by
      rw [Real.exp_add, Real.exp_log (by norm_num)]]
    apply Real.exp_le_exp.mpr
    have h' : (K₀ : ℝ) * Real.log 2 ≤ (Y / Real.log 2 + 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_right this.le hlog2.le
    rw [add_mul, div_mul_cancel₀ _ hlog2.ne'] at h'
    linarith
  refine ⟨?_, h2K, h2K'⟩
  have hαpos : 0 < α := Real.exp_pos _
  have hαY : α * Real.exp Y = 1 := by rw [hα, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hinv : 1 / Real.exp Y = α := by rw [hα, Real.exp_neg, one_div]
  have hG2 : G / 2 ^ K₀ ≤ G * α := by
    rw [div_le_iff₀ (by positivity)]
    calc G = G * (α * Real.exp Y) := by rw [hαY, mul_one]
      _ ≤ G * (α * 2 ^ K₀) := by gcongr
      _ = G * α * 2 ^ K₀ := by ring
  have h2 : 2 * K / Real.exp Y = 2 * K * α := by rw [← hinv]; ring
  rw [h2]
  have hK0 : 0 < K := by linarith
  have hE0 : 0 < E := by linarith
  have h0 : 0 ≤ α * K ^ 2 * E := by positivity
  have hπ := Real.pi_lt_d2
  have hmain : E * (4 * K * (4 * Real.pi * K * α + 2 * K * α) +
      8 * (K ^ 2 * (2 * Real.pi * (9 * α)))) + 8 * (K ^ 2 * (E * (E₁ * (G * α)))) ≤
      α * ((1000 + 8 * G * E₁) * K ^ 2 * E) := by
    have e1 : E * (4 * K * (4 * Real.pi * K * α + 2 * K * α) +
        8 * (K ^ 2 * (2 * Real.pi * (9 * α)))) + 8 * (K ^ 2 * (E * (E₁ * (G * α)))) =
        (α * K ^ 2 * E) * (160 * Real.pi + 8) + 8 * ((α * K ^ 2 * E) * (G * E₁)) := by ring
    have e2 : α * ((1000 + 8 * G * E₁) * K ^ 2 * E) =
        (α * K ^ 2 * E) * 1000 + 8 * ((α * K ^ 2 * E) * (G * E₁)) := by ring
    rw [e1, e2]
    have : (α * K ^ 2 * E) * (160 * Real.pi + 8) ≤ (α * K ^ 2 * E) * 1000 :=
      mul_le_mul_of_nonneg_left (by linarith) h0
    linarith
  have hfin : α * ((1000 + 8 * G * E₁) * K ^ 2 * E) ≤ ε := by
    have := mul_le_mul_of_nonneg_left hbig hαpos.le
    rw [hαY, mul_div_assoc', div_le_one hε] at this
    exact this
  calc _ ≤ E * (4 * K * (4 * Real.pi * K * α + 2 * K * α) +
        8 * (K ^ 2 * (2 * Real.pi * (9 * α)))) + 8 * (K ^ 2 * (E * (E₁ * (G * α)))) := by
        gcongr
    _ ≤ _ := hmain.trans hfin

/-- The logarithmic count is polynomial. -/
theorem count_logs_le {d m : ℕ} {Z a E Y : ℝ} {K₀ : ℕ} (hZ2 : 2 ≤ Z) (hdZ : (d : ℝ) ≤ Z)
    (ha : 1 ≤ a) (hE : 1 ≤ E) (hlE : Real.log E ≤ a * Z ^ m)
    (hY : Y = (2 * a + 23) * Z ^ m) (h2K : (2 : ℝ) ^ K₀ ≤ 2 * Real.exp Y) :
    9 * (32 * (((d * d + 1 : ℕ) : ℝ) + 1) ^ 4 *
        (Real.log (2 * E) + Real.log (2 * E / Real.exp (-Y)))) +
      32 * (((d + 1 : ℕ) : ℝ) + 1) ^ 4 *
        (Real.log (2 * (E * (1 + 2 ^ K₀))) + Real.log (2 * Real.exp Y / Real.exp (-Y))) ≤
      (4608 * (4 * a + 25) + 512 * (7 * a + 73)) * Z ^ (m + 8) := by
  have hZ1 : 1 ≤ Z := by linarith
  have hZm1 : 1 ≤ Z ^ m := one_le_pow₀ hZ1
  have hE0 : 0 < E := by linarith
  have hYpos : 0 < Y := by rw [hY]; positivity
  have h2 := log_two_le_one
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlE0 : 0 ≤ Real.log E := Real.log_nonneg hE
  have hYe : Y = 2 * (a * Z ^ m) + 23 * Z ^ m := by rw [hY]; ring
  have hlogA : Real.log (2 * E) + Real.log (2 * E / Real.exp (-Y)) =
      2 * Real.log 2 + 2 * Real.log E + Y := by
    rw [Real.log_mul (by norm_num) hE0.ne', Real.log_div (by positivity) (Real.exp_pos _).ne',
      Real.log_mul (by norm_num) hE0.ne', Real.log_exp]; ring
  have hl1 : Real.log (2 * E) + Real.log (2 * E / Real.exp (-Y)) ≤ (4 * a + 25) * Z ^ m := by
    rw [hlogA]
    have he : (4 * a + 25) * Z ^ m = 4 * (a * Z ^ m) + 25 * Z ^ m := by ring
    rw [he]; linarith
  have hl1' : 0 ≤ Real.log (2 * E) + Real.log (2 * E / Real.exp (-Y)) := by
    rw [hlogA]; linarith
  have hEY : 1 + (2 : ℝ) ^ K₀ ≤ Real.exp 2 * Real.exp Y := by
    have h3 : 3 ≤ Real.exp 2 := by linarith [exp_two_ge_seven]
    have hY1 : 1 ≤ Real.exp Y := Real.one_le_exp hYpos.le
    have := mul_le_mul_of_nonneg_right h3 (by linarith : (0 : ℝ) ≤ Real.exp Y)
    linarith
  have hlog3 : Real.log (2 * (E * (1 + 2 ^ K₀))) ≤ Real.log 2 + Real.log E + 2 + Y := by
    calc Real.log (2 * (E * (1 + 2 ^ K₀))) ≤ Real.log (2 * (E * (Real.exp 2 * Real.exp Y))) :=
          Real.log_le_log (by positivity) (by gcongr)
      _ = Real.log 2 + Real.log E + 2 + Y := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul hE0.ne' (by positivity),
            Real.log_mul (by positivity) (by positivity)]
          simp only [Real.log_exp]; ring
  have hlog3' : 0 ≤ Real.log (2 * (E * (1 + 2 ^ K₀))) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ 2 ^ K₀ := one_le_pow₀ (by norm_num)
    have := one_le_mul_of_one_le_of_one_le hE (by linarith : (1 : ℝ) ≤ 1 + 2 ^ K₀)
    linarith)
  have hlog4 : Real.log (2 * Real.exp Y / Real.exp (-Y)) = Real.log 2 + 2 * Y := by
    rw [Real.log_div (by positivity) (Real.exp_pos _).ne', Real.log_mul (by norm_num)
      (Real.exp_pos _).ne']
    simp only [Real.log_exp]; ring
  have hl2' : Real.log (2 * (E * (1 + 2 ^ K₀))) + Real.log (2 * Real.exp Y / Real.exp (-Y)) ≤
      (7 * a + 73) * Z ^ m := by
    rw [hlog4]
    have he : (7 * a + 73) * Z ^ m = 7 * (a * Z ^ m) + 73 * Z ^ m := by ring
    rw [he]; linarith
  have hl2'' : 0 ≤ Real.log (2 * (E * (1 + 2 ^ K₀))) +
      Real.log (2 * Real.exp Y / Real.exp (-Y)) := by
    rw [hlog4]; linarith
  have hd1 : (((d * d + 1 : ℕ) : ℝ) + 1) ≤ 2 * Z ^ 2 := by
    push_cast
    have h1 := mul_le_mul hdZ hdZ (Nat.cast_nonneg d) (by linarith)
    have h2 : (2 : ℝ) * 2 ≤ Z * Z := mul_le_mul hZ2 hZ2 (by norm_num) (by linarith)
    rw [sq]; linarith
  have hd2 : (((d + 1 : ℕ) : ℝ) + 1) ≤ 2 * Z := by push_cast; linarith
  have hb1 : (((d * d + 1 : ℕ) : ℝ) + 1) ^ 4 ≤ 16 * Z ^ 8 := by
    calc _ ≤ (2 * Z ^ 2) ^ 4 := by gcongr
      _ = 16 * Z ^ 8 := by ring
  have hb2 : (((d + 1 : ℕ) : ℝ) + 1) ^ 4 ≤ 16 * Z ^ 8 := by
    calc _ ≤ (2 * Z) ^ 4 := by gcongr
      _ = 16 * Z ^ 4 := by ring
      _ ≤ 16 * Z ^ 8 := by gcongr; norm_num
  have hZ8 : Z ^ (m + 8) = Z ^ 8 * Z ^ m := by rw [pow_add, mul_comm]
  calc _ ≤ 9 * (32 * (16 * Z ^ 8) * ((4 * a + 25) * Z ^ m)) +
        32 * (16 * Z ^ 8) * ((7 * a + 73) * Z ^ m) := by
        gcongr
    _ = _ := by rw [hZ8]; ring

/-- Blueprint prop:base, proof line 1651: the number of scales at which the doubled-kernel
integral of a fixed three-variable chart exceeds `ε` is polynomial in
`log H + log K + log ε⁻¹`. -/
theorem sixTheta_scale_count (c₀ : ℕ) (hc : 1 ≤ c₀) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ {d : ℕ} (H K ε r₀ : ℝ) (A : MultivariableQuadraticChartData 3 d),
      MultivariableQuadraticChartComplexity c₀ H A → 1 ≤ K → 0 < ε → ε ≤ 1 → 0 < r₀ →
      ∀ (T : Finset ℤ) (W : ℤ → ℝ × ℝ → ℂ), (∀ n, Continuous (W n)) →
      (∀ n p, ‖W n p‖ ≤ K) → (∀ n p q, ‖W n p - W n q‖ ≤ K * ‖p - q‖) →
      (∀ n p, W n p ≠ 0 → |p.1| ≤ 1 ∧ |p.2| ≤ 1) → (∀ n u, ∫ τ, W n (u, τ) = 0) →
      (∀ n ∈ T, ε < ‖∫ z, sixTheta (W n) z *
        multivariableQuadraticChartAtom A ((r₀ * (2 : ℝ) ^ (-n)) • z)‖) →
      (T.card : ℝ) ≤ C * (Real.log H + Real.log K + Real.log ε⁻¹) ^ C := by
  obtain ⟨D, hD, DJ, hcount⟩ := sixTheta_count_thresholds c₀ hc
  set m : ℕ := D + DJ 1 + 2 with hm
  set a : ℝ := D * 3 ^ D + DJ 1 * 3 ^ DJ 1 + 1 with ha
  have ha1 : 1 ≤ a := by
    have : (0 : ℝ) ≤ D * 3 ^ D + DJ 1 * 3 ^ DJ 1 := by positivity
    rw [ha]; linarith
  set c : ℝ := 4608 * (4 * a + 25) + 512 * (7 * a + 73) with hcdef
  refine ⟨⌈c⌉₊ + m + 8, by omega, ?_⟩
  intro d H K ε r₀ A hA hK1 hε hε1 hr₀ T W hWc hWb hWL hWs hWm hT
  set Z := Real.log H + Real.log K + Real.log ε⁻¹ with hZ
  have hlogH : 2 ≤ Real.log H := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) hA.lower
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hlogε : 0 ≤ Real.log ε⁻¹ := Real.log_nonneg (one_le_inv_iff₀.mpr ⟨hε, hε1⟩)
  have hZ2 : 2 ≤ Z := by rw [hZ]; linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hdZ : (d : ℝ) ≤ Z := by have := hA.dimension; rw [hZ]; linarith
  set! X := 1 + Real.log (2 * H * K ^ 2) + Real.log (max 1 ε⁻¹) with hX
  have hH0 : 0 < H := lt_of_lt_of_le (Real.exp_pos 2) hA.lower
  have hK0 : 0 < K := by linarith
  have hXZ : X ≤ 3 * Z := by
    rw [hX, Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hH0.ne',
      Real.log_pow, max_eq_right (one_le_inv_iff₀.mpr ⟨hε, hε1⟩), hZ]
    have := log_two_le_one
    push_cast
    linarith
  have hX0 : 0 ≤ X := by
    have hK2 : (1 : ℝ) ≤ K ^ 2 := one_le_pow₀ hK1
    have hH1 : 1 ≤ H := by linarith [hA.lower, Real.add_one_le_exp (2 : ℝ)]
    have h2HK : 1 ≤ 2 * H * K ^ 2 := one_le_mul_of_one_le_of_one_le (by linarith) hK2
    have : 0 ≤ Real.log (2 * H * K ^ 2) := Real.log_nonneg h2HK
    have : 0 ≤ Real.log (max 1 ε⁻¹) := Real.log_nonneg (le_max_left _ _)
    rw [hX]; linarith
  have hpowZ : ∀ {e : ℕ}, e ≤ m → Z ^ e ≤ Z ^ m := fun he => pow_le_pow_right₀ hZ1 he
  have hlE : (D : ℝ) * X ^ D ≤ a * Z ^ m := by
    calc (D : ℝ) * X ^ D ≤ D * (3 * Z) ^ D := by gcongr
      _ = D * 3 ^ D * Z ^ D := by rw [mul_pow, mul_assoc]
      _ ≤ a * Z ^ m := by
          apply mul_le_mul _ (hpowZ (by omega)) (by positivity) (by linarith)
          rw [ha]; have : (0 : ℝ) ≤ DJ 1 * 3 ^ DJ 1 := by positivity
          linarith
  have hlE₁ : (DJ 1 : ℝ) * X ^ DJ 1 ≤ a * Z ^ m := by
    calc (DJ 1 : ℝ) * X ^ DJ 1 ≤ DJ 1 * (3 * Z) ^ DJ 1 := by gcongr
      _ = DJ 1 * 3 ^ DJ 1 * Z ^ DJ 1 := by rw [mul_pow, mul_assoc]
      _ ≤ a * Z ^ m := by
          apply mul_le_mul _ (hpowZ (by omega)) (by positivity) (by linarith)
          rw [ha]; have : (0 : ℝ) ≤ D * 3 ^ D := by positivity
          linarith
  have hE1 : 1 ≤ Real.exp (D * X ^ D) := Real.one_le_exp (by positivity)
  have hE₁1 : 1 ≤ Real.exp (DJ 1 * X ^ DJ 1) := Real.one_le_exp (by positivity)
  have hG1 : 1 ≤ 2 * 7 ^ (d + d) * (2 * Real.pi) ^ ((d + 1) ^ 2) := by
    have h7 : (1 : ℝ) ≤ 7 ^ (d + d) := one_le_pow₀ (by norm_num)
    have hπ : (1 : ℝ) ≤ (2 * Real.pi) ^ ((d + 1) ^ 2) :=
      one_le_pow₀ (by linarith [Real.pi_gt_three])
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr; norm_num
  have hYpos : 0 < (2 * a + 23) * Z ^ m := by positivity
  have hZm : Z ≤ Z ^ m := by simpa using hpowZ (e := 1) (by omega)
  have hbig := count_threshold_big (m := m) hK1 hE1 hE₁1 hG1 hε hZ1 hZm (hpowZ (by omega))
    (by rw [hZ]; linarith) (by rw [hZ]; linarith) (log_lattice_const_le hZ1 hdZ)
    (by rw [Real.log_exp]; exact hlE) (by rw [Real.log_exp]; exact hlE₁)
  obtain ⟨herr, h2K, h2K'⟩ := count_threshold_err hK1 hE1 hE₁1 hG1 hYpos hbig hε
  have hαpos : 0 < Real.exp (-((2 * a + 23) * Z ^ m)) := Real.exp_pos _
  have hαle : Real.exp (-((2 * a + 23) * Z ^ m)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hβ1 : 1 ≤ Real.exp ((2 * a + 23) * Z ^ m) := Real.one_le_exp hYpos.le
  have hc := hcount H K ε r₀ A hA hK1 hε hr₀ T W hWc hWb hWL hWs hWm hT
    (Real.exp (-((2 * a + 23) * Z ^ m))) (Real.exp (-((2 * a + 23) * Z ^ m)))
    (Real.exp ((2 * a + 23) * Z ^ m)) ⌈(2 * a + 23) * Z ^ m / Real.log 2⌉₊ hαpos
    (hαle.trans hE1) hαpos (hαle.trans hβ1) hβ1 herr
  have hfin := hc.trans (count_logs_le hZ2 hdZ ha1 hE1 (by rw [Real.log_exp]; exact hlE) rfl
    h2K')
  refine hfin.trans ?_
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  calc c * Z ^ (m + 8) ≤ (⌈c⌉₊ + m + 8 : ℕ) * Z ^ (m + 8) := by
        gcongr
        exact (Nat.le_ceil c).trans (by exact_mod_cast (by omega : ⌈c⌉₊ ≤ ⌈c⌉₊ + m + 8))
    _ ≤ (⌈c⌉₊ + m + 8 : ℕ) * Z ^ (⌈c⌉₊ + m + 8) := by
        gcongr
        · omega

/-! ### The rescaled kernel slice at a fixed path point -/

/-- The kernel in the rescaled coordinates `(U, τ) = ((u - y)/r, t/r)` of the transposed form
in slot `m`: `W(U, τ) = w(y + r(U - mτ), rτ)` (blueprint prop:base, line 1645). -/
noncomputable def kernelSlice (w : ℝ × ℝ → ℂ) (y r : ℝ) (m : Fin 4) (p : ℝ × ℝ) : ℂ :=
  w (y + r * (p.1 - (m : ℝ) * p.2), r * p.2)

/-- Lipschitz constant of the kernel slices of the class. -/
noncomputable def kernelLipConst (κ : LocalKernelClass) : ℝ :=
  5 * (κ.derivativeConstant * 3) ^ (κ.derivativeConstant * 3)

/-- One constant bounding the slices and their Lipschitz constants. -/
noncomputable def sliceConst (κ : LocalKernelClass) : ℝ :=
  localKernelSupBound κ + kernelLipConst κ + 1

theorem kernelLipConst_nonneg (κ : LocalKernelClass) : 0 ≤ kernelLipConst κ := by
  unfold kernelLipConst
  have := κ.one_le_derivativeConstant
  have : 0 ≤ κ.derivativeConstant * 3 := by linarith
  positivity

theorem one_le_sliceConst (κ : LocalKernelClass) : 1 ≤ sliceConst κ := by
  unfold sliceConst
  have := localKernelSupBound_nonneg κ
  have := kernelLipConst_nonneg κ
  linarith

theorem kernelSlice_continuous {κ : LocalKernelClass} {a₀ r : ℝ} {w : ℝ × ℝ → ℂ}
    (hw : IsAdmissibleLocalKernel κ a₀ r w) (y : ℝ) (m : Fin 4) :
    Continuous (kernelSlice w y r m) := by
  unfold kernelSlice
  exact hw.smooth.continuous.comp ((continuous_const.add (continuous_const.mul
    (continuous_fst.sub (continuous_const.mul continuous_snd)))).prodMk
    (continuous_const.mul continuous_snd))

theorem kernelSlice_norm_le {κ : LocalKernelClass} {a₀ r : ℝ} {w : ℝ × ℝ → ℂ}
    (hw : IsAdmissibleLocalKernel κ a₀ r w) (y : ℝ) (m : Fin 4) (p : ℝ × ℝ) :
    ‖kernelSlice w y r m p‖ ≤ sliceConst κ := by
  have := admissibleLocalKernel_norm_le hw (y + r * (p.1 - (m : ℝ) * p.2), r * p.2)
  have := kernelLipConst_nonneg κ
  unfold kernelSlice sliceConst
  linarith

theorem kernelSlice_support {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r) {w : ℝ × ℝ → ℂ}
    (hw : IsAdmissibleLocalKernel κ a₀ r w) {y : ℝ} (hy : y ∈ Set.Icc a₀ (a₀ + r)) (m : Fin 4)
    (p : ℝ × ℝ) (hp : kernelSlice w y r m p ≠ 0) : |p.1| ≤ 1 ∧ |p.2| ≤ 1 := by
  have hs := admissibleLocalKernel_support hr.le hw
  have ht := localProgressionSupport_time hr.le hs hp
  have hm := hs _ hp m
  simp only [realProgressionCoordinate] at hm
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨hm1, hm2⟩ := hm
  have e : y + r * (p.1 - (m : ℝ) * p.2) + (m : ℝ) * (r * p.2) = y + r * p.1 := by ring
  rw [e] at hm1 hm2
  constructor
  · rw [abs_le]; constructor
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith
  · rw [abs_le]; constructor
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith

theorem kernelSlice_marginal {κ : LocalKernelClass} {a₀ r : ℝ} {w : ℝ × ℝ → ℂ}
    (hw : IsAdmissibleLocalKernel κ a₀ r w) (y : ℝ) (m : Fin 4) (U : ℝ) :
    ∫ τ, kernelSlice w y r m (U, τ) = 0 := by
  have h := Measure.integral_comp_mul_left (fun t => w (y + r * U - (m : ℝ) * t, t)) r
  have e : (fun τ => kernelSlice w y r m (U, τ)) =
      fun τ => (fun t => w (y + r * U - (m : ℝ) * t, t)) (r * τ) := by
    funext τ; unfold kernelSlice; congr 2; ring
  rw [e, h, hw.marginal (y + r * U) m, smul_zero]

/-- Mean value bound for the kernel along coordinate lines. -/
theorem admissibleKernel_lipschitz {κ : LocalKernelClass} {a₀ r : ℝ}
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) (x x' t t' : ℝ) :
    ‖w (x, t) - w (x', t')‖ ≤
      r⁻¹ * (κ.derivativeConstant * 3) ^ (κ.derivativeConstant * 3) * (|x - x'| + |t - t'|) := by
  set c := (κ.derivativeConstant * 3) ^ (κ.derivativeConstant * 3) with hc
  have hdiff : Differentiable ℝ w := hw.smooth.differentiable (by simp)
  have hx : ‖w (x, t) - w (x', t)‖ ≤ r⁻¹ * c * |x - x'| := by
    have hd : ∀ s, DifferentiableAt ℝ (fun s => w (s, t)) s := fun s =>
      (hdiff _).comp s ((differentiableAt_id).prodMk (differentiableAt_const _))
    have hb : ∀ s, ‖deriv (fun s => w (s, t)) s‖ ≤ r⁻¹ * c := fun s => by
      have := hw.derivativeBound 1 0 (s, t)
      simp only [localKernelPartial, iteratedDeriv_one, iteratedDeriv_zero] at this
      have e : κ.derivativeConstant * (((1 + 0 : ℕ) : ℝ) + 2) = κ.derivativeConstant * 3 := by
        norm_num
      simp only [e] at this
      simpa only [Nat.add_zero, pow_one] using this
    have := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (fun s _ => hd s)
      (fun s _ => hb s) convex_univ (Set.mem_univ x') (Set.mem_univ x)
    rwa [Real.norm_eq_abs] at this
  have ht : ‖w (x', t) - w (x', t')‖ ≤ r⁻¹ * c * |t - t'| := by
    have hd : ∀ s, DifferentiableAt ℝ (fun s => w (x', s)) s := fun s =>
      (hdiff _).comp s ((differentiableAt_const _).prodMk differentiableAt_id)
    have hb : ∀ s, ‖deriv (fun s => w (x', s)) s‖ ≤ r⁻¹ * c := fun s => by
      have := hw.derivativeBound 0 1 (x', s)
      simp only [localKernelPartial, iteratedDeriv_one, iteratedDeriv_zero] at this
      have e : κ.derivativeConstant * (((0 + 1 : ℕ) : ℝ) + 2) = κ.derivativeConstant * 3 := by
        norm_num
      simp only [e] at this
      simpa only [Nat.zero_add, pow_one] using this
    have := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (fun s _ => hd s)
      (fun s _ => hb s) convex_univ (Set.mem_univ t') (Set.mem_univ t)
    rwa [Real.norm_eq_abs] at this
  calc ‖w (x, t) - w (x', t')‖ ≤ ‖w (x, t) - w (x', t)‖ + ‖w (x', t) - w (x', t')‖ := by
        rw [← sub_add_sub_cancel (w (x, t)) (w (x', t)) (w (x', t'))]; exact norm_add_le _ _
    _ ≤ r⁻¹ * c * |x - x'| + r⁻¹ * c * |t - t'| := add_le_add hx ht
    _ = _ := by ring

theorem kernelSlice_lipschitz {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r) {w : ℝ × ℝ → ℂ}
    (hw : IsAdmissibleLocalKernel κ a₀ r w) (y : ℝ) (m : Fin 4) (p q : ℝ × ℝ) :
    ‖kernelSlice w y r m p - kernelSlice w y r m q‖ ≤ sliceConst κ * ‖p - q‖ := by
  set c := (κ.derivativeConstant * 3) ^ (κ.derivativeConstant * 3) with hc
  have hc0 : 0 ≤ c := by
    have := κ.one_le_derivativeConstant
    have : 0 ≤ κ.derivativeConstant * 3 := by linarith
    positivity
  have h := admissibleKernel_lipschitz hw (y + r * (p.1 - (m : ℝ) * p.2)) (y + r * (q.1 -
    (m : ℝ) * q.2)) (r * p.2) (r * q.2)
  have h1 : |p.1 - q.1| ≤ ‖p - q‖ := by
    have := norm_fst_le (p - q); rwa [Prod.fst_sub, Real.norm_eq_abs] at this
  have h2 : |p.2 - q.2| ≤ ‖p - q‖ := by
    have := norm_snd_le (p - q); rwa [Prod.snd_sub, Real.norm_eq_abs] at this
  have hm3 : (m : ℝ) ≤ 3 := by exact_mod_cast Nat.lt_succ_iff.mp m.2
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have e1 : |y + r * (p.1 - (m : ℝ) * p.2) - (y + r * (q.1 - (m : ℝ) * q.2))| ≤
      r * (|p.1 - q.1| + 3 * |p.2 - q.2|) := by
    have : y + r * (p.1 - (m : ℝ) * p.2) - (y + r * (q.1 - (m : ℝ) * q.2)) =
        r * ((p.1 - q.1) - (m : ℝ) * (p.2 - q.2)) := by ring
    rw [this, abs_mul, abs_of_pos hr]
    gcongr
    refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul, abs_of_nonneg hm0]
    gcongr
  have e2 : |r * p.2 - r * q.2| = r * |p.2 - q.2| := by
    rw [← mul_sub, abs_mul, abs_of_pos hr]
  unfold kernelSlice
  refine h.trans ?_
  rw [e2]
  have hsc : sliceConst κ = localKernelSupBound κ + 5 * c + 1 := rfl
  have hsup := localKernelSupBound_nonneg κ
  calc r⁻¹ * c * (|y + r * (p.1 - (m : ℝ) * p.2) - (y + r * (q.1 - (m : ℝ) * q.2))| +
        r * |p.2 - q.2|) ≤ r⁻¹ * c * (r * (|p.1 - q.1| + 3 * |p.2 - q.2|) + r * |p.2 - q.2|) := by
        gcongr
    _ = c * (|p.1 - q.1| + 4 * |p.2 - q.2|) := by field_simp; ring
    _ ≤ c * (5 * ‖p - q‖) := by gcongr; linarith
    _ ≤ sliceConst κ * ‖p - q‖ := by
        rw [hsc]; nlinarith only [norm_nonneg (p - q), hsup]

/-! ### The transposed form in one slot -/

/-- The shear `(x, t) ↦ (x + c t, t)` of the plane. -/
noncomputable def shearEquiv (c : ℝ) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun z := (z.1 + c * z.2, z.2)
  invFun z := (z.1 - c * z.2, z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  measurable_toFun := (by fun_prop : Measurable fun z : ℝ × ℝ => (z.1 + c * z.2, z.2))
  measurable_invFun := (by fun_prop : Measurable fun z : ℝ × ℝ => (z.1 - c * z.2, z.2))

theorem shearEquiv_measurePreserving (c : ℝ) :
    MeasurePreserving (shearEquiv c) (volume : Measure (ℝ × ℝ)) volume := by
  have hτ : MeasurePreserving (fun p : ℝ × ℝ => (p.1, p.2 + c * p.1))
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) :=
    (MeasurePreserving.id volume).skew_product (g := fun t x => x + c * t) (by fun_prop)
      (Filter.Eventually.of_forall fun t => (measurePreserving_add_right volume (c * t)).map_eq)
  have h := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)).comp
    (hτ.comp (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)))
  rw [Measure.volume_eq_prod]
  convert h using 1
  funext z; rfl

/-- The product of the three fixed slots along the transposed line. -/
noncomputable def transposeProduct (φ : Fin 4 → ℝ → ℂ) (m : Fin 4) (u t : ℝ) : ℂ :=
  ∏ j ∈ Finset.univ.erase m, φ j (u + ((j : ℝ) - m) * t)

/-- The transposed function of the local form in slot `m`:
`T(u) = r⁻¹ ∫ w(u - m t, t) ∏_{j ≠ m} φ_j(u + (j - m) t) dt`. -/
noncomputable def tripleTranspose (r : ℝ) (w : ℝ × ℝ → ℂ) (m : Fin 4) (φ : Fin 4 → ℝ → ℂ)
    (u : ℝ) : ℂ :=
  (r : ℂ)⁻¹ * ∫ t, w (u - (m : ℝ) * t, t) * transposeProduct φ m u t

theorem transposeProduct_measurable {φ : Fin 4 → ℝ → ℂ} (hφ : ∀ j, Measurable (φ j))
    (m : Fin 4) : Measurable (Function.uncurry (transposeProduct φ m)) := by
  unfold transposeProduct
  refine Finset.measurable_prod _ fun j _ => (hφ j).comp ?_
  fun_prop

theorem transposeProduct_norm_le {φ : Fin 4 → ℝ → ℂ} {B : ℝ} (m : Fin 4)
    (hB : ∀ j, j ≠ m → ∀ x, ‖φ j x‖ ≤ B) (u t : ℝ) : ‖transposeProduct φ m u t‖ ≤ B ^ 3 := by
  unfold transposeProduct
  rw [norm_prod]
  have hc : (Finset.univ.erase m).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
  calc ∏ j ∈ Finset.univ.erase m, ‖φ j (u + ((j : ℝ) - m) * t)‖ ≤
      ∏ _j ∈ Finset.univ.erase m, B :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          fun j hj => hB j (Finset.ne_of_mem_erase hj) _
    _ = B ^ 3 := by rw [Finset.prod_const, hc]

theorem kernel_transpose_support {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) (m : Fin 4) {u t : ℝ}
    (h : w (u - (m : ℝ) * t, t) ≠ 0) : u ∈ Set.Icc a₀ (a₀ + r) ∧ t ∈ Set.Icc (-r) r := by
  have hs := admissibleLocalKernel_support hr.le hw
  have hm := hs _ h m
  simp only [realProgressionCoordinate, sub_add_cancel] at hm
  exact ⟨hm, localProgressionSupport_time hr.le hs h⟩

theorem tripleTranspose_support {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) (m : Fin 4) (φ : Fin 4 → ℝ → ℂ)
    {u : ℝ} (hu : u ∉ Set.Icc a₀ (a₀ + r)) : tripleTranspose r w m φ u = 0 := by
  unfold tripleTranspose
  have : (fun t => w (u - (m : ℝ) * t, t) * transposeProduct φ m u t) = fun _ => 0 := by
    funext t
    by_cases h : w (u - (m : ℝ) * t, t) = 0
    · rw [h, zero_mul]
    · exact absurd (kernel_transpose_support hr hw m h).1 hu
  rw [this, integral_zero, mul_zero]

theorem tripleTranspose_norm_le {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) (m : Fin 4) {φ : Fin 4 → ℝ → ℂ}
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j, j ≠ m → ∀ x, ‖φ j x‖ ≤ B) (u : ℝ) :
    ‖tripleTranspose r w m φ u‖ ≤ 2 * (localKernelSupBound κ * B ^ 3) := by
  unfold tripleTranspose
  have hM := localKernelSupBound_nonneg κ
  have hbound : ∀ t, ‖w (u - (m : ℝ) * t, t) * transposeProduct φ m u t‖ ≤
      Set.indicator (Set.Icc (-r) r) (fun _ => localKernelSupBound κ * B ^ 3) t := by
    intro t
    by_cases h : w (u - (m : ℝ) * t, t) = 0
    · rw [h, zero_mul, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => by positivity) _
    · rw [Set.indicator_of_mem (kernel_transpose_support hr hw m h).2, norm_mul]
      exact mul_le_mul (admissibleLocalKernel_norm_le hw _)
        (transposeProduct_norm_le m hB u t) (norm_nonneg _) hM
  have hI : ‖∫ t, w (u - (m : ℝ) * t, t) * transposeProduct φ m u t‖ ≤
      2 * r * (localKernelSupBound κ * B ^ 3) := by
    calc _ ≤ ∫ t, Set.indicator (Set.Icc (-r) r) (fun _ => localKernelSupBound κ * B ^ 3) t :=
          norm_integral_le_of_norm_le
            ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc)
            (Filter.Eventually.of_forall hbound)
      _ = _ := by
          rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc, smul_eq_mul,
            max_eq_left (by linarith)]; ring
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  calc r⁻¹ * ‖∫ t, w (u - (m : ℝ) * t, t) * transposeProduct φ m u t‖ ≤
      r⁻¹ * (2 * r * (localKernelSupBound κ * B ^ 3)) := by gcongr
    _ = _ := by field_simp

theorem tripleTranspose_measurable {κ : LocalKernelClass} {a₀ r : ℝ}
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) (m : Fin 4) {φ : Fin 4 → ℝ → ℂ}
    (hφ : ∀ j, Measurable (φ j)) : Measurable (tripleTranspose r w m φ) := by
  unfold tripleTranspose
  refine Measurable.const_mul ?_ _
  have hf : StronglyMeasurable (Function.uncurry fun u t =>
      w (u - (m : ℝ) * t, t) * transposeProduct φ m u t) := by
    refine Measurable.stronglyMeasurable ?_
    exact (hw.smooth.continuous.measurable.comp (by fun_prop)).mul
      (transposeProduct_measurable hφ m)
  exact (hf.integral_prod_right' (ν := volume)).measurable

/-- The local form transposed to slot `m`: `H(F) = r⁻¹ ∫ F_m T`. -/
theorem localProgressionForm_transpose {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) (m : Fin 4) {F : Fin 4 → ℝ → ℂ}
    (hF : ∀ j, Measurable (F j)) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j, j ≠ m → ∀ x, ‖F j x‖ ≤ B)
    (hFm : IntegrableOn (F m) (Set.Icc a₀ (a₀ + r))) :
    localProgressionForm r w F = (r : ℂ)⁻¹ * ∫ u, F m u * tripleTranspose r w m F u := by
  set G : ℝ × ℝ → ℂ := fun z => F m z.1 * (w (z.1 - (m : ℝ) * z.2, z.2) *
    transposeProduct F m z.1 z.2) with hG
  have hpt : ∀ z : ℝ × ℝ, w (z.1 + -(m : ℝ) * z.2, z.2) *
      ∏ j, F j (realProgressionCoordinate j (z.1 + -(m : ℝ) * z.2, z.2)) = G z := by
    intro z
    rw [hG]
    dsimp only
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
    unfold transposeProduct realProgressionCoordinate
    have e1 : z.1 - (m : ℝ) * z.2 + (m : ℝ) * z.2 = z.1 := by ring
    have e2 : z.1 + -(m : ℝ) * z.2 = z.1 - (m : ℝ) * z.2 := by ring
    have e3 : ∀ j : Fin 4, z.1 - (m : ℝ) * z.2 + (j : ℝ) * z.2 = z.1 + ((j : ℝ) - m) * z.2 :=
      fun j => by ring
    simp only [e2]
    simp only [e1, e3]
    ring
  have hshear : (∫ z : ℝ × ℝ, w z * ∏ j, F j (realProgressionCoordinate j z)) = ∫ z, G z := by
    rw [← (shearEquiv_measurePreserving (-(m : ℝ))).integral_comp']
    exact congrArg (fun f => ∫ z, f z) (funext hpt)
  have hM := localKernelSupBound_nonneg κ
  have hGi : Integrable G (volume.prod volume) := by
    set h1 : ℝ → ℝ := Set.indicator (Set.Icc a₀ (a₀ + r)) fun u => ‖F m u‖ with hh1
    set h2 : ℝ → ℝ := Set.indicator (Set.Icc (-r) r) fun _ => localKernelSupBound κ * B ^ 3
      with hh2
    have hi1 : Integrable h1 :=
      IntegrableOn.integrable_indicator (f := fun u => ‖F m u‖) hFm.norm measurableSet_Icc
    have hi2 : Integrable h2 :=
      (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
    refine (hi1.mul_prod hi2).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine Measurable.aestronglyMeasurable ?_
      exact ((hF m).comp measurable_fst).mul
        ((hw.smooth.continuous.measurable.comp (by fun_prop)).mul
          (transposeProduct_measurable hF m))
    · by_cases h : w (z.1 - (m : ℝ) * z.2, z.2) = 0
      · simp only [hG, h, zero_mul, mul_zero, norm_zero]
        exact mul_nonneg (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
          (Set.indicator_nonneg (fun _ _ => by positivity) _)
      · obtain ⟨hu, ht⟩ := kernel_transpose_support hr hw m h
        simp only [hh1, hh2, Set.indicator_of_mem hu, Set.indicator_of_mem ht, hG, norm_mul]
        gcongr
        · exact admissibleLocalKernel_norm_le hw _
        · exact transposeProduct_norm_le m hB _ _
  unfold localProgressionForm
  rw [hshear, Measure.volume_eq_prod, integral_prod G hGi]
  have hinner : ∀ u, (∫ t, G (u, t)) = F m u * ((r : ℂ) * tripleTranspose r w m F u) := by
    intro u
    simp only [hG, tripleTranspose]
    rw [integral_const_mul]
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    field_simp
  simp only [hinner]
  have : (fun u => F m u * ((r : ℂ) * tripleTranspose r w m F u)) =
      fun u => (r : ℂ) * (F m u * tripleTranspose r w m F u) := by funext u; ring
  rw [this, integral_const_mul]
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

/-- The six atoms of the squared transposed form at the path point `y` (blueprint prop:base,
line 1645): the triple at anchor `y + r z₀` with times `r z₁` and its conjugate with `r z₂`. -/
noncomputable def sixPsi (φ : Fin 4 → ℝ → ℂ) (m : Fin 4) (y r : ℝ) (z : Fin 3 → ℝ) : ℂ :=
  transposeProduct φ m (y + r * z 0) (r * z 1) * conj (transposeProduct φ m (y + r * z 0) (r * z 2))

/-- A bounded measurable function vanishing outside a set of finite measure is integrable. -/
theorem integrable_of_bound_of_support {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} {S : Set X} (hSμ : μ S ≠ ⊤)
    (hf : AEStronglyMeasurable f μ) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (hs : ∀ x, x ∉ S → f x = 0) :
    Integrable f μ := by
  have hon : IntegrableOn f S μ :=
    Measure.integrableOn_of_bounded hSμ hf (Filter.Eventually.of_forall hM)
  exact hon.integrable_of_forall_notMem_eq_zero hs

/-- Blueprint prop:base, line 1645: the squared normalized `L²` norm of the transposed function
is the doubled-kernel integral of the six atoms in the rescaled variables. -/
theorem tripleTranspose_sq_eq {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) (m : Fin 4) {φ : Fin 4 → ℝ → ℂ}
    (hφ : ∀ j, Measurable (φ j)) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j, j ≠ m → ∀ x, ‖φ j x‖ ≤ B)
    (y : ℝ) :
    (((r⁻¹ * ∫ u, ‖tripleTranspose r w m φ u‖ ^ 2 : ℝ)) : ℂ) =
      ∫ z, sixTheta (kernelSlice w y r m) z * sixPsi φ m y r z := by
  set K : ℝ → ℝ → ℂ := fun u t => w (u - (m : ℝ) * t, t) * transposeProduct φ m u t with hK
  set Φ : (Fin 3 → ℝ) → ℂ := fun z => K (z 0) (z 1) * conj (K (z 0) (z 2)) with hΦ
  have hM := localKernelSupBound_nonneg κ
  have hKm : Measurable (Function.uncurry K) :=
    (hw.smooth.continuous.measurable.comp (by fun_prop)).mul (transposeProduct_measurable hφ m)
  have hKb : ∀ u t, ‖K u t‖ ≤ localKernelSupBound κ * B ^ 3 := fun u t => by
    simp only [hK, norm_mul]
    exact mul_le_mul (admissibleLocalKernel_norm_le hw _) (transposeProduct_norm_le m hB u t)
      (norm_nonneg _) hM
  have hKs : ∀ u t, K u t ≠ 0 → u ∈ Set.Icc a₀ (a₀ + r) ∧ t ∈ Set.Icc (-r) r := fun u t h =>
    kernel_transpose_support hr hw m (left_ne_zero_of_mul h)
  -- the left side as an iterated integral
  have hT : ∀ u, tripleTranspose r w m φ u = (r : ℂ)⁻¹ * ∫ t, K u t := fun u => rfl
  have hsq : ∀ u, ((‖tripleTranspose r w m φ u‖ ^ 2 : ℝ) : ℂ) =
      (r : ℂ)⁻¹ ^ 2 * ∫ q : ℝ × ℝ, K u q.1 * conj (K u q.2) := by
    intro u
    rw [Measure.volume_eq_prod, integral_prod_mul (fun t => K u t) (fun t => conj (K u t)),
      integral_conj, Complex.ofReal_pow, ← Complex.mul_conj', hT, map_mul, map_inv₀,
      Complex.conj_ofReal]
    ring
  -- the right side
  have hrhs : (∫ z, sixTheta (kernelSlice w y r m) z * sixPsi φ m y r z) =
      ∫ z : Fin 3 → ℝ, Φ ((Fin.cons y 0 : Fin 3 → ℝ) + r • z) := by
    congr 1; funext z
    simp only [hΦ, hK, sixTheta, sixPsi, kernelSlice, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e0 : (Fin.cons y 0 : Fin 3 → ℝ) 0 = y := rfl
    have e1 : (Fin.cons y 0 : Fin 3 → ℝ) 1 = 0 := rfl
    have e2 : (Fin.cons y 0 : Fin 3 → ℝ) 2 = 0 := rfl
    rw [e0, e1, e2, zero_add, zero_add, map_mul]
    have h1 : y + r * (z 0 - (m : ℝ) * z 1) = y + r * z 0 - (m : ℝ) * (r * z 1) := by ring
    have h2 : y + r * (z 0 - (m : ℝ) * z 2) = y + r * z 0 - (m : ℝ) * (r * z 2) := by ring
    rw [h1, h2]
    ring
  have hscale : (∫ z : Fin 3 → ℝ, Φ ((Fin.cons y 0 : Fin 3 → ℝ) + r • z)) =
      (r : ℂ)⁻¹ ^ 3 * ∫ z, Φ z := by
    have h := Measure.integral_comp_smul (volume : Measure (Fin 3 → ℝ))
      (fun z => Φ ((Fin.cons y 0 : Fin 3 → ℝ) + z)) r
    rw [h, integral_add_left_eq_self, Module.finrank_fin_fun, abs_inv, abs_pow, abs_of_pos hr,
      Complex.real_smul]
    push_cast; ring
  -- the triple integral as an iterated integral
  have hΦi : Integrable (fun p : ℝ × (Fin 2 → ℝ) => Φ (Fin.insertNth 0 p.1 p.2))
      ((volume : Measure ℝ).prod volume) := by
    have hmeas : Measurable fun p : ℝ × (Fin 2 → ℝ) => Φ (Fin.insertNth 0 p.1 p.2) := by
      have hins : Measurable fun p : ℝ × (Fin 2 → ℝ) =>
          (Fin.insertNth 0 p.1 p.2 : Fin 3 → ℝ) :=
        (Continuous.finInsertNth (A := fun _ : Fin 3 => ℝ) 0 continuous_fst
          continuous_snd).measurable
      have h0 := (measurable_pi_apply 0).comp hins
      have h1 := (measurable_pi_apply 1).comp hins
      have h2 := (measurable_pi_apply 2).comp hins
      exact (hKm.comp (h0.prodMk h1)).mul (Complex.continuous_conj.measurable.comp (hKm.comp
          (h0.prodMk h2)))
    refine integrable_of_bound_of_support (S := Set.Icc a₀ (a₀ + r) ×ˢ
      Set.Icc (fun _ => -r) (fun _ => r))
      (by
        rw [Measure.prod_prod]
        exact ENNReal.mul_ne_top measure_Icc_lt_top.ne measure_Icc_lt_top.ne)
      hmeas.aestronglyMeasurable (M := (localKernelSupBound κ * B ^ 3) ^ 2) ?_ ?_
    · intro p
      simp only [hΦ, norm_mul, Complex.norm_conj, sq]
      exact mul_le_mul (hKb _ _) (hKb _ _) (norm_nonneg _) (by positivity)
    · intro p hp
      have e1 : (Fin.insertNth 0 p.1 p.2 : Fin 3 → ℝ) 1 = p.2 0 := by
        change (Fin.insertNth 0 p.1 p.2 : Fin 3 → ℝ) (Fin.succAbove 0 0) = p.2 0
        exact Fin.insertNth_apply_succAbove (α := fun _ => ℝ) (0 : Fin 3) p.1 p.2 0
      have e2 : (Fin.insertNth 0 p.1 p.2 : Fin 3 → ℝ) 2 = p.2 1 := by
        change (Fin.insertNth 0 p.1 p.2 : Fin 3 → ℝ) (Fin.succAbove 0 1) = p.2 1
        exact Fin.insertNth_apply_succAbove (α := fun _ => ℝ) (0 : Fin 3) p.1 p.2 1
      by_contra hne
      simp only [hΦ] at hne
      have hA := hKs _ _ (left_ne_zero_of_mul hne)
      have hB' := hKs _ _ (fun h => (right_ne_zero_of_mul hne) (by rw [h, map_zero]))
      apply hp
      refine ⟨?_, ?_, ?_⟩
      · simpa using hA.1
      · intro i; fin_cases i
        · simpa [e1] using hA.2.1
        · simpa [e2] using hB'.2.1
      · intro i; fin_cases i
        · simpa [e1] using hA.2.2
        · simpa [e2] using hB'.2.2
  have hiter : (∫ z, Φ z) = ∫ u, ∫ q : ℝ × ℝ, K u q.1 * conj (K u q.2) := by
    rw [integral_fin_three, Measure.volume_eq_prod, integral_prod _ hΦi]
    congr 1; funext a
    rw [integral_fin_two]
    rfl
  rw [hrhs, hscale, hiter]
  push_cast
  rw [← integral_complex_ofReal]
  simp only [hsq]
  rw [integral_const_mul]
  ring

/-- Integrals against the normalized measure of functions vanishing off the cell. -/
theorem integral_normalized_of_support {a₀ r : ℝ} (hr : 0 < r) {f : ℝ → ℂ}
    (hf : ∀ u, u ∉ Set.Icc a₀ (a₀ + r) → f u = 0) :
    ∫ u, f u ∂normalizedIntervalMeasure a₀ r = (r : ℂ)⁻¹ * ∫ u, f u := by
  unfold normalizedIntervalMeasure
  rw [integral_smul_measure, setIntegral_eq_integral_of_forall_compl_eq_zero hf,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hr.le), Complex.real_smul]
  push_cast; ring

theorem integral_normalized_of_support_real {a₀ r : ℝ} (hr : 0 < r) {f : ℝ → ℝ}
    (hf : ∀ u, u ∉ Set.Icc a₀ (a₀ + r) → f u = 0) :
    ∫ u, f u ∂normalizedIntervalMeasure a₀ r = r⁻¹ * ∫ u, f u := by
  unfold normalizedIntervalMeasure
  rw [integral_smul_measure, setIntegral_eq_integral_of_forall_compl_eq_zero hf,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hr.le), smul_eq_mul]

/-- Blueprint prop:base, line 1645: the transpose norm of three fixed slots against a
normalized `L²` input in the fourth slot is the square root of the doubled-kernel integral of
the six atoms. -/
theorem localProgressionForm_le_six {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) (m : Fin 4) {F : Fin 4 → ℝ → ℂ}
    (hF : ∀ j, Measurable (F j)) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j, j ≠ m → ∀ x, ‖F j x‖ ≤ B)
    (hFm : MemLp (F m) 2 (normalizedIntervalMeasure a₀ r)) (y : ℝ) :
    ‖localProgressionForm r w F‖ ≤
      (eLpNorm (F m) 2 (normalizedIntervalMeasure a₀ r)).toReal *
        Real.sqrt ‖∫ z, sixTheta (kernelSlice w y r m) z * sixPsi F m y r z‖ := by
  set μ := normalizedIntervalMeasure a₀ r with hμ
  have hprob : IsProbabilityMeasure μ := normalizedIntervalMeasure_probability a₀ hr
  set T := tripleTranspose r w m F with hTdef
  have hTs : ∀ u, u ∉ Set.Icc a₀ (a₀ + r) → T u = 0 := fun u hu =>
    tripleTranspose_support hr hw m F hu
  have hTm : Measurable T := tripleTranspose_measurable hw m hF
  have hTb := tripleTranspose_norm_le hr hw m hB0 hB
  -- integrability of the input on the cell
  have hFmI : IntegrableOn (F m) (Set.Icc a₀ (a₀ + r)) := by
    have h1 : Integrable (F m) μ := (hFm.mono_exponent (by norm_num)).integrable le_rfl
    rw [hμ, normalizedIntervalMeasure, integrable_smul_measure (by simp [hr]) (by simp)] at h1
    exact h1
  have htrans := localProgressionForm_transpose hr hw m hF hB0 hB hFmI
  -- pass to the normalized measure
  have hμint : (r : ℂ)⁻¹ * ∫ u, F m u * T u = ∫ u, F m u * T u ∂μ :=
    (integral_normalized_of_support hr fun u hu => by rw [hTs u hu, mul_zero]).symm
  have hTL : MemLp T (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    exact MemLp.of_bound hTm.aestronglyMeasurable _ (Filter.Eventually.of_forall hTb)
  have hFL : MemLp (F m) (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]; exact hFm
  have hhold := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hFL hTL
  -- the two factors
  have hF2 : (∫ u, ‖F m u‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = (eLpNorm (F m) 2 μ).toReal := by
    rw [hFm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
      ENNReal.toReal_ofReal (by positivity)]
    norm_num
  have hT2 : (∫ u, ‖T u‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) =
      Real.sqrt ‖∫ z, sixTheta (kernelSlice w y r m) z * sixPsi F m y r z‖ := by
    rw [← tripleTranspose_sq_eq hr hw m hF hB0 hB y]
    have e : (fun u => ‖T u‖ ^ (2 : ℝ)) = fun u => ‖T u‖ ^ 2 := by
      funext u; exact Real.rpow_two _
    rw [e, integral_normalized_of_support_real hr fun u hu => by rw [hTs u hu, norm_zero]; norm_num,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hr.le) (integral_nonneg fun u => by positivity)),
      Real.sqrt_eq_rpow]
  rw [htrans, hμint]
  calc ‖∫ u, F m u * T u ∂μ‖ ≤ ∫ u, ‖F m u‖ * ‖T u‖ ∂μ := by
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        congr 1; funext u; exact norm_mul _ _
    _ ≤ _ := hhold
    _ = _ := by rw [hF2, hT2]

theorem prod_erase_eq_succAbove {M : Type*} [CommMonoid M] (m : Fin 4) (f : Fin 4 → M) :
    ∏ j ∈ Finset.univ.erase m, f j = ∏ i : Fin 3, f (m.succAbove i) := by
  rw [← Finset.compl_singleton, ← Fin.image_succAbove_univ,
    Finset.prod_image fun a _ b _ h => Fin.succAbove_right_injective h]

/-- The two atoms of one slot: the slot atom along `z₀ + c z₁` and its conjugate along
`z₀ + c z₂`. -/
noncomputable def pairChart {d : ℕ} (B : QuadraticChartData d) (c : ℝ) :
    MultivariableQuadraticChartData 3 (d + d) :=
  mvProductChart (liftChart B ![1, c, 0]) (liftChart (conjugateQuadraticChart B) ![1, 0, c])

theorem pairChart_atom {d : ℕ} (B : QuadraticChartData d) (c r : ℝ) (z : Fin 3 → ℝ) :
    multivariableQuadraticChartAtom (pairChart B c) (r • z) =
      quadraticChartAtom B (r * (z 0 + c * z 1)) *
        conj (quadraticChartAtom B (r * (z 0 + c * z 2))) := by
  unfold pairChart
  rw [mvProductChart_atom, liftChart_atom, liftChart_atom, conjugateQuadraticChart_atom]
  congr 2
  · simp [dotProduct, Fin.sum_univ_three]; ring
  · simp [dotProduct, Fin.sum_univ_three]; ring_nf

/-- The six-atom chart in three variables (blueprint prop:base, line 1645). -/
noncomputable def sixChart {d : Fin 3 → ℕ} (B : (i : Fin 3) → QuadraticChartData (d i))
    (c : Fin 3 → ℝ) :
    MultivariableQuadraticChartData 3 (((d 0 + d 0) + (d 1 + d 1)) + (d 2 + d 2)) :=
  mvProductChart (mvProductChart (pairChart (B 0) (c 0)) (pairChart (B 1) (c 1)))
    (pairChart (B 2) (c 2))

theorem sixChart_atom {d : Fin 3 → ℕ} (B : (i : Fin 3) → QuadraticChartData (d i))
    (c : Fin 3 → ℝ) (r : ℝ) (z : Fin 3 → ℝ) :
    multivariableQuadraticChartAtom (sixChart B c) (r • z) =
      ∏ i, (quadraticChartAtom (B i) (r * (z 0 + c i * z 1)) *
        conj (quadraticChartAtom (B i) (r * (z 0 + c i * z 2)))) := by
  unfold sixChart
  rw [mvProductChart_atom, mvProductChart_atom, pairChart_atom, pairChart_atom, pairChart_atom,
    Fin.prod_univ_three]

theorem pairChart_complexity {d c₀ : ℕ} {H : ℝ} {B : QuadraticChartData d}
    (hB : QuadraticChartComplexity c₀ H B) (hc : 1 ≤ c₀) (c : ℝ) :
    MultivariableQuadraticChartComplexity c₀ (H ^ 6) (pairChart B c) :=
  mvProductChart_complexity (liftChart_complexity hB _)
    (liftChart_complexity (conjugateQuadraticChart_complexity hB) _) hc

theorem mvComplexity_mono {k d c₀ : ℕ} {H K : ℝ} {A : MultivariableQuadraticChartData k d}
    (hA : MultivariableQuadraticChartComplexity c₀ H A) (hHK : H ≤ K) :
    MultivariableQuadraticChartComplexity c₀ K A :=
  quadraticChartComplexity_mono hA hHK

theorem sixChart_complexity {d : Fin 3 → ℕ} {c₀ : ℕ} {H : ℝ}
    {B : (i : Fin 3) → QuadraticChartData (d i)}
    (hB : ∀ i, QuadraticChartComplexity c₀ H (B i)) (hc : 1 ≤ c₀) (c : Fin 3 → ℝ) :
    MultivariableQuadraticChartComplexity c₀ (H ^ 216) (sixChart B c) := by
  have hH1 : 1 ≤ H := by linarith [(hB 0).lower, Real.add_one_le_exp (2 : ℝ)]
  have h01 := mvProductChart_complexity (pairChart_complexity (hB 0) hc (c 0))
    (pairChart_complexity (hB 1) hc (c 1)) hc
  have h2 : MultivariableQuadraticChartComplexity c₀ ((H ^ 6) ^ 6) (pairChart (B 2) (c 2)) :=
    mvComplexity_mono (pairChart_complexity (hB 2) hc (c 2))
      (le_self_pow₀ (one_le_pow₀ hH1) (by norm_num))
  have h := mvProductChart_complexity h01 h2 hc
  rw [← pow_mul, ← pow_mul] at h
  exact h

/-- The six atoms as a chart atom: with `φ_{m.succAbove i}(y + s) = Bᵢ(s)`,
`Ψ(z) = Q(r z)` for the fixed six-atom chart `Q`. -/
theorem sixPsi_eq_sixChart {φ : Fin 4 → ℝ → ℂ} (m : Fin 4) (y r : ℝ) {d : Fin 3 → ℕ}
    (B : (i : Fin 3) → QuadraticChartData (d i))
    (hB : ∀ i s, quadraticChartAtom (B i) s = φ (m.succAbove i) (s + y)) (z : Fin 3 → ℝ) :
    sixPsi φ m y r z = multivariableQuadraticChartAtom
      (sixChart B fun i => ((m.succAbove i : ℕ) : ℝ) - m) (r • z) := by
  rw [sixChart_atom, sixPsi, transposeProduct, transposeProduct, prod_erase_eq_succAbove,
    prod_erase_eq_succAbove, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hB, hB]
  congr 1
  · congr 1; ring
  · congr 2; ring

/-- The transpose norm of three fixed slots on a cell of scale `r` through `y`
(blueprint prop:base, line 1645): `A_I = (∫ θ Ψ)^{1/2}`. -/
noncomputable def tripleNorm (w : ℝ × ℝ → ℂ) (φ : Fin 4 → ℝ → ℂ) (m : Fin 4) (y r : ℝ) : ℝ :=
  Real.sqrt ‖∫ z, sixTheta (kernelSlice w y r m) z * sixPsi φ m y r z‖

theorem tripleNorm_nonneg (w : ℝ × ℝ → ℂ) (φ : Fin 4 → ℝ → ℂ) (m : Fin 4) (y r : ℝ) :
    0 ≤ tripleNorm w φ m y r := Real.sqrt_nonneg _

/-- Blueprint prop:base, proof line 1651: along a path through `y`, the scales where three fixed
basic atoms have transpose norm above `s` are polynomially many in `log H + log s⁻¹`. -/
theorem tripleNorm_count (κ : LocalKernelClass) (c₀ : ℕ) (hc : 1 ≤ c₀) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ {d : Fin 3 → ℕ} (H r₀ s y : ℝ) (B : (i : Fin 3) → QuadraticChartData (d i))
      (φ : Fin 4 → ℝ → ℂ) (m : Fin 4), (∀ i, QuadraticChartComplexity c₀ H (B i)) →
      (∀ i u, quadraticChartAtom (B i) u = φ (m.succAbove i) (u + y)) → 0 < r₀ → 0 < s →
      s ≤ 1 → ∀ (a : ℤ → ℝ) (w : ℤ → ℝ × ℝ → ℂ) (T : Finset ℤ),
      (∀ n ∈ T, IsAdmissibleLocalKernel κ (a n) (r₀ * (2 : ℝ) ^ (-n)) (w n)) →
      (∀ n ∈ T, y ∈ Set.Icc (a n) (a n + r₀ * (2 : ℝ) ^ (-n))) →
      (∀ n ∈ T, s < tripleNorm (w n) φ m y (r₀ * (2 : ℝ) ^ (-n))) →
      (T.card : ℝ) ≤ C * (216 * Real.log H + Real.log (sliceConst κ) + 2 * Real.log s⁻¹) ^ C := by
  obtain ⟨C, hC, hcount⟩ := sixTheta_scale_count c₀ hc
  refine ⟨C, hC, ?_⟩
  intro d H r₀ s y B φ m hB hBφ hr₀ hs hs1 a w T hw hy hT
  classical
  have hH1 : 1 ≤ H := by linarith [(hB 0).lower, Real.add_one_le_exp (2 : ℝ)]
  have hA := sixChart_complexity hB hc (fun i => ((m.succAbove i : ℕ) : ℝ) - m)
  have hrn : ∀ n : ℤ, 0 < r₀ * (2 : ℝ) ^ (-n) := fun n => by positivity
  set! W : ℤ → ℝ × ℝ → ℂ := fun n =>
    if n ∈ T then kernelSlice (w n) y (r₀ * (2 : ℝ) ^ (-n)) m else 0 with hW
  have hK1 := one_le_sliceConst κ
  have h := hcount (H ^ 216) (sliceConst κ) (s ^ 2) r₀ _ hA hK1
    (by positivity) (pow_le_one₀ hs.le hs1) hr₀ T W
    (fun n => by
      by_cases hn : n ∈ T
      · simp only [hW, hn, ↓reduceIte]; exact kernelSlice_continuous (hw n hn) y m
      · simp only [hW, hn, ↓reduceIte]; exact continuous_const)
    (fun n p => by
      by_cases hn : n ∈ T
      · simp only [hW, hn, ↓reduceIte]; exact kernelSlice_norm_le (hw n hn) y m p
      · simp only [hW, hn, ↓reduceIte, Pi.zero_apply, norm_zero]; linarith)
    (fun n p q => by
      by_cases hn : n ∈ T
      · simp only [hW, hn, ↓reduceIte]; exact kernelSlice_lipschitz (hrn n) (hw n hn) y m p q
      · simp only [hW, hn, ↓reduceIte, Pi.zero_apply, sub_zero, norm_zero]; positivity)
    (fun n p hp => by
      by_cases hn : n ∈ T
      · simp only [hW, hn, ↓reduceIte] at hp
        exact kernelSlice_support (hrn n) (hw n hn) (hy n hn) m p hp
      · simp only [hW, hn, ↓reduceIte, Pi.zero_apply, ne_eq, not_true_eq_false] at hp)
    (fun n u => by
      by_cases hn : n ∈ T
      · simp only [hW, hn, ↓reduceIte]; exact kernelSlice_marginal (hw n hn) y m u
      · simp only [hW, hn, ↓reduceIte, Pi.zero_apply, integral_zero]) ?_
  · have e1 : Real.log (H ^ 216) = 216 * Real.log H := by rw [Real.log_pow]; norm_num
    have e2 : Real.log (s ^ 2)⁻¹ = 2 * Real.log s⁻¹ := by
      rw [Real.log_inv, Real.log_pow, Real.log_inv]; push_cast; ring
    rw [e1, e2] at h; exact h
  · intro n hn
    have h1 := hT n hn
    unfold tripleNorm at h1
    have h2 : s ^ 2 < ‖∫ z, sixTheta (kernelSlice (w n) y (r₀ * (2 : ℝ) ^ (-n)) m) z *
        sixPsi φ m y (r₀ * (2 : ℝ) ^ (-n)) z‖ := by
      have := Real.lt_sqrt hs.le |>.mp h1
      exact this
    simp only [sixPsi_eq_sixChart m y _ B hBφ] at h2
    simpa only [hW, hn, ↓reduceIte] using h2

/-- `∑_j (j+1)^C 2^{-j}` converges. -/
theorem summable_succ_pow_geometric (C : ℕ) :
    Summable fun j : ℕ => ((j : ℝ) + 1) ^ C * (1 / 2 : ℝ) ^ j := by
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) C (r := 1 / 2) (by norm_num)
  have h' := (summable_nat_add_iff 1).mpr h
  convert h'.mul_left 2 using 1
  funext j
  push_cast
  rw [pow_succ]; ring

/-- Blueprint prop:base, eq:triple-tail (line 1653): along a path through `y`, the transpose
norms of three fixed basic atoms that are at most `δ` sum to at most
`δ poly(log H, log δ⁻¹)`. -/
theorem tripleTail (κ : LocalKernelClass) (c₀ : ℕ) (hc : 1 ≤ c₀) :
    ∃ (C : ℕ) (Cr : ℝ), 0 ≤ Cr ∧ ∀ {d : Fin 3 → ℕ} (H r₀ δ y : ℝ)
      (B : (i : Fin 3) → QuadraticChartData (d i)) (φ : Fin 4 → ℝ → ℂ) (m : Fin 4),
      (∀ i, QuadraticChartComplexity c₀ H (B i)) →
      (∀ i u, quadraticChartAtom (B i) u = φ (m.succAbove i) (u + y)) → 0 < r₀ → 0 < δ →
      δ ≤ 1 → ∀ (a : ℤ → ℝ) (w : ℤ → ℝ × ℝ → ℂ) (T : Finset ℤ),
      (∀ n ∈ T, IsAdmissibleLocalKernel κ (a n) (r₀ * (2 : ℝ) ^ (-n)) (w n)) →
      (∀ n ∈ T, y ∈ Set.Icc (a n) (a n + r₀ * (2 : ℝ) ^ (-n))) →
      ∑ n ∈ T with tripleNorm (w n) φ m y (r₀ * (2 : ℝ) ^ (-n)) ≤ δ,
          tripleNorm (w n) φ m y (r₀ * (2 : ℝ) ^ (-n)) ≤
        δ * Cr * (Real.log H + Real.log δ⁻¹ + 1) ^ C := by
  obtain ⟨C, hC, hcnt⟩ := tripleNorm_count κ c₀ hc
  set K := sliceConst κ with hK
  have hK1 : 1 ≤ K := one_le_sliceConst κ
  have hlK : 0 ≤ Real.log K := Real.log_nonneg hK1
  set S := ∑' j : ℕ, ((j : ℝ) + 1) ^ C * (1 / 2 : ℝ) ^ j with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun j => by positivity
  refine ⟨C, C * (218 + Real.log K) ^ C * S, by positivity, ?_⟩
  intro d H r₀ δ y B φ m hB hBφ hr₀ hδ hδ1 a w T hw hy
  set A : ℤ → ℝ := fun n => tripleNorm (w n) φ m y (r₀ * (2 : ℝ) ^ (-n)) with hAdef
  have hA0 : ∀ n, 0 ≤ A n := fun n => tripleNorm_nonneg _ _ _ _ _
  have hlogH : 2 ≤ Real.log H := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) (hB 0).lower
  have hlδ : 0 ≤ Real.log δ⁻¹ := Real.log_nonneg (one_le_inv_iff₀.mpr ⟨hδ, hδ1⟩)
  set P := Real.log H + Real.log δ⁻¹ + 1 with hP
  have hP1 : 1 ≤ P := by rw [hP]; linarith
  set! L₀ := 216 * Real.log H + Real.log K + 2 * Real.log δ⁻¹ + 2 with hL₀
  have hL₀P : L₀ ≤ (218 + Real.log K) * P := by
    rw [hL₀, hP]; nlinarith only [hlK, hlogH, hlδ]
  have hL₀0 : 0 ≤ L₀ := by rw [hL₀]; linarith
  -- the layer of each positive norm
  classical
  set T' := T.filter (fun n => A n ≤ δ) with hT'
  have hex : ∀ n, 0 < A n → ∃ j : ℕ, δ / 2 ^ (j + 1) < A n := by
    intro n hn
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hn (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨j, ?_⟩
    calc δ / 2 ^ (j + 1) ≤ (1 / 2) ^ j := by
          rw [div_le_iff₀ (by positivity), one_div_pow, pow_succ]
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          nlinarith only [pow_pos (by norm_num : (0 : ℝ) < 2) j, hδ1]
      _ < A n := hj
  set! jn : ℤ → ℕ := fun n => if h : 0 < A n then Nat.find (hex n h) else 0 with hjn
  have hjn_lo : ∀ n, 0 < A n → δ / 2 ^ (jn n + 1) < A n := fun n h => by
    simp only [hjn, h, ↓reduceDIte]; exact Nat.find_spec (hex n h)
  have hjn_hi : ∀ n ∈ T', A n ≤ δ / 2 ^ jn n := by
    intro n hn
    have hnδ := (Finset.mem_filter.mp hn).2
    by_cases h : 0 < A n
    · simp only [hjn, h, ↓reduceDIte]
      rcases Nat.eq_zero_or_pos (Nat.find (hex n h)) with h0 | h0
      · rw [h0, pow_zero, div_one]; exact hnδ
      · have hmin := Nat.find_min (hex n h) (Nat.sub_lt h0 one_pos)
        push Not at hmin
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ Nat.find (hex n h))] at hmin
    · have : A n = 0 := le_antisymm (not_lt.mp h) (hA0 n)
      rw [this]; positivity
  -- the count in each layer
  have hlayer : ∀ j : ℕ, ((T'.filter fun n => 0 < A n ∧ jn n = j).card : ℝ) ≤
      C * L₀ ^ C * ((j : ℝ) + 1) ^ C := by
    intro j
    set! s := δ / 2 ^ (j + 1) with hsdef
    have hs : 0 < s := by positivity
    have hs1 : s ≤ 1 := by
      rw [hsdef, div_le_one (by positivity)]
      exact hδ1.trans (one_le_pow₀ (by norm_num))
    have hsub : ∀ n ∈ T'.filter (fun n => 0 < A n ∧ jn n = j), n ∈ T := fun n hn =>
      (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
    have hc := hcnt H r₀ s y B φ m hB hBφ hr₀ hs hs1 a w
      (T'.filter fun n => 0 < A n ∧ jn n = j) (fun n hn => hw n (hsub n hn))
      (fun n hn => hy n (hsub n hn)) (fun n hn => by
        have h := (Finset.mem_filter.mp hn).2
        have := hjn_lo n h.1
        rw [h.2] at this
        exact this)
    refine hc.trans ?_
    have hls : Real.log s⁻¹ = Real.log δ⁻¹ + (j + 1) * Real.log 2 := by
      rw [hsdef, inv_div, Real.log_div (by positivity) hδ.ne', Real.log_inv, Real.log_pow]
      push_cast; ring
    have hl2 := log_two_le_one
    have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hbase : 216 * Real.log H + Real.log K + 2 * Real.log s⁻¹ ≤ L₀ * ((j : ℝ) + 1) := by
      rw [hls, hL₀]
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have : (j + 1 : ℝ) * Real.log 2 ≤ (j + 1) * 1 :=
        mul_le_mul_of_nonneg_left hl2 (by positivity)
      nlinarith only [hlK, hlogH, hlδ, this]
    have hb0 : 0 ≤ 216 * Real.log H + Real.log K + 2 * Real.log s⁻¹ := by
      have : 0 ≤ Real.log s⁻¹ := by rw [hls]; positivity
      linarith
    calc (C : ℝ) * (216 * Real.log H + Real.log K + 2 * Real.log s⁻¹) ^ C ≤
        C * (L₀ * ((j : ℝ) + 1)) ^ C := by gcongr
      _ = C * L₀ ^ C * ((j : ℝ) + 1) ^ C := by rw [mul_pow]; ring
  -- summation
  set! N : ℕ := T'.sup jn + 1 with hN
  have hjN : ∀ n ∈ T', jn n < N := fun n hn => Nat.lt_succ_of_le (Finset.le_sup hn)
  have hsum1 : ∑ n ∈ T', A n ≤ ∑ n ∈ T' with 0 < A n, δ / 2 ^ jn n := by
    rw [Finset.sum_filter (p := fun n => 0 < A n) (f := fun n => δ / 2 ^ jn n)]
    refine Finset.sum_le_sum fun n hn => ?_
    split_ifs with h
    · exact hjn_hi n hn
    · exact le_of_eq (le_antisymm (not_lt.mp h) (hA0 n))
  have hsum2 : ∑ n ∈ T' with 0 < A n, δ / 2 ^ jn n =
      ∑ j ∈ Finset.range N, ((T'.filter fun n => 0 < A n ∧ jn n = j).card : ℝ) * (δ / 2 ^ j) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := jn) (t := Finset.range N)
      (fun n hn => Finset.mem_range.mpr (hjN n (Finset.mem_filter.mp hn).1))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.filter_filter, Finset.sum_congr rfl (fun n hn => by
      rw [(Finset.mem_filter.mp hn).2.2]), Finset.sum_const, nsmul_eq_mul]
  have hsum3 : ∑ j ∈ Finset.range N, ((T'.filter fun n => 0 < A n ∧ jn n = j).card : ℝ) *
      (δ / 2 ^ j) ≤ δ * (C * L₀ ^ C) * S := by
    calc _ ≤ ∑ j ∈ Finset.range N, C * L₀ ^ C * ((j : ℝ) + 1) ^ C * (δ / 2 ^ j) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hlayer j) (by positivity)
      _ = δ * (C * L₀ ^ C) * ∑ j ∈ Finset.range N, ((j : ℝ) + 1) ^ C * (1 / 2 : ℝ) ^ j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [one_div_pow]; field_simp
      _ ≤ δ * (C * L₀ ^ C) * S := by
          gcongr
          exact (summable_succ_pow_geometric C).sum_le_tsum _ fun j _ => by positivity
  calc ∑ n ∈ T with A n ≤ δ, A n = ∑ n ∈ T', A n := rfl
    _ ≤ δ * (C * L₀ ^ C) * S := hsum1.trans (hsum2.le.trans hsum3)
    _ ≤ δ * (C * ((218 + Real.log K) * P) ^ C) * S := by gcongr
    _ = δ * (C * (218 + Real.log K) ^ C * S) * P ^ C := by rw [mul_pow]; ring

/-! ### Active cells (blueprint prop:base, lines 1655-1660) -/

/-- The transpose norm of the three slots other than `m` on a cell of scale `r`:
`A = (r⁻¹ ∫ |T|²)^{1/2}`. -/
noncomputable def transposeNorm (r : ℝ) (w : ℝ × ℝ → ℂ) (m : Fin 4) (φ : Fin 4 → ℝ → ℂ) : ℝ :=
  Real.sqrt (r⁻¹ * ∫ u, ‖tripleTranspose r w m φ u‖ ^ 2)

theorem transposeNorm_nonneg (r : ℝ) (w : ℝ × ℝ → ℂ) (m : Fin 4) (φ : Fin 4 → ℝ → ℂ) :
    0 ≤ transposeNorm r w m φ := Real.sqrt_nonneg _

/-- The transpose norm is the doubled-kernel triple norm at every path point. -/
theorem tripleNorm_eq_transposeNorm {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) (m : Fin 4) {φ : Fin 4 → ℝ → ℂ}
    (hφ : ∀ j, Measurable (φ j)) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j, j ≠ m → ∀ x, ‖φ j x‖ ≤ B)
    (y : ℝ) : tripleNorm w φ m y r = transposeNorm r w m φ := by
  unfold tripleNorm transposeNorm
  rw [← tripleTranspose_sq_eq hr hw m hφ hB0 hB y, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hr.le) (integral_nonneg fun u => by positivity))]

/-- `|H_I(F)| ≤ ‖F_m‖_{2,I} A_I` for bounded slots other than `m`. -/
theorem localProgressionForm_le_transposeNorm {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) (m : Fin 4) {F : Fin 4 → ℝ → ℂ}
    (hF : ∀ j, Measurable (F j)) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j, j ≠ m → ∀ x, ‖F j x‖ ≤ B)
    (hFm : MemLp (F m) 2 (normalizedIntervalMeasure a₀ r)) :
    ‖localProgressionForm r w F‖ ≤
      (eLpNorm (F m) 2 (normalizedIntervalMeasure a₀ r)).toReal * transposeNorm r w m F := by
  have h := localProgressionForm_le_six hr hw m hF hB0 hB hFm 0
  rwa [show Real.sqrt ‖∫ z, sixTheta (kernelSlice w 0 r m) z * sixPsi F m 0 r z‖ =
    tripleNorm w F m 0 r from rfl, tripleNorm_eq_transposeNorm hr hw m hF hB0 hB 0] at h

/-- The transposed function only sees the slots other than `m` inside the cell. -/
theorem tripleTranspose_congr {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) (m : Fin 4)
    {φ ψ : Fin 4 → ℝ → ℂ} (h : ∀ j, j ≠ m → ∀ x ∈ Set.Ico a₀ (a₀ + r), φ j x = ψ j x) :
    tripleTranspose r w m φ = tripleTranspose r w m ψ := by
  funext u
  unfold tripleTranspose
  congr 1
  congr 1; funext t
  by_cases hk : w (u - (m : ℝ) * t, t) = 0
  · rw [hk, zero_mul, zero_mul]
  · congr 1
    unfold transposeProduct
    refine Finset.prod_congr rfl fun j hj => h j (Finset.ne_of_mem_erase hj) _ ?_
    have hs := hw.support _ hk j
    simp only [realProgressionCoordinate] at hs
    have hmr := mul_pos κ.margin_pos hr
    have e : u - (m : ℝ) * t + (j : ℝ) * t = u + ((j : ℝ) - m) * t := by ring
    rw [e] at hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem transposeNorm_congr {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) (m : Fin 4)
    {φ ψ : Fin 4 → ℝ → ℂ} (h : ∀ j, j ≠ m → ∀ x ∈ Set.Ico a₀ (a₀ + r), φ j x = ψ j x) :
    transposeNorm r w m φ = transposeNorm r w m ψ := by
  unfold transposeNorm; rw [tripleTranspose_congr hr hw m h]

/-- Expansion of one slot given as a finite combination. -/
theorem localProgressionForm_slot_sum_le {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) {F : Fin 4 → ℝ → ℂ}
    (hF : ∀ j, Measurable (F j))
    (hFf : ∀ j, eLpNorm (F j) 2 (normalizedIntervalMeasure a₀ r) ≠ ⊤) (k : Fin 4)
    {L : Type*} [Fintype L] (c : L → ℂ) (φ : L → ℝ → ℂ) (hφ : ∀ v, Measurable (φ v))
    (hφf : ∀ v, eLpNorm (φ v) 2 (normalizedIntervalMeasure a₀ r) ≠ ⊤)
    (hk : F k = fun x => ∑ v, c v * φ v x) :
    ‖localProgressionForm r w F‖ ≤
      ∑ v, ‖c v‖ * ‖localProgressionForm r w (Function.update F k (φ v))‖ := by
  have h := localProgressionForm_update_sum hr hw hF hFf k Finset.univ c φ hφ hφf
  rw [← hk, Function.update_eq_self] at h
  rw [h]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun v _ => norm_mul _ _

/-- The tuple with the three slots other than `m` replaced. -/
noncomputable def tripleSlots (F : Fin 4 → ℝ → ℂ) (m : Fin 4) (f : Fin 3 → ℝ → ℂ) :
    Fin 4 → ℝ → ℂ :=
  Function.update (Function.update (Function.update F (m.succAbove 0) (f 0)) (m.succAbove 1)
    (f 1)) (m.succAbove 2) (f 2)

theorem tripleSlots_self (F : Fin 4 → ℝ → ℂ) (m : Fin 4) (f : Fin 3 → ℝ → ℂ) :
    tripleSlots F m f m = F m := by
  unfold tripleSlots
  rw [Function.update_of_ne (Fin.succAbove_ne m 2).symm,
    Function.update_of_ne (Fin.succAbove_ne m 1).symm,
    Function.update_of_ne (Fin.succAbove_ne m 0).symm]

theorem tripleSlots_succAbove (F : Fin 4 → ℝ → ℂ) (m : Fin 4) (f : Fin 3 → ℝ → ℂ) (i : Fin 3) :
    tripleSlots F m f (m.succAbove i) = f i := by
  unfold tripleSlots
  have hinj := Fin.succAbove_right_injective (p := m)
  match i with
  | 0 =>
    rw [Function.update_of_ne (fun h => absurd (hinj h) (by decide)),
      Function.update_of_ne (fun h => absurd (hinj h) (by decide)), Function.update_self]
  | 1 =>
    rw [Function.update_of_ne (fun h => absurd (hinj h) (by decide)), Function.update_self]
  | 2 => rw [Function.update_self]

/-- Blueprint prop:base, line 1657: expanding the three slots other than `m`, each a finite
combination of bounded atoms, bounds the form by the coefficient products times the transpose
norms of the atom triples against the fourth slot. -/
theorem localProgressionForm_triple_le {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) (m : Fin 4) {F : Fin 4 → ℝ → ℂ}
    (hF : ∀ j, Measurable (F j))
    (hFm : MemLp (F m) 2 (normalizedIntervalMeasure a₀ r))
    {L : Type*} [Fintype L] (c : Fin 3 → L → ℂ) (φ : Fin 3 → L → ℝ → ℂ)
    (hφ : ∀ i v, Measurable (φ i v)) (hφb : ∀ i v x, ‖φ i v x‖ ≤ 1)
    (hFs : ∀ i, F (m.succAbove i) = fun x => ∑ v, c i v * φ i v x) :
    ‖localProgressionForm r w F‖ ≤
      ∑ v₀, ∑ v₁, ∑ v₂, ‖c 0 v₀‖ * ‖c 1 v₁‖ * ‖c 2 v₂‖ *
        ((eLpNorm (F m) 2 (normalizedIntervalMeasure a₀ r)).toReal *
          transposeNorm r w m (tripleSlots F m ![φ 0 v₀, φ 1 v₁, φ 2 v₂])) := by
  set μ := normalizedIntervalMeasure a₀ r with hμ
  have hprob : IsProbabilityMeasure μ := normalizedIntervalMeasure_probability a₀ hr
  have hφf : ∀ i v, eLpNorm (φ i v) 2 μ ≠ ⊤ := fun i v =>
    (MemLp.of_bound (hφ i v).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (hφb i v))).eLpNorm_ne_top
  have hFf : ∀ j, eLpNorm (F j) 2 μ ≠ ⊤ := by
    intro j
    by_cases hjm : j = m
    · subst hjm; exact hFm.eLpNorm_ne_top
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hjm
      rw [hFs i]
      exact (memLp_finsetSum Finset.univ fun v _ => (MemLp.of_bound (hφ i v).aestronglyMeasurable
        1 (Filter.Eventually.of_forall (hφb i v))).const_mul (c i v)).eLpNorm_ne_top
  have hupd_m : ∀ (G : Fin 4 → ℝ → ℂ) (k : Fin 4) (g : ℝ → ℂ), (∀ j, Measurable (G j)) →
      (∀ j, eLpNorm (G j) 2 μ ≠ ⊤) → Measurable g → eLpNorm g 2 μ ≠ ⊤ →
      (∀ j, Measurable (Function.update G k g j)) ∧
        ∀ j, eLpNorm (Function.update G k g j) 2 μ ≠ ⊤ := by
    intro G k g hG hGf hg hgf
    refine ⟨fun j => ?_, fun j => ?_⟩
    · by_cases hj : j = k
      · subst hj; rw [Function.update_self]; exact hg
      · rw [Function.update_of_ne hj]; exact hG j
    · by_cases hj : j = k
      · subst hj; rw [Function.update_self]; exact hgf
      · rw [Function.update_of_ne hj]; exact hGf j
  have hs01 : m.succAbove 0 ≠ m.succAbove 1 :=
    fun h => absurd (Fin.succAbove_right_injective h) (by decide)
  have hs02 : m.succAbove 0 ≠ m.succAbove 2 :=
    fun h => absurd (Fin.succAbove_right_injective h) (by decide)
  have hs12 : m.succAbove 1 ≠ m.succAbove 2 :=
    fun h => absurd (Fin.succAbove_right_injective h) (by decide)
  refine (localProgressionForm_slot_sum_le hr hw hF hFf (m.succAbove 0) (c 0) (φ 0) (hφ 0)
    (hφf 0) (hFs 0)).trans (Finset.sum_le_sum fun v₀ _ => ?_)
  obtain ⟨hF1, hF1f⟩ := hupd_m F _ _ hF hFf (hφ 0 v₀) (hφf 0 v₀)
  have h1 := localProgressionForm_slot_sum_le hr hw hF1 hF1f (m.succAbove 1) (c 1) (φ 1)
    (hφ 1) (hφf 1) (by rw [Function.update_of_ne hs01.symm, hFs 1])
  refine (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v₁ _ => ?_
  obtain ⟨hF2, hF2f⟩ := hupd_m _ _ _ hF1 hF1f (hφ 1 v₁) (hφf 1 v₁)
  have h2 := localProgressionForm_slot_sum_le hr hw hF2 hF2f (m.succAbove 2) (c 2) (φ 2)
    (hφ 2) (hφf 2) (by rw [Function.update_of_ne hs12.symm, Function.update_of_ne hs02.symm,
      hFs 2])
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    (norm_nonneg _)).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun v₂ _ => ?_
  set F3 := tripleSlots F m ![φ 0 v₀, φ 1 v₁, φ 2 v₂] with hF3
  have hF3e : Function.update (Function.update (Function.update F (m.succAbove 0) (φ 0 v₀))
      (m.succAbove 1) (φ 1 v₁)) (m.succAbove 2) (φ 2 v₂) = F3 := rfl
  rw [hF3e]
  obtain ⟨hF3m, -⟩ := hupd_m _ _ _ hF2 hF2f (hφ 2 v₂) (hφf 2 v₂)
  have hb : ∀ j, j ≠ m → ∀ x, ‖F3 j x‖ ≤ 1 := by
    intro j hj x
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj
    rw [hF3, tripleSlots_succAbove]
    fin_cases i <;> exact hφb _ _ x
  have hm3 : F3 m = F m := tripleSlots_self F m _
  have hlast := localProgressionForm_le_transposeNorm hr hw m (F := F3) hF3m zero_le_one hb
    (by rw [hm3]; exact hFm)
  rw [hm3] at hlast
  have := mul_le_mul_of_nonneg_left hlast (mul_nonneg (mul_nonneg (norm_nonneg (c 0 v₀))
    (norm_nonneg (c 1 v₁))) (norm_nonneg (c 2 v₂)))
  calc ‖c 0 v₀‖ * (‖c 1 v₁‖ * (‖c 2 v₂‖ * ‖localProgressionForm r w F3‖)) =
      ‖c 0 v₀‖ * ‖c 1 v₁‖ * ‖c 2 v₂‖ * ‖localProgressionForm r w F3‖ := by ring
    _ ≤ _ := this

open scoped Classical in
/-- Blueprint eq:triple-tail for a finite collection of dyadic cells: the cells through `y`
whose triple, a fixed chart triple near the path, has transpose norm at most `δ` contribute at
most `δ poly(log H, log δ⁻¹)`. -/
theorem cells_tripleTail (κ : LocalKernelClass) (c₀ : ℕ) (hc : 1 ≤ c₀) :
    ∃ (C : ℕ) (Cr : ℝ), 0 ≤ Cr ∧ ∀ {d : Fin 3 → ℕ} (G : RealDyadicGrid) (cells : Finset (ℤ × ℤ))
      (w : ℤ × ℤ → ℝ × ℝ → ℂ),
      (∀ I ∈ cells, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)
        (w I)) →
      ∀ (H δ y : ℝ) (B : (i : Fin 3) → QuadraticChartData (d i)),
      (∀ i, QuadraticChartComplexity c₀ H (B i)) → (∀ i, IsBoundedQuadraticChart (B i)) →
      0 < δ → δ ≤ 1 → ∀ (m : Fin 4) (Φ : ℤ × ℤ → Fin 4 → ℝ → ℂ),
      (∀ I ∈ cells, y ∈ dyadicGridCell G I.1 I.2 → ∀ i, ∀ x ∈ dyadicGridCell G I.1 I.2,
        Φ I (m.succAbove i) x = quadraticChartAtom (B i) (x - y)) →
      ∑ I ∈ cells with y ∈ dyadicGridCell G I.1 I.2 ∧
          transposeNorm (dyadicGridLength G I.1) (w I) m (Φ I) ≤ δ,
        transposeNorm (dyadicGridLength G I.1) (w I) m (Φ I) ≤
        δ * Cr * (Real.log H + Real.log δ⁻¹ + 1) ^ C := by
  obtain ⟨C, Cr, hCr, htail⟩ := tripleTail κ c₀ hc
  refine ⟨C, Cr, hCr, ?_⟩
  intro d G cells w hw H δ y B hB hBb hδ hδ1 m Φ hΦ
  classical
  set A : ℤ × ℤ → ℝ := fun I => transposeNorm (dyadicGridLength G I.1) (w I) m (Φ I) with hAdef
  set S := cells.filter fun I => y ∈ dyadicGridCell G I.1 I.2 with hS
  have hinj : Set.InjOn Prod.fst (S : Set (ℤ × ℤ)) := by
    intro I hI J hJ hIJ
    have hI' := (Finset.mem_filter.mp hI).2
    have hJ' := (Finset.mem_filter.mp hJ).2
    exact dyadicGridCell_eq_of_common_point G hI' hJ' hIJ.symm
  set T := S.image Prod.fst with hT
  set! cellAt : ℤ → ℤ × ℤ := fun n => if h : ∃ I ∈ S, I.1 = n then h.choose else (n, 0)
    with hcellAt
  have hcell_mem : ∀ n ∈ T, cellAt n ∈ S ∧ (cellAt n).1 = n := by
    intro n hn
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hn
    have h : ∃ J ∈ S, J.1 = I.1 := ⟨I, hI, rfl⟩
    simp only [hcellAt, h, ↓reduceDIte]
    exact h.choose_spec
  have hcell_eq : ∀ I ∈ S, cellAt I.1 = I := by
    intro I hI
    have := hcell_mem I.1 (Finset.mem_image_of_mem _ hI)
    exact hinj this.1 hI this.2
  set! φ : Fin 4 → ℝ → ℂ := Fin.insertNth m 0 (fun i x => quadraticChartAtom (B i) (x - y))
    with hφ
  have hφs : ∀ i, φ (m.succAbove i) = fun x => quadraticChartAtom (B i) (x - y) := fun i =>
    Fin.insertNth_apply_succAbove (α := fun _ => ℝ → ℂ) m 0 _ i
  have hφm : ∀ j, Measurable (φ j) := by
    intro j
    by_cases hj : j = m
    · subst hj; simp only [hφ, Fin.insertNth_apply_same]; exact measurable_const
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj
      rw [hφs]; exact (quadraticChartAtom_measurable _).comp (measurable_id.sub_const _)
  have hφb : ∀ j, j ≠ m → ∀ x, ‖φ j x‖ ≤ 1 := by
    intro j hj x
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj
    rw [hφs]; exact hBb i _
  set! a : ℤ → ℝ := fun n => dyadicGridLeft G n (cellAt n).2 with ha
  set! w' : ℤ → ℝ × ℝ → ℂ := fun n => w (cellAt n) with hw'
  have hlen : ∀ n : ℤ, dyadicGridLength G n = G.baseLength * (2 : ℝ) ^ (-n) := fun n => rfl
  have hadm : ∀ n ∈ T, IsAdmissibleLocalKernel κ (a n) (G.baseLength * (2 : ℝ) ^ (-n)) (w' n) := by
    intro n hn
    obtain ⟨hmem, hfst⟩ := hcell_mem n hn
    have h := hw _ (Finset.mem_filter.mp hmem).1
    rw [hfst] at h
    simpa only [ha, hw', hlen] using h
  have hyn : ∀ n ∈ T, y ∈ Set.Icc (a n) (a n + G.baseLength * (2 : ℝ) ^ (-n)) := by
    intro n hn
    obtain ⟨hmem, hfst⟩ := hcell_mem n hn
    have h := (Finset.mem_filter.mp hmem).2
    rw [hfst] at h
    exact Set.Ico_subset_Icc_self (by simpa only [ha, hlen, dyadicGridCell] using h)
  have hAn : ∀ n ∈ T, A (cellAt n) =
      tripleNorm (w' n) φ m y (G.baseLength * (2 : ℝ) ^ (-n)) := by
    intro n hn
    obtain ⟨hmem, hfst⟩ := hcell_mem n hn
    have hy := (Finset.mem_filter.mp hmem).2
    have hcm := (Finset.mem_filter.mp hmem).1
    have hpos : 0 < G.baseLength * (2 : ℝ) ^ (-n) := by have := G.baseLength_pos; positivity
    rw [tripleNorm_eq_transposeNorm hpos (hadm n hn) m hφm zero_le_one hφb y]
    simp only [hAdef, hw']
    rw [hfst, hlen]
    refine transposeNorm_congr hpos (hadm n hn) m fun j hj x hx => ?_
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj
    rw [hφs]
    have hx' : x ∈ dyadicGridCell G (cellAt n).1 (cellAt n).2 := by
      rw [hfst]; simpa only [dyadicGridCell, ha, hlen] using hx
    exact hΦ _ hcm hy i x hx'
  have hmain := htail H G.baseLength δ y B φ m hB (fun i u => by rw [hφs]; simp)
    G.baseLength_pos hδ hδ1 a w' T hadm hyn
  have hsum : ∑ I ∈ cells with y ∈ dyadicGridCell G I.1 I.2 ∧ A I ≤ δ, A I =
      ∑ n ∈ T with tripleNorm (w' n) φ m y (G.baseLength * (2 : ℝ) ^ (-n)) ≤ δ,
        tripleNorm (w' n) φ m y (G.baseLength * (2 : ℝ) ^ (-n)) := by
    rw [Finset.sum_filter, Finset.sum_filter, hT, Finset.sum_image hinj]
    rw [show (∑ I ∈ cells, if y ∈ dyadicGridCell G I.1 I.2 ∧ A I ≤ δ then A I else 0) =
        ∑ I ∈ S, if A I ≤ δ then A I else 0 by
      rw [hS, Finset.sum_filter]
      refine Finset.sum_congr rfl fun I _ => ?_
      by_cases hy : y ∈ dyadicGridCell G I.1 I.2 <;> simp [hy]]
    refine Finset.sum_congr rfl fun I hI => ?_
    have hn : I.1 ∈ T := Finset.mem_image_of_mem _ hI
    rw [← hAn I.1 hn, hcell_eq I hI]
  rw [hsum]
  exact hmain

open scoped Classical in
/-- Blueprint prop:base, line 1655: the cells through `y` whose triple, a fixed chart triple
near the path, has transpose norm above `δ` are polynomially many in `log H + log δ⁻¹`. -/
theorem cells_tripleCount (κ : LocalKernelClass) (c₀ : ℕ) (hc : 1 ≤ c₀) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ {d : Fin 3 → ℕ} (G : RealDyadicGrid) (cells : Finset (ℤ × ℤ))
      (w : ℤ × ℤ → ℝ × ℝ → ℂ),
      (∀ I ∈ cells, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)
        (w I)) →
      ∀ (H δ y : ℝ) (B : (i : Fin 3) → QuadraticChartData (d i)),
      (∀ i, QuadraticChartComplexity c₀ H (B i)) → (∀ i, IsBoundedQuadraticChart (B i)) →
      0 < δ → δ ≤ 1 → ∀ (m : Fin 4) (Φ : ℤ × ℤ → Fin 4 → ℝ → ℂ),
      (∀ I ∈ cells, y ∈ dyadicGridCell G I.1 I.2 → ∀ i, ∀ x ∈ dyadicGridCell G I.1 I.2,
        Φ I (m.succAbove i) x = quadraticChartAtom (B i) (x - y)) →
      ((cells.filter fun I => y ∈ dyadicGridCell G I.1 I.2 ∧
          δ < transposeNorm (dyadicGridLength G I.1) (w I) m (Φ I)).card : ℝ) ≤
        C * (216 * Real.log H + Real.log (sliceConst κ) + 2 * Real.log δ⁻¹) ^ C := by
  obtain ⟨C, hC, hcnt⟩ := tripleNorm_count κ c₀ hc
  refine ⟨C, hC, ?_⟩
  intro d G cells w hw H δ y B hB hBb hδ hδ1 m Φ hΦ
  classical
  set A : ℤ × ℤ → ℝ := fun I => transposeNorm (dyadicGridLength G I.1) (w I) m (Φ I) with hAdef
  set S := cells.filter fun I => y ∈ dyadicGridCell G I.1 I.2 with hS
  have hinj : Set.InjOn Prod.fst (S : Set (ℤ × ℤ)) := by
    intro I hI J hJ hIJ
    have hI' := (Finset.mem_filter.mp hI).2
    have hJ' := (Finset.mem_filter.mp hJ).2
    exact dyadicGridCell_eq_of_common_point G hI' hJ' hIJ.symm
  set T := S.image Prod.fst with hT
  set! cellAt : ℤ → ℤ × ℤ := fun n => if h : ∃ I ∈ S, I.1 = n then h.choose else (n, 0)
    with hcellAt
  have hcell_mem : ∀ n ∈ T, cellAt n ∈ S ∧ (cellAt n).1 = n := by
    intro n hn
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hn
    have h : ∃ J ∈ S, J.1 = I.1 := ⟨I, hI, rfl⟩
    simp only [hcellAt, h, ↓reduceDIte]
    exact h.choose_spec
  have hcell_eq : ∀ I ∈ S, cellAt I.1 = I := by
    intro I hI
    have := hcell_mem I.1 (Finset.mem_image_of_mem _ hI)
    exact hinj this.1 hI this.2
  set! φ : Fin 4 → ℝ → ℂ := Fin.insertNth m 0 (fun i x => quadraticChartAtom (B i) (x - y))
    with hφ
  have hφs : ∀ i, φ (m.succAbove i) = fun x => quadraticChartAtom (B i) (x - y) := fun i =>
    Fin.insertNth_apply_succAbove (α := fun _ => ℝ → ℂ) m 0 _ i
  have hφm : ∀ j, Measurable (φ j) := by
    intro j
    by_cases hj : j = m
    · subst hj; simp only [hφ, Fin.insertNth_apply_same]; exact measurable_const
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj
      rw [hφs]; exact (quadraticChartAtom_measurable _).comp (measurable_id.sub_const _)
  have hφb : ∀ j, j ≠ m → ∀ x, ‖φ j x‖ ≤ 1 := by
    intro j hj x
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj
    rw [hφs]; exact hBb i _
  set! a : ℤ → ℝ := fun n => dyadicGridLeft G n (cellAt n).2 with ha
  set! w' : ℤ → ℝ × ℝ → ℂ := fun n => w (cellAt n) with hw'
  have hlen : ∀ n : ℤ, dyadicGridLength G n = G.baseLength * (2 : ℝ) ^ (-n) := fun n => rfl
  have hadm : ∀ n ∈ T, IsAdmissibleLocalKernel κ (a n) (G.baseLength * (2 : ℝ) ^ (-n)) (w' n) := by
    intro n hn
    obtain ⟨hmem, hfst⟩ := hcell_mem n hn
    have h := hw _ (Finset.mem_filter.mp hmem).1
    rw [hfst] at h
    simpa only [ha, hw', hlen] using h
  have hyn : ∀ n ∈ T, y ∈ Set.Icc (a n) (a n + G.baseLength * (2 : ℝ) ^ (-n)) := by
    intro n hn
    obtain ⟨hmem, hfst⟩ := hcell_mem n hn
    have h := (Finset.mem_filter.mp hmem).2
    rw [hfst] at h
    exact Set.Ico_subset_Icc_self (by simpa only [ha, hlen, dyadicGridCell] using h)
  have hAn : ∀ n ∈ T, A (cellAt n) =
      tripleNorm (w' n) φ m y (G.baseLength * (2 : ℝ) ^ (-n)) := by
    intro n hn
    obtain ⟨hmem, hfst⟩ := hcell_mem n hn
    have hy := (Finset.mem_filter.mp hmem).2
    have hcm := (Finset.mem_filter.mp hmem).1
    have hpos : 0 < G.baseLength * (2 : ℝ) ^ (-n) := by have := G.baseLength_pos; positivity
    rw [tripleNorm_eq_transposeNorm hpos (hadm n hn) m hφm zero_le_one hφb y]
    simp only [hAdef, hw']
    rw [hfst, hlen]
    refine transposeNorm_congr hpos (hadm n hn) m fun j hj x hx => ?_
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj
    rw [hφs]
    have hx' : x ∈ dyadicGridCell G (cellAt n).1 (cellAt n).2 := by
      rw [hfst]; simpa only [dyadicGridCell, ha, hlen] using hx
    exact hΦ _ hcm hy i x hx'
  set! T' := T.filter fun n => δ < tripleNorm (w' n) φ m y (G.baseLength * (2 : ℝ) ^ (-n))
    with hT'
  have hmain := hcnt H G.baseLength δ y B φ m hB (fun i u => by rw [hφs]; simp)
    G.baseLength_pos hδ hδ1 a w' T' (fun n hn => hadm n (Finset.mem_filter.mp hn).1)
    (fun n hn => hyn n (Finset.mem_filter.mp hn).1) (fun n hn => (Finset.mem_filter.mp hn).2)
  refine le_trans (le_of_eq ?_) hmain
  have hcard : (cells.filter fun I => y ∈ dyadicGridCell G I.1 I.2 ∧ δ < A I).card =
      T'.card := by
    have h1 : (cells.filter fun I => y ∈ dyadicGridCell G I.1 I.2 ∧ δ < A I) =
        S.filter fun I => δ < A I := by
      rw [hS, Finset.filter_filter]
    rw [h1, hT', hT, Finset.filter_image]
    rw [Finset.card_image_of_injOn (fun I hI J hJ h => hinj (Finset.mem_filter.mp hI).1
      (Finset.mem_filter.mp hJ).1 h)]
    congr 1
    refine Finset.filter_congr fun I hI => ?_
    have hn : I.1 ∈ T := Finset.mem_image_of_mem _ hI
    rw [← hAn I.1 hn, hcell_eq I hI]
  rw [hcard]

namespace AccSetup

/-- Blueprint prop:base, proof lines 1634-1638: the tuple-specific accurate fits. With the
detection budget of `lem:detection` at accuracy `e^{-k}` and a cap `M > 16 B²`, the greedy
attempts satisfy the hypotheses, their restart roots have total length at most `4/3 |J|`, and on
every coarse cell the residual of the delayed fine projection is `e^{-k}`-small. -/
theorem accurateFit (κ : LocalKernelClass) :
    ∃ (c₂ C : ℕ), 1 ≤ c₂ ∧ 1 ≤ C ∧ ∀ q : ℝ, 2 < q → ∃ Cq : ℝ, 0 < Cq ∧
    ∀ S : AccSetup, S.c₂ = c₂ → S.q = q → S.B = fitBudget Cq C S.k → 1 ≤ S.k →
      Measurable S.f →
      (∀ c ∈ dyadicFiniteTree S.G S.J S.N, (c = S.J ∨ kernelHull S.G S.J S.N S.w c) →
        eLpNorm S.f 2
          (normalizedIntervalMeasure (dyadicGridLeft S.G c.1 c.2) (dyadicGridLength S.G c.1)) ≤
            1) →
      S.K₀ ≤ S.N →
      (∀ I, IsAdmissibleLocalKernel κ (dyadicGridLeft S.G I.1 I.2) (dyadicGridLength S.G I.1)
        (S.w I)) →
      16 * S.B ^ 2 < S.M →
      S.Hyp ∧ dyadicRootLength S.G S.tree.roots ≤ 4 / 3 * dyadicGridLength S.G S.J.1 ∧
        ∀ I ∈ dyadicFiniteTree S.G S.J S.Nc, S.tree.seg I ∈ S.tree.roots ∧
          S.cell I ⊆ S.cell (S.tree.seg I) ∧
          FormSmall (dyadicGridLeft S.G I.1 I.2) (dyadicGridLength S.G I.1) (S.w I) S.e S.q
            (S.res I (S.tree.st I).1 (S.tree.st I).2) (Real.exp (-(S.k : ℝ))) := by
  obtain ⟨c₂, C, hc₂, hC, hdet⟩ := fit_detect κ
  refine ⟨c₂, C, hc₂, hC, fun q hq => ?_⟩
  obtain ⟨Cq, hCq, hd⟩ := hdet q hq
  refine ⟨Cq, hCq, fun S hSc hSq hSB hk hfm hfn hK₀ hw hM => ?_⟩
  have hB1 : 1 ≤ S.B := hSB ▸ one_le_fitBudget hCq C S.k
  have h : S.Hyp := {
    f_meas := hfm
    f_norm_root := hfn S.J (dyadicFiniteTree_root_mem _ _ _) (Or.inl rfl)
    f_norm := fun c hc hcT => hfn c hc (Or.inr hcT)
    B_pos := by linarith
    K₀_le := hK₀
    detect := fun I a n _ hm h2 hns => by
      have hr := dyadicGridLength_pos S.G I.1
      rw [hSq] at hns
      obtain ⟨d, Φ, hΦc, hΦb, hΦr⟩ := hd hr (hw I) hm h2 hk hns
      exact ⟨⟨d, Φ⟩, by rw [hSc, hSB]; exact hΦc, hΦb, by rw [hSB]; exact hΦr⟩ }
  have hth := h.treeHyp
  have hT : S.tree.T < S.tree.M := by
    change 4 * S.B ^ 2 / (1 / 4) < S.M
    have : 4 * S.B ^ 2 / (1 / 4) = 16 * S.B ^ 2 := by ring
    rw [this]; exact hM
  refine ⟨h, hth.roots_length_le, fun I hI => ?_⟩
  obtain ⟨hKr, hIK, -, -⟩ := hth.seg_spec hI
  obtain ⟨-, hP⟩ := hth.retained hT hI
  refine ⟨hKr, hIK, ?_⟩
  rcases hP with hno | hsmall
  · exact absurd hI hno
  · exact hsmall

end AccSetup

/-- A predictor cover persists in the accurate-fit system, whose predictor labels are those of
the underlying system. -/
theorem AccSetup.predictorCover_system {κ : LocalKernelClass} (S : AccSetup) (K : ℤ × ℤ)
    {a i k b : Fin 4} {B Dl ε : ℝ} {d e : ℕ} {A : QuadraticChartData d}
    {A' : QuadraticChartData e} {J' : ℤ × ℤ}
    (h : PredictorCover κ S.P₀ a i k b B Dl ε A A' J') :
    PredictorCover κ (S.system K) a i k b B Dl ε A A' J' := by
  obtain ⟨ι, L, ψa, ψb, lam, coef, p, happ, hcard, hsum, hlam, hbd, hav, hwt⟩ := h
  refine ⟨ι, L, ψa, ψb, lam, coef, fun ℓ => Sum.inl (p ℓ), happ, hcard, hsum, hlam, hbd,
    fun ℓ hℓ => ⟨?_, fun y => ?_⟩, fun ℓ hℓ => ?_⟩
  · change Sum.inl (p ℓ) ∈ (S.P₀.avail J').disjSum _
    exact Finset.inl_mem_disjSum.mpr (hav ℓ hℓ).1
  · change S.sc J' (S.fatoms K J') (Sum.inl (p ℓ)) y = _
    exact (hav ℓ hℓ).2 y
  · exact hwt ℓ hℓ

/-- Two dyadic cells containing a common cell are nested. -/
theorem dyadicGridCell_nested_of_common (G : RealDyadicGrid) {I A B : ℤ × ℤ}
    (hA : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G A.1 A.2)
    (hB : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G B.1 B.2) :
    dyadicGridCell G A.1 A.2 ⊆ dyadicGridCell G B.1 B.2 ∨
      dyadicGridCell G B.1 B.2 ⊆ dyadicGridCell G A.1 A.2 := by
  have hx := dyadicGridCell_left_mem G I.1 I.2
  rcases le_total A.1 B.1 with h | h
  · rcases dyadicGridCell_nested_or_disjoint_of_le G h A.2 B.2 with hd | hs
    · exact absurd (Set.disjoint_left.mp hd (hA hx)) (not_not.mpr (hB hx))
    · exact Or.inr hs
  · rcases dyadicGridCell_nested_or_disjoint_of_le G h B.2 A.2 with hd | hs
    · exact absurd (Set.disjoint_left.mp hd (hB hx)) (not_not.mpr (hA hx))
    · exact Or.inl hs

namespace LowList
variable {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {R : ℤ × ℤ} {c₀ : ℕ} {H : ℝ}
  (X : LowList G J N R c₀ H)

/-- A label is inherited by the subroot `K` when it is available below `K` but born strictly
above. -/
def Inh (K : ℤ × ℤ) (l : X.Λ) : Prop :=
  ∃ I, X.avail I l ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G K.1 K.2 ∧
    ¬ dyadicGridCell G (X.birth I l).1 (X.birth I l).2 ⊆ dyadicGridCell G K.1 K.2

open scoped Classical in
/-- The original birth of an inherited label. -/
noncomputable def inhBirth (K : ℤ × ℤ) (l : X.Λ) : ℤ × ℤ :=
  if h : X.Inh K l then X.birth (Classical.choose h) l else K

open scoped Classical in
/-- The chart of the restriction: inherited labels keep the chart of their original birth. -/
noncomputable def restrictChart (K c : ℤ × ℤ) (l : X.Λ) : Σ d, QuadraticChartData d :=
  if c = K ∧ X.Inh K l then ⟨_, X.chart (X.inhBirth K l) l⟩ else ⟨_, X.chart c l⟩

theorem restrictChart_good (K c : ℤ × ℤ) (l : X.Λ) :
    1 ≤ (X.restrictChart K c l).1 ∧ QuadraticChartComplexity c₀ H (X.restrictChart K c l).2 ∧
      IsBoundedQuadraticChart (X.restrictChart K c l).2 := by
  by_cases h : c = K ∧ X.Inh K l
  · have e : X.restrictChart K c l = ⟨_, X.chart (X.inhBirth K l) l⟩ := by
      unfold restrictChart; simp only [h, and_self, ↓reduceIte]
    rw [e]; exact ⟨X.one_le_dim _ l, X.complexity _ l, X.bounded _ l⟩
  · have e : X.restrictChart K c l = ⟨_, X.chart c l⟩ := by
      unfold restrictChart; simp only [h, ↓reduceIte]
    rw [e]; exact ⟨X.one_le_dim _ l, X.complexity _ l, X.bounded _ l⟩

/-- Every available cell lies below the subroot or its birth contains it. -/
theorem birth_of_inh {K I : ℤ × ℤ} {l : X.Λ} (hav : X.avail I l)
    (hIK : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G K.1 K.2)
    (hb : ¬ dyadicGridCell G (X.birth I l).1 (X.birth I l).2 ⊆ dyadicGridCell G K.1 K.2) :
    dyadicGridCell G K.1 K.2 ⊆ dyadicGridCell G (X.birth I l).1 (X.birth I l).2 :=
  ((dyadicGridCell_nested_of_common G hIK (X.birth_spec I l hav).1).resolve_right hb)

theorem inhBirth_eq {K I : ℤ × ℤ} {l : X.Λ} (hav : X.avail I l)
    (hIK : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G K.1 K.2)
    (hb : ¬ dyadicGridCell G (X.birth I l).1 (X.birth I l).2 ⊆ dyadicGridCell G K.1 K.2) :
    X.inhBirth K l = X.birth I l := by
  have hinh : X.Inh K l := ⟨I, hav, hIK, hb⟩
  unfold inhBirth
  simp only [hinh, ↓reduceDIte]
  obtain ⟨hav', hI'K, hb'⟩ := Classical.choose_spec hinh
  have h1 := X.birth_of_inh hav' hI'K hb'
  have h2 := X.birth_of_inh hav hIK hb
  refine X.birth_canon' _ _ l hav' hav fun hd => ?_
  have hx := dyadicGridCell_left_mem G K.1 K.2
  exact Set.disjoint_left.mp hd (h1 hx) (h2 hx)

open scoped Classical in
/-- Restriction of a low list to a subroot `K`: coefficients below `K`, and labels inherited from
above `K` are treated as born at `K` (blueprint prop:base, line 1628). -/
noncomputable def restrict (K : ℤ × ℤ) (hK : K ∈ dyadicFiniteTree G J N) :
    LowList G J N K c₀ H where
  Λ := X.Λ
  coef := fun I l => if dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G K.1 K.2 then X.coef I l else 0
  coef_le := fun I l => by
    split_ifs
    · exact X.coef_le I l
    · simp
  avail := fun I l => X.avail I l ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G K.1 K.2
  coef_avail := fun I l h => by
    split_ifs at h with hI
    · exact ⟨X.coef_avail I l h, hI⟩
    · exact absurd rfl h
  avail_mono := fun c d l hc hd hcd h => ⟨X.avail_mono c d l hc hd hcd h.1, hcd.trans h.2⟩
  birth := fun I l => if dyadicGridCell G (X.birth I l).1 (X.birth I l).2 ⊆
    dyadicGridCell G K.1 K.2 then X.birth I l else K
  dim := fun c l => (X.restrictChart K c l).1
  chart := fun c l => (X.restrictChart K c l).2
  birth_spec := fun I l h => by
    split_ifs with hb
    · exact ⟨(X.birth_spec I l h.1).1, (X.birth_spec I l h.1).2.1, hb⟩
    · exact ⟨h.2, hK, subset_rfl⟩
  avail_birth := fun I l h => by
    split_ifs with hb
    · exact ⟨X.avail_birth I l h.1, hb⟩
    · refine ⟨?_, subset_rfl⟩
      have hsub := X.birth_of_inh h.1 h.2 hb
      exact X.avail_mono K _ l hK (X.birth_spec I l h.1).2.1 hsub (X.avail_birth I l h.1)
  birth_canon' := fun I₁ I₂ l h₁ h₂ hnd => by
    have hx := dyadicGridCell_left_mem G K.1 K.2
    split_ifs at hnd ⊢ with hb₁ hb₂ hb₂
    · exact X.birth_canon' I₁ I₂ l h₁.1 h₂.1 hnd
    · exfalso
      have hK2 := X.birth_of_inh h₂.1 h₂.2 hb₂
      have := X.birth_canon' I₁ I₂ l h₁.1 h₂.1 fun hd =>
        Set.disjoint_left.mp hd ((X.birth_spec I₁ l h₁.1).1 (dyadicGridCell_left_mem G _ _))
          (hK2 (h₁.2 (dyadicGridCell_left_mem G _ _)))
      exact hb₂ (this ▸ hb₁)
    · exfalso
      have hK1 := X.birth_of_inh h₁.1 h₁.2 hb₁
      have := X.birth_canon' I₁ I₂ l h₁.1 h₂.1 fun hd =>
        Set.disjoint_left.mp hd (hK1 (h₂.2 (dyadicGridCell_left_mem G _ _)))
          ((X.birth_spec I₂ l h₂.1).1 (dyadicGridCell_left_mem G _ _))
      exact hb₁ (this ▸ hb₂)
    · rfl
  one_le_dim := fun c l => (X.restrictChart_good K c l).1
  complexity := fun c l => (X.restrictChart_good K c l).2.1
  bounded := fun c l => (X.restrictChart_good K c l).2.2

theorem restrict_atom (K : ℤ × ℤ) (hK : K ∈ dyadicFiniteTree G J N) {I : ℤ × ℤ} {l : X.Λ}
    (hav : X.avail I l) (hIK : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G K.1 K.2) :
    (X.restrict K hK).atom I l = X.atom I l := by
  unfold atom
  by_cases hb : dyadicGridCell G (X.birth I l).1 (X.birth I l).2 ⊆ dyadicGridCell G K.1 K.2
  · have hbirth : (X.restrict K hK).birth I l = X.birth I l := by
      simp only [restrict, hb, ↓reduceIte]
    have hn : ¬ (X.birth I l = K ∧ X.Inh K l) := by
      rintro ⟨hbK, I', hav', hI'K, hb'⟩
      have h1 := X.birth_of_inh hav' hI'K hb'
      have := X.birth_canon' I I' l hav hav' fun hd => by
        have hx := dyadicGridCell_left_mem G K.1 K.2
        rw [hbK] at hd
        exact Set.disjoint_left.mp hd hx (h1 hx)
      exact hb' (this ▸ hb)
    have hchart : X.restrictChart K (X.birth I l) l = ⟨_, X.chart (X.birth I l) l⟩ := by
      unfold restrictChart; simp only [hn, ↓reduceIte]
    rw [hbirth]
    change quadraticChartAtom (X.restrictChart K (X.birth I l) l).2 = _
    rw [hchart]
  · have hinh : X.Inh K l := ⟨I, hav, hIK, hb⟩
    have hbirth : (X.restrict K hK).birth I l = K := by
      simp only [restrict, hb, ↓reduceIte]
    have hchart : X.restrictChart K K l = ⟨_, X.chart (X.inhBirth K l) l⟩ := by
      unfold restrictChart; simp only [hinh, and_self, ↓reduceIte]
    rw [hbirth]
    change quadraticChartAtom (X.restrictChart K K l).2 = _
    rw [hchart, X.inhBirth_eq hav hIK hb]

theorem restrict_val (K : ℤ × ℤ) (hK : K ∈ dyadicFiniteTree G J N) {I : ℤ × ℤ}
    (hIK : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G K.1 K.2) (y : ℝ) :
    (X.restrict K hK).val I y = X.val I y := by
  unfold val
  refine Finset.sum_congr rfl fun l _ => ?_
  have hc' : (X.restrict K hK).coef I l = X.coef I l := by simp only [restrict, hIK, ↓reduceIte]
  rw [hc']
  by_cases hc : X.coef I l = 0
  · rw [hc, zero_mul, zero_mul]
  · rw [X.restrict_atom K hK (X.coef_avail I l hc) hIK]

theorem restrict_birth_sub (K : ℤ × ℤ) (hK : K ∈ dyadicFiniteTree G J N) {I : ℤ × ℤ} {l : X.Λ}
    (hav : X.avail I l) (hIK : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G K.1 K.2) :
    dyadicGridCell G ((X.restrict K hK).birth I l).1 ((X.restrict K hK).birth I l).2 ⊆
      dyadicGridCell G (X.birth I l).1 (X.birth I l).2 := by
  by_cases hb : dyadicGridCell G (X.birth I l).1 (X.birth I l).2 ⊆ dyadicGridCell G K.1 K.2
  · have hbirth : (X.restrict K hK).birth I l = X.birth I l := by
      simp only [restrict, hb, ↓reduceIte]
    rw [hbirth]
  · have hbirth : (X.restrict K hK).birth I l = K := by
      simp only [restrict, hb, ↓reduceIte]
    rw [hbirth]
    exact X.birth_of_inh hav hIK hb

theorem restrict_chart_sigma (K : ℤ × ℤ) (hK : K ∈ dyadicFiniteTree G J N) {I : ℤ × ℤ}
    {l : X.Λ} (hav : X.avail I l) (hIK : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G K.1 K.2) :
    (⟨_, (X.restrict K hK).chart ((X.restrict K hK).birth I l) l⟩ : Σ d, QuadraticChartData d) =
      ⟨_, X.chart (X.birth I l) l⟩ := by
  by_cases hb : dyadicGridCell G (X.birth I l).1 (X.birth I l).2 ⊆ dyadicGridCell G K.1 K.2
  · have hbirth : (X.restrict K hK).birth I l = X.birth I l := by
      simp only [restrict, hb, ↓reduceIte]
    have hn : ¬ (X.birth I l = K ∧ X.Inh K l) := by
      rintro ⟨hbK, I', hav', hI'K, hb'⟩
      have h1 := X.birth_of_inh hav' hI'K hb'
      have := X.birth_canon' I I' l hav hav' fun hd => by
        have hx := dyadicGridCell_left_mem G K.1 K.2
        rw [hbK] at hd
        exact Set.disjoint_left.mp hd hx (h1 hx)
      exact hb' (this ▸ hb)
    have hchart : X.restrictChart K (X.birth I l) l = ⟨_, X.chart (X.birth I l) l⟩ := by
      unfold restrictChart; simp only [hn, ↓reduceIte]
    rw [hbirth]
    exact hchart
  · have hinh : X.Inh K l := ⟨I, hav, hIK, hb⟩
    have hbirth : (X.restrict K hK).birth I l = K := by
      simp only [restrict, hb, ↓reduceIte]
    have hchart : X.restrictChart K K l = ⟨_, X.chart (X.inhBirth K l) l⟩ := by
      unfold restrictChart; simp only [hinh, and_self, ↓reduceIte]
    rw [hbirth]
    change X.restrictChart K K l = _
    rw [hchart, X.inhBirth_eq hav hIK hb]

end LowList

theorem PredictorCover.congr_chart {κ : LocalKernelClass} {G : RealDyadicGrid} {J : ℤ × ℤ}
    {N : ℕ} {V : Type} [Fintype V] {P : PathColumnSystem G J N V} {a i k b : Fin 4}
    {B Dl ε : ℝ} {d d' e e' : ℕ} {A : QuadraticChartData d} {A₁ : QuadraticChartData d'}
    {A' : QuadraticChartData e} {A₁' : QuadraticChartData e'} {J' : ℤ × ℤ}
    (h1 : (⟨d, A⟩ : Σ d, QuadraticChartData d) = ⟨d', A₁⟩)
    (h2 : (⟨e, A'⟩ : Σ d, QuadraticChartData d) = ⟨e', A₁'⟩)
    (hc : PredictorCover κ P a i k b B Dl ε A A' J') : PredictorCover κ P a i k b B Dl ε A₁ A₁'
        J' := by
  cases h1; cases h2; exact hc

section PredCoverRestrict
variable (κ : LocalKernelClass) {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {R : ℤ × ℤ} {c₀ c₁ : ℕ}
  {H : ℝ} (Xi Xk : LowList G J N R c₀ H) (a i k b : Fin 4) (B D : ℝ)
  (pkg : ∀ (K K' : ℤ × ℤ) (li : Xi.Λ) (lk : Xk.Λ),
    PredictorPackage κ (Xi.chart K li) (Xk.chart K' lk) a i k b B D c₁)

/-- A predictor cover of the predictor system persists at smaller cells of the tree. -/
theorem predSystem_cover_mono {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {d e : ℕ}
    {A : QuadraticChartData d} {A' : QuadraticChartData e} {c c' : ℤ × ℤ}
    (hc : c ∈ dyadicFiniteTree G J N)
    (hcc' : dyadicGridCell G c.1 c.2 ⊆ dyadicGridCell G c'.1 c'.2)
    (h : PredictorCover κ (predSystem κ Xi Xk a i k b B D pkg hε0 hε1) a i k b B D ε A A' c') :
    PredictorCover κ (predSystem κ Xi Xk a i k b B D pkg hε0 hε1) a i k b B D ε A A' c := by
  obtain ⟨ι, L, ψa, ψb, lam, coef, p, happ, hcard, hsum, hlam, hbd, hav, hwt⟩ := h
  refine ⟨ι, L, ψa, ψb, lam, coef, p, happ, hcard, hsum, hlam, hbd, fun ℓ hℓ => ?_, hwt⟩
  obtain ⟨hpav, hpsc⟩ := hav ℓ hℓ
  have hPA : PredAvail κ Xi Xk a i k b B D pkg c' (p ℓ) := by
    simpa [predSystem] using hpav
  have hPAc := predAvail_mono κ Xi Xk a i k b B D pkg hc hcc' hPA
  refine ⟨by simpa [predSystem] using hPAc, fun y => ?_⟩
  change predScalar κ Xi Xk a i k b B D pkg c (p ℓ) y = _
  rw [predScalar_eq κ Xi Xk a i k b B D pkg hc hcc' hPA]
  exact hpsc y

/-- Blueprint prop:base, line 1628: at a restart root `K` the restricted low lists (inherited
labels born at `K`) are covered by the predictor system of the original lists. -/
theorem predSystem_cover_restrict {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hD1 : 1 ≤ D)
    (K : ℤ × ℤ) (hK : K ∈ dyadicFiniteTree G J N) {I : ℤ × ℤ} {li : Xi.Λ} {lk : Xk.Λ}
    (hci : (Xi.restrict K hK).coef I li ≠ 0) (hck : (Xk.restrict K hK).coef I lk ≠ 0) :
    PredictorCover κ (predSystem κ Xi Xk a i k b B D pkg hε0 hε1) a i k b B D ε
      ((Xi.restrict K hK).chart ((Xi.restrict K hK).birth I li) li)
      ((Xk.restrict K hK).chart ((Xk.restrict K hK).birth I lk) lk)
      (jointBirth (Xi.restrict K hK) (Xk.restrict K hK) I li lk) := by
  classical
  have hIK : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G K.1 K.2 := by
    by_contra h
    exact hci (by simp only [LowList.restrict, h, ↓reduceIte])
  have hci0 : Xi.coef I li ≠ 0 := by
    intro h0; exact hci (by simp only [LowList.restrict, hIK, ↓reduceIte, h0])
  have hck0 : Xk.coef I lk ≠ 0 := by
    intro h0; exact hck (by simp only [LowList.restrict, hIK, ↓reduceIte, h0])
  have hai := Xi.coef_avail I li hci0
  have hak := Xk.coef_avail I lk hck0
  have hcov := predSystem_cover κ Xi Xk a i k b B D pkg hε0 hε1 hD1 hci0 hck0
  obtain ⟨-, hJT, hJi, hJk⟩ := jointBirth_spec (Xi.restrict K hK) (Xk.restrict K hK) hci hck
  obtain ⟨hIJo, -, hJoi, hJok⟩ := jointBirth_spec Xi Xk hci0 hck0
  have hsub : dyadicGridCell G (jointBirth (Xi.restrict K hK) (Xk.restrict K hK) I li lk).1
      (jointBirth (Xi.restrict K hK) (Xk.restrict K hK) I li lk).2 ⊆
      dyadicGridCell G (jointBirth Xi Xk I li lk).1 (jointBirth Xi Xk I li lk).2 := by
    have h1 := hJi.trans (Xi.restrict_birth_sub K hK hai hIK)
    have h2 := hJk.trans (Xk.restrict_birth_sub K hK hak hIK)
    have hor : jointBirth Xi Xk I li lk = Xi.birth I li ∨ jointBirth Xi Xk I li lk = Xk.birth I
        lk := by
      unfold jointBirth; split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
    rcases hor with h | h
    · rw [h]; exact h1
    · rw [h]; exact h2
  have hmono := predSystem_cover_mono κ Xi Xk a i k b B D pkg hε0 hε1 hJT hsub hcov
  exact PredictorCover.congr_chart (Xi.restrict_chart_sigma K hK hai hIK).symm
    (Xk.restrict_chart_sigma K hK hak hIK).symm hmono

end PredCoverRestrict

end TrilinearHT.Auto

end
