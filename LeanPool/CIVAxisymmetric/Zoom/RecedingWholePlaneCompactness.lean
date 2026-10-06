/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.OmegaEquicontinuous

/-!
# Receding Whole Plane Compactness

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Filter Set Topology

noncomputable section

namespace CIV

@[expose] def planeBox (j : ℕ) : Set (ℝ × ℝ) :=
  Icc (-((j : ℝ) + 1)) ((j : ℝ) + 1) ×ˢ Icc (-((j : ℝ) + 1)) ((j : ℝ) + 1)

@[expose] def planeTimeInterval (j : ℕ) : Set ℝ := Icc (-((j : ℝ) + 1)) (-1)

theorem isCompact_planeBox (j : ℕ) : IsCompact (planeBox j) :=
  isCompact_Icc.prod isCompact_Icc

theorem isCompact_planeTimeInterval (j : ℕ) : IsCompact (planeTimeInterval j) :=
  isCompact_Icc

private theorem le_of_mem_planeTimeInterval {j : ℕ} {τ : ℝ} (hτ : τ ∈ planeTimeInterval j) :
    τ ≤ -1 := hτ.2

private theorem zero_mem_planeBox (j : ℕ) : (0 : ℝ × ℝ) ∈ planeBox j := by
  simp only [planeBox, Set.mem_prod, Set.mem_Icc, Prod.fst_zero, Prod.snd_zero]
  have h : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  exact ⟨⟨by linarith only [h], h⟩, ⟨by linarith only [h], h⟩⟩

private theorem left_mem_planeTimeInterval (j : ℕ) :
    (-((j : ℝ) + 1)) ∈ planeTimeInterval j := by
  simp only [planeTimeInterval, Set.mem_Icc]
  have h : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  exact ⟨le_refl _, by linarith only [h]⟩

private theorem exists_nat_add_one_gt_four (a b c d : ℝ) :
    ∃ j : ℕ, a < (j : ℝ) + 1 ∧ b < (j : ℝ) + 1 ∧ c < (j : ℝ) + 1 ∧ d < (j : ℝ) + 1 := by
  obtain ⟨j, hj⟩ := exists_nat_gt (max (max a b) (max c d))
  have h0 : ((j : ℕ) : ℝ) < (j : ℝ) + 1 := by linarith only []
  refine ⟨j, ?_, ?_, ?_, ?_⟩
  · exact lt_trans (lt_of_le_of_lt (le_trans (le_max_left a b) (le_max_left _ _)) hj) h0
  · exact lt_trans (lt_of_le_of_lt (le_trans (le_max_right a b) (le_max_left _ _)) hj) h0
  · exact lt_trans (lt_of_le_of_lt (le_trans (le_max_left c d) (le_max_right _ _)) hj) h0
  · exact lt_trans (lt_of_le_of_lt (le_trans (le_max_right c d) (le_max_right _ _)) hj) h0

theorem exists_subset_planeBox_prod {C : Set ((ℝ × ℝ) × ℝ)} (hC : IsCompact C)
    (hCsub : ∀ q ∈ C, q.2 ≤ -1) :
    ∃ j : ℕ, C ⊆ planeBox j ×ˢ planeTimeInterval j := by
  rcases C.eq_empty_or_nonempty with hempty | hne
  · exact ⟨0, by rw [hempty]; exact empty_subset _⟩
  obtain ⟨p, hpC, hpmin⟩ := hC.exists_isMinOn hne
    (continuous_fst.comp continuous_fst).abs.continuousOn
  obtain ⟨q, hqC, hqmax⟩ := hC.exists_isMaxOn hne
    (continuous_fst.comp continuous_fst).abs.continuousOn
  obtain ⟨r, hrC, hrmax⟩ := hC.exists_isMaxOn hne
    (continuous_snd.comp continuous_fst).abs.continuousOn
  obtain ⟨s, hsC, hsmin⟩ := hC.exists_isMinOn hne continuous_snd.continuousOn
  let M := max (max (|q.1.1|) (|r.1.2|)) (-s.2)
  obtain ⟨j, hj⟩ := exists_nat_gt M
  have hq_bound : |q.1.1| < (j : ℝ) + 1 := by
    have hle : |q.1.1| ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
    have hpos : (j : ℝ) < (j : ℝ) + 1 := by linarith only []
    linarith only [hle, hj, hpos]
  have hr_bound : |r.1.2| < (j : ℝ) + 1 := by
    have hle : |r.1.2| ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
    have hpos : (j : ℝ) < (j : ℝ) + 1 := by linarith only []
    linarith only [hle, hj, hpos]
  have hs_bound : -s.2 < (j : ℝ) + 1 := by
    have hle : -s.2 ≤ M := le_max_right _ _
    have hpos : (j : ℝ) < (j : ℝ) + 1 := by linarith only []
    linarith only [hle, hj, hpos]
  have hqmax_on : ∀ x ∈ C, |x.1.1| ≤ |q.1.1| := fun x hx => isMaxOn_iff.mp hqmax x hx
  have hrmax_on : ∀ x ∈ C, |x.1.2| ≤ |r.1.2| := fun x hx => isMaxOn_iff.mp hrmax x hx
  have hsmin_on : ∀ x ∈ C, s.2 ≤ x.2 := fun x hx => isMinOn_iff.mp hsmin x hx
  refine ⟨j, fun x hx => ?_⟩
  have hx1 : |x.1.1| < (j : ℝ) + 1 := lt_of_le_of_lt (hqmax_on x hx) hq_bound
  have hx2 : |x.1.2| < (j : ℝ) + 1 := lt_of_le_of_lt (hrmax_on x hx) hr_bound
  have hx3 : -((j : ℝ) + 1) < x.2 := by
    have h := hsmin_on x hx
    have hs_lt : s.2 > -((j : ℝ) + 1) := by linarith only [hs_bound]
    linarith only [h, hs_lt]
  have hx_tau_le : x.2 ≤ -1 := hCsub x hx
  have hx1_abs := abs_lt.mp hx1
  have hx2_abs := abs_lt.mp hx2
  have hx_mem_planeBox : x.1 ∈ planeBox j := by
    rw [planeBox, Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
    exact ⟨⟨hx1_abs.1.le, hx1_abs.2.le⟩, ⟨hx2_abs.1.le, hx2_abs.2.le⟩⟩
  have hx_mem_time : x.2 ∈ planeTimeInterval j := by
    rw [planeTimeInterval, Set.mem_Icc]
    exact ⟨hx3.le, hx_tau_le⟩
  exact Set.mem_prod.mpr ⟨hx_mem_planeBox, hx_mem_time⟩

theorem planeBox_subset_interior_biggerBox (j : ℕ) :
    planeBox j ⊆ interior (planeBox (j + 1)) := by
  rw [planeBox, planeBox]
  have hleft : -((((j : ℕ) + 1 : ℕ) : ℝ) + 1) < -(((j : ℝ) + 1)) := by
    push_cast
    linarith only []
  have hright : ((j : ℝ) + 1) < ((((j : ℕ) + 1 : ℕ) : ℝ) + 1) := by
    push_cast
    linarith only []
  rw [interior_prod_eq, interior_Icc]
  refine Set.prod_mono (Icc_subset_Ioo hleft hright) (Icc_subset_Ioo hleft hright)

theorem exists_subseq_tendstoUniformlyOn_of_lipschitz_of_pairings_plane
    (Θ : ℕ → (ℝ × ℝ) × ℝ → ℝ)
    (hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K →
      ∀ J : Set ℝ, IsCompact J → (∀ τ ∈ J, τ ≤ -1) →
      ∃ M : ℝ, ∀ n, ∀ y ∈ K, ∀ τ ∈ J, |Θ n (y, τ)| ≤ M)
    (hlip : ∀ K : Set (ℝ × ℝ), IsCompact K →
      ∀ J : Set ℝ, IsCompact J → (∀ τ ∈ J, τ ≤ -1) →
      ∃ L : ℝ, ∀ n, ∀ τ ∈ J, LipschitzOnWith (Real.toNNReal L) (fun y => Θ n (y, τ)) K)
    (hpair : ∀ K : Set (ℝ × ℝ), IsCompact K →
      ∀ J : Set ℝ, IsCompact J → (∀ τ ∈ J, τ ≤ -1) →
      ∃ Cₒ : ℝ, 0 ≤ Cₒ ∧
        ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ interior K →
        ∀ B : ℝ, 0 ≤ B →
          (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
          ∀ n : ℕ, ∀ τ ∈ J, ∀ τ' ∈ J,
            |∫ y, (Θ n (y, τ) - Θ n (y, τ')) * ψ y| ≤ Cₒ * B * |τ - τ'|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ω : (ℝ × ℝ) × ℝ → ℝ,
      ContinuousOn Ω {q : (ℝ × ℝ) × ℝ | q.2 ≤ -1} ∧
      ∀ C : Set ((ℝ × ℝ) × ℝ), IsCompact C → C ⊆ {q : (ℝ × ℝ) × ℝ | q.2 ≤ -1} →
        TendstoUniformlyOn (fun n => Θ (φ n)) Ω atTop C := by
  classical
  have hMex : ∀ j : ℕ, ∃ M : ℝ, ∀ n, ∀ y ∈ planeBox (j + 1), ∀ τ ∈ planeTimeInterval j,
      |Θ n (y, τ)| ≤ M := fun j =>
    hbdd (planeBox (j + 1)) (isCompact_planeBox (j + 1)) (planeTimeInterval j)
      (isCompact_planeTimeInterval j) (fun τ hτ => le_of_mem_planeTimeInterval hτ)
  choose Mc hMc using hMex
  have hLex : ∀ j : ℕ, ∃ L : ℝ, ∀ n, ∀ τ ∈ planeTimeInterval j,
      LipschitzOnWith (Real.toNNReal L) (fun y => Θ n (y, τ)) (planeBox (j + 1)) := fun j =>
    hlip (planeBox (j + 1)) (isCompact_planeBox (j + 1)) (planeTimeInterval j)
      (isCompact_planeTimeInterval j) (fun τ hτ => le_of_mem_planeTimeInterval hτ)
  choose Lc hLc using hLex
  have hPc : ∀ j : ℕ, ∃ Cₒ : ℝ, 0 ≤ Cₒ ∧
      ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ interior (planeBox (j + 1)) → ∀ B : ℝ, 0 ≤ B →
      (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
      ∀ n : ℕ, ∀ τ ∈ planeTimeInterval j, ∀ τ' ∈ planeTimeInterval j,
        |∫ y, (Θ n (y, τ) - Θ n (y, τ')) * ψ y| ≤ Cₒ * B * |τ - τ'| := fun j =>
    hpair (planeBox (j + 1)) (isCompact_planeBox (j + 1)) (planeTimeInterval j)
      (isCompact_planeTimeInterval j) (fun τ hτ => le_of_mem_planeTimeInterval hτ)
  have hmod : ∀ j : ℕ, ∀ ε > 0, ∃ δ > 0, ∀ n,
      ∀ p ∈ planeBox j ×ˢ planeTimeInterval j, ∀ q ∈ planeBox j ×ˢ planeTimeInterval j,
        dist p q < δ → |Θ n p - Θ n q| ≤ ε := fun j =>
    exists_modulus_of_lipschitz_of_pairings (planeBox (j + 1)) (isCompact_planeBox (j + 1))
      (planeTimeInterval j) Θ (Lc j) (hLc j) (hPc j) (planeBox j)
      (isCompact_planeBox j) (planeBox_subset_interior_biggerBox j)
  have hstep : ∀ (j : ℕ) (g : ℕ → ℕ), StrictMono g →
      ∃ g' : ℕ → ℕ, StrictMono g' ∧ ∃ w : (ℝ × ℝ) × ℝ → ℝ,
        TendstoUniformlyOn (fun n => Θ (g (g' n))) w atTop
          (planeBox j ×ˢ planeTimeInterval j) := by
    intro j g _
    obtain ⟨Cₒ, hCₒ, hC⟩ := hPc j
    obtain ⟨g', hg'mono, w, -, hw⟩ :=
      exists_subseq_tendstoUniformlyOn_prod (planeBox (j + 1)) (isCompact_planeBox (j + 1))
        (planeTimeInterval j) (isCompact_planeTimeInterval j) (fun n => Θ (g n)) (Mc j) (Lc j)
        (fun n => hMc j (g n)) (fun n => hLc j (g n))
        ⟨Cₒ, hCₒ, fun ψ h1 h2 h3 B hB hB' n => hC ψ h1 h2 h3 B hB hB' (g n)⟩
        (planeBox j) (isCompact_planeBox j) (planeBox_subset_interior_biggerBox j)
    exact ⟨g', hg'mono, w, hw⟩
  obtain ⟨φ, hφmono, Ω, hΩ⟩ :=
    exists_subseq_tendstoUniformlyOn_forall
      (fun j => planeBox j ×ˢ planeTimeInterval j) Θ hstep
  have hcontbox : ∀ j : ℕ, ContinuousOn Ω (planeBox j ×ˢ planeTimeInterval j) := by
    intro j
    refine (hΩ j).continuousOn (Filter.Eventually.frequently
      (Filter.Eventually.of_forall fun n => ?_))
    refine continuousOn_of_modulus _ (Θ (φ n)) fun ε hε => ?_
    obtain ⟨δ, hδ, hd⟩ := hmod j ε hε
    exact ⟨δ, hδ, fun x hx y hy hxy => hd (φ n) x hx y hy hxy⟩
  refine ⟨φ, hφmono, Ω, ?_, ?_⟩
  · intro q hq
    have hqτ : q.2 ≤ -1 := hq
    obtain ⟨j, hj1, hj2, hj3, hj4⟩ :=
      exists_nat_add_one_gt_four (|q.1.1|) (|q.1.2|) (-q.2) (-q.2)
    obtain ⟨hz1, hz2⟩ := abs_lt.mp hj2
    obtain ⟨hq1l, hq1u⟩ := abs_lt.mp hj1
    obtain ⟨hq2l, hq2u⟩ := abs_lt.mp hj2
    obtain ⟨U, hUopen, hqU, hUsub⟩ :
        ∃ U : Set ((ℝ × ℝ) × ℝ), IsOpen U ∧ q ∈ U ∧
          {x : (ℝ × ℝ) × ℝ | x.2 ≤ -1} ∩ U
            ⊆ planeBox j ×ˢ planeTimeInterval j := by
      refine ⟨(Ioo (-((j : ℝ) + 1)) ((j : ℝ) + 1) ×ˢ Ioo (-((j : ℝ) + 1)) ((j : ℝ) + 1)) ×ˢ
        Ioi (-((j : ℝ) + 1)), (isOpen_Ioo.prod isOpen_Ioo).prod isOpen_Ioi,
        ⟨⟨⟨hq1l, hq1u⟩, ⟨hq2l, hq2u⟩⟩, Set.mem_Ioi.mpr (by linarith only [hj4])⟩, fun x hx => ?_⟩
      obtain ⟨hx_dom, hx_U⟩ := hx
      rw [Set.mem_prod] at hx_U
      obtain ⟨hxU1, hxU2⟩ := hx_U
      rw [Set.mem_prod] at hxU1
      obtain ⟨hxU11, hxU12⟩ := hxU1
      rw [Set.mem_Ioo] at hxU11 hxU12
      rw [Set.mem_Ioi] at hxU2
      have hx1l := hxU11.1
      have hx1u := hxU11.2
      have hx2l := hxU12.1
      have hx2u := hxU12.2
      have hxτ' := hxU2
      rw [planeBox, planeTimeInterval, Set.mem_prod]
      have hmem_planeBox : x.1 ∈ planeBox j := by
        rw [planeBox, Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
        exact ⟨⟨hx1l.le, hx1u.le⟩, ⟨hx2l.le, hx2u.le⟩⟩
      have hx_time_le : x.2 ≤ -1 := hx_dom
      have hmem_time : x.2 ∈ planeTimeInterval j := by
        rw [planeTimeInterval, Set.mem_Icc]
        exact ⟨le_of_lt hxτ', hx_time_le⟩
      exact Set.mem_prod.mpr ⟨hmem_planeBox, hmem_time⟩
    have hmem : q ∈ planeBox j ×ˢ planeTimeInterval j := hUsub ⟨hq, hqU⟩
    have hcw : ContinuousWithinAt Ω ({x : (ℝ × ℝ) × ℝ | x.2 ≤ -1} ∩ U) q :=
      (hcontbox j q hmem).mono hUsub
    rwa [continuousWithinAt_inter (hUopen.mem_nhds hqU)] at hcw
  · intro C hC hCsub
    obtain ⟨j, hj⟩ := exists_subset_planeBox_prod hC fun q hq => hCsub hq
    exact (hΩ j).mono hj

/-- A version of `exists_subseq_tendstoUniformlyOn_of_lipschitz_of_pairings_plane` where the
three hypotheses hold only eventually (for large `n`), with the threshold chosen before the
test function `ψ` and its bound `B` in `hpair` — matching the shape `hbdd`/`hlip` already use
(the constant `M`/`L`/`Cₒ` and the eventual threshold are both chosen before the data they
bound). For each box of the exhaustion the three eventual thresholds combine into one common
threshold beyond which all three bounds hold with all-`n` shape; a modified sequence, zero
before that threshold and equal to `Θ` after, then lets the original all-`n` theorem apply
directly, and since uniform limits only depend on the tail, the extracted subsequence also
converges for the original `Θ`. -/
theorem exists_subseq_tendstoUniformlyOn_of_lipschitz_of_pairings_plane_eventually
    (Θ : ℕ → (ℝ × ℝ) × ℝ → ℝ)
    (hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K →
      ∀ J : Set ℝ, IsCompact J → (∀ τ ∈ J, τ ≤ -1) →
      ∃ M : ℝ, ∀ᶠ n in atTop, ∀ y ∈ K, ∀ τ ∈ J, |Θ n (y, τ)| ≤ M)
    (hlip : ∀ K : Set (ℝ × ℝ), IsCompact K →
      ∀ J : Set ℝ, IsCompact J → (∀ τ ∈ J, τ ≤ -1) →
      ∃ L : ℝ, ∀ᶠ n in atTop, ∀ τ ∈ J, LipschitzOnWith (Real.toNNReal L) (fun y => Θ n (y, τ)) K)
    (hpair : ∀ K : Set (ℝ × ℝ), IsCompact K →
      ∀ J : Set ℝ, IsCompact J → (∀ τ ∈ J, τ ≤ -1) →
      ∃ Cₒ : ℝ, 0 ≤ Cₒ ∧ ∀ᶠ n in atTop,
        ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ interior K →
        ∀ B : ℝ, 0 ≤ B →
          (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
          ∀ τ ∈ J, ∀ τ' ∈ J,
            |∫ y, (Θ n (y, τ) - Θ n (y, τ')) * ψ y| ≤ Cₒ * B * |τ - τ'|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ω : (ℝ × ℝ) × ℝ → ℝ,
      ContinuousOn Ω {q : (ℝ × ℝ) × ℝ | q.2 ≤ -1} ∧
      ∀ C : Set ((ℝ × ℝ) × ℝ), IsCompact C → C ⊆ {q : (ℝ × ℝ) × ℝ | q.2 ≤ -1} →
        TendstoUniformlyOn (fun n => Θ (φ n)) Ω atTop C := by
  classical
  have hMex : ∀ j : ℕ, ∃ M : ℝ, ∀ᶠ n in atTop, ∀ y ∈ planeBox (j + 1),
      ∀ τ ∈ planeTimeInterval j, |Θ n (y, τ)| ≤ M := fun j =>
    hbdd (planeBox (j + 1)) (isCompact_planeBox (j + 1)) (planeTimeInterval j)
      (isCompact_planeTimeInterval j) (fun τ hτ => le_of_mem_planeTimeInterval hτ)
  choose Mc hMc using hMex
  have hLex : ∀ j : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ τ ∈ planeTimeInterval j,
      LipschitzOnWith (Real.toNNReal L) (fun y => Θ n (y, τ)) (planeBox (j + 1)) := fun j =>
    hlip (planeBox (j + 1)) (isCompact_planeBox (j + 1)) (planeTimeInterval j)
      (isCompact_planeTimeInterval j) (fun τ hτ => le_of_mem_planeTimeInterval hτ)
  choose Lc hLc using hLex
  have hPc : ∀ j : ℕ, ∃ Cₒ : ℝ, 0 ≤ Cₒ ∧ ∀ᶠ n in atTop,
      ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ interior (planeBox (j + 1)) → ∀ B : ℝ, 0 ≤ B →
      (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
      ∀ τ ∈ planeTimeInterval j, ∀ τ' ∈ planeTimeInterval j,
        |∫ y, (Θ n (y, τ) - Θ n (y, τ')) * ψ y| ≤ Cₒ * B * |τ - τ'| := fun j =>
    hpair (planeBox (j + 1)) (isCompact_planeBox (j + 1)) (planeTimeInterval j)
      (isCompact_planeTimeInterval j) (fun τ hτ => le_of_mem_planeTimeInterval hτ)
  choose Cc hCc0 hCc using hPc
  -- Combine the three eventual thresholds on box `j` into one, `Nc j`.
  have hN : ∀ j : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      (∀ y ∈ planeBox (j + 1), ∀ τ ∈ planeTimeInterval j, |Θ n (y, τ)| ≤ Mc j) ∧
      (∀ τ ∈ planeTimeInterval j,
        LipschitzOnWith (Real.toNNReal (Lc j)) (fun y => Θ n (y, τ)) (planeBox (j + 1))) ∧
      (∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ interior (planeBox (j + 1)) → ∀ B : ℝ, 0 ≤ B →
        (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
        ∀ τ ∈ planeTimeInterval j, ∀ τ' ∈ planeTimeInterval j,
          |∫ y, (Θ n (y, τ) - Θ n (y, τ')) * ψ y| ≤ Cc j * B * |τ - τ'|) := by
    intro j
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp (hMc j)
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (hLc j)
    obtain ⟨N3, hN3⟩ := Filter.eventually_atTop.mp (hCc j)
    refine ⟨max N1 (max N2 N3), fun n hn => ⟨?_, ?_, ?_⟩⟩
    · exact hN1 n (le_trans (le_max_left _ _) hn)
    · exact hN2 n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
    · exact hN3 n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)
  choose Nc hNc using hN
  have hMc_bound : ∀ j n, Nc j ≤ n →
      ∀ y ∈ planeBox (j + 1), ∀ τ ∈ planeTimeInterval j, |Θ n (y, τ)| ≤ Mc j :=
    fun j n hn => (hNc j n hn).1
  have hLc_bound : ∀ j n, Nc j ≤ n →
      ∀ τ ∈ planeTimeInterval j,
        LipschitzOnWith (Real.toNNReal (Lc j)) (fun y => Θ n (y, τ)) (planeBox (j + 1)) :=
    fun j n hn => (hNc j n hn).2.1
  have hCc_bound : ∀ j n, Nc j ≤ n → ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ interior (planeBox (j + 1)) → ∀ B : ℝ, 0 ≤ B →
      (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
      ∀ τ ∈ planeTimeInterval j, ∀ τ' ∈ planeTimeInterval j,
        |∫ y, (Θ n (y, τ) - Θ n (y, τ')) * ψ y| ≤ Cc j * B * |τ - τ'| :=
    fun j n hn => (hNc j n hn).2.2
  have hstep : ∀ (j : ℕ) (g : ℕ → ℕ), StrictMono g →
      ∃ g' : ℕ → ℕ, StrictMono g' ∧ ∃ w : (ℝ × ℝ) × ℝ → ℝ,
        TendstoUniformlyOn (fun n => Θ (g (g' n))) w atTop
          (planeBox j ×ˢ planeTimeInterval j) := by
    intro j g hg
    set N := Nc j with hNdef
    set Θ' : ℕ → (ℝ × ℝ) × ℝ → ℝ := fun n => if n < N then 0 else Θ n with hΘ'def
    have hMc_nonneg : 0 ≤ Mc j :=
      le_trans (abs_nonneg _)
        (hMc_bound j N (le_refl N) 0 (zero_mem_planeBox (j + 1)) (-((j : ℝ) + 1))
          (left_mem_planeTimeInterval j))
    have hbdd' : ∀ n, ∀ y ∈ planeBox (j + 1), ∀ τ ∈ planeTimeInterval j, |Θ' n (y, τ)| ≤ Mc j := by
      intro n y hy τ hτ
      dsimp only [Θ']
      split
      · simpa using hMc_nonneg
      · exact hMc_bound j n (by omega) y hy τ hτ
    have hlip' : ∀ n, ∀ τ ∈ planeTimeInterval j,
        LipschitzOnWith (Real.toNNReal (Lc j)) (fun y => Θ' n (y, τ)) (planeBox (j + 1)) := by
      intro n τ hτ
      dsimp only [Θ']
      split
      · exact (LipschitzWith.const' (0 : ℝ)).lipschitzOnWith
      · exact hLc_bound j n (by omega) τ hτ
    have hpair' : ∃ Cₒ : ℝ, 0 ≤ Cₒ ∧
        ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ interior (planeBox (j + 1)) → ∀ B : ℝ, 0 ≤ B →
        (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
        ∀ n : ℕ, ∀ τ ∈ planeTimeInterval j, ∀ τ' ∈ planeTimeInterval j,
          |∫ y, (Θ' n (y, τ) - Θ' n (y, τ')) * ψ y| ≤ Cₒ * B * |τ - τ'| := by
      refine ⟨Cc j, hCc0 j, fun ψ hψ1 hψ2 hψ3 B hB hB' n τ hτ τ' hτ' => ?_⟩
      dsimp only [Θ']
      split
      · simp only [Pi.zero_apply, sub_self, zero_mul, MeasureTheory.integral_zero, abs_zero]
        exact mul_nonneg (mul_nonneg (hCc0 j) hB) (abs_nonneg _)
      · exact hCc_bound j n (by omega) ψ hψ1 hψ2 hψ3 B hB hB' τ hτ τ' hτ'
    obtain ⟨g', hg'mono, w, -, hw⟩ :=
      exists_subseq_tendstoUniformlyOn_prod (planeBox (j + 1)) (isCompact_planeBox (j + 1))
        (planeTimeInterval j) (isCompact_planeTimeInterval j) (fun n => Θ' (g n)) (Mc j) (Lc j)
        (fun n => hbdd' (g n)) (fun n => hlip' (g n))
        (by
          obtain ⟨Cₒ, hCₒ, hC⟩ := hpair'
          exact ⟨Cₒ, hCₒ, fun ψ h1 h2 h3 B hB hB' n => hC ψ h1 h2 h3 B hB hB' (g n)⟩)
        (planeBox j) (isCompact_planeBox j) (planeBox_subset_interior_biggerBox j)
    have h_limit : TendstoUniformlyOn (fun n => Θ (g (g' n))) w atTop
        (planeBox j ×ˢ planeTimeInterval j) := by
      apply hw.congr
      filter_upwards [Filter.eventually_ge_atTop N] with n hn p _
      have hge : ¬ g (g' n) < N := by
        have h1 : n ≤ g' n := hg'mono.le_apply
        have h2 : g' n ≤ g (g' n) := hg.le_apply
        omega
      change Θ' (g (g' n)) p = Θ (g (g' n)) p
      dsimp only [Θ']
      split_ifs
      rfl
    exact ⟨g', hg'mono, w, h_limit⟩
  obtain ⟨φ, hφmono, Ω, hΩ⟩ :=
    exists_subseq_tendstoUniformlyOn_forall
      (fun j => planeBox j ×ˢ planeTimeInterval j) Θ hstep
  have hcontbox : ∀ j : ℕ, ContinuousOn Ω (planeBox j ×ˢ planeTimeInterval j) := by
    intro j
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp (hMc j)
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (hLc j)
    obtain ⟨N3, hN3⟩ := Filter.eventually_atTop.mp (hCc j)
    set N := max N1 (max N2 N3) with hNdef
    have hN2N : N2 ≤ N := le_trans (le_max_left N2 N3) (le_max_right N1 (max N2 N3))
    have hN3N : N3 ≤ N := le_trans (le_max_right N2 N3) (le_max_right N1 (max N2 N3))
    have hlipTail : ∀ n : ℕ, ∀ τ ∈ planeTimeInterval j,
        LipschitzOnWith (Real.toNNReal (Lc j)) (fun y => Θ (n + N) (y, τ)) (planeBox (j + 1)) :=
      fun n τ hτ => hN2 (n + N) (le_trans hN2N (Nat.le_add_left N n)) τ hτ
    have hpairTail : ∃ Cₒ : ℝ, 0 ≤ Cₒ ∧
        ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ interior (planeBox (j + 1)) → ∀ B : ℝ, 0 ≤ B →
        (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
        ∀ n : ℕ, ∀ τ ∈ planeTimeInterval j, ∀ τ' ∈ planeTimeInterval j,
          |∫ y, (Θ (n + N) (y, τ) - Θ (n + N) (y, τ')) * ψ y| ≤ Cₒ * B * |τ - τ'| :=
      ⟨Cc j, hCc0 j, fun ψ hψ1 hψ2 hψ3 B hB hB' n =>
        hN3 (n + N) (le_trans hN3N (Nat.le_add_left N n)) ψ hψ1 hψ2 hψ3 B hB hB'⟩
    have hmodTail : ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ p ∈ planeBox j ×ˢ planeTimeInterval j,
        ∀ q ∈ planeBox j ×ˢ planeTimeInterval j, dist p q < δ →
          |Θ (n + N) p - Θ (n + N) q| ≤ ε := fun ε hε =>
      exists_modulus_of_lipschitz_of_pairings (planeBox (j + 1)) (isCompact_planeBox (j + 1))
        (planeTimeInterval j) (fun n => Θ (n + N)) (Lc j) hlipTail hpairTail (planeBox j)
        (isCompact_planeBox j) (planeBox_subset_interior_biggerBox j) ε hε
    refine (hΩ j).continuousOn (Filter.Eventually.frequently ?_)
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hφnN : N ≤ φ n := le_trans hn hφmono.le_apply
    refine continuousOn_of_modulus _ (Θ (φ n)) fun ε hε => ?_
    obtain ⟨δ, hδ, hd⟩ := hmodTail ε hε
    refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
    have h := hd (φ n - N) x hx y hy hxy
    rwa [Nat.sub_add_cancel hφnN] at h
  refine ⟨φ, hφmono, Ω, ?_, ?_⟩
  · intro q hq
    have hqτ : q.2 ≤ -1 := hq
    obtain ⟨j, hj1, hj2, hj3, hj4⟩ :=
      exists_nat_add_one_gt_four (|q.1.1|) (|q.1.2|) (-q.2) (-q.2)
    obtain ⟨hz1, hz2⟩ := abs_lt.mp hj2
    obtain ⟨hq1l, hq1u⟩ := abs_lt.mp hj1
    obtain ⟨hq2l, hq2u⟩ := abs_lt.mp hj2
    obtain ⟨U, hUopen, hqU, hUsub⟩ :
        ∃ U : Set ((ℝ × ℝ) × ℝ), IsOpen U ∧ q ∈ U ∧
          {x : (ℝ × ℝ) × ℝ | x.2 ≤ -1} ∩ U
            ⊆ planeBox j ×ˢ planeTimeInterval j := by
      refine ⟨(Ioo (-((j : ℝ) + 1)) ((j : ℝ) + 1) ×ˢ Ioo (-((j : ℝ) + 1)) ((j : ℝ) + 1)) ×ˢ
        Ioi (-((j : ℝ) + 1)), (isOpen_Ioo.prod isOpen_Ioo).prod isOpen_Ioi,
        ⟨⟨⟨hq1l, hq1u⟩, ⟨hq2l, hq2u⟩⟩, Set.mem_Ioi.mpr (by linarith only [hj4])⟩, fun x hx => ?_⟩
      obtain ⟨hx_dom, hx_U⟩ := hx
      rw [Set.mem_prod] at hx_U
      obtain ⟨hxU1, hxU2⟩ := hx_U
      rw [Set.mem_prod] at hxU1
      obtain ⟨hxU11, hxU12⟩ := hxU1
      rw [Set.mem_Ioo] at hxU11 hxU12
      rw [Set.mem_Ioi] at hxU2
      have hx1l := hxU11.1
      have hx1u := hxU11.2
      have hx2l := hxU12.1
      have hx2u := hxU12.2
      have hxτ' := hxU2
      rw [planeBox, planeTimeInterval, Set.mem_prod]
      have hmem_planeBox : x.1 ∈ planeBox j := by
        rw [planeBox, Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
        exact ⟨⟨hx1l.le, hx1u.le⟩, ⟨hx2l.le, hx2u.le⟩⟩
      have hx_time_le : x.2 ≤ -1 := hx_dom
      have hmem_time : x.2 ∈ planeTimeInterval j := by
        rw [planeTimeInterval, Set.mem_Icc]
        exact ⟨le_of_lt hxτ', hx_time_le⟩
      exact Set.mem_prod.mpr ⟨hmem_planeBox, hmem_time⟩
    have hmem : q ∈ planeBox j ×ˢ planeTimeInterval j := hUsub ⟨hq, hqU⟩
    have hcw : ContinuousWithinAt Ω ({x : (ℝ × ℝ) × ℝ | x.2 ≤ -1} ∩ U) q :=
      (hcontbox j q hmem).mono hUsub
    rwa [continuousWithinAt_inter (hUopen.mem_nhds hqU)] at hcw
  · intro C hC hCsub
    obtain ⟨j, hj⟩ := exists_subset_planeBox_prod hC fun q hq => hCsub hq
    exact (hΩ j).mono hj

end CIV
