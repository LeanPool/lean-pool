/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RecedingWholePlaneCompactness

/-!
# Locally uniform extraction on the half-plane from eventual bounds

The compactness step `eq:aniso:zoom:finite:compactness` of Step 2 of the proof of
`prop:aniso:small`, in the form in which the zoom data supply it: the uniform bound, the
uniform spatial Lipschitz bound and the time-pairing bound on a compact subset of the open
half-plane hold only for all large `n` (the zoom preimage of the unit cylinder exhausts the
half-plane only as `n → ∞`). This is the half-plane counterpart of
`CIV.exists_subseq_tendstoUniformlyOn_of_lipschitz_of_pairings_plane_eventually`, and the
eventual counterpart of `CIV.exists_subseq_tendstoUniformlyOn_of_lipschitz_of_pairings`.
-/

public section

open Filter Set Topology

noncomputable section

namespace CIV

/-- The closed rectangles `[1/(j+1), j+1] × [-(j+1), j+1]` exhausting the open half-plane. -/
@[expose] def halfBox (j : ℕ) : Set (ℝ × ℝ) :=
  Icc (1 / ((j : ℝ) + 1)) ((j : ℝ) + 1) ×ˢ Icc (-((j : ℝ) + 1)) ((j : ℝ) + 1)

theorem isCompact_halfBox (j : ℕ) : IsCompact (halfBox j) := isCompact_Icc.prod isCompact_Icc

theorem pos_of_mem_halfBox {j : ℕ} {y : ℝ × ℝ} (hy : y ∈ halfBox j) : 0 < y.1 :=
  lt_of_lt_of_le (by positivity) hy.1.1

theorem one_zero_mem_halfBox (j : ℕ) : ((1 : ℝ), (0 : ℝ)) ∈ halfBox j := by
  have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  refine ⟨⟨?_, by linarith only [h0]⟩, ⟨by linarith only [h0], by linarith only [h0]⟩⟩
  rw [div_le_one (by positivity)]; linarith only [h0]

theorem halfBox_subset_interior_succ (j : ℕ) : halfBox j ⊆ interior (halfBox (j + 1)) := by
  rw [halfBox, halfBox, interior_prod_eq, interior_Icc, interior_Icc]
  have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hlo : 1 / (((j + 1 : ℕ) : ℝ) + 1) < 1 / ((j : ℝ) + 1) := by
    push_cast
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith only [])
  have hhi : (j : ℝ) + 1 < (((j + 1 : ℕ) : ℝ) + 1) := by push_cast; linarith only []
  exact prod_mono (Icc_subset_Ioo hlo hhi) (Icc_subset_Ioo (by linarith only [hhi]) hhi)

theorem left_mem_planeTimeInterval' (j : ℕ) : (-((j : ℝ) + 1)) ∈ planeTimeInterval j := by
  have h : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  exact ⟨le_refl _, by linarith only [h]⟩

theorem le_of_mem_planeTimeInterval' {j : ℕ} {τ : ℝ} (hτ : τ ∈ planeTimeInterval j) :
    τ ≤ -1 := hτ.2

/-- A point of `{R > 0}` with bounded coordinates lies strictly inside some `halfBox j`. -/
theorem exists_nat_halfBox_bounds {a b c : ℝ} (ha : 0 < a) :
    ∃ j : ℕ, 1 / ((j : ℝ) + 1) < a ∧ a < (j : ℝ) + 1 ∧ b < (j : ℝ) + 1 ∧ c < (j : ℝ) + 1 := by
  obtain ⟨j, hj⟩ := exists_nat_gt (max (max (1 / a) a) (max b c))
  have h1 : 1 / a < (j : ℝ) + 1 := by
    have := le_trans (le_max_left (1 / a) a) (le_max_left (max (1 / a) a) (max b c))
    linarith only [this, hj]
  refine ⟨j, ?_, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ ha] at h1
    linarith only [h1]
  · have := le_trans (le_max_right (1 / a) a) (le_max_left _ (max b c)); linarith only [this, hj]
  · have := le_trans (le_max_left b c) (le_max_right (max (1 / a) a) _); linarith only [this, hj]
  · have := le_trans (le_max_right b c) (le_max_right (max (1 / a) a) _); linarith only [this, hj]

/-- A compact subset of `{R > 0, τ ≤ -1}` lies in some `halfBox j ×ˢ planeTimeInterval j`. -/
theorem exists_subset_halfBox_prod {C : Set ((ℝ × ℝ) × ℝ)} (hC : IsCompact C)
    (hCsub : C ⊆ {q : (ℝ × ℝ) × ℝ | 0 < q.1.1 ∧ q.2 ≤ -1}) :
    ∃ j : ℕ, C ⊆ halfBox j ×ˢ planeTimeInterval j := by
  rcases C.eq_empty_or_nonempty with hempty | hne
  · exact ⟨0, by rw [hempty]; exact empty_subset _⟩
  obtain ⟨p, hpC, hpmin⟩ := hC.exists_isMinOn hne
    (continuous_fst.comp continuous_fst).continuousOn
  obtain ⟨B, hB⟩ := hC.isBounded.exists_norm_le
  obtain ⟨j, hj1, -, hj3, hj4⟩ := exists_nat_halfBox_bounds (b := B) (c := B) (hCsub hpC).1
  refine ⟨j, fun q hq => ?_⟩
  have hn := hB q hq
  have h1 : ‖q.1.1‖ ≤ B := le_trans (norm_fst_le q.1) (le_trans (norm_fst_le q) hn)
  have h2 : ‖q.1.2‖ ≤ B := le_trans (norm_snd_le q.1) (le_trans (norm_fst_le q) hn)
  have h3 : ‖q.2‖ ≤ B := le_trans (norm_snd_le q) hn
  rw [Real.norm_eq_abs] at h1 h2 h3
  have hmin : p.1.1 ≤ q.1.1 := hpmin hq
  refine ⟨⟨⟨by linarith only [hj1, hmin], by linarith only [(abs_le.mp h1).2, hj3]⟩,
    ⟨by linarith only [(abs_le.mp h2).1, hj3], by linarith only [(abs_le.mp h2).2, hj3]⟩⟩,
    ⟨by linarith only [(abs_le.mp h3).1, hj4], (hCsub hq).2⟩⟩

/-- `eq:aniso:zoom:finite:compactness` from eventual bounds: a sequence which on every compact
subset of the open half-plane and every compact time set in `(-∞, -1]` is eventually uniformly
bounded, eventually uniformly Lipschitz in space and eventually obeys the pairing bound in time,
has a subsequence converging uniformly on every compact subset of `{R > 0} × ℝ × (-∞, -1]`, to a
limit continuous there. -/
theorem exists_subseq_tendstoUniformlyOn_of_lipschitz_of_pairings_eventually
    (Θ : ℕ → (ℝ × ℝ) × ℝ → ℝ)
    (hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K → (∀ y ∈ K, 0 < y.1) →
      ∀ J : Set ℝ, IsCompact J → (∀ τ ∈ J, τ ≤ -1) →
      ∃ M : ℝ, ∀ᶠ n in atTop, ∀ y ∈ K, ∀ τ ∈ J, |Θ n (y, τ)| ≤ M)
    (hlip : ∀ K : Set (ℝ × ℝ), IsCompact K → (∀ y ∈ K, 0 < y.1) →
      ∀ J : Set ℝ, IsCompact J → (∀ τ ∈ J, τ ≤ -1) →
      ∃ L : ℝ, ∀ᶠ n in atTop, ∀ τ ∈ J, LipschitzOnWith (Real.toNNReal L) (fun y => Θ n (y, τ)) K)
    (hpair : ∀ K : Set (ℝ × ℝ), IsCompact K → (∀ y ∈ K, 0 < y.1) →
      ∀ J : Set ℝ, IsCompact J → (∀ τ ∈ J, τ ≤ -1) →
      ∃ Cₒ : ℝ, 0 ≤ Cₒ ∧ ∀ᶠ n in atTop,
        ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ interior K →
        ∀ B : ℝ, 0 ≤ B →
          (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
          ∀ τ ∈ J, ∀ τ' ∈ J,
            |∫ y, (Θ n (y, τ) - Θ n (y, τ')) * ψ y| ≤ Cₒ * B * |τ - τ'|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ω : (ℝ × ℝ) × ℝ → ℝ,
      ContinuousOn Ω {q : (ℝ × ℝ) × ℝ | 0 < q.1.1 ∧ q.2 ≤ -1} ∧
      ∀ C : Set ((ℝ × ℝ) × ℝ), IsCompact C → C ⊆ {q : (ℝ × ℝ) × ℝ | 0 < q.1.1 ∧ q.2 ≤ -1} →
        TendstoUniformlyOn (fun n => Θ (φ n)) Ω atTop C := by
  classical
  have hMex : ∀ j : ℕ, ∃ M : ℝ, ∀ᶠ n in atTop, ∀ y ∈ halfBox (j + 1),
      ∀ τ ∈ planeTimeInterval j, |Θ n (y, τ)| ≤ M := fun j =>
    hbdd (halfBox (j + 1)) (isCompact_halfBox (j + 1)) (fun y hy => pos_of_mem_halfBox hy)
      (planeTimeInterval j)
      (isCompact_planeTimeInterval j) (fun τ hτ => le_of_mem_planeTimeInterval' hτ)
  choose Mc hMc using hMex
  have hLex : ∀ j : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ τ ∈ planeTimeInterval j,
      LipschitzOnWith (Real.toNNReal L) (fun y => Θ n (y, τ)) (halfBox (j + 1)) := fun j =>
    hlip (halfBox (j + 1)) (isCompact_halfBox (j + 1)) (fun y hy => pos_of_mem_halfBox hy)
      (planeTimeInterval j)
      (isCompact_planeTimeInterval j) (fun τ hτ => le_of_mem_planeTimeInterval' hτ)
  choose Lc hLc using hLex
  have hPc : ∀ j : ℕ, ∃ Cₒ : ℝ, 0 ≤ Cₒ ∧ ∀ᶠ n in atTop,
      ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ interior (halfBox (j + 1)) → ∀ B : ℝ, 0 ≤ B →
      (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
      ∀ τ ∈ planeTimeInterval j, ∀ τ' ∈ planeTimeInterval j,
        |∫ y, (Θ n (y, τ) - Θ n (y, τ')) * ψ y| ≤ Cₒ * B * |τ - τ'| := fun j =>
    hpair (halfBox (j + 1)) (isCompact_halfBox (j + 1)) (fun y hy => pos_of_mem_halfBox hy)
      (planeTimeInterval j)
      (isCompact_planeTimeInterval j) (fun τ hτ => le_of_mem_planeTimeInterval' hτ)
  choose Cc hCc0 hCc using hPc
  -- Combine the three eventual thresholds on box `j` into one, `Nc j`.
  have hN : ∀ j : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      (∀ y ∈ halfBox (j + 1), ∀ τ ∈ planeTimeInterval j, |Θ n (y, τ)| ≤ Mc j) ∧
      (∀ τ ∈ planeTimeInterval j,
        LipschitzOnWith (Real.toNNReal (Lc j)) (fun y => Θ n (y, τ)) (halfBox (j + 1))) ∧
      (∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ interior (halfBox (j + 1)) → ∀ B : ℝ, 0 ≤ B →
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
      ∀ y ∈ halfBox (j + 1), ∀ τ ∈ planeTimeInterval j, |Θ n (y, τ)| ≤ Mc j :=
    fun j n hn => (hNc j n hn).1
  have hLc_bound : ∀ j n, Nc j ≤ n →
      ∀ τ ∈ planeTimeInterval j,
        LipschitzOnWith (Real.toNNReal (Lc j)) (fun y => Θ n (y, τ)) (halfBox (j + 1)) :=
    fun j n hn => (hNc j n hn).2.1
  have hCc_bound : ∀ j n, Nc j ≤ n → ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ interior (halfBox (j + 1)) → ∀ B : ℝ, 0 ≤ B →
      (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
      ∀ τ ∈ planeTimeInterval j, ∀ τ' ∈ planeTimeInterval j,
        |∫ y, (Θ n (y, τ) - Θ n (y, τ')) * ψ y| ≤ Cc j * B * |τ - τ'| :=
    fun j n hn => (hNc j n hn).2.2
  have hstep : ∀ (j : ℕ) (g : ℕ → ℕ), StrictMono g →
      ∃ g' : ℕ → ℕ, StrictMono g' ∧ ∃ w : (ℝ × ℝ) × ℝ → ℝ,
        TendstoUniformlyOn (fun n => Θ (g (g' n))) w atTop
          (halfBox j ×ˢ planeTimeInterval j) := by
    intro j g hg
    set N := Nc j with hNdef
    set Θ' : ℕ → (ℝ × ℝ) × ℝ → ℝ := fun n => if n < N then 0 else Θ n with hΘ'def
    have hMc_nonneg : 0 ≤ Mc j :=
      le_trans (abs_nonneg _)
        (hMc_bound j N (le_refl N) ((1 : ℝ), (0 : ℝ)) (one_zero_mem_halfBox (j + 1)) (-((j : ℝ)
          + 1))
          (left_mem_planeTimeInterval' j))
    have hbdd' : ∀ n, ∀ y ∈ halfBox (j + 1), ∀ τ ∈ planeTimeInterval j, |Θ' n (y, τ)| ≤ Mc j := by
      intro n y hy τ hτ
      dsimp only [Θ']
      split
      · simpa using hMc_nonneg
      · exact hMc_bound j n (by omega) y hy τ hτ
    have hlip' : ∀ n, ∀ τ ∈ planeTimeInterval j,
        LipschitzOnWith (Real.toNNReal (Lc j)) (fun y => Θ' n (y, τ)) (halfBox (j + 1)) := by
      intro n τ hτ
      dsimp only [Θ']
      split
      · exact (LipschitzWith.const' (0 : ℝ)).lipschitzOnWith
      · exact hLc_bound j n (by omega) τ hτ
    have hpair' : ∃ Cₒ : ℝ, 0 ≤ Cₒ ∧
        ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ interior (halfBox (j + 1)) → ∀ B : ℝ, 0 ≤ B →
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
      exists_subseq_tendstoUniformlyOn_prod (halfBox (j + 1)) (isCompact_halfBox (j + 1))
        (planeTimeInterval j) (isCompact_planeTimeInterval j) (fun n => Θ' (g n)) (Mc j) (Lc j)
        (fun n => hbdd' (g n)) (fun n => hlip' (g n))
        (by
          obtain ⟨Cₒ, hCₒ, hC⟩ := hpair'
          exact ⟨Cₒ, hCₒ, fun ψ h1 h2 h3 B hB hB' n => hC ψ h1 h2 h3 B hB hB' (g n)⟩)
        (halfBox j) (isCompact_halfBox j) (halfBox_subset_interior_succ j)
    have h_limit : TendstoUniformlyOn (fun n => Θ (g (g' n))) w atTop
        (halfBox j ×ˢ planeTimeInterval j) := by
      apply hw.congr
      filter_upwards [Filter.eventually_ge_atTop N] with n hn p _
      have hge : ¬ g (g' n) < N := by
        have h1 : n ≤ g' n := hg'mono.le_apply
        have h2 : g' n ≤ g (g' n) := hg.le_apply
        omega
      show Θ' (g (g' n)) p = Θ (g (g' n)) p
      dsimp only [Θ']
      split_ifs
      rfl
    exact ⟨g', hg'mono, w, h_limit⟩
  obtain ⟨φ, hφmono, Ω, hΩ⟩ :=
    exists_subseq_tendstoUniformlyOn_forall
      (fun j => halfBox j ×ˢ planeTimeInterval j) Θ hstep
  have hcontbox : ∀ j : ℕ, ContinuousOn Ω (halfBox j ×ˢ planeTimeInterval j) := by
    intro j
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp (hMc j)
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (hLc j)
    obtain ⟨N3, hN3⟩ := Filter.eventually_atTop.mp (hCc j)
    set N := max N1 (max N2 N3) with hNdef
    have hN2N : N2 ≤ N := le_trans (le_max_left N2 N3) (le_max_right N1 (max N2 N3))
    have hN3N : N3 ≤ N := le_trans (le_max_right N2 N3) (le_max_right N1 (max N2 N3))
    have hlipTail : ∀ n : ℕ, ∀ τ ∈ planeTimeInterval j,
        LipschitzOnWith (Real.toNNReal (Lc j)) (fun y => Θ (n + N) (y, τ)) (halfBox (j + 1)) :=
      fun n τ hτ => hN2 (n + N) (le_trans hN2N (Nat.le_add_left N n)) τ hτ
    have hpairTail : ∃ Cₒ : ℝ, 0 ≤ Cₒ ∧
        ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ interior (halfBox (j + 1)) → ∀ B : ℝ, 0 ≤ B →
        (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
        ∀ n : ℕ, ∀ τ ∈ planeTimeInterval j, ∀ τ' ∈ planeTimeInterval j,
          |∫ y, (Θ (n + N) (y, τ) - Θ (n + N) (y, τ')) * ψ y| ≤ Cₒ * B * |τ - τ'| :=
      ⟨Cc j, hCc0 j, fun ψ hψ1 hψ2 hψ3 B hB hB' n =>
        hN3 (n + N) (le_trans hN3N (Nat.le_add_left N n)) ψ hψ1 hψ2 hψ3 B hB hB'⟩
    have hmodTail : ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ p ∈ halfBox j ×ˢ planeTimeInterval j,
        ∀ q ∈ halfBox j ×ˢ planeTimeInterval j, dist p q < δ →
          |Θ (n + N) p - Θ (n + N) q| ≤ ε := fun ε hε =>
      exists_modulus_of_lipschitz_of_pairings (halfBox (j + 1)) (isCompact_halfBox (j + 1))
        (planeTimeInterval j) (fun n => Θ (n + N)) (Lc j) hlipTail hpairTail (halfBox j)
        (isCompact_halfBox j) (halfBox_subset_interior_succ j) ε hε
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
    obtain ⟨hq1, hqτ⟩ := hq
    obtain ⟨j, hj1, hj2, hj3, hj4⟩ := exists_nat_halfBox_bounds (b := |q.1.2|) (c := -q.2) hq1
    obtain ⟨hq2l, hq2u⟩ := abs_lt.mp hj3
    set U : Set ((ℝ × ℝ) × ℝ) := (Ioo (1 / ((j : ℝ) + 1)) ((j : ℝ) + 1) ×ˢ
      Ioo (-((j : ℝ) + 1)) ((j : ℝ) + 1)) ×ˢ Ioi (-((j : ℝ) + 1)) with hU
    have hUopen : IsOpen U := (isOpen_Ioo.prod isOpen_Ioo).prod isOpen_Ioi
    have hqU : q ∈ U := ⟨⟨⟨hj1, hj2⟩, ⟨hq2l, hq2u⟩⟩, Set.mem_Ioi.mpr (by linarith only [hj4])⟩
    have hUsub : {x : (ℝ × ℝ) × ℝ | 0 < x.1.1 ∧ x.2 ≤ -1} ∩ U
        ⊆ halfBox j ×ˢ planeTimeInterval j := by
      rintro x ⟨hx_dom, ⟨⟨hx1, hx2⟩, hx3⟩⟩
      exact ⟨⟨⟨hx1.1.le, hx1.2.le⟩, ⟨hx2.1.le, hx2.2.le⟩⟩, ⟨le_of_lt hx3, hx_dom.2⟩⟩
    have hmem : q ∈ halfBox j ×ˢ planeTimeInterval j := hUsub ⟨⟨hq1, hqτ⟩, hqU⟩
    have hcw : ContinuousWithinAt Ω ({x : (ℝ × ℝ) × ℝ | 0 < x.1.1 ∧ x.2 ≤ -1} ∩ U) q :=
      (hcontbox j q hmem).mono hUsub
    rwa [continuousWithinAt_inter (hUopen.mem_nhds hqU)] at hcw
  · intro C hC hCsub
    obtain ⟨j, hj⟩ := exists_subset_halfBox_prod hC hCsub
    exact (hΩ j).mono hj

end CIV
