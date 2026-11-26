/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Draw9

/-!
# Counting the cuffs of a model surface, continued

Here we finish the proof that `SurfaceModel a b c` has at least `c` cuffs, and we move drawings
along
homeomorphisms.
-/

@[expose] public section

namespace GraphMinor.GM20.Draw

open Set Topology GraphMinor.Surface Metric GraphMinor.GM17

variable {a b c : ℕ}

/-- The centre of a circle, as a complex number. -/
noncomputable def cz (i : ℕ) : ℂ := ((3 * (i : ℝ) : ℝ) : ℂ)

theorem nsq (ζ : ℂ) (i : ℕ) : ‖ζ - cz i‖ ^ 2 = ((cp ζ).1 - 3 * i) ^ 2 + (cp ζ).2 ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [cz, cp, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem three_le {i j : ℕ} (h : i ≠ j) : 3 ≤ ‖cz i - cz j‖ := by
  have h₁ : cz i - cz j = ((3 * ((i : ℝ) - j) : ℝ) : ℂ) := by
    simp only [cz]
    push_cast
    ring
  rw [h₁, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have h₂ : (1 : ℤ) ≤ |(i : ℤ) - j| := Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast h))
  have h₃ : (1 : ℝ) ≤ |(i : ℝ) - j| := by exact_mod_cast h₂
  linarith

theorem one_lt_far {i I : ℕ} (h : i ≠ I) {ζ : ℂ} (hζ : ‖ζ - cz I‖ < 2) : 1 < ‖ζ - cz i‖ := by
  have h₁ := three_le h
  have h₂ : ‖cz i - cz I‖ ≤ ‖ζ - cz i‖ + ‖ζ - cz I‖ := by
    have h₃ : cz i - cz I = (ζ - cz I) - (ζ - cz i) := by ring
    rw [h₃, add_comm]
    exact norm_sub_le _ _
  linarith

theorem sq_of_one_lt {r : ℝ} (h : 1 < r) : 1 < r ^ 2 := by nlinarith

/-- A point near the `I`th circle, but not inside it, is clear. -/
theorem clear_near {I : ℕ} {ζ : ℂ} (h₁ : 1 < ‖ζ - cz I‖) (h₂ : ‖ζ - cz I‖ < 2) :
    Clear a b c (cp ζ) := fun i _ ↦ by
  rw [← nsq]
  rcases eq_or_ne i I with rfl | hne
  · exact sq_of_one_lt h₁
  · exact sq_of_one_lt (one_lt_far hne h₂)

/-- A point near a circle that is not pasted is off the pasted circles. -/
theorem free_near {I : ℕ} (hI : 2 * a + b ≤ I) {ζ : ℂ} (h : ‖ζ - cz I‖ < 2) :
    Free a b (cp ζ) := fun i hi ↦ by
  rw [← nsq]
  exact sq_of_one_lt (one_lt_far (by omega) h)

theorem cp_cz (I : ℕ) : cp (cz I + 1) = (3 * (I : ℝ) + 1, 0) := by
  simp [cp, cz]

theorem ok_cz (I : ℕ) : Ok a b c (3 * (I : ℝ) + 1, 0) :=
  ok_circle (x := 1) (y := 0) (by norm_num)

/-- The points of the circles that are not pasted are boundary points. -/
theorem qq_mem_bd {I : ℕ} (hI : 2 * a + b ≤ I) (hI' : I < 2 * a + b + c) :
    qq a b c (3 * (I : ℝ) + 1, 0) ∈ bd (SurfaceModel a b c) := by
  have hB : ∀ ζ ∈ ball (cz I + 1) (1 / 2), ‖ζ - cz I‖ < 3 / 2 := fun ζ hζ ↦ by
    have h₁ : ‖ζ - (cz I + 1)‖ < 1 / 2 := by simpa [dist_eq_norm] using hζ
    have h₂ : ζ - cz I = (ζ - (cz I + 1)) + 1 := by ring
    rw [h₂]
    have h₃ := norm_add_le (ζ - (cz I + 1)) 1
    rw [norm_one] at h₃
    linarith
  have hj := isOpenEmbedding_chart (a := a) (b := b) (c := c) (B := ball (cz I + 1) (1 / 2))
    isOpen_ball fun ζ hζ _ ↦ free_near hI (by linarith [hB ζ hζ])
  have hw : cz I + 1 ∈ chartDom a b c (ball (cz I + 1) (1 / 2)) :=
    ⟨mem_ball_self (by norm_num), by
      change Ok a b c (cp (cz I + 1))
      rw [cp_cz]
      exact ok_cz I⟩
  have h₁ := not_interior_of_chart hj ⟨_, hw⟩ ?_
  · have h₂ : chart a b c (ball (cz I + 1) (1 / 2)) ⟨_, hw⟩ = qq a b c (3 * (I : ℝ) + 1, 0) := by
      change qq a b c (cp (cz I + 1)) = _
      rw [cp_cz]
    rw [h₂] at h₁
    exact h₁
  · intro hint
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
    set t : ℝ := min ε 1 / 2 with ht
    have ht₀ : 0 < t := by positivity
    have ht₁ : t ≤ 1 / 2 := by
      have := min_le_right ε 1
      rw [ht]
      linarith
    have ht₂ : t < ε := by
      have := min_le_left ε 1
      rw [ht]
      linarith [lt_min hε one_pos]
    have hmem : cz I + 1 - (t : ℂ) ∈ ball (cz I + 1) ε := by
      rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos ht₀]
      exact ht₂
    have hok := (hball hmem).2 I hI'
    change 1 ≤ ((cp _).1 - 3 * (I : ℝ)) ^ 2 + (cp _).2 ^ 2 at hok
    rw [← nsq] at hok
    have h₂ : cz I + 1 - (t : ℂ) - cz I = ((1 - t : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h₂, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hok
    nlinarith

/-- The points at distance `3/2` from a circle centre are interior points. -/
theorem interior_sphere {I : ℕ} {ζ₀ : ℂ} (h : ‖ζ₀ - cz I‖ = 3 / 2) :
    IsInteriorPoint (qq a b c (cp ζ₀)) := by
  have hB : ∀ ζ ∈ ball ζ₀ (1 / 4), 1 < ‖ζ - cz I‖ ∧ ‖ζ - cz I‖ < 2 := fun ζ hζ ↦ by
    have h₁ : ‖ζ - ζ₀‖ < 1 / 4 := by simpa [dist_eq_norm] using hζ
    have h₂ : ‖ζ - cz I‖ ≤ ‖ζ - ζ₀‖ + ‖ζ₀ - cz I‖ := by
      have h₃ : ζ - cz I = (ζ - ζ₀) + (ζ₀ - cz I) := by ring
      rw [h₃]
      exact norm_add_le _ _
    have h₃ : ‖ζ₀ - cz I‖ ≤ ‖ζ - ζ₀‖ + ‖ζ - cz I‖ := by
      have h₄ : ζ₀ - cz I = (ζ - cz I) - (ζ - ζ₀) := by ring
      rw [h₄, add_comm]
      exact norm_sub_le _ _
    constructor <;> linarith
  have hcl : ∀ ζ ∈ ball ζ₀ (1 / 4), Clear a b c (cp ζ) := fun ζ hζ ↦
    clear_near (hB ζ hζ).1 (hB ζ hζ).2
  have hj := isOpenEmbedding_chart (a := a) (b := b) (c := c) (B := ball ζ₀ (1 / 4))
    isOpen_ball fun ζ hζ _ i _ ↦ hcl ζ hζ i (by omega)
  have hdom : chartDom a b c (ball ζ₀ (1 / 4)) = ball ζ₀ (1 / 4) :=
    Set.inter_eq_left.mpr fun ζ hζ ↦ (hcl ζ hζ).ok
  have hw : ζ₀ ∈ chartDom a b c (ball ζ₀ (1 / 4)) := by
    rw [hdom]
    exact mem_ball_self (by norm_num)
  exact interior_of_chart hj
    ⟨(Homeomorph.setCongr hdom).trans (ballHomeo ζ₀ (by norm_num))⟩ ⟨ζ₀, hw⟩

theorem isClosed_ok : IsClosed {ζ : ℂ | Ok a b c (cp ζ)} := by
  have : {ζ : ℂ | Ok a b c (cp ζ)} =
      ⋂ i ∈ Finset.range (2 * a + b + c), {ζ : ℂ | 1 ≤ ‖ζ - cz i‖ ^ 2} := by
    ext ζ
    simp only [mem_ofPred_eq, mem_iInter, Finset.mem_range, nsq]
    rfl
  rw [this]
  refine isClosed_biInter fun i _ ↦ isClosed_le continuous_const ?_
  fun_prop

/-- The circles that are not pasted lie in different components of the boundary. -/
theorem not_connected [T2Space (SurfaceModel a b c)] {I J : ℕ} (hI : 2 * a + b ≤ I)
    (hJ : 2 * a + b ≤ J) (_hJ' : J < 2 * a + b + c) (hne : I ≠ J)
    {K : Set (SurfaceModel a b c)} (hK : IsPreconnected K) (hbd : K ⊆ bd _)
    (h₁ : qq a b c (3 * (I : ℝ) + 1, 0) ∈ K) (h₂ : qq a b c (3 * (J : ℝ) + 1, 0) ∈ K) : False := by
  have hf : ∀ ζ ∈ ball (cz I) (3 / 2), Ok a b c (cp ζ) → Free a b (cp ζ) := fun ζ hζ _ ↦
    free_near hI (by
      have : ‖ζ - cz I‖ < 3 / 2 := by simpa [dist_eq_norm] using hζ
      linarith)
  have hV₁ : IsOpen (range (chart a b c (ball (cz I) (3 / 2)))) :=
    (isOpenEmbedding_chart isOpen_ball hf).isOpen_range
  let E : Set ℂ := closedBall (cz I) (3 / 2) ∩ {ζ : ℂ | Ok a b c (cp ζ)}
  have hE : IsCompact E := (isCompact_closedBall _ _).inter_right isClosed_ok
  have hEc : ContinuousOn (fun ζ ↦ qq a b c (cp ζ)) E :=
    continuousOn_qq.comp continuous_cp.continuousOn fun ζ hζ ↦ hζ.2
  have hV₂ : IsOpen ((fun ζ ↦ qq a b c (cp ζ)) '' E)ᶜ :=
    (hE.image_of_continuousOn hEc).isClosed.isOpen_compl
  have hcover : K ⊆ range (chart a b c (ball (cz I) (3 / 2))) ∪
      ((fun ζ ↦ qq a b c (cp ζ)) '' E)ᶜ := by
    intro x hx
    by_cases hxE : x ∈ (fun ζ ↦ qq a b c (cp ζ)) '' E
    · left
      obtain ⟨ζ, hζ, rfl⟩ := hxE
      have h₃ : ‖ζ - cz I‖ ≤ 3 / 2 := by simpa [dist_eq_norm] using hζ.1
      rcases h₃.lt_or_eq with h₄ | h₄
      · exact ⟨⟨ζ, by simpa [dist_eq_norm] using h₄, hζ.2⟩, rfl⟩
      · exact absurd (interior_sphere h₄) (hbd hx)
    · exact Or.inr hxE
  have hcI : ‖(cz I + 1) - cz I‖ = 1 := by simp
  have hmem₁ : (K ∩ range (chart a b c (ball (cz I) (3 / 2)))).Nonempty := by
    refine ⟨_, h₁, ⟨cz I + 1, ?_, ?_⟩, ?_⟩
    · rw [mem_ball, dist_eq_norm, hcI]
      norm_num
    · change Ok a b c (cp (cz I + 1))
      rw [cp_cz]
      exact ok_cz I
    · change qq a b c (cp (cz I + 1)) = _
      rw [cp_cz]
  have hdist : 2 ≤ ‖(cz J + 1) - cz I‖ := by
    have h₃ := three_le hne.symm
    have h₄ : cz J - cz I = ((cz J + 1) - cz I) - 1 := by ring
    have h₅ := norm_sub_le ((cz J + 1) - cz I) 1
    rw [← h₄, norm_one] at h₅
    linarith
  have hfJ : Free a b (3 * (J : ℝ) + 1, 0) := by
    rw [← cp_cz]
    exact free_near hJ (by simp)
  have hmem₂ : (K ∩ ((fun ζ ↦ qq a b c (cp ζ)) '' E)ᶜ).Nonempty := by
    refine ⟨_, h₂, ?_⟩
    rintro ⟨ζ, hζ, heq⟩
    have h₃ : ‖ζ - cz I‖ ≤ 3 / 2 := by simpa [dist_eq_norm] using hζ.1
    have h₄ := eq_of_free hζ.2 (free_near hI (by linarith)) (ok_cz J) hfJ heq
    rw [← cp_cz] at h₄
    have h₅ := cp_injective h₄
    subst h₅
    linarith
  obtain ⟨x, -, hx₁, hx₂⟩ := hK _ _ hV₁ hV₂ hcover hmem₁ hmem₂
  obtain ⟨ζ, rfl⟩ := hx₁
  refine hx₂ ⟨ζ.1, ⟨?_, ζ.2.2⟩, rfl⟩
  exact mem_closedBall.mpr (mem_ball.mp ζ.2.1).le

/-- A model has at least `c` cuffs. -/
theorem le_encard_cuffs [T2Space (SurfaceModel a b c)] :
    (c : ℕ∞) ≤ (cuffs (SurfaceModel a b c)).encard := by
  classical
  let w : Fin c → SurfaceModel a b c := fun i ↦ qq a b c (3 * ((2 * a + b + i : ℕ) : ℝ) + 1, 0)
  have hw : ∀ i, w i ∈ bd (SurfaceModel a b c) := fun i ↦
    qq_mem_bd (by omega) (by omega)
  let f : Fin c → Set (SurfaceModel a b c) := fun i ↦ connectedComponentIn (bd _) (w i)
  have hf : ∀ i, f i ∈ cuffs (SurfaceModel a b c) := fun i ↦ ⟨w i, hw i, rfl⟩
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hne' : 2 * a + b + (i : ℕ) ≠ 2 * a + b + (j : ℕ) := fun h ↦
      hne (Fin.ext (by omega))
    refine not_connected (I := 2 * a + b + i) (J := 2 * a + b + j) (by omega) (by omega) (by omega)
      hne' (K := f i) isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
      (mem_connectedComponentIn (hw i)) ?_
    change w j ∈ f i
    rw [hij]
    exact mem_connectedComponentIn (hw j)
  have h₁ : (f '' univ).encard = (c : ℕ∞) := by
    rw [hinj.injOn.encard_image, Set.encard_univ]
    simp
  rw [← h₁]
  exact Set.encard_le_encard (by
    rintro _ ⟨i, -, rfl⟩
    exact hf i)

/-- A homeomorphism carries a line to a line with the corresponding ends. -/
theorem image_isLineWithEnds {S T : Type*} [TopologicalSpace S] [TopologicalSpace T] (ψ : S ≃ₜ T)
    {L : Set S} {u v : S} (h : IsLineWithEnds L u v) : IsLineWithEnds (ψ '' L) (ψ u) (ψ v) := by
  obtain ⟨f, rfl, rfl⟩ := h
  exact ⟨f.trans (ψ.image L), rfl, rfl⟩

/-- A homeomorphism carries a drawing to a drawing. -/
theorem CanBeDrawn.map {α' : Type*} {β' : Type*} {S T : Type} [TopologicalSpace S]
    [TopologicalSpace T] (ψ : S ≃ₜ T) {H : Hypergraph α' β'} (h : CanBeDrawn S H) :
    CanBeDrawn T H := by
  obtain ⟨ν, F, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨ψ ∘ ν, fun e ↦ ψ '' F e, ψ.injective.comp_injOn h₁, ?_, ?_, ?_, ?_⟩
  · intro e he u v hu hv huv
    exact image_isLineWithEnds ψ (h₂ e he u v hu hv huv)
  · intro e he v hv
    obtain ⟨h₆, h₇⟩ := h₃ e he v hv
    obtain ⟨g⟩ := h₆
    exact ⟨⟨g.trans (ψ.image _)⟩, mem_image_of_mem _ h₇⟩
  · intro e he f hf hef w hw
    rw [← image_inter ψ.injective] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    obtain ⟨v, hv, rfl⟩ := h₄ e he f hf hef hx
    exact ⟨v, hv, rfl⟩
  · rintro e he v hv ⟨x, hx, hxv⟩
    obtain rfl := ψ.injective hxv
    exact h₅ e he v hv hx

end GraphMinor.GM20.Draw
