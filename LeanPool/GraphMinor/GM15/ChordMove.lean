/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Section3Parallel
public import LeanPool.GraphMinor.GM15.LineMove
import LeanPool.GraphMinor.Surface.Cap
import LeanPool.GraphMinor.Surface.DiscPolygon
import LeanPool.GraphMinor.Surface.TriPath
import LeanPool.GraphMinor.GM11.RadialChord

/-!
# Moving disjoint lines onto vertical chords

Graph Minors XV, (3.4), page 122, takes a drawing $H' = H \cup P_1 \cup \dots \cup P_{k-1}$ whose
paths cross the closed disc $\bar\Lambda$. The proof in `GraphMinor/GM15/Section3Parallel.lean`
works in a chart of $\bar\Lambda$ in which the paths are vertical chords of the unit disc. This
file shows that such a chart exists for any such paths: disjoint lines `M j` across the unit disc,
with the ends of the chord at `x j` and meeting the circle only there, are the images of the
chords under a homeomorphism of the unit disc that fixes the circle
(`exists_ballHomeo_moving_chords`).

The proof moves one line at a time. After the first `n` lines are straight, the next line lies to
the left of the last straight chord, so it is moved onto its chord inside the closed left cap by
`exists_homeo_moving_line`, and the rest of the disc is fixed.
-/

@[expose] public section

namespace GraphMinor.GM15

open Set Function Topology Metric Surface

/-- `Φ` is a homeomorphism of the closed unit disc onto itself, with inverse `Φ'`, that fixes the
unit circle. -/
structure IsBallHomeo (Φ Φ' : ℂ → ℂ) : Prop where
  maps : MapsTo Φ (closedBall 0 1) (closedBall 0 1)
  maps' : MapsTo Φ' (closedBall 0 1) (closedBall 0 1)
  cont : ContinuousOn Φ (closedBall 0 1)
  cont' : ContinuousOn Φ' (closedBall 0 1)
  left : LeftInvOn Φ' Φ (closedBall 0 1)
  right : LeftInvOn Φ Φ' (closedBall 0 1)
  fix : ∀ z ∈ sphere (0 : ℂ) 1, Φ z = z

namespace IsBallHomeo

theorem id : IsBallHomeo id id :=
  ⟨mapsTo_id _, mapsTo_id _, continuousOn_id, continuousOn_id, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl⟩

theorem comp {Φ Φ' Ψ Ψ' : ℂ → ℂ} (h₁ : IsBallHomeo Φ Φ') (h₂ : IsBallHomeo Ψ Ψ') :
    IsBallHomeo (Φ ∘ Ψ) (Ψ' ∘ Φ') where
  maps := h₁.maps.comp h₂.maps
  maps' := h₂.maps'.comp h₁.maps'
  cont := h₁.cont.comp h₂.cont h₂.maps
  cont' := h₂.cont'.comp h₁.cont' h₁.maps'
  left := fun z hz => by
    simp only [Function.comp_apply]
    rw [h₁.left (h₂.maps hz), h₂.left hz]
  right := fun z hz => by
    simp only [Function.comp_apply]
    rw [h₂.right (h₁.maps' hz), h₁.right hz]
  fix := fun z hz => by
    simp only [Function.comp_apply]
    rw [h₂.fix z hz, h₁.fix z hz]

theorem fix' {Φ Φ' : ℂ → ℂ} (h : IsBallHomeo Φ Φ') {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) :
    Φ' z = z := by
  conv_lhs => rw [← h.fix z hz]
  exact h.left (sphere_subset_closedBall hz)

end IsBallHomeo

/-- A vertical chord is a line between its ends. -/
theorem isLineWithEnds_vertChord {r y : ℝ} (hry : r ^ 2 + y ^ 2 = 1) (hy : 0 < y) :
    IsLineWithEnds (vertChord r) ⟨r, y⟩ ⟨r, -y⟩ := by
  have h0 : vertChordMap r y 0 = ⟨r, y⟩ := by
    apply Complex.ext <;> simp [vertChordMap]
  have h1 : vertChordMap r y 1 = ⟨r, -y⟩ := by
    apply Complex.ext <;> simp [vertChordMap]
    ring
  rw [← range_vertChordMap hry hy, ← h0, ← h1]
  exact GM11.isLine_range (continuous_vertChordMap r y) (injective_vertChordMap hy)

/-! ## The closed left cap -/

section Cap

variable {r : ℝ}

theorem leftClosedCap_subset_closedBall (r : ℝ) : leftClosedCap r ⊆ closedBall (0 : ℂ) 1 :=
  fun _ hz => hz.1

theorem isClosedDisc_leftClosedCap (hr : -1 < r) (hr1 : r ≤ 1) :
    IsClosedDisc (leftClosedCap r) ∧ discBd (leftClosedCap r) = frontier (leftClosedCap r) := by
  refine isClosedDisc_of_convex (convex_leftClosedCap r) ?_
    (isBounded_closedBall.subset (leftClosedCap_subset_closedBall r)) (isClosed_leftClosedCap r)
  refine ⟨⟨(r - 1) / 2, 0⟩, ?_⟩
  have hsub : leftOpenCap r ⊆ interior (leftClosedCap r) :=
    interior_maximal (fun z hz => ⟨ball_subset_closedBall hz.1, hz.2.le⟩) (isOpen_leftOpenCap r)
  refine hsub ⟨?_, ?_⟩
  · rw [mem_ball_unit_iff]
    simp only
    nlinarith
  · simp only
    linarith

/-- A point of a closed set with points outside it arbitrarily close is on its frontier. -/
theorem mem_frontier_of_approx {K : Set ℂ} (hK : IsClosed K) {z : ℂ} (hz : z ∈ K)
    (h : ∀ ε > 0, ∃ w, dist w z < ε ∧ w ∉ K) : z ∈ frontier K := by
  rw [frontier, hK.closure_eq]
  refine ⟨hz, ?_⟩
  intro hint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hint
  obtain ⟨w, hw, hwK⟩ := h ε hε
  exact hwK (interior_subset (hball hw))

theorem frontier_leftClosedCap_subset (z : ℂ) (hz : z ∈ frontier (leftClosedCap r)) :
    z ∈ sphere (0 : ℂ) 1 ∨ z ∈ vertChord r := by
  have hzK : z ∈ leftClosedCap r := (isClosed_leftClosedCap r).frontier_subset hz
  by_contra hne
  push Not at hne
  have hball : z ∈ ball (0 : ℂ) 1 := by
    have h1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hzK.1
    have h2 : ‖z‖ ≠ 1 := fun h => hne.1 (mem_sphere_zero_iff_norm.mpr h)
    exact mem_ball_zero_iff.mpr (lt_of_le_of_ne h1 h2)
  have hlt : z.re < r := lt_of_le_of_ne hzK.2 fun h => hne.2 ⟨hzK.1, h⟩
  have hint : z ∈ interior (leftClosedCap r) :=
    interior_maximal (show leftOpenCap r ⊆ leftClosedCap r from
      fun w hw => ⟨ball_subset_closedBall hw.1, hw.2.le⟩) (isOpen_leftOpenCap r)
      (show z ∈ leftOpenCap r from ⟨hball, hlt⟩)
  exact hz.2 hint

theorem sphere_inter_subset_frontier :
    sphere (0 : ℂ) 1 ∩ leftClosedCap r ⊆ frontier (leftClosedCap r) := by
  rintro z ⟨hzs, hzK⟩
  refine mem_frontier_of_approx (isClosed_leftClosedCap r) hzK fun ε hε => ?_
  have hn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hzs
  refine ⟨(1 + ε / 2 : ℝ) • z, ?_, fun hw => ?_⟩
  · rw [dist_eq_norm]
    have : (1 + ε / 2 : ℝ) • z - z = (ε / 2 : ℝ) • z := by
      rw [add_smul, one_smul]
      abel
    rw [this, norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  · have h1 := mem_closedBall_zero_iff.mp hw.1
    rw [norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)] at h1
    linarith

theorem vertChord_subset_frontier : vertChord r ⊆ frontier (leftClosedCap r) := by
  intro z hz
  have hzK : z ∈ leftClosedCap r := ⟨hz.1, hz.2.le⟩
  refine mem_frontier_of_approx (isClosed_leftClosedCap r) hzK fun ε hε => ?_
  refine ⟨z + ((ε / 2 : ℝ) : ℂ), ?_, fun hw => ?_⟩
  · rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  · have h1 := hw.2
    simp only [Complex.add_re, Complex.ofReal_re] at h1
    rw [hz.2] at h1
    linarith

end Cap

/-- If a preconnected set in the unit disc has a point left of the vertical line `re = r` and
misses the chord at `r`, it lies left of that line. -/
theorem re_lt_of_isPreconnected {N : Set ℂ} (hN : IsPreconnected N)
    (hNB : N ⊆ closedBall (0 : ℂ) 1) {r : ℝ} {z₀ : ℂ} (hz₀ : z₀ ∈ N) (hz₀r : z₀.re < r)
    (hNr : Disjoint N (vertChord r)) : ∀ z ∈ N, z.re < r := by
  intro z hz
  by_contra hle
  push Not at hle
  have hre : IsPreconnected (Complex.re '' N) := hN.image _ Complex.continuous_re.continuousOn
  obtain ⟨w, hw, hwr⟩ := hre.Icc_subset (mem_image_of_mem _ hz₀) (mem_image_of_mem _ hz)
    ⟨hz₀r.le, hle⟩
  exact disjoint_left.mp hNr hw ⟨hNB hw, hwr⟩

/-! ## One step -/

open Classical in
/-- Extending a homeomorphism of the closed left cap that fixes its boundary by the identity. -/
theorem isBallHomeo_extend {r : ℝ} {Ψ Ψ' : ℂ → ℂ}
    (hm : MapsTo Ψ (leftClosedCap r) (leftClosedCap r))
    (hm' : MapsTo Ψ' (leftClosedCap r) (leftClosedCap r))
    (hc : ContinuousOn Ψ (leftClosedCap r)) (hc' : ContinuousOn Ψ' (leftClosedCap r))
    (hl : LeftInvOn Ψ' Ψ (leftClosedCap r)) (hr : LeftInvOn Ψ Ψ' (leftClosedCap r))
    (hfix : ∀ z ∈ frontier (leftClosedCap r), Ψ z = z) :
    IsBallHomeo (fun z => if z ∈ leftClosedCap r then Ψ z else z)
      (fun z => if z ∈ leftClosedCap r then Ψ' z else z) ∧
    ∀ z ∈ rightClosedCap r, (if z ∈ leftClosedCap r then Ψ z else z) = z := by
  classical
  have hfix' : ∀ z ∈ frontier (leftClosedCap r), Ψ' z = z := fun z hz => by
    have hzK := (isClosed_leftClosedCap r).frontier_subset hz
    conv_lhs => rw [← hfix z hz]
    exact hl hzK
  have hB : closedBall (0 : ℂ) 1 = leftClosedCap r ∪ rightClosedCap r := by
    ext z
    refine ⟨fun hz => ?_, fun hz => hz.elim (·.1) (·.1)⟩
    rcases le_total z.re r with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  have hKK' : ∀ z ∈ rightClosedCap r, z ∈ leftClosedCap r → z ∈ frontier (leftClosedCap r) :=
    fun z hz hzK => vertChord_subset_frontier ⟨hz.1, le_antisymm hzK.2 hz.2⟩
  have hright : ∀ {Θ : ℂ → ℂ}, (∀ z ∈ frontier (leftClosedCap r), Θ z = z) →
      ∀ z ∈ rightClosedCap r, (if z ∈ leftClosedCap r then Θ z else z) = z := by
    intro Θ hΘ z hz
    by_cases hzK : z ∈ leftClosedCap r
    · rw [ite_eq_left hzK]
      exact hΘ z (hKK' z hz hzK)
    · rw [ite_eq_right hzK]
  have hcont : ∀ {Θ : ℂ → ℂ}, ContinuousOn Θ (leftClosedCap r) →
      (∀ z ∈ frontier (leftClosedCap r), Θ z = z) →
      ContinuousOn (fun z => if z ∈ leftClosedCap r then Θ z else z) (closedBall 0 1) := by
    intro Θ hΘ hΘf
    rw [hB]
    refine ContinuousOn.union_of_isClosed (hΘ.congr fun z hz => ite_eq_left hz)
      (continuousOn_id.congr fun z hz => hright hΘf z hz) (isClosed_leftClosedCap r)
      (isClosed_rightClosedCap r)
  have hmaps : ∀ {Θ : ℂ → ℂ}, MapsTo Θ (leftClosedCap r) (leftClosedCap r) →
      MapsTo (fun z => if z ∈ leftClosedCap r then Θ z else z) (closedBall 0 1) (closedBall 0 1)
        := by
    intro Θ hΘ z hz
    by_cases hzK : z ∈ leftClosedCap r
    · simp only [ite_eq_left hzK]
      exact (hΘ hzK).1
    · simpa [hzK] using hz
  have hinv : ∀ {Θ Θ' : ℂ → ℂ}, MapsTo Θ (leftClosedCap r) (leftClosedCap r) →
      LeftInvOn Θ' Θ (leftClosedCap r) →
      LeftInvOn (fun z => if z ∈ leftClosedCap r then Θ' z else z)
        (fun z => if z ∈ leftClosedCap r then Θ z else z) (closedBall 0 1) := by
    intro Θ Θ' hΘ hl z _
    by_cases hzK : z ∈ leftClosedCap r
    · simp only [ite_eq_left hzK, ite_eq_left (hΘ hzK)]
      exact hl hzK
    · simp [hzK]
  refine ⟨⟨hmaps hm, hmaps hm', hcont hc hfix, hcont hc' hfix', hinv hm hl, hinv hm' hr,
    fun z hz => ?_⟩, hright hfix⟩
  by_cases hzK : z ∈ leftClosedCap r
  · simp only [ite_eq_left hzK]
    exact hfix z (sphere_inter_subset_frontier ⟨hz, hzK⟩)
  · simp [hzK]

/-- One step of the induction: if `Φ` already straightens the lines with index `< n`, and the line
`M j₀` is moved by `Φ⁻¹` to a line left of the chord at `r`, it is straightened inside the left
cap at `r`. -/
theorem exists_step {m : ℕ} {x y : Fin m → ℝ} (hxy : ∀ j, x j ^ 2 + y j ^ 2 = 1)
    (hy : ∀ j, 0 < y j) {M : Fin m → Set ℂ} (hMB : ∀ j, M j ⊆ closedBall (0 : ℂ) 1)
    (hM : ∀ j, IsLineWithEnds (M j) ⟨x j, y j⟩ ⟨x j, -y j⟩)
    (hMs : ∀ j, M j ∩ sphere (0 : ℂ) 1 = {⟨x j, y j⟩, ⟨x j, -y j⟩})
    {Φ Φ' : ℂ → ℂ} (hΦ : IsBallHomeo Φ Φ') {n : ℕ} (j₀ : Fin m) (hj₀ : j₀.1 = n)
    (hprev : ∀ j : Fin m, j.1 < n → Φ '' vertChord (x j) = M j) {r : ℝ} (hxr : x j₀ < r)
    (hr : ∀ j : Fin m, j.1 < n → r ≤ x j) (hr1' : r ≤ 1) (hNr : Disjoint (Φ' '' M j₀)
      (vertChord r)) :
    ∃ Θ Θ' : ℂ → ℂ, IsBallHomeo Θ Θ' ∧ ∀ j : Fin m, j.1 < n + 1 → Θ '' vertChord (x j) = M j := by
  classical
  set e₁ : ℂ := ⟨x j₀, y j₀⟩
  set e₂ : ℂ := ⟨x j₀, -y j₀⟩
  set N := Φ' '' M j₀ with hN
  have hy₀ := hy j₀
  have hx₀ : -1 < x j₀ := by nlinarith [hxy j₀]
  have hr1 : -1 < r := by linarith
  have he₁₂ : e₁ ≠ e₂ := fun h => by
    have := congrArg Complex.im h
    simp only [e₁, e₂] at this
    linarith
  have he₁s : e₁ ∈ sphere (0 : ℂ) 1 := by
    rw [mem_sphere_unit_iff]
    exact hxy j₀
  have he₂s : e₂ ∈ sphere (0 : ℂ) 1 := by
    rw [mem_sphere_unit_iff]
    simp only [e₂]
    nlinarith [hxy j₀]
  -- `N` is a line in the closed disc with the same ends, meeting the circle only in them.
  have hNB : N ⊆ closedBall (0 : ℂ) 1 := image_subset_iff.mpr fun w hw => hΦ.maps' (hMB j₀ hw)
  have hNline : IsLineWithEnds N e₁ e₂ := by
    have h := (hM j₀).image_injOn (hΦ.cont'.mono (hMB j₀))
      (hΦ.right.injOn.mono (hMB j₀))
    rwa [hΦ.fix' he₁s, hΦ.fix' he₂s] at h
  have hNs : N ∩ sphere (0 : ℂ) 1 = {e₁, e₂} := by
    ext z
    constructor
    · rintro ⟨⟨w, hw, rfl⟩, hzs⟩
      have hw' : Φ (Φ' w) = w := hΦ.right (hMB j₀ hw)
      have hzw : Φ' w = w := by
        conv_rhs => rw [← hw', hΦ.fix _ hzs]
      rw [hzw] at hzs ⊢
      have hmem : w ∈ M j₀ ∩ sphere (0 : ℂ) 1 := ⟨hw, hzs⟩
      rw [hMs j₀] at hmem
      exact hmem
    · rintro (rfl | rfl)
      · refine ⟨⟨e₁, ?_, hΦ.fix' he₁s⟩, he₁s⟩
        have hmem : e₁ ∈ M j₀ ∩ sphere (0 : ℂ) 1 := by
          rw [hMs j₀]
          exact Or.inl rfl
        exact hmem.1
      · refine ⟨⟨e₂, ?_, hΦ.fix' he₂s⟩, he₂s⟩
        have hmem : e₂ ∈ M j₀ ∩ sphere (0 : ℂ) 1 := by
          rw [hMs j₀]
          exact Or.inr rfl
        exact hmem.1
  have he₁N : e₁ ∈ N := by
    have hmem : e₁ ∈ N ∩ sphere (0 : ℂ) 1 := by
      rw [hNs]
      exact Or.inl rfl
    exact hmem.1
  -- `N` lies left of the chord at `r`, so in the closed left cap.
  have hNlt : ∀ z ∈ N, z.re < r :=
    re_lt_of_isPreconnected hNline.isPreconnected_self hNB he₁N hxr hNr
  have hNK : N ⊆ leftClosedCap r := fun z hz => ⟨hNB hz, (hNlt z hz).le⟩
  have hCK : vertChord (x j₀) ⊆ leftClosedCap r := fun z hz => ⟨hz.1, hz.2 ▸ hxr.le⟩
  obtain ⟨hK, hKbd⟩ := isClosedDisc_leftClosedCap hr1 hr1'
  have hbdK : ∀ {L : Set ℂ}, L ⊆ leftClosedCap r → L ∩ sphere (0 : ℂ) 1 = {e₁, e₂} →
      (∀ z ∈ L, z.re < r) → L ∩ discBd (leftClosedCap r) = {e₁, e₂} := by
    intro L hLK hLs hLr
    rw [hKbd, ← hLs]
    ext z
    constructor
    · rintro ⟨hzL, hzf⟩
      rcases frontier_leftClosedCap_subset z hzf with h | h
      · exact ⟨hzL, h⟩
      · exact absurd h.2 (hLr z hzL).ne
    · rintro ⟨hzL, hzs⟩
      exact ⟨hzL, sphere_inter_subset_frontier ⟨hzs, hLK hzL⟩⟩
  have hCs : vertChord (x j₀) ∩ sphere (0 : ℂ) 1 = {e₁, e₂} := vertChord_inter_sphere (hxy j₀)
  obtain ⟨Ψ, Ψ', hm, hm', hc, hc', hl, hr', hfix, himg⟩ :=
    exists_homeo_moving_line hK he₁₂ (isLineWithEnds_vertChord (hxy j₀) hy₀) hNline hCK hNK
      (hbdK hCK hCs fun z hz => hz.2 ▸ hxr) (hbdK hNK hNs hNlt)
  obtain ⟨hext, hextfix⟩ := isBallHomeo_extend hm hm' hc hc' hl hr' fun z hz =>
    hfix z (hKbd ▸ hz)
  refine ⟨_, _, hΦ.comp hext, fun j hj => ?_⟩
  rw [image_comp]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjn | hjn
  · -- An earlier chord lies in the right cap, which the new map fixes.
    have hfixC : ∀ z ∈ vertChord (x j), (if z ∈ leftClosedCap r then Ψ z else z) = z :=
      fun z hz => hextfix z ⟨hz.1, hz.2 ▸ hr j hjn⟩
    rw [image_congr hfixC, image_id', hprev j hjn]
  · have hjj : j = j₀ := Fin.ext (hjn.trans hj₀.symm)
    subst hjj
    have h1 : (fun z => if z ∈ leftClosedCap r then Ψ z else z) '' vertChord (x j) = N := by
      rw [← himg]
      exact image_congr fun z hz => ite_eq_left (hCK hz)
    rw [h1, hN, image_image]
    conv_rhs => rw [← image_id (M j)]
    exact image_congr fun w hw => hΦ.right (hMB j hw)

/-- **Straightening disjoint lines.** Let `x` be strictly decreasing with `x j ^ 2 + y j ^ 2 = 1`
and `y j > 0`, and let `M j` be disjoint lines in the closed unit disc, with ends `⟨x j, y j⟩` and
`⟨x j, -y j⟩` and meeting the unit circle only there. Then a homeomorphism of the closed unit disc
fixing the circle maps each vertical chord `vertChord (x j)` onto `M j`. -/
theorem exists_ballHomeo_moving_chords {m : ℕ} {x y : Fin m → ℝ} (hx : StrictAnti x)
    (hxy : ∀ j, x j ^ 2 + y j ^ 2 = 1) (hy : ∀ j, 0 < y j) {M : Fin m → Set ℂ}
    (hMB : ∀ j, M j ⊆ closedBall (0 : ℂ) 1)
    (hM : ∀ j, IsLineWithEnds (M j) ⟨x j, y j⟩ ⟨x j, -y j⟩)
    (hMs : ∀ j, M j ∩ sphere (0 : ℂ) 1 = {⟨x j, y j⟩, ⟨x j, -y j⟩})
    (hdisj : Pairwise fun i j => Disjoint (M i) (M j)) :
    ∃ Φ Φ' : ℂ → ℂ, IsBallHomeo Φ Φ' ∧ ∀ j, Φ '' vertChord (x j) = M j := by
  suffices h : ∀ n ≤ m, ∃ Φ Φ' : ℂ → ℂ, IsBallHomeo Φ Φ' ∧
      ∀ j : Fin m, j.1 < n → Φ '' vertChord (x j) = M j by
    obtain ⟨Φ, Φ', hΦ, h⟩ := h m le_rfl
    exact ⟨Φ, Φ', hΦ, fun j => h j j.2⟩
  intro n
  induction n with
  | zero => exact fun _ => ⟨_, _, IsBallHomeo.id, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro hn
    obtain ⟨Φ, Φ', hΦ, hprev⟩ := ih (by omega)
    let j₀ : Fin m := ⟨n, by omega⟩
    have hx₀ : x j₀ < 1 := by nlinarith [hxy j₀, hy j₀]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · -- No chord is straight yet: work in the whole disc, the left cap at `1`.
      refine exists_step hxy hy hMB hM hMs hΦ j₀ rfl hprev hx₀
        (fun j hj => absurd hj (Nat.not_lt_zero _)) le_rfl ?_
      refine disjoint_left.mpr fun z hz hz1 => ?_
      have hzs : z ∈ sphere (0 : ℂ) 1 := by
        have h1 := (mem_closedBall_unit_iff z).mp hz1.1
        rw [hz1.2] at h1
        rw [mem_sphere_unit_iff, hz1.2]
        nlinarith [sq_nonneg z.im]
      obtain ⟨w, hw, rfl⟩ := hz
      have hw' : Φ (Φ' w) = w := hΦ.right (hMB j₀ hw)
      rw [hΦ.fix _ hzs] at hw'
      rw [hw'] at hzs hz1
      have hwe : w ∈ M j₀ ∩ sphere (0 : ℂ) 1 := ⟨hw, hzs⟩
      rw [hMs j₀] at hwe
      have hre : w.re = x j₀ := by
        rcases hwe with rfl | rfl <;> rfl
      linarith [hz1.2]
    · -- The last straight chord is at `x (n - 1)`.
      let jp : Fin m := ⟨n - 1, by omega⟩
      have hjp : jp ≠ j₀ := fun h => by
        have := congrArg Fin.val h
        simp only [jp, j₀] at this
        omega
      refine exists_step hxy hy hMB hM hMs hΦ j₀ rfl hprev (hx (show jp < j₀ from
        Fin.mk_lt_mk.mpr (by omega))) (fun j hj => hx.antitone (Fin.mk_le_mk.mpr (by omega)))
        (by nlinarith [hxy jp, hy jp]) ?_
      refine disjoint_left.mpr fun z hz hzC => ?_
      obtain ⟨w, hw, rfl⟩ := hz
      have h1 : Φ (Φ' w) ∈ M jp := hprev jp (by simp only [jp]; omega) ▸ mem_image_of_mem Φ hzC
      rw [hΦ.right (hMB j₀ hw)] at h1
      exact disjoint_left.mp (hdisj hjp.symm) hw h1

end GraphMinor.GM15
