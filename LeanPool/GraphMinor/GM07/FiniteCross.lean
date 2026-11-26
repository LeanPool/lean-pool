/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffSlide
public import LeanPool.GraphMinor.GM07.Section11

/-!
# Lines that cross a set in finitely many points

Graph Minors VII, (3.5) (page 221), is left to the reader. Its proof needs a way to join two points
of a connected open set in a surface
by a line that meets a drawing in finitely many points. This file gives one
(`exists_line_finite_cross`). Near each point of the set `Z`
that we must cross, `Z` is an arc, so a straight segment in a strip chart around this arc crosses
`Z` at most once. The points we can
reach with finitely many crossings then fill the connected open set.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric Complex GraphMinor.Surface GraphMinor.GM11

variable {T : Type} [TopologicalSpace T]

/-- `a` and `b` are joined inside `O` with finitely many points of `Z`. -/
def FinReach (O Z : Set T) (a b : T) : Prop := ∃ K ⊆ O, (K ∩ Z).Finite ∧ JoinedIn K a b

theorem FinReach.trans {O Z : Set T} {a b c : T} (h₁ : FinReach O Z a b)
  (h₂ : FinReach O Z b c) : FinReach O Z a c := by
  obtain ⟨K₁, h1, h2, h3⟩ := h₁
  obtain ⟨K₂, h4, h5, h6⟩ := h₂
  refine ⟨K₁ ∪ K₂, union_subset h1 h4, ?_, (h3.mono subset_union_left).trans
    (h6.mono subset_union_right)⟩
  rw [union_inter_distrib_right]
  exact h2.union h5

theorem FinReach.symm {O Z : Set T} {a b : T} (h : FinReach O Z a b) : FinReach O Z b a := by
  obtain ⟨K, h1, h2, h3⟩ := h
  exact ⟨K, h1, h2, h3.symm⟩

/-- A set `N` around a point, in which any two points off `Z` are joined with finitely many
crossings, and each open set around the point has
points of `N` off `Z`. -/
theorem exists_good_nhd (hT : IsClosedSurface T) {O Z : Set T} (hO : IsOpen O) (hZ : IsClosed Z)
    (hloc : ∀ z ∈ O ∩ Z, ∃ (a : unitInterval → T) (W : Set T), IsArcMap a ∧ IsOpen W ∧ z ∈ W
      ∧ z ∈ a '' Ioo 0 1 ∧ range a ⊆ Z ∧ Z ∩ W ⊆ range a)
    {z : T} (hz : z ∈ O) :
    ∃ N, IsOpen N ∧ z ∈ N ∧ N ⊆ O ∧ (∀ p ∈ N \ Z, ∀ q ∈ N \ Z, FinReach O Z p q) ∧ ∀ W, IsOpen W
      → z ∈ W → ((W ∩ N) \ Z).Nonempty := by
  have ht2 : T2Space T := hT.2.1
  by_cases hzZ : z ∈ Z
  · obtain ⟨a, W₀, ha, hW₀, hzW, ⟨t, ht, rfl⟩, hra, hZW⟩ := hloc z ⟨hz, hzZ⟩
    obtain ⟨Os, K, θ, hK, hθc, hθm, hθ⟩ := exists_stripChart_of_arc hT ha
    have hK0 : K (θ t) = a t := (hθ t).2
    let Ω : Set ℂ := Os ∩ K ⁻¹' (O ∩ W₀)
    have hΩ : IsOpen Ω := hK.hc.isOpen_inter_preimage hK.isOpen (hO.inter hW₀)
    have hmem : (θ t : ℂ) ∈ Ω := ⟨(hθ t).1, by rw [mem_preimage, hK0]; exact ⟨hz, hzW⟩⟩
    obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.mp hΩ _ hmem
    have h1 : θ 0 < θ t := hθm ht.1
    have h2 : θ t < θ 1 := hθm ht.2
    let δ := min δ₀ (min (θ t - θ 0) (θ 1 - θ t))
    have hδ : 0 < δ := lt_min hδ₀ (lt_min (by linarith) (by linarith))
    have hδ1 : δ ≤ δ₀ := min_le_left _ _
    have hδ2 : δ ≤ θ t - θ 0 := (min_le_right _ _).trans (min_le_left _ _)
    have hδ3 : δ ≤ θ 1 - θ t := (min_le_right _ _).trans (min_le_right _ _)
    let B : Set ℂ := ball (θ t : ℂ) δ
    have hBΩ : B ⊆ Ω := (ball_subset_ball hδ1).trans hball
    have hBO : B ⊆ Os := fun w hw => (hBΩ hw).1
    have hreal : ∀ w ∈ B, w.im = 0 → ∃ u, w = θ u := fun w hw him => by
      have h3 : |w.re - θ t| < δ := by
        have h4 : w - (θ t : ℂ) = ((w.re - θ t : ℝ) : ℂ) := by
          apply Complex.ext <;> simp [him]
        have h5 : dist w (θ t : ℂ) < δ := hw
        rwa [dist_eq_norm, h4, Complex.norm_real, Real.norm_eq_abs] at h5
      obtain ⟨h6, h7⟩ := abs_lt.mp h3
      obtain ⟨u, hu⟩ := intermediate_value_univ (0 : unitInterval) 1 hθc (show w.re ∈ Icc (θ 0)
        (θ 1) from ⟨by linarith, by linarith⟩)
      refine ⟨u, Complex.ext ?_ ?_⟩
      · simp [hu]
      · simp [him]
    have hKZ : ∀ w ∈ B, K w ∈ Z ↔ w.im = 0 := fun w hw => by
      constructor
      · intro h3
        obtain ⟨u, hu⟩ := hZW ⟨h3, (hBΩ hw).2.2⟩
        have h4 : K w = K (θ u) := by rw [(hθ u).2, hu]
        rw [hK.hi (hBO hw) (hθ u).1 h4]
        simp
      · intro h3
        obtain ⟨u, rfl⟩ := hreal w hw h3
        rw [(hθ u).2]
        exact hra ⟨u, rfl⟩
    have hopenN : IsOpen (K '' B) := hK.ho _ isOpen_ball hBO
    refine ⟨K '' B, hopenN, ⟨_, mem_ball_self hδ, hK0⟩, ?_, ?_, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact (hBΩ hw).2.1
    · rintro _ ⟨⟨w, hw, rfl⟩, hp⟩ _ ⟨⟨w', hw', rfl⟩, hq⟩
      have him : w.im ≠ 0 := fun h => hp ((hKZ w hw).mpr h)
      have him' : w'.im ≠ 0 := fun h => hq ((hKZ w' hw').mpr h)
      have hsub : segment ℝ w w' ⊆ B := (convex_ball _ _).segment_subset hw hw'
      refine ⟨K '' segment ℝ w w', ?_, ?_, ?_⟩
      · rintro _ ⟨v, hv, rfl⟩
        exact (hBΩ (hsub hv)).2.1
      · have hsg : (segment ℝ w w' ∩ {v | v.im = 0}).Subsingleton := by
          rintro x ⟨hx, hx0⟩ y ⟨hy, hy0⟩
          rw [segment_eq_image] at hx hy
          obtain ⟨s₁, -, rfl⟩ := hx
          obtain ⟨s₂, -, rfl⟩ := hy
          simp only [mem_ofPred_eq, add_im, Complex.real_smul, mul_im, ofReal_re, ofReal_im,
            zero_mul, add_zero] at hx0 hy0
          have h3 : (s₁ - s₂) * (w'.im - w.im) = 0 := by linarith
          rcases mul_eq_zero.mp h3 with h4 | h4
          · rw [show s₁ = s₂ by linarith]
          · have h5 : w'.im = w.im := by linarith
            rw [h5] at hx0
            exact (him (by linarith)).elim
        refine (hsg.finite.image K).subset ?_
        rintro _ ⟨⟨v, hv, rfl⟩, hvZ⟩
        exact ⟨v, ⟨hv, (hKZ v (hsub hv)).mp hvZ⟩, rfl⟩
      · have hj : JoinedIn (segment ℝ w w') w w' :=
          ((convex_segment w w').isPathConnected ⟨w, left_mem_segment ℝ w w'⟩).joinedIn _
            (left_mem_segment ℝ w w') _ (right_mem_segment ℝ w w')
        exact hj.map (hK.hc.mono fun v hv => hBO (hsub hv))
    · intro W hW hzW'
      have hop : IsOpen (B ∩ K ⁻¹' W ∩ Os) := by
        have hopen := hK.hc.isOpen_inter_preimage hK.isOpen hW
        simpa only [inter_assoc, inter_comm Os] using isOpen_ball.inter hopen
      have hWmem : (θ t : ℂ) ∈ K ⁻¹' W := by
        rw [mem_preimage, hK0]
        exact hzW'
      have hin : (θ t : ℂ) ∈ B ∩ K ⁻¹' W ∩ Os := ⟨⟨mem_ball_self hδ, hWmem⟩, (hθ t).1⟩
      obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hop _ hin
      let w : ℂ := (θ t : ℂ) + ((ε / 2 : ℝ) : ℂ) * I
      have hw : w ∈ ball (θ t : ℂ) ε := by
        rw [mem_ball, dist_eq_norm]
        simp only [w, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs]
        rw [abs_of_pos (by linarith)]
        linarith
      obtain ⟨⟨h3, h4⟩, -⟩ := hb hw
      refine ⟨K w, ⟨h4, ⟨w, h3, rfl⟩⟩, fun h5 => ?_⟩
      have := (hKZ w h3).mp h5
      simp only [w, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
        zero_add, add_zero] at this
      linarith
  · obtain ⟨U, h, g, c, hUO, hg0⟩ := (hT.2.2 z).exists_ballChart (hO.inter hZ.isOpen_compl) ⟨hz,
      hzZ⟩ (R := 1) (by norm_num)
    have hzU : z ∈ U := hg0 ▸ c.gm (mem_ball_self one_pos)
    have hdis : U ∩ Z = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      exact fun hx h => (hUO hx).2 h
    refine ⟨U, c.isOpen, hzU, fun x hx => (hUO hx).1,
      fun p hp q hq => ⟨U, fun x hx => (hUO hx).1, by rw [hdis]; exact finite_empty, ?_⟩,
      fun W _ hzW => ⟨z, ⟨hzW, hzU⟩, hzZ⟩⟩
    have hj : JoinedIn (ball (0 : ℂ) 1) (h p) (h q) :=
      ((convex_ball (0 : ℂ) 1).isPathConnected ⟨0, mem_ball_self one_pos⟩).joinedIn _ (c.hm hp.1) _
        (c.hm hq.1)
    have hj2 := hj.map c.gc
    rw [c.gh hp.1, c.gh hq.1] at hj2
    exact hj2.mono (by
      rintro _ ⟨x, hx, rfl⟩
      exact c.gm hx)

/-- **Joining points with finitely many crossings.** In a closed surface, let `O` be a connected
open set and `Z` a closed set which is
an arc near each of its points in `O`. Then any two distinct points of `O` off `Z` are joined in `O`
with finitely many crossings of `Z`. -/
theorem finReach_of_connected (hT : IsClosedSurface T) {O Z : Set T} (hO : IsOpen O)
  (hc : IsPreconnected O) (hZ : IsClosed Z)
    (hloc : ∀ z ∈ O ∩ Z, ∃ (a : unitInterval → T) (W : Set T), IsArcMap a ∧ IsOpen W ∧ z ∈ W
      ∧ z ∈ a '' Ioo 0 1 ∧ range a ⊆ Z ∧ Z ∩ W ⊆ range a)
    {x y : T} (hx : x ∈ O \ Z) (hy : y ∈ O \ Z) : FinReach O Z x y := by
  classical
  have hgood := fun z hz => exists_good_nhd hT hO hZ hloc (z := z) hz
  let P : T → Prop := fun z => ∃ N, IsOpen N ∧ z ∈ N ∧ N ⊆ O ∧ (∀ p ∈ N \ Z, ∀ q ∈ N \ Z, FinReach
    O Z p q) ∧ ∃ p ∈ N \ Z, FinReach O Z x p
  let A : Set T := {z | P z}
  let B : Set T := {z | z ∈ O ∧ ¬ P z}
  have hAo : IsOpen A := isOpen_iff_forall_mem_open.mpr fun z hz => by
    obtain ⟨N, h1, h2, h3, h4, h5⟩ := hz
    exact ⟨N, fun w hw => ⟨N, h1, hw, h3, h4, h5⟩, h1, h2⟩
  have hBo : IsOpen B := isOpen_iff_forall_mem_open.mpr fun z hz => by
    obtain ⟨N, h1, h2, h3, h4, -⟩ := hgood z hz.1
    refine ⟨N, fun w hw => ⟨h3 hw, fun hP => hz.2 ?_⟩, h1, h2⟩
    obtain ⟨N', h5, h6, -, h8, p, hp, h9⟩ := hP
    obtain ⟨M, -, h11, -, -, h12⟩ := hgood w (h3 hw)
    obtain ⟨q, ⟨⟨hq1, hq2⟩, hq3⟩, hq4⟩ := h12 (N ∩ N') (h1.inter h5) ⟨hw, h6⟩
    exact ⟨N, h1, h2, h3, h4, q, ⟨hq1, hq4⟩, h9.trans (h8 p hp q ⟨hq2, hq4⟩)⟩
  have hxA : x ∈ A := by
    obtain ⟨N, h1, h2, h3, h4, -⟩ := hgood x hx.1
    exact ⟨N, h1, h2, h3, h4, x, ⟨h2, hx.2⟩, {x}, by simpa using hx.1,
      (finite_singleton x).subset inter_subset_left, JoinedIn.refl rfl⟩
  have hcov : O ⊆ A ∪ B := fun z hz => by
    by_cases h : P z
    · exact .inl h
    · exact .inr ⟨hz, h⟩
  have hdis : O ∩ (A ∩ B) = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    exact fun _ h1 h2 => h2.2 h1
  by_cases hyA : y ∈ A
  · obtain ⟨N, -, h2, -, h4, p, hp, h5⟩ := hyA
    exact h5.trans (h4 p hp y ⟨h2, hy.2⟩)
  · exfalso
    obtain ⟨z, hz⟩ := hc A B hAo hBo hcov ⟨x, hx.1, hxA⟩ ⟨y, hy.1, hy.1, hyA⟩
    have : z ∈ O ∩ (A ∩ B) := hz
    rw [hdis] at this
    exact this

/-- The line form of `finReach_of_connected`. -/
theorem FinReach.exists_line [T2Space T] {O Z : Set T} {a b : T} (h : FinReach O Z a b)
  (hne : a ≠ b) :
    ∃ L ⊆ O, IsLineWithEnds L a b ∧ (L ∩ Z).Finite := by
  obtain ⟨K, h1, h2, h3⟩ := h
  obtain ⟨L, hL, hl⟩ := ((joinedIn_iff_eq_or_exists_isLineWithEnds h3.source_mem h3.target_mem).mp
    h3).resolve_left hne
  exact ⟨L, hL.trans h1, hl, h2.subset (inter_subset_inter_left _ hL)⟩

end GraphMinor.GM07
