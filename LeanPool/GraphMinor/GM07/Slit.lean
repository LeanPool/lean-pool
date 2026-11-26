/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.SlitPlane
public import LeanPool.GraphMinor.Surface.Collapse
public import LeanPool.GraphMinor.Surface.DiscRemove
public import LeanPool.GraphMinor.Surface.PushOff
public import LeanPool.GraphMinor.Surface.SurfacePull

/-!
# Cutting a surface along a line

Let `L` be a line of a surface that misses the boundary. We make `L` a segment of the real axis in a
chart, and remove the
open ball around it that has the segment as a diameter. The map `slitMap` of `SlitPlane.lean` folds
the circle onto the
segment, and it is the identity on a larger circle. So the surface without the open disc, with this
map, is the surface cut
along `L`. The surface with the disc back in is the old surface, and the inclusion is homotopic to
the map onto the old
surface. `IsSlit` collects these facts, and `exists_slit` proves them.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric Complex GraphMinor.Surface

universe u

local notation "𝕀" => unitInterval

theorem closedBall_disc {s : ℝ} (h0 : 0 < s) :
    IsClosedDisc (closedBall (0 : ℂ) s) ∧ discBd (closedBall (0 : ℂ) s) = sphere 0 s := by
  have h := isClosedDisc_of_convex (K := closedBall (0 : ℂ) s) (convex_closedBall 0 s)
    (by rw [interior_closedBall _ h0.ne']; exact ⟨0, by simpa using h0⟩) isBounded_closedBall
      isClosed_closedBall
  rw [frontier_closedBall _ h0.ne'] at h
  exact h

/-- The chart of a line, as a segment of the real axis, in a given open set. -/
theorem exists_ball_chart {T : Type} [TopologicalSpace T] (hT : IsClosedSurface T) {a : 𝕀 → T}
  (ha : IsArcMap a) {W : Set T}
    (hW : IsOpen W) (haW : range a ⊆ W) :
    ∃ (O : Set ℂ) (K : ℂ → T) (s : ℝ), StripChart O K ∧ 0 < s ∧ s < 1 ∧ closedBall 0 1 ⊆ O
      ∧ K '' closedBall 0 1 ⊆ W ∧
      K (-s : ℝ) = a 0 ∧ K (s : ℝ) = a 1 ∧ ∀ x, x ∈ range a ↔ ∃ z ∈ closedBall (0 : ℂ) 1, z.im = 0
        ∧ |z.re| ≤ s ∧ K z = x :=
  exists_stretched_arc_chart hT ha hW haW

private theorem exists_line_chart_in_cap {M : Type} [TopologicalSpace M]
    (hM : IsSurface M) {L : Set M} {u v : M}
    (hL : IsLineWithEnds L u v) (hd : L ∩ bd M = ∅)
    {W : Set M} (hW : IsOpen W) (hLW : L ⊆ W) :
    let B : Set ℂ := closedBall 0 1
    ∃ (T : Type) (_ : TopologicalSpace T) (j : M → T) (J : T → M)
      (O : Set ℂ) (K : ℂ → T) (s : ℝ),
      IsClosedSurface T ∧ IsClosedEmbedding j ∧ StripChart O K ∧
      0 < s ∧ s < 1 ∧ B ⊆ O ∧
      (∀ z ∈ B, K z ∈ range j) ∧ (∀ y ∈ range j, j (J y) = y) ∧
      ContinuousOn (J ∘ K) B ∧ InjOn (J ∘ K) B ∧ (J ∘ K) '' B ⊆ W ∧
      (∀ z ∈ B, J (K z) ∉ bd M) ∧ J (K (-s : ℝ)) = u ∧ J (K (s : ℝ)) = v ∧
      ∀ x, x ∈ L ↔ ∃ z ∈ B, z.im = 0 ∧ |z.re| ≤ s ∧ J (K z) = x := by
  classical
  obtain ⟨T, tT, j, Kc, hT, hj, hKc, hun, hint, -⟩ := exists_capAll M hM
  have ht2 : T2Space T := hT.2.1
  have ht2M : T2Space M := hM.2.1
  have hcM : CompactSpace M := hM.1
  obtain ⟨a₀, ha₀, hr, ha0, ha1⟩ := hL.exists_arc
  have ha : IsArcMap (j ∘ a₀) := ⟨hj.continuous.comp ha₀.1, hj.injective.comp ha₀.2⟩
  have hWT : IsOpen (Kcᶜ ∩ (j '' Wᶜ)ᶜ) := hKc.isOpen_compl.inter (hj.isClosedMap _
    hW.isClosed_compl).isOpen_compl
  have haW : range (j ∘ a₀) ⊆ Kcᶜ ∩ (j '' Wᶜ)ᶜ := by
    rintro _ ⟨t, rfl⟩
    have htL : a₀ t ∈ L := hr ▸ mem_range_self t
    refine ⟨fun hc => ?_, ?_⟩
    · have h1 : j (a₀ t) ∈ range j ∩ Kc := ⟨mem_range_self _, hc⟩
      rw [hint] at h1
      obtain ⟨y, hy, he⟩ := h1
      have h3 : a₀ t ∈ L ∩ bd M := ⟨htL, hj.injective he ▸ hy⟩
      rw [hd] at h3
      exact h3
    · rintro ⟨y, hy, he⟩
      exact hy (hj.injective he ▸ hLW htL)
  obtain ⟨O, K, s, hK, hs0, hs1, hBO, hBW, hKm, hKp, hrange⟩ := exists_ball_chart hT ha hWT haW
  let B : Set ℂ := closedBall 0 1
  have hKr : ∀ z ∈ B, K z ∈ range j := fun z hz => by
    have h1 := hun.ge (mem_univ (K z))
    exact h1.resolve_right (hBW ⟨z, hz, rfl⟩).1
  have : Nonempty M := by
    obtain ⟨y, -⟩ := hKr 0 (by simp [B])
    exact ⟨y⟩
  let J : T → M := Function.invFun j
  have hJ : ∀ x, J (j x) = x := Function.leftInverse_invFun hj.injective
  have hjJ : ∀ y ∈ range j, j (J y) = y := fun y ⟨x, hx⟩ => by rw [← hx, hJ]
  let K₀ : ℂ → M := fun z => J (K z)
  have hjK : ∀ z ∈ B, j (K₀ z) = K z := fun z hz => hjJ _ (hKr z hz)
  have hK₀i : InjOn K₀ B := fun z hz w hw he => hK.hi (hBO hz) (hBO hw)
    (by rw [← hjK z hz, ← hjK w hw, he])
  have hK₀c : ContinuousOn K₀ B := by
    rw [hj.isEmbedding.continuousOn_iff]
    exact (hK.hc.mono hBO).congr fun z hz => hjK z hz
  refine ⟨T, tT, j, J, O, K, s, hT, hj, hK, hs0, hs1, hBO, hKr, hjJ,
    hK₀c, hK₀i, ?_, ?_, ?_, ?_, fun x => ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    by_contra hn
    exact (hBW ⟨z, hz, rfl⟩).2 ⟨_, hn, hjK z hz⟩
  · intro z hz hb
    have h1 : j (K₀ z) ∈ range j ∩ Kc := hint ▸ mem_image_of_mem j hb
    rw [hjK z hz] at h1
    exact (hBW ⟨z, hz, rfl⟩).1 h1.2
  · rw [hKm, Function.comp_apply, ha0, hJ]
  · rw [hKp, Function.comp_apply, ha1, hJ]
  · constructor
    · intro hx
      rw [← hr] at hx
      obtain ⟨t, rfl⟩ := hx
      obtain ⟨z, hz, him, hre, hEq⟩ := (hrange (j (a₀ t))).mp ⟨t, rfl⟩
      exact ⟨z, hz, him, hre, by rw [hEq, hJ]⟩
    · rintro ⟨z, hz, him, hre, rfl⟩
      obtain ⟨t, ht⟩ := (hrange (K z)).mpr ⟨z, hz, him, hre, rfl⟩
      have he : a₀ t = J (K z) := hj.injective (by rw [hjK z hz]; exact ht)
      rw [← he, ← hr]
      exact mem_range_self t

/-- A chart of a disc around a line off the boundary: the line is a segment of a diameter. -/
theorem exists_line_chart_aux {M : Type} [TopologicalSpace M] (hM : IsSurface M) {L : Set M} {u v :
  M} (hL : IsLineWithEnds L u v) (hd : L ∩ bd M = ∅)
    {W : Set M} (hW : IsOpen W) (hLW : L ⊆ W) :
    ∃ (K₀ : ℂ → M) (s : ℝ), 0 < s ∧ s < 1 ∧ ContinuousOn K₀ (closedBall 0 1) ∧ InjOn K₀
      (closedBall 0 1) ∧ K₀ '' closedBall 0 1 ⊆ W ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, K₀ z ∉ bd M) ∧ K₀ (-s : ℝ) = u ∧ K₀ (s : ℝ) = v
        ∧ ∀ x, x ∈ L ↔ ∃ z ∈ closedBall (0 : ℂ) 1, z.im = 0 ∧ |z.re| ≤ s ∧ K₀ z = x := by
  obtain ⟨T, tT, j, J, O, K, s, _, _, _, hs0, hs1, _, _, _, hc, hi, hW, hb, hu, hv, hL⟩ :=
    exists_line_chart_in_cap hM hL hd hW hLW
  exact ⟨J ∘ K, s, hs0, hs1, hc, hi, hW, hb, hu, hv, hL⟩

/-- `E` is a closed disc off the boundary, and `c` is a homotopy from the identity to a map of the
surface that takes `E`
to the line `L`. Off the inside of `E`, this map is onto, it folds `discBd E` onto `L` with two
points over each inner point
of `L` and one over each end, and it is one to one elsewhere. -/
structure IsSlit {S : Type u} [TopologicalSpace S] (L : Set S) (u v : S) (E : Set S) (c : 𝕀 × S
  → S) : Prop where
  disc : IsClosedDisc E
  off_bd : E ∩ bd S = ∅
  cont : Continuous c
  c0 : ∀ x, c (0, x) = x
  fix : ∀ x ∈ bd S, ∀ t, c (t, x) = x
  bd_iff : ∀ x, c (1, x) ∈ bd S ↔ x ∈ bd S
  onto : ∀ y, ∃ x, x ∉ discInt E ∧ c (1, x) = y
  fold : ∀ x ∈ discBd E, c (1, x) ∈ L
  off : ∀ x, x ∉ E → c (1, x) ∉ L
  sub : L ⊆ E
  inj : ∀ x y, x ∉ discInt E → y ∉ discInt E → c (1, x) = c (1, y) →
    x = y ∨ (x ∈ discBd E ∧ y ∈ discBd E ∧ c (1, x) ≠ u ∧ c (1, x) ≠ v)
  two : ∀ y ∈ L, y ≠ u → y ≠ v → ∃ x x', x ≠ x' ∧ x ∈ discBd E ∧ x' ∈ discBd E ∧ c (1, x) = y ∧ c
    (1, x') = y
  /-- Off the inside of `E`, each fiber of the map has at most two points. -/
  pair : ∀ y, ∃ a b, {x | x ∉ discInt E ∧ c (1, x) = y} ⊆ {a, b}

/-- Off the inside of `E`, the map has finite fibers. -/
theorem IsSlit.fiber {S : Type u} [TopologicalSpace S] {L : Set S} {u v : S} {E : Set S}
    {c : 𝕀 × S → S} (hs : IsSlit L u v E c) (y : S) :
    {x | x ∉ discInt E ∧ c (1, x) = y}.Finite := by
  obtain ⟨a, b, h⟩ := hs.pair y
  exact ((finite_singleton b).insert a).subset h

private theorem discInt_image_closedBall
    {M : Type}
    [TopologicalSpace M]
    (s : ℝ)
    (B : Set ℂ)
    (K₀ : ℂ → M)
    (hK₀i : InjOn K₀ B)
    (hsB : closedBall 0 s ⊆ B)
    (hEb : discBd (K₀ '' closedBall 0 s) = K₀ '' sphere 0 s) :
    discInt (K₀ '' closedBall 0 s) = K₀ '' ball 0 s := by
  let E := K₀ '' closedBall 0 s
  ext x
  simp only [discInt, mem_sdiff, hEb]
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, h2⟩
    refine ⟨z, ?_, rfl⟩
    have hz' : ‖z‖ ≤ s := mem_closedBall_zero_iff.mp hz
    refine mem_ball_zero_iff.mpr (lt_of_le_of_ne hz' fun he => h2 ⟨z,
      mem_sphere_zero_iff_norm.mpr he, rfl⟩)
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨z, ball_subset_closedBall hz, rfl⟩, ?_⟩
    rintro ⟨w, hw, he⟩
    have h1 := hK₀i (hsB (sphere_subset_closedBall hw)) (hsB (ball_subset_closedBall hz)) he
    rw [h1, mem_sphere_zero_iff_norm] at hw
    exact (mem_ball_zero_iff.mp hz).ne hw

private theorem slit_boundary_collision
    {M : Type}
    [TopologicalSpace M]
    {u : M}
    {v : M}
    (s : ℝ)
    (hs0 : 0 < s)
    (hs1 : s < 1)
    (B : Set ℂ)
    (hslB : ∀ z ∈ B, slitMap s z ∈ B)
    (K₀ : ℂ → M)
    (hK₀i : InjOn K₀ B)
    (c₀ : 𝕀 × M → M)
    (hc₀2 : ∀ (p : 𝕀), ∀ x ∉ K₀ '' B, c₀ (p, x) = x)
    (E : Set M)
    (hEb : discBd E = K₀ '' sphere 0 s)
    (hreal : ∀ {x : ℝ}, |x| ≤ s → ↑x ∈ B)
    (hu : K₀ ↑(-s) = u)
    (hv : K₀ ↑s = v)
    (hnotint : ∀ {z : ℂ}, z ∈ B → K₀ z ∉ discInt E → s ≤ ‖z‖)
    (hc₀s : ∀ z ∈ B, c₀ (1, K₀ z) = K₀ (slitMap s z)) :
    ∀ (x y : M), x ∉ discInt E → y ∉ discInt E → c₀ (1, x) = c₀ (1, y) → x = y ∨ x ∈ discBd E ∧ y
      ∈ discBd E ∧ c₀ (1, x) ≠ u ∧ c₀ (1, x) ≠ v := by
  intro x y hx hy he
  by_cases hin : x ∈ K₀ '' B <;> by_cases hin' : y ∈ K₀ '' B
  · obtain ⟨z, hz, rfl⟩ := hin
    obtain ⟨w, hw, rfl⟩ := hin'
    rw [hc₀s z hz, hc₀s w hw] at he
    have h1 := hK₀i (hslB z hz) (hslB w hw) he
    rcases slitMap_eq hs0 hs1 (hnotint hz hx) (hnotint hw hy) h1 with rfl | ⟨h2, h3, h4⟩
    · exact .inl rfl
    by_cases hre : z.im = 0
    · have : w = z := by rw [h4]; exact Complex.conj_eq_iff_im.mpr hre
      rw [this]
      exact .inl rfl
    right
    refine ⟨hEb ▸ ⟨z, mem_sphere_zero_iff_norm.mpr h2, rfl⟩, hEb ▸ ⟨w,
      mem_sphere_zero_iff_norm.mpr h3, rfl⟩, ?_, ?_⟩
    all_goals
      rw [hc₀s z hz, slitMap_of_norm_le hs0 hs1 h2.le]
      intro hb
      have hb' : K₀ (z.re : ℂ) = K₀ _ := hb.trans (by first | exact hu.symm | exact hv.symm)
      have hre1 : |z.re| ≤ s := (Complex.abs_re_le_norm z).trans h2.le
      have h6 := congrArg Complex.re (hK₀i (hreal hre1) (hreal (x := _)
        (by first | rw [abs_neg, abs_of_pos hs0] | rw [abs_of_pos hs0])) hb')
      simp only [ofReal_re] at h6
      have h7 : z.re ^ 2 + z.im ^ 2 = s ^ 2 := by
        rw [← h2, Complex.sq_norm, Complex.normSq_apply]
        ring
      have h8 : z.im ^ 2 = 0 := by rw [h6] at h7; nlinarith
      exact hre (pow_eq_zero_iff (two_ne_zero)|>.mp h8)
  · obtain ⟨z, hz, rfl⟩ := hin
    rw [hc₀s z hz, hc₀2 _ y hin'] at he
    exact absurd ⟨_, hslB z hz, he⟩ hin'
  · obtain ⟨w, hw, rfl⟩ := hin'
    rw [hc₀s w hw, hc₀2 _ x hin] at he
    exact absurd ⟨_, hslB w hw, he.symm⟩ hin
  · rw [hc₀2 _ x hin, hc₀2 _ y hin'] at he
    exact .inl he

private theorem slit_boundary_pair
    {M : Type}
    [TopologicalSpace M]
    {L : Set M}
    {u : M}
    {v : M}
    (s : ℝ)
    (hs0 : 0 < s)
    (hs1 : s < 1)
    (B : Set ℂ)
    (K₀ : ℂ → M)
    (hK₀i : InjOn K₀ B)
    (c₀ : 𝕀 × M → M)
    (E : Set M)
    (hEb : discBd E = K₀ '' sphere 0 s)
    (hjp : ∀ (x : M), x ∈ L ↔ ∃ z ∈ B, z.im = 0 ∧ |z.re| ≤ s ∧ K₀ z = x)
    (hmem : ∀ {z : ℂ}, ‖z‖ ≤ 1 → z ∈ B)
    (hu : K₀ ↑(-s) = u)
    (hv : K₀ ↑s = v)
    (hc₀s : ∀ z ∈ B, c₀ (1, K₀ z) = K₀ (slitMap s z)) :
    ∀ y ∈ L, y ≠ u → y ≠ v → ∃ x x', x ≠ x' ∧ x ∈ discBd E ∧ x' ∈ discBd E ∧ c₀ (1, x) = y ∧ c₀
      (1, x') = y := by
  intro y hy hyu hyv
  obtain ⟨z, hz, h2, h3, rfl⟩ := (hjp y).mp hy
  have hlt : |z.re| < s := by
    refine lt_of_le_of_ne h3 fun he => ?_
    have hz_eq : ∀ r : ℝ, z.re = r → z = (r : ℂ) := fun r hr => Complex.ext (by simpa using hr)
      (by simpa using h2)
    rcases abs_eq hs0.le |>.mp he with h5 | h5
    · exact hyv (by rw [hz_eq _ h5, hv])
    · exact hyu (by rw [hz_eq _ h5, ← hu])
  set r := Real.sqrt (s ^ 2 - z.re ^ 2) with hr
  have hs2 : 0 < s ^ 2 - z.re ^ 2 := by
    have : z.re ^ 2 < s ^ 2 := by
      rw [sq_lt_sq, abs_of_pos hs0]
      exact hlt
    linarith
  have hrpos : 0 < r := Real.sqrt_pos.mpr hs2
  have hr2 : r ^ 2 = s ^ 2 - z.re ^ 2 := Real.sq_sqrt hs2.le
  have hn : ∀ σ : ℝ, σ ^ 2 = 1 → ‖(⟨z.re, σ * r⟩ : ℂ)‖ = s := fun σ hσ => by
    rw [norm_of_re_im, mul_pow, hσ, one_mul, hr2]
    have : z.re ^ 2 + (s ^ 2 - z.re ^ 2) = s ^ 2 := by ring
    rw [this, Real.sqrt_sq hs0.le]
  have hzeq : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using h2)
  have hfold : ∀ σ : ℝ, σ ^ 2 = 1 → c₀ (1, K₀ ⟨z.re, σ * r⟩) = K₀ z := fun σ hσ => by
    have h5 := hn σ hσ
    rw [hc₀s _ (hmem (by linarith)), slitMap_of_norm_le hs0 hs1 h5.le]
    rw [hzeq]
    simp
  have hb : ∀ σ : ℝ, σ ^ 2 = 1 → K₀ ⟨z.re, σ * r⟩ ∈ discBd E := fun σ hσ =>
    hEb ▸ ⟨_, mem_sphere_zero_iff_norm.mpr (hn σ hσ), rfl⟩
  refine ⟨K₀ ⟨z.re, 1 * r⟩, K₀ ⟨z.re, -1 * r⟩, ?_, hb 1 (by norm_num), hb (-1) (by norm_num),
    hfold 1 (by norm_num), hfold (-1) (by norm_num)⟩
  intro he
  have hleft : ‖(⟨z.re, 1 * r⟩ : ℂ)‖ ≤ 1 := (hn 1 (by norm_num)).le.trans hs1.le
  have hright : ‖(⟨z.re, -1 * r⟩ : ℂ)‖ ≤ 1 := (hn (-1) (by norm_num)).le.trans hs1.le
  have h5 := hK₀i (hmem hleft) (hmem hright) he
  have h6 := congrArg Complex.im h5
  simp only at h6
  linarith

private theorem slit_boundary_fiber
    {M : Type}
    [TopologicalSpace M]
    (s : ℝ)
    (hs0 : 0 < s)
    (hs1 : s < 1)
    (B : Set ℂ)
    (hslB : ∀ z ∈ B, slitMap s z ∈ B)
    (K₀ : ℂ → M)
    (hK₀i : InjOn K₀ B)
    (c₀ : 𝕀 × M → M)
    (hc₀2 : ∀ (p : 𝕀), ∀ x ∉ K₀ '' B, c₀ (p, x) = x)
    (E : Set M)
    (hnotint : ∀ {z : ℂ}, z ∈ B → K₀ z ∉ discInt E → s ≤ ‖z‖)
    (hc₀s : ∀ z ∈ B, c₀ (1, K₀ z) = K₀ (slitMap s z)) :
    ∀ (y : M), ∃ a b, {x | x ∉ discInt E ∧ c₀ (1, x) = y} ⊆ {a, b} := by
  intro y₀
  by_cases hne : {x | x ∉ discInt E ∧ c₀ (1, x) = y₀}.Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact ⟨y₀, y₀, empty_subset _⟩
  obtain ⟨x₀, hx₀, rfl⟩ := hne
  by_cases hin : x₀ ∈ K₀ '' B
  · obtain ⟨z, hz, rfl⟩ := hin
    refine ⟨K₀ z, K₀ ((starRingEnd ℂ) z), ?_⟩
    rintro y ⟨hy, he⟩
    by_cases hin' : y ∈ K₀ '' B
    · obtain ⟨w, hw, rfl⟩ := hin'
      rw [hc₀s w hw, hc₀s z hz] at he
      rcases slitMap_eq hs0 hs1 (hnotint hz hx₀) (hnotint hw hy) (hK₀i (hslB z hz)
        (hslB w hw) he.symm) with rfl | ⟨-, -, h4⟩
      · exact .inl rfl
      · rw [h4]
        exact .inr rfl
    · rw [hc₀s z hz, hc₀2 _ y hin'] at he
      exact absurd ⟨_, hslB z hz, he.symm⟩ hin'
  · refine ⟨x₀, x₀, ?_⟩
    rintro y ⟨hy, he⟩
    by_cases hin' : y ∈ K₀ '' B
    · obtain ⟨w, hw, rfl⟩ := hin'
      rw [hc₀s w hw, hc₀2 _ x₀ hin] at he
      exact absurd ⟨_, hslB w hw, he⟩ hin
    · rw [hc₀2 _ y hin', hc₀2 _ x₀ hin] at he
      exact .inl he

/-- A line off the boundary of a surface has a slit. -/
theorem exists_slit_aux {M : Type} [TopologicalSpace M] (hM : IsSurface M) {L : Set M} {u v : M}
    (hL : IsLineWithEnds L u v) (hd : L ∩ bd M = ∅) : ∃ E c, IsSlit L u v E c := by
  classical
  obtain ⟨T, tT, j, J, O, K, s, hT, hj, hK, hs0, hs1, hBO, hKr, hjJ,
    hK₀c, hK₀i, _, hK₀bd, hu, hv, hjp⟩ :=
    exists_line_chart_in_cap hM hL hd isOpen_univ (subset_univ L)
  have ht2 : T2Space T := hT.2.1
  have ht2M : T2Space M := hM.2.1
  have hcM : CompactSpace M := hM.1
  let B : Set ℂ := closedBall 0 1
  have hBc : IsCompact B := isCompact_closedBall _ _
  let K₀ : ℂ → M := J ∘ K
  change (∀ z ∈ B, K₀ z ∉ bd M) at hK₀bd
  have hjK : ∀ z ∈ B, j (K₀ z) = K z := fun z hz => hjJ _ (hKr z hz)
  let Φ : 𝕀 × ℂ → ℂ := fun q => ((1 - q.1.1 : ℝ) : ℂ) * q.2 + ((q.1.1 : ℝ) : ℂ) * slitMap s q.2
  have hsl := continuous_slitMap hs0
  have hΦc : Continuous Φ := by
    have h1 : Continuous fun q : 𝕀 × ℂ => ((q.1.1 : ℝ) : ℂ) := continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_fst)
    have h2 : Continuous fun q : 𝕀 × ℂ => ((1 - q.1.1 : ℝ) : ℂ) := continuous_ofReal.comp
      (by fun_prop)
    exact (h2.mul continuous_snd).add (h1.mul (hsl.comp continuous_snd))
  have hslB : ∀ z ∈ B, slitMap s z ∈ B := fun z hz => by
    have h1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    exact mem_closedBall_zero_iff.mpr (norm_slitMap_le hs0 hs1 h1)
  have hΦm : ∀ p, ∀ z ∈ B, Φ (p, z) ∈ B := fun p z hz => by
    have h1 := (convex_closedBall (0 : ℂ) 1) hz (hslB z hz) (a := 1 - p.1) (b := p.1)
      (by linarith [p.2.2]) p.2.1 (by ring)
    have h2 : Φ (p, z) = (1 - p.1) • z + p.1 • slitMap s z := by simp [Φ, Complex.real_smul]
    rw [h2]
    exact h1
  have hΦid : ∀ p, ∀ z ∈ frontier B, Φ (p, z) = z := fun p z hz => by
    have hz' : z ∈ sphere (0 : ℂ) 1 := by rwa [frontier_closedBall _ one_ne_zero] at hz
    have h1 : slitMap s z = z := slitMap_of_norm_eq_one hs1 (mem_sphere_zero_iff_norm.mp hz')
    simp only [Φ, h1]
    push_cast
    ring
  obtain ⟨c, hcc, hc1, hc2⟩ := exists_glue hK hBc hBO Φ hΦc.continuousOn hΦm hΦid
  have hΦ0 : ∀ z, Φ (0, z) = z := fun z => by simp [Φ]
  have hΦ1 : ∀ z, Φ (1, z) = slitMap s z := fun z => by simp [Φ]
  have hrj : ∀ q : 𝕀 × M, c (q.1, j q.2) ∈ range j := fun q => by
    by_cases hin : j q.2 ∈ K '' B
    · obtain ⟨z, hz, he⟩ := hin
      rw [← he, hc1 _ z hz]
      exact hKr _ (hΦm _ z hz)
    · rw [hc2 _ _ hin]
      exact mem_range_self _
  let c₀ : 𝕀 × M → M := fun q => J (c (q.1, j q.2))
  have hjc : ∀ q, j (c₀ q) = c (q.1, j q.2) := fun q => hjJ _ (hrj q)
  have hc₀c : Continuous c₀ := by
    rw [hj.isEmbedding.continuous_iff]
    have : j ∘ c₀ = fun q => c (q.1, j q.2) := funext hjc
    rw [this]
    exact hcc.comp (continuous_fst.prodMk (hj.continuous.comp continuous_snd))
  have hc₀1 : ∀ p, ∀ z ∈ B, c₀ (p, K₀ z) = K₀ (Φ (p, z)) := fun p z hz => hj.injective (by
    rw [hjc, hjK z hz, hc1 _ z hz, hjK _ (hΦm p z hz)])
  have hc₀2 : ∀ p, ∀ x, x ∉ K₀ '' B → c₀ (p, x) = x := fun p x hx => hj.injective (by
    rw [hjc]
    refine hc2 _ _ ?_
    rintro ⟨z, hz, he⟩
    exact hx ⟨z, hz, hj.injective (by rw [hjK z hz, he])⟩)
  have hsB : closedBall (0 : ℂ) s ⊆ B := closedBall_subset_closedBall hs1.le
  obtain ⟨hD, hDb⟩ := closedBall_disc hs0
  obtain ⟨K', hK'c, hK'l⟩ := exists_inv_of_compactOn (hBc.of_isClosed_subset isClosed_closedBall
    hsB) (hK₀c.mono hsB)
    (hK₀i.mono hsB)
  obtain ⟨hE, hEb⟩ := hD.image (hK₀c.mono hsB) hK'c hK'l
  set E := K₀ '' closedBall (0 : ℂ) s with hEdef
  rw [hDb] at hEb
  have hint' : discInt E = K₀ '' ball 0 s := by
    exact discInt_image_closedBall (M := M) s B K₀ hK₀i hsB hEb
  have hmem : ∀ {z : ℂ}, ‖z‖ ≤ 1 → z ∈ B := fun h => mem_closedBall_zero_iff.mpr h
  have hreal : ∀ {x : ℝ}, |x| ≤ s → (x : ℂ) ∈ B := fun {x} h => hmem (by
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith)
  have hnotint : ∀ {z}, z ∈ B → K₀ z ∉ discInt E → s ≤ ‖z‖ := fun {z} hz hn => by
    by_contra hlt
    exact hn (hint' ▸ ⟨z, mem_ball_zero_iff.mpr (not_le.mp hlt), rfl⟩)
  have hc₀s : ∀ z ∈ B, c₀ (1, K₀ z) = K₀ (slitMap s z) := fun z hz => by rw [hc₀1 _ z hz, hΦ1]
  have hLsub : L ⊆ E := by
    intro x hx
    obtain ⟨z, hz, h2, h3, rfl⟩ := (hjp x).mp hx
    refine ⟨z, mem_closedBall_zero_iff.mpr ?_, rfl⟩
    rw [Complex.norm_eq_sqrt_sq_add_sq, h2]
    simpa [Real.sqrt_sq_eq_abs] using h3
  have hEB : E ⊆ K₀ '' B := image_mono hsB
  refine ⟨E, c₀, hE, ?_, hc₀c, ?_, ?_, ?_, ?_, ?_, ?_, hLsub, ?_, ?_, ?_⟩
  · rw [eq_empty_iff_forall_notMem]
    rintro x ⟨⟨z, hz, rfl⟩, hb⟩
    exact hK₀bd z (hsB hz) hb
  · intro x
    by_cases hx : x ∈ K₀ '' B
    · obtain ⟨z, hz, rfl⟩ := hx
      rw [hc₀1 _ z hz, hΦ0]
    · exact hc₀2 _ x hx
  · intro x hx t
    exact hc₀2 _ x fun ⟨z, hz, he⟩ => hK₀bd z hz (he ▸ hx)
  · intro x
    by_cases hx : x ∈ K₀ '' B
    · obtain ⟨z, hz, rfl⟩ := hx
      rw [hc₀s z hz]
      exact ⟨fun h => (hK₀bd _ (hslB z hz) h).elim, fun h => (hK₀bd _ hz h).elim⟩
    · rw [hc₀2 _ x hx]
  · intro y
    by_cases hy : y ∈ K₀ '' B
    · obtain ⟨w, hw, rfl⟩ := hy
      obtain ⟨z, h1, h2, rfl⟩ := exists_slitMap_eq hs0 hs1 (mem_closedBall_zero_iff.mp hw)
      refine ⟨K₀ z, ?_, hc₀s z (hmem h2)⟩
      rw [hint']
      rintro ⟨z', hz', he⟩
      have h3 := hK₀i (hsB (ball_subset_closedBall hz')) (hmem h2) he
      rw [h3, mem_ball_zero_iff] at hz'
      linarith
    · refine ⟨y, fun h => hy (hEB h.1), hc₀2 _ y hy⟩
  · intro x hx
    rw [hEb] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hz' : ‖z‖ = s := mem_sphere_zero_iff_norm.mp hz
    have hzB : z ∈ B := hsB (sphere_subset_closedBall hz)
    rw [hc₀s z hzB, slitMap_of_norm_le hs0 hs1 hz'.le]
    have h1 : |z.re| ≤ s := (Complex.abs_re_le_norm z).trans hz'.le
    exact (hjp _).mpr ⟨_, hreal h1, by simp, by simpa using h1, rfl⟩
  · intro x hx hL'
    by_cases hin : x ∈ K₀ '' B
    · obtain ⟨z, hz, rfl⟩ := hin
      have hzs : s < ‖z‖ := by
        by_contra hle
        exact hx ⟨z, mem_closedBall_zero_iff.mpr (not_lt.mp hle), rfl⟩
      rw [hc₀s z hz] at hL'
      obtain ⟨w, hw, h2, h3, he⟩ := (hjp _).mp hL'
      have h4 := hK₀i hw (hslB z hz) he
      have h5 : (slitMap s z).im = 0 := by rw [← h4, h2]
      have h6 := slitMap_notMem_segment hs0 hs1 hzs h5
      rw [h4, slitMap_re] at h3
      linarith
    · rw [hc₀2 _ x hin] at hL'
      exact hx (hLsub hL')
  · exact slit_boundary_collision (M := M) (u := u) (v := v) s hs0 hs1 B hslB K₀ hK₀i c₀ hc₀2 E
      hEb hreal hu hv hnotint hc₀s
  · exact slit_boundary_pair (M := M) (L := L) (u := u) (v := v) s hs0 hs1 B K₀ hK₀i c₀ E hEb hjp
      hmem hu hv hc₀s
  · exact slit_boundary_fiber (M := M) s hs0 hs1 B hslB K₀ hK₀i c₀ hc₀2 E hnotint hc₀s
/-- A slit, on a surface in any universe: we move it from the model. -/
theorem exists_slit {S : Type u} [TopologicalSpace S] {M : Type} [TopologicalSpace M]
  (hM : IsSurface M) (h : S ≃ₜ M)
    {L : Set S} {u v : S} (hL : IsLineWithEnds L u v) (hd : L ∩ bd S = ∅) : ∃ E c, IsSlit L u v E c
      := by
  have hb : ∀ x, h x ∈ bd M ↔ x ∈ bd S := fun x => by
    rw [← image_bd_homeomorph h]
    exact h.injective.mem_set_image
  have hL' : IsLineWithEnds (h '' L) (h u) (h v) := by
    obtain ⟨f, h0, h1⟩ := hL
    exact ⟨f.trans (h.image L), congrArg h h0, congrArg h h1⟩
  obtain ⟨E₀, c₀, hs⟩ := exists_slit_aux hM hL' (by
    rw [eq_empty_iff_forall_notMem]
    rintro _ ⟨⟨x, hx, rfl⟩, hxb⟩
    have : x ∈ L ∩ bd S := ⟨hx, (hb x).mp hxb⟩
    rw [hd] at this
    exact this)
  obtain ⟨hE, hEb⟩ := hs.disc.image (f := h.symm) (f' := h) h.symm.continuous.continuousOn
    h.continuous.continuousOn
    fun x _ => h.apply_symm_apply x
  have hmem : ∀ {A : Set M} {x : S}, x ∈ h.symm '' A ↔ h x ∈ A := fun {A x} => by
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [h.apply_symm_apply]
    · intro hx
      exact ⟨h x, hx, h.symm_apply_apply x⟩
  have hint : ∀ x, x ∈ discInt (h.symm '' E₀) ↔ h x ∈ discInt E₀ := fun x => by
    simp only [discInt, mem_sdiff, hEb, hmem]
  have hmemL : ∀ {x : S}, h x ∈ h '' L ↔ x ∈ L := h.injective.mem_set_image
  refine ⟨h.symm '' E₀, fun q => h.symm (c₀ (q.1, h q.2)), hE, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hxb⟩
    have : h x ∈ E₀ ∩ bd M := ⟨hmem.mp hx, (hb x).mpr hxb⟩
    rw [hs.off_bd] at this
    exact this
  · exact h.symm.continuous.comp (hs.cont.comp (continuous_fst.prodMk
      (h.continuous.comp continuous_snd)))
  · intro x
    simp [hs.c0]
  · intro x hx t
    simp [hs.fix _ ((hb x).mpr hx)]
  · intro x
    rw [← hb, h.apply_symm_apply, hs.bd_iff, hb]
  · intro y
    obtain ⟨x, hx, he⟩ := hs.onto (h y)
    refine ⟨h.symm x, fun hi => hx (by simpa using (hint _).mp hi), ?_⟩
    simp [he]
  · intro x hx
    have h1 : h x ∈ discBd E₀ := by rw [hEb] at hx; exact hmem.mp hx
    have h2 := hs.fold _ h1
    obtain ⟨y, hy, he⟩ := h2
    change h.symm _ ∈ L
    rw [← he, h.symm_apply_apply]
    exact hy
  · intro x hx hL2
    refine hs.off (h x) (fun h1 => hx (hmem.mpr h1)) ?_
    have : h (h.symm (c₀ (1, h x))) ∈ h '' L := mem_image_of_mem h hL2
    rwa [h.apply_symm_apply] at this
  · intro x hx
    exact hmem.mpr (hs.sub (mem_image_of_mem h hx))
  · intro x y hx hy he
    have he' : c₀ (1, h x) = c₀ (1, h y) := h.symm.injective he
    rcases hs.inj (h x) (h y) (fun h1 => hx ((hint x).mpr h1)) (fun h1 => hy
      ((hint y).mpr h1)) he' with h1 | ⟨h1, h2, h3, h4⟩
    · exact .inl (h.injective h1)
    · right
      rw [hEb]
      refine ⟨hmem.mpr h1, hmem.mpr h2, fun h5 => h3 ?_, fun h5 => h4 ?_⟩
      · have := congrArg h h5
        simpa using this
      · have := congrArg h h5
        simpa using this
  · intro y hy hyu hyv
    obtain ⟨x, x', hne, hx, hx', h1, h2⟩ := hs.two (h y) (mem_image_of_mem h hy) (fun he => hyu
      (h.injective he)) (fun he => hyv (h.injective he))
    refine ⟨h.symm x, h.symm x', fun he => hne (h.symm.injective he), ?_, ?_, ?_, ?_⟩
    · rw [hEb]
      exact mem_image_of_mem _ hx
    · rw [hEb]
      exact mem_image_of_mem _ hx'
    · simp [h1]
    · simp [h2]
  · intro y
    obtain ⟨a, b, hab⟩ := hs.pair (h y)
    refine ⟨h.symm a, h.symm b, ?_⟩
    rintro x ⟨hx, he⟩
    have hx' : h x ∈ {x | x ∉ discInt E₀ ∧ c₀ (1, x) = h y} := by
      refine ⟨fun h1 => hx ((hint x).mpr h1), ?_⟩
      have := congrArg h he
      simpa using this
    rcases hab hx' with h1 | h1
    · exact .inl (by rw [← h1, h.symm_apply_apply])
    · exact .inr (by rw [← mem_singleton_iff.mp h1, h.symm_apply_apply]; rfl)

end GraphMinor.GM07
