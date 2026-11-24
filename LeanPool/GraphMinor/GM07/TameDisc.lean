/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.JoinDiscs
public import LeanPool.GraphMinor.GM07.Slit
public import LeanPool.GraphMinor.Surface.Collar
public import LeanPool.GraphMinor.Surface.EdgeLens
public import LeanPool.GraphMinor.GM07.StarDisc
public import LeanPool.GraphMinor.GM14.DiscSlope
public import LeanPool.GraphMinor.GM12.Section3OneDiscComplement

/-!
# Growing a disc around a part of a drawing

The tools here fill in two sentences of Graph Minors VII: "by Menger's theorem" in the use of Graph
Minors III, (4.1) for (5.8), and "because `G` is
boundary-linked" on page 238. Each says that a part of a drawing, cut off from the rest by a set `X`
of vertices, is cut off by a normal `O`-arc through `X`.
We grow a closed disc around the part.

First, `exists_disc_push_off`: a closed disc grows a little past its boundary, keeping away from a
closed set.
-/

public section

namespace GraphMinor.GM07

open Set Topology Metric Function GraphMinor.Surface GraphMinor.GM11

/-- Scaling by a bounded factor is continuous at `0`. -/
theorem continuous_mul_of_bounded {u : ℂ → ℝ} (hu : ContinuousOn u {0}ᶜ) {M : ℝ} (hM : ∀ z, |u z|
  ≤ M) : Continuous fun z : ℂ => z * (u z : ℂ) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    rw [ContinuousAt, zero_mul]
    have h1 : Filter.Tendsto (fun z : ℂ => ‖z‖ * M) (𝓝 0) (𝓝 0) := by
      have : Continuous fun z : ℂ => ‖z‖ * M := by fun_prop
      simpa using this.tendsto 0
    refine squeeze_zero_norm (fun z => ?_) h1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM z) (norm_nonneg z)
  · have h2 : ContinuousAt u z := hu.continuousAt (isOpen_compl_singleton.mem_nhds hz)
    exact continuousAt_id.mul (Complex.continuous_ofReal.continuousAt.comp h2)

/-- The point of the unit circle in the direction of `z`. -/
noncomputable def dirOf (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

theorem norm_dirOf {z : ℂ} (hz : z ≠ 0) : ‖dirOf z‖ = 1 := by
  rw [dirOf, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr hz)]

theorem continuousOn_dirOf : ContinuousOn dirOf {0}ᶜ := by
  refine ContinuousOn.div continuousOn_id (by fun_prop) fun z hz => ?_
  simpa using hz

theorem eq_mul_dirOf {z : ℂ} (hz : z ≠ 0) : z = (‖z‖ : ℂ) * dirOf z := by
  have : (‖z‖ : ℂ) ≠ 0 := by simpa using hz
  rw [dirOf]
  field_simp

theorem dirOf_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : dirOf z = z := by
  simp [dirOf, hz]

theorem dirOf_mul_pos {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : z ≠ 0) : dirOf ((r : ℂ) * z) = dirOf z
  := by
  have h0 : (r : ℂ) ≠ 0 := by simpa using hr.ne'
  have h1 : (‖z‖ : ℂ) ≠ 0 := by simpa using hz
  rw [dirOf, dirOf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  push_cast
  field_simp

variable {T : Type*} [TopologicalSpace T] [T2Space T]

private theorem radial_push_injective
    (Z₁ : Set ℂ)
    (m : ℂ → ℂ)
    (u : ℂ → ℝ)
    (hu : u = fun z => 1 + infDist (dirOf z) Z₁ / 2)
    (hun : ∀ (z : ℂ), 1 ≤ u z)
    (hm0 : m 0 = 0)
    (hmne : ∀ (z : ℂ), z ≠ 0 → m z ≠ 0)
    (hnorm : ∀ (z : ℂ), z ≠ 0 → ‖m z‖ = ‖z‖ * u z)
    (hdir : ∀ (z : ℂ), z ≠ 0 → dirOf (m z) = dirOf z)
    (a : ℂ)
    (b : ℂ)
    (he : m a = m b) :
    a = b := by
  by_cases ha : a = 0
  · subst ha
    by_contra hne
    exact hmne b (Ne.symm hne) (by rw [← he, hm0])
  by_cases hb : b = 0
  · subst hb
    exact absurd (he.trans hm0) (hmne a ha)
  have h1 : dirOf a = dirOf b := by rw [← hdir a ha, he, hdir b hb]
  have h2 : u a = u b := by simp only [hu, h1]
  have h3 : ‖a‖ = ‖b‖ := by
    have := hnorm a ha
    rw [he, hnorm b hb, h2] at this
    have h4 := hun b
    exact (mul_right_cancel₀ (by linarith) this).symm
  rw [eq_mul_dirOf ha, eq_mul_dirOf hb, h1, h3]

private theorem radial_push_avoids_outer_set
    (Z₁ : Set ℂ)
    (m : ℂ → ℂ)
    (u : ℂ → ℝ)
    (hu : u = fun z => 1 + infDist (dirOf z) Z₁ / 2)
    (hun : ∀ (z : ℂ), 1 ≤ u z)
    (hm0 : m 0 = 0)
    (hmne : ∀ (z : ℂ), z ≠ 0 → m z ≠ 0)
    (hnorm : ∀ (z : ℂ), z ≠ 0 → ‖m z‖ = ‖z‖ * u z)
    (hdir : ∀ (z : ℂ), z ≠ 0 → dirOf (m z) = dirOf z)
    (z : ℂ)
    (hz : z ∈ closedBall 0 1)
    (h1 : m z ∈ Z₁) :
    ‖m z‖ ≤ 1 := by
  by_contra hgt
  push Not at hgt
  have h0 : z ≠ 0 := fun h => by simp [h, hm0] at hgt; linarith
  have hz1 : ‖z‖ ≤ 1 := by simpa using hz
  have hn := hnorm z h0
  set d := dirOf z with hd
  have hdn : ‖d‖ = 1 := norm_dirOf h0
  have h2 : m z = (‖m z‖ : ℂ) * d := by
    have h7 := eq_mul_dirOf (hmne z h0)
    rw [hdir z h0] at h7
    exact h7
  have h3 : dist d (m z) = ‖m z‖ - 1 := by
    rw [dist_comm, dist_eq_norm]
    conv_lhs => rw [h2]
    have heq : (‖m z‖ : ℂ) * d - d = ((‖m z‖ - 1 : ℝ) : ℂ) * d := by
      push_cast
      ring
    rw [heq, norm_mul, hdn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have h4 : infDist d Z₁ ≤ ‖m z‖ - 1 := h3 ▸ infDist_le_dist_of_mem h1
  have h5 : ‖m z‖ ≤ 1 + infDist d Z₁ / 2 := by
    rw [hn]
    have h6 : u z = 1 + infDist d Z₁ / 2 := by rw [hd, hu]
    nlinarith [hun z, norm_nonneg z]
  linarith

/-- **Pushing a disc off a closed set.** A closed disc `B` inside `E` lies in a slightly larger
closed disc, which adds no point of `Z`, and whose boundary
meets `B` only in points of `Z`. -/
theorem exists_disc_push_off {B E Z : Set T} (hB : IsClosedDisc B) (hE : IsClosedDisc E)
  (hBE : B ⊆ E \ discBd E) (hZ : IsClosed Z) :
    ∃ D, IsClosedDisc D ∧ B ⊆ D ∧ D ⊆ E \ discBd E ∧ Disjoint (D \ B) Z ∧ discBd D ∩ B ⊆ Z
      ∧ discBd B ∩ Z ⊆ discBd D ∧ discBd D ∩ Z ⊆ discBd B := by
  classical
  obtain ⟨p⟩ := hB.isOArc_discBd
  obtain ⟨c, c', hc, hc', hm, hm', hl, hr, hin, hs, hcp⟩ := exists_disc_collar hB hE hBE p
  have hEc : IsCompact E := hE.isCompact
  have hZE : IsCompact (Z ∩ E) := hEc.inter_left hZ
  have hZ₀ : IsCompact (c' '' (Z ∩ E)) := hZE.image_of_continuousOn (hc'.mono inter_subset_right)
  set Z₁ : Set ℂ := (c' '' (Z ∩ E) ∩ {z | 1 ≤ ‖z‖}) ∪ sphere 0 2 with hZ₁
  have hZ₁c : IsCompact Z₁ := (hZ₀.inter_right (isClosed_le continuous_const
    continuous_norm)).union (isCompact_sphere 0 2)
  have hZ₁ne : Z₁.Nonempty := ⟨2, .inr (by simp)⟩
  set u : ℂ → ℝ := fun z => 1 + infDist (dirOf z) Z₁ / 2 with hu
  have hdist : ∀ w : ℂ, ‖w‖ = 1 → infDist w Z₁ ≤ 1 := fun w hw => by
    have hmem : (2 : ℂ) * w ∈ Z₁ := .inr (by simp [hw])
    refine (infDist_le_dist_of_mem hmem).trans (le_of_eq ?_)
    rw [dist_eq_norm, show w - 2 * w = -w by ring, norm_neg, hw]
  have hun : ∀ z, 1 ≤ u z := fun z => by
    have := infDist_nonneg (x := dirOf z) (s := Z₁)
    simp only [hu]
    linarith
  have hub : ∀ z, z ≠ 0 → u z ≤ 3 / 2 := fun z hz => by
    have := hdist _ (norm_dirOf hz)
    simp only [hu]
    linarith
  -- At `0` the factor is arbitrary, so we cut it off.
  set v : ℂ → ℝ := fun z => min (u z) (3 / 2) with hv
  have hvz : ∀ z, z ≠ 0 → v z = u z := fun z hz => min_eq_left (hub z hz)
  have hvb : ∀ z, |v z| ≤ 3 / 2 := fun z => by
    have h1 := hun z
    simp only [hv]
    rw [abs_of_nonneg (le_min (by linarith) (by norm_num))]
    exact min_le_right _ _
  have hvc : ContinuousOn v {0}ᶜ := by
    have h1 : ContinuousOn u {0}ᶜ := by
      refine continuousOn_const.add (ContinuousOn.div_const ?_ _)
      exact (continuous_infDist_pt Z₁).comp_continuousOn continuousOn_dirOf
    exact continuous_min.comp_continuousOn (h1.prodMk continuousOn_const)
  set m : ℂ → ℂ := fun z => z * (v z : ℂ) with hmdef
  have hmc : Continuous m := continuous_mul_of_bounded hvc hvb
  have hmz : ∀ z, z ≠ 0 → m z = (‖z‖ * u z : ℝ) * dirOf z := fun z hz => by
    have h1 := eq_mul_dirOf hz
    calc z * (v z : ℂ) = ((‖z‖ : ℂ) * dirOf z) * (u z : ℂ) := by rw [← h1, hvz z hz]
      _ = _ := by push_cast; ring
  have hm0 : m 0 = 0 := by simp [hmdef]
  have hmne : ∀ z, z ≠ 0 → m z ≠ 0 := fun z hz => by
    simp only [hmdef, ne_eq, mul_eq_zero, not_or]
    refine ⟨hz, ?_⟩
    rw [hvz z hz]
    have := hun z
    exact_mod_cast (by linarith : u z ≠ 0)
  have hnorm : ∀ z, z ≠ 0 → ‖m z‖ = ‖z‖ * u z := fun z hz => by
    rw [hmz z hz, norm_mul, norm_dirOf hz, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg]
    have := hun z
    positivity
  have hdir : ∀ z, z ≠ 0 → dirOf (m z) = dirOf z := fun z hz => by
    have h1 : 0 < ‖z‖ * u z := by
      have := hun z
      have := norm_pos_iff.mpr hz
      positivity
    have h5 : dirOf z ≠ 0 := fun h => by simpa [h] using norm_dirOf hz
    rw [hmz z hz, dirOf_mul_pos h1 h5]
    exact dirOf_of_norm_one (norm_dirOf hz)
  have hminj : Injective m := fun a b he => by
    exact radial_push_injective Z₁ m u hu hun hm0 hmne hnorm hdir a b he
  have hmr : ∀ z ∈ closedBall (0 : ℂ) 1, ‖m z‖ ≤ 3 / 2 := fun z hz => by
    by_cases h0 : z = 0
    · rw [h0, hm0]
      norm_num
    · rw [hnorm z h0]
      have h1 := hub z h0
      have h2 : ‖z‖ ≤ 1 := by simpa using hz
      have h3 := hun z
      nlinarith [norm_nonneg z]
  have hball : closedBall (0 : ℂ) (3 / 2) ⊆ closedBall 0 2 := closedBall_subset_closedBall
    (by norm_num)
  have hmb : MapsTo m (closedBall 0 1) (closedBall 0 2) := fun z hz => hball
    (by simpa using hmr z hz)
  have hgi : InjOn (c ∘ m) (closedBall 0 1) := fun a ha b hb he => hminj (hl.injOn (hmb ha)
    (hmb hb) he)
  have hgc : ContinuousOn (c ∘ m) (closedBall 0 1) := hc.comp hmc.continuousOn hmb
  have hdisc := isClosedDisc_image (closedBall_disc (s := 1) one_pos).1 hgc hgi
  rw [(closedBall_disc (s := 1) one_pos).2] at hdisc
  have hcball : ∀ z ∈ closedBall (0 : ℂ) 1, c z ∈ B := fun z hz => hin ▸ mem_image_of_mem c hz
  have hB2 : ∀ {a : ℂ}, a ∈ closedBall (0 : ℂ) 2 → c a ∈ B → ‖a‖ ≤ 1 := fun {a} ha h1 => by
    rw [← hin] at h1
    obtain ⟨b, hb, he⟩ := h1
    have := hl.injOn (closedBall_subset_closedBall (by norm_num) hb) ha he
    simpa [← this] using hb
  -- The boundary of the new disc meets `B` only where the factor is `1`.
  have hzero : ∀ z : ℂ, ‖z‖ = 1 → u z = 1 → z ∈ Z₁ := fun z hz h1 => by
    have h2 : infDist z Z₁ = 0 := by
      have h3 : u z = 1 + infDist z Z₁ / 2 := by simp only [hu, dirOf_of_norm_one hz]
      linarith
    exact (hZ₁c.isClosed.mem_iff_infDist_zero hZ₁ne).mpr h2
  have hunit : ∀ z : ℂ, ‖z‖ = 1 → z ∈ Z₁ → u z = 1 := fun z hz h1 => by
    simp only [hu, dirOf_of_norm_one hz, infDist_zero_of_mem h1]
    norm_num
  have hne1 : ∀ z : ℂ, ‖z‖ = 1 → z ≠ 0 := fun z hz h => by simp [h] at hz
  have hZ₁pt : ∀ a : ℂ, ‖a‖ = 1 → a ∈ Z₁ → c a ∈ Z := fun a ha h1 => by
    rcases h1 with ⟨⟨x, hx, rfl⟩, -⟩ | h1
    · rw [hr hx.2]
      exact hx.1
    · simp [ha] at h1
  have hnotB : ∀ z ∈ closedBall (0 : ℂ) 1, m z ∈ Z₁ → ‖m z‖ ≤ 1 := fun z hz h1 => by
    exact radial_push_avoids_outer_set Z₁ m u hu hun hm0 hmne hnorm hdir z hz h1
  have hin1 : ∀ z, ‖z‖ = 1 → c (m z) ∈ B → u z = 1 ∧ m z = z := fun z hz h1 => by
    have h0 := hne1 z hz
    have h2 : ‖m z‖ ≤ 1 := hB2 (hmb (by simp [hz])) h1
    rw [hnorm z h0, hz, one_mul] at h2
    have h3 : u z = 1 := le_antisymm h2 (hun z)
    refine ⟨h3, ?_⟩
    simp only [hmdef, hvz z h0, h3]
    simp
  have hbdD : discBd ((c ∘ m) '' closedBall 0 1) = c '' (m '' sphere 0 1) := by
    rw [hdisc.2, image_comp]
  have hsZ : ∀ z : ℂ, ‖z‖ = 1 → c z ∈ Z → z ∈ Z₁ := fun z hz h1 => by
    have hz2 : z ∈ closedBall (0 : ℂ) 2 := by
      rw [mem_closedBall_zero_iff, hz]
      norm_num
    exact .inl ⟨⟨c z, ⟨h1, hm hz2⟩, hl hz2⟩, hz.ge⟩
  have hDisj : Disjoint ((c ∘ m) '' closedBall 0 1 \ B) Z := by
    rw [disjoint_left]
    rintro _ ⟨⟨z, hz, rfl⟩, hnB⟩ hZm
    have hz2 := hmb hz
    have h1 : m z ∈ Z₁ := by
      by_contra hn
      have h2 : ¬ ‖m z‖ ≤ 1 := fun h3 => hnB (hcball _ (by simpa using h3))
      push Not at h2
      exact hn (.inl ⟨⟨_, ⟨hZm, hm hz2⟩, hl hz2⟩, h2.le⟩)
    exact hnB (hcball _ (by simpa using hnotB z hz h1))
  refine ⟨(c ∘ m) '' closedBall 0 1, hdisc.1, ?_, ?_, hDisj, ?_, ?_, ?_⟩
  · intro x hx
    rw [← hin] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    by_cases h0 : z = 0
    · exact ⟨0, by simp, by simp [h0, hm0]⟩
    · have hz1 : ‖z‖ ≤ 1 := by simpa using hz
      have hp := lt_of_lt_of_le one_pos (hun z)
      have hnz := norm_pos_iff.mpr h0
      set y : ℂ := ((‖z‖ / u z : ℝ) : ℂ) * dirOf z with hy
      have hd0 : dirOf z ≠ 0 := fun h => by simpa [h] using norm_dirOf h0
      have hr0 : 0 < ‖z‖ / u z := by positivity
      have hy0 : y ≠ 0 := mul_ne_zero (by exact_mod_cast hr0.ne') hd0
      have hdy : dirOf y = dirOf z := by
        rw [hy, dirOf_mul_pos hr0 hd0]
        exact dirOf_of_norm_one (norm_dirOf h0)
      have huy : u y = u z := by simp only [hu, hdy]
      have hny : ‖y‖ = ‖z‖ / u z := by
        rw [hy, norm_mul, norm_dirOf h0, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr0]
      refine ⟨y, ?_, ?_⟩
      · have : ‖y‖ ≤ 1 := by
          rw [hny, div_le_one hp]
          linarith [hun z]
        simpa using this
      · change c (m y) = c z
        rw [hmz y hy0, huy, hny, hdy, div_mul_cancel₀ _ hp.ne', ← eq_mul_dirOf h0]
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨hm (hmb hz), fun hb => ?_⟩
    rw [← hs] at hb
    obtain ⟨a, ha, he⟩ := hb
    have h1 := hl.injOn (sphere_subset_closedBall ha) (hmb hz) he
    have h2 := hmr z hz
    rw [← h1] at h2
    simp only [mem_sphere_zero_iff_norm] at ha
    linarith
  · rintro x ⟨hxb, hxB⟩
    rw [hbdD] at hxb
    obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hxb
    have hz1 : ‖z‖ = 1 := by simpa using hz
    obtain ⟨h1, h2⟩ := hin1 z hz1 hxB
    rw [h2]
    exact hZ₁pt z hz1 (hzero z hz1 h1)
  · rintro x ⟨hxb, hxZ⟩
    obtain ⟨w, rfl⟩ : ∃ w : Circle, (p w).1 = x := by
      obtain ⟨w, hw⟩ := p.surjective ⟨x, hxb⟩
      exact ⟨w, congrArg Subtype.val hw⟩
    have hw1 : ‖(w : ℂ)‖ = 1 := Circle.norm_coe w
    rw [← hcp w] at hxZ ⊢
    have h1 := hunit _ hw1 (hsZ _ hw1 hxZ)
    rw [hbdD]
    refine ⟨m w, ⟨w, by simp, rfl⟩, ?_⟩
    have h2 : m (w : ℂ) = w := by
      simp only [hmdef, hvz _ (hne1 _ hw1), h1]
      simp
    rw [h2]
  · rintro x ⟨hxb, hxZ⟩
    by_cases hxB : x ∈ B
    · rw [hbdD] at hxb
      obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hxb
      have hz1 : ‖z‖ = 1 := by simpa using hz
      obtain ⟨-, h2⟩ := hin1 z hz1 hxB
      have hw : ∃ w : Circle, (w : ℂ) = z := ⟨Circle.exp (Complex.arg z), by
        rw [Circle.coe_exp]
        have h7 := Complex.norm_mul_exp_arg_mul_I z
        rw [hz1] at h7
        simpa using h7⟩
      obtain ⟨w, rfl⟩ := hw
      rw [h2, hcp w]
      exact (p w).2
    · exact absurd hxZ (disjoint_left.mp hDisj ⟨Surface.discBd_subset _ hxb, hxB⟩)

omit [T2Space T] in
theorem closure_line_diff_ends {L : Set T} {u v : T} (hL : IsLineWithEnds L u v) : L ⊆ closure
  (L \ {u, v}) := by
  obtain ⟨f, h0, h1⟩ := hL
  intro x hx
  obtain ⟨z, hz⟩ := f.surjective ⟨x, hx⟩
  have hx' : x = (f z).1 := by rw [hz]
  have hc : Continuous fun t : unitInterval => (f t).1 := continuous_subtype_val.comp f.continuous
  have hd : closure (Ioo (0 : unitInterval) 1) = univ := by
    rw [closure_Ioo zero_ne_one]
    ext t
    exact ⟨fun _ => trivial, fun _ => ⟨unitInterval.nonneg t, unitInterval.le_one t⟩⟩
  have h2 : (fun t : unitInterval => (f t).1) z ∈ closure ((fun t : unitInterval =>
    (f t).1) '' Ioo 0 1) :=
    image_closure_subset_closure_image hc ⟨z, by rw [hd]; trivial, rfl⟩
  rw [hx']
  refine closure_mono ?_ h2
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨(f t).2, ?_⟩
  rintro (he | he)
  · have := f.injective (Subtype.ext (he.trans h0.symm))
    exact ht.1.ne' this
  · have := f.injective (Subtype.ext (he.trans h1.symm))
    exact ht.2.ne this

/-- What a line must satisfy, relative to a disc `B`, a closed set `Y` and a finite set `X`, to be
absorbed: it runs from a point `a` of the boundary of `B`
outside `X` to a point `b` that is on the boundary or is a point of `X` outside `B`, and it meets
`B` and `Y` only as allowed. -/
structure IsOutLine (X Y B L : Set T) (a b : T) : Prop where
  line : IsLineWithEnds L a b
  ne : a ≠ b
  a_notX : a ∉ X
  a_bd : a ∈ discBd B
  b_mem : b ∈ discBd B ∨ b ∈ X ∧ b ∉ B
  inter : L ∩ B ⊆ {a, b}
  interY : L ∩ Y ⊆ X
  mid : Disjoint (L \ {a, b}) X

variable {T : Type} [TopologicalSpace T] [T2Space T]

/-- The chord case of `exists_disc_absorbing`: a line with both ends on the boundary of `B` lies,
with one side of it, in a larger disc. -/
theorem exists_chord_fill (hS : IsClosedSurface T) (hsph : IsSphere T) {B L Y₀ : Set T} {a b : T}
  (hB : IsClosedDisc B) (hL : IsLineWithEnds L a b) (hab : a ≠ b)
    (ha : a ∈ discBd B) (hb : b ∈ discBd B) (hLB : L ∩ B ⊆ {a, b}) (hY₀ : IsPreconnected Y₀)
      (hYB : Disjoint Y₀ B) (hYL : Disjoint Y₀ L) :
    ∃ A₂ Δ₁ Δ₂, IsClosedDisc (B ∪ Δ₁) ∧ L ⊆ Δ₁ ∧ Disjoint Y₀ (B ∪ Δ₁) ∧ discBd (B ∪ Δ₁) = A₂ ∪ L
      ∧ A₂ ⊆ discBd B ∧ IsClosed Δ₁ ∧ IsClosed Δ₂ ∧ A₂ ⊆ Δ₂ ∧ Δ₁ ∩ Δ₂ = L ∧
      (B ∪ Δ₁) ∩ Δ₂ = A₂ ∪ L ∧ B ∪ Δ₁ ∪ Δ₂ = univ := by
  obtain ⟨hE, hbE⟩ := GM12.isClosedDisc_closure_compl_of_sphere hS hsph hB
  set E := closure (univ \ B) with hEdef
  have hfr := IsClosedDisc.frontier_eq_discBd hS hB
  have hBc : IsClosed B := hB.isClosed
  have hEB : E ∩ B = discBd B := by
    rw [← hfr, frontier_eq_closure_inter_closure, hBc.closure_eq, compl_eq_univ_sdiff, inter_comm]
  have hcov : B ∪ E = univ := by
    refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ B
    · exact .inl hx
    · exact .inr (subset_closure ⟨mem_univ x, hx⟩)
  have hbdB : discBd B ⊆ E := hEB ▸ inter_subset_left
  have hLE : L ⊆ E := fun x hx => by
    by_cases hxB : x ∈ B
    · rcases hLB ⟨hx, hxB⟩ with rfl | rfl
      · exact hbdB ha
      · exact hbdB hb
    · exact subset_closure ⟨mem_univ x, hxB⟩
  have hLbd : L ∩ discBd E = {a, b} := by
    rw [hbE]
    apply Subset.antisymm
    · exact fun x hx => hLB ⟨hx.1, GM11.discBd_subset B hx.2⟩
    · rintro x (rfl | rfl)
      · exact ⟨hL.left_mem, ha⟩
      · exact ⟨hL.right_mem, hb⟩
  obtain ⟨Δ₁, Δ₂, A₁, A₂, l₁, l₂, hun, hin, d₁, d₂, hcup, hcap, b₁, b₂, -, -⟩
    := disc_split hE hLE hab hL hLbd
  rw [hbE] at hun
  -- `Y₀` lies on one side.
  have hYE : Y₀ ⊆ Δ₁ ∪ Δ₂ := fun x hx => by
    rw [hcup]
    exact (hcov.ge (mem_univ x)).resolve_left (disjoint_left.mp hYB hx)
  -- By symmetry, the side away from `Y₀` is the first.
  wlog hmiss : Disjoint Y₀ Δ₁ generalizing Δ₁ Δ₂ A₁ A₂
  · have hmiss₂ : Disjoint Y₀ Δ₂ := by
      by_contra hn
      obtain ⟨x, hx1, hx2⟩ := not_disjoint_iff.mp hn
      obtain ⟨y, hy1, hy2⟩ := not_disjoint_iff.mp hmiss
      obtain ⟨z, hz, hz1, hz2⟩ := isPreconnected_closed_iff.mp hY₀ _ _ d₁.isClosed d₂.isClosed hYE
        ⟨y, hy1, hy2⟩ ⟨x, hx1, hx2⟩
      have : z ∈ L := hcap ▸ ⟨hz1, hz2⟩
      exact disjoint_left.mp hYL hz this
    exact this Δ₂ Δ₁ A₂ A₁ l₂ l₁ (by rw [union_comm]; exact hun) (by rw [inter_comm]; exact hin)
      d₂ d₁ (by rw [union_comm]; exact hcup) (by rw [inter_comm]; exact hcap) b₂ b₁
      (by rw [union_comm]; exact hYE) hmiss₂
  have hA₁Δ : A₁ ⊆ Δ₁ := fun x hx => GM11.discBd_subset Δ₁ (b₁ ▸ .inl hx)
  have hA₂Δ : A₂ ⊆ Δ₂ := fun x hx => GM11.discBd_subset Δ₂ (b₂ ▸ .inl hx)
  have hLΔ₁ : L ⊆ Δ₁ := fun x hx => GM11.discBd_subset Δ₁ (b₁ ▸ .inr hx)
  have hLΔ₂ : L ⊆ Δ₂ := fun x hx => GM11.discBd_subset Δ₂ (b₂ ▸ .inr hx)
  have hBΔ : B ∩ Δ₁ = A₁ := by
    apply Subset.antisymm
    · rintro x ⟨hx, hx1⟩
      have hxE : x ∈ E := hcup ▸ Or.inl hx1
      have hxb : x ∈ discBd B := hEB ▸ ⟨hxE, hx⟩
      rcases hun.ge hxb with h | h
      · exact h
      · have : x ∈ L := hcap ▸ ⟨hx1, hA₂Δ h⟩
        have h3 := hLB ⟨this, hx⟩
        have h4 : x ∈ A₁ ∩ A₂ := by
          rw [hin]; exact h3
        exact h4.1
    · intro x hx
      exact ⟨GM11.discBd_subset B (hun ▸ .inl hx), hA₁Δ hx⟩
  obtain ⟨hdisc, hbd⟩ := disc_union B Δ₁ A₁ a b hB d₁ l₁ hBΔ (hun ▸ subset_union_left)
    (b₁ ▸ subset_union_left)
  have hLA₁ : ∀ x ∈ L, x ∈ A₁ → x ∈ ({a, b} : Set T) := fun x hx h =>
    hLbd.le ⟨hx, hbE ▸ hun ▸ .inl h⟩
  have hend : ∀ x ∈ ({a, b} : Set T), x ∈ L := by
    rintro x (rfl | rfl)
    · exact hL.left_mem
    · exact hL.right_mem
  have hbdeq : discBd (B ∪ Δ₁) = A₂ ∪ L := by
    rw [hbd, ← hun, b₁]
    apply Subset.antisymm
    · rintro x ⟨h | h, h2⟩
      · rcases h with h | h
        · exact .inr (hend x (by_contra fun hn => h2 ⟨h, hn⟩))
        · exact .inl h
      · rcases h with h | h
        · exact .inr (hend x (by_contra fun hn => h2 ⟨h, hn⟩))
        · exact .inr h
    · rintro x (h | h)
      · exact ⟨.inl (.inr h), fun h3 => h3.2 (hin ▸ ⟨h3.1, h⟩)⟩
      · exact ⟨.inr (.inr h), fun h3 => h3.2 (hLA₁ x h h3.1)⟩
  refine ⟨A₂, Δ₁, Δ₂, hdisc, hLΔ₁, ?_, hbdeq, hun ▸ subset_union_right, d₁.isClosed, d₂.isClosed,
    hA₂Δ, hcap, ?_, ?_⟩
  · exact disjoint_union_right.mpr ⟨hYB, hmiss⟩
  · apply Subset.antisymm
    · rintro x ⟨h | h, h2⟩
      · have hxE : x ∈ E := hcup ▸ Or.inr h2
        have hxb : x ∈ discBd B := hEB ▸ ⟨hxE, h⟩
        rcases hun.ge hxb with h3 | h3
        · exact .inr (hcap ▸ ⟨hA₁Δ h3, h2⟩)
        · exact .inl h3
      · exact .inr (hcap ▸ ⟨h, h2⟩)
    · exact union_subset (fun x hx => ⟨.inl (GM11.discBd_subset B (hun ▸ .inr hx)),
        hA₂Δ hx⟩) fun x hx => ⟨.inr (hLΔ₁ hx), hLΔ₂ hx⟩
  · refine eq_univ_of_forall fun x => ?_
    rcases hcov.ge (mem_univ x) with h | h
    · exact .inl (.inl h)
    · rw [← hcup] at h
      rcases h with h | h
      · exact .inl (.inr h)
      · exact .inr h

omit [T2Space T] in
private theorem extend_disc_over_line
    {T : Type}
    [TopologicalSpace T]
    (hS : IsClosedSurface T)
    (hsph : IsSphere T)
    {ι : Type*}
    (ℓ : ι → Set T)
    (a : ι → T)
    (b : ι → T)
    {X : Set T}
    {Y₀ : Set T}
    (hY₀ : IsPreconnected Y₀)
    (hXY : Disjoint X Y₀)
    [T2Space T]
    (s : Finset ι)
    (B : Set T)
    (Y : Set T)
    (hB : IsClosedDisc B)
    (hY₀Y : Y₀ ⊆ Y)
    (hY₀B : Disjoint Y₀ B)
    (hbY : discBd B ∩ Y ⊆ X)
    (hl : ∀ i ∈ s, IsOutLine X Y B (ℓ i) (a i) (b i))
    (hp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ℓ i ∩ ℓ j ⊆ X)
    (i : ι)
    (hi : i ∈ s)
    (hli : IsOutLine X Y B (ℓ i) (a i) (b i))
    (s' : Finset ι)
    (hmem' : ∀ {j : ι}, j ∈ s' → j ∈ s ∧ i ≠ j)
    (Z : Set T)
    (hYZ : Y ⊆ Z)
    (hZc : IsClosed Z)
    (hZj : ∀ {j : ι}, j ∈ s' → ℓ j ⊆ Z)
    (hℓZ : ℓ i ∩ Z ⊆ X)
    (haZ : a i ∉ Z) :
    ∃ B₁, IsClosedDisc B₁ ∧ B ⊆ B₁ ∧ ℓ i ⊆ B₁ ∧ Disjoint Y₀ B₁ ∧ discBd B₁ ∩ Y ⊆ X ∧ ∀ j ∈ s', ℓ j
      ∩ B₁ ⊆ {a j, b j} ∧ a j ∈ discBd B₁ ∧ (b j ∈ discBd B₁ ∨ b j ∈ X ∧ b j ∉ B₁) ∨ discBd B₁ ∩ ℓ
      j ⊆ X := by
  rcases hli.b_mem with hbi | ⟨hbX, hbB⟩
  · have hYL : Disjoint Y₀ (ℓ i) := disjoint_left.mpr fun x hx hxl =>
      disjoint_left.mp hXY (hli.interY ⟨hxl, hY₀Y hx⟩) hx
    obtain ⟨A₂, Δ₁, Δ₂, hd, hLΔ, hYd, hbd, hA₂, hc₁, hc₂, hA₂Δ, hcap, hcap', hcov⟩
      := exists_chord_fill hS hsph hB hli.line hli.ne hli.a_bd hbi hli.inter hY₀ hY₀B hYL
    refine ⟨B ∪ Δ₁, hd, subset_union_left, hLΔ.trans subset_union_right, hYd, ?_, fun j hj => ?_⟩
    · rw [hbd]
      rintro x ⟨h | h, hy⟩
      · exact hbY ⟨hA₂ h, hy⟩
      · exact hli.interY ⟨h, hy⟩
    obtain ⟨hjs, hij⟩ := hmem' hj
    have hlj := hl j hjs
    have hOi : ∀ x ∈ ℓ j \ {a j, b j}, x ∉ ℓ i := fun x hx hxi =>
      disjoint_left.mp hlj.mid hx (hp i hi j hjs hij ⟨hxi, hx.1⟩)
    have hOB : ∀ x ∈ ℓ j \ {a j, b j}, x ∉ B := fun x hx hxB => hx.2 (hlj.inter ⟨hx.1, hxB⟩)
    have hO := hlj.line.isPreconnected_diff
    have hcovO : ℓ j \ {a j, b j} ⊆ Δ₁ ∪ Δ₂ := fun x hx => by
      rcases hcov.ge (mem_univ x) with (h | h) | h
      · exact absurd h (hOB x hx)
      · exact .inl h
      · exact .inr h
    have hside : ℓ j \ {a j, b j} ⊆ Δ₁ ∨ ℓ j \ {a j, b j} ⊆ Δ₂ := by
      by_contra hn
      push Not at hn
      obtain ⟨hn1, hn2⟩ := hn
      obtain ⟨x, hx, hx1⟩ := not_subset.mp hn1
      obtain ⟨y, hy, hy2⟩ := not_subset.mp hn2
      obtain ⟨z, hz, hz1, hz2⟩ := isPreconnected_closed_iff.mp hO _ _ hc₁ hc₂ hcovO ⟨y, hy,
        (hcovO hy).resolve_right hy2⟩ ⟨x, hx, (hcovO hx).resolve_left hx1⟩
      exact hOi z hz (hcap ▸ ⟨hz1, hz2⟩)
    rcases hside with hs₁ | hs₂
    · refine .inr ?_
      have hlΔ : ℓ j ⊆ Δ₁ := (closure_line_diff_ends hlj.line).trans (closure_minimal hs₁ hc₁)
      rw [hbd]
      rintro x ⟨h | h, hx⟩
      · exact hp i hi j hjs hij ⟨hcap ▸ ⟨hlΔ hx, hA₂Δ h⟩, hx⟩
      · exact hp i hi j hjs hij ⟨h, hx⟩
    · refine .inl ?_
      have hlΔ : ℓ j ⊆ Δ₂ := (closure_line_diff_ends hlj.line).trans (closure_minimal hs₂ hc₂)
      have hon : ∀ x, x ∈ ℓ j → x ∈ B → x ∈ discBd (B ∪ Δ₁) := fun x hx hxB => by
        rw [hbd, ← hcap']
        exact ⟨.inl hxB, hlΔ hx⟩
      refine ⟨?_, hon _ hlj.line.left_mem (GM11.discBd_subset B hlj.a_bd), ?_⟩
      · rintro x ⟨hx, h | h⟩
        · exact hlj.inter ⟨hx, h⟩
        · by_contra hn
          exact hOi x ⟨hx, hn⟩ (hcap ▸ ⟨h, hlΔ hx⟩)
      · rcases hlj.b_mem with h | ⟨h1, h2⟩
        · exact .inl (hon _ hlj.line.right_mem (GM11.discBd_subset B h))
        · by_cases h3 : b j ∈ B ∪ Δ₁
          · refine .inl ?_
            rw [hbd, ← hcap']
            exact ⟨h3, hlΔ hlj.line.right_mem⟩
          · exact .inr ⟨h1, h3⟩
  · -- A thin disc around the line.
    have hBc : IsClosed B := hB.isClosed
    have hend : ∀ x ∈ ℓ i, x ∈ X → x = a i ∨ x = b i := fun x hx hxX => by
      by_contra hn
      have h1 : x ∉ ({a i, b i} : Set T) := hn
      exact disjoint_left.mp hli.mid ⟨hx, h1⟩ hxX
    have hLZ : ℓ i ∩ (B ∪ Z) ⊆ {a i, b i} := by
      rintro x ⟨hx, h | h⟩
      · exact hli.inter ⟨hx, h⟩
      · exact hend x hx (hℓZ ⟨hx, h⟩)
    obtain ⟨D, -, -, hD, hLD, hDZ, haD, hbD, -, -⟩ := exists_edge_lens hS hli.line hli.ne
      (hBc.union hZc) hLZ
    have hab : B ∩ D = {a i} := by
      apply Subset.antisymm
      · rintro x ⟨h1, h2⟩
        rcases hDZ ⟨h2, .inl h1⟩ with h | h
        · exact h
        · exact absurd (h ▸ h1) hbB
      · rintro x rfl
        exact ⟨GM11.discBd_subset B hli.a_bd, GM11.discBd_subset D haD⟩
    obtain ⟨D', hD', hsub, hsup, -, hkeep, hbsub⟩ := exists_join hS hB hD hab hli.a_bd haD
      hZc.isOpen_compl haZ
    have hb'Z : ∀ x ∈ discBd D', x ∈ Z → x ∈ discBd B ∨ x ∈ D := fun x hx hxZ => by
      rcases hbsub hx with (h | h) | h
      · exact .inl h
      · exact .inr (GM11.discBd_subset D h)
      · exact absurd hxZ h
    have hD'Z : ∀ x ∈ D', x ∈ Z → x ∈ B ∨ x ∈ D := fun x hx hxZ => by
      rcases hsup hx with (h | h) | h
      · exact .inl h
      · exact .inr h
      · exact absurd hxZ h
    have hDZ' : ∀ x ∈ D, x ∈ Z → x = b i := fun x hx hxZ => by
      rcases hDZ ⟨hx, .inr hxZ⟩ with rfl | h
      · exact absurd hxZ haZ
      · exact h
    refine ⟨D', hD', subset_union_left.trans hsub, hLD.trans (subset_union_right.trans hsub),
      ?_, ?_, fun j hj => .inl ?_⟩
    · refine disjoint_left.mpr fun x hx hxD => ?_
      have hxZ : x ∈ Z := hYZ (hY₀Y hx)
      rcases hD'Z x hxD hxZ with h | h
      · exact disjoint_left.mp hY₀B hx h
      · exact disjoint_left.mp hXY (hDZ' x h hxZ ▸ hbX) hx
    · rintro x ⟨hx, hy⟩
      rcases hb'Z x hx (hYZ hy) with h | h
      · exact hbY ⟨h, hy⟩
      · rw [hDZ' x h (hYZ hy)]
        exact hbX
    · obtain ⟨hjs, hij⟩ := hmem' hj
      have hlj := hl j hjs
      have hjZ := hZj hj
      have hkeepZ : ∀ x, x ∈ Z → x ∈ discBd B ∪ discBd D → x ∈ discBd D' := fun x hx h
        => hkeep ⟨h, not_not.mpr hx⟩
      have hbon : ∀ x, x ∈ Z → x ∈ D' → x ∉ B → x ∈ discBd D' := fun x hx h1 h2 => by
        rcases hD'Z x h1 hx with h | h
        · exact absurd h h2
        · rw [hDZ' x h hx]
          exact hkeepZ _ (hDZ' x h hx ▸ hx) (.inr hbD)
      refine ⟨?_, hkeepZ _ (hjZ hlj.line.left_mem) (.inl hlj.a_bd), ?_⟩
      · rintro x ⟨hx, hxD⟩
        rcases hD'Z x hxD (hjZ hx) with h | h
        · exact hlj.inter ⟨hx, h⟩
        · have h3 := hDZ' x h (hjZ hx)
          have h4 : x ∈ X := hp i hi j hjs hij ⟨h3 ▸ hli.line.right_mem, hx⟩
          by_contra hn
          exact disjoint_left.mp hlj.mid ⟨hx, hn⟩ h4
      · rcases hlj.b_mem with h | ⟨h1, h2⟩
        · exact .inl (hkeepZ _ (hjZ hlj.line.right_mem) (.inl h))
        · by_cases h3 : b j ∈ D'
          · exact .inl (hbon _ (hjZ hlj.line.right_mem) h3 h2)
          · exact .inr ⟨h1, h3⟩

omit [T2Space T] in
/-- **Absorbing lines into a disc.** On a sphere, let `B` be a closed disc and let `ℓ` be finitely
many lines, which run outside `B` from its boundary to its boundary
or to points of `X`. They meet each other and `Y` only in `X`. Then a larger disc holds `B`, it
misses the connected set `Y₀`, and its boundary meets `Y` and the
lines only in `X`. We take the lines one at a time. A line with both ends on `B` is added with the
side of it away from `Y₀`, and any other line is added with a
thin disc around it. Then `exists_disc_push_off` takes the boundary off the line. -/
theorem exists_disc_absorbing (hS : IsClosedSurface T) (hsph : IsSphere T) {ι : Type*} (ℓ : ι
  → Set T) (a b : ι → T) {X Y₀ : Set T} (hY₀ : IsPreconnected Y₀)
    (hY₀n : Y₀.Nonempty) (hXY : Disjoint X Y₀) :
    ∀ (n : ℕ) (s : Finset ι), s.card = n → ∀ B Y : Set T, IsClosedDisc B → IsClosed Y → Y₀ ⊆ Y
      → Disjoint Y₀ B → discBd B ∩ Y ⊆ X →
      (∀ i ∈ s, IsOutLine X Y B (ℓ i) (a i) (b i)) → (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ℓ i ∩ ℓ j ⊆ X) →
      ∃ B', IsClosedDisc B' ∧ B ⊆ B' ∧ Disjoint Y₀ B' ∧ discBd B' ∩ Y ⊆ X
        ∧ ∀ i ∈ s, discBd B' ∩ ℓ i ⊆ X := by
  classical
  have ht2 : T2Space T := hS.2.1
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hs B Y hB hY hY₀Y hY₀B hbY hl hp
  rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · exact ⟨B, hB, Subset.rfl, hY₀B, hbY, by simp⟩
  have hli := hl i hi
  set s' := s.erase i with hs'
  have hmem' : ∀ {j}, j ∈ s' → j ∈ s ∧ i ≠ j := fun {j} hj => by
    rw [hs', Finset.mem_erase] at hj
    exact ⟨hj.2, hj.1.symm⟩
  set Z : Set T := Y ∪ ⋃ j ∈ s', ℓ j with hZ
  have hZc : IsClosed Z := hY.union (s'.finite_toSet.isClosed_biUnion fun j hj => (hl j
    (hmem' hj).1).line.isCompact.isClosed)
  have hZj : ∀ {j}, j ∈ s' → ℓ j ⊆ Z := fun {j} hj x hx => .inr (mem_iUnion₂.mpr ⟨j, hj, hx⟩)
  have hℓZ : ℓ i ∩ Z ⊆ X := by
    rintro x ⟨h1, h2 | h2⟩
    · exact hli.interY ⟨h1, h2⟩
    · obtain ⟨j, hj, h3⟩ := mem_iUnion₂.mp h2
      exact hp i hi j (hmem' hj).1 (hmem' hj).2 ⟨h1, h3⟩
  have haZ : a i ∉ Z := fun h => hli.a_notX (hℓZ ⟨hli.line.left_mem, h⟩)
  -- The disc that holds the line `ℓ i`.
  have hstep : ∃ B₁, IsClosedDisc B₁ ∧ B ⊆ B₁ ∧ ℓ i ⊆ B₁ ∧ Disjoint Y₀ B₁ ∧ discBd B₁ ∩ Y ⊆ X
    ∧ ∀ j ∈ s',
      (ℓ j ∩ B₁ ⊆ {a j, b j} ∧ a j ∈ discBd B₁ ∧ (b j ∈ discBd B₁ ∨ b j ∈ X ∧ b j ∉ B₁))
        ∨ discBd B₁ ∩ ℓ j ⊆ X := by
    exact extend_disc_over_line (T := T) hS hsph (ι := ι) ℓ a b (X := X) (Y₀ := Y₀) hY₀ hXY s B Y
      hB hY₀Y hY₀B hbY hl hp i hi hli s' hmem' Z subset_union_left hZc hZj hℓZ haZ
  obtain ⟨B₁, hB₁, hBB₁, hℓB₁, hY₀B₁, hb₁Y, hdich⟩ := hstep
  -- Move the boundary off the line.
  obtain ⟨w, hw⟩ := hY₀n
  have hwB₁ : w ∉ B₁ := disjoint_left.mp hY₀B₁ hw
  obtain ⟨E, hE, hsubE, -⟩ := exists_disc_around hman hB₁ (fun x _ => hS.2.2 x) (W
    := {w}ᶜ) isOpen_compl_singleton
    (fun x hx (h : x = w) => hwB₁ (h ▸ GM11.discBd_subset B₁ hx))
  obtain ⟨D, hD, hB₁D, -, hdiff, hbdZ, hkeep, hbdZ'⟩ := exists_disc_push_off hB₁ hE hsubE hZc
  have hDZ : ∀ x ∈ D, x ∈ Z → x ∈ B₁ := fun x hx hxZ => by
    by_contra hn
    exact disjoint_left.mp hdiff ⟨hx, hn⟩ hxZ
  set keep : Set ι := {j | ℓ j ∩ B₁ ⊆ {a j, b j} ∧ a j ∈ discBd B₁ ∧ (b j ∈ discBd B₁ ∨ b j ∈ X
    ∧ b j ∉ B₁)} with hkeepdef
  set s'' := s'.filter (· ∈ keep) with hs''
  set Y' : Set T := Y ∪ (ℓ i ∪ ⋃ j ∈ s' \ s'', ℓ j) with hY'
  have hsplit : ∀ j ∈ s', j ∈ s'' ∨ j ∈ s' \ s'' := fun j hj => by
    by_cases h : j ∈ s''
    · exact .inl h
    · exact .inr (Finset.mem_sdiff.mpr ⟨hj, h⟩)
  have hgone : ∀ j ∈ s' \ s'', discBd B₁ ∩ ℓ j ⊆ X := fun j hj => by
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hj
    rcases hdich j h1 with h | h
    · exact absurd (Finset.mem_filter.mpr ⟨h1, h⟩) h2
    · exact h
  have hsub'' : ∀ {j}, j ∈ s'' → j ∈ s' := fun {j} hj => (Finset.mem_filter.mp hj).1
  have hY'c : IsClosed Y' := hY.union (hli.line.isCompact.isClosed.union
    (((s' \ s'').finite_toSet).isClosed_biUnion fun j hj =>
    (hl j (hmem' (Finset.mem_sdiff.mp hj).1).1).line.isCompact.isClosed))
  have hcard : s''.card < n := by
    have h1 : s''.card ≤ s'.card := Finset.card_filter_le _ _
    have h2 : s'.card = s.card - 1 := Finset.card_erase_of_mem hi
    have h3 := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  have hD_bdY' : discBd D ∩ Y' ⊆ X := by
    rintro x ⟨hx, h | h | h⟩
    · exact hb₁Y ⟨hbdZ' ⟨hx, .inl h⟩, h⟩
    · rcases hbdZ ⟨hx, hℓB₁ h⟩ with h2 | h2
      · exact hli.interY ⟨h, h2⟩
      · obtain ⟨j, hj, h3⟩ := mem_iUnion₂.mp h2
        exact hp i hi j (hmem' hj).1 (hmem' hj).2 ⟨h, h3⟩
    · obtain ⟨j, hj, h3⟩ := mem_iUnion₂.mp h
      have hj' := (Finset.mem_sdiff.mp hj).1
      exact hgone j hj ⟨hbdZ' ⟨hx, hZj hj' h3⟩, h3⟩
  have hlines : ∀ j ∈ s'', IsOutLine X Y' D (ℓ j) (a j) (b j) := fun j hj => by
    have hj' := hsub'' hj
    obtain ⟨hjs, hij⟩ := hmem' hj'
    have hlj := hl j hjs
    obtain ⟨h1, h2, h3⟩ : j ∈ keep := (Finset.mem_filter.mp hj).2
    have hjZ := hZj hj'
    refine ⟨hlj.line, hlj.ne, hlj.a_notX, hkeep ⟨h2, hjZ hlj.line.left_mem⟩, ?_, ?_, ?_, hlj.mid⟩
    · rcases h3 with h | ⟨h4, h5⟩
      · exact .inl (hkeep ⟨h, hjZ hlj.line.right_mem⟩)
      · exact .inr ⟨h4, fun h6 => h5 (hDZ _ h6 (hjZ hlj.line.right_mem))⟩
    · exact fun x hx => h1 ⟨hx.1, hDZ x hx.2 (hjZ hx.1)⟩
    · rintro x ⟨hx, h | h | h⟩
      · exact hlj.interY ⟨hx, h⟩
      · exact hp i hi j hjs hij ⟨h, hx⟩
      · obtain ⟨k, hk, h4⟩ := mem_iUnion₂.mp h
        obtain ⟨hk1, hk2⟩ := Finset.mem_sdiff.mp hk
        have hjk : j ≠ k := fun e => hk2 (e ▸ hj)
        exact hp j hjs k (hmem' hk1).1 hjk ⟨hx, h4⟩
  obtain ⟨B', hB', hDB', hYB', hbY', hbl⟩ := ih s''.card hcard s'' rfl D Y' hD hY'c
    (hY₀Y.trans subset_union_left)
    (disjoint_left.mpr fun x hx hxD => disjoint_left.mp hY₀B₁ hx (hDZ x hxD (.inl
      (hY₀Y hx)))) hD_bdY' hlines
    (fun j hj k hk => hp j (hmem' (hsub'' hj)).1 k (hmem' (hsub'' hk)).1)
  refine ⟨B', hB', hBB₁.trans (hB₁D.trans hDB'), hYB', fun x hx => hbY' ⟨hx.1, .inl hx.2⟩,
    fun j hj => ?_⟩
  by_cases hji : j = i
  · subst hji
    exact fun x hx => hbY' ⟨hx.1, .inr (.inl hx.2)⟩
  have hj' : j ∈ s' := Finset.mem_erase.mpr ⟨hji, hj⟩
  rcases hsplit j hj' with h | h
  · exact hbl j h
  · exact fun x hx => hbY' ⟨hx.1, .inr (.inr (mem_iUnion₂.mpr ⟨j, h, hx.2⟩))⟩

end GraphMinor.GM07
