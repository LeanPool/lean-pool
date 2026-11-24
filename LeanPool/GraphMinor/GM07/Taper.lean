/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.MoveCuff

/-!
# Pushing a surface off a cuff

Let `C` be a cuff of a surface and let `Z` be a closed set. In a collar of `C`, each point `(w, t)`
has a height `t`. Let
`d w` be at most the distance from `(w, 0)` to `Z`, so that `Z` has no point under the height `d w`.
The map that sends height
`t` to `max t ((d w + t) / 2)` leaves `Z` alone and lifts the cuff to height `d w / 2`, which is
positive off `Z`. It extends by
the identity to a one to one map `ρ` of the surface, homotopic to the identity (`exists_taper`). The
paper uses this in
"we may assume that `X ∩ bd(Σ') ⊆ V(G')`" in its proofs of (7.1) and (7.2), and for pushing a loop
off itself in (7.3).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric GraphMinor.Surface

universe u

local notation "𝕀" => unitInterval

/-- A height function under a closed set of `Circle × 𝕀`, positive where the set misses the bottom.
-/
theorem exists_gap {A : Set (Circle × 𝕀)} (hA : IsClosed A) :
    ∃ d : Circle → ℝ, Continuous d ∧ (∀ w, 0 ≤ d w) ∧ (∀ w, d w ≤ 1) ∧ (∀ w, ∀ t : 𝕀, (w, t) ∈ A
      → d w ≤ t) ∧
      ∀ w, d w = 0 → (w, (0 : 𝕀)) ∈ A := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 1, continuous_const, fun _ => zero_le_one, fun _ => le_rfl,
      fun _ _ h => h.elim, fun _ h => absurd h one_ne_zero⟩
  have hcont : Continuous fun w : Circle => infDist (w, (0 : 𝕀)) A :=
    (continuous_infDist_pt A).comp (continuous_id.prodMk continuous_const)
  refine ⟨fun w => min 1 (infDist (w, (0 : 𝕀)) A), continuous_const.min hcont,
    fun w => le_min zero_le_one infDist_nonneg,
    fun w => min_le_left _ _, fun w t h => ?_, fun w h => ?_⟩
  · refine (min_le_right _ _).trans ((infDist_le_dist_of_mem h).trans ?_)
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, Subtype.dist_eq]
    simp [Real.dist_eq, abs_of_nonneg t.2.1]
  · have h1 : infDist (w, (0 : 𝕀)) A = 0 := by
      rcases min_choice 1 (infDist (w, (0 : 𝕀)) A) with h2 | h2
      · have h3 : min 1 (infDist (w, (0 : 𝕀)) A) = 0 := h
        rw [h2] at h3
        exact absurd h3 one_ne_zero
      · have h3 : min 1 (infDist (w, (0 : 𝕀)) A) = 0 := h
        rwa [h2] at h3
    exact (hA.mem_iff_infDist_zero hne).mpr h1

/-- A map of heights that fixes the top extends a map of the collar to the surface, by the identity.
-/
theorem exists_collar_glue {Y : Type u} [TopologicalSpace Y] [T2Space Y] {b : Circle × 𝕀 → Y}
  (hbc : Continuous b)
    (hbi : Function.Injective b) (hopen : IsOpen (range b \ b '' {x | x.2
      = 1})) {M : 𝕀 × Circle × 𝕀 → 𝕀}
    (hM : Continuous M) (htop : ∀ p w, M (p, w, 1) = 1) :
    ∃ c : 𝕀 × Y → Y, Continuous c ∧ (∀ p w t, c (p, b (w, t)) = b (w, M (p, w, t)))
      ∧ ∀ p y, y ∉ range b → c (p, y) = y := by
  classical
  have hcpt : CompactSpace (Circle × 𝕀) := inferInstance
  have hemb : IsClosedEmbedding b := hbc.isClosedEmbedding hbi
  have : Nonempty (Circle × 𝕀) := ⟨(1, 0)⟩
  let J : Y → Circle × 𝕀 := Function.invFun b
  have hJ : ∀ x, J (b x) = x := Function.leftInverse_invFun hbi
  have hJc : ContinuousOn J (range b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (range b).domRestrict J = hemb.isEmbedding.toHomeomorph.symm := by
      funext y
      obtain ⟨y, x, rfl⟩ := y
      change J (b x) = _
      rw [hJ]
      exact (hemb.isEmbedding.toHomeomorph.symm_apply_apply x).symm
    rw [this]
    exact Homeomorph.continuous _
  let c : 𝕀 × Y → Y := fun q => if q.2 ∈ range b then b ((J q.2).1, M (q.1, J q.2)) else q.2
  have hR : IsClosed (range b) := hemb.isClosed_range
  have hO : IsOpen (range b \ b '' {x | x.2 = 1}) := hopen
  have hc1 : ContinuousOn c (univ ×ˢ range b) := by
    have h1 : ContinuousOn (fun q : 𝕀 × Y => b ((J q.2).1, M (q.1, J q.2))) (univ ×ˢ range b) := by
      refine hbc.comp_continuousOn ?_
      have h2 : ContinuousOn (fun q : 𝕀 × Y => J q.2) (univ ×ˢ range b)
        := hJc.comp continuousOn_snd fun q hq => hq.2
      exact (continuous_fst.comp_continuousOn h2).prodMk (hM.comp_continuousOn
        (continuousOn_fst.prodMk h2))
    exact h1.congr fun q hq => ite_eq_left hq.2
  have hc2 : ContinuousOn c (univ ×ˢ (range b \ b '' {x | x.2 = 1})ᶜ) := by
    refine continuousOn_snd.congr ?_
    rintro ⟨p, y⟩ ⟨-, hy⟩
    change (if y ∈ range b then _ else _) = y
    split_ifs with hyr
    · obtain ⟨x, rfl⟩ := hyr
      have h1 : x.2 = 1 := by
        by_contra hne
        exact hy ⟨mem_range_self x, fun ⟨x', hx', he⟩ => hne (hbi he ▸ hx')⟩
      obtain ⟨w, t⟩ := x
      simp only at h1
      subst h1
      rw [hJ, htop]
    · rfl
  have hcov : (univ ×ˢ range b) ∪ (univ ×ˢ (range b \ b '' {x | x.2 = 1})ᶜ) = (univ : Set (𝕀 × Y))
    := by
    ext ⟨p, y⟩
    by_cases hy : y ∈ range b \ b '' {x | x.2 = 1}
    · simp [hy.1]
    · simp [hy]
  refine ⟨c, ?_, fun p w t => ?_, fun p y hy => ite_eq_right hy⟩
  · rw [← continuousOn_univ, ← hcov]
    exact hc1.union_of_isClosed hc2 (isClosed_univ.prod hR) (isClosed_univ.prod hO.isClosed_compl)
  · change (if b (w, t) ∈ range b then _ else _) = _
    rw [ite_eq_left (mem_range_self _), hJ]

private theorem joined_in_collar_below_gap {Y : Type u} [TopologicalSpace Y]
    {C Z : Set Y} {b : Circle × 𝕀 → Y} (φ : Circle ≃ₜ C)
    (hbc : Continuous b) (hbi : Function.Injective b) (hb0 : ∀ w, b (w, 0) = (φ w : Y))
    {d : Circle → ℝ} (hd1 : ∀ w, d w ≤ 1)
    (hdZ : ∀ w t, b (w, t) ∈ Z → d w ≤ (t : ℝ))
    (w : Circle) (t r : 𝕀) (ht0 : 0 < (t : ℝ)) (htd : (t : ℝ) < d w)
    (hr : (r : ℝ) = d w / 2) :
    JoinedIn (Zᶜ ∩ Cᶜ) (b (w, t)) (b (w, r)) := by
  have hdw := ht0.trans htd
  let c : ℝ → ℝ := fun u => (1 - u) * t + u * (d w / 2)
  have hcI : ∀ u ∈ Icc (0 : ℝ) 1, c u ∈ Icc (0 : ℝ) 1 ∧ 0 < c u ∧ c u < d w := by
    rintro u ⟨hu0, hu1⟩
    have h3 : 0 < c u := by
      have : 0 < (1 - u) * t + u * (d w / 2) := by
        rcases eq_or_lt_of_le hu0 with rfl | h
        · simpa using ht0
        · have : 0 ≤ (1 - u) * t := mul_nonneg (by linarith) ht0.le
          have : 0 < u * (d w / 2) := by positivity
          linarith
      exact this
    have h4 : c u < d w := by
      have h5 : (1 - u) * t ≤ (1 - u) * d w := mul_le_mul_of_nonneg_left htd.le (by linarith)
      have : (1 - u) * t + u * (d w / 2) < d w := by
        rcases eq_or_lt_of_le hu0 with rfl | h
        · simpa using htd
        · nlinarith
      exact this
    exact ⟨⟨h3.le, h4.le.trans (hd1 w)⟩, h3, h4⟩
  have hcc : Continuous c := by fun_prop
  refine JoinedIn.ofLine (f := fun u => b (w, Set.projIcc 0 1 zero_le_one (c u))) ?_ ?_ ?_ ?_
  · exact (hbc.comp (by fun_prop)).continuousOn
  · have : c 0 = t := by simp [c]
    change b (w, Set.projIcc 0 1 zero_le_one (c 0)) = b (w, t)
    rw [this]
    congr 2
    exact Set.projIcc_val zero_le_one t
  · have h3 : c 1 = d w / 2 := by simp [c]
    change b (w, Set.projIcc 0 1 zero_le_one (c 1)) = _
    have h4 : Set.projIcc 0 1 zero_le_one (c 1) = r := by
      apply Subtype.ext
      rw [Set.projIcc_of_mem zero_le_one ⟨by rw [h3]; linarith, by rw [h3]; linarith [hd1 w]⟩ ]
      change c 1 = (r : ℝ)
      rw [hr, h3]
    rw [h4]
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨h3, h4, h5⟩ := hcI u hu
    have h6 : ((Set.projIcc 0 1 zero_le_one (c u) : 𝕀) : ℝ) = c u := by
      rw [Set.projIcc_of_mem zero_le_one h3]
    refine ⟨fun hz => ?_, fun hc' => ?_⟩
    · have := hdZ w _ hz
      rw [h6] at this
      linarith
    · obtain ⟨w', he⟩ : ∃ w', b (w', 0) = b (w, Set.projIcc 0 1 zero_le_one (c u)) :=
        ⟨φ.symm ⟨_, hc'⟩, by rw [hb0, φ.apply_symm_apply]⟩
      have h7 := congrArg Prod.snd (hbi he)
      have h8 : (0 : ℝ) = c u := by
        have := congrArg Subtype.val h7
        rw [h6] at this
        exact this
      linarith

/-- **Pushing off a cuff.** See the module docstring. The last two conclusions say that the homotopy
fixes `Z`, and that each point
near a point of the cuff off `Z` can be joined, off `Z` and off the cuff, to the image of the cuff.
-/
theorem exists_taper_sides {Y : Type u} [TopologicalSpace Y] (hY : IsSurface Y) {C : Set Y}
  (hC : IsCuff C) (φ : Circle ≃ₜ C)
    {Z : Set Y} (hZ : IsClosed Z) :
    ∃ H : 𝕀 × Y → Y, Continuous H ∧ (∀ y, H (0, y) = y) ∧ Function.Injective (fun y => H (1, y)) ∧
      (∀ z ∈ Z, H (1, z) = z) ∧
      (∀ y, H (1, y) ∈ Z → y ∈ Z) ∧ (∀ y, H (1, y) ∈ C → H (1, y) ∈ Z) ∧ (∀ p, ∀ z ∈ Z, H (p, z)
        = z) ∧
      ∀ y ∈ C, y ∉ Z → ∃ N ∈ 𝓝 y, ∀ y' ∈ N, y' ∉ C → ∃ y'' ∈ C, JoinedIn (Zᶜ ∩ Cᶜ) y' (H (1, y''))
        := by
  classical
  have ht2 : T2Space Y := hY.2.1
  obtain ⟨b, hbc, hbi, -, hb0, hopen⟩ := exists_collar hY hC φ isOpen_univ (subset_univ _)
  obtain ⟨d, hdc, hd0, hd1, hdZ, hd⟩ := exists_gap (hZ.preimage hbc)
  let g : Circle × 𝕀 → ℝ := fun x => max x.2.1 ((d x.1 + x.2.1) / 2)
  have hgc : Continuous g := by fun_prop
  have hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1 := fun x => by
    have h2 := x.2.2
    refine ⟨le_max_of_le_left h2.1, max_le h2.2 ?_⟩
    have h3 := hd1 x.1
    have h4 : (x.2.1 : ℝ) ≤ 1 := h2.2
    linarith
  have hglow : ∀ x, x.2.1 ≤ g x ∧ (d x.1 + x.2.1) / 2 ≤ g x := fun x => ⟨le_max_left _ _,
    le_max_right _ _⟩
  let M : 𝕀 × Circle × 𝕀 → 𝕀 := fun q => ⟨(1 - q.1.1) * q.2.2.1 + q.1.1 * g q.2, by
    have h1 := q.1.2
    have h2 := q.2.2.2
    have h3 := hg01 q.2
    exact (convex_Icc (0 : ℝ) 1) h2 h3 (a := 1 - q.1.1) (b := q.1.1) (by linarith [h1.2]) h1.1
      (by ring)⟩
  have hMc : Continuous M := by
    refine Continuous.subtype_mk ?_ _
    have : Continuous fun q : 𝕀 × Circle × 𝕀 => g q.2 := hgc.comp continuous_snd
    fun_prop
  have htop : ∀ p w, M (p, w, 1) = 1 := fun p w => by
    apply Subtype.ext
    have h1 : g (w, 1) = 1 := max_eq_left (by
      have := hd1 w
      change (d w + 1) / 2 ≤ 1
      linarith)
    change (1 - p.1) * 1 + p.1 * g (w, 1) = 1
    rw [h1]
    ring
  obtain ⟨H, hH, h1, h2⟩ := exists_collar_glue hbc hbi hopen hMc htop
  have hH1 : ∀ w t, H (1, b (w, t)) = b (w, ⟨g (w, t), hg01 _⟩) := fun w t => by
    rw [h1]
    congr 2
    apply Subtype.ext
    change (1 - (1 : ℝ)) * t.1 + 1 * g (w, t) = g (w, t)
    ring
  have hfix : ∀ w t, b (w, t) ∈ Z → g (w, t) = t.1 := fun w t hz => by
    have h3 : d w ≤ t := hdZ w t hz
    exact max_eq_left (by linarith [(show d (w, t).1 ≤ t from h3)])
  have hgmono : ∀ w (t t' : 𝕀), g (w, t) = g (w, t') → t = t' := fun w t t' he => by
    apply Subtype.ext
    rcases le_total (t : ℝ) (d w) with h3 | h3 <;> rcases le_total (t' : ℝ) (d w) with h4 | h4
    · have h5 : g (w, t) = (d w + t) / 2 := max_eq_right (by
        change (t : ℝ) ≤ (d w + t) / 2
        linarith)
      have h6 : g (w, t') = (d w + t') / 2 := max_eq_right (by
        change (t' : ℝ) ≤ (d w + t') / 2
        linarith)
      rw [h5, h6] at he
      linarith
    · have h5 : g (w, t) = (d w + t) / 2 := max_eq_right (by
        change (t : ℝ) ≤ (d w + t) / 2
        linarith)
      have h6 : g (w, t') = t' := max_eq_left (by change (d w + t') / 2 ≤ (t' : ℝ); linarith)
      rw [h5, h6] at he
      linarith
    · have h5 : g (w, t) = t := max_eq_left (by change (d w + t) / 2 ≤ (t : ℝ); linarith)
      have h6 : g (w, t') = (d w + t') / 2 := max_eq_right (by
        change (t' : ℝ) ≤ (d w + t') / 2
        linarith)
      rw [h5, h6] at he
      linarith
    · have h5 : g (w, t) = t := max_eq_left (by change (d w + t) / 2 ≤ (t : ℝ); linarith)
      have h6 : g (w, t') = t' := max_eq_left (by change (d w + t') / 2 ≤ (t' : ℝ); linarith)
      rw [h5, h6] at he
      exact he
  refine ⟨H, hH, fun y => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hy : y ∈ range b
    · obtain ⟨⟨w, t⟩, rfl⟩ := hy
      rw [h1]
      congr 2
      apply Subtype.ext
      change (1 - (0 : ℝ)) * t.1 + 0 * g (w, t) = t.1
      ring
    · exact h2 _ _ hy
  · intro y y' he
    change H (1, y) = H (1, y') at he
    by_cases hy : y ∈ range b <;> by_cases hy' : y' ∈ range b
    · obtain ⟨⟨w, t⟩, rfl⟩ := hy
      obtain ⟨⟨w', t'⟩, rfl⟩ := hy'
      rw [hH1, hH1] at he
      have h3 := hbi he
      obtain ⟨rfl, h4⟩ := Prod.mk.inj h3
      rw [hgmono w t t' (congrArg Subtype.val h4)]
    · obtain ⟨⟨w, t⟩, rfl⟩ := hy
      rw [hH1, h2 _ _ hy'] at he
      exact absurd ⟨_, he⟩ hy'
    · obtain ⟨⟨w, t⟩, rfl⟩ := hy'
      rw [hH1, h2 _ _ hy] at he
      exact absurd ⟨_, he.symm⟩ hy
    · rwa [h2 _ _ hy, h2 _ _ hy'] at he
  · intro z hz
    by_cases hy : z ∈ range b
    · obtain ⟨⟨w, t⟩, rfl⟩ := hy
      rw [hH1]
      congr 2
      exact Subtype.ext (hfix w t hz)
    · exact h2 _ _ hy
  · intro y hy
    by_cases hyr : y ∈ range b
    · obtain ⟨⟨w, t⟩, rfl⟩ := hyr
      rw [hH1] at hy
      have h3 : d w ≤ g (w, t) := hdZ w _ hy
      have h4 : t.1 ≥ d w := by
        by_contra hlt
        have h5 : g (w, t) = (d w + t) / 2 := max_eq_right (by
          change (t : ℝ) ≤ (d w + t) / 2
          linarith)
        rw [h5] at h3
        linarith
      have h5 : g (w, t) = t := max_eq_left (by change (d w + t) / 2 ≤ (t : ℝ); linarith)
      have h6 : (⟨g (w, t), hg01 _⟩ : 𝕀) = t := Subtype.ext h5
      rwa [h6] at hy
    · rwa [h2 _ _ hyr] at hy
  · intro y hy
    obtain ⟨w₀, hyb⟩ : ∃ w₀, H (1, y) = b (w₀, 0) := ⟨φ.symm ⟨_, hy⟩, by rw [hb0,
      φ.apply_symm_apply]⟩
    by_cases hyr : y ∈ range b
    · obtain ⟨⟨w, t⟩, rfl⟩ := hyr
      rw [hH1] at hyb
      have h3 := hbi hyb
      obtain ⟨h4, h5⟩ := Prod.mk.inj h3
      have h6 : g (w, t) = 0 := congrArg Subtype.val h5
      have h7 := (hglow (w, t)).2
      rw [h6] at h7
      have h8 := hd0 w
      have h9 : (0 : ℝ) ≤ t := t.2.1
      change (d w + t) / 2 ≤ 0 at h7
      have h10 : d w = 0 := by linarith
      have h11 : (t : ℝ) = 0 := by linarith
      have h12 := hd w h10
      have h13 : (⟨g (w, t), hg01 _⟩ : 𝕀) = 0 := Subtype.ext h6
      rw [hH1, h13]
      exact h12
    · have h3 := h2 1 y hyr
      rw [h3] at hyb
      exact absurd ⟨_, hyb.symm⟩ hyr
  · intro p z hz
    by_cases hyr : z ∈ range b
    · obtain ⟨⟨w, t⟩, rfl⟩ := hyr
      rw [h1]
      congr 2
      apply Subtype.ext
      change (1 - p.1) * t.1 + p.1 * g (w, t) = t.1
      rw [hfix w t hz]
      ring
    · exact h2 _ _ hyr
  · intro y hyC hyZ
    obtain ⟨w₀, hw₀⟩ : ∃ w₀, b (w₀, 0) = y := ⟨φ.symm ⟨y, hyC⟩, by rw [hb0, φ.apply_symm_apply]⟩
    have hd0' : 0 < d w₀ := by
      refine lt_of_le_of_ne (hd0 w₀) fun h => hyZ ?_
      have := hd w₀ h.symm
      rwa [mem_preimage, hw₀] at this
    have hemb : IsClosedEmbedding b := hbc.isClosedEmbedding hbi
    let A : Set (Circle × 𝕀) := {x | x.2.1 < d x.1}
    have hAo : IsOpen A := isOpen_lt (by fun_prop) (by fun_prop)
    have hAt : A ∩ {x | x.2 ≠ 1} = A := by
      refine inter_eq_left.mpr fun x hx h1' => ?_
      have h3 : (x.2 : ℝ) < d x.1 := hx
      rw [show x.2 = 1 from h1'] at h3
      have h4 := hd1 x.1
      have h5 : (((1 : 𝕀) : ℝ)) = 1 := rfl
      linarith
    obtain ⟨V, hV, hVe⟩ := hemb.isInducing.isOpen_iff.mp hAo
    have hsub : V ∩ (range b \ b '' {x | x.2 = 1}) ⊆ b '' A := by
      rintro _ ⟨hv, ⟨x, rfl⟩, -⟩
      exact ⟨x, by rw [← hVe]; exact hv, rfl⟩
    refine ⟨V ∩ (range b \ b '' {x | x.2 = 1}), (hV.inter hopen).mem_nhds ⟨?_, ?_⟩, ?_⟩
    · have : (w₀, (0 : 𝕀)) ∈ A := hd0'
      rw [← hVe] at this
      rw [← hw₀]
      exact this
    · refine ⟨⟨(w₀, 0), hw₀⟩, ?_⟩
      rintro ⟨x, hx, he⟩
      rw [← hw₀] at he
      have h3 := hbi he
      rw [h3] at hx
      exact zero_ne_one hx
    · intro y' hy' hyC'
      obtain ⟨⟨w, t⟩, htA, rfl⟩ := hsub hy'
      have htd : (t : ℝ) < d w := htA
      have ht0 : 0 < (t : ℝ) := by
        refine lt_of_le_of_ne t.2.1 fun h => hyC' ?_
        have ht : t = 0 := Subtype.ext h.symm
        rw [ht, hb0]
        exact (φ w).2
      refine ⟨b (w, 0), by rw [hb0]; exact (φ w).2, ?_⟩
      have hdw : 0 < d w := ht0.trans htd
      have hg0 : g (w, 0) = d w / 2 := by
        have : max ((0 : 𝕀) : ℝ) ((d w + ((0 : 𝕀) : ℝ)) / 2) = d w / 2 := by
          simp only [Icc.coe_zero, add_zero]
          exact max_eq_right (by linarith)
        exact this
      rw [hH1]
      exact joined_in_collar_below_gap φ hbc hbi hb0 hd1 hdZ w t _ ht0 htd hg0

/-- **Pushing off a cuff.** See the module docstring. -/
theorem exists_taper {Y : Type u} [TopologicalSpace Y] (hY : IsSurface Y) {C : Set Y}
  (hC : IsCuff C) (φ : Circle ≃ₜ C)
    {Z : Set Y} (hZ : IsClosed Z) :
    ∃ H : 𝕀 × Y → Y, Continuous H ∧ (∀ y, H (0, y) = y) ∧ Function.Injective (fun y => H (1, y)) ∧
      (∀ z ∈ Z, H (1, z) = z) ∧
      (∀ y, H (1, y) ∈ Z → y ∈ Z) ∧ (∀ y, H (1, y) ∈ C → H (1, y) ∈ Z) := by
  obtain ⟨H, h1, h2, h3, h4, h5, h6, -⟩ := exists_taper_sides hY hC φ hZ
  exact ⟨H, h1, h2, h3, h4, h5, h6⟩

end GraphMinor.GM07
