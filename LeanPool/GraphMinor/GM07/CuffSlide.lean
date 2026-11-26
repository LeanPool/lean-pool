/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.MatchDiscs

/-!
# Moving points along the cuffs

The matching from `exists_matching_of_discs` has its ends close to the points of `Y`, at places that
depend on the forest. The
statement of Graph Minors VII, (3.4) (page 220), asks for a set `X` fixed in advance. So we slide
the ends along the cuffs to the
points of `X`, by a homeomorphism of `Σ` that fixes the forest. We get the slide in the closed
surface with the cuffs capped, in a
thin rectangle around a piece of a cuff (`exists_bd_slide`). This slide keeps the two sides of the
cuff apart, so it restricts to `Σ`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric Complex GraphMinor.Surface GraphMinor.GM11

variable {S : Type} [TopologicalSpace S]

/-- An injective arc on an interval has a strip chart in the surface obtained by capping. -/
theorem exists_capped_strip_chart (hS : IsSurface S) {g : ℝ → S} {a b : ℝ}
    (hg : Continuous g) (hab : a < b) (hi : InjOn g (Icc a b)) :
    ∃ (T : Type) (_ : TopologicalSpace T) (j : S → T) (O : Set ℂ) (K : ℂ → T)
      (θ : unitInterval → ℝ),
      IsClosedSurface T ∧ IsClosedEmbedding j ∧ frontier (range j) = j '' bd S ∧
      let par : unitInterval → ℝ := fun u => a + u.1 * (b - a)
      (∀ u, par u ∈ Icc a b) ∧ StrictMono par ∧ (∀ r ∈ Icc a b, ∃ u, par u = r) ∧
      StripChart O K ∧ Continuous θ ∧ StrictMono θ ∧
      ∀ u, (θ u : ℂ) ∈ O ∧ K (θ u) = j (g (par u)) := by
  have ht2S : T2Space S := hS.2.1
  have hcS : CompactSpace S := hS.1
  obtain ⟨T, tT, j, K', hT, hj, hK', hu, hi', -⟩ := exists_capAll S hS
  have ht2 : T2Space T := hT.2.1
  have hcT : CompactSpace T := hT.1
  have hab' : 0 < b - a := sub_pos.mpr hab
  let par : unitInterval → ℝ := fun u => a + u.1 * (b - a)
  have hpar : ∀ u, par u ∈ Icc a b := fun u => by
    have h0 := u.2.1
    have h1 := u.2.2
    exact ⟨by simp only [par]; nlinarith, by simp only [par]; nlinarith⟩
  have hparc : Continuous par := by simp only [par]; fun_prop
  have hparm : StrictMono par := fun s t h => by
    have h' : s.1 < t.1 := h
    simp only [par]
    nlinarith
  have hpars : ∀ r ∈ Icc a b, ∃ u, par u = r := fun r hr => by
    refine ⟨⟨(r - a) / (b - a), div_nonneg (by linarith [hr.1]) hab'.le,
      (div_le_one hab').mpr (by linarith [hr.2])⟩, ?_⟩
    simp only [par]
    field_simp
    ring
  let A : unitInterval → T := fun u => j (g (par u))
  have hA : IsArcMap A := ⟨hj.continuous.comp (hg.comp hparc), fun s t h => hparm.injective (hi
    (hpar s) (hpar t) (hj.injective h))⟩
  obtain ⟨O, K, θ, hK, hθc, hθm, hθ⟩ := exists_stripChart_of_arc hT hA
  exact ⟨T, tT, j, O, K, θ, hT, hj, cap_frontier hT hj hK' hu hi',
    hpar, hparm, hpars, hK, hθc, hθm, hθ⟩

/-- **A slide along a piece of `bd(Σ)`.** If `g` is an arc in `bd(Σ)` that misses the closed set
`Z`, there is a homeomorphism of `Σ`
that fixes `Z` and moves `g m` to `g x`. -/
theorem exists_bd_slide (hS : IsSurface S) {g : ℝ → S} {a x m b : ℝ} (hg : Continuous g)
  (hax : a < x) (hxm : x < m) (hmb : m < b)
    (hi : InjOn g (Icc a b)) (_hbd : ∀ u ∈ Icc a b, g u ∈ bd S) (hrest : IsClosed
      (bd S \ g '' Ioo a b)) {Z : Set S} (hZ : IsClosed Z)
    (hZg : ∀ u ∈ Icc a b, g u ∉ Z) : ∃ α : S ≃ₜ S, (∀ z ∈ Z, α z = z) ∧ α (g m) = g x := by
  have ht2S : T2Space S := hS.2.1
  have hcS : CompactSpace S := hS.1
  have hab : a < b := by linarith
  obtain ⟨T, tT, j, O, K, θ, hT, hj, hfr, hpar, hparm, hpars, hK, hθc, hθm, hθ⟩ :=
    exists_capped_strip_chart hS hg hab hi
  have ht2 : T2Space T := hT.2.1
  have hcT : CompactSpace T := hT.1
  let par : unitInterval → ℝ := fun u => a + u.1 * (b - a)
  let A : unitInterval → T := fun u => j (g (par u))
  change StrictMono par at hparm
  change ∀ r ∈ Icc a b, ∃ u, par u = r at hpars
  change ∀ u, (θ u : ℂ) ∈ O ∧ K (θ u) = A u at hθ
  -- The points in the chart.
  obtain ⟨ux, hux⟩ := hpars x ⟨hax.le, by linarith⟩
  obtain ⟨um, hum⟩ := hpars m ⟨by linarith, hmb.le⟩
  have hux0 : (0 : unitInterval) < ux := hparm.lt_iff_lt.mp (by rw [hux]; simpa [par] using hax)
  have hum1 : um < 1 := hparm.lt_iff_lt.mp (by rw [hum]; simpa [par] using hmb)
  have huxm : ux < um := hparm.lt_iff_lt.mp (by rw [hux, hum]; exact hxm)
  set x' := θ ux with hx'
  set m' := θ um with hm'
  set a' := (θ 0 + x') / 2 with ha'
  set b' := (θ 1 + m') / 2 with hb'
  have h0x : θ 0 < x' := hθm hux0
  have hxm' : x' < m' := hθm huxm
  have hm1 : m' < θ 1 := hθm hum1
  have ha1 : θ 0 < a' := by linarith
  have ha2 : a' < x' := by linarith
  have hb1 : m' < b' := by linarith
  have hb2 : b' < θ 1 := by linarith
  have hreal : ∀ r ∈ Icc a' b', ∃ u : unitInterval, u ≠ 0 ∧ u ≠ 1 ∧ θ u = r := fun r hr => by
    obtain ⟨u, hu'⟩ := intermediate_value_univ (0 : unitInterval) 1 hθc (show r ∈ Icc (θ 0)
      (θ 1) from ⟨by linarith [hr.1], by linarith [hr.2]⟩)
    refine ⟨u, ?_, ?_, hu'⟩
    · rintro rfl
      linarith [hr.1, hu'.symm]
    · rintro rfl
      linarith [hr.2, hu'.symm]
  -- The closed set the rectangle must miss.
  let Z₂ : Set T := j '' Z ∪ j '' (bd S \ g '' Ioo a b)
  have hZ₂ : IsClosed Z₂ := (hj.isClosedMap _ hZ).union (hj.isClosedMap _ hrest)
  have hparIoo : ∀ u : unitInterval, u ≠ 0 → u ≠ 1 → par u ∈ Ioo a b := fun u h0 h1 => by
    have h2 : 0 < u.1 := unitInterval.pos_iff_ne_zero.mpr h0
    have h3 : u.1 < 1 := unitInterval.lt_one_iff_ne_one.mpr h1
    exact ⟨by simp only [par]; nlinarith, by simp only [par]; nlinarith⟩
  have hAZ : ∀ u : unitInterval, u ≠ 0 → u ≠ 1 → A u ∉ Z₂ := fun u h0 h1 => by
    rintro (⟨z, hz, e⟩ | ⟨z, hz, e⟩)
    · rw [hj.injective e] at hz
      exact hZg _ (hpar u) hz
    · rw [hj.injective e] at hz
      exact hz.2 ⟨_, hparIoo u h0 h1, rfl⟩
  let Ω : Set ℂ := O ∩ K ⁻¹' Z₂ᶜ
  have hΩ : IsOpen Ω := hK.hc.isOpen_inter_preimage hK.isOpen hZ₂.isOpen_compl
  have hcpt : IsCompact (((↑) : ℝ → ℂ) '' Icc a' b') := isCompact_Icc.image continuous_ofReal
  have hsubΩ : ((↑) : ℝ → ℂ) '' Icc a' b' ⊆ Ω := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨u, h0, h1, rfl⟩ := hreal r hr
    refine ⟨(hθ u).1, ?_⟩
    simp only [mem_preimage, mem_compl_iff]
    rw [(hθ u).2]
    exact hAZ u h0 h1
  obtain ⟨δ₀, hδ₀, hth⟩ := hcpt.exists_thickening_subset_open hΩ hsubΩ
  let δ := δ₀ / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  let R : Set ℂ := Icc a' b' ×ℂ Icc (-δ) δ
  have hRΩ : R ⊆ Ω := fun z hz => by
    refine hth (mem_thickening_iff.mpr ⟨(z.re : ℂ), ⟨z.re, hz.1, rfl⟩, ?_⟩)
    have h1 : z - (z.re : ℂ) = (z.im : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [dist_eq_norm, h1, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have := abs_le.mpr hz.2
    simp only [δ] at this
    linarith
  have hRO : R ⊆ O := fun z hz => (hRΩ hz).1
  obtain ⟨ψ, hψc, hψm, hψa, hψb, hψx, hψl⟩ := exists_slide_fun ha2 hxm' hb1
  obtain ⟨e, he1, he2, he3⟩ := exists_slide hK (a := a') (b := b') (ε := δ)
    (by linarith) hδ hRO hψc hψm hψa hψb hψl
  -- The two sides of the rectangle.
  have hbdaxis : ∀ w ∈ R, K w ∈ j '' bd S → w.im = 0 := fun w hw h => by
    obtain ⟨z, hz, e'⟩ := h
    have h2 : z ∈ g '' Ioo a b := by
      by_contra hn
      exact (hRΩ hw).2 (.inr ⟨z, ⟨hz, hn⟩, e'⟩)
    obtain ⟨r, hr, rfl⟩ := h2
    obtain ⟨u, hu'⟩ := hpars r ⟨hr.1.le, hr.2.le⟩
    have h3 : K w = K (θ u) := by
      rw [(hθ u).2, ← e']
      simp only [A, hu']
    have h4 := hK.hi (hRO hw) (hθ u).1 h3
    rw [h4]
    simp
  have hside : ∀ {P : ℝ → Prop}, Convex ℝ {w : ℂ | w ∈ R ∧ P w.im} → (∀ r, P r → r ≠ 0)
    → ∀ w ∈ R, ∀ w' ∈ R, P w.im → P w'.im →
      K w ∈ range j → K w' ∈ range j := fun {P} hconv hP w hw w' hw' h1 h2 h3 => by
    by_contra hn
    have hset : IsPreconnected (K '' {w : ℂ | w ∈ R ∧ P w.im}) :=
      hconv.isPreconnected.image K (hK.hc.mono fun z hz => hRO hz.1)
    have hcov : K '' {w : ℂ | w ∈ R ∧ P w.im} ⊆ range j ∪ closure (range j)ᶜ := fun z _ => by
      by_cases hzr : z ∈ range j
      · exact .inl hzr
      · exact .inr (subset_closure hzr)
    obtain ⟨z, ⟨w₀, hw₀, rfl⟩, hz⟩ := isPreconnected_closed_iff.mp hset _ _ hj.isClosed_range
      isClosed_closure hcov
      ⟨K w, ⟨w, ⟨hw, h1⟩, rfl⟩, h3⟩ ⟨K w', ⟨w', ⟨hw', h2⟩, rfl⟩, subset_closure hn⟩
    have hz' : K w₀ ∈ frontier (range j) := by
      rw [frontier_eq_closure_inter_closure, hj.isClosed_range.closure_eq]
      exact hz
    rw [hfr] at hz'
    exact hP _ hw₀.2 (hbdaxis w₀ hw₀.1 hz')
  have hRconv : Convex ℝ R := ((convex_Icc a' b').linear_preimage Complex.reLm).inter ((convex_Icc
    (-δ) δ).linear_preimage Complex.imLm)
  have hup : Convex ℝ {w : ℂ | w ∈ R ∧ 0 < w.im} := hRconv.inter (convex_halfSpace_im_gt 0)
  have hlo : Convex ℝ {w : ℂ | w ∈ R ∧ w.im < 0} := hRconv.inter (convex_halfSpace_im_lt 0)
  have hsameR : ∀ w ∈ R, ∀ w' ∈ R, w.im = w'.im → (K w ∈ range j → K w' ∈ range j)
    := fun w hw w' hw' him h => by
    rcases lt_trichotomy w.im 0 with h0 | h0 | h0
    · exact hside (P := fun r => r < 0) hlo (fun r hr => hr.ne) w hw w' hw' h0 (him ▸ h0) h
    · have : w'.im = 0 := him ▸ h0
      have h2 : w' = (w'.re : ℂ) := by
        apply Complex.ext <;> simp [this]
      obtain ⟨u, -, -, hu'⟩ := hreal _ hw'.1
      rw [h2, ← hu', (hθ u).2]
      exact ⟨_, rfl⟩
    · exact hside (P := fun r => 0 < r) hup (fun r hr => hr.ne') w hw w' hw' h0 (him ▸ h0) h
  have hinv : ∀ z, z ∈ range j ↔ e z ∈ range j := fun z => by
    by_cases hz : z ∈ K '' R
    · obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨w', hw', -, him, he⟩ := he3 w hw
      rw [he]
      exact ⟨hsameR w hw w' hw' him.symm, hsameR w' hw' w hw him⟩
    · rw [he1 z hz]
  let hjh := hj.isEmbedding.toHomeomorph
  let α : S ≃ₜ S := hjh.trans ((e.subtype hinv).trans hjh.symm)
  have hα : ∀ s, j (α s) = e (j s) := fun s => by
    have h1 : hjh (α s) = (e.subtype hinv) (hjh s) := by
      simp only [α, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
    exact congrArg Subtype.val h1
  refine ⟨α, fun z hz => hj.injective ?_, hj.injective ?_⟩
  · rw [hα, he1]
    rintro ⟨w, hw, h⟩
    exact (hRΩ hw).2 (.inl ⟨z, hz, h.symm⟩)
  · rw [hα]
    have h1 : j (g m) = K m' := by
      rw [hm', (hθ um).2]
      simp only [A, hum]
    have h2 : j (g x) = K x' := by
      rw [hx', (hθ ux).2]
      simp only [A, hux]
    rw [h1, h2, he2 m' ⟨by linarith, by linarith⟩, hψx]

/-- **Many slides at once.** If the arcs `g i` are disjoint and miss the closed set `Z`, then one
homeomorphism of `Σ` fixes `Z` and moves
`g i (m i)` to `g i (x i)` for all `i`. -/
theorem exists_bd_slides (hS : IsSurface S) {ι : Type*} [Finite ι] {g : ι → ℝ → S} {a x m b : ι
  → ℝ} (hg : ∀ i, Continuous (g i))
    (hax : ∀ i, a i < x i) (hxm : ∀ i, x i < m i) (hmb : ∀ i, m i < b i) (hi : ∀ i, InjOn (g i)
      (Icc (a i) (b i)))
    (hbd : ∀ i, ∀ u ∈ Icc (a i) (b i), g i u ∈ bd S) (hrest : ∀ i, IsClosed (bd S \ g i '' Ioo
      (a i) (b i))) {Z : Set S} (hZ : IsClosed Z)
    (hZg : ∀ i, ∀ u ∈ Icc (a i) (b i), g i u ∉ Z)
    (hdis : ∀ i j, i ≠ j → Disjoint (g i '' Icc (a i) (b i)) (g j '' Icc (a j) (b j))) :
    ∃ α : S ≃ₜ S, (∀ z ∈ Z, α z = z) ∧ ∀ i, α (g i (m i)) = g i (x i) := by
  classical
  have ht2S : T2Space S := hS.2.1
  have : Fintype ι := Fintype.ofFinite ι
  have hArc : ∀ i, IsClosed (g i '' Icc (a i) (b i)) := fun i => (isCompact_Icc.image
    (hg i)).isClosed
  have key : ∀ J : Finset ι, ∃ α : S ≃ₜ S, (∀ z ∈ Z, α z = z) ∧ (∀ i ∈ J, α (g i (m i)) = g i
    (x i)) ∧
      ∀ i, i ∉ J → ∀ u ∈ Icc (a i) (b i), α (g i u) = g i u := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      exact ⟨Homeomorph.refl S, fun _ _ => rfl, by simp, fun _ _ _ _ => rfl⟩
    | insert i₀ J hi₀ ih =>
      obtain ⟨α, h1, h2, h3⟩ := ih
      let Z' : Set S := Z ∪ ⋃ i ∈ {i | i ≠ i₀}, g i '' Icc (a i) (b i)
      have hZ' : IsClosed Z' := hZ.union ((toFinite _).isClosed_biUnion fun i _ => hArc i)
      have hZ'g : ∀ u ∈ Icc (a i₀) (b i₀), g i₀ u ∉ Z' := fun u hu => by
        rintro (h | h)
        · exact hZg i₀ u hu h
        · obtain ⟨i, hi', h4⟩ := mem_iUnion₂.mp h
          exact disjoint_left.mp (hdis i i₀ hi') h4 ⟨u, hu, rfl⟩
      obtain ⟨β, h4, h5⟩ := exists_bd_slide hS (hg i₀) (hax i₀) (hxm i₀) (hmb i₀) (hi i₀) (hbd i₀)
        (hrest i₀) hZ' hZ'g
      have hxI : ∀ i, x i ∈ Icc (a i) (b i) := fun i => ⟨(hax i).le, by linarith [hxm i, hmb i]⟩
      have hmI : ∀ i, m i ∈ Icc (a i) (b i) := fun i => ⟨by linarith [hax i, hxm i], (hmb i).le⟩
      refine ⟨α.trans β, fun z hz => ?_, fun i hi' => ?_, fun i hi' u hu => ?_⟩
      · rw [Homeomorph.trans_apply, h1 z hz, h4 z (.inl hz)]
      · rw [Homeomorph.trans_apply]
        rcases Finset.mem_insert.mp hi' with rfl | h6
        · rw [h3 _ hi₀ _ (hmI _), h5]
        · have hne : i ≠ i₀ := fun e => hi₀ (e ▸ h6)
          rw [h2 i h6]
          exact h4 _ (.inr (mem_iUnion₂.mpr ⟨i, hne, _, hxI i, rfl⟩))
      · have hne : i ≠ i₀ := fun e => hi' (e ▸ Finset.mem_insert_self _ _)
        have hJ : i ∉ J := fun e => hi' (Finset.mem_insert_of_mem e)
        rw [Homeomorph.trans_apply, h3 i hJ u hu]
        exact h4 _ (.inr (mem_iUnion₂.mpr ⟨i, hne, _, hu, rfl⟩))
  obtain ⟨α, h1, h2, -⟩ := key Finset.univ
  exact ⟨α, h1, fun i => h2 i (Finset.mem_univ i)⟩

/-- Each point of `bd(Σ)` has a parameter of its cuff, with the point at a place `q` of our choice
on the circle. -/
theorem exists_cuffParam (hS : IsSurface S) {y : S} (hy : y ∈ bd S) (q : Circle) : ∃ f : ℝ
  → S, Continuous f ∧ (∀ t, Circle.exp t = q → f t = y) ∧
    InjOn f (Ioc (-Real.pi) Real.pi) ∧ f (-Real.pi) = f Real.pi ∧ (∀ t ∈ Icc
      (-Real.pi) Real.pi, f t ∈ bd S) ∧
    IsClosed (bd S \ f '' Icc (-Real.pi) Real.pi) := by
  classical
  have ht2 : T2Space S := hS.2.1
  obtain ⟨hcl, hfin, harc⟩ := cuff_statement.{0} S hS
  let C : Set S := connectedComponentIn (bd S) y
  have hC : C ∈ cuffs S := ⟨y, hy, rfl⟩
  obtain ⟨φ⟩ := harc C hC
  have hyC : y ∈ C := mem_connectedComponentIn hy
  let p : Circle := φ.symm ⟨y, hyC⟩ * q⁻¹
  let f : ℝ → S := fun t => (φ (p * Circle.exp t)).1
  have hfc : Continuous f := continuous_subtype_val.comp (φ.continuous.comp
    (continuous_const.mul Circle.exp.continuous))
  have hCb : C ⊆ bd S := connectedComponentIn_subset _ _
  have hinj : InjOn f (Ioc (-Real.pi) Real.pi) := fun s hs t ht h => by
    have h1 := φ.injective (Subtype.ext h)
    have h2 : Circle.exp s = Circle.exp t := mul_left_cancel h1
    exact Circle.invOn_arg_exp.1.injOn hs ht h2
  have hper : f (-Real.pi) = f Real.pi := by
    have h1 : Circle.exp (-Real.pi) = Circle.exp Real.pi := by
      have h2 := Circle.periodic_exp (-Real.pi)
      rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h2
      exact h2.symm
    simp only [f, h1]
  have himg : f '' Icc (-Real.pi) Real.pi = C := by
    ext x
    constructor
    · rintro ⟨t, -, rfl⟩
      exact (φ _).2
    · intro hx
      obtain ⟨t, ht, h⟩ := Circle.surjOn_exp_neg_pi_pi (mem_univ (p⁻¹ * φ.symm ⟨x, hx⟩))
      refine ⟨t, ⟨ht.1.le, ht.2⟩, ?_⟩
      simp [f, h]
  have hrest : bd S \ C = ⋃₀ ((cuffs S) \ {C}) := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨connectedComponentIn (bd S) x, ⟨⟨x, h1, rfl⟩, ?_⟩, mem_connectedComponentIn h1⟩
      intro h3
      exact h2 (h3 ▸ mem_connectedComponentIn h1)
    · rintro ⟨D, ⟨⟨z, hz, rfl⟩, hne⟩, hx⟩
      refine ⟨connectedComponentIn_subset _ _ hx, fun h2 => hne ?_⟩
      change connectedComponentIn (bd S) z = C
      rw [connectedComponentIn_eq hx]
      exact (connectedComponentIn_eq h2).symm
  refine ⟨f, hfc, ?_, hinj, hper, fun t ht => hCb (himg ▸ mem_image_of_mem f ht), ?_⟩
  · intro t ht
    simp [f, p, ht]
  · rw [himg, hrest]
    refine (hfin.subset sdiff_subset).isClosed_sUnion fun D hD => ?_
    exact (harc D hD.1).isCompact.isClosed

/-- Each point of `bd(Σ)` has a parameter of its cuff, with the point at `0`. -/
theorem exists_cuffMark (hS : IsSurface S) {y : S} (hy : y ∈ bd S) : ∃ f : ℝ → S, Continuous f
  ∧ f 0 = y ∧
    InjOn f (Ioc (-Real.pi) Real.pi) ∧ f (-Real.pi) = f Real.pi ∧ (∀ t ∈ Icc
      (-Real.pi) Real.pi, f t ∈ bd S) ∧
    IsClosed (bd S \ f '' Icc (-Real.pi) Real.pi) := by
  obtain ⟨f, h1, h2, h3⟩ := exists_cuffParam hS hy 1
  exact ⟨f, h1, h2 0 (by simp), h3⟩

/-- Each point of `bd(Σ)` has a parameter of its cuff, with the point at the seam `π`. -/
theorem exists_cuffSeam (hS : IsSurface S) {y : S} (hy : y ∈ bd S) : ∃ f : ℝ → S, Continuous f
  ∧ f Real.pi = y ∧
    InjOn f (Ioc (-Real.pi) Real.pi) ∧ f (-Real.pi) = f Real.pi ∧ (∀ t ∈ Icc
      (-Real.pi) Real.pi, f t ∈ bd S) ∧
    IsClosed (bd S \ f '' Icc (-Real.pi) Real.pi) := by
  obtain ⟨f, h1, h2, h3⟩ := exists_cuffParam hS hy (Circle.exp Real.pi)
  exact ⟨f, h1, h2 _ rfl, h3⟩

/-- A homeomorphism that fixes a drawing point by point does not change it. -/
theorem mapDrawingHomeo_eq_self {α : S ≃ₜ S} {H : Drawing S} (h : ∀ z ∈ H.U, α z
  = z) : mapDrawingHomeo α H = H := by
  have h1 : α '' H.U = H.U := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rwa [h w hw]
    · exact fun hz => ⟨z, hz, h z hz⟩
  have h2 : α '' H.V = H.V := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rwa [h w (H.V_subset_U hw)]
    · exact fun hz => ⟨z, hz, h z (H.V_subset_U hz)⟩
  cases H
  simp only [mapDrawingHomeo, Drawing.mk.injEq]
  exact ⟨h1, h2⟩

/-- Pieces of the cuffs around the points of a finite set `Y`, with disjoint doubles. -/
theorem exists_marks (hS : IsSurface S) {Y : Set S} (hY : Y ⊆ bd S) (hf : Y.Finite) :
    ∃ (f : S → ℝ → S) (ε : S → ℝ), (∀ y ∈ Y, CuffMark (f y) (ε y) y) ∧
      ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → Disjoint (f y '' Icc (-(2 * ε y)) (2 * ε y)) (f y' '' Icc
        (-(2 * ε y')) (2 * ε y')) := by
  classical
  have ht2 : T2Space S := hS.2.1
  obtain ⟨O, hO, hd⟩ := hf.t2_separation
  have key : ∀ y : S, ∃ (g : ℝ → S) (e : ℝ), y ∈ Y → CuffMark g e y ∧ g '' Icc (-(2 * e))
    (2 * e) ⊆ O y := fun y => by
    by_cases hy : y ∈ Y
    · obtain ⟨g, hc, h0, hi, hp, hb, hr⟩ := exists_cuffMark hS (hY hy)
      have hopen : IsOpen (g ⁻¹' O y) := (hO y).2.preimage hc
      have hz : (0 : ℝ) ∈ g ⁻¹' O y := by
        rw [mem_preimage, h0]
        exact (hO y).1
      obtain ⟨r, hr0, hball⟩ := Metric.isOpen_iff.mp hopen 0 hz
      have hmin : 0 < min (r / 4) (1 / 2) := lt_min (by linarith) (by norm_num)
      refine ⟨g, min (r / 4) (1 / 2), fun _ => ⟨⟨hc, h0, hmin, ?_, hi, hp, hb, hr⟩, ?_⟩⟩
      · linarith [min_le_right (r / 4) (1 / 2 : ℝ)]
      · rintro _ ⟨t, ht, rfl⟩
        refine hball (mem_ball_zero_iff.mpr ?_)
        have h1 := min_le_left (r / 4) (1 / 2 : ℝ)
        rw [Real.norm_eq_abs, abs_lt]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · exact ⟨fun _ => y, 0, fun h => (hy h).elim⟩
  choose f ε hfe using key
  exact ⟨f, ε, fun y hy => (hfe y hy).1, fun y hy y' hy' hne =>
    (hd hy hy' hne).mono (hfe y hy).2 (hfe y' hy').2⟩

/-- **A matching around a forest.** From marks on the cuffs at `Y = V(H) ∩ bd(Σ)`, we get the discs
of `exists_forest_thick` and the matching of
`exists_matching_of_discs`. Its ends lie on the marks, it strictly surrounds `H`, and it surrounds
other forests in the same discs. -/
theorem exists_thick_matching (hS : IsSurface S) {Y : Set S} {H : Drawing S}
  (hHf : IsSurfaceForest H) (hHY : H.V ∩ bd S = Y) {f : S → ℝ → S} {ε : S → ℝ}
    (hm : ∀ y ∈ Y, CuffMark (f y) (ε y) y)
    (hd : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → Disjoint (f y '' Icc (-(2 * ε y)) (2 * ε y)) (f y' '' Icc
      (-(2 * ε y')) (2 * ε y'))) :
    ∃ (c : S → Set S) (σ₁ σ₂ : S → ℝ) (G : Drawing S), (∀ y ∈ Y, 0 < σ₁ y ∧ σ₁ y < ε y ∧ 0 < σ₂ y
      ∧ σ₂ y < ε y) ∧ IsMatching G ∧
      G.V = (⋃ y ∈ Y, {f y (σ₁ y), f y (-σ₂ y)}) ∧ MatchingStrictlySurroundsForest G H ∧
      (∀ y ∈ Y, IsClosedDisc (c y) ∧ y ∈ discBd (c y) ∧ ∃ O, IsOpen O ∧ y ∈ O ∧ O \ bd S ⊆ discInt
        (c y)) ∧
      (∀ u ∈ Y, ∀ v ∈ Y, c u ≠ c v → Disjoint (c u) (c v)) ∧ (∀ y ∈ Y, Disjoint (discInt (c y))
        (bd S)) ∧
      ∀ H' : Drawing S, H'.V ∩ bd S = Y → (∀ u ∈ Y, ∀ v ∈ Y, c u = c v → Nonempty
        (GraphWalk H'.toGraph u v)) →
      (∀ e ∈ H'.E, ∀ u ∈ H'.V, ∀ y ∈ Y, u ∈ closure e → u ∈ c y → closure e ⊆ c y) →
      (∀ y ∈ Y, ∀ z ∈ H'.U, z ∈ discBd (c y) → z ∈ Y) → MatchingStrictlySurroundsForest G H' := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hpi := Real.pi_gt_three
  have hf : Y.Finite := H.finite_V.subset fun y hy => (hHY ▸ hy : y ∈ H.V ∩ bd S).1
  have hε0 : ∀ y ∈ Y, 0 < ε y := fun y hy => (hm y hy).pos
  have hε1 : ∀ y ∈ Y, ε y < 1 := fun y hy => (hm y hy).lt
  have hinj : ∀ y ∈ Y, ∀ u ∈ Icc (-(2 * ε y)) (2 * ε y), ∀ v ∈ Icc (-(2 * ε y)) (2 * ε y), f y u
    = f y v → u = v := fun y hy u hu v hv h => by
    have h1 := hε1 y hy
    exact (hm y hy).inj ⟨by linarith [hu.1], by linarith [hu.2]⟩ ⟨by linarith [hv.1],
      by linarith [hv.2]⟩ h
  have honBd : ∀ y ∈ Y, ∀ u ∈ Icc (-(2 * ε y)) (2 * ε y), f y u ∈ bd S := fun y hy u hu => by
    have h1 := hε1 y hy
    exact (hm y hy).onBd u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hdis : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → ∀ u ∈ Icc (-(2 * ε y)) (2 * ε y), ∀ v ∈ Icc (-(2 * ε y'))
    (2 * ε y'), f y u ≠ f y' v :=
    fun y hy y' hy' hne u hu v hv e => disjoint_left.mp (hd y hy y' hy' hne) ⟨u, hu, rfl⟩ ⟨v, hv,
      e.symm⟩
  have hY' : Y = H.V ∩ bd S := hHY.symm
  have hprop : ∀ z ∈ H.U, z ∈ bd S → z ∈ H.V := fun z h1 h2 => hHf.1 ⟨h2, h1⟩
  have hYm : ∀ z, z ∈ H.V → z ∈ bd S → z ∈ Y := fun z h1 h2 => hHY ▸ (⟨h1, h2⟩ : z ∈ H.V ∩ bd S)
  obtain ⟨c, σ₁, σ₂, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := exists_forest_thick hS hHf (f := f) (ε
    := ε) (fun y hy => hm y (hY' ▸ hy))
  have hσ : ∀ y ∈ Y, 0 < σ₁ y ∧ σ₁ y < ε y ∧ 0 < σ₂ y ∧ σ₂ y < ε y ∧ f y '' Icc (-σ₂ y)
    (σ₁ y) ⊆ discBd (c y) ∧
      ∃ O, IsOpen O ∧ f y '' Ioo (-σ₂ y) (σ₁ y) ⊆ O ∧ O ⊆ c y ∧ O \ bd S ⊆ discInt (c y)
        := fun y hy => h8 y (hY' ▸ hy)
  have hsubI : ∀ y ∈ Y, Icc (-σ₂ y) (σ₁ y) ⊆ Icc (-(2 * ε y)) (2 * ε y) := fun y hy u hu => by
    obtain ⟨a1, a2, a3, a4, -⟩ := hσ y hy
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h0m : ∀ y ∈ Y, (0 : ℝ) ∈ Icc (-(2 * ε y)) (2 * ε y) := fun y hy => by
    have := hε0 y hy
    exact ⟨by linarith, by linarith⟩
  have hYH : ∀ y ∈ Y, y ∈ H.V := fun y hy => (hY' ▸ hy : y ∈ H.V ∩ bd S).1
  obtain ⟨G, hG1, hG2, hG4, hG3'⟩ := exists_matching_of_discs hf (c := c) (ℓ := fun y => f y '' Icc
    (-σ₂ y) (σ₁ y)) (s := fun y => f y (σ₁ y))
    (t := fun y => f y (-σ₂ y)) (fun y hy => h1 y (hYH y hy)) (fun y hy => h7 y (hYH y hy))
    (fun u hu v hv h => h3 u (hYH u hu) v (hYH v hv) h) (fun y hy => by
      obtain ⟨a1, a2, a3, a4, a5, O, a6, a7, a8, -⟩ := hσ y hy
      have hlt : -σ₂ y < σ₁ y := by linarith
      have hne : f y (σ₁ y) ≠ f y (-σ₂ y) := fun e => by
        have := hinj y hy _ (hsubI y hy ⟨hlt.le, le_rfl⟩) _ (hsubI y hy ⟨le_rfl, hlt.le⟩) e
        linarith
      have hmemy : y = f y 0 := (hm y hy).zero.symm
      have h0I : (0 : ℝ) ∈ Icc (-σ₂ y) (σ₁ y) := ⟨by linarith, by linarith⟩
      refine ⟨(isLine_of_injOn (hm y hy).cont hlt fun u hu v hv e => hinj y hy u (hsubI y hy hu) v
        (hsubI y hy hv) e).symm, hne, a5, ?_, ⟨0, h0I, hmemy.symm⟩, ?_, ?_, O, a6, ?_, a8⟩
      · rintro _ ⟨u, hu, rfl⟩
        exact honBd y hy u (hsubI y hy hu)
      · intro e
        have := hinj y hy 0 (h0m y hy) _ (hsubI y hy ⟨hlt.le, le_rfl⟩)
          (by rw [(hm y hy).zero]; exact e)
        linarith
      · intro e
        have := hinj y hy 0 (h0m y hy) _ (hsubI y hy ⟨le_rfl, hlt.le⟩)
          (by rw [(hm y hy).zero]; exact e)
        linarith
      · rintro z ⟨⟨u, hu, rfl⟩, hz⟩
        exact a7 ⟨u, ⟨lt_of_le_of_ne hu.1 fun e => hz (.inr (congrArg _ e.symm)),
          lt_of_le_of_ne hu.2 fun e => hz (.inl (congrArg _ e))⟩, rfl⟩)
    (fun y hy y' hy' hne => disjoint_left.mpr fun z hz hz' => by
      obtain ⟨u, hu, rfl⟩ := hz
      obtain ⟨v, hv, e⟩ := hz'
      exact hdis y hy y' hy' hne u (hsubI y hy hu) v (hsubI y' hy' hv) e.symm)
    (fun v hv z hz => by
      obtain ⟨y, hy, h10⟩ := mem_iUnion₂.mp (h9 v (hYH v hv) hz)
      exact mem_iUnion₂.mpr ⟨y, hY' ▸ hy, h10⟩)
  have hG3 : MatchingStrictlySurroundsForest G H := hG3' H hHY (fun u hu v hv h => h2 u
    (hYH u hu) v (hYH v hv) h)
    (fun e he u hu y hy huc huy => by
      have h10 := h4 e he u hu huc
      by_cases h11 : c u = c y
      · exact h11 ▸ h10
      · exact (disjoint_left.mp (h3 u hu y (hYH y hy) h11) (h5 u hu) huy).elim)
    (fun y hy z hz hzb => hYm z (h6 y (hYH y hy) z hz hzb).1 (h6 y (hYH y hy) z hz hzb).2)
  refine ⟨c, σ₁, σ₂, G, fun y hy => ?_, hG1, hG2, hG3, fun y hy => ?_,
    fun u hu v hv h => h3 u (hYH u hu) v (hYH v hv) h, fun y hy => ?_, hG3'⟩
  · obtain ⟨a1, a2, a3, a4, -⟩ := hσ y hy
    exact ⟨a1, a2, a3, a4⟩
  · obtain ⟨a1, a2, a3, a4, a5, O, a6, a7, a8, a9⟩ := hσ y hy
    have h0I : (0 : ℝ) ∈ Icc (-σ₂ y) (σ₁ y) := ⟨by linarith, by linarith⟩
    have h0J : (0 : ℝ) ∈ Ioo (-σ₂ y) (σ₁ y) := ⟨by linarith, by linarith⟩
    exact ⟨h1 y (hYH y hy), a5 ⟨0, h0I, (hm y hy).zero⟩, O, a6, a7 ⟨0, h0J, (hm y hy).zero⟩, a9⟩
  · refine disjoint_left.mpr fun z hz hzb => hz.2 ?_
    obtain ⟨y', hy', h10⟩ := mem_iUnion₂.mp (h9 y (hYH y hy) ⟨hz.1, hzb⟩)
    have h11 := (hσ y' (hY' ▸ hy')).2.2.2.2.1 h10
    by_cases h12 : c y = c y'
    · exact h12 ▸ h11
    · exact (disjoint_left.mp (h3 y (hYH y hy) y' (hY'.symm ▸ hy' |> fun h =>
        (h : y' ∈ H.V ∩ bd S).1) h12) hz.1 (GM11.discBd_subset _ h11)).elim

omit [TopologicalSpace S] in
private theorem marked_cuff_point_has_signed_parameter
    {S : Type}
    {Y : Set S}
    (f : S → ℝ → S)
    (ε : S → ℝ)
    (hε0 : ∀ y ∈ Y, 0 < ε y) :
    ∀ (p : ↑Y × Bool), ∃ u ∈ Icc (-(2 * ε ↑p.1)) (2 * ε ↑p.1), u ≠ 0 ∧ (p.2 = true → 0 < u) ∧ (p.2
      = false → u < 0) ∧
        (fun p : Y × Bool => if p.2 = true then f (↑p.1) (ε ↑p.1) else f (↑p.1) (-ε ↑p.1)) p
      = f (↑p.1) u := by
  let pt := fun p : Y × Bool => if p.2 = true then f (↑p.1) (ε ↑p.1) else f (↑p.1) (-ε ↑p.1)
  rintro ⟨y, b⟩
  have h0 : 0 < ε y := hε0 y y.2
  cases b
  · refine ⟨-ε y, ⟨?_, ?_⟩, neg_ne_zero.mpr h0.ne', (fun h => by cases h),
      fun _ => neg_lt_zero.mpr h0, rfl⟩
    · change -(2 * ε y) ≤ -ε y
      linarith
    · change -ε y ≤ 2 * ε y
      linarith
  · refine ⟨ε y, ⟨?_, ?_⟩, h0.ne', fun _ => h0, (fun h => by cases h), rfl⟩
    · change -(2 * ε y) ≤ ε y
      linarith
    · change ε y ≤ 2 * ε y
      linarith

omit [TopologicalSpace S] in
private theorem marked_cuff_points_are_distinct
    {S : Type}
    {Y : Set S}
    (f : S → ℝ → S)
    (ε : S → ℝ)
    (hinj : ∀ y ∈ Y, ∀ u ∈ Icc (-(2 * ε y)) (2 * ε y), ∀ v ∈ Icc (-(2 * ε y)) (2 * ε y), f y u = f
      y v → u = v)
    (hdis : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → ∀ u ∈ Icc (-(2 * ε y)) (2 * ε y), ∀ v ∈ Icc (-(2 * ε y'))
      (2 * ε y'), f y u ≠ f y' v)
    (pt : ↑Y × Bool → S)
    (hptI : ∀ (p : ↑Y × Bool), ∃ u ∈ Icc (-(2 * ε ↑p.1)) (2 * ε ↑p.1), u ≠ 0 ∧ (p.2 = true → 0 <
      u) ∧ (p.2 = false → u < 0) ∧ pt p = f (↑p.1) u) :
    Function.Injective pt := by
  rintro ⟨y, b⟩ ⟨y', b'⟩ h
  obtain ⟨u, hu, -, hp1, hn1, e1⟩ := hptI ⟨y, b⟩
  obtain ⟨v, hv, -, hp2, hn2, e2⟩ := hptI ⟨y', b'⟩
  simp only at hu hv hp1 hn1 hp2 hn2 e1 e2
  rw [e1, e2] at h
  by_cases hy : y = y'
  · subst hy
    have huv := hinj y y.2 u hu v hv h
    have hb : b = b' := by
      cases b <;> cases b' <;> simp_all <;> linarith
    rw [hb]
  · exact (hdis y y.2 y' y'.2 (fun e => hy (Subtype.ext e)) u hu v hv h).elim

/-- **Graph Minors VII, (3.4), claim (1) (page 220).** For a finite set `Y` in `bd(Σ)`, there is a
set `X ⊆ bd(Σ)` with `|X| = 2|Y|` such that each
`Y`-forest is strictly surrounded by some `X`-matching. The route is as in the paper: take discs
around the components of the forest (`exists_forest_thick`), cut
their boundaries at `bd(Σ)` (`exists_matching_of_discs`), and slide the ends of the lines to `X`
(`exists_bd_slides`). -/
theorem exists_forest_matching (hS : IsSurface S) {Y : Set S} (hY : Y ⊆ bd S) (hf : Y.Finite) :
    ∃ X : Set S, X ⊆ bd S ∧ X.Finite ∧ X.ncard = 2 * Y.ncard ∧ ∀ H : Drawing S, IsYForest Y H →
      ∃ G : Drawing S, IsXMatching X G ∧ MatchingStrictlySurroundsForest G H := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hpi := Real.pi_gt_three
  obtain ⟨f, ε, hm, hd⟩ := exists_marks hS hY hf
  have hε0 : ∀ y ∈ Y, 0 < ε y := fun y hy => (hm y hy).pos
  have hε1 : ∀ y ∈ Y, ε y < 1 := fun y hy => (hm y hy).lt
  have hinj : ∀ y ∈ Y, ∀ u ∈ Icc (-(2 * ε y)) (2 * ε y), ∀ v ∈ Icc (-(2 * ε y)) (2 * ε y), f y u
    = f y v → u = v := fun y hy u hu v hv h => by
    have h1 := hε1 y hy
    exact (hm y hy).inj ⟨by linarith [hu.1], by linarith [hu.2]⟩ ⟨by linarith [hv.1],
      by linarith [hv.2]⟩ h
  have honBd : ∀ y ∈ Y, ∀ u ∈ Icc (-(2 * ε y)) (2 * ε y), f y u ∈ bd S := fun y hy u hu => by
    have h1 := hε1 y hy
    exact (hm y hy).onBd u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hdis : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → ∀ u ∈ Icc (-(2 * ε y)) (2 * ε y), ∀ v ∈ Icc (-(2 * ε y'))
    (2 * ε y'), f y u ≠ f y' v :=
    fun y hy y' hy' hne u hu v hv e => disjoint_left.mp (hd y hy y' hy' hne) ⟨u, hu, rfl⟩ ⟨v, hv,
      e.symm⟩
  have hpt : ∀ y ∈ Y, ∀ δ, |δ| ≤ 2 * ε y → δ ∈ Icc (-(2 * ε y)) (2 * ε y) := fun y _ δ h
    => abs_le.mp h
  let pt : ↥Y × Bool → S := fun p => if p.2 then f p.1 (ε p.1) else f p.1 (-ε p.1)
  have hptI : ∀ p : ↥Y × Bool, ∃ u ∈ Icc (-(2 * ε p.1)) (2 * ε p.1),
      u ≠ 0 ∧ (p.2 = true → 0 < u) ∧ (p.2 = false → u < 0) ∧ pt p = f p.1 u := by
    exact marked_cuff_point_has_signed_parameter (S := S) (Y := Y) f ε hε0
  have hptinj : Function.Injective pt := by
    exact marked_cuff_points_are_distinct (S := S) (Y := Y) f ε hinj hdis pt hptI
  let X : Set S := range pt
  have : Finite Y := hf.to_subtype
  have hXfin : X.Finite := finite_range pt
  have hXb : X ⊆ bd S := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨u, hu, -, -, -, e⟩ := hptI p
    rw [e]
    exact honBd _ p.1.2 u hu
  have hXcard : X.ncard = 2 * Y.ncard := by
    have h1 : X.ncard = Nat.card (↥Y × Bool) := by
      rw [← Nat.card_coe_set_eq]
      exact Nat.card_congr (Equiv.ofInjective pt hptinj).symm
    rw [h1, Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
      Nat.card_coe_set_eq]
    ring
  refine ⟨X, hXb, hXfin, hXcard, fun H hH => ?_⟩
  obtain ⟨hHf, hHY⟩ := hH
  have hprop : ∀ z ∈ H.U, z ∈ bd S → z ∈ H.V := fun z h1 h2 => hHf.1 ⟨h2, h1⟩
  have hYm : ∀ z, z ∈ H.V → z ∈ bd S → z ∈ Y := fun z h1 h2 => hHY ▸ (⟨h1, h2⟩ : z ∈ H.V ∩ bd S)
  obtain ⟨c, σ₁, σ₂, G, hσ, hG1, hG2, hG3, -, -, -, -⟩ := exists_thick_matching hS hHf hHY hm hd
  have h0m : ∀ y ∈ Y, (0 : ℝ) ∈ Icc (-(2 * ε y)) (2 * ε y) := fun y hy => by
    have := hε0 y hy
    exact ⟨by linarith, by linarith⟩
  -- The slides.
  let sg : ↥Y × Bool → ℝ := fun p => if p.2 then -1 else 1
  let g : ↥Y × Bool → ℝ → S := fun p u => f p.1 (sg p * u)
  let a : ↥Y × Bool → ℝ := fun p => -(2 * ε p.1)
  let x : ↥Y × Bool → ℝ := fun p => -ε p.1
  let m : ↥Y × Bool → ℝ := fun p => if p.2 then -σ₁ p.1 else -σ₂ p.1
  let b : ↥Y × Bool → ℝ := fun p => m p / 2
  have hsg : ∀ p, sg p = -1 ∨ sg p = 1 := fun p => by
    simp only [sg]
    split_ifs
    · exact .inl rfl
    · exact .inr rfl
  have hsgm : ∀ p, sg p * sg p = 1 := fun p => by
    rcases hsg p with h | h <;> rw [h] <;> norm_num
  have hmm : ∀ p : ↥Y × Bool, x p < m p ∧ m p < 0 := fun p => by
    obtain ⟨a1, a2, a3, a4⟩ := hσ p.1 p.1.2
    simp only [m, x]
    split_ifs
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  have hax : ∀ p, a p < x p := fun p => by
    have := hε0 p.1 p.1.2
    simp only [a, x]
    linarith
  have hmb : ∀ p, m p < b p := fun p => by
    have := (hmm p).2
    simp only [b]
    linarith
  have hb0 : ∀ p, b p < 0 := fun p => by
    have := (hmm p).2
    simp only [b]
    linarith
  have hpar : ∀ p, ∀ u ∈ Icc (a p) (b p), sg p * u ∈ Icc (-(2 * ε p.1)) (2 * ε p.1) := fun p u hu
    => by
    have h10 := hu.1
    have h11 := hb0 p
    have h12 := hu.2
    simp only [a] at h10
    rcases hsg p with h | h <;> rw [h]
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  have hparne : ∀ p, ∀ u ∈ Icc (a p) (b p), sg p * u ≠ 0 := fun p u hu e => by
    have h11 := hb0 p
    have h12 := hu.2
    rcases hsg p with h | h <;> rw [h] at e <;> linarith
  have hZg : ∀ p, ∀ u ∈ Icc (a p) (b p), g p u ∉ H.U := fun p u hu h => by
    have hb' := honBd _ p.1.2 _ (hpar p u hu)
    have hV := hprop _ h hb'
    have hmemY : f p.1 (sg p * u) ∈ Y := hYm _ hV hb'
    by_cases he : f p.1 (sg p * u) = p.1.1
    · have h0 : f p.1 0 = p.1.1 := (hm _ p.1.2).zero
      exact hparne p u hu (hinj _ p.1.2 _ (hpar p u hu) 0 (h0m _ p.1.2) (he.trans h0.symm))
    · exact hdis _ hmemY _ p.1.2 he 0 (h0m _ hmemY) _ (hpar p u hu) ((hm _ hmemY).zero)
  have hxI : ∀ p, x p ∈ Icc (a p) (b p) := fun p => ⟨(hax p).le, by linarith [(hmm p).1, hmb p]⟩
  have hmI : ∀ p, m p ∈ Icc (a p) (b p) := fun p => ⟨by linarith [(hmm p).1, hax p], (hmb p).le⟩
  obtain ⟨α, hα1, hα2⟩ := exists_bd_slides hS (g := g) (a := a) (x := x) (m := m) (b := b) (fun p
    => (hm _ p.1.2).cont.comp (by fun_prop))
    hax (fun p => (hmm p).1) hmb
    (fun p u hu v hv e => by
      have h10 := hinj _ p.1.2 _ (hpar p u hu) _ (hpar p v hv) e
      have h11 := congrArg (sg p * ·) h10
      simp only [← mul_assoc, hsgm, one_mul] at h11
      exact h11)
    (fun p u hu => honBd _ p.1.2 _ (hpar p u hu))
    (fun p => by
      have h0 : 0 < ε p.1 := hε0 p.1 p.1.2
      have h1' := hε1 p.1 p.1.2
      have h2' := hb0 p
      have h3' : a p = -(2 * ε p.1) := rfl
      have h4' := hmb p
      rcases hsg p with h | h
      · have heq : g p '' Ioo (a p) (b p) = f p.1 '' Ioo (-b p) (-a p) := by
          ext z
          constructor
          · rintro ⟨u, hu, rfl⟩
            exact ⟨-u, ⟨by linarith [hu.2], by linarith [hu.1]⟩, by simp [g, h]⟩
          · rintro ⟨u, hu, rfl⟩
            exact ⟨-u, ⟨by linarith [hu.2], by linarith [hu.1]⟩, by simp [g, h]⟩
        rw [heq]
        exact (hm _ p.1.2).isClosed_rest' (by linarith) (by linarith) (by linarith [hax p,
          (hmm p).1])
      · have heq : g p '' Ioo (a p) (b p) = f p.1 '' Ioo (a p) (b p) := by
          ext z
          constructor
          · rintro ⟨u, hu, rfl⟩
            exact ⟨u, hu, by simp [g, h]⟩
          · rintro ⟨u, hu, rfl⟩
            exact ⟨u, hu, by simp [g, h]⟩
        rw [heq]
        exact (hm _ p.1.2).isClosed_rest' (by linarith) (by linarith) (by linarith [hax p,
          (hmm p).1]))
    H.isClosed_U hZg
    (fun p q hne => disjoint_left.mpr fun z hz hz' => by
      obtain ⟨u, hu, rfl⟩ := hz
      obtain ⟨v, hv, e⟩ := hz'
      by_cases hy : p.1.1 = q.1.1
      · have hpq : p.1 = q.1 := Subtype.ext hy
        have hbne : p.2 ≠ q.2 := fun e' => hne (Prod.ext hpq e')
        have h10 : f q.1 (sg q * v) = f p.1 (sg p * u) := e
        rw [← hpq] at h10
        have hvp := hpar q v hv
        rw [← hpq] at hvp
        have h11 := hinj _ p.1.2 _ hvp _ (hpar p u hu) h10
        have hu0 := hb0 p
        have hv0 := hb0 q
        have hu1 := hu.2
        have hv1 := hv.2
        have hsgs : ∀ r : ↥Y × Bool, sg r = if r.2 then -1 else 1 := fun _ => rfl
        rw [hsgs p, hsgs q] at h11
        cases hp2 : p.2 <;> cases hq2 : q.2
        · exact hbne (hp2.trans hq2.symm)
        · simp only [hp2, hq2] at h11
          norm_num at h11
          linarith
        · simp only [hp2, hq2] at h11
          norm_num at h11
          linarith
        · exact hbne (hp2.trans hq2.symm)
      · exact hdis _ p.1.2 _ q.1.2 hy _ (hpar p u hu) _ (hpar q v hv) e.symm)
  have hFix : mapDrawingHomeo α H = H := mapDrawingHomeo_eq_self hα1
  have hXG : α '' G.V = X := by
    rw [hG2]
    have hval₁ : ∀ y : Y, α (f y (σ₁ y)) = f y (ε y) := fun y => by
      have := hα2 (y, true)
      simpa [g, sg, m, x] using this
    have hval₂ : ∀ y : Y, α (f y (-σ₂ y)) = f y (-ε y) := fun y => by
      have := hα2 (y, false)
      simpa [g, sg, m, x] using this
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨y, hy, hw'⟩ := mem_iUnion₂.mp hw
      rcases hw' with rfl | rfl
      · exact ⟨(⟨y, hy⟩, true), by simpa [pt] using (hval₁ ⟨y, hy⟩).symm⟩
      · exact ⟨(⟨y, hy⟩, false), by simpa [pt] using (hval₂ ⟨y, hy⟩).symm⟩
    · rintro ⟨⟨y, c'⟩, rfl⟩
      cases c'
      · exact ⟨f y (-σ₂ y), mem_iUnion₂.mpr ⟨y, y.2, .inr rfl⟩, by simpa [pt] using hval₂ y⟩
      · exact ⟨f y (σ₁ y), mem_iUnion₂.mpr ⟨y, y.2, .inl rfl⟩, by simpa [pt] using hval₁ y⟩
  have hXm : IsXMatching (α '' G.V) (mapDrawingHomeo α G) := IsXMatching.map_homeo α ⟨hG1, rfl⟩
  rw [hXG] at hXm
  have hsur := MatchingStrictlySurroundsForest.map_homeo α (G' := mapDrawingHomeo α G) rfl hG3
  rw [hFix] at hsur
  exact ⟨_, hXm, hsur⟩

/-- Graph Minors VII, (3.4), claim (1) (page 220), as the statement used in Sections 3, 7, and 9. -/
theorem forestSurroundingMatching.{u} : ForestSurroundingMatchingStatement.{u} := by
  intro S _ hS Y hY hf
  have : T2Space S := hS.2.1
  obtain ⟨S₀, tS₀, ⟨β⟩⟩ := exists_homeo_type_zero hS
  have hS₀ : IsSurface S₀ := isSurface_of_homeo β hS
  have : T2Space S₀ := hS₀.2.1
  have hY₀ : β '' Y ⊆ bd S₀ := by
    rw [← image_bd_homeomorph β]
    exact image_mono hY
  obtain ⟨X₀, hX₀_bd, hX₀_fin, hX₀_card, hX₀_surr⟩ :=
    exists_forest_matching hS₀ hY₀ (hf.image β)
  refine ⟨β.symm '' X₀, ?_, hX₀_fin.image β.symm, ?_, fun H hH => ?_⟩
  · rw [← image_bd_homeomorph β.symm]
    exact image_mono hX₀_bd
  · rw [ncard_image_of_injective _ β.symm.injective, hX₀_card,
      ncard_image_of_injective _ β.injective]
  · obtain ⟨G₀, hG₀_match, hG₀_surr⟩ := hX₀_surr (mapDrawingHomeo β H) (hH.map_homeo β)
    refine ⟨mapDrawingHomeo β.symm G₀, hG₀_match.map_homeo β.symm, ?_⟩
    have hsur := MatchingStrictlySurroundsForest.map_homeo β.symm
      (G' := mapDrawingHomeo β.symm G₀) rfl hG₀_surr
    rwa [mapDrawingHomeo_symm_mapDrawingHomeo] at hsur

end GraphMinor.GM07
