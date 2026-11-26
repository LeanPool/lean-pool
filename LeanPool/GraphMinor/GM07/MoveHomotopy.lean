/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.PushForest
public import LeanPool.GraphMinor.GM07.StarDisc

/-!
# Homeomorphisms homotopic to the identity

(4.4) of Graph Minors VII (page 223) asks for a forest homotopic to a given one, not only
homoplastic. So the forest may be moved only by homeomorphisms that keep curves in their homotopy
classes. `IsMove α` says this for curves with ends on the boundary. A homeomorphism that lives in a
convex chart is a move, by a straight line homotopy in the chart (`isMove_of_chart`), and the image
of a forest under a move is homotopic to it (`forestsHomotopic_of_move`). The main example shrinks
an arc off the boundary towards one of its ends (`exists_line_slide`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric Complex GraphMinor.Surface GraphMinor.GM11

variable {S : Type} [TopologicalSpace S]

/-- `α` fixes `bd(Σ)`, and it moves each path with ends on `bd(Σ)` to a homotopic path. -/
def IsMove (α : S ≃ₜ S) : Prop :=
  (∀ x ∈ bd S, α x = x) ∧ ∀ a ∈ bd S, ∀ b ∈ bd S, ∀ p q : Path a b, (∀ u, q u = α (p u))
    → p.Homotopic q

theorem IsMove.refl : IsMove (Homeomorph.refl S) :=
  ⟨fun _ _ => rfl, fun a _ b _ p q h => by
    have : p = q := by
      ext u
      exact (h u).symm
    rw [this]⟩

theorem IsMove.trans {α β : S ≃ₜ S} (hα : IsMove α) (hβ : IsMove β) : IsMove (α.trans β) := by
  refine ⟨fun x hx => by simp [hα.1 x hx, hβ.1 x hx], fun a ha b hb p q h => ?_⟩
  have h0 : α (p 0) = a := by rw [p.source, hα.1 a ha]
  have h1 : α (p 1) = b := by rw [p.target, hα.1 b hb]
  let r : Path a b := ⟨⟨fun u => α (p u), by fun_prop⟩, h0, h1⟩
  exact (hα.2 a ha b hb p r fun _ => rfl).trans (hβ.2 a ha b hb r q fun u => by simpa [r] using h u)

theorem IsMove.symm {α : S ≃ₜ S} (hα : IsMove α) : IsMove α.symm := by
  have hfix : ∀ x ∈ bd S, α.symm x = x := fun x hx => by
    rw [Homeomorph.symm_apply_eq, hα.1 x hx]
  refine ⟨hfix, fun a ha b hb p q h => ?_⟩
  refine (hα.2 a ha b hb q p fun u => ?_).symm
  rw [h u, Homeomorph.apply_symm_apply]

/-- **A homeomorphism in a convex chart is a move.** The straight line homotopy in the chart stays
fixed on the frontier of the chart, because `α` is the identity outside it. -/
theorem isHomotopic_of_chart [T2Space S] {K : ℂ → S} {Z : Set ℂ} (hZ : IsCompact Z)
  (hconv : Convex ℝ Z) (hc : ContinuousOn K Z) (hi : InjOn K Z) {α : S ≃ₜ S}
    (hout : ∀ x ∉ K '' Z, α x = x) (hin : ∀ x ∈ K '' Z, α x ∈ K '' Z)
    {a b : S} (p q : Path a b) (hq : ∀ u, q u = α (p u)) : p.Homotopic q := by
  classical
  have hcom : CompactSpace Z := isCompact_iff_compactSpace.mp hZ
  let e0 : Z → K '' Z := fun z => ⟨K z.1, mem_image_of_mem K z.2⟩
  have he0c : Continuous e0 := (hc.domRestrict).subtype_mk _
  have he0b : Function.Bijective e0 := ⟨fun x y h => Subtype.ext (hi x.2 y.2
    (congrArg Subtype.val h)), fun ⟨w, z, hz, hw⟩ => ⟨⟨z, hz⟩, Subtype.ext hw⟩⟩
  let e : Z ≃ₜ K '' Z := (Equiv.ofBijective e0 he0b).toHomeomorphOfIsInducing
    (he0c.isClosedEmbedding he0b.1).isInducing
  let ρ : S → ℂ := fun x => if h : x ∈ K '' Z then (e.symm ⟨x, h⟩).1 else 0
  have hρc : ContinuousOn ρ (K '' Z) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (K '' Z).domRestrict ρ = fun x => (e.symm x).1 := by
      ext z
      change ρ z.1 = (e.symm z).1
      exact dite_eq_left z.2
    rw [this]
    fun_prop
  have hρZ : ∀ x ∈ K '' Z, ρ x ∈ Z := fun x hx => by
    simp only [ρ, dite_eq_left hx]
    exact (e.symm ⟨x, hx⟩).2
  have hKρ : ∀ x ∈ K '' Z, K (ρ x) = x := fun x hx => by
    simp only [ρ, dite_eq_left hx]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
  have hZc : IsClosed (K '' Z) := (hZ.image_of_continuousOn hc).isClosed
  let line : unitInterval → ℂ → ℂ → ℂ := fun t z w => (1 - t.1 : ℝ) • z + (t.1 : ℝ) • w
  have hline : ∀ t, ∀ z ∈ Z, ∀ w ∈ Z, line t z w ∈ Z := fun t z hz w hw =>
    hconv hz hw (by linarith [t.2.2]) t.2.1 (by ring)
  let F : unitInterval × unitInterval → S := fun w => if p w.2 ∈ K '' Z then K (line w.1 (ρ
    (p w.2)) (ρ (α (p w.2)))) else p w.2
  let A : Set unitInterval := p ⁻¹' (K '' Z)
  have hAc : IsClosed A := hZc.preimage p.continuous
  have hfix : ∀ u ∈ closure Aᶜ, α (p u) = p u := fun u hu => by
    have hcl : IsClosed {u | α (p u) = p u} := isClosed_eq (by fun_prop) (by fun_prop)
    exact hcl.closure_subset_iff.mpr (fun v hv => hout _ hv) hu
  have hF1 : ContinuousOn F (univ ×ˢ A) := by
    have h1 : ContinuousOn (fun w : unitInterval × unitInterval => ρ (p w.2)) (univ ×ˢ A) :=
      hρc.comp (p.continuous.comp continuous_snd).continuousOn fun w hw => hw.2
    have h2 : ContinuousOn (fun w : unitInterval × unitInterval => ρ (α (p w.2))) (univ ×ˢ A) :=
      hρc.comp (by fun_prop) fun w hw => hin _ hw.2
    have h3 : ContinuousOn (fun w : unitInterval × unitInterval => line w.1 (ρ (p w.2)) (ρ (α
      (p w.2)))) (univ ×ˢ A) := by
      simp only [line]
      exact (((by fun_prop : Continuous fun w : unitInterval × unitInterval =>
        (1 - w.1.1 : ℝ)).continuousOn).smul h1).add ((by fun_prop : Continuous fun w : unitInterval
          × unitInterval => (w.1.1 : ℝ)).continuousOn.smul h2)
    refine (hc.comp h3 fun w hw => hline _ _ (hρZ _ hw.2) _ (hρZ _ (hin _ hw.2))).congr fun w hw
      => ?_
    exact ite_eq_left hw.2
  have hF2 : ContinuousOn F (univ ×ˢ closure Aᶜ) := by
    refine (p.continuous.comp continuous_snd).continuousOn.congr fun w hw => ?_
    change F w = p w.2
    simp only [F]
    split_ifs with h
    · rw [hfix _ hw.2]
      have : line w.1 (ρ (p w.2)) (ρ (p w.2)) = ρ (p w.2) := by
        simp only [line, ← add_smul]
        simp
      rw [this, hKρ _ h]
    · rfl
  have hcov : (univ ×ˢ A) ∪ (univ ×ˢ closure Aᶜ) = (univ : Set (unitInterval × unitInterval)) := by
    ext w
    simp only [mem_union, mem_prod, mem_univ, true_and, iff_true]
    by_cases h : w.2 ∈ A
    · exact .inl h
    · exact .inr (subset_closure h)
  have hF : Continuous F := by
    rw [← continuousOn_univ, ← hcov]
    exact hF1.union_of_isClosed hF2 (isClosed_univ.prod hAc) (isClosed_univ.prod isClosed_closure)
  have hF0 : ∀ u, F (0, u) = p u := fun u => by
    simp only [F]
    split_ifs with h
    · simp [line, hKρ _ h]
    · rfl
  have hF3 : ∀ u, F (1, u) = q u := fun u => by
    simp only [F, hq]
    split_ifs with h
    · simp [line, hKρ _ (hin _ h)]
    · exact (hout _ h).symm
  have hend : ∀ u, q u = p u → ∀ t, F (t, u) = p u := fun u h t => by
    have h' : α (p u) = p u := by rw [← hq, h]
    simp only [F]
    split_ifs with hm
    · rw [h']
      have : line t (ρ (p u)) (ρ (p u)) = ρ (p u) := by
        simp only [line, ← add_smul]
        simp
      rw [this, hKρ _ hm]
    · rfl
  refine ⟨⟨⟨⟨F, hF⟩, hF0, hF3⟩, fun t x hx => ?_⟩⟩
  rcases hx with rfl | hx
  · exact hend 0 (by simp) t
  · obtain rfl : x = 1 := hx
    exact hend 1 (by simp) t

theorem isMove_of_chart [T2Space S] {K : ℂ → S} {Z : Set ℂ} (hZ : IsCompact Z) (hconv : Convex ℝ Z)
  (hc : ContinuousOn K Z) (hi : InjOn K Z) {α : S ≃ₜ S} (hout : ∀ x ∉ K '' Z, α x = x)
    (hin : ∀ x ∈ K '' Z, α x ∈ K '' Z)
    (hbd : ∀ x ∈ bd S, x ∉ K '' Z) : IsMove α :=
  ⟨fun x hx => hout x (hbd x hx), fun _ _ _ _ p q h => isHomotopic_of_chart hZ hconv hc hi hout hin
    p q h⟩

/-- **The image of a forest under a move is homotopic to it.** -/
theorem forestsHomotopic_of_move [T2Space S] {α : S ≃ₜ S} (hα : IsMove α) {H : Drawing S}
  (hH : IsSurfaceForest H) : ForestsHomotopic (mapDrawingHomeo α H) H := by
  have hF := hH.map_homeo α
  have hfix : ∀ x ∈ bd S, α.symm x = x := (hα.symm).1
  have hbd : (mapDrawingHomeo α H).V ∩ bd S = H.V ∩ bd S := by
    ext z
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, hz⟩
      have : v = α v := by
        conv_lhs => rw [← α.symm_apply_apply v]
        exact hfix _ hz
      exact ⟨this ▸ hv, hz⟩
    · rintro ⟨hz, hb⟩
      exact ⟨⟨z, hz, hα.1 z hb⟩, hb⟩
  refine ⟨hF.1, hH.1, hF.2, hH.2, hbd, fun s hs t ht _ => ?_⟩
  have hsb := hs.2
  have htb := ht.2
  have hps : α.symm s = s := hfix s hsb
  have hpt : α.symm t = t := hfix t htb
  refine ⟨⟨fun ⟨P, hP⟩ => pullback_simple_walk_aux α hps hpt P hP, fun ⟨P, hP⟩ => ?_⟩,
    fun P₁ P₂ φ₁ φ₂ _ _ h₁ h₂ => ?_⟩
  · have key : ∀ {x y : S}, x = s → y = t → ∀ Q : GraphWalk (mapDrawingHomeo α H).toGraph x y,
      Q.IsSimple → ∃ Q' : GraphWalk (mapDrawingHomeo α H).toGraph s t, Q'.IsSimple := by
      rintro _ _ rfl rfl Q hQ
      exact ⟨Q, hQ⟩
    exact key (hα.1 s hsb) (hα.1 t htb) (mapWalkHomeo α P) (isSimple_mapWalkHomeo α hP)
  · obtain ⟨g0, g1⟩ := h₁.endpoints
    obtain ⟨c0, c1⟩ := h₂.endpoints
    have hbs : α s = s := hα.1 s hsb
    have hbt : α t = t := hα.1 t htb
    let p₁ : Path s t := ⟨φ₁, g0, g1⟩
    let p₂ : Path s t := ⟨φ₂, c0, c1⟩
    let p₃ : Path s t := ⟨⟨fun u => α (φ₂ u), by fun_prop⟩, by simp [c0, hbs], by simp [c1, hbt]⟩
    have h13 : p₁.Homotopic p₃ := IsFlat.flat (isFlat_forest hF.2) p₁ p₃ (fun u
      => h₁.range_subset_U ⟨u, rfl⟩) fun u => mem_image_of_mem α (h₂.range_subset_U ⟨u, rfl⟩)
    have h23 : p₂.Homotopic p₃ := hα.2 s hsb t htb p₂ p₃ fun _ => rfl
    exact curves_of_homotopic (h13.trans h23.symm)

/-- A point of a thin rectangle round a real interval is close to the interval. -/
theorem mem_cthickening_seg {s t ε : ℝ} (hst : s ≤ t) {w : ℂ} (h1 : s ≤ w.re) (h2 : w.re ≤ t + ε)
  (h3 : |w.im| ≤ ε) : w ∈ cthickening (2 * ε) ((fun u : ℝ => (u : ℂ)) '' Icc s t) := by
  refine mem_cthickening_of_dist_le w (((min w.re t : ℝ) : ℂ)) _ _ ⟨_, ⟨le_min h1 hst,
    min_le_right _ _⟩, rfl⟩ ?_
  have h4 : |w.re - min w.re t| ≤ ε := by
    have hε : 0 ≤ ε := (abs_nonneg _).trans h3
    rw [abs_le]
    constructor
    · have : min w.re t ≤ w.re := min_le_left _ _
      linarith
    · rcases le_total w.re t with h | h
      · rw [min_eq_left h]
        linarith
      · rw [min_eq_right h]
        linarith
  have h5 : dist w ((min w.re t : ℝ) : ℂ) ≤ |w.re - min w.re t| + |w.im| := by
    rw [dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans_eq ?_
    simp
  linarith

/-- **Shrinking an arc towards an end.** Let `A` be an arc off `bd(Σ)` that misses a closed set `Z`,
except perhaps at `A 0`, and let `N` be an open set around `A 0`. Then a move carries `A` into `N`,
and each point of `Z` stays where it is or moves inside `N`. The move is the slide `exists_slide` in
a thin rectangle round `A`, which moves points only to the left, towards `A 0`. -/
theorem exists_line_slide (hS : IsSurface S) {A : unitInterval → S} (hA : IsArcMap A)
  (hoff : ∀ t, A t ∉ bd S) {Z : Set S} (hZ : IsClosed Z) (hZA : ∀ t, t ≠ 0 → A t ∉ Z) {N : Set S}
    (hN : IsOpen N) (h0 : A 0 ∈ N) :
    ∃ α : S ≃ₜ S, IsMove α ∧ (∀ z ∈ Z, α z = z ∨ (z ∈ N ∧ α z ∈ N)) ∧ ∀ t, α (A t) ∈ N := by
  classical
  have ht2S : T2Space S := hS.2.1
  have hcS : CompactSpace S := hS.1
  obtain ⟨T, tT, j, Kc, hT, hj, hKc, hu, hi', -⟩ := exists_capAll S hS
  have ht2 : T2Space T := hT.2.1
  have hcT : CompactSpace T := hT.1
  have hA' : IsArcMap (j ∘ A) := ⟨hj.continuous.comp hA.1, hj.injective.comp hA.2⟩
  obtain ⟨O, K, θ, hK, hθc, hθm, hθ⟩ := exists_stripChart_of_arc hT hA'
  have ham : θ 0 < θ 1 := hθm zero_lt_one
  set a := θ 0 with ha
  set m := θ 1 with hm
  have hseg : ∀ u ∈ Icc a m, ∃ t, θ t = u := fun u hu => by
    obtain ⟨t, -, ht⟩ := intermediate_value_Icc (zero_le_one' unitInterval) hθc.continuousOn hu
    exact ⟨t, ht⟩
  have hKA : ∀ t, K (θ t) = j (A t) := fun t => (hθ t).2
  have hoffC : ∀ t, j (A t) ∉ Kc := fun t h => by
    obtain ⟨y, hy, hyj⟩ : j (A t) ∈ j '' bd S := by
      rw [← hi']
      exact ⟨mem_range_self _, h⟩
    exact hoff t (hj.injective hyj ▸ hy)
  -- Three open sets in the chart.
  let C : Set T := Kc ∪ j '' Z
  have hCc : IsClosed C := hKc.union (hj.isClosedMap _ hZ)
  obtain ⟨N', hN', hNe⟩ := hj.isInducing.isOpen_iff.mp hN
  let W₀ : Set ℂ := O ∩ K ⁻¹' Kcᶜ
  let W₂ : Set ℂ := O ∩ K ⁻¹' Cᶜ
  let W₃ : Set ℂ := O ∩ K ⁻¹' N'
  have hW₀ : IsOpen W₀ := hK.hc.isOpen_inter_preimage hK.isOpen hKc.isOpen_compl
  have hW₂ : IsOpen W₂ := hK.hc.isOpen_inter_preimage hK.isOpen hCc.isOpen_compl
  have hW₃ : IsOpen W₃ := hK.hc.isOpen_inter_preimage hK.isOpen hN'
  have ha₃ : (a : ℂ) ∈ W₃ := by
    refine ⟨(hθ 0).1, ?_⟩
    change K (θ 0) ∈ N'
    rw [hKA]
    exact (hNe ▸ h0 : A 0 ∈ j ⁻¹' N')
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW₃ _ ha₃
  let x₁ := min (a + r / 2) ((a + m) / 2)
  have hx₁a : a < x₁ := lt_min (by linarith) (by linarith)
  have hx₁m : x₁ < m := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hx₁r : x₁ ≤ a + r / 2 := min_le_left _ _
  have hsc : ∀ s, IsCompact ((fun u : ℝ => (u : ℂ)) '' Icc s m) := fun s => isCompact_Icc.image
    (by fun_prop)
  have hs₀ : ((fun u : ℝ => (u : ℂ)) '' Icc a m) ⊆ W₀ := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨t, rfl⟩ := hseg u hu
    refine ⟨(hθ t).1, ?_⟩
    change K (θ t) ∉ Kc
    rw [hKA]
    exact hoffC t
  have hs₂ : ((fun u : ℝ => (u : ℂ)) '' Icc x₁ m) ⊆ W₂ := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨t, rfl⟩ := hseg u ⟨hx₁a.le.trans hu.1, hu.2⟩
    have ht0 : t ≠ 0 := fun h => by
      have : θ t = a := by rw [h]
      linarith [hu.1]
    refine ⟨(hθ t).1, ?_⟩
    change K (θ t) ∉ C
    rw [hKA]
    rintro (h | ⟨z, hz, he⟩)
    · exact hoffC t h
    · exact hZA t ht0 (hj.injective he ▸ hz)
  obtain ⟨δ₀, hδ₀, hsub₀⟩ := (hsc a).exists_cthickening_subset_open hW₀ hs₀
  obtain ⟨δ₂, hδ₂, hsub₂⟩ := (hsc x₁).exists_cthickening_subset_open hW₂ hs₂
  set ε := min (min δ₀ δ₂) r / 4 with hε
  have hεp : 0 < ε := by
    have : 0 < min (min δ₀ δ₂) r := lt_min (lt_min hδ₀ hδ₂) hr
    positivity
  have hε1 : 2 * ε ≤ δ₀ := by
    have : min (min δ₀ δ₂) r ≤ δ₀ := (min_le_left _ _).trans (min_le_left _ _)
    have h0 : 0 < min (min δ₀ δ₂) r := lt_min (lt_min hδ₀ hδ₂) hr
    rw [hε]
    linarith
  have hε2 : 2 * ε ≤ δ₂ := by
    have : min (min δ₀ δ₂) r ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
    have h0 : 0 < min (min δ₀ δ₂) r := lt_min (lt_min hδ₀ hδ₂) hr
    rw [hε]
    linarith
  have hε3 : 4 * ε ≤ r := by
    have : min (min δ₀ δ₂) r ≤ r := min_le_right _ _
    rw [hε]
    linarith
  set b := m + ε with hb
  have hmb : m < b := by linarith
  have hab : a < b := by linarith
  let R : Set ℂ := Icc a b ×ℂ Icc (-ε) ε
  have hRW : R ⊆ W₀ := fun w hw => hsub₀ (cthickening_mono hε1 _ (mem_cthickening_seg ham.le hw.1.1
    hw.1.2 (abs_le.mpr hw.2)))
  have hRW₂ : ∀ w ∈ R, x₁ ≤ w.re → w ∈ W₂ := fun w hw h => hsub₂ (cthickening_mono hε2 _
    (mem_cthickening_seg hx₁m.le h hw.1.2 (abs_le.mpr hw.2)))
  have hRN : ∀ w ∈ R, w.re ≤ x₁ → K w ∈ N' := fun w hw h => by
    refine (hball ?_).2
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 := Complex.norm_le_abs_re_add_abs_im (w - a)
    have h2 : |(w - (a : ℂ)).re| ≤ r / 2 := by
      have := hw.1.1
      simp only [Complex.sub_re, Complex.ofReal_re]
      rw [abs_of_nonneg (by linarith)]
      linarith
    have h3 : |(w - (a : ℂ)).im| ≤ ε := by
      simpa using abs_le.mpr hw.2
    linarith
  have hRO : R ⊆ O := fun w hw => (hRW hw).1
  let x := (a + x₁) / 2
  have hxa : a < x := by simp only [x]; linarith
  have hxx₁ : x < x₁ := by simp only [x]; linarith
  obtain ⟨ψ, hψc, hψm, hψa, hψb, hψx, hψle⟩ := exists_slide_fun hxa (hxx₁.trans hx₁m) hmb
  obtain ⟨e, he1, he2, he3⟩ := exists_slide hK hab hεp hRO hψc hψm hψa hψb hψle
  have hRr : ∀ w ∈ R, K w ∈ range j := fun w hw => by
    have h1 : K w ∉ Kc := (hRW hw).2
    rcases hu.symm ▸ mem_univ (K w) with h | h
    · exact h
    · exact (h1 h).elim
  have hinv : ∀ z, z ∈ range j ↔ e z ∈ range j := fun z => by
    by_cases hz : z ∈ K '' R
    · obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨w', hw', -, -, he⟩ := he3 w hw
      rw [he]
      exact ⟨fun _ => hRr w' hw', fun _ => hRr w hw⟩
    · rw [he1 z hz]
  let hjh := hj.isEmbedding.toHomeomorph
  let α : S ≃ₜ S := hjh.trans ((e.subtype hinv).trans hjh.symm)
  have hα : ∀ s, j (α s) = e (j s) := fun s => by
    have h1 : hjh (α s) = (e.subtype hinv) (hjh s) := by
      simp only [α, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
    exact congrArg Subtype.val h1
  have hne : Nonempty S := ⟨A 0⟩
  let κ : T → S := Function.invFun j
  have hκ : ∀ s, κ (j s) = s := Function.leftInverse_invFun hj.injective
  have hjκ : ∀ w ∈ R, j (κ (K w)) = K w := fun w hw => by
    obtain ⟨s, hs⟩ := hRr w hw
    rw [← hs, hκ]
  let K' : ℂ → S := fun w => κ (K w)
  have hRc : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  have hRconv : Convex ℝ R := ((convex_Icc a b).linear_preimage Complex.reLm).inter ((convex_Icc
    (-ε) ε).linear_preimage Complex.imLm)
  have hK'c : ContinuousOn K' R := by
    rw [hj.isInducing.continuousOn_iff]
    exact (hK.hc.mono hRO).congr fun w hw => hjκ w hw
  have hK'i : InjOn K' R := fun w hw w' hw' h => hK.hi (hRO hw) (hRO hw')
    (by
      rw [← hjκ w hw, ← hjκ w' hw']
      exact congrArg j h)
  have hmemR : ∀ s, s ∈ K' '' R ↔ j s ∈ K '' R := fun s => by
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, (hjκ w hw).symm⟩
    · rintro ⟨w, hw, h⟩
      exact ⟨w, hw, by simp only [K', h, hκ]⟩
  have hout : ∀ s ∉ K' '' R, α s = s := fun s hs => hj.injective (by
    rw [hα, he1 _ fun h => hs ((hmemR s).mpr h)])
  have hin : ∀ s ∈ K' '' R, α s ∈ K' '' R := fun s hs => by
    rw [hmemR] at hs ⊢
    obtain ⟨w, hw, h⟩ := hs
    obtain ⟨w', hw', -, -, he⟩ := he3 w hw
    rw [hα, ← h, he]
    exact mem_image_of_mem K hw'
  have hbd : ∀ s ∈ bd S, s ∉ K' '' R := fun s hs h => by
    obtain ⟨w, hw, hj'⟩ := (hmemR s).mp h
    have hk : j s ∈ Kc := by
      have : j s ∈ range j ∩ Kc := by rw [hi']; exact mem_image_of_mem j hs
      exact this.2
    exact (hRW hw).2 (hj' ▸ hk)
  have hNj : ∀ s, j s ∈ N' ↔ s ∈ N := fun s => by
    rw [← hNe]
    rfl
  refine ⟨α, isMove_of_chart hRc hRconv hK'c hK'i hout hin hbd, fun z hz => ?_, fun t => ?_⟩
  · by_cases hzR : z ∈ K' '' R
    · obtain ⟨w, hw, hj'⟩ := (hmemR z).mp hzR
      have hre : w.re ≤ x₁ := by
        by_contra hc
        exact (hRW₂ w hw (not_le.mp hc).le).2 (.inr ⟨z, hz, hj'.symm⟩)
      obtain ⟨w', hw', hle, -, he⟩ := he3 w hw
      refine .inr ⟨(hNj z).mp (hj' ▸ hRN w hw hre), (hNj _).mp ?_⟩
      rw [hα, ← hj', he]
      exact hRN w' hw' (hle.trans hre)
    · exact .inl (hout z hzR)
  · have h1 : θ t ∈ Icc a b := ⟨hθm.monotone (show (0 : unitInterval) ≤ t from t.2.1),
      (hθm.monotone (show t ≤ 1 from t.2.2)).trans hmb.le⟩
    have h2 : j (α (A t)) = K ((ψ (θ t) : ℝ) : ℂ) := by
      rw [hα, ← hKA, he2 _ h1]
    have h3 : ψ (θ t) ∈ Icc a x := by
      constructor
      · rw [← hψa]
        exact hψm.monotone h1.1
      · rw [← hψx]
        exact hψm.monotone (hθm.monotone (show t ≤ 1 from t.2.2))
    refine (hNj _).mp ?_
    rw [h2]
    refine hRN _ ⟨⟨?_, ?_⟩, ?_⟩ ?_
    · simpa using h3.1
    · simp only [Complex.ofReal_re]
      linarith [h3.2, hxx₁, hx₁m]
    · simp [hεp.le]
    · simp only [Complex.ofReal_re]
      linarith [h3.2]

end GraphMinor.GM07
