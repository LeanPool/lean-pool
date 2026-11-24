/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FragmentShape
import LeanPool.GraphMinor.GM19.Section6Cuff

/-!
# A chord that passes along an inner disc

Let `D₀` lie inside the closed disc `D₁`. A straight line of a chart of `D₁` through a point inside
`D₀` leaves `D₀` for the last time at
two boundary points of `D₀`. The two outer pieces of this line and one arc of the boundary of `D₀`
form a chord of `D₁`. So `D₁` has a
closed subdisc `Δ` that holds `D₀`, shares an arc of its boundary with `D₀`, and shares an arc of
its boundary with `D₁`
(`exists_nested_chord`). This links the direction of the boundary of `D₀` to the direction of the
boundary of `D₁`, in the proof of
`FragmentOrientationStatement`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric Filter GraphMinor.Surface

/-- `U` has three distinct points. -/
def HasTriple {X : Type*} (U : Set X) : Prop :=
  ∃ a b c, a ∈ U ∧ b ∈ U ∧ c ∈ U ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c

theorem HasTriple.of_infinite {X : Type*} {U : Set X} (h : U.Infinite) : HasTriple U := by
  classical
  obtain ⟨s, hs, hc⟩ := h.exists_subset_card_eq 3
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hc
  exact ⟨a, b, c, hs (by simp), hs (by simp), hs (by simp), hab, hbc, hac⟩

theorem HasTriple.mono {X : Type*} {U V : Set X} (h : HasTriple U) (hs : U ⊆ V) : HasTriple V := by
  obtain ⟨a, b, c, ha, hb, hc, h1, h2, h3⟩ := h
  exact ⟨a, b, c, hs ha, hs hb, hs hc, h1, h2, h3⟩

theorem HasTriple.image {X Y : Type*} {U : Set X} (h : HasTriple U) {f : X → Y}
  (hf : InjOn f U) : HasTriple (f '' U) := by
  obtain ⟨a, b, c, ha, hb, hc, h1, h2, h3⟩ := h
  exact ⟨f a, f b, f c, mem_image_of_mem _ ha, mem_image_of_mem _ hb, mem_image_of_mem _ hc,
    fun e ↦ h1 (hf ha hb e),
    fun e ↦ h2 (hf hb hc e), fun e ↦ h3 (hf ha hc e)⟩

theorem hasTriple_of_line {X : Type} [TopologicalSpace X] [T1Space X] {L : Set X} {a b : X}
  (hl : IsLineWithEnds L a b) : HasTriple L :=
  HasTriple.of_infinite ((isPreconnected_of_line hl).infinite_of_nontrivial
    ⟨a, (ends_of_line hl).1, b, (ends_of_line hl).2.1, (ends_of_line hl).2.2⟩)

theorem isManifoldPoint_complex (x : ℂ) : IsManifoldPoint x := by
  obtain ⟨e⟩ := exists_homeomorph_ball x one_pos
  have : IsInteriorPoint x := ⟨ball x 1, isOpen_ball, mem_ball_self one_pos, ⟨e⟩⟩
  exact this.isManifoldPoint

/-- A ray from a point inside a closed disc of the plane leaves the disc for the last time at a
boundary point. -/
theorem exists_last_point {K : Set ℂ} (hK : IsClosedDisc K) {c : ℂ} (hc : c ∈ discInt K) {u : ℂ}
  (hu : ‖u‖ = 1) :
    ∃ t : ℝ, 0 < t ∧ c + t * u ∈ discBd K ∧ ∀ t' : ℝ, t < t' → c + t' * u ∉ K := by
  have hop : IsOpen (discInt K) := hK.isOpen_discInt isManifoldPoint_complex
  have hcpt : IsCompact K := by
    obtain ⟨e⟩ := hK
    have : K = range fun z ↦ (e z).1 := by
      ext x
      constructor
      · intro hx
        exact ⟨e.symm ⟨x, hx⟩, by simp⟩
      · rintro ⟨z, rfl⟩
        exact (e z).2
    rw [this]
    have : CompactSpace ClosedUnitDisc := isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
    exact isCompact_range (continuous_subtype_val.comp e.continuous)
  let p : ℝ → ℂ := fun t ↦ c + t * u
  have hp : Continuous p := by fun_prop
  obtain ⟨R, hR⟩ := hcpt.isBounded.subset_closedBall 0
  have hbound : ∀ t : ℝ, 0 ≤ t → p t ∈ K → t ≤ R + ‖c‖ := by
    intro t ht hk
    have h1 : ‖p t‖ ≤ R := by simpa using hR hk
    have h2 : ‖(t : ℂ) * u‖ = t := by simp [hu, abs_of_nonneg ht]
    have h3 : ‖(t : ℂ) * u‖ ≤ ‖p t‖ + ‖c‖ := by
      have : (t : ℂ) * u = p t - c := by simp [p]
      rw [this]
      exact norm_sub_le _ _
    linarith
  have hset : IsCompact (Icc 0 (R + ‖c‖) ∩ p ⁻¹' K) := isCompact_Icc.inter_right
    (hcpt.isClosed.preimage hp)
  have hne : (Icc 0 (R + ‖c‖) ∩ p ⁻¹' K).Nonempty := by
    have h0 : p 0 ∈ K := by
      simpa [p] using discInt_subset K hc
    exact ⟨0, ⟨le_rfl, hbound 0 le_rfl h0⟩, h0⟩
  obtain ⟨t, ⟨⟨ht0, -⟩, htK⟩, hmax⟩ := hset.exists_isGreatest hne
  have hlast : ∀ t' : ℝ, t < t' → p t' ∉ K := fun t' hlt hk ↦ by
    have h0 : 0 ≤ t' := ht0.trans hlt.le
    exact absurd (hmax ⟨⟨h0, hbound t' h0 hk⟩, hk⟩) (not_le.2 hlt)
  have hint : ∀ {s : ℝ}, p s ∈ discInt K → ∃ s', s < s' ∧ p s' ∈ K := by
    intro s hs
    have : ∀ᶠ r in 𝓝[>] s, p r ∈ discInt K :=
      (hp.continuousAt.eventually (hop.mem_nhds hs)).filter_mono nhdsWithin_le_nhds
    obtain ⟨r, hr, hr'⟩ := (this.and self_mem_nhdsWithin).exists
    exact ⟨r, hr', discInt_subset K hr⟩
  have htpos : 0 < t := by
    obtain ⟨s', hs', hk⟩ := hint (s := 0) (by simpa [p] using hc)
    exact hs'.trans_le (hmax ⟨⟨hs'.le, hbound s' hs'.le hk⟩, hk⟩)
  refine ⟨t, htpos, ?_, hlast⟩
  by_contra hn
  obtain ⟨s', hs', hk⟩ := hint (s := t) ⟨htK, hn⟩
  exact hlast s' hs' hk

/-- A ray from a point of the open unit ball reaches the unit circle, and it stays in the open ball
up to then. -/
theorem exists_exit {y : ℂ} (hy : ‖y‖ < 1) {u : ℂ} (hu : ‖u‖ = 1) :
    ∃ r : ℝ, 0 < r ∧ ‖y + r * u‖ = 1 ∧ ∀ t : ℝ, 0 ≤ t → t < r → ‖y + t * u‖ < 1 := by
  let f : ℝ → ℝ := fun t ↦ ‖y + t * u‖
  have hf : Continuous f := by fun_prop
  have h2 : 1 ≤ f 2 := by
    have h3 : ‖(2 : ℂ) * u‖ = 2 := by simp [hu]
    have h4 : ‖(2 : ℂ) * u‖ ≤ f 2 + ‖y‖ := by
      have : (2 : ℂ) * u = (y + ((2 : ℝ) : ℂ) * u) - y := by simp
      rw [this]
      exact norm_sub_le _ _
    linarith
  have hset : IsCompact (Icc 0 2 ∩ f ⁻¹' Ici 1) := isCompact_Icc.inter_right
    (isClosed_Ici.preimage hf)
  obtain ⟨r, ⟨⟨hr0, -⟩, hr1⟩, hmin⟩ := hset.exists_isLeast ⟨2, ⟨by norm_num, le_rfl⟩, h2⟩
  have hf0 : f 0 < 1 := by simpa [f] using hy
  have hr2 : r ≤ 2 := hmin ⟨⟨by norm_num, le_rfl⟩, h2⟩
  have hlt : ∀ t : ℝ, 0 ≤ t → t < r → f t < 1 := fun t h0 ht ↦ by
    by_contra hn
    have h3 : r ≤ t := hmin ⟨⟨h0, ht.le.trans hr2⟩, not_lt.1 hn⟩
    linarith
  have hrpos : 0 < r := by
    rcases hr0.eq_or_lt with h | h
    · rw [← h] at hr1
      exact absurd (mem_Ici.1 hr1) (not_le.2 hf0)
    · exact h
  have heq : f r = 1 := by
    apply le_antisymm _ hr1
    have hcl : ∀ᶠ t in 𝓝[<] r, f t ≤ 1 := by
      filter_upwards [Ioo_mem_nhdsLT hrpos] with t ht
      exact (hlt t ht.1.le ht.2).le
    exact le_of_tendsto (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hcl
  exact ⟨r, hrpos, heq, hlt⟩

/-- A closed disc in the open unit ball of the plane, and a closed subdisc of the unit disc that
holds it and shares with it and with
the unit disc arcs of the boundary. -/
theorem exists_chord_plane {K : Set ℂ} (hK : IsClosedDisc K) (hin : K ⊆ ball 0 1) :
    ∃ Δ : Set ℂ, IsClosedDisc Δ ∧ K ⊆ Δ ∧ Δ ⊆ closedBall 0 1 ∧ HasTriple (discBd K ∩ discBd Δ) ∧
      HasTriple (discBd Δ ∩ sphere 0 1) := by
  classical
  obtain ⟨c, hc⟩ := hK.nonempty_discInt
  have hnorm : ∀ {x}, x ∈ K → ‖x‖ < 1 := fun hx ↦ by simpa using hin hx
  let p : ℝ → ℂ := fun t ↦ c + t
  have hp : Continuous p := by fun_prop
  have hpi : Function.Injective p := fun s t h ↦ by
    have : (s : ℂ) = t := add_left_cancel h
    exact_mod_cast this
  obtain ⟨a, ha, hab, hall⟩ := exists_last_point hK hc (u := 1) (by simp)
  obtain ⟨b, hb, hbb, hbll⟩ := exists_last_point hK hc (u := -1) (by simp)
  have hpa : c + (a : ℂ) * 1 = p a := by simp [p]
  have hpb : ∀ t : ℝ, c + (t : ℂ) * (-1) = p (-t) := fun t ↦ by simp [p]
  rw [hpa] at hab
  rw [hpb] at hbb
  have hall' : ∀ t, a < t → p t ∉ K := fun t ht ↦ by
    have := hall t ht
    rwa [show c + (t : ℂ) * 1 = p t by simp [p]] at this
  have hbll' : ∀ t, t < -b → p t ∉ K := fun t ht ↦ by
    have := hbll (-t) (by linarith)
    rwa [hpb, neg_neg] at this
  obtain ⟨r, hr, hre, hrl⟩ := exists_exit (hnorm (Surface.discBd_subset _ hab)) (u := 1) (by simp)
  obtain ⟨r', hr', hre', hrl'⟩ := exists_exit (hnorm (Surface.discBd_subset _ hbb)) (u := -1)
    (by simp)
  have hshift : ∀ t : ℝ, p a + (t : ℂ) * 1 = p (a + t) := fun t ↦ by simp [p, add_assoc]
  have hshift' : ∀ t : ℝ, p (-b) + (t : ℂ) * (-1) = p (-b - t) := fun t ↦ by
    simp [p, add_assoc, sub_eq_add_neg]
  rw [hshift] at hre
  rw [hshift'] at hre'
  have hLa := GM11.isLine_of_injOn hp (show a < a + r by linarith) hpi.injOn
  have hLb := GM11.isLine_of_injOn hp (show -b - r' < -b by linarith) hpi.injOn
  have hne : p (-b) ≠ p a := fun h ↦ by
    have := hpi h
    linarith
  obtain ⟨J, J', hJ, hJ', hun, hinter⟩ := hK.isOArc_discBd.lines hbb hab hne
  have hJb : J ⊆ discBd K := fun x hx ↦ hun ▸ Or.inl hx
  have hJK : J ⊆ K := hJb.trans (Surface.discBd_subset K)
  set La := p '' Icc a (a + r) with hLp
  set Lb := p '' Icc (-b - r') (-b) with hLm
  have hma : ∀ {t}, t ∈ Icc a (a + r) → p t ∈ K → t = a := fun {t} ht hk ↦ by
    by_contra hn
    exact hall' t (lt_of_le_of_ne ht.1 (Ne.symm hn)) hk
  have hmb : ∀ {t}, t ∈ Icc (-b - r') (-b) → p t ∈ K → t = -b := fun {t} ht hk ↦ by
    by_contra hn
    exact hbll' t (lt_of_le_of_ne ht.2 hn) hk
  have haJ : p a ∈ J := (ends_of_line hJ).2.1
  have hbJ : p (-b) ∈ J := (ends_of_line hJ).1
  have h₁ : Lb ∩ J = {p (-b)} := by
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hx⟩
      rw [hmb ht (hJK hx)]
      rfl
    · rintro rfl
      exact ⟨⟨_, ⟨by linarith, le_rfl⟩, rfl⟩, hbJ⟩
  have hF₁ := hLb.union hJ h₁
  have h₂ : (Lb ∪ J) ∩ La = {p a} := by
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩ | hx, ⟨t', ht', he⟩⟩
      · have h3 := hpi he
        linarith [ht.2, ht'.1]
      · rw [← he] at hx ⊢
        rw [hma ht' (hJK hx)]
        rfl
    · rintro rfl
      exact ⟨Or.inr haJ, _, ⟨le_rfl, by linarith⟩, rfl⟩
  have hF := hF₁.union hLa h₂
  set F := Lb ∪ J ∪ La with hFdef
  set s₀ := p (-b - r') with hs₀
  set e₀ := p (a + r) with he₀
  have hse : s₀ ≠ e₀ := fun h ↦ by
    have := hpi h
    linarith
  have hballa : ∀ {t}, t ∈ Icc a (a + r) → t ≠ a + r → ‖p t‖ < 1 := fun {t} ht hn ↦ by
    have := hrl (t - a) (by linarith [ht.1]) (by
      have : t < a + r := lt_of_le_of_ne ht.2 hn
      linarith)
    rwa [hshift, show a + (t - a) = t by ring] at this
  have hballb : ∀ {t}, t ∈ Icc (-b - r') (-b) → t ≠ -b - r' → ‖p t‖ < 1 := fun {t} ht hn ↦ by
    have := hrl' (-b - t) (by linarith [ht.2]) (by
      have : -b - r' < t := lt_of_le_of_ne ht.1 (Ne.symm hn)
      linarith)
    rwa [hshift', show -b - (-b - t) = t by ring] at this
  have hFball : F ⊆ closedBall 0 1 := by
    rintro x ((⟨t, ht, rfl⟩ | hx) | ⟨t, ht, rfl⟩)
    · by_cases h : t = -b - r'
      · rw [h]
        exact mem_closedBall_zero_iff.2 hre'.le
      · exact mem_closedBall_zero_iff.2 (hballb ht h).le
    · exact ball_subset_closedBall (hin (hJK hx))
    · by_cases h : t = a + r
      · rw [h]
        exact mem_closedBall_zero_iff.2 hre.le
      · exact mem_closedBall_zero_iff.2 (hballa ht h).le
  have hbdb := isClosedDisc_closedBall.2
  have hmeet : F ∩ discBd (closedBall (0 : ℂ) 1) = {s₀, e₀} := by
    rw [hbdb]
    ext x
    constructor
    · rintro ⟨(⟨t, ht, rfl⟩ | hx) | ⟨t, ht, rfl⟩, hsp⟩
      · by_cases h : t = -b - r'
        · exact Or.inl (by rw [h])
        · exact absurd (mem_sphere_zero_iff_norm.1 hsp) (hballb ht h).ne
      · exact absurd (mem_sphere_zero_iff_norm.1 hsp) (hnorm (hJK hx)).ne
      · by_cases h : t = a + r
        · exact Or.inr (by rw [h]; rfl)
        · exact absurd (mem_sphere_zero_iff_norm.1 hsp) (hballa ht h).ne
    · rintro (rfl | h)
      · exact ⟨(ends_of_line hF).1, mem_sphere_zero_iff_norm.2 hre'⟩
      · rw [mem_singleton_iff.1 h]
        exact ⟨(ends_of_line hF).2.1, mem_sphere_zero_iff_norm.2 hre⟩
  obtain ⟨A₁, A₂, Δ₁, Δ₂, -, hcomp, hd₁, hd₂, hun', hint, hb₁, hb₂, hcomp'⟩ :=
    disc_iArc (closedBall (0 : ℂ) 1) F s₀ e₀ isClosedDisc_closedBall.1 hFball hse hF hmeet
  have hFcl : IsClosed F := isClosed_of_cuffLine hF
  have hJF : J ⊆ F := fun x hx ↦ Or.inl (Or.inr hx)
  have hfinish : ∀ {Δ A : Set ℂ}, IsClosedDisc Δ → discBd Δ = A ∪ F → A ∈ componentsIn (discBd
    (closedBall (0 : ℂ) 1) \ {s₀, e₀}) →
      Δ ⊆ closedBall 0 1 → K \ J ⊆ Δ → F ⊆ Δ → ∃ Δ : Set ℂ, IsClosedDisc Δ ∧ K ⊆ Δ
        ∧ Δ ⊆ closedBall 0 1 ∧
        HasTriple (discBd K ∩ discBd Δ) ∧ HasTriple (discBd Δ ∩ sphere 0 1) := by
    intro Δ A hd hb hA hsub hQ hFΔ
    refine ⟨Δ, hd, fun x hx ↦ ?_, hsub, ?_, ?_⟩
    · by_cases hxJ : x ∈ J
      · exact hFΔ (hJF hxJ)
      · exact hQ ⟨hx, hxJ⟩
    · exact (hasTriple_of_line hJ).mono fun x hx ↦ ⟨hJb hx, hb ▸ Or.inr (hJF hx)⟩
    · obtain ⟨x, hx, rfl⟩ := hA
      set A := connectedComponentIn (discBd (closedBall (0 : ℂ) 1) \ {s₀, e₀}) x with hAdef
      have hxA : x ∈ A := mem_connectedComponentIn hx
      have hAs : A ⊆ discBd (closedBall (0 : ℂ) 1) \ {s₀, e₀} := connectedComponentIn_subset _ _
      have hAF : ∀ {z}, z ∈ A → z ∉ F := fun {z} hz hzF ↦ (hAs hz).2 (hmeet ▸ ⟨hzF, (hAs hz).1⟩)
      have hnt : A.Nontrivial := by
        by_contra hn
        rw [not_nontrivial_iff] at hn
        have hsing : A = {x} := hn.eq_singleton_of_mem hxA
        have hx₂ : x ∈ discBd Δ := hb ▸ Or.inl hxA
        have hlim := mem_closure_oArc_sdiff hd.isOArc_discBd hx₂
        have hsubF : discBd Δ \ {x} ⊆ F := by
          rintro z ⟨hz, hne⟩
          rw [hb] at hz
          rcases hz with h | h
          · exact absurd (hsing ▸ h) hne
          · exact h
        exact hAF hxA (closure_minimal hsubF hFcl hlim)
      refine HasTriple.of_infinite ((isPreconnected_connectedComponentIn.infinite_of_nontrivial
        hnt).mono fun z hz ↦ ?_)
      refine ⟨hb ▸ Or.inl hz, ?_⟩
      rw [← hbdb]
      exact (hAs hz).1
  have hdisjQ : Disjoint (discInt K) J := disjoint_left.2 fun x hx hxJ ↦ hx.2 (hJb hxJ)
  have hQc : IsPreconnected (K \ J) := hK.isPreconnected_discInt.subset_closure
    (fun x hx ↦ ⟨discInt_subset K hx, disjoint_left.1 hdisjQ hx⟩) (sdiff_subset.trans
      hK.subset_closure_discInt)
  have hcQ : c ∈ K \ J := ⟨discInt_subset K hc, disjoint_left.1 hdisjQ hc⟩
  have hQsub : K \ J ⊆ closedBall (0 : ℂ) 1 \ F := by
    rintro x ⟨hx, hxJ⟩
    refine ⟨ball_subset_closedBall (hin hx), ?_⟩
    rintro ((⟨t, ht, rfl⟩ | h) | ⟨t, ht, rfl⟩)
    · apply hxJ
      rw [hmb ht hx]
      exact hbJ
    · exact hxJ h
    · apply hxJ
      rw [hma ht hx]
      exact haJ
  have hQC := hQc.subset_connectedComponentIn hcQ hQsub
  have hmemc : connectedComponentIn (closedBall (0 : ℂ) 1 \ F) c ∈ componentsIn (closedBall
    (0 : ℂ) 1 \ F) :=
    mem_image_of_mem _ (hQsub hcQ)
  rw [hcomp'] at hmemc
  have hFΔ₁ : F ⊆ Δ₁ := fun x hx ↦ (hint ▸ hx : x ∈ Δ₁ ∩ Δ₂).1
  have hFΔ₂ : F ⊆ Δ₂ := fun x hx ↦ (hint ▸ hx : x ∈ Δ₁ ∩ Δ₂).2
  rcases hmemc with h | h
  · refine hfinish hd₁ hb₁ (by rw [hcomp]; exact mem_insert _ _) (hun' ▸ subset_union_left) ?_ hFΔ₁
    rw [h] at hQC
    exact hQC.trans sdiff_subset
  · refine hfinish hd₂ hb₂ (by rw [hcomp]; exact mem_insert_of_mem _ rfl)
      (hun' ▸ subset_union_right) ?_ hFΔ₂
    rw [mem_singleton_iff.1 h] at hQC
    exact hQC.trans sdiff_subset

/-- A closed disc `D₀` inside a closed disc `D₁`. There is a closed disc `Δ` between them that
shares with each of them three points
of the boundary. -/
theorem exists_nested_chord {T : Type} [TopologicalSpace T] [T2Space T] {D₀ D₁ : Set T}
  (h₀ : IsClosedDisc D₀) (h₁ : IsClosedDisc D₁)
    (hin : D₀ ⊆ discInt D₁) : ∃ Δ : Set T, IsClosedDisc Δ ∧ D₀ ⊆ Δ ∧ Δ ⊆ D₁ ∧ HasTriple
      (discBd D₀ ∩ discBd Δ) ∧
      HasTriple (discBd Δ ∩ discBd D₁) := by
  obtain ⟨h, g, c⟩ := h₁.exists_isChart
  have hsub : D₀ ⊆ D₁ := hin.trans (discInt_subset D₁)
  have hinj : InjOn h D₁ := c.gh.injOn
  obtain ⟨hK, hbK⟩ := isClosedDisc_image_injOn h₀ (c.hc.mono hsub) (hinj.mono hsub)
  have hball : h '' D₀ ⊆ ball 0 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hcb : h x ∈ closedBall (0 : ℂ) 1 := c.hm (hsub hx)
    refine (mem_ball_zero_iff).2 (lt_of_le_of_ne (mem_closedBall_zero_iff.1 hcb) fun he ↦ ?_)
    have : h x ∈ h '' discBd D₁ := by
      rw [c.bd]
      exact mem_sphere_zero_iff_norm.2 he
    obtain ⟨y, hy, hxy⟩ := this
    have hxe : y = x := hinj (Surface.discBd_subset _ hy) (hsub hx) hxy
    exact (hin hx).2 (hxe ▸ hy)
  obtain ⟨Δ, hd, hKΔ, hΔ, ht₁, ht₂⟩ := exists_chord_plane hK hball
  have hginj : InjOn g (closedBall 0 1) := c.hg.injOn
  obtain ⟨hd', hb'⟩ := isClosedDisc_image_injOn hd (c.gc.mono hΔ) (hginj.mono hΔ)
  have hgh : ∀ {x}, x ∈ D₁ → g (h x) = x := fun hx ↦ c.gh hx
  have hD₀ : g '' (h '' D₀) = D₀ := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      rwa [hgh (hsub hy)]
    · intro hx
      exact ⟨_, mem_image_of_mem _ hx, hgh (hsub hx)⟩
  have hsph : g '' sphere 0 1 = discBd D₁ := by
    rw [← c.bd]
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      rwa [hgh (Surface.discBd_subset _ hy)]
    · intro hx
      exact ⟨_, mem_image_of_mem _ hx, hgh (Surface.discBd_subset _ hx)⟩
  have hcomm : ∀ {U V : Set ℂ}, U ⊆ closedBall 0 1 → V ⊆ closedBall 0 1 → g '' (U ∩ V)
    = g '' U ∩ g '' V :=
    fun hU hV ↦ hginj.image_inter hU hV
  have hD₀' : g '' (h '' discBd D₀) = discBd D₀ := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      rwa [hgh (hsub (Surface.discBd_subset _ hy))]
    · intro hx
      exact ⟨_, mem_image_of_mem _ hx, hgh (hsub (Surface.discBd_subset _ hx))⟩
  refine ⟨g '' Δ, hd', ?_, ?_, ?_, ?_⟩
  · rw [← hD₀]
    exact image_mono hKΔ
  · exact (image_mono hΔ).trans (image_subset_iff.2 fun x hx ↦ c.gm hx)
  · have hs₁ : discBd (h '' D₀) ⊆ closedBall 0 1 :=
      (Surface.discBd_subset _).trans (hball.trans ball_subset_closedBall)
    have hs₂ : discBd Δ ⊆ closedBall 0 1 := (Surface.discBd_subset _).trans hΔ
    have := ht₁.image (hginj.mono (inter_subset_left.trans hs₁))
    rw [hcomm hs₁ hs₂, hbK, hD₀', ← hb'] at this
    exact this
  · have hs₂ : discBd Δ ⊆ closedBall 0 1 := (Surface.discBd_subset _).trans hΔ
    have := ht₂.image (hginj.mono (inter_subset_left.trans hs₂))
    rw [hcomm hs₂ sphere_subset_closedBall, ← hb', hsph] at this
    exact this

end GraphMinor.GM19
