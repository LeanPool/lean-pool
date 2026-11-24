/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.DiscRegions
public import LeanPool.GraphMinor.GM11.EdgeChart
public import LeanPool.GraphMinor.Surface.Crossing

/-!
# Edge Charts and Arc Non-Separation on a Closed Disc Space

This file proves two topological tools for proper drawings on a closed disc space `S`
(`IsClosedDiscSpace S`), without requiring `IsClosedSurface S`:
1. `disc_exists_edge_chart`: around any point `γ t₀` of an edge `e ∈ H.E` of a proper drawing `H`
   on `S`, inside any open neighborhood `O` of `γ t₀`, there is an injective continuous chart
   `G : ℂ → S` on `closedBall (0 : ℂ) 1` mapping `0` to `γ t₀`, the real diameter into `e`, and the
   rest of `closedBall (0 : ℂ) 1` into `O \ (bd S ∪ H.U)`, such that `G '' ball (0 : ℂ) ρ` is open
   in `S` for every `0 < ρ ≤ 1`.
2. `disc_sdiff_arc_connectedComponentIn`: an arc `J` in `S` that meets a closed set `K` and `bd S`
   in at most a single point `v` does not separate any connected component of `(univ \ bd S) \ K`.
-/

public section

namespace GraphMinor.GM06

open Set Function Topology Metric unitInterval Complex GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-- CompactSpace instance for a closed disc space `S`. -/
theorem compactSpace_of_isClosedDiscSpace (hS : IsClosedDiscSpace S) : CompactSpace S := by
  have : CompactSpace ClosedUnitDisc :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : EuclideanPlane) 1)
  obtain ⟨φ⟩ := hS
  exact φ.compactSpace

/-- Global complex disc coordinates on a closed disc space `S`. -/
theorem exists_disc_complex_chart (hS : IsClosedDiscSpace S) :
    ∃ (h : S → ℂ) (g : ℂ → S),
      Continuous h ∧ Function.Injective h ∧ ContinuousOn g (closedBall 0 1) ∧
      (∀ x : S, h x ∈ closedBall (0 : ℂ) 1) ∧
      (∀ x : S, g (h x) = x) ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, h (g z) = z) ∧
      h '' bd S = sphere (0 : ℂ) 1 ∧
      (∀ x : S, x ∈ bd S ↔ ‖h x‖ = 1) ∧
      (∀ x : S, x ∉ bd S ↔ h x ∈ ball (0 : ℂ) 1) := by
  obtain ⟨h, g, hh, hg, hmaps, _, hleft, hright, hbd⟩ := hS.isClosedDisc_univ.exists_chart
  rw [discBd_univ] at hbd
  have hcont : Continuous h := continuousOn_univ.mp hh
  have hgl : ∀ x : S, g (h x) = x := fun x => hleft (mem_univ x)
  have hinj : Function.Injective h := fun x y hxy => by
    rw [← hgl x, ← hgl y, hxy]
  have hmem : ∀ x : S, h x ∈ closedBall (0 : ℂ) 1 := fun x => hmaps (mem_univ x)
  have hbd_iff : ∀ x : S, x ∈ bd S ↔ ‖h x‖ = 1 := by
    intro x
    rw [← mem_sphere_zero_iff_norm, ← hbd, hinj.mem_set_image]
  have hball_iff : ∀ x : S, x ∉ bd S ↔ h x ∈ ball (0 : ℂ) 1 := by
    intro x
    rw [hbd_iff, mem_ball_zero_iff]
    have hle : ‖h x‖ ≤ 1 := mem_closedBall_zero_iff.mp (hmem x)
    exact ⟨fun hne => lt_of_le_of_ne hle hne, fun hlt => hlt.ne⟩
  exact ⟨h, g, hcont, hinj, hg, hmem, hgl, fun z hz => hright hz, hbd, hbd_iff, hball_iff⟩

/-- An injective continuous map `G : ℂ → S` on `closedBall (0 : ℂ) 1` into `univ \ bd S` maps
`ball (0 : ℂ) ρ` (`0 < ρ ≤ 1`) to an open set in `S`. -/
theorem isOpen_image_ball_of_disc (hS : IsClosedDiscSpace S) {G : ℂ → S}
    (hGc : ContinuousOn G (closedBall (0 : ℂ) 1)) (hGi : InjOn G (closedBall (0 : ℂ) 1))
    {ρ : ℝ} (hρ1 : ρ ≤ 1) :
    IsOpen (G '' ball (0 : ℂ) ρ) := by
  obtain ⟨h, _, hh, hinj, _, _, _, _, _, _, _⟩ := exists_disc_complex_chart hS
  have hsub : ball (0 : ℂ) ρ ⊆ closedBall (0 : ℂ) 1 :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hρ1)
  have hcomp_c : ContinuousOn (h ∘ G) (ball (0 : ℂ) ρ) :=
    hh.comp_continuousOn (hGc.mono hsub)
  have hcomp_i : InjOn (h ∘ G) (ball (0 : ℂ) ρ) :=
    hinj.comp_injOn (hGi.mono hsub)
  have hopen_C : IsOpen ((h ∘ G) '' ball (0 : ℂ) ρ) :=
    isOpen_image_of_injOn isOpen_ball hcomp_c hcomp_i
  rw [image_comp] at hopen_C
  have hpre : h ⁻¹' (h '' (G '' ball (0 : ℂ) ρ)) = G '' ball (0 : ℂ) ρ :=
    preimage_image_eq _ hinj
  rw [← hpre]
  exact hopen_C.preimage hh

private theorem edge_has_collared_disc (hS : IsClosedDiscSpace S) (H : Drawing S)
  (hprop : H.IsProper)
    {e : Set S} (he : e ∈ H.E) {γ : I → S} (hγ : Continuous γ) (hγ0 : γ 0 ∈ H.V)
    (hγ1 : γ 1 ∈ H.V) (hinj : InjOn γ (Ioo 0 1)) (hγe : γ '' Ioo 0 1 = e)
    {s t₀ u : I} (ht₀ : t₀ ∈ Ioo (0 : I) 1) (hs : s < t₀) (hu : t₀ < u)
    {O : Set S} (hO : IsOpen O) (hpO : γ t₀ ∈ O) :
    ∃ (a₀ b₀ : I) (W A₁ Δ₁ : Set S),
      a₀ < t₀ ∧ t₀ < b₀ ∧ Icc a₀ b₀ ⊆ Ioo 0 1 ∧
      IsOpen W ∧ γ t₀ ∈ W ∧ W ⊆ O \ bd S ∧ Disjoint A₁ W ∧
      W ⊆ ((H.U \ e) ∪ γ '' {t | t ≤ s ∨ u ≤ t})ᶜ ∧
      W ⊆ ((H.U \ e) ∪ γ '' {t | t ≤ a₀ ∨ b₀ ≤ t})ᶜ ∧
      IsClosedDisc Δ₁ ∧ Δ₁ ⊆ univ \ discBd (univ : Set S) ∧
      discBd Δ₁ = A₁ ∪ γ '' Icc a₀ b₀ ∧ γ '' Icc a₀ b₀ ⊆ H.U := by
  classical
  have hT2 : T2Space S := t2Space_of_isClosedDiscSpace hS
  have hbd_cl : IsClosed (bd S) := isClosed_bd_of_isClosedDiscSpace hS
  have hpe : γ t₀ ∈ e := hγe ▸ mem_image_of_mem γ ht₀
  have hpbd₀ : γ t₀ ∉ bd S := fun hbd => (he.2.1 hpe).2 (hprop ⟨hbd, (he.2.1 hpe).1⟩)
  have hX₀ := isClosed_U_sdiff_edge H he
  have hmemIoo : ∀ {t : I}, γ t ∈ e → γ t ∉ H.V := fun h => (he.2.1 h).2
  have hend : ∀ {t : I}, t ∉ Ioo (0 : I) 1 → γ t ∈ H.V := by
    intro t ht
    have : t = 0 ∨ t = 1 := by
      by_contra hc
      push Not at hc
      exact ht ⟨unitInterval.pos_iff_ne_zero.mpr hc.1, unitInterval.lt_one_iff_ne_one.mpr hc.2⟩
    rcases this with rfl | rfl
    · exact hγ0
    · exact hγ1
  have hpiece : ∀ {t : I}, γ t = γ t₀ → t = t₀ := by
    intro t ht
    by_cases hti : t ∈ Ioo (0 : I) 1
    · exact hinj hti ht₀ ht
    · exact absurd (ht ▸ hend hti) (hmemIoo hpe)
  let Y₀ : Set S := (H.U \ e) ∪ γ '' {t | t ≤ s ∨ u ≤ t}
  have hY₀ : IsClosed Y₀ :=
    hX₀.union ((isClosed_Iic.union isClosed_Ici).isCompact.image hγ).isClosed
  have hpY₀ : γ t₀ ∉ Y₀ := by
    rintro (h | ⟨t, ht, hte⟩)
    · exact h.2 hpe
    · have := hpiece hte
      subst this
      rcases ht with h | h
      · exact absurd h (not_le.mpr hs)
      · exact absurd h (not_le.mpr hu)
  let O' : Set S := (O \ bd S) ∩ Y₀ᶜ
  have hO' : IsOpen O' := (hO.sdiff hbd_cl).inter hY₀.isOpen_compl
  have hpO' : γ t₀ ∈ O' := ⟨⟨hpO, hpbd₀⟩, hpY₀⟩
  obtain ⟨D, D', hD, hD', hpD', hD'D, hDO', hbdD⟩ :=
    disc_exists_closedDisc_nbhd hS hO' hpO' hpbd₀
  have hDO : ∀ {x}, x ∈ D → x ∉ Y₀ := fun hx => (hDO' hx).2
  have hD_sub_Obd : D ⊆ O \ bd S := fun x hx => (hDO' hx).1
  have hVout : ∀ x ∈ H.V, x ∉ D := fun x hx hxD =>
    hDO hxD (Or.inl ⟨H.V_subset_U hx, fun hxe => (he.2.1 hxe).2 hx⟩)
  have hDclosed : IsClosed D := hD.isClosed
  have hC₁ : IsCompact {t : I | t ≤ t₀ ∧ γ t ∉ D'} :=
    (isClosed_Iic.inter (hD'.isClosed_compl.preimage hγ)).isCompact
  have hC₂ : IsCompact {t : I | t₀ ≤ t ∧ γ t ∉ D'} :=
    (isClosed_Ici.inter (hD'.isClosed_compl.preimage hγ)).isCompact
  obtain ⟨a₀, ⟨hat, hagamma⟩, hamax⟩ := hC₁.exists_isGreatest
    ⟨0, unitInterval.nonneg _, fun h => hVout _ hγ0 (hD'D h)⟩
  obtain ⟨b₀, ⟨htb, hbgamma⟩, hbmin⟩ := hC₂.exists_isLeast
    ⟨1, unitInterval.le_one _, fun h => hVout _ hγ1 (hD'D h)⟩
  have ha₀ : a₀ < t₀ := lt_of_le_of_ne hat fun h => hagamma (h ▸ hpD')
  have hb₀ : t₀ < b₀ := lt_of_le_of_ne htb fun h => hbgamma (h ▸ hpD')
  have hIoo : ∀ t, a₀ < t → t < b₀ → γ t ∈ D' := by
    intro t h₁ h₂
    by_contra hcon
    rcases le_total t t₀ with h | h
    · exact absurd (hamax ⟨h, hcon⟩) (not_le.mpr h₁)
    · exact absurd (hbmin ⟨h, hcon⟩) (not_le.mpr h₂)
  have hab : a₀ < b₀ := ha₀.trans hb₀
  have hclosure : ∀ t ∈ closure (Ioo a₀ b₀), γ t ∈ D := by
    intro t ht
    have h₁ : γ t ∈ closure (γ '' Ioo a₀ b₀) := image_closure_subset_closure_image hγ ⟨t, ht, rfl⟩
    have h₂ : γ '' Ioo a₀ b₀ ⊆ D := by
      rintro _ ⟨v, hv, rfl⟩
      exact hD'D (hIoo v hv.1 hv.2)
    exact hDclosed.closure_subset_iff.mpr h₂ h₁
  have hamem : γ a₀ ∈ D := hclosure a₀ (by rw [closure_Ioo hab.ne]; exact ⟨le_rfl, hab.le⟩)
  have hbmem : γ b₀ ∈ D := hclosure b₀ (by rw [closure_Ioo hab.ne]; exact ⟨hab.le, le_rfl⟩)
  have ha0 : 0 < a₀ := unitInterval.pos_iff_ne_zero.mpr fun h => hVout _ hγ0 (h ▸ hamem)
  have hb1 : b₀ < 1 := unitInterval.lt_one_iff_ne_one.mpr fun h => hVout _ hγ1 (h ▸ hbmem)
  have hIcc : Icc a₀ b₀ ⊆ Ioo 0 1 := fun t ht => ⟨ha0.trans_le ht.1, ht.2.trans_lt hb1⟩
  have habR : (a₀ : ℝ) < b₀ := hab
  have hρmem : ∀ v : I, (a₀ : ℝ) + v.1 * (b₀ - a₀) ∈ Set.Icc (0 : ℝ) 1 := by
    intro v
    have hv₀ := v.2.1
    have hv₁ := v.2.2
    have ha' := a₀.2.1
    have hb' := b₀.2.2
    constructor
    · have : 0 ≤ v.1 * ((b₀ : ℝ) - a₀) := mul_nonneg hv₀ (by linarith)
      linarith
    · have : v.1 * ((b₀ : ℝ) - a₀) ≤ 1 * ((b₀ : ℝ) - a₀) :=
        mul_le_mul_of_nonneg_right hv₁ (by linarith)
      linarith
  let ρ : I → I := fun v => ⟨(a₀ : ℝ) + v.1 * (b₀ - a₀), hρmem v⟩
  have hρ : Continuous ρ := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  have hρIcc : ∀ v, ρ v ∈ Icc a₀ b₀ := by
    intro v
    have hv₀ := v.2.1
    have hv₁ := v.2.2
    constructor
    · have : 0 ≤ v.1 * ((b₀ : ℝ) - a₀) := mul_nonneg hv₀ (by linarith)
      exact Subtype.mk_le_mk.mpr (by linarith)
    · have : v.1 * ((b₀ : ℝ) - a₀) ≤ 1 * ((b₀ : ℝ) - a₀) :=
        mul_le_mul_of_nonneg_right hv₁ (by linarith)
      exact Subtype.mk_le_mk.mpr (by linarith)
  have hρsurj : ∀ t ∈ Icc a₀ b₀, ∃ v, ρ v = t := by
    intro t ht
    have ht₁ : (a₀ : ℝ) ≤ t := ht.1
    have ht₂ : (t : ℝ) ≤ b₀ := ht.2
    have hd : (0 : ℝ) < b₀ - a₀ := by linarith
    have hv : ((t : ℝ) - a₀) / (b₀ - a₀) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (by linarith) hd.le, (div_le_one hd).mpr (by linarith)⟩
    refine ⟨⟨_, hv⟩, Subtype.ext ?_⟩
    change (a₀ : ℝ) + ((t : ℝ) - a₀) / (b₀ - a₀) * (b₀ - a₀) = t
    field_simp
    ring
  have hρ0 : ρ 0 = a₀ := Subtype.ext (by simp [ρ])
  have hρ1 : ρ 1 = b₀ := Subtype.ext (by simp [ρ])
  have hρinj : Function.Injective ρ := by
    intro v w h
    have h₁ : (a₀ : ℝ) + v.1 * (b₀ - a₀) = a₀ + w.1 * (b₀ - a₀) := congrArg Subtype.val h
    have hd : ((b₀ : ℝ) - a₀) ≠ 0 := by linarith
    exact Subtype.ext (mul_right_cancel₀ hd (add_left_cancel h₁))
  let k : I → S := fun v => γ (ρ v)
  have hk : Continuous k := hγ.comp hρ
  have hkinj : Function.Injective k := fun v w h =>
    hρinj (hinj (hIcc (hρIcc v)) (hIcc (hρIcc w)) h)
  set F : Set S := γ '' Icc a₀ b₀ with hF
  have hFk : F = range k := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨v, rfl⟩ := hρsurj t ht
      exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨ρ v, hρIcc v, rfl⟩
  have hFline : IsLineWithEnds F (γ a₀) (γ b₀) := by
    rw [hFk]
    refine ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective k hkinj)
      hk.rangeFactorization, ?_, ?_⟩
    · change k 0 = γ a₀
      simp [k, hρ0]
    · change k 1 = γ b₀
      simp [k, hρ1]
  have hFD : F ⊆ D := by
    rintro _ ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.1 with rfl | h₁
    · exact hamem
    rcases eq_or_lt_of_le ht.2 with rfl | h₂
    · exact hbmem
    exact hD'D (hIoo t h₁ h₂)
  have hst : γ a₀ ≠ γ b₀ :=
    fun h => hab.ne (hinj (hIcc ⟨le_rfl, hab.le⟩) (hIcc ⟨hab.le, le_rfl⟩) h)
  have hFcap : F ∩ discBd D = {γ a₀, γ b₀} := by
    rw [← hbdD]
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, -, hxD'⟩
      rcases eq_or_lt_of_le ht.1 with rfl | h₁
      · exact Or.inl rfl
      rcases eq_or_lt_of_le ht.2 with rfl | h₂
      · exact Or.inr rfl
      exact absurd (hIoo t h₁ h₂) hxD'
    · rintro (rfl | hx)
      · exact ⟨⟨a₀, ⟨le_rfl, hab.le⟩, rfl⟩, hamem, hagamma⟩
      · rw [mem_singleton_iff.mp hx]
        exact ⟨⟨b₀, ⟨hab.le, le_rfl⟩, rfl⟩, hbmem, hbgamma⟩
  obtain ⟨A₁, A₂, Δ₁, Δ₂, -, hcomp, hΔ₁, -, hunion, -, hbd₁, -, -⟩ :=
    disc_iArc D F (γ a₀) (γ b₀) hD hFD hst hFline hFcap
  have hA₁ : A₁ ⊆ discBd D := by
    have hmem : A₁ ∈ componentsIn (discBd D \ {γ a₀, γ b₀}) := by rw [hcomp]; simp
    obtain ⟨x, -, rfl⟩ := hmem
    exact (connectedComponentIn_subset _ _).trans sdiff_subset
  have hA₁D' : Disjoint A₁ D' := by
    refine disjoint_left.mpr fun x hx hx' => ?_
    have := hA₁ hx
    rw [← hbdD] at this
    exact this.2 hx'
  have hFU : F ⊆ H.U := by
    rintro _ ⟨t, ht, rfl⟩
    exact (he.2.1 (hγe ▸ mem_image_of_mem γ (hIcc ht))).1
  let Y₁ : Set S := (H.U \ e) ∪ γ '' {t | t ≤ a₀ ∨ b₀ ≤ t}
  have hY₁ : IsClosed Y₁ :=
    hX₀.union ((isClosed_Iic.union isClosed_Ici).isCompact.image hγ).isClosed
  have hpY₁ : γ t₀ ∉ Y₁ := by
    rintro (h | ⟨t, ht, hte⟩)
    · exact h.2 hpe
    · have := hpiece hte
      subst this
      rcases ht with h | h
      · exact absurd h (not_le.mpr ha₀)
      · exact absurd h (not_le.mpr hb₀)
  let W : Set S := D' ∩ Y₁ᶜ
  have hW : IsOpen W := hD'.inter hY₁.isOpen_compl
  have hpW : γ t₀ ∈ W := ⟨hpD', hpY₁⟩
  have hW_Obd : W ⊆ O \ bd S := fun x hx => hD_sub_Obd (hD'D hx.1)
  have hin_univ : Δ₁ ⊆ univ \ discBd (univ : Set S) := by
    rw [discBd_univ]
    intro x hx
    exact ⟨mem_univ x, (hD_sub_Obd (hunion ▸ Or.inl hx)).2⟩
  exact ⟨a₀, b₀, W, A₁, Δ₁, ha₀, hb₀, hIcc, hW, hpW, hW_Obd,
    hA₁D'.mono_right inter_subset_left, fun _ hx => hDO (hD'D hx.1), fun _ hx => hx.2,
    hΔ₁, hin_univ, hbd₁, hFU⟩

private theorem chart_in_collared_disc (hS : IsClosedDiscSpace S) (H : Drawing S)
    {e : Set S} {γ : I → S} (hγe : γ '' Ioo 0 1 = e)
    {a₀ b₀ t₀ : I} (ha₀ : a₀ < t₀) (hb₀ : t₀ < b₀)
    {W A₁ Δ₁ : Set S} (hW : IsOpen W) (hpW : γ t₀ ∈ W) (hA₁W : Disjoint A₁ W)
    (hW_avoid : W ⊆ ((H.U \ e) ∪ γ '' {t | t ≤ a₀ ∨ b₀ ≤ t})ᶜ)
    (hΔ₁ : IsClosedDisc Δ₁) (hin_univ : Δ₁ ⊆ univ \ discBd (univ : Set S))
    (hbd₁ : discBd Δ₁ = A₁ ∪ γ '' Icc a₀ b₀) (hFU : γ '' Icc a₀ b₀ ⊆ H.U) :
    ∃ G : ℂ → S, ContinuousOn G (closedBall 0 1) ∧ InjOn G (closedBall 0 1) ∧ G 0 = γ t₀ ∧
      G '' closedBall 0 1 ⊆ W ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, z.im = 0 → G z ∈ γ '' Ioo a₀ b₀) ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, G z ∈ H.U ↔ z.im = 0) := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have hpbd : γ t₀ ∈ discBd Δ₁ := by
    rw [hbd₁]
    exact Or.inr (mem_image_of_mem γ ⟨ha₀.le, hb₀.le⟩)
  obtain ⟨p⟩ := hΔ₁.isOArc_discBd
  obtain ⟨c, c', hc, -, -, -, hl, -, -, -, hcp⟩ :=
    exists_disc_collar hΔ₁ hS.isClosedDisc_univ hin_univ p
  have hcinj : InjOn c (closedBall 0 2) := hl.injOn
  let w₀ : Circle := p.symm ⟨γ t₀, hpbd⟩
  have hcw₀ : c w₀ = γ t₀ := by
    rw [hcp]
    simp [w₀]
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ : ℝ, Circle.exp θ₀ = w₀ :=
    ⟨Complex.arg (w₀ : ℂ), Circle.exp_arg w₀⟩
  have hw₀c : cis' θ₀ = w₀ := by rw [cis'_eq_exp, hθ₀]
  have hopen : IsOpen (ball (0 : ℂ) 2 ∩ c ⁻¹' W) :=
    (hc.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball hW
  have hmemw : (w₀ : ℂ) ∈ ball (0 : ℂ) 2 ∩ c ⁻¹' W := by
    refine ⟨by simp, ?_⟩
    change c w₀ ∈ W
    rw [hcw₀]
    exact hpW
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen _ hmemw
  obtain ⟨δ₁, hδ₁, hd⟩ := Metric.continuous_iff.mp continuous_cis' θ₀ (r / 2) (by positivity)
  obtain ⟨ε, hε, hεr, hε1⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ r / 2 ∧ ε ≤ 1 / 2 :=
    ⟨min (r / 2) (1 / 2), by positivity, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨δ, hδ, hδ₂, hδ1⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < δ₁ ∧ δ ≤ 1 :=
    ⟨min (δ₁ / 2) 1, by positivity, (min_le_left _ _).trans_lt (by linarith), min_le_right _ _⟩
  let m : ℂ → ℂ := fun z => ((1 + ε * z.im : ℝ) : ℂ) * cis' (θ₀ + δ * z.re)
  have hmc : Continuous m := by
    refine Continuous.mul (Complex.continuous_ofReal.comp ?_) (continuous_cis'.comp ?_)
    · exact continuous_const.add (continuous_const.mul Complex.continuous_im)
    · exact continuous_const.add (continuous_const.mul Complex.continuous_re)
  have hbound : ∀ z ∈ closedBall (0 : ℂ) 1, |z.re| ≤ 1 ∧ |z.im| ≤ 1 := fun z hz => by
    have hn : ‖z‖ ≤ 1 := by simpa using hz
    exact ⟨(Complex.abs_re_le_norm z).trans hn, (Complex.abs_im_le_norm z).trans hn⟩
  have hpos : ∀ z ∈ closedBall (0 : ℂ) 1, 0 < 1 + ε * z.im := fun z hz => by
    have h₁ := abs_le.mp (hbound z hz).2
    nlinarith [h₁.1, h₁.2]
  have hmn : ∀ z ∈ closedBall (0 : ℂ) 1, ‖m z‖ = 1 + ε * z.im := fun z hz => by
    simp only [m, norm_mul, norm_cis', mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (hpos z hz)
  have hmball : ∀ z ∈ closedBall (0 : ℂ) 1, m z ∈ ball (w₀ : ℂ) r := by
    intro z hz
    obtain ⟨h₁, h₂⟩ := hbound z hz
    have h₃ : dist (θ₀ + δ * z.re) θ₀ < δ₁ := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_mul, abs_of_pos hδ]
      nlinarith [abs_nonneg z.re]
    have h₄ : ‖cis' (θ₀ + δ * z.re) - w₀‖ < r / 2 := by
      have := hd _ h₃
      rwa [dist_eq_norm, hw₀c] at this
    have h₅ : m z - w₀ = ((ε * z.im : ℝ) : ℂ) * cis' (θ₀ + δ * z.re) + (cis' (θ₀ + δ * z.re) - w₀)
      := by
      simp only [m]
      push_cast
      ring
    have h₆ : ‖((ε * z.im : ℝ) : ℂ) * cis' (θ₀ + δ * z.re)‖ ≤ r / 2 := by
      rw [norm_mul, norm_cis', mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hε]
      nlinarith [abs_nonneg z.im]
    rw [mem_ball, dist_eq_norm, h₅]
    exact (norm_add_le _ _).trans_lt (by linarith)
  have hmW : ∀ z ∈ closedBall (0 : ℂ) 1, m z ∈ ball (0 : ℂ) 2 ∧ c (m z) ∈ W := fun z hz =>
    hball (hmball z hz)
  have hmball2 : ∀ z ∈ closedBall (0 : ℂ) 1, m z ∈ closedBall (0 : ℂ) 2 := fun z hz =>
    ball_subset_closedBall (hmW z hz).1
  let G : ℂ → S := fun z => c (m z)
  have hGc : ContinuousOn G (closedBall 0 1) :=
    hc.comp hmc.continuousOn hmball2
  have hGi : InjOn G (closedBall 0 1) := by
    intro y hy z hz hyz
    have h₁ : m y = m z := hcinj (hmball2 y hy) (hmball2 z hz) hyz
    have h₂ : y.im = z.im := by
      have := congrArg norm h₁
      rw [hmn y hy, hmn z hz] at this
      exact mul_left_cancel₀ hε.ne' (add_left_cancel this)
    have h₃ : cis' (θ₀ + δ * y.re) = cis' (θ₀ + δ * z.re) := by
      have hne : ((1 + ε * y.im : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (hpos y hy).ne'
      simp only [m, h₂] at h₁
      rw [h₂] at hne
      exact mul_left_cancel₀ hne h₁
    have h₄ : Circle.exp (θ₀ + δ * y.re) = Circle.exp (θ₀ + δ * z.re) := by
      apply Circle.ext
      rw [← cis'_eq_exp, ← cis'_eq_exp, h₃]
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp h₄
    have h₅ : δ * (y.re - z.re) = k * (2 * Real.pi) := by linarith
    have h₆ : |y.re - z.re| ≤ 2 := by
      have a₁ := abs_le.mp (hbound y hy).1
      have a₂ := abs_le.mp (hbound z hz).1
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have h₇ : |(k : ℝ) * (2 * Real.pi)| ≤ 2 := by
      rw [← h₅, abs_mul, abs_of_pos hδ]
      nlinarith [abs_nonneg (y.re - z.re)]
    have hπ := Real.pi_gt_three
    have hk0 : k = 0 := by
      by_contra hk0
      have h₈ : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at h₇
      nlinarith
    have h₉ : δ * (y.re - z.re) = 0 := by rw [h₅, hk0]; simp
    have h₁₀ : y.re = z.re := by
      have := (mul_eq_zero.mp h₉).resolve_left hδ.ne'
      linarith
    exact Complex.ext h₁₀ h₂
  have hG0 : G 0 = γ t₀ := by
    change c (m 0) = _
    have : m 0 = w₀ := by simp [m, hw₀c]
    rw [this, hcw₀]
  have hreal : ∀ z ∈ closedBall (0 : ℂ) 1, z.im = 0 → G z ∈ γ '' Ioo a₀ b₀ := by
    intro z hz him
    have hmz : m z = (Circle.exp (θ₀ + δ * z.re) : ℂ) := by
      simp only [m, him, mul_zero, add_zero, Complex.ofReal_one, one_mul]
      exact cis'_eq_exp _
    have hW' := (hmW z hz).2
    have hb : G z ∈ discBd Δ₁ := by
      change c (m z) ∈ _
      rw [hmz, hcp]
      exact (p _).2
    rw [hbd₁] at hb
    rcases hb with hb | ⟨t, ht, hte⟩
    · exact absurd hW' (disjoint_left.mp hA₁W hb)
    · refine ⟨t, ?_, hte⟩
      refine ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩
      · rintro rfl
        exact hW_avoid hW' (Or.inr ⟨_, Or.inl le_rfl, hte⟩)
      · rintro rfl
        exact hW_avoid hW' (Or.inr ⟨_, Or.inr le_rfl, hte⟩)
  have hUiff : ∀ z ∈ closedBall (0 : ℂ) 1, G z ∈ H.U ↔ z.im = 0 := by
    intro z hz
    constructor
    · intro hzU
      have hW' := (hmW z hz).2
      have hze : G z ∈ e := by
        by_contra hn
        exact hW_avoid hW' (Or.inl ⟨hzU, hn⟩)
      obtain ⟨t, ht, hte⟩ : G z ∈ γ '' Ioo 0 1 := hγe ▸ hze
      have htab : t ∈ Icc a₀ b₀ := by
        by_contra hn
        have : t ≤ a₀ ∨ b₀ ≤ t := by
          by_contra hc'
          push Not at hc'
          exact hn ⟨hc'.1.le, hc'.2.le⟩
        exact hW_avoid hW' (Or.inr ⟨t, this, hte⟩)
      have hb : G z ∈ discBd Δ₁ := by
        rw [hbd₁]
        exact Or.inr ⟨t, htab, hte⟩
      obtain ⟨w, hw⟩ := (show ∃ w : discBd Δ₁, w.1 = G z from ⟨⟨_, hb⟩, rfl⟩)
      have hcw : c (p.symm w) = G z := by
        rw [hcp]
        simpa using hw
      have hwn : ((p.symm w : Circle) : ℂ) ∈ closedBall (0 : ℂ) 2 := by simp
      have heq := hcinj hwn (hmball2 z hz) hcw
      have hn₁ := hmn z hz
      rw [← heq] at hn₁
      simp only [Circle.norm_coe] at hn₁
      have : ε * z.im = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hε.ne'
    · intro him
      obtain ⟨t, ht, hte⟩ := hreal z hz him
      exact hte ▸ hFU ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
  exact ⟨G, hGc, hGi, hG0, by rintro _ ⟨z, hz, rfl⟩; exact (hmW z hz).2, hreal, hUiff⟩

/-- **A chart around a point of an edge on a closed disc space.** Here `G` maps the closed unit disc
of `ℂ` onto a closed disc around `γ t₀` inside `O \ bd S`. The real part of the disc is the piece
of `e` from `γ a` to `γ b`, and there is no other point of `U(H)` in the disc. -/
theorem disc_exists_edge_chart (hS : IsClosedDiscSpace S) (H : Drawing S) (hprop : H.IsProper)
    {e : Set S} (he : e ∈ H.E) {γ : I → S} (hγ : Continuous γ) (hγ0 : γ 0 ∈ H.V)
    (hγ1 : γ 1 ∈ H.V) (hinj : InjOn γ (Ioo 0 1)) (hγe : γ '' Ioo 0 1 = e)
    {s t₀ u : I} (ht₀ : t₀ ∈ Ioo (0 : I) 1) (hs : s < t₀) (hu : t₀ < u)
    {O : Set S} (hO : IsOpen O) (hpO : γ t₀ ∈ O) :
    ∃ (G : ℂ → S) (a b : I), ContinuousOn G (closedBall 0 1) ∧ InjOn G (closedBall 0 1) ∧
      s < a ∧ a < t₀ ∧ t₀ < b ∧ b < u ∧ G 0 = γ t₀ ∧
      G '' closedBall (0 : ℂ) 1 ⊆ O \ bd S ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, G z ∈ H.U ↔ z.im = 0) ∧
      G '' {z | z ∈ ball (0 : ℂ) 1 ∧ z.im = 0} = γ '' Ioo a b ∧
      G '' {z | z ∈ closedBall (0 : ℂ) 1 ∧ z.im = 0} = γ '' Icc a b ∧
      ((G (-1) = γ a ∧ G 1 = γ b) ∨ (G (-1) = γ b ∧ G 1 = γ a)) := by
  classical
  have hT2 : T2Space S := t2Space_of_isClosedDiscSpace hS
  have hpe : γ t₀ ∈ e := hγe ▸ mem_image_of_mem γ ht₀
  have hmemIoo : ∀ {t : I}, γ t ∈ e → γ t ∉ H.V := fun h => (he.2.1 h).2
  have hend : ∀ {t : I}, t ∉ Ioo (0 : I) 1 → γ t ∈ H.V := by
    intro t ht
    have : t = 0 ∨ t = 1 := by
      by_contra hc
      push Not at hc
      exact ht ⟨unitInterval.pos_iff_ne_zero.mpr hc.1, unitInterval.lt_one_iff_ne_one.mpr hc.2⟩
    rcases this with rfl | rfl
    · exact hγ0
    · exact hγ1
  have hpiece : ∀ {t : I}, γ t = γ t₀ → t = t₀ := by
    intro t ht
    by_cases hti : t ∈ Ioo (0 : I) 1
    · exact hinj hti ht₀ ht
    · exact absurd (ht ▸ hend hti) (hmemIoo hpe)
  obtain ⟨a₀, b₀, W, A₁, Δ₁, ha₀, hb₀, hIcc, hW, hpW, hW_Obd, hA₁W, hW₀, hW₁,
    hΔ₁, hin_univ, hbd₁, hFU⟩ :=
    edge_has_collared_disc hS H hprop he hγ hγ0 hγ1 hinj hγe ht₀ hs hu hO hpO
  obtain ⟨G, hGc, hGi, hG0, hGW, hreal, hUiff⟩ :=
    chart_in_collared_disc hS H hγe ha₀ hb₀ hW hpW hA₁W hW₁ hΔ₁ hin_univ hbd₁ hFU
  let F := γ '' Icc a₀ b₀
  let Y₀ : Set S := ((H.U \ e) ∪ γ '' {t | t ≤ s ∨ u ≤ t})
  have hG_Obd := hGW.trans hW_Obd
  let zv : I → ℂ := fun v => ((2 * v.1 - 1 : ℝ) : ℂ)
  have hzvc : Continuous zv := Complex.continuous_ofReal.comp (by fun_prop)
  have hzvi : Function.Injective zv := fun v w h => by
    have h₁ : 2 * v.1 - 1 = 2 * w.1 - 1 := Complex.ofReal_injective h
    exact Subtype.ext (by linarith)
  have hzvb : ∀ v, zv v ∈ closedBall (0 : ℂ) 1 := fun v => by
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have := v.2.1
    have := v.2.2
    constructor <;> linarith
  have hzvim : ∀ v, (zv v).im = 0 := fun v => Complex.ofReal_im _
  have hzvex : ∀ z ∈ closedBall (0 : ℂ) 1, z.im = 0 → ∃ v, z = zv v := by
    intro z hz him
    have hn : ‖z‖ ≤ 1 := by simpa using hz
    have h := abs_le.mp ((Complex.abs_re_le_norm z).trans hn)
    refine ⟨⟨(z.re + 1) / 2, by linarith [h.1], by linarith [h.2]⟩, Complex.ext ?_ ?_⟩
    · simp [zv]
      ring
    · simp [zv, him]
  have hzvball : ∀ v, v ∈ Ioo (0 : I) 1 ↔ zv v ∈ ball (0 : ℂ) 1 := by
    intro v
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor
    · rintro ⟨h₁, h₂⟩
      have h₁' : (0 : ℝ) < v.1 := h₁
      have h₂' : v.1 < 1 := h₂
      constructor <;> linarith
    · rintro ⟨h₁, h₂⟩
      exact ⟨show (0 : ℝ) < v.1 by linarith, show v.1 < 1 by linarith⟩
  have hIccF : ∀ v, G (zv v) ∈ F := fun v => by
    obtain ⟨t, ht, hte⟩ := hreal _ (hzvb v) (hzvim v)
    exact ⟨t, ⟨ht.1.le, ht.2.le⟩, hte⟩
  have hc₁ : CompactSpace (Icc a₀ b₀) := isCompact_iff_compactSpace.mp isCompact_Icc
  let j : Icc a₀ b₀ → F := fun t => ⟨γ t.1, mem_image_of_mem γ t.2⟩
  have hjc : Continuous j := Continuous.subtype_mk (hγ.comp continuous_subtype_val) _
  have hjb : Function.Bijective j := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hinj (hIcc x.2) (hIcc y.2) (congrArg Subtype.val hxy))
    · rintro ⟨_, t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  let q : Icc a₀ b₀ ≃ₜ F := hjc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective j hjb)
  let ψ : I → I := fun v => (q.symm ⟨G (zv v), hIccF v⟩).1
  have hψγ : ∀ v, γ (ψ v) = G (zv v) := fun v =>
    congrArg Subtype.val (q.apply_symm_apply ⟨G (zv v), hIccF v⟩)
  have hψc : Continuous ψ := by
    refine continuous_subtype_val.comp (q.symm.continuous.comp (Continuous.subtype_mk ?_ _))
    exact hGc.comp_continuous hzvc hzvb
  have hψi : Function.Injective ψ := fun v w h => by
    have h₁ : G (zv v) = G (zv w) := by rw [← hψγ, ← hψγ, h]
    exact hzvi (hGi (hzvb v) (hzvb w) h₁)
  have hmid : ψ ⟨1 / 2, by norm_num, by norm_num⟩ = t₀ := by
    apply hpiece
    rw [hψγ]
    have : zv ⟨1 / 2, by norm_num, by norm_num⟩ = 0 := by simp [zv]
    rw [this, hG0]
  have hW' : ∀ v, G (zv v) ∉ Y₀ := fun v => hW₀ (hGW (mem_image_of_mem G (hzvb v)))
  have hboth : ∀ v, s < ψ v ∧ ψ v < u := by
    intro v
    constructor
    · by_contra hc'
      exact hW' v (Or.inr ⟨ψ v, Or.inl (not_lt.mp hc'), hψγ v⟩)
    · by_contra hc'
      exact hW' v (Or.inr ⟨ψ v, Or.inr (not_lt.mp hc'), hψγ v⟩)
  have hz0 : zv 0 = -1 := by simp [zv]
  have hz1 : zv 1 = 1 := by
    simp only [zv]
    norm_num
  have hmid₀ : (0 : I) < ⟨1 / 2, by norm_num, by norm_num⟩ :=
    show (0 : ℝ) < 1 / 2 by norm_num
  have hmid₁ : (⟨1 / 2, by norm_num, by norm_num⟩ : I) < 1 :=
    show (1 / 2 : ℝ) < 1 by norm_num
  have hrange : ∀ {a b : I}, a ∈ range ψ → b ∈ range ψ → Icc a b ⊆ range ψ := fun ha hb =>
    isPreconnected_range hψc |>.Icc_subset ha hb
  have hseg₁ : ∀ X : Set I, G '' (zv '' X) = γ '' (ψ '' X) := by
    intro X
    rw [image_image, image_image]
    exact image_congr fun v _ => (hψγ v).symm
  have hball' : {z | z ∈ ball (0 : ℂ) 1 ∧ z.im = 0} = zv '' Ioo 0 1 := by
    ext z
    constructor
    · rintro ⟨hz, him⟩
      obtain ⟨v, rfl⟩ := hzvex z (ball_subset_closedBall hz) him
      exact ⟨v, (hzvball v).mpr hz, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨(hzvball v).mp hv, hzvim v⟩
  have hclosed' : {z | z ∈ closedBall (0 : ℂ) 1 ∧ z.im = 0} = zv '' univ := by
    ext z
    constructor
    · rintro ⟨hz, him⟩
      obtain ⟨v, rfl⟩ := hzvex z hz him
      exact ⟨v, mem_univ _, rfl⟩
    · rintro ⟨v, -, rfl⟩
      exact ⟨hzvb v, hzvim v⟩
  rcases Continuous.strictMono_of_inj hψc hψi with hmono | hanti
  · refine ⟨G, ψ 0, ψ 1, hGc, hGi, (hboth 0).1, ?_, ?_, (hboth 1).2, hG0, hG_Obd, hUiff,
      ?_, ?_, Or.inl ?_⟩
    · rw [← hmid]
      exact hmono hmid₀
    · rw [← hmid]
      exact hmono hmid₁
    · rw [hball', hseg₁]
      congr 1
      apply subset_antisymm
      · rintro _ ⟨v, hv, rfl⟩
        exact ⟨hmono hv.1, hmono hv.2⟩
      · rintro t ⟨h₁, h₂⟩
        obtain ⟨v, rfl⟩ := hrange ⟨0, rfl⟩ ⟨1, rfl⟩ (⟨h₁.le, h₂.le⟩ : t ∈ Icc (ψ 0) (ψ 1))
        exact ⟨v, ⟨hmono.lt_iff_lt.mp h₁, hmono.lt_iff_lt.mp h₂⟩, rfl⟩
    · rw [hclosed', hseg₁]
      congr 1
      apply subset_antisymm
      · rintro _ ⟨v, -, rfl⟩
        exact ⟨hmono.monotone v.2.1, hmono.monotone v.2.2⟩
      · rintro t ht
        obtain ⟨v, rfl⟩ := hrange ⟨0, rfl⟩ ⟨1, rfl⟩ ht
        exact ⟨v, mem_univ _, rfl⟩
    · exact ⟨by rw [← hz0, hψγ], by rw [hψγ 1, hz1]⟩
  · refine ⟨G, ψ 1, ψ 0, hGc, hGi, (hboth 1).1, ?_, ?_, (hboth 0).2, hG0, hG_Obd, hUiff,
      ?_, ?_, Or.inr ?_⟩
    · rw [← hmid]
      exact hanti hmid₁
    · rw [← hmid]
      exact hanti hmid₀
    · rw [hball', hseg₁]
      congr 1
      apply subset_antisymm
      · rintro _ ⟨v, hv, rfl⟩
        exact ⟨hanti hv.2, hanti hv.1⟩
      · rintro t ⟨h₁, h₂⟩
        obtain ⟨v, rfl⟩ := hrange ⟨1, rfl⟩ ⟨0, rfl⟩ (⟨h₁.le, h₂.le⟩ : t ∈ Icc (ψ 1) (ψ 0))
        exact ⟨v, ⟨hanti.lt_iff_gt.mp h₂, hanti.lt_iff_gt.mp h₁⟩, rfl⟩
    · rw [hclosed', hseg₁]
      congr 1
      apply subset_antisymm
      · rintro _ ⟨v, -, rfl⟩
        exact ⟨hanti.antitone v.2.2, hanti.antitone v.2.1⟩
      · rintro t ht
        obtain ⟨v, rfl⟩ := hrange ⟨1, rfl⟩ ⟨0, rfl⟩ ht
        exact ⟨v, mem_univ _, rfl⟩
    · exact ⟨by rw [← hz0, hψγ], by rw [hψγ 1, hz1]⟩

/-- An arc `J` in a closed disc space `S` that meets `K ∪ bd S` in at most a single point `v`
does not separate any connected component of `(univ \ bd S) \ K`. -/
theorem disc_sdiff_arc_connectedComponentIn (hS : IsClosedDiscSpace S) {K J : Set S} {v : S}
    (hK : IsClosed K) (hJ : IsLine J) (hJK : J ∩ K ⊆ {v}) (hJbd : J ∩ bd S ⊆ {v})
    {a b : S} (ha : a ∈ (univ \ bd S) \ (K ∪ J)) (hb : b ∈ (univ \ bd S) \ (K ∪ J))
    (hab : b ∈ connectedComponentIn ((univ \ bd S) \ K) a) :
    b ∈ connectedComponentIn ((univ \ bd S) \ (K ∪ J)) a := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have : CompactSpace S := compactSpace_of_isClosedDiscSpace hS
  have hbd_cl : IsClosed (bd S) := isClosed_bd_of_isClosedDiscSpace hS
  obtain ⟨h, g, hh, hinj, hg, hmem, hgl, hgr, hbd_img, _, hball_iff⟩ := exists_disc_complex_chart hS
  obtain ⟨φ⟩ := hJ
  have : CompactSpace J := φ.compactSpace
  let fJ : J → h '' J := fun x => ⟨h x.1, x.1, x.2, rfl⟩
  have hfJ_c : Continuous fJ := Continuous.subtype_mk (hh.comp continuous_subtype_val) _
  have hfJ_b : Function.Bijective fJ := by
    refine ⟨fun x y hxy => Subtype.ext (hinj (congrArg Subtype.val hxy)), ?_⟩
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  let ψJ : I ≃ₜ h '' J := φ.trans (hfJ_c.homeoOfEquivCompactToT2 (f := Equiv.ofBijective fJ hfJ_b))
  let L₁ : Set ℂ := h '' J
  let L₂ : Set ℂ := h '' (K ∪ bd S)
  have hL₁_comp : IsCompact L₁ := isCompact_iff_compactSpace.mpr ψJ.compactSpace
  have hL₂_comp : IsCompact L₂ := ((hK.union hbd_cl).isCompact.image hh)
  have h_inter : L₁ ∩ L₂ ⊆ {h v} := by
    rw [← image_inter hinj]
    rintro _ ⟨x, ⟨hxJ, hxK | hxbd⟩, rfl⟩
    · rw [mem_singleton_iff.mp (hJK ⟨hxJ, hxK⟩)]
      exact rfl
    · rw [mem_singleton_iff.mp (hJbd ⟨hxJ, hxbd⟩)]
      exact rfl
  have h_inter_pre : IsPreconnected (L₁ ∩ L₂) :=
    (subsingleton_singleton.anti h_inter).isPreconnected
  have ha_L₁ : h a ∉ L₁ := by
    rw [hinj.mem_set_image]
    exact fun hJ' => ha.2 (Or.inr hJ')
  have hb_L₁ : h b ∉ L₁ := by
    rw [hinj.mem_set_image]
    exact fun hJ' => hb.2 (Or.inr hJ')
  have ha_L₂ : h a ∉ L₂ := by
    rw [hinj.mem_set_image]
    rintro (hK' | hbd')
    · exact ha.2 (Or.inl hK')
    · exact ha.1.2 hbd'
  have hb_L₂ : h b ∉ L₂ := by
    rw [hinj.mem_set_image]
    rintro (hK' | hbd')
    · exact hb.2 (Or.inl hK')
    · exact hb.1.2 hbd'
  have hab₁ : h b ∈ connectedComponentIn L₁ᶜ (h a) := by
    rw [component_eq_of_arc ψJ ha_L₁ hb_L₁]
    exact mem_connectedComponentIn hb_L₁
  have hab₂ : h b ∈ connectedComponentIn L₂ᶜ (h a) := by
    let C₀ := connectedComponentIn ((univ \ bd S) \ K) a
    have hC₀_pre : IsPreconnected (h '' C₀) :=
      isPreconnected_connectedComponentIn.image _ hh.continuousOn
    have hC₀_sub : h '' C₀ ⊆ L₂ᶜ := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' := connectedComponentIn_subset _ _ hx
      rw [mem_compl_iff, hinj.mem_set_image]
      rintro (hxK | hxbd)
      · exact hx'.2 hxK
      · exact hx'.1.2 hxbd
    have ha_C₀ : h a ∈ h '' C₀ := ⟨a, mem_connectedComponentIn ⟨ha.1, fun hK' => ha.2
      (Or.inl hK')⟩, rfl⟩
    have hb_C₀ : h b ∈ h '' C₀ := ⟨b, hab, rfl⟩
    exact hC₀_pre.subset_connectedComponentIn ha_C₀ hC₀_sub hb_C₀
  have hab₁₂ : h b ∈ connectedComponentIn (L₁ ∪ L₂)ᶜ (h a) :=
    janiszewski hL₁_comp hL₂_comp h_inter_pre
      (fun h' => h'.elim ha_L₁ ha_L₂) (fun h' => h'.elim hb_L₁ hb_L₂) hab₁ hab₂
  let C := connectedComponentIn (L₁ ∪ L₂)ᶜ (h a)
  have hC_pre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hC_sub_compl : C ⊆ (L₁ ∪ L₂)ᶜ := connectedComponentIn_subset _ _
  have hC_ball : C ⊆ ball (0 : ℂ) 1 := by
    refine hC_pre.subset_left_of_subset_union isOpen_ball isClosed_closedBall.isOpen_compl
      (disjoint_left.mpr fun z hz₁ hz₂ => hz₂ (ball_subset_closedBall hz₁)) ?_
      ⟨h a, mem_connectedComponentIn (fun h' => h'.elim ha_L₁ ha_L₂), (hball_iff a).mp ha.1.2⟩
    intro z hz
    by_cases hlt : ‖z‖ < 1
    · exact Or.inl (mem_ball_zero_iff.mpr hlt)
    · refine Or.inr ?_
      rw [mem_compl_iff, mem_closedBall_zero_iff, not_le]
      refine lt_of_le_of_ne (not_lt.mp hlt) fun heq => ?_
      have hsph : z ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr heq.symm
      rw [← hbd_img] at hsph
      obtain ⟨x, hxbd, rfl⟩ := hsph
      exact hC_sub_compl hz (Or.inr ⟨x, Or.inr hxbd, rfl⟩)
  have hC_cb : C ⊆ closedBall (0 : ℂ) 1 := hC_ball.trans ball_subset_closedBall
  have hgC_pre : IsPreconnected (g '' C) :=
    hC_pre.image g (hg.mono hC_cb)
  have hgC_sub : g '' C ⊆ (univ \ bd S) \ (K ∪ J) := by
    rintro _ ⟨z, hz, rfl⟩
    have hgz : h (g z) = z := hgr z (hC_cb hz)
    have hz_compl := hC_sub_compl hz
    refine ⟨⟨mem_univ _, fun hbd' => hz_compl (Or.inr ⟨g z, Or.inr hbd', hgz⟩)⟩, ?_⟩
    rintro (hK' | hJ')
    · exact hz_compl (Or.inr ⟨g z, Or.inl hK', hgz⟩)
    · exact hz_compl (Or.inl ⟨g z, hJ', hgz⟩)
  have ha_gC : a ∈ g '' C :=
    ⟨h a, mem_connectedComponentIn (fun h' => h'.elim ha_L₁ ha_L₂), hgl a⟩
  have hb_gC : b ∈ g '' C := ⟨h b, hab₁₂, hgl b⟩
  exact hgC_pre.subset_connectedComponentIn ha_gC hgC_sub hb_gC

end GraphMinor.GM06
