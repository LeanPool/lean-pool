/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.PolarChart
public import LeanPool.GraphMinor.GM11.Corners
public import LeanPool.GraphMinor.GM11.EdgeSides
public import LeanPool.GraphMinor.GM11.Solid
public import LeanPool.GraphMinor.GM11.NiceStatements
import Mathlib.Analysis.Convex.Contractible
import LeanPool.GraphMinor.Surface.ArcTools

/-!
# Closed nice sets are cones near each point

`isLocalCone` says that two closed nice sets `X, Y` look like a cone near each point `z` of `X ∪ Y`.
There
is a simply-connected set `K` that contains all of `X ∪ Y` near `z`, and each point of `K` is joined
to `z`
inside `K`, by a path in `X` or by a path in `Y`.

The proof takes a polar chart at `z`, in which each ray from the centre lies in one atom of the
drawing. A
closed nice set then contains, with each point of the chart, the whole segment from that point to
the
centre. A polar chart exists at a vertex with at least two half-edges (`exists_isPolar_of_sectors`)
and at a
point of an edge (`exists_isPolar_of_edge`). At other points only one region is near `z`, and at
most one
edge, and `isLocalCone` treats them directly.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- `X` and `Y` are a cone at `z`. See the module docstring. -/
def IsLocalCone (X Y : Set S) (z : S) : Prop :=
  ∃ O K : Set S, IsOpen O ∧ z ∈ O ∧ (X ∪ Y) ∩ O ⊆ K ∧ K ⊆ X ∪ Y ∧ IsSimplyConnectedSet K ∧ z ∈ K ∧
    ∀ a ∈ K, JoinedIn (K ∩ X) a z ∨ JoinedIn (K ∩ Y) a z

theorem IsLocalCone.symm {X Y : Set S} {z : S} (h : IsLocalCone X Y z) : IsLocalCone Y X z := by
  obtain ⟨O, K, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  exact ⟨O, K, h₁, h₂, by rwa [union_comm], by rwa [union_comm], h₅, h₆, fun a ha => (h₇ a ha).symm⟩

/-- A simply-connected set inside `X` that contains `X ∪ Y` near `z` makes a cone. -/
theorem isLocalCone_of_subset {X Y K O : Set S} {z : S} (hK : IsSimplyConnectedSet K) (hKX : K ⊆ X)
    (hz : z ∈ K) (hO : IsOpen O) (hzO : z ∈ O) (hsub : (X ∪ Y) ∩ O ⊆ K) : IsLocalCone X Y z := by
  refine ⟨O, K, hO, hzO, hsub, hKX.trans subset_union_left, hK, hz, fun a ha => Or.inl ?_⟩
  exact ((hK.1.joinedIn a ha z hz).mono fun x hx => ⟨hx, hKX hx⟩)

theorem isSimplyConnected_singleton (z : S) : IsSimplyConnectedSet ({z} : Set S) := by
  refine ⟨isPathConnected_singleton z, fun φ hφ => ⟨z, rfl, ⟨ContinuousMap.const _ z,
    fun _ => rfl, fun x => ?_,
    fun _ => rfl⟩⟩⟩
  exact (hφ (mem_range_self x)).symm

/-- A line is simply-connected. -/
theorem IsLine.isSimplyConnected {L : Set S} (h : IsLine L) : IsSimplyConnectedSet L := by
  obtain ⟨f⟩ := h
  have hne : L.Nonempty := ⟨(f 0).1, (f 0).2⟩
  have hc : Continuous fun t : I => (f t).1 := by fun_prop
  have hrange : L = range fun t : I => (f t).1 := by
    ext x
    constructor
    · intro hx
      exact ⟨f.symm ⟨x, hx⟩, by simp⟩
    · rintro ⟨t, rfl⟩
      exact (f t).2
  have hpc : PathConnectedSpace I :=
    have : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
    inferInstance
  refine ⟨hrange ▸ isPathConnected_range hc, fun φ hφ => ?_⟩
  let g : Circle → I := fun z => f.symm ⟨φ z, hφ (mem_range_self z)⟩
  have hg : Continuous g := by fun_prop
  refine ⟨(f 0).1, (f 0).2, ⟨⟨fun p => (f (g p.1 * σ p.2)).1, by fun_prop⟩, fun p => (f _).2,
    fun x => ?_,
    fun x => ?_⟩⟩
  · simp [g]
  · simp

/-! ## Polar charts of a drawing -/

/-- A polar chart of `Γ` at `z`: an embedded closed disc with centre `z`, around `z`, such that for
each
point of the disc other than `z`, the segment from that point towards `z` stays in one atom of `Γ`.
-/
structure IsPolar (Γ : Drawing S) (z : S) (Φ : C(ClosedUnitDisc, S)) : Prop where
  inj : Function.Injective Φ
  centre : Φ polarCentre = z
  nhd : z ∈ interior (range Φ)
  ray : ∀ x, x ≠ polarCentre → ∀ c : I, 0 < c → ∃ a ∈ Γ.A, Φ x ∈ a ∧ Φ (discScale c x) ∈ a

variable [T2Space S]

/-- The image of a set that is star-shaped about the centre is simply-connected. -/
theorem isSimplyConnected_star {Φ : C(ClosedUnitDisc, S)} (hΦ : Function.Injective Φ)
    {T : Set ClosedUnitDisc} (hT : ∀ x ∈ T, ∀ c : I, discScale c x ∈ T) (hne : T.Nonempty) :
    IsSimplyConnectedSet (Φ '' T) := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hc : polarCentre ∈ T := discScale_zero x₀ ▸ hT x₀ hx₀ 0
  have hcont : Continuous fun p : I × ClosedUnitDisc => Φ (discScale p.1 p.2) :=
    Φ.continuous.comp continuous_discScale
  refine ⟨⟨Φ polarCentre, ⟨_, hc, rfl⟩, ?_⟩, fun φ hφ => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hp : Continuous fun t : I => Φ (discScale t x) :=
      hcont.comp (Continuous.prodMk continuous_id continuous_const)
    refine ⟨⟨⟨fun t => Φ (discScale t x), hp⟩, by simp [discScale_zero],
      by simp [discScale_one]⟩, fun t => ?_⟩
    exact ⟨_, hT x hx t, rfl⟩
  · have hemb : IsEmbedding Φ := (Φ.continuous.isClosedEmbedding hΦ).isEmbedding
    have hex : ∀ z, ∃ x ∈ T, Φ x = φ z := fun z => hφ (mem_range_self z)
    choose ψ hψT hψ using hex
    have hψc : Continuous ψ := hemb.continuous_iff.mpr (by
      have : (Φ ∘ ψ) = φ := funext hψ
      rw [this]
      exact φ.continuous)
    refine ⟨Φ polarCentre, ⟨_, hc, rfl⟩, ⟨⟨fun p => Φ (discScale (σ p.2) (ψ p.1)), ?_⟩, ?_, ?_, ?_⟩⟩
    · exact hcont.comp (Continuous.prodMk (by fun_prop) (by fun_prop))
    · intro p
      exact ⟨_, hT _ (hψT _) _, rfl⟩
    · intro z
      change Φ (discScale (σ 0) (ψ z)) = φ z
      rw [unitInterval.symm_zero, discScale_one, hψ]
    · intro z
      change Φ (discScale (σ 1) (ψ z)) = Φ polarCentre
      rw [unitInterval.symm_one, discScale_zero]

omit [T2Space S] in
/-- A closed nice set contains, with each point of a polar chart, the segment to the centre. -/
theorem IsPolar.star {Γ : Drawing S} {z : S} {Φ : C(ClosedUnitDisc, S)}
  (hp : IsPolar Γ z Φ) {Z : Set S}
    (hc : IsClosed Z) (hn : IsGammaNice Γ Z) {x : ClosedUnitDisc} (hx : Φ x ∈ Z) (c : I) :
    Φ (discScale c x) ∈ Z := by
  have hpos : ∀ c : I, 0 < c → Φ (discScale c x) ∈ Z := by
    intro c hc₀
    by_cases hxc : x = polarCentre
    · have : discScale c x = x := by
        subst hxc
        exact Subtype.ext (by simp [discScale, polarCentre])
      rwa [this]
    · obtain ⟨a, ha, h₁, h₂⟩ := hp.ray x hxc c hc₀
      exact nice_atom hn ha ⟨_, h₁, hx⟩ h₂
  rcases eq_or_lt_of_le (unitInterval.nonneg c) with h0 | h0
  · have hcf : Continuous fun t : I => Φ (discScale t x) :=
      (Φ.continuous.comp continuous_discScale).comp (Continuous.prodMk continuous_id
        continuous_const)
    have hcl : IsClosed {t : I | Φ (discScale t x) ∈ Z} := hc.preimage hcf
    have hsub : Ioi (0 : I) ⊆ {t : I | Φ (discScale t x) ∈ Z} := fun t ht => hpos t ht
    have h₁ := closure_minimal hsub hcl
    rw [closure_Ioi' ⟨1, zero_lt_one⟩] at h₁
    have h₂ : c = 0 := Subtype.ext h0.symm
    rw [h₂]
    exact h₁ (mem_Ici.mpr le_rfl)
  · exact hpos c h0

theorem IsPolar.isLocalCone {Γ : Drawing S} {z : S} {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ z Φ)
    {X Y : Set S} (hX : IsClosed X) (hY : IsClosed Y) (hXn : IsGammaNice Γ X)
      (hYn : IsGammaNice Γ Y)
    (hz : z ∈ X ∪ Y) : IsLocalCone X Y z := by
  let T : Set ClosedUnitDisc := Φ ⁻¹' (X ∪ Y)
  have hT : ∀ x ∈ T, ∀ c : I, discScale c x ∈ T := by
    intro x hx c
    rcases hx with hx | hx
    · exact Or.inl (hp.star hX hXn hx c)
    · exact Or.inr (hp.star hY hYn hx c)
  have hcT : polarCentre ∈ T := by
    change Φ polarCentre ∈ X ∪ Y
    rw [hp.centre]
    exact hz
  have hzK : z ∈ Φ '' T := ⟨_, hcT, hp.centre⟩
  have hcont : Continuous fun p : I × ClosedUnitDisc => Φ (discScale p.1 p.2) :=
    Φ.continuous.comp continuous_discScale
  have hjoin : ∀ {Z : Set S}, IsClosed Z → IsGammaNice Γ Z → ∀ x ∈ T, Φ x ∈ Z →
      JoinedIn (Φ '' T ∩ Z) (Φ x) z := by
    intro Z hc hn x hx hxZ
    have hpc : Continuous fun t : I => Φ (discScale (σ t) x) :=
      hcont.comp (Continuous.prodMk (by fun_prop) continuous_const)
    refine ⟨⟨⟨fun t => Φ (discScale (σ t) x), hpc⟩, by simp [discScale_one],
      by simp [discScale_zero, hp.centre]⟩, fun t => ?_⟩
    exact ⟨⟨_, hT x hx _, rfl⟩, hp.star hc hn hxZ _⟩
  refine ⟨interior (range Φ), Φ '' T, isOpen_interior, hp.nhd, ?_, ?_,
    isSimplyConnected_star hp.inj hT ⟨_, hcT⟩,
    hzK, ?_⟩
  · rintro y ⟨hy, hyi⟩
    obtain ⟨x, rfl⟩ := interior_subset hyi
    exact ⟨x, hy, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hx
  · rintro _ ⟨x, hx, rfl⟩
    rcases id hx with hx' | hx'
    · exact Or.inl (hjoin hX hXn x hx hx')
    · exact Or.inr (hjoin hY hYn x hx hx')

/-- A fan whose sectors and spokes lie in atoms gives a polar chart. -/
theorem exists_isPolar_of_fan {H : Type*} [Finite H] [Nonempty H] (hS : IsClosedSurface S) {Γ :
  Drawing S}
    {next : H → H} {v : S} {s : H → I → S} {Q B : H → Set S} {W : Set S} {τ : H → I}
    (hf : IsFan next v s Q B W τ) (hB : ∀ k x y, x ∈ B k → y ∈ B k → ∃ a ∈ Γ.A, x ∈ a ∧ y ∈ a)
    (hs : ∀ k (t t' : I), 0 < t → t < 1 → 0 < t' → t' < 1 → ∃ a ∈ Γ.A, s k t ∈ a ∧ s k t' ∈ a) :
    ∃ Φ, IsPolar Γ v Φ := by
  obtain ⟨Φ, hΦ, hc, -, hray⟩ := exists_polar_of_fan hS hf
  refine ⟨Φ, hΦ, hc, ?_, fun x hx c hc₀ => ?_⟩
  · have hemb : IsEmbedding Φ := (Φ.continuous.isClosedEmbedding hΦ).isEmbedding
    let e : ClosedUnitDisc ≃ₜ range Φ := hemb.toHomeomorph
    have hD : IsClosedDisc (range Φ) := ⟨e⟩
    rw [interior_eq_sdiff_discBd hS hD, disc_boundary (range Φ) e]
    refine ⟨⟨_, hc⟩, ?_⟩
    rintro ⟨y, hy, hye⟩
    have hy₀ : y = polarCentre := by
      apply hΦ
      rw [hc]
      exact hye
    have : ‖y.1‖ = 1 := mem_sphere_zero_iff_norm.mp hy
    rw [hy₀] at this
    simp [polarCentre] at this
  · rcases hray x hx c hc₀ with ⟨k, h₁, h₂⟩ | ⟨k, t, t', h₁, h₂, h₃, h₄, e₁, e₂⟩
    · exact hB k _ _ h₁ h₂
    · rw [e₁, e₂]
      exact hs k t t' h₁ h₂ h₃ h₄

/-- A polar chart at a vertex with at least two half-edges. -/
theorem exists_isPolar_of_sectors (hS : IsClosedSurface S) {Γ : Drawing S} {γ : Set S → I → S}
    (hγ : EdgePar Γ γ) {v : S} (hv : v ∈ Γ.V) (h2 : 2 ≤ Nat.card (halfEdges Γ γ v)) :
    ∃ Φ, IsPolar Γ v Φ := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨next, ρ, P, W, Q, τ, hsec⟩ := exists_sectors hS Γ hγ hv h2
  have hcor := IsSectors.corners hsec
  have hfin : Finite (halfEdges Γ γ v) := (finite_halfEdges Γ γ v).to_subtype
  have hne : Nonempty (halfEdges Γ γ v) := (Finite.one_lt_card_iff_nontrivial.mp h2).to_nonempty
  have hR : ∀ k, ρ k ∈ Γ.R := IsCorners.region hcor
  have hPoff : ∀ k x, x ∈ P k → x ∉ Γ.U := fun k x hx => region_subset (hR k)
    (IsSectors.sub hsec k hx)
  have hspU : ∀ (i : halfEdges Γ γ v) (t : I), spoke γ i.1 t ∈ Γ.U := by
    intro i t
    rcases eq_or_lt_of_le (unitInterval.nonneg t) with h0 | h0
    · have : t = 0 := Subtype.ext h0.symm
      rw [this, spoke_zero, i.2.2]
      exact Γ.V_subset_U hv
    · exact (i.2.1.2.1 (spoke_mem_edge hγ i.2.1 h0)).1
  have hspV : ∀ (i : halfEdges Γ γ v), spoke γ i.1 0 = v := fun i => by
    rw [spoke_zero]
    exact i.2.2
  have hf : IsFan next v (fun i t => spoke γ i.1 t) Q P W τ := by
    refine ⟨IsCorners.inj hcor, IsCorners.reach hcor, IsSectors.next_ne hsec,
      fun k => continuous_spoke hγ k.2.1,
      fun k => spoke_injective hγ k.2.1, hspV, ?_, IsSectors.disc hsec, IsSectors.bd hsec,
      IsSectors.isOpen hsec, IsSectors.mem hsec, IsSectors.pos hsec, IsSectors.left hsec,
        IsSectors.right hsec,
      IsSectors.inside hsec, ?_, fun k i t _ h => hPoff k _ h (hspU i t)⟩
    · intro i j hij t t' ht ht' h
      by_contra ht0
      have htp : 0 < t := unitInterval.pos_iff_ne_zero.mpr ht0
      rcases eq_or_lt_of_le (unitInterval.nonneg t') with h0 | h0
      · have ht'0 : t' = 0 := Subtype.ext h0.symm
        rw [ht'0, hspV] at h
        have hv' : spoke γ i.1 t ∈ Γ.V := by rwa [h]
        exact (i.2.1.2.1 (spoke_mem_edge hγ i.2.1 htp)).2 hv'
      · have hne' : i.1 ≠ j.1 := fun e => hij (Subtype.ext e)
        exact ht.ne (spoke_eq_of_ne hγ i.2.1 j.2.1 hne' htp h0 h).1
    · intro k j hkj
      refine disjoint_left.mpr fun x hx hxQ => hPoff k x hx ?_
      exact IsSectors.inter hsec k j hkj ⟨IsSectors.subQ hsec k hx, hxQ⟩
  refine exists_isPolar_of_fan hS hf (fun k x y hx hy => ?_) fun k t t' h₁ _ h₃ _ => ?_
  · exact ⟨ρ k, Or.inr (hR k), IsSectors.sub hsec k hx, IsSectors.sub hsec k hy⟩
  · exact ⟨k.1.1, Or.inl (Or.inr k.2.1), spoke_mem_edge hγ k.2.1 h₁, spoke_mem_edge hγ k.2.1 h₃⟩

omit [T2Space S] in
/-- Two discs on the two sides of a line through `v` form a fan with two sectors. -/
private theorem isFan_bool {v : S} {f₁ f₂ : I → S} {Δ₁ Δ₂ S₁ S₂ W F : Set S} (hf₁ : IsArcMap f₁)
    (hf₂ : IsArcMap f₂) (h₁0 : f₁ 0 = v) (h₂0 : f₂ 0 = v) (hm : ∀ t t', f₁ t = f₂ t' → t = 0)
    (hm' : ∀ t t', f₂ t = f₁ t' → t = 0) (hF₁ : range f₁ ⊆ F) (hF₂ : range f₂ ⊆ F)
      (hΔ₁ : IsClosedDisc Δ₁)
    (hΔ₂ : IsClosedDisc Δ₂) (hb₁ : F ⊆ discBd Δ₁) (hb₂ : F ⊆ discBd Δ₂) (hW : IsOpen W)
      (hvW : v ∈ W)
    (hvF : v ∈ F) (hin₁ : (W ∩ Δ₁) \ discBd Δ₁ ⊆ S₁) (hin₂ : (W ∩ Δ₂) \ discBd Δ₂ ⊆ S₂)
    (hd₁ : ∀ x ∈ S₁, x ∉ Δ₂) (hd₂ : ∀ x ∈ S₂, x ∉ Δ₁) (hoff₁ : ∀ x ∈ S₁, x ∉ F)
      (hoff₂ : ∀ x ∈ S₂, x ∉ F) :
    IsFan not v (fun k => if k then f₁ else f₂) (fun k => if k then Δ₁ else Δ₂)
      (fun k => if k then S₁ else S₂) W (fun _ => 1) := by
  refine ⟨Function.Involutive.injective (fun k => by simp), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hW, hvW,
    fun _ => zero_lt_one, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    cases x <;> cases y
    · exact .refl
    · exact .single rfl
    · exact .single rfl
    · exact .refl
  · intro k
    cases k <;> simp
  · intro k
    cases k
    · exact hf₂.1
    · exact hf₁.1
  · intro k
    cases k
    · exact hf₂.2
    · exact hf₁.2
  · intro k
    cases k
    · exact h₂0
    · exact h₁0
  · intro i j hij t t' _ _ h
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hm' t t' h
    · exact hm t t' h
    · exact (hij rfl).elim
  · intro k
    cases k
    · exact hΔ₂
    · exact hΔ₁
  · intro k
    cases k
    · exact hb₂ hvF
    · exact hb₁ hvF
  · intro k t _
    cases k
    · exact hb₂ (hF₂ (mem_range_self t))
    · exact hb₁ (hF₁ (mem_range_self t))
  · intro k t _
    cases k
    · exact hb₂ (hF₁ (mem_range_self t))
    · exact hb₁ (hF₂ (mem_range_self t))
  · intro k
    cases k
    · exact hin₂
    · exact hin₁
  · intro k j hkj
    cases k <;> cases j
    · exact (hkj rfl).elim
    · exact disjoint_left.mpr hd₂
    · exact disjoint_left.mpr hd₁
    · exact (hkj rfl).elim
  · intro k i t _ h
    cases k <;> cases i
    · exact hoff₂ _ h (hF₂ (mem_range_self t))
    · exact hoff₂ _ h (hF₁ (mem_range_self t))
    · exact hoff₁ _ h (hF₂ (mem_range_self t))
    · exact hoff₁ _ h (hF₁ (mem_range_self t))

/-- A polar chart at a point of an edge. The two sides of the edge near `p` form a fan with two
sectors. -/
theorem exists_isPolar_of_edge (hS : IsClosedSurface S) (Γ : Drawing S) {e : Set S}
  (he : e ∈ Γ.E) {p : S}
    (hp : p ∈ e) : ∃ Φ, IsPolar Γ p Φ := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨γ, hγ, hγ0, hγ1, hinj, hγe⟩ := exists_edge_param Γ he
  have hX₀ := isClosed_U_sdiff_edge Γ he
  have hpX₀ : p ∉ Γ.U \ e := fun h => h.2 hp
  obtain ⟨t₀, ht₀, rfl⟩ : p ∈ γ '' Ioo 0 1 := by rw [hγe]; exact hp
  obtain ⟨D, D', a, b, hD, hD', hpD', hD'D, -, hbdD, hat', htb', hIcc, hIoo, hFline, hFD, hFcap,
    hst⟩ :=
    exists_edge_piece hS Γ he hγ hγ0 hγ1 hinj hγe ht₀ hX₀.isOpen_compl hpX₀ disjoint_compl_left
  obtain ⟨ht₀0, ht₀1⟩ := ht₀
  have hat : a ≤ t₀ := hat'.le
  have htb : t₀ ≤ b := htb'.le
  set F : Set S := γ '' Icc a b with hF
  have hFmem : ∀ x, x ∈ F ↔ ∃ t ∈ Icc a b, γ t = x := fun x => Iff.rfl
  obtain ⟨A₁, A₂, Δ₁, Δ₂, -, -, hΔ₁, hΔ₂, -, hmeet, hbd₁, hbd₂, -⟩ :=
    disc_iArc D F (γ a) (γ b) hD hFD hst hFline hFcap
  have hFe : F ⊆ e := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← hγe]
    exact ⟨t, hIcc ht, rfl⟩
  have hFU : F ⊆ Γ.U := fun x hx => (he.2.1 (hFe hx)).1
  let Y : Set S := (Γ.U \ e) ∪ γ '' {t | t ≤ a ∨ b ≤ t}
  have hY : IsClosed Y := hX₀.union ((isClosed_Iic.union isClosed_Ici).isCompact.image hγ).isClosed
  have hpY : γ t₀ ∉ Y := by
    rintro (h | ⟨t, ht, hteq⟩)
    · exact h.2 hp
    · have hpV : t ∈ Ioo (0 : unitInterval) 1 := by
        refine ⟨unitInterval.pos_iff_ne_zero.mpr ?_, unitInterval.lt_one_iff_ne_one.mpr ?_⟩
        · rintro rfl
          exact (he.2.1 hp).2 (hteq ▸ hγ0)
        · rintro rfl
          exact (he.2.1 hp).2 (hteq ▸ hγ1)
      have := hinj hpV ⟨ht₀0, ht₀1⟩ hteq
      subst this
      rcases ht with h | h
      · exact absurd h (not_le.mpr hat')
      · exact absurd h (not_le.mpr htb')
  have hpF : γ t₀ ∈ F := (hFmem _).mpr ⟨t₀, ⟨hat, htb⟩, rfl⟩
  have hFsub : ∀ x ∈ e, x ∉ Y → x ∈ F := by
    intro x hx hxY
    obtain ⟨t, -, rfl⟩ : x ∈ γ '' Ioo 0 1 := by rw [hγe]; exact hx
    refine (hFmem _).mpr ⟨t, ?_, rfl⟩
    have hn : ¬ (t ≤ a ∨ b ≤ t) := fun h => hxY (Or.inr ⟨t, h, rfl⟩)
    push Not at hn
    exact ⟨hn.1.le, hn.2.le⟩
  have side : ∀ Δ A₀ : Set S, IsClosedDisc Δ → discBd Δ = A₀ ∪ F →
      ∃ A W : Set S, IsOpen W ∧ γ t₀ ∈ W ∧ IsPreconnected A ∧ A ⊆ Δ ∧ Disjoint A Γ.U ∧
        (W ∩ Δ) \ discBd Δ ⊆ A := by
    intro Δ A₀ hΔ hbdΔ
    have hpbd : γ t₀ ∈ discBd Δ := by rw [hbdΔ]; exact Or.inr hpF
    obtain ⟨A, W, hW, hpW, hconn, hAΔ, hAbd, hAY, hin, -⟩ := exists_half_nbhd hΔ hY hpbd hpY
    refine ⟨A, W, hW, hpW, hconn, hAΔ, ?_, hin⟩
    refine disjoint_left.mpr fun x hxA hxU => ?_
    have hxY : x ∉ Y := disjoint_left.mp hAY hxA
    have hxe : x ∈ e := by
      by_contra hxe
      exact hxY (Or.inl ⟨hxU, hxe⟩)
    refine disjoint_left.mp hAbd hxA ?_
    rw [hbdΔ]
    exact Or.inr (hFsub x hxe hxY)
  obtain ⟨S₁, W₁, hW₁, hpW₁, hconn₁, hs₁, hdis₁, hin₁⟩ := side Δ₁ A₁ hΔ₁ hbd₁
  obtain ⟨S₂, W₂, hW₂, hpW₂, hconn₂, hs₂, hdis₂, hin₂⟩ := side Δ₂ A₂ hΔ₂ hbd₂
  -- The two halves of `F`, from `p`.
  have hne₁ : γ t₀ ≠ γ a := fun h => by
    have := hinj ⟨ht₀0, ht₀1⟩ (hIcc ⟨le_rfl, hat.trans htb⟩) h
    exact hat'.ne this.symm
  have hne₂ : γ t₀ ≠ γ b := fun h => by
    have := hinj ⟨ht₀0, ht₀1⟩ (hIcc ⟨hat.trans htb, le_rfl⟩) h
    exact htb'.ne this
  obtain ⟨L₁, L₂, hL₁, hL₂, hLu, hLi⟩ := IsLineWithEnds.split hFline hpF hne₁ hne₂
  obtain ⟨f₁, hf₁, hr₁, h₁0, -⟩ := (IsLineWithEnds.symm hL₁).exists_arc
  obtain ⟨f₂, hf₂, hr₂, h₂0, -⟩ := hL₂.exists_arc
  have hf₁F : range f₁ ⊆ F := fun x hx => by
    rw [← hLu]
    exact Or.inl (hr₁ ▸ hx)
  have hf₂F : range f₂ ⊆ F := fun x hx => by
    rw [← hLu]
    exact Or.inr (hr₂ ▸ hx)
  have hmf : ∀ t t', f₁ t = f₂ t' → t = 0 := by
    intro t t' h
    have hm : f₁ t ∈ L₁ ∩ L₂ := ⟨hr₁ ▸ mem_range_self t, h ▸ (hr₂ ▸ mem_range_self t' : f₂ t' ∈ L₂)⟩
    rw [hLi] at hm
    exact hf₁.2 (hm.trans h₁0.symm)
  have hmf' : ∀ t t', f₂ t = f₁ t' → t = 0 := by
    intro t t' h
    have hm : f₂ t ∈ L₁ ∩ L₂ := ⟨h ▸ (hr₁ ▸ mem_range_self t' : f₁ t' ∈ L₁), hr₂ ▸ mem_range_self t⟩
    rw [hLi] at hm
    exact hf₂.2 (hm.trans h₂0.symm)
  have hoff₁ : ∀ x ∈ S₁, x ∉ F := fun x hx hxF => disjoint_left.mp hdis₁ hx (hFU hxF)
  have hoff₂ : ∀ x ∈ S₂, x ∉ F := fun x hx hxF => disjoint_left.mp hdis₂ hx (hFU hxF)
  have hf := isFan_bool hf₁ hf₂ h₁0 h₂0 hmf hmf' hf₁F hf₂F hΔ₁ hΔ₂
    (show F ⊆ discBd Δ₁ by rw [hbd₁]; exact subset_union_right)
    (show F ⊆ discBd Δ₂ by rw [hbd₂]; exact subset_union_right) (hW₁.inter hW₂) ⟨hpW₁, hpW₂⟩ hpF
    (fun x hx => hin₁ ⟨⟨hx.1.1.1, hx.1.2⟩, hx.2⟩) (fun x hx => hin₂ ⟨⟨hx.1.1.2, hx.1.2⟩, hx.2⟩)
    (fun x hx hxΔ => hoff₁ x hx (hmeet ▸ ⟨hs₁ hx, hxΔ⟩)) (fun x hx hxΔ => hoff₂ x hx
      (hmeet ▸ ⟨hxΔ, hs₂ hx⟩))
    hoff₁ hoff₂
  have hreg : ∀ {A : Set S}, IsPreconnected A → Disjoint A Γ.U → ∀ x y, x ∈ A → y ∈ A →
      ∃ a ∈ Γ.A, x ∈ a ∧ y ∈ a := by
    intro A hA hdis x y hx hy
    obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem (disjoint_left.mp hdis hx)
    exact ⟨r, Or.inr hr, hxr, subset_region hr hA hdis hx hxr hy⟩
  refine exists_isPolar_of_fan hS hf (fun k x y => ?_) fun k t t' _ _ _ _ => ?_
  · cases k
    · exact hreg hconn₂ hdis₂ x y
    · exact hreg hconn₁ hdis₁ x y
  · refine ⟨e, Or.inl (Or.inr he), ?_, ?_⟩ <;> cases k
    · exact hFe (hf₂F (mem_range_self t))
    · exact hFe (hf₁F (mem_range_self t))
    · exact hFe (hf₂F (mem_range_self t'))
    · exact hFe (hf₁F (mem_range_self t'))

omit [T2Space S] in
/-- If a neighbourhood `Z` of `z` lies in the closure of a set `r ⊆ X`, then `z` is a cone point. -/
private theorem cone_of_region (hS : IsClosedSurface S) {X Y Z : Set S} {z : S} {r : Set S}
    (hr : r ⊆ X) (hX : IsClosed X) (hZ : IsOpen Z) (hzZ : z ∈ Z) (hZr : Z ⊆ closure r) :
    IsLocalCone X Y z := by
  obtain ⟨D, D', hD, hD', hzD', hD'D, hDZ, -⟩ := exists_closedDisc_nbhd hS hZ hzZ
  have hDX : D ⊆ X := hDZ.trans (hZr.trans (closure_minimal hr hX))
  exact isLocalCone_of_subset (IsClosedDisc.isSimplyConnectedSet hD) hDX (hD'D hzD') hD' hzD'
    fun y hy => hD'D hy.2

/-- **Closed nice sets are cones.** -/
theorem isLocalCone [ConnectedSpace S] (hS : IsClosedSurface S) {Γ : Drawing S} {X Y : Set S}
    (hX : IsClosed X) (hY : IsClosed Y) (hXn : IsGammaNice Γ X) (hYn : IsGammaNice Γ Y) {z : S}
    (hz : z ∈ X ∪ Y) : IsLocalCone X Y z := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hne : Nonempty S := ⟨z⟩
  by_cases hzV : z ∈ Γ.V
  · obtain ⟨γ, hγ⟩ := exists_edgePar Γ
    by_cases h2 : 2 ≤ Nat.card (halfEdges Γ γ z)
    · obtain ⟨Φ, hΦ⟩ := exists_isPolar_of_sectors hS hγ hzV h2
      exact hΦ.isLocalCone hX hY hXn hYn hz
    -- A region near `z`.
    obtain ⟨r, hr, hzr⟩ : ∃ r ∈ Γ.R, z ∈ closure r := by
      have hfin := finite_R hS Γ
      have hd : z ∈ closure (⋃ r ∈ Γ.R, r) := mem_closure_iff.mpr fun O hO hzO => by
        obtain ⟨y, hyO, hyU⟩ := exists_notMem_U (Γ := Γ) hS hO ⟨z, hzO⟩
        obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem hyU
        exact ⟨y, hyO, mem_iUnion₂.mpr ⟨r, hr, hyr⟩⟩
      rw [hfin.closure_biUnion] at hd
      obtain ⟨r, hr, hzr⟩ := mem_iUnion₂.mp hd
      exact ⟨r, hr, hzr⟩
    obtain ⟨Z, hZ, hzZ, hZr⟩ := exists_nbhd_of_few hS hγ hzV h2 hr hzr
    have hrA : r ∈ Γ.A := Or.inr hr
    by_cases hrX : (r ∩ X).Nonempty
    · exact cone_of_region hS (nice_atom hXn hrA hrX) hX hZ hzZ hZr
    by_cases hrY : (r ∩ Y).Nonempty
    · exact (cone_of_region hS (nice_atom hYn hrA hrY) hY hZ hzZ hZr).symm
    have hoff : ∀ y ∈ Z, y ∈ X ∪ Y → y ∈ Γ.U := by
      intro y hyZ hy
      rcases closure_region_subset hr (hZr hyZ) with h | h
      · rcases hy with h' | h'
        · exact (hrX ⟨y, h, h'⟩).elim
        · exact (hrY ⟨y, h, h'⟩).elim
      · exact h
    have hpoint : ∀ {T : Set S}, IsClosed T → z ∉ T → (∀ y ∈ Z \ T, y ∈ X ∪ Y → y = z) →
        IsLocalCone X Y z := by
      intro T hT hzT hy
      have hsub : (X ∪ Y) ∩ (Z \ T) ⊆ {z} := fun y h => hy y h.2 h.1
      rcases hz with h | h
      · exact isLocalCone_of_subset (isSimplyConnected_singleton z) (singleton_subset_iff.mpr h) rfl
          (hZ.sdiff hT) ⟨hzZ, hzT⟩ hsub
      · exact (isLocalCone_of_subset (Y := X) (isSimplyConnected_singleton z)
          (singleton_subset_iff.mpr h)
          rfl (hZ.sdiff hT) ⟨hzZ, hzT⟩ (by rwa [union_comm])).symm
    have hfinH : Finite (halfEdges Γ γ z) := (finite_halfEdges Γ γ z).to_subtype
    have hss : Subsingleton (halfEdges Γ γ z) := Finite.card_le_one_iff_subsingleton.mp (by omega)
    rcases isEmpty_or_nonempty (halfEdges Γ γ z) with h0 | ⟨⟨k⟩⟩
    · have hno : ∀ g ∈ Γ.E, z ∉ closure g := by
        intro g hg hzg
        obtain ⟨b, hb⟩ := exists_end_eq hγ hg hzV hzg
        exact h0.false ⟨(g, b), hg, hb⟩
      let T : Set S := (Γ.V \ {z}) ∪ ⋃ g ∈ Γ.E, closure g
      have hT : IsClosed T := (Γ.finite_V.subset sdiff_subset).isClosed.union
        (Γ.finite_edges.isClosed_biUnion fun _ _ => isClosed_closure)
      have hzT : z ∉ T := by
        rintro (h | h)
        · exact h.2 rfl
        · obtain ⟨g, hg, hzg⟩ := mem_iUnion₂.mp h
          exact hno g hg hzg
      refine hpoint hT hzT fun y hy hyU => ?_
      have hyU' := hoff y hy.1 hyU
      rw [Γ.U_eq] at hyU'
      rcases hyU' with h | h
      · by_contra hyz
        exact hy.2 (Or.inl ⟨h, hyz⟩)
      · exact (hy.2 (Or.inr h)).elim
    · obtain ⟨⟨e, b⟩, he, hb⟩ := k
      let T : Set S := (Γ.V \ {z}) ∪ ⋃ g ∈ Γ.E \ {e}, closure g
      have hT : IsClosed T := (Γ.finite_V.subset sdiff_subset).isClosed.union
        ((Γ.finite_edges.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure)
      have hzT : z ∉ T := by
        rintro (h | h)
        · exact h.2 rfl
        · obtain ⟨g, hg, hzg⟩ := mem_iUnion₂.mp h
          obtain ⟨b', hb'⟩ := exists_end_eq hγ hg.1 hzV hzg
          have := congrArg (fun k : halfEdges Γ γ z => k.1.1)
            (hss.elim ⟨(g, b'), hg.1, hb'⟩ ⟨(e, b), he, hb⟩)
          exact hg.2 this
      have hin : ∀ y ∈ Z \ T, y ∈ X ∪ Y → y = z ∨ y ∈ e := by
        intro y hy hyU
        have hyU' := hoff y hy.1 hyU
        by_cases hyV : y ∈ Γ.V
        · left
          by_contra hyz
          exact hy.2 (Or.inl ⟨hyV, hyz⟩)
        · obtain ⟨g, hg, hyg⟩ := Γ.exists_edge_of_mem hyU' hyV
          right
          by_cases hge : g = e
          · exact hge ▸ hyg
          · exact (hy.2 (Or.inr (mem_iUnion₂.mpr ⟨g, ⟨hg, hge⟩, subset_closure hyg⟩))).elim
      have hzcl : z ∈ closure e := by
        have := end_mem_closure hγ he b
        rwa [hb] at this
      have hline : IsLine (closure e) := by
        rcases Γ.edge_cond e he with ⟨u, v, -, -, hl⟩ | ⟨u, hu, -⟩
        · obtain ⟨f, -, -⟩ := hl
          exact ⟨f⟩
        · exfalso
          have hend : ∀ c, γ e (endOf c) = z := by
            intro c
            have h₁ : γ e (endOf c) ∈ closure e ∩ Γ.V := by
              refine ⟨end_mem_closure hγ he c, ?_⟩
              cases c
              · exact hγ.zero e he
              · exact hγ.one e he
            have h₂ : z ∈ closure e ∩ Γ.V := ⟨hzcl, hzV⟩
            rw [hu] at h₁ h₂
            exact h₁.trans h₂.symm
          have := congrArg (fun k : halfEdges Γ γ z => k.1.2)
            (hss.elim ⟨(e, true), he, hend true⟩ ⟨(e, false), he, hend false⟩)
          simp at this
      have heA : e ∈ Γ.A := Or.inl (Or.inr he)
      have hsub : ∀ {X' Y' : Set S}, X ∪ Y = X' ∪ Y' → (X' ∪ Y') ∩ (Z \ T) ⊆ closure e := by
        intro X' Y' h y hy
        rw [← h] at hy
        rcases hin y hy.2 hy.1 with rfl | h'
        · exact hzcl
        · exact subset_closure h'
      by_cases heX : (e ∩ X).Nonempty
      · have hclX : closure e ⊆ X := closure_minimal (nice_atom hXn heA heX) hX
        exact isLocalCone_of_subset (IsLine.isSimplyConnected hline) hclX hzcl
          (hZ.sdiff hT) ⟨hzZ, hzT⟩
          (hsub rfl)
      by_cases heY : (e ∩ Y).Nonempty
      · have hclY : closure e ⊆ Y := closure_minimal (nice_atom hYn heA heY) hY
        exact (isLocalCone_of_subset (IsLine.isSimplyConnected hline) hclY hzcl
          (hZ.sdiff hT) ⟨hzZ, hzT⟩
          (hsub (union_comm X Y))).symm
      refine hpoint hT hzT fun y hy hyU => ?_
      rcases hin y hy hyU with h | h
      · exact h
      · rcases hyU with h' | h'
        · exact (heX ⟨y, h, h'⟩).elim
        · exact (heY ⟨y, h, h'⟩).elim
  by_cases hzU : z ∈ Γ.U
  · obtain ⟨e, he, hze⟩ := Γ.exists_edge_of_mem hzU hzV
    obtain ⟨Φ, hΦ⟩ := exists_isPolar_of_edge hS Γ he hze
    exact hΦ.isLocalCone hX hY hXn hYn hz
  · obtain ⟨r, hr, hzr⟩ := exists_region_of_notMem hzU
    have hrA : r ∈ Γ.A := Or.inr hr
    have hZ := region_isOpen hr
    rcases hz with h | h
    · exact cone_of_region hS (nice_atom hXn hrA ⟨z, hzr, h⟩) hX hZ hzr subset_closure
    · exact (cone_of_region hS (nice_atom hYn hrA ⟨z, hzr, h⟩) hY hZ hzr subset_closure).symm

end GraphMinor.GM11
