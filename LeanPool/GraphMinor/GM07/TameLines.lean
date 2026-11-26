/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.TameDisc
public import LeanPool.GraphMinor.GM07.SplitForest
public import LeanPool.GraphMinor.GM07.JoinDiscs

/-!
# How an edge leaves a disc around its end

Let `R` be a star disc at an end of an edge, and let `γ` be a parametrization of the edge. The edge
leaves `R` once, and it does not come back, except at its other
end if that end is the same vertex. So the edge is cut by the boundaries of the discs around its
ends into three pieces, and the middle one is a line that the tools
of `GM07.TameDisc` can absorb.
-/

public section

namespace GraphMinor.GM07

open Set Topology Metric Function GraphMinor.Surface GraphMinor.GM11

local notation "I" => unitInterval

variable {T : Type} [TopologicalSpace T] [T2Space T] {H : Drawing T} {f : Set T} {γ : I → T}

/-- A connected part of the closure of an edge that holds an end and an inner point holds one of the
two ways from one to the other. -/
theorem EdgeParam.arc_of_preconnected (h : EdgeParam H f γ) (hf : f ∈ H.E) {C : Set T}
  (hC : IsPreconnected C) (hsub : C ⊆ range γ) (h0 : γ 0 ∈ C) {τ : I}
    (hy : γ τ ∈ C) : γ '' Icc 0 τ ⊆ C ∨ γ '' Icc τ 1 ⊆ C := by
  by_contra hn
  push Not at hn
  obtain ⟨hn1, hn2⟩ := hn
  obtain ⟨_, ⟨a, ha, rfl⟩, haC⟩ := not_subset.mp hn1
  obtain ⟨_, ⟨b, hb, rfl⟩, hbC⟩ := not_subset.mp hn2
  have hat : a < τ := lt_of_le_of_ne ha.2 fun e => haC (e ▸ hy)
  have htb : τ < b := lt_of_le_of_ne hb.1 fun e => hbC (e ▸ hy)
  have hcl : ∀ u v : I, IsClosed (γ '' Icc u v) := fun u v => (isCompact_Icc.image h.cont).isClosed
  have hcov : C ⊆ γ '' Icc a b ∪ (γ '' Icc 0 a ∪ γ '' Icc b 1) := fun x hx => by
    obtain ⟨z, rfl⟩ := hsub hx
    by_cases h1 : z ≤ a
    · exact .inr (.inl ⟨z, ⟨unitInterval.nonneg z, h1⟩, rfl⟩)
    by_cases h2 : b ≤ z
    · exact .inr (.inr ⟨z, ⟨h2, unitInterval.le_one z⟩, rfl⟩)
    · exact .inl ⟨z, ⟨le_of_not_ge h1, le_of_not_ge h2⟩, rfl⟩
  obtain ⟨z, hz, ⟨p, hp, rfl⟩, hz2⟩ := isPreconnected_closed_iff.mp hC _ _ (hcl a b)
    ((hcl 0 a).union (hcl b 1)) hcov
    ⟨_, hy, τ, ⟨hat.le, htb.le⟩, rfl⟩ ⟨_, h0, .inl ⟨0, ⟨le_rfl, unitInterval.nonneg a⟩, rfl⟩⟩
  have hpa : a < p := lt_of_le_of_ne hp.1 fun e => haC (e ▸ hz)
  have hpb : p < b := lt_of_le_of_ne hp.2 fun e => hbC (e ▸ hz)
  have hp0 : 0 < p := lt_of_le_of_lt (unitInterval.nonneg a) hpa
  have hp1 : p < 1 := lt_of_lt_of_le hpb (unitInterval.le_one b)
  have hq : ∃ q, γ q = γ p ∧ (q ≤ a ∨ b ≤ q) := by
    rcases hz2 with ⟨q, hq, he⟩ | ⟨q, hq, he⟩
    · exact ⟨q, he, .inl hq.2⟩
    · exact ⟨q, he, .inr hq.1⟩
  obtain ⟨q, he, hqc⟩ := hq
  have hqV := (h.pos_of_ne (y := q) (he ▸ h.not_V hf hp0 hp1))
  have := h.inj ⟨hqV.1, hqV.2⟩ ⟨hp0, hp1⟩ he
  subst this
  rcases hqc with h1 | h1
  · exact absurd h1 (not_le.mpr hpa)
  · exact absurd h1 (not_le.mpr hpb)

/-- The first time a path from inside a disc reaches its boundary. -/
theorem exists_first_exit {R : Set T} {γ : I → T} (hc : Continuous γ) (hR : IsClosedDisc R)
  (hint : IsOpen (discInt R)) (h0 : γ 0 ∈ discInt R) {z : I} (hz : γ z ∉ R) :
    ∃ s, 0 < s ∧ s < z ∧ γ s ∈ discBd R ∧ ∀ τ < s, γ τ ∈ discInt R := by
  have hA : IsClosed {τ | γ τ ∉ discInt R} := (hint.preimage hc).isClosed_compl
  have hzA : z ∈ {τ | γ τ ∉ discInt R} := fun h => hz h.1
  obtain ⟨s, hs, hl⟩ := hA.isCompact.exists_isLeast ⟨z, hzA⟩
  have h0s : 0 < s := unitInterval.pos_iff_ne_zero.mpr fun e => hs (e ▸ h0)
  have hpre : ∀ τ < s, γ τ ∈ discInt R := fun τ hτ => by
    by_contra hn
    exact absurd (hl hn) (not_le.mpr hτ)
  have hsR : γ s ∈ R := by
    have h1 : s ∈ closure (Iio s) := by
      have hne : (Iio s).Nonempty := ⟨0, h0s⟩
      rw [closure_Iio' hne]
      exact le_refl s
    have h2 := image_closure_subset_closure_image hc ⟨s, h1, rfl⟩
    refine closure_minimal ?_ hR.isClosed h2
    rintro _ ⟨τ, hτ, rfl⟩
    exact (hpre τ hτ).1
  refine ⟨s, h0s, lt_of_le_of_ne (hl hzA) fun e => hz (e ▸ hsR), ?_, hpre⟩
  by_contra hn
  exact hs ⟨hsR, hn⟩

/-- After it leaves a star disc at `γ 0`, an edge comes back only at the place `t`, where it reaches
the boundary from the other side, or not at all if its other end
is outside the disc. -/
theorem EdgeParam.no_return (h : EdgeParam H f γ) (hf : f ∈ H.E) {R : Set T}
  (hstar : ∀ y ∈ R ∩ range γ, ∃ C, IsPreconnected C ∧ C ⊆ range γ ∧ y ∈ C ∧ γ 0 ∈ C
    ∧ C \ {y} ⊆ discInt R)
    {s t : I} (hs : 0 < s) (hsb : γ s ∈ discBd R) (hend : γ 1 ∉ R ∨ t < 1 ∧ γ t ∈ discBd R) {τ : I}
      (hsτ : s < τ) (hτt : τ < t) : γ τ ∉ R := by
  intro hy
  have hτ0 : 0 < τ := hs.trans hsτ
  have hτ1 : τ < 1 := lt_of_lt_of_le hτt (unitInterval.le_one t)
  have hbad : ∀ q, 0 < q → q < 1 → q ≠ τ → γ q ≠ γ τ := fun q h1 h2 h3 he => h3
    (h.inj ⟨h1, h2⟩ ⟨hτ0, hτ1⟩ he)
  have hnotbd : ∀ x, x ∈ discInt R → x ∉ discBd R := fun x h1 => h1.2
  obtain ⟨C, hC, hsub, hyC, h0, hin⟩ := hstar _ ⟨hy, mem_range_self τ⟩
  have hs1 : s < 1 := hsτ.trans hτ1
  rcases h.arc_of_preconnected hf hC hsub h0 hyC with h1 | h1
  · exact hnotbd _ (hin ⟨h1 ⟨s, ⟨hs.le, hsτ.le⟩, rfl⟩, hbad s hs hs1 hsτ.ne⟩) hsb
  · rcases hend with h2 | ⟨h2, h3⟩
    · have h4 : γ 1 ≠ γ τ := fun e => h.not_V hf hτ0 hτ1 (e ▸ h.mem1)
      exact h2 (hin ⟨h1 ⟨1, ⟨hτ1.le, le_rfl⟩, rfl⟩, h4⟩).1
    · have ht0 := hτ0.trans hτt
      exact hnotbd _ (hin ⟨h1 ⟨t, ⟨hτt.le, unitInterval.le_one t⟩, rfl⟩, hbad t ht0 h2 hτt.ne'⟩) h3

/-- A piece of an edge is a line. -/
theorem EdgeParam.line_Icc (h : EdgeParam H f γ) (hf : f ∈ H.E) {s t : I} (hs : 0 < s)
  (hst : s < t) : IsLineWithEnds (γ '' Icc s t) (γ s) (γ t) := by
  have ha : IsArcMap (subArc γ s t) := by
    refine ⟨h.cont.comp (continuous_lerpI _ _), ?_⟩
    intro x y he
    have hm : ∀ z, lerpI s t z ∈ Icc s t := fun z => by
      rw [← range_lerpI hst.le]
      exact mem_range_self z
    have hin : ∀ q ∈ Icc s t, q < 1 ∨ q = 1 := fun q _ => lt_or_eq_of_le (unitInterval.le_one q)
    refine lerpI_injective hst.ne ?_
    replace he : γ (lerpI s t x) = γ (lerpI s t y) := he
    have hx := hm x
    have hy := hm y
    have hs0 : ∀ q ∈ Icc s t, 0 < q := fun q hq => hs.trans_le hq.1
    rcases hin _ hx with h1 | h1
    · rcases hin _ hy with h2 | h2
      · exact h.inj ⟨hs0 _ hx, h1⟩ ⟨hs0 _ hy, h2⟩ he
      · rw [h2] at he
        exact absurd h.mem1 (he ▸ h.not_V hf (hs0 _ hx) h1)
    · rcases hin _ hy with h2 | h2
      · rw [h1] at he
        exact absurd h.mem1 (he.symm ▸ h.not_V hf (hs0 _ hy) h2)
      · rw [h1, h2]
  have := isLineWithEnds_range_of_arc ha
  rwa [range_subArc _ hst.le, subArc_zero, subArc_one] at this

/-- **A chord of a star disc along a curve.** If `R` is a star disc at a point `v` of the `O`-arc
`C`, and `C` is not inside `R`, then `R ∩ C` is a chord of `R` through `v`. -/
theorem exists_star_chord {C R : Set T} {v z : T} (hC : IsOArc C) (hv : v ∈ C)
  (hR : IsClosedDisc R) (hint : IsOpen (discInt R)) (hvR : v ∈ discInt R) (hz : z ∈ C) (hzR : z ∉ R)
    (hstar : ∀ y ∈ R ∩ C, ∃ C', IsPreconnected C' ∧ C' ⊆ C ∧ y ∈ C' ∧ v ∈ C'
      ∧ C' \ {y} ⊆ discInt R) :
    ∃ F y₁ y₂, IsLineWithEnds F y₁ y₂ ∧ y₁ ≠ y₂ ∧ F ⊆ R ∧ F ∩ discBd R = {y₁, y₂} ∧ R ∩ C = F
      ∧ v ∈ F := by
  obtain ⟨ι, hιc, h0, h1, hi0, hi1, him⟩ := hC.exists_iota hv
  obtain ⟨D, hDU, hDV⟩ := exists_loop_drawing hC hv
  set γ : I → T := fun t => ι t with hγdef
  have hvD : v ∈ D.V := hDV ▸ mem_singleton v
  have hIoo : γ '' Ioo 0 1 = C \ {v} := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      have h2 : (0 : ℝ) < t := ht.1
      have h3 : (t : ℝ) < 1 := ht.2
      refine ⟨him ▸ mem_image_of_mem ι ⟨h2.le, h3⟩, fun e => ?_⟩
      have h4 : ι t = ι 0 := by rw [h0]; exact e
      exact h2.ne' (hi0 ⟨h2.le, h3⟩ ⟨le_rfl, one_pos⟩ h4)
    · rintro ⟨hx, hxv⟩
      rw [← him] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      have hr0 : 0 < r := lt_of_le_of_ne hr.1 fun e => hxv (by rw [← e]; exact h0)
      exact ⟨⟨r, hr.1, hr.2.le⟩, ⟨hr0, hr.2⟩, rfl⟩
  have hγ : EdgeParam D (C \ {v}) γ := by
    refine ⟨hιc.comp continuous_subtype_val, ?_, ?_, ?_, hIoo⟩
    · change ι 0 ∈ D.V
      rwa [h0]
    · change ι 1 ∈ D.V
      rwa [h1]
    · intro a ha b hb he
      have ha0 : (0 : ℝ) ≤ a := a.2.1
      have hb0 : (0 : ℝ) ≤ b := b.2.1
      exact Subtype.ext (hi0 ⟨ha0, ha.2⟩ ⟨hb0, hb.2⟩ he)
  have hf : C \ {v} ∈ D.E := by
    have hpc : IsPathConnected (C \ {v}) := by
      rw [← hIoo]
      exact hγ.isPathConnected_Ioo zero_lt_one
    have hE : D.U \ D.V = C \ {v} := by rw [hDU, hDV]
    change C \ {v} ∈ arcComponentsIn (D.U \ D.V)
    rw [hE]
    exact ⟨hpc.nonempty, Subset.rfl, hpc, fun E h1 _ h3 => Subset.antisymm h1 h3⟩
  have hrange : range γ = C := by
    apply Subset.antisymm
    · rintro _ ⟨t, rfl⟩
      by_cases h2 : t = 1
      · subst h2
        change ι 1 ∈ C
        rwa [h1]
      · exact him ▸ mem_image_of_mem ι ⟨t.2.1, lt_of_le_of_ne t.2.2 fun e => h2 (Subtype.ext e)⟩
    · intro x hx
      rw [← him] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      exact ⟨⟨r, hr.1, hr.2.le⟩, rfl⟩
  have hv0 : γ 0 = v := h0
  have hv1 : γ 1 = v := h1
  obtain ⟨m, rfl⟩ : ∃ m, γ m = z := by
    have : z ∈ range γ := hrange ▸ hz
    exact this
  have hmv : γ m ∉ D.V := fun h => by
    rw [hDV] at h
    exact hzR (h ▸ hvR.1)
  obtain ⟨hm0, hm1⟩ := hγ.pos_of_ne hmv
  obtain ⟨s, hs0, hsm, hsb, hspre⟩ := exists_first_exit hγ.cont hR hint (hv0.symm ▸ hvR) hzR
  have hγ' := hγ.rev
  have hσ : ∀ x : I, (γ ∘ unitInterval.symm) (unitInterval.symm x) = γ x := fun x => by simp
  obtain ⟨t', ht0, htm, htb, htpre⟩ := exists_first_exit (z := unitInterval.symm m) hγ'.cont hR
    hint (by simpa [hv1] using hvR) (by simpa using hzR)
  set t := unitInterval.symm t' with ht
  have hγt : γ t = (γ ∘ unitInterval.symm) t' := rfl
  have hmt : m < t := by
    have := unitInterval.symm_lt_symm.mpr htm
    simpa [ht] using this
  have ht1 : t < 1 := by
    have := unitInterval.symm_lt_symm.mpr ht0
    simpa [ht] using this
  have hs1 : s < 1 := hsm.trans hm1
  have hst : s < t := hsm.trans hmt
  have hL₁ := hγ.line hf hs0 hs1
  have ht'1 : t' < 1 := htm.trans_le (unitInterval.le_one _)
  have hL₂ := hγ'.line hf ht0 ht'1
  rw [hv0] at hL₁
  have hv' : (γ ∘ unitInterval.symm) 0 = v := by simpa using hv1
  rw [hv'] at hL₂
  have hL₂eq : (γ ∘ unitInterval.symm) '' Icc 0 t' = γ '' Icc t 1 := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      refine ⟨unitInterval.symm r, ⟨?_, unitInterval.le_one _⟩, rfl⟩
      exact unitInterval.symm_le_symm.mpr hr.2
    · rintro ⟨r, hr, rfl⟩
      refine ⟨unitInterval.symm r, ⟨unitInterval.nonneg _, ?_⟩, by simp⟩
      have := unitInterval.symm_le_symm.mpr hr.1
      simpa [ht] using this
  rw [hL₂eq] at hL₂
  have hmeet : γ '' Icc 0 s ∩ γ '' Icc t 1 = {v} := by
    apply Subset.antisymm
    · rintro _ ⟨⟨a, ha, rfl⟩, b, hb, he⟩
      have hat : a < b := lt_of_le_of_lt ha.2 (hst.trans_le hb.1)
      by_cases ha0 : a = 0
      · rw [ha0]; exact hv0
      by_cases hb1 : b = 1
      · have h2 : 0 < a := unitInterval.pos_iff_ne_zero.mpr ha0
        rw [hb1] at he
        exact absurd hγ.mem1 (he ▸ hγ.not_V hf h2 (ha.2.trans_lt hs1))
      · exact absurd (hγ.inj ⟨unitInterval.pos_iff_ne_zero.mpr ha0, ha.2.trans_lt hs1⟩
          ⟨lt_of_le_of_lt (unitInterval.nonneg a) hat, unitInterval.lt_one_iff_ne_one.mpr hb1⟩
            he.symm) hat.ne
    · rintro x rfl
      exact ⟨⟨0, ⟨le_rfl, hs0.le⟩, hv0⟩, 1, ⟨ht1.le, le_rfl⟩, hv1⟩
  have hsint : ∀ a ∈ Icc 0 s, γ a ∈ R := fun a ha => by
    rcases ha.2.lt_or_eq with h | rfl
    · exact (hspre a h).1
    · exact GM11.discBd_subset R hsb
  have htb' : γ t ∈ discBd R := htb
  have htint : ∀ a ∈ Icc t 1, γ a ∈ R := fun a ha => by
    have h2 : unitInterval.symm a ≤ t' := by
      have := unitInterval.symm_le_symm.mpr ha.1
      simpa [ht] using this
    have h3 : γ a = (γ ∘ unitInterval.symm) (unitInterval.symm a) := by simp
    rcases h2.lt_or_eq with h | h
    · rw [h3]
      exact (htpre _ h).1
    · rw [h3, h]
      exact GM11.discBd_subset R htb
  refine ⟨γ '' Icc 0 s ∪ γ '' Icc t 1, γ s, γ t, GM11.IsLineWithEnds.union hL₁ hL₂ hmeet, fun e
    => hst.ne (hγ.inj ⟨hs0, hs1⟩ ⟨hs0.trans hst, ht1⟩ e), ?_, ?_, ?_, .inl ⟨0, ⟨le_rfl, hs0.le⟩,
      hv0⟩⟩
  · exact union_subset (image_subset_iff.mpr hsint) (image_subset_iff.mpr htint)
  · apply Subset.antisymm
    · rintro x ⟨⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩, hb⟩
      · rcases ha.2.lt_or_eq with h | rfl
        · exact absurd hb (hspre a h).2
        · exact .inl rfl
      · rcases ha.1.lt_or_eq with h | rfl
        · have h2 : unitInterval.symm a < t' := by
            have := unitInterval.symm_lt_symm.mpr h
            simpa [ht] using this
          have h3 := htpre _ h2
          simp only [comp_apply, unitInterval.symm_symm] at h3
          exact absurd hb h3.2
        · exact .inr rfl
    · rintro x (rfl | rfl)
      · exact ⟨.inl ⟨s, ⟨hs0.le, le_rfl⟩, rfl⟩, hsb⟩
      · exact ⟨.inr ⟨t, ⟨le_rfl, ht1.le⟩, rfl⟩, htb⟩
  · apply Subset.antisymm
    · rintro x ⟨hx, hxC⟩
      rw [← hrange] at hxC
      obtain ⟨τ, rfl⟩ := hxC
      by_cases h2 : τ ≤ s
      · exact .inl ⟨τ, ⟨unitInterval.nonneg τ, h2⟩, rfl⟩
      by_cases h3 : t ≤ τ
      · exact .inr ⟨τ, ⟨h3, unitInterval.le_one τ⟩, rfl⟩
      · exact absurd hx (hγ.no_return hf (fun y hy => by
          obtain ⟨C', h4, h5, h6, h7, h8⟩ := hstar y ⟨hy.1, hrange ▸ hy.2⟩
          exact ⟨C', h4, hrange.symm ▸ h5, h6, hv0.symm ▸ h7, h8⟩) hs0 hsb (.inr ⟨ht1,
            htb'⟩) (not_le.mp h2) (not_le.mp h3))
    · rintro x (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
      · exact ⟨hsint a ha, hrange ▸ mem_range_self a⟩
      · exact ⟨htint a ha, hrange ▸ mem_range_self a⟩

/-- Adding to a disc `B` a disc `R` that meets its boundary in a chord of `R`. -/
theorem exists_half_union (hS : IsClosedSurface T) {B R F : Set T} {y₁ y₂ v : T}
  (hB : IsClosedDisc B) (hR : IsClosedDisc R) (hF : IsLineWithEnds F y₁ y₂) (hne : y₁ ≠ y₂)
    (hFR : F ⊆ R)
    (hb : F ∩ discBd R = {y₁, y₂}) (hRB : R ∩ discBd B = F) (hv : v ∈ F) (hvR : v ∈ discInt R) :
    IsClosedDisc (B ∪ R) ∧ discBd (B ∪ R) ⊆ discBd B ∪ discBd R ∧ Disjoint (discBd (B ∪ R))
      (discInt R) ∧ discBd B \ R ⊆ discBd (B ∪ R) ∧ discBd R \ B ⊆ discBd (B ∪ R) := by
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hfr := IsClosedDisc.frontier_eq_discBd hS hB
  have hBc := hB.isClosed
  have hFB : F ⊆ discBd B := hRB ▸ inter_subset_right
  have hvB : v ∈ discBd B := hFB hv
  have hint := hR.isOpen_discInt hman
  have hintB := hB.isOpen_discInt hman
  obtain ⟨Δ₁, Δ₂, A₁, A₂, l₁, l₂, hun, hin, d₁, d₂, hcup, hcap, b₁, b₂, p₁, p₂⟩
    := disc_split hR hFR hne hF hb
  -- A point near `v` outside `B`, and one inside.
  obtain ⟨p, hpR, hpB⟩ : ∃ p ∈ discInt R, p ∉ B := by
    have h1 : v ∈ closure Bᶜ := by
      have : v ∈ frontier B := hfr ▸ hvB
      rw [frontier_eq_closure_inter_closure] at this
      exact this.2
    obtain ⟨p, h2, h3⟩ := mem_closure_iff.mp h1 _ hint hvR
    exact ⟨p, h2, h3⟩
  obtain ⟨q, hqR, hqB⟩ : ∃ q ∈ discInt R, q ∈ discInt B := by
    obtain ⟨q, h2, h3⟩ := mem_closure_iff.mp (hB.subset_closure_discInt
      (GM11.discBd_subset B hvB)) _ hint hvR
    exact ⟨q, h2, h3⟩
  have hqIn : q ∈ interior B := interior_maximal (discInt_subset B) hintB hqB
  have hside : ∀ {E : Set T}, IsPreconnected (E \ F) → E ⊆ R → E \ F ⊆ interior B ∨ E \ F ⊆ Bᶜ
    := fun {E} h1 h2 => by
    refine inside_or_outside h1 hBc (disjoint_left.mpr fun x hx hxf => ?_)
    rw [hfr] at hxf
    exact hx.2 (hRB ▸ ⟨h2 hx.1, hxf⟩)
  wlog hpΔ : p ∈ Δ₁ generalizing Δ₁ Δ₂ A₁ A₂
  · have hp2 : p ∈ Δ₂ := by
      have : p ∈ Δ₁ ∪ Δ₂ := hcup ▸ hpR.1
      exact this.resolve_left hpΔ
    exact this Δ₂ Δ₁ A₂ A₁ l₂ l₁ (by rw [union_comm]; exact hun)
      (by rw [inter_comm]; exact hin) d₂ d₁ (by rw [union_comm]; exact hcup)
      (by rw [inter_comm]; exact hcap) b₂ b₁ p₂ p₁ hp2
  have hsub₁ : Δ₁ ⊆ R := hcup ▸ subset_union_left
  have hsub₂ : Δ₂ ⊆ R := hcup ▸ subset_union_right
  have hqF : q ∉ F := fun h => (hqB.2 (hFB h))
  have hs₁ : Δ₁ \ F ⊆ Bᶜ := by
    rcases hside p₁ hsub₁ with h | h
    · exact absurd (interior_subset (h ⟨hpΔ, fun hf => hpB (GM11.discBd_subset B (hFB hf))⟩)) hpB
    · exact h
  have hqΔ₂ : q ∈ Δ₂ := by
    have : q ∈ Δ₁ ∪ Δ₂ := hcup ▸ hqR.1
    refine this.resolve_left fun h => hs₁ ⟨h, hqF⟩ hqB.1
  have hs₂ : Δ₂ \ F ⊆ interior B := by
    rcases hside p₂ hsub₂ with h | h
    · exact h
    · exact absurd hqB.1 (h ⟨hqΔ₂, hqF⟩)
  have hΔ₂B : Δ₂ ⊆ B := fun x hx => by
    by_cases h : x ∈ F
    · exact GM11.discBd_subset B (hFB h)
    · exact interior_subset (hs₂ ⟨hx, h⟩)
  have hFΔ₁ : F ⊆ discBd Δ₁ := b₁ ▸ subset_union_right
  have hcapB : B ∩ Δ₁ = F := by
    apply Subset.antisymm
    · rintro x ⟨h1, h2⟩
      by_contra hn
      exact hs₁ ⟨h2, hn⟩ h1
    · exact fun x hx => ⟨GM11.discBd_subset B (hFB hx), GM11.discBd_subset Δ₁ (hFΔ₁ hx)⟩
  obtain ⟨hd, hbd⟩ := disc_union B Δ₁ F y₁ y₂ hB d₁ hF hcapB hFB hFΔ₁
  have hBR : B ∪ R = B ∪ Δ₁ := by
    rw [← hcup]
    apply Subset.antisymm
    · exact union_subset subset_union_left (union_subset subset_union_right
        (hΔ₂B.trans subset_union_left))
    · exact union_subset_union_right _ subset_union_left
  rw [hBR]
  have hA₁ : A₁ ⊆ discBd R := hun ▸ subset_union_left
  have hends : ∀ x ∈ F, x ∉ F \ {y₁, y₂} → x ∈ discBd R := fun x hx h => by
    have h2 : x ∈ ({y₁, y₂} : Set T) := by
      by_contra hn
      exact h ⟨hx, hn⟩
    exact (hb.ge h2).2
  refine ⟨hd, ?_, ?_, ?_, ?_⟩
  · rw [hbd, b₁]
    rintro x ⟨h | h | h, -⟩
    · exact .inl h
    · exact .inr (hA₁ h)
    · exact .inl (hFB h)
  · refine disjoint_left.mpr fun x hx hxR => hxR.2 ?_
    rw [hbd, b₁] at hx
    rcases hx with ⟨h | h | h, h2⟩
    · exact hends x (hRB ▸ ⟨hxR.1, h⟩) h2
    · exact hA₁ h
    · exact hends x h h2
  · rintro x ⟨h1, h2⟩
    rw [hbd]
    exact ⟨.inl h1, fun h => h2 (hFR h.1)⟩
  · rintro x ⟨h1, h2⟩
    rw [hbd, b₁]
    have hxF : x ∉ F := fun h => h2 (GM11.discBd_subset B (hFB h))
    rw [← hun] at h1
    rcases h1 with h | h
    · exact ⟨.inr (.inl h), fun h3 => hxF h3.1⟩
    · exact absurd (hΔ₂B (GM11.discBd_subset Δ₂ (b₂ ▸ .inl h))) h2

/-- **Adding half discs.** Let finitely many disjoint discs `R i` each meet the boundary of `B₀` in
a chord. Then `B₀` and the discs form one disc, and each point of the
boundary of a disc outside `B₀` is on its boundary. -/
theorem exists_blob (hS : IsClosedSurface T) {B₀ : Set T} (hB₀ : IsClosedDisc B₀) {ι : Type*} {R F
  : ι → Set T} {y₁ y₂ v : ι → T} (s : Finset ι)
    (hR : ∀ i ∈ s, IsClosedDisc (R i)) (hF : ∀ i ∈ s, IsLineWithEnds (F i) (y₁ i) (y₂ i))
      (hne : ∀ i ∈ s, y₁ i ≠ y₂ i) (hFR : ∀ i ∈ s, F i ⊆ R i)
    (hb : ∀ i ∈ s, F i ∩ discBd (R i) = {y₁ i, y₂ i}) (hRB : ∀ i ∈ s, R i ∩ discBd B₀ = F i)
      (hv : ∀ i ∈ s, v i ∈ F i) (hvR : ∀ i ∈ s, v i ∈ discInt (R i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (R i) (R j)) :
    ∃ B, IsClosedDisc B ∧ B₀ ⊆ B ∧ (∀ i ∈ s, R i ⊆ B) ∧ B ⊆ B₀ ∪ ⋃ i ∈ s, R i
      ∧ discBd B ⊆ discBd B₀ ∪ ⋃ i ∈ s, discBd (R i) ∧ (∀ i ∈ s, Disjoint (discBd B) (discInt
        (R i))) ∧
      (∀ i ∈ s, discBd (R i) \ B₀ ⊆ discBd B) ∧ discBd B₀ \ (⋃ i ∈ s, R i) ⊆ discBd B := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨B₀, hB₀, Subset.rfl, by simp, by simp, by simp, by simp, by simp, by simp⟩
  | insert i s his ih =>
  have hm : ∀ {j}, j ∈ s → j ∈ insert i s := fun {j} hj => Finset.mem_insert_of_mem hj
  have hi := Finset.mem_insert_self i s
  obtain ⟨B, hB, h1, h2, h3, h4, h5, h6, h7⟩ := ih (fun j hj => hR j (hm hj)) (fun j hj => hF j
    (hm hj)) (fun j hj => hne j (hm hj)) (fun j hj => hFR j (hm hj)) (fun j hj => hb j (hm hj))
    (fun j hj => hRB j (hm hj)) (fun j hj => hv j (hm hj)) (fun j hj => hvR j (hm hj))
      (fun j hj k hk => hd j (hm hj) k (hm hk))
  have hdi : ∀ j ∈ s, Disjoint (R i) (R j) := fun j hj => hd i hi j (hm hj) fun e => his (e ▸ hj)
  have hoff : ∀ x ∈ R i, x ∉ ⋃ j ∈ s, R j := fun x hx h => by
    obtain ⟨j, hj, h8⟩ := mem_iUnion₂.mp h
    exact disjoint_left.mp (hdi j hj) hx h8
  have hRBi : R i ∩ discBd B = F i := by
    rw [← hRB i hi]
    apply Subset.antisymm
    · rintro x ⟨hx, hxb⟩
      rcases h4 hxb with h | h
      · exact ⟨hx, h⟩
      · obtain ⟨j, hj, h8⟩ := mem_iUnion₂.mp h
        exact absurd (GM11.discBd_subset _ h8) (disjoint_left.mp (hdi j hj) hx)
    · rintro x ⟨hx, hxb⟩
      exact ⟨hx, h7 ⟨hxb, hoff x hx⟩⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := exists_half_union hS hB (hR i hi) (hF i hi) (hne i hi) (hFR i hi)
    (hb i hi) hRBi (hv i hi) (hvR i hi)
  have hsplit : ∀ {P : ι → Set T} {x : T}, x ∈ ⋃ j ∈ insert i s, P j → x ∈ P i ∨ x ∈ ⋃ j ∈ s, P j
    := fun {P x} h => by
    obtain ⟨j, hj, h8⟩ := mem_iUnion₂.mp h
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact .inl h8
    · exact .inr (mem_iUnion₂.mpr ⟨j, hj, h8⟩)
  have hincl : ∀ {P : ι → Set T} {x : T}, x ∈ ⋃ j ∈ s, P j → x ∈ ⋃ j ∈ insert i s, P j
    := fun {P x} h => by
    obtain ⟨j, hj, h8⟩ := mem_iUnion₂.mp h
    exact mem_iUnion₂.mpr ⟨j, hm hj, h8⟩
  refine ⟨B ∪ R i, a1, h1.trans subset_union_left, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact subset_union_right
    · exact (h2 j hj).trans subset_union_left
  · rintro x (hx | hx)
    · rcases h3 hx with h | h
      · exact .inl h
      · exact .inr (hincl h)
    · exact .inr (mem_iUnion₂.mpr ⟨i, hi, hx⟩)
  · intro x hx
    rcases a2 hx with h | h
    · rcases h4 h with h' | h'
      · exact .inl h'
      · exact .inr (hincl h')
    · exact .inr (mem_iUnion₂.mpr ⟨i, hi, h⟩)
  · intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact a3
    · refine disjoint_left.mpr fun x hx hxj => ?_
      rcases a2 hx with h | h
      · exact disjoint_left.mp (h5 j hj) h hxj
      · exact disjoint_left.mp (hdi j hj) (GM11.discBd_subset _ h) hxj.1
  · intro j hj x hx
    rcases Finset.mem_insert.mp hj with rfl | hj
    · refine a5 ⟨hx.1, fun h => ?_⟩
      rcases h3 h with h' | h'
      · exact hx.2 h'
      · exact hoff x (GM11.discBd_subset _ hx.1) h'
    · refine a4 ⟨h6 j hj hx, fun h => ?_⟩
      exact disjoint_left.mp (hdi j hj) h (GM11.discBd_subset _ hx.1)
  · rintro x ⟨hx, hn⟩
    refine a4 ⟨h7 ⟨hx, fun h => hn (hincl h)⟩, fun h => hn (mem_iUnion₂.mpr ⟨i, hi, h⟩)⟩

/-- A parent map that lowers a rank has no cycles, so each edge of it is a bridge. -/
theorem not_reach_of_rank {N : Type} {par : N → Option N} {ρ : N → ℕ} (hρ : ∀ u v, par u = some v
  → ρ v < ρ u) (E : Set N) (i : N) (hi : i ∉ E) :
    ¬ Reach (fun u : N => (some u : Option N)) par E (some i) (par i) := by
  -- The descendants of `i`.
  let Dsc : N → Prop := Relation.ReflTransGen (fun y z => par z = some y) i
  have hrank : ∀ {u : N}, Dsc u → ρ i ≤ ρ u := fun {u} h => by
    induction h with
    | refl => exact le_rfl
    | tail _ hstep ih => exact ih.trans (hρ _ _ hstep).le
  have hkey : ∀ x, Reach (fun u : N => (some u : Option N)) par E (some i) x → ∃ u, x = some u
    ∧ Dsc u := fun x h => by
    induction h with
    | refl => exact ⟨i, rfl, .refl⟩
    | tail _ hstep ih =>
      obtain ⟨u, rfl, hu⟩ := ih
      obtain ⟨j, hj, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hstep
      · obtain rfl := Option.some.inj h1
        rcases Relation.ReflTransGen.cases_tail hu with h3 | ⟨z, hz, h4⟩
        · exact absurd (h3 ▸ hj) hi
        · exact ⟨z, h2 ▸ h4, hz⟩
      · exact ⟨j, h1.symm, hu.tail h2⟩
  intro h
  rcases hp : par i with _ | v
  · obtain ⟨u, h1, -⟩ := hkey _ h
    rw [hp] at h1
    exact absurd h1 (by simp)
  · obtain ⟨u, h1, h2⟩ := hkey _ h
    rw [hp] at h1
    obtain rfl := Option.some.inj h1
    exact absurd (hρ _ _ hp) (not_lt.mpr (hrank h2))

omit [T2Space T] in
/-- **A disc around a tree of discs and more lines.** On a sphere, take disjoint discs `c₀`, joined
to the root disc by lines `L`, along a parent map. Let `ℓ` be further lines
as in `exists_disc_absorbing`. Then a disc holds all of them, it misses `Y₀`, and its boundary meets
`Y` and the lines `ℓ` only in `X`. -/
theorem exists_disc_of_tree (hS : IsClosedSurface T) (hsph : IsSphere T) {N : Type} [Finite N] {c₀
  : Option N → Set T} {L : N → Set T} {p q : N → T} {par : N → Option N} {ρ : N → ℕ}
    (hd : ∀ n, IsClosedDisc (c₀ n)) (hdj : ∀ m n, m ≠ n → Disjoint (c₀ m) (c₀ n))
      (hρ : ∀ u v, par u = some v → ρ v < ρ u) (hL : ∀ u, IsLineWithEnds (L u) (p u) (q u))
    (hp : ∀ u, p u ∈ discBd (c₀ (some u))) (hq : ∀ u, q u ∈ discBd (c₀ (par u)))
      (hLc : ∀ u n, L u ∩ c₀ n ⊆ {p u, q u}) (hLL : ∀ u v, u ≠ v → Disjoint (L u) (L v))
    {ι : Type*} (s : Finset ι) (ℓ : ι → Set T) (a b : ι → T) {X Y Y₀ : Set T}
      (hY₀ : IsPreconnected Y₀) (hY₀n : Y₀.Nonempty) (hXY : Disjoint X Y₀) (hYc : IsClosed Y)
        (hY₀Y : Y₀ ⊆ Y)
    (hLY : ∀ u, Disjoint (L u) Y) (hLℓ : ∀ u, ∀ i ∈ s, Disjoint (L u) (ℓ i))
      (hcY₀ : ∀ n, Disjoint Y₀ (c₀ n)) (hbY : ∀ n, discBd (c₀ n) ∩ Y ⊆ X)
    (hline : ∀ i ∈ s, IsLineWithEnds (ℓ i) (a i) (b i)) (hne : ∀ i ∈ s, a i ≠ b i)
      (haX : ∀ i ∈ s, a i ∉ X) (ha : ∀ i ∈ s, ∃ n, a i ∈ discBd (c₀ n))
    (hb : ∀ i ∈ s, (∃ n, b i ∈ discBd (c₀ n)) ∨ b i ∈ X ∧ ∀ n, b i ∉ c₀ n)
      (hin : ∀ i ∈ s, ∀ n, ℓ i ∩ c₀ n ⊆ {a i, b i}) (hinY : ∀ i ∈ s, ℓ i ∩ Y ⊆ X)
    (hmid : ∀ i ∈ s, Disjoint (ℓ i \ {a i, b i}) X) (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j
      → ℓ i ∩ ℓ j ⊆ X) :
    ∃ B, IsClosedDisc B ∧ (∀ n, c₀ n ⊆ B ∧ discInt (c₀ n) ⊆ discInt B) ∧ (∀ u, L u ⊆ discInt B)
      ∧ Disjoint Y₀ B ∧ discBd B ∩ Y ⊆ X ∧ ∀ i ∈ s, discBd B ∩ ℓ i ⊆ X := by
  classical
  have ht2 : T2Space T := hS.2.1
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  set Z : Set T := Y ∪ ⋃ i ∈ s, ℓ i with hZ
  have hZc : IsClosed Z := hYc.union (s.finite_toSet.isClosed_biUnion fun i hi =>
    (hline i hi).isCompact.isClosed)
  have hℓZ : ∀ i ∈ s, ℓ i ⊆ Z := fun i hi x hx => .inr (mem_iUnion₂.mpr ⟨i, hi, hx⟩)
  have hLZ : ∀ u, Disjoint (L u) Z := fun u => disjoint_union_right.mpr ⟨hLY u, by
    refine disjoint_left.mpr fun x hx h => ?_
    obtain ⟨i, hi, h2⟩ := mem_iUnion₂.mp h
    exact disjoint_left.mp (hLℓ u i hi) hx h2⟩
  obtain ⟨c, h1, h2, h3, h4, h5, h6, h7, h8⟩ := exists_forest_discs (V := Option N) (ι := N) hS (c₀
    := c₀) (L := L) (p := p) (q := q) (a := some) (b := par) (Z := Z) hd hdj hL hp hq hLc
    (fun u v huv => hLL u v huv) hZc hLZ (fun E i hi => not_reach_of_rank hρ E i hi)
  -- All discs are one.
  have hone : ∀ n, c n = c none := by
    have hrk : ∀ (k : ℕ) (u : N), ρ u = k → c (some u) = c none := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
      intro u hu
      rw [(h4 u).2]
      rcases hp' : par u with _ | v
      · rfl
      · exact ih (ρ v) (hu ▸ hρ u v hp') v rfl
    intro n
    cases n with
    | none => rfl
    | some u => exact hrk _ u rfl
  set B := c none with hB
  have hBd : IsClosedDisc B := h1 none
  have hc₀ : ∀ n, c₀ n ⊆ B ∧ discInt (c₀ n) ⊆ discInt B := fun n => by
    have := h5 n
    rwa [hone n] at this
  have hZB : ∀ x, x ∈ Z → x ∈ B → ∃ n, x ∈ c₀ n := fun x hx hxB => by
    have h9 := h6 none ⟨hxB, hx⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp h9
    exact ⟨n, hn⟩
  have hbB : ∀ n, discBd (c₀ n) ∩ Z ⊆ discBd B := fun n => by
    have := h7 n
    rwa [hone n] at this
  have hbB' : ∀ x, x ∈ discBd B → x ∈ Z → ∃ n, x ∈ discBd (c₀ n) := fun x hx hxZ => by
    have h9 := h8 none ⟨hx, hxZ⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp h9
    exact ⟨n, hn⟩
  have hY₀B : Disjoint Y₀ B := disjoint_left.mpr fun x hx hxB => by
    obtain ⟨n, hn⟩ := hZB x (.inl (hY₀Y hx)) hxB
    exact disjoint_left.mp (hcY₀ n) hx hn
  have hbdY : discBd B ∩ Y ⊆ X := by
    rintro x ⟨hx, hy⟩
    obtain ⟨n, hn⟩ := hbB' x hx (.inl hy)
    exact hbY n ⟨hn, hy⟩
  obtain ⟨B', hB', hBB', hYB', hbY', hbl⟩ := exists_disc_absorbing hS hsph ℓ a b hY₀ hY₀n hXY
    s.card s rfl B Y hBd hYc hY₀Y hY₀B hbdY (fun i hi => by
    have hl := hline i hi
    refine ⟨hl, hne i hi, haX i hi, ?_, ?_, ?_, fun x hx => hinY i hi hx, hmid i hi⟩
    · obtain ⟨n, hn⟩ := ha i hi
      exact hbB n ⟨hn, hℓZ i hi hl.left_mem⟩
    · rcases hb i hi with ⟨n, hn⟩ | ⟨h9, h10⟩
      · exact .inl (hbB n ⟨hn, hℓZ i hi hl.right_mem⟩)
      · refine .inr ⟨h9, fun h11 => ?_⟩
        obtain ⟨n, hn⟩ := hZB _ (hℓZ i hi hl.right_mem) h11
        exact h10 n hn
    · rintro x ⟨hx, hxB⟩
      obtain ⟨n, hn⟩ := hZB x (hℓZ i hi hx) hxB
      exact hin i hi n ⟨hx, hn⟩) hpair
  refine ⟨B', hB', fun n => ⟨(hc₀ n).1.trans hBB', (hc₀ n).2.trans (discInt_mono hman hBd hBB')⟩,
    fun u => ?_, hYB', hbY', hbl⟩
  have := (h4 u).1
  rw [hone] at this
  exact this.trans (discInt_mono hman hBd hBB')

/-- **Cutting an edge at the discs around its ends.** Each end in `K` has a disc around it, and the
discs meet the edge only near those ends. Then the middle piece of the edge,
from `s` to `t`, misses all discs, except at its ends. -/
theorem EdgeParam.exists_cut (h : EdgeParam H f γ) (hf : f ∈ H.E) {K : Set T} {R : T → Set T}
  (hR : ∀ v ∈ K, IsClosedDisc (R v) ∧ v ∈ discInt (R v) ∧ IsOpen (discInt (R v)))
    (hstar : ∀ v ∈ K, ∀ y ∈ R v ∩ range γ, ∃ C, IsPreconnected C ∧ C ⊆ range γ ∧ y ∈ C ∧ v ∈ C
      ∧ C \ {y} ⊆ discInt (R v)) (h0 : γ 0 ∈ K) {m : I} (hm1 : m < 1) (hm : ∀ v ∈ K, γ m ∉ R v)
    (hoff : γ 1 ∉ K → ∀ v ∈ K, γ 1 ∉ R v) (hends : ∀ v ∈ K, (R v ∩ range γ).Nonempty → v = γ 0 ∨ v
      = γ 1) (hsep : γ 1 ≠ γ 0 → γ 1 ∈ K → γ 0 ∉ R (γ 1) ∧ γ 1 ∉ R (γ 0)) :
    ∃ s t, 0 < s ∧ s < m ∧ m < t ∧ γ s ∈ discBd (R (γ 0)) ∧ (∀ τ < s, γ τ ∈ discInt (R (γ 0))) ∧
      ((γ 1 ∈ K ∧ t < 1 ∧ γ t ∈ discBd (R (γ 1)) ∧ ∀ τ, t < τ → γ τ ∈ discInt (R (γ 1))) ∨ γ 1 ∉ K
        ∧ t = 1) ∧ ∀ v ∈ K, ∀ τ, s < τ → τ < t → γ τ ∉ R v := by
  obtain ⟨hd₀, hm₀, ho₀⟩ := hR _ h0
  obtain ⟨s, hs0, hsm, hsb, hspre⟩ := exists_first_exit h.cont hd₀ ho₀ hm₀ (hm _ h0)
  have hrev : ∀ x : I, (γ ∘ unitInterval.symm) (unitInterval.symm x) = γ x := fun x => by simp
  have hrange : range (γ ∘ unitInterval.symm) = range γ := by
    rw [range_comp, unitInterval.symm_bijective.surjective.range_eq, image_univ]
  have hγ1 : (γ ∘ unitInterval.symm) 0 = γ 1 := by simp
  have hγ0 : (γ ∘ unitInterval.symm) 1 = γ 0 := by simp
  have hex : ∃ t, m < t ∧ ((γ 1 ∈ K ∧ t < 1 ∧ γ t ∈ discBd (R (γ 1)) ∧ ∀ τ, t < τ → γ τ ∈ discInt
    (R (γ 1))) ∨ γ 1 ∉ K ∧ t = 1) := by
    by_cases h1 : γ 1 ∈ K
    · obtain ⟨hd₁, hm₁, ho₁⟩ := hR _ h1
      obtain ⟨t', ht0, htm, htb, htpre⟩ := exists_first_exit (z := unitInterval.symm m) h.rev.cont
        hd₁ ho₁
        (by rwa [hγ1]) (by rw [hrev]; exact hm _ h1)
      refine ⟨unitInterval.symm t', ?_, .inl ⟨h1, ?_, htb, fun τ hτ => ?_⟩⟩
      · have := unitInterval.symm_lt_symm.mpr htm
        simpa using this
      · have := unitInterval.symm_lt_symm.mpr ht0
        simpa using this
      · have h3 : unitInterval.symm τ < t' := by
          have := unitInterval.symm_lt_symm.mpr hτ
          simpa using this
        have := htpre _ h3
        rwa [hrev] at this
    · exact ⟨1, hm1, .inr ⟨h1, rfl⟩⟩
  obtain ⟨t, hmt, hcase⟩ := hex
  refine ⟨s, t, hs0, hsm, hmt, hsb, hspre, hcase, fun v hv τ hsτ hτt hy => ?_⟩
  have hst : s < t := hsm.trans hmt
  have hrg : ((R v) ∩ range γ).Nonempty := ⟨_, hy, mem_range_self τ⟩
  have hgo : ∀ v ∈ K, ∀ y ∈ R v ∩ range (γ ∘ unitInterval.symm), ∃ C, IsPreconnected C ∧ C ⊆ range
    (γ ∘ unitInterval.symm) ∧ y ∈ C ∧ v ∈ C ∧ C \ {y} ⊆ discInt (R v) := by
    rw [hrange]
    exact hstar
  have hfirst : v = γ 0 → False := by
    rintro rfl
    refine h.no_return hf (hstar _ h0) hs0 hsb (t := t) ?_ hsτ hτt hy
    rcases hcase with ⟨h1, h2, h3, -⟩ | ⟨h1, -⟩
    · by_cases he : γ 1 = γ 0
      · exact .inr ⟨h2, he ▸ h3⟩
      · exact .inl (hsep he h1).2
    · exact .inl (hoff h1 _ h0)
  rcases hends v hv hrg with hv0 | hv1
  · exact hfirst hv0
  · subst hv1
    by_cases he : γ 1 = γ 0
    · exact hfirst he
    rcases hcase with ⟨h1, h2, h3, -⟩ | ⟨h1, -⟩
    · have h4 : unitInterval.symm t < unitInterval.symm τ := unitInterval.symm_lt_symm.mpr hτt
      have h5 : unitInterval.symm τ < unitInterval.symm s := unitInterval.symm_lt_symm.mpr hsτ
      have h6 : 0 < unitInterval.symm t := by
        have := unitInterval.symm_lt_symm.mpr h2
        simpa using this
      have hg := hgo _ hv
      rw [← hγ1] at hg h3 hy
      refine h.rev.no_return hf hg h6 (by rwa [hrev]) (t := unitInterval.symm s) (.inl ?_) h4 h5
        (by rwa [hrev])
      rw [hγ0, hγ1]
      exact (hsep he h1).1
    · exact h1 hv

end GraphMinor.GM07
