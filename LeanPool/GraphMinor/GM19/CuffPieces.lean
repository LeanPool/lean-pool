/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FrameExists
public import LeanPool.GraphMinor.GM19.FrameMove
public import LeanPool.GraphMinor.Surface.Classification

/-!
# Cutting the boundary at a finite set

When we cut a surface, the new boundary carries a finite set `N` of vertices. If every cuff has at
least
two points of `N`, then `bd(Σ) \ N` has finitely many arc-wise components, and each is an open arc
of a
cuff with two different ends in `N`. This is what makes the boundary of a fragment into the border
edges of a painting.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S] [T2Space S]

section OneCuff

variable {Θ : Set S} (f : Circle ≃ₜ Θ) {N : Set S}

omit [T2Space S] in
theorem finite_angles (hN : N.Finite) (a : ℝ) :
    ({t | t ∈ Ico a (a + 2 * Real.pi) ∧ cuffPoint f t ∈ N}).Finite := by
  refine Set.Finite.of_injOn (f := cuffPoint f) (t := N) (fun t ht ↦ ht.2) ?_ hN
  exact fun s hs t ht h ↦ cuffPoint_injOn f le_rfl hs.1 ht.1 h

omit [T2Space S] in
theorem finite_angles' (hN : N.Finite) (a : ℝ) :
    ({t | t ∈ Ioc a (a + 2 * Real.pi) ∧ cuffPoint f t ∈ N}).Finite := by
  have hpi := Real.pi_pos
  refine Set.Finite.of_injOn (f := cuffPoint f) (t := N) (fun t ht ↦ ht.2) ?_ hN
  intro s hs t ht h
  obtain ⟨m, hm⟩ := cuffPoint_eq f h
  have h0 : m = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have h2 : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
      nlinarith [hs.1.1, hs.1.2, ht.1.1, ht.1.2]
    · have h2 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      nlinarith [hs.1.1, hs.1.2, ht.1.1, ht.1.2]
  rw [hm, h0]
  simp

omit [T2Space S] in
/-- A point of a cuff off `N` lies on an open arc that misses `N` and has two ends in `N`, as long
as the
cuff has two points of `N`. The ends are the last point of `N` before the point and the first one
after
it. The arc is not the whole circle, because `N` has a second point. -/
theorem exists_arc_of_two (hN : N.Finite) {p q : S} (hp : p ∈ N ∩ Θ) (hq : q ∈ N ∩ Θ) (hpq : p ≠ q)
    {x : S} (hx : x ∈ Θ \ N) :
    ∃ a b : ℝ, a < b ∧ b < a + 2 * Real.pi ∧ x ∈ arcOf f a b ∧ Disjoint (arcOf f a b) N ∧
      cuffPoint f a ∈ N ∧ cuffPoint f b ∈ N := by
  have hpi := Real.pi_pos
  obtain ⟨t, -, ht⟩ := exists_angle_in f 0 ⟨x, hx.1⟩
  change cuffPoint f t = x at ht
  have htN : cuffPoint f t ∉ N := ht ▸ hx.2
  have hA := finite_angles f hN (t - 2 * Real.pi)
  have hB := finite_angles' f hN t
  obtain ⟨s₀, hs₀, hs₀p⟩ := exists_angle_in f (t - 2 * Real.pi) ⟨p, hp.2⟩
  change cuffPoint f s₀ = p at hs₀p
  obtain ⟨s₁, hs₁, hs₁p⟩ := exists_angle_in f t ⟨p, hp.2⟩
  change cuffPoint f s₁ = p at hs₁p
  have hs₁t : s₁ ≠ t := fun h ↦ htN (h ▸ (hs₁p ▸ hp.1))
  obtain ⟨a, ha, hamax⟩ := hA.exists_le_maximal (a := s₀) ⟨hs₀, hs₀p ▸ hp.1⟩
  obtain ⟨b, hb, hbmin⟩ := hB.exists_le_minimal (a := s₁)
    ⟨⟨lt_of_le_of_ne hs₁.1 hs₁t.symm, hs₁.2.le⟩, hs₁p ▸ hp.1⟩
  have haI := hamax.prop.1
  have hbI := hbmin.prop.1
  have haN := hamax.prop.2
  have hbN := hbmin.prop.2
  have hat : a < t := lt_of_le_of_ne (by linarith [haI.2]) fun h ↦ htN (h ▸ haN)
  have htb : t < b := hbI.1
  have hAno : ∀ s, a < s → s < t → cuffPoint f s ∉ N := fun s h₁ h₂ hsN ↦
    absurd (hamax.le_of_ge (y := s) ⟨⟨by linarith [haI.1], by linarith⟩, hsN⟩ h₁.le) (not_le.mpr h₁)
  have hBno : ∀ s, t < s → s < b → cuffPoint f s ∉ N := fun s h₁ h₂ hsN ↦
    absurd (hbmin.le_of_le (y := s) ⟨⟨h₁, by linarith [hbI.2]⟩, hsN⟩ h₂.le) (not_le.mpr h₂)
  -- A point of `N` other than the left end gives `b < a + 2π`.
  have hub : b < a + 2 * Real.pi := by
    have hr : ∃ r ∈ N ∩ Θ, r ≠ cuffPoint f a := by
      by_cases h : p = cuffPoint f a
      · exact ⟨q, hq, fun h' ↦ hpq (h.trans h'.symm)⟩
      · exact ⟨p, hp, h⟩
    obtain ⟨r, hr, hra⟩ := hr
    obtain ⟨s, hs, hsr⟩ := exists_angle_in f a ⟨r, hr.2⟩
    change cuffPoint f s = r at hsr
    have hsa : a < s := lt_of_le_of_ne hs.1 fun h ↦ hra (hsr ▸ h ▸ rfl)
    have hsN : cuffPoint f s ∈ N := hsr ▸ hr.1
    rcases lt_trichotomy s t with h | h | h
    · exact absurd hsN (hAno s hsa h)
    · exact absurd hsN (h ▸ htN)
    · by_contra hge
      exact hBno s h (by linarith [hs.2, not_lt.mp hge]) hsN
  refine ⟨a, b, by linarith, hub, ⟨t, ⟨hat, htb⟩, ht⟩, disjoint_left.mpr ?_, haN, hbN⟩
  rintro _ ⟨s, hs, rfl⟩ hsN
  rcases lt_trichotomy s t with h | h | h
  · exact hAno s hs.1 h hsN
  · exact htN (h ▸ hsN)
  · exact hBno s h hs.2 hsN

omit [T2Space S] in
theorem cuffPoint_shift (a : ℝ) (m : ℤ) : cuffPoint f (a + m * (2 * Real.pi)) = cuffPoint f a := by
  have h : Circle.exp (a + m * (2 * Real.pi)) = Circle.exp a := Circle.exp_eq_exp.mpr ⟨m, rfl⟩
  simp only [cuffPoint, h]

omit [T2Space S] in
theorem arcOf_shift (a b : ℝ) (m : ℤ) :
    arcOf f (a + m * (2 * Real.pi)) (b + m * (2 * Real.pi)) = arcOf f a b := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t - m * (2 * Real.pi), ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    have h := cuffPoint_shift f (t - m * (2 * Real.pi)) m
    rw [sub_add_cancel] at h
    exact h.symm
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t + m * (2 * Real.pi), ⟨by linarith [ht.1], by linarith [ht.2]⟩, cuffPoint_shift f t m⟩

omit [T2Space S] in
/-- Two arcs that miss `N` and have the same left end in `N` and right ends in `N` are equal. -/
theorem arcOf_eq_of_left {a b a' b' : ℝ} (hab : a < b) (hab' : a' < b')
    (hd : Disjoint (arcOf f a b) N) (hd' : Disjoint (arcOf f a' b') N)
    (hb : cuffPoint f b ∈ N) (hb' : cuffPoint f b' ∈ N) (h : cuffPoint f a = cuffPoint f a') :
    arcOf f a b = arcOf f a' b' := by
  obtain ⟨m, hm⟩ := cuffPoint_eq f h
  subst hm
  have hshift := arcOf_shift f a' (b - m * (2 * Real.pi)) m
  rw [sub_add_cancel] at hshift
  rw [hshift] at hd ⊢
  have hcp : cuffPoint f (b - m * (2 * Real.pi)) = cuffPoint f b := by
    have h := cuffPoint_shift f (b - m * (2 * Real.pi)) m
    rwa [sub_add_cancel, eq_comm] at h
  have hab₂ : a' < b - m * (2 * Real.pi) := by linarith
  rcases lt_trichotomy (b - m * (2 * Real.pi)) b' with h₁ | h₁ | h₁
  · exact absurd (hcp ▸ hb) (disjoint_left.mp hd' ⟨_, ⟨hab₂, h₁⟩, rfl⟩)
  · rw [h₁]
  · exact absurd hb' (disjoint_left.mp hd ⟨_, ⟨hab', h₁⟩, rfl⟩)

end OneCuff

section Pieces

variable (hS : IsSurface S) (par : ∀ C : cuffs S, Circle ≃ₜ C.1) {N : Set S}

include hS in
/-- The points of `bd(Σ)` outside the cuff `C` form a closed set. -/
theorem isClosed_bd_sdiff (C : cuffs S) : IsClosed (bd S \ C.1) := by
  have hfin : (cuffs S).Finite := (cuff_statement S hS).2.1
  have h : bd S \ C.1 = ⋃ D ∈ cuffs S \ {C.1}, D := by
    ext x
    constructor
    · rintro ⟨hx, hxC⟩
      rw [← sUnion_cuffs] at hx
      obtain ⟨D, hD, hxD⟩ := hx
      exact mem_biUnion (show D ∈ cuffs S \ {C.1} from ⟨hD, fun h ↦ hxC (h ▸ hxD)⟩) hxD
    · intro hx
      obtain ⟨D, hD, hxD⟩ := mem_iUnion₂.mp hx
      refine ⟨sUnion_cuffs (S := S) ▸ ⟨D, hD.1, hxD⟩, fun hxC ↦ ?_⟩
      exact disjoint_left.mp (Surface.cuffs_disjoint hD.1 C.2 hD.2) hxD hxC
  rw [h]
  refine (hfin.subset sdiff_subset).isClosed_biUnion fun D hD ↦ ?_
  exact isClosed_cuff hS ⟨D, hD.1⟩

include hS in
/-- Each arc-wise component of `bd(Σ) \ N` is an open arc of a cuff, with two ends in `N`. -/
theorem exists_arc_of_mem (hN : N.Finite)
    (h2 : ∀ C : cuffs S, ∃ p ∈ N ∩ C.1, ∃ q ∈ N ∩ C.1, p ≠ q) {e : Set S}
    (he : e ∈ arcComponentsIn (bd S \ N)) :
    ∃ (C : cuffs S) (a b : ℝ), a < b ∧ b < a + 2 * Real.pi ∧ e = arcOf (par C) a b ∧
      Disjoint e N ∧ cuffPoint (par C) a ∈ N ∧ cuffPoint (par C) b ∈ N := by
  have hpi := Real.pi_pos
  obtain ⟨x, hx⟩ := he.1
  have hxb := he.2.1 hx
  obtain ⟨C, hC, hxC⟩ := sUnion_cuffs (S := S) ▸ hxb.1
  let C' : cuffs S := ⟨C, hC⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := h2 C'
  obtain ⟨a, b, hab, hub, hxA, hdis, ha, hb⟩ := exists_arc_of_two (par C') hN hp hq hpq
    (x := x) ⟨hxC, hxb.2⟩
  have hsub : arcOf (par C') a b ⊆ bd S \ N := fun y hy ↦
    ⟨cuff_subset_bd C' (arcOf_subset _ _ _ hy), disjoint_left.mp hdis hy⟩
  -- `e` lies in the closed arc, since the rest of `bd(Σ)` meets it only in its ends.
  let X : Set S := cuffPoint (par C') '' Icc a b
  let Y : Set S := cuffPoint (par C') '' Icc b (a + 2 * Real.pi) ∪ (bd S \ C)
  have hXc : IsClosed X := (isCompact_Icc.image (continuous_cuffPoint _)).isClosed
  have hYc : IsClosed Y := ((isCompact_Icc.image (continuous_cuffPoint _)).isClosed).union
    (isClosed_bd_sdiff hS C')
  have hcov : e ⊆ X ∪ Y := by
    intro y hy
    have hyb := (he.2.1 hy).1
    by_cases hyC : y ∈ C
    · obtain ⟨t, ht, hty⟩ := exists_angle_in (par C') a ⟨y, hyC⟩
      change cuffPoint (par C') t = y at hty
      by_cases htb : t ≤ b
      · exact Or.inl ⟨t, ⟨ht.1, htb⟩, hty⟩
      · exact Or.inr (Or.inl ⟨t, ⟨(not_le.mp htb).le, ht.2.le⟩, hty⟩)
    · exact Or.inr (Or.inr ⟨hyb, hyC⟩)
  have hxX : x ∈ X := by
    obtain ⟨t, ht, rfl⟩ := hxA
    exact ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
  have hsubX : e ⊆ X := by
    by_contra hne
    obtain ⟨y, hy, hyX⟩ := not_subset.mp hne
    obtain ⟨z, hz, hzX, hzY⟩ := isPreconnected_closed_iff.mp he.2.2.1.isConnected.isPreconnected
      X Y hXc hYc hcov ⟨x, hx, hxX⟩ ⟨y, hy, (hcov hy).resolve_left hyX⟩
    have hzN : z ∉ N := (he.2.1 hz).2
    obtain ⟨t, ht, rfl⟩ := hzX
    rcases hzY with ⟨s, hs, hst⟩ | ⟨-, hn⟩
    · have hta : t ≠ a := fun h ↦ hzN (h ▸ ha)
      have htb : t ≠ b := fun h ↦ hzN (h ▸ hb)
      have hsa : s ≠ a + 2 * Real.pi := fun h ↦ hzN (by
        rw [← hst, h, cuffPoint_add_two_pi]; exact ha)
      have hsb : s ≠ b := fun h ↦ hzN (by rw [← hst, h]; exact hb)
      have := cuffPoint_injOn (par C') (a := a) (b := a + 2 * Real.pi) le_rfl
        ⟨ht.1, by linarith [ht.2]⟩ ⟨by linarith [hs.1], lt_of_le_of_ne hs.2 hsa⟩ hst.symm
      have h₃ : t < b := lt_of_le_of_ne ht.2 htb
      have h₄ : b < s := lt_of_le_of_ne hs.1 hsb.symm
      linarith
    · exact hn (cuffPoint_mem (par C') t)
  have hsubA : e ⊆ arcOf (par C') a b := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := hsubX hy
    have hyN := (he.2.1 hy).2
    exact ⟨t, ⟨lt_of_le_of_ne ht.1 fun h ↦ hyN (h ▸ ha), lt_of_le_of_ne ht.2 fun h ↦ hyN (h ▸ hb)⟩,
      rfl⟩
  have heq : e = arcOf (par C') a b :=
    (he.2.2.2 _ hsub (isPathConnected_arcOf _ hab) hsubA).symm
  exact ⟨C', a, b, hab, hub, heq, heq ▸ hdis, ha, hb⟩

include hS in
/-- The boundary minus `N` has finitely many arc-wise components, since an arc is determined by its
left
end. -/
theorem finite_arcComponentsIn_bd (hN : N.Finite)
    (h2 : ∀ C : cuffs S, ∃ p ∈ N ∩ C.1, ∃ q ∈ N ∩ C.1, p ≠ q) :
    (arcComponentsIn (bd S \ N)).Finite := by
  have par : ∀ C : cuffs S, Circle ≃ₜ C.1 := fun C ↦ ((cuff_statement S hS).2.2 C.1 C.2).some
  have hex := fun e : arcComponentsIn (bd S \ N) ↦ exists_arc_of_mem hS par hN h2 e.2
  choose C a b hab hub heq hdis ha hb using hex
  have : Finite N := hN.to_subtype
  have key : ∀ (C₁ C₂ : cuffs S) (a₁ b₁ a₂ b₂ : ℝ), C₁ = C₂ → a₁ < b₁ → a₂ < b₂ →
      Disjoint (arcOf (par C₁) a₁ b₁) N → Disjoint (arcOf (par C₂) a₂ b₂) N →
      cuffPoint (par C₁) b₁ ∈ N → cuffPoint (par C₂) b₂ ∈ N →
      cuffPoint (par C₁) a₁ = cuffPoint (par C₂) a₂ →
      arcOf (par C₁) a₁ b₁ = arcOf (par C₂) a₂ b₂ := by
    rintro C₁ _ a₁ b₁ a₂ b₂ rfl h₁ h₂ d₁ d₂ e₁ e₂ h
    exact arcOf_eq_of_left _ h₁ h₂ d₁ d₂ e₁ e₂ h
  have hinj : Function.Injective fun e : arcComponentsIn (bd S \ N) ↦
      (⟨cuffPoint (par (C e)) (a e), ha e⟩ : N) := by
    intro e e' h
    have h' : cuffPoint (par (C e)) (a e) = cuffPoint (par (C e')) (a e') := congrArg Subtype.val h
    have hC : C e = C e' := by
      by_contra hne
      exact disjoint_left.mp (cuffs_disjoint' hne) (cuffPoint_mem _ _)
        (h' ▸ cuffPoint_mem (par (C e')) (a e'))
    refine Subtype.ext ?_
    rw [heq e, heq e']
    exact key _ _ _ _ _ _ hC (hab e) (hab e') (heq e ▸ hdis e) (heq e' ▸ hdis e') (hb e) (hb e') h'
  have := Finite.of_injective _ hinj
  exact Set.toFinite _

end Pieces

end GraphMinor.GM19
