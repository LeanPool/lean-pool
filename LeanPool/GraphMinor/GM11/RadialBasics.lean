/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section6
public import LeanPool.GraphMinor.GM11.Corners
public import LeanPool.GraphMinor.GM11.Section3

/-!
# Tools for radial drawings

Graph Minors XI omits the proof that "every region of $\Gamma'$ includes a unique edge of $\Gamma$",
for a radial
drawing `Γ'` of `Γ` (Section 3, page 75). This file has three general tools for that proof.

* `Drawing.glue`: the union of two drawings that meet only in common vertices, with its edges.
* `isOArc_union`: two lines with the same ends and nothing else in common form an `O`-arc.
* `exists_disc_in_openDisc`: an `O`-arc in an open disc bounds a closed disc in that open disc.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface Metric

universe u

variable {S : Type u} [TopologicalSpace S]

section Glue

variable {A B : Set S} {X Y : Set S}

/-- A connected subset of two closed sets, which misses their intersection, lies in one of them. -/
theorem subset_or_subset_of_closed {C : Set S} (hC : IsPreconnected C) (hX : IsClosed X)
    (hY : IsClosed Y) (hsub : C ⊆ X ∪ Y) (hdis : ∀ x ∈ C, x ∈ X → x ∉ Y) : C ⊆ X ∨ C ⊆ Y := by
  by_contra hno
  push Not at hno
  obtain ⟨hnX, hnY⟩ := hno
  obtain ⟨y, hyC, hyX⟩ := not_subset.mp hnX
  obtain ⟨x, hxC, hxY⟩ := not_subset.mp hnY
  have hxX : x ∈ X := (hsub hxC).resolve_right hxY
  have hyY : y ∈ Y := (hsub hyC).resolve_left hyX
  obtain ⟨z, hzC, hzX, hzY⟩ := isPreconnected_closed_iff.mp hC X Y hX hY hsub ⟨x, hxC, hxX⟩
    ⟨y, hyC, hyY⟩
  exact hdis z hzC hzX hzY

end Glue

/-- The arc-wise connected components of the union of two sets `A`, `B` that lie in closed sets
meeting only outside `A` and `B`. -/
theorem arcComponentsIn_union {U₁ U₂ A B : Set S} (h₁ : IsClosed U₁) (h₂ : IsClosed U₂)
    (hA : A ⊆ U₁) (hB : B ⊆ U₂) (hAB : ∀ x ∈ A ∪ B, x ∈ U₁ → x ∉ U₂) :
    arcComponentsIn (A ∪ B) = arcComponentsIn A ∪ arcComponentsIn B := by
  have hdisj : ∀ x, x ∈ A → x ∈ B → False := fun x h h' =>
    hAB x (Or.inl h) (hA h) (hB h')
  have hsplit : ∀ {C : Set S}, IsPathConnected C → C ⊆ A ∪ B → C ⊆ A ∨ C ⊆ B := by
    intro C hC hsub
    have hc : C ⊆ U₁ ∪ U₂ := hsub.trans (union_subset_union hA hB)
    rcases subset_or_subset_of_closed hC.isConnected.isPreconnected h₁ h₂ hc
      (fun x hx => hAB x (hsub hx)) with h | h
    · refine Or.inl fun x hx => (hsub hx).resolve_right fun hxB => ?_
      exact hAB x (hsub hx) (h hx) (hB hxB)
    · refine Or.inr fun x hx => (hsub hx).resolve_left fun hxA => ?_
      exact hAB x (hsub hx) (hA hxA) (h hx)
  ext C
  constructor
  · rintro ⟨hne, hsub, hp, hmax⟩
    rcases hsplit hp hsub with h | h
    · exact Or.inl ⟨hne, h, hp, fun D hD hpD hCD => hmax D (hD.trans subset_union_left) hpD hCD⟩
    · exact Or.inr ⟨hne, h, hp, fun D hD hpD hCD => hmax D (hD.trans subset_union_right) hpD hCD⟩
  · rintro (⟨hne, hsub, hp, hmax⟩ | ⟨hne, hsub, hp, hmax⟩)
    · refine ⟨hne, hsub.trans subset_union_left, hp, fun D hD hpD hCD => ?_⟩
      obtain ⟨x, hx⟩ := hne
      rcases hsplit hpD hD with h | h
      · exact hmax D h hpD hCD
      · exact (hdisj x (hsub hx) (h (hCD hx))).elim
    · refine ⟨hne, hsub.trans subset_union_right, hp, fun D hD hpD hCD => ?_⟩
      obtain ⟨x, hx⟩ := hne
      rcases hsplit hpD hD with h | h
      · exact (hdisj x (h (hCD hx)) (hsub hx)).elim
      · exact hmax D h hpD hCD

theorem glue_sdiff {Γ₁ Γ₂ : Drawing S} (h : Γ₁.U ∩ Γ₂.U ⊆ Γ₁.V ∩ Γ₂.V) :
    (Γ₁.U ∪ Γ₂.U) \ (Γ₁.V ∪ Γ₂.V) = (Γ₁.U \ Γ₁.V) ∪ (Γ₂.U \ Γ₂.V) := by
  ext x
  constructor
  · rintro ⟨hx | hx, hn⟩
    · exact Or.inl ⟨hx, fun h' => hn (Or.inl h')⟩
    · exact Or.inr ⟨hx, fun h' => hn (Or.inr h')⟩
  · rintro (⟨hx, hn⟩ | ⟨hx, hn⟩)
    · refine ⟨Or.inl hx, ?_⟩
      rintro (h' | h')
      · exact hn h'
      · exact hn (h ⟨hx, Γ₂.V_subset_U h'⟩).1
    · refine ⟨Or.inr hx, ?_⟩
      rintro (h' | h')
      · exact hn (h ⟨Γ₁.V_subset_U h', hx⟩).2
      · exact hn h'

theorem glue_arc {Γ₁ Γ₂ : Drawing S} (h : Γ₁.U ∩ Γ₂.U ⊆ Γ₁.V ∩ Γ₂.V) :
    arcComponentsIn ((Γ₁.U ∪ Γ₂.U) \ (Γ₁.V ∪ Γ₂.V)) =
      arcComponentsIn (Γ₁.U \ Γ₁.V) ∪ arcComponentsIn (Γ₂.U \ Γ₂.V) := by
  rw [glue_sdiff h]
  refine arcComponentsIn_union Γ₁.isClosed_U Γ₂.isClosed_U sdiff_subset sdiff_subset ?_
  rintro x (⟨-, hn⟩ | ⟨-, hn⟩) hx₁ hx₂
  · exact hn (h ⟨hx₁, hx₂⟩).1
  · exact hn (h ⟨hx₁, hx₂⟩).2

/-- The union of two drawings that meet only in common vertices. -/
def _root_.GraphMinor.Surface.Drawing.glue (Γ₁ Γ₂ : Drawing S) (h : Γ₁.U ∩ Γ₂.U ⊆ Γ₁.V ∩ Γ₂.V) :
  Drawing S where
  U := Γ₁.U ∪ Γ₂.U
  V := Γ₁.V ∪ Γ₂.V
  V_subset_U := union_subset_union Γ₁.V_subset_U Γ₂.V_subset_U
  isClosed_U := Γ₁.isClosed_U.union Γ₂.isClosed_U
  finite_V := Γ₁.finite_V.union Γ₂.finite_V
  finite_edges := by
    rw [glue_arc h]
    exact Γ₁.finite_edges.union Γ₂.finite_edges
  edge_cond := by
    intro e he
    rw [glue_arc h] at he
    rcases he with he | he
    · have hcap : closure e ∩ (Γ₁.V ∪ Γ₂.V) = closure e ∩ Γ₁.V := by
        ext x
        constructor
        · rintro ⟨hx, hv | hv⟩
          · exact ⟨hx, hv⟩
          · exact ⟨hx, (h ⟨Γ₁.closure_subset_U he hx, Γ₂.V_subset_U hv⟩).1⟩
        · exact fun hx => ⟨hx.1, Or.inl hx.2⟩
      rw [hcap]
      exact Γ₁.edge_cond e he
    · have hcap : closure e ∩ (Γ₁.V ∪ Γ₂.V) = closure e ∩ Γ₂.V := by
        ext x
        constructor
        · rintro ⟨hx, hv | hv⟩
          · exact ⟨hx, (h ⟨Γ₁.V_subset_U hv, Γ₂.closure_subset_U he hx⟩).2⟩
          · exact ⟨hx, hv⟩
        · exact fun hx => ⟨hx.1, Or.inr hx.2⟩
      rw [hcap]
      exact Γ₂.edge_cond e he

theorem _root_.GraphMinor.Surface.Drawing.glue_E {Γ₁ Γ₂ : Drawing S} (h : Γ₁.U ∩ Γ₂.U ⊆ Γ₁.V ∩
  Γ₂.V) :
    (Γ₁.glue Γ₂ h).E = Γ₁.E ∪ Γ₂.E :=
  glue_arc h

/-- Two lines with the same two ends and nothing else in common form an `O`-arc. -/
theorem isOArc_union [T2Space S] {L₁ L₂ : Set S} {a b : S} (h₁ : IsLineWithEnds L₁ a b)
    (h₂ : IsLineWithEnds L₂ a b) (hcap : L₁ ∩ L₂ ⊆ {a, b}) : IsOArc (L₁ ∪ L₂) := by
  obtain ⟨f₁, a₁, b₁⟩ := h₁
  obtain ⟨f₂, a₂, b₂⟩ := h₂
  let I := unitInterval
  -- The loop that runs along `L₁` and back along `L₂`.
  let up : I → I := fun t => Set.projIcc 0 1 zero_le_one (2 * t.1)
  let dn : I → I := fun t => Set.projIcc 0 1 zero_le_one (2 - 2 * t.1)
  let γ : I → S := fun t => if t.1 ≤ 1 / 2 then (f₁ (up t)).1 else (f₂ (dn t)).1
  have hup : ∀ t : I, t.1 ≤ 1 / 2 → (up t).1 = 2 * t.1 := fun t ht => by
    simp only [up]
    rw [Set.projIcc_of_mem zero_le_one ⟨by have := t.2.1; positivity, by linarith⟩]
  have hdn : ∀ t : I, 1 / 2 ≤ t.1 → (dn t).1 = 2 - 2 * t.1 := fun t ht => by
    simp only [dn]
    rw [Set.projIcc_of_mem zero_le_one ⟨by have := t.2.2; linarith, by linarith⟩]
  have hγ : Continuous γ := by
    refine Continuous.if_le ?_ ?_ continuous_subtype_val continuous_const ?_
    · exact continuous_subtype_val.comp (f₁.continuous.comp (by fun_prop))
    · exact continuous_subtype_val.comp (f₂.continuous.comp (by fun_prop))
    · intro t ht
      have e₁ : up t = 1 := Subtype.ext (by rw [hup t ht.le]; rw [ht]; norm_num)
      have e₂ : dn t = 1 := Subtype.ext (by rw [hdn t ht.ge]; rw [ht]; norm_num)
      rw [e₁, e₂, b₁, b₂]
  have hγ₀ : ∀ t : I, t.1 ≤ 1 / 2 → γ t = (f₁ (up t)).1 := fun t ht => by simp only [γ, ht,
    ite_true]
  have hγ₁ : ∀ t : I, ¬ t.1 ≤ 1 / 2 → γ t = (f₂ (dn t)).1 := fun t ht => by
    simp only [γ, ht, ite_false]
  have hup0 : ∀ t : I, t.1 ≤ 1 / 2 → up t = 0 → t = 0 := fun t ht h => by
    have := congrArg Subtype.val h
    rw [hup t ht] at this
    exact Subtype.ext (by simpa using this)
  have hup1 : ∀ t : I, t.1 ≤ 1 / 2 → up t = 1 → t.1 = 1 / 2 := fun t ht h => by
    have := congrArg Subtype.val h
    rw [hup t ht] at this
    have h' : 2 * t.1 = 1 := this
    linarith
  have hdn0 : ∀ t : I, ¬ t.1 ≤ 1 / 2 → dn t = 0 → t = 1 := fun t ht h => by
    have := congrArg Subtype.val h
    rw [hdn t (le_of_not_ge ht)] at this
    have h' : 2 - 2 * t.1 = 0 := this
    exact Subtype.ext (by change t.1 = 1; linarith)
  have hdn1 : ∀ t : I, ¬ t.1 ≤ 1 / 2 → dn t ≠ 1 := fun t ht h => by
    have := congrArg Subtype.val h
    rw [hdn t (le_of_not_ge ht)] at this
    have h' : 2 - 2 * t.1 = 1 := this
    exact ht (by linarith)
  have cross : ∀ s t : I, s.1 ≤ 1 / 2 → ¬ t.1 ≤ 1 / 2 → γ s = γ t → s = 0 ∧ t = 1 := by
    intro s t hs ht h
    rw [hγ₀ s hs, hγ₁ t ht] at h
    have hmem : (f₁ (up s)).1 ∈ L₁ ∩ L₂ := ⟨(f₁ _).2, h ▸ (f₂ _).2⟩
    rcases hcap hmem with h' | h'
    · have e₁ : up s = 0 := f₁.injective (Subtype.ext (h'.trans a₁.symm))
      have e₂ : dn t = 0 := f₂.injective (Subtype.ext ((h.symm.trans h').trans a₂.symm))
      exact ⟨hup0 s hs e₁, hdn0 t ht e₂⟩
    · have e₂ : dn t = 1 := f₂.injective (Subtype.ext ((h.symm.trans h').trans b₂.symm))
      exact absurd e₂ (hdn1 t ht)
  have hinj : ∀ s t : I, γ s = γ t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
    intro s t h
    by_cases hs : s.1 ≤ 1 / 2 <;> by_cases ht : t.1 ≤ 1 / 2
    · rw [hγ₀ s hs, hγ₀ t ht] at h
      have e : up s = up t := f₁.injective (Subtype.ext h)
      have := congrArg Subtype.val e
      rw [hup s hs, hup t ht] at this
      exact Or.inl (Subtype.ext (by linarith))
    · exact Or.inr (Or.inl (cross s t hs ht h))
    · obtain ⟨e₁, e₂⟩ := cross t s ht hs h.symm
      exact Or.inr (Or.inr ⟨e₂, e₁⟩)
    · rw [hγ₁ s hs, hγ₁ t ht] at h
      have e : dn s = dn t := f₂.injective (Subtype.ext h)
      have := congrArg Subtype.val e
      rw [hdn s (le_of_not_ge hs), hdn t (le_of_not_ge ht)] at this
      exact Or.inl (Subtype.ext (by linarith))
  have hγ01 : γ 0 = γ 1 := by
    have e₀ : up 0 = 0 := Subtype.ext (by rw [hup 0 (by norm_num)]; simp)
    have e₁ : dn 1 = 0 := Subtype.ext (by rw [hdn 1 (by norm_num)]; norm_num)
    rw [hγ₀ 0 (by norm_num), hγ₁ 1 (by norm_num), e₀, e₁, a₁, a₂]
  let q : I → Circle := arcParam 1
  have hq : Continuous q := (arcParam 1).continuous
  have hqs : Function.Surjective q := arcParam_surjective 1
  have hqq : Topology.IsQuotientMap q := hq.isClosedMap.isQuotientMap hq hqs
  let G : Circle → S := fun z => γ (Function.surjInv hqs z)
  have hGq : G ∘ q = γ := by
    funext t
    have hsi : q (Function.surjInv hqs (q t)) = q t := Function.surjInv_eq hqs _
    change γ (Function.surjInv hqs (q t)) = γ t
    rcases arcParam_eq_iff 1 hsi with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h]
    · rw [h₁, h₂, hγ01]
    · rw [h₁, h₂, hγ01]
  have hG : Continuous G := hqq.continuous_iff.mpr (hGq ▸ hγ)
  have hGi : Function.Injective G := by
    intro z w h
    rw [← Function.surjInv_eq hqs z, ← Function.surjInv_eq hqs w]
    rcases hinj _ _ h with h' | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h']
    · rw [h₁, h₂]
      change arcParam 1 0 = arcParam 1 1
      simp
    · rw [h₁, h₂]
      change arcParam 1 1 = arcParam 1 0
      simp
  have hrange : range G = L₁ ∪ L₂ := by
    have hγr : range γ = L₁ ∪ L₂ := by
      apply subset_antisymm
      · rintro _ ⟨t, rfl⟩
        by_cases ht : t.1 ≤ 1 / 2
        · rw [hγ₀ t ht]
          exact Or.inl (f₁ _).2
        · rw [hγ₁ t ht]
          exact Or.inr (f₂ _).2
      · rintro x (hx | hx)
        · obtain ⟨u, hu⟩ := f₁.surjective ⟨x, hx⟩
          let t : I := ⟨u.1 / 2, by have := u.2.1; positivity, by have := u.2.2; linarith⟩
          have ht : t.1 ≤ 1 / 2 := by
            change u.1 / 2 ≤ 1 / 2
            have := u.2.2
            linarith
          have e : up t = u := Subtype.ext (by
            rw [hup t ht]
            change 2 * (u.1 / 2) = u.1
            ring)
          exact ⟨t, by rw [hγ₀ t ht, e, hu]⟩
        · obtain ⟨u, hu⟩ := f₂.surjective ⟨x, hx⟩
          by_cases hu1 : u = 1
          · subst hu1
            have hxb : x = b := by
              have := congrArg Subtype.val hu
              exact this.symm.trans b₂
            let t : I := ⟨1 / 2, by norm_num, by norm_num⟩
            have ht : t.1 ≤ 1 / 2 := le_rfl
            have e : up t = 1 := Subtype.ext (by
              rw [hup t ht]
              change (2 : ℝ) * (1 / 2) = 1
              norm_num)
            exact ⟨t, by rw [hγ₀ t ht, e, b₁, hxb]⟩
          · have hu' : u.1 < 1 := lt_of_le_of_ne u.2.2 fun h => hu1 (Subtype.ext h)
            let t : I := ⟨1 - u.1 / 2, by have := u.2.2; linarith, by have := u.2.1; linarith⟩
            have ht : ¬ t.1 ≤ 1 / 2 := by
              change ¬ 1 - u.1 / 2 ≤ 1 / 2
              linarith
            have e : dn t = u := Subtype.ext (by
              rw [hdn t (le_of_not_ge ht)]
              change 2 - 2 * (1 - u.1 / 2) = u.1
              ring)
            exact ⟨t, by rw [hγ₁ t ht, e, hu]⟩
    rw [← hγr, ← hGq, range_comp, hqs.range_eq, image_univ]
  have hemb := hG.isClosedEmbedding hGi
  rw [← hrange]
  exact ⟨hemb.isEmbedding.toHomeomorph⟩

/-- An `O`-arc in an open disc bounds a closed disc in that open disc. -/
theorem exists_disc_in_openDisc [T2Space S] {r J : Set S} (hr : IsOpenDisc r) (hJ : IsOArc J)
    (hsub : J ⊆ r) : ∃ Δ : Set S, Δ ⊆ r ∧ IsClosedDisc Δ ∧ discBd Δ = J := by
  obtain ⟨-, ⟨φ⟩⟩ := hr
  have hJc : IsCompact J := by
    obtain ⟨f⟩ := hJ
    have : J = range fun x : Circle => (f x).1 := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx⟩ := f.surjective ⟨y, hy⟩
        exact ⟨x, by simp [hx]⟩
      · rintro ⟨x, rfl⟩
        exact (f x).2
    rw [this]
    exact isCompact_range (by fun_prop)
  -- The points of the plane that correspond to `J` lie in a smaller closed disc.
  let T : Set r := Subtype.val ⁻¹' J
  have hT : IsCompact T := Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr (by
    rw [Subtype.image_preimage_coe]
    rwa [inter_eq_right.mpr hsub])
  have hT' : IsCompact (φ.symm '' T) := hT.image φ.symm.continuous
  have hbd : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ x ∈ φ.symm '' T, ‖(x : EuclideanPlane)‖ ≤ ρ := by
    by_cases hne : (φ.symm '' T).Nonempty
    · obtain ⟨x₀, hx₀, hmax⟩ := hT'.exists_isMaxOn hne
        (f := fun x : OpenUnitDisc => ‖(x : EuclideanPlane)‖) (by fun_prop)
      have hn : ‖(x₀ : EuclideanPlane)‖ < 1 := by
        have := x₀.2
        simpa [OpenUnitDisc] using this
      refine ⟨(‖(x₀ : EuclideanPlane)‖ + 1) / 2, by positivity, by linarith, fun x hx => ?_⟩
      have := hmax hx
      have this' : ‖(x : EuclideanPlane)‖ ≤ ‖(x₀ : EuclideanPlane)‖ := this
      linarith
    · refine ⟨1 / 2, by norm_num, by norm_num, fun x hx => ?_⟩
      exact absurd ⟨x, hx⟩ hne
  obtain ⟨ρ, h0, h1, hρ⟩ := hbd
  have hin : ∀ x : ClosedUnitDisc, ρ • (x : EuclideanPlane) ∈ OpenUnitDisc := by
    intro x
    have hx : ‖(x : EuclideanPlane)‖ ≤ 1 := by
      have := x.2
      simpa [ClosedUnitDisc] using this
    have : ‖ρ • (x : EuclideanPlane)‖ < 1 := by
      rw [norm_smul, Real.norm_of_nonneg h0.le]
      nlinarith
    simpa [OpenUnitDisc] using this
  let m : ClosedUnitDisc → S := fun x => (φ ⟨ρ • x.1, hin x⟩).1
  have hmc : Continuous m := by
    refine continuous_subtype_val.comp (φ.continuous.comp ?_)
    exact Continuous.subtype_mk (by fun_prop) _
  have hmi : Function.Injective m := by
    intro x y hxy
    have h₁ := φ.injective (Subtype.ext hxy)
    have h₂ : ρ • x.1 = ρ • y.1 := congrArg Subtype.val h₁
    exact Subtype.ext (smul_right_injective _ h0.ne' h₂)
  have : CompactSpace ClosedUnitDisc := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  have hemb := hmc.isClosedEmbedding hmi
  have hD : IsClosedDisc (range m) := ⟨hemb.isEmbedding.toHomeomorph⟩
  have hJD : J ⊆ range m := by
    intro y hy
    have hyr := hsub hy
    set z := φ.symm ⟨y, hyr⟩ with hz
    have hzn : ‖(z : EuclideanPlane)‖ ≤ ρ := hρ z ⟨⟨y, hyr⟩, hy, rfl⟩
    have hmem : ρ⁻¹ • (z : EuclideanPlane) ∈ ClosedUnitDisc := by
      have : ‖ρ⁻¹ • (z : EuclideanPlane)‖ ≤ 1 := by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg h0.le]
        exact (inv_mul_le_iff₀ h0).mpr (by simpa using hzn)
      simpa [ClosedUnitDisc] using this
    refine ⟨⟨_, hmem⟩, ?_⟩
    have heq : (⟨ρ • (ρ⁻¹ • (z : EuclideanPlane)), hin ⟨_, hmem⟩⟩ : OpenUnitDisc) = z :=
      Subtype.ext (smul_inv_smul₀ h0.ne' _)
    change (φ _).1 = y
    rw [heq, hz, φ.apply_symm_apply]
  obtain ⟨Δ, ⟨hsubΔ, hd, hb, -⟩, -⟩ := disc_oArc (range m) J hD hJD hJ
  refine ⟨Δ, hsubΔ.trans ?_, hd, hb⟩
  rintro _ ⟨x, rfl⟩
  exact (φ _).2

end GraphMinor.GM11
