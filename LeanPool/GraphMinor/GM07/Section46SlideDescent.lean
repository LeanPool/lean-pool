/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46DiscSlide
import LeanPool.GraphMinor.GM07.Section46IntervalSlide
import LeanPool.GraphMinor.GM07.Section2Base
import LeanPool.GraphMinor.GM07.NetSwapBasic

/-!
# The slide along the matching in `Σ′`

We bring the slide of `Δ` down to `Σ′` by the quotient map `ψ`, for one
side, and then for all the central edges at once. This gives the
homeomorphism for the sentence of VII (4.6), page 227, that `H₃` may be
chosen to meet the matching only at vertices of `θ⁻¹(G)`.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

/-- A homeomorphism which respects the fibres of a quotient map comes down. -/
theorem exists_descended_homeo {D S' : Type*} [TopologicalSpace D] [TopologicalSpace S']
    {ψ : D → S'} (hq : IsQuotientMap ψ) (b : D ≃ₜ D)
    (h₁ : ∀ x y, ψ x = ψ y → ψ (b x) = ψ (b y))
    (h₂ : ∀ x y, ψ x = ψ y → ψ (b.symm x) = ψ (b.symm y)) :
    ∃ β : S' ≃ₜ S', ∀ x, β (ψ x) = ψ (b x) := by
  choose sec hsec using hq.surjective
  have ht : ∀ x, ψ (b (sec (ψ x))) = ψ (b x) := fun x => h₁ _ _ (hsec _)
  have hi : ∀ x, ψ (b.symm (sec (ψ x))) = ψ (b.symm x) := fun x => h₂ _ _ (hsec _)
  let β : S' ≃ₜ S' :=
    { toFun := fun y => ψ (b (sec y))
      invFun := fun y => ψ (b.symm (sec y))
      left_inv := fun y => by
        obtain ⟨x, rfl⟩ := hq.surjective y
        change ψ (b.symm (sec (ψ (b (sec (ψ x)))))) = ψ x
        rw [ht, hi, b.symm_apply_apply]
      right_inv := fun y => by
        obtain ⟨x, rfl⟩ := hq.surjective y
        change ψ (b (sec (ψ (b.symm (sec (ψ x)))))) = ψ x
        rw [hi, ht, b.apply_symm_apply]
      continuous_toFun := by
        rw [hq.continuous_iff]
        have : (fun y => ψ (b (sec y))) ∘ ψ = ψ ∘ b := funext ht
        rw [this]
        exact hq.continuous.comp b.continuous
      continuous_invFun := by
        rw [hq.continuous_iff]
        have : (fun y => ψ (b.symm (sec y))) ∘ ψ = ψ ∘ b.symm := funext hi
        rw [this]
        exact hq.continuous.comp b.symm.continuous }
  exact ⟨β, ht⟩

section

variable {S S' : Type} [TopologicalSpace S] [TopologicalSpace S'] (N : Net S)
  {ψ : N.D → S'}

omit [TopologicalSpace S'] in
private theorem slide_compat (hφ : ∀ x y, ψ x = ψ y → N.φ x = N.φ y) (i : Fin N.r)
    {a c : unitInterval} (ha : a ∈ Ioo (0 : unitInterval) 1) (hc : c ∈ Ioo (0 : unitInterval) 1)
    (hsame : ∀ r ∈ Icc a c, ψ (N.f i r) = ψ (N.g i r)) {τ : unitInterval → unitInterval}
    (hτ : ∀ r ∈ Ioo a c, τ r ∈ Icc a c) (hfix : ∀ r, r ∉ Ioo a c → τ r = r)
    (b : N.D → N.D) (hf : ∀ r, b (N.f i r) = N.f i (τ r)) (hg : ∀ r, b (N.g i r) = N.g i (τ r))
    (hoff : ∀ x ∈ bd N.D, x ∉ N.f i '' Ioo (0 : unitInterval) 1 →
      x ∉ N.g i '' Ioo (0 : unitInterval) 1 → b x = x) :
    (∀ x ∈ bd N.D, x ∉ N.f i '' Ioo a c → x ∉ N.g i '' Ioo a c → b x = x) ∧
      ∀ x y, ψ x = ψ y → ψ (b x) = ψ (b y) := by
  have hfix' : ∀ x ∈ bd N.D, x ∉ N.f i '' Ioo a c → x ∉ N.g i '' Ioo a c → b x = x := by
    intro x hx h₁ h₂
    by_cases h₃ : x ∈ N.f i '' Ioo (0 : unitInterval) 1
    · obtain ⟨r, -, rfl⟩ := h₃
      rw [hf, hfix r fun h => h₁ ⟨r, h, rfl⟩]
    by_cases h₄ : x ∈ N.g i '' Ioo (0 : unitInterval) 1
    · obtain ⟨r, -, rfl⟩ := h₄
      rw [hg, hfix r fun h => h₂ ⟨r, h, rfl⟩]
    exact hoff x hx h₃ h₄
  have hsub : Ioo a c ⊆ Ioo (0 : unitInterval) 1 := fun r hr => ⟨ha.1.trans hr.1, hr.2.trans hc.2⟩
  have hside : ∀ x, (x ∈ N.f i '' Ioo a c ∨ x ∈ N.g i '' Ioo a c) → ∀ y, ψ x = ψ y →
      ψ (b x) = ψ (b y) := by
    intro x hx y hxy
    have hφxy := hφ x y hxy
    obtain ⟨r, hr, hxr⟩ : ∃ r ∈ Ioo a c, x = N.f i r ∨ x = N.g i r := by
      rcases hx with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
      · exact ⟨r, hr, .inl rfl⟩
      · exact ⟨r, hr, .inr rfl⟩
    have hpair := N.fiber_eq_pair_of_mem_Ioo i (hsub hr)
    have hval : ψ (b (N.f i r)) = ψ (b (N.g i r)) := by
      rw [hf, hg]
      exact hsame _ (hτ r hr)
    have hy : y ∈ N.φ ⁻¹' {N.φ (N.f i r)} := by
      change N.φ y = N.φ (N.f i r)
      rcases hxr with rfl | rfl
      · exact hφxy.symm
      · rw [← hφxy, N.pasting_eq]
    rw [hpair] at hy
    rcases hxr with rfl | rfl <;> rcases hy with rfl | hy
    · rfl
    · rw [show y = N.g i r from hy, hval]
    · exact hval.symm
    · rw [show y = N.g i r from hy]
  refine ⟨hfix', fun x y hxy => ?_⟩
  by_cases hx : x ∈ N.f i '' Ioo a c ∨ x ∈ N.g i '' Ioo a c
  · exact hside x hx y hxy
  by_cases hy : y ∈ N.f i '' Ioo a c ∨ y ∈ N.g i '' Ioo a c
  · exact (hside y hy x hxy.symm).symm
  push Not at hx hy
  by_cases hxb : x ∈ bd N.D
  · by_cases hyb : y ∈ bd N.D
    · rw [hfix' x hxb hx.1 hx.2, hfix' y hyb hy.1 hy.2, hxy]
    · have := N.interior_inj y hyb x (hφ _ _ hxy.symm)
      rw [this]
  · have := N.interior_inj x hxb y (hφ _ _ hxy)
    rw [this]

/-- The slide along one central edge, in `Σ′`. -/
theorem Net.exists_side_slide (hq : IsQuotientMap ψ) (hφ : ∀ x y, ψ x = ψ y → N.φ x = N.φ y)
    (i : Fin N.r) {a c : unitInterval} (ha : a ∈ Ioo (0 : unitInterval) 1)
    (hc : c ∈ Ioo (0 : unitInterval) 1)
    (hsame : ∀ r ∈ Icc a c, ψ (N.f i r) = ψ (N.g i r)) (σ : unitInterval ≃ₜ unitInterval)
    (hσ : ∀ r, r ∉ Ioo a c → σ r = r) :
    ∃ β : S' ≃ₜ S', (∀ r, β (ψ (N.f i r)) = ψ (N.f i (σ r))) ∧
      ∀ x ∈ bd N.D, x ∉ N.f i '' Ioo a c → x ∉ N.g i '' Ioo a c → β (ψ x) = ψ x := by
  have h0 : σ 0 = 0 := hσ 0 fun h => not_lt_of_ge bot_le (ha.1.trans h.1)
  have h1 : σ 1 = 1 := hσ 1 fun h => not_lt_of_ge le_top (h.2.trans hc.2)
  have hσ' : ∀ r, r ∉ Ioo a c → σ.symm r = r := fun r hr => by
    rw [σ.symm_apply_eq, hσ r hr]
  have hin : ∀ τ : unitInterval ≃ₜ unitInterval, (∀ r, r ∉ Ioo a c → τ r = r) →
      ∀ r ∈ Ioo a c, τ r ∈ Ioo a c := by
    intro τ hτ r hr
    by_contra h
    have heq := τ.injective (hτ _ h)
    exact h (by rw [heq]; exact hr)
  have h0' : σ.symm 0 = 0 := by rw [← h0, σ.symm_apply_apply, h0]
  have h1' : σ.symm 1 = 1 := by rw [← h1, σ.symm_apply_apply, h1]
  obtain ⟨b, hbf, hbg, hboff⟩ := N.exists_disc_slide i σ h0 h1
  have hbf' : ∀ r, b.symm (N.f i r) = N.f i (σ.symm r) := fun r => by
    rw [Homeomorph.symm_apply_eq, hbf, σ.apply_symm_apply]
  have hbg' : ∀ r, b.symm (N.g i r) = N.g i (σ.symm r) := fun r => by
    rw [Homeomorph.symm_apply_eq, hbg, σ.apply_symm_apply]
  have hboff' : ∀ x ∈ bd N.D, x ∉ N.f i '' Ioo (0 : unitInterval) 1 →
      x ∉ N.g i '' Ioo (0 : unitInterval) 1 → b.symm x = x := fun x hx h₁ h₂ => by
    rw [Homeomorph.symm_apply_eq, hboff x hx h₁ h₂]
  obtain ⟨hfix, hc₁⟩ := slide_compat N hφ i ha hc hsame
    (fun r hr => Ioo_subset_Icc_self (hin σ hσ r hr)) hσ b hbf hbg hboff
  obtain ⟨-, hc₂⟩ := slide_compat N hφ i ha hc hsame
    (fun r hr => Ioo_subset_Icc_self (hin σ.symm hσ' r hr)) hσ' b.symm hbf' hbg' hboff'
  obtain ⟨β, hβ⟩ := exists_descended_homeo hq b hc₁ hc₂
  refine ⟨β, fun r => by rw [hβ, hbf], fun x hx h₁ h₂ => by rw [hβ, hfix x hx h₁ h₂]⟩

/-- The slide along all the central edges at once, in `Σ′`. -/
theorem Net.exists_slide_family {ι : Type*} [Finite ι] (hq : IsQuotientMap ψ)
    (hφ : ∀ x y, ψ x = ψ y → N.φ x = N.φ y) (i : ι → Fin N.r) (hi : Function.Injective i)
    (a c : ι → unitInterval) (ha : ∀ e, a e ∈ Ioo (0 : unitInterval) 1)
    (hc : ∀ e, c e ∈ Ioo (0 : unitInterval) 1)
    (hsame : ∀ e, ∀ r ∈ Icc (a e) (c e), ψ (N.f (i e) r) = ψ (N.g (i e) r))
    {X : Set S'} (hX : X.Finite) (Y : ι → Set unitInterval) (hYf : ∀ e, (Y e).Finite)
    (hY : ∀ e, Y e ⊆ Ioo (a e) (c e))
    (hcard : ∀ e, {r ∈ Ioo (a e) (c e) | ψ (N.f (i e) r) ∈ X}.ncard ≤ (Y e).ncard) :
    ∃ β : S' ≃ₜ S',
      (∀ x ∈ bd N.D, (∀ e, x ∉ N.f (i e) '' Ioo (a e) (c e) ∧ x ∉ N.g (i e) '' Ioo (a e) (c e)) →
        β (ψ x) = ψ x) ∧
      (∀ e, ∀ r' ∈ Ioo (a e) (c e), ∃ r ∈ Ioo (a e) (c e), β (ψ (N.f (i e) r)) = ψ (N.f (i e) r')) ∧
      (∀ e, ∀ r ∈ Ioo (a e) (c e), ψ (N.f (i e) r) ∈ X → ∃ r' ∈ Y e,
        β (ψ (N.f (i e) r)) = ψ (N.f (i e) r')) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hsub : ∀ e, Ioo (a e) (c e) ⊆ Ioo (0 : unitInterval) 1 := fun e r hr =>
    ⟨(ha e).1.trans hr.1, hr.2.trans (hc e).2⟩
  have hother : ∀ e e', e ≠ e' → ∀ r ∈ Ioo (a e) (c e),
      N.f (i e) r ∉ N.f (i e') '' Ioo (a e') (c e') ∧ N.f (i e) r ∉ N.g (i e') '' Ioo (a e') (c e')
        := by
    intro e e' hne r hr
    constructor
    · rintro ⟨r', -, hr'⟩
      exact N.internally_disjoint_ff _ _ (fun h => hne (hi h)) r (hsub e hr) ⟨r', hr'⟩
    · rintro ⟨r', -, hr'⟩
      exact N.internally_disjoint_fg _ _ r (hsub e hr) ⟨r', hr'⟩
  have hfbd : ∀ j r, N.f j r ∈ bd N.D := fun j r => N.range_f_subset_bd j ⟨r, rfl⟩
  have key : ∀ A : Finset ι, ∃ β : S' ≃ₜ S',
      (∀ x ∈ bd N.D, (∀ e ∈ A, x ∉ N.f (i e) '' Ioo (a e) (c e) ∧
        x ∉ N.g (i e) '' Ioo (a e) (c e)) → β (ψ x) = ψ x) ∧
      (∀ e ∈ A, ∀ r' ∈ Ioo (a e) (c e), ∃ r ∈ Ioo (a e) (c e),
        β (ψ (N.f (i e) r)) = ψ (N.f (i e) r')) ∧
      (∀ e ∈ A, ∀ r ∈ Ioo (a e) (c e), ψ (N.f (i e) r) ∈ X → ∃ r' ∈ Y e,
        β (ψ (N.f (i e) r)) = ψ (N.f (i e) r')) := by
    intro A
    induction A using Finset.induction_on with
    | empty => exact ⟨Homeomorph.refl S', fun _ _ _ => rfl, by simp, by simp⟩
    | insert e₀ A he₀ ih =>
      obtain ⟨β, hβ₁, hβ₂, hβ₃⟩ := ih
      have hinj : InjOn (fun r => ψ (N.f (i e₀) r)) (Ioo (a e₀) (c e₀)) := by
        intro r hr r' hr' h
        exact N.injective_f _ (N.injOn_image_open_side _ ⟨r, hsub e₀ hr, rfl⟩ ⟨r', hsub e₀ hr', rfl⟩
          (hφ _ _ h))
      have hXf : {r ∈ Ioo (a e₀) (c e₀) | ψ (N.f (i e₀) r) ∈ X}.Finite := by
        refine Set.Finite.of_finite_image (f := fun r => ψ (N.f (i e₀) r)) (hX.subset ?_)
          (hinj.mono fun r hr => hr.1)
        rintro _ ⟨r, hr, rfl⟩
        exact hr.2
      obtain ⟨σ, hσf, hσX⟩ := exists_interval_slide hXf (hYf e₀) (fun r hr => hr.1) (hY e₀)
        (hcard e₀)
      obtain ⟨γ, hγf, hγoff⟩ := N.exists_side_slide hq hφ (i e₀) (ha e₀) (hc e₀) (hsame e₀) σ hσf
      have hfixA : ∀ r ∈ Ioo (a e₀) (c e₀), β (ψ (N.f (i e₀) r)) = ψ (N.f (i e₀) r) := by
        intro r hr
        apply hβ₁ _ (hfbd _ _)
        intro e he
        exact hother e₀ e (fun h => he₀ (h ▸ he)) r hr
      have hfix₀ : ∀ e ∈ A, ∀ r ∈ Ioo (a e) (c e), γ (ψ (N.f (i e) r)) = ψ (N.f (i e) r) := by
        intro e he r hr
        have hne : e ≠ e₀ := fun h => he₀ (h ▸ he)
        exact hγoff _ (hfbd _ _) (hother e e₀ hne r hr).1 (hother e e₀ hne r hr).2
      have hσin : ∀ r ∈ Ioo (a e₀) (c e₀), σ r ∈ Ioo (a e₀) (c e₀) := by
        intro r hr
        by_contra h
        have heq := σ.injective (hσf _ h)
        exact h (by rw [heq]; exact hr)
      refine ⟨β.trans γ, ?_, ?_, ?_⟩
      · intro x hx h
        change γ (β (ψ x)) = ψ x
        rw [hβ₁ x hx fun e he => h e (Finset.mem_insert_of_mem he)]
        exact hγoff x hx (h e₀ (Finset.mem_insert_self _ _)).1 (h e₀ (Finset.mem_insert_self _ _)).2
      · intro e he r' hr'
        rcases Finset.mem_insert.mp he with rfl | heA
        · have hin : σ.symm r' ∈ Ioo (a e) (c e) := by
            by_contra h
            have h' := hσf _ h
            rw [σ.apply_symm_apply] at h'
            exact h (h' ▸ hr')
          refine ⟨σ.symm r', hin, ?_⟩
          change γ (β (ψ _)) = _
          rw [hfixA _ hin, hγf, σ.apply_symm_apply]
        · obtain ⟨r, hr, hrr⟩ := hβ₂ e heA r' hr'
          refine ⟨r, hr, ?_⟩
          change γ (β (ψ _)) = _
          rw [hrr, hfix₀ e heA r' hr']
      · intro e he r hr hrX
        rcases Finset.mem_insert.mp he with rfl | heA
        · refine ⟨σ r, hσX r ⟨hr, hrX⟩, ?_⟩
          change γ (β (ψ _)) = _
          rw [hfixA r hr, hγf]
        · obtain ⟨r', hr', hrr⟩ := hβ₃ e heA r hr hrX
          refine ⟨r', hr', ?_⟩
          change γ (β (ψ _)) = _
          rw [hrr, hfix₀ e heA r' (hY e hr')]
  obtain ⟨β, h₁, h₂, h₃⟩ := key Finset.univ
  exact ⟨β, fun x hx h => h₁ x hx fun e _ => h e, fun e => h₂ e (Finset.mem_univ e),
    fun e => h₃ e (Finset.mem_univ e)⟩

end

end GraphMinor.GM07
