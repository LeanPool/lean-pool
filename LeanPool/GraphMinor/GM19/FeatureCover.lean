/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FeatureForm

/-!
# A local cocycle from a function on a space that maps onto a surface

Let `F` map a compact space `D` onto `S`, and let `g` be a function on `D` with values in a finite
group. Suppose that the
difference of `g` on two points of one fibre of `F` has closed level sets. The copies of `D` indexed
by the group, pasted along
the fibres of `F` with the shift by `g`, form a finite cover of `S`, and this cover gives a local
cocycle on `S` with `g` as a
primitive (`exists_cocycle_quot`). It is the construction of `exists_cocycle`, with the map `F` in
place of a word.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Function GraphMinor.Surface

universe u

variable {D S : Type*} [TopologicalSpace D] [CompactSpace D] [T2Space D] [TopologicalSpace S]
  [T2Space S] {A : Type} [AddCommGroup A] [Finite A]

/-- Two points of the copies of `D` are the same when they lie on one fibre, at the same height
after the shift by `g`. -/
def qSetoid (F : D → S) (g : D → A) : Setoid (D × A) :=
  ⟨fun x y ↦ F x.1 = F y.1 ∧ -g x.1 + x.2 = -g y.1 + y.2, ⟨fun _ ↦ ⟨rfl, rfl⟩, fun h ↦ ⟨h.1.symm,
    h.2.symm⟩, fun h h' ↦ ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩⟩

/-- **A local cocycle from a map onto a surface.** -/
theorem exists_cocycle_quot [Nonempty D] {F : D → S} (hF : Continuous F) (hs : Surjective F) (g : D
  → A)
    (hcl : ∀ c : A, IsClosed {p : D × D | F p.1 = F p.2 ∧ g p.2 - g p.1 = c}) :
    ∃ φ : S → S → A, IsCoc φ ∧ (∃ N : Set (D × D), NearDiag N ∧ ∀ a b, (a, b) ∈ N → φ (F a) (F b)
      = -g a + g b) ∧
      ((∀ a, F a ∈ bd S → g a = 0) → BdTriv φ) := by
  classical
  let _ : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  have hrel : IsClosed {p : (D × A) × (D × A) | (qSetoid F g).r p.1 p.2} := by
    have e : {p : (D × A) × (D × A) | (qSetoid F g).r p.1 p.2} = ⋃ t : A, ⋃ u : A, ((fun p :
      (D × A) × (D × A) ↦ (p.1.1, p.2.1)) ⁻¹' {p : D × D | F p.1 = F p.2 ∧ g p.2 - g p.1 = u - t}) ∩
        ((fun p : (D × A) × (D × A) ↦ (p.1.2, p.2.2)) ⁻¹' {(t, u)}) := by
      ext ⟨⟨a, t⟩, ⟨b, u⟩⟩
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff,
        Prod.mk.injEq]
      constructor
      · rintro ⟨h₁, h₂⟩
        refine ⟨t, u, ⟨h₁, ?_⟩, rfl, rfl⟩
        have h₃ : -g a + t = -g b + u := h₂
        have h₄ : g b - g a = u - t := by
          have : g b + (-g a + t) = g b + (-g b + u) := by rw [h₃]
          simp only [add_neg_cancel_left] at this
          rw [← this]
          abel
        exact h₄
      · rintro ⟨t', u', ⟨h₁, h₂⟩, h₃, h₅⟩
        rw [← h₃, ← h₅] at h₂
        refine ⟨h₁, ?_⟩
        have h₄ : -g a + t = -g b + u := by
          have : g b = g a + (u - t) := by rw [← h₂]; abel
          rw [this]
          abel
        exact h₄
    rw [e]
    refine isClosed_iUnion_of_finite fun t ↦ isClosed_iUnion_of_finite fun u ↦ ?_
    refine ((hcl _).preimage (by fun_prop)).inter ((isClosed_singleton (x := (t,
      u))).preimage (by fun_prop))
  have ht : T2Space (Quotient (qSetoid F g)) := t2Space_quotient_of_isClosed (qSetoid F g) hrel
  let Z := Quotient (qSetoid F g)
  let mk : D × A → Z := Quotient.mk (qSetoid F g)
  have hmk : Continuous mk := continuous_quotient_mk'
  have hsound : ∀ {x y : D × A}, F x.1 = F y.1 → -g x.1 + x.2 = -g y.1 + y.2 → mk x = mk y
    := fun h₁ h₂ ↦ Quotient.sound ⟨h₁, h₂⟩
  have hexact : ∀ {x y : D × A}, mk x = mk y → F x.1 = F y.1 ∧ -g x.1 + x.2 = -g y.1 + y.2
    := fun h ↦ Quotient.exact h
  let τ : A → Z → Z := fun s ↦ Quotient.lift (fun x ↦ mk (x.1, x.2 + s)) (fun x y h ↦ hsound h.1 (by
    have h₂ : -g x.1 + x.2 = -g y.1 + y.2 := h.2
    simp only
    rw [← add_assoc, h₂, add_assoc]))
  have hτmk : ∀ s x, τ s (mk x) = mk (x.1, x.2 + s) := fun _ _ ↦ rfl
  have hτc : ∀ s, Continuous (τ s) := fun s ↦ Continuous.quotient_lift (hmk.comp (by fun_prop)) _
  have hexZ : ∀ z : Z, ∃ x, mk x = z := fun z ↦ Quotient.exists_rep z
  have hτ0 : ∀ z, τ 0 z = z := by
    intro z
    obtain ⟨x, rfl⟩ := hexZ z
    rw [hτmk, add_zero]
  have hτa : ∀ s t z, τ s (τ t z) = τ (t + s) z := by
    intro s t z
    obtain ⟨x, rfl⟩ := hexZ z
    rw [hτmk, hτmk, hτmk, add_assoc]
  have hfree : ∀ s z, τ s z = z → s = 0 := by
    intro s z he
    obtain ⟨x, rfl⟩ := hexZ z
    rw [hτmk] at he
    have h₁ := (hexact he).2
    simp only at h₁
    exact add_eq_left.mp (add_left_cancel h₁)
  let q : Z → S := Quotient.lift (fun x ↦ F x.1) (fun x y h ↦ h.1)
  have hq : Continuous q := Continuous.quotient_lift (hF.comp continuous_fst) _
  have hsq : Surjective q := fun y ↦ by
    obtain ⟨a, rfl⟩ := hs y
    exact ⟨mk (a, 0), rfl⟩
  have hfib : ∀ z z', q z = q z' → ∃ s, z' = τ s z := by
    intro z z' he
    obtain ⟨x, rfl⟩ := hexZ z
    obtain ⟨y, rfl⟩ := hexZ z'
    have h₁ : F x.1 = F y.1 := he
    refine ⟨-x.2 + (g x.1 + (-g y.1 + y.2)), ?_⟩
    rw [hτmk]
    refine hsound h₁.symm ?_
    simp only [add_neg_cancel_left, neg_add_cancel_left]
  have hfib' : ∀ s z, q (τ s z) = q z := by
    intro s z
    obtain ⟨x, rfl⟩ := hexZ z
    rfl
  choose l hl using hs
  let σ : S → Z := fun y ↦ mk (l y, g (l y))
  have hσ : ∀ y, q (σ y) = y := fun y ↦ hl y
  have hσf : ∀ a, σ (F a) = mk (a, g a) := fun a ↦ hsound (hl _) (by simp)
  obtain ⟨φ, V, hV, hφ, hφs, hinv⟩ := cocycle_of_cover τ hτc hτ0 hτa hfree q hq hsq hfib hfib' σ hσ
  have hP : Continuous fun a : D ↦ mk (a, 0) := hmk.comp (by fun_prop)
  refine ⟨φ, hφ, ⟨(fun p : D × D ↦ (mk (p.1, 0), mk (p.2, 0))) ⁻¹' V, fun a ↦ ?_,
    fun a b hab ↦ ?_⟩, fun hbd ↦ ?_⟩
  · have hc : Continuous fun p : D × D ↦ (mk (p.1, 0), mk (p.2, 0)) := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (hV (mk (a, 0)))
  · have h₂ := hinv (g b) _ _ hab
    rw [hτmk, hτmk] at h₂
    refine hφs _ _ _ ?_
    rw [hσf, hσf, hτmk]
    simp only [zero_add] at h₂ ⊢
    have e₃ : g a + (-g a + g b) = g b := add_neg_cancel_left _ _
    rw [e₃]
    exact h₂
  · have hcl' : IsClosed (bd S) := isClosed_bd S
    let K : Set Z := (fun a : D ↦ mk (a, 0)) '' (F ⁻¹' bd S)
    have hK : IsCompact K := ((hcl'.preimage hF).isCompact).image hP
    have hinj : InjOn q K := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ he
      refine hsound he ?_
      simp only
      rw [hbd a ha, hbd b hb]
    have : Nonempty Z := ⟨mk (Classical.arbitrary D, 0)⟩
    obtain ⟨q', hq', hql⟩ := exists_inv_of_compactOn hK hq.continuousOn hinj
    have hσK : ∀ x ∈ bd S, σ x ∈ K := fun x hx ↦ by
      have h₁ : F (l x) ∈ bd S := by rwa [hl x]
      refine ⟨l x, h₁, ?_⟩
      simp only [σ]
      rw [hbd _ h₁]
    have hσc : ContinuousOn σ (bd S) := by
      have hsub : bd S ⊆ q '' K := fun x hx ↦ ⟨σ x, hσK x hx, hσ x⟩
      refine (hq'.mono hsub).congr fun x hx ↦ ?_
      have h₁ := hql (hσK x hx)
      rw [hσ] at h₁
      exact h₁.symm
    refine ⟨0, {p | p.1 ∈ bd S → p.2 ∈ bd S → (σ p.1, σ p.2) ∈ V}, fun y ↦ ?_,
      fun x hx y hy hxy ↦ ?_⟩
    · by_cases hy : y ∈ bd S
      · have h₁ : ContinuousWithinAt (fun p : S × S ↦ (σ p.1, σ p.2)) (bd S ×ˢ bd S) (y, y) := by
          have h₂ := hσc.prodMap hσc
          exact h₂ (y, y) ⟨hy, hy⟩
        have h₃ := h₁ (hV (σ y))
        obtain ⟨u, hu, hus⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h₃
        refine Filter.mem_of_superset hu fun p hp h₄ h₅ ↦ ?_
        exact hus ⟨hp, h₄, h₅⟩
      · have h₁ : (bd S)ᶜ ×ˢ (univ : Set S) ∈ 𝓝 (y, y) := (hcl'.isOpen_compl.prod
        isOpen_univ).mem_nhds ⟨hy, mem_univ _⟩
        refine Filter.mem_of_superset h₁ fun p hp h₄ ↦ ?_
        exact absurd h₄ hp.1
    · have h₁ := hφs x y 0 (by rw [hτ0]; exact hxy hx hy)
      simp [h₁]

end GraphMinor.GM19
