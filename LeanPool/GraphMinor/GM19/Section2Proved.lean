/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section2
public import LeanPool.GraphMinor.GM19.CapExists
public import LeanPool.GraphMinor.GM19.Section4c
public import LeanPool.GraphMinor.GM20.Cited
public import LeanPool.GraphMinor.Surface.MoveCuff

import LeanPool.GraphMinor.GM19.Section15b
import LeanPool.GraphMinor.GM19.Thinning
import LeanPool.GraphMinor.GM19.UniverseLift1

/-!
# Graph Minors XIX: proved deductions from Section2 and Section4c

This file proves **Graph Minors XIX, (3.1)** (`theorem_3_1`) and **Graph Minors XIX, (2.1)**
(`theorem_2_1`, `gm19Theorem21`) in arbitrary surface and label universes, using the proved (4.1)
and `theorem21Topology_u`.
-/

@[expose] public section
namespace GraphMinor.GM19
open Set Function Topology GraphMinor.Surface
universe u w

/-- **Graph Minors XIX, (3.1)**, from (4.1) (Graph Minors XIX, Section 4, page 334): no colour
scheme
is bad. The paper's "we may choose it to satisfy `S₁`" is the induction on the capped surface, by
`GraphMinor.Surface.simplerWellFounded`. -/
theorem theorem_3_1_proof
    {S Shat : Type u} [TopologicalSpace S] [TopologicalSpace Shat] {α : Type w}
    (cap : IsCappedSurface S Shat) (χ : ColourScheme S α) : ¬ χ.IsBad := by
  intro hbad
  -- Choose a bad scheme with the capped surface minimal, which gives `S₁`.
  obtain ⟨X₀, ⟨β₀, D₀, hX₀, hbad₀⟩, hmin⟩ := (simplerWellFounded.{u}).has_min
    {X | ∃ (β : Type w) (D : CappedScheme.{u, w} β), (⟨D.Shat, D.iH⟩ : Σ X : Type u,
      TopologicalSpace X) = X ∧ D.χ.IsBad}
    ⟨_, α, ⟨S, Shat, cap, χ⟩, rfl, hbad⟩
  subst hX₀
  have hS1 : ∀ (Z : Type u) [TopologicalSpace Z], Nonempty (Z ≃ₜ D₀.Shat) → ConditionS1.{u, w} Z
    := by
    rintro Z _ ⟨e⟩ S' Shat' _ _ β χ' ⟨cap'⟩ hsimp hb
    exact hmin ⟨Shat', _⟩ ⟨β, ⟨S', Shat', cap', χ'⟩, rfl, hb⟩ (IsSimplerThan.of_homeo hsimp e)
  -- Pass to an orientedly bad scheme with infinitely many labels.
  obtain ⟨χ₁, -, hor₁⟩ := theorem_4_2_proof (D₀.χ.liftMap.isBad hbad₀)
  let 𝒜 : Set (CappedScheme.{u, w} ((Option β₀ × ℕ) × Bool)) :=
    {D | Nonempty (D.Shat ≃ₜ D₀.Shat) ∧ D.χ.IsOrientedlyBad}
  have hne : 𝒜.Nonempty := ⟨⟨_, _, D₀.cap, χ₁⟩, ⟨Homeomorph.refl _⟩, hor₁⟩
  -- Choose `Ω(3)`, `Ω(2)` minimal, which gives `S₂`.
  have hwf : WellFounded (Prod.Lex (fun a b : WQOKey ((Option β₀ × ℕ) × Bool) ↦ a < b)
      (fun a b : WQOKey ((Option β₀ × ℕ) × Bool) ↦ a < b)) :=
    WellFounded.prod_lex wellFounded_lt wellFounded_lt
  obtain ⟨_, ⟨D₁, hD₁, rfl⟩, hmin₁⟩ := hwf.has_min (CappedScheme.key '' 𝒜) (hne.image _)
  let 𝒜₁ : Set (CappedScheme.{u, w} ((Option β₀ × ℕ) × Bool)) :=
    {D | D ∈ 𝒜 ∧ D.χ.Ω2 = D₁.χ.Ω2 ∧ D.χ.Ω3 = D₁.χ.Ω3}
  have hS2 : ∀ D ∈ 𝒜₁, ConditionS2 D.χ D.cap := by
    rintro D ⟨hD, h2, h3⟩ S' Shat' _ _ χ' ⟨cap'⟩ ⟨e⟩ h3' h2' hstrict hb
    rw [h3] at h3' hstrict
    rw [h2] at h2' hstrict
    obtain ⟨e₀⟩ := hD.1
    refine hmin₁ _ ⟨⟨S', Shat', cap', χ'⟩, ⟨⟨e.trans e₀⟩, hb⟩, rfl⟩ ?_
    by_cases hE : χ'.Ω3.E = D₁.χ.Ω3.E
    · have hk : (⟨χ'.Ω3.norm, QuasiOrder.norm_isWQO χ'.isWQO_3⟩ : WQOKey _) =
          ⟨D₁.χ.Ω3.norm, QuasiOrder.norm_isWQO D₁.χ.isWQO_3⟩ := Subtype.ext (h3'.norm_eq hE)
      have hs2 := hstrict.resolve_left fun h ↦ h.2 hE
      simp only [CappedScheme.key]
      rw [hk]
      exact Prod.Lex.right _ (WQOKey.lt_iff.2 ⟨h2'.norm, hs2.2⟩)
    · exact Prod.Lex.left _ _ (WQOKey.lt_iff.2 ⟨h3'.norm, hE⟩)
  -- Choose `c(Σ)` minimal, which gives `S₃`.
  have hne₁ : 𝒜₁.Nonempty := ⟨D₁, hD₁, rfl, rfl⟩
  obtain ⟨_, ⟨D₂, hD₂, rfl⟩, hmin₂⟩ := wellFounded_lt.has_min
    ((fun D : CappedScheme.{u, w} ((Option β₀ × ℕ) × Bool) ↦ numCuffs D.S) '' 𝒜₁) (hne₁.image _)
  let 𝒜₂ : Set (CappedScheme.{u, w} ((Option β₀ × ℕ) × Bool)) := {D | D ∈ 𝒜₁ ∧ numCuffs D.S
    = numCuffs D₂.S}
  have hS3 : ∀ D ∈ 𝒜₂, ConditionS3 D.χ D.cap := by
    rintro D ⟨⟨hD, h2, h3⟩, hc⟩ S' Shat' _ _ χ' ⟨cap'⟩ ⟨e⟩ h2' h3' hlt hb
    obtain ⟨e₀⟩ := hD.1
    exact hmin₂ _ ⟨⟨S', Shat', cap', χ'⟩, ⟨⟨⟨e.trans e₀⟩, hb⟩, h2'.trans h2, h3'.trans h3⟩, rfl⟩
      (by simpa [hc] using hlt)
  -- By (4.4), choose a scheme with no refinement in the family, which gives `S₄`.
  have hstep : ∃ D ∈ 𝒜₂, ∀ D' ∈ 𝒜₂, ¬ D'.χ.IsRefinement D.χ := by
    by_contra hno
    push Not at hno
    choose! next hnext hrefn using hno
    have hD₂' : D₂ ∈ 𝒜₂ := ⟨hD₂, rfl⟩
    let g : ℕ → CappedScheme.{u, w} ((Option β₀ × ℕ) × Bool) := fun n ↦ next^[n] D₂
    have hg : ∀ n, g n ∈ 𝒜₂ := by
      intro n
      induction n with
      | zero => exact hD₂'
      | succ n ih =>
        change next^[n + 1] D₂ ∈ 𝒜₂
        rw [iterate_succ_apply']
        exact hnext _ ih
    refine theorem_4_4_proof (fun n ↦ (g n).S) (fun n ↦ (g n).χ) fun n ↦ ?_
    have := hrefn _ (hg n)
    change (next^[n + 1] D₂).χ.IsRefinement (g n).χ
    rw [iterate_succ_apply']
    exact this
  obtain ⟨D₃, hD₃, hno⟩ := hstep
  have hS4 : ConditionS4 D₃.χ := by
    intro S' _ χ' hrefn hb
    obtain ⟨⟨e⟩, h2, h3, -⟩ := id hrefn
    obtain ⟨⟨⟨⟨e₀⟩, -⟩, h2₃, h3₃⟩, hc⟩ := hD₃
    exact hno ⟨S', _, D₃.cap.ofHomeo e, χ'⟩
      ⟨⟨⟨⟨e₀⟩, hb⟩, h2.trans h2₃, h3.trans h3₃⟩, (numCuffs_eq e).trans hc⟩ hrefn
  obtain ⟨e₃⟩ := hD₃.1.1.1
  exact theorem_4_1_proof.{u, w} D₃.S D₃.Shat _ D₃.cap D₃.χ (hS1 _ ⟨e₃⟩) (hS2 D₃ hD₃.1)
    (hS3 D₃ hD₃) hS4 hD₃.1.1.2

/-- **Graph Minors XIX, (2.1)**, from (3.1) and the topology of its proof. -/
theorem theorem_2_1_proof
    (S : Type u) [TopologicalSpace S] {Ω : Type w} [Preorder Ω] (hS : IsSurface S)
    (hc : ConnectedSpace S) (hwqo : WellQuasiOrderedLE Ω) (Γ : ℕ → Painting S)
    (φ : ℕ → Set S → Ω) (h3 : ∀ i, (Γ i).IsInternallyThreeConnected) :
    ∃ i j, i < j ∧ ∃ (σv : S → Set S) (σe : Set S → Set S),
      IsLinearInflation (Γ i) (Γ j) σv σe ∧ ∀ e ∈ (Γ i).E, φ i e ≤ φ j (σe e) := by
  classical
  obtain ⟨Φ, hΦ⟩ := theorem21Topology_u.{u} S hS hc
  choose h Γ' s T using fun i ↦ hΦ (Γ i) (h3 i)
  obtain ⟨Shat, _, ⟨cap⟩⟩ := exists_cappedSurface _ S hS hc rfl
  let x₀ : Ω := φ 0 ∅
  have hshfin : Φ.shortSides.Finite := Φ.finite_sides.subset fun _ h ↦ h.1
  have : Finite Φ.shortSides := hshfin.to_subtype
  choose e he hEt using fun i (t : Φ.shortSides) ↦ (T i).short t.1 t.2
  let L : ℕ → Φ.shortSides → Ω × Prop := fun i t ↦
    (φ i (e i t), ((Γ' i).γ t.1 = ((Γ i).γ (e i t)).map (h i)))
  let r : Ω × Prop → Ω × Prop → Prop := fun a b ↦ a.1 ≤ b.1 ∧ (a.2 ↔ b.2)
  have hr : WellQuasiOrdered r := by
    have h₁ := (wellQuasiOrdered_le (α := Ω)).prod
      (Finite.wellQuasiOrdered (fun a b : Prop ↦ a ↔ b))
    exact h₁
  have : IsPreorder (Ω × Prop) r :=
    { refl := fun a ↦ ⟨le_rfl, Iff.rfl⟩
      trans := fun a b c h₁ h₂ ↦ ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩ }
  have hpi : WellQuasiOrdered fun a b : Φ.shortSides → Ω × Prop ↦ ∀ t, r (a t) (b t) :=
    WellQuasiOrdered.pi fun _ ↦ hr
  have : IsPreorder (Φ.shortSides → Ω × Prop) (fun a b ↦ ∀ t, r (a t) (b t)) :=
    { refl := fun a t ↦ ⟨le_rfl, Iff.rfl⟩
      trans := fun a b c h₁ h₂ t ↦ ⟨(h₁ t).1.trans (h₂ t).1, (h₁ t).2.trans (h₂ t).2⟩ }
  obtain ⟨g, hg⟩ := hpi.exists_monotone_subseq L
  have hnotbad := theorem_3_1_proof cap (thinScheme hS hc Φ x₀)
  have hgood : ¬ IsBadSequence (thinScheme hS hc Φ x₀)
      fun n ↦ thinPainting (T (g n)) hS hc (φ (g n)) x₀ := fun hb ↦ hnotbad ⟨_, hb⟩
  rw [IsBadSequence] at hgood
  push Not at hgood
  obtain ⟨n, m, hnm, σv', σe', hσ⟩ := hgood
  have hunique : ∀ i (t : Φ.shortSides) e', e' ∈ (Γ i).E → h i '' e' = t.1 → e' = e i t :=
    fun i t e' _ he' ↦ image_injective.2 (h i).injective (he'.trans (hEt i t).symm)
  obtain ⟨σv, σe, hlin, hle⟩ := exists_pull hS hc (T (g n)) (T (g m))
    (fun t ht e₁ he₁ e₂ he₂ h₁ h₂ ↦ by
    have hu₁ := hunique (g n) ⟨t, ht⟩ e₁ he₁ h₁
    have hu₂ := hunique (g m) ⟨t, ht⟩ e₂ he₂ h₂
    have := hg n m hnm.le ⟨t, ht⟩
    rw [hu₁, hu₂]
    exact this) hσ
  exact ⟨g n, g m, g.strictMono hnm, σv, σe, hlin, hle⟩

/-- Graph Minors XIX, (2.1), in the form used by XX. -/
theorem gm19Theorem21
     : GM20.GM19Theorem21Statement.{w} := by
  intro S _ Ω _ hS hc hwqo Γ φ h3
  exact theorem_2_1_proof S hS hc hwqo Γ φ h3

end GraphMinor.GM19
