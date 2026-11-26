/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM11.Theorem61
import LeanPool.GraphMinor.GM14.WhitneyFaces
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.Surface.DiscUnion
import LeanPool.GraphMinor.Surface.CutLift
import LeanPool.GraphMinor.Surface.Fan

/-!
# Lines that start and end on a filled-in disc

We prove the heart of Graph Minors XII, (5.4) (page 255), in the capped surface `Σ̂₁`. The caps are
the closed discs `E k`, the closures of the discs `D_k` of the paper. A short normal line `L` with
ends on the caps must have both ends on the same cap, by condition (i) of (5.3). A chord `P` of this
cap closes `L` up to a short normal `O`-arc. So `P ∪ L` bounds a disc `Δ₁` chosen by the tangle.
This disc includes one half of the cap and misses the other. The part of `Δ₁` outside the cap is the
disc `Δ` of (5.4).
-/

public section

namespace GraphMinor.GM12

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 Hypergraph

universe u

variable {T : Type u} [TopologicalSpace T] [T2Space T]

/-- The conditions of XII (5.3), read in the capped surface. The closed discs `E k` are disjoint,
the
drawing `Γ` meets them only in vertices on their boundaries, condition (i) holds for lines off the
open discs, and condition (ii) holds. -/
structure CapSetup {n : ℕ} (E : Fin n → Set T) (Γ : Drawing T) (θ : ℕ)
    (𝒯 : Set (Hypergraph T (Set T) × Hypergraph T (Set T))) : Prop where
  /-- Each cap is a closed disc. -/
  disc : ∀ k, IsClosedDisc (E k)
  /-- The caps are disjoint. -/
  disj : ∀ k l, k ≠ l → Disjoint (E k) (E l)
  /-- The drawing meets a cap only in vertices on its boundary. -/
  normal : ∀ k, E k ∩ Γ.U ⊆ discBd (E k) ∩ Γ.V
  /-- `𝒯` is a tangle of order `θ`. -/
  tangle : IsTangle Γ.toHypergraph θ 𝒯
  /-- `𝒯` is respectful. -/
  respect : (PaintingOrDrawing.drawing Γ).IsRespectful θ 𝒯
  /-- Condition (i) of (5.3). -/
  line : ∀ k l, k ≠ l → ∀ L : Set T, IsLine L → Γ.IsNormal L → (∀ m, Disjoint L (discInt (E m))) →
    (L ∩ E k).Nonempty → (L ∩ E l).Nonempty → θ ≤ (L ∩ Γ.V).ncard
  /-- The first half of condition (ii) of (5.3). -/
  many : ∀ k, θ ≤ (discBd (E k) ∩ Γ.V).ncard
  /-- The second half of condition (ii) of (5.3). -/
  free : ∀ k, ∀ X ⊆ discBd (E k) ∩ Γ.V, X.ncard ≤ θ → IsFreeSet Γ.toHypergraph 𝒯 θ X

variable {n : ℕ} {E : Fin n → Set T} {Γ : Drawing T} {θ : ℕ}
  {𝒯 : Set (Hypergraph T (Set T) × Hypergraph T (Set T))}

/-- Two points of the boundary of a closed disc are joined by an arc through the interior. -/
theorem exists_cap_chord {Δ : Set T} (hΔ : IsClosedDisc Δ) {a b : T} (ha : a ∈ discBd Δ)
    (hb : b ∈ discBd Δ) (hab : a ≠ b) :
    ∃ F, IsLineWithEnds F a b ∧ F ⊆ Δ ∧ F ∩ discBd Δ = {a, b} :=
  Surface.exists_chord hΔ ha hb hab

omit [T2Space T] in
/-- The order of the separation of a closed disc in a closed surface is at most the number of
vertices on its boundary. -/
theorem order_le_of_disc {Δ : Set T} :
    separationOrder ((PaintingOrDrawing.drawing Γ).inter Δ)
      ((PaintingOrDrawing.drawing Γ).interOutside Δ) ≤ (frontier Δ ∩ Γ.V).ncard :=
  ncard_le_ncard (fun _ hx => inter_outside_subset hx) (Γ.finite_V.subset inter_subset_right)

omit [T2Space T] in
/-- A set of vertices that is free, and lies on the small side of a separation, is at most as large
as the order. -/
theorem card_le_of_free {X Δ : Set T} (hX : IsFreeSet Γ.toHypergraph 𝒯 θ X)
    (hmem : ((PaintingOrDrawing.drawing Γ).inter Δ, (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈
      𝒯)
    (hXΔ : X ⊆ Δ) (hXV : X ⊆ Γ.V) : X.ncard ≤ (frontier Δ ∩ Γ.V).ncard :=
  (hX.2.2 hmem fun _ hx => ⟨hXV hx, hXΔ hx⟩).trans order_le_of_disc

/-- The output of (5.4) in the capped surface. -/
structure SideData (E : Fin n → Set T) (Γ : Drawing T)
    (𝒯 : Set (Hypergraph T (Set T) × Hypergraph T (Set T))) (L : Set T) (a b : T)
    (R Δ₁ Δ : Set T) : Prop where
  /-- `R` is a line with the same ends as `L`. -/
  line : IsLineWithEnds R a b
  /-- It lies on the boundary of one cap. -/
  on_cap : ∃ k, R ⊆ discBd (E k)
  /-- `L` and `R` meet just in their ends. -/
  meet : L ∩ R = {a, b}
  /-- `R` is as short as `L`. -/
  count : (R ∩ Γ.V).ncard ≤ (L ∩ Γ.V).ncard
  /-- `Δ` is a closed disc. -/
  disc : IsClosedDisc Δ
  /-- It is bounded by `L ∪ R`. -/
  bd : discBd Δ = L ∪ R
  /-- It misses the open caps. -/
  off : ∀ k, Disjoint Δ (discInt (E k))
  /-- `Δ₁` is a closed disc. -/
  disc₁ : IsClosedDisc Δ₁
  /-- It includes `Δ`. -/
  sub : Δ ⊆ Δ₁
  /-- It includes `R`. -/
  sub_R : R ⊆ Δ₁
  /-- Off the open caps, its frontier is in `L`. -/
  frontier₁ : ∀ x ∈ frontier Δ₁, (∀ k, x ∉ discInt (E k)) → x ∈ L
  /-- The tangle puts it on the small side. -/
  mem : ((PaintingOrDrawing.drawing Γ).inter Δ₁, (PaintingOrDrawing.drawing Γ).interOutside Δ₁) ∈ 𝒯

/-- The step of (5.4) after the side of the chord has been found: `Δ₁` includes the half `E₁` of the
cap and misses the open half `E₂`. -/
theorem sideData_of_side (H : CapSetup E Γ θ 𝒯) (hS : IsClosedSurface T)
    {L P A B E₁ E₂ Δ₁ : Set T} {a b : T} {i : Fin n}
    (hL : IsLineWithEnds L a b) (hP : IsLineWithEnds P a b) (hA : IsLineWithEnds A a b)
    (hAB : A ∩ B = {a, b}) (hPA : P ∩ A = {a, b}) (hPB : P ∩ B = {a, b})
    (hbdE : discBd (E i) = A ∪ B) (hPE : P ⊆ E i)
    (hmeet : ∀ k, L ∩ E k ⊆ {a, b})
    (hsmall : (L ∩ Γ.V).ncard < θ)
    (hE₁ : IsClosedDisc E₁) (hE₂ : IsClosedDisc E₂) (hU : E₁ ∪ E₂ = E i)
    (hb₁ : discBd E₁ = A ∪ P) (hb₂ : discBd E₂ = B ∪ P)
    (hΔ₁ : IsClosedDisc Δ₁) (hfr : frontier Δ₁ = P ∪ L)
    (hsub : discInt E₁ ⊆ Δ₁) (hoff : Disjoint (discInt E₂) Δ₁)
    (hmem : ((PaintingOrDrawing.drawing Γ).inter Δ₁,
      (PaintingOrDrawing.drawing Γ).interOutside Δ₁) ∈ 𝒯) :
    ∃ Δ, SideData E Γ 𝒯 L a b A Δ₁ Δ := by
  classical
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hbdΔ₁ : discBd Δ₁ = P ∪ L := by rw [← IsClosedDisc.frontier_eq_discBd hS hΔ₁, hfr]
  have hcl : IsClosed Δ₁ := hΔ₁.isClosed
  have hE₁Δ : E₁ ⊆ Δ₁ := hE₁.subset_closure_discInt.trans (closure_minimal hsub hcl)
  have hab : a ∈ P ∧ b ∈ P := by
    have h : ({a, b} : Set T) ⊆ P := hPA ▸ inter_subset_left
    exact ⟨h (by simp), h (by simp)⟩
  have hAE₁ : A ⊆ E₁ := fun x hx => GraphMinor.Surface.discBd_subset E₁ (hb₁ ▸ .inl hx)
  have hAE : A ⊆ E i := fun x hx => hU ▸ .inl (hAE₁ hx)
  have hLA : L ∩ A ⊆ {a, b} := fun x hx => hmeet i ⟨hx.1, hAE hx.2⟩
  have hmeetbd : discBd E₁ ∩ discBd Δ₁ = P := by
    rw [hb₁, hbdΔ₁]
    ext x
    constructor
    · rintro ⟨hx | hx, hy | hy⟩
      · exact hy
      · rcases hLA ⟨hy, hx⟩ with rfl | rfl
        · exact hab.1
        · exact hab.2
      · exact hx
      · exact hx
    · intro hx
      exact ⟨.inr hx, .inl hx⟩
  obtain ⟨hd, hdb, hdE⟩ := disc_difference E₁ Δ₁ P a b hE₁ hΔ₁ hE₁Δ hP hmeetbd
  set Δ := closure (Δ₁ \ E₁) with hΔdef
  have hΔΔ₁ : Δ ⊆ Δ₁ := closure_minimal sdiff_subset hcl
  have hbΔ : discBd Δ = L ∪ A := by
    rw [hdb, hb₁, hbdΔ₁]
    ext x
    constructor
    · rintro ⟨(hx | hx) | hx | hx, hn⟩
      · exact .inr hx
      · by_cases hend : x = a ∨ x = b
        · rcases hend with rfl | rfl
          · exact .inr ((hPA.symm ▸ (by simp) : x ∈ P ∩ A)).2
          · exact .inr ((hPA.symm ▸ (by simp) : x ∈ P ∩ A)).2
        · exact absurd ⟨hx, hend⟩ hn
      · by_cases hend : x = a ∨ x = b
        · rcases hend with rfl | rfl
          · exact .inr ((hPA.symm ▸ (by simp) : x ∈ P ∩ A)).2
          · exact .inr ((hPA.symm ▸ (by simp) : x ∈ P ∩ A)).2
        · exact absurd ⟨hx, hend⟩ hn
      · exact .inl hx
    · rintro (hx | hx)
      · refine ⟨.inr (.inr hx), fun hn => hn.2 ?_⟩
        exact hmeet i ⟨hx, hPE hn.1⟩
      · refine ⟨.inl (.inl hx), fun hn => hn.2 ?_⟩
        exact (hPA.symm ▸ (⟨hn.1, hx⟩ : x ∈ P ∩ A) : x ∈ ({a, b} : Set T))
  have hint : ∀ x ∈ discInt (E i), x ∈ discInt E₁ ∨ x ∈ discInt E₂ ∨ x ∈ P := by
    intro x hx
    have hxE : x ∈ E₁ ∪ E₂ := hU ▸ hx.1
    rcases hxE with hx₁ | hx₂
    · by_cases hb : x ∈ discBd E₁
      · rw [hb₁] at hb
        rcases hb with hb | hb
        · exact absurd (hbdE ▸ .inl hb) hx.2
        · exact .inr (.inr hb)
      · exact .inl ⟨hx₁, hb⟩
    · by_cases hb : x ∈ discBd E₂
      · rw [hb₂] at hb
        rcases hb with hb | hb
        · exact absurd (hbdE ▸ .inr hb) hx.2
        · exact .inr (.inr hb)
      · exact .inr (.inl ⟨hx₂, hb⟩)
  have hBfr : ∀ x ∈ B, x ≠ a → x ≠ b → x ∉ Δ₁ := by
    intro x hxB hxa hxb hxΔ
    have hxE₂ : x ∈ E₂ := GraphMinor.Surface.discBd_subset E₂ (hb₂ ▸ .inl hxB)
    have hxE : x ∈ E i := hU ▸ .inr hxE₂
    have hnot : x ∉ discBd Δ₁ := by
      rw [hbdΔ₁]
      rintro (hx | hx)
      · have : x ∈ P ∩ B := ⟨hx, hxB⟩
        rw [hPB] at this
        rcases this with rfl | rfl
        · exact hxa rfl
        · exact hxb rfl
      · rcases hmeet i ⟨hx, hxE⟩ with rfl | rfl
        · exact hxa rfl
        · exact hxb rfl
    have hopen := hΔ₁.isOpen_discInt hman
    have hcl₂ := hE₂.subset_closure_discInt hxE₂
    obtain ⟨y, hy, hy₂⟩ := mem_closure_iff.mp hcl₂ _ hopen ⟨hxΔ, hnot⟩
    exact Set.disjoint_left.mp hoff hy₂ hy.1
  have hΔE₁ : Δ ∩ E₁ = A := by
    rw [hdE, hb₁]
    ext x
    constructor
    · rintro ⟨hx | hx, hn⟩
      · exact hx
      · by_cases hend : x = a ∨ x = b
        · rcases hend with rfl | rfl
          · exact (hPA.symm ▸ (by simp) : x ∈ P ∩ A).2
          · exact (hPA.symm ▸ (by simp) : x ∈ P ∩ A).2
        · exact absurd ⟨hx, hend⟩ hn
    · intro hx
      refine ⟨.inl hx, fun hn => hn.2 ?_⟩
      exact (hPA.symm ▸ (⟨hn.1, hx⟩ : x ∈ P ∩ A) : x ∈ ({a, b} : Set T))
  have hPK : ∀ x ∈ P, x ∈ discBd (E i) → x = a ∨ x = b := by
    intro x hx hxK
    rw [hbdE] at hxK
    rcases hxK with h | h
    · have : x ∈ P ∩ A := ⟨hx, h⟩
      rw [hPA] at this
      exact this
    · have : x ∈ P ∩ B := ⟨hx, h⟩
      rw [hPB] at this
      exact this
  have hfrV : frontier Δ₁ ∩ Γ.V = L ∩ Γ.V := by
    rw [hfr]
    ext x
    constructor
    · rintro ⟨hx | hx, hV⟩
      · have hxK : x ∈ discBd (E i) := (H.normal i ⟨hPE hx, Γ.V_subset_U hV⟩).1
        rcases hPK x hx hxK with rfl | rfl
        · exact ⟨hL.left_mem, hV⟩
        · exact ⟨hL.right_mem, hV⟩
      · exact ⟨hx, hV⟩
    · exact fun hx => ⟨.inr hx.1, hx.2⟩
  have hbound : ∀ X : Set T, X ⊆ Γ.V → X ⊆ Δ₁ → IsFreeSet Γ.toHypergraph 𝒯 θ X →
      X.ncard ≤ (L ∩ Γ.V).ncard := fun X hXV hXΔ hf => by
    have := card_le_of_free hf hmem hXΔ hXV
    rwa [hfrV] at this
  have hVfin : ∀ Y : Set T, (Y ∩ Γ.V).Finite := fun Y => Γ.finite_V.subset inter_subset_right
  have hcount : (A ∩ Γ.V).ncard ≤ (L ∩ Γ.V).ncard := by
    by_contra hlt
    push Not at hlt
    obtain ⟨X, hXA, hXc⟩ := exists_subset_card_eq (s := A ∩ Γ.V) hlt
    have hXK : X ⊆ discBd (E i) ∩ Γ.V := fun x hx => ⟨hbdE ▸ .inl (hXA hx).1, (hXA hx).2⟩
    have hf := H.free i X hXK (by omega)
    have := hbound X (fun x hx => (hXA hx).2) (fun x hx => hE₁Δ (hAE₁ (hXA hx).1)) hf
    omega
  have hother : ∀ k, k ≠ i → Disjoint Δ₁ (discInt (E k)) := by
    intro k hk
    have hdj : Disjoint (discInt (E k)) (discBd Δ₁) := by
      rw [hbdΔ₁]
      refine Set.disjoint_left.mpr fun x hx hx' => ?_
      have hxk : x ∈ E k := hx.1
      rcases hx' with h | h
      · exact Set.disjoint_left.mp (H.disj i k hk.symm) (hPE h) hxk
      · rcases hmeet k ⟨h, hxk⟩ with rfl | rfl
        · exact Set.disjoint_left.mp (H.disj i k hk.symm) (hPE hab.1) hxk
        · exact Set.disjoint_left.mp (H.disj i k hk.symm) (hPE hab.2) hxk
    rcases hΔ₁.side hman (H.disc k).isPreconnected_discInt hdj with h | h
    · exfalso
      have hEk : E k ⊆ Δ₁ :=
        (H.disc k).subset_closure_discInt.trans (closure_minimal (h.trans (discInt_subset _)) hcl)
      obtain ⟨X, hXK, hXc⟩ := exists_subset_card_eq (s := discBd (E k) ∩ Γ.V) (H.many k)
      have hf := H.free k X hXK hXc.le
      have := hbound X (fun x hx => (hXK hx).2)
        (fun x hx => hEk (GraphMinor.Surface.discBd_subset _ (hXK hx).1)) hf
      omega
    · exact h.symm
  refine ⟨Δ, ⟨hA, ⟨i, fun x hx => hbdE ▸ .inl hx⟩, ?_, hcount, hd, hbΔ, ?_, hΔ₁, hΔΔ₁,
    fun x hx => hE₁Δ (hAE₁ hx), ?_, hmem⟩⟩
  · apply Subset.antisymm hLA
    rintro x (rfl | rfl)
    · exact ⟨hL.left_mem, hA.left_mem⟩
    · exact ⟨hL.right_mem, hA.right_mem⟩
  · intro k
    by_cases hk : k = i
    · subst hk
      refine Set.disjoint_left.mpr fun x hxΔ hx => ?_
      rcases hint x hx with h | h | h
      · have : x ∈ Δ ∩ E₁ := ⟨hxΔ, h.1⟩
        rw [hΔE₁] at this
        exact hx.2 (hbdE ▸ .inl this)
      · exact Set.disjoint_left.mp hoff h (hΔΔ₁ hxΔ)
      · have : x ∈ Δ ∩ E₁ := ⟨hxΔ, GraphMinor.Surface.discBd_subset _ (hb₁ ▸ .inr h)⟩
        rw [hΔE₁] at this
        exact hx.2 (hbdE ▸ .inl this)
    · exact (hother k hk).mono_left hΔΔ₁
  · intro x hx hk
    rw [hfr] at hx
    rcases hx with h | h
    · by_cases hKx : x ∈ discBd (E i)
      · rcases hPK x h hKx with rfl | rfl
        · exact hL.left_mem
        · exact hL.right_mem
      · exact absurd ⟨hPE h, hKx⟩ (hk i)
    · exact h

/-- **The heart of Graph Minors XII, (5.4)** (page 255), in the capped surface: a short normal line
`L` with ends on the caps and no other point on them has a partner `R` on the boundary of a cap, and
`L ∪ R` bounds a closed disc off the open caps. -/
theorem exists_sideData (H : CapSetup E Γ θ 𝒯) (hS : IsClosedSurface T)
    {L : Set T} {a b : T} {i j : Fin n} (hL : IsLineWithEnds L a b) (hab : a ≠ b)
    (hN : Γ.IsNormal L) (hsmall : (L ∩ Γ.V).ncard < θ)
    (ha : a ∈ discBd (E i)) (hb : b ∈ discBd (E j)) (hmeet : ∀ k, L ∩ E k ⊆ {a, b}) :
    ∃ R Δ₁ Δ, SideData E Γ 𝒯 L a b R Δ₁ Δ := by
  classical
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hE_sub : ∀ {k x}, x ∈ discBd (E k) → x ∈ E k := fun hx => GraphMinor.Surface.discBd_subset _
    hx
  -- Both ends lie on one cap, by condition (i).
  have hij : i = j := by
    by_contra h
    have hoff : ∀ m, Disjoint L (discInt (E m)) := fun m => Set.disjoint_left.mpr fun x hx hx' => by
      rcases hmeet m ⟨hx, hx'.1⟩ with rfl | rfl
      · have hm : m = i := by
          by_contra hne
          exact Set.disjoint_left.mp (H.disj m i hne) hx'.1 (hE_sub ha)
        subst hm
        exact hx'.2 ha
      · have hm : m = j := by
          by_contra hne
          exact Set.disjoint_left.mp (H.disj m j hne) hx'.1 (hE_sub hb)
        subst hm
        exact hx'.2 hb
    have := H.line i j h L (let ⟨f, _⟩ := hL; ⟨f⟩) hN hoff ⟨a, hL.left_mem, hE_sub ha⟩
      ⟨b, hL.right_mem, hE_sub hb⟩
    omega
  subst hij
  have hdisc := H.disc i
  obtain ⟨P, hPl, hPE, hPK⟩ := exists_cap_chord hdisc ha hb hab
  obtain ⟨A, B, hA, hB, hAB, hAiB⟩ := hdisc.isOArc_discBd.lines ha hb hab
  have hsubK : ∀ {Q : Set T}, Q ⊆ discBd (E i) → ({a, b} : Set T) ⊆ Q → P ∩ Q = {a, b} := by
    intro Q hQ hend
    apply Subset.antisymm
    · exact fun x hx => hPK ▸ ⟨hx.1, hQ hx.2⟩
    · exact subset_inter (hPK ▸ inter_subset_left) hend
  have hends : ∀ {Q : Set T}, IsLineWithEnds Q a b → ({a, b} : Set T) ⊆ Q := by
    intro Q hQ x hx
    rcases hx with rfl | rfl
    · exact hQ.left_mem
    · exact hQ.right_mem
  have hPA := hsubK (hAB ▸ subset_union_left) (hends hA)
  have hPB := hsubK (hAB ▸ subset_union_right) (hends hB)
  obtain ⟨E₁, E₂, hE₁, hE₂, hU, hI, hb₁, hb₂⟩ :=
    GM14.Whitney.disc_split hdisc hPl hA hB hAiB hPA hPB hAB.symm hPE hab
  have hPL : P ∩ L = {a, b} := by
    apply Subset.antisymm
    · exact fun x hx => hmeet i ⟨hx.2, hPE hx.1⟩
    · exact subset_inter (hends hPl) (hends hL)
  have hO : IsOArc (P ∪ L) := oArc_of_lines hPl hL hPL
  have hPint : ∀ x ∈ P, x ∈ Γ.U → x ∈ L ∧ x ∈ Γ.V := by
    intro x hx hxU
    have h := H.normal i ⟨hPE hx, hxU⟩
    have : x ∈ P ∩ discBd (E i) := ⟨hx, h.1⟩
    rw [hPK] at this
    rcases this with rfl | rfl
    · exact ⟨hL.left_mem, h.2⟩
    · exact ⟨hL.right_mem, h.2⟩
  have hNF : (PaintingOrDrawing.drawing Γ).IsNormal (P ∪ L) := by
    rintro x ⟨hx | hx, hxU⟩
    · exact (hPint x hx hxU).2
    · exact hN ⟨hx, hxU⟩
  have hFV : (P ∪ L) ∩ Γ.V = L ∩ Γ.V := by
    ext x
    constructor
    · rintro ⟨hx | hx, hV⟩
      · exact ⟨(hPint x hx (Γ.V_subset_U hV)).1, hV⟩
      · exact ⟨hx, hV⟩
    · exact fun hx => ⟨.inr hx.1, hx.2⟩
  obtain ⟨Δ₁, hΔ₁, hbd₁, hmem⟩ := H.respect.2 (P ∪ L) hO hNF (by
    change ((P ∪ L) ∩ Γ.V).ncard < θ
    rwa [hFV])
  have hfr : frontier Δ₁ = P ∪ L := by rw [← subBd_eq_frontier, hbd₁]
  have hbdΔ₁ : discBd Δ₁ = P ∪ L := by rw [← IsClosedDisc.frontier_eq_discBd hS hΔ₁, hfr]
  obtain ⟨m, hmP, hmn⟩ := GM14.Whitney.line_interior_nonempty hPl
  have hmK : m ∉ discBd (E i) := fun h => hmn (hPK ▸ ⟨hmP, h⟩)
  have hEP : ∀ {Q}, Q ⊆ E i → discBd Q ⊆ A ∪ B ∪ P → P ⊆ discBd Q → Disjoint (discInt Q)
    (discBd Δ₁) := by
    intro Q hQE _ hPQ
    rw [hbdΔ₁]
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    rcases hx' with h | h
    · exact hx.2 (hPQ h)
    · have : x ∈ ({a, b} : Set T) := hmeet i ⟨h, hQE hx.1⟩
      rcases this with rfl | rfl
      · exact hx.2 (hPQ hPl.left_mem)
      · exact hx.2 (hPQ hPl.right_mem)
  have hsubE₁ : E₁ ⊆ E i := hU ▸ subset_union_left
  have hsubE₂ : E₂ ⊆ E i := hU ▸ subset_union_right
  have hb₁' : discBd E₁ ⊆ A ∪ B ∪ P := hb₁ ▸ union_subset_union_left _ subset_union_left
  have hb₂' : discBd E₂ ⊆ A ∪ B ∪ P := hb₂ ▸ union_subset_union_left _ subset_union_right
  have hd₁ := hEP hsubE₁ hb₁' (hb₁ ▸ subset_union_right)
  have hd₂ := hEP hsubE₂ hb₂' (hb₂ ▸ subset_union_right)
  -- `Δ₁` includes exactly one of the two open halves of the cap.
  have hW : IsOpen (discInt (E i)) := hdisc.isOpen_discInt hman
  have hmW : m ∈ discInt (E i) := ⟨hPE hmP, hmK⟩
  have hint : ∀ x ∈ discInt (E i), x ∈ discInt E₁ ∨ x ∈ discInt E₂ ∨ x ∈ P := by
    intro x hx
    have hxE : x ∈ E₁ ∪ E₂ := hU ▸ hx.1
    rcases hxE with hx₁ | hx₂
    · by_cases hb : x ∈ discBd E₁
      · rw [hb₁] at hb
        rcases hb with hb | hb
        · exact absurd (hAB ▸ .inl hb) hx.2
        · exact .inr (.inr hb)
      · exact .inl ⟨hx₁, hb⟩
    · by_cases hb : x ∈ discBd E₂
      · rw [hb₂] at hb
        rcases hb with hb | hb
        · exact absurd (hAB ▸ .inr hb) hx.2
        · exact .inr (.inr hb)
      · exact .inr (.inl ⟨hx₂, hb⟩)
  have hmfr : m ∈ frontier Δ₁ := hfr ▸ .inl hmP
  have hsub_of : discInt E₁ ⊆ Δ₁ → discInt E₂ ⊆ Δ₁ → False := by
    intro h₁ h₂
    have hWΔ : discInt (E i) ⊆ Δ₁ := fun x hx => by
      rcases hint x hx with h | h | h
      · exact h₁ h
      · exact h₂ h
      · exact frontier_subset_closure.trans_eq hΔ₁.isClosed.closure_eq (hfr ▸ .inl h)
    exact hmfr.2 (interior_maximal hWΔ hW hmW)
  have hoff_of : Disjoint (discInt E₁) Δ₁ → Disjoint (discInt E₂) Δ₁ → False := by
    intro h₁ h₂
    have hcl := IsClosedDisc.subset_closure_diff_frontier hS hΔ₁
      (frontier_subset_closure.trans_eq hΔ₁.isClosed.closure_eq hmfr)
    obtain ⟨x, hxW, hxΔ, hxf⟩ := mem_closure_iff.mp hcl _ hW hmW
    rcases hint x hxW with h | h | h
    · exact Set.disjoint_left.mp h₁ h hxΔ
    · exact Set.disjoint_left.mp h₂ h hxΔ
    · exact hxf (hfr ▸ .inl h)
  have hPA' : P ∩ A = {a, b} := hPA
  rcases hΔ₁.side hman hE₁.isPreconnected_discInt hd₁ with h₁ | h₁ <;>
    rcases hΔ₁.side hman hE₂.isPreconnected_discInt hd₂ with h₂ | h₂
  · exact (hsub_of (h₁.trans (discInt_subset _)) (h₂.trans (discInt_subset _))).elim
  · obtain ⟨Δ, hΔ⟩ := sideData_of_side H hS hL hPl hA hAiB hPA hPB hAB.symm hPE hmeet hsmall hE₁
      hE₂ hU hb₁ hb₂
      hΔ₁ hfr (h₁.trans (discInt_subset _)) h₂ hmem
    exact ⟨A, Δ₁, Δ, hΔ⟩
  · have hAiB' : B ∩ A = {a, b} := by rw [Set.inter_comm]; exact hAiB
    have hU' : E₂ ∪ E₁ = E i := by
      rw [Set.union_comm]; exact hU
    obtain ⟨Δ, hΔ⟩ := sideData_of_side H hS hL hPl hB hAiB' hPB hPA
      (hAB.symm.trans (Set.union_comm _ _)) hPE hmeet hsmall hE₂ hE₁ hU' hb₂ hb₁ hΔ₁ hfr
      (h₂.trans (discInt_subset _)) h₁ hmem
    exact ⟨B, Δ₁, Δ, hΔ⟩
  · exact (hoff_of h₁ h₂).elim

end GraphMinor.GM12
