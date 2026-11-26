/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section8a
public import LeanPool.GraphMinor.GM11.Fan
public import LeanPool.GraphMinor.GM11.Forest
public import LeanPool.GraphMinor.Surface.PushOff

/-!
# Three lenses in a disc

Let `a`, `b`, `c` be three points on the boundary of a closed disc `D`. In the proof of Graph Minors
XIX,
(2.1), we choose a disc `Δ ⊆ D` that meets `bd(D)` exactly in these three points. Here we cut `D`
along three
chords, one after the other. Each cut takes off a lens `R` next to one arc of `bd(D)`. What stays is
`Δ`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM20.Thin

variable {S : Type} [TopologicalSpace S] [T2Space S]

/-- A connected part of an `O`-arc that misses the ends of a line in the `O`-arc, and meets the
line,
lies in the line. -/
theorem subset_line_of_preconnected {F Y X : Set S} {p q b : S} (hF : IsOArc F)
    (hY : IsLineWithEnds Y p q) (hYF : Y ⊆ F) (hX : IsPreconnected X) (hXF : X ⊆ F \ {p, q})
    (hb : b ∈ X) (hbY : b ∈ Y) : X ⊆ Y := by
  obtain ⟨u, v, huv, hr, h0, h1, hun⟩ := exists_arcs_of_line hF hY hYF
  have hc₁ : IsClosed (range u) := (isCompact_range huv.arc_left.1).isClosed
  have hc₂ : IsClosed (range v) := (isCompact_range huv.arc_right.1).isClosed
  intro x hx
  by_contra hxY
  have hxv : x ∈ range v := by
    have := (hXF hx).1
    rw [← hun, hr] at this
    exact this.resolve_left hxY
  obtain ⟨y, hyX, hy₁, hy₂⟩ := isPreconnected_closed_iff.mp hX _ _ hc₁ hc₂
    (fun z hz ↦ by
      have := (hXF hz).1
      rwa [← hun] at this)
    ⟨b, hb, hr ▸ hbY⟩ ⟨x, hx, hxv⟩
  obtain ⟨s, rfl⟩ := hy₁
  obtain ⟨t, ht⟩ := hy₂
  rcases huv.meet s t ht.symm with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact (hXF hyX).2 (Or.inl h0)
  · exact (hXF hyX).2 (Or.inr h1)

/-- One cut. A chord from `a` to `b` splits `D` into a lens `R` and a disc `Q`, with `c` on the
boundary of `Q` and not in `R`. -/
theorem exists_cut {D : Set S} (hD : IsClosedDisc D) {a b c : S} (ha : a ∈ discBd D)
    (hb : b ∈ discBd D) (hc : c ∈ discBd D) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ L R Q : Set S, IsLineWithEnds L a b ∧ IsClosedDisc R ∧ IsClosedDisc Q ∧ R ∪ Q = D ∧ R ∩ Q = L
      ∧
      L ∩ discBd D = {a, b} ∧ L ⊆ discBd R ∧ L ⊆ discBd Q ∧ discBd R ⊆ L ∪ discBd D ∧
      discBd Q ⊆ L ∪ connectedComponentIn (discBd D \ {a, b}) c ∧ discBd D ∩ Q ⊆ discBd Q ∧
      ∀ X : Set S, IsPreconnected X → X ⊆ discBd D \ {a, b} → c ∈ X → X ⊆ discBd Q \ R := by
  obtain ⟨L, hL, hLD, hLi⟩ := GM20.exists_chord hD ha hb hab
  have haL : a ∈ L := by
    obtain ⟨f, h0, -⟩ := hL
    exact h0 ▸ (f 0).2
  have hbL : b ∈ L := by
    obtain ⟨f, -, h1⟩ := hL
    exact h1 ▸ (f 1).2
  have hcap : L ∩ discBd D = {a, b} := by
    ext x
    constructor
    · rintro ⟨hx, hxb⟩
      by_contra hn
      exact (hLi ⟨hx, hn⟩).2 hxb
    · rintro (rfl | rfl)
      · exact ⟨haL, ha⟩
      · exact ⟨hbL, hb⟩
  obtain ⟨A₁, A₂, Δ₁, Δ₂, -, hcomp, hd₁, hd₂, hun, hint, hbd₁, hbd₂, -⟩ :=
    disc_iArc D L a b hD hLD hab hL hcap
  have key : ∀ A₁ A₂ Δ₁ Δ₂ : Set S, componentsIn (discBd D \ {a, b}) = {A₁, A₂} → IsClosedDisc Δ₁ →
      IsClosedDisc Δ₂ → Δ₁ ∪ Δ₂ = D → Δ₁ ∩ Δ₂ = L → discBd Δ₁ = A₁ ∪ L → discBd Δ₂ = A₂ ∪ L →
      connectedComponentIn (discBd D \ {a, b}) c = A₂ →
      ∃ L R Q : Set S, IsLineWithEnds L a b ∧ IsClosedDisc R ∧ IsClosedDisc Q ∧ R ∪ Q = D ∧
        R ∩ Q = L ∧ L ∩ discBd D = {a, b} ∧ L ⊆ discBd R ∧ L ⊆ discBd Q ∧
        discBd R ⊆ L ∪ discBd D ∧ discBd Q ⊆ L ∪ connectedComponentIn (discBd D \ {a, b}) c
          ∧ discBd D ∩ Q ⊆ discBd Q ∧
        ∀ X : Set S, IsPreconnected X → X ⊆ discBd D \ {a, b} → c ∈ X → X ⊆ discBd Q \ R := by
    intro A₁ A₂ Δ₁ Δ₂ hcomp hd₁ hd₂ hun hint hbd₁ hbd₂ hA
    have hsub : ∀ A ∈ componentsIn (discBd D \ {a, b}), A ⊆ discBd D \ {a, b} := by
      rintro _ ⟨x, -, rfl⟩
      exact connectedComponentIn_subset _ _
    have hA₁ : A₁ ⊆ discBd D \ {a, b} := hsub _ (hcomp ▸ Or.inl rfl)
    have hA₂ : A₂ ⊆ discBd D \ {a, b} := hsub _ (hcomp ▸ Or.inr rfl)
    have hcov : discBd D \ {a, b} ⊆ A₁ ∪ A₂ := by
      intro x hx
      have : connectedComponentIn (discBd D \ {a, b}) x ∈ componentsIn (discBd D \ {a, b})
        := ⟨x, hx, rfl⟩
      rw [hcomp] at this
      rcases this with h | h
      · exact Or.inl (h ▸ mem_connectedComponentIn hx)
      · exact Or.inr (h ▸ mem_connectedComponentIn hx)
    have hcm : c ∈ discBd D \ {a, b} := ⟨hc, by
      rintro (rfl | rfl)
      · exact hac rfl
      · exact hbc rfl⟩
    have hmeet : ∀ x ∈ Δ₁, x ∈ A₂ → False := fun x hx₁ hx₂ ↦ by
      have hxL : x ∈ L := hint ▸ ⟨hx₁, discBd_subset Δ₂ (hbd₂ ▸ Or.inl hx₂)⟩
      have hx : x ∈ L ∩ discBd D := ⟨hxL, (hA₂ hx₂).1⟩
      rw [hcap] at hx
      exact (hA₂ hx₂).2 hx
    refine ⟨L, Δ₁, Δ₂, hL, hd₁, hd₂, hun, hint, hcap, hbd₁ ▸ subset_union_right,
      hbd₂ ▸ subset_union_right, ?_, ?_, ?_, ?_⟩
    · rw [hbd₁]
      rintro x (hx | hx)
      · exact Or.inr (hA₁ hx).1
      · exact Or.inl hx
    · rw [hbd₂, hA, union_comm]
    · rintro x ⟨hxb, hxQ⟩
      by_cases hab' : x ∈ ({a, b} : Set S)
      · rw [hbd₂]
        rcases hab' with rfl | rfl
        · exact Or.inr haL
        · exact Or.inr hbL
      · rcases hcov ⟨hxb, hab'⟩ with h | h
        · have hx1 : x ∈ Δ₁ := discBd_subset Δ₁ (hbd₁ ▸ Or.inl h)
          have hxL : x ∈ L := hint ▸ ⟨hx1, hxQ⟩
          exact absurd (hcap ▸ (⟨hxL, hxb⟩ : x ∈ L ∩ discBd D)) hab'
        · rw [hbd₂]
          exact Or.inl h
    · intro X hX hXs hcX x hx
      have : x ∈ A₂ := hA ▸ hX.subset_connectedComponentIn hcX hXs hx
      refine ⟨hbd₂ ▸ Or.inl this, fun h ↦ hmeet x h this⟩
  have hcm : c ∈ discBd D \ {a, b} := ⟨hc, by
    rintro (rfl | rfl)
    · exact hac rfl
    · exact hbc rfl⟩
  have hin : connectedComponentIn (discBd D \ {a, b}) c ∈ componentsIn (discBd D \ {a, b}) :=
    ⟨c, hcm, rfl⟩
  rw [hcomp] at hin
  rcases hin with h | h
  · refine key A₂ A₁ Δ₂ Δ₁ (by rw [hcomp, pair_comm]) hd₂ hd₁ (by rw [union_comm, hun])
      (by rw [inter_comm, hint]) hbd₂ hbd₁ h
  · exact key A₁ A₂ Δ₁ Δ₂ hcomp hd₁ hd₂ hun hint hbd₁ hbd₂ h

/-- `Δ` and the three lenses `R₁`, `R₂`, `R₃` of a disc `D` with three points on its boundary. Each
lens `Rᵢ` is cut off along a line `Lᵢ` of `Δ` joining two of the points. -/
structure IsLens (D Δ L R : Set S) (a b c : S) : Prop where
  line : IsLineWithEnds L a b
  disc : IsClosedDisc R
  sub : R ⊆ D
  sub_Δ : L ⊆ Δ
  inter : R ∩ Δ = L
  cap : L ∩ discBd D = {a, b}
  L_bd : L ⊆ discBd R
  bd : discBd R ⊆ L ∪ discBd D
  third : c ∉ R

theorem exists_lenses {D : Set S} (hD : IsClosedDisc D) {a b c : S} (ha : a ∈ discBd D)
    (hb : b ∈ discBd D) (hc : c ∈ discBd D) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ Δ L₁ L₂ L₃ R₁ R₂ R₃ : Set S, IsClosedDisc Δ ∧ Δ ⊆ D ∧ a ∈ discBd Δ ∧ b ∈ discBd Δ ∧
      c ∈ discBd Δ ∧ Δ ∩ discBd D = {a, b, c} ∧ discBd Δ ⊆ L₁ ∪ L₂ ∪ L₃ ∧
      IsLens D Δ L₁ R₁ a b c ∧ IsLens D Δ L₂ R₂ b c a ∧ IsLens D Δ L₃ R₃ c a b ∧
      R₁ ∩ R₂ ⊆ {a, b, c} ∧ R₁ ∩ R₃ ⊆ {a, b, c} ∧ R₂ ∩ R₃ ⊆ {a, b, c} ∧ D = Δ ∪ R₁ ∪ R₂ ∪ R₃ := by
  have hmemL : ∀ {L : Set S} {u v : S}, IsLineWithEnds L u v → u ∈ L ∧ v ∈ L := by
    rintro L u v ⟨f, h0, h1⟩
    exact ⟨h0 ▸ (f 0).2, h1 ▸ (f 1).2⟩
  obtain ⟨L₁, R₁, Q₁, hL₁, hR₁, hQ₁, hu₁, hi₁, hcap₁, hLR₁, hLQ₁, hbR₁, hbQ₁, hsub₁, hX₁⟩ :=
    exists_cut hD ha hb hc hab hac hbc
  have hcQ₁ := hX₁ {c} isPreconnected_singleton
    (singleton_subset_iff.mpr ⟨hc, by
      rintro (rfl | rfl)
      · exact hac rfl
      · exact hbc rfl⟩) rfl rfl
  have haQ₁ := hLQ₁ (hmemL hL₁).1
  have hbQ₁' := hLQ₁ (hmemL hL₁).2
  obtain ⟨L₂, R₂, Q₂, hL₂, hR₂, hQ₂, hu₂, hi₂, hcap₂, hLR₂, hLQ₂, hbR₂, hbQ₂, hsub₂, hX₂⟩ :=
    exists_cut hQ₁ hbQ₁' hcQ₁.1 haQ₁ hbc hab.symm hac.symm
  have hb₂ := hLQ₂ (hmemL hL₂).1
  have hc₂ := hLQ₂ (hmemL hL₂).2
  have hX₁₂ : L₁ \ {b} ⊆ discBd Q₂ \ R₂ := by
    refine hX₂ _ (GM11.IsLineWithEnds.isPreconnected_sdiff (GM11.IsLineWithEnds.symm hL₁)) ?_
      ⟨(hmemL hL₁).1, hab⟩
    rintro x ⟨hx, hxb⟩
    refine ⟨hLQ₁ hx, ?_⟩
    rintro (rfl | rfl)
    · exact hxb rfl
    · exact (hX₁ {x} isPreconnected_singleton (singleton_subset_iff.mpr ⟨hc, by
        rintro (rfl | rfl)
        · exact hac rfl
        · exact hbc rfl⟩) rfl rfl).2 (hi₁ ▸ hx |>.1)
  have ha₂ : a ∈ discBd Q₂ := (hX₁₂ ⟨(hmemL hL₁).1, hab⟩).1
  have hL₁Q₂ : L₁ ⊆ discBd Q₂ := fun x hx ↦ by
    by_cases h : x = b
    · exact h ▸ hb₂
    · exact (hX₁₂ ⟨hx, h⟩).1
  have haR₂ : a ∉ R₂ := (hX₁₂ ⟨(hmemL hL₁).1, hab⟩).2
  obtain ⟨L₃, R₃, Q₃, hL₃, hR₃, hQ₃, hu₃, hi₃, hcap₃, hLR₃, hLQ₃, hbR₃, hbQ₃, hsub₃, hX₃⟩ :=
    exists_cut hQ₂ hc₂ ha₂ hb₂ hac.symm hbc.symm hab
  have hcL₁ : c ∉ L₁ := fun h ↦ (hcQ₁.2) (hi₁ ▸ h |>.1)
  have haL₂ : a ∉ L₂ := fun h ↦ haR₂ (hi₂ ▸ h |>.1)
  have hX₁₃ : L₁ \ {a} ⊆ discBd Q₃ \ R₃ := by
    refine hX₃ _ (GM11.IsLineWithEnds.isPreconnected_sdiff hL₁) ?_ ⟨(hmemL hL₁).2, hab.symm⟩
    rintro x ⟨hx, hxa⟩
    refine ⟨hL₁Q₂ hx, ?_⟩
    rintro (rfl | rfl)
    · exact hcL₁ hx
    · exact hxa rfl
  have hX₂₃ : L₂ \ {c} ⊆ discBd Q₃ \ R₃ := by
    refine hX₃ _ (GM11.IsLineWithEnds.isPreconnected_sdiff (GM11.IsLineWithEnds.symm hL₂)) ?_
      ⟨(hmemL hL₂).1, hbc⟩
    rintro x ⟨hx, hxc⟩
    refine ⟨hLQ₂ hx, ?_⟩
    rintro (rfl | rfl)
    · exact hxc rfl
    · exact haL₂ hx
  have ha₃ := hLQ₃ (hmemL hL₃).2
  have hc₃ := hLQ₃ (hmemL hL₃).1
  have hb₃ : b ∈ discBd Q₃ := (hX₁₃ ⟨(hmemL hL₁).2, hab.symm⟩).1
  have hbnR₃ : b ∉ R₃ := (hX₁₃ ⟨(hmemL hL₁).2, hab.symm⟩).2
  have hQ₃₂ : Q₃ ⊆ Q₂ := hu₃ ▸ subset_union_right
  have hQ₂₁ : Q₂ ⊆ Q₁ := hu₂ ▸ subset_union_right
  have hQ₁D : Q₁ ⊆ D := hu₁ ▸ subset_union_right
  have hL₁Q₃ : L₁ ⊆ Q₃ := fun x hx ↦ by
    by_cases h : x = a
    · exact h ▸ discBd_subset _ ha₃
    · exact discBd_subset _ (hX₁₃ ⟨hx, h⟩).1
  have hL₂Q₃ : L₂ ⊆ Q₃ := fun x hx ↦ by
    by_cases h : x = c
    · exact h ▸ discBd_subset _ hc₃
    · exact discBd_subset _ (hX₂₃ ⟨hx, h⟩).1
  have hL₃Q₃ : L₃ ⊆ Q₃ := hi₃ ▸ inter_subset_right
  have hR₂Q₁ : R₂ ⊆ Q₁ := hu₂ ▸ subset_union_left
  have hR₃Q₂ : R₃ ⊆ Q₂ := hu₃ ▸ subset_union_left
  have hYline : IsLineWithEnds (L₁ ∪ L₂) a c := by
    refine GM11.IsLineWithEnds.union (v := b) (GM11.IsLineWithEnds.symm hL₁) hL₂ ?_
    ext x
    constructor
    · rintro ⟨hx₁, hx₂⟩
      by_contra hn
      exact (hX₁₂ ⟨hx₁, hn⟩).2 (hi₂ ▸ hx₂ |>.1)
    · rintro rfl
      exact ⟨(hmemL hL₁).2, (hmemL hL₂).1⟩
  have hbd₃ : discBd Q₃ ⊆ L₁ ∪ L₂ ∪ L₃ := by
    intro x hx
    rcases hbQ₃ hx with h | h
    · exact Or.inr h
    · have hY :=
        subset_line_of_preconnected (F := discBd Q₂) hQ₂.isOArc_discBd
          (GM11.IsLineWithEnds.symm hYline) (union_subset hL₁Q₂ hLQ₂) (X := connectedComponentIn
            (discBd Q₂ \ {c, a}) b)
          isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
          (mem_connectedComponentIn ⟨hb₂, by
            rintro (rfl | rfl)
            · exact hbc rfl
            · exact hab.symm rfl⟩) (Or.inl (hmemL hL₁).2) h
      exact Or.inl hY
  have hbdQ₁ : ∀ {x}, x ∈ discBd D → x ∈ Q₂ → x ∈ discBd Q₂ := fun hx hxQ ↦
    hsub₂ ⟨hsub₁ ⟨hx, hQ₂₁ hxQ⟩, hxQ⟩
  have hbQ₁₂ : discBd Q₁ ⊆ L₁ ∪ discBd D := fun x hx ↦
    (hbQ₁ hx).imp_right fun h ↦ (connectedComponentIn_subset (discBd D \ {a, b}) c h).1
  have hbQ₂₂ : discBd Q₂ ⊆ L₂ ∪ discBd Q₁ := fun x hx ↦
    (hbQ₂ hx).imp_right fun h ↦ (connectedComponentIn_subset (discBd Q₁ \ {b, c}) a h).1
  have hL₂c : L₂ ∩ discBd D = {b, c} := by
    ext x
    constructor
    · rintro ⟨hx, hxb⟩
      have : x ∈ L₂ ∩ discBd Q₁ := ⟨hx, hsub₁ ⟨hxb, hR₂Q₁ (hi₂ ▸ hx |>.1)⟩⟩
      rwa [hcap₂] at this
    · rintro (rfl | rfl)
      · exact ⟨(hmemL hL₂).1, hb⟩
      · exact ⟨(hmemL hL₂).2, hc⟩
  have hL₃c : L₃ ∩ discBd D = {c, a} := by
    ext x
    constructor
    · rintro ⟨hx, hxb⟩
      have hxQ : x ∈ Q₂ := hR₃Q₂ (hi₃ ▸ hx |>.1)
      have : x ∈ L₃ ∩ discBd Q₂ := ⟨hx, hbdQ₁ hxb hxQ⟩
      rwa [hcap₃] at this
    · rintro (rfl | rfl)
      · exact ⟨(hmemL hL₃).1, hc⟩
      · exact ⟨(hmemL hL₃).2, ha⟩
  have hcapD : Q₃ ∩ discBd D = {a, b, c} := by
    ext x
    constructor
    · rintro ⟨hx, hxb⟩
      rcases hbd₃ (hsub₃ ⟨hbdQ₁ hxb (hQ₃₂ hx), hx⟩) with (h | h) | h
      · have : x ∈ L₁ ∩ discBd D := ⟨h, hxb⟩
        rw [hcap₁] at this
        rcases this with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · have : x ∈ L₂ ∩ discBd D := ⟨h, hxb⟩
        rw [hL₂c] at this
        rcases this with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · have : x ∈ L₃ ∩ discBd D := ⟨h, hxb⟩
        rw [hL₃c] at this
        rcases this with rfl | rfl
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl
    · rintro (rfl | rfl | rfl)
      · exact ⟨discBd_subset _ ha₃, ha⟩
      · exact ⟨discBd_subset _ hb₃, hb⟩
      · exact ⟨discBd_subset _ hc₃, hc⟩
  refine ⟨Q₃, L₁, L₂, L₃, R₁, R₂, R₃, hQ₃, (hQ₃₂.trans hQ₂₁).trans hQ₁D, ha₃, hb₃, hc₃, hcapD, hbd₃,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨hL₁, hR₁, hu₁ ▸ subset_union_left, hL₁Q₃, ?_, hcap₁, hLR₁, hbR₁, hcQ₁.2⟩
    ext x
    constructor
    · rintro ⟨hx, hxQ⟩
      exact hi₁ ▸ ⟨hx, hQ₂₁ (hQ₃₂ hxQ)⟩
    · intro hx
      exact ⟨(hi₁ ▸ hx : x ∈ R₁ ∩ Q₁).1, hL₁Q₃ hx⟩
  · refine ⟨hL₂, hR₂, hR₂Q₁.trans hQ₁D, hL₂Q₃, ?_, hL₂c, hLR₂, ?_, haR₂⟩
    · ext x
      constructor
      · rintro ⟨hx, hxQ⟩
        exact hi₂ ▸ ⟨hx, hQ₃₂ hxQ⟩
      · intro hx
        exact ⟨(hi₂ ▸ hx : x ∈ R₂ ∩ Q₂).1, hL₂Q₃ hx⟩
    · intro x hx
      rcases hbR₂ hx with h | h
      · exact Or.inl h
      · rcases hbQ₁₂ h with h' | h'
        · by_cases hxb : x = b
          · exact Or.inl (hxb ▸ (hmemL hL₂).1)
          · exact absurd (discBd_subset _ hx) (hX₁₂ ⟨h', hxb⟩).2
        · exact Or.inr h'
  · refine ⟨hL₃, hR₃, (hR₃Q₂.trans hQ₂₁).trans hQ₁D, hL₃Q₃, hi₃, hL₃c, hLR₃, ?_, hbnR₃⟩
    intro x hx
    have hxR := discBd_subset _ hx
    rcases hbR₃ hx with h | h
    · exact Or.inl h
    · rcases hbQ₂₂ h with h' | h'
      · by_cases hxc : x = c
        · exact Or.inl (hxc ▸ (hmemL hL₃).1)
        · exact absurd hxR (hX₂₃ ⟨h', hxc⟩).2
      · rcases hbQ₁₂ h' with h'' | h''
        · by_cases hxa : x = a
          · exact Or.inl (hxa ▸ (hmemL hL₃).2)
          · exact absurd hxR (hX₁₃ ⟨h'', hxa⟩).2
        · exact Or.inr h''
  · rintro x ⟨hx₁, hx₂⟩
    have hxL : x ∈ L₁ := hi₁ ▸ ⟨hx₁, hR₂Q₁ hx₂⟩
    by_contra hn
    exact (hX₁₂ ⟨hxL, fun h ↦ hn (Or.inr (Or.inl h))⟩).2 hx₂
  · rintro x ⟨hx₁, hx₃⟩
    have hxL : x ∈ L₁ := hi₁ ▸ ⟨hx₁, hQ₂₁ (hR₃Q₂ hx₃)⟩
    by_contra hn
    exact (hX₁₃ ⟨hxL, fun h ↦ hn (Or.inl h)⟩).2 hx₃
  · rintro x ⟨hx₂, hx₃⟩
    have hxL : x ∈ L₂ := hi₂ ▸ ⟨hx₂, hR₃Q₂ hx₃⟩
    by_contra hn
    exact (hX₂₃ ⟨hxL, fun h ↦ hn (Or.inr (Or.inr h))⟩).2 hx₃
  · rw [← hu₁, ← hu₂, ← hu₃]
    ext x
    simp only [mem_union]
    tauto

end GraphMinor.GM19
