/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.CutCell

/-!
# The painting on the cut surface

Let `ψ` map a part of the cut surface to the surface, and let `Γ` be a painting that is normal along
the arc `F`. We lift the cells that
lie in the image of `ψ`, and we add one new border cell along each lift of `F` (`cutPainting`). This
is the painting `Γ₀` of the proof of
(5.3) of Graph Minors XVII (page 172). The new cells are thin discs from `exists_wedge`.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {Y S : Type} [TopologicalSpace Y] [TopologicalSpace S]

/-- The data of a cut: `Ks` are the lifts of the arc `F` in `Y`, and `e₁ K`, `e₂ K` are the ends of
a lift `K`. -/
structure LiftData (ψ : Y → S) (F : Set S) (n₁ n₂ : S) (Ks : Set (Set Y)) (e₁ e₂ : Set Y
  → Y) : Prop where
  finite : Ks.Finite
  line : ∀ K ∈ Ks, IsLineWithEnds K (e₁ K) (e₂ K)
  bij : ∀ K ∈ Ks, BijOn ψ K F
  end₁ : ∀ K ∈ Ks, ψ (e₁ K) = n₁
  end₂ : ∀ K ∈ Ks, ψ (e₂ K) = n₂
  disj : Ks.PairwiseDisjoint id
  cover : ⋃₀ Ks = ψ ⁻¹' F

omit [TopologicalSpace S] in
/-- There are disjoint thin discs along the lifts. -/
theorem exists_wedges {ψ : Y → S} {F : Set S} {n₁ n₂ : S} {Ks : Set (Set Y)} {e₁ e₂ : Set Y → Y}
  (hY : IsSurface Y) (hbdF : ψ ⁻¹' F ⊆ bd Y)
    (hL : LiftData ψ F n₁ n₂ Ks e₁ e₂) {Z : Set Y} (hZ : IsClosed Z) (hZK : ∀ K ∈ Ks, Z ∩ K ⊆
      {e₁ K, e₂ K}) :
    ∃ D : Set Y → Set Y, (∀ K ∈ Ks, IsClosedDisc (D K) ∧ K ⊆ discBd (D K) ∧ D K ∩ Z ⊆ {e₁ K, e₂ K}
      ∧ D K ∩ bd Y = K) ∧
      ∀ K ∈ Ks, ∀ K' ∈ Ks, K ≠ K' → Disjoint (D K) (D K') := by
  classical
  have ht2 : T2Space Y := hY.2.1
  have hsub : ∀ Ls ⊆ Ks, Ls.Finite → ∃ D : Set Y → Set Y, (∀ K ∈ Ls, IsClosedDisc (D K)
    ∧ K ⊆ discBd (D K) ∧ D K ∩ Z ⊆ {e₁ K, e₂ K} ∧ D K ∩ bd Y = K) ∧
      ∀ K ∈ Ls, ∀ K' ∈ Ls, K ≠ K' → Disjoint (D K) (D K') := by
    intro Ls hLs hfin
    induction Ls, hfin using Set.Finite.induction_on with
    | empty => exact ⟨fun _ => ∅, by simp, by simp⟩
    | @insert K Ms hKn hfin ih =>
      obtain ⟨D, hD, hdis⟩ := ih ((subset_insert _ _).trans hLs)
      have hKs : K ∈ Ks := hLs (mem_insert _ _)
      have hKb : K ⊆ bd Y := fun z hz => hbdF (hL.cover ▸ ⟨K, hKs, hz⟩)
      have hcl : IsClosed (Z ∪ ⋃ K' ∈ Ms, D K') :=
        hZ.union (hfin.isClosed_biUnion fun K' hK' => (hD K' hK').1.isClosed)
      have hm : (Z ∪ ⋃ K' ∈ Ms, D K') ∩ K ⊆ {e₁ K, e₂ K} := by
        rintro z ⟨h | h, hzK⟩
        · exact hZK K hKs ⟨h, hzK⟩
        · obtain ⟨K', hK', hz⟩ := mem_iUnion₂.mp h
          have h1 : z ∈ D K' ∩ bd Y := ⟨hz, hKb hzK⟩
          rw [(hD K' hK').2.2.2] at h1
          have hne : K ≠ K' := fun h2 => hKn (h2 ▸ hK')
          exact absurd h1 (disjoint_left.mp (hL.disj hKs (hLs ((subset_insert _ _) hK')) hne) hzK)
      obtain ⟨E, hE, hEb, hEZ, hEbd⟩ := exists_wedge hY (hL.line K hKs) hKb hcl hm
      have hdisE : ∀ K' ∈ Ms, Disjoint E (D K') := fun K' hK' => by
        rw [disjoint_left]
        intro z hzE hzD
        have h1 : z ∈ E ∩ (Z ∪ ⋃ K' ∈ Ms, D K') := ⟨hzE, .inr (mem_iUnion₂.mpr ⟨K', hK', hzD⟩)⟩
        have h2 := hEZ h1
        have h3 : z ∈ K := by
          rcases h2 with rfl | rfl
          · exact (hL.line K hKs).left_mem
          · exact (hL.line K hKs).right_mem
        have h4 : z ∈ D K' ∩ bd Y := ⟨hzD, hKb h3⟩
        rw [(hD K' hK').2.2.2] at h4
        have hne : K ≠ K' := fun h5 => hKn (h5 ▸ hK')
        exact disjoint_left.mp (hL.disj hKs (hLs ((subset_insert _ _) hK')) hne) h3 h4
      have hne' : ∀ K' ∈ Ms, K' ≠ K := fun K' h he => hKn (he ▸ h)
      refine ⟨Function.update D K E, ?_, ?_⟩
      · rintro K' (rfl | hK')
        · simp only [Function.update_self]
          exact ⟨hE, hEb, fun z hz => hEZ ⟨hz.1, .inl hz.2⟩, hEbd⟩
        · rw [Function.update_of_ne (hne' _ hK')]
          exact hD K' hK'
      · rintro K₁ (rfl | h₁) K₂ (rfl | h₂) hne
        · exact absurd rfl hne
        · rw [Function.update_self, Function.update_of_ne (hne' _ h₂)]
          exact hdisE K₂ h₂
        · rw [Function.update_self, Function.update_of_ne (hne' _ h₁)]
          exact (hdisE K₁ h₁).symm
        · rw [Function.update_of_ne (hne' _ h₁), Function.update_of_ne (hne' _ h₂)]
          exact hdis K₁ h₁ K₂ h₂ hne
  exact hsub Ks subset_rfl hL.finite

/-- The hypotheses on a cut of a painted surface. -/
structure CutSetup (Γ : Painting S) (ψ : Y → S) (F : Set S) (n₁ n₂ : S) (Ks : Set (Set Y))
  (e₁ e₂ : Set Y → Y) : Prop where
  map : CutMap ψ F
  lift : LiftData ψ F n₁ n₂ Ks e₁ e₂
  surfS : IsSurface S
  surfY : IsSurface Y
  norm : Γ.IsNormal F
  arc : IsLineWithEnds F n₁ n₂
  bdF : F ∩ bd S = {n₁, n₂}
  internal : ∀ c ∈ Γ.C, Γ.IsInternalCell c → Disjoint (tilde c) F

/-- The cells of `Γ` in the image of `ψ`, off `F`. -/
def keepCells (Γ : Painting S) (ψ : Y → S) (F : Set S) : Set (Set S) := {c ∈ Γ.C | c ⊆ range ψ \ F}

/-- The nodes that stay: those off `F`, and the ends of `F`. -/
def keepNodes (Γ : Painting S) (F : Set S) (n₁ n₂ : S) : Set S := (Γ.N \ F) ∪ {n₁, n₂}

section

variable {Γ : Painting S} {ψ : Y → S} {F : Set S} {n₁ n₂ : S} {Ks : Set (Set Y)} {e₁ e₂ : Set Y → Y}

namespace CutSetup

variable (h : CutSetup Γ ψ F n₁ n₂ Ks e₁ e₂)
include h

theorem t2 : T2Space S := h.surfS.2.1
theorem t2Y : T2Space Y := h.surfY.2.1
theorem compY : CompactSpace Y := h.surfY.1

theorem n₁_mem : n₁ ∈ F ∩ bd S := h.bdF ▸ mem_insert _ _
theorem n₂_mem : n₂ ∈ F ∩ bd S := h.bdF ▸ mem_insert_of_mem _ rfl

theorem n₁_N : n₁ ∈ Γ.N := h.norm ⟨h.n₁_mem.1, Γ.bd_subset h.n₁_mem.2⟩
theorem n₂_N : n₂ ∈ Γ.N := h.norm ⟨h.n₂_mem.1, Γ.bd_subset h.n₂_mem.2⟩

theorem keepNodes_subset : keepNodes Γ F n₁ n₂ ⊆ Γ.N := by
  rintro x (hx | rfl | rfl)
  · exact hx.1
  · exact h.n₁_N
  · exact h.n₂_N

theorem cell_disjoint {c : Set S} (hc : c ∈ Γ.C) : Disjoint c F :=
  disjoint_left.mpr fun _ hx hF => (arcComponentsIn_subset hc hx).2 (h.norm ⟨hF,
    (arcComponentsIn_subset hc hx).1⟩)

theorem side {c : Set S} (hc : c ∈ Γ.C) : c ⊆ range ψ \ F ∨ Disjoint c (range ψ) := by
  have := h.t2
  have := h.t2Y
  have := h.compY
  have hrc : IsClosed (range ψ) := (isCompact_range h.map.cont).isClosed
  have hp := (arcComponentsIn_isPathConnected hc).isConnected.isPreconnected
  have hsub : c ⊆ (range ψ \ F) ∪ (range ψ)ᶜ := fun x hx => by
    by_cases hr : x ∈ range ψ
    · exact .inl ⟨hr, disjoint_left.mp (h.cell_disjoint hc) hx⟩
    · exact .inr hr
  rcases hp.subset_or_subset h.map.isOpen hrc.isOpen_compl (disjoint_left.mpr fun x hx hx'
    => hx' hx.1) hsub with h1 | h1
  · exact .inl h1
  · exact .inr (disjoint_left.mpr fun x hx hx' => h1 hx hx')

theorem tilde_F {c : Set S} (hc : c ∈ Γ.C) : tilde c ∩ F ⊆ {n₁, n₂} := by
  have := h.t2
  by_cases hb : (c ∩ bd S).Nonempty
  · obtain ⟨u, v, -, htilde, -, -, hu, hv⟩ := Γ.border_cell_exists_ends hc hb
    rintro x ⟨hx, hxF⟩
    rw [← h.bdF]
    refine ⟨hxF, ?_⟩
    rw [htilde] at hx
    rcases hx with rfl | rfl
    · exact hu.2
    · exact hv.2
  · rintro x ⟨hx, hxF⟩
    exact absurd hxF (disjoint_left.mp (h.internal c hc ⟨hc, hb⟩) hx)

theorem finite_nodes : (ψ ⁻¹' keepNodes Γ F n₁ n₂).Finite := by
  refine (Γ.finite_N.subset h.keepNodes_subset).preimage' fun x _ => ?_
  by_cases hx : x ∈ F
  · exact Set.finite_of_encard_le_coe (h.map.fib x hx)
  · refine Set.Subsingleton.finite fun y hy y' hy' => ?_
    have h1 : ψ y = x := hy
    have h2 : ψ y' = x := hy'
    exact h.map.inj (show ψ y ∉ F by rwa [h1]) (show ψ y' ∉ F by rwa [h2]) (h1.trans h2.symm)

theorem end_of_mem {K : Set Y} (hK : K ∈ Ks) {y : Y} (hy : y ∈ K) (h1 : ψ y = n₁ ∨ ψ y = n₂) : y ∈
  ({e₁ K, e₂ K} : Set Y) := by
  have hl := h.lift.line K hK
  have hi := (h.lift.bij K hK).injOn
  rcases h1 with h1 | h1
  · exact .inl (hi hy hl.left_mem (h1.trans (h.lift.end₁ K hK).symm))
  · exact .inr (hi hy hl.right_mem (h1.trans (h.lift.end₂ K hK).symm))

variable [Nonempty Y]

theorem exists_lift {c : Set S} (hc : c ∈ keepCells Γ ψ F) :
    ∃ τ : S → Y, ContinuousOn τ (closure c) ∧ τ '' closure c = closure (ψ ⁻¹' c) ∧
      (∀ x ∈ closure c, ψ (τ x) = x) ∧ (∀ y ∈ closure (ψ ⁻¹' c), τ (ψ y) = y) ∧
      tilde (ψ ⁻¹' c) = τ '' tilde c ∧ IsClosedDisc (closure (ψ ⁻¹' c)) ∧ tilde (ψ ⁻¹' c) ⊆ discBd
        (closure (ψ ⁻¹' c)) := by
  have := h.t2
  have := h.t2Y
  have := h.compY
  exact h.map.exists_lift (h.cell_disjoint hc.1) (Γ.isClosedDisc_closure_cell hc.1)
    (Γ.tilde_subset_discBd hc.1) (Γ.cell_disc c hc.1).2.2.1 hc.2

theorem closure_lift {c : Set S} (hc : c ∈ keepCells Γ ψ F) : closure
  (ψ ⁻¹' c) ⊆ ψ ⁻¹' c ∪ ψ ⁻¹' keepNodes Γ F n₁ n₂ := by
  obtain ⟨τ, -, -, h3, h4, h5, -, -⟩ := h.exists_lift hc
  intro y hy
  by_cases hyc : y ∈ ψ ⁻¹' c
  · exact .inl hyc
  · right
    obtain ⟨x, hx, rfl⟩ := (h5 ▸ (⟨hy, hyc⟩ : y ∈ tilde (ψ ⁻¹' c)) : y ∈ τ '' tilde c)
    rw [mem_preimage, h3 x hx.1]
    by_cases hxF : x ∈ F
    · exact .inr (h.tilde_F hc.1 ⟨hx, hxF⟩)
    · exact .inl ⟨Γ.tilde_subset_N hc.1 hx, hxF⟩

omit [Nonempty Y] in
theorem lift_nodes {c : Set S} (hc : c ∈ keepCells Γ ψ F) : Disjoint (ψ ⁻¹' c)
  (ψ ⁻¹' keepNodes Γ F n₁ n₂) :=
  disjoint_left.mpr fun _ hy hy' => (arcComponentsIn_subset hc.1 hy).2 (h.keepNodes_subset hy')

/-- The closed set that the new cells have to avoid. -/
def Z (_h : CutSetup Γ ψ F n₁ n₂ Ks e₁ e₂) : Set Y := (⋃ c ∈ keepCells Γ ψ F, closure
  (ψ ⁻¹' c)) ∪ ψ ⁻¹' keepNodes Γ F n₁ n₂

omit [Nonempty Y] in
theorem isClosed_Z : IsClosed h.Z := by
  have := h.t2Y
  have hfin : (keepCells Γ ψ F).Finite := Γ.finite_cells.subset fun c hc => hc.1
  exact (hfin.isClosed_biUnion fun c _ => isClosed_closure).union h.finite_nodes.isClosed

theorem Z_inter {K : Set Y} (hK : K ∈ Ks) : h.Z ∩ K ⊆ {e₁ K, e₂ K} := by
  have hF : ∀ y ∈ K, ψ y ∈ F := fun y hy => (show y ∈ ψ ⁻¹' F from h.lift.cover ▸ ⟨K, hK, hy⟩)
  have key : ∀ y ∈ K, y ∈ ψ ⁻¹' keepNodes Γ F n₁ n₂ → y ∈ ({e₁ K, e₂ K} : Set Y) := fun y hy hn
    => by
    rcases hn with hn | hn | hn
    · exact absurd (hF y hy) hn.2
    · exact h.end_of_mem hK hy (.inl hn)
    · exact h.end_of_mem hK hy (.inr hn)
  rintro y ⟨hy | hy, hyK⟩
  · obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.mp hy
    rcases h.closure_lift hc hyc with h1 | h1
    · exact absurd (hF y hyK) (disjoint_left.mp (h.cell_disjoint hc.1) h1)
    · exact key y hyK h1
  · exact key y hyK hy

theorem exists_painting : ∃ (D : Set Y → Set Y) (Γ' : Painting Y),
    (∀ K ∈ Ks, IsClosedDisc (D K) ∧ K ⊆ discBd (D K) ∧ D K ∩ h.Z ⊆ {e₁ K, e₂ K} ∧ D K ∩ bd Y = K) ∧
    Γ'.N = ψ ⁻¹' keepNodes Γ F n₁ n₂ ∧ Γ'.C = (fun c => ψ ⁻¹' c) '' keepCells Γ ψ F ∪ (fun K
      => D K \ {e₁ K, e₂ K}) '' Ks := by
  have ht2S := h.t2
  have ht2 := h.t2Y
  have hcY := h.compY
  obtain ⟨D, hD, hdis⟩ := exists_wedges h.surfY h.map.bdF h.lift h.isClosed_Z fun K hK
    => h.Z_inter hK
  have hfinC : (keepCells Γ ψ F).Finite := Γ.finite_cells.subset fun c hc => hc.1
  have hbdD : ∀ K ∈ Ks, e₁ K ∈ discBd (D K) ∧ e₂ K ∈ discBd (D K) := fun K hK =>
    ⟨(hD K hK).2.1 (h.lift.line K hK).left_mem, (hD K hK).2.1 (h.lift.line K hK).right_mem⟩
  have hnew := fun K (hK : K ∈ Ks) => disc_diff_two (hD K hK).1 (hbdD K hK).1 (hbdD K hK).2
  have hends : ∀ K ∈ Ks, e₁ K ∈ ψ ⁻¹' keepNodes Γ F n₁ n₂ ∧
      e₂ K ∈ ψ ⁻¹' keepNodes Γ F n₁ n₂ := by
    intro K hK
    constructor
    · rw [mem_preimage, h.lift.end₁ K hK]
      exact .inr (.inl rfl)
    · rw [mem_preimage, h.lift.end₂ K hK]
      exact .inr (.inr rfl)
  have hDN : ∀ K ∈ Ks, ∀ y ∈ D K, y ∈ ψ ⁻¹' keepNodes Γ F n₁ n₂ → y ∈ ({e₁ K, e₂ K} : Set Y)
    := fun K hK y hy hn =>
    (hD K hK).2.2.1 ⟨hy, .inr hn⟩
  let U' : Set Y := ((⋃ c ∈ keepCells Γ ψ F, closure (ψ ⁻¹' c)) ∪ ψ ⁻¹' keepNodes Γ F n₁ n₂) ∪ ⋃ K
    ∈ Ks, D K
  let N' : Set Y := ψ ⁻¹' keepNodes Γ F n₁ n₂
  let J : Set (Set Y) := (fun c => ψ ⁻¹' c) '' keepCells Γ ψ F ∪ (fun K => D K \ {e₁ K, e₂ K}) '' Ks
  have hJ : arcComponentsIn (U' \ N') = J := by
    refine arcComponentsIn_eq_of_finite_cover ((hfinC.image _).union (h.lift.finite.image _)) ?_ ?_
      ?_ ?_ ?_
    · ext y
      constructor
      · rintro ⟨d, (⟨c, hc, rfl⟩ | ⟨K, hK, rfl⟩), hy⟩
        · exact ⟨.inl (.inl (mem_iUnion₂.mpr ⟨c, hc, subset_closure hy⟩)),
            disjoint_left.mp (h.lift_nodes hc) hy⟩
        · exact ⟨.inr (mem_iUnion₂.mpr ⟨K, hK, hy.1⟩), fun hn => hy.2 (hDN K hK y hy.1 hn)⟩
      · rintro ⟨(hy | hy) | hy, hn⟩
        · obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.mp hy
          exact ⟨_, .inl ⟨c, hc, rfl⟩, (h.closure_lift hc hyc).resolve_right hn⟩
        · exact absurd hy hn
        · obtain ⟨K, hK, hyK⟩ := mem_iUnion₂.mp hy
          refine ⟨_, .inr ⟨K, hK, rfl⟩, hyK, ?_⟩
          rintro (rfl | rfl)
          · exact hn (hends K hK).1
          · exact hn (hends K hK).2
    · rintro d (⟨c, hc, rfl⟩ | ⟨K, hK, rfl⟩)
      · obtain ⟨x, hx⟩ := arcComponentsIn_nonempty hc.1
        obtain ⟨y, rfl⟩ := (hc.2 hx).1
        exact ⟨y, hx⟩
      · exact (hnew K hK).2.2.2
    · rintro d (⟨c, hc, rfl⟩ | ⟨K, hK, rfl⟩)
      · obtain ⟨σ, h1, h2, h3⟩ := h.map.exists_sec
        have h4 : ψ ⁻¹' c = σ '' c := by
          ext y
          constructor
          · intro hy
            exact ⟨ψ y, hy, h3 y (hc.2 hy).2⟩
          · rintro ⟨x, hx, rfl⟩
            rw [mem_preimage, h2 x (hc.2 hx)]
            exact hx
        change IsPathConnected (ψ ⁻¹' c)
        rw [h4]
        exact (arcComponentsIn_isPathConnected hc.1).image' (h1.mono hc.2)
      · exact (hnew K hK).2.2.1
    · have hcd : ∀ c ∈ keepCells Γ ψ F, ∀ K ∈ Ks, Disjoint (ψ ⁻¹' c) (D K \ {e₁ K, e₂ K})
      := fun c hc K hK => by
        rw [disjoint_left]
        intro y hy hy'
        exact hy'.2 ((hD K hK).2.2.1 ⟨hy'.1, .inl (mem_iUnion₂.mpr ⟨c, hc, subset_closure hy⟩)⟩)
      rintro d (⟨c, hc, rfl⟩ | ⟨K, hK, rfl⟩) d' (⟨c', hc', rfl⟩ | ⟨K', hK', rfl⟩) hne
      · have hcc : c ≠ c' := fun he => hne (by rw [he])
        exact (arcComponentsIn_disjoint hc.1 hc'.1 hcc).preimage _
      · exact hcd c hc K' hK'
      · exact (hcd c' hc' K hK).symm
      · have hkk : K ≠ K' := fun he => hne (by rw [he])
        exact (hdis K hK K' hK' hkk).mono sdiff_subset sdiff_subset
    · rintro d (⟨c, hc, rfl⟩ | ⟨K, hK, rfl⟩)
      · apply subset_antisymm
        · rintro y ⟨hy, -, hn⟩
          exact (h.closure_lift hc hy).resolve_right hn
        · intro y hy
          exact ⟨subset_closure hy, .inl (.inl (mem_iUnion₂.mpr ⟨c, hc, subset_closure hy⟩)),
            disjoint_left.mp (h.lift_nodes hc) hy⟩
      · simp only [(hnew K hK).1]
        apply subset_antisymm
        · rintro y ⟨hy, -, hn⟩
          refine ⟨hy, ?_⟩
          rintro (rfl | rfl)
          · exact hn (hends K hK).1
          · exact hn (hends K hK).2
        · intro y hy
          exact ⟨hy.1, .inr (mem_iUnion₂.mpr ⟨K, hK, hy.1⟩), fun hn => hy.2 (hDN K hK y hy.1 hn)⟩
  let Γ' : Painting Y :=
    { U := U'
      N := N'
      isClosed_U := ((hfinC.isClosed_biUnion fun c _ => isClosed_closure).union
        h.finite_nodes.isClosed).union
        (h.lift.finite.isClosed_biUnion fun K hK => (hD K hK).1.isClosed)
      N_subset := fun y hy => .inl (.inr hy)
      finite_N := h.finite_nodes
      finite_cells := by
        rw [hJ]
        exact (hfinC.image _).union (h.lift.finite.image _)
      cell_disc := by
        rw [hJ]
        rintro d (⟨c, hc, rfl⟩ | ⟨K, hK, rfl⟩)
        · obtain ⟨τ, -, -, -, -, h5, h6, h7⟩ := h.exists_lift hc
          have hf := (Γ.cell_disc c hc.1).2.2
          exact ⟨h6, h7, h5 ▸ hf.1.image _, by
            change (tilde (ψ ⁻¹' c)).ncard ≤ 3
            rw [h5]
            exact (ncard_image_le hf.1).trans hf.2⟩
        · simp only [(hnew K hK).1, (hnew K hK).2.1]
          refine ⟨(hD K hK).1, ?_, by simp, ?_⟩
          · rintro _ (rfl | rfl)
            · exact (hbdD K hK).1
            · exact (hbdD K hK).2
          · exact (ncard_insert_le _ _).trans (by simp)
      bd_subset := by
        intro y hy
        by_cases hyF : ψ y ∈ F
        · obtain ⟨K, hK, hyK⟩ := (show y ∈ ⋃₀ Ks from h.lift.cover ▸ hyF)
          exact .inr (mem_iUnion₂.mpr ⟨K, hK, discBd_subset _ ((hD K hK).2.1 hyK)⟩)
        · have hyb := (h.map.mem_bd_iff hyF).mp hy
          by_cases hyN : ψ y ∈ Γ.N
          · exact .inl (.inr (.inl ⟨hyN, hyF⟩))
          · obtain ⟨c, hc, hyc⟩ := exists_mem_arcComponentsIn (show ψ y ∈ Γ.U \ Γ.N from
            ⟨Γ.bd_subset hyb, hyN⟩)
            have hck : c ∈ keepCells Γ ψ F := ⟨hc, (h.side hc).resolve_right fun h1
              => disjoint_left.mp h1 hyc (mem_range_self y)⟩
            exact .inl (.inl (mem_iUnion₂.mpr ⟨c, hck, subset_closure hyc⟩))
      border_cell := by
        rw [hJ]
        rintro d (⟨c, hc, rfl⟩ | ⟨K, hK, rfl⟩) hb
        · obtain ⟨τ, h1, h2, h3, h4, h5, -, -⟩ := h.exists_lift hc
          obtain ⟨y, hyc, hyb⟩ := hb
          have hyF : ψ y ∉ F := disjoint_left.mp (h.cell_disjoint hc.1) hyc
          have hb' : (c ∩ bd S).Nonempty := ⟨ψ y, hyc, (h.map.mem_bd_iff hyF).mp hyb⟩
          obtain ⟨u, v, huv, htilde, hL, hdiff, -, -⟩ := Γ.border_cell_exists_ends hc.1 hb'
          have hLe : closure (ψ ⁻¹' c) ∩ bd Y = τ '' (closure c ∩ bd S) := by
            apply subset_antisymm
            · rintro y ⟨hy, hyb⟩
              have hyA : ψ y ∈ closure c := by
                rw [← h2] at hy
                obtain ⟨x, hx, rfl⟩ := hy
                rw [h3 x hx]
                exact hx
              refine ⟨ψ y, ⟨hyA, ?_⟩, h4 y hy⟩
              by_cases hF : ψ y ∈ F
              · have h9 : ψ y ∈ ({n₁, n₂} : Set S) := h.tilde_F hc.1 ⟨⟨hyA, disjoint_right.mp
                (h.cell_disjoint hc.1) hF⟩, hF⟩
                exact (h.bdF.symm.subset h9).2
              · exact (h.map.mem_bd_iff hF).mp hyb
            · rintro _ ⟨x, hx, rfl⟩
              refine ⟨h2.subset (mem_image_of_mem _ hx.1), ?_⟩
              by_cases hF : x ∈ F
              · exact h.map.bdF (by rw [mem_preimage, h3 x hx.1]; exact hF)
              · exact (h.map.mem_bd_iff (by rw [h3 x hx.1]; exact hF)).mpr
                  (by rw [h3 x hx.1]; exact hx.2)
          obtain ⟨a, ha, hr, rfl, rfl⟩ := hL.exists_arc
          have hmem : ∀ t, a t ∈ closure c := fun t => (hr.subset (mem_range_self t)).1
          have hcomp : Continuous (τ ∘ a) := h1.comp_continuous ha.1 hmem
          have harc : IsArcMap (τ ∘ a) := ⟨hcomp, fun s t he => ha.2 (by
            have := congrArg ψ he
            simpa only [Function.comp, h3 _ (hmem _)] using this)⟩
          have hline := harc.isLineWithEnds
          rw [range_comp, hr, ← hLe] at hline
          have hne : τ (a 0) ≠ τ (a 1) := hline.ne'
          have ht : tilde (ψ ⁻¹' c) = {τ (a 0), τ (a 1)} := by
            rw [h5, htilde, image_pair]
          rw [ht]
          obtain ⟨f, -⟩ := id hline
          exact ⟨ncard_pair hne, by simp, ⟨f⟩, lineEnds_eq hline⟩
        · simp only [(hnew K hK).1, (hnew K hK).2.1, (hD K hK).2.2.2]
          have hl := h.lift.line K hK
          obtain ⟨f, -⟩ := id hl
          exact ⟨ncard_pair hl.ne', by simp, ⟨f⟩, lineEnds_eq hl⟩ }
  exact ⟨D, Γ', hD, rfl, hJ⟩

end CutSetup

end

end GraphMinor.GM17
