/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.ThinPainting

/-!
# The narrow painting is internally 3-connected

We keep the setting of `GraphMinor.GM19.ThinPainting`, with the small disc `Δ(c)` taken from
`GraphMinor.GM19.exists_lenses`. Between `Δ(c)` and the boundary of `cBar` lie three lenses. A
closed curve that
misses the new painting away from its vertices can be pushed off the lenses, by `push_off_side`.
After that
it misses the old painting too. So the old painting says what we need of the curve.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric GraphMinor.Surface

variable {S : Type} [TopologicalSpace S] [T2Space S]

/-- The small disc `Δ` and the lenses of a disc `D` with three marked boundary points `T`. -/
structure LensAt (D Δ T : Set S) (L R : Fin 3 → Set S) : Prop where
  disc : IsClosedDisc Δ
  sub : Δ ⊆ D
  T_bd : T ⊆ discBd Δ
  cap : Δ ∩ discBd D = T
  bdΔ : discBd Δ ⊆ ⋃ i, L i
  lens : ∀ i, ∃ a b d, T = {a, b, d} ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ IsLens D Δ (L i) (R i) a b d
  inter : ∀ i j, i ≠ j → R i ∩ R j ⊆ T
  cover : D = Δ ∪ ⋃ i, R i

theorem exists_lensAt {D T : Set S} (hD : IsClosedDisc D) (hT : T ⊆ discBd D) (h3 : T.ncard = 3) :
    ∃ Δ, ∃ L R : Fin 3 → Set S, LensAt D Δ T L R := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ncard_eq_three.mp h3
  have ha : a ∈ discBd D := hT (by simp)
  have hb : b ∈ discBd D := hT (by simp)
  have hc : c ∈ discBd D := hT (by simp)
  obtain ⟨Δ, L₁, L₂, L₃, R₁, R₂, R₃, h₁, h₂, h₃, h₄, h₅, h₆, h₇, l₁, l₂, l₃, i₁, i₂, i₃, hcov⟩ :=
    exists_lenses hD ha hb hc hab hac hbc
  refine ⟨Δ, ![L₁, L₂, L₃], ![R₁, R₂, R₃], ⟨h₁, h₂, ?_, h₆, ?_, ?_, ?_, ?_⟩⟩
  · rintro x (rfl | rfl | rfl)
    · exact h₃
    · exact h₄
    · exact h₅
  · intro x hx
    rcases h₇ hx with (h | h) | h
    · exact mem_iUnion.2 ⟨0, h⟩
    · exact mem_iUnion.2 ⟨1, h⟩
    · exact mem_iUnion.2 ⟨2, h⟩
  · intro i
    fin_cases i
    · exact ⟨a, b, c, rfl, hab, hac, hbc, l₁⟩
    · refine ⟨b, c, a, ?_, hbc, hab.symm, hac.symm, l₂⟩
      ext x
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
    · refine ⟨c, a, b, ?_, hac.symm, hbc.symm, hab, l₃⟩
      ext x
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | exact i₁
      | exact i₂
      | exact i₃
      | (rw [inter_comm]; first | exact i₁ | exact i₂ | exact i₃)
  · rw [hcov]
    ext x
    simp only [mem_union, mem_iUnion, Fin.exists_fin_succ]
    simp
    tauto

namespace LensAt

variable {D Δ T : Set S} {L R : Fin 3 → Set S}

omit [T2Space S] in
theorem line_mem {M : Set S} {u v : S} (h : IsLineWithEnds M u v) : u ∈ M ∧ v ∈ M := by
  obtain ⟨f, h0, h1⟩ := h
  exact ⟨h0 ▸ (f 0).2, h1 ▸ (f 1).2⟩

omit [T2Space S] in
/-- A lens holds exactly two marked points, the ends of its line. -/
theorem inter_T (h : LensAt D Δ T L R) (i : Fin 3) :
    ∃ a b, IsLineWithEnds (L i) a b ∧ R i ∩ T = {a, b} ∧ a ≠ b := by
  obtain ⟨a, b, d, rfl, hab, had, hbd, hl⟩ := h.lens i
  refine ⟨a, b, hl.line, ?_, hab⟩
  have hsub : L i ⊆ R i := hl.L_bd.trans (discBd_subset _)
  obtain ⟨ha, hb⟩ := line_mem hl.line
  ext x
  constructor
  · rintro ⟨hx, rfl | rfl | rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hx hl.third
  · rintro (rfl | rfl)
    · exact ⟨hsub ha, by simp⟩
    · exact ⟨hsub hb, by simp⟩

end LensAt

/-- Each edge of size 3 of `Γ` has a small disc and lenses. -/
def IsLensed (Γ : Painting S) (Δ : Set S → Set S) (L R : Set S → Fin 3 → Set S) : Prop :=
  ∀ c ∈ Γ.E, (tilde c).ncard = 3 → LensAt (closure c) (Δ c) (tilde c) (L c) (R c)

theorem exists_isLensed (Γ : Painting S) : ∃ Δ L R, IsLensed Γ Δ L R := by
  classical
  have h : ∀ c : Set S, ∃ Δ, ∃ L R : Fin 3 → Set S, c ∈ Γ.E → (tilde c).ncard = 3 →
      LensAt (closure c) Δ (tilde c) L R := by
    intro c
    by_cases hc : c ∈ Γ.E ∧ (tilde c).ncard = 3
    · obtain ⟨hD, hT, -⟩ := Γ.isDisc_of_three hc.1 hc.2
      obtain ⟨Δ, L, R, h⟩ := exists_lensAt hD hT hc.2
      exact ⟨Δ, L, R, fun _ _ ↦ h⟩
    · exact ⟨∅, fun _ ↦ ∅, fun _ ↦ ∅, fun h₁ h₂ ↦ absurd ⟨h₁, h₂⟩ hc⟩
  choose Δ L R h using h
  exact ⟨Δ, L, R, h⟩

section

variable {Γ : Painting S} {Δ : Set S → Set S} {L R : Set S → Fin 3 → Set S}

omit [T2Space S] in
theorem IsLensed.isCore (hl : IsLensed Γ Δ L R) : IsCore Γ Δ := fun c hc h3 ↦
  ⟨(hl c hc h3).disc, (hl c hc h3).sub, (hl c hc h3).T_bd, (hl c hc h3).cap⟩

omit [T2Space S] in
theorem closure_inter_closure_subset {c c' : Set S} (hc : c ∈ Γ.E) (hc' : c' ∈ Γ.E) (hne : c ≠ c') :
    closure c ∩ closure c' ⊆ Γ.V := by
  rintro x ⟨h₁, h₂⟩
  by_contra hn
  rcases Γ.closure_subset hc h₁ with h₃ | h₃
  · rcases Γ.closure_subset hc' h₂ with h₄ | h₄
    · exact hne (arcComp_eq_of_mem hc hc' h₃ h₄)
    · exact hn h₄
  · exact hn h₃

/-- The closed set that stays fixed: the vertices, the edges of size 2, and the small discs. -/
def fixedZ (Γ : Painting S) (Δ : Set S → Set S) : Set S :=
  Γ.V ∪ (⋃ e ∈ {e ∈ Γ.E | (tilde e).ncard = 2}, closure e) ∪
    ⋃ c ∈ {c ∈ Γ.E | (tilde c).ncard = 3}, Δ c

theorem isClosed_fixedZ (hΔ : IsCore Γ Δ) : IsClosed (fixedZ Γ Δ) := by
  have htwo : {e ∈ Γ.E | (tilde e).ncard = 2}.Finite :=
    Γ.finite_edges.subset fun _ h => h.1
  have hthree : {c ∈ Γ.E | (tilde c).ncard = 3}.Finite :=
    Γ.finite_edges.subset fun _ h => h.1
  exact (Γ.finite_V.isClosed.union (htwo.isClosed_biUnion fun _ _ => isClosed_closure)).union
    (hthree.isClosed_biUnion fun c hc => (hΔ c hc.1 hc.2).1.isClosed)

omit [T2Space S] in
theorem fixedZ_subset : fixedZ Γ Δ ⊆ thinU Γ Δ := by
  rintro x ((hx | hx) | hx)
  · exact Or.inl (Or.inl (Or.inl hx))
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    rcases Γ.closure_subset he.1 hxe with h | h
    · exact Or.inl (Or.inl (Or.inr (mem_iUnion₂.2 ⟨e, he, h⟩)))
    · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inr hx

omit [T2Space S] in
theorem lens_inter_fixedZ (hl : IsLensed Γ Δ L R) {c : Set S} (hc : c ∈ Γ.E)
    (h3 : (tilde c).ncard = 3) (i : Fin 3) : R c i ∩ fixedZ Γ Δ ⊆ L c i := by
  obtain ⟨a, b, d, ht, -, -, -, hlens⟩ := (hl c hc h3).lens i
  have hV : ∀ x ∈ R c i, x ∈ Γ.V → x ∈ L c i := fun x hx hxV ↦ by
    have h₁ : x ∈ closure c ∩ Γ.V := ⟨hlens.sub hx, hxV⟩
    rw [Γ.closure_inter_V hc] at h₁
    obtain ⟨u, v, hline, hset, -⟩ := (hl c hc h3).inter_T i
    have h₂ : x ∈ R c i ∩ tilde c := ⟨hx, h₁⟩
    rw [hset] at h₂
    obtain ⟨hu, hv⟩ := LensAt.line_mem hline
    rcases h₂ with rfl | rfl
    · exact hu
    · exact hv
  rintro x ⟨hx, (hz | hz) | hz⟩
  · exact hV x hx hz
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hz
    have hne : c ≠ e := fun h ↦ by
      have := he.2
      rw [← h] at this
      omega
    exact hV x hx (closure_inter_closure_subset hc he.1 hne ⟨hlens.sub hx, hxe⟩)
  · obtain ⟨c', hc', hxc⟩ := mem_iUnion₂.mp hz
    by_cases hcc : c = c'
    · subst hcc
      rw [← hlens.inter]
      exact ⟨hx, hxc⟩
    · exact hV x hx (closure_inter_closure_subset hc hc'.1 hcc
        ⟨hlens.sub hx, (hl c' hc'.1 hc'.2).sub hxc⟩)

/-- A closed curve that misses the narrow painting away from its vertices can be moved so that it
misses `Γ` away from its vertices, with all vertices fixed. -/
theorem exists_push (hS : IsSurface S) (hl : IsLensed Γ Δ L R) {F : Set S} (hF : IsOArc F)
    (hFU : F ∩ thinU Γ Δ ⊆ Γ.V) :
    ∃ h : S ≃ₜ S, (∀ n ∈ Γ.V, h n = n) ∧ (h '' F) ∩ Γ.U ⊆ Γ.V := by
  let Z3 : Type := {c : Set S // c ∈ Γ.E ∧ (tilde c).ncard = 3}
  have hfin : {c ∈ Γ.E | (tilde c).ncard = 3}.Finite :=
    Γ.finite_edges.subset fun _ h => h.1
  have : Finite Z3 := hfin.to_subtype
  let ι : Type := Z3 × Fin 3
  obtain ⟨h, hfix, hZ', hD'⟩ := push_off_side (ι := ι) hS (N := Γ.V) (Z := fixedZ Γ Δ)
    (D := fun i ↦ R i.1.1 i.2) (L := fun i ↦ L i.1.1 i.2) Γ.finite_V (isClosed_fixedZ hl.isCore)
    (fun i ↦ by
      obtain ⟨a, b, d, ht, -, -, -, hlens⟩ := (hl _ i.1.2.1 i.1.2.2).lens i.2
      exact hlens.disc)
    (fun i ↦ by
      rcases i with ⟨⟨c, hc, h3⟩, i⟩
      obtain ⟨a, b, hline, hset, -⟩ := (hl c hc h3).inter_T i
      obtain ⟨a', b', d', ht, -, -, -, hlens⟩ := (hl c hc h3).lens i
      refine ⟨a, b, hline, ?_, hlens.L_bd, ?_⟩
      · have heq : R c i ∩ Γ.V = R c i ∩ tilde c := by
          rw [← Γ.closure_inter_V hc]
          ext x
          exact ⟨fun hx ↦ ⟨hx.1, hlens.sub hx.1, hx.2⟩, fun hx ↦ ⟨hx.1, hx.2.2⟩⟩
        exact heq.trans hset
      · rintro x ⟨hx, hxb⟩
        rcases Γ.closure_subset hc (hlens.sub hx) with h | h
        · have := size_two_of_border Γ hc ⟨x, h, hxb⟩
          omega
        · exact h)
    (fun i j hij ↦ by
      obtain ⟨⟨c, hc, h3⟩, i'⟩ := i
      obtain ⟨⟨c', hc', h3'⟩, j'⟩ := j
      obtain ⟨_, _, _, -, -, -, -, l₁⟩ := (hl c hc h3).lens i'
      obtain ⟨_, _, _, -, -, -, -, l₂⟩ := (hl c' hc' h3').lens j'
      by_cases hcc : c = c'
      · subst hcc
        have hne : i' ≠ j' := fun he ↦ hij (by rw [he])
        exact ((hl c hc h3).inter _ _ hne).trans (Γ.tilde_subset_V hc)
      · exact (inter_subset_inter l₁.sub l₂.sub).trans (closure_inter_closure_subset hc hc' hcc))
    (fun i ↦ lens_inter_fixedZ hl i.1.2.1 i.1.2.2 i.2)
    hF (fun x hx ↦ hFU ⟨hx.1, fixedZ_subset hx.2⟩)
    (fun i x hx ↦ by
      rcases i with ⟨⟨c, hc, h3⟩, i⟩
      obtain ⟨_, _, _, -, -, -, -, l₁⟩ := (hl c hc h3).lens i
      exact hFU ⟨hx.1, Or.inr (mem_biUnion (show c ∈ {c ∈ Γ.E | (tilde c).ncard = 3} from ⟨hc, h3⟩)
        (l₁.sub_Δ hx.2))⟩)
  refine ⟨h, hfix, ?_⟩
  rintro x ⟨hxF, hxU⟩
  by_contra hn
  have hm : x ∈ Γ.U \ Γ.V := ⟨hxU, hn⟩
  have hc : pathComponentIn (Γ.U \ Γ.V) x ∈ Γ.E := GM20.mem_arcComponentsIn_pathComponentIn hm
  have hxc : x ∈ pathComponentIn (Γ.U \ Γ.V) x := mem_pathComponentIn_self hm
  rcases Γ.size_cases hc with h2 | h3
  · exact hn (hZ' ⟨hxF, Or.inl (Or.inr (mem_iUnion₂.2 ⟨_, ⟨hc, h2⟩, subset_closure hxc⟩))⟩)
  · have hcov := (hl _ hc h3).cover
    have hx' : x ∈ closure (pathComponentIn (Γ.U \ Γ.V) x) := subset_closure hxc
    rw [hcov] at hx'
    rcases hx' with hx' | hx'
    · exact hn (hZ' ⟨hxF, Or.inr (mem_biUnion (show _ ∈ {c ∈ Γ.E | (tilde c).ncard = 3} from ⟨hc,
        h3⟩) hx')⟩)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx'
      exact hn (hD' (⟨⟨_, hc, h3⟩, i⟩ : ι) ⟨hxF, hi⟩)

/-- The narrow painting is internally 3-connected. -/
theorem thin_internally (hS : IsSurface S) (hΓ : Γ.IsInternallyThreeConnected)
    (hl : IsLensed Γ Δ L R) (g : Set S → List S)
    (hg : ∀ e ∈ Γ.E, (tilde e).ncard = 2 → g e = Γ.γ e ∨ g e = (Γ.γ e).reverse) :
    (thinP hl.isCore g hg).IsInternallyThreeConnected := by
  have hΔ := hl.isCore
  refine ⟨?_, ?_⟩
  · change (arcComponentsIn (thinU Γ Δ \ Γ.V)).Nonempty
    rw [pieces_eq hΔ]
    obtain ⟨e, he⟩ := hΓ.1
    rcases Γ.size_cases he with h2 | h3
    · exact ⟨e, Or.inl (Γ.two_mem_sk he h2)⟩
    · exact ⟨_, Or.inr ⟨e, ⟨he, h3⟩, rfl⟩⟩
  · intro F hF hFU hfin hcard
    change F ∩ thinU Γ Δ ⊆ Γ.V at hFU
    change (F ∩ Γ.V).ncard + _ ≤ 2 at hcard
    obtain ⟨h, hfix, hnorm⟩ := exists_push hS hl hF hFU
    have hsymm : ∀ n ∈ Γ.V, h.symm n = n := fun n hn ↦ by
      rw [Homeomorph.symm_apply_eq, hfix n hn]
    have hF' : (h '' F) ∩ Γ.V ⊆ F ∩ Γ.V := by
      rintro _ ⟨⟨y, hy, rfl⟩, hn⟩
      have h₁ := hsymm _ hn
      rw [h.symm_apply_apply] at h₁
      rw [← h₁] at hn ⊢
      exact ⟨hy, hn⟩
    have hbd : (h '' F) ∩ bd S = h '' (F ∩ bd S) := by
      rw [image_inter h.injective, image_bd h]
    have hcard' : ((h '' F) ∩ bd S).ncard = (F ∩ bd S).ncard := by
      rw [hbd, ncard_image_of_injective _ h.injective]
    have hle : ((h '' F) ∩ Γ.V).ncard + ((h '' F) ∩ bd S).ncard ≤ 2 := by
      have := Set.ncard_le_ncard hF' (Γ.finite_V.inter_of_right _)
      rw [hcard']
      omega
    obtain ⟨D, h₁, h₂, h₄⟩ := hΓ.2 _ (GM20.image_isOArc h hF) hnorm
      (by rw [hbd]; exact hfin.image _) hle
    refine ⟨h.symm '' D, GM20.image_isClosedDisc h.symm h₁, ?_, ?_⟩
    · rw [GM20.image_discBd, h₂, ← image_comp]
      simp
    · rintro _ ⟨⟨y, hy, rfl⟩, hn⟩
      have h₅ : h.symm y ∈ Γ.V := hn
      have hyN : y = h (h.symm y) := by simp
      rw [hfix _ h₅] at hyN
      have h₆ : y ∈ Γ.V := by rw [hyN]; exact h₅
      rw [hsymm y h₆]
      exact (hF' ⟨h₄ ⟨hy, h₆⟩, h₆⟩).1

/-- The fifth condition of a frame: the only regions next to a new disc are lenses, and a lens has
two
vertices. -/
theorem thin_region (hS : IsSurface S) (hl : IsLensed Γ Δ L R) (g : Set S → List S)
    (hg : ∀ e ∈ Γ.E, (tilde e).ncard = 2 → g e = Γ.γ e ∨ g e = (Γ.γ e).reverse) :
    ∀ e ∈ (thinP hl.isCore g hg).E, (tilde e).ncard = 3 → ∀ r ∈ (thinP hl.isCore g hg).regions,
      3 ≤ (closure r ∩ (thinP hl.isCore g hg).V).ncard →
      ∀ f ∈ componentsIn (e ∩ closure r), (closure f ∩ bd S).Nonempty := by
  have hΔ := hl.isCore
  obtain ⟨-, -, hman⟩ := id hS
  intro e he h3e r hr hcard f hf
  exfalso
  change e ∈ arcComponentsIn (thinU Γ Δ \ Γ.V) at he
  rw [pieces_eq hΔ] at he
  obtain ⟨y₀, hy₀, rfl⟩ := id hf
  obtain ⟨c, hc, rfl⟩ : ∃ c, (c ∈ Γ.E ∧ (tilde c).ncard = 3) ∧ core Δ c = e := by
    rcases he with he | ⟨c, hc, rfl⟩
    · have := (Γ.sk_size he).1
      omega
    · exact ⟨c, hc, rfl⟩
  obtain ⟨hc, h3⟩ := hc
  obtain ⟨hxc, hxr⟩ := hy₀
  obtain ⟨r₀, hr₀, hrr⟩ := id hr
  have hrU : r ⊆ (thinU Γ Δ)ᶜ := hrr ▸ connectedComponentIn_subset _ _
  have hrc : IsPreconnected r := hrr ▸ isPreconnected_connectedComponentIn
  have hlc := hl c hc h3
  have hΔU : Δ c ⊆ thinU Γ Δ := fun x hx ↦ Or.inr (mem_biUnion (show c ∈ {c ∈ Γ.E | (tilde c).ncard
    = 3}
    from ⟨hc, h3⟩) hx)
  have hbdU : discBd (closure c) ⊆ thinU Γ Δ := fun x hx ↦ Or.inl (Or.inr (mem_biUnion
    (show c ∈ {c ∈ Γ.E | (tilde c).ncard = 3} from ⟨hc, h3⟩) hx))
  have hopen : ∀ {W : Set S}, IsOpen W → y₀ ∈ W → (W ∩ r).Nonempty := fun hW hy ↦
    mem_closure_iff.mp hxr _ hW hy
  by_cases hint : y₀ ∈ discBd (Δ c)
  · obtain ⟨i, hi⟩ := mem_iUnion.mp (hlc.bdΔ hint)
    obtain ⟨a, b, d, ht, -, -, -, hlens⟩ := hlc.lens i
    have hyT : y₀ ∉ tilde c := hxc.2
    have hyR : y₀ ∈ R c i := hlens.L_bd.trans (discBd_subset _) hi
    have hyD : y₀ ∉ discBd (closure c) := fun h ↦ hyT (by
      rw [← hlc.cap]
      exact ⟨hlens.sub_Δ hi, h⟩)
    let W : Set S := discInt (closure c) \ ⋃ j ∈ ({i}ᶜ : Set (Fin 3)), R c j
    have hW : IsOpen W := by
      refine ((Γ.isDisc_of_three hc h3).1.isOpen_discInt hman).sdiff ?_
      refine (Set.toFinite _).isClosed_biUnion fun j _ ↦ ?_
      obtain ⟨_, _, _, -, -, -, -, hlj⟩ := hlc.lens j
      exact hlj.disc.isClosed
    have hyW : y₀ ∈ W := by
      refine ⟨⟨hlens.sub hyR, hyD⟩, fun hm ↦ ?_⟩
      obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hm
      exact hyT (hlc.inter i j (Ne.symm hj) ⟨hyR, hyj⟩)
    obtain ⟨y, hyw, hyr⟩ := hopen hW hyW
    have hyR' : y ∈ R c i := by
      have hyD' : y ∈ closure c := hyw.1.1
      rw [hlc.cover] at hyD'
      rcases hyD' with h | h
      · exact absurd (hΔU h) (hrU hyr)
      · obtain ⟨j, hj⟩ := mem_iUnion.mp h
        by_cases hji : j = i
        · exact hji ▸ hj
        · exact absurd (mem_biUnion (show j ∈ ({i}ᶜ : Set (Fin 3)) from hji) hj) hyw.2
    have hdisj : Disjoint r (discBd (R c i)) := disjoint_left.mpr fun x hxr hxb ↦ by
      rcases hlens.bd hxb with h | h
      · exact hrU hxr (hΔU (hlens.sub_Δ h))
      · exact hrU hxr (hbdU h)
    have hsubR : r ⊆ discInt (R c i) := by
      have hcover : r ⊆ discInt (R c i) ∪ (R c i)ᶜ := fun x hx ↦ by
        by_cases hxR : x ∈ R c i
        · exact Or.inl ⟨hxR, disjoint_left.mp hdisj hx⟩
        · exact Or.inr hxR
      refine hrc.subset_left_of_subset_union (hlens.disc.isOpen_discInt hman)
        hlens.disc.isClosed.isOpen_compl ?_ hcover ?_
      · exact disjoint_left.mpr fun x hx hxn ↦ hxn hx.1
      · exact ⟨y, hyr, hyR', disjoint_left.mp hdisj hyr⟩
    have hclR : closure r ⊆ R c i :=
      closure_minimal (hsubR.trans sdiff_subset) hlens.disc.isClosed
    obtain ⟨u, v, -, hset, -⟩ := hlc.inter_T i
    have hsub : closure r ∩ Γ.V ⊆ {u, v} := fun x hx ↦ by
      rw [← hset]
      refine ⟨hclR hx.1, ?_⟩
      rw [← Γ.closure_inter_V hc]
      exact ⟨hlens.sub (hclR hx.1), hx.2⟩
    have hle := Set.ncard_le_ncard hsub (toFinite _)
    have h2 : ({u, v} : Set S).ncard ≤ 2 := (Set.ncard_insert_le u {v}).trans (by simp)
    change 3 ≤ (closure r ∩ Γ.V).ncard at hcard
    omega
  · obtain ⟨y, hyw, hyr⟩ := hopen (hlc.disc.isOpen_discInt hman) ⟨hxc.1, hint⟩
    exact hrU hyr (hΔU hyw.1)

end

end GraphMinor.GM19
