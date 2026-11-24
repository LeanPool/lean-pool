/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Collar
public import LeanPool.GraphMinor.Surface.PlaneDisc
public import LeanPool.GraphMinor.Surface.DiscGrow
public import LeanPool.GraphMinor.Surface.Gluing
public import Mathlib.Topology.Homotopy.Basic

/-!
# Collapsing closed discs of a closed surface

To compare the capping of a fragment with a closed surface we use a simple fact. Let `D` be a closed
disc in a closed
surface `T`. There is a map of `T` onto itself that sends `D` to one point, is one to one off `D`,
and is homotopic to the
identity (`exists_collapse`). So `T` without `D` looks like `T` without a point.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric GraphMinor.Surface

variable {T : Type*} [TopologicalSpace T]

/-- A one to one continuous image of a closed disc in a Hausdorff space is a closed disc. -/
theorem isClosedDisc_image_injOn {T' : Type*} [TopologicalSpace T'] [T2Space T'] {Δ : Set T}
  (hΔ : IsClosedDisc Δ)
    {f : T → T'} (hf : ContinuousOn f Δ) (hi : InjOn f Δ) :
    IsClosedDisc (f '' Δ) ∧ discBd (f '' Δ) = f '' discBd Δ := by
  classical
  obtain ⟨z, hz⟩ := hΔ.nonempty_discInt
  have : Nonempty T := ⟨z⟩
  have hc : IsCompact Δ := hΔ.isCompact
  refine hΔ.image hf (f' := Function.invFunOn f Δ) ?_ hi.leftInvOn_invFunOn
  have hl := hi.leftInvOn_invFunOn
  refine continuousOn_iff_isClosed.2 fun C hC ↦ ⟨f '' (C ∩ Δ), ?_, ?_⟩
  · exact ((hc.inter_left hC).image_of_continuousOn (hf.mono inter_subset_right)).isClosed
  · ext y
    constructor
    · rintro ⟨hy, x, hx, rfl⟩
      rw [mem_preimage, hl hx] at hy
      exact ⟨⟨x, ⟨hy, hx⟩, rfl⟩, x, hx, rfl⟩
    · rintro ⟨⟨x, ⟨hx, hxd⟩, rfl⟩, -⟩
      exact ⟨by rw [mem_preimage, hl hxd]; exact hx, x, hxd, rfl⟩

/-- `c` collapses `X` to the finite set `P`: it is onto, one to one off `X`, sends `X` into `P` and
nothing else into `P`,
and it is homotopic to the identity. -/
structure IsCollapse (c : C(T, T)) (X P : Set T) : Prop where
  surjective : Function.Surjective c
  mapsTo : MapsTo c X P
  preimage : c ⁻¹' P ⊆ X
  injOn : InjOn c Xᶜ
  finite : P.Finite
  homotopic : c.Homotopic (ContinuousMap.id T)

theorem IsCollapse.comp {c c' : C(T, T)} {X X' P P' : Set T} (h : IsCollapse c X P)
  (h' : IsCollapse c' X' P') :
    IsCollapse (c'.comp c) (X ∪ c ⁻¹' X') (c' '' P ∪ P') := by
  refine ⟨h'.surjective.comp h.surjective, ?_, ?_, ?_, (h.finite.image _).union h'.finite, ?_⟩
  · rintro x (hx | hx)
    · exact Or.inl ⟨_, h.mapsTo hx, rfl⟩
    · exact Or.inr (h'.mapsTo hx)
  · rintro x (⟨p, hp, he⟩ | hx)
    · by_cases hc : c x ∈ X'
      · exact Or.inr hc
      · by_cases hpX : p ∈ X'
        · exact absurd (h'.preimage (by have := h'.mapsTo hpX; rw [he] at this; exact this)) hc
        · have : p = c x := h'.injOn hpX hc he
          exact Or.inl (h.preimage (by rw [mem_preimage, ← this]; exact hp))
    · exact Or.inr (h'.preimage hx)
  · intro x hx y hy he
    simp only [mem_compl_iff, mem_union, not_or, mem_preimage] at hx hy
    exact h.injOn hx.1 hy.1 (h'.injOn hx.2 hy.2 he)
  · simpa using h'.homotopic.comp h.homotopic

/-- The radial map of the disc of radius `2` that sends the unit disc to `0`. -/
noncomputable def squash (z : ℂ) : ℂ := ((2 - 2 / max 1 ‖z‖ : ℝ) : ℂ) * z

theorem continuous_squash : Continuous squash := by
  unfold squash
  have : Continuous fun z : ℂ ↦ (2 - 2 / max 1 ‖z‖ : ℝ) :=
    continuous_const.sub (continuous_const.div (continuous_const.max continuous_norm) fun z ↦ by
      positivity)
  exact (Complex.continuous_ofReal.comp this).mul continuous_id

theorem squash_of_le {z : ℂ} (h : ‖z‖ ≤ 1) : squash z = 0 := by
  simp [squash, max_eq_left h]

theorem squash_of_ge {z : ℂ} (h : 1 ≤ ‖z‖) : squash z = ((2 - 2 / ‖z‖ : ℝ) : ℂ) * z := by
  simp [squash, max_eq_right h]

theorem norm_squash {z : ℂ} (h : 1 ≤ ‖z‖) : ‖squash z‖ = 2 * ‖z‖ - 2 := by
  have h0 : ‖z‖ ≠ 0 := by positivity
  have hnn : 0 ≤ 2 - 2 / ‖z‖ := by
    rw [sub_nonneg, div_le_iff₀ (by positivity)]
    linarith
  rw [squash_of_ge h, norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn]
  field_simp

theorem squash_eq_of_norm {z : ℂ} (h : ‖z‖ = 2) : squash z = z := by
  rw [squash_of_ge (by rw [h]; norm_num), h]
  norm_num

theorem norm_squash_le {z : ℂ} (h : ‖z‖ ≤ 2) : ‖squash z‖ ≤ 2 := by
  rcases le_total ‖z‖ 1 with h1 | h1
  · rw [squash_of_le h1]; simp
  · rw [norm_squash h1]; linarith

theorem squash_inj {z w : ℂ} (hz : 1 < ‖z‖) (hw : 1 < ‖w‖) (h : squash z = squash w) : z = w := by
  have hn : ‖z‖ = ‖w‖ := by
    have := congrArg norm h
    rw [norm_squash hz.le, norm_squash hw.le] at this
    linarith
  rw [squash_of_ge hz.le, squash_of_ge hw.le, hn] at h
  have hne : (2 - 2 / ‖w‖ : ℝ) ≠ 0 := by
    have : 2 / ‖w‖ < 2 := by rw [div_lt_iff₀ (by linarith)]; linarith
    linarith
  exact mul_left_cancel₀ (by exact_mod_cast hne) h

theorem exists_squash_eq {w : ℂ} (h : ‖w‖ ≤ 2) : ∃ z, ‖z‖ ≤ 2 ∧ squash z = w := by
  by_cases h0 : w = 0
  · exact ⟨0, by simp, by rw [squash_of_le (by simp)]; exact h0.symm⟩
  have hp : 0 < ‖w‖ := norm_pos_iff.2 h0
  refine ⟨((1 / 2 + 1 / ‖w‖ : ℝ) : ℂ) * w, ?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have : (1 / 2 + 1 / ‖w‖) * ‖w‖ = ‖w‖ / 2 + 1 := by field_simp
    rw [this]; linarith
  · have hn : ‖((1 / 2 + 1 / ‖w‖ : ℝ) : ℂ) * w‖ = ‖w‖ / 2 + 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      field_simp
    rw [squash_of_ge (by rw [hn]; linarith), hn, ← mul_assoc, ← Complex.ofReal_mul]
    have : (2 - 2 / (‖w‖ / 2 + 1)) * (1 / 2 + 1 / ‖w‖) = 1 := by field_simp; ring
    rw [this]; simp

section Disc

variable [T2Space T]

/-- One closed disc of a closed surface collapses to a point. -/
theorem exists_collapse_disc (hT : IsClosedSurface T) {D : Set T} (hD : IsClosedDisc D) :
    ∃ (c : C(T, T)) (p : T), IsCollapse c D {p} := by
  classical
  have hman : ∀ x : T, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  obtain ⟨D', hD', hin, -⟩ := exists_disc_around hman hD (fun x _ ↦ hT.2.2 x) isOpen_univ
    (subset_univ _)
  obtain ⟨p₀⟩ := IsClosedDisc.isOArc_discBd hD
  obtain ⟨g, g', hgc, hg'c, hgm, hg'm, hl, hr, h1, h2, -⟩ := exists_disc_collar hD hD' hin p₀
  have hcl : IsClosed D' := hD'.isClosed
  have hb : D' ∩ closure D'ᶜ ⊆ discBd D' := by
    rintro x ⟨hx, hxc⟩
    by_contra hn
    have hxi : x ∈ discInt D' := ⟨hx, hn⟩
    obtain ⟨y, hy, hyD⟩ := mem_closure_iff.1 hxc _ (hD'.isOpen_discInt hman) hxi
    exact hyD hy.1
  have hnorm : ∀ {x}, x ∈ D' → ‖g' x‖ ≤ 2 := fun hx ↦ by simpa using hg'm hx
  have hbd2 : ∀ {x}, x ∈ discBd D' → ‖g' x‖ = 2 := fun hx ↦ by
    obtain ⟨w, hw, rfl⟩ := h2 ▸ hx
    have hw' : ‖w‖ = 2 := by simpa using hw
    rw [hl (by simp [hw'])]
    exact hw'
  let A : T × unitInterval → ℂ := fun p ↦ (p.2.1 : ℂ) * g' p.1 + (1 - p.2.1 : ℂ) * squash (g' p.1)
  let H : T × unitInterval → T := fun p ↦ if p.1 ∈ D' then g (A p) else p.1
  have hA : ∀ {x} (t : unitInterval), x ∈ D' → A (x, t) ∈ closedBall (0 : ℂ) 2 := fun {x} t hx ↦ by
    have ht0 : (0 : ℝ) ≤ t := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have h1 := hnorm hx
    have h2 := norm_squash_le h1
    rw [mem_closedBall_zero_iff]
    calc ‖A (x, t)‖ ≤ ‖((t : ℝ) : ℂ) * g' x‖ + ‖(1 - (t : ℝ) : ℂ) * squash (g' x)‖
      := norm_add_le _ _
      _ = t * ‖g' x‖ + (1 - t) * ‖squash (g' x)‖ := by
          rw [norm_mul, norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
            Complex.norm_real,
            Real.norm_of_nonneg ht0, Real.norm_of_nonneg (by linarith)]
      _ ≤ t * 2 + (1 - t) * 2 := by gcongr
      _ = 2 := by ring
  have hAb : ∀ {x} (t : unitInterval), x ∈ discBd D' → g (A (x, t)) = x := fun {x} t hx ↦ by
    have : squash (g' x) = g' x := squash_eq_of_norm (hbd2 hx)
    have hAe : A (x, t) = g' x := by
      simp only [A, this]
      ring
    rw [hAe]
    exact hr (discBd_subset _ hx)
  have hH : Continuous H := by
    have hAc : ContinuousOn A {p | p.1 ∈ D'} := by
      have h₁ : ContinuousOn (fun p : T × unitInterval ↦ g' p.1) {p | p.1 ∈ D'} :=
        hg'c.comp continuous_fst.continuousOn fun p hp ↦ hp
      have ht : Continuous fun p : T × unitInterval ↦ ((p.2.1 : ℝ) : ℂ) := by fun_prop
      exact (ht.continuousOn.mul h₁).add ((continuous_const.sub ht).continuousOn.mul
        (continuous_squash.comp_continuousOn h₁))
    have hon₁ : ContinuousOn H {p | p.1 ∈ D'} := by
      refine (hgc.comp hAc fun p hp ↦ ?_).congr fun p hp ↦ ite_eq_left hp
      exact hA p.2 hp
    have hon₂ : ContinuousOn H {p | p.1 ∈ closure D'ᶜ} := by
      refine continuous_fst.continuousOn.congr fun p hp ↦ ?_
      by_cases h : p.1 ∈ D'
      · have := hAb p.2 (hb ⟨h, hp⟩)
        exact (ite_eq_left h).trans this
      · exact ite_eq_right h
    have hcA : IsClosed {p : T × unitInterval | p.1 ∈ D'} := hcl.preimage continuous_fst
    have hcB : IsClosed {p : T × unitInterval | p.1 ∈ closure D'ᶜ} := isClosed_closure.preimage
      continuous_fst
    have := hon₁.union_of_isClosed hon₂ hcA hcB
    have hu : {p : T × unitInterval | p.1 ∈ D'} ∪ {p | p.1 ∈ closure D'ᶜ} = univ := by
      refine eq_univ_of_forall fun p ↦ ?_
      by_cases h : p.1 ∈ D'
      · exact Or.inl h
      · exact Or.inr (subset_closure (show p.1 ∈ D'ᶜ from h))
    rwa [hu, continuousOn_univ] at this
  let c : C(T, T) := ⟨fun x ↦ H (x, 0), by fun_prop⟩
  have hcin : ∀ {x}, x ∈ D' → c x = g (squash (g' x)) := fun {x} hx ↦ by
    have : A (x, 0) = squash (g' x) := by simp [A]
    change (if x ∈ D' then g (A (x, 0)) else x) = _
    rw [ite_eq_left hx, this]
  have hcout : ∀ {x}, x ∉ D' → c x = x := fun hx ↦ ite_eq_right hx
  have hsub : D ⊆ D' := fun x hx ↦ (hin hx).1
  have hgi : InjOn g (closedBall 0 2) := hl.injOn
  have hD1 : ∀ {x}, x ∈ D' → (x ∈ D ↔ ‖g' x‖ ≤ 1) := fun {x} hx ↦ by
    constructor
    · intro hxD
      obtain ⟨w, hw, rfl⟩ := h1 ▸ hxD
      rw [hl (closedBall_subset_closedBall (by norm_num) hw)]
      simpa using hw
    · intro h
      rw [← hr hx, ← h1]
      exact mem_image_of_mem g (by simpa using h)
  refine ⟨c, g 0, ⟨fun y ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx y hy he ↦ ?_,
    finite_singleton _, ?_⟩⟩
  · by_cases hy : y ∈ D'
    · obtain ⟨z, hz, he⟩ := exists_squash_eq (hnorm hy)
      have hz' : z ∈ closedBall (0 : ℂ) 2 := by simpa using hz
      refine ⟨g z, ?_⟩
      rw [hcin (hgm hz'), hl hz', he]
      exact hr hy
    · exact ⟨y, hcout hy⟩
  · rw [hcin (hsub hx), squash_of_le ((hD1 (hsub hx)).1 hx)]
    rfl
  · have hx' : c x = g 0 := hx
    have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) 2 := by simp
    have hg0 : g 0 ∈ D := h1 ▸ mem_image_of_mem g (by simp)
    by_cases hxD : x ∈ D'
    · rw [hcin hxD] at hx'
      have hs : squash (g' x) = 0 := hgi (by simpa using norm_squash_le (hnorm hxD)) h0 hx'
      by_contra hn
      have hlt : 1 < ‖g' x‖ := not_le.1 fun h ↦ hn ((hD1 hxD).2 h)
      have := norm_squash hlt.le
      rw [hs, norm_zero] at this
      linarith
    · rw [hcout hxD] at hx'
      rw [hx']
      exact hg0
  · have hgt : ∀ {x}, x ∈ D' → x ∉ D → 1 < ‖g' x‖ := fun hx hn ↦ not_le.1 fun h ↦ hn ((hD1 hx).2 h)
    have hin' : ∀ {x}, x ∈ D' → c x ∈ D' := fun {x} hx ↦ by
      rw [hcin hx]
      exact hgm (by simpa using norm_squash_le (hnorm hx))
    by_cases hxD : x ∈ D' <;> by_cases hyD : y ∈ D'
    · rw [hcin hxD, hcin hyD] at he
      have hxm : squash (g' x) ∈ closedBall 0 2 := by
        simpa using norm_squash_le (hnorm hxD)
      have hym : squash (g' y) ∈ closedBall 0 2 := by
        simpa using norm_squash_le (hnorm hyD)
      have hs := hgi hxm hym he
      rw [← hr hxD, ← hr hyD, squash_inj (hgt hxD hx) (hgt hyD hy) hs]
    · exact absurd ((hcout hyD) ▸ he ▸ hin' hxD) hyD
    · exact absurd ((hcout hxD) ▸ he.symm ▸ hin' hyD) hxD
    · rwa [hcout hxD, hcout hyD] at he
  · refine ⟨⟨⟨fun p ↦ H (p.2, p.1), by fun_prop⟩, fun x ↦ rfl, fun x ↦ ?_⟩⟩
    change H (x, 1) = x
    by_cases hx : x ∈ D'
    · have : A (x, 1) = g' x := by simp [A]
      change (if x ∈ D' then g (A (x, 1)) else x) = _
      rw [ite_eq_left hx, this]
      exact hr hx
    · exact ite_eq_right hx

/-- Finitely many pairwise disjoint closed discs of a closed surface collapse, each to its own
point. -/
theorem exists_collapse [Nonempty T] (hT : IsClosedSurface T) {𝓐 : Set (Set T)} (hf : 𝓐.Finite)
  (hd : ∀ E ∈ 𝓐, IsClosedDisc E)
    (hp : 𝓐.PairwiseDisjoint id) :
    ∃ (c : C(T, T)) (P : Set T) (q : Set T → T), IsCollapse c (⋃₀ 𝓐) P ∧ (∀ E ∈ 𝓐, ∀ x ∈ E, c x
      = q E) ∧
      P = q '' 𝓐 ∧ InjOn q 𝓐 := by
  classical
  induction 𝓐, hf using Set.Finite.induction_on with
  | empty =>
    exact ⟨.id T, ∅, fun _ ↦ Classical.arbitrary T, ⟨Function.surjective_id, by simp [MapsTo],
      by simp, by simp [InjOn],
      finite_empty, .refl _⟩, by simp, by simp, by simp⟩
  | @insert D 𝓐 hD hf ih =>
    obtain ⟨c, P, q, hc, hq, rfl, hqi⟩ := ih (fun E hE ↦ hd E (mem_insert_of_mem _ hE))
      (hp.subset (subset_insert _ _))
    have hdis : Disjoint D (⋃₀ 𝓐) := by
      refine disjoint_sUnion_right.2 fun E hE ↦ ?_
      exact hp (mem_insert _ _) (mem_insert_of_mem _ hE) (fun h ↦ hD (h ▸ hE))
    have hDsub : D ⊆ (⋃₀ 𝓐)ᶜ := fun _ hx hn ↦ disjoint_left.1 hdis hx hn
    have hcD : InjOn c D := hc.injOn.mono hDsub
    obtain ⟨hdc, -⟩ := isClosedDisc_image_injOn (hd D (mem_insert _ _)) c.continuous.continuousOn
      hcD
    obtain ⟨c₁, p, h₁⟩ := exists_collapse_disc hT hdc
    have hpre : ⋃₀ 𝓐 ∪ c ⁻¹' (c '' D) = ⋃₀ insert D 𝓐 := by
      rw [sUnion_insert]
      apply Subset.antisymm
      · rintro x (hx | ⟨d, hd, he⟩)
        · exact Or.inr hx
        · by_cases hxA : x ∈ ⋃₀ 𝓐
          · exact Or.inr hxA
          · exact Or.inl (hc.injOn (fun h ↦ disjoint_left.1 hdis hd h) hxA he ▸ hd)
      · rintro x (hx | hx)
        · exact Or.inr ⟨x, hx, rfl⟩
        · exact Or.inl hx
    have hcomp := hc.comp h₁
    rw [hpre] at hcomp
    have hPd : Disjoint (q '' 𝓐) (c '' D) := by
      refine disjoint_left.2 ?_
      rintro _ ⟨E, hE, rfl⟩ ⟨d, hdD, he⟩
      exact disjoint_left.1 hdis hdD (hc.preimage ⟨E, hE, he.symm⟩)
    have hmem : ∀ x ∈ c '' D, c₁ x = p := fun x hx ↦ h₁.mapsTo hx
    have hout : ∀ E ∈ 𝓐, c₁ (q E) ≠ p := fun E hE h ↦ disjoint_left.1 hPd ⟨E, hE, rfl⟩
      (h₁.preimage h)
    refine ⟨c₁.comp c, _, fun E ↦ if E = D then p else c₁ (q E), hcomp, ?_, ?_, ?_⟩
    · rintro E (rfl | hE) x hx
      · simpa using hmem _ (mem_image_of_mem c hx)
      · have hne : E ≠ D := fun h ↦ hD (h ▸ hE)
        simp only [ContinuousMap.comp_apply, ite_eq_right hne, hq E hE x hx]
    · rw [image_insert_eq, union_comm, image_image, singleton_union]
      simp only [ite_true]
      congr 1
      exact image_congr fun E hE ↦ (ite_eq_right fun h : E = D ↦ hD (h ▸ hE)).symm
    · rintro E (rfl | hE) F (rfl | hF) he
      · rfl
      · have hne : F ≠ E := fun h ↦ hD (h ▸ hF)
        simp only [ite_true, ite_eq_right hne] at he
        exact absurd he.symm (hout F hF)
      · have hne : E ≠ F := fun h ↦ hD (h ▸ hE)
        simp only [ite_true, ite_eq_right hne] at he
        exact absurd he (hout E hE)
      · have hne : E ≠ D := fun h ↦ hD (h ▸ hE)
        have hne' : F ≠ D := fun h ↦ hD (h ▸ hF)
        simp only [ite_eq_right hne, ite_eq_right hne'] at he
        have hPout : ∀ G ∈ 𝓐, q G ∉ c '' D := fun G hG h ↦ disjoint_left.1 hPd ⟨G, hG, rfl⟩ h
        exact hqi hE hF (h₁.injOn (hPout E hE) (hPout F hF) he)

end Disc

end GraphMinor.GM19
