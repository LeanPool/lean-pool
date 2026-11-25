/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscUnion
public import LeanPool.GraphMinor.Surface.PlaneDisc
public import LeanPool.GraphMinor.Surface.TriPath
public import LeanPool.GraphMinor.Surface.DiscFan
public import LeanPool.GraphMinor.Surface.ChartCells
public import LeanPool.GraphMinor.Surface.ArcTools
public import LeanPool.GraphMinor.Surface.SurfaceGraph
public import LeanPool.GraphMinor.GM11.Fan

/-!
# The two sides of an arc in a closed disc

Let `Q` be an arc in a closed disc `Δ` with ends on `bd(Δ)`. Unlike a cross-cut, `Q` may meet
`bd(Δ)` at other points, and it may even run along `bd(Δ)`. This happens in Graph Minors IX, (10.2),
since a path of a weakly-linked set may pass through vertices of `ΩBar`.

The ends cut `bd(Δ)` into two open arcs `I₁, I₂`. We show that `Δ - Q` falls into two parts `Y₁, Y₂`
with no connected set meeting both, with `I₁ - Q ⊆ Y₁` and `I₂ - Q ⊆ Y₂` (`IsArcSides`). To prove
this we place `Δ` in the plane as the disc of radius `1/2`, and extend `Q` by two radial segments to
the circle of radius `1`. Then `Q` becomes a true cross-cut of the unit disc.

`exists_hole_sides` is the case that we need in (10.2). A closed disc `D ⊆ Δ` has boundary `A ∪ A'`,
and two arcs `R ∪ A` and `R ∪ A'` have the same ends on `bd(Δ)`. Exactly one of `A, A'` has `D` on
the side of `I₂`.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Metric GraphMinor GraphMinor.Surface

universe u

/-- The radial segment from `p` to `2 p`. -/
def outerSeg (p : ℂ) : Set ℂ := {z | ∃ t ∈ Icc (1 : ℝ) 2, z = (t : ℂ) * p}

theorem isLineWithEnds_outerSeg {p : ℂ} (hp : p ≠ 0) : IsLineWithEnds (outerSeg p) p (2 * p) := by
  let f : C(unitInterval, ℂ) := ⟨fun t => ((1 + (t : ℝ) : ℝ) : ℂ) * p, by fun_prop⟩
  have hinj : Injective f := by
    intro s t hst
    have h : ((1 + (s : ℝ) : ℝ) : ℂ) * p = ((1 + (t : ℝ) : ℝ) : ℂ) * p := hst
    have h' := mul_right_cancel₀ hp h
    have h'' : (1 + (s : ℝ) : ℝ) = 1 + (t : ℝ) := by exact_mod_cast h'
    exact Subtype.ext (by linarith)
  have hl := GraphMinor.GM11.isLineWithEnds_range f hinj
  have hr : range f = outerSeg p := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨1 + (t : ℝ), ⟨by linarith [t.2.1], by linarith [t.2.2]⟩, rfl⟩
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨t - 1, by linarith, by linarith⟩, ?_⟩
      change ((1 + (t - 1) : ℝ) : ℂ) * p = _
      congr 2
      ring
  rw [hr] at hl
  have h0 : f 0 = p := by
    change ((1 + ((0 : unitInterval) : ℝ) : ℝ) : ℂ) * p = p
    simp
  have h1 : f 1 = 2 * p := by
    change ((1 + ((1 : unitInterval) : ℝ) : ℝ) : ℂ) * p = 2 * p
    norm_num
  rwa [h0, h1] at hl

theorem norm_of_mem_outerSeg {p z : ℂ} (hp : ‖p‖ = 1 / 2) (hz : z ∈ outerSeg p) :
    1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1 := by
  obtain ⟨t, ⟨h1, h2⟩, rfl⟩ := hz
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), hp]
  constructor <;> linarith

theorem eq_of_mem_outerSeg_of_norm_le {p z : ℂ} (hp : ‖p‖ = 1 / 2) (hz : z ∈ outerSeg p)
    (hn : ‖z‖ ≤ 1 / 2) : z = p := by
  obtain ⟨t, ⟨h1, h2⟩, rfl⟩ := hz
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), hp] at hn
  have : t = 1 := by linarith
  simp [this]

theorem eq_of_mem_outerSeg_of_norm_eq {p z : ℂ} (hp : ‖p‖ = 1 / 2) (hz : z ∈ outerSeg p)
    (hn : ‖z‖ = 1) : z = 2 * p := by
  obtain ⟨t, ⟨h1, h2⟩, rfl⟩ := hz
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), hp] at hn
  have : t = 2 := by linarith
  simp [this]

theorem disjoint_outerSeg {p q : ℂ} (hp : ‖p‖ = 1 / 2) (hq : ‖q‖ = 1 / 2) (hpq : p ≠ q) :
    Disjoint (outerSeg p) (outerSeg q) := by
  rw [Set.disjoint_left]
  rintro z ⟨t, ⟨h1, h2⟩, rfl⟩ ⟨s, ⟨h3, h4⟩, hs⟩
  have hn := congrArg norm hs
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), hp, hq] at hn
  have hts : t = s := by linarith
  subst hts
  have ht0 : (t : ℂ) ≠ 0 := by
    have : t ≠ 0 := by linarith
    exact_mod_cast this
  exact hpq (mul_left_cancel₀ ht0 hs)

/-- `Q` extended by the radial segments at its ends. -/
def extArc (p q : ℂ) (Q : Set ℂ) : Set ℂ := outerSeg p ∪ Q ∪ outerSeg q

theorem isLineWithEnds_extArc {p q : ℂ} {Q : Set ℂ} (hQ : IsLineWithEnds Q p q)
    (hQb : Q ⊆ closedBall 0 (1 / 2)) (hp : ‖p‖ = 1 / 2) (hq : ‖q‖ = 1 / 2) (hpq : p ≠ q) :
    IsLineWithEnds (extArc p q Q) (2 * p) (2 * q) := by
  have np : p ≠ 0 := by
    intro h
    rw [h, norm_zero] at hp
    norm_num at hp
  have nq : q ≠ 0 := by
    intro h
    rw [h, norm_zero] at hq
    norm_num at hq
  have h1 : outerSeg p ∩ Q = {p} := by
    ext z
    constructor
    · rintro ⟨hz, hzQ⟩
      exact eq_of_mem_outerSeg_of_norm_le hp hz (by simpa using hQb hzQ)
    · rintro rfl
      exact ⟨(isLineWithEnds_outerSeg np).left_mem, hQ.left_mem⟩
  have h2 : (outerSeg p ∪ Q) ∩ outerSeg q = {q} := by
    ext z
    constructor
    · rintro ⟨hz | hz, hzq⟩
      · exact (Set.disjoint_left.mp (disjoint_outerSeg hp hq hpq) hz hzq).elim
      · exact eq_of_mem_outerSeg_of_norm_le hq hzq (by simpa using hQb hz)
    · rintro rfl
      exact ⟨Or.inr hQ.right_mem, (isLineWithEnds_outerSeg nq).left_mem⟩
  exact (((isLineWithEnds_outerSeg np).symm.union hQ h1).union (isLineWithEnds_outerSeg nq) h2)

theorem extArc_inter_sphere {p q : ℂ} {Q : Set ℂ} (hQ : IsLineWithEnds Q p q)
    (hQb : Q ⊆ closedBall 0 (1 / 2)) (hp : ‖p‖ = 1 / 2) (hq : ‖q‖ = 1 / 2) (hpq : p ≠ q) :
    extArc p q Q ∩ sphere 0 1 = {2 * p, 2 * q} := by
  have hl := isLineWithEnds_extArc hQ hQb hp hq hpq
  ext z
  simp only [mem_inter_iff, mem_sphere_zero_iff_norm, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨(hz | hz) | hz, hn⟩
    · exact Or.inl (eq_of_mem_outerSeg_of_norm_eq hp hz hn)
    · have := hQb hz
      simp only [mem_closedBall_zero_iff] at this
      norm_num [hn] at this
    · exact Or.inr (eq_of_mem_outerSeg_of_norm_eq hq hz hn)
  · rintro (rfl | rfl)
    · refine ⟨hl.left_mem, ?_⟩
      rw [norm_mul, hp]
      norm_num
    · refine ⟨hl.right_mem, ?_⟩
      rw [norm_mul, hq]
      norm_num

theorem extArc_subset_closedBall {p q : ℂ} {Q : Set ℂ} (hQb : Q ⊆ closedBall 0 (1 / 2))
    (hp : ‖p‖ = 1 / 2) (hq : ‖q‖ = 1 / 2) : extArc p q Q ⊆ closedBall 0 1 := by
  rintro z ((hz | hz) | hz)
  · exact mem_closedBall_zero_iff.mpr (norm_of_mem_outerSeg hp hz).2
  · have := hQb hz
    simp only [mem_closedBall_zero_iff] at this ⊢
    linarith
  · exact mem_closedBall_zero_iff.mpr (norm_of_mem_outerSeg hq hz).2

/-- The discs into which the extended arc cuts the unit disc. `T₁, T₂` are the two open arcs of the
unit circle. -/
structure IsExtSplit (F T₁ T₂ E₁ E₂ : Set ℂ) : Prop where
  disc₁ : IsClosedDisc E₁
  disc₂ : IsClosedDisc E₂
  cover : E₁ ∪ E₂ = closedBall 0 1
  inter : E₁ ∩ E₂ = F
  bd₁ : discBd E₁ = T₁ ∪ F
  bd₂ : discBd E₂ = T₂ ∪ F
  conn : ∀ Z : Set ℂ, Z ⊆ closedBall 0 1 \ F → IsPreconnected Z → Z ⊆ E₁ ∨ Z ⊆ E₂

theorem IsExtSplit.symm {F T₁ T₂ E₁ E₂ : Set ℂ} (h : IsExtSplit F T₁ T₂ E₁ E₂) :
    IsExtSplit F T₂ T₁ E₂ E₁ where
  disc₁ := h.disc₂
  disc₂ := h.disc₁
  cover := by rw [Set.union_comm]; exact h.cover
  inter := by rw [Set.inter_comm]; exact h.inter
  bd₁ := h.bd₂
  bd₂ := h.bd₁
  conn := fun Z hZ hp => (h.conn Z hZ hp).symm

theorem exists_isExtSplit {F : Set ℂ} {s t : ℂ} (hF : IsLineWithEnds F s t)
    (hFb : F ⊆ closedBall 0 1) (hcap : F ∩ sphere 0 1 = {s, t}) (hst : s ≠ t) {T₁ T₂ : Set ℂ}
    (hT₁ : IsPreconnected T₁) (hT₂ : IsPreconnected T₂) (hd : Disjoint T₁ T₂)
    (hu : T₁ ∪ T₂ = sphere 0 1 \ {s, t}) :
    ∃ E₁ E₂, IsExtSplit F T₁ T₂ E₁ E₂ := by
  obtain ⟨hdisc, hbd⟩ := isClosedDisc_closedBall
  obtain ⟨A₁, A₂, Δ₁, Δ₂, hne, hcomp, h₁, h₂, hU, hI, hb₁, hb₂, hcomp'⟩ :=
    disc_iArc (closedBall 0 1) F s t hdisc hFb hst hF (by rw [hbd]; exact hcap)
  rw [hbd] at hcomp
  set X := sphere (0 : ℂ) 1 \ {s, t} with hX
  have hmem : ∀ C ∈ componentsIn X, C ⊆ X ∧ C.Nonempty ∧ ∀ Z : Set ℂ, Z ⊆ X → IsPreconnected Z →
      (Z ∩ C).Nonempty → Z ⊆ C := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨connectedComponentIn_subset _ _, ⟨x, mem_connectedComponentIn hx⟩, ?_⟩
    rintro Z hZ hc ⟨z, hzZ, hzC⟩
    rw [connectedComponentIn_eq hzC]
    exact hc.subset_connectedComponentIn hzZ hZ
  have m₁ : A₁ ∈ componentsIn X := by rw [hcomp]; exact Or.inl rfl
  have m₂ : A₂ ∈ componentsIn X := by rw [hcomp]; exact Or.inr rfl
  have dA : Disjoint A₁ A₂ := by
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    apply hne
    obtain ⟨u, hu', rfl⟩ := m₁
    obtain ⟨v, hv', rfl⟩ := m₂
    rw [connectedComponentIn_eq hx₁, connectedComponentIn_eq hx₂]
  have cA : A₁ ∪ A₂ = X := by
    apply Subset.antisymm (union_subset (hmem _ m₁).1 (hmem _ m₂).1)
    intro x hx
    have : connectedComponentIn X x ∈ ({A₁, A₂} : Set (Set ℂ)) := hcomp ▸ ⟨x, hx, rfl⟩
    rcases this with h | h
    · exact Or.inl (h ▸ mem_connectedComponentIn hx)
    · exact Or.inr (h ▸ mem_connectedComponentIn hx)
  have hTX₁ : T₁ ⊆ X := hu ▸ subset_union_left
  have hTX₂ : T₂ ⊆ X := hu ▸ subset_union_right
  have side : ∀ T : Set ℂ, T ⊆ X → IsPreconnected T → T ⊆ A₁ ∨ T ⊆ A₂ := by
    intro T hTX hT
    by_cases hne₁ : (T ∩ A₁).Nonempty
    · exact Or.inl ((hmem _ m₁).2.2 T hTX hT hne₁)
    · refine Or.inr fun x hx => ?_
      rcases (cA ▸ hTX hx : x ∈ A₁ ∪ A₂) with h | h
      · exact (hne₁ ⟨x, hx, h⟩).elim
      · exact h
  have hcomp2 : ∀ Z : Set ℂ, Z ⊆ closedBall 0 1 \ F → IsPreconnected Z → Z ⊆ Δ₁ ∨ Z ⊆ Δ₂ := by
    intro Z hZ hZc
    rcases Z.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
    · exact Or.inl (empty_subset _)
    have hz' : connectedComponentIn (closedBall 0 1 \ F) z ∈
        ({Δ₁ \ F, Δ₂ \ F} : Set (Set ℂ)) := hcomp' ▸ ⟨z, hZ hz, rfl⟩
    have hsub : Z ⊆ connectedComponentIn (closedBall 0 1 \ F) z :=
      hZc.subset_connectedComponentIn hz hZ
    rcases hz' with h | h
    · exact Or.inl fun x hx => (h ▸ hsub hx : x ∈ Δ₁ \ F).1
    · exact Or.inr fun x hx => (h ▸ hsub hx : x ∈ Δ₂ \ F).1
  have dT : ∀ x, x ∈ T₁ → x ∈ T₂ → False := fun x h h' => Set.disjoint_left.mp hd h h'
  rcases side T₁ hTX₁ hT₁ with h₁₁ | h₁₂
  · rcases side T₂ hTX₂ hT₂ with h₂₁ | h₂₂
    · obtain ⟨x, hx⟩ := (hmem _ m₂).2.1
      have hxX := (hmem _ m₂).1 hx
      rcases (hu ▸ hxX : x ∈ T₁ ∪ T₂) with h | h
      · exact (Set.disjoint_left.mp dA (h₁₁ h) hx).elim
      · exact (Set.disjoint_left.mp dA (h₂₁ h) hx).elim
    · have e₁ : A₁ = T₁ := Subset.antisymm (fun x hx => by
        rcases (hu ▸ (hmem _ m₁).1 hx : x ∈ T₁ ∪ T₂) with h | h
        · exact h
        · exact (Set.disjoint_left.mp dA hx (h₂₂ h)).elim) h₁₁
      have e₂ : A₂ = T₂ := Subset.antisymm (fun x hx => by
        rcases (hu ▸ (hmem _ m₂).1 hx : x ∈ T₁ ∪ T₂) with h | h
        · exact (Set.disjoint_left.mp dA (h₁₁ h) hx).elim
        · exact h) h₂₂
      exact ⟨Δ₁, Δ₂, h₁, h₂, hU, hI, e₁ ▸ hb₁, e₂ ▸ hb₂, hcomp2⟩
  · rcases side T₂ hTX₂ hT₂ with h₂₁ | h₂₂
    · have e₂ : A₂ = T₁ := Subset.antisymm (fun x hx => by
        rcases (hu ▸ (hmem _ m₂).1 hx : x ∈ T₁ ∪ T₂) with h | h
        · exact h
        · exact (Set.disjoint_left.mp dA (h₂₁ h) hx).elim) h₁₂
      have e₁ : A₁ = T₂ := Subset.antisymm (fun x hx => by
        rcases (hu ▸ (hmem _ m₁).1 hx : x ∈ T₁ ∪ T₂) with h | h
        · exact (Set.disjoint_left.mp dA hx (h₁₂ h)).elim
        · exact h) h₂₁
      refine ⟨Δ₂, Δ₁, h₂, h₁, by rw [Set.union_comm]; exact hU, by rw [Set.inter_comm]; exact hI,
        e₂ ▸ hb₂, e₁ ▸ hb₁, fun Z hZ hc => (hcomp2 Z hZ hc).symm⟩
    · obtain ⟨x, hx⟩ := (hmem _ m₁).2.1
      have hxX := (hmem _ m₁).1 hx
      rcases (hu ▸ hxX : x ∈ T₁ ∪ T₂) with h | h
      · exact (Set.disjoint_left.mp dA hx (h₁₂ h)).elim
      · exact (Set.disjoint_left.mp dA hx (h₂₂ h)).elim

theorem IsExtSplit.mem_side {F T₁ T₂ E₁ E₂ Q : Set ℂ} {p q c : ℂ}
    (h : IsExtSplit F T₁ T₂ E₁ E₂) (hF : F = extArc p q Q) (hQb : Q ⊆ closedBall 0 (1 / 2))
    (hp : ‖p‖ = 1 / 2) (hq : ‖q‖ = 1 / 2) (hc : ‖c‖ = 1 / 2) (hcp : c ≠ p) (hcq : c ≠ q)
    (hcQ : c ∉ Q) (hcT : 2 * c ∈ T₁) (hT : Disjoint T₁ F) : c ∈ E₁ := by
  have nc : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc
    norm_num at hc
  have hl := isLineWithEnds_outerSeg nc
  have hZ : outerSeg c ⊆ closedBall 0 1 \ F := by
    intro z hz
    refine ⟨mem_closedBall_zero_iff.mpr (norm_of_mem_outerSeg hc hz).2, ?_⟩
    rw [hF]
    rintro ((h' | h') | h')
    · exact Set.disjoint_left.mp (disjoint_outerSeg hc hp hcp) hz h'
    · have hn : ‖z‖ ≤ 1 / 2 := by simpa using hQb h'
      exact hcQ (eq_of_mem_outerSeg_of_norm_le hc hz hn ▸ h')
    · exact Set.disjoint_left.mp (disjoint_outerSeg hc hq hcq) hz h'
  have hE₁ : 2 * c ∈ E₁ := by
    have : 2 * c ∈ discBd E₁ := h.bd₁ ▸ Or.inl hcT
    exact discBd_subset _ this
  rcases h.conn _ hZ hl.isPreconnected_self with h' | h'
  · exact h' hl.left_mem
  · exfalso
    have : 2 * c ∈ E₁ ∩ E₂ := ⟨hE₁, h' hl.right_mem⟩
    rw [h.inter] at this
    exact Set.disjoint_left.mp hT hcT this

/-- If `D` lies on the side `E°` of `R ∪ A` and on the side `E°'` of `R ∪ A'`, then the other two
sides share `T` and differ by `D`, which is impossible. -/
theorem false_of_hole_on_same_side {D A A' Rp T E Eo E' Eo' : Set ℂ} {y y' : ℂ}
    (hD : IsClosedDisc D) (hA : IsLineWithEnds A y y') (hbd : discBd D = A ∪ A')
    (hAA' : A ∩ A' = {y, y'}) (hRD : Rp ∩ D = {y, y'})
    (hTD : Disjoint T D)
    (hE : IsClosedDisc E) (hE' : IsClosedDisc E')
    (hI : E ∩ Eo = Rp ∪ A) (hI' : E' ∩ Eo' = Rp ∪ A')
    (hb : discBd E = T ∪ (Rp ∪ A)) (hb' : discBd E' = T ∪ (Rp ∪ A'))
    (hs : D \ A ⊆ Eo) (hs' : D \ A' ⊆ Eo') : False := by
  have hyA : y ∈ A := hA.left_mem
  have hyA' : y ∈ A' := (hAA'.symm ▸ (Or.inl rfl : y ∈ ({y, y'} : Set ℂ)) : y ∈ A ∩ A').2
  have hzA' : y' ∈ A' := (hAA'.symm ▸ (Or.inr rfl : y' ∈ ({y, y'} : Set ℂ)) : y' ∈ A ∩ A').2
  have hzA : y' ∈ A := hA.right_mem
  have hAD : A ⊆ D := fun x hx => discBd_subset D (hbd ▸ Or.inl hx)
  have hA'D : A' ⊆ D := fun x hx => discBd_subset D (hbd ▸ Or.inr hx)
  have hRA : ∀ x, x ∈ Rp → x ∈ D → x ∈ A ∧ x ∈ A' := by
    intro x h h'
    have : x ∈ Rp ∩ D := ⟨h, h'⟩
    rw [hRD] at this
    rcases this with rfl | rfl
    · exact ⟨hyA, hyA'⟩
    · exact ⟨hzA, hzA'⟩
  have hED : E ∩ D = A := by
    apply Subset.antisymm
    · rintro x ⟨hxE, hxD⟩
      by_contra hxA
      have : x ∈ E ∩ Eo := ⟨hxE, hs ⟨hxD, hxA⟩⟩
      rw [hI] at this
      rcases this with h | h
      · exact hxA (hRA x h hxD).1
      · exact hxA h
    · intro x hx
      have : x ∈ E ∩ Eo := hI.symm ▸ Or.inr hx
      exact ⟨this.1, hAD hx⟩
  have hAE : A ⊆ discBd E := fun x hx => hb ▸ Or.inr (Or.inr hx)
  have hAbd : A ⊆ discBd D := fun x hx => hbd ▸ Or.inl hx
  obtain ⟨hU, hbU⟩ := disc_union E D A y y' hE hD hA hED hAE hAbd
  have hbU' : discBd (E ∪ D) = T ∪ (Rp ∪ A') := by
    rw [hbU, hb, hbd]
    ext x
    simp only [mem_sdiff, mem_union, mem_insert_iff, mem_singleton_iff, not_and, not_not]
    constructor
    · rintro ⟨h, h'⟩
      by_cases hxA : x ∈ A
      · have := h' hxA
        rcases this with rfl | rfl
        · exact Or.inr (Or.inr hyA')
        · exact Or.inr (Or.inr hzA')
      · tauto
    · intro h
      refine ⟨by tauto, fun hxA => ?_⟩
      rcases h with h | h | h
      · exact (Set.disjoint_left.mp hTD h (hAD hxA)).elim
      · have : x ∈ Rp ∩ D := ⟨h, hAD hxA⟩
        rw [hRD] at this
        exact this
      · have : x ∈ A ∩ A' := ⟨hxA, h⟩
        rw [hAA'] at this
        exact this
  have hG : IsOArc (T ∪ (Rp ∪ A')) := hb' ▸ hE'.isOArc_discBd
  have heq : E ∪ D = E' :=
    (eq_closedInner_of_discBd hG hU hbU').trans (eq_closedInner_of_discBd hG hE' hb').symm
  have hsub : D ⊆ A' := by
    intro x hxD
    by_contra hxA
    have : x ∈ E' ∩ Eo' := ⟨heq ▸ Or.inr hxD, hs' ⟨hxD, hxA⟩⟩
    rw [hI'] at this
    rcases this with h | h
    · exact hxA (hRA x h hxD).2
    · exact hxA h
  obtain ⟨x, hx₁, hx₂⟩ : (A \ {y, y'}).Nonempty := hA.nonempty_sdiff
  exact hx₂ (hAA' ▸ ⟨hx₁, hsub (hAD hx₁)⟩)

theorem isPreconnected_disc_sdiff {D A : Set ℂ} (hD : IsClosedDisc D) (hA : A ⊆ discBd D) :
    IsPreconnected (D \ A) := by
  refine hD.isPreconnected_discInt.subset_closure ?_ ?_
  · rintro x ⟨hx, hxb⟩
    exact ⟨hx, fun h => hxb (hA h)⟩
  · exact sdiff_subset.trans hD.subset_closure_discInt

/-- The two sides of an arc `Q` in a closed disc `Δ`, where `I₁, I₂` are the open arcs of `bd(Δ)`
between the ends of `Q`. No connected set of `Δ - Q` meets both sides. -/
structure IsArcSides {S : Type u} [TopologicalSpace S] (Δ Q I₁ I₂ Y₁ Y₂ : Set S) : Prop where
  cover : Y₁ ∪ Y₂ = Δ \ Q
  disj : Disjoint Y₁ Y₂
  conn : ∀ Z : Set S, Z ⊆ Δ \ Q → IsPreconnected Z → Z ⊆ Y₁ ∨ Z ⊆ Y₂
  left : I₁ \ Q ⊆ Y₁
  right : I₂ \ Q ⊆ Y₂

theorem IsLineWithEnds.image_of_injOn {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [T2Space T] {L : Set S} {u v : S} (hL : IsLineWithEnds L u v) {f : S → T}
    (hc : ContinuousOn f L) (hi : InjOn f L) : IsLineWithEnds (f '' L) (f u) (f v) := by
  obtain ⟨a, ha, hr, h0, h1⟩ := hL.exists_arc
  have hm : ∀ t, a t ∈ L := fun t => hr ▸ mem_range_self t
  let b : C(unitInterval, T) :=
    ⟨fun t => f (a t), hc.comp_continuous ha.1 hm⟩
  have hb : Injective b := fun s t h => ha.2 (hi (hm s) (hm t) h)
  have hl := GraphMinor.GM11.isLineWithEnds_range b hb
  have hr' : range b = f '' L := by
    rw [← hr, ← range_comp]
    rfl
  rw [hr'] at hl
  have e0 : b 0 = f u := by
    change f (a 0) = f u
    rw [h0]
  have e1 : b 1 = f v := by
    change f (a 1) = f v
    rw [h1]
  rwa [e0, e1] at hl

/-- Sides of an arc read off from the sides of its image in the plane. -/
theorem IsExtSplit.arcSides {S : Type u} [TopologicalSpace S] {Δ Q I₁ I₂ : Set S} {w : S → ℂ}
    (hwc : ContinuousOn w Δ) (hwi : InjOn w Δ) (hwn : ∀ x ∈ Δ, ‖w x‖ ≤ 1 / 2)
    (hQΔ : Q ⊆ Δ) (hIΔ₁ : I₁ ⊆ Δ) (hIΔ₂ : I₂ ⊆ Δ)
    {p q : ℂ} {F T₁ T₂ E₁ E₂ : Set ℂ} (h : IsExtSplit F T₁ T₂ E₁ E₂)
    (hF : F = extArc p q (w '' Q)) (hp : p ∈ w '' Q) (hq : q ∈ w '' Q)
    (hp1 : ‖p‖ = 1 / 2) (hq1 : ‖q‖ = 1 / 2)
    (hl : ∀ x ∈ I₁ \ Q, w x ∈ E₁) (hr : ∀ x ∈ I₂ \ Q, w x ∈ E₂) :
    IsArcSides Δ Q I₁ I₂ {x ∈ Δ \ Q | w x ∈ E₁} {x ∈ Δ \ Q | w x ∈ E₂} := by
  have hnF : ∀ x ∈ Δ \ Q, w x ∈ closedBall (0 : ℂ) 1 \ F := by
    rintro x ⟨hx, hxQ⟩
    have hn := hwn x hx
    refine ⟨mem_closedBall_zero_iff.mpr (by linarith), ?_⟩
    have hnQ : w x ∉ w '' Q := by
      rintro ⟨y, hy, he⟩
      exact hxQ (hwi (hQΔ hy) hx he ▸ hy)
    rw [hF]
    rintro ((h' | h') | h')
    · exact hnQ (eq_of_mem_outerSeg_of_norm_le hp1 h' hn ▸ hp)
    · exact hnQ h'
    · exact hnQ (eq_of_mem_outerSeg_of_norm_le hq1 h' hn ▸ hq)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro _ (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro x hx
      have := (hnF x hx).1
      rw [← h.cover] at this
      rcases this with h' | h'
      · exact Or.inl ⟨hx, h'⟩
      · exact Or.inr ⟨hx, h'⟩
  · rw [Set.disjoint_left]
    rintro x ⟨hx, h₁⟩ ⟨-, h₂⟩
    have : w x ∈ E₁ ∩ E₂ := ⟨h₁, h₂⟩
    rw [h.inter] at this
    exact (hnF x hx).2 this
  · intro Z hZ hc
    have hZ' : w '' Z ⊆ closedBall 0 1 \ F := by
      rintro _ ⟨x, hx, rfl⟩
      exact hnF x (hZ hx)
    rcases h.conn _ hZ' (hc.image _ (hwc.mono fun x hx => (hZ hx).1)) with h' | h'
    · exact Or.inl fun x hx => ⟨hZ hx, h' (mem_image_of_mem w hx)⟩
    · exact Or.inr fun x hx => ⟨hZ hx, h' (mem_image_of_mem w hx)⟩
  · intro x hx
    exact ⟨⟨hIΔ₁ hx.1, hx.2⟩, hl x hx⟩
  · intro x hx
    exact ⟨⟨hIΔ₂ hx.1, hx.2⟩, hr x hx⟩

private theorem hole_sides_of_ext_splits {S : Type u} [TopologicalSpace S]
    {Δ D R A A' I₁ I₂ : Set S} {a b y y' : S} {w : S → ℂ} {w' : ℂ → S}
    (hD : IsClosedDisc D) (hDΔ : D ⊆ Δ)
    (hA : IsLineWithEnds A y y') (hbd : discBd D = A ∪ A') (hAA' : A ∩ A' = {y, y'})
    (hRD : R ∩ D = {y, y'}) (hRΔ : R ⊆ Δ) (haR : a ∈ R) (hbR : b ∈ R)
    (hwc : ContinuousOn w Δ) (hw'c : ContinuousOn w' (w '' Δ)) (hL : LeftInvOn w' w Δ)
    (hwn : ∀ x ∈ Δ, ‖w x‖ ≤ 1 / 2) (hp : ‖w a‖ = 1 / 2) (hq : ‖w b‖ = 1 / 2)
    {T₁ T₂ E₁ E₂ E₁' E₂' : Set ℂ} (hTu : T₁ ∪ T₂ = sphere 0 1 \ {2 * w a, 2 * w b})
    (hE : IsExtSplit (extArc (w a) (w b) (w '' (R ∪ A))) T₁ T₂ E₁ E₂)
    (hE' : IsExtSplit (extArc (w a) (w b) (w '' (R ∪ A'))) T₁ T₂ E₁' E₂')
    (hext : ∀ X : Set S, X ⊆ Δ → extArc (w a) (w b) (w '' (R ∪ X)) =
      (outerSeg (w a) ∪ w '' R ∪ outerSeg (w b)) ∪ w '' X)
    (sd₁ : IsArcSides Δ (R ∪ A) I₁ I₂
      {x ∈ Δ \ (R ∪ A) | w x ∈ E₁} {x ∈ Δ \ (R ∪ A) | w x ∈ E₂})
    (sd₂ : IsArcSides Δ (R ∪ A') I₁ I₂
      {x ∈ Δ \ (R ∪ A') | w x ∈ E₁'} {x ∈ Δ \ (R ∪ A') | w x ∈ E₂'}) :
    ∃ Y₁ Y₂ Y₁' Y₂', IsArcSides Δ (R ∪ A) I₁ I₂ Y₁ Y₂ ∧ IsArcSides Δ (R ∪ A') I₁ I₂ Y₁' Y₂' ∧
      ((D \ A ⊆ Y₂ ∧ D \ A' ⊆ Y₁') ∨ (D \ A ⊆ Y₁ ∧ D \ A' ⊆ Y₂')) := by
  let p := w a
  let q := w b
  have hwi := hL.injOn
  have hAD : A ⊆ D := fun _ hx => discBd_subset D (hbd ▸ Or.inl hx)
  have hA'D : A' ⊆ D := fun _ hx => discBd_subset D (hbd ▸ Or.inr hx)
  obtain ⟨hDM, hDMb⟩ := hD.image (hwc.mono hDΔ) (hw'c.mono (image_mono hDΔ)) (hL.mono hDΔ)
  set DM := w '' D
  set Rp := outerSeg p ∪ w '' R ∪ outerSeg q
  have hyD : y ∈ D := hAD hA.left_mem
  have hy'D : y' ∈ D := hAD hA.right_mem
  have hDMn : ∀ z ∈ DM, ‖z‖ ≤ 1 / 2 := by
    rintro _ ⟨x, hx, rfl⟩
    exact hwn x (hDΔ hx)
  have hRDM : Rp ∩ DM = {w y, w y'} := by
    have hR' : ∀ u ∈ R, ∀ v ∈ D, w u = w v → u = v := fun u hu v hv e =>
      hwi (hRΔ hu) (hDΔ hv) e
    have hmem : ∀ u, u ∈ R → w u ∈ DM → w u = w y ∨ w u = w y' := by
      rintro u hu ⟨v, hv, he⟩
      have huv := hR' u hu v hv he.symm
      have : u ∈ R ∩ D := ⟨hu, huv ▸ hv⟩
      rw [hRD] at this
      rcases this with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    apply Subset.antisymm
    · rintro z ⟨(((h' | ⟨u, hu, rfl⟩) | h')), hz⟩
      · have : z = p := eq_of_mem_outerSeg_of_norm_le hp h' (hDMn z hz)
        subst this
        exact hmem a haR hz
      · exact hmem u hu hz
      · have : z = q := eq_of_mem_outerSeg_of_norm_le hq h' (hDMn z hz)
        subst this
        exact hmem b hbR hz
    · rintro z (rfl | rfl)
      · have hyR : y ∈ R := ((hRD.symm ▸ (Or.inl rfl : y ∈ ({y, y'} : Set S))) : y ∈ R ∩ D).1
        exact ⟨Or.inl (Or.inr ⟨y, hyR, rfl⟩), y, hyD, rfl⟩
      · have hyR : y' ∈ R := ((hRD.symm ▸ (Or.inr rfl : y' ∈ ({y, y'} : Set S))) : y' ∈ R ∩ D).1
        exact ⟨Or.inl (Or.inr ⟨y', hyR, rfl⟩), y', hy'D, rfl⟩
  have hTD : ∀ T : Set ℂ, T ⊆ sphere 0 1 \ {2 * p, 2 * q} → Disjoint T DM := by
    intro T hT
    rw [Set.disjoint_left]
    intro z hz hzD
    have h1 := mem_sphere_zero_iff_norm.mp (hT hz).1
    have h2 := hDMn z hzD
    norm_num [h1] at h2
  have hAA'm : w '' A ∩ w '' A' = {w y, w y'} := by
    rw [← image_inter_on (fun x hx u hu e => hwi (hDΔ (hA'D hx)) (hDΔ (hAD hu)) e), hAA',
      image_pair]
  have hbm : discBd DM = w '' A ∪ w '' A' := by rw [hDMb, hbd, image_union]
  have hF : extArc p q (w '' (R ∪ A)) = Rp ∪ w '' A := hext A (hAD.trans hDΔ)
  have hF' : extArc p q (w '' (R ∪ A')) = Rp ∪ w '' A' := hext A' (hA'D.trans hDΔ)
  have hlA : IsLineWithEnds (w '' A) (w y) (w y') :=
    IsLineWithEnds.image_of_injOn hA (hwc.mono (hAD.trans hDΔ)) (hwi.mono (hAD.trans hDΔ))
  have hsub : ∀ X : Set S, X ⊆ D → (∀ x ∈ D, x ∈ R → x ∈ X) →
      ∀ x ∈ D \ X, w x ∈ closedBall (0 : ℂ) 1 \ (Rp ∪ w '' X) := by
    rintro X hX hRX x ⟨hx, hxX⟩
    have hn := hwn x (hDΔ hx)
    refine ⟨mem_closedBall_zero_iff.mpr (by linarith), ?_⟩
    have hm : w x ∈ DM := mem_image_of_mem w hx
    rintro (h' | ⟨u, hu, he⟩)
    · have : w x ∈ Rp ∩ DM := ⟨h', hm⟩
      rw [hRDM] at this
      have hyX := hRX y hyD ((hRD.symm ▸ (Or.inl rfl : y ∈ ({y, y'} : Set S))) : y ∈ R ∩ D).1
      have hy'X := hRX y' hy'D ((hRD.symm ▸ (Or.inr rfl : y' ∈ ({y, y'} : Set S))) : y' ∈ R ∩ D).1
      rcases this with e | e
      · exact hxX (hwi (hDΔ hx) (hDΔ hyD) e ▸ hyX)
      · exact hxX (hwi (hDΔ hx) (hDΔ hy'D) e ▸ hy'X)
    · exact hxX (hwi (hDΔ (hX hu)) (hDΔ hx) he ▸ hu)
  have hRin : ∀ x ∈ D, x ∈ R → x ∈ A ∧ x ∈ A' := by
    intro x hx hxR
    have : x ∈ R ∩ D := ⟨hxR, hx⟩
    rw [hRD] at this
    have e : A ∩ A' ⊇ {y, y'} := hAA'.ge
    rcases this with rfl | rfl
    · exact e (Or.inl rfl)
    · exact e (Or.inr rfl)
  have himg : ∀ X : Set S, X ⊆ D → w '' (D \ X) = DM \ w '' X := by
    intro X hX
    rw [image_sdiff_of_injOn (hwi.mono hDΔ) hX]
  have hconn : ∀ X : Set S, X ⊆ discBd D → IsPreconnected (DM \ w '' X) := by
    intro X hX
    refine isPreconnected_disc_sdiff hDM ?_
    rw [hDMb]
    exact image_mono hX
  have hXA : A ⊆ discBd D := fun x hx => hbd ▸ Or.inl hx
  have hXA' : A' ⊆ discBd D := fun x hx => hbd ▸ Or.inr hx
  have side : ∀ (X : Set S) (F E₁ E₂ : Set ℂ) (T₁ T₂ : Set ℂ), X ⊆ discBd D →
      (∀ x ∈ D, x ∈ R → x ∈ X) → F = Rp ∪ w '' X → IsExtSplit F T₁ T₂ E₁ E₂ →
      (∀ x ∈ D \ X, w x ∈ E₁) ∨ (∀ x ∈ D \ X, w x ∈ E₂) := by
    intro X F E₁ E₂ T₁ T₂ hX hRX hFe hS
    have hXD : X ⊆ D := hX.trans (discBd_subset D)
    have hZ : DM \ w '' X ⊆ closedBall 0 1 \ F := by
      rw [hFe, ← himg X hXD]
      rintro _ ⟨x, hx, rfl⟩
      exact hsub X hXD hRX x hx
    rcases hS.conn _ hZ (hconn X hX) with h' | h'
    · exact Or.inl fun x hx => h' (himg X hXD ▸ mem_image_of_mem w hx)
    · exact Or.inr fun x hx => h' (himg X hXD ▸ mem_image_of_mem w hx)
  rcases side A _ E₁ E₂ T₁ T₂ hXA (fun x h h' => (hRin x h h').1) hF hE with hs | hs <;>
  rcases side A' _ E₁' E₂' T₁ T₂ hXA' (fun x h h' => (hRin x h h').2) hF' hE' with hs' | hs'
  · exfalso
    refine false_of_hole_on_same_side (T := T₂) (E := E₂) (Eo := E₁) (E' := E₂') (Eo'
      := E₁') hDM hlA
      hbm hAA'm hRDM (hTD T₂ (hTu ▸ subset_union_right)) hE.disc₂ hE'.disc₂ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [Set.inter_comm, hE.inter, hF]
    · rw [Set.inter_comm, hE'.inter, hF']
    · rw [hE.bd₂, hF]
    · rw [hE'.bd₂, hF']
    · rw [← himg A (hXA.trans (discBd_subset D))]
      rintro _ ⟨x, hx, rfl⟩
      exact hs x hx
    · rw [← himg A' (hXA'.trans (discBd_subset D))]
      rintro _ ⟨x, hx, rfl⟩
      exact hs' x hx
  · refine ⟨_, _, _, _, sd₁, sd₂, Or.inr ⟨fun x hx => ?_, fun x hx => ?_⟩⟩
    · refine ⟨⟨hDΔ hx.1, fun h' => ?_⟩, hs x hx⟩
      rcases h' with h' | h'
      · exact hx.2 (hRin x hx.1 h').1
      · exact hx.2 h'
    · refine ⟨⟨hDΔ hx.1, fun h' => ?_⟩, hs' x hx⟩
      rcases h' with h' | h'
      · exact hx.2 (hRin x hx.1 h').2
      · exact hx.2 h'
  · refine ⟨_, _, _, _, sd₁, sd₂, Or.inl ⟨fun x hx => ?_, fun x hx => ?_⟩⟩
    · refine ⟨⟨hDΔ hx.1, fun h' => ?_⟩, hs x hx⟩
      rcases h' with h' | h'
      · exact hx.2 (hRin x hx.1 h').1
      · exact hx.2 h'
    · refine ⟨⟨hDΔ hx.1, fun h' => ?_⟩, hs' x hx⟩
      rcases h' with h' | h'
      · exact hx.2 (hRin x hx.1 h').2
      · exact hx.2 h'
  · exfalso
    refine false_of_hole_on_same_side (T := T₁) (E := E₁) (Eo := E₂) (E' := E₁') (Eo'
      := E₂') hDM hlA
      hbm hAA'm hRDM (hTD T₁ (hTu ▸ subset_union_left)) hE.disc₁ hE'.disc₁ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hE.inter, hF]
    · rw [hE'.inter, hF']
    · rw [hE.bd₁, hF]
    · rw [hE'.bd₁, hF']
    · rw [← himg A (hXA.trans (discBd_subset D))]
      rintro _ ⟨x, hx, rfl⟩
      exact hs x hx
    · rw [← himg A' (hXA'.trans (discBd_subset D))]
      rintro _ ⟨x, hx, rfl⟩
      exact hs' x hx

/-- **The hole lies on one side.** `D ⊆ Δ` is a closed disc with boundary `A ∪ A'`, and `R ∪ A`, `R
∪ A'` are arcs with the same ends on `bd(Δ)`. Then `D - A` lies on the side of `I₂` of `R ∪ A` and
`D - A'` on the side of `I₁` of `R ∪ A'`, or the other way around. -/
theorem exists_hole_sides {S : Type u} [TopologicalSpace S]
    {Δ D R A A' I₁ I₂ : Set S} {a b y y' : S}
    (hΔ : IsClosedDisc Δ) (hD : IsClosedDisc D) (hDΔ : D ⊆ Δ)
    (hA : IsLineWithEnds A y y') (hbd : discBd D = A ∪ A') (hAA' : A ∩ A' = {y, y'})
    (hRD : R ∩ D = {y, y'}) (hRΔ : R ⊆ Δ)
    (hQ : IsLineWithEnds (R ∪ A) a b) (hQ' : IsLineWithEnds (R ∪ A') a b)
    (ha : a ∈ discBd Δ) (hb : b ∈ discBd Δ) (hab : a ≠ b) (haR : a ∈ R) (hbR : b ∈ R)
    (hI₁ : IsPreconnected I₁) (hI₂ : IsPreconnected I₂) (hId : Disjoint I₁ I₂)
    (hIu : I₁ ∪ I₂ = discBd Δ \ {a, b}) :
    ∃ Y₁ Y₂ Y₁' Y₂', IsArcSides Δ (R ∪ A) I₁ I₂ Y₁ Y₂ ∧ IsArcSides Δ (R ∪ A') I₁ I₂ Y₁' Y₂' ∧
      ((D \ A ⊆ Y₂ ∧ D \ A' ⊆ Y₁') ∨ (D \ A ⊆ Y₁ ∧ D \ A' ⊆ Y₂')) := by
  obtain ⟨h, g, c⟩ := hΔ.exists_isChart
  let w : S → ℂ := fun x => (1 / 2 : ℂ) * h x
  let w' : ℂ → S := fun z => g (2 * z)
  have hwc : ContinuousOn w Δ := continuousOn_const.mul c.hc
  have hL : LeftInvOn w' w Δ := by
    intro x hx
    have : (2 : ℂ) * ((1 / 2 : ℂ) * h x) = h x := by ring
    simp only [w', w, this]
    exact c.gh hx
  have hwi : InjOn w Δ := hL.injOn
  have hwn : ∀ x ∈ Δ, ‖w x‖ ≤ 1 / 2 := by
    intro x hx
    have := mem_closedBall_zero_iff.mp (c.hm hx)
    simp only [w, norm_mul]
    norm_num
    linarith
  have hwb : ∀ x ∈ discBd Δ, ‖w x‖ = 1 / 2 := by
    intro x hx
    have : h x ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hx
    simp only [w, norm_mul, mem_sphere_zero_iff_norm.mp this]
    norm_num
  have hw'c : ContinuousOn w' (w '' Δ) := by
    refine c.gc.comp (by fun_prop) ?_
    rintro _ ⟨x, hx, rfl⟩
    have : (2 : ℂ) * ((1 / 2 : ℂ) * h x) = h x := by ring
    simp only [w, this]
    exact c.hm hx
  have hbΔ : discBd Δ ⊆ Δ := discBd_subset Δ
  have hAD : A ⊆ D := fun x hx => discBd_subset D (hbd ▸ Or.inl hx)
  have hA'bd : ∀ x, x ∈ A' → x ∈ discBd D := fun x hx => hbd ▸ Or.inr hx
  have hA'D : A' ⊆ D := fun x hx => discBd_subset D (hA'bd x hx)
  set p := w a
  set q := w b
  have hp : ‖p‖ = 1 / 2 := hwb a ha
  have hq : ‖q‖ = 1 / 2 := hwb b hb
  have hpq : p ≠ q := fun e => hab (hwi (hbΔ ha) (hbΔ hb) e)
  have hsmall : ∀ X : Set S, X ⊆ Δ → w '' X ⊆ closedBall 0 (1 / 2) := by
    rintro X hX _ ⟨x, hx, rfl⟩
    exact mem_closedBall_zero_iff.mpr (hwn x (hX hx))
  have hQΔ : R ∪ A ⊆ Δ := union_subset hRΔ (hAD.trans hDΔ)
  have hQ'Δ : R ∪ A' ⊆ Δ := union_subset hRΔ (hA'D.trans hDΔ)
  have hlQ : IsLineWithEnds (w '' (R ∪ A)) p q :=
    IsLineWithEnds.image_of_injOn hQ (hwc.mono hQΔ) (hwi.mono hQΔ)
  have hlQ' : IsLineWithEnds (w '' (R ∪ A')) p q :=
    IsLineWithEnds.image_of_injOn hQ' (hwc.mono hQ'Δ) (hwi.mono hQ'Δ)
  let dbl : ℂ → ℂ := fun z => 2 * z
  let T₁ := dbl '' (w '' I₁)
  let T₂ := dbl '' (w '' I₂)
  have hI₁Δ : I₁ ⊆ Δ := fun x hx => hbΔ ((hIu ▸ Or.inl hx : x ∈ discBd Δ \ {a, b}).1)
  have hI₂Δ : I₂ ⊆ Δ := fun x hx => hbΔ ((hIu ▸ Or.inr hx : x ∈ discBd Δ \ {a, b}).1)
  have hdb : Continuous dbl := by fun_prop
  have hdbi : Injective dbl := fun u v e => mul_left_cancel₀ (two_ne_zero) e
  have hT₁ : IsPreconnected T₁ := (hI₁.image _ (hwc.mono hI₁Δ)).image _ hdb.continuousOn
  have hT₂ : IsPreconnected T₂ := (hI₂.image _ (hwc.mono hI₂Δ)).image _ hdb.continuousOn
  have hTd : Disjoint T₁ T₂ := by
    rw [Set.disjoint_left]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ ⟨_, ⟨y₁, hy, rfl⟩, he⟩
    have := hwi (hI₂Δ hy) (hI₁Δ hx) (hdbi he)
    exact Set.disjoint_left.mp hId hx (this ▸ hy)
  have hTu : T₁ ∪ T₂ = sphere 0 1 \ {2 * p, 2 * q} := by
    apply Subset.antisymm
    · rintro _ (⟨_, ⟨x, hx, rfl⟩, rfl⟩ | ⟨_, ⟨x, hx, rfl⟩, rfl⟩)
      · have hx' : x ∈ discBd Δ \ {a, b} := hIu ▸ Or.inl hx
        refine ⟨?_, ?_⟩
        · rw [mem_sphere_zero_iff_norm]
          simp only [dbl, norm_mul, hwb x hx'.1]
          norm_num
        · rintro (e | e)
          · exact hx'.2 (Or.inl (hwi (hbΔ hx'.1) (hbΔ ha) (hdbi e)))
          · exact hx'.2 (Or.inr (hwi (hbΔ hx'.1) (hbΔ hb) (hdbi e)))
      · have hx' : x ∈ discBd Δ \ {a, b} := hIu ▸ Or.inr hx
        refine ⟨?_, ?_⟩
        · rw [mem_sphere_zero_iff_norm]
          simp only [dbl, norm_mul, hwb x hx'.1]
          norm_num
        · rintro (e | e)
          · exact hx'.2 (Or.inl (hwi (hbΔ hx'.1) (hbΔ ha) (hdbi e)))
          · exact hx'.2 (Or.inr (hwi (hbΔ hx'.1) (hbΔ hb) (hdbi e)))
    · rintro z ⟨hz, hne⟩
      have : h (g z) = z := c.hg (sphere_subset_closedBall hz)
      obtain ⟨x, hx, hxe⟩ : z ∈ h '' discBd Δ := c.bd ▸ hz
      have hz2 : z = dbl (w x) := by
        simp only [dbl, w, ← hxe]
        ring
      have hxne : x ∈ discBd Δ \ {a, b} := by
        refine ⟨hx, ?_⟩
        rintro (rfl | rfl)
        · exact hne (Or.inl hz2)
        · exact hne (Or.inr hz2)
      rw [← hIu] at hxne
      rcases hxne with h' | h'
      · exact Or.inl ⟨_, mem_image_of_mem w h', hz2.symm⟩
      · exact Or.inr ⟨_, mem_image_of_mem w h', hz2.symm⟩
  have hext : ∀ X : Set S, X ⊆ Δ → extArc p q (w '' (R ∪ X)) =
      (outerSeg p ∪ w '' R ∪ outerSeg q) ∪ w '' X := by
    intro X _
    simp only [extArc, image_union]
    ext z
    simp only [mem_union]
    tauto
  have hs₂ : ∀ X : Set S, IsLineWithEnds (w '' (R ∪ X)) p q → (R ∪ X) ⊆ Δ →
      ∃ E₁ E₂, IsExtSplit (extArc p q (w '' (R ∪ X))) T₁ T₂ E₁ E₂ := by
    intro X hl hX
    refine exists_isExtSplit (isLineWithEnds_extArc hl (hsmall _ hX) hp hq hpq)
      (extArc_subset_closedBall (hsmall _ hX) hp hq)
      (extArc_inter_sphere hl (hsmall _ hX) hp hq hpq) ?_ hT₁ hT₂ hTd hTu
    intro e
    exact hpq (hdbi e)
  obtain ⟨E₁, E₂, hE⟩ := hs₂ A hlQ hQΔ
  obtain ⟨E₁', E₂', hE'⟩ := hs₂ A' hlQ' hQ'Δ
  have hsides : ∀ (X E₁ E₂ : Set _), IsLineWithEnds (w '' (R ∪ X)) p q → (R ∪ X) ⊆ Δ →
      IsExtSplit (extArc p q (w '' (R ∪ X))) T₁ T₂ E₁ E₂ →
      IsArcSides Δ (R ∪ X) I₁ I₂ {x ∈ Δ \ (R ∪ X) | w x ∈ E₁} {x ∈ Δ \ (R ∪ X) | w x ∈ E₂} := by
    intro X E₁ E₂ hl hX hS
    have hsph : ∀ Y : Set S, Y ⊆ discBd Δ \ {a, b} → ∀ x ∈ Y,
        ‖w x‖ = 1 / 2 ∧ w x ≠ p ∧ w x ≠ q ∧ dbl (w x) ∉ extArc p q (w '' (R ∪ X)) := by
      intro Y hY x hx
      have hx' := hY hx
      have hnp : w x ≠ p := fun e => hx'.2 (Or.inl (hwi (hbΔ hx'.1) (hbΔ ha) e))
      have hnq : w x ≠ q := fun e => hx'.2 (Or.inr (hwi (hbΔ hx'.1) (hbΔ hb) e))
      refine ⟨hwb x hx'.1, hnp, hnq, fun hm => ?_⟩
      have hn : dbl (w x) ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm]
        simp only [dbl, norm_mul, hwb x hx'.1]
        norm_num
      have : dbl (w x) ∈ extArc p q (w '' (R ∪ X)) ∩ sphere 0 1 := ⟨hm, hn⟩
      rw [extArc_inter_sphere hl (hsmall _ hX) hp hq hpq] at this
      rcases this with e | e
      · exact hnp (hdbi e)
      · exact hnq (hdbi e)
    have hinQ : ∀ x, x ∉ R ∪ X → x ∈ Δ → w x ∉ w '' (R ∪ X) := by
      rintro x hx hxΔ ⟨u, hu, he⟩
      exact hx (hwi (hX hu) hxΔ he ▸ hu)
    have hdT : ∀ T : Set ℂ, T ⊆ sphere 0 1 \ {2 * p, 2 * q} →
        Disjoint T (extArc p q (w '' (R ∪ X))) := by
      intro T hT
      rw [Set.disjoint_left]
      intro z hz hm
      have : z ∈ extArc p q (w '' (R ∪ X)) ∩ sphere 0 1 := ⟨hm, (hT hz).1⟩
      rw [extArc_inter_sphere hl (hsmall _ hX) hp hq hpq] at this
      exact (hT hz).2 this
    refine hS.arcSides hwc hwi hwn hX hI₁Δ hI₂Δ rfl
      ⟨a, Or.inl haR, rfl⟩ ⟨b, Or.inl hbR, rfl⟩ hp hq ?_ ?_
    · rintro x ⟨hx, hxQ⟩
      obtain ⟨hn, hnp, hnq, -⟩ := hsph I₁ (hIu ▸ subset_union_left) x hx
      exact hS.mem_side rfl (hsmall _ hX) hp hq hn hnp hnq (hinQ x hxQ (hI₁Δ hx))
        ⟨_, mem_image_of_mem w hx, rfl⟩ (hdT T₁ (hTu ▸ subset_union_left))
    · rintro x ⟨hx, hxQ⟩
      obtain ⟨hn, hnp, hnq, -⟩ := hsph I₂ (hIu ▸ subset_union_right) x hx
      exact hS.symm.mem_side rfl (hsmall _ hX) hp hq hn hnp hnq (hinQ x hxQ (hI₂Δ hx))
        ⟨_, mem_image_of_mem w hx, rfl⟩ (hdT T₂ (hTu ▸ subset_union_right))
  have sd₁ := hsides A E₁ E₂ hlQ hQΔ hE
  have sd₂ := hsides A' E₁' E₂' hlQ' hQ'Δ hE'
  exact hole_sides_of_ext_splits hD hDΔ hA hbd hAA' hRD hRΔ haR hbR hwc hw'c hL hwn
    hp hq hTu hE hE' hext sd₁ sd₂

end GraphMinor.GM09
