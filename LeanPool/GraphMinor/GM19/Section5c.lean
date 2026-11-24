/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section5b
public import LeanPool.GraphMinor.GM19.ArcDirection

/-!
# Graph Minors XIX, Section 5: the frame of a fragment

The frame `ψ⁻¹(Φ) ∩ Σ₁` of a fragment has vertex set `ψ⁻¹(V(Φ) ∪ V(K))`. Its sides are open arcs of
the
cuffs of `Σ₁`. Each side is read along the circle that parametrises its cuff, forward or backward as
the
parameter `flip` says. A border edge of the pulled back painting is read the same way as the side
that
holds it, so the two directions agree (`DirAgrees`). The long sides are those that `ψ` maps into a
long side of `Φ`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S S₁ : Type} [TopologicalSpace S] [TopologicalSpace S₁] [T2Space S] [T2Space S₁]

/-- A fixed way to read each cuff as a circle. -/
noncomputable def cuffPar (hS : IsSurface S₁) (C : cuffs S₁) : Circle ≃ₜ C.1 :=
  ((cuff_statement S₁ hS).2.2 C.1 C.2).some

/-- `l` lists the ends of the open arc `e` of a cuff, in the sense given by `ε`. -/
def IsArcMarch (hS : IsSurface S₁) (ε : Bool) (e : Set S₁) (l : List S₁) : Prop :=
  ∃ (C : cuffs S₁) (a b : ℝ), a < b ∧ b < a + 2 * Real.pi ∧ e = arcOf (cuffPar hS C) a b ∧
    l = if ε then [cuffPoint (cuffPar hS C) b, cuffPoint (cuffPar hS C) a]
      else [cuffPoint (cuffPar hS C) a, cuffPoint (cuffPar hS C) b]

open Classical in
/-- The march of an open arc of a cuff, in the sense given by `ε`. -/
noncomputable def arcMarch (hS : IsSurface S₁) (ε : Bool) (e : Set S₁) : List S₁ :=
  if h : ∃ l, IsArcMarch hS ε e l then h.choose else []

omit [T2Space S₁] in
theorem arcMarch_spec (hS : IsSurface S₁) (ε : Bool) {e : Set S₁} {C : cuffs S₁} {a b : ℝ}
    (hab : a < b) (hub : b < a + 2 * Real.pi) (he : e = arcOf (cuffPar hS C) a b) :
    IsArcMarch hS ε e (arcMarch hS ε e) := by
  have h : ∃ l, IsArcMarch hS ε e l := ⟨_, C, a, b, hab, hub, he, rfl⟩
  rw [arcMarch, dite_eq_left h]
  exact h.choose_spec

theorem IsArcMarch.nodup {hS : IsSurface S₁} {ε : Bool} {e : Set S₁} {l : List S₁}
    (h : IsArcMarch hS ε e l) : l.Nodup := by
  obtain ⟨C, a, b, hab, hub, -, rfl⟩ := h
  have hne := (GM20.line_facts (isLine_arcOf (cuffPar hS C) hab hub)).1
  cases ε <;> simp [hne, hne.symm]

theorem IsArcMarch.set_eq {hS : IsSurface S₁} {ε : Bool} {e : Set S₁} {l : List S₁}
    (h : IsArcMarch hS ε e l) : {v | v ∈ l} = tilde e := by
  obtain ⟨C, a, b, hab, hub, rfl, rfl⟩ := h
  rw [tilde_arcOf _ hab hub]
  ext x
  cases ε <;> simp [or_comm]

/-- The shape of an arc-wise component of `bd(Σ₁) \ N`. -/
theorem arc_shape (hS : IsSurface S₁) {N : Set S₁} (hN : N.Finite)
    (h2 : ∀ C : cuffs S₁, ∃ p ∈ N ∩ C.1, ∃ q ∈ N ∩ C.1, p ≠ q) {e : Set S₁}
    (he : e ∈ arcComponentsIn (bd S₁ \ N)) :
    (tilde e).ncard = 2 ∧ (tilde e).Finite ∧ IsLine (closure e) ∧ lineEnds (closure e) = tilde e
      := by
  obtain ⟨C, a, b, hab, hub, rfl, -, -, -⟩ := exists_arc_of_mem hS (cuffPar hS) hN h2 he
  have hL := isLine_arcOf (cuffPar hS C) hab hub
  have ht := tilde_arcOf (cuffPar hS C) hab hub
  obtain ⟨f, -⟩ := id hL
  refine ⟨by rw [ht, ncard_pair (GM20.line_facts hL).1], ?_, ⟨f⟩, ?_⟩
  · rw [ht]
    exact (finite_singleton _).insert _
  · rw [ht]
    exact (GM20.line_facts hL).2.2.2

/-- The vertex set `ψ⁻¹(V(Φ) ∪ V(K))` of the frame of a fragment. -/
def pullFrameV (Φ : Frame S) (K : Drawing S) (ψ : S₁ → S) : Set S₁ := ψ ⁻¹' (Φ.V ∪ K.V)

/-- The hypotheses for the frame of a fragment. -/
structure FrameData (Φ : Frame S) (Γ : Painting S) (K : Drawing S) (ψ : S₁ → S) : Prop where
  pull : PullData Γ K ψ
  fits : Γ.Fits Φ
  two : ∀ C : cuffs S₁, ∃ p ∈ pullFrameV Φ K ψ ∩ C.1, ∃ q ∈ pullFrameV Φ K ψ ∩ C.1, p ≠ q
  K_bd : K.U ∩ bd S ⊆ K.V

namespace FrameData

variable {Φ : Frame S} {Γ : Painting S} {K : Drawing S} {ψ : S₁ → S}

omit [T2Space S] [T2Space S₁] in
theorem finite_pullFrameV (D : FrameData Φ Γ K ψ) : (pullFrameV Φ K ψ).Finite :=
  (Φ.finite_V.union K.finite_V).preimage' fun y _ ↦ D.pull.frag.finite_fibres y

omit [T2Space S] [T2Space S₁] in
theorem pullFrameV_subset_bd (D : FrameData Φ Γ K ψ) : pullFrameV Φ K ψ ⊆ bd S₁ := by
  rintro x (hx | hx)
  · exact D.pull.mem_bd_of_notMem_R (Or.inl (Φ.V_subset hx))
  · exact D.pull.mem_bd_of_notMem_R (Or.inr (K.V_subset_U hx))

omit [T2Space S] [T2Space S₁] in
theorem pullFrameV_subset (D : FrameData Φ Γ K ψ) : pullFrameV Φ K ψ ⊆ pullV Γ K ψ := by
  rintro x (hx | hx)
  · exact Or.inl (D.fits.V_subset hx)
  · exact Or.inr hx

end FrameData

/-- **The frame `ψ⁻¹(Φ) ∩ Σ₁`** (Graph Minors XIX, Section 5, page 335). No two long sides have a
common end,
which we take as a hypothesis here. -/
noncomputable def pullFrame {Φ : Frame S} {Γ : Painting S} {K : Drawing S} {ψ : S₁ → S}
    (D : FrameData Φ Γ K ψ) (flip : Set S₁ → Bool)
    (hlong : ∀ s₁ ∈ arcComponentsIn (bd S₁ \ pullFrameV Φ K ψ),
      ∀ s₂ ∈ arcComponentsIn (bd S₁ \ pullFrameV Φ K ψ), s₁ ≠ s₂ →
      (∃ s ∈ Φ.longSides, ψ '' s₁ ⊆ s) → (∃ s ∈ Φ.longSides, ψ '' s₂ ⊆ s) →
      Disjoint (tilde s₁) (tilde s₂)) : Frame S₁ where
  V := pullFrameV Φ K ψ
  γ s := arcMarch D.pull.frag.isSurface (flip s) s
  isLong s := ∃ s' ∈ Φ.longSides, ψ '' s ⊆ s'
  V_subset := D.pullFrameV_subset_bd
  finite_V := D.finite_pullFrameV
  finite_sides := finite_arcComponentsIn_bd D.pull.frag.isSurface D.finite_pullFrameV D.two
  side_shape _ hs := arc_shape D.pull.frag.isSurface D.finite_pullFrameV D.two hs
  γ_nodup s hs := by
    have hS := D.pull.frag.isSurface
    obtain ⟨C, a, b, hab, hub, he, -, -, -⟩ :=
      exists_arc_of_mem hS (cuffPar hS) D.finite_pullFrameV D.two hs
    exact (arcMarch_spec hS (flip s) hab hub he).nodup
  γ_set s hs := by
    have hS := D.pull.frag.isSurface
    obtain ⟨C, a, b, hab, hub, he, -, -, -⟩ :=
      exists_arc_of_mem hS (cuffPar hS) D.finite_pullFrameV D.two hs
    exact (arcMarch_spec hS (flip s) hab hub he).set_eq
  long_disjoint := hlong

open Classical in
/-- The side of the frame of the fragment that holds a border edge. -/
noncomputable def sideOf (Φ : Frame S) (K : Drawing S) (ψ : S₁ → S) (e : Set S₁) : Set S₁ :=
  if h : ∃ s ∈ arcComponentsIn (bd S₁ \ pullFrameV Φ K ψ), e ⊆ s then h.choose else ∅

namespace FrameData

variable {Φ : Frame S} {Γ : Painting S} {K : Drawing S} {ψ : S₁ → S} (D : FrameData Φ Γ K ψ)
include D

omit [T2Space S] [T2Space S₁] D in
theorem sideOf_eq {e s : Set S₁} (hne : e.Nonempty)
    (hs : s ∈ arcComponentsIn (bd S₁ \ pullFrameV Φ K ψ)) (hes : e ⊆ s) : sideOf Φ K ψ e = s := by
  have h : ∃ s ∈ arcComponentsIn (bd S₁ \ pullFrameV Φ K ψ), e ⊆ s := ⟨s, hs, hes⟩
  rw [sideOf, dite_eq_left h]
  obtain ⟨h₁, h₂⟩ := h.choose_spec
  obtain ⟨x, hx⟩ := hne
  exact arcComp_eq_of_mem h₁ hs (h₂ hx) (hes hx)

omit [T2Space S] in
/-- The two parts of the third condition of "fit" for the pull-back: an edge inside a side, read in
the
sense of the side, has the direction of the side. -/
theorem dirAgrees_pull (flip : Set S₁ → Bool) {e s : Set S₁}
    (he : e ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ))
    (hs : s ∈ arcComponentsIn (bd S₁ \ pullFrameV Φ K ψ)) (hes : e ⊆ s) :
    DirAgrees s (arcMarch D.pull.frag.isSurface (flip s) s) e
      (arcMarch D.pull.frag.isSurface (flip s) e) := by
  have hS := D.pull.frag.isSurface
  generalize flip s = ε
  obtain ⟨C, a, b, hab, hub, hse, -, -, -⟩ :=
    exists_arc_of_mem hS (cuffPar hS) D.finite_pullFrameV D.two hs
  obtain ⟨C', a', b', hab', hub', hee, -, -, -⟩ :=
    exists_arc_of_mem hS (cuffPar hS) D.pull.finite_pullV D.pull.two he
  obtain ⟨C₁, a₁, b₁, hab₁, hub₁, hs₁, hl₁⟩ := arcMarch_spec hS ε hab hub hse
  obtain ⟨C₂, a₂, b₂, hab₂, hub₂, he₂, hl₂⟩ := arcMarch_spec hS ε hab' hub' hee
  rw [hl₁, hl₂]
  -- The two arcs lie on the same cuff.
  have hC : C₂ = C₁ := by
    by_contra hne
    obtain ⟨x, hx⟩ := he.1
    have h₁ : x ∈ C₁.1 := arcOf_subset _ _ _ (hs₁ ▸ hes hx)
    have h₂ : x ∈ C₂.1 := arcOf_subset _ _ _ (he₂ ▸ hx)
    exact disjoint_left.mp (cuffs_disjoint' hne) h₂ h₁
  subst hC
  obtain ⟨m, h₁, h₂⟩ := exists_shift (cuffPar hS C₂) hab₁ hab₂ hub₁ (by
    rw [← he₂, ← hs₁]
    exact hes)
  have hshift := arcOf_shift (cuffPar hS C₂) a₂ b₂ m
  have hp₁ := cuffPoint_shift (cuffPar hS C₂) a₂ m
  have hp₂ := cuffPoint_shift (cuffPar hS C₂) b₂ m
  rw [hs₁, he₂, ← hshift, ← hp₁, ← hp₂]
  have hlt : a₂ + m * (2 * Real.pi) < b₂ + m * (2 * Real.pi) := by linarith
  cases ε
  · simpa using dirAgrees_forward (cuffPar hS C₂) hub₁ h₁ hlt h₂
  · simpa using dirAgrees_backward (cuffPar hS C₂) hub₁ h₁ hlt h₂

end FrameData

end GraphMinor.GM19
