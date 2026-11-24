/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.JoinDiscs
public import LeanPool.GraphMinor.GM07.Section5b
public import LeanPool.GraphMinor.GM19.RadialExists
public import LeanPool.GraphMinor.Surface.PushOff
public import LeanPool.GraphMinor.Surface.SurfacePull

/-!
# Discs around a forest in a surface

Graph Minors VII, (3.4), claim (1) (page 220), says that a thin neighbourhood of each component of a
forest `H` is a disc. This
file proves it. We add discs to the cuffs of `Σ`, to get a closed surface. Around each vertex of `H`
we take a star disc of the
drawing made of `H` and the cuffs. At a vertex in `bd(Σ)` we keep the half of the disc in `Σ`
(`exists_half`). Each edge of `H` now
leaves the star disc at its ends in one point, and between them it is a line that misses all these
discs (`exists_edge_piece`). So
`exists_forest_discs` applies.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11 unitInterval

variable {S T : Type} [TopologicalSpace S] [TopologicalSpace T]

/-- A surface with its cuffs capped: the frontier of the surface is its boundary. -/
theorem cap_frontier {j : S → T} {K : Set T} (hT : IsClosedSurface T) (hj : IsClosedEmbedding j)
  (hK : IsClosed K)
    (hu : range j ∪ K = univ) (hi : range j ∩ K = j '' bd S) : frontier (range j) = j '' bd S := by
  have hoff : ∀ z, z ∉ bd S → j z ∈ interior (range j) := fun z hz => by
    have h1 : j z ∉ K := fun h => by
      have : j z ∈ j '' bd S := hi ▸ ⟨⟨z, rfl⟩, h⟩
      obtain ⟨z', hz', e⟩ := this
      exact hz (hj.injective e ▸ hz')
    refine interior_maximal (s := range j) ?_ hK.isOpen_compl h1
    intro x hx
    have : x ∈ range j ∪ K := hu ▸ mem_univ x
    exact this.resolve_right hx
  have hon : ∀ z, z ∈ bd S → j z ∉ interior (range j) := fun z hz hin => by
    have hO : IsOpen (j ⁻¹' interior (range j)) := isOpen_interior.preimage hj.continuous
    let k : (j ⁻¹' interior (range j)) → T := fun x => j x.1
    have hk : IsOpenEmbedding k := by
      refine ⟨hj.isEmbedding.comp IsEmbedding.subtypeVal, ?_⟩
      have : range k = interior (range j) := by
        ext x
        constructor
        · rintro ⟨y, rfl⟩
          exact y.2
        · intro hx
          obtain ⟨y, rfl⟩ := interior_subset hx
          exact ⟨⟨y, hx⟩, rfl⟩
      rw [this]
      exact isOpen_interior
    have h1 : IsInteriorPoint (⟨z, hin⟩ : (j ⁻¹' interior (range j))) :=
      (isInteriorPoint_iff_of_isOpenEmbedding hk).mp (hT.2.2 _)
    exact hz ((isInteriorPoint_sub hO).mp h1)
  have hc : IsClosed (range j) := hj.isClosed_range
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    rw [hc.closure_eq] at h1
    obtain ⟨z, rfl⟩ := h1
    by_cases hz : z ∈ bd S
    · exact ⟨z, hz, rfl⟩
    · exact (h2 (hoff z hz)).elim
  · rintro ⟨z, hz, rfl⟩
    rw [frontier, hc.closure_eq]
    exact ⟨⟨z, rfl⟩, hon z hz⟩

/-- A point of the boundary is a limit of interior points of the capped surface inside the surface,
and of points outside. -/
theorem cap_limits {j : S → T} {K : Set T} (hS : IsSurface S) (hT : IsClosedSurface T)
  (hj : IsClosedEmbedding j) (hK : IsClosed K)
    (hu : range j ∪ K = univ) (hi : range j ∩ K = j '' bd S) {y : S} (hy : y ∈ bd S) :
    j y ∈ closure (interior (range j)) ∧ j y ∈ closure (range j)ᶜ := by
  have hf := cap_frontier hT hj hK hu hi
  have hyf : j y ∈ frontier (range j) := hf ▸ ⟨y, hy, rfl⟩
  constructor
  · have h1 : y ∈ closure (bd S)ᶜ := mem_closure_compl_bd (hS.2.2 y)
    refine map_mem_closure hj.continuous h1 fun z hz => ?_
    by_contra hn
    have : j z ∈ frontier (range j) := ⟨subset_closure ⟨z, rfl⟩, hn⟩
    rw [hf] at this
    obtain ⟨z', hz', e⟩ := this
    exact hz (hj.injective e ▸ hz')
  · rw [closure_compl]
    exact hyf.2

/-- **Half of a star disc.** A closed set `B` with frontier a chord of the star disc through its
centre. -/
theorem exists_half (hT : IsClosedSurface T) {Γ : Drawing T} {y w : T} {R C A₁ A₂ B : Set T}
  (h : IsStarDisc Γ y R)
    (h₁ : IsLineWithEnds A₁ w y) (h₂ : IsLineWithEnds A₂ w y) (hC : C = A₁ ∪ A₂) (hm : A₁ ∩ A₂
      = {w, y}) (hw : w ∉ R)
    (hCc : IsClosed C) (hCn : IsGammaNice Γ C) (hB : IsClosed B) (hf : frontier B ∩ R = C ∩ R)
    (hin : y ∈ closure (interior B)) (hout : y ∈ closure Bᶜ) :
    ∃ s t ℓ P E c c', IsLineWithEnds ℓ s t ∧ s ≠ t ∧ ℓ = C ∩ R ∧ IsClosedDisc P ∧ IsClosedDisc E
      ∧ P ∪ E = R ∧ P ∩ E = ℓ ∧
      IsLineWithEnds c s t ∧ IsLineWithEnds c' s t ∧ c ∪ c' = discBd R ∧ c ∩ c' = {s, t} ∧ discBd P
        = c ∪ ℓ ∧ discBd E = c' ∪ ℓ ∧
      ℓ ∩ discBd R = {s, t} ∧ y ∈ ℓ ∧ P ⊆ B ∧ Disjoint (E \ ℓ) B ∧ s ∈ A₁ ∧ t ∈ A₂ := by
  have ht2 : T2Space T := hT.2.1
  obtain ⟨s, t, ρ₁, ρ₂, B₁, B₂, r₁, r₂, l₁, l₂, u₁, u₂, hl, hst, hF, hbd⟩
    := exists_chord hT h h₁ h₂ hC hm hw hCc hCn
  have hyℓ : y ∈ ρ₁ ∪ ρ₂ := .inl r₁.right_mem
  have hsub : ρ₁ ∪ ρ₂ ⊆ R := by rw [hF]; exact inter_subset_right
  have hsA : s ∈ A₁ := u₁ ▸ .inl l₁.right_mem
  have htA : t ∈ A₂ := u₂ ▸ .inl l₂.right_mem
  obtain ⟨Δ₁, Δ₂, c₁, c₂, c1, c2, hu, hi, d₁, d₂, hU, hI, b₁, b₂, p₁, p₂⟩
    := disc_split h.disc hsub hst hl hbd
  have hfr : frontier B ∩ R = ρ₁ ∪ ρ₂ := by rw [hf, hF]
  rcases side_of_frontier hT h.disc hU hI p₁ p₂ hB hfr hyℓ h.mem hin hout with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact ⟨s, t, _, Δ₁, Δ₂, c₁, c₂, hl, hst, hF, d₁, d₂, hU, hI, c1, c2, hu, hi, b₁, b₂, hbd,
      hyℓ, h3, h4, hsA, htA⟩
  · exact ⟨s, t, _, Δ₂, Δ₁, c₂, c₁, hl, hst, hF, d₂, d₁, by rw [union_comm, hU],
      by rw [inter_comm, hI], c2, c1,
      by rw [union_comm, hu], by rw [inter_comm, hi], b₂, b₁, hbd, hyℓ, h3, h4, hsA, htA⟩

/-- **An edge between two star discs.** It is a ray in each disc, and a line between them. -/
theorem exists_edge_piece (hT : IsClosedSurface T) {Γ : Drawing T} {u v : T} {Ru Rv L : Set T}
  (hu : IsStarDisc Γ u Ru)
    (hv : IsStarDisc Γ v Rv) (hdis : Disjoint Ru Rv) (hL : IsLineWithEnds L u v) (hLc : IsClosed L)
      (hLn : IsGammaNice Γ L) :
    ∃ p q M ρu ρv, IsLineWithEnds M p q ∧ L = ρu ∪ M ∪ ρv ∧ ρu = L ∩ Ru ∧ ρv = L ∩ Rv ∧ M ∩ Ru
      = {p} ∧ M ∩ Rv = {q} ∧
      p ∈ discBd Ru ∧ q ∈ discBd Rv ∧ ρu \ {p} ⊆ discInt Ru ∧ ρv \ {q} ⊆ discInt Rv ∧ u ∉ M ∧ v ∉ M
        := by
  have ht2 : T2Space T := hT.2.1
  have huRv : u ∉ Rv := disjoint_left.mp hdis hu.mem.1
  obtain ⟨q, L₁, L₂, l1, l2, hun, hin, e₂, hqb, hqi, hqu, hqv⟩ :=
    exists_ray hT hv hL huRv hLc hLn (by simp) isClosed_empty (by simp)
  have hqRv : q ∈ Rv := by
    have : q ∈ L₂ := l2.left_mem
    rw [e₂] at this
    exact this.2
  have hqRu : q ∉ Ru := fun h => disjoint_left.mp hdis h hqRv
  obtain ⟨p, N₁, N₂, n1, n2, hun', hin', e₃, hpb, hpi, hpq, hpu⟩ :=
    exists_ray hT hu l1.symm hqRu hLc hLn (by rw [hun]) l2.isCompact.isClosed
      (by rw [hin]; exact fun x hx => .inl hx)
  have hL₂Rv : L₂ ⊆ Rv := fun x hx => (e₂ ▸ hx : x ∈ L ∩ Rv).2
  have hN₁L₁ : N₁ ⊆ L₁ := hun' ▸ subset_union_left
  have hN₂L₁ : N₂ ⊆ L₁ := hun' ▸ subset_union_right
  have hN₂Ru : N₂ ⊆ Ru := fun x hx => (e₃ ▸ hx : x ∈ L₁ ∩ Ru).2
  have hL₂off : ∀ x ∈ L₂, x ∉ Ru := fun x hx h => disjoint_left.mp hdis h (hL₂Rv hx)
  refine ⟨p, q, N₁, N₂, L₂, n1.symm, ?_, ?_, e₂, ?_, ?_, hpb, hqb, hpi, hqi, ?_, ?_⟩
  · rw [← hun, ← hun', union_comm N₂ N₁]
  · ext x
    constructor
    · intro hx
      exact ⟨hun ▸ .inl (hN₂L₁ hx), hN₂Ru hx⟩
    · rintro ⟨h1, h2⟩
      rw [← hun] at h1
      rcases h1 with h1 | h1
      · rw [e₃]
        exact ⟨h1, h2⟩
      · exact (hL₂off x h1 h2).elim
  · ext x
    constructor
    · rintro ⟨h1, h2⟩
      have : x ∈ N₁ ∩ N₂ := ⟨h1, by rw [e₃]; exact ⟨hN₁L₁ h1, h2⟩⟩
      rwa [hin'] at this
    · rintro rfl
      exact ⟨n1.right_mem, hN₂Ru n2.left_mem⟩
  · ext x
    constructor
    · rintro ⟨h1, h2⟩
      have : x ∈ L₁ ∩ L₂ := ⟨hN₁L₁ h1, by rw [e₂]; exact ⟨hun ▸ .inl (hN₁L₁ h1), h2⟩⟩
      rwa [hin] at this
    · rintro rfl
      exact ⟨n1.left_mem, hqRv⟩
  · intro h
    have : u ∈ N₁ ∩ N₂ := ⟨h, n2.right_mem⟩
    rw [hin'] at this
    exact hpu this.symm
  · intro h
    have : v ∈ L₁ ∩ L₂ := ⟨hN₁L₁ h, l2.right_mem⟩
    rw [hin] at this
    exact hqv this.symm

/-- A point `y` of a cuff, with a parameter `f` of the cuff that starts at `y`, and a piece `f [-ε,
ε]` of it around `y`. -/
structure CuffMark (f : ℝ → S) (ε : ℝ) (y : S) : Prop where
  cont : Continuous f
  zero : f 0 = y
  pos : 0 < ε
  lt : ε < 1
  inj : InjOn f (Ioc (-Real.pi) Real.pi)
  per : f (-Real.pi) = f Real.pi
  onBd : ∀ t ∈ Icc (-Real.pi) Real.pi, f t ∈ bd S
  rest : IsClosed (bd S \ f '' Icc (-Real.pi) Real.pi)

private theorem cuff_image_eq_union_of_half_cuff_ranges
    {S : Type}
    {T : Type}
    {j : S → T}
    {f : ℝ → S}
    {ε : ℝ}
    (hpi : 3 < Real.pi)
    (hε : 0 < ε)
    (hε1 : ε < 1)
    (hmap₁ : ∀ (u : ↑I), (1 - ↑u) * Real.pi ∈ Ioc (-Real.pi) Real.pi ∧ 0 ≤ (1 - ↑u) * Real.pi)
    (hform₁ : ∀ θ ∈ Icc 0 Real.pi, ∃ u : I, (1 - ↑u) * Real.pi = θ) :
    j '' f '' Icc (-Real.pi) Real.pi = range (fun u : I => j (f ((1 - ↑u) * Real.pi))) ∪
      range (fun u : I => j (f (-((1 - ↑u) * Real.pi)))) := by
  ext z
  constructor
  · rintro ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩
    rcases le_total 0 θ with h0 | h0
    · obtain ⟨u, hu⟩ := hform₁ θ ⟨h0, hθ.2⟩
      exact .inl ⟨u, by simp only [hu]⟩
    · obtain ⟨u, hu⟩ := hform₁ (-θ) ⟨by linarith, by linarith [hθ.1]⟩
      exact .inr ⟨u, by simp only [hu, neg_neg]⟩
  · rintro (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · have := hmap₁ u
      exact ⟨_, ⟨_, ⟨by linarith [this.1.1], this.1.2⟩, rfl⟩, rfl⟩
    · have := hmap₁ u
      exact ⟨_, ⟨_, ⟨by linarith [this.1.2], by linarith [this.2]⟩, rfl⟩, rfl⟩

private theorem half_cuff_ranges_intersect_at_endpoints
    {S : Type}
    {T : Type}
    [TopologicalSpace T]
    {j : S → T}
    {y : S}
    {f : ℝ → S}
    (hg0₁ : (fun u : I => j (f ((1 - ↑u) * Real.pi))) 0 = j (f Real.pi))
    (hg1₁ : (fun u : I => j (f ((1 - ↑u) * Real.pi))) 1 = j y)
    (hl₁ : IsLineWithEnds (range (fun u : I => j (f ((1 - ↑u) * Real.pi)))) (j (f Real.pi)) (j y))
    (hl₂ : IsLineWithEnds (range (fun u : I => j (f (-((1 - ↑u) * Real.pi)))))
      (j (f Real.pi)) (j y))
    (hmeet : ∀ (s t : ↑I), (fun u : I => j (f ((1 - ↑u) * Real.pi))) s =
      (fun u : I => j (f (-((1 - ↑u) * Real.pi)))) t → s = 0 ∧ t = 0 ∨ s = 1 ∧ t = 1) :
    range (fun u : I => j (f ((1 - ↑u) * Real.pi))) ∩
      range (fun u : I => j (f (-((1 - ↑u) * Real.pi)))) = {j (f Real.pi), j y} := by
  let g₁ := fun u : I => j (f ((1 - ↑u) * Real.pi))
  let g₂ := fun u : I => j (f (-((1 - ↑u) * Real.pi)))
  ext z
  constructor
  · rintro ⟨⟨s, rfl⟩, ⟨t, ht⟩⟩
    rcases hmeet s t ht.symm with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact .inl (by rw [h1, hg0₁])
    · exact .inr (by rw [h1, hg1₁]; rfl)
  · rintro (rfl | rfl)
    · exact ⟨hl₁.left_mem, hl₂.left_mem⟩
    · exact ⟨hl₁.right_mem, hl₂.right_mem⟩

private theorem vertex_half_disc_boundary_equals_cuff_interval
    {S : Type}
    {T : Type}
    {j : S → T}
    {f : ℝ → S}
    {ε : ℝ}
    (hpi : 3 < Real.pi)
    (hε1 : ε < 1)
    (R : Set T)
    (ℓ : Set T)
    (eℓ : ℓ = j '' f '' Icc (-Real.pi) Real.pi ∩ R)
    (σ₁ : ℝ)
    (σ₂ : ℝ)
    (hσp₁ : 0 < σ₁)
    (hσp₂ : 0 < σ₂)
    (hin₁ : ∀ θ ∈ Icc 0 Real.pi, j (f θ) ∈ R ↔ θ ≤ σ₁)
    (hin₂ : ∀ θ ∈ Icc 0 Real.pi, j (f (-θ)) ∈ R ↔ θ ≤ σ₂)
    (hσε₁ : σ₁ < ε)
    (hσε₂ : σ₂ < ε) :
    ℓ = j '' f '' Icc (-σ₂) σ₁ := by
  rw [eℓ]
  ext z
  constructor
  · rintro ⟨⟨_, ⟨θ, hθ, rfl⟩, rfl⟩, h2⟩
    rcases le_total 0 θ with h0 | h0
    · exact ⟨_, ⟨θ, ⟨by linarith, (hin₁ θ ⟨h0, hθ.2⟩).mp h2⟩, rfl⟩, rfl⟩
    · have h3 : j (f (- -θ)) ∈ R := by rwa [neg_neg]
      have := (hin₂ (-θ) ⟨by linarith, by linarith [hθ.1]⟩).mp h3
      exact ⟨_, ⟨θ, ⟨by linarith, by linarith⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩
    refine ⟨⟨_, ⟨θ, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩, rfl⟩, rfl⟩, ?_⟩
    rcases le_total 0 θ with h0 | h0
    · exact (hin₁ θ ⟨h0, by linarith [hθ.2]⟩).mpr hθ.2
    · have := (hin₂ (-θ) ⟨by linarith, by linarith [hθ.1]⟩).mpr (by linarith [hθ.1])
      rwa [neg_neg] at this

/-- **The half disc at a vertex on a cuff.** -/
theorem exists_vertex_bd {j : S → T} {K : Set T} (hS : IsSurface S) (hT : IsClosedSurface T)
  (hj : IsClosedEmbedding j)
    (hK : IsClosed K) (hu : range j ∪ K = univ) (hi : range j ∩ K = j '' bd S) {Γ : Drawing T} {y :
      S} {f : ℝ → S} {ε : ℝ}
    (m : CuffMark f ε y) (hyV : j y ∈ Γ.V) {W : Set T} (hW : IsOpen W) (hyW : j y ∈ W)
    (hoff : Disjoint W (j '' (bd S \ f '' Ioo (-ε) ε))) (hCn : IsGammaNice Γ (j '' (f '' Icc
      (-Real.pi) Real.pi))) :
    ∃ R P σ₁ σ₂, IsStarDisc Γ (j y) R ∧ R ⊆ W ∧ IsClosedDisc P ∧ P ⊆ R ∧ P ⊆ range j ∧
      (∀ z ∈ R, z ∈ range j → z ∈ P) ∧
      (∀ z ∈ discBd R, z ∈ range j → z ∉ K → z ∈ discBd P) ∧ (∀ z ∈ discInt R, z ∈ range j → z ∉ K
        → z ∈ discInt P) ∧
      0 < σ₁ ∧ σ₁ < ε ∧ 0 < σ₂ ∧ σ₂ < ε ∧ P ∩ K = j '' (f '' Icc (-σ₂) σ₁) ∧ j '' (f '' Icc
        (-σ₂) σ₁) ⊆ discBd P ∧
      j '' (f '' Ioo (-σ₂) σ₁) ⊆ discInt R := by
  have ht2 : T2Space T := hT.2.1
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hε := m.pos
  have hε1 := m.lt
  have hyb : y ∈ bd S := m.zero ▸ m.onBd 0 ⟨by linarith, by linarith⟩
  obtain ⟨R, hR, hRW⟩ := exists_starDisc hT Γ hyV hW hyW
  have hRoff : ∀ x, x ∈ bd S → j x ∈ R → x ∈ f '' Ioo (-ε) ε := fun x hx h => by
    by_contra hn
    exact disjoint_left.mp hoff (hRW h) ⟨x, ⟨hx, hn⟩, rfl⟩
  -- The two halves of the cuff, as arcs that end at `y`.
  have hmap₁ : ∀ u : I, (1 - u.1) * Real.pi ∈ Ioc (-Real.pi) Real.pi ∧ 0 ≤ (1 - u.1) * Real.pi
    := fun u => by
    have h0 := u.2.1
    have h1 := u.2.2
    have h2 : 0 ≤ (1 - u.1) * Real.pi := mul_nonneg (by linarith) (by linarith)
    exact ⟨⟨by linarith, by nlinarith⟩, h2⟩
  let g₁ : I → T := fun u => j (f ((1 - u.1) * Real.pi))
  let g₂ : I → T := fun u => j (f (-((1 - u.1) * Real.pi)))
  have hc₁ : Continuous g₁ := hj.continuous.comp (m.cont.comp (by fun_prop))
  have hc₂ : Continuous g₂ := hj.continuous.comp (m.cont.comp (by fun_prop))
  have hinjR : ∀ {s t : ℝ}, s = t → (1 - s) * Real.pi = (1 - t) * Real.pi := fun h => by rw [h]
  have hval : ∀ {s t : I}, (1 - s.1) * Real.pi = (1 - t.1) * Real.pi → s = t := fun {s t} h => by
    have : 1 - s.1 = 1 - t.1 := mul_right_cancel₀ (by linarith) h
    exact Subtype.ext (by linarith)
  have hi₁ : Function.Injective g₁ := fun s t h => hval (m.inj (hmap₁ s).1 (hmap₁ t).1
    (hj.injective h))
  have hg0₁ : g₁ 0 = j (f Real.pi) := by simp [g₁]
  have hg1₁ : g₁ 1 = j y := by simp [g₁, m.zero]
  have hg0₂ : g₂ 0 = j (f Real.pi) := by simp [g₂, m.per]
  have hg1₂ : g₂ 1 = j y := by simp [g₂, m.zero]
  have hmap₂ : ∀ u : I, u ≠ 0 → -((1 - u.1) * Real.pi) ∈ Ioc (-Real.pi) Real.pi := fun u hu0 => by
    have h0 : 0 < u.1 := unitInterval.pos_iff_ne_zero.mpr hu0
    have h1 := u.2.2
    have h2 := (hmap₁ u).2
    exact ⟨by nlinarith, by linarith⟩
  have hi₂ : Function.Injective g₂ := fun s t h => by
    by_cases hs : s = 0 <;> by_cases ht : t = 0
    · rw [hs, ht]
    · rw [hs, hg0₂] at h
      have h3 := hj.injective h
      have h4 := m.inj ⟨by linarith, le_rfl⟩ (hmap₂ t ht) h3
      have h5 := (hmap₁ t).2
      linarith
    · rw [ht, hg0₂] at h
      have h3 := hj.injective h
      have h4 := m.inj (hmap₂ s hs) ⟨by linarith, le_rfl⟩ h3
      have h5 := (hmap₁ s).2
      linarith
    · have h4 := m.inj (hmap₂ s hs) (hmap₂ t ht) (hj.injective h)
      exact hval (by linarith)
  have ha₁ : IsArcMap g₁ := ⟨hc₁, hi₁⟩
  have ha₂ : IsArcMap g₂ := ⟨hc₂, hi₂⟩
  have hl₁ : IsLineWithEnds (range g₁) (j (f Real.pi)) (j y) := by
    have := ha₁.isLineWithEnds
    rwa [hg0₁, hg1₁] at this
  have hl₂ : IsLineWithEnds (range g₂) (j (f Real.pi)) (j y) := by
    have := ha₂.isLineWithEnds
    rwa [hg0₂, hg1₂] at this
  have hform₁ : ∀ θ ∈ Icc (0 : ℝ) Real.pi, ∃ u : I, (1 - u.1) * Real.pi = θ := fun θ hθ => by
    refine ⟨⟨1 - θ / Real.pi, ?_, ?_⟩, ?_⟩
    · have : θ / Real.pi ≤ 1 := (div_le_one (by linarith)).mpr hθ.2
      linarith
    · have : 0 ≤ θ / Real.pi := div_nonneg hθ.1 (by linarith)
      linarith
    · field_simp
      ring
  have hC : j '' (f '' Icc (-Real.pi) Real.pi) = range g₁ ∪ range g₂ := by
    exact cuff_image_eq_union_of_half_cuff_ranges (S := S) (T := T) (j := j) (f := f) (ε := ε) hpi
      hε hε1 hmap₁ hform₁
  have hmeet : ∀ s t, g₁ s = g₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := fun s t h => by
    by_cases ht : t = 0
    · refine .inl ⟨?_, ht⟩
      rw [ht, hg0₂, ← hg0₁] at h
      exact hi₁ h
    · have h4 := m.inj (hmap₁ s).1 (hmap₂ t ht) (hj.injective h)
      have h5 := (hmap₁ s).2
      have h6 := (hmap₁ t).2
      have h7 : (1 - s.1) * Real.pi = 0 := by linarith
      have h8 : (1 - t.1) * Real.pi = 0 := by linarith
      have h9 : ∀ u : I, (1 - u.1) * Real.pi = 0 → u = 1 := fun u hu => by
        have := (mul_eq_zero.mp hu).resolve_right Real.pi_ne_zero
        exact Subtype.ext (show (u : ℝ) = 1 by linarith)
      exact .inr ⟨h9 s h7, h9 t h8⟩
  have hm : range g₁ ∩ range g₂ = {j (f Real.pi), j y} := by
    exact half_cuff_ranges_intersect_at_endpoints (S := S) (T := T) (j := j) (y := y) (f := f)
      hg0₁ hg1₁ hl₁ hl₂ hmeet
  have hpiB : f Real.pi ∈ bd S := m.onBd _ ⟨by linarith, le_rfl⟩
  have hwR : j (f Real.pi) ∉ R := fun h => by
    obtain ⟨t, ht, e⟩ := hRoff _ hpiB h
    have := m.inj ⟨by linarith [ht.1], by linarith [ht.2]⟩ ⟨by linarith, le_rfl⟩ e
    linarith [ht.2]
  have hCc : IsClosed (j '' (f '' Icc (-Real.pi) Real.pi)) :=
    ((isCompact_Icc.image m.cont).image hj.continuous).isClosed
  have hR₁ : IsStarDisc Γ (g₁ 1) R := hg1₁ ▸ hR
  have hR₂ : IsStarDisc Γ (g₂ 1) R := hg1₂ ▸ hR
  obtain ⟨τ₁, h0₁, h1₁, hT₁, hb₁, ha₁'⟩ := exists_ray_param hT hR₁ ha₁
    (by rwa [hg0₁]) hCc hCn hC ha₂.isLineWithEnds.isCompact.isClosed
    (by rw [hm, hg0₁, hg1₁])
  obtain ⟨τ₂, h0₂, h1₂, hT₂, hb₂, ha₂'⟩ := exists_ray_param hT hR₂ ha₂ (by rwa [hg0₂]) hCc hCn
    (by rw [hC, union_comm])
    ha₁.isLineWithEnds.isCompact.isClosed (by rw [inter_comm, hm, hg0₂, hg1₂])
  have hf : frontier (range j) ∩ R = j '' (f '' Icc (-Real.pi) Real.pi) ∩ R := by
    rw [cap_frontier hT hj hK hu hi]
    ext z
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, h2⟩
      obtain ⟨t, ht, e⟩ := hRoff x hx h2
      exact ⟨⟨x, ⟨t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, e⟩, rfl⟩, h2⟩
    · rintro ⟨⟨_, ⟨t, ht, rfl⟩, rfl⟩, h2⟩
      exact ⟨⟨_, m.onBd t ht, rfl⟩, h2⟩
  obtain ⟨hin, hout⟩ := cap_limits hS hT hj hK hu hi hyb
  obtain ⟨s, t, ℓ, P, E, c, c', hl, hst, eℓ, dP, dE, hU, hI, lc, lc', huc, hic, bP, bE, hbd, hyℓ,
    hPB, hEB, -, -⟩ :=
    exists_half hT hR hl₁ hl₂ hC hm hwR hCc hCn hj.isClosed_range hf hin hout
  set σ₁ : ℝ := (1 - τ₁.1) * Real.pi with hσ₁
  set σ₂ : ℝ := (1 - τ₂.1) * Real.pi with hσ₂
  have hlt₁ : (τ₁ : ℝ) < 1 := h1₁
  have hlt₂ : (τ₂ : ℝ) < 1 := h1₂
  have hσp₁ : 0 < σ₁ := mul_pos (by linarith) (by linarith)
  have hσp₂ : 0 < σ₂ := mul_pos (by linarith) (by linarith)
  have hle : ∀ {a b : I}, (1 - a.1) * Real.pi ≤ (1 - b.1) * Real.pi ↔ b ≤ a := fun {a b} => by
    constructor
    · intro h
      have := le_of_mul_le_mul_right h (by linarith : (0 : ℝ) < Real.pi)
      exact Subtype.coe_le_coe.mp (by linarith)
    · intro h
      have h' : (b : ℝ) ≤ a := h
      exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hlts : ∀ {a b : I}, (1 - a.1) * Real.pi < (1 - b.1) * Real.pi ↔ b < a := fun {a b} => by
    rw [← not_le, ← not_le, hle]
  have hin₁ : ∀ θ ∈ Icc (0 : ℝ) Real.pi, j (f θ) ∈ R ↔ θ ≤ σ₁ := fun θ hθ => by
    obtain ⟨u, rfl⟩ := hform₁ θ hθ
    exact (hT₁ u).trans hle.symm
  have hin₂ : ∀ θ ∈ Icc (0 : ℝ) Real.pi, j (f (-θ)) ∈ R ↔ θ ≤ σ₂ := fun θ hθ => by
    obtain ⟨u, rfl⟩ := hform₁ θ hθ
    exact (hT₂ u).trans hle.symm
  have hσε₁ : σ₁ < ε := by
    have hmem : g₁ τ₁ ∈ R := (hT₁ τ₁).mpr le_rfl
    obtain ⟨t, ht, e⟩ := hRoff _ (m.onBd _ ⟨by linarith [(hmap₁ τ₁).2], (hmap₁ τ₁).1.2⟩) hmem
    have := m.inj ⟨by linarith [ht.1], by linarith [ht.2]⟩ (hmap₁ τ₁).1 e
    linarith [ht.2]
  have hσε₂ : σ₂ < ε := by
    have hmem : g₂ τ₂ ∈ R := (hT₂ τ₂).mpr le_rfl
    obtain ⟨t, ht, e⟩ := hRoff _ (m.onBd _ ⟨by linarith [(hmap₁ τ₂).1.2], by linarith [(hmap₁
      τ₂).2]⟩) hmem
    have := m.inj ⟨by linarith [ht.1], by linarith [ht.2]⟩ (hmap₂ τ₂ h0₂.ne') e
    linarith [ht.1]
  have hℓ : ℓ = j '' (f '' Icc (-σ₂) σ₁) := by
    exact vertex_half_disc_boundary_equals_cuff_interval (S := S) (T := T) (j := j) (f := f) (ε :=
      ε) hpi hε1 R ℓ eℓ σ₁ σ₂ hσp₁ hσp₂ hin₁ hin₂ hσε₁ hσε₂
  have hℓP : ℓ ⊆ P := fun x hx => (hI ▸ hx : x ∈ P ∩ E).1
  have hoffE : ∀ z ∈ E, z ∈ range j → z ∈ ℓ := fun z h1 h2 => by
    by_contra h3
    exact disjoint_left.mp hEB ⟨h1, h3⟩ h2
  have hℓK : ℓ ⊆ K := fun z hz => by
    have h1 : z ∈ j '' (f '' Icc (-Real.pi) Real.pi) ∩ R := eℓ ▸ hz
    obtain ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩ := h1.1
    have hjb : j (f θ) ∈ range j ∩ K := hi ▸ mem_image_of_mem j (m.onBd θ hθ)
    exact hjb.2
  have hcbd : c ⊆ discBd R := huc ▸ subset_union_left
  have hsplit : ∀ z ∈ discBd R, z ∈ range j → z ∉ K → z ∈ c := fun z h1 h2 h3 => by
    have h4 : z ∈ c ∪ c' := huc ▸ h1
    refine h4.resolve_right fun h5 => h3 (hℓK (hoffE z ?_ h2))
    exact GM11.discBd_subset E (bE ▸ Or.inl h5)
  have hRP : ∀ z ∈ R, z ∈ range j → z ∈ P := fun z h1 h2 => by
    have h3 : z ∈ P ∪ E := hU ▸ h1
    rcases h3 with h3 | h3
    · exact h3
    · exact hℓP (hoffE z h3 h2)
  refine ⟨R, P, σ₁, σ₂, hR, hRW, dP, fun x hx => hU ▸ Or.inl hx, hPB, hRP, fun z h1 h2 h3 => ?_,
    fun z h1 h2 h3 => ?_, hσp₁, hσε₁, hσp₂, hσε₂,
    ?_, ?_, ?_⟩
  · exact bP ▸ Or.inl (hsplit z h1 h2 h3)
  · refine ⟨hRP z h1.1 h2, fun h4 => ?_⟩
    rw [bP] at h4
    rcases h4 with h4 | h4
    · exact h1.2 (hcbd h4)
    · exact h3 (hℓK h4)
  · rw [← hℓ]
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      have hzr : z ∈ range j ∩ K := ⟨hPB h1, h2⟩
      rw [hi] at hzr
      obtain ⟨x, hx, rfl⟩ := hzr
      have hxR : j x ∈ R := hU ▸ Or.inl h1
      obtain ⟨t, ht, e⟩ := hRoff x hx hxR
      rw [eℓ]
      exact ⟨⟨x, ⟨t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, e⟩, rfl⟩, hxR⟩
    · exact fun h => ⟨hℓP h, hℓK h⟩
  · rw [← hℓ, bP]
    exact subset_union_right
  · rintro _ ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩
    rcases le_total 0 θ with h0 | h0
    · obtain ⟨u, hu⟩ := hform₁ θ ⟨h0, by linarith [hθ.2]⟩
      have := ha₁' u (hlts.mp (by rw [hu]; exact hθ.2))
      simpa only [g₁, hu] using this
    · obtain ⟨u, hu⟩ := hform₁ (-θ) ⟨by linarith, by linarith [hθ.1]⟩
      have := ha₂' u (hlts.mp (by rw [hu]; linarith [hθ.1]))
      simpa only [g₂, hu, neg_neg] using this

/-- The part of `bd(Σ)` off a piece of the cuff is closed. -/
theorem CuffMark.isClosed_rest' {f : ℝ → S} {ε : ℝ} {y : S} [T2Space S]
  (m : CuffMark f ε y) {c d : ℝ} (hc : -Real.pi ≤ c) (hd : d < Real.pi)
    (hcd : c < d) : IsClosed (bd S \ f '' Ioo c d) := by
  have hsub : ∀ {t}, t ∈ Ioo c d → t ∈ Ioc (-Real.pi) Real.pi := fun ht
    => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have heq : bd S \ f '' Ioo c d = (bd S \ f '' Icc (-Real.pi) Real.pi) ∪ f '' Icc
    (-Real.pi) c ∪ f '' Icc d Real.pi := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h3 : x ∈ f '' Icc (-Real.pi) Real.pi
      · obtain ⟨t, ht, rfl⟩ := h3
        rcases le_total t c with h4 | h4
        · exact .inl (.inr ⟨t, ⟨ht.1, h4⟩, rfl⟩)
        · rcases le_total d t with h5 | h5
          · exact .inr ⟨t, ⟨h5, ht.2⟩, rfl⟩
          · rcases h4.eq_or_lt with h6 | h6
            · exact .inl (.inr ⟨t, ⟨ht.1, h6.ge⟩, rfl⟩)
            · rcases h5.eq_or_lt with h7 | h7
              · exact .inr ⟨t, ⟨h7.ge, ht.2⟩, rfl⟩
              · exact (h2 ⟨t, ⟨h6, h7⟩, rfl⟩).elim
      · exact .inl (.inl ⟨h1, h3⟩)
    · rintro ((h | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩)
      · refine ⟨h.1, ?_⟩
        rintro ⟨t, ht, rfl⟩
        exact h.2 ⟨t, ⟨(hsub ht).1.le, (hsub ht).2⟩, rfl⟩
      · refine ⟨m.onBd t ⟨ht.1, by linarith [ht.2, Real.pi_pos]⟩, ?_⟩
        rintro ⟨r, hr, e⟩
        rcases ht.1.eq_or_lt with h0 | h0
        · rw [← h0, m.per] at e
          have := m.inj (hsub hr) ⟨by linarith [Real.pi_pos], le_rfl⟩ e
          linarith [hr.2]
        · have := m.inj (hsub hr) ⟨h0, by linarith [ht.2]⟩ e
          linarith [hr.1, ht.2]
      · refine ⟨m.onBd t ⟨by linarith [ht.1], ht.2⟩, ?_⟩
        rintro ⟨r, hr, e⟩
        have := m.inj (hsub hr) ⟨by linarith [ht.1], ht.2⟩ e
        linarith [hr.2, ht.1]
  rw [heq]
  exact (m.rest.union (isCompact_Icc.image m.cont).isClosed).union (isCompact_Icc.image
    m.cont).isClosed

theorem CuffMark.isClosed_rest {f : ℝ → S} {ε : ℝ} {y : S} [T2Space S]
  (m : CuffMark f ε y) : IsClosed (bd S \ f '' Ioo (-ε) ε) :=
  m.isClosed_rest' (by linarith [m.lt, Real.pi_gt_three]) (by linarith [m.lt, Real.pi_gt_three])
    (by linarith [m.pos])

/-- A forest has no loops. -/
theorem forest_edge_line {H : Drawing S} (hf : IsGraphForest H.toGraph) {e : Set S} (he : e ∈ H.E) :
    ∃ u v, u ≠ v ∧ u ∈ H.V ∧ v ∈ H.V ∧ closure e ∩ H.V = {u, v} ∧ IsLineWithEnds (closure e) u v
      := by
  rcases H.edge_cond e he with ⟨u, v, huv, hcap, hl⟩ | ⟨u, hcap, -⟩
  · have hu : u ∈ closure e ∩ H.V := by rw [hcap]; exact .inl rfl
    have hv : v ∈ closure e ∩ H.V := by rw [hcap]; exact .inr rfl
    exact ⟨u, v, huv, hu.2, hv.2, hcap, hl⟩
  · exfalso
    have hu : u ∈ H.V := (hcap ▸ rfl : u ∈ closure e ∩ H.V).2
    have hl : H.toGraph.IsLink e u u := ⟨he, hu, hu, by simpa using hcap⟩
    have := hf u (.cons hl (.nil hu)) ⟨by simp [GraphWalk.support], by simp [GraphWalk.edges]⟩
    simp [GraphWalk.length, GraphWalk.edges] at this

/-- A walk along edges in `E` gives a walk of the drawing. -/
theorem exists_walk_of_reach {H : Drawing S} {a b : H.E → H.V} (hl : ∀ i, H.toGraph.IsLink i.1
  (a i).1 (b i).1) {E : Set H.E}
    {x y : H.V} (h : Reach a b E x y) : ∃ W : GraphWalk H.toGraph x.1 y.1, ∀ e ∈ W.edges, ∃ k ∈ E,
      k.1 = e := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨.nil y.2, by simp [GraphWalk.edges]⟩
  | @head x z hs _ ih =>
    obtain ⟨W, hW⟩ := ih
    obtain ⟨k, hk, h1⟩ := hs
    have hlink : H.toGraph.IsLink k.1 x.1 z.1 := by
      rcases h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [← e1, ← e2]
        exact hl k
      · rw [← e1, ← e2]
        exact (hl k).symm
    refine ⟨.cons hlink W, fun e he => ?_⟩
    simp only [GraphWalk.edges, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨k, hk, rfl⟩
    · exact hW e he

/-- In a forest, the ends of an edge are not joined by the other edges. -/
theorem forest_no_reach {H : Drawing S} (hf : IsGraphForest H.toGraph) {a b : H.E → H.V}
    (hl : ∀ i, H.toGraph.IsLink i.1 (a i).1 (b i).1) (hne : ∀ i, (a i).1 ≠ (b i).1) (E : Set H.E)
      (i : H.E) (hi : i ∉ E) :
    ¬ Reach a b E (a i) (b i) := by
  classical
  intro hr
  obtain ⟨W, hW⟩ := exists_walk_of_reach hl hr
  obtain ⟨W', hs, -, hed⟩ := GraphWalk.exists_isSimple W
  let W₂ : GraphWalk H.toGraph (b i).1 (a i).1 := .cons (hl i).symm (.nil (a i).2)
  have hs₂ : W₂.IsSimple := by
    simp [W₂, GraphWalk.IsSimple, GraphWalk.support, (hne i).symm]
  have hc := GraphWalk.isSimpleClosed_append hs hs₂ (fun x _ hx => by
    simp only [W₂, GraphWalk.support, List.mem_cons, List.not_mem_nil, or_false] at hx
    exact hx.symm) (fun e he hmem => by
    simp only [W₂, GraphWalk.edges, List.mem_cons, List.not_mem_nil, or_false] at hmem
    obtain ⟨k, hk, e1⟩ := hW e (hed e he)
    exact hi ((Subtype.ext (e1.trans hmem) : k = i) ▸ hk))
  have := hf _ _ hc
  rw [GraphWalk.length_append] at this
  simp [W₂, GraphWalk.length, GraphWalk.edges] at this

private theorem exists_thick_vertex_discs
    {S : Type}
    [TopologicalSpace S]
    (hS : IsSurface S)
    {H : Drawing S}
    {f : S → ℝ → S}
    {ε : S → ℝ}
    (hm : ∀ y ∈ H.V ∩ bd S, CuffMark (f y) (ε y) y)
    (T : Type)
    [TopologicalSpace T]
    (j : S → T)
    (K : Set T)
    (hT : IsClosedSurface T)
    (hj : IsClosedEmbedding j)
    (hK : IsClosed K)
    (hu : range j ∪ K = univ)
    (hi : range j ∩ K = j '' bd S)
    (Γ : GM19.Drawing T)
    (hHV : ∀ v ∈ H.V, j v ∈ Γ.V)
    (hoffK : ∀ z ∉ K, z ∈ range j)
    (hCnice : ∀ y ∈ H.V ∩ bd S, IsGammaNice Γ (j '' f y '' Icc (-Real.pi) Real.pi))
    (W : S → Set T)
    (hWo : ∀ v ∈ H.V, IsOpen (W v))
    (hWm : ∀ v ∈ H.V, j v ∈ W v)
    (hWboundary : ∀ v ∈ bd S, Disjoint (W v) (j '' (bd S \ f v '' Ioo (-ε v) (ε v))))
    (hWinterior : ∀ v ∉ bd S, Disjoint (W v) K) :
    ∀ v : H.V, ∃ R P s₁ s₂, IsStarDisc Γ (j v.1) R ∧ R ⊆ W v.1 ∧ IsClosedDisc P ∧ P ⊆ R ∧
      P ⊆ range j ∧ (∀ z ∈ R, z ∈ range j → z ∈ P) ∧
      (∀ z ∈ discBd R, z ∈ range j → z ∉ K → z ∈ discBd P) ∧
      (∀ z ∈ discInt R, z ∈ range j → z ∉ K → z ∈ discInt P) ∧
      (v.1 ∈ bd S → 0 < s₁ ∧ s₁ < ε v.1 ∧ 0 < s₂ ∧ s₂ < ε v.1 ∧
        P ∩ K = j '' f v.1 '' Icc (-s₂) s₁ ∧
        j '' f v.1 '' Icc (-s₂) s₁ ⊆ discBd P ∧ j '' f v.1 '' Ioo (-s₂) s₁ ⊆ discInt R) ∧
      (v.1 ∉ bd S → P ∩ K = ∅) := by
  classical
  rintro ⟨v, hv⟩
  by_cases hb : v ∈ bd S
  · have hoff := hWboundary v hb
    obtain ⟨R, P, s₁, s₂, h1, h2, h3, h4, h5, h6, h7, h8, a1, a2, a3, a4, a5, a6, a7⟩ :=
      exists_vertex_bd hS hT hj hK hu hi (hm v ⟨hv, hb⟩) (hHV v hv) (hWo v hv) (hWm v hv) hoff
        (hCnice v ⟨hv, hb⟩)
    exact ⟨R, P, s₁, s₂, h1, h2, h3, h4, h5, h6, h7, h8, fun _ => ⟨a1, a2, a3, a4, a5, a6, a7⟩,
      fun h => (h hb).elim⟩
  · obtain ⟨R, hR, hRW⟩ := exists_starDisc hT Γ (hHV v hv) (hWo v hv) (hWm v hv)
    have hRK : ∀ z ∈ R, z ∉ K := fun z hz => disjoint_left.mp (hWinterior v hb) (hRW hz)
    exact ⟨R, R, 0, 0, hR, hRW, hR.disc, subset_rfl, fun z hz => hoffK z (hRK z hz),
      fun z hz _ => hz, fun z hz _ _ => hz,
      fun z hz _ _ => hz, fun h => (hb h).elim, fun _ => by
        ext z
        simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
        exact fun hz => hRK z hz⟩

private theorem edge_middle_meets_vertex_discs_only_at_ends
    {S : Type}
    [TopologicalSpace S]
    {H : Drawing S}
    (T : Type)
    (j : S → T)
    (W : S → Set T)
    (hWe : ∀ v ∈ H.V, ∀ e ∈ H.E, v ∉ closure e → Disjoint (W v) (j '' closure e))
    (R : ↑H.V → Set T)
    (P : ↑H.V → Set T)
    (hRW : ∀ (v : ↑H.V), R v ⊆ W ↑v)
    (hPR : ∀ (v : ↑H.V), P v ⊆ R v)
    (a : ↑H.E → ↑H.V)
    (b : ↑H.E → ↑H.V)
    (hcap : ∀ i : H.E, closure i.1 ∩ H.V = {(a i).1, (b i).1})
    (p : ↑H.E → T)
    (q : ↑H.E → T)
    (M : ↑H.E → Set T)
    (hMa : ∀ (i : ↑H.E), M i ∩ R (a i) = {p i})
    (hMb : ∀ (i : ↑H.E), M i ∩ R (b i) = {q i})
    (hML : ∀ (i : ↑H.E), M i ⊆ j '' closure ↑i) :
    ∀ (i : ↑H.E) (v : ↑H.V), M i ∩ P v ⊆ {p i, q i} := by
  intro i v z hz
  by_cases h1 : v = a i
  · have : z ∈ M i ∩ R (a i) := ⟨hz.1, hPR _ (h1 ▸ hz.2)⟩
    rw [hMa i] at this
    exact .inl this
  by_cases h2 : v = b i
  · have : z ∈ M i ∩ R (b i) := ⟨hz.1, hPR _ (h2 ▸ hz.2)⟩
    rw [hMb i] at this
    exact .inr this
  · have hv : v.1 ∉ closure i.1 := fun h => by
      have : v.1 ∈ closure i.1 ∩ H.V := ⟨h, v.2⟩
      rw [hcap i] at this
      rcases this with e | e
      · exact h1 (Subtype.ext e)
      · exact h2 (Subtype.ext e)
    exact (disjoint_left.mp (hWe v.1 v.2 i.1 i.2 hv) (hRW v (hPR v hz.2)) (hML i hz.1)).elim

private theorem forest_edge_closure_is_nice_in_capped_drawing
    {S : Type}
    [TopologicalSpace S]
    {H : Drawing S}
    [T2Space S]
    (T : Type)
    [TopologicalSpace T]
    (j : S → T)
    (hj : IsClosedEmbedding j)
    (G₀ : Drawing S)
    (hG₀U : G₀.U = H.U ∪ bd S)
    (Γ : GM19.Drawing T)
    (hΓU : Γ.U = j '' G₀.U)
    (hbc : IsClosed (bd S))
    (hHV : ∀ v ∈ H.V, j v ∈ Γ.V)
    (hprop' : ∀ x ∈ H.U, x ∈ bd S → x ∈ H.V)
    (hcle : ∀ e ∈ H.E, closure e ⊆ e ∪ H.V)
    (hclU : ∀ e ∈ H.E, closure e ⊆ H.U)
    (hclc : ∀ e ∈ H.E, IsClosed (j '' closure e))
    (e : Set S)
    (he : e ∈ H.E) :
    IsGammaNice Γ (j '' closure e) := by
  let Y₀ : Set S := H.V ∪ bd S ∪ ⋃ g ∈ H.E \ {e}, closure g
  have hY₀ : IsClosed Y₀ := (H.finite_V.isClosed.union hbc).union
    ((H.finite_edges.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure)
  refine nice_of_cover (hclc e he) (hj.isClosedMap _ hY₀) ?_ ?_ ?_
  · rw [hΓU, hG₀U]
    rintro _ ⟨x, hx | hx, rfl⟩
    · by_cases hxV : x ∈ H.V
      · exact .inr ⟨x, .inl (.inl hxV), rfl⟩
      · obtain ⟨g, hg, hxg⟩ := H.exists_edge_of_mem hx hxV
        by_cases hge : g = e
        · exact .inl ⟨x, subset_closure (hge ▸ hxg), rfl⟩
        · exact .inr ⟨x, .inr (mem_iUnion₂.mpr ⟨g, ⟨hg, hge⟩, subset_closure hxg⟩), rfl⟩
    · exact .inr ⟨x, .inl (.inr hx), rfl⟩
  · rw [hΓU, hG₀U]
    exact image_mono ((hclU e he).trans subset_union_left)
  · rintro _ ⟨⟨x, hx, rfl⟩, ⟨x', hx', e'⟩⟩
    have hxx : x' = x := hj.injective e'
    subst hxx
    rcases hx' with (h1 | h1) | h1
    · exact hHV _ h1
    · exact hHV _ (hprop' _ (hclU e he hx) h1)
    · obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h1
      rcases hcle e he hx with h2 | h2
      · rcases hcle g hg.1 hxg with h3 | h3
        · exact (hg.2 (H.edge_eq_of_mem hg.1 he h3 h2)).elim
        · exact hHV _ h3
      · exact hHV _ h2

private theorem cuff_image_is_nice_in_capped_drawing
    {S : Type}
    [TopologicalSpace S]
    {H : Drawing S}
    {f : S → ℝ → S}
    {ε : S → ℝ}
    (hm : ∀ y ∈ H.V ∩ bd S, CuffMark (f y) (ε y) y)
    (T : Type)
    [TopologicalSpace T]
    (j : S → T)
    (hj : IsClosedEmbedding j)
    [T2Space T]
    (G₀ : Drawing S)
    (hG₀U : G₀.U = H.U ∪ bd S)
    (Γ : GM19.Drawing T)
    (hΓU : Γ.U = j '' G₀.U)
    (hHV : ∀ v ∈ H.V, j v ∈ Γ.V)
    (hprop' : ∀ x ∈ H.U, x ∈ bd S → x ∈ H.V) :
    ∀ y ∈ H.V ∩ bd S, IsGammaNice Γ (j '' f y '' Icc (-Real.pi) Real.pi) := by
  intro y hy
  have m := hm y hy
  have hCc : IsClosed (j '' (f y '' Icc (-Real.pi) Real.pi)) := ((isCompact_Icc.image
    m.cont).image hj.continuous).isClosed
  have hCb : f y '' Icc (-Real.pi) Real.pi ⊆ bd S := by
    rintro _ ⟨t, ht, rfl⟩
    exact m.onBd t ht
  refine nice_of_cover hCc (hj.isClosedMap _ (H.isClosed_U.union m.rest)) ?_ ?_ ?_
  · rw [hΓU, hG₀U]
    rintro _ ⟨x, hx | hx, rfl⟩
    · exact .inr ⟨x, .inl hx, rfl⟩
    · by_cases h1 : x ∈ f y '' Icc (-Real.pi) Real.pi
      · exact .inl ⟨x, h1, rfl⟩
      · exact .inr ⟨x, .inr ⟨hx, h1⟩, rfl⟩
  · rw [hΓU, hG₀U]
    exact image_mono (hCb.trans subset_union_right)
  · rintro _ ⟨⟨x, hx, rfl⟩, ⟨x', hx', e'⟩⟩
    have hxx : x' = x := hj.injective e'
    subst hxx
    rcases hx' with h1 | h1
    · exact hHV _ (hprop' _ h1 (hCb hx))
    · exact (h1.2 hx).elim

private theorem thick_forest_disc_contains_incident_edge
    {S : Type}
    [TopologicalSpace S]
    {H : Drawing S}
    (T : Type)
    [TopologicalSpace T]
    (j : S → T)
    (R : ↑H.V → Set T)
    (P : ↑H.V → Set T)
    (hRP : ∀ (v : ↑H.V), ∀ z ∈ R v, z ∈ range j → z ∈ P v)
    (a : ↑H.E → ↑H.V)
    (b : ↑H.E → ↑H.V)
    (hcap : ∀ i : H.E, closure i.1 ∩ H.V = {(a i).1, (b i).1})
    (M : ↑H.E → Set T)
    (ρa : ↑H.E → Set T)
    (ρb : ↑H.E → Set T)
    (hLeq : ∀ (i : ↑H.E), j '' closure ↑i = ρa i ∪ M i ∪ ρb i)
    (hρa : ∀ (i : ↑H.E), ρa i = j '' closure ↑i ∩ R (a i))
    (hρb : ∀ (i : ↑H.E), ρb i = j '' closure ↑i ∩ R (b i))
    (C : ↑H.V → Set T)
    (hC4 : ∀ (i : ↑H.E), M i ⊆ discInt (C (a i)) ∧ C (a i) = C (b i))
    (hC5 : ∀ (v : ↑H.V), P v ⊆ C v ∧ discInt (P v) ⊆ discInt (C v)) :
    ∀ (i : H.E) (u : H.V), u.1 ∈ closure i.1 → j '' closure i.1 ⊆ C u := by
  intro i u hu z hz
  have hzr : z ∈ range j := ⟨_, hz.choose_spec.2⟩
  have hab2 := (hC4 i).2
  have h2 : M i ⊆ C (a i) := fun w hw => ((hC4 i).1 hw).1
  have hbig : z ∈ C (a i) := by
    rw [hLeq i] at hz
    rcases hz with (h | h) | h
    · rw [hρa i] at h
      exact (hC5 _).1 (hRP _ _ h.2 hzr)
    · exact h2 h
    · rw [hρb i] at h
      rw [hab2]
      exact (hC5 _).1 (hRP _ _ h.2 hzr)
  have : u.1 ∈ closure i.1 ∩ H.V := ⟨hu, u.2⟩
  rw [hcap i] at this
  rcases this with e | e
  · rwa [show u = a i from Subtype.ext e]
  · rwa [show u = b i from Subtype.ext e, ← hab2]

private theorem thick_forest_contains_interior_points_in_open_discs
    {S : Type}
    [TopologicalSpace S]
    {H : Drawing S}
    (T : Type)
    [TopologicalSpace T]
    (j : S → T)
    (K : Set T)
    (Γ : GM19.Drawing T)
    (hKb : ∀ (x : S), j x ∈ K → x ∈ bd S)
    (R : ↑H.V → Set T)
    (P : ↑H.V → Set T)
    (hR : ∀ (v : ↑H.V), IsStarDisc Γ (j ↑v) (R v))
    (hPint : ∀ (v : ↑H.V), ∀ z ∈ discInt (R v), z ∈ range j → z ∉ K → z ∈ discInt (P v))
    (a : ↑H.E → ↑H.V)
    (b : ↑H.E → ↑H.V)
    (p : ↑H.E → T)
    (q : ↑H.E → T)
    (M : ↑H.E → Set T)
    (ρa : ↑H.E → Set T)
    (ρb : ↑H.E → Set T)
    (hLeq : ∀ (i : ↑H.E), j '' closure ↑i = ρa i ∪ M i ∪ ρb i)
    (hρai : ∀ (i : ↑H.E), ρa i \ {p i} ⊆ discInt (R (a i)))
    (hρbi : ∀ (i : ↑H.E), ρb i \ {q i} ⊆ discInt (R (b i)))
    (hpM : ∀ (i : ↑H.E), p i ∈ M i)
    (hqM : ∀ (i : ↑H.E), q i ∈ M i)
    (C : ↑H.V → Set T)
    (hC4 : ∀ (i : ↑H.E), M i ⊆ discInt (C (a i)) ∧ C (a i) = C (b i))
    (hC5 : ∀ (v : ↑H.V), P v ⊆ C v ∧ discInt (P v) ⊆ discInt (C v)) :
    ∀ z ∈ H.U, z ∉ bd S → ∃ w, j z ∈ discInt (C w) := by
  intro z hz hzb
  have hzK : j z ∉ K := fun h => hzb (hKb z h)
  have hmemP : ∀ w, j z ∈ discInt (R w) → j z ∈ discInt (C w) := fun w h => (hC5 w).2
    (hPint w _ h ⟨z, rfl⟩ hzK)
  by_cases hzV : z ∈ H.V
  · exact ⟨⟨z, hzV⟩, hmemP _ (hR ⟨z, hzV⟩).mem⟩
  · obtain ⟨e, he, hze⟩ := H.exists_edge_of_mem hz hzV
    let i : H.E := ⟨e, he⟩
    have h1 : j z ∈ j '' closure i.1 := ⟨z, subset_closure hze, rfl⟩
    rw [hLeq i] at h1
    rcases h1 with (h | h) | h
    · by_cases hp : j z = p i
      · exact ⟨a i, (hC4 i).1 (hp ▸ hpM i)⟩
      · exact ⟨a i, hmemP _ (hρai i ⟨h, hp⟩)⟩
    · exact ⟨a i, (hC4 i).1 h⟩
    · by_cases hq : j z = q i
      · exact ⟨a i, (hC4 i).1 (hq ▸ hqM i)⟩
      · exact ⟨b i, hmemP _ (hρbi i ⟨h, hq⟩)⟩

private theorem forest_thickening_pulls_back_from_capped_surface
    {S : Type}
    [TopologicalSpace S]
    {H : Drawing S}
    {f : S → ℝ → S}
    {ε : S → ℝ}
    (hm : ∀ y ∈ H.V ∩ bd S, CuffMark (f y) (ε y) y)
    (T : Type)
    [TopologicalSpace T]
    (j : S → T)
    (K : Set T)
    (hj : IsClosedEmbedding j)
    (hman : ∀ (x : T), IsManifoldPoint x)
    (Γ : GM19.Drawing T)
    (hbK : ∀ x ∈ bd S, j x ∈ K)
    (hKb : ∀ (x : S), j x ∈ K → x ∈ bd S)
    (hprop' : ∀ x ∈ H.U, x ∈ bd S → x ∈ H.V)
    (R : ↑H.V → Set T)
    (P : ↑H.V → Set T)
    (s₁ : ↑H.V → ℝ)
    (s₂ : ↑H.V → ℝ)
    (hR : ∀ (v : ↑H.V), IsStarDisc Γ (j ↑v) (R v))
    (hRP : ∀ (v : ↑H.V), ∀ z ∈ R v, z ∈ range j → z ∈ P v)
    (hPint : ∀ (v : ↑H.V), ∀ z ∈ discInt (R v), z ∈ range j → z ∉ K → z ∈ discInt (P v))
    (hPb : ∀ (v : ↑H.V), ↑v ∈ bd S → 0 < s₁ v ∧ s₁ v < ε ↑v ∧ 0 < s₂ v ∧ s₂ v < ε ↑v ∧ P v ∩ K = j
      '' f ↑v '' Icc (-s₂ v) (s₁ v) ∧ j '' f ↑v '' Icc (-s₂ v) (s₁ v) ⊆ discBd (P v) ∧ j '' f ↑v
      '' Ioo (-s₂ v) (s₁ v) ⊆ discInt (R v))
    (hPi : ∀ (v : ↑H.V), ↑v ∉ bd S → P v ∩ K = ∅)
    (a : ↑H.E → ↑H.V)
    (b : ↑H.E → ↑H.V)
    (hlink : ∀ (i : ↑H.E), H.toGraph.IsLink ↑i ↑(a i) ↑(b i))
    (C : ↑H.V → Set T)
    (hC1 : ∀ (v : ↑H.V), IsClosedDisc (C v))
    (hC2 : ∀ (u v : ↑H.V), C u = C v → Reach a b univ u v)
    (hC3 : ∀ (u v : ↑H.V), C u ≠ C v → Disjoint (C u) (C v))
    (hC5 : ∀ (v : ↑H.V), P v ⊆ C v ∧ discInt (P v) ⊆ discInt (C v))
    (hC6 : ∀ (v : ↑H.V), C v ∩ K ⊆ ⋃ w, P w)
    (hC7 : ∀ (v : ↑H.V), discBd (P v) ∩ K ⊆ discBd (C v))
    (hCr : ∀ (v : ↑H.V), C v ⊆ range j)
    (hpre : ∀ (v : ↑H.V), IsClosedDisc (j ⁻¹' C v) ∧ discBd (j ⁻¹' C v) = j ⁻¹' discBd (C v))
    (hmeet : ∀ {u v : ↑H.V} {z : T}, z ∈ C u → z ∈ C v → C u = C v)
    (hline : ∀ (i : H.E) (u : H.V), u.1 ∈ closure i.1 → j '' closure i.1 ⊆ C u)
    (hint : ∀ z ∈ H.U, z ∉ bd S → ∃ w, j z ∈ discInt (C w)) :
    ∃ (c : S → Set S) (σ₁ σ₂ : S → ℝ), (∀ v ∈ H.V, IsClosedDisc (c v)) ∧
      (∀ u ∈ H.V, ∀ v ∈ H.V, c u = c v → Nonempty (GraphWalk H.toGraph u v)) ∧
      (∀ u ∈ H.V, ∀ v ∈ H.V, c u ≠ c v → Disjoint (c u) (c v)) ∧
      (∀ e ∈ H.E, ∀ u ∈ H.V, u ∈ closure e → closure e ⊆ c u) ∧ (∀ v ∈ H.V, v ∈ c v) ∧
      (∀ v ∈ H.V, ∀ z ∈ H.U, z ∈ discBd (c v) → z ∈ H.V ∩ bd S) ∧ (∀ v ∈ H.V, IsOpen (discInt
        (c v))) ∧
      (∀ y ∈ H.V ∩ bd S, 0 < σ₁ y ∧ σ₁ y < ε y ∧ 0 < σ₂ y ∧ σ₂ y < ε y ∧ f y '' Icc (-σ₂ y)
        (σ₁ y) ⊆ discBd (c y) ∧
        ∃ O, IsOpen O ∧ f y '' Ioo (-σ₂ y) (σ₁ y) ⊆ O ∧ O ⊆ c y ∧ O \ bd S ⊆ discInt (c y)) ∧
      ∀ v ∈ H.V, c v ∩ bd S ⊆ ⋃ y ∈ H.V ∩ bd S, f y '' Icc (-σ₂ y) (σ₁ y) := by
  classical
  let c : S → Set S := fun v => if h : v ∈ H.V then j ⁻¹' C ⟨v, h⟩ else ∅
  have hc : ∀ v : H.V, c v.1 = j ⁻¹' C v := fun v => by simp [c, v.2]
  let σ₁ : S → ℝ := fun v => if h : v ∈ H.V then s₁ ⟨v, h⟩ else 0
  let σ₂ : S → ℝ := fun v => if h : v ∈ H.V then s₂ ⟨v, h⟩ else 0
  have hs1 : ∀ v : H.V, σ₁ v.1 = s₁ v := fun v => by simp [σ₁, v.2]
  have hs2 : ∀ v : H.V, σ₂ v.1 = s₂ v := fun v => by simp [σ₂, v.2]
  have himg : ∀ {A B : Set T}, A ⊆ range j → B ⊆ range j → j ⁻¹' A = j ⁻¹' B → A = B
    := fun {A B} hA hB h => by
    rw [← image_preimage_eq_of_subset hA, ← image_preimage_eq_of_subset hB, h]
  refine ⟨c, σ₁, σ₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [hc ⟨v, hv⟩]
    exact (hpre _).1
  · intro u hu v hv h
    rw [hc ⟨u, hu⟩, hc ⟨v, hv⟩] at h
    obtain ⟨W, -⟩ := exists_walk_of_reach hlink (hC2 ⟨u, hu⟩ ⟨v, hv⟩ (himg (hCr _) (hCr _) h))
    exact ⟨W⟩
  · intro u hu v hv h
    rw [hc ⟨u, hu⟩, hc ⟨v, hv⟩] at h ⊢
    exact (hC3 ⟨u, hu⟩ ⟨v, hv⟩ fun e => h (by rw [e])).preimage j
  · intro e he u hu hue x hx
    rw [hc ⟨u, hu⟩]
    exact hline ⟨e, he⟩ ⟨u, hu⟩ hue ⟨x, hx, rfl⟩
  · intro v hv
    rw [hc ⟨v, hv⟩]
    exact (hC5 _).1 (hRP ⟨v, hv⟩ _ (hR ⟨v, hv⟩).mem.1 ⟨v, rfl⟩)
  · intro v hv z hz h
    by_cases hzb : z ∈ bd S
    · exact ⟨hprop' z hz hzb, hzb⟩
    · exfalso
      rw [hc ⟨v, hv⟩, (hpre _).2] at h
      obtain ⟨w, hw⟩ := hint z hz hzb
      have h1 : C w = C ⟨v, hv⟩ := hmeet hw.1 (GM11.discBd_subset _ h)
      exact (h1 ▸ hw).2 h
  · intro v hv
    have h1 : discInt (c v) = j ⁻¹' discInt (C ⟨v, hv⟩) := by
      unfold discInt
      rw [hc ⟨v, hv⟩, (hpre _).2]
      rfl
    rw [h1]
    exact ((hC1 _).isOpen_discInt hman).preimage hj.continuous
  · intro y hy
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hPb ⟨y, hy.1⟩ hy.2
    rw [hs1 ⟨y, hy.1⟩, hs2 ⟨y, hy.1⟩]
    refine ⟨a1, a2, a3, a4, ?_, j ⁻¹' discInt (R ⟨y, hy.1⟩), ((hR _).disc.isOpen_discInt
      hman).preimage hj.continuous, ?_, ?_, ?_⟩
    · rintro x hx
      rw [hc ⟨y, hy.1⟩, (hpre _).2]
      have hxb : x ∈ bd S := by
        obtain ⟨t, ht, rfl⟩ := hx
        have h3 := hm y hy
        exact h3.onBd t ⟨by linarith [ht.1, h3.lt, Real.pi_gt_three], by linarith [ht.2, h3.lt,
          Real.pi_gt_three]⟩
      exact hC7 _ ⟨a6 ⟨x, hx, rfl⟩, hbK x hxb⟩
    · exact fun x hx => a7 ⟨x, hx, rfl⟩
    · intro x hx
      rw [hc ⟨y, hy.1⟩]
      exact (hC5 _).1 (hRP _ _ hx.1 ⟨x, rfl⟩)
    · rintro x ⟨hx, hxb⟩
      have h1 : j x ∈ discInt (C ⟨y, hy.1⟩) := (hC5 _).2 (hPint _ _ hx ⟨x, rfl⟩ fun h => hxb
        (hKb x h))
      refine ⟨?_, fun h => ?_⟩
      · rw [hc ⟨y, hy.1⟩]
        exact h1.1
      · rw [hc ⟨y, hy.1⟩, (hpre _).2] at h
        exact h1.2 h
  · intro v hv x hx
    rw [hc ⟨v, hv⟩] at hx
    obtain ⟨w, hw⟩ := mem_iUnion.mp (hC6 _ ⟨hx.1, hbK x hx.2⟩)
    by_cases hwb : w.1 ∈ bd S
    · obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hPb w hwb
      have h1 : j x ∈ P w ∩ K := ⟨hw, hbK x hx.2⟩
      rw [a5] at h1
      obtain ⟨x', hx', e⟩ := h1
      refine mem_iUnion₂.mpr ⟨w.1, ⟨w.2, hwb⟩, ?_⟩
      rw [hs1 w, hs2 w, ← hj.injective e]
      exact hx'
    · have h1 : j x ∈ P w ∩ K := ⟨hw, hbK x hx.2⟩
      rw [hPi w hwb] at h1
      exact h1.elim

/-- **Thickening a forest.** Each vertex `v` of a forest `H` gets a closed disc `c v`. Two vertices
have the same disc if they are
in one component of `H`, and otherwise their discs are disjoint. The disc holds the component, which
meets its boundary only in
points of `bd(Σ)`. Each `y ∈ V(H) ∩ bd(Σ)` has a small piece of its cuff on the boundary of the
disc, and the disc is a neighbourhood of the
inside of this piece. There are no other points of `bd(Σ)` in the disc. -/
theorem exists_forest_thick (hS : IsSurface S) {H : Drawing S} (hH : IsSurfaceForest H) {f : S → ℝ
  → S} {ε : S → ℝ}
    (hm : ∀ y ∈ H.V ∩ bd S, CuffMark (f y) (ε y) y) :
    ∃ (c : S → Set S) (σ₁ σ₂ : S → ℝ), (∀ v ∈ H.V, IsClosedDisc (c v)) ∧
      (∀ u ∈ H.V, ∀ v ∈ H.V, c u = c v → Nonempty (GraphWalk H.toGraph u v)) ∧
      (∀ u ∈ H.V, ∀ v ∈ H.V, c u ≠ c v → Disjoint (c u) (c v)) ∧
      (∀ e ∈ H.E, ∀ u ∈ H.V, u ∈ closure e → closure e ⊆ c u) ∧ (∀ v ∈ H.V, v ∈ c v) ∧
      (∀ v ∈ H.V, ∀ z ∈ H.U, z ∈ discBd (c v) → z ∈ H.V ∩ bd S) ∧ (∀ v ∈ H.V, IsOpen (discInt
        (c v))) ∧
      (∀ y ∈ H.V ∩ bd S, 0 < σ₁ y ∧ σ₁ y < ε y ∧ 0 < σ₂ y ∧ σ₂ y < ε y ∧ f y '' Icc (-σ₂ y)
        (σ₁ y) ⊆ discBd (c y) ∧
        ∃ O, IsOpen O ∧ f y '' Ioo (-σ₂ y) (σ₁ y) ⊆ O ∧ O ⊆ c y ∧ O \ bd S ⊆ discInt (c y)) ∧
      ∀ v ∈ H.V, c v ∩ bd S ⊆ ⋃ y ∈ H.V ∩ bd S, f y '' Icc (-σ₂ y) (σ₁ y) := by
  classical
  obtain ⟨hprop, hfor⟩ := hH
  have ht2S : T2Space S := hS.2.1
  have hcS : CompactSpace S := hS.1
  obtain ⟨T, tT, j, K, hT, hj, hK, hu, hi, -⟩ := exists_capAll S hS
  have ht2 : T2Space T := hT.2.1
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  obtain ⟨G₀, hG₀U, hG₀V, hG₀V'⟩ := exists_drawing_union_bd hS H hprop
  obtain ⟨Γ, hΓU, hΓV⟩ := GM19.exists_drawing_image G₀ hj
  have hbc : IsClosed (bd S) := (cuff_statement.{0} S hS).1
  have hHV : ∀ v ∈ H.V, j v ∈ Γ.V := fun v hv => hΓV ▸ ⟨v, hG₀V hv, rfl⟩
  have hbK : ∀ x, x ∈ bd S → j x ∈ K := fun x hx => by
    have : j x ∈ range j ∩ K := hi ▸ ⟨x, hx, rfl⟩
    exact this.2
  have hKb : ∀ x, j x ∈ K → x ∈ bd S := fun x hx => by
    have : j x ∈ j '' bd S := hi ▸ ⟨⟨x, rfl⟩, hx⟩
    obtain ⟨x', hx', e⟩ := this
    exact hj.injective e ▸ hx'
  have hoffK : ∀ z, z ∉ K → z ∈ range j := fun z hz => by
    have : z ∈ range j ∪ K := hu ▸ mem_univ z
    exact this.resolve_right hz
  have hprop' : ∀ x ∈ H.U, x ∈ bd S → x ∈ H.V := fun x h1 h2 => hprop ⟨h2, h1⟩
  -- Edges of the forest.
  have hcle : ∀ e ∈ H.E, closure e ⊆ e ∪ H.V := fun e he x hx => by
    obtain ⟨γ, hγc, h0, h1, -, himg⟩ := exists_edge_param H he
    have hc : closure e ⊆ range γ := by
      refine closure_minimal (fun y hy => ?_) (isCompact_range hγc).isClosed
      rw [← himg] at hy
      obtain ⟨t, -, rfl⟩ := hy
      exact ⟨t, rfl⟩
    obtain ⟨t, rfl⟩ := hc hx
    by_cases h3 : t ∈ Ioo (0 : I) 1
    · exact .inl (himg ▸ mem_image_of_mem _ h3)
    · have : t = 0 ∨ t = 1 := by
        by_contra hn
        push Not at hn
        exact h3 ⟨unitInterval.pos_iff_ne_zero.mpr hn.1, unitInterval.lt_one_iff_ne_one.mpr hn.2⟩
      rcases this with rfl | rfl
      · exact .inr h0
      · exact .inr h1
  have hclU : ∀ e ∈ H.E, closure e ⊆ H.U := fun e he => H.closure_subset_U he
  have hfinV : Finite H.V := H.finite_V.to_subtype
  have hfinE : Finite H.E := Set.Finite.to_subtype H.finite_edges
  have hclc : ∀ e ∈ H.E, IsClosed (j '' closure e) := fun e _ => hj.isClosedMap _ isClosed_closure
  have hnice : ∀ e ∈ H.E, IsGammaNice Γ (j '' closure e) := fun e he => by
    exact forest_edge_closure_is_nice_in_capped_drawing (S := S) (H := H) T j hj G₀ hG₀U Γ hΓU hbc
      hHV hprop' hcle hclU hclc e he
  have hCnice : ∀ y ∈ H.V ∩ bd S, IsGammaNice Γ (j '' (f y '' Icc (-Real.pi) Real.pi)) := by
    exact cuff_image_is_nice_in_capped_drawing (S := S) (H := H) (f := f) (ε := ε) hm T j hj G₀
      hG₀U Γ hΓU hHV hprop'
  -- Small neighbourhoods of the vertices.
  obtain ⟨O, hO, hOd⟩ := (H.finite_V.image j).t2_separation
  let BB : S → Set T := fun v => j '' (H.V \ {v}) ∪ (⋃ e ∈ {e ∈ H.E | v ∉ closure e}, j '' closure
    e) ∪
    (if v ∈ bd S then j '' (bd S \ f v '' Ioo (-ε v) (ε v)) else K)
  have hBc : ∀ v ∈ H.V, IsClosed (BB v) := fun v hv => by
    refine (((H.finite_V.subset sdiff_subset).image j).isClosed.union ?_).union ?_
    · have hfinite : {e ∈ H.E | v ∉ closure e}.Finite :=
        H.finite_edges.subset fun _ he => he.1
      exact hfinite.isClosed_biUnion fun e he => hclc e he.1
    · by_cases h : v ∈ bd S
      · simp only [h, ite_true]
        exact hj.isClosedMap _ (hm v ⟨hv, h⟩).isClosed_rest
      · simp only [h, ite_false]
        exact hK
  have hvB : ∀ v ∈ H.V, j v ∉ BB v := fun v hv => by
    rintro ((⟨x, hx, e⟩ | h) | h)
    · exact hx.2 (hj.injective e)
    · obtain ⟨g, hg, x, hx, e⟩ := mem_iUnion₂.mp h
      exact hg.2 (hj.injective e ▸ hx)
    · by_cases hb : v ∈ bd S
      · simp only [hb, ite_true] at h
        obtain ⟨x, hx, e⟩ := h
        have m := hm v ⟨hv, hb⟩
        have : x = v := hj.injective e
        subst this
        exact hx.2 ⟨0, ⟨by linarith [m.pos], m.pos⟩, m.zero⟩
      · simp only [hb, ite_false] at h
        exact hb (hKb v h)
  let W : S → Set T := fun v => O (j v) \ BB v
  have hWo : ∀ v ∈ H.V, IsOpen (W v) := fun v hv => (hO _).2.sdiff (hBc v hv)
  have hWm : ∀ v ∈ H.V, j v ∈ W v := fun v hv => ⟨(hO _).1, hvB v hv⟩
  have hWO : ∀ u ∈ H.V, ∀ v ∈ H.V, u ≠ v → Disjoint (W u) (W v) := fun u hu v hv huv =>
    Disjoint.mono sdiff_subset sdiff_subset
      (hOd ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ fun e => huv (hj.injective e))
  have hWe : ∀ v ∈ H.V, ∀ e ∈ H.E, v ∉ closure e → Disjoint (W v) (j '' closure e)
    := fun v _ e he hve =>
    disjoint_left.mpr fun x hx hxe => hx.2 (.inl (.inr (mem_iUnion₂.mpr ⟨e, ⟨he, hve⟩, hxe⟩)))
  have hvd : ∀ v : H.V, ∃ R P s₁ s₂, IsStarDisc Γ (j v.1) R ∧ R ⊆ W v.1 ∧ IsClosedDisc P ∧ P ⊆ R
    ∧ P ⊆ range j ∧
      (∀ z ∈ R, z ∈ range j → z ∈ P) ∧ (∀ z ∈ discBd R, z ∈ range j → z ∉ K → z ∈ discBd P) ∧
      (∀ z ∈ discInt R, z ∈ range j → z ∉ K → z ∈ discInt P) ∧
      (v.1 ∈ bd S → 0 < s₁ ∧ s₁ < ε v.1 ∧ 0 < s₂ ∧ s₂ < ε v.1 ∧ P ∩ K = j '' (f v.1 '' Icc
        (-s₂) s₁) ∧
        j '' (f v.1 '' Icc (-s₂) s₁) ⊆ discBd P ∧ j '' (f v.1 '' Ioo (-s₂) s₁) ⊆ discInt R) ∧
          (v.1 ∉ bd S → P ∩ K = ∅) := by
    exact exists_thick_vertex_discs (S := S) hS (H := H) (f := f) (ε := ε) hm T j K hT hj hK hu hi
      Γ hHV hoffK hCnice W hWo hWm
        (fun v hb => disjoint_left.mpr fun z hz hz' => hz.2 (.inr (by
          simp only [hb, ite_true]
          exact hz')))
        (fun v hb => disjoint_left.mpr fun z hz hz' => hz.2 (.inr (by
          simp only [hb, ite_false]
          exact hz')))
  choose R P s₁ s₂ hR hRW hPd hPR hPr hRP hPbd hPint hPb hPi using hvd
  have hRdis : ∀ u v : H.V, u ≠ v → Disjoint (R u) (R v) := fun u v huv =>
    Disjoint.mono (hRW u) (hRW v) (hWO _ u.2 _ v.2 fun e => huv (Subtype.ext e))
  -- The edges between the discs.
  choose a' b' hne hau hbu hcap hl using fun i : H.E => forest_edge_line hfor i.2
  let a : H.E → H.V := fun i => ⟨a' i, hau i⟩
  let b : H.E → H.V := fun i => ⟨b' i, hbu i⟩
  have hab : ∀ i, a i ≠ b i := fun i e => hne i (congrArg Subtype.val e)
  have hlink : ∀ i, H.toGraph.IsLink i.1 (a i).1 (b i).1 := fun i => ⟨i.2, hau i, hbu i, hcap i⟩
  have hlT : ∀ i : H.E, IsLineWithEnds (j '' closure i.1) (j (a i).1) (j (b i).1) := fun i =>
    (hl i).map_of_embedding hj.isEmbedding
  choose p q M ρa ρb hlM hLeq hρa hρb hMa hMb hpb hqb hρai hρbi hum hvm using fun i : H.E =>
    exists_edge_piece hT (hR (a i)) (hR (b i)) (hRdis _ _ (hab i)) (hlT i) (hclc _ i.2)
      (hnice _ i.2)
  have hML : ∀ i, M i ⊆ j '' closure i.1 := fun i z hz => by
    rw [hLeq i]
    exact .inl (.inr hz)
  have hMe : ∀ i, M i ⊆ j '' i.1 := fun i z hz => by
    obtain ⟨x, hx, rfl⟩ := hML i hz
    rcases hcle i.1 i.2 hx with h | h
    · exact ⟨x, h, rfl⟩
    · have : x ∈ closure i.1 ∩ H.V := ⟨hx, h⟩
      rw [hcap i] at this
      rcases this with e | e
      · have ha : j (a i).1 ∈ M i := by
          rw [show (a i).1 = a' i from rfl, ← e]
          exact hz
        exact (hum i ha).elim
      · have hb : j (b i).1 ∈ M i := by
          rw [show (b i).1 = b' i from rfl, ← e]
          exact hz
        exact (hvm i hb).elim
  have hMK : ∀ i, ∀ z ∈ M i, z ∉ K := fun i z hz hzK => by
    obtain ⟨x, hx, rfl⟩ := hMe i hz
    have h1 := i.2.2.1 hx
    exact h1.2 (hprop' x h1.1 (hKb x hzK))
  have hMr : ∀ i, ∀ z ∈ M i, z ∈ range j := fun i z hz => hoffK z (hMK i z hz)
  have hpM : ∀ i, p i ∈ M i := fun i => (hlM i).left_mem
  have hqM : ∀ i, q i ∈ M i := fun i => (hlM i).right_mem
  have hEdgeDiscs : ∀ (i : H.E) (v : H.V), M i ∩ P v ⊆ {p i, q i} := by
    exact edge_middle_meets_vertex_discs_only_at_ends (S := S) (H := H) T j W hWe R P hRW hPR
      a b hcap p q M hMa hMb hML
  obtain ⟨C, hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8⟩ := exists_forest_discs hT (c₀ := P) (L := M)
    (p := p) (q := q) (a := a) (b := b)
    (Z := K) hPd (fun u v huv => Disjoint.mono (hPR u) (hPR v) (hRdis u v huv)) hlM
    (fun i => hPbd _ _ (hpb i) (hMr i _ (hpM i)) (hMK i _ (hpM i)))
    (fun i => hPbd _ _ (hqb i) (hMr i _ (hqM i)) (hMK i _ (hqM i)))
    hEdgeDiscs
    (fun i k hik => disjoint_left.mpr fun z h1 h2 => by
      obtain ⟨x, hx, rfl⟩ := hMe i h1
      obtain ⟨x', hx', e⟩ := hMe k h2
      have hxx : x' = x := hj.injective e
      subst hxx
      exact hik (Subtype.ext (H.edge_eq_of_mem i.2 k.2 hx hx')))
    hK (fun i => disjoint_left.mpr fun z hz h => hMK i z hz h)
    (fun E i hi => forest_no_reach hfor hlink hne E i hi)
  have hCr : ∀ v, C v ⊆ range j := fun v z hz => by
    by_cases hzK : z ∈ K
    · obtain ⟨w, hw⟩ := mem_iUnion.mp (hC6 v ⟨hz, hzK⟩)
      exact hPr w hw
    · exact hoffK z hzK
  have hne' : ∀ v : H.V, Nonempty S := fun v => ⟨v.1⟩
  have hpre : ∀ v, IsClosedDisc (j ⁻¹' C v) ∧ discBd (j ⁻¹' C v) = j ⁻¹' discBd (C v) := fun v =>
    haveI := hne' v
    isClosedDisc_preimage hj (hC1 v) (hCr v)
  have hmeet : ∀ {u v z}, z ∈ C u → z ∈ C v → C u = C v := fun {u v z} h1 h2 => by
    by_contra hn
    exact disjoint_left.mp (hC3 u v hn) h1 h2
  have hline : ∀ i : H.E, ∀ u : H.V, u.1 ∈ closure i.1 → j '' closure i.1 ⊆ C u := by
    exact thick_forest_disc_contains_incident_edge (S := S) (H := H) T j R P hRP a b hcap M
      ρa ρb hLeq hρa hρb C hC4 hC5
  have hint : ∀ z ∈ H.U, z ∉ bd S → ∃ w, j z ∈ discInt (C w) := by
    exact thick_forest_contains_interior_points_in_open_discs (S := S) (H := H) T j K Γ hKb R P hR
      hPint a b p q M ρa ρb hLeq hρai hρbi hpM hqM C hC4 hC5
  have hPulledBackDiscs :
      ∃ (c : S → Set S) (σ₁ σ₂ : S → ℝ), (∀ v ∈ H.V, IsClosedDisc (c v)) ∧
        (∀ u ∈ H.V, ∀ v ∈ H.V, c u = c v → Nonempty (GraphWalk H.toGraph u v)) ∧
        (∀ u ∈ H.V, ∀ v ∈ H.V, c u ≠ c v → Disjoint (c u) (c v)) ∧
        (∀ e ∈ H.E, ∀ u ∈ H.V, u ∈ closure e → closure e ⊆ c u) ∧ (∀ v ∈ H.V, v ∈ c v) ∧
        (∀ v ∈ H.V, ∀ z ∈ H.U, z ∈ discBd (c v) → z ∈ H.V ∩ bd S) ∧ (∀ v ∈ H.V, IsOpen (discInt
          (c v))) ∧
        (∀ y ∈ H.V ∩ bd S, 0 < σ₁ y ∧ σ₁ y < ε y ∧ 0 < σ₂ y ∧ σ₂ y < ε y ∧ f y '' Icc (-σ₂ y)
          (σ₁ y) ⊆ discBd (c y) ∧
          ∃ O, IsOpen O ∧ f y '' Ioo (-σ₂ y) (σ₁ y) ⊆ O ∧ O ⊆ c y ∧ O \ bd S ⊆ discInt (c y)) ∧
        ∀ v ∈ H.V, c v ∩ bd S ⊆ ⋃ y ∈ H.V ∩ bd S, f y '' Icc (-σ₂ y) (σ₁ y) := by
    exact forest_thickening_pulls_back_from_capped_surface (S := S) (H := H) (f := f) (ε := ε) hm
      T j K hj hman Γ hbK hKb hprop' R P s₁ s₂ hR hRP hPint hPb hPi a b hlink C hC1 hC2 hC3 hC5
      hC6 hC7 hCr hpre hmeet hline hint
  exact hPulledBackDiscs

end GraphMinor.GM07
