/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CylinderTrim
public import LeanPool.GraphMinor.GM07.CylinderPaths
public import LeanPool.GraphMinor.GM07.RegionNest
public import LeanPool.GraphMinor.GM16.LineDrawingPath

/-!
# The grid in a capped cylinder

This is the proof of Graph Minors VII, (5.8), in a sphere with two disjoint discs. The paper says
that (5.8) is Graph Minors III, (4.1). That theorem takes a nest and a family of paths and
uncrosses them. Here the paths come from Menger's theorem (`exists_cylinder_paths`), the nest from
layers of regions (`exists_region_nest`), and the uncrossing is
`GM09.PlanarNests.planar_nest_uncrossing`, used through the wheels of `CylinderWheel`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM09.PlanarNests

local notation "I" => unitInterval

variable {T : Type} [TopologicalSpace T] [T2Space T]

/-- A chain of regions from one disc to the other gives a line that meets the drawing in the
vertices of the chain. -/
theorem exists_cross_line (hS : IsClosedSurface T) {Γ : Drawing T} {D₁ D₂ : Set T}
  (h₁ : IsClosedDisc D₁) (h₂ : IsClosedDisc D₂) (hd : Disjoint D₁ D₂) {r₀ r₂ : Set T} {p a : T}
    (h₀ : r₀ ∈ Γ.R)
    (hp : p ∈ r₀) (hp₁ : p ∈ D₁) (ha : a ∈ r₂) (ha₂ : a ∈ D₂) {t : ℕ}
      (hmem : r₂ ∈ regLayer Γ r₀ t) :
    ∃ (L : Set T) (u v : T), IsLineWithEnds L u v ∧ u ∈ discBd D₁ ∧ v ∈ discBd D₂ ∧ L ∩ Γ.U ⊆ Γ.V
      ∧ Disjoint L (discInt D₁) ∧ Disjoint L (discInt D₂) ∧ (L ∩ Γ.V).ncard ≤ t := by
  classical
  obtain ⟨A, a1, a2, a3, X, b1, b2, b3⟩ := exists_chain_set hS h₀ t r₂ hmem
  have hpa : p ≠ a := fun h => disjoint_left.mp hd hp₁ (h ▸ ha₂)
  obtain ⟨γ, hγ⟩ := (a1.joinedIn p (a2 hp) a (a3 ha))
  obtain ⟨e, hec, hei, he0, he1, her⟩ := exists_arc_of_path γ.continuous (by simpa using hpa)
  have heA : ∀ τ, e τ ∈ A := fun τ => by
    obtain ⟨σ, hσ⟩ := her (mem_range_self τ)
    exact hσ ▸ hγ σ
  rw [γ.source] at he0
  rw [γ.target] at he1
  have hc₁ : IsCompact (e ⁻¹' D₁) := (h₁.isClosed.preimage hec).isCompact
  obtain ⟨t₁, ht₁, htop⟩ := hc₁.exists_isGreatest ⟨0, by simpa [he0] using hp₁⟩
  have hc₂ : IsCompact (Ici t₁ ∩ e ⁻¹' D₂) := (isClosed_Ici.inter (h₂.isClosed.preimage
    hec)).isCompact
  obtain ⟨t₂, ⟨htt, ht₂⟩, hlow⟩ :=
    hc₂.exists_isLeast ⟨1, unitInterval.le_one _, by simpa [he1] using ha₂⟩
  have hlt : t₁ < t₂ := lt_of_le_of_ne htt fun h => disjoint_left.mp hd ht₁ (h ▸ ht₂)
  have hgap : (0 : ℝ) < (t₂ : ℝ) - t₁ := sub_pos.mpr hlt
  let r : I → I := fun σ => ⟨t₁ + σ * ((t₂ : ℝ) - t₁), by
    have h3 := mul_nonneg σ.2.1 hgap.le
    have h4 := mul_le_of_le_one_left hgap.le σ.2.2
    exact ⟨by linarith [t₁.2.1], by linarith [t₂.2.2]⟩⟩
  have hrc : Continuous r := Continuous.subtype_mk (by fun_prop) _
  have hr0 : r 0 = t₁ := Subtype.ext (by simp [r])
  have hr1 : r 1 = t₂ := Subtype.ext (by simp [r])
  have hri : Injective r := fun σ σ' he => by
    have h3 : (σ : ℝ) * ((t₂ : ℝ) - t₁) = σ' * ((t₂ : ℝ) - t₁) := by
      have := congrArg Subtype.val he
      simp only [r] at this
      linarith
    exact Subtype.ext (mul_right_cancel₀ hgap.ne' h3)
  let φ : I → T := e ∘ r
  have hφ : IsArcMap φ := ⟨hec.comp hrc, hei.comp hri⟩
  have hφ0 : φ 0 ∈ D₁ := by
    change e (r 0) ∈ D₁
    rw [hr0]
    exact ht₁
  have hφ1 : φ 1 ∈ D₂ := by
    change e (r 1) ∈ D₂
    rw [hr1]
    exact ht₂
  have hoff₁ : ∀ σ : I, 0 < σ → φ σ ∉ D₁ := fun σ hσ h => by
    have h3 : r σ ≤ t₁ := htop h
    have h4 : (r σ : ℝ) ≤ t₁ := h3
    have h5 : (0 : ℝ) < σ := hσ
    have h6 := mul_pos h5 hgap
    simp only [r] at h4
    linarith
  have hoff₂ : ∀ σ : I, σ < 1 → φ σ ∉ D₂ := fun σ hσ h => by
    have h7 : (r σ : ℝ) = t₁ + σ * ((t₂ : ℝ) - t₁) := rfl
    have h8 : (t₁ : ℝ) ≤ r σ := by
      rw [h7]
      linarith [mul_nonneg σ.2.1 hgap.le]
    have h3 : t₂ ≤ r σ := hlow ⟨h8, h⟩
    have h4 : (t₂ : ℝ) ≤ r σ := h3
    have h5 : (σ : ℝ) < 1 := hσ
    have h6 := mul_lt_mul_of_pos_right h5 hgap
    linarith
  have hb₁ : φ 0 ∈ discBd D₁ := by
    rw [← IsClosedDisc.frontier_eq_discBd hS h₁, frontier_eq_closure_inter_closure]
    refine ⟨subset_closure hφ0, ?_⟩
    have h3 : (0 : I) ∈ closure (Ioi (0 : I)) := by
      rw [closure_Ioi' ⟨1, zero_lt_one⟩]
      exact le_refl _
    exact map_mem_closure hφ.1 h3 fun σ hσ => hoff₁ σ hσ
  have hb₂ : φ 1 ∈ discBd D₂ := by
    rw [← IsClosedDisc.frontier_eq_discBd hS h₂, frontier_eq_closure_inter_closure]
    refine ⟨subset_closure hφ1, ?_⟩
    have h3 : (1 : I) ∈ closure (Iio (1 : I)) := by
      rw [closure_Iio' ⟨0, zero_lt_one⟩]
      exact le_refl _
    exact map_mem_closure hφ.1 h3 fun σ hσ => hoff₂ σ hσ
  have hLA : ∀ z ∈ range φ, z ∈ A := by
    rintro _ ⟨σ, rfl⟩
    exact heA _
  have hLX : range φ ∩ Γ.U ⊆ X := fun z hz => by
    rcases b3 (hLA z hz.1) with h | h
    · exact h
    · exact absurd hz.2 h
  refine ⟨range φ, φ 0, φ 1, isLineWithEnds_range_of_arc hφ, hb₁, hb₂, fun z hz => b2 (hLX hz),
    ?_, ?_, ?_⟩
  · refine disjoint_left.mpr ?_
    rintro _ ⟨σ, rfl⟩ ⟨h3, h4⟩
    rcases eq_or_lt_of_le (unitInterval.nonneg σ) with h | h
    · have h5 : σ = 0 := Subtype.ext h.symm
      exact h4 (h5 ▸ hb₁)
    · exact hoff₁ σ h h3
  · refine disjoint_left.mpr ?_
    rintro _ ⟨σ, rfl⟩ ⟨h3, h4⟩
    rcases eq_or_lt_of_le (unitInterval.le_one σ) with h | h
    · have h5 : σ = 1 := Subtype.ext h
      exact h4 (h5 ▸ hb₂)
    · exact hoff₂ σ h h3
  · have h3 : range φ ∩ Γ.V ⊆ (X : Set T) := fun z hz => hLX ⟨hz.1, Γ.V_subset_U hz.2⟩
    have h4 := Set.ncard_le_ncard h3 X.finite_toSet
    rw [Set.ncard_coe_finset] at h4
    omega

/-- Points of the interior of a disc lie on one side of a disc whose boundary misses it. -/
theorem side_of_disc (hS : IsClosedSurface T) {D Δ : Set T} (hD : IsClosedDisc D)
  (hΔ : IsClosedDisc Δ) (hf : Disjoint (discInt D) (discBd Δ)) {x y : T} (hx : x ∈ discInt D)
    (hy : y ∈ discInt D)
    (h : x ∈ Δ) : y ∈ Δ := by
  rw [← IsClosedDisc.frontier_eq_discBd hS hΔ] at hf
  rcases inside_or_outside hD.isPreconnected_discInt hΔ.isClosed hf with h1 | h1
  · exact interior_subset (h1 hy)
  · exact absurd h (h1 hx)

/-- Extend a path across the two discs by the spokes at its ends. -/
theorem exists_extended_path {Γ H C₁ C₂ : Drawing T} {D₁ D₂ E₁ E₂ : Set T} {q : T → T} {ℓ : T
  → Set T} (w : IsWheeled Γ H C₁ C₂ D₁ D₂ E₁ E₂ q ℓ) (hd : Disjoint D₁ D₂)
    (hi₁ : Disjoint Γ.U (discInt D₁)) (hi₂ : Disjoint Γ.U (discInt D₂)) {P : Drawing T} {u v : T}
      (hP : P.IsSubdrawing Γ) (hu : u ∈ Γ.V ∩ D₁) (hv : v ∈ Γ.V ∩ D₂)
        (hpath : P.IsPathBetween u v) :
    ∃ P' : Drawing T, P'.IsSubdrawing H ∧ P'.IsPathBetween (q u) (q v) ∧ P'.V ⊆ P.V ∪ {q u, q v}
      ∧ P'.U = ℓ u ∪ P.U ∪ ℓ v := by
  have hu' : u ∈ Γ.V ∩ (D₁ ∪ D₂) := ⟨hu.1, .inl hu.2⟩
  have hv' : v ∈ Γ.V ∩ (D₁ ∪ D₂) := ⟨hv.1, .inr hv.2⟩
  obtain ⟨hlu, hneu, heu⟩ := w.line u hu'
  obtain ⟨hlv, hnev, hev⟩ := w.line v hv'
  obtain ⟨cu1, cu2, cu3⟩ := w.cap₁ u hu
  obtain ⟨cv1, cv2, cv3⟩ := w.cap₂ v hv
  have huv : u ≠ v := fun h => disjoint_left.mp hd hu.2 (h ▸ hv.2)
  have hPL := isLine_of_isPathBetween hpath huv
  have huP : u ∈ P.U := hPL.left_mem
  have hvP : v ∈ P.U := hPL.right_mem
  have hPV : ∀ {z}, z ∈ P.U → z ∈ Γ.U := fun {z} h => hP.U_subset h
  have hm1 : ℓ u ∩ P.U = {u} := by
    ext z
    constructor
    · rintro ⟨h3, h4⟩
      have hb : z ∈ discBd D₁ := by
        by_contra hn
        exact disjoint_left.mp hi₁ (hPV h4) ⟨cu1 h3, hn⟩
      have : z ∈ ℓ u ∩ discBd D₁ := ⟨h3, hb⟩
      rwa [cu2] at this
    · rintro rfl
      exact ⟨hlu.left_mem, huP⟩
  have hm2 : P.U ∩ ℓ v = {v} := by
    ext z
    constructor
    · rintro ⟨h4, h3⟩
      have hb : z ∈ discBd D₂ := by
        by_contra hn
        exact disjoint_left.mp hi₂ (hPV h4) ⟨cv1 h3, hn⟩
      have : z ∈ ℓ v ∩ discBd D₂ := ⟨h3, hb⟩
      rwa [cv2] at this
    · rintro rfl
      exact ⟨hvP, hlv.left_mem⟩
  have huvd : ∀ z, z ∈ ℓ u → z ∈ ℓ v → False := fun z h3 h4 => disjoint_left.mp hd (cu1 h3) (cv1 h4)
  obtain ⟨W, -, hWV, -⟩ := id hpath
  have huV : u ∈ P.V := by rw [hWV]; exact W.start_mem_support
  have hvV : v ∈ P.V := by rw [hWV]; exact W.end_mem_support
  let A := lineDrawing hlu.symm hneu.symm
  let B := lineDrawing hlv hnev
  have g1 : A.U ∩ P.U ⊆ A.V ∩ P.V := fun z hz => by
    have h3 : z ∈ ℓ u ∩ P.U := hz
    rw [hm1] at h3
    obtain rfl := h3
    exact ⟨.inr rfl, huV⟩
  let G₁ := A.glue P g1
  have g2 : G₁.U ∩ B.U ⊆ G₁.V ∩ B.V := by
    rintro z ⟨h3 | h3, h4⟩
    · exact (huvd z h3 h4).elim
    · have h5 : z ∈ P.U ∩ ℓ v := ⟨h3, h4⟩
      rw [hm2] at h5
      obtain rfl := h5
      exact ⟨.inr hvV, .inl rfl⟩
  let G := G₁.glue B g2
  have hLine : IsLineWithEnds G.U (q u) (q v) := by
    have h3 := Surface.IsLineWithEnds.union hlu.symm hPL hm1
    refine Surface.IsLineWithEnds.union h3 hlv ?_
    ext z
    constructor
    · rintro ⟨h4 | h4, h5⟩
      · exact (huvd z h4 h5).elim
      · have : z ∈ P.U ∩ ℓ v := ⟨h4, h5⟩
        rwa [hm2] at this
    · rintro rfl
      exact ⟨.inr hvP, hlv.left_mem⟩
  have hquv : q u ≠ q v := fun h => huvd _ hlu.right_mem (h ▸ hlv.right_mem)
  have hqu : q u ∈ H.V := (w.ends hu').2.2.2.2.2
  have hqv : q v ∈ H.V := (w.ends hv').2.2.2.2.2
  refine ⟨G, ⟨?_, ?_⟩, GM16.drawing_isPathBetween_of_isLine_U hLine hquv (.inl (.inl (.inl rfl)))
    (.inr (.inr rfl)), ?_, rfl⟩
  · rintro z ((h | h) | h | h)
    · rcases h with rfl | rfl
      · exact hqu
      · exact w.sub.1 hu.1
    · exact w.sub.1 (hP.1 h)
    · obtain rfl := h
      exact w.sub.1 hv.1
    · obtain rfl := h
      exact hqv
  · change (A.glue P g1 |>.glue B g2).E ⊆ _
    rw [Drawing.glue_E, Drawing.glue_E, lineDrawing_E, lineDrawing_E]
    rintro e ((h | h) | h)
    · obtain rfl := h
      rw [pair_comm]
      exact heu
    · exact w.sub.2 (hP.2 h)
    · obtain rfl := h
      exact hev
  · rintro z ((h | h) | h | h)
    · rcases h with rfl | rfl
      · exact .inr (.inl rfl)
      · exact .inl huV
    · exact .inl h
    · obtain rfl := h
      exact .inl hvV
    · obtain rfl := h
      exact .inr (.inr rfl)

/-- The sequence of the inner circuit, the nest, and the outer circuit. -/
def nestAt {X : Type*} (a b : X) (s : ℕ) (f : Fin s → X) : ℕ → X
  | 0 => a
  | t + 1 => if h : t < s then f ⟨t, h⟩ else b

theorem nestAt_succ {X : Type*} (a b : X) (s : ℕ) (f : Fin s → X) (t : Fin s) : nestAt a b s f
  (t + 1) = f t := by
  simp [nestAt]

theorem nestAt_last {X : Type*} (a b : X) (s : ℕ) (f : Fin s → X) : nestAt a b s f (s + 1) = b := by
  simp [nestAt]

theorem nest_cases {s j : ℕ} (hj : j < s + 2) : j = 0 ∨ (∃ t : Fin s, j = t + 1) ∨ j = s + 1 := by
  rcases j with _ | t
  · exact .inl rfl
  · by_cases h : t < s
    · exact .inr (.inl ⟨⟨t, h⟩, rfl⟩)
    · exact .inr (.inr (by omega))

/-- The inner circle, the nest, and the outer circle form a nest of `H`. -/
theorem isDiscNest_of_layers {Γ H C₁ C₂ : Drawing T} {D₁ D₂ E₁ E₂ Δ : Set T} {q : T → T} {ℓ : T
  → Set T} (w : IsWheeled Γ H C₁ C₂ D₁ D₂ E₁ E₂ q ℓ) (hΔ : IsClosedDisc Δ) (hbΔ : discBd Δ = C₂.U)
    (hE₁Δ : E₁ ⊆ Δ) {s : ℕ} {N : Fin s → Drawing T} {Dn : Fin s → Set T}
    (hN : ∀ t, (N t).IsCircuit ∧ (N t).IsSubdrawing Γ ∧ IsClosedDisc (Dn t) ∧ discBd (Dn t) =
      (N t).U ∧ E₁ ⊆ Dn t ∧ Dn t ⊆ Δ) (hNN : ∀ t t', t < t' → Disjoint (N t).V (N t').V
        ∧ Dn t ⊆ Dn t')
    (hΓ₁ : Disjoint Γ.V C₁.V) (hΓ₂ : Disjoint Γ.V C₂.V) (h12 : Disjoint C₁.V C₂.V) :
    IsDiscNest H Δ C₁ C₂ (fun j : Fin (s + 2) => nestAt C₁ C₂ s N j) := by
  have hNV : ∀ t, ∀ x ∈ (N t).V, x ∈ Γ.V := fun t x hx => (hN t).2.1.1 hx
  set F := nestAt C₁ C₂ s N with hF
  set d := nestAt E₁ Δ s Dn with hd
  have hprop : ∀ j, j < s + 2 → (F j).IsSubdrawing H ∧ (F j).IsCircuit ∧ IsClosedDisc (d j)
    ∧ discBd (d j) = (F j).U ∧ d j ⊆ Δ := fun j hj => by
    rcases nest_cases hj with rfl | ⟨t, rfl⟩ | rfl
    · exact ⟨w.sub₁, w.circ₁, w.disc₁, w.bd₁, hE₁Δ⟩
    · rw [hF, hd, nestAt_succ, nestAt_succ]
      obtain ⟨h1, h2, h3, h4, -, h6⟩ := hN t
      exact ⟨h2.trans w.sub, h1, h3, h4, h6⟩
    · rw [hF, hd, nestAt_last, nestAt_last]
      exact ⟨w.sub₂, w.circ₂, hΔ, hbΔ, Subset.rfl⟩
  have hins : ∀ j, j < s + 2 → GM14.discIns Δ (F j) = d j := fun j hj => by
    obtain ⟨-, h2, h3, h4, h5⟩ := hprop j hj
    exact ((GM14.discIns_spec hΔ h2 (h4 ▸ (Surface.discBd_subset _).trans h5)).2
      (d j) h5 h3 h4).symm
  have hlt : ∀ i j, i < j → j < s + 2 → Disjoint (F i).V (F j).V ∧ d i ⊆ d j := fun i j hij hj => by
    rcases nest_cases (hij.trans hj) with rfl | ⟨t, rfl⟩ | rfl
    · rcases nest_cases hj with rfl | ⟨t', rfl⟩ | rfl
      · omega
      · rw [hF, hd, nestAt_succ, nestAt_succ]
        exact ⟨disjoint_left.mpr fun x h1 h2 => disjoint_left.mp hΓ₁ (hNV t' x h2) h1,
          (hN t').2.2.2.2.1⟩
      · rw [hF, hd, nestAt_last, nestAt_last]
        exact ⟨h12, hE₁Δ⟩
    · rcases nest_cases hj with rfl | ⟨t', rfl⟩ | rfl
      · omega
      · rw [hF, hd, nestAt_succ, nestAt_succ, nestAt_succ, nestAt_succ]
        exact hNN t t' (Fin.lt_def.mpr (by omega))
      · rw [hF, hd, nestAt_succ, nestAt_succ, nestAt_last, nestAt_last]
        exact ⟨disjoint_left.mpr fun x h1 h2 => disjoint_left.mp hΓ₂ (hNV t x h1) h2,
          (hN t).2.2.2.2.2⟩
    · omega
  refine ⟨fun j => ?_, fun i j hne => ?_, fun i j hij => ?_, fun _ => ⟨rfl, nestAt_last _ _ _ _⟩⟩
  · obtain ⟨h1, h2, -, h4, h5⟩ := hprop j j.2
    exact ⟨h1, h2, h4 ▸ (Surface.discBd_subset _).trans h5⟩
  · rcases lt_or_gt_of_ne hne with h | h
    · exact (hlt i j h j.2).1
    · exact (hlt j i h i.2).1.symm
  · change GM14.discIns Δ (F i) ⊆ GM14.discIns Δ (F j)
    rw [hins i i.2, hins j j.2]
    rcases eq_or_lt_of_le (Fin.le_def.mp hij) with h | h
    · rw [h]
    · exact (hlt i j h j.2).2

/-- **(5.8) in the capped cylinder.** -/
theorem exists_cylinder_grid (hS : IsClosedSurface T) (hsph : IsSphere T) [ConnectedSpace T]
  (Γ : Drawing T) {D₁ D₂ : Set T} (h₁ : IsClosedDisc D₁) (h₂ : IsClosedDisc D₂)
    (hd : Disjoint D₁ D₂)
    (hU₁ : Γ.U ∩ D₁ ⊆ Γ.V) (hi₁ : Disjoint Γ.U (discInt D₁)) (hU₂ : Γ.U ∩ D₂ ⊆ Γ.V)
      (hi₂ : Disjoint Γ.U (discInt D₂)) {p a : T} (hp : p ∈ discInt D₁)
        (ha : a ∈ discInt D₂) {r s : ℕ}
    (hi : ∀ B, IsClosedDisc B → D₁ ⊆ B → Disjoint (discInt D₂) B → discBd B ∩ Γ.U ⊆ Γ.V → r ≤
      (discBd B ∩ Γ.U).ncard)
    (hii : ∀ (L : Set T) (u v : T), IsLineWithEnds L u v → u ∈ discBd D₁ → v ∈ discBd D₂
      → L ∩ Γ.U ⊆ Γ.V → Disjoint L (discInt D₁) → Disjoint L (discInt D₂) → s ≤ (L ∩ Γ.V).ncard) :
    ∃ (P : Fin r → Drawing T) (u v : Fin r → T) (B : Fin s → Drawing T) (E : Fin s → Set T), (∀ i,
      (P i).IsSubdrawing Γ ∧ u i ∈ D₁ ∧ v i ∈ D₂ ∧ (P i).IsPathBetween (u i) (v i)) ∧
      (∀ i i', i ≠ i' → Disjoint (P i).V (P i').V) ∧
      (∀ j, (B j).IsSubdrawing Γ ∧ (B j).IsCircuit ∧ IsClosedDisc (E j) ∧ discBd (E j) = (B j).U
        ∧ p ∈ E j ∧ a ∉ E j) ∧
      (∀ j j', j ≤ j' → E j ⊆ E j') ∧
      (∀ j j', j ≠ j' → Disjoint (B j).V (B j').V) ∧
      ∀ i j, ∃ (Q : Drawing T) (x y : T), Q.IsSubdrawing Γ ∧ Q.U = (P i).U ∩ (B j).U ∧ Q.V =
        (P i).V ∩ (B j).V ∧ Q.IsPathBetween x y := by
  classical
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hlc : LocallyConnectedSpace T := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨P₀, u₀, v₀, hP₀, hP₀d⟩ := exists_cylinder_paths hS hsph Γ h₁ h₂ hd hU₁ hi₁ hU₂ hi₂ hi
  -- the nest from the layers
  have hpU : p ∉ Γ.U := fun h => disjoint_left.mp hi₁ h hp
  have haU : a ∉ Γ.U := fun h => disjoint_left.mp hi₂ h ha
  let r₀ := connectedComponentIn (univ \ Γ.U) p
  let r₂ := connectedComponentIn (univ \ Γ.U) a
  have hr₀ : r₀ ∈ Γ.R := (mem_R_iff Γ).mpr ⟨p, hpU, rfl⟩
  have hr₂ : r₂ ∈ Γ.R := (mem_R_iff Γ).mpr ⟨a, haU, rfl⟩
  have hpr : p ∈ r₀ := mem_connectedComponentIn ⟨mem_univ _, hpU⟩
  have har : a ∈ r₂ := mem_connectedComponentIn ⟨mem_univ _, haU⟩
  have hfar : ∀ t < s, r₂ ∉ regLayer Γ r₀ t := fun t ht hmem => by
    obtain ⟨L, u, v, c1, c2, c3, c4, c5, c6, c7⟩ := exists_cross_line hS h₁ h₂ hd hr₀ hpr hp.1 har
      ha.1 hmem
    have := hii L u v c1 c2 c3 c4 c5 c6
    omega
  obtain ⟨N, Dn, hN, hNN⟩ := exists_region_nest hS hsph hr₀ hr₂ hpr har hfar
  -- the wheels
  obtain ⟨H, C₁, C₂, E₁, E₂, q, ℓ, w⟩ := exists_wheeled Γ h₁ h₂ hd hi₁ hi₂
  have hC₁I : ∀ x ∈ C₁.U, x ∈ discInt D₁ := fun x hx => w.in₁ (Surface.discBd_subset _ (w.bd₁ ▸ hx))
  have hC₂I : ∀ x ∈ C₂.U, x ∈ discInt D₂ := fun x hx => w.in₂ (Surface.discBd_subset _ (w.bd₂ ▸ hx))
  have hΓ₁ : Disjoint Γ.V C₁.V := disjoint_left.mpr fun x h3 h4 => disjoint_left.mp hi₁
    (Γ.V_subset_U h3) (hC₁I x (C₁.V_subset_U h4))
  have hΓ₂ : Disjoint Γ.V C₂.V := disjoint_left.mpr fun x h3 h4 => disjoint_left.mp hi₂
    (Γ.V_subset_U h3) (hC₂I x (C₂.V_subset_U h4))
  have h12 : Disjoint C₁.V C₂.V := disjoint_left.mpr fun x h3 h4 => disjoint_left.mp hd (hC₁I x
    (C₁.V_subset_U h3)).1 (hC₂I x (C₂.V_subset_U h4)).1
  have hE₁I : E₁ ⊆ discInt D₁ := w.in₁
  have hE₂I : E₂ ⊆ discInt D₂ := w.in₂
  obtain ⟨hΔ, hbΔ₀⟩ := GM12.isClosedDisc_closure_compl_of_sphere hS hsph w.disc₂
  set Δ := closure (univ \ E₂) with hΔdef
  have hbΔ : discBd Δ = C₂.U := hbΔ₀.trans w.bd₂
  have hoffΔ : ∀ {x}, x ∉ E₂ → x ∈ Δ := fun {x} hx => subset_closure ⟨mem_univ x, hx⟩
  have hnotΔ : ∀ {x}, x ∈ discInt E₂ → x ∉ Δ := fun {x} hx h => by
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp h _ (w.disc₂.isOpen_discInt hman) hx
    exact hy2.2 hy1.1
  have hE₁Δ : E₁ ⊆ Δ := fun x hx => hoffΔ fun h => disjoint_left.mp hd (hE₁I hx).1 (hE₂I h).1
  have hbI : ∀ {X : Drawing T}, X.IsSubdrawing Γ → ∀ {Y}, discBd Y = X.U → Disjoint (discInt D₁)
    (discBd Y) ∧ Disjoint (discInt D₂) (discBd Y) := fun {X} hX {Y} hY => by
    rw [hY]
    exact ⟨hi₁.symm.mono_right hX.U_subset, hi₂.symm.mono_right hX.U_subset⟩
  have hN' : ∀ t, (N t).IsCircuit ∧ (N t).IsSubdrawing Γ ∧ IsClosedDisc (Dn t) ∧ discBd (Dn t) =
    (N t).U ∧ E₁ ⊆ Dn t ∧ Dn t ⊆ Δ := fun t => by
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hN t
    have hf := hbI c2 c4
    refine ⟨c1, c2, c3, c4, fun x hx => side_of_disc hS h₁ c3 hf.1 hp (hE₁I hx) c5,
      fun x hx => hoffΔ fun h => c6 ?_⟩
    exact side_of_disc hS h₂ c3 hf.2 (hE₂I h) ha hx
  have hnest := isDiscNest_of_layers w hΔ hbΔ hE₁Δ hN' hNN hΓ₁ hΓ₂ h12
  -- the paths, extended by spokes
  have hends : ∀ i, u₀ i ∈ Γ.V ∩ D₁ ∧ v₀ i ∈ Γ.V ∩ D₂ := fun i => by
    obtain ⟨c1, c2, c3, W, -, hV, -⟩ := hP₀ i
    exact ⟨⟨c1.1 (by rw [hV]; exact W.start_mem_support), c2⟩,
      ⟨c1.1 (by rw [hV]; exact W.end_mem_support), c3⟩⟩
  have hstart : ∀ i, u₀ i ∈ (P₀ i).V ∧ v₀ i ∈ (P₀ i).V := fun i => by
    obtain ⟨-, -, -, W, -, hV, -⟩ := hP₀ i
    exact ⟨by rw [hV]; exact W.start_mem_support, by rw [hV]; exact W.end_mem_support⟩
  have hext : ∀ i, ∃ P' : Drawing T, P'.IsSubdrawing H ∧ P'.IsPathBetween (q (u₀ i)) (q (v₀ i))
    ∧ P'.V ⊆ (P₀ i).V ∪ {q (u₀ i), q (v₀ i)} ∧ P'.U = ℓ (u₀ i) ∪ (P₀ i).U ∪ ℓ (v₀ i) := fun i =>
    exists_extended_path w hd hi₁ hi₂ (hP₀ i).1 (hends i).1 (hends i).2 (hP₀ i).2.2.2
  choose P₁ hP₁H hP₁p hP₁V hP₁U using hext
  have hq₁ := fun i => w.q₁ _ (hends i).1
  have hq₂ := fun i => w.q₂ _ (hends i).2
  have hu' : ∀ i, u₀ i ∈ Γ.V ∩ (D₁ ∪ D₂) := fun i => ⟨(hends i).1.1, .inl (hends i).1.2⟩
  have hv' : ∀ i, v₀ i ∈ Γ.V ∩ (D₁ ∪ D₂) := fun i => ⟨(hends i).2.1, .inr (hends i).2.2⟩
  have hquu : ∀ i i', i ≠ i' → q (u₀ i) ≠ q (u₀ i') := fun i i' hne he => by
    have hne' : u₀ i ≠ u₀ i' := fun h => disjoint_left.mp (hP₀d i i' hne) (hstart i).1 (h ▸
      (hstart i').1)
    exact disjoint_left.mp (w.disj _ (hu' i) _ (hu' i') hne') (w.line _ (hu' i)).1.right_mem (he ▸
      (w.line _ (hu' i')).1.right_mem)
  have hqvv : ∀ i i', i ≠ i' → q (v₀ i) ≠ q (v₀ i') := fun i i' hne he => by
    have hne' : v₀ i ≠ v₀ i' := fun h => disjoint_left.mp (hP₀d i i' hne) (hstart i).2 (h ▸
      (hstart i').2)
    exact disjoint_left.mp (w.disj _ (hv' i) _ (hv' i') hne') (w.line _ (hv' i)).1.right_mem (he ▸
      (w.line _ (hv' i')).1.right_mem)
  have hP₁dis : ∀ i i', i ≠ i' → Disjoint (P₁ i).V (P₁ i').V := fun i i' hne
    => disjoint_left.mpr fun z h3 h4 => by
    have hΓz : ∀ k, z ∈ (P₀ k).V → z ∈ Γ.V := fun k h => (hP₀ k).1.1 h
    have hc1 : ∀ k, z = q (u₀ k) → z ∈ C₁.V := fun k h => h ▸ hq₁ k
    have hc2 : ∀ k, z = q (v₀ k) → z ∈ C₂.V := fun k h => h ▸ hq₂ k
    rcases hP₁V i h3 with h5 | h5 | h5 <;> rcases hP₁V i' h4 with h6 | h6 | h6
    · exact disjoint_left.mp (hP₀d i i' hne) h5 h6
    · exact disjoint_left.mp hΓ₁ (hΓz i h5) (hc1 i' h6)
    · exact disjoint_left.mp hΓ₂ (hΓz i h5) (hc2 i' h6)
    · exact disjoint_left.mp hΓ₁ (hΓz i' h6) (hc1 i h5)
    · exact hquu i i' hne (h5.symm.trans h6)
    · exact disjoint_left.mp h12 (hc1 i h5) (hc2 i' h6)
    · exact disjoint_left.mp hΓ₂ (hΓz i' h6) (hc2 i h5)
    · exact disjoint_left.mp h12 (hc1 i' h6) (hc2 i h5)
    · exact hqvv i i' hne (h5.symm.trans h6)
  have hP₁Δ : ∀ i, (P₁ i).U ⊆ Δ := fun i => by
    rw [hP₁U]
    refine union_subset (union_subset (fun z hz => hoffΔ fun h => ?_) (fun z hz => hoffΔ fun h
      => ?_)) fun z hz => ?_
    · exact disjoint_left.mp hd ((w.cap₁ _ (hends i).1).1 hz) (hE₂I h).1
    · exact disjoint_left.mp hi₂ ((hP₀ i).1.U_subset hz) (hE₂I h)
    · by_cases h : z ∈ E₂
      · have h3 : z ∈ ℓ (v₀ i) ∩ E₂ := ⟨hz, h⟩
        rw [(w.cap₂ _ (hends i).2).2.2] at h3
        obtain rfl := h3
        exact Surface.discBd_subset _ (hbΔ ▸ C₂.V_subset_U (hq₂ i))
      · exact hoffΔ h
  have hpaths : IsDiscPaths H Δ C₁ C₂ P₁ := ⟨fun i => ⟨hP₁H i, hP₁Δ i, _, hq₁ i, _, hq₂ i, hP₁p i⟩,
    fun i i' hne => hP₁dis i i' hne⟩
  -- the uncrossing
  obtain ⟨C, Pu, hC, hPu, hinf⟩ := planar_nest_uncrossing hS hΔ hbΔ ⟨_, hnest⟩ ⟨P₁, hpaths⟩
  obtain ⟨hCdata, hCdis, hCmono, hCend⟩ := hC
  obtain ⟨hC0, hCl⟩ := hCend (by omega)
  let i₀ : Fin (s + 2) := ⟨0, by omega⟩
  let il : Fin (s + 2) := ⟨s + 2 - 1, by omega⟩
  let idx : Fin s → Fin (s + 2) := fun j => ⟨j + 1, by omega⟩
  have hidx0 : ∀ j, idx j ≠ i₀ := fun j h => by
    have := congrArg Fin.val h
    simp [idx, i₀] at this
  have hidxl : ∀ j, idx j ≠ il := fun j h => by
    have h3 := congrArg Fin.val h
    have h4 := j.2
    simp only [idx, il] at h3
    omega
  have hBC₁ : ∀ j, Disjoint (C (idx j)).V C₁.V := fun j => by
    have : Disjoint (C (idx j)).V (C i₀).V := hCdis (hidx0 j)
    rwa [show C i₀ = C₁ from hC0] at this
  have hBC₂ : ∀ j, Disjoint (C (idx j)).V C₂.V := fun j => by
    have : Disjoint (C (idx j)).V (C il).V := hCdis (hidxl j)
    rwa [show C il = C₂ from hCl] at this
  have hBΓ : ∀ j, (C (idx j)).IsSubdrawing Γ := fun j => by
    obtain ⟨c1, -, -⟩ := hCdata (idx j)
    have hVΓ : ∀ x ∈ (C (idx j)).V, x ∈ Γ.V := fun x hx => by
      have h3 := c1.1 hx
      rw [w.V] at h3
      rcases h3 with (h | h) | h
      · exact h
      · exact absurd h (disjoint_left.mp (hBC₁ j) hx)
      · exact absurd h (disjoint_left.mp (hBC₂ j) hx)
    refine ⟨hVΓ, fun e he => ?_⟩
    obtain ⟨y, z, hl⟩ := ((C (idx j)).toGraph.edge_mem_iff_exists_isLink e).mp he
    exact w.mem_E_of_link hΓ₁ hΓ₂ ((c1.isLink_iff he).mp hl) (hVΓ y hl.2.1) (hVΓ z hl.2.2.1)
  have htrim : ∀ i, ∃ (P : Drawing T) (u v : T), P.IsSubdrawing Γ ∧ P.IsSubdrawing (Pu i) ∧ u ∈ D₁
    ∧ v ∈ D₂ ∧ P.IsPathBetween u v ∧
      ∀ B : Drawing T, B.IsSubdrawing H → Disjoint B.V C₁.V → Disjoint B.V C₂.V → B.V ∩
        (Pu i).V ⊆ P.V ∧ B.E ∩ (Pu i).E ⊆ P.E := fun i => by
    obtain ⟨c1, -, a', ha', b', hb', hpa⟩ := hPu.1 i
    have h3 := (hinf i₀ i).isPreconnected_U
    have h4 := (hinf il i).isPreconnected_U
    rw [show C i₀ = C₁ from hC0] at h3
    rw [show C il = C₂ from hCl] at h4
    exact exists_trimmed_path w hΓ₁ hΓ₂ h12 c1 ha' hb' hpa h3 h4
  choose P u v hPΓ hPPu hu hv hPp hPB using htrim
  refine ⟨P, u, v, fun j => C (idx j), fun j => GM14.discIns Δ (C (idx j)), fun i
    => ⟨hPΓ i, hu i, hv i, hPp i⟩, fun i i' hne => (hPu.2 hne).mono (hPPu i).1 (hPPu i').1, fun j
      => ⟨hBΓ j, (hCdata (idx j)).2.1, ?_⟩,
    fun j j' hj => hCmono (Fin.le_def.mpr (by simpa [idx] using hj)), fun j j' hne => hCdis fun h
      => hne (Fin.ext (by simpa [idx] using congrArg Fin.val h)), fun i j => ?_⟩
  · obtain ⟨-, c2, c3⟩ := hCdata (idx j)
    obtain ⟨⟨d1, d2, d3⟩, -⟩ := GM14.discIns_spec hΔ c2 c3
    have hE₁eq : GM14.discIns Δ C₁ = E₁ := ((GM14.discIns_spec hΔ w.circ₁ (w.bd₁ ▸
      (Surface.discBd_subset _).trans hE₁Δ)).2 E₁ hE₁Δ w.disc₁ w.bd₁).symm
    have hmono : E₁ ⊆ GM14.discIns Δ (C (idx j)) := by
      have h3 : GM14.discIns Δ (C i₀) ⊆ GM14.discIns Δ (C (idx j)) := hCmono (Fin.le_def.mpr
        (Nat.zero_le _))
      rwa [show C i₀ = C₁ from hC0, hE₁eq] at h3
    have hf := hbI (hBΓ j) d3
    refine ⟨d2, d3, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := w.disc₁.nonempty_discInt
      exact side_of_disc hS h₁ d2 hf.1 (hE₁I hz.1) hp (hmono hz.1)
    · intro haΔ
      obtain ⟨z, hz⟩ := w.disc₂.nonempty_discInt
      exact hnotΔ hz (d1 (side_of_disc hS h₂ d2 hf.2 ha (hE₂I hz.1) haΔ))
  · have hBH := (hCdata (idx j)).1
    have hPuH := (hPu.1 i).1
    have hPH := (hPPu i).trans hPuH
    obtain ⟨hV, hE⟩ := hPB i (C (idx j)) hBH (hBC₁ j) (hBC₂ j)
    have heq : Drawing.inf Γ (P i) (C (idx j)) = Drawing.inf H (C (idx j)) (Pu i) := by
      refine Drawing.ext_of_V_E ?_ ?_
      · rw [Drawing.inf_V (hPΓ i) (hBΓ j), Drawing.inf_V hBH hPuH]
        exact subset_antisymm (fun x hx => ⟨hx.2, (hPPu i).1 hx.1⟩) fun x hx => ⟨hV hx, hx.1⟩
      · rw [Drawing.inf_E (hPΓ i), Drawing.inf_E hBH]
        exact subset_antisymm (fun x hx => ⟨hx.2, (hPPu i).2 hx.1⟩) fun x hx => ⟨hE hx, hx.1⟩
    obtain ⟨x, y, hxy⟩ := hinf (idx j) i
    exact ⟨_, x, y, Drawing.inf_isSubdrawing _ _ _, Drawing.inf_U (hPΓ i) (hBΓ j),
      Drawing.inf_V (hPΓ i) (hBΓ j), heq ▸ hxy⟩

end GraphMinor.GM07
