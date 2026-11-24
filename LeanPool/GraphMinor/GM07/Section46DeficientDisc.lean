/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section2
public import LeanPool.GraphMinor.GM07.Section46Constants
public import LeanPool.GraphMinor.GM07.Section26Path
public import LeanPool.GraphMinor.GM07.Section46DeficientCap
import LeanPool.GraphMinor.GM07.Section3
import LeanPool.GraphMinor.GM07.Section5b
import LeanPool.GraphMinor.GM07.Section46NullCircle
import LeanPool.GraphMinor.GM07.CutBounds
import LeanPool.GraphMinor.Surface.ChartCells
import LeanPool.GraphMinor.Surface.CutLift
import LeanPool.GraphMinor.Surface.SurfacePull
import LeanPool.GraphMinor.Surface.DiscFan
import LeanPool.GraphMinor.GM11.PerimeterExists
import LeanPool.GraphMinor.GM07.Section11a

/-!
# Step 7 of VII (4.6): a short circle that bounds a disc

Page 228. If `F` carries few vertices, (2.6) gives a short `O`-arc `A` through `φ(F)`. By (ii), `A`
is null-homotopic in `Σ` or in `Σ + CHat`. In the second case we replace `A` by an arc of `A` and an
arc of `C`. Either way we get a closed disc in `Σ` whose boundary has the properties of `A`.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The count on a set in `Δ` is the count on its image, if `φ` is injective on the set. -/
theorem Net.ncard_image_inter_of_injOn {N : Net S} {G : Drawing S} {G_D : Drawing N.D}
    (hPull : IsPullbackDrawing N.φ G G_D) {T : Set N.D} (hinj : InjOn N.φ T) :
    (N.φ '' T ∩ G.V).ncard = (G_D.V ∩ T).ncard := by
  have himage : N.φ '' T ∩ G.V = N.φ '' (G_D.V ∩ T) := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hx⟩
      exact ⟨y, ⟨hPull.2 ▸ hx, hy⟩, rfl⟩
    · rintro ⟨y, ⟨hyV, hy⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, by rw [hPull.2] at hyV; exact hyV⟩
  rw [himage, InjOn.ncard_image (hinj.mono inter_subset_right)]

/-- The count on `F` in `Δ` is the count on `φ(F)` in `Σ`, because a proper `I`-arc has
its inner points off `bd(Δ)`, and `φ` is injective there. -/
theorem Net.ncard_image_inner_inter {N : Net S} {G : Drawing S} {G_D : Drawing N.D}
    (hPull : IsPullbackDrawing N.φ G G_D) {F : Set N.D} {s t : N.D}
    (hF : F ∩ bd N.D = {s, t}) :
    (N.φ '' (F \ {s, t}) ∩ G.V).ncard = (G_D.V ∩ (F \ {s, t})).ncard := by
  refine N.ncard_image_inter_of_injOn hPull ?_
  intro x hx y _ hxy
  refine N.interior_inj x (fun hb => hx.2 ?_) y hxy
  rw [← hF]
  exact ⟨hx.1, hb⟩

/-- The two ends of a proper `I`-arc are its points on the boundary. -/
theorem proper_arc_inter_bd {T : Type*} [TopologicalSpace T] {F : Set T} {s t : T}
    (hF : IsProperIArc F) (hEnds : IsLineWithEnds F s t) : F ∩ bd T = {s, t} := by
  obtain ⟨u, v, -, huv, hl⟩ := hF
  rw [huv]
  apply Subset.antisymm
  · rintro x (rfl | rfl)
    · exact seam_line_end_mem hl hEnds
    · exact seam_line_end_mem (GM07.IsLineWithEnds.symm hl) hEnds
  · rintro x (rfl | rfl)
    · exact seam_line_end_mem hEnds hl
    · exact seam_line_end_mem (GM07.IsLineWithEnds.symm hEnds) hl

/-- The opening of the deficient case of VII (4.6), page 228: if `F` carries fewer than
`w + k` vertices, (2.6) gives a `G`-normal `O`-arc `A` through `φ(F)`, inside `φ(F) ∪ U(J)`,
with at most `μ` vertices. -/
theorem Net.exists_short_circle [T1Space S] (hS : IsSurface S) (N : Net S)
    {a b c k : ℕ} (hc : 2 ≤ c) (hmodel : Nonempty (S ≃ₜ SurfaceModel a b c))
    {G J : Drawing S} {G_D : Drawing N.D} (hG : G.IsProper) (hmin : N.IsMinimalFor G)
    (hJ : N.IsSeamGraphFor J) (hPull : IsPullbackDrawing N.φ G G_D)
    (hbd : (G.V ∩ bd S).ncard ≤ 2 * k)
    {F : Set N.D} {s t : N.D} (hFn : G_D.IsNormal F) (hF : IsProperIArc F)
    (hEnds : IsLineWithEnds F s t) (hFbd : F ∩ bd N.D = {s, t})
    (hsmall : (G_D.V ∩ (F \ {s, t})).ncard + 1 ≤ wMaxModel a b c k + k) :
    ∃ A : Set S, G.IsNormal A ∧ IsOArc A ∧ (A ∩ G.V).ncard ≤ muModel a b c k ∧
      N.φ '' F ⊆ A ∧ A ⊆ N.φ '' F ∪ J.U := by
  obtain ⟨A, hAn, hAo, hAc, hFA, hAF⟩ :=
    theorem_2_6_proof hS (by omega) hmodel hG hmin hJ hPull hFn hF hEnds
  refine ⟨A, hAn, hAo, hAc.trans ?_, hFA, hAF⟩
  rw [N.ncard_image_inner_inter hPull hFbd, inter_comm (bd S) G.V]
  unfold muModel
  rw [add_comm (wMaxModel a b c k) k] at hsmall
  exact Nat.add_le_add (Nat.mul_le_mul_left _ hsmall) hbd

/-- A connected part `W` of a line off a closed set `Y`, which contains the ends of the line, lies
in
a subarc that has its ends in `Y` and no other point in `Y`. -/
theorem exists_gap_of_line {X : Type*} [TopologicalSpace X] [T2Space X] {L Y W : Set X}
    {y₁ y₂ : X} (hL : IsLineWithEnds L y₁ y₂) (hY : IsClosed Y) (hy₁ : y₁ ∈ Y) (hy₂ : y₂ ∈ Y)
    (hW : IsPreconnected W) (hWne : W.Nonempty) (hWA : W ⊆ L \ Y) :
    ∃ (B : Set X) (a b : X), a ≠ b ∧ IsLineWithEnds B a b ∧ B ⊆ L ∧ a ∈ Y ∧ b ∈ Y ∧ W ⊆ B ∧
      ∀ x ∈ B, x ∈ Y → x = a ∨ x = b := by
  have hWL : W ⊆ L := fun x hx => (hWA hx).1
  obtain ⟨k, hk, hkr, hk0, hk1⟩ := hL.exists_arc
  obtain ⟨w₀, hw₀⟩ := hWne
  obtain ⟨u₀, hu₀⟩ : w₀ ∈ range k := hkr ▸ hWL hw₀
  subst hu₀
  have hYk : IsClosed (k ⁻¹' Y) := hY.preimage hk.1
  let P : Set unitInterval := k ⁻¹' Y ∩ Iic u₀
  let Q : Set unitInterval := k ⁻¹' Y ∩ Ici u₀
  have hPc : IsClosed P := hYk.inter isClosed_Iic
  have hQc : IsClosed Q := hYk.inter isClosed_Ici
  have hPne : P.Nonempty := ⟨0, by simpa only [mem_preimage, hk0] using hy₁, unitInterval.nonneg'⟩
  have hQne : Q.Nonempty := ⟨1, by simpa only [mem_preimage, hk1] using hy₂, unitInterval.le_one'⟩
  have ha := hPc.csSup_mem hPne (OrderTop.bddAbove _)
  have hb := hQc.csInf_mem hQne (OrderBot.bddBelow _)
  set a := sSup P
  set b := sInf Q
  have hne₀ : ∀ {x}, x ∈ k ⁻¹' Y → x ≠ u₀ := fun {x} hx h => (hWA hw₀).2 (h ▸ hx)
  have hau : a < u₀ := lt_of_le_of_ne ha.2 (hne₀ ha.1)
  have hub : u₀ < b := lt_of_le_of_ne hb.2 (hne₀ hb.1).symm
  have hab : a < b := hau.trans hub
  have hkinj : Function.Injective k := hk.2
  refine ⟨k '' Icc a b, k a, k b, fun h => hab.ne (hkinj h),
    isLineWithEnds_image_Icc_of_injOn hk.1 hab hkinj.injOn, ?_, ha.1, hb.1, ?_, ?_⟩
  · rintro _ ⟨t, -, rfl⟩
    exact hkr ▸ mem_range_self t
  · intro x hx
    obtain ⟨t, rfl⟩ : x ∈ range k := hkr ▸ hWL hx
    have hpre : IsPreconnected (k ⁻¹' W) := by
      have hemb : IsEmbedding k := hk.1.isClosedEmbedding hk.2 |>.isEmbedding
      refine hemb.isInducing.isPreconnected_image.mp ?_
      rw [image_preimage_eq_of_subset (hkr ▸ hWL)]
      exact hW
    have hord := hpre.ordConnected
    have hnot : ∀ c ∈ k ⁻¹' Y, c ∉ k ⁻¹' W := fun c hc hcw => (hWA hcw).2 hc
    refine ⟨t, ⟨?_, ?_⟩, rfl⟩
    · by_contra hlt
      have hta : t < a := not_le.mp hlt
      exact hnot a ha.1 (hord.out hx hw₀ ⟨hta.le, hau.le⟩)
    · by_contra hlt
      have hbt : b < t := not_le.mp hlt
      exact hnot b hb.1 (hord.out hw₀ hx ⟨hub.le, hbt.le⟩)
  · rintro _ ⟨t, ⟨h₁, h₂⟩, rfl⟩ hx
    rcases lt_trichotomy t u₀ with h | h | h
    · have hle : t ≤ a := le_csSup (OrderTop.bddAbove _) ⟨hx, h.le⟩
      exact .inl (congrArg k (le_antisymm hle h₁))
    · exact absurd h (hne₀ hx)
    · have hle : b ≤ t := csInf_le (OrderBot.bddBelow _) ⟨hx, h.le⟩
      exact .inr (congrArg k (le_antisymm h₂ hle))

/-- A connected set in the union of two lines that meet only in their ends, and that misses the
ends, lies in one of the two lines. -/
theorem subset_one_line {X : Type*} [TopologicalSpace X] [T2Space X] {L₁ L₂ W : Set X} {y₁ y₂ : X}
    (hL₁ : IsLineWithEnds L₁ y₁ y₂) (hL₂ : IsLineWithEnds L₂ y₁ y₂) (hi : L₁ ∩ L₂ = {y₁, y₂})
    (hW : IsPreconnected W) (hcov : W ⊆ L₁ ∪ L₂) (h₁ : y₁ ∉ W) (h₂ : y₂ ∉ W) :
    W ⊆ L₁ ∨ W ⊆ L₂ := by
  by_cases h : W ⊆ L₁
  · exact .inl h
  by_cases h' : W ⊆ L₂
  · exact .inr h'
  exfalso
  obtain ⟨x, hx, hxn⟩ := not_subset.mp h
  obtain ⟨y, hy, hyn⟩ := not_subset.mp h'
  obtain ⟨z, hz, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp hW L₁ L₂ hL₁.isCompact.isClosed
    hL₂.isCompact.isClosed hcov ⟨y, hy, (hcov hy).resolve_right hyn⟩
    ⟨x, hx, (hcov hx).resolve_left hxn⟩
  have hzp : z ∈ ({y₁, y₂} : Set X) := hi ▸ ⟨hz₁, hz₂⟩
  rcases hzp with rfl | h
  · exact h₁ hz
  · rw [mem_singleton_iff.mp h] at hz
    exact h₂ hz

/-- A connected part `W` of a circle `A` off a closed set `Y` with two points on `A` lies in an arc
of `A` that has its ends in `Y` and no other point in `Y`. -/
theorem exists_gap_of_circle {X : Type*} [TopologicalSpace X] [T2Space X] {A Y W : Set X}
    (hA : IsOArc A) (hY : IsClosed Y) {y₁ y₂ : X} (hy₁ : y₁ ∈ A ∩ Y) (hy₂ : y₂ ∈ A ∩ Y)
    (hne : y₁ ≠ y₂) (hW : IsPreconnected W) (hWne : W.Nonempty) (hWA : W ⊆ A \ Y) :
    ∃ (B : Set X) (a b : X), a ≠ b ∧ IsLineWithEnds B a b ∧ B ⊆ A ∧ a ∈ Y ∧ b ∈ Y ∧ W ⊆ B ∧
      ∀ x ∈ B, x ∈ Y → x = a ∨ x = b := by
  obtain ⟨L₁, L₂, hL₁, hL₂, hu, hi⟩ := IsOArc.lines hA hy₁.1 hy₂.1 hne
  have hoff : ∀ {y}, y ∈ Y → y ∉ W := fun hy hw => (hWA hw).2 hy
  have hsub : ∃ L, IsLineWithEnds L y₁ y₂ ∧ L ⊆ A ∧ W ⊆ L := by
    rcases subset_one_line hL₁ hL₂ hi hW (hu ▸ fun x hx => (hWA hx).1) (hoff hy₁.2) (hoff hy₂.2)
      with h | h
    · exact ⟨L₁, hL₁, hu ▸ subset_union_left, h⟩
    · exact ⟨L₂, hL₂, hu ▸ subset_union_right, h⟩
  obtain ⟨L, hL, hLA, hWL⟩ := hsub
  obtain ⟨B, a, b, hab, hB, hBL, ha, hb, hWB, hBY⟩ := exists_gap_of_line hL hY hy₁.2 hy₂.2 hW hWne
    fun x hx => ⟨hWL hx, (hWA hx).2⟩
  exact ⟨B, a, b, hab, hB, hBL.trans hLA, ha, hb, hWB, hBY⟩

/-- Step 7 of VII (4.6), page 228: the short circle through `φ(F)` can be chosen to bound a closed
disc of `Σ`. By (ii) the circle `A` from (2.6) bounds a disc in `Σ` or a disc `R` in `Σ + CHat`. If
`R`
misses the inside of the cap, `R` lies in `Σ`. If not, `R` contains the cap, and we take the arc of
`A` through `φ(F)` between two points of `C`, with the arc of `C` given by
`exists_disc_beside_cap`. -/
theorem Net.exists_short_disc [T1Space S] (hS : IsSurface S) (N : Net S)
    {a b c k : ℕ} (hc : 2 ≤ c) (hmodel : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hv : vSurface S k = vModel a b c k)
    {G J : Drawing S} {G_D : Drawing N.D} (hG : G.IsProper) (hmin : N.IsMinimalFor G)
    (hJ : N.IsSeamGraphFor J) (hPull : IsPullbackDrawing N.φ G G_D)
    (hbd : (G.V ∩ bd S).ncard ≤ 2 * k)
    (hii : ∀ B : Set S, G.IsNormal B → IsOArc B → (G.V ∩ B).ncard ≤ vSurface S k →
      IsNullHomotopicOArc B ∨
        ∃ C ∈ cuffs S, IsNullHomotopicOArcInCappedCuff C B ∧ G.V ∩ C ⊆ B)
    (hiii : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard)
    {F : Set N.D} {s t : N.D} (hFn : G_D.IsNormal F) (hF : IsProperIArc F)
    (hEnds : IsLineWithEnds F s t) (hFbd : F ∩ bd N.D = {s, t})
    (hsmall : (G_D.V ∩ (F \ {s, t})).ncard + 1 ≤ wMaxModel a b c k + k) :
    ∃ Z : Set S, IsClosedDisc Z ∧ G.IsNormal (discBd Z) ∧
      (discBd Z ∩ G.V).ncard ≤ muModel a b c k ∧
      N.φ '' F ⊆ discBd Z ∧ discBd Z ⊆ N.φ '' F ∪ J.U := by
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have : T2Space N.D := N.isSurface_D.2.1
  obtain ⟨A, hAn, hAo, hAc, hFA, hAF⟩ := N.exists_short_circle hS hc hmodel hG hmin hJ hPull hbd
    hFn hF hEnds hFbd hsmall
  have hμv : muModel a b c k ≤ vSurface S k := hv ▸ (constants_bounds_4_6 hc).2.1
  have hAv : (G.V ∩ A).ncard ≤ vSurface S k := by
    rw [inter_comm]
    exact hAc.trans hμv
  rcases hii A hAn hAo hAv with hnull | ⟨C, hC, hcap, hVCA⟩
  · obtain ⟨Z, hZ, hbZ⟩ := nullHomotopicOArc_bounds_disc hS hAo hnull
    exact ⟨Z, hZ, hbZ ▸ hAn, hbZ ▸ hAc, hbZ ▸ hFA, hbZ ▸ hAF⟩
  obtain ⟨T, _, j, E, hcp, hbdT⟩ := exists_cappedCuff hS hC
  have : T2Space T := hcp.isSurface.2.1
  have hman : ∀ x : T, IsManifoldPoint x := hcp.isSurface.2.2
  have hn : IsNullHomotopicOArc (j '' A) := hcap.2.2 T j E hcp
  have hOjA : IsOArc (j '' A) := isOArc_image hAo hcp.isEmbedding.continuous.continuousOn
    hcp.isEmbedding.injective.injOn
  obtain ⟨R, hR, hRbd⟩ := nullHomotopicOArc_bounds_disc hcp.isSurface hOjA hn
  have hEd : IsClosedDisc E := hcp.isClosedDisc
  have hjc : IsClosedEmbedding j :=
    hcp.isEmbedding.continuous.isClosedEmbedding hcp.isEmbedding.injective
  have hne : Nonempty S := by
    obtain ⟨x, -⟩ := isOArc_nonempty hAo
    exact ⟨x⟩
  have hintoff : ∀ x ∈ discInt E, x ∉ range j := by
    intro x hx hxj
    have : x ∈ j '' C := hcp.inter_eq ▸ ⟨hxj, hx.1⟩
    exact hx.2 (hcp.discBd_eq ▸ this)
  have hdisR : Disjoint (discInt E) (discBd R) := by
    rw [disjoint_left, hRbd]
    rintro x hx ⟨y, -, rfl⟩
    exact hintoff _ hx (mem_range_self y)
  rcases hR.side hman hEd.isPreconnected_discInt hdisR with hin | hout
  swap
  · have hRj : R ⊆ range j := by
      intro x hx
      rcases (hcp.union_eq ▸ mem_univ x : x ∈ range j ∪ E) with h | h
      · exact h
      · by_cases hb : x ∈ discBd E
        · have : x ∈ j '' C := hcp.discBd_eq ▸ hb
          obtain ⟨y, -, rfl⟩ := this
          exact mem_range_self y
        · exact (disjoint_right.mp hout hx ⟨h, hb⟩).elim
    obtain ⟨hZ, hbZ⟩ := isClosedDisc_preimage hjc hR hRj
    have hbA : discBd (j ⁻¹' R) = A := by
      rw [hbZ, hRbd, preimage_image_eq _ hcp.isEmbedding.injective]
    exact ⟨_, hZ, hbA ▸ hAn, hbA ▸ hAc, hbA ▸ hFA, hbA ▸ hAF⟩
  have hER : E ⊆ R := hEd.subset_closure_discInt.trans
    (closure_minimal (hin.trans (discInt_subset _)) hR.isClosed)
  have hCO : IsOArc C := (cuff_statement S hS).2.2 C hC
  have hCc : IsClosed C := hCO.isCompact.isClosed
  have hCbd : C ⊆ bd S := fun x hx => sUnion_cuffs (S := S) ▸ ⟨C, hC, hx⟩
  have hCU : C ⊆ J.U := fun x hx => hJ.2.1 ▸ N.bd_subset_seamU (hCbd hx)
  have hAcomp : IsCompact A := hAo.isCompact
  have hne2 : s ≠ t := hEnds.ne'
  obtain ⟨y₁, hy₁, y₂, hy₂, hy₁₂⟩ := (Set.one_lt_ncard
    (G.finite_V.subset inter_subset_left)).mp (by have := hiii C hC; omega :
      1 < (G.V ∩ C).ncard)
  have hW : IsPreconnected (N.φ '' (F \ {s, t})) :=
    hEnds.isPreconnected_diff.image _ N.quotientMap_φ.continuous.continuousOn
  have hWne : (N.φ '' (F \ {s, t})).Nonempty := by
    obtain ⟨p, hp, hp0, hp1⟩ := exists_mem_line_ne hEnds hne2
    exact ⟨_, p, ⟨hp, by rintro (h | h); exacts [hp0 h, hp1 h]⟩, rfl⟩
  have hWoff : ∀ x ∈ N.φ '' (F \ {s, t}), x ∉ J.U := by
    rintro _ ⟨y, hy, rfl⟩ hxU
    have hybd : y ∈ bd N.D := by
      have : N.φ y ∈ N.seamU := hJ.2.1 ▸ hxU
      rwa [← mem_preimage, N.preimage_seamU] at this
    exact hy.2 (hFbd ▸ ⟨hy.1, hybd⟩)
  have hWA : N.φ '' (F \ {s, t}) ⊆ A \ (A ∩ C) := by
    intro x hx
    exact ⟨hFA (image_mono sdiff_subset hx), fun h => hWoff x hx (hCU h.2)⟩
  obtain ⟨B, p, q, hpq, hB, hBA, hpY, hqY, hWB, hBY⟩ := exists_gap_of_circle hAo
    (hAcomp.isClosed.inter hCc) (y₁ := y₁) (y₂ := y₂)
    ⟨hVCA hy₁, hVCA hy₁, hy₁.2⟩ ⟨hVCA hy₂, hVCA hy₂, hy₂.2⟩ hy₁₂ hW hWne hWA
  have hFB : N.φ '' F ⊆ B := by
    have h1 := image_mono (f := N.φ) hEnds.subset_closure_diff
    have h2 := image_closure_subset_closure_image (s := F \ {s, t})
      N.quotientMap_φ.continuous
    exact (h1.trans h2).trans (closure_minimal hWB hB.isCompact.isClosed)
  have hjB := IsLineWithEnds.map_of_embedding hcp.isEmbedding hB
  have hbE : ∀ {x}, x ∈ C → j x ∈ discBd E := fun {x} hx => hcp.discBd_eq ▸ mem_image_of_mem j hx
  have hBE : j '' B ∩ E ⊆ {j p, j q} := by
    rintro _ ⟨⟨y, hy, rfl⟩, hyE⟩
    have hyC : j y ∈ j '' C := hcp.inter_eq ▸ ⟨mem_range_self y, hyE⟩
    obtain ⟨y', hy', hyy⟩ := hyC
    have hyC' : y ∈ C := hcp.isEmbedding.injective hyy ▸ hy'
    rcases hBY y hy ⟨hBA hy, hyC'⟩ with h | h
    · exact .inl (congrArg j h)
    · exact .inr (congrArg j h)
  obtain ⟨Z', C', hC', hC'E, hZ', hbZ', hZoff, -⟩ := exists_disc_beside_cap hman
    (fun h => hpq (hcp.isEmbedding.injective h)) hR hEd hER hdisR hjB
    (hRbd ▸ image_mono hBA) hBE (hbE hpY.2) (hbE hqY.2)
  have hZj : Z' ⊆ range j := by
    intro x hx
    rcases (hcp.union_eq ▸ mem_univ x : x ∈ range j ∪ E) with h | h
    · exact h
    · by_cases hb : x ∈ discBd E
      · have : x ∈ j '' C := hcp.discBd_eq ▸ hb
        obtain ⟨y, -, rfl⟩ := this
        exact mem_range_self y
      · exact (disjoint_left.mp hZoff hx ⟨h, hb⟩).elim
  obtain ⟨hZ, hbZ⟩ := isClosedDisc_preimage hjc hZ' hZj
  have hbsub : discBd (j ⁻¹' Z') ⊆ C ∪ B := by
    rw [hbZ, hbZ']
    rintro x (h | h)
    · have hx : j x ∈ j '' C := hcp.discBd_eq ▸ hC'E h
      obtain ⟨y, hy, hyx⟩ := hx
      exact .inl (hcp.isEmbedding.injective hyx ▸ hy)
    · obtain ⟨y, hy, hyx⟩ := h
      exact .inr (hcp.isEmbedding.injective hyx ▸ hy)
  have hBsub : B ⊆ discBd (j ⁻¹' Z') := by
    rw [hbZ, hbZ']
    exact fun x hx => .inr (mem_image_of_mem j hx)
  refine ⟨_, hZ, ?_, ?_, hFB.trans hBsub, ?_⟩
  · rintro x ⟨hx, hxU⟩
    rcases hbsub hx with h | h
    · exact hG ⟨hCbd h, hxU⟩
    · exact hAn ⟨hBA h, hxU⟩
  · refine le_trans (Set.ncard_le_ncard ?_ ((hAcomp.isClosed.inter hCc |> fun _
      => G.finite_V.subset inter_subset_right))) hAc
    · rintro x ⟨hx, hxV⟩
      rcases hbsub hx with h | h
      · exact ⟨hVCA ⟨hxV, h⟩, hxV⟩
      · exact ⟨hBA h, hxV⟩
  · intro x hx
    rcases hbsub hx with h | h
    · exact .inr (hCU h)
    · exact hAF (hBA h)

end GraphMinor.GM07
