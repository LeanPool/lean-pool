/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section2
public import LeanPool.GraphMinor.GM07.Section46SeamPartsDefs
public import LeanPool.GraphMinor.GM07.Section46Constants
public import LeanPool.GraphMinor.GM07.Section46DeficientDisc
public import LeanPool.GraphMinor.GM07.Section46DeficientSide
public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM07.Section46EdgeContacts
import LeanPool.GraphMinor.GM07.Section46LongEdges
import LeanPool.GraphMinor.GM07.Section2Base
import LeanPool.GraphMinor.GM07.Section46JPlus
import LeanPool.GraphMinor.GM07.Section46ClaimTwo
import LeanPool.GraphMinor.Surface.DiscMerge

/-!
# Steps 7 to 10 of VII (4.6): the deficient test arc

Pages 228-230. We have a test arc `F` in `Δ` and a set `Λ` of at most `w + k` disjoint
vertex sets, each meeting both sides of `F`. We must show that `F` carries at least `|Λ|` vertices
of `φ⁻¹(G)`. If not, (2.6) and (ii) give a closed disc with a short boundary `A` through `φ(F)`. The
open disc misses `U(J)`, and one side `C` of `F` maps into `A ∩ U(J)`. By claim (2), `φ` maps the
closed half `R` of `Δ` with boundary `C ∪ F` one to one onto the disc, so `φ(C) = A - φ(F)` and `φ`
is one to one on `C`. By claim (3), a point of a
member of `Λ` on `C` lies over `U(K)`. The two buffers of length `μ` then put `C` inside one long
edge, and minimality of the net bounds the vertices on `C` by those on `F`.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The deficient test arc of VII (4.6), pages 228-230. Here `(N, J)` is the minimal net, `K` is
the graph of central edges, `l z` is the point `l(z)` with its paths, and `F` is a test arc with
sides `C₁`, `C₂`. The set `Λ` is a family of at most `w + k` disjoint sets, each meeting both
sides, and each of their points on a side is a vertex of `φ⁻¹(G)` lying over `U(K)` or equal to some
`l(z)`. -/
theorem Net.deficient_test_arc [T1Space S] (hS : IsSurface S) [ConnectedSpace S] (N : Net S)
    (hcuffs : 2 ≤ (cuffs S).ncard) {a b c k : ℕ} (hc : 2 ≤ c)
    (hmodel : Nonempty (S ≃ₜ SurfaceModel a b c)) (hv : vSurface S k = vModel a b c k)
    {G J K : Drawing S} {G_D : Drawing N.D} (hG : G.IsProper) (hmin : N.IsMinimalFor G)
    (hJ : N.IsSeamGraphFor J) (hPull : IsPullbackDrawing N.φ G G_D)
    (hbd : (G.V ∩ bd S).ncard ≤ 2 * k)
    (hi : ∀ B : Set S, G.IsNormal B → IsIArc B → (G.V ∩ B).ncard ≤ vSurface S k →
      ∃ C ∈ cuffs S, lineEnds B ⊆ C)
    (hii : ∀ B : Set S, G.IsNormal B → IsOArc B → (G.V ∩ B).ncard ≤ vSurface S k →
      IsNullHomotopicOArc B ∨
        ∃ C ∈ cuffs S, IsNullHomotopicOArcInCappedCuff C B ∧ G.V ∩ C ⊆ B)
    (hiii : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard)
    {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    (sK tK : longSeamEdges G J (muModel a b c k) (wMaxModel a b c k) → unitInterval)
    (hcut : ∀ e, sK e ∈ Ioo 0 1 ∧ tK e ∈ Ioo 0 1 ∧ sK e < tK e ∧
      (γ e.1 '' Iic (sK e) ∩ G.V).ncard = muModel a b c k + 1 ∧
      (γ e.1 '' Ici (tK e) ∩ G.V).ncard = muModel a b c k + 1)
    (hKU : K.U ⊆ ⋃ e, γ e.1 '' Icc (sK e) (tK e))
    (l : S → N.D)
    (hl : ∀ z ∈ G.V ∩ bd S, N.φ (l z) = z ∧ ∃ C ∈ cuffs S, z ∈ C ∧
      ∃ (n : ℕ) (P : Fin n → Drawing S) (e : Fin n → S),
        (∀ i, (P i).IsSubdrawing G ∧ e i ∈ G.V ∩ (bd S \ C) ∧ (P i).IsPathBetween z (e i)) ∧
        (∀ i j, i ≠ j → Disjoint ((P i).V \ {z, e i}) ((P j).V \ {z, e j})) ∧
        ∃ I : Finset (Fin n), muModel a b c k ≤ I.card ∧
          ∀ i ∈ I, ∃ f ∈ (P i).E, l z ∈ closure (N.φ ⁻¹' f) ∧
            ∀ x ∈ closure (N.φ ⁻¹' f), N.φ x = z → x = l z)
    {F : Set N.D} {s t : N.D} {C₁ C₂ : Set N.D} (hFn : G_D.IsNormal F) (hF : IsProperIArc F)
    (hEnds : IsLineWithEnds F s t) (hC : componentsIn (bd N.D \ {s, t}) = {C₁, C₂})
    (hne : C₁ ≠ C₂) {Λ : Set (Set N.D)} (hΛc : Λ.ncard ≤ wMaxModel a b c k + k)
    (hΛd : Λ.PairwiseDisjoint id)
    (hΛm : ∀ lam ∈ Λ, (lam ∩ C₁).Nonempty ∧ (lam ∩ C₂).Nonempty)
    (hΛv : ∀ lam ∈ Λ, ∀ d ∈ lam ∩ (C₁ ∪ C₂), d ∈ G_D.V ∧
      (N.φ d ∈ K.U ∨ ∃ z ∈ G.V ∩ bd S, d = l z)) :
    Λ.ncard ≤ (G_D.V ∩ (F \ {s, t})).ncard := by
  by_contra hlt
  have : T2Space S := hS.2.1
  have : T2Space N.D := N.isSurface_D.2.1
  have hFbd : F ∩ bd N.D = {s, t} := proper_arc_inter_bd hF hEnds
  obtain ⟨Z, hZ, hZn, hZc, hFZ, hZF⟩ := N.exists_short_disc hS hc hmodel hv hG hmin hJ hPull hbd
    hii hiii hFn hF hEnds hFbd (by omega)
  have hμv : muModel a b c k ≤ vSurface S k := hv ▸ (constants_bounds_4_6 hc).2.1
  have hmodelc : ∀ {a' b' c' : ℕ}, c' < 2 → ¬Nonempty (S ≃ₜ SurfaceModel a' b' c') := by
    rintro a' b' c' hlt' ⟨e⟩
    have := ncard_cuffs_eq_of_surface_model e
    omega
  have hval := theorem_2_3_proof hS (hmodelc (by omega)) (hmodelc (by omega)) (hmodelc
    (by omega)) hG
    hmin hJ
  have hmiss := N.disc_misses_seam hS hcuffs hJ hval hPull hFn hEnds hFbd hZ hFZ hZF
  have hsbd : s ∈ F ∩ bd N.D := hFbd.symm ▸ Or.inl rfl
  have htbd : t ∈ F ∩ bd N.D := hFbd.symm ▸ Or.inr rfl
  have hsU : N.φ s ∈ J.U := hJ.2.1 ▸ mem_image_of_mem N.φ hsbd.2
  have htU : N.φ t ∈ J.U := hJ.2.1 ▸ mem_image_of_mem N.φ htbd.2
  have hsubV : J.V ∪ {N.φ s, N.φ t} ⊆ J.U := by
    refine union_subset J.V_subset_U ?_
    rintro x (rfl | h)
    · exact hsU
    · exact (mem_singleton_iff.mp h) ▸ htU
  obtain ⟨J', hU', hV'⟩ := exists_drawing_with_more_vertices J (J.finite_V.union (by simp))
    subset_union_left hsubV
  obtain ⟨X, hXc, hXU, hXA, hAX, hsX, htX, -, -⟩ := N.exists_seam_arc hJ hPull hFn hEnds hFbd
    hZ.isOArc_discBd hFZ hZF hU' (hV' ▸ Or.inr (Or.inl rfl)) (hV' ▸ Or.inr (Or.inr rfl))
  obtain ⟨R, R', C, hCe, hR, hR'c, hRu, hCbd, hCR, hCR', hbR, hRZ, hCA, hYline, hCst⟩ :=
    N.exists_disc_side hS hJ hEnds hFbd hC hZ hmiss hFZ hZF
  -- Claim (2): `φ` maps `R` and its boundary `C ∪ F` one to one onto `Z` and `A`, so `φ(C) = A -
  -- φ(F)`.
  have hmanD := N.isSurface_D.2.2
  have hRint : InjOn N.φ (discInt R) := fun x hx y _ he =>
    N.interior_inj x (fun hb => hb (isInteriorPoint_of_mem_discInt hmanD hR hx)) y he
  have hRbd : N.φ '' discBd R ⊆ discBd Z := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hbR] at hx
    rcases hx with hx | hx
    · exact hCA x hx
    · exact hFZ (mem_image_of_mem _ hx)
  obtain ⟨hinjR, -, hbdR⟩ := injOn_of_disc_to_disc hmanD hS.2.2 N.quotientMap_φ.continuous
    (finite_preimage_singleton N) hR hZ
    hRint hRZ hRbd
  have hCF : Disjoint C F := by
    rw [disjoint_left]
    intro x hxC hxF
    have hx : x ∈ F ∩ bd N.D := ⟨hxF, hCbd hxC⟩
    rw [hFbd] at hx
    exact (eq_empty_iff_forall_notMem.mp hCst) x ⟨hxC, hx⟩
  have hclaim2 : N.φ '' C = discBd Z \ N.φ '' F := by
    rw [← hbdR, hbR]
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨mem_image_of_mem _ (.inl hx), ?_⟩
      rintro ⟨y, hy, he⟩
      have hyR : y ∈ discBd R := hbR ▸ .inr hy
      have hxR : x ∈ discBd R := hbR ▸ .inl hx
      have := hinjR (Surface.discBd_subset R hyR) (Surface.discBd_subset R hxR) he
      exact disjoint_left.mp hCF hx (this ▸ hy)
    · rintro _ ⟨⟨x, hx | hx, rfl⟩, hn⟩
      · exact mem_image_of_mem _ hx
      · exact absurd (mem_image_of_mem _ hx) hn
  have hCX : ∀ x ∈ C, N.φ x ∈ X := by
    intro x hx
    have hxA : N.φ x ∈ discBd Z \ N.φ '' F := hclaim2 ▸ mem_image_of_mem N.φ hx
    exact (hAX hxA.1).resolve_left fun h => hxA.2 (image_mono sdiff_subset h)
  have hnorm : G.IsNormal J.U := by
    rw [hJ.2.1]
    exact ((N.isNormalFor_iff hS G).mp hmin.1).2
  have hbdJ : bd S ⊆ J.U := hJ.2.1 ▸ N.bd_subset_seamU
  have hmemC : ∀ lam ∈ Λ, (lam ∩ C).Nonempty := by
    intro lam hlam
    rcases hCe with rfl | rfl
    · exact (hΛm lam hlam).1
    · exact (hΛm lam hlam).2
  have hsideC : ∀ {d : N.D}, d ∈ C → d ∈ C₁ ∪ C₂ := by
    intro d hd
    rcases hCe with rfl | rfl
    · exact .inl hd
    · exact .inr hd
  -- Claim (3).
  have hclaim : ∀ lam ∈ Λ, ∀ d ∈ lam ∩ C, N.φ d ∈ K.U := by
    intro lam hlam d hd
    obtain ⟨-, h | ⟨z, hz, rfl⟩⟩ := hΛv lam hlam d ⟨hd.1, hsideC hd.2⟩
    · exact h
    exfalso
    obtain ⟨hφ, C', hC', hzC', n, P, e, hP, hdis, I, hI, hfirst⟩ := hl z hz
    have hzA : z ∈ discBd Z := hφ ▸ hCA _ hd.2
    refine no_lift_on_side hS.2.2 hZ hmiss hbdJ hZn hZc hμv hi hz.1 hzA hC' hzC' hP hdis hI ?_
    intro i hiI
    obtain ⟨f, hf, hlc, -⟩ := hfirst i hiI
    have hfG : f ∈ G.E := (hP i).1.2 hf
    have hfoff := hfG.2.1
    refine ⟨f, hf, ?_, ?_⟩
    · have h₁ := image_closure_subset_closure_image (s := N.φ ⁻¹' f)
        N.quotientMap_φ.continuous (mem_image_of_mem _ hlc)
      rw [hφ] at h₁
      exact closure_mono (image_preimage_subset _ _) h₁
    · have hdisA : Disjoint f (discBd Z) := by
        rw [disjoint_left]
        intro x hxf hxA
        exact (hfoff hxf).2 (hZn ⟨hxA, (hfoff hxf).1⟩)
      obtain ⟨y, hyR', hyf⟩ := mem_closure_iff.mp hlc _ hR'c.isOpen_compl
        (fun h => disjoint_left.mp hCR' hd.2 h)
      have hyf' : N.φ y ∈ f := hyf
      have hyb : y ∉ bd N.D := fun h =>
        (hfoff hyf').2 (hnorm ⟨hJ.2.1 ▸ mem_image_of_mem N.φ h, (hfoff hyf').1⟩)
      have hyF : y ∉ F := by
        intro h
        have hyU : y ∈ G_D.U := by
          rw [hPull.1]
          exact (hfoff hyf').1
        have hyV : y ∈ G_D.V := hFn ⟨h, hyU⟩
        rw [hPull.2] at hyV
        exact (hfoff hyf').2 hyV
      have hyR : y ∈ R := (hRu ▸ mem_univ y : y ∈ R ∪ R').resolve_right hyR'
      have hyint : y ∈ discInt R := ⟨hyR, fun h => by
        rw [hbR] at h
        rcases h with h | h
        · exact hyb (hCbd h)
        · exact hyF h⟩
      have hyZ : N.φ y ∈ discInt Z := hRZ (mem_image_of_mem _ hyint)
      rcases hZ.side hS.2.2 hfG.2.2.1.isConnected.isPreconnected hdisA with h | h
      · exact h
      · exact (disjoint_left.mp h hyf' hyZ.1).elim
  -- A long edge through `φ(d)`, and the two buffers.
  have hΛne : Λ.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    rw [hemp, ncard_empty] at hlt
    omega
  obtain ⟨lam₀, hlam₀⟩ := hΛne
  obtain ⟨d₀, hd₀⟩ := hmemC lam₀ hlam₀
  obtain ⟨e, u, hu, hud⟩ := mem_iUnion.mp (hKU (hclaim lam₀ hlam₀ d₀ hd₀))
  have hXfin : (X ∩ G.V).Finite := G.finite_V.subset inter_subset_right
  have hXsub : X ∩ G.V ⊆ discBd Z ∩ G.V := fun _ hx => ⟨hXA hx.1, hx.2⟩
  have hXc' : (X ∩ G.V).ncard ≤ muModel a b c k :=
    (Set.ncard_le_ncard hXsub (G.finite_V.subset inter_subset_right)).trans hZc
  have hbuf : ∀ T : Set unitInterval,
      (γ e.1 '' T ∩ G.V).ncard = muModel a b c k + 1 → ∃ r ∈ T, γ e.1 r ∉ X := by
    intro T hT
    by_contra hno
    push Not at hno
    have hsub : γ e.1 '' T ∩ G.V ⊆ X ∩ G.V := by
      rintro _ ⟨⟨r, hr, rfl⟩, hxV⟩
      exact ⟨hno r hr, hxV⟩
    have := Set.ncard_le_ncard hsub hXfin
    omega
  obtain ⟨hs0, ht0, hlt', hleft, hright⟩ := hcut e
  obtain ⟨p, hp, hpX⟩ := hbuf _ hleft
  obtain ⟨q, hq, hqX⟩ := hbuf _ hright
  have hd₀X := hCX d₀ hd₀.2
  rw [← hud] at hd₀X
  have hup : p < u := lt_of_le_of_ne ((show p ≤ sK e from hp).trans hu.1)
    fun h => hpX (h ▸ hd₀X)
  have huq : u < q := lt_of_le_of_ne (hu.2.trans (show tK e ≤ q from hq))
    fun h => hqX (h ▸ hd₀X)
  have hXpiece := subset_edge_piece hγ e.2.1 hXc hXU hpX hqX hd₀X ⟨u, ⟨hup, huq⟩, rfl⟩
  have hXe : X ⊆ e.1 := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := hXpiece hx
    refine (hγ.image e.1 e.2.1).subset ⟨r, ?_, rfl⟩
    exact ⟨lt_of_le_of_lt unitInterval.nonneg' hr.1, lt_of_lt_of_le hr.2 unitInterval.le_one'⟩
  -- The side `C` lies in one side of a pair, and the exchange gives the last inequality.
  have hYX : ∀ y ∈ C ∪ {s, t}, N.φ y ∈ X := by
    rintro y (h | rfl | h)
    · exact hCX y h
    · exact hsX
    · exact (mem_singleton_iff.mp h) ▸ htX
  have hoffbd : ∀ y ∈ C ∪ {s, t}, N.φ y ∉ bd S := fun y hy h =>
    disjoint_left.mp (longSeamEdge_disjoint_bd hS N hJ hbd e.2) (hXe (hYX y hy)) h
  have hoffV : ∀ y ∈ C ∪ {s, t}, N.φ y ∉ N.seamV := fun y hy h =>
    (e.2.1.2.1 (hXe (hYX y hy))).2 (hJ.2.2 ▸ h)
  have hYbd : C ∪ {s, t} ⊆ bd N.D := by
    rintro y (h | rfl | h)
    · exact hCbd h
    · exact hsbd.2
    · exact (mem_singleton_iff.mp h) ▸ htbd.2
  obtain ⟨i, hside⟩ := N.exists_side_of_connected (line_preconnected hYline)
    ⟨s, .inr (.inl rfl)⟩ hYbd hoffbd hoffV
  obtain ⟨hle, -⟩ := N.contacts_le_of_side hS i hmin hEnds hFbd hPull hFn hYline hside hoffV
  have hYC : (C ∪ {s, t}) \ {s, t} = C := by
    rw [union_sdiff_right]
    exact sdiff_eq_left.mpr (disjoint_iff_inter_eq_empty.mpr hCst)
  rw [hYC, N.ncard_image_inter_of_injOn hPull (hinjR.mono hCR),
    N.ncard_image_inner_inter hPull hFbd] at hle
  have hchoose : ∀ lam : Λ, ∃ d, d ∈ lam.1 ∩ C := fun lam => hmemC lam.1 lam.2
  choose dd hdd using hchoose
  have hcount : Λ.ncard ≤ (G_D.V ∩ C).ncard := by
    have hfinV : (G_D.V ∩ C).Finite := G_D.finite_V.subset inter_subset_left
    have hinjd : Function.Injective fun lam : (Λ : Set (Set N.D)) => dd lam := by
      intro lam lam' heq
      by_contra hne
      have hdis := hΛd lam.2 lam'.2 (fun h => hne (Subtype.ext h))
      have heq' : dd lam = dd lam' := heq
      exact disjoint_left.mp hdis (hdd lam).1 (heq'.symm ▸ (hdd lam').1)
    have hmaps : ∀ lam : Λ, dd lam ∈ G_D.V ∩ C := fun lam =>
      ⟨(hΛv lam.1 lam.2 _ ⟨(hdd lam).1, hsideC (hdd lam).2⟩).1, (hdd lam).2⟩
    have : Finite ↥(G_D.V ∩ C) := hfinV.to_subtype
    have hle' := Nat.card_le_card_of_injective (fun lam : Λ => (⟨dd lam, hmaps lam⟩ :
      ↥(G_D.V ∩ C))) (fun x y h => hinjd (congrArg Subtype.val h))
    simpa only [Nat.card_coe_set_eq] using hle'
  omega

end GraphMinor.GM07
