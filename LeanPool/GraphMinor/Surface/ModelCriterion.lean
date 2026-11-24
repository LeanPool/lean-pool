/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CohCard
public import LeanPool.GraphMinor.Surface.TopologyStatements

/-!
# Which model surfaces are homeomorphic

`modelCriterion` proves `ModelCriterionStatement`. Two moves on words give the homeomorphisms
between models. For the
other direction, the number `c` is the number of cuffs. The number `2 * a + b` and the question
whether `b = 0` are read
off from the number of classes of local cocycles with values in `ZMod 2` and `ZMod 3`, by
`card_kCl`.
This is the classical proof that the first cohomology classifies surfaces (see W. Massey, Algebraic
Topology: an
Introduction, Chapter 1, Section 10, with homology in place of cohomology).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

variable {Y : Type u} [TopologicalSpace Y]

theorem image_componentsIn {Y' : Type*} [TopologicalSpace Y'] (e : Y ≃ₜ Y') (F : Set Y) :
    (fun K => e '' K) '' componentsIn F = componentsIn (e '' F) := by
  have key : ∀ x ∈ F, e '' connectedComponentIn F x = connectedComponentIn (e '' F) (e x) := by
    intro x hx
    exact e.image_connectedComponentIn hx
  ext K
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨e x, mem_image_of_mem _ hx, (key x hx).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, key x hx⟩

theorem ncard_cuffs_congr {Y' : Type*} [TopologicalSpace Y'] (e : Y ≃ₜ Y') : (cuffs Y).ncard =
  (cuffs Y').ncard := by
  have h1 := image_componentsIn e (bd Y)
  rw [image_bd_homeomorph e] at h1
  unfold cuffs
  rw [← h1, ncard_image_of_injective _ (image_injective.mpr e.injective)]

/-- Disjoint closed connected sets are the components of their union. -/
theorem componentsIn_eq {C : ℕ → Set Y} {c : ℕ} (hcl : ∀ i < c, IsClosed (C i))
  (hconn : ∀ i < c, IsPreconnected (C i))
    (hne : ∀ i < c, (C i).Nonempty) (hd : ∀ i < c, ∀ j < c, i ≠ j → Disjoint (C i) (C j)) :
    componentsIn (⋃ i ∈ {i | i < c}, C i) = C '' {i | i < c} := by
  have key : ∀ i < c, ∀ x ∈ C i, connectedComponentIn (⋃ i ∈ {i | i < c}, C i) x = C i := by
    intro i hi x hx
    have hsub : C i ⊆ ⋃ i ∈ {i | i < c}, C i := subset_biUnion_of_mem (u := C) hi
    apply Subset.antisymm
    · set K := connectedComponentIn (⋃ i ∈ {i | i < c}, C i) x with hK
      have hKp : IsPreconnected K := isPreconnected_connectedComponentIn
      have hKs : K ⊆ ⋃ i ∈ {i | i < c}, C i := connectedComponentIn_subset _ _
      let D : Set Y := ⋃ j ∈ {j | j < c ∧ j ≠ i}, C j
      have hDcl : IsClosed D := by
        refine Set.Finite.isClosed_biUnion ?_ fun j hj => hcl j hj.1
        exact (finite_lt_nat c).subset fun j hj => hj.1
      have hcov : K ⊆ C i ∪ D := fun z hz => by
        obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp (hKs hz)
        by_cases he : j = i
        · exact .inl (he ▸ hzj)
        · exact .inr (mem_biUnion (x := j) ⟨hj, he⟩ hzj)
      have hxK : x ∈ K := mem_connectedComponentIn (hsub hx)
      by_contra hc
      obtain ⟨z, hz, hzi⟩ := not_subset.mp hc
      have hzD : z ∈ D := (hcov hz).resolve_left hzi
      obtain ⟨w, -, hw1, hw2⟩ := isPreconnected_closed_iff.mp hKp _ _
        (hcl i hi) hDcl hcov ⟨x, hxK, hx⟩ ⟨z, hz, hzD⟩
      obtain ⟨j, hj, hwj⟩ := mem_iUnion₂.mp hw2
      exact Set.disjoint_left.mp (hd i hi j hj.1 (Ne.symm hj.2)) hw1 hwj
    · exact (hconn i hi).subset_connectedComponentIn hx hsub
  ext K
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact ⟨i, hi, (key i hi x hxi).symm⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨x, hx⟩ := hne i hi
    exact ⟨x, mem_biUnion hi hx, key i hi x hx⟩

variable {a b c : ℕ} {f : ℕ × ℂ → Y}

/-- The image of the free side of the hole `i`. -/
noncomputable def holeC (a b c : ℕ) (f : ℕ × ℂ → Y) (i : ℕ) : Set Y :=
  (fun u : ℝ => pmap f (per (4 * a + 2 * b + 3 * c + 2) ((4 * a + 2 * b + 3 * i + 1 : ℕ) + u))) ''
    Icc (0 : ℝ) 1

theorem continuousOn_hole (hf : Presents (sW (ew a b c)) f) (i : ℕ) :
    ContinuousOn (fun u : ℝ => pmap f (per (4 * a + 2 * b + 3 * c + 2)
      ((4 * a + 2 * b + 3 * i + 1 : ℕ) + u))) (Icc 0 1) := by
  refine (pmap_cont hf).comp ?_ fun u _ => mem_ball_per _ _
  have := continuous_per (4 * a + 2 * b + 3 * c + 2)
  fun_prop

/-- The images of the free sides of two holes are disjoint. -/
theorem disjoint_holeC (hf : Presents (sW (ew a b c)) f) {i j : ℕ} (hi : i < c)
  (hj : j < c) (hne : i ≠ j) :
    Disjoint (holeC a b c f i) (holeC a b c f j) := by
  classical
  let V : ℕ → ZMod 2 := fun k => if k = 2 * a + b + 2 * i then 1 else 0
  have hV1 : ∀ k < 2 * a + b, V k = 0 := fun k hk => ite_eq_right (by omega)
  have hV2 : ∀ l < c, V (2 * a + b + 2 * l + 1) = 0 := fun l _ => ite_eq_right (by omega)
  have hV3 : ∀ l, V (2 * a + b + 2 * l) = if l = i then 1 else 0 := fun l => by
    simp only [V]
    by_cases h : l = i
    · simp [h]
    · rw [ite_eq_right (by omega), ite_eq_right h]
  have hS : ∀ l ≤ c, Sm a b c V (4 * a + 2 * b + 3 * l) = 0 := by
    intro l hl
    rw [Sm_holes V hl, Finset.sum_eq_zero fun m hm => hV1 _ (by
      have := Finset.mem_range.mp hm
      omega), Finset.sum_eq_zero fun m hm => hV2 _ (by
      have := Finset.mem_range.mp hm
      omega)]
    simp
  have hSn : Sm a b c V (4 * a + 2 * b + 3 * c + 2) = 0 := by
    rw [Sm_last]
    exact hS c le_rfl
  have hstp : ∀ x y, Stp (sW (ew a b c)) x y → gz a b c V x.2 = gz a b c V y.2 := by
    intro x y hs
    obtain ⟨i', j', p, q, k, e, e', u, h1, h2, h3, hu, rfl, rfl⟩ := stp_iff.mp hs
    obtain ⟨rfl, h4⟩ := sW_get h1
    obtain ⟨rfl, h5⟩ := sW_get h2
    obtain ⟨hp, hl, rfl⟩ := (ew_get_iff _ _ _ _ _ _).mp h4
    obtain ⟨hq, hl', rfl⟩ := (ew_get_iff _ _ _ _ _ _).mp h5
    have hne' : p ≠ q := fun he => h3 (by rw [he])
    have hll := hl.trans hl'.symm
    have ht1 : twin a b c p ≠ p := by
      intro ht
      rcases lab_two hp hq hll with h6 | h6
      · exact hne' h6.symm
      · exact hne' (ht.symm.trans h6.symm)
    have ht2 : twin a b c q ≠ q := by
      intro ht
      rcases lab_two hq hp hll.symm with h6 | h6
      · exact hne' h6
      · exact hne' (h6.trans ht)
    simp only [spt_ew]
    rw [gz_per V hSn hp hu, gz_per V hSn hq (flp_mem hu), gx, gx, ofs_flp', hl, hl',
      Sm_st_zero V hV1 hV2 hp ht1, Sm_st_zero V hV1 hV2 hq ht2]
  have hprel : ∀ x y, PRel (sW (ew a b c)) x y → gz a b c V x.2 = gz a b c V y.2 := by
    intro x y hxy
    induction hxy with
    | rel x y hs => exact hstp x y hs
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h1 h2 => exact h1.trans h2
  have hval : ∀ l < c, ∀ u ∈ Icc (0 : ℝ) 1,
      gz a b c V (per (4 * a + 2 * b + 3 * c + 2) ((4 * a + 2 * b + 3 * l + 1 : ℕ) + u)) = if l
        = i then 1 else 0 := by
    intro l hl u hu
    rw [gz_per V hSn (by omega) hu, gx, lab_t hl (by omega : 1 < 3), show 1 % 2 = 1 from rfl,
      hV2 l hl]
    have h1 : st a b c (4 * a + 2 * b + 3 * l + 1) = 4 * a + 2 * b + 3 * l + 1 := by
      simp only [st, sgn_t hl (by omega : 1 < 3)]
      rfl
    have h2 : Sm a b c V (4 * a + 2 * b + 3 * l + 1) = if l = i then 1 else 0 := by
      have e : 4 * a + 2 * b + 3 * l + 1 = 4 * a + 2 * b + 3 * l + 0 + 1 := rfl
      have h3 := lv_t (a := a) (b := b) (c := c) V hl (δ := 0) (by omega)
      rw [add_zero] at h3
      rw [e, add_zero, Sm_succ, h3]
      simp only [Nat.zero_mod, add_zero, Nat.ofNat_pos, ite_true]
      rw [hS l (by omega), zero_add, hV3]
    rw [h1, h2]
    simp
  have hm : ∀ z ∈ closedBall (0 : ℂ) 1, ((0 : ℕ), z) ∈ Dsk (sW (ew a b c)) := fun z hz =>
    ⟨(ew_mem_dsk a b c).1, by simpa using hz⟩
  rw [Set.disjoint_left]
  rintro _ ⟨u, hu, rfl⟩ ⟨u', hu', he⟩
  have h1 := hprel (0, _) (0, _) ((hf.2.2 _ (hm _ (mem_ball_per _ _)) _ (hm _
    (mem_ball_per _ _))).mp he)
  simp only at h1
  rw [hval j hj u' hu', hval i hi u hu, ite_eq_right hne.symm, ite_eq_left rfl] at h1
  exact absurd h1 (by decide)

/-- The cuffs of a model surface are the images of the free sides of the holes. -/
theorem cuffs_eq_holeC [T2Space Y] (hf : Presents (sW (ew a b c)) f) : cuffs Y
  = holeC a b c f '' {i | i < c} := by
  have hbd := (surface_of_presents (finW_sW _) (isPaired_ew a b c) hf).2
  have hcover : bd Y = ⋃ i ∈ {i | i < c}, holeC a b c f i := by
    rw [hbd]
    ext y
    constructor
    · rintro ⟨x, ⟨i, p, u, hp, hfr, hu, rfl⟩, rfl⟩
      have hi : i = 0 := by
        by_contra hi
        simp [sW, hi, nW] at hp
      subst hi
      rw [sW_zero, ew_length] at hp
      obtain ⟨l, hl, rfl⟩ := (twin_eq_iff hp).mp (twin_of_free hp hfr)
      refine mem_biUnion hl ⟨u, hu, ?_⟩
      rw [spt_ew]
      rfl
    · intro hy
      obtain ⟨l, hl, u, hu, rfl⟩ := mem_iUnion₂.mp hy
      refine ⟨spt (sW (ew a b c)) 0 (4 * a + 2 * b + 3 * l + 1) u, ⟨0, _, u, ?_,
        freeSide_hole hl, hu, rfl⟩, ?_⟩
      · rw [sW_zero, ew_length]
        have : l < c := hl
        omega
      · rw [spt_ew]
        rfl
  have hne : ∀ i < c, (holeC a b c f i).Nonempty := fun i _ => ⟨_, 0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hc := componentsIn_eq (C := holeC a b c f) (c := c)
    (fun i _ => (isCompact_Icc.image_of_continuousOn (continuousOn_hole hf i)).isClosed)
    (fun i _ => isPreconnected_Icc.image _ (continuousOn_hole hf i)) hne (fun i hi j hj h
      => disjoint_holeC hf hi hj h)
  unfold cuffs
  rw [hcover, hc]

theorem ncard_cuffs [T2Space Y] (hf : Presents (sW (ew a b c)) f) : (cuffs Y).ncard = c := by
  have hne : ∀ i < c, (holeC a b c f i).Nonempty := fun i _ => ⟨_, 0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  rw [cuffs_eq_holeC hf, Set.InjOn.ncard_image]
  · have : {i | i < c} = ((Finset.range c : Finset ℕ) : Set ℕ) := by
      ext i
      simp
    rw [this, ncard_coe_finset, Finset.card_range]
  · intro i hi j hj he
    by_contra hij
    obtain ⟨x, hx⟩ := hne i hi
    exact Set.disjoint_left.mp (disjoint_holeC hf hi hj hij) hx (he ▸ hx)

/-- A handle and a cross-cap are three cross-caps. -/
theorem model_tp (a b c : ℕ) : Nonempty (SurfaceModel (a + 1) (b + 1) c ≃ₜ SurfaceModel a
  (b + 3) c) := by
  obtain ⟨ht, f, hf⟩ := presents_ew (a + 1) (b + 1) c
  obtain ⟨w, h1, h2⟩ := exists_modelW_nf.{0} (a + 1) (b + 1) c
  obtain ⟨w', h1', h2'⟩ := exists_modelW_nf.{0} a (b + 3) c
  have h3 : IsNF w (a + 1) (b + 1) c := by
    rcases h2 with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · omega
  have h3' : IsNF w' a (b + 3) c := by
    rcases h2' with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · omega
  have h4 : WEq.{0} w w' := nf_tp h3 h3'
  have h5 := (peq_modelW_ew (a + 1) (b + 1) c (SurfaceModel (a + 1) (b + 1) c)).mpr ⟨f, hf⟩
  obtain ⟨g, hg⟩ := ((h1.trans (PEq.trans h4 h1'.symm)) (SurfaceModel (a + 1) (b + 1) c)).mp h5
  exact model_homeo a (b + 3) c hg

theorem model_to_caps (a b c : ℕ) : Nonempty (SurfaceModel a (b + 1) c ≃ₜ SurfaceModel 0
  (2 * a + b + 1) c) := by
  induction a generalizing b with
  | zero =>
    have e : 2 * 0 + b + 1 = b + 1 := by omega
    rw [e]
    exact ⟨Homeomorph.refl _⟩
  | succ a ih =>
    obtain ⟨e1⟩ := model_tp a b c
    obtain ⟨e2⟩ := ih (b + 2)
    have e : 2 * a + (b + 2) + 1 = 2 * (a + 1) + b + 1 := by omega
    rw [e] at e2
    exact ⟨e1.trans e2⟩

/-- **The model criterion.** -/
theorem modelCriterion : ModelCriterionStatement := by
  refine ⟨isSurface_model, fun a b c a' b' c' => ⟨?_, ?_⟩⟩
  · rintro ⟨e⟩
    obtain ⟨ht, f, hf⟩ := presents_ew a b c
    obtain ⟨ht', f', hf'⟩ := presents_ew a' b' c'
    have hc : c = c' := by
      rw [← ncard_cuffs hf, ← ncard_cuffs hf', ncard_cuffs_congr e]
    have h2 : 2 * a + b = 2 * a' + b' := by
      have h3 := card_kCl (A := ZMod 2) hf
      have h4 := card_kCl (A := ZMod 2) hf'
      rw [card_lam_two, card_kCl_congr e, h4, card_lam_two] at h3
      exact (Nat.pow_right_injective (le_refl 2) h3).symm
    refine ⟨hc, h2, ?_⟩
    have h3 := card_kCl (A := ZMod 3) hf
    have h4 := card_kCl (A := ZMod 3) hf'
    rw [card_kCl_congr e, h4] at h3
    have hinj : Function.Injective fun n : ℕ => 3 ^ n := Nat.pow_right_injective (by norm_num)
    cases b with
    | zero =>
      cases b' with
      | zero => simp
      | succ b' =>
        rw [card_lam_three_succ, card_lam_three_zero] at h3
        have := hinj h3
        omega
    | succ b =>
      cases b' with
      | zero =>
        rw [card_lam_three_succ, card_lam_three_zero] at h3
        have := hinj h3
        omega
      | succ b' => simp
  · rintro ⟨rfl, h2, h3⟩
    cases b with
    | zero =>
      have hb' : b' = 0 := h3.mp rfl
      subst hb'
      have ha : a = a' := by omega
      subst ha
      exact ⟨Homeomorph.refl _⟩
    | succ b =>
      cases b' with
      | zero => exact absurd (h3.mpr rfl) (by omega)
      | succ b' =>
        obtain ⟨e1⟩ := model_to_caps a b c
        obtain ⟨e2⟩ := model_to_caps a' b' c
        have e : 2 * a + b + 1 = 2 * a' + b' + 1 := by omega
        rw [e] at e1
        exact ⟨e1.trans e2.symm⟩

/-- The relation "simpler than" is well-founded, since `4 * a + 2 * b + c` depends only on the space
by the model
criterion. -/
theorem simplerWellFounded : SimplerWellFoundedStatement.{u} := by
  classical
  let rk : (Σ X : Type u, TopologicalSpace X) → ℕ := fun X =>
    sInf {n | ∃ a b c, 4 * a + 2 * b + c = n ∧ @Nonempty (@Homeomorph X.1
      (SurfaceModel a b c) X.2 _)}
  refine Subrelation.wf (r := InvImage (· < ·) rk) ?_ (InvImage.wf rk Nat.lt_wfRel.wf)
  rintro ⟨X, tX⟩ ⟨Y, tY⟩ ⟨a, b, c, a', b', c', ⟨e⟩, ⟨e'⟩, -, -, h⟩
  have h1 : rk ⟨X, tX⟩ ≤ 4 * a + 2 * b + c := Nat.sInf_le ⟨a, b, c, rfl, ⟨e⟩⟩
  have h2 : rk ⟨Y, tY⟩ = 4 * a' + 2 * b' + c' := by
    refine le_antisymm (Nat.sInf_le ⟨a', b', c', rfl, ⟨e'⟩⟩) ?_
    refine le_csInf ⟨_, a', b', c', rfl, ⟨e'⟩⟩ ?_
    rintro _ ⟨a₂, b₂, c₂, rfl, ⟨e₂⟩⟩
    obtain ⟨h3, h4, -⟩ := (modelCriterion.2 a' b' c' a₂ b₂ c₂).mp ⟨e'.symm.trans e₂⟩
    omega
  change rk ⟨X, tX⟩ < rk ⟨Y, tY⟩
  omega

end GraphMinor.Surface
