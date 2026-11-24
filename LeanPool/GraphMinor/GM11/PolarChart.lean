/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RadialCap
public import LeanPool.GraphMinor.GM11.Cylinder

/-!
# Polar charts

Near a point of a surface, a drawing looks like a finite set of rays from one centre. This file
makes
that precise. A *fan* at `v` (`IsFan`) is a cyclic list of closed discs around `v`, in which two
consecutive discs share a line from `v`. Then `exists_polar_of_fan` gives an embedding `Φ` of the
closed
unit disc with `Φ 0 = v`, in which every ray from the centre stays in one sector or on one line.

The sets that this is used for are closed unions of atoms of a drawing. Such a set is a cone in the
chart,
and so it is simply-connected near each of its points. These local facts are what (3.1) and (7.3) of
Graph
Minors XI need for nice sets.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## The closed disc as a cone over the circle -/

instance : CompactSpace ClosedUnitDisc :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)

/-- The plane as the complex numbers. -/
noncomputable def planeOf : ℂ ≃ₗᵢ[ℝ] EuclideanPlane := Complex.orthonormalBasisOneI.repr

/-- The centre of the closed unit disc. -/
noncomputable def polarCentre : ClosedUnitDisc := ⟨0, by simp [ClosedUnitDisc]⟩

/-- The point of the closed disc at distance `1 - t` from the centre, in direction `z`. -/
noncomputable def coneMap (p : Circle × I) : ClosedUnitDisc :=
  ⟨(1 - p.2.1 : ℝ) • planeOf (p.1 : ℂ), by
    have h₀ := p.2.2.1
    have h₁ := p.2.2.2
    simp only [ClosedUnitDisc, Metric.mem_closedBall, dist_zero_right, norm_smul,
      LinearIsometryEquiv.norm_map, Circle.norm_coe, mul_one, Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith)]
    linarith⟩

/-- Multiply a point of the closed disc by `c ∈ [0, 1]`. -/
noncomputable def discScale (c : I) (x : ClosedUnitDisc) : ClosedUnitDisc :=
  ⟨(c.1 : ℝ) • x.1, by
    have h₀ := c.2.1
    have h₁ := c.2.2
    have hx : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
    simp only [ClosedUnitDisc, Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg h₀]
    nlinarith [norm_nonneg x.1]⟩

theorem continuous_coneMap : Continuous coneMap := by
  refine Continuous.subtype_mk ?_ _
  have : Continuous fun z : Circle => planeOf (z : ℂ) :=
    planeOf.continuous.comp continuous_subtype_val
  fun_prop

theorem continuous_discScale : Continuous fun p : I × ClosedUnitDisc => discScale p.1 p.2 := by
  refine Continuous.subtype_mk ?_ _
  fun_prop

theorem discScale_coneMap (c : I) (hc : 0 < c) (p : Circle × I) (hp : p.2 < 1) :
    ∃ t : I, t < 1 ∧ discScale c (coneMap p) = coneMap (p.1, t) := by
  have h₀ := p.2.2.1
  have h₁ := p.2.2.2
  have hc₀ := c.2.1
  have hc₁ := c.2.2
  have hlt : p.2.1 < 1 := hp
  have hcp : 0 < c.1 := hc
  have hmem : (1 - c.1 * (1 - p.2.1) : ℝ) ∈ I := ⟨by nlinarith, by nlinarith⟩
  refine ⟨⟨_, hmem⟩, ?_, Subtype.ext ?_⟩
  · have : (1 - c.1 * (1 - p.2.1) : ℝ) < 1 := by nlinarith
    exact this
  · simp only [discScale, coneMap, smul_smul]
    congr 1
    ring

theorem discScale_zero (x : ClosedUnitDisc) : discScale 0 x = polarCentre :=
  Subtype.ext (by simp [discScale, polarCentre])

theorem discScale_one (x : ClosedUnitDisc) : discScale 1 x = x :=
  Subtype.ext (by simp [discScale])

theorem coneMap_top (z : Circle) : coneMap (z, 1) = polarCentre :=
  Subtype.ext (by simp [coneMap, polarCentre])

theorem coneMap_surjective : Function.Surjective coneMap := by
  rintro ⟨x, hx⟩
  have hn : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  by_cases h0 : x = 0
  · subst h0
    exact ⟨(1, 1), Subtype.ext (by simp [coneMap])⟩
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr h0
  let w : ℂ := planeOf.symm x
  have hw : ‖w‖ = ‖x‖ := planeOf.symm.norm_map x
  have hne : w ≠ 0 := norm_pos_iff.mp (hw ▸ hpos)
  let z : Circle := ⟨(‖w‖ : ℂ)⁻¹ * w, mem_sphere_zero_iff_norm.2 (by
    rw [norm_mul, norm_inv, Complex.norm_real, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne))⟩
  have hlt : (1 - ‖x‖ : ℝ) ∈ I := ⟨by linarith, by linarith⟩
  refine ⟨(z, ⟨1 - ‖x‖, hlt⟩), Subtype.ext ?_⟩
  have hzc : (z : ℂ) = (‖x‖ : ℂ)⁻¹ * w := by
    rw [← hw]
  have hsmul : (z : ℂ) = (‖x‖⁻¹ : ℝ) • w := by
    rw [hzc, Complex.real_smul]
    push_cast
    ring
  simp only [coneMap, sub_sub_cancel]
  rw [hsmul, map_smul, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  exact planeOf.apply_symm_apply x

private theorem coneMap_norm (p : Circle × I) : ‖(coneMap p).1‖ = 1 - p.2.1 := by
  have h₁ := p.2.2.2
  simp only [coneMap, norm_smul, LinearIsometryEquiv.norm_map, Circle.norm_coe, mul_one,
    Real.norm_eq_abs]
  exact abs_of_nonneg (by linarith)

private theorem coneMap_eq {p q : Circle × I} (h : coneMap p = coneMap q) (hp : p.2 < 1) : p = q
  := by
  have hn := congrArg (fun x : ClosedUnitDisc => ‖x.1‖) h
  simp only [coneMap_norm] at hn
  have ht : p.2 = q.2 := Subtype.ext (by linarith)
  have hv := congrArg Subtype.val h
  simp only [coneMap] at hv
  rw [← ht] at hv
  have hne : (1 - p.2.1 : ℝ) ≠ 0 := by
    have : p.2.1 < 1 := hp
    linarith
  have := smul_right_injective _ hne hv
  refine Prod.ext ?_ ht
  exact Circle.coe_injective (planeOf.injective this)

private theorem isQuotientMap_coneMap : IsQuotientMap coneMap :=
  continuous_coneMap.isClosedMap.isQuotientMap continuous_coneMap coneMap_surjective

/-- A cylinder that is pinched at its top, and is injective elsewhere, is a closed disc. -/
theorem exists_disc_of_cone {h : C(Circle × I, S)} {v : S} (htop : ∀ z, h (z, 1) = v)
    (hinj : InjOn h {p | p.2 < 1}) (hne : ∀ p : Circle × I, p.2 < 1 → h p ≠ v) :
    ∃ Φ : C(ClosedUnitDisc, S), Function.Injective Φ ∧ ∀ p, Φ (coneMap p) = h p := by
  have htop' : ∀ p : Circle × I, ¬ p.2 < 1 → h p = v := fun p hp => by
    have : p.2 = 1 := le_antisymm (unitInterval.le_one _) (not_lt.mp hp)
    rw [show p = (p.1, 1) from Prod.ext rfl this, htop]
  have hft : Function.FactorsThrough h coneMap := by
    intro p q hpq
    by_cases hp : p.2 < 1
    · rw [coneMap_eq hpq hp]
    · by_cases hq : q.2 < 1
      · rw [coneMap_eq hpq.symm hq]
      · rw [htop' p hp, htop' q hq]
  let cm : C(Circle × I, ClosedUnitDisc) := ⟨coneMap, continuous_coneMap⟩
  have hcm : IsQuotientMap cm := isQuotientMap_coneMap
  let Φ : C(ClosedUnitDisc, S) := hcm.lift h hft
  have hΦ : ∀ p, Φ (coneMap p) = h p := fun p =>
    congrArg (fun f : C(Circle × I, S) => f p) (hcm.lift_comp h hft)
  refine ⟨Φ, ?_, hΦ⟩
  intro x y hxy
  obtain ⟨p, rfl⟩ := coneMap_surjective x
  obtain ⟨q, rfl⟩ := coneMap_surjective y
  rw [hΦ, hΦ] at hxy
  by_cases hp : p.2 < 1
  · by_cases hq : q.2 < 1
    · rw [hinj hp hq hxy]
    · exact (hne p hp (hxy.trans (htop' q hq))).elim
  · by_cases hq : q.2 < 1
    · exact (hne q hq (hxy.symm.trans (htop' p hp))).elim
    · have e₁ : p.2 = 1 := le_antisymm (unitInterval.le_one _) (not_lt.mp hp)
      have e₂ : q.2 = 1 := le_antisymm (unitInterval.le_one _) (not_lt.mp hq)
      rw [show p = (p.1, 1) from Prod.ext rfl e₁, show q = (q.1, 1) from Prod.ext rfl e₂,
        coneMap_top, coneMap_top]

/-! ## Fans -/

/-- A *fan* at `v`. The index set `H` is cyclically ordered by `next`. Each `s k` is a line from
`v`, and
`Q k` is a closed disc that has the first part of `s k` and of `s (next k)` in its boundary. Near
`v`, the
points of `Q k` off its boundary lie in `B k`. -/
structure IsFan {H : Type*} (next : H → H) (v : S) (s : H → I → S) (Q B : H → Set S) (W : Set S)
    (τ : H → I) : Prop where
  inj : Function.Injective next
  reach : ∀ a b, Relation.ReflTransGen (fun x y => y = next x) a b
  next_ne : ∀ k, next k ≠ k
  cont : ∀ k, Continuous (s k)
  sInj : ∀ k, Function.Injective (s k)
  zero : ∀ k, s k 0 = v
  meet : ∀ i j, i ≠ j → ∀ t t' : I, t < 1 → t' < 1 → s i t = s j t' → t = 0
  disc : ∀ k, IsClosedDisc (Q k)
  bd : ∀ k, v ∈ discBd (Q k)
  isOpen : IsOpen W
  mem : v ∈ W
  pos : ∀ k, 0 < τ k
  left : ∀ k t, t ≤ τ k → s k t ∈ discBd (Q k)
  right : ∀ k t, t ≤ τ (next k) → s (next k) t ∈ discBd (Q k)
  inside : ∀ k, (W ∩ Q k) \ discBd (Q k) ⊆ B k
  disj : ∀ k j, k ≠ j → Disjoint (B k) (Q j)
  off : ∀ k i (t : I), t < 1 → s i t ∉ B k

private theorem exists_small {f : I → S} (hf : Continuous f) {O : Set S} (hO : IsOpen O)
    (h0 : f 0 ∈ O) {τ : I} (hτ : 0 < τ) : ∃ t : I, 0 < t ∧ t < 1 ∧ t ≤ τ ∧ ∀ u, u ≤ t → f u ∈ O
      := by
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp (hO.preimage hf) 0 h0
  have hτ' : 0 < τ.1 := hτ
  let r : ℝ := min (ε / 2) (min τ.1 (1 / 2))
  have hr : 0 < r := by positivity
  have hr₁ : r ≤ τ.1 := (min_le_right _ _).trans (min_le_left _ _)
  have hr₂ : r ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hr₃ : r ≤ ε / 2 := min_le_left _ _
  refine ⟨⟨r, hr.le, by linarith⟩, hr, ?_, hr₁, fun u hu => ?_⟩
  · change r < 1
    linarith
  · have hu' : u.1 ≤ r := hu
    refine hb ?_
    rw [Metric.mem_ball, Subtype.dist_eq]
    have hu0 := u.2.1
    simp only [Set.Icc.coe_zero, Real.dist_eq, sub_zero]
    rw [abs_of_nonneg hu0]
    linarith

omit [TopologicalSpace S] in
private theorem adjacent_spokes_inter {H : Type*} {next : H → H} {v : S}
    {sp : H → I → S} (hsp1 : ∀ k, sp k 1 = v) (hnext : ∀ k, next k ≠ k)
    (hspeq : ∀ a b r r', r < 1 → r' < 1 → sp a r = sp b r' → a = b ∧ r = r') :
    ∀ k, range (sp k) ∩ range (sp (next k)) = {v} := by
  intro k
  ext x
  constructor
  · rintro ⟨⟨r, rfl⟩, ⟨r', hr'⟩⟩
    by_contra hne
    have hr : r < 1 := unitInterval.lt_one_iff_ne_one.mpr fun h => hne (by rw [h, hsp1]; rfl)
    have hr'' : r' < 1 := unitInterval.lt_one_iff_ne_one.mpr fun h => hne (by
      rw [← hr', h, hsp1]; rfl)
    exact hnext k (hspeq _ _ _ _ hr'' hr hr').1
  · rintro rfl
    exact ⟨⟨1, hsp1 k⟩, ⟨1, hsp1 _⟩⟩

theorem exists_polar_of_fan {H : Type*} [Finite H] [Nonempty H] (hS : IsClosedSurface S)
    {next : H → H} {v : S} {s : H → I → S} {Q B : H → Set S} {W : Set S} {τ : H → I}
    (hf : IsFan next v s Q B W τ) :
    ∃ Φ : C(ClosedUnitDisc, S), Function.Injective Φ ∧ Φ polarCentre = v ∧ range Φ ⊆ W ∧
      ∀ x, x ≠ polarCentre → ∀ c : I, 0 < c →
        (∃ k, Φ x ∈ B k ∧ Φ (discScale c x) ∈ B k) ∨
        ∃ k, ∃ t t' : I, 0 < t ∧ t < 1 ∧ 0 < t' ∧ t' < 1 ∧ Φ x = s k t ∧ Φ (discScale c x) = s k t'
          := by
  classical
  have hT2 : T2Space S := hS.2.1
  have hcapk := fun k => exists_cap hS (hf.disc k) (hf.bd k) hf.isOpen hf.mem
  choose W' hW'o hvW' hW'c using hcapk
  have hW₀o : IsOpen (⋂ k, W' k) := isOpen_iInter_of_finite hW'o
  have hvW₀ : v ∈ ⋂ k, W' k := mem_iInter.mpr hvW'
  have hsmall : ∀ k, ∃ t : I, 0 < t ∧ t < 1 ∧ t ≤ τ k ∧ ∀ u, u ≤ t → s k u ∈ ⋂ k, W' k := fun k =>
    exists_small (hf.cont k) hW₀o (by rw [hf.zero]; exact hvW₀) (hf.pos k)
  choose t ht0 ht1 htτ htW using hsmall
  -- The spokes, from the rim to `v`.
  let par : H → I → I := fun k r => t k * σ r
  have hparc : ∀ k, Continuous (par k) := fun k => by fun_prop
  have hparinj : ∀ k, Function.Injective (par k) := fun k a b h => by
    have h' : (t k).1 * (1 - a.1) = (t k).1 * (1 - b.1) := congrArg Subtype.val h
    have := mul_left_cancel₀ (ne_of_gt (show 0 < (t k).1 from ht0 k)) h'
    exact Subtype.ext (by linarith)
  have hparle : ∀ k r, par k r ≤ t k := fun k r => unitInterval.mul_le_left
  have hparlt : ∀ k r, par k r < 1 := fun k r => (hparle k r).trans_lt (ht1 k)
  have hparpos : ∀ k r, r < 1 → 0 < par k r := fun k r hr => by
    have h₁ : 0 < 1 - r.1 := sub_pos.mpr hr
    exact mul_pos (ht0 k) h₁
  let sp : H → I → S := fun k r => s k (par k r)
  have hspc : ∀ k, Continuous (sp k) := fun k => (hf.cont k).comp (hparc k)
  have hspi : ∀ k, Function.Injective (sp k) := fun k => (hf.sInj k).comp (hparinj k)
  have hsp1 : ∀ k, sp k 1 = v := fun k => by
    simp only [sp, par, unitInterval.symm_one, mul_zero]
    exact hf.zero k
  have hspne : ∀ k r, r < 1 → sp k r ≠ v := fun k r hr h =>
    hr.ne (hspi k (h.trans (hsp1 k).symm))
  have hspeq : ∀ a b r r', r < 1 → r' < 1 → sp a r = sp b r' → a = b ∧ r = r' := by
    intro a b r r' hr hr' h
    by_cases hab : a = b
    · subst hab
      exact ⟨rfl, hspi a h⟩
    · exact ((hparpos a r hr).ne' (hf.meet a b hab _ _ (hparlt a r) (hparlt b r') h)).elim
  have hrange : ∀ k, IsLineWithEnds (range (sp k)) v (sp k 0) := fun k => by
    have := IsArcMap.isLineWithEnds (⟨hspc k, hspi k⟩ : IsArcMap (sp k))
    have h' := IsLineWithEnds.symm this
    rwa [hsp1] at h'
  have hrcap := adjacent_spokes_inter hsp1 hf.next_ne hspeq
  have hTline : ∀ k, IsLineWithEnds (range (sp k) ∪ range (sp (next k))) (sp k 0) (sp (next k) 0) :=
    fun k => IsLineWithEnds.union (hrange k) (hrange (next k)) (hrcap k)
  have hTbd : ∀ k, range (sp k) ∪ range (sp (next k)) ⊆ discBd (Q k) := by
    rintro k x (⟨r, rfl⟩ | ⟨r, rfl⟩)
    · exact hf.left k _ ((hparle k r).trans (htτ k))
    · exact hf.right k _ ((hparle _ r).trans (htτ _))
  have hTW : ∀ k, range (sp k) ∪ range (sp (next k)) ⊆ W' k := by
    rintro k x (⟨r, rfl⟩ | ⟨r, rfl⟩)
    · exact mem_iInter.mp (htW k _ (hparle k r)) k
    · exact mem_iInter.mp (htW _ _ (hparle _ r)) k
  have hend₁ : ∀ k, sp k 0 ≠ sp (next k) 0 := fun k h =>
    hf.next_ne k (hspeq _ _ _ _ zero_lt_one zero_lt_one h).1.symm
  have hvT : ∀ k, v ∈ range (sp k) ∪ range (sp (next k)) := fun k => Or.inl ⟨1, hsp1 k⟩
  have hcap := fun k => hW'c k (sp k 0) (sp (next k) 0) _ (hend₁ k) (hTline k) (hTbd k) (hTW k)
    (hvT k)
    (hspne k 0 zero_lt_one).symm (hspne _ 0 zero_lt_one).symm
  choose C Q₁ hCl hCW hCQ hCdis hQ₁ hQ₁W hQ₁Q hQ₁bd hQ₁cap using hcap
  have hCarc := fun k => IsLineWithEnds.exists_arc (hCl k)
  choose e he her he0 he1 using hCarc
  -- A point of the cap is not on a spoke, except at the ends of the cap.
  have hcapoff : ∀ k x, x ∈ C k → x ∈ discBd (Q k) → x = sp k 0 ∨ x = sp (next k) 0 := by
    intro k x hx hb
    by_contra hne
    push Not at hne
    exact disjoint_left.mp (hCdis k) ⟨hx, fun h => (h.elim hne.1 hne.2)⟩ hb
  have hsquare : ∀ k, ∃ G : I × I → S, Continuous G ∧ (∀ u, G (u, 0) = e k u) ∧ (∀ r, G (0, r)
    = sp k r) ∧
      (∀ r, G (1, r) = sp (next k) r) ∧ (∀ u, G (u, 1) = sp k 1) ∧ InjOn G {p | p.2 < 1} ∧
      range G = Q₁ k ∧
      (∀ p : I × I, 0 < p.1 → p.1 < 1 → 0 < p.2 → p.2 < 1 → G p ∉ discBd (Q₁ k)) := by
    intro k
    have hneq : ∀ {a b : I}, sp k a = sp (next k) b → a = 1 ∧ b = 1 := by
      intro a b h
      have hm : sp k a ∈ range (sp k) ∩ range (sp (next k)) := ⟨⟨a, rfl⟩, ⟨b, h.symm⟩⟩
      rw [hrcap k] at hm
      exact ⟨hspi k (hm.trans (hsp1 k).symm), hspi _ ((h.symm.trans hm).trans (hsp1 _).symm)⟩
    have hmemC : ∀ a, e k a ∈ C k := fun a => her k ▸ mem_range_self a
    refine exists_square_chart (hQ₁ k) hS.2.2 (he k).1 (hspc k) (hspc (next k)) (he k).2 (hspi k)
      (hspi (next k)) (he0 k) (he1 k) ((hsp1 k).trans (hsp1 _).symm) ?_ ?_ ?_ ?_
    · intro a b h
      have hb : e k a ∈ discBd (Q k) := hTbd k (Or.inl ⟨b, h.symm⟩)
      rcases hcapoff k _ (hmemC a) hb with h₁ | h₁
      · exact ⟨(he k).2 (h₁.trans (he0 k).symm), hspi k ((h.symm.trans h₁))⟩
      · have := hneq (a := b) (b := 0) (h.symm.trans h₁)
        exact absurd this.2 zero_ne_one
    · intro a b h
      have hb : e k a ∈ discBd (Q k) := hTbd k (Or.inr ⟨b, h.symm⟩)
      rcases hcapoff k _ (hmemC a) hb with h₁ | h₁
      · have := hneq (a := 0) (b := b) (h₁.symm.trans h)
        exact absurd this.1 zero_ne_one
      · exact ⟨(he k).2 (h₁.trans (he1 k).symm), hspi _ ((h.symm.trans h₁))⟩
    · intro a b h
      exact hneq h
    · rw [hQ₁bd k, her k]
      ext x
      simp only [mem_union]
      tauto
  choose G hGc hGb hGl hGr hGt hGi hGR hGint using hsquare
  -- Where the points of a sector lie.
  have hclass : ∀ k (p : I × I), p.2 < 1 → p.1 < 1 → (0 < p.1 ∧ G k p ∈ B k) ∨ (p.1 = 0 ∧ G k p
    = sp k p.2) := by
    rintro k ⟨u, r⟩ hr hu
    simp only at hr hu ⊢
    by_cases hu0 : u = 0
    · subst hu0
      exact Or.inr ⟨rfl, hGl k r⟩
    have hupos : 0 < u := unitInterval.pos_iff_ne_zero.mpr hu0
    refine Or.inl ⟨hupos, ?_⟩
    have hmem : G k (u, r) ∈ Q₁ k := hGR k ▸ mem_range_self _
    refine hf.inside k ⟨⟨hQ₁W k hmem, hQ₁Q k hmem⟩, fun hb => ?_⟩
    by_cases hr0 : r = 0
    · subst hr0
      rw [hGb] at hb
      have hmemC : e k u ∈ C k := her k ▸ mem_range_self u
      rcases hcapoff k _ hmemC hb with h₁ | h₁
      · exact hu0 ((he k).2 (h₁.trans (he0 k).symm))
      · exact hu.ne ((he k).2 (h₁.trans (he1 k).symm))
    · have hrpos : 0 < r := unitInterval.pos_iff_ne_zero.mpr hr0
      have hT := hQ₁cap k ⟨hmem, hb⟩
      exact hGint k (u, r) hupos hu hrpos hr ((hQ₁bd k).symm ▸ Or.inl hT)
  -- The cyclic order.
  obtain ⟨k₀⟩ := ‹Nonempty H›
  let n := Function.minimalPeriod next k₀
  have hn : 0 < n := Function.minimalPeriod_pos_of_mem_periodicPts (hf.inj.mem_periodicPts k₀)
  let κ : ℕ → H := fun i => next^[i] k₀
  have hκs : ∀ i, κ (i + 1) = next (κ i) := fun i => Function.iterate_succ_apply' next i k₀
  have hκn : ∀ i, κ (i + n) = κ i := fun i => by
    change next^[i + n] k₀ = next^[i] k₀
    rw [Function.iterate_add_apply, Function.iterate_minimalPeriod]
  have hκinj : ∀ i j, i < n → j < n → κ i = κ j → i = j := fun i j hi hj h =>
    Function.iterate_injOn_Iio_minimalPeriod hi hj h
  obtain ⟨h, hh⟩ := exists_cylinder hn (G := fun i => G (κ i)) (fun i => hGc _)
    (fun i r => by
      rw [hGr, hGl, hκs])
    (fun r => by
      have := hκn 0
      rw [zero_add] at this
      rw [this])
  have hpar : ∀ z : Circle, ∃ i, i < n ∧ ∃ u : I, u < 1 ∧
      z = Circle.exp (2 * Real.pi * ((i + u.1) / n)) ∧ ∀ r, h (z, r) = G (κ i) (u, r) := by
    intro z
    obtain ⟨i, hi, u, hu, rfl⟩ := exists_circle_param hn z
    exact ⟨i, hi, u, hu, rfl, fun r => hh i hi u r⟩
  have htop : ∀ z, h (z, 1) = v := fun z => by
    obtain ⟨i, -, u, -, -, hz⟩ := hpar z
    rw [hz, hGt, hsp1]
  have hne : ∀ p : Circle × I, p.2 < 1 → h p ≠ v := by
    rintro ⟨z, r⟩ hr
    obtain ⟨i, -, u, hu, -, hz⟩ := hpar z
    rw [hz]
    rcases hclass (κ i) (u, r) hr hu with ⟨-, hb⟩ | ⟨-, hb⟩
    · intro h'
      rw [h'] at hb
      exact hf.off _ (κ i) 0 zero_lt_one (by rw [hf.zero]; exact hb)
    · rw [hb]
      exact hspne _ _ hr
  have hinjh : InjOn h {p | p.2 < 1} := by
    rintro ⟨z, r⟩ hr ⟨z', r'⟩ hr' heq
    simp only [mem_ofPred_eq] at hr hr'
    obtain ⟨i, hi, u, hu, ez, hz⟩ := hpar z
    obtain ⟨i', hi', u', hu', ez', hz'⟩ := hpar z'
    have hsame : i = i' ∧ u = u' ∧ r = r' := by
      rw [hz, hz'] at heq
      have hmem' : G (κ i') (u', r') ∈ Q₁ (κ i') := hGR _ ▸ mem_range_self _
      have hmem : G (κ i) (u, r) ∈ Q₁ (κ i) := hGR _ ▸ mem_range_self _
      rcases hclass (κ i) (u, r) hr hu with ⟨h₀, hb⟩ | ⟨h₀, hb⟩ <;>
        rcases hclass (κ i') (u', r') hr' hu' with ⟨h₀', hb'⟩ | ⟨h₀', hb'⟩
      · have hk : κ i = κ i' := by
          by_contra hk
          exact disjoint_left.mp (hf.disj _ _ hk) hb (hQ₁Q _ (heq ▸ hmem'))
        obtain rfl := hκinj i i' hi hi' hk
        have := hGi (κ i) (show (u, r).2 < 1 from hr) (show (u', r').2 < 1 from hr') heq
        exact ⟨rfl, congrArg Prod.fst this, congrArg Prod.snd this⟩
      · rw [heq, hb'] at hb
        exact (hf.off _ _ _ (hparlt _ _) hb).elim
      · rw [← heq, hb] at hb'
        exact (hf.off _ _ _ (hparlt _ _) hb').elim
      · rw [hb, hb'] at heq
        obtain ⟨e₁, e₂⟩ := hspeq _ _ _ _ hr hr' heq
        exact ⟨hκinj i i' hi hi' e₁, h₀.trans h₀'.symm, e₂⟩
    obtain ⟨rfl, rfl, rfl⟩ := hsame
    rw [ez, ez']
  obtain ⟨Φ, hΦinj, hΦ⟩ := exists_disc_of_cone htop hinjh hne
  refine ⟨Φ, hΦinj, ?_, ?_, ?_⟩
  · rw [← coneMap_top 1, hΦ, htop]
  · rintro _ ⟨x, rfl⟩
    obtain ⟨⟨z, r⟩, rfl⟩ := coneMap_surjective x
    obtain ⟨i, -, u, -, -, hz⟩ := hpar z
    rw [hΦ, hz]
    exact hQ₁W _ (hGR _ ▸ mem_range_self _)
  · intro x hx c hc
    obtain ⟨⟨z, r⟩, rfl⟩ := coneMap_surjective x
    have hr : r < 1 := unitInterval.lt_one_iff_ne_one.mpr fun h' => hx (by rw [h', coneMap_top])
    obtain ⟨r', hr', he'⟩ := discScale_coneMap c hc (z, r) hr
    obtain ⟨i, -, u, hu, -, hz⟩ := hpar z
    simp only at he'
    rw [he', hΦ, hΦ, hz, hz]
    rcases hclass (κ i) (u, r) hr hu with ⟨h₀, hb⟩ | ⟨h₀, hb⟩ <;>
      rcases hclass (κ i) (u, r') hr' hu with ⟨h₀', hb'⟩ | ⟨h₀', hb'⟩
    · exact Or.inl ⟨_, hb, hb'⟩
    · exact absurd h₀' h₀.ne'
    · exact absurd h₀ h₀'.ne'
    · refine Or.inr ⟨κ i, _, _, hparpos _ _ hr, hparlt _ _, hparpos _ _ hr', hparlt _ _, hb, hb'⟩

end GraphMinor.GM11
