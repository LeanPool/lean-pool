/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.Defs
import LeanPool.GraphMinor.GM06.RegionLocal
import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.Surface.Crossing
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Complementary Curves in Regions of a Proper Drawing on a Disc

This file proves `exists_region_curve`: for any proper drawing `G` on a closed disc space `S`,
any region `r ∈ G.R`, and any two points `p, q ∈ closure r`, there is a continuous curve
`γ : C(unitInterval, S)` with `γ 0 = p`, `γ 1 = q`, and `γ t ∈ r` for all `t ∈ Ioo 0 1`.
-/

public section

namespace GraphMinor.GM06

open Set Function Topology Metric GraphMinor.Surface unitInterval

universe u

/-! ## 1. Pulling Back Plane Entry Curves to the Closed Disc Space -/

private theorem subset_openUnitDisc_of_isPreconnected
    {P : Set EuclideanPlane} (hP : IsPreconnected P)
    (hdisj : Disjoint P UnitCircle) (hinter : (P ∩ OpenUnitDisc).Nonempty) :
    P ⊆ OpenUnitDisc := by
  refine hP.subset_left_of_subset_union Metric.isOpen_ball
    (show IsOpen ClosedUnitDiscᶜ from Metric.isClosed_closedBall.isOpen_compl) ?_ ?_ hinter
  · exact disjoint_left.mpr fun z hz h => h (Metric.ball_subset_closedBall hz)
  · intro z hz
    by_cases hzb : z ∈ OpenUnitDisc
    · exact Or.inl hzb
    · refine Or.inr fun hzc => ?_
      have hle : ‖z‖ ≤ 1 := by simpa [ClosedUnitDisc] using hzc
      have hge : 1 ≤ ‖z‖ := not_lt.mp (by simpa [OpenUnitDisc] using hzb)
      have heq : ‖z‖ = 1 := le_antisymm hle hge
      exact disjoint_left.mp hdisj hz (by simpa [UnitCircle] using heq)

private theorem entry_path_of_plane {S : Type u} [TopologicalSpace S]
    (e : ClosedUnitDisc ≃ₜ S) (G : Drawing S) {r : Set S} (hr : r ∈ G.R) {p : S}
    {P : Set EuclideanPlane} {α : C(I, EuclideanPlane)}
    (hP_conn : IsPreconnected P)
    (hP_disj : Disjoint P (UnitCircle ∪ (fun x => (e.symm x).1) '' G.U))
    (hP_inter : (P ∩ (fun x => (e.symm x).1) '' (r \ bd S)).Nonempty)
    (hα0 : α 0 = (e.symm p).1)
    (hαP : ∀ t : I, 0 < (t : ℝ) → α t ∈ P) :
    ∃ α_S : C(I, S), α_S 0 = p ∧ ∀ t : I, 0 < (t : ℝ) → α_S t ∈ r \ bd S := by
  have hbd_img := image_bd_homeomorph e
  rw [bd_closedUnitDisc] at hbd_img
  have hR_sub_open : (fun x => (e.symm x).1) '' (r \ bd S) ⊆ OpenUnitDisc := by
    rintro _ ⟨x, ⟨_, hxbd⟩, rfl⟩
    have hle : ‖(e.symm x).1‖ ≤ 1 := mem_closedBall_zero_iff.mp (e.symm x).2
    have hne : ‖(e.symm x).1‖ ≠ 1 := by
      intro h1
      apply hxbd
      rw [← hbd_img]
      exact ⟨e.symm x, by simpa [UnitCircle] using h1, e.apply_symm_apply x⟩
    simpa [OpenUnitDisc] using lt_of_le_of_ne hle hne
  have hP_open : P ⊆ OpenUnitDisc :=
    subset_openUnitDisc_of_isPreconnected hP_conn
      (hP_disj.mono_right subset_union_left)
      (hP_inter.mono (inter_subset_inter_right P hR_sub_open))
  have hP_disc : P ⊆ ClosedUnitDisc := fun z hz => Metric.ball_subset_closedBall (hP_open hz)
  have hα_disc : ∀ t : I, α t ∈ ClosedUnitDisc := by
    intro t
    rcases eq_or_lt_of_le (t.2.1 : (0 : ℝ) ≤ t) with ht0 | ht
    · have ht_eq : t = 0 := Subtype.ext ht0.symm
      rw [ht_eq, hα0]
      exact (e.symm p).2
    · exact hP_disc (hαP t ht)
  let g : I → ClosedUnitDisc := fun t => ⟨α t, hα_disc t⟩
  have hg_cont : Continuous g := Continuous.subtype_mk α.continuous _
  let A : Set S := e '' (Subtype.val ⁻¹' P)
  have hP'_conn : IsPreconnected (Subtype.val ⁻¹' P : Set ClosedUnitDisc) := by
    refine (IsInducing.subtypeVal :
      IsInducing (Subtype.val : ClosedUnitDisc → EuclideanPlane)).isPreconnected_image.mp ?_
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hP_disc]
    exact hP_conn
  have hA_conn : IsPreconnected A := hP'_conn.image e e.continuous.continuousOn
  have hA_disj : Disjoint A G.U := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨x, hxP, rfl⟩ hxU
    exact disjoint_left.mp hP_disj hxP (Or.inr ⟨e x, hxU, by simp⟩)
  have hA_inter : (A ∩ r).Nonempty := by
    rcases hP_inter with ⟨_, hzP, x, ⟨hxr, _⟩, rfl⟩
    exact ⟨x, ⟨e.symm x, hzP, e.apply_symm_apply x⟩, hxr⟩
  have hA_sub : A ⊆ r := region_subset_of_isPreconnected G hr hA_conn hA_disj hA_inter
  refine ⟨⟨e ∘ g, e.continuous.comp hg_cont⟩, ?_, ?_⟩
  · change e (g 0) = p
    have hg0 : g 0 = e.symm p := Subtype.ext hα0
    rw [hg0, e.apply_symm_apply]
  · intro t ht
    refine ⟨hA_sub ⟨g t, hαP t ht, rfl⟩, fun hb => ?_⟩
    rw [← hbd_img] at hb
    obtain ⟨y, hy, hye⟩ := hb
    have hyg : y = g t := e.injective hye
    have hcirc : α t ∈ UnitCircle := by
      have : (y : EuclideanPlane) ∈ UnitCircle := by simpa [UnitCircle] using hy
      rw [hyg] at this
      exact this
    exact disjoint_left.mp hP_disj (hαP t ht) (Or.inl hcirc)

/-! ## 2. Semicircle Spokes of `UnitCircle` at a Boundary Vertex -/

private noncomputable def bdAngle (b : Bool) (t : I) : ℝ :=
  if b then -(Real.pi * (t : ℝ)) else Real.pi * (t : ℝ)

private noncomputable def bdSpoke (c : EuclideanPlane) (b : Bool) (t : I) : EuclideanPlane :=
  complexPlane (complexPlane.symm c * (Circle.exp (bdAngle b t) : ℂ))

private theorem continuous_bdSpoke (c : EuclideanPlane) (b : Bool) :
    Continuous (bdSpoke c b) := by
  unfold bdSpoke bdAngle
  refine complexPlane.continuous.comp
    (continuous_const.mul (continuous_subtype_val.comp (Circle.exp.continuous.comp ?_)))
  cases b <;> dsimp <;> fun_prop

private theorem bdSpoke_zero (c : EuclideanPlane) (b : Bool) :
    bdSpoke c b 0 = c := by
  simp [bdSpoke, bdAngle]

private theorem bdSpoke_mem_unitCircle {c : EuclideanPlane} (hc : c ∈ UnitCircle)
    (b : Bool) (t : I) : bdSpoke c b t ∈ UnitCircle := by
  have hc_norm : ‖complexPlane.symm c‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map]
    simpa [UnitCircle] using hc
  simp only [bdSpoke, UnitCircle, Metric.mem_sphere, dist_zero_right,
    LinearIsometryEquiv.norm_map, norm_mul, hc_norm, one_mul, Circle.norm_coe]

private theorem bdSpoke_injective {c : EuclideanPlane} (hc : c ∈ UnitCircle) (b : Bool) :
    Function.Injective (bdSpoke c b) := by
  have hc_ne : complexPlane.symm c ≠ 0 := by
    intro h0
    have hnorm : ‖complexPlane.symm c‖ = 1 := by
      rw [LinearIsometryEquiv.norm_map]; simpa [UnitCircle] using hc
    rw [h0, norm_zero] at hnorm
    exact zero_ne_one hnorm
  intro s t h
  have h1 := complexPlane.injective h
  have h2 := mul_left_cancel₀ hc_ne h1
  have h3 : Circle.exp (bdAngle b s) = Circle.exp (bdAngle b t) := Subtype.ext h2
  rw [Circle.exp_eq_exp] at h3
  rcases h3 with ⟨m, hm⟩
  have hpi := Real.pi_pos
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hm0 : m = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm_le : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
      cases b <;> dsimp [bdAngle] at hm <;> nlinarith
    · have hm_ge : (1 : ℝ) ≤ m := by exact_mod_cast Int.add_one_le_of_lt hgt
      cases b <;> dsimp [bdAngle] at hm <;> nlinarith
  subst hm0
  simp only [Int.cast_zero, zero_mul, add_zero] at hm
  have h_eq : (s : ℝ) = (t : ℝ) := by
    cases b <;> dsimp [bdAngle] at hm <;> nlinarith
  exact Subtype.ext h_eq

private theorem bdSpoke_eq_of_ne {c : EuclideanPlane} (hc : c ∈ UnitCircle)
    {b₁ b₂ : Bool} (hb : b₁ ≠ b₂) {s t : I} (hs : 0 < s) (ht : 0 < t)
    (heq : bdSpoke c b₁ s = bdSpoke c b₂ t) : s = 1 ∧ t = 1 := by
  have hc_ne : complexPlane.symm c ≠ 0 := by
    intro h0
    have hnorm : ‖complexPlane.symm c‖ = 1 := by
      rw [LinearIsometryEquiv.norm_map]; simpa [UnitCircle] using hc
    rw [h0, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have h1 := mul_left_cancel₀ hc_ne (complexPlane.injective heq)
  have h2 : Circle.exp (bdAngle b₁ s) = Circle.exp (bdAngle b₂ t) := Subtype.ext h1
  rw [Circle.exp_eq_exp] at h2
  rcases h2 with ⟨m, hm⟩
  have hpi := Real.pi_pos
  have hs0 : 0 < (s : ℝ) := hs
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  have ht0 : 0 < (t : ℝ) := ht
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  cases b₁ <;> cases b₂
  · exact absurd rfl hb
  · dsimp [bdAngle] at hm
    have hm1 : m = 1 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hm_le : (m : ℝ) ≤ 0 := by exact_mod_cast Int.le_sub_one_of_lt hlt
        nlinarith
      · have hm_ge : (2 : ℝ) ≤ m := by exact_mod_cast Int.add_one_le_of_lt hgt
        nlinarith
    subst hm1
    simp only [Int.cast_one, one_mul] at hm
    exact ⟨Subtype.ext (show (s : ℝ) = 1 by nlinarith), Subtype.ext (show (t : ℝ) = 1 by nlinarith)⟩
  · dsimp [bdAngle] at hm
    have hm1 : m = -1 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hm_le : (m : ℝ) ≤ -2 := by exact_mod_cast Int.le_sub_one_of_lt hlt
        nlinarith
      · have hm_ge : (0 : ℝ) ≤ m := by exact_mod_cast Int.add_one_le_of_lt hgt
        nlinarith
    subst hm1
    simp only [Int.cast_neg, Int.cast_one] at hm
    exact ⟨Subtype.ext (show (s : ℝ) = 1 by nlinarith), Subtype.ext (show (t : ℝ) = 1 by nlinarith)⟩
  · exact absurd rfl hb

private theorem unitCircle_subset_range_bdSpoke {c : EuclideanPlane} (hc : c ∈ UnitCircle) :
    UnitCircle ⊆ range (bdSpoke c false) ∪ range (bdSpoke c true) := by
  intro w hw
  have hc_norm : ‖complexPlane.symm c‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map]; simpa [UnitCircle] using hc
  have hw_norm : ‖complexPlane.symm w‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map]; simpa [UnitCircle] using hw
  let zc : Circle := ⟨complexPlane.symm c, mem_sphere_zero_iff_norm.mpr hc_norm⟩
  let zw : Circle := ⟨complexPlane.symm w, mem_sphere_zero_iff_norm.mpr hw_norm⟩
  let q : Circle := zc⁻¹ * zw
  have hq : complexPlane.symm c * (q : ℂ) = complexPlane.symm w :=
    congrArg Subtype.val (mul_inv_cancel_left zc zw)
  have hexp : Circle.exp (Complex.arg (q : ℂ)) = q := Circle.exp_arg q
  have h_le_pi : Complex.arg (q : ℂ) ≤ Real.pi := Complex.arg_le_pi (q : ℂ)
  have h_gt_neg_pi : -Real.pi < Complex.arg (q : ℂ) := Complex.neg_pi_lt_arg (q : ℂ)
  have hpi := Real.pi_pos
  rcases le_or_gt 0 (Complex.arg (q : ℂ)) with hnonneg | hneg
  · left
    let t : I := ⟨Complex.arg (q : ℂ) / Real.pi,
      div_nonneg hnonneg hpi.le, (div_le_one hpi).mpr h_le_pi⟩
    refine ⟨t, ?_⟩
    unfold bdSpoke
    have hmul : bdAngle false t = Complex.arg (q : ℂ) := by
      dsimp [bdAngle, t]; field_simp
    rw [hmul, hexp, hq, LinearIsometryEquiv.apply_symm_apply]
  · right
    let t : I := ⟨(-Complex.arg (q : ℂ)) / Real.pi,
      div_nonneg (by linarith) hpi.le, (div_le_one hpi).mpr (by linarith)⟩
    refine ⟨t, ?_⟩
    unfold bdSpoke
    have hmul : bdAngle true t = Complex.arg (q : ℂ) := by
      dsimp [bdAngle, t]; field_simp
    rw [hmul, hexp, hq, LinearIsometryEquiv.apply_symm_apply]

/-! ## 3. Decomposing `G.U` into Half-Edge Spokes Around a Vertex -/

private theorem endOf_eq (b : Bool) : GM11.endOf b = if b then 1 else 0 := by
  ext
  rw [← GM11.halfPar_zero, GM11.halfPar_coe]
  cases b <;> simp

private def localHalfEdges {S : Type u} [TopologicalSpace S]
    (G : Drawing S) (γ : Set S → I → S) (p : S) : Set (Set S × Bool) :=
  {x | x.1 ∈ G.E ∧ γ x.1 (GM11.endOf x.2) = p}

private theorem finite_localHalfEdges {S : Type u} [TopologicalSpace S]
    (G : Drawing S) (γ : Set S → I → S) (p : S) :
    (localHalfEdges G γ p).Finite :=
  (G.finite_edges.prod (finite_univ (α := Bool))).subset fun _ hx => ⟨hx.1, mem_univ _⟩

private noncomputable def localSpoke {S : Type u} (γ : Set S → I → S)
    (x : Set S × Bool) (t : I) : S :=
  γ x.1 (GM11.halfPar x.2 t)

private theorem localSpoke_zero {S : Type u} (γ : Set S → I → S) (x : Set S × Bool) :
    localSpoke γ x 0 = γ x.1 (GM11.endOf x.2) := by
  simp [localSpoke]

private theorem continuous_localSpoke {S : Type u} [TopologicalSpace S]
    {G : Drawing S} {γ : Set S → I → S} (hγ : GM11.EdgePar G γ)
    {x : Set S × Bool} (hx : x.1 ∈ G.E) :
    Continuous (localSpoke γ x) :=
  (hγ.cont _ hx).comp (GM11.continuous_halfPar x.2)

private theorem localSpoke_mem_edge {S : Type u} [TopologicalSpace S]
    {G : Drawing S} {γ : Set S → I → S} (hγ : GM11.EdgePar G γ)
    {x : Set S × Bool} (hx : x.1 ∈ G.E) {t : I} (ht : 0 < t) :
    localSpoke γ x t ∈ x.1 := by
  have := mem_image_of_mem (γ x.1) (GM11.halfPar_mem_Ioo x.2 ht)
  rwa [hγ.image _ hx] at this

private theorem localSpoke_injective {S : Type u} [TopologicalSpace S]
    {G : Drawing S} {γ : Set S → I → S} (hγ : GM11.EdgePar G γ)
    {x : Set S × Bool} (hx : x.1 ∈ G.E) :
    Function.Injective (localSpoke γ x) := by
  intro s t h
  by_cases hs : 0 < s
  · by_cases ht : 0 < t
    · exact GM11.halfPar_injective _
        (hγ.inj _ hx (GM11.halfPar_mem_Ioo _ hs) (GM11.halfPar_mem_Ioo _ ht) h)
    · have ht0 : t = 0 := le_antisymm (not_lt.mp ht) bot_le
      subst ht0
      rw [localSpoke_zero] at h
      have hmem := localSpoke_mem_edge hγ hx hs
      rw [h] at hmem
      have hV : γ x.1 (GM11.endOf x.2) ∈ G.V := by
        rw [endOf_eq]
        cases x.2
        · exact hγ.zero _ hx
        · exact hγ.one _ hx
      exact absurd hV (GM11.edge_notMem_V hx hmem)
  · have hs0 : s = 0 := le_antisymm (not_lt.mp hs) bot_le
    subst hs0
    by_cases ht : 0 < t
    · rw [localSpoke_zero] at h
      have hmem := localSpoke_mem_edge hγ hx ht
      rw [← h] at hmem
      have hV : γ x.1 (GM11.endOf x.2) ∈ G.V := by
        rw [endOf_eq]
        cases x.2
        · exact hγ.zero _ hx
        · exact hγ.one _ hx
      exact absurd hV (GM11.edge_notMem_V hx hmem)
    · exact (le_antisymm (not_lt.mp ht) bot_le).symm

private theorem localSpoke_eq_of_ne {S : Type u} [TopologicalSpace S]
    {G : Drawing S} {γ : Set S → I → S} (hγ : GM11.EdgePar G γ)
    {x y : Set S × Bool} (hx : x.1 ∈ G.E) (hy : y.1 ∈ G.E)
    (hxy : x ≠ y) {s t : I} (hs : 0 < s) (ht : 0 < t)
    (h : localSpoke γ x s = localSpoke γ y t) :
    s = 1 ∧ t = 1 := by
  obtain ⟨e, b⟩ := x
  obtain ⟨e', b'⟩ := y
  have h1 := localSpoke_mem_edge hγ hx hs
  have h2 := localSpoke_mem_edge hγ hy ht
  rw [h] at h1
  have he : e = e' := G.edge_eq_of_mem hx hy h1 h2
  subst he
  have hb : b ≠ b' := fun hb => hxy (by rw [hb])
  exact GM11.halfPar_eq_of_ne hb
    (hγ.inj _ hx (GM11.halfPar_mem_Ioo b hs) (GM11.halfPar_mem_Ioo b' ht) h)

private theorem closure_edge_subset_spoke_union {S : Type u} [TopologicalSpace S] [T2Space S]
    {G : Drawing S} {γ : Set S → I → S} (hγ : GM11.EdgePar G γ)
    {e : Set S} (he : e ∈ G.E) :
    closure e ⊆ range (localSpoke γ (e, false)) ∪ range (localSpoke γ (e, true)) := by
  have hcl : closure e ⊆ range (γ e) := by
    refine closure_minimal ?_ (isCompact_range (hγ.cont e he)).isClosed
    intro x hx
    rw [← hγ.image e he] at hx
    rcases hx with ⟨t, _, rfl⟩
    exact ⟨t, rfl⟩
  rintro x hx
  obtain ⟨t, rfl⟩ := hcl hx
  rcases le_or_gt (t : ℝ) (1 / 2) with ht | ht
  · left
    let s : I := ⟨2 * (t : ℝ), by linarith [t.2.1], by linarith⟩
    refine ⟨s, ?_⟩
    unfold localSpoke
    congr 1
    ext
    rw [GM11.halfPar_coe]
    simp only [Bool.false_eq_true, ite_false, s]
    ring
  · right
    let s : I := ⟨2 * (1 - (t : ℝ)), by linarith [t.2.2], by linarith⟩
    refine ⟨s, ?_⟩
    unfold localSpoke
    congr 1
    ext
    rw [GM11.halfPar_coe]
    simp only [ite_true, s]
    ring

private noncomputable def vertexBad {S : Type u} [TopologicalSpace S]
    (G : Drawing S) (γ : Set S → I → S) (p : S) : Set S :=
  (G.V \ {p}) ∪ ⋃ x ∈ {x : Set S × Bool | x.1 ∈ G.E ∧ x ∉ localHalfEdges G γ p},
    range (localSpoke γ x)

private theorem isClosed_vertexBad {S : Type u} [TopologicalSpace S] [T2Space S]
    (G : Drawing S) {γ : Set S → I → S} (hγ : GM11.EdgePar G γ) (p : S) :
    IsClosed (vertexBad G γ p) := by
  have hfin : {x : Set S × Bool | x.1 ∈ G.E ∧ x ∉ localHalfEdges G γ p}.Finite :=
    (G.finite_edges.prod (finite_univ (α := Bool))).subset fun _ hx => ⟨hx.1, mem_univ _⟩
  refine (G.finite_V.subset sdiff_subset).isClosed.union ?_
  exact hfin.isClosed_biUnion fun x hx =>
    (isCompact_range (continuous_localSpoke hγ hx.1)).isClosed

private theorem notMem_vertexBad {S : Type u} [TopologicalSpace S]
    (G : Drawing S) {γ : Set S → I → S} (hγ : GM11.EdgePar G γ) {p : S} (hp : p ∈ G.V) :
    p ∉ vertexBad G γ p := by
  rintro (⟨_, hp_ne⟩ | h)
  · exact hp_ne rfl
  · obtain ⟨x, ⟨hxE, hxH⟩, s, hsp⟩ := mem_iUnion₂.mp h
    by_cases hs0 : 0 < s
    · have hmem := localSpoke_mem_edge hγ hxE hs0
      rw [hsp] at hmem
      exact GM11.edge_notMem_V hxE hmem hp
    · have hs_eq : s = 0 := le_antisymm (not_lt.mp hs0) bot_le
      rw [hs_eq, localSpoke_zero] at hsp
      exact hxH ⟨hxE, hsp⟩

private theorem U_sdiff_subset_vertexBad_union_spokes {S : Type u} [TopologicalSpace S] [T2Space S]
    (G : Drawing S) {γ : Set S → I → S} (hγ : GM11.EdgePar G γ) (p : S) :
    G.U \ {p} ⊆ vertexBad G γ p ∪
      ⋃ x : localHalfEdges G γ p, range (localSpoke γ x.1) := by
  rintro z ⟨hzU, hzp⟩
  rw [G.U_eq] at hzU
  rcases hzU with hzV | hzE
  · exact Or.inl (Or.inl ⟨hzV, hzp⟩)
  · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hzE
    rcases closure_edge_subset_spoke_union hγ he hze with h1 | h1
    · by_cases hm : (e, false) ∈ localHalfEdges G γ p
      · exact Or.inr (mem_iUnion.mpr ⟨⟨(e, false), hm⟩, h1⟩)
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨(e, false), ⟨he, hm⟩, h1⟩))
    · by_cases hm : (e, true) ∈ localHalfEdges G γ p
      · exact Or.inr (mem_iUnion.mpr ⟨⟨(e, true), hm⟩, h1⟩)
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨(e, true), ⟨he, hm⟩, h1⟩))

/-! ## 4. Entry Curve from Any Point of `closure r` (`exists_region_entry_path`) -/

private theorem exists_region_entry_path_at_vertex
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (e : ClosedUnitDisc ≃ₜ S) (G : Drawing S) (hProper : G.IsProper)
    {r : Set S} (hr : r ∈ G.R) {p : S} (hpU : p ∈ G.U) (hpV : p ∈ G.V) :
    let ι : S → EuclideanPlane := fun x => (e.symm x).1
    let U_full : Set EuclideanPlane := UnitCircle ∪ ι '' G.U
    let R_open : Set EuclideanPlane := ι '' (r \ bd S)
    Continuous ι → Function.Injective ι → IsClosedMap ι →
    (∀ x : S, ι x ∈ UnitCircle ↔ x ∈ bd S) →
    IsOpen R_open → R_open ⊆ U_fullᶜ → ι p ∈ closure R_open →
    ∃ α : C(I, S), α 0 = p ∧ ∀ t : I, 0 < (t : ℝ) → α t ∈ r \ bd S := by
  classical
  intro ι U_full R_open hι_cont hι_inj hι_closed hι_bd hR_open hR_sub hc_cl
  have : Nonempty S := ⟨p⟩
  obtain ⟨γ, hγ⟩ := GM11.exists_edgePar G
  let H := localHalfEdges G γ p
  have : Fintype H := (finite_localHalfEdges G γ p).fintype
  have hBad_closed : IsClosed (vertexBad G γ p) := isClosed_vertexBad G hγ p
  have hp_not_Bad : p ∉ vertexBad G γ p := notMem_vertexBad G hγ hpV
  have hU_sdiff := U_sdiff_subset_vertexBad_union_spokes G hγ p
  have hspoke_sub : ∀ x : H, range (fun t => ι (localSpoke γ x.1 t)) ⊆ U_full := by
    rintro x _ ⟨t, rfl⟩
    right
    refine ⟨localSpoke γ x.1 t, ?_, rfl⟩
    by_cases ht0 : 0 < t
    · exact G.closure_subset_U x.2.1 (subset_closure (localSpoke_mem_edge hγ x.2.1 ht0))
    · have ht_eq : t = 0 := le_antisymm (not_lt.mp ht0) bot_le
      rw [ht_eq, localSpoke_zero, x.2.2]
      exact G.V_subset_U hpV
  by_cases hp_bd : p ∈ bd S
  · -- Boundary vertex: combine H with the two boundary semicircles
    have hc_unit : ι p ∈ UnitCircle := (hι_bd p).mpr hp_bd
    let sp : H ⊕ Bool → I → EuclideanPlane := fun i t =>
      match i with
      | .inl x => ι (localSpoke γ x.1 t)
      | .inr b => bdSpoke (ι p) b t
    have h2 : 2 ≤ Fintype.card (H ⊕ Bool) := by
      rw [Fintype.card_sum, Fintype.card_bool]
      omega
    let Bad : Set EuclideanPlane := ι '' vertexBad G γ p
    have hBad : IsClosed Bad := hι_closed _ hBad_closed
    have hcBad : ι p ∉ Bad := by
      rintro ⟨x, hx, hxp⟩
      exact hp_not_Bad (hι_inj hxp ▸ hx)
    have hsp_cont : ∀ i, Continuous (sp i) := by
      rintro (x | b)
      · exact hι_cont.comp (continuous_localSpoke hγ x.2.1)
      · exact continuous_bdSpoke (ι p) b
    have hsp_zero : ∀ i, sp i 0 = ι p := by
      rintro (x | b)
      · simp [sp, localSpoke_zero, x.2.2]
      · exact bdSpoke_zero (ι p) b
    have hsp_inj : ∀ i, Function.Injective (sp i) := by
      rintro (x | b)
      · exact hι_inj.comp (localSpoke_injective hγ x.2.1)
      · exact bdSpoke_injective hc_unit b
    have hsp_disj : ∀ i j, i ≠ j → ∀ s t : I, 0 < s → 0 < t →
        sp i s = sp j t → s = 1 ∧ t = 1 := by
      rintro (x | b₁) (y | b₂) hij s t hs ht heq
      · have hxy : x.1 ≠ y.1 := fun h => hij (congrArg Sum.inl (Subtype.ext h))
        exact localSpoke_eq_of_ne hγ x.2.1 y.2.1 hxy hs ht (hι_inj heq)
      · exfalso
        have hmem_e : localSpoke γ x.1 s ∈ x.1.1 := localSpoke_mem_edge hγ x.2.1 hs
        have hmem_U : localSpoke γ x.1 s ∈ G.U := (x.2.1.2.1 hmem_e).1
        have hnot_V : localSpoke γ x.1 s ∉ G.V := (x.2.1.2.1 hmem_e).2
        have hmem_bd : localSpoke γ x.1 s ∈ bd S := by
          rw [← hι_bd]
          change sp (.inl x) s ∈ UnitCircle
          rw [heq]
          exact bdSpoke_mem_unitCircle hc_unit b₂ t
        exact hnot_V (hProper ⟨hmem_bd, hmem_U⟩)
      · exfalso
        have hmem_e : localSpoke γ y.1 t ∈ y.1.1 := localSpoke_mem_edge hγ y.2.1 ht
        have hmem_U : localSpoke γ y.1 t ∈ G.U := (y.2.1.2.1 hmem_e).1
        have hnot_V : localSpoke γ y.1 t ∉ G.V := (y.2.1.2.1 hmem_e).2
        have hmem_bd : localSpoke γ y.1 t ∈ bd S := by
          rw [← hι_bd]
          change sp (.inl y) t ∈ UnitCircle
          rw [← heq]
          exact bdSpoke_mem_unitCircle hc_unit b₁ s
        exact hnot_V (hProper ⟨hmem_bd, hmem_U⟩)
      · have hb : b₁ ≠ b₂ := fun h => hij (congrArg Sum.inr h)
        exact bdSpoke_eq_of_ne hc_unit hb hs ht heq
    have hsp_sub : ∀ i, range (sp i) ⊆ U_full := by
      rintro (x | b)
      · exact hspoke_sub x
      · rintro _ ⟨t, rfl⟩
        exact Or.inl (bdSpoke_mem_unitCircle hc_unit b t)
    have hU_cover : U_full ⊆ Bad ∪ ⋃ i, range (sp i) := by
      rintro z (hz_unit | ⟨x, hxU, rfl⟩)
      · rcases unitCircle_subset_range_bdSpoke hc_unit hz_unit with h1 | h1
        · exact Or.inr (mem_iUnion.mpr ⟨.inr false, h1⟩)
        · exact Or.inr (mem_iUnion.mpr ⟨.inr true, h1⟩)
      · by_cases hxp : x = p
        · subst hxp
          exact Or.inr (mem_iUnion.mpr ⟨.inr false, ⟨0, bdSpoke_zero (ι x) false⟩⟩)
        · rcases hU_sdiff ⟨hxU, hxp⟩ with hxBad | hxH
          · exact Or.inl ⟨x, hxBad, rfl⟩
          · obtain ⟨y, ⟨t, rfl⟩⟩ := mem_iUnion.mp hxH
            exact Or.inr (mem_iUnion.mpr ⟨.inl y, ⟨t, rfl⟩⟩)
    obtain ⟨P, α, hP_conn, hP_disj, hP_inter, hα0, hαP⟩ :=
      exists_entry_path_of_spokes h2 hR_open hR_sub hc_cl Bad hBad hcBad sp
        hsp_cont hsp_zero hsp_inj hsp_disj hsp_sub hU_cover
    exact entry_path_of_plane e G hr hP_conn hP_disj hP_inter hα0 hαP
  · -- Interior vertex: p ∈ G.V \ bd S
    let Bad : Set EuclideanPlane := UnitCircle ∪ ι '' vertexBad G γ p
    have hBad : IsClosed Bad := Metric.isClosed_sphere.union (hι_closed _ hBad_closed)
    have hcBad : ι p ∉ Bad := by
      rintro (h_unit | ⟨x, hx, hxp⟩)
      · exact hp_bd ((hι_bd p).mp h_unit)
      · exact hp_not_Bad (hι_inj hxp ▸ hx)
    by_cases h2 : 2 ≤ Fintype.card H
    · let sp : H → I → EuclideanPlane := fun x t => ι (localSpoke γ x.1 t)
      have hsp_cont : ∀ x, Continuous (sp x) :=
        fun x => hι_cont.comp (continuous_localSpoke hγ x.2.1)
      have hsp_zero : ∀ x, sp x 0 = ι p := by
        intro x; simp [sp, localSpoke_zero, x.2.2]
      have hsp_inj : ∀ x, Function.Injective (sp x) :=
        fun x => hι_inj.comp (localSpoke_injective hγ x.2.1)
      have hsp_disj : ∀ x y, x ≠ y → ∀ s t : I, 0 < s → 0 < t →
          sp x s = sp y t → s = 1 ∧ t = 1 := by
        intro x y hxy s t hs ht heq
        have hne : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
        exact localSpoke_eq_of_ne hγ x.2.1 y.2.1 hne hs ht (hι_inj heq)
      have hU_cover : U_full ⊆ Bad ∪ ⋃ x, range (sp x) := by
        rintro z (hz_unit | ⟨x, hxU, rfl⟩)
        · exact Or.inl (Or.inl hz_unit)
        · by_cases hxp : x = p
          · subst hxp
            obtain ⟨x₀⟩ : Nonempty H :=
              Fintype.card_pos_iff.mp (lt_of_lt_of_le zero_lt_two h2)
            exact Or.inr (mem_iUnion.mpr ⟨x₀, ⟨0, hsp_zero x₀⟩⟩)
          · rcases hU_sdiff ⟨hxU, hxp⟩ with hxBad | hxH
            · exact Or.inl (Or.inr ⟨x, hxBad, rfl⟩)
            · obtain ⟨y, ⟨t, rfl⟩⟩ := mem_iUnion.mp hxH
              exact Or.inr (mem_iUnion.mpr ⟨y, ⟨t, rfl⟩⟩)
      obtain ⟨P, α, hP_conn, hP_disj, hP_inter, hα0, hαP⟩ :=
        exists_entry_path_of_spokes h2 hR_open hR_sub hc_cl Bad hBad hcBad sp
          hsp_cont hsp_zero hsp_inj hsp_disj hspoke_sub hU_cover
      exact entry_path_of_plane e G hr hP_conn hP_disj hP_inter hα0 hαP
    · by_cases h1 : Fintype.card H = 1
      · obtain ⟨x₀, hx₀⟩ := Fintype.card_eq_one_iff.mp h1
        let sp₀ : I → EuclideanPlane := fun t => ι (localSpoke γ x₀.1 t)
        have hsp_cont : Continuous sp₀ := hι_cont.comp (continuous_localSpoke hγ x₀.2.1)
        have hsp_zero : sp₀ 0 = ι p := by simp [sp₀, localSpoke_zero, x₀.2.2]
        have hsp_inj : Function.Injective sp₀ := hι_inj.comp (localSpoke_injective hγ x₀.2.1)
        have hU_cover : U_full ⊆ Bad ∪ range sp₀ := by
          rintro z (hz_unit | ⟨x, hxU, rfl⟩)
          · exact Or.inl (Or.inl hz_unit)
          · by_cases hxp : x = p
            · subst hxp
              exact Or.inr ⟨0, hsp_zero⟩
            · rcases hU_sdiff ⟨hxU, hxp⟩ with hxBad | hxH
              · exact Or.inl (Or.inr ⟨x, hxBad, rfl⟩)
              · obtain ⟨y, ⟨t, rfl⟩⟩ := mem_iUnion.mp hxH
                rw [hx₀ y]
                exact Or.inr ⟨t, rfl⟩
        obtain ⟨P, α, hP_conn, hP_disj, hP_inter, hα0, hαP⟩ :=
          exists_entry_path_of_one_spoke hR_sub hc_cl Bad hBad hcBad sp₀
            hsp_cont hsp_zero hsp_inj (hspoke_sub x₀) hU_cover
        exact entry_path_of_plane e G hr hP_conn hP_disj hP_inter hα0 hαP
      · have h0 : Fintype.card H = 0 := by omega
        have hH_empty : IsEmpty H := Fintype.card_eq_zero_iff.mp h0
        have hU_cover : U_full \ {ι p} ⊆ Bad := by
          rintro z ⟨hz_unit | ⟨x, hxU, rfl⟩, hzp⟩
          · exact Or.inl hz_unit
          · have hxp : x ≠ p := fun h => hzp (congrArg ι h)
            rcases hU_sdiff ⟨hxU, hxp⟩ with hxBad | hxH
            · exact Or.inr ⟨x, hxBad, rfl⟩
            · obtain ⟨y, _⟩ := mem_iUnion.mp hxH
              exact False.elim (hH_empty.false y)
        obtain ⟨P, α, hP_conn, hP_disj, hP_inter, hα0, hαP⟩ :=
          exists_entry_path_of_zero_spokes hR_sub hc_cl (Or.inr ⟨p, hpU, rfl⟩)
            Bad hBad hcBad hU_cover
        exact entry_path_of_plane e G hr hP_conn hP_disj hP_inter hα0 hαP

private theorem exists_region_entry_path_at_edge
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (e : ClosedUnitDisc ≃ₜ S) (G : Drawing S) (hProper : G.IsProper)
    {r : Set S} (hr : r ∈ G.R) {p : S} (hpU : p ∈ G.U) (hpV : p ∉ G.V) :
    let ι : S → EuclideanPlane := fun x => (e.symm x).1
    let U_full : Set EuclideanPlane := UnitCircle ∪ ι '' G.U
    let R_open : Set EuclideanPlane := ι '' (r \ bd S)
    Continuous ι → Function.Injective ι → IsClosedMap ι →
    (∀ x : S, ι x ∈ UnitCircle ↔ x ∈ bd S) →
    IsOpen R_open → R_open ⊆ U_fullᶜ → ι p ∈ closure R_open →
    ∃ α : C(I, S), α 0 = p ∧ ∀ t : I, 0 < (t : ℝ) → α t ∈ r \ bd S := by
  classical
  intro ι U_full R_open hι_cont hι_inj hι_closed hι_bd hR_open hR_sub hc_cl
  have hp_not_bd : p ∉ bd S := fun hbd => hpV (hProper ⟨hbd, hpU⟩)
  have hpE_mem : ∃ e_edge ∈ G.E, p ∈ e_edge := by
    rw [G.U_eq] at hpU
    rcases hpU with hpV' | hpE
    · exact False.elim (hpV hpV')
    · obtain ⟨e_edge, he_edge, hpe⟩ := mem_iUnion₂.mp hpE
      refine ⟨e_edge, he_edge, ?_⟩
      rw [← G.closure_diff_V he_edge]
      exact ⟨hpe, hpV⟩
  rcases hpE_mem with ⟨e_edge, he_edge, hpe⟩
  obtain ⟨γ_e, hγ_cont, hγ0, hγ1, hγ_inj, hγ_img⟩ := GM11.exists_edge_param G he_edge
  obtain ⟨t₀, ⟨ht₀0, ht₀1⟩, rfl⟩ : p ∈ γ_e '' Ioo 0 1 := by
    rw [hγ_img]; exact hpe
  have ht₀0_R : 0 < (t₀ : ℝ) := ht₀0
  have ht₀1_R : (t₀ : ℝ) < 1 := ht₀1
  have h_left_mem : ∀ s : I, (1 - (s : ℝ) / 2) * (t₀ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    intro s
    have hs0 := s.2.1
    have hs1 := s.2.2
    constructor <;> nlinarith
  have h_right_mem : ∀ s : I, (t₀ : ℝ) + ((s : ℝ) / 2) * (1 - (t₀ : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
    intro s
    have hs0 := s.2.1
    have hs1 := s.2.2
    constructor <;> nlinarith
  let par : Bool → I → I := fun b s =>
    if b then ⟨(t₀ : ℝ) + ((s : ℝ) / 2) * (1 - (t₀ : ℝ)), h_right_mem s⟩
    else ⟨(1 - (s : ℝ) / 2) * (t₀ : ℝ), h_left_mem s⟩
  have hpar_cont : ∀ b, Continuous (par b) := by
    intro b
    cases b <;> refine Continuous.subtype_mk ?_ _ <;> fun_prop
  have hpar_zero : ∀ b, par b 0 = t₀ := by
    intro b
    cases b <;> ext <;> simp [par]
  have hpar_ioo : ∀ b s, par b s ∈ Ioo (0 : I) 1 := by
    intro b s
    have hs0 := s.2.1
    have hs1 := s.2.2
    cases b
    · constructor
      · change (0 : ℝ) < (1 - (s : ℝ) / 2) * (t₀ : ℝ); nlinarith
      · change (1 - (s : ℝ) / 2) * (t₀ : ℝ) < 1; nlinarith
    · constructor
      · change (0 : ℝ) < (t₀ : ℝ) + ((s : ℝ) / 2) * (1 - (t₀ : ℝ)); nlinarith
      · change (t₀ : ℝ) + ((s : ℝ) / 2) * (1 - (t₀ : ℝ)) < 1; nlinarith
  let sp : Bool → I → EuclideanPlane := fun b s => ι (γ_e (par b s))
  have hsp_cont : ∀ b, Continuous (sp b) :=
    fun b => hι_cont.comp (hγ_cont.comp (hpar_cont b))
  have hsp_zero : ∀ b, sp b 0 = ι (γ_e t₀) := by
    intro b; simp [sp, hpar_zero]
  have hsp_inj : ∀ b, Function.Injective (sp b) := by
    intro b s₁ s₂ heq
    have h1 := hγ_inj (hpar_ioo b s₁) (hpar_ioo b s₂) (hι_inj heq)
    have h2 := congrArg Subtype.val h1
    cases b <;> simp only [par, Bool.false_eq_true, ite_false, ite_true] at h2 <;>
      exact Subtype.ext (by nlinarith)
  have hsp_disj : ∀ b₁ b₂, b₁ ≠ b₂ → ∀ s t : I, 0 < s → 0 < t →
      sp b₁ s = sp b₂ t → s = 1 ∧ t = 1 := by
    intro b₁ b₂ hb s t hs ht heq
    exfalso
    have h1 := hγ_inj (hpar_ioo b₁ s) (hpar_ioo b₂ t) (hι_inj heq)
    have h2 := congrArg Subtype.val h1
    have hs_pos : (0 : ℝ) < s := hs
    have ht_pos : (0 : ℝ) < t := ht
    cases b₁ <;> cases b₂
    · exact hb rfl
    · simp only [par, Bool.false_eq_true, ite_false, ite_true] at h2
      nlinarith
    · simp only [par, Bool.false_eq_true, ite_true, ite_false] at h2
      nlinarith
    · exact hb rfl
  have hsp_sub : ∀ b, range (sp b) ⊆ U_full := by
    rintro b _ ⟨s, rfl⟩
    right
    refine ⟨γ_e (par b s), ?_, rfl⟩
    have hmem_e : γ_e (par b s) ∈ e_edge := by
      rw [← hγ_img]
      exact ⟨par b s, hpar_ioo b s, rfl⟩
    exact (he_edge.2.1 hmem_e).1
  let Far : Set I := {t : I | (t : ℝ) ≤ (t₀ : ℝ) / 2 ∨ (t₀ : ℝ) + (1 - (t₀ : ℝ)) / 2 ≤ (t : ℝ)}
  have hFar_closed : IsClosed Far :=
    (isClosed_le continuous_subtype_val continuous_const).union
      (isClosed_le continuous_const continuous_subtype_val)
  let Bad : Set EuclideanPlane :=
    UnitCircle ∪ ι '' ((G.U \ e_edge) ∪ γ_e '' Far)
  have hBad : IsClosed Bad := by
    refine Metric.isClosed_sphere.union (hι_closed _ ?_)
    exact (GM11.isClosed_U_sdiff_edge G he_edge).union
      (hFar_closed.isCompact.image hγ_cont).isClosed
  have hcBad : ι (γ_e t₀) ∉ Bad := by
    rintro (h_unit | ⟨x, hx, hxe⟩)
    · exact hp_not_bd ((hι_bd (γ_e t₀)).mp h_unit)
    · have hxp : x = γ_e t₀ := hι_inj hxe
      subst hxp
      rcases hx with ⟨_, hnot_e⟩ | ⟨t, htFar, hteq⟩
      · exact hnot_e hpe
      · have ht_ioo : t ∈ Ioo (0 : I) 1 := by
          refine ⟨unitInterval.pos_iff_ne_zero.mpr ?_, unitInterval.lt_one_iff_ne_one.mpr ?_⟩
          · rintro rfl; exact hpV (hteq ▸ hγ0)
          · rintro rfl; exact hpV (hteq ▸ hγ1)
        have h_eq := hγ_inj ht_ioo ⟨ht₀0, ht₀1⟩ hteq
        subst h_eq
        rcases htFar with hle | hge <;> linarith
  have hU_cover : U_full ⊆ Bad ∪ ⋃ b, range (sp b) := by
    rintro z (hz_unit | ⟨x, hxU, rfl⟩)
    · exact Or.inl (Or.inl hz_unit)
    · by_cases hxe : x ∈ e_edge
      · rw [← hγ_img] at hxe
        rcases hxe with ⟨t, _, rfl⟩
        by_cases htFar : t ∈ Far
        · exact Or.inl (Or.inr ⟨γ_e t, Or.inr ⟨t, htFar, rfl⟩, rfl⟩)
        · simp only [Far, mem_ofPred_eq, not_or, not_le] at htFar
          rcases le_or_gt (t : ℝ) (t₀ : ℝ) with hle | hgt
          · right
            refine mem_iUnion.mpr ⟨false, ?_⟩
            let s : I := ⟨2 * (1 - (t : ℝ) / (t₀ : ℝ)),
              by have : (t : ℝ) / (t₀ : ℝ) ≤ 1 := (div_le_one ht₀0_R).mpr hle; linarith,
              by
                have : (1 / 2 : ℝ) < (t : ℝ) / (t₀ : ℝ) := by
                  rw [div_lt_div_iff₀ zero_lt_two ht₀0_R]; linarith [htFar.1]
                linarith⟩
            refine ⟨s, ?_⟩
            change ι (γ_e (par false s)) = ι (γ_e t)
            congr 2
            ext
            change (1 - (2 * (1 - (t : ℝ) / (t₀ : ℝ))) / 2) * (t₀ : ℝ) = (t : ℝ)
            field_simp
            ring
          · right
            refine mem_iUnion.mpr ⟨true, ?_⟩
            have h_one_sub : 0 < 1 - (t₀ : ℝ) := by linarith
            let s : I := ⟨2 * ((t : ℝ) - (t₀ : ℝ)) / (1 - (t₀ : ℝ)),
              div_nonneg (by linarith) h_one_sub.le,
              (div_le_one h_one_sub).mpr (by linarith [htFar.2])⟩
            refine ⟨s, ?_⟩
            change ι (γ_e (par true s)) = ι (γ_e t)
            congr 2
            ext
            change (t₀ : ℝ) + ((2 * ((t : ℝ) - (t₀ : ℝ)) / (1 - (t₀ : ℝ))) / 2) *
              (1 - (t₀ : ℝ)) = (t : ℝ)
            field_simp
            ring
      · exact Or.inl (Or.inr ⟨x, Or.inl ⟨hxU, hxe⟩, rfl⟩)
  have h2_bool : 2 ≤ Fintype.card Bool := by simp
  obtain ⟨P, α, hP_conn, hP_disj, hP_inter, hα0, hαP⟩ :=
    exists_entry_path_of_spokes h2_bool hR_open hR_sub hc_cl Bad hBad hcBad sp
      hsp_cont hsp_zero hsp_inj hsp_disj hsp_sub hU_cover
  exact entry_path_of_plane e G hr hP_conn hP_disj hP_inter hα0 hαP

/-- From a point of `U(G)` in the closure of a region `r` there is a curve into `r` that leaves
`bd(S)` at once.
Its open part lies in the plane model of the open disc, so `exists_region_entry_path` gets this
stronger form for free. -/
theorem exists_region_entry_path_of_mem_U
    {S : Type u} [TopologicalSpace S] (G : Drawing S)
    (hDisc : IsClosedDiscSpace S) (hProper : G.IsProper)
    (r : Set S) (hr : r ∈ G.R)
    (p : S) (hp : p ∈ closure r) (hpU : p ∈ G.U) :
    ∃ α : C(I, S), α 0 = p ∧ ∀ t : I, 0 < (t : ℝ) → α t ∈ r \ bd S := by
  classical
  have : T2Space S := t2Space_of_isClosedDiscSpace hDisc
  obtain ⟨e⟩ := hDisc
  have hDisc : IsClosedDiscSpace S := ⟨e⟩
  have : Nonempty S := ⟨e ⟨0, Metric.mem_closedBall_self zero_le_one⟩⟩
  let ι : S → EuclideanPlane := fun x => (e.symm x).1
  have hι_cont : Continuous ι := continuous_subtype_val.comp e.symm.continuous
  have hι_inj : Function.Injective ι := fun x y h => e.symm.injective (Subtype.ext h)
  have hι_closed : IsClosedMap ι :=
    Metric.isClosed_closedBall.isClosedEmbedding_subtypeVal.isClosedMap.comp e.symm.isClosedMap
  have hbd_img := image_bd_homeomorph e
  rw [bd_closedUnitDisc] at hbd_img
  have hbd_closed : IsClosed (bd S) := by
    rw [← hbd_img]
    exact e.isClosedMap _ (Metric.isClosed_sphere.preimage continuous_subtype_val)
  have hι_bd : ∀ x : S, ι x ∈ UnitCircle ↔ x ∈ bd S := by
    intro x
    rw [← hbd_img]
    constructor
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [ι] using hy
  let U_full : Set EuclideanPlane := UnitCircle ∪ ι '' G.U
  let R_open : Set EuclideanPlane := ι '' (r \ bd S)
  have hr_open : IsOpen r := isOpen_region hDisc G hr
  have hR_open : IsOpen R_open := by
    have h1 : IsOpen (e ⁻¹' (r \ bd S)) :=
      (hr_open.sdiff hbd_closed).preimage e.continuous
    have h2 : Subtype.val '' (e ⁻¹' (r \ bd S)) = R_open := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨e x, hx, by simp [ι]⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨e.symm y, by simpa using hy, rfl⟩
    have hsub : Subtype.val '' (e ⁻¹' (r \ bd S)) ⊆ OpenUnitDisc := by
      rw [h2]
      rintro _ ⟨x, ⟨_, hxbd⟩, rfl⟩
      have hle : ‖ι x‖ ≤ 1 := mem_closedBall_zero_iff.mp (e.symm x).2
      have hne : ‖ι x‖ ≠ 1 := by
        intro hnorm
        exact hxbd ((hι_bd x).mp (by simpa [UnitCircle] using hnorm))
      simpa [OpenUnitDisc] using lt_of_le_of_ne hle hne
    rw [← h2]
    obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp h1
    have h_eq : Subtype.val '' (e ⁻¹' (r \ bd S)) = W ∩ OpenUnitDisc := by
      ext z
      constructor
      · intro hz
        have hzO := hsub hz
        rcases hz with ⟨x, hx, rfl⟩
        rw [← hWeq] at hx
        exact ⟨hx, hzO⟩
      · rintro ⟨hzW, hzO⟩
        let x : ClosedUnitDisc := ⟨z, Metric.ball_subset_closedBall hzO⟩
        have hx : x ∈ e ⁻¹' (r \ bd S) := by rw [← hWeq]; exact hzW
        exact ⟨x, hx, rfl⟩
    rw [h_eq]
    exact hW.inter Metric.isOpen_ball
  have hR_sub : R_open ⊆ U_fullᶜ := by
    rintro _ ⟨x, ⟨hxr, hxbd⟩, rfl⟩ (h_unit | ⟨y, hyU, hyx⟩)
    · exact hxbd ((hι_bd x).mp h_unit)
    · have hyx' : y = x := hι_inj hyx
      subst hyx'
      rcases hr with ⟨z₀, _, rfl⟩
      exact (connectedComponentIn_subset (univ \ G.U) z₀ hxr).2 hyU
  have hc_cl : ι p ∈ closure R_open := by
    have hp_cl' : p ∈ closure (r \ bd S) := by
      rw [closure_sdiff_bd_eq hDisc hr_open]
      exact hp
    exact image_closure_subset_closure_image hι_cont ⟨p, hp_cl', rfl⟩
  by_cases hpV : p ∈ G.V
  · exact exists_region_entry_path_at_vertex e G hProper hr hpU hpV
      hι_cont hι_inj hι_closed hι_bd hR_open hR_sub hc_cl
  · exact exists_region_entry_path_at_edge e G hProper hr hpU hpV
      hι_cont hι_inj hι_closed hι_bd hR_open hR_sub hc_cl

/-- For any point `p ∈ closure r` of a region `r ∈ G.R` of a proper drawing `G` on a closed disc
space `S`, there is a continuous curve `α : C(unitInterval, S)` with `α 0 = p` and `α t ∈ r` for all
`t > 0`. -/
theorem exists_region_entry_path
    {S : Type u} [TopologicalSpace S] (G : Drawing S)
    (hDisc : IsClosedDiscSpace S) (hProper : G.IsProper)
    (r : Set S) (hr : r ∈ G.R)
    (p : S) (hp : p ∈ closure r) :
    ∃ α : C(I, S), α 0 = p ∧ ∀ t : I, 0 < (t : ℝ) → α t ∈ r := by
  classical
  have : T2Space S := t2Space_of_isClosedDiscSpace hDisc
  by_cases hpU : p ∈ G.U
  · obtain ⟨α, h0, h1⟩ := exists_region_entry_path_of_mem_U G hDisc hProper r hr p hp hpU
    exact ⟨α, h0, fun t ht => (h1 t ht).1⟩
  · -- Point off G.U: p ∈ r directly, so constant path works
    have hpr : p ∈ r := by
      have hp_compl : p ∈ univ \ G.U := ⟨mem_univ p, hpU⟩
      let r' := connectedComponentIn (univ \ G.U) p
      have hr'_mem : r' ∈ G.R := ⟨p, hp_compl, rfl⟩
      have hr'_open : IsOpen r' := isOpen_region hDisc G hr'_mem
      have hp_r' : p ∈ r' := mem_connectedComponentIn hp_compl
      obtain ⟨z, hzr', hzr⟩ := _root_.mem_closure_iff.mp hp r' hr'_open hp_r'
      rcases hr with ⟨z₀, _, rfl⟩
      have h_eq : connectedComponentIn (univ \ G.U) p = connectedComponentIn (univ \ G.U) z₀ :=
        (connectedComponentIn_eq hzr').trans (connectedComponentIn_eq hzr).symm
      rw [← h_eq]
      exact hp_r'
    exact ⟨ContinuousMap.const I p, rfl, fun _ _ => hpr⟩

/-! ## 5. Complementary Curves Between Two Points of `closure r` (`exists_region_curve`) -/

/-- Any two points `p, q ∈ closure r` of a region `r ∈ G.R` of a proper drawing `G` on a closed
disc space `S` are joined by a continuous curve `γ : C(unitInterval, S)` with `γ 0 = p`,
`γ 1 = q`, and `γ t ∈ r` for all `t ∈ Ioo 0 1`. -/
theorem exists_region_curve
    {S : Type u} [TopologicalSpace S] (G : Drawing S)
    (hDisc : IsClosedDiscSpace S) (hProper : G.IsProper)
    (r : Set S) (hr : r ∈ G.R)
    (p : S) (hp : p ∈ closure r)
    (q : S) (hq : q ∈ closure r) :
    ∃ γ : C(I, S), γ 0 = p ∧ γ 1 = q ∧
      ∀ t : I, (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 → γ t ∈ r := by
  obtain ⟨α_p, hα_p0, hα_pr⟩ := exists_region_entry_path G hDisc hProper r hr p hp
  obtain ⟨α_q, hα_q0, hα_qr⟩ := exists_region_entry_path G hDisc hProper r hr q hq
  have hp1_r : α_p 1 ∈ r := hα_pr 1 zero_lt_one
  have hq1_r : α_q 1 ∈ r := hα_qr 1 zero_lt_one
  have hr_pc : IsPathConnected r := isPathConnected_region hDisc G hr
  obtain ⟨β, hβ_r⟩ := hr_pc.joinedIn (α_p 1) hp1_r (α_q 1) hq1_r
  let P_p : Path p (α_p 1) := ⟨α_p, hα_p0, rfl⟩
  let P_q : Path q (α_q 1) := ⟨α_q, hα_q0, rfl⟩
  let P : Path p q := P_p.trans (β.trans P_q.symm)
  refine ⟨P.toContinuousMap, P.source, P.target, ?_⟩
  intro t ⟨ht0, ht1⟩
  change (P_p.trans (β.trans P_q.symm)) t ∈ r
  rw [Path.trans_apply]
  split_ifs with h1
  · apply hα_pr
    change 0 < 2 * (t : ℝ)
    linarith
  · rw [Path.trans_apply]
    split_ifs with h2
    · exact hβ_r _
    · change α_q (σ ⟨2 * (2 * (t : ℝ) - 1) - 1, _⟩) ∈ r
      apply hα_qr
      change 0 < 1 - (2 * (2 * (t : ℝ) - 1) - 1)
      linarith

theorem not_mem_U_of_mem_region {S : Type u} [TopologicalSpace S]
    (G : Drawing S) {r : Set S} (hr : r ∈ G.R) {z : S} (hz : z ∈ r) : z ∉ G.U := by
  rcases hr with ⟨z₀, _, rfl⟩
  exact (connectedComponentIn_subset (univ \ G.U) z₀ hz).2

theorem IsXYChain.leftEndpoint_mem_closure
    {S : Type u} [TopologicalSpace S] {G : Drawing S} {x y : S} {A : List (ChainTerm S)}
    (hChain : IsXYChain G x y A) :
    let leftPt := ChainTerm.leftEndpoint A x
    ∀ (i : Fin A.length) (r : Set S),
        A[i.1]'i.2 = .inr r → leftPt i ∈ closure r ∧
          (leftPt i ∈ G.U → leftPt i ∈ G.V ∧ Sum.inl (leftPt i) ∈ A) := by
  intro leftPt
  have h_chain_rel : ∀ (j : ℕ) (hj : j + 1 < A.length),
      ChainTerm.AreIncident G A[j] A[j + 1] :=
    fun j hj => List.isChain_iff_getElem.mp hChain.isChain j hj
  intro i r hir
  have hrR : r ∈ G.R := by
    have hv := hChain.valid (A[i.1]'i.2) (List.getElem_mem i.2)
    simpa [hir, ChainTerm.IsValid] using hv
  by_cases hi0 : i.1 = 0
  · have hhead : A.head hChain.ne_nil = A[i.1]'i.2 := by
      rw [List.head_eq_getElem_zero]
      congr 1; omega
    have hmatch := hChain.head_matches
    rw [hhead, hir] at hmatch
    change x ∈ r at hmatch
    have hleft : leftPt i = x := by
      dsimp [leftPt, ChainTerm.leftEndpoint]
      rw [hir]
      simp [hi0]
    rw [hleft]
    refine ⟨subset_closure hmatch, fun hxU => ?_⟩
    exfalso
    exact not_mem_U_of_mem_region G hrR hmatch hxU
  · have hprev_lt : i.1 - 1 < A.length := Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.2
    have hstep : (i.1 - 1) + 1 < A.length := by omega
    have hinc := h_chain_rel (i.1 - 1) hstep
    have h_idx_eq : A[(i.1 - 1) + 1]'hstep = A[i.1]'i.2 := by congr 1; omega
    rw [h_idx_eq, hir] at hinc
    rcases h_prev : A[i.1 - 1]'hprev_lt with v | r'
    · rw [h_prev] at hinc
      rcases hinc with ⟨hvV, _, hv_cl⟩
      have hleft : leftPt i = v := by simp [leftPt, ChainTerm.leftEndpoint, hir, hi0, h_prev]
      rw [hleft]
      refine ⟨hv_cl, fun _ => ⟨hvV, ?_⟩⟩
      rw [← h_prev]
      exact List.getElem_mem hprev_lt
    · rw [h_prev] at hinc
      exact False.elim hinc

theorem IsXYChain.rightEndpoint_mem_closure
    {S : Type u} [TopologicalSpace S] {G : Drawing S} {x y : S} {A : List (ChainTerm S)}
    (hChain : IsXYChain G x y A) :
    let rightPt := ChainTerm.rightEndpoint A y
    ∀ (i : Fin A.length) (r : Set S),
        A[i.1]'i.2 = .inr r → rightPt i ∈ closure r ∧
          (rightPt i ∈ G.U → rightPt i ∈ G.V ∧ Sum.inl (rightPt i) ∈ A) := by
  intro rightPt
  have h_chain_rel : ∀ (j : ℕ) (hj : j + 1 < A.length),
      ChainTerm.AreIncident G A[j] A[j + 1] :=
    fun j hj => List.isChain_iff_getElem.mp hChain.isChain j hj
  intro i r hir
  have hrR : r ∈ G.R := by
    have hv := hChain.valid (A[i.1]'i.2) (List.getElem_mem i.2)
    simpa [hir, ChainTerm.IsValid] using hv
  by_cases hi1 : i.1 + 1 = A.length
  · have hlast : A.getLast hChain.ne_nil = A[i.1]'i.2 := by
      rw [List.getLast_eq_getElem]
      congr 1; omega
    have hmatch := hChain.last_matches
    rw [hlast, hir] at hmatch
    change y ∈ r at hmatch
    have hright : rightPt i = y := by simp [rightPt, ChainTerm.rightEndpoint, hir, hi1]
    rw [hright]
    refine ⟨subset_closure hmatch, fun hyU => ?_⟩
    exfalso
    exact not_mem_U_of_mem_region G hrR hmatch hyU
  · have hnext_lt : i.1 + 1 < A.length := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt i.2) hi1
    have hinc := h_chain_rel i.1 hnext_lt
    rw [hir] at hinc
    rcases h_next : A[i.1 + 1]'hnext_lt with v | r'
    · rw [h_next] at hinc
      rcases hinc with ⟨hvV, _, hv_cl⟩
      have hright : rightPt i = v := by simp [rightPt, ChainTerm.rightEndpoint, hir, hi1, h_next]
      rw [hright]
      refine ⟨hv_cl, fun _ => ⟨hvV, ?_⟩⟩
      rw [← h_next]
      exact List.getElem_mem hnext_lt
    · rw [h_next] at hinc
      exact False.elim hinc

end GraphMinor.GM06
