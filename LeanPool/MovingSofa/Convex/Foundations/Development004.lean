/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Analysis.Foundations.Development003
public import LeanPool.MovingSofa.Infrastructure.Analysis.Foundations.Development002
public import LeanPool.MovingSofa.Convex.Foundations.Development002
public import LeanPool.MovingSofa.Convex.Foundations.Development003
public import LeanPool.MovingSofa.Infrastructure.Curves.Foundations.Development002
public import LeanPool.MovingSofa.Infrastructure.MathlibExtensions.Foundations.Development001
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development004
public import LeanPool.MovingSofa.Infrastructure.Topology.Foundations.Development001

/-!
# Moving sofa: related mathematical developments

* `Convex.ArcCutBoundary`.
* `Convex.ArcArea`.
* `Convex.ArcBilinear`.
* `Convex.ArcJordan`.
* `Convex.ArcRegionArea`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Arc Cut Boundary
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open Set

private theorem normalVector_injective_cut : Function.Injective normalVector := by
  intro a b hab
  induction a using Real.Angle.induction_on with
  | _ a =>
    induction b using Real.Angle.induction_on with
    | _ b =>
      apply Real.Angle.cos_sin_inj
      · exact congrFun (congrArg WithLp.ofLp hab) 0
      · exact congrFun (congrArg WithLp.ofLp hab) 1

-- Duplicate of the current private UpperGraph helper; promote with the separation helper.
private theorem exteriorNormal_eq_of_orthogonal_of_interior_nonempty_cut
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    {p v : Point} (hv : v ≠ 0) {a b : Real.Angle}
    (ha : IsExteriorNormal K p a) (hb : IsExteriorNormal K p b)
    (hva : inner ℝ v (normalVector a) = 0)
    (hvb : inner ℝ v (normalVector b) = 0) : a = b := by
  let orientation : Orientation ℝ Point (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  rcases EuclideanGeometry.eq_or_eq_neg_of_unit_orthogonal orientation hv
      (norm_normalVector a) (norm_normalVector b) hva hvb with hab | hab
  · exact normalVector_injective_cut hab
  · exfalso
    obtain ⟨z, hz⟩ := hK
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
    let q := z + (ε / 2) • normalVector a
    have hq : q ∈ K := interior_subset (hball (by
      rw [Metric.mem_ball, dist_eq_norm]
      rw [show q - z = (ε / 2) • normalVector a by simp [q], norm_smul,
        norm_normalVector, Real.norm_eq_abs, abs_of_pos (div_pos hε (by norm_num))]
      norm_num
      linarith))
    have haz := ha z (interior_subset hz)
    have hbz := hb z (interior_subset hz)
    have hba : normalVector b = -normalVector a := by rw [hab]; simp
    rw [hba, inner_neg_right] at hbz
    have heq : inner ℝ (z - p) (normalVector a) = 0 := by linarith
    have haq := ha q hq
    have hqp : q - p = (z - p) + (ε / 2) • normalVector a := by
      dsimp only [q]
      module
    rw [hqp, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq,
      norm_normalVector a, heq, zero_add] at haq
    have : ε / 2 ≤ 0 := by simpa using haq
    linarith

private theorem isExteriorNormal_of_mem_exposedEdge
    (K : ConvexBody Point) {p : Point} {a : Real.Angle}
    (hp : p ∈ exposedEdge K a) : IsExteriorNormal K p a := by
  intro q hq
  have hqle := inner_le_supportValue K hq a
  have hpEq := hp.2
  change inner ℝ p (normalVector a) = supportValue K a at hpEq
  rw [inner_sub_left, hpEq]
  linarith

/-- The frontier of a cut body is the retained convex boundary arc together with its chord. -/
theorem frontier_eq_convexBoundaryArc_union_segment_of_cut
    (K K' : ConvexBody Point) (a b t : ℝ) (P Q : Point)
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P})
    (hmiddle : ∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s)
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q})
    (hterminal : exposedEdge K' (t + Real.pi) = segment ℝ Q P)
    (hInt : (interior (K' : Set Point)).Nonempty) :
    frontier (K' : Set Point) = convexBoundaryArc K a b ∪ segment ℝ P Q := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨u, hxu⟩ := exists_mem_exposedEdge_of_mem_frontier K' hInt hx
    let _ : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
    let s := AddCircle.equivIoc (2 * Real.pi) (t - Real.pi) u
    have hs : (s : ℝ) ∈ Set.Ioc (t - Real.pi) (t + Real.pi) := by
      have := s.property
      convert this using 1
      ring_nf
    have hsu : (((s : ℝ) : Real.Angle)) = u := AddCircle.coe_equivIoc
    have hxs : x ∈ exposedEdge K' (s : ℝ) := by simpa [hsu] using hxu
    rcases le_or_gt (s : ℝ) a with hsa | has
    · left
      left
      left
      have hface := hleft (s : ℝ) ⟨hs.1, hsa⟩
      rw [hface] at hxs
      simpa [hP] using hxs
    · rcases lt_or_ge (s : ℝ) b with hsb | hbs
      · left
        left
        right
        refine Set.mem_iUnion_of_mem (s : ℝ) ?_
        refine Set.mem_iUnion_of_mem ⟨has, hsb⟩ ?_
        · rw [← hmiddle (s : ℝ) ⟨has, hsb⟩]
          exact hxs
      · rcases lt_or_eq_of_le hs.2 with hst | hst
        · left
          right
          have hface := hright (s : ℝ) ⟨hbs, hst⟩
          rw [hface] at hxs
          simpa [hQ] using hxs
        · right
          rw [hst] at hxs
          change x ∈ exposedEdge K'
            ((t : Real.Angle) + (Real.pi : Real.Angle)) at hxs
          rw [hterminal] at hxs
          simpa [segment_symm] using hxs
  · rintro x (hx | hx)
    · rcases hx with hx | hx
      · rcases hx with hx | hx
        · have hPa : P ∈ exposedEdge K' (a : ℝ) := by
            rw [hleft a ⟨by linarith [Real.pi_pos], le_rfl⟩]
            simp
          have hxP : x = P := by simpa [hP] using hx
          rw [hxP]
          exact exposedEdge_subset_frontier K'
            (a : Real.Angle) hPa
        · rcases Set.mem_iUnion.mp hx with ⟨s, hx⟩
          rcases Set.mem_iUnion.mp hx with ⟨hs, hx⟩
          rw [← hmiddle s hs] at hx
          exact exposedEdge_subset_frontier K' (s : Real.Angle) hx
      · have hQb : Q ∈ exposedEdge K' (b : ℝ) := by
          rw [hright b ⟨le_rfl, by linarith [Real.pi_pos]⟩]
          simp
        have hxQ : x = Q := by simpa [hQ] using hx
        rw [hxQ]
        exact exposedEdge_subset_frontier K'
          (b : Real.Angle) hQb
    · rw [segment_symm, ← hterminal] at hx
      exact exposedEdge_subset_frontier K'
        ((t + Real.pi : ℝ) : Real.Angle) hx

/-- A retained convex boundary arc meets its cutting chord only at the endpoints. -/
theorem convexBoundaryArc_inter_segment_eq_endpoints_of_cut
    (K K' : ConvexBody Point) (a b t c : ℝ) (P Q : Point)
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hPQ : P ≠ Q)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P})
    (hmiddle : ∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s)
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q})
    (hterminal : exposedEdge K' (t + Real.pi) = segment ℝ Q P)
    (hInt : (interior (K' : Set Point)).Nonempty) :
    convexBoundaryArc K a b ∩ segment ℝ P Q = {P, Q} := by
  have hPa : P ∈ exposedEdge K' (a : ℝ) := by
    rw [hleft a ⟨by linarith [Real.pi_pos], le_rfl⟩]
    simp
  have hQb : Q ∈ exposedEdge K' (b : ℝ) := by
    rw [hright b ⟨le_rfl, by linarith [Real.pi_pos]⟩]
    simp
  have hPterm : P ∈ exposedEdge K' (t + Real.pi) := by
    rw [hterminal]
    exact right_mem_segment ℝ Q P
  have hQterm : Q ∈ exposedEdge K' (t + Real.pi) := by
    rw [hterminal]
    exact left_mem_segment ℝ Q P
  apply Set.Subset.antisymm
  · rintro x ⟨hxarc, hxseg⟩
    rcases hxarc with hxarc | hxQ
    · rcases hxarc with hxP | hxmid
      · left
        simpa [hP] using hxP
      · rcases Set.mem_iUnion.mp hxmid with ⟨s, hxmid⟩
        rcases Set.mem_iUnion.mp hxmid with ⟨hs, hxsK⟩
        have hxs : x ∈ exposedEdge K' (s : ℝ) := by
          rw [hmiddle s hs]
          exact hxsK
        rw [segment_eq_image] at hxseg
        obtain ⟨r, hr, hxr⟩ := hxseg
        by_cases hr0 : r = 0
        · left
          subst r
          simpa using hxr.symm
        by_cases hr1 : r = 1
        · right
          subst r
          simpa using hxr.symm
        have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
        have hrlt : r < 1 := lt_of_le_of_ne hr.2 hr1
        have hPK : P ∈ K' := hPa.1
        have hQK : Q ∈ K' := hQb.1
        have hPLe := inner_le_supportValue K' hPK (s : Real.Angle)
        have hQLe := inner_le_supportValue K' hQK (s : Real.Angle)
        have hxEq := hxs.2
        change inner ℝ x (normalVector (s : Real.Angle)) =
          supportValue K' (s : Real.Angle) at hxEq
        rw [← hxr, inner_add_left, inner_smul_left, inner_smul_left] at hxEq
        simp only [map_sub, map_one, RCLike.conj_to_real] at hxEq
        have hPEq : inner ℝ P (normalVector (s : Real.Angle)) =
            supportValue K' (s : Real.Angle) := by
          nlinarith
        have hQEq : inner ℝ Q (normalVector (s : Real.Angle)) =
            supportValue K' (s : Real.Angle) := by
          nlinarith
        have hPs : P ∈ exposedEdge K' (s : ℝ) := ⟨hPK, hPEq⟩
        have hQs : Q ∈ exposedEdge K' (s : ℝ) := ⟨hQK, hQEq⟩
        have hos : inner ℝ (Q - P) (normalVector (s : Real.Angle)) = 0 := by
          rw [inner_sub_left, hPEq, hQEq]
          ring
        have hot : inner ℝ (Q - P) (normalVector (t + Real.pi : Real.Angle)) = 0 := by
          change inner ℝ (Q - P)
            (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = 0
          rw [normalVector_add_pi, inner_neg_right, inner_sub_left, hPt, hQt]
          ring
        have hQP : Q - P ≠ 0 := sub_ne_zero.mpr (Ne.symm hPQ)
        have hang : (s : Real.Angle) = ((t + Real.pi : ℝ) : Real.Angle) :=
          exteriorNormal_eq_of_orthogonal_of_interior_nonempty_cut K' hInt hQP
            (isExteriorNormal_of_mem_exposedEdge K' hPs)
            (isExteriorNormal_of_mem_exposedEdge K' hPterm) hos hot
        have hnv := congrArg normalVector hang
        have hcos : Real.cos (s - (t + Real.pi)) = 1 := by
          rw [← inner_normalVector_normalVector s (t + Real.pi), hnv,
            inner_normalVector_self]
        have htupper : t < a + Real.pi := lt_trans htb hba
        have hlower : -(2 * Real.pi) < s - (t + Real.pi) := by
          nlinarith [hs.1, htupper]
        have hupper : s - (t + Real.pi) < 2 * Real.pi := by
          nlinarith [hs.2, hat, Real.pi_pos]
        have := (Real.cos_eq_one_iff_of_lt_of_lt hlower hupper).mp hcos
        have hbtpi : b < t + Real.pi := by nlinarith [hba, hat]
        linarith [hs.2, hbtpi]
    · right
      simpa [hQ] using hxQ
  · intro x hx
    rcases hx with hx | hx
    · subst x
      constructor
      · left
        left
        simp [hP]
      · exact left_mem_segment ℝ P Q
    · subst x
      constructor
      · right
        simp [hQ]
      · exact right_mem_segment ℝ P Q

/-- A convex body admits a counterclockwise BV frontier parametrization based off a fixed face. -/
theorem exists_closedBVJordan_frontier_base_not_mem_chord
    (K : ConvexBody Point) (t : ℝ) (P Q : Point)
    (hInt : (interior (K : Set Point)).Nonempty)
    (hterminal : exposedEdge K (t + Real.pi) = segment ℝ Q P) :
    ∃ (a b : ℝ) (x : ContinuousBVPaths a b),
      ∃ hab : a < b, IsOrientedJordanParametrization hab.le (frontier (K : Set Point))
        true x.val ∧ x.val ⟨a, le_rfl, hab.le⟩ ∉ segment ℝ P Q := by
  obtain ⟨R, hRt⟩ := exposedEdge_nonempty K (t : Real.Angle)
  have hRnot : R ∉ segment ℝ P Q := by
    intro hRseg
    have hRopp : R ∈ exposedEdge K (t + Real.pi) := by
      rw [hterminal]
      simpa [segment_symm] using hRseg
    have hv : tangentVector (t : Real.Angle) ≠ 0 := by
      intro hzero
      have := inner_tangentVector_self t
      rw [hzero, inner_zero_left] at this
      norm_num at this
    have hot : inner ℝ (tangentVector (t : Real.Angle))
        (normalVector (t : Real.Angle)) = 0 := by
      rw [real_inner_comm]
      exact inner_normalVector_tangentVector t
    have hopp : inner ℝ (tangentVector (t : Real.Angle))
        (normalVector (t + Real.pi : Real.Angle)) = 0 := by
      change inner ℝ (tangentVector (t : Real.Angle))
        (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = 0
      rw [normalVector_add_pi, inner_neg_right, hot, neg_zero]
    have hang : (t : Real.Angle) = ((t + Real.pi : ℝ) : Real.Angle) :=
      exteriorNormal_eq_of_orthogonal_of_interior_nonempty_cut K hInt hv
        (isExteriorNormal_of_mem_exposedEdge K hRt)
        (isExteriorNormal_of_mem_exposedEdge K hRopp) hot hopp
    have hnv := congrArg normalVector hang
    change normalVector (t : Real.Angle) =
      normalVector (((t + Real.pi : ℝ) : Real.Angle)) at hnv
    rw [normalVector_add_pi] at hnv
    have hz : normalVector (t : Real.Angle) = 0 := by
      ext i
      have hi := congrFun (congrArg WithLp.ofLp hnv) i
      simp only [PiLp.neg_apply] at hi
      have : (normalVector (t : Real.Angle)) i = 0 := by linarith
      exact this
    have := norm_normalVector (t : Real.Angle)
    rw [hz, norm_zero] at this
    norm_num at this
  obtain ⟨o, ho⟩ := hInt
  obtain ⟨ρ, e, C, γ, hradial, he, hLip, hγ, hγJordan, hinterior⟩ :=
    convexBody_radial_boundary K o ho
  have hRrange : R ∈ Set.range γ.val := by
    rw [hγJordan.2.2.2.1]
    exact exposedEdge_subset_frontier K (t : Real.Angle) hRt
  obtain ⟨s, hstop, hsR⟩ := exists_param_lt_top_of_mem_range (by positivity) γ.val
    hγJordan.2.2.2.2.1 hRrange
  by_cases hs0 : (s : ℝ) = 0
  · refine ⟨0, 2 * Real.pi, γ, mul_pos (by norm_num) Real.pi_pos, hγJordan, ?_⟩
    have hs : s = ⟨0, le_rfl, (mul_pos (by norm_num) Real.pi_pos).le⟩ :=
      Subtype.ext hs0
    rw [← hsR, hs] at hRnot
    exact hRnot
  · have hspos : 0 < (s : ℝ) := lt_of_le_of_ne s.property.1 (Ne.symm hs0)
    obtain ⟨r, hrJordan, hr⟩ :=
      exists_oriented_cyclic_rotation_eq_concat (by positivity) γ hγJordan s hspos hstop
    refine ⟨0, 2, r, by norm_num, hrJordan, ?_⟩
    simpa [hr, Function.concatUnitIntervals, hsR] using hRnot

end MovingSofa

noncomputable section

namespace MovingSofa

/-- The nonterminal boundary of a convex cut body realizes the corresponding convex boundary arc. -/
theorem exists_rectifiableOrientedArc_convexBoundaryArc_of_cut
    (K K' : ConvexBody Point) (a b t c : ℝ) (P Q : Point)
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hPQ : P ≠ Q)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P})
    (hmiddle : ∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s)
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q})
    (hterminal : exposedEdge K' (t + Real.pi) = segment ℝ Q P)
    (hInt : (interior (K' : Set Point)).Nonempty) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = convexBoundaryArc K a b ∧
        A.val.startPoint = P ∧ A.val.endPoint = Q := by
  have hfrontier := frontier_eq_convexBoundaryArc_union_segment_of_cut
    K K' a b t P Q hat htb hba hP hQ hleft hmiddle hright hterminal hInt
  have hinter := convexBoundaryArc_inter_segment_eq_endpoints_of_cut
    K K' a b t c P Q hat htb hba hPQ hPt hQt hP hQ hleft hmiddle hright
      hterminal hInt
  obtain ⟨α, β, x, hαβ, hx, hbase⟩ :=
    exists_closedBVJordan_frontier_base_not_mem_chord K' t P Q hInt hterminal
  exact exists_rectifiableOrientedArc_of_closedJordan_cut hαβ hx P Q hPQ hbase
    hfrontier hinter

private theorem isExposed_exposedEdge_jordan (K : ConvexBody Point) (t : Real.Angle) :
    IsExposed ℝ (K : Set Point) (exposedEdge K t) := by
  intro _
  refine ⟨innerSL ℝ (normalVector t), ?_⟩
  ext p
  simp only [Set.mem_ofPred_eq, innerSL_apply_apply, real_inner_comm]
  constructor
  · intro hp
    refine ⟨hp.1, fun q hq ↦ ?_⟩
    rw [hp.2]
    exact inner_le_supportValue K hq t
  · rintro ⟨hp, hmax⟩
    refine ⟨hp, le_antisymm (inner_le_supportValue K hp t) ?_⟩
    apply csSup_le (K.nonempty.image _)
    rintro _ ⟨q, hq, rfl⟩
    exact hmax q hq

/-- A singleton exposed face of a segment is one of its endpoints. -/
theorem endpoint_of_exposedEdge_eq_singleton_of_eq_segment
    (K : ConvexBody Point) (x y P : Point) (s : Real.Angle)
    (hK : (K : Set Point) = segment ℝ x y)
    (hface : exposedEdge K s = {P}) : x = P ∨ y = P := by
  have hPextreme : P ∈ Set.extremePoints ℝ (K : Set Point) := by
    have hexposed : IsExposed ℝ (K : Set Point) {P} := by
      rw [← hface]
      exact isExposed_exposedEdge_jordan K s
    exact hexposed.isExtreme.mem_extremePoints
  rw [mem_extremePoints_iff_forall_segment] at hPextreme
  have hxK : x ∈ (K : Set Point) := by rw [hK]; exact left_mem_segment ℝ x y
  have hyK : y ∈ (K : Set Point) := by rw [hK]; exact right_mem_segment ℝ x y
  have hPseg : P ∈ segment ℝ x y := by rw [← hK]; exact hPextreme.1
  exact hPextreme.2 x hxK y hyK hPseg

/-- A cut body with empty interior has its selected boundary arc equal to the endpoint segment. -/
theorem convexBoundaryArc_eq_segment_of_cut_interior_empty
    (K K' : ConvexBody Point) (a b t c : ℝ) (P Q : Point)
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hPQ : P ≠ Q)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P})
    (hmiddle : ∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s)
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q})
    (hInt : interior (K' : Set Point) = ∅) :
    convexBoundaryArc K a b = segment ℝ P Q := by
  have hPmem : P ∈ (K' : Set Point) := by
    have ha : a ∈ Set.Ioc (t - Real.pi) a := ⟨by linarith, le_rfl⟩
    have : P ∈ exposedEdge K' (a : Real.Angle) := by rw [hleft a ha]; simp
    exact this.1
  have hQmem : Q ∈ (K' : Set Point) := by
    have hb : b ∈ Set.Ico b (t + Real.pi) := ⟨le_rfl, by linarith⟩
    have : Q ∈ exposedEdge K' (b : Real.Angle) := by rw [hright b hb]; simp
    exact this.1
  have hnsub : ¬(K' : Set Point).Subsingleton := by
    intro hs
    exact hPQ (hs hPmem hQmem)
  obtain ⟨x, y, hxy, hK'⟩ := K'.exists_eq_segment_of_interior_empty hnsub hInt
  have hxP : x = P ∨ y = P := endpoint_of_exposedEdge_eq_singleton_of_eq_segment
    K' x y P (a : Real.Angle) hK' (hleft a ⟨by linarith, le_rfl⟩)
  have hxQ : x = Q ∨ y = Q := endpoint_of_exposedEdge_eq_singleton_of_eq_segment
    K' x y Q (b : Real.Angle) hK' (hright b ⟨le_rfl, by linarith⟩)
  have hK'PQ : (K' : Set Point) = segment ℝ P Q := by
    rcases hxP with rfl | rfl <;> rcases hxQ with hxQ | hxQ
    · exact (hPQ hxQ).elim
    · simpa [hxQ] using hK'
    · simpa [hxQ, segment_symm ℝ] using hK'
    · exact (hPQ hxQ).elim
  have horth : inner ℝ (Q - P) (normalVector (t : Real.Angle)) = 0 := by
    rw [inner_sub_left, hQt, hPt, sub_self]
  let d : Point × Point × Real.Angle := (P, Q, (t : Real.Angle))
  have hd : IsSegmentPresentation K' d := ⟨hPQ, hK'PQ, horth⟩
  have hface : exposedEdge K (t : Real.Angle) = (K' : Set Point) := by
    rw [← hmiddle t ⟨hat, htb⟩]
    exact exposedEdge_eq_segment_of_orthogonal K' d hd (t : Real.Angle) horth
  apply Set.Subset.antisymm
  · rw [convexBoundaryArc]
    refine Set.union_subset (Set.union_subset (by
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      rw [hP]
      exact left_mem_segment ℝ _ _) ?_) (by
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      rw [hQ]
      exact right_mem_segment ℝ _ _)
    refine Set.iUnion₂_subset fun s hs z hz ↦ ?_
    rw [← hK'PQ]
    have hz' : z ∈ exposedEdge K' (s : Real.Angle) := by
      rw [hmiddle s hs]
      exact hz
    exact hz'.1
  · intro z hz
    have hzK' : z ∈ (K' : Set Point) := by rw [hK'PQ]; exact hz
    have hzface : z ∈ exposedEdge K (t : Real.Angle) := by rw [hface]; exact hzK'
    rw [convexBoundaryArc]
    apply Set.mem_union_left
    apply Set.mem_union_right
    apply Set.mem_iUnion.mpr
    refine ⟨t, Set.mem_iUnion.mpr ⟨⟨hat, htb⟩, hzface⟩⟩

end MovingSofa

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Arc Area
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- An oriented rectifiable arc agrees with the prescribed convex boundary arc and its
endpoints. -/
def RealizesConvexArc (K : ConvexBody Point) (a b : ℝ)
    (Γ : RectifiableOrientedArc) : Prop :=
  Γ.val.carrier = convexBoundaryArc K a b ∧
    Γ.val.startPoint = (edgeVertices K (a : Real.Angle)).1 ∧
    Γ.val.endPoint = (edgeVertices K (b : Real.Angle)).2

/-- The signed area of a realization of the convex boundary arc, or zero if none exists. -/
def convexArcArea (K : ConvexBody Point) (a b : ℝ) : ℝ := by
  classical
  exact if h : ∃ Γ, RealizesConvexArc K a b Γ then jordanArcArea h.choose else 0

/-- Every realization of a convex boundary arc computes that arc's signed area. -/
theorem convexArcArea_eq_jordanArcArea_of_realizes {K : ConvexBody Point} {a b : ℝ}
    {Γ : RectifiableOrientedArc} (hΓ : RealizesConvexArc K a b Γ) :
    convexArcArea K a b = jordanArcArea Γ := by
  rw [convexArcArea, dite_eq_left ⟨Γ, hΓ⟩]
  let Δ := Classical.choose (show ∃ Γ, RealizesConvexArc K a b Γ from ⟨Γ, hΓ⟩)
  have hΔ : RealizesConvexArc K a b Δ :=
    Classical.choose_spec (show ∃ Γ, RealizesConvexArc K a b Γ from ⟨Γ, hΓ⟩)
  change curveAreaFunctional (Classical.choice Δ.property).path =
    curveAreaFunctional (Classical.choice Γ.property).path
  exact (curveArea_reparametrization.2.1 Δ Γ
    (Classical.choice Δ.property) (Classical.choice Γ.property)
    (hΔ.1.trans hΓ.1.symm)).1
      (hΔ.2.1.trans hΓ.2.1.symm) (hΔ.2.2.trans hΓ.2.2.symm)

/-- Any bounded-variation parametrization of a convex boundary arc computes that arc's signed
area. -/
theorem convexArcArea_eq_curveAreaFunctional_of_realizes {K : ConvexBody Point} {a b : ℝ}
    {Γ : OrientedJordanArc} (p : ArcBVParametrization Γ)
    (hΓ : RealizesConvexArc K a b ⟨Γ, ⟨p⟩⟩) :
    convexArcArea K a b = curveAreaFunctional p.path := by
  rw [convexArcArea_eq_jordanArcArea_of_realizes hΓ]
  exact (curveArea_arc_same_carrier Γ Γ
    (Classical.choice (⟨Γ, ⟨p⟩⟩ : RectifiableOrientedArc).property) p rfl).1 rfl rfl

/-- A continuous bounded-variation path on `[a, b]` that traces a convex boundary arc
injectively, from the arc's first vertex to its last, computes that arc's signed area. -/
theorem convexArcArea_eq_curveAreaFunctional_of_injOn {K : ConvexBody Point} {α β a b : ℝ}
    {f : ℝ → Point} (x : ContinuousBVPaths a b) (hab : a < b)
    (hx : ∀ t : Set.Icc a b, x.val t = f t) (hinj : Set.InjOn f (Set.Icc a b))
    (himage : f '' Set.Icc a b = convexBoundaryArc K α β)
    (hstart : f a = (edgeVertices K (α : Real.Angle)).1)
    (hend : f b = (edgeVertices K (β : Real.Angle)).2) :
    convexArcArea K α β = curveAreaFunctional x := by
  have hxinj : Function.Injective x.val := fun s t hst ↦
    Subtype.ext (hinj s.2 t.2 (by rw [← hx s, ← hx t, hst]))
  have hrange : Set.range x.val = convexBoundaryArc K α β := by
    rw [← himage, Set.image_eq_range]
    exact congrArg Set.range (funext hx)
  have hstart' : x.val ⟨a, le_rfl, hab.le⟩ = (edgeVertices K (α : Real.Angle)).1 := by
    rw [hx, hstart]
  have hend' : x.val ⟨b, hab.le, le_rfl⟩ = (edgeVertices K (β : Real.Angle)).2 := by
    rw [hx, hend]
  let Γ : OrientedJordanArc :=
    { carrier := convexBoundaryArc K α β
      startPoint := (edgeVertices K (α : Real.Angle)).1
      endPoint := (edgeVertices K (β : Real.Angle)).2
      parametrizable :=
        ⟨a, b, hab.le, x.val, x.property.1, hxinj, hrange, hstart', hend'⟩ }
  exact convexArcArea_eq_curveAreaFunctional_of_realizes (Γ := Γ)
    ⟨a, b, hab.le, x, hxinj, hrange, hstart', hend'⟩ ⟨rfl, rfl, rfl⟩

private theorem exists_degenerate_convexArc (K : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (hba : b < a + Real.pi)
    (heq : (edgeVertices K (a : Real.Angle)).1 =
      (edgeVertices K (b : Real.Angle)).2) :
    ∃ Γ : RectifiableOrientedArc,
      RealizesConvexArc K a b Γ ∧ convexArcArea K a b = jordanArcArea Γ ∧
      (Γ.val.startPoint = Γ.val.endPoint → Γ.val.carrier = {Γ.val.startPoint}) := by
  let P := (edgeVertices K (a : Real.Angle)).1
  have hcut := (convexBoundaryArc_cut K a b hab hba P P (supportingIntersection K a b)
    rfl heq rfl).1 rfl
  obtain ⟨Γ, hcarrier, hstart, hend, _⟩ := (segmentArea_jordan_and_frame P P).1
  have hreal : RealizesConvexArc K a b Γ := by
    refine ⟨hcarrier.trans (segment_same ℝ P) |>.trans hcut.2.symm,
      hstart, hend.trans heq⟩
  exact ⟨Γ, hreal, convexArcArea_eq_jordanArcArea_of_realizes hreal, fun _ ↦ by
    rw [hcarrier, segment_same, hstart]⟩

private theorem surfaceAreaMeasure_openArc_eq_zero_of_convexBoundaryArc_eq_singleton
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    {P : Point} (hArc : convexBoundaryArc K a b = {P}) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) = 0 := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  have hmeas : MeasurableSet E := (Real.Angle.isOpen_image_Ioo a b).measurableSet
  have hsubset : E ⊆ (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc a b :=
    Set.image_mono Set.Ioo_subset_Icc_self
  rw [(surfaceAreaMeasure_face_union K).2.2.2.2 E hmeas
    (Or.inr ⟨a, b, hab.le, hba, hsubset⟩)]
  have hunion_sub : (⋃ t ∈ E, exposedEdge K t) ⊆ {P} := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨t, ht⟩ := hx
    obtain ⟨htE, hxt⟩ := ht
    obtain ⟨r, hr, rfl⟩ := htE
    have hxArc : x ∈ convexBoundaryArc K a b := by
      change x ∈ ({(edgeVertices K (a : Real.Angle)).1} ∪
        (⋃ t ∈ Set.Ioo a b, exposedEdge K (t : Real.Angle))) ∪
        {(edgeVertices K (b : Real.Angle)).2}
      apply Set.mem_union_left
      apply Set.mem_union_right
      exact Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨hr, hxt⟩⟩
    rw [hArc] at hxArc
    exact hxArc
  have hunion_nonempty : (⋃ t ∈ E, exposedEdge K t).Nonempty := by
    let r := (a + b) / 2
    have hr : r ∈ Set.Ioo a b := by dsimp [r]; constructor <;> linarith
    obtain ⟨x, hx⟩ := exposedEdge_nonempty K (r : Real.Angle)
    exact ⟨x, Set.mem_iUnion.2 ⟨(r : Real.Angle), Set.mem_iUnion.2
      ⟨⟨r, hr, rfl⟩, hx⟩⟩⟩
  have hunion : (⋃ t ∈ E, exposedEdge K t) = {P} :=
    Set.Nonempty.subset_singleton_iff hunion_nonempty |>.mp hunion_sub
  rw [hunion]
  let _ := MeasureTheory.Measure.nullSingletonClass_hausdorff Point
    (by norm_num : (0 : ℝ) < 1)
  exact measure_singleton P

private theorem convexArcArea_eq_integral_of_endpoints_eq (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (heq : (edgeVertices K (a : Real.Angle)).1 =
      (edgeVertices K (b : Real.Angle)).2) :
    convexArcArea K a b =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure K) / 2 := by
  let P := (edgeVertices K (a : Real.Angle)).1
  have hcut := (convexBoundaryArc_cut K a b hab hba P P (supportingIntersection K a b)
    rfl heq rfl).1 rfl
  obtain ⟨Γ, hcarrier, hstart, hend, hΓarea⟩ := (segmentArea_jordan_and_frame P P).1
  have hreal : RealizesConvexArc K a b Γ := by
    refine ⟨hcarrier.trans (segment_same ℝ P) |>.trans hcut.2.symm,
      hstart, hend.trans heq⟩
  rw [convexArcArea_eq_jordanArcArea_of_realizes hreal, hΓarea]
  have hμ := surfaceAreaMeasure_openArc_eq_zero_of_convexBoundaryArc_eq_singleton
    K hab hba hcut.2
  rw [MeasureTheory.setIntegral_measure_zero _ hμ]
  simp [segmentArea, planeCrossProduct]
  ring

private theorem exists_pos_smul_tangentVector_of_cut
    (K : ConvexBody Point) {a t : ℝ} (hat : a < t) (hta : t < a + Real.pi)
    {P Q : Point} (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQK : Q ∈ K) (hne : P ≠ Q)
    (hnormal : inner ℝ P (normalVector (t : Real.Angle)) =
      inner ℝ Q (normalVector (t : Real.Angle))) :
    ∃ d : ℝ, 0 < d ∧ Q - P = d • tangentVector (t : Real.Angle) := by
  let d := inner ℝ (Q - P) (tangentVector (t : Real.Angle))
  have hnormal0 : inner ℝ (Q - P) (normalVector (t : Real.Angle)) = 0 := by
    rw [inner_sub_left, hnormal, sub_self]
  have hdecomp : Q - P = d • tangentVector (t : Real.Angle) := by
    rw [← inner_normalVector_smul_add_inner_tangentVector_smul
      (Q - P) (t : Real.Angle), hnormal0, zero_smul, zero_add]
  have hPa : inner ℝ P (normalVector (a : Real.Angle)) = supportValue K a := by
    rw [hP]
    exact (edgeVertices_fst_mem K (a : Real.Angle)).2
  have hQa : inner ℝ Q (normalVector (a : Real.Angle)) ≤ supportValue K a :=
    inner_le_supportValue K hQK (a : Real.Angle)
  have hinner : inner ℝ (Q - P) (normalVector (a : Real.Angle)) ≤ 0 := by
    rw [inner_sub_left, hPa]
    linarith
  have hsin : 0 < Real.sin (t - a) := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hat) (by linarith)
  have htana : inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (a : Real.Angle)) = -Real.sin (t - a) := by
    rw [real_inner_comm]
    have h := sin_sub_eq_neg_inner_normalVector_tangentVector
      (a : Real.Angle) (t : Real.Angle)
    have h' : (((t - a : ℝ) : Real.Angle)).sin =
        -inner ℝ (normalVector (a : Real.Angle)) (tangentVector (t : Real.Angle)) := by
      simpa only [Real.Angle.coe_sub] using h
    rw [Real.Angle.sin_coe] at h'
    linarith
  have hdnonneg : 0 ≤ d := by
    rw [hdecomp, real_inner_smul_left, htana] at hinner
    nlinarith
  have hdne : d ≠ 0 := by
    intro hd
    apply hne
    have : Q - P = 0 := by rw [hdecomp, hd, zero_smul]
    exact (sub_eq_zero.mp this).symm
  exact ⟨d, lt_of_le_of_ne hdnonneg (Ne.symm hdne), hdecomp⟩

/-- The half support integral against a surface measure is convex-bilinear in the pair of
bodies, by convex-linearity of support functions and surface measures. -/
theorem convexArcIntegral_bilinear (a b : ℝ) :
    IsConvexBilinear convexBodyCombination convexBodyCombination realCombination
      (fun K L : ConvexBody Point ↦ (1 / 2 : ℝ) *
        ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
          supportValue K t ∂surfaceAreaMeasure L) := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  have hcont (K : ConvexBody Point) : Continuous (fun u : Real.Angle ↦ supportValue K u) :=
    (compactSet_support_continuity K K K.nonempty K.isCompact K.nonempty K.isCompact).2.2.1
  have hint (K L : ConvexBody Point) :
      Integrable (fun u : Real.Angle ↦ supportValue K u) (surfaceAreaMeasure L) := by
    let _ : IsFiniteMeasure (surfaceAreaMeasure L) := (surfaceAreaMeasure_face_union L).1
    exact (hcont K).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  constructor
  · intro K t L M
    have hmeasure := (convexBody_maps_linear t L M).2.2.2
    change (1 / 2 : ℝ) * (∫ u in E, supportValue K u ∂surfaceAreaMeasure
        (convexBodyCombination t L M)) = _
    simp only [realCombination]
    rw [hmeasure, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
      integral_add_measure ((hint K L).restrict.smul_measure _)
        ((hint K M).restrict.smul_measure _)]
    simp only [integral_smul_measure, ENNReal.toReal_ofReal,
      sub_nonneg.mpr (show (t : ℝ) ≤ 1 from t.property.2), t.property.1]
    ring
    all_goals exact ENNReal.ofReal_ne_top
  · intro L t K M
    change (1 / 2 : ℝ) * (∫ u in E, supportValue (convexBodyCombination t K M) u
      ∂surfaceAreaMeasure L) = _
    simp only [realCombination]
    have hfun : (fun u : Real.Angle ↦ supportValue (convexBodyCombination t K M) u) =
        fun u ↦ (1 - (t : ℝ)) * supportValue K u + (t : ℝ) * supportValue M u := by
      funext u
      exact (convexBody_maps_linear t K M).1 u
    rw [hfun, integral_add ((hint K L).restrict.const_mul _) ((hint M L).restrict.const_mul _),
      integral_const_mul, integral_const_mul]
    ring

private theorem convexArcArea_quadratic_of_integral_eq (a b : ℝ)
    (harea : ∀ K : ConvexBody Point, convexArcArea K a b =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure K) / 2) :
    IsQuadraticFunctional convexBodyCombination (fun K ↦ convexArcArea K a b) := by
  let B := fun K L : ConvexBody Point ↦ (1 / 2 : ℝ) *
    ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
      supportValue K t ∂surfaceAreaMeasure L
  refine ⟨B, convexArcIntegral_bilinear a b, ?_⟩
  intro K
  change convexArcArea K a b = B K K
  rw [harea K]
  simp only [B]
  ring

private theorem convexArc_area_of_realization_and_integral
    (a b : ℝ)
    (hgeom : ∀ K : ConvexBody Point,
      ∃ Γ : RectifiableOrientedArc,
        RealizesConvexArc K a b Γ ∧
        (Γ.val.startPoint = Γ.val.endPoint → Γ.val.carrier = {Γ.val.startPoint}))
    (harea : ∀ K : ConvexBody Point, convexArcArea K a b =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure K) / 2) :
    (∀ K : ConvexBody Point, ∃ Γ : RectifiableOrientedArc,
      RealizesConvexArc K a b Γ ∧ convexArcArea K a b = jordanArcArea Γ ∧
      (Γ.val.startPoint = Γ.val.endPoint → Γ.val.carrier = {Γ.val.startPoint})) ∧
    (∀ K : ConvexBody Point, convexArcArea K a b =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure K) / 2) ∧
    IsQuadraticFunctional convexBodyCombination (fun K ↦ convexArcArea K a b) := by
  refine ⟨?_, harea, convexArcArea_quadratic_of_integral_eq a b harea⟩
  intro K
  obtain ⟨Γ, hreal, hsingleton⟩ := hgeom K
  exact ⟨Γ, hreal, convexArcArea_eq_jordanArcArea_of_realizes hreal, hsingleton⟩

private theorem exists_convexArc_realization (a b : ℝ) (hab : a < b)
    (hba : b < a + Real.pi) (K : ConvexBody Point) :
    ∃ Γ : RectifiableOrientedArc,
      RealizesConvexArc K a b Γ ∧
      (Γ.val.startPoint = Γ.val.endPoint → Γ.val.carrier = {Γ.val.startPoint}) := by
  by_cases heq : (edgeVertices K (a : Real.Angle)).1 =
      (edgeVertices K (b : Real.Angle)).2
  · obtain ⟨Γ, hreal, -, hsingleton⟩ := exists_degenerate_convexArc K a b hab hba heq
    exact ⟨Γ, hreal, hsingleton⟩
  · let P := (edgeVertices K (a : Real.Angle)).1
    let Q := (edgeVertices K (b : Real.Angle)).2
    let O := supportingIntersection K a b
    obtain ⟨-, hcut⟩ := convexBoundaryArc_cut K a b hab hba P Q O rfl rfl rfl
    obtain ⟨hncol, t, c, K', hat, htb, hPt, hQt, hcO, hK', hleft, hmiddle,
      hright, hterminal⟩ := hcut heq
    by_cases hInt : (interior (K' : Set Point)).Nonempty
    · obtain ⟨Γ, hcarrier, hstart, hend⟩ :=
        exists_rectifiableOrientedArc_convexBoundaryArc_of_cut K K' a b t c P Q
          hat htb hba heq hPt hQt rfl rfl hleft hmiddle hright hterminal hInt
      have hreal : RealizesConvexArc K a b Γ := ⟨hcarrier, hstart, hend⟩
      refine ⟨Γ, hreal, ?_⟩
      intro hendpoints
      exact (heq (hstart.symm.trans (hendpoints.trans hend))) |>.elim
    · have hInt' : interior (K' : Set Point) = ∅ := Set.not_nonempty_iff_eq_empty.mp hInt
      have harc := convexBoundaryArc_eq_segment_of_cut_interior_empty K K' a b t c P Q
        hat htb hba heq hPt hQt rfl rfl hleft hmiddle hright hInt'
      obtain ⟨Γ, hcarrier, hstart, hend, -⟩ := (segmentArea_jordan_and_frame P Q).1
      have hreal : RealizesConvexArc K a b Γ :=
        ⟨hcarrier.trans harc.symm, hstart, hend⟩
      refine ⟨Γ, hreal, ?_⟩
      intro hendpoints
      exact (heq (hstart.symm.trans (hendpoints.trans hend))) |>.elim

private theorem surfaceAreaMeasure_restrict_openArc_eq_of_exposedEdge_eq
    (K L : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hfaces : ∀ s ∈ Set.Ioo a b,
      exposedEdge K (s : Real.Angle) = exposedEdge L (s : Real.Angle)) :
    (surfaceAreaMeasure K).restrict
        ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) =
      (surfaceAreaMeasure L).restrict
        ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  have hE : MeasurableSet E := Real.Angle.isOpen_image_Ioo a b |>.measurableSet
  apply Measure.ext
  intro S hS
  rw [Measure.restrict_apply hS, Measure.restrict_apply hS]
  have hSE : MeasurableSet (S ∩ E) := hS.inter hE
  have hdomain : S ∩ E ⊆ (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc a b :=
    Set.inter_subset_right.trans (Set.image_mono Set.Ioo_subset_Icc_self)
  rw [(surfaceAreaMeasure_face_union K).2.2.2.2 (S ∩ E) hSE
      (Or.inr ⟨a, b, hab.le, hba, hdomain⟩),
    (surfaceAreaMeasure_face_union L).2.2.2.2 (S ∩ E) hSE
      (Or.inr ⟨a, b, hab.le, hba, hdomain⟩)]
  congr 2
  ext p
  simp only [Set.mem_iUnion, Set.mem_inter_iff, E]
  constructor
  · rintro ⟨⟨hpS, s, hs, hsp⟩, hx⟩
    subst p
    exact ⟨⟨hpS, ⟨s, hs, rfl⟩⟩, hfaces s hs ▸ hx⟩
  · rintro ⟨⟨hpS, s, hs, hsp⟩, hx⟩
    subst p
    exact ⟨⟨hpS, ⟨s, hs, rfl⟩⟩, hfaces s hs |>.symm ▸ hx⟩

private theorem surfaceAreaMeasure_compl_openArc_union_terminal_eq_zero_of_cut
    (K : ConvexBody Point) {a b t : ℝ} {P Q : Point}
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K s = {P})
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K s = {Q})
    (hInt : (interior (K : Set Point)).Nonempty) :
    surfaceAreaMeasure K
      (((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b ∪
        {((t + Real.pi : ℝ) : Real.Angle)})ᶜ) = 0 := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  let θ : Real.Angle := (t + Real.pi : ℝ)
  let D := (E ∪ {θ})ᶜ
  have hD : MeasurableSet D :=
    ((Real.Angle.isOpen_image_Ioo a b).measurableSet.union
      (measurableSet_singleton θ)).compl
  have hface := (surfaceAreaMeasure_face_union K).2.2.2.2 D hD (Or.inl hInt)
  have hunion : (⋃ u ∈ D, exposedEdge K u) ⊆ {P, Q} := by
    intro x hx
    obtain ⟨u, huD, hxu⟩ := Set.mem_iUnion₂.mp hx
    let _ : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
    let s := AddCircle.equivIoc (2 * Real.pi) (t - Real.pi) u
    have hs : (s : ℝ) ∈ Set.Ioc (t - Real.pi) (t + Real.pi) := by
      have hs' := s.property
      convert hs' using 1
      ring_nf
    have hsu : (((s : ℝ) : Real.Angle)) = u := AddCircle.coe_equivIoc
    have hxs : x ∈ exposedEdge K (s : ℝ) := by simpa [hsu] using hxu
    rcases le_or_gt (s : ℝ) a with hsa | has
    · rw [hleft (s : ℝ) ⟨hs.1, hsa⟩] at hxs
      exact Or.inl (by simpa using hxs)
    · rcases lt_or_ge (s : ℝ) b with hsb | hbs
      · exfalso
        apply huD
        apply Set.mem_union_left
        exact ⟨s, ⟨has, hsb⟩, hsu⟩
      · rcases lt_or_eq_of_le hs.2 with hst | hst
        · rw [hright (s : ℝ) ⟨hbs, hst⟩] at hxs
          exact Or.inr (by simpa using hxs)
        · exfalso
          apply huD
          apply Set.mem_union_right
          simp only [Set.mem_singleton_iff, θ]
          rw [← hsu, hst]
  rw [show (((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b ∪
      {((t + Real.pi : ℝ) : Real.Angle)})ᶜ) = D by rfl, hface]
  let _ := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  exact measure_mono_null hunion
    ((Set.toFinite {P, Q}).measure_zero (Measure.hausdorffMeasure 1))

private theorem integral_eq_openArc_add_terminal_of_cut
    (K : ConvexBody Point) {a b t : ℝ} {P Q : Point}
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K s = {P})
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K s = {Q})
    (hInt : (interior (K : Set Point)).Nonempty) :
    (∫ u, supportValue K u ∂surfaceAreaMeasure K) =
      (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K u ∂surfaceAreaMeasure K) +
      (surfaceAreaMeasure K).real {((t + Real.pi : ℝ) : Real.Angle)} *
        supportValue K ((t + Real.pi : ℝ) : Real.Angle) := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  let θ : Real.Angle := (t + Real.pi : ℝ)
  let C := E ∪ {θ}
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hcont : Continuous (fun u : Real.Angle ↦ supportValue K u) :=
    (compactSet_support_continuity K K K.nonempty K.isCompact K.nonempty K.isCompact).2.2.1
  have hint : Integrable (fun u : Real.Angle ↦ supportValue K u) (surfaceAreaMeasure K) :=
    hcont.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  have hC : MeasurableSet C :=
    (Real.Angle.isOpen_image_Ioo a b).measurableSet.union (measurableSet_singleton θ)
  have hzero : surfaceAreaMeasure K Cᶜ = 0 := by
    exact surfaceAreaMeasure_compl_openArc_union_terminal_eq_zero_of_cut
      K hleft hright hInt
  have hdisj : Disjoint E {θ} := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨s, hs, heq⟩
    have hlow : t - Real.pi < a := by linarith
    have hupp : b < t + Real.pi := by linarith
    have hsrange : s ∈ Set.Ioc (t - Real.pi) (t + Real.pi) :=
      ⟨hlow.trans hs.1, (hs.2.trans hupp).le⟩
    have htrange : t + Real.pi ∈ Set.Ioc (t - Real.pi) (t + Real.pi) :=
      ⟨by linarith [Real.pi_pos], le_rfl⟩
    have hinj := Real.Angle.injOn_coe_Ioc (by linarith [Real.pi_pos]) hsrange htrange heq
    rw [hinj] at hs
    exact (not_lt_of_ge hupp.le hs.2)
  have hsplit := MeasureTheory.setIntegral_union hdisj (measurableSet_singleton θ)
    hint.integrableOn hint.integrableOn
  have hall := MeasureTheory.integral_add_compl hC hint
  rw [MeasureTheory.setIntegral_measure_zero _ hzero, add_zero] at hall
  rw [← hall, hsplit, MeasureTheory.integral_singleton]
  rfl

private theorem terminal_surface_term_eq_segmentArea_of_cut
    (K : ConvexBody Point) {t c d : ℝ} {P Q : Point}
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hterminal : exposedEdge K (t + Real.pi) = segment ℝ Q P)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle)) :
    (surfaceAreaMeasure K).real {((t + Real.pi : ℝ) : Real.Angle)} *
        supportValue K ((t + Real.pi : ℝ) : Real.Angle) / 2 =
      segmentArea Q P := by
  let θ : Real.Angle := (t + Real.pi : ℝ)
  have hterminal' : exposedEdge K θ = segment ℝ Q P := by
    simpa only [θ, Real.Angle.coe_add] using hterminal
  have hmass : (surfaceAreaMeasure K).real {θ} = d := by
    have htangent_norm : ‖tangentVector (t : Real.Angle)‖ = 1 := by
      have hsq : ‖tangentVector (t : Real.Angle)‖ ^ 2 = 1 := by
        rw [← real_inner_self_eq_norm_sq, inner_tangentVector_self]
      nlinarith [norm_nonneg (tangentVector (t : Real.Angle))]
    rw [Measure.real, (surfaceAreaMeasure_atom_length K θ).1, hterminal',
      MeasureTheory.hausdorffMeasure_segment, edist_dist]
    simp only [dist_eq_norm, sub_eq_add_neg]
    rw [show Q + -P = Q - P by rfl, hdir, norm_smul, htangent_norm,
      mul_one, Real.norm_eq_abs, abs_of_pos hd]
    exact ENNReal.toReal_ofReal hd.le
  have hsupp : supportValue K θ = -c := by
    have hPterm : P ∈ exposedEdge K θ := by
      rw [hterminal']
      exact right_mem_segment ℝ Q P
    have h := hPterm.2
    change inner ℝ P (normalVector θ) = supportValue K θ at h
    change inner ℝ P (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = _ at h
    rw [normalVector_add_pi, inner_neg_right, hPt] at h
    linarith
  have hQline : Q ∈ normalLine θ (-c) := by
    change inner ℝ Q (normalVector θ) = -c
    change inner ℝ Q (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = -c
    rw [normalVector_add_pi, inner_neg_right, hQt]
  have hPline : P ∈ normalLine θ (-c) := by
    change inner ℝ P (normalVector θ) = -c
    change inner ℝ P (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = -c
    rw [normalVector_add_pi, inner_neg_right, hPt]
  have hdir' : P - Q = d • tangentVector θ := by
    have htangent : tangentVector θ = -tangentVector (t : Real.Angle) := by
      ext i
      fin_cases i <;> simp [θ, tangentVector, frame]
    calc
      P - Q = -(Q - P) := by module
      _ = -(d • tangentVector (t : Real.Angle)) := congrArg Neg.neg hdir
      _ = d • tangentVector θ := by rw [htangent]; module
  rw [hmass, hsupp]
  rw [mul_comm]
  exact ((segmentArea_jordan_and_frame Q P).2 θ (-c) d hQline hPline hdir').symm

private theorem supportValue_eq_of_exposedEdge_eq (K L : ConvexBody Point)
    (t : Real.Angle) (hface : exposedEdge K t = exposedEdge L t) :
    supportValue K t = supportValue L t := by
  obtain ⟨p, hp⟩ := exposedEdge_nonempty K t
  have hp' : p ∈ exposedEdge L t := hface ▸ hp
  exact hp.2.symm.trans hp'.2

private theorem integral_openArc_eq_of_exposedEdge_eq
    (K L : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hfaces : ∀ s ∈ Set.Ioo a b,
      exposedEdge K (s : Real.Angle) = exposedEdge L (s : Real.Angle)) :
    (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure K) =
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue L t ∂surfaceAreaMeasure L := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  have hμ := surfaceAreaMeasure_restrict_openArc_eq_of_exposedEdge_eq
    K L hab hba hfaces
  change (∫ t, supportValue K t ∂(surfaceAreaMeasure K).restrict E) =
    ∫ t, supportValue L t ∂(surfaceAreaMeasure L).restrict E
  rw [hμ]
  apply MeasureTheory.integral_congr_ae
  have hE : MeasurableSet E := Real.Angle.isOpen_image_Ioo a b |>.measurableSet
  filter_upwards [ae_restrict_mem hE] with t ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact supportValue_eq_of_exposedEdge_eq K L _ (hfaces s hs)

private theorem jordanArcArea_eq_integral_of_cut_interior_nonempty
    (K : ConvexBody Point) {a b t c d α β : ℝ} {P Q : Point}
    {x : ContinuousBVPaths α β} {A : RectifiableOrientedArc}
    (hαβ : α < β)
    (hx : IsOrientedJordanParametrization hαβ.le (frontier (K : Set Point)) true x.val)
    (hAarea : curveAreaFunctional x = jordanArcArea A + segmentArea Q P)
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K s = {P})
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K s = {Q})
    (hterminal : exposedEdge K (t + Real.pi) = segment ℝ Q P)
    (hInt : (interior (K : Set Point)).Nonempty)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle)) :
    jordanArcArea A =
      (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K u ∂surfaceAreaMeasure K) / 2 := by
  have hxarea := curveArea_eq_jordanInterior_area α β hαβ.le
    (frontier (K : Set Point)) x hx
  rw [jordanInterior_frontier_eq_interior K.convex K.isCompact.isClosed
    K.isCompact.isBounded K.nonempty] at hxarea
  have hinterarea : ClassicalResults.area (interior (K : Set Point)) =
      ClassicalResults.area (K : Set Point) := by
    simp only [ClassicalResults.area]
    rw [measure_interior_of_null_frontier (K.convex.addHaar_frontier volume)]
  rw [hinterarea, (convexBody_area_support_integral.1 K)] at hxarea
  have hsplit := integral_eq_openArc_add_terminal_of_cut K hat htb hba hleft hright hInt
  have hterminalArea := terminal_surface_term_eq_segmentArea_of_cut K hPt hQt hterminal
    hd hdir
  rw [hAarea, hsplit] at hxarea
  linarith

private theorem convexArcArea_eq_integral_of_cut_interior_nonempty
    (K K' : ConvexBody Point) {a b t c d α β : ℝ} {P Q : Point}
    {x : ContinuousBVPaths α β} {A : RectifiableOrientedArc}
    (hαβ : α < β)
    (hx : IsOrientedJordanParametrization hαβ.le (frontier (K' : Set Point)) true x.val)
    (hAcarrier : A.val.carrier = convexBoundaryArc K a b)
    (hAstart : A.val.startPoint = P) (hAend : A.val.endPoint = Q)
    (hAarea : curveAreaFunctional x = jordanArcArea A + segmentArea Q P)
    (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hmiddle : ∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P})
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q})
    (hterminal : exposedEdge K' (t + Real.pi) = segment ℝ Q P)
    (hInt : (interior (K' : Set Point)).Nonempty)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle)) :
    convexArcArea K a b =
      (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K u ∂surfaceAreaMeasure K) / 2 := by
  have hreal : RealizesConvexArc K a b A := ⟨hAcarrier, hAstart.trans hP, hAend.trans hQ⟩
  rw [convexArcArea_eq_jordanArcArea_of_realizes hreal]
  rw [jordanArcArea_eq_integral_of_cut_interior_nonempty K' hαβ hx hAarea
    hat htb hba hPt hQt hleft hright hterminal hInt hd hdir]
  exact congrArg (fun z : ℝ ↦ z / 2)
    (integral_openArc_eq_of_exposedEdge_eq K' K (hat.trans htb) hba hmiddle)

private theorem integral_openArc_eq_segmentArea_of_segment
    (K : ConvexBody Point) {a b t c d : ℝ} {P Q : Point}
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hK : (K : Set Point) = segment ℝ P Q) (hPQ : P ≠ Q)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle)) :
    (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
      supportValue K u ∂surfaceAreaMeasure K) / 2 = segmentArea P Q := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  let θ : Real.Angle := (t : ℝ)
  have horth : inner ℝ (Q - P) (normalVector θ) = 0 := by
    change inner ℝ (Q - P) (normalVector (t : Real.Angle)) = 0
    rw [inner_sub_left, hQt, hPt, sub_self]
  have hpres : IsSegmentPresentation K (P, Q, θ) := ⟨hPQ, hK, horth⟩
  have htangent_norm : ‖tangentVector (t : Real.Angle)‖ = 1 := by
    have hsq : ‖tangentVector (t : Real.Angle)‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, inner_tangentVector_self]
    nlinarith [norm_nonneg (tangentVector (t : Real.Angle))]
  have hdist : dist P Q = d := by
    rw [dist_eq_norm, show P - Q = -(Q - P) by module, norm_neg, hdir,
      norm_smul, htangent_norm, mul_one, Real.norm_eq_abs, abs_of_pos hd]
  have hE : MeasurableSet E := Real.Angle.isOpen_image_Ioo a b |>.measurableSet
  have htE : θ ∈ E := ⟨t, ⟨hat, htb⟩, rfl⟩
  have hopp : θ + (Real.pi : Real.Angle) ∉ E := by
    rintro ⟨s, hs, heq⟩
    have hsupper : s ≤ a + 2 * Real.pi := by
      have : s < a + Real.pi := hs.2.trans hba
      linarith [Real.pi_pos]
    have htupper : t + Real.pi ≤ a + 2 * Real.pi := by
      linarith [htb, hba, Real.pi_pos]
    have hsrange : s ∈ Set.Ioc a (a + 2 * Real.pi) := ⟨hs.1, hsupper⟩
    have htrange : t + Real.pi ∈ Set.Ioc a (a + 2 * Real.pi) :=
      ⟨by linarith [hat, Real.pi_pos], htupper⟩
    have hinj := Real.Angle.injOn_coe_Ioc (by linarith [Real.pi_pos])
      hsrange htrange
    have hst : s = t + Real.pi := hinj (by
      change (s : Real.Angle) = ((t + Real.pi : ℝ) : Real.Angle)
      simpa only [θ, Real.Angle.coe_add] using heq)
    linarith [hs.2, hba]
  have hmeasure : (surfaceAreaMeasure K).restrict E =
      ENNReal.ofReal d • Measure.dirac θ := by
    classical
    rw [surfaceAreaMeasure_eq_segmentPresentation K (P, Q, θ) hpres, hdist,
      Measure.restrict_smul, Measure.restrict_add]
    simp [restrict_dirac, htE, hopp]
  change (∫ u, supportValue K u ∂(surfaceAreaMeasure K).restrict E) / 2 = _
  rw [hmeasure, MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac,
    ENNReal.toReal_ofReal hd.le]
  have hPline : P ∈ normalLine θ c := hPt
  have hQline : Q ∈ normalLine θ c := hQt
  have hsupp : supportValue K θ = c := by
    have hpK : P ∈ K := by
      change P ∈ (K : Set Point)
      rw [hK]
      exact left_mem_segment ℝ P Q
    have hp : P ∈ exposedEdge K θ := by
      rw [exposedEdge_eq_segment_of_orthogonal K (P, Q, θ) hpres θ horth]
      exact hpK
    have hpEq := hp.2
    change inner ℝ P (normalVector θ) = supportValue K θ at hpEq
    exact hpEq.symm.trans hPt
  rw [hsupp]
  simp only [smul_eq_mul]
  convert ((segmentArea_jordan_and_frame P Q).2 θ c d hPline hQline hdir).symm using 1
  ring

private theorem convexArcArea_eq_integral_of_cut_interior_empty
    (K K' : ConvexBody Point) {a b t c d : ℝ} {P Q : Point}
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hPQ : P ≠ Q)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P})
    (hmiddle : ∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s)
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q})
    (hInt : interior (K' : Set Point) = ∅)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle)) :
    convexArcArea K a b =
      (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K u ∂surfaceAreaMeasure K) / 2 := by
  have hPmem : P ∈ (K' : Set Point) := by
    have : P ∈ exposedEdge K' (a : Real.Angle) := by
      rw [hleft a ⟨by linarith [Real.pi_pos], le_rfl⟩]
      simp
    exact this.1
  have hQmem : Q ∈ (K' : Set Point) := by
    have : Q ∈ exposedEdge K' (b : Real.Angle) := by
      rw [hright b ⟨le_rfl, by linarith [Real.pi_pos]⟩]
      simp
    exact this.1
  have hnsub : ¬(K' : Set Point).Subsingleton := by
    intro hs
    exact hPQ (hs hPmem hQmem)
  obtain ⟨x, y, hxy, hK'⟩ := K'.exists_eq_segment_of_interior_empty hnsub hInt
  have hxP : x = P ∨ y = P := endpoint_of_exposedEdge_eq_singleton_of_eq_segment
    K' x y P (a : Real.Angle) hK' (hleft a ⟨by linarith [Real.pi_pos], le_rfl⟩)
  have hxQ : x = Q ∨ y = Q := endpoint_of_exposedEdge_eq_singleton_of_eq_segment
    K' x y Q (b : Real.Angle) hK' (hright b ⟨le_rfl, by linarith [Real.pi_pos]⟩)
  have hK'PQ : (K' : Set Point) = segment ℝ P Q := by
    rcases hxP with rfl | rfl <;> rcases hxQ with hxQ | hxQ
    · exact (hPQ hxQ).elim
    · simpa [hxQ] using hK'
    · simpa [hxQ, segment_symm ℝ] using hK'
    · exact (hPQ hxQ).elim
  have harc := convexBoundaryArc_eq_segment_of_cut_interior_empty K K' a b t c P Q
    hat htb hba hPQ hPt hQt hP hQ hleft hmiddle hright hInt
  obtain ⟨A, hAcarrier, hAstart, hAend, hAarea⟩ :=
    (segmentArea_jordan_and_frame P Q).1
  have hreal : RealizesConvexArc K a b A :=
    ⟨hAcarrier.trans harc.symm, hAstart.trans hP, hAend.trans hQ⟩
  rw [convexArcArea_eq_jordanArcArea_of_realizes hreal]
  rw [hAarea]
  rw [← integral_openArc_eq_segmentArea_of_segment K' hat htb hba hK'PQ hPQ
    hPt hQt hd hdir]
  exact congrArg (fun z : ℝ ↦ z / 2)
    (integral_openArc_eq_of_exposedEdge_eq K' K (hat.trans htb) hba hmiddle)

private theorem convexArcArea_eq_integral_of_endpoints_ne
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    convexArcArea K a b =
      (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K u ∂surfaceAreaMeasure K) / 2 := by
  let P := (edgeVertices K (a : Real.Angle)).1
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K a b
  obtain ⟨-, hcut⟩ := convexBoundaryArc_cut K a b hab hba P Q O rfl rfl rfl
  obtain ⟨hncol, t, c, K', hat, htb, hPt, hQt, hcO, hK', hleft, hmiddle,
    hright, hterminal⟩ := hcut hne
  have hnormal : inner ℝ P (normalVector (t : Real.Angle)) =
      inner ℝ Q (normalVector (t : Real.Angle)) := hPt.trans hQt.symm
  obtain ⟨d, hd, hdir⟩ := exists_pos_smul_tangentVector_of_cut K hat
    (htb.trans hba) rfl (edgeVertices_snd_mem K (b : Real.Angle)).1 hne hnormal
  by_cases hInt : (interior (K' : Set Point)).Nonempty
  · have hfrontier := frontier_eq_convexBoundaryArc_union_segment_of_cut
      K K' a b t P Q hat htb hba rfl rfl hleft hmiddle hright hterminal hInt
    have hinter := convexBoundaryArc_inter_segment_eq_endpoints_of_cut
      K K' a b t c P Q hat htb hba hne hPt hQt rfl rfl hleft hmiddle hright
        hterminal hInt
    obtain ⟨α, β, x, hαβ, hx, hbase⟩ :=
      exists_closedBVJordan_frontier_base_not_mem_chord K' t P Q hInt hterminal
    obtain ⟨A, hAcarrier, hAstart, hAend, hAarea⟩ :=
      exists_rectifiableOrientedArc_of_cut_with_area K' hαβ hx hne hbase
        hfrontier hinter hPt hQt hterminal hd hdir
    exact convexArcArea_eq_integral_of_cut_interior_nonempty K K' hαβ hx
      hAcarrier hAstart hAend hAarea rfl rfl hat htb hba hPt hQt hmiddle hleft hright
        hterminal hInt hd hdir
  · exact convexArcArea_eq_integral_of_cut_interior_empty K K' hat htb hba hne
      hPt hQt rfl rfl hleft hmiddle hright (Set.not_nonempty_iff_eq_empty.mp hInt)
      hd hdir

theorem convexArc_area (a b : ℝ) (hab : a < b) (hba : b < a + Real.pi) :
    (∀ K : ConvexBody Point, ∃ Γ : RectifiableOrientedArc,
      RealizesConvexArc K a b Γ ∧ convexArcArea K a b = jordanArcArea Γ ∧
      (Γ.val.startPoint = Γ.val.endPoint → Γ.val.carrier = {Γ.val.startPoint})) ∧
    (∀ K : ConvexBody Point, convexArcArea K a b =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure K) / 2) ∧
    IsQuadraticFunctional convexBodyCombination (fun K ↦ convexArcArea K a b) := by
  apply convexArc_area_of_realization_and_integral a b
    (exists_convexArc_realization a b hab hba)
  intro K
  by_cases heq : (edgeVertices K (a : Real.Angle)).1 =
      (edgeVertices K (b : Real.Angle)).2
  · exact convexArcArea_eq_integral_of_endpoints_eq K hab hba heq
  · exact convexArcArea_eq_integral_of_endpoints_ne K hab hba heq

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Arc Bilinear
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace MovingSofa

/-- Half the coordinate cross Stieltjes integral over the open parameter interval. -/
def openIntervalCrossIntegral {a b : ℝ} (f : Fin 2 → RightContinuousIntervalBV a b)
    (g : Set.Icc a b → Point) : ℝ :=
  (intervalStieltjesIntegral (f 1) (fun t ↦ g t 0) {t | a < (t : ℝ) ∧ (t : ℝ) < b} -
    intervalStieltjesIntegral (f 0) (fun t ↦ g t 1) {t | a < (t : ℝ) ∧ (t : ℝ) < b}) / 2

/-- The half-support integral is the vertex cross Stieltjes integral, for any bounded
measurable selection from the first body's exposed edges. -/
private theorem halfSupportIntegral_eq_openIntervalCrossIntegral
    (K L : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (F : Fin 2 → RightContinuousIntervalBV a b)
    (hF : ∀ (i : Fin 2) (E : Set (Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (F i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure L)
    (W : Real.Angle → Point) (C : ℝ)
    (hWm : ∀ i : Fin 2, Measurable fun t : Ioc a b ↦ W (((t : ℝ) : Real.Angle)) i)
    (hWb : ∀ (u : Real.Angle) (i : Fin 2), ‖W u i‖ ≤ C)
    (hWsupp : ∀ u : Real.Angle, planeCrossProduct (W u) (tangentVector u) = supportValue K u) :
    ((1 / 2 : ℝ) * ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
      supportValue K t ∂surfaceAreaMeasure L) =
      openIntervalCrossIntegral F (fun t ↦ W (((t : ℝ) : Real.Angle))) := by
  have hWcoord : ∀ u : Real.Angle,
      W u 0 * tangentVector u 1 - W u 1 * tangentVector u 0 = supportValue K u := hWsupp
  have hE : MeasurableSet {t : Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} :=
    measurableSet_Ioo.preimage measurable_subtype_coe
  have hEa : ∀ t ∈ {t : Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b}, a < (t : ℝ) :=
    fun _ ht ↦ ht.1
  have himg : (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) ''
      {t : Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} =
      (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(t : ℝ), ht, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs.1.le, hs.2.le⟩, hs, rfl⟩
  have hsub : (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) ''
      {t : Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} ⊆
      Set.range fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle) := by
    rintro u ⟨t, ht, rfl⟩
    exact ⟨⟨(t : ℝ), ht.1, ht.2.le⟩, rfl⟩
  have hSmeas : MeasurableSet ((fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) ''
      {t : Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b}) := by
    rw [himg]
    exact (Real.Angle.isOpen_image_Ioo a b).measurableSet
  have h1 := intervalStieltjesIntegral_positiveVertex_coordinate_of_measurable L hab hturn F hF
    1 (fun u ↦ W u 0) C (hWm 0) (fun u ↦ hWb u 0) _ hE hEa
  have h0 := intervalStieltjesIntegral_positiveVertex_coordinate_of_measurable L hab hturn F hF
    0 (fun u ↦ W u 1) C (hWm 1) (fun u ↦ hWb u 1) _ hE hEa
  have hi1 := integrableOn_mul_tangentVector_of_bounded L hturn 1 (fun u ↦ W u 0) C (hWm 0)
    (fun u ↦ hWb u 0) _ hSmeas hsub
  have hi0 := integrableOn_mul_tangentVector_of_bounded L hturn 0 (fun u ↦ W u 1) C (hWm 1)
    (fun u ↦ hWb u 1) _ hSmeas hsub
  rw [openIntervalCrossIntegral, h1, h0, ← integral_sub hi1 hi0,
    setIntegral_congr_fun hSmeas (fun u _ ↦ hWcoord u), himg]
  ring

theorem convexArc_bilinear_computation (a b : ℝ) (hab : a < b) (hba : b < a + Real.pi) :
    IsConvexBilinear convexBodyCombination convexBodyCombination realCombination
      (fun K L : ConvexBody Point ↦ (1 / 2 : ℝ) *
        ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
          supportValue K t ∂surfaceAreaMeasure L) ∧
    ∃ F : ConvexBody Point → Fin 2 → RightContinuousIntervalBV a b,
      (∀ K i t, (F K i).toFun t = (edgeVertices K ((t : ℝ) : Real.Angle)).1 i) ∧
      (∀ K L : ConvexBody Point,
        ((1 / 2 : ℝ) * ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
          supportValue K t ∂surfaceAreaMeasure L) =
          openIntervalCrossIntegral (F L) (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1) ∧
        ((1 / 2 : ℝ) * ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
          supportValue K t ∂surfaceAreaMeasure L) =
          openIntervalCrossIntegral (F L) (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).2)) ∧
      (∀ K : ConvexBody Point, convexArcArea K a b =
        openIntervalCrossIntegral (F K) (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1)) := by
  have hturn : b ≤ a + 2 * Real.pi := by linarith [Real.pi_pos]
  refine ⟨convexArcIntegral_bilinear a b, ?_⟩
  choose F hFtoFun hFmeasure using fun L : ConvexBody Point ↦
    positiveVertex_stieltjes_surface L a b hab hturn
  have hcross1 (K L : ConvexBody Point) :
      ((1 / 2 : ℝ) * ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure L) =
        openIntervalCrossIntegral (F L)
          (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1) := by
    obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall (0 : Point)
    refine halfSupportIntegral_eq_openIntervalCrossIntegral K L hab hturn (F L) (hFmeasure L)
      (fun u ↦ (edgeVertices K u).1) R
      (fun i ↦ measurable_positiveVertex_coordinate_Ioc K hab.le i)
      (fun u i ↦ ?_) (fun u ↦ ?_)
    · have hmem := hR (edgeVertices_fst_mem K u).1
      rw [Metric.mem_closedBall, dist_zero_right] at hmem
      exact le_trans (by simpa [Real.norm_eq_abs] using Point.abs_apply_le_norm _ i) hmem
    · rw [planeCrossProduct_tangentVector, (edgeVertices_fst_mem K u).2]
  have hcross2 (K L : ConvexBody Point) :
      ((1 / 2 : ℝ) * ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure L) =
        openIntervalCrossIntegral (F L)
          (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).2) := by
    obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall (0 : Point)
    refine halfSupportIntegral_eq_openIntervalCrossIntegral K L hab hturn (F L) (hFmeasure L)
      (fun u ↦ (edgeVertices K u).2) R
      (fun i ↦ measurable_negativeVertex_coordinate K hab.le i) (fun u i ↦ ?_) (fun u ↦ ?_)
    · have hmem := hR (edgeVertices_snd_mem K u).1
      rw [Metric.mem_closedBall, dist_zero_right] at hmem
      exact le_trans (by simpa [Real.norm_eq_abs] using Point.abs_apply_le_norm _ i) hmem
    · rw [planeCrossProduct_tangentVector, (edgeVertices_snd_mem K u).2]
  refine ⟨F, hFtoFun, fun K L ↦ ⟨hcross1 K L, hcross2 K L⟩, fun K ↦ ?_⟩
  have harea := (convexArc_area a b hab hba).2.1 K
  have hK := hcross1 K K
  rw [harea]
  linarith

/-- Antisymmetry of the vertex cross Stieltjes integral over the open interval, up to the two
endpoint corrections: the negative vertices at `b` and the positive vertices at `a`. -/
theorem openIntervalCrossIntegral_antisymm {a b : ℝ} (hab : a < b)
    (K L : ConvexBody Point) (FK FL : Fin 2 → RightContinuousIntervalBV a b)
    (hFK : ∀ i t, (FK i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i)
    (hFL : ∀ i t, (FL i).toFun t =
      (edgeVertices L (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i) :
    openIntervalCrossIntegral FL (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).2) -
        openIntervalCrossIntegral FK (fun t ↦ (edgeVertices L ((t : ℝ) : Real.Angle)).1) =
      segmentArea (edgeVertices K (b : Real.Angle)).2 (edgeVertices L (b : Real.Angle)).2 -
        segmentArea (edgeVertices K (a : Real.Angle)).1 (edgeVertices L (a : Real.Angle)).1 := by
  have key (i j : Fin 2) :
      intervalStieltjesIntegral (FL j)
          (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).2 i)
          {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} +
        intervalStieltjesIntegral (FK i)
          (fun t ↦ (edgeVertices L ((t : ℝ) : Real.Angle)).1 j)
          {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} =
      (edgeVertices K (b : Real.Angle)).2 i * (edgeVertices L (b : Real.Angle)).2 j -
        (edgeVertices K (a : Real.Angle)).1 i * (edgeVertices L (a : Real.Angle)).1 j := by
    have h := intervalStieltjes_integration_by_parts_Ioo a b hab (FK i) (FL j)
    have h1 : intervalStieltjesIntegral (FL j) (Function.leftLim (FK i).toFun)
          {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} =
        intervalStieltjesIntegral (FL j)
          (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).2 i)
          {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} :=
      VectorMeasure.setIntegral_congr_fun
        (fun t ht ↦ leftLim_positiveVertex_coordinate K FK hFK i t ht.1)
    have h2 : (FL j).toFun =
        fun t : Set.Icc a b ↦ (edgeVertices L ((t : ℝ) : Real.Angle)).1 j :=
      funext (hFL j)
    rw [h1, leftLim_positiveVertex_coordinate K FK hFK i ⟨b, hab.le, le_rfl⟩ hab,
      leftLim_positiveVertex_coordinate L FL hFL j ⟨b, hab.le, le_rfl⟩ hab,
      hFK i ⟨a, le_rfl, hab.le⟩, hFL j ⟨a, le_rfl, hab.le⟩, h2] at h
    exact h
  have k01 := key 0 1
  have k10 := key 1 0
  simp only [openIntervalCrossIntegral, segmentArea, planeCrossProduct]
  linarith

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Arc Jordan
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open Set

/-- A rectifiable path traverses a segment with monotone surjective reparametrizations. -/
def IsSegmentTraversal (γ : RectifiablePathData) (P Q : Point) : Prop :=
  ∃ (φ : Set.Icc (0 : ℝ) 1 → Set.Icc γ.a γ.b)
    (τ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1),
    Continuous φ ∧ Monotone φ ∧ Function.Surjective φ ∧
    Continuous τ ∧ Monotone τ ∧ Function.Surjective τ ∧
    ∀ s, γ.path.val (φ s) = (1 - (τ s : ℝ)) • P + (τ s : ℝ) • Q

/-- A rectifiable path traverses an oriented Jordan arc in reverse. -/
def IsReverseArcTraversal (γ : RectifiablePathData) {A : OrientedJordanArc}
    (p : ArcBVParametrization A) : Prop :=
  ∃ (φ : Set.Icc (0 : ℝ) 1 → Set.Icc γ.a γ.b)
    (ψ : Set.Icc (0 : ℝ) 1 → Set.Icc p.a p.b),
    Continuous φ ∧ Monotone φ ∧ Function.Surjective φ ∧
    Continuous ψ ∧ Monotone ψ ∧ Function.Surjective ψ ∧
    ∀ s, γ.path.val (φ s) = p.path.val
      ⟨p.a + p.b - (ψ s : ℝ), by
        constructor <;> linarith [(ψ s).property.1, (ψ s).property.2]⟩

/-- A path traversing an oriented segment has the segment's signed area. -/
theorem IsSegmentTraversal.curveAreaFunctional_eq {γ : RectifiablePathData} {P Q : Point}
    (h : IsSegmentTraversal γ P Q) : curveAreaFunctional γ.path = segmentArea P Q := by
  obtain ⟨φ, τ, hφc, hφm, hφs, hτc, hτm, hτs, heq⟩ := h
  obtain ⟨y, hy, hymono, -⟩ := curveArea_comp_monotone_or_antitone_surjective
    γ.ordered zero_le_one γ.path φ hφc hφs (Or.inl hφm)
  obtain ⟨y', hy', hy'mono, -⟩ := curveArea_comp_monotone_or_antitone_surjective
    zero_le_one zero_le_one (lineSegmentBVPath P Q) τ hτc hτs (Or.inl hτm)
  have hyy : y = y' := by
    refine Subtype.ext ?_
    rw [hy, hy']
    funext s
    rw [Function.comp_apply, Function.comp_apply, heq s, lineSegmentBVPath_apply]
  rw [← hymono hφm, hyy, hy'mono hτm, curveAreaFunctional_lineSegmentBVPath]

/-- A path traversing an oriented Jordan arc backwards has the opposite signed area. -/
theorem IsReverseArcTraversal.curveAreaFunctional_eq {γ : RectifiablePathData}
    {A : OrientedJordanArc} {p : ArcBVParametrization A} (h : IsReverseArcTraversal γ p) :
    curveAreaFunctional γ.path = -curveAreaFunctional p.path := by
  obtain ⟨φ, ψ, hφc, hφm, hφs, hψc, hψm, hψs, heq⟩ := h
  set ρ : Set.Icc (0 : ℝ) 1 → Set.Icc p.a p.b := fun s ↦
    ⟨p.a + p.b - (ψ s : ℝ), by
      constructor <;> linarith [(ψ s).property.1, (ψ s).property.2]⟩ with hρdef
  have hcomp : ∀ s, γ.path.val (φ s) = p.path.val (ρ s) := heq
  have hρc : Continuous ρ :=
    (continuous_const.sub (continuous_subtype_val.comp hψc)).subtype_mk _
  have hρa : Antitone ρ := fun s t hst ↦
    Subtype.coe_le_coe.mp (by
      simp only [hρdef]
      linarith [Subtype.coe_le_coe.mpr (hψm hst)])
  have hρs : Function.Surjective ρ := by
    intro u
    obtain ⟨s, hs⟩ := hψs ⟨p.a + p.b - (u : ℝ), by
      constructor <;> linarith [u.property.1, u.property.2]⟩
    refine ⟨s, Subtype.ext ?_⟩
    have hval : ((ψ s : ℝ)) = p.a + p.b - (u : ℝ) := congrArg Subtype.val hs
    simp only [hρdef, hval]
    ring
  obtain ⟨y, hy, hymono, -⟩ := curveArea_comp_monotone_or_antitone_surjective
    γ.ordered zero_le_one γ.path φ hφc hφs (Or.inl hφm)
  obtain ⟨y', hy', -, hy'anti⟩ := curveArea_comp_monotone_or_antitone_surjective
    p.ordered zero_le_one p.path ρ hρc hρs (Or.inr hρa)
  have hyy : y = y' := by
    refine Subtype.ext ?_
    rw [hy, hy']
    funext s
    exact hcomp s
  rw [← hymono hφm, hyy, hy'anti hρa]

private def reverseArcPath {A : OrientedJordanArc} (p : ArcBVParametrization A) :
    ContinuousBVPaths p.a p.b where
  val := p.path.val ∘ Set.Icc.reverse p.ordered
  property := by
    constructor
    · exact p.path.property.1.comp (Set.Icc.continuous_reverse p.ordered)
    · intro i
      exact BoundedVariationOn.comp_antitone_surjective_Icc p.ordered
        (p.path.property.2 i) (Set.Icc.antitone_reverse p.ordered)
        (Set.Icc.surjective_reverse p.ordered)

private lemma reverseArcPath_start {A : OrientedJordanArc}
    (p : ArcBVParametrization A) :
    (reverseArcPath p).val ⟨p.a, le_rfl, p.ordered⟩ = A.endPoint := by
  simpa [reverseArcPath, Set.Icc.reverse] using p.end_eq

private lemma isSegmentTraversal_lineSegmentBVPath (P Q : Point) :
    IsSegmentTraversal
      { a := 0, b := 1, ordered := by norm_num, path := lineSegmentBVPath P Q } P Q := by
  refine ⟨id, id, continuous_id, monotone_id, Function.surjective_id,
    continuous_id, monotone_id, Function.surjective_id, ?_⟩
  intro s
  simp [lineSegmentBVPath, Path.segment_apply, AffineMap.lineMap_apply_module']
  module

private theorem boundedVariation_concatUnitIntervals_coordinate_jordan
    (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩) (i : Fin 2) :
    BoundedVariationOn (fun t ↦ Function.concatUnitIntervals p.val q.val t i) Set.univ := by
  let z : Set.Icc (0 : ℝ) 2 := ⟨0, by norm_num⟩
  let o : Set.Icc (0 : ℝ) 2 := ⟨1, by norm_num⟩
  let w : Set.Icc (0 : ℝ) 2 := ⟨2, by norm_num⟩
  let f := fun t ↦ Function.concatUnitIntervals p.val q.val t i
  have hzo : z ≤ o := by change (0 : ℝ) ≤ 1; norm_num
  have how : o ≤ w := by change (1 : ℝ) ≤ 2; norm_num
  have hsplit := eVariationOn.Icc_add_Icc f hzo how (Set.mem_univ o)
  simp only [Set.univ_inter] at hsplit
  have hwhole : Set.Icc z w = Set.univ := by
    ext t
    exact iff_true_intro t.property
  rw [hwhole] at hsplit
  change eVariationOn f Set.univ ≠ ⊤
  rw [← hsplit]
  apply ENNReal.add_ne_top.mpr
  constructor
  · refine ne_top_of_le_ne_top (p.property.2 i) ?_
    calc
      eVariationOn f (Set.Icc z o) =
          eVariationOn (fun t : Set.Icc (0 : ℝ) 2 ↦
            p.val (Set.projIcc 0 1 (by norm_num) (t : ℝ)) i) (Set.Icc z o) := by
              apply eVariationOn.congr
              intro t ht
              have ht' : (t : ℝ) ≤ 1 := by exact ht.2
              simp [f, Function.concatUnitIntervals, ht']
      _ ≤ eVariationOn (fun t ↦ p.val t i) Set.univ := by
        simpa only [Function.comp_def] using
          (eVariationOn.comp_le_of_monotoneOn (fun t ↦ p.val t i)
            (t := Set.Icc z o)
            (fun t : Set.Icc (0 : ℝ) 2 ↦ Set.projIcc 0 1 (by norm_num) (t : ℝ))
            (fun _ _ _ _ hxy ↦ Set.monotone_projIcc (by norm_num) hxy)
            (Set.mapsTo_univ _ _))
  · refine ne_top_of_le_ne_top (q.property.2 i) ?_
    calc
      eVariationOn f (Set.Icc o w) =
          eVariationOn (fun t : Set.Icc (0 : ℝ) 2 ↦
            q.val (Set.projIcc 0 1 (by norm_num) ((t : ℝ) - 1)) i) (Set.Icc o w) := by
              apply eVariationOn.congr
              intro t ht
              have hleft : (1 : ℝ) ≤ t := by exact ht.1
              have ht' : ¬(t : ℝ) ≤ 1 ∨ (t : ℝ) = 1 := by
                rcases lt_or_eq_of_le hleft with h | h
                · exact Or.inl (not_le_of_gt h)
                · exact Or.inr h.symm
              rcases ht' with ht' | htEq
              · simp [f, Function.concatUnitIntervals, ht']
              · simpa [f, Function.concatUnitIntervals, htEq] using
                  congrArg (fun z ↦ z i) hjoin
      _ ≤ eVariationOn (fun t ↦ q.val t i) Set.univ := by
        simpa only [Function.comp_def] using
          (eVariationOn.comp_le_of_monotoneOn (fun t ↦ q.val t i)
            (t := Set.Icc o w)
            (fun t : Set.Icc (0 : ℝ) 2 ↦
              Set.projIcc 0 1 (by norm_num) ((t : ℝ) - 1))
            (fun _ _ _ _ hxy ↦ Set.monotone_projIcc (by norm_num)
              (sub_le_sub_right (show (_ : ℝ) ≤ _ from hxy) 1))
            (Set.mapsTo_univ _ _))

private def concatUnitPaths_jordan (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩) :
    ContinuousBVPaths 0 2 :=
  ⟨Function.concatUnitIntervals p.val q.val,
    Function.continuous_concatUnitIntervals p.property.1 q.property.1 hjoin,
    boundedVariation_concatUnitIntervals_coordinate_jordan p q hjoin⟩

private lemma concatUnitPaths_jordan_end (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩) :
    (concatUnitPaths_jordan p q hjoin).val ⟨2, by norm_num⟩ =
      q.val ⟨1, by norm_num⟩ := by
  change Function.concatUnitIntervals p.val q.val ⟨2, by norm_num⟩ = _
  unfold Function.concatUnitIntervals
  simp only
  rw [ite_eq_right (by norm_num : ¬(2 : ℝ) ≤ 1)]
  apply congrArg q.val
  apply Subtype.ext
  norm_num

private def unitParam_jordan (a b : ℝ) (hab : a ≤ b) :
    Set.Icc (0 : ℝ) 1 → Set.Icc a b :=
  Set.Icc.convexComb ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩

private lemma continuous_unitParam_jordan (a b : ℝ) (hab : a ≤ b) :
    Continuous (unitParam_jordan a b hab) :=
  Set.Icc.continuous_convexComb _ _

private lemma monotone_unitParam_jordan (a b : ℝ) (hab : a ≤ b) :
    Monotone (unitParam_jordan a b hab) := by
  intro s t hst
  apply Subtype.coe_le_coe.mp
  simp only [unitParam_jordan, Set.Icc.coe_convexComb]
  nlinarith [show (s : ℝ) ≤ t from hst]

private lemma surjective_unitParam_jordan (a b : ℝ) (hab : a ≤ b) :
    Function.Surjective (unitParam_jordan a b hab) :=
  surjective_convexComb_endpoints a b hab

private theorem exists_reverseArcUnitPath {A : OrientedJordanArc}
    (p : ArcBVParametrization A) :
    ∃ q : ContinuousBVPaths 0 1,
      q.val = (reverseArcPath p).val ∘ unitParam_jordan p.a p.b p.ordered ∧
      IsReverseArcTraversal
        { a := 0, b := 1, ordered := by norm_num, path := q } p := by
  obtain ⟨q, hq⟩ := continuousBVPaths_comp_monotone_surjective p.ordered
    (reverseArcPath p) (unitParam_jordan p.a p.b p.ordered)
    (continuous_unitParam_jordan _ _ _) (monotone_unitParam_jordan _ _ _)
    (surjective_unitParam_jordan _ _ _)
  refine ⟨q, hq, ?_⟩
  let φ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 := id
  let ψ := unitParam_jordan p.a p.b p.ordered
  refine ⟨φ, ψ, continuous_id, monotone_id, Function.surjective_id,
    continuous_unitParam_jordan _ _ _, monotone_unitParam_jordan _ _ _,
    surjective_unitParam_jordan _ _ _, ?_⟩
  intro s
  rw [hq]
  change p.path.val (Set.Icc.reverse p.ordered (ψ s)) = p.path.val _
  simp only [ψ, unitParam_jordan, Set.Icc.reverse, Set.Icc.coe_convexComb]

private def doubleParam_jordan : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 2 :=
  fun t ↦ ⟨2 * (t : ℝ), by constructor <;> nlinarith [t.property.1, t.property.2]⟩

private lemma continuous_doubleParam_jordan : Continuous doubleParam_jordan :=
  Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _

private lemma monotone_doubleParam_jordan : Monotone doubleParam_jordan := by
  intro s t hst
  exact Subtype.coe_le_coe.mp (mul_le_mul_of_nonneg_left hst (by norm_num))

private lemma surjective_doubleParam_jordan : Function.Surjective doubleParam_jordan := by
  intro t
  refine ⟨⟨(t : ℝ) / 2, by constructor <;> nlinarith [t.property.1, t.property.2]⟩, ?_⟩
  apply Subtype.ext
  change 2 * ((t : ℝ) / 2) = t
  ring

private def reparamTwoToUnit_jordan (q : ContinuousBVPaths 0 2) :
    ContinuousBVPaths 0 1 :=
  ⟨q.val ∘ doubleParam_jordan,
    q.property.1.comp continuous_doubleParam_jordan,
    fun i ↦ BoundedVariationOn.comp_monotone_surjective_Icc (by norm_num)
      (q.property.2 i) monotone_doubleParam_jordan surjective_doubleParam_jordan⟩

private lemma reparamTwoToUnit_one (q : ContinuousBVPaths 0 2) :
    (reparamTwoToUnit_jordan q).val ⟨1, by norm_num⟩ = q.val ⟨2, by norm_num⟩ := by
  change q.val (doubleParam_jordan ⟨1, by norm_num⟩) = q.val ⟨2, by norm_num⟩
  rw [show doubleParam_jordan ⟨1, by norm_num⟩ = ⟨2, by norm_num⟩ by
    apply Subtype.ext
    norm_num [doubleParam_jordan]]

private def concatThreeUnitPaths_jordan (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩) :
    ContinuousBVPaths 0 2 :=
  let q := concatUnitPaths_jordan p₀ p₁ h01
  concatUnitPaths_jordan (reparamTwoToUnit_jordan q) p₂ (by
    rw [reparamTwoToUnit_one]
    exact (concatUnitPaths_jordan_end p₀ p₁ h01).trans h12)

private lemma concatThreeUnitPaths_first_jordan
    (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩)
    (t : Set.Icc (0 : ℝ) 1) :
    (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val
      ⟨(t : ℝ) / 2, by constructor <;> nlinarith [t.property.1, t.property.2]⟩ =
        p₀.val t := by
  simp only [concatThreeUnitPaths_jordan, concatUnitPaths_jordan,
    reparamTwoToUnit_jordan]
  unfold Function.concatUnitIntervals
  rw [ite_eq_left (by nlinarith [t.property.1, t.property.2] : (t : ℝ) / 2 ≤ 1)]
  have houter : Set.projIcc 0 1 (by norm_num) ((t : ℝ) / 2) =
      ⟨(t : ℝ) / 2, by constructor <;> nlinarith [t.property.1, t.property.2]⟩ := by
    exact Set.projIcc_of_mem (by norm_num) (by
      constructor <;> nlinarith [t.property.1, t.property.2])
  rw [houter]
  change Function.concatUnitIntervals p₀.val p₁.val
    (doubleParam_jordan ⟨(t : ℝ) / 2, by
      constructor <;> nlinarith [t.property.1, t.property.2]⟩) = p₀.val t
  rw [show doubleParam_jordan ⟨(t : ℝ) / 2, by
      constructor <;> nlinarith [t.property.1, t.property.2]⟩ =
      ⟨(t : ℝ), ⟨t.property.1, t.property.2.trans (by norm_num)⟩⟩ by
    apply Subtype.ext
    simp [doubleParam_jordan]
    ring]
  unfold Function.concatUnitIntervals
  rw [ite_eq_left t.property.2]
  apply congrArg p₀.val
  exact Set.projIcc_of_mem (by norm_num) t.property

private lemma concatThreeUnitPaths_middle_jordan
    (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩)
    (t : Set.Icc (0 : ℝ) 1) :
    (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val
      ⟨(1 + (t : ℝ)) / 2, by
        constructor <;> nlinarith [t.property.1, t.property.2]⟩ = p₁.val t := by
  simp only [concatThreeUnitPaths_jordan, concatUnitPaths_jordan,
    reparamTwoToUnit_jordan]
  unfold Function.concatUnitIntervals
  rw [ite_eq_left (by nlinarith [t.property.2] : (1 + (t : ℝ)) / 2 ≤ 1)]
  have houter : Set.projIcc 0 1 (by norm_num) ((1 + (t : ℝ)) / 2) =
      ⟨(1 + (t : ℝ)) / 2, by
        constructor <;> nlinarith [t.property.1, t.property.2]⟩ := by
    exact Set.projIcc_of_mem (by norm_num) (by
      constructor <;> nlinarith [t.property.1, t.property.2])
  rw [houter]
  change Function.concatUnitIntervals p₀.val p₁.val
    (doubleParam_jordan ⟨(1 + (t : ℝ)) / 2, by
      constructor <;> nlinarith [t.property.1, t.property.2]⟩) = p₁.val t
  rw [show doubleParam_jordan ⟨(1 + (t : ℝ)) / 2, by
      constructor <;> nlinarith [t.property.1, t.property.2]⟩ =
      ⟨1 + (t : ℝ), by
        constructor <;> nlinarith [t.property.1, t.property.2]⟩ by
    apply Subtype.ext
    simp [doubleParam_jordan]
    ring]
  unfold Function.concatUnitIntervals
  by_cases ht : (t : ℝ) = 0
  · have ht' : t = ⟨0, by norm_num⟩ := Subtype.ext ht
    subst t
    simpa using h01
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    rw [ite_eq_right (by linarith : ¬(1 + (t : ℝ) ≤ 1))]
    apply congrArg p₁.val
    apply Subtype.ext
    simp only [Set.coe_projIcc]
    rw [show 1 + (t : ℝ) - 1 = t by ring, min_eq_right t.property.2,
      max_eq_right t.property.1]

private lemma concatThreeUnitPaths_last_jordan
    (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩)
    (t : Set.Icc (0 : ℝ) 1) :
    (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val
      ⟨1 + (t : ℝ), by
        constructor <;> nlinarith [t.property.1, t.property.2]⟩ = p₂.val t := by
  by_cases ht : (t : ℝ) = 0
  · have ht' : t = ⟨0, by norm_num⟩ := Subtype.ext ht
    rw [ht']
    rw [show (⟨1 + ((⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) : ℝ), by
      norm_num⟩ : Set.Icc (0 : ℝ) 2) = ⟨1, by norm_num⟩ by
      apply Subtype.ext
      norm_num]
    change (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val
      ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩
    unfold concatThreeUnitPaths_jordan
    change Function.concatUnitIntervals _ p₂.val ⟨1, by norm_num⟩ = _
    unfold Function.concatUnitIntervals
    rw [ite_eq_left (by norm_num : (1 : ℝ) ≤ 1)]
    calc
      _ = (reparamTwoToUnit_jordan
          (concatUnitPaths_jordan p₀ p₁ h01)).val ⟨1, by norm_num⟩ := by
        apply congrArg _
        apply Subtype.ext
        norm_num [Set.coe_projIcc]
      _ = _ := by
        rw [reparamTwoToUnit_one, concatUnitPaths_jordan_end]
        exact h12
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    simp only [concatThreeUnitPaths_jordan, concatUnitPaths_jordan]
    unfold Function.concatUnitIntervals
    rw [ite_eq_right (by linarith : ¬(1 + (t : ℝ) ≤ 1))]
    apply congrArg p₂.val
    apply Subtype.ext
    simp only [Set.coe_projIcc]
    rw [show 1 + (t : ℝ) - 1 = t by ring, min_eq_right t.property.2,
      max_eq_right t.property.1]

private theorem isPathConcatenation_concatThreeUnitPaths_jordan
    (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩) :
    IsPathConcatenation
      { a := 0, b := 2, ordered := by norm_num,
        path := concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12 }
      ![{ a := 0, b := 1, ordered := by norm_num, path := p₀ },
        { a := 0, b := 1, ordered := by norm_num, path := p₁ },
        { a := 0, b := 1, ordered := by norm_num, path := p₂ }] := by
  let cuts : Fin 4 → Set.Icc (0 : ℝ) 2 :=
    ![⟨0, by norm_num⟩, ⟨1 / 2, by norm_num⟩,
      ⟨1, by norm_num⟩, ⟨2, by norm_num⟩]
  refine ⟨by norm_num, cuts, ?_, rfl, rfl, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [cuts, Matrix.cons_val_zero, Matrix.cons_val_one] at hij <;>
      norm_num [cuts, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro i
  fin_cases i
  · let φ : Set.Icc (0 : ℝ) 1 → Set.Icc (cuts (Fin.castSucc 0) : ℝ)
        (cuts (Fin.succ 0) : ℝ) := fun t ↦ ⟨(t : ℝ) / 2, by
          change (0 : ℝ) ≤ (t : ℝ) / 2 ∧ (t : ℝ) / 2 ≤ 1 / 2
          constructor <;> nlinarith [t.property.1, t.property.2]⟩
    refine ⟨φ, id, Continuous.subtype_mk (continuous_subtype_val.div_const 2) _,
      ?_, ?_, continuous_id, monotone_id, Function.surjective_id, ?_⟩
    · intro s t hst
      exact Subtype.coe_le_coe.mp (div_le_div_of_nonneg_right hst (by norm_num))
    · intro t
      have ht : (0 : ℝ) ≤ t ∧ (t : ℝ) ≤ 1 / 2 := by
        simpa [cuts, Matrix.cons_val_zero, Matrix.cons_val_one] using t.property
      refine ⟨⟨2 * (t : ℝ), by
        change (0 : ℝ) ≤ 2 * (t : ℝ) ∧ 2 * (t : ℝ) ≤ 1
        constructor <;> nlinarith [ht.1, ht.2]⟩, ?_⟩
      apply Subtype.ext
      change 2 * (t : ℝ) / 2 = t
      ring
    · intro t
      exact concatThreeUnitPaths_first_jordan p₀ p₁ p₂ h01 h12 t
  · let φ : Set.Icc (0 : ℝ) 1 → Set.Icc (cuts (Fin.castSucc 1) : ℝ)
        (cuts (Fin.succ 1) : ℝ) := fun t ↦ ⟨(1 + (t : ℝ)) / 2, by
          change (1 / 2 : ℝ) ≤ (1 + (t : ℝ)) / 2 ∧ (1 + (t : ℝ)) / 2 ≤ 1
          constructor <;> nlinarith [t.property.1, t.property.2]⟩
    refine ⟨φ, id, Continuous.subtype_mk
      ((continuous_const.add continuous_subtype_val).div_const 2) _, ?_, ?_,
      continuous_id, monotone_id, Function.surjective_id, ?_⟩
    · intro s t hst
      apply Subtype.coe_le_coe.mp
      have hst' : (s : ℝ) ≤ t := hst
      change (1 + (s : ℝ)) / 2 ≤ (1 + (t : ℝ)) / 2
      linarith
    · intro t
      have ht : (1 / 2 : ℝ) ≤ t ∧ (t : ℝ) ≤ 1 := by
        simpa [cuts, Matrix.cons_val_zero, Matrix.cons_val_one] using t.property
      refine ⟨⟨2 * (t : ℝ) - 1, by
        change (0 : ℝ) ≤ 2 * (t : ℝ) - 1 ∧ 2 * (t : ℝ) - 1 ≤ 1
        constructor <;> nlinarith [ht.1, ht.2]⟩, ?_⟩
      apply Subtype.ext
      change (1 + (2 * (t : ℝ) - 1)) / 2 = t
      ring
    · intro t
      exact concatThreeUnitPaths_middle_jordan p₀ p₁ p₂ h01 h12 t
  · let φ : Set.Icc (0 : ℝ) 1 → Set.Icc (cuts (Fin.castSucc 2) : ℝ)
        (cuts (Fin.succ 2) : ℝ) := fun t ↦ ⟨1 + (t : ℝ), by
          change (1 : ℝ) ≤ 1 + (t : ℝ) ∧ 1 + (t : ℝ) ≤ 2
          constructor <;> nlinarith [t.property.1, t.property.2]⟩
    refine ⟨φ, id, Continuous.subtype_mk
      (continuous_const.add continuous_subtype_val) _, ?_, ?_,
      continuous_id, monotone_id, Function.surjective_id, ?_⟩
    · intro s t hst
      apply Subtype.coe_le_coe.mp
      have hst' : (s : ℝ) ≤ t := hst
      change 1 + (s : ℝ) ≤ 1 + (t : ℝ)
      linarith
    · intro t
      have ht : (1 : ℝ) ≤ t ∧ (t : ℝ) ≤ 2 := by
        simpa [cuts, Matrix.cons_val_zero, Matrix.cons_val_one] using t.property
      refine ⟨⟨(t : ℝ) - 1, by
        change (0 : ℝ) ≤ (t : ℝ) - 1 ∧ (t : ℝ) - 1 ≤ 1
        constructor <;> nlinarith [ht.1, ht.2]⟩, ?_⟩
      apply Subtype.ext
      change 1 + ((t : ℝ) - 1) = t
      ring
    · intro t
      exact concatThreeUnitPaths_last_jordan p₀ p₁ p₂ h01 h12 t

private lemma range_comp_surjective {α β γ : Type*} (f : β → γ) (g : α → β)
    (hg : Function.Surjective g) : Set.range (f ∘ g) = Set.range f := by
  apply Set.Subset.antisymm
  · exact Set.range_comp_subset_range _ _
  · rintro y ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := hg x
    exact ⟨z, rfl⟩

private lemma range_concatThreeUnitPaths_jordan
    (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩) :
    Set.range (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val =
      Set.range p₀.val ∪ Set.range p₁.val ∪ Set.range p₂.val := by
  let q := concatUnitPaths_jordan p₀ p₁ h01
  have hqend : q.val ⟨2, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩ :=
    (concatUnitPaths_jordan_end p₀ p₁ h01).trans h12
  have houter : (reparamTwoToUnit_jordan q).val ⟨1, by norm_num⟩ =
      p₂.val ⟨0, by norm_num⟩ := (reparamTwoToUnit_one q).trans hqend
  change Set.range (Function.concatUnitIntervals
    (reparamTwoToUnit_jordan q).val p₂.val) = _
  rw [Function.range_concatUnitIntervals _ _ houter]
  have hrepr : Set.range (reparamTwoToUnit_jordan q).val = Set.range q.val := by
    exact range_comp_surjective q.val doubleParam_jordan surjective_doubleParam_jordan
  rw [hrepr]
  change Set.range (Function.concatUnitIntervals p₀.val p₁.val) ∪ Set.range p₂.val = _
  rw [Function.range_concatUnitIntervals _ _ h01]

private lemma range_reverseArcUnitPath {A : OrientedJordanArc}
    (p : ArcBVParametrization A) (q : ContinuousBVPaths 0 1)
    (hq : q.val = (reverseArcPath p).val ∘ unitParam_jordan p.a p.b p.ordered) :
    Set.range q.val = A.carrier := by
  rw [hq, range_comp_surjective _ _ (surjective_unitParam_jordan _ _ _)]
  change Set.range (p.path.val ∘ Set.Icc.reverse p.ordered) = _
  rw [range_comp_surjective _ _ (Set.Icc.surjective_reverse p.ordered), p.range_eq]

private theorem segment_fst_supportingIntersection_inter_body
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    segment ℝ (edgeVertices K (a : Real.Angle)).1 (supportingIntersection K a b) ∩
        (K : Set Point) = {(edgeVertices K (a : Real.Angle)).1} := by
  let P := (edgeVertices K (a : Real.Angle)).1
  let O := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  obtain ⟨d, hd, hO⟩ := supportingIntersection_eq_fst_add_pos_tangent K hab hba hne
  change O = P + d • tangentVector (a : Real.Angle) at hO
  apply Set.Subset.antisymm
  · rintro z ⟨hzseg, hzK⟩
    rw [segment_eq_image] at hzseg
    obtain ⟨r, hr, rfl⟩ := hzseg
    have hPn := (edgeVertices_fst_mem K (a : Real.Angle)).2
    have hOn := supportingIntersection_inner_left K a b
    have hzline : inner ℝ ((1 - r) • P + r • O) (normalVector (a : Real.Angle)) =
        supportValue K a := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      change (1 - r) * inner ℝ P (normalVector (a : Real.Angle)) +
        r * inner ℝ O (normalVector (a : Real.Angle)) = _
      rw [show inner ℝ P (normalVector (a : Real.Angle)) = supportValue K a from hPn,
        show inner ℝ O (normalVector (a : Real.Angle)) = supportValue K a from hOn]
      ring
    have hzedge : (1 - r) • P + r • O ∈ exposedEdge K (a : Real.Angle) :=
      ⟨hzK, hzline⟩
    have hzle : inner ℝ ((1 - r) • P + r • O) (tangentVector (a : Real.Angle)) ≤
        inner ℝ P (tangentVector (a : Real.Angle)) := by
      rw [inner_edgeVertices_fst_tangent]
      exact le_csSup ((isCompact_exposedEdge K _).image
        (continuous_id.inner continuous_const)).bddAbove ⟨_, hzedge, rfl⟩
    rw [hO, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_add_left, real_inner_smul_left, inner_tangentVector_self] at hzle
    have hr0 : r = 0 := by nlinarith [hr.1]
    simp [hr0]
  · intro z hz
    have hzP : z = P := by simpa [P] using hz
    subst z
    exact ⟨left_mem_segment ℝ P O, (edgeVertices_fst_mem K _).1⟩

private theorem segment_supportingIntersection_snd_inter_body
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    segment ℝ (supportingIntersection K a b) (edgeVertices K (b : Real.Angle)).2 ∩
        (K : Set Point) = {(edgeVertices K (b : Real.Angle)).2} := by
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  obtain ⟨d, hd, hO⟩ := supportingIntersection_eq_snd_sub_pos_tangent K hab hba hne
  change O = Q - d • tangentVector (b : Real.Angle) at hO
  apply Set.Subset.antisymm
  · rintro z ⟨hzseg, hzK⟩
    rw [segment_eq_image] at hzseg
    obtain ⟨r, hr, rfl⟩ := hzseg
    have hQn := (edgeVertices_snd_mem K (b : Real.Angle)).2
    have hOn := supportingIntersection_inner_right K a b
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)).ne'
    have hzline : inner ℝ ((1 - r) • O + r • Q) (normalVector (b : Real.Angle)) =
        supportValue K b := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      change (1 - r) * inner ℝ O (normalVector (b : Real.Angle)) +
        r * inner ℝ Q (normalVector (b : Real.Angle)) = _
      rw [show inner ℝ O (normalVector (b : Real.Angle)) = supportValue K b from hOn,
        show inner ℝ Q (normalVector (b : Real.Angle)) = supportValue K b from hQn]
      ring
    have hzedge : (1 - r) • O + r • Q ∈ exposedEdge K (b : Real.Angle) :=
      ⟨hzK, hzline⟩
    have hzge : inner ℝ Q (tangentVector (b : Real.Angle)) ≤
        inner ℝ ((1 - r) • O + r • Q) (tangentVector (b : Real.Angle)) := by
      rw [inner_edgeVertices_snd_tangent]
      exact csInf_le ((isCompact_exposedEdge K _).image
        (continuous_id.inner continuous_const)).bddBelow ⟨_, hzedge, rfl⟩
    rw [hO, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_sub_left, real_inner_smul_left, inner_tangentVector_self] at hzge
    have hr1 : r = 1 := by nlinarith [hr.2]
    simp [hr1]
  · intro z hz
    have hzQ : z = Q := by simpa [Q] using hz
    subst z
    exact ⟨right_mem_segment ℝ O Q, (edgeVertices_snd_mem K _).1⟩

/-- A convex boundary arc lies in its convex body. -/
theorem convexBoundaryArc_subset_body (K : ConvexBody Point) (a b : ℝ) :
    convexBoundaryArc K a b ⊆ (K : Set Point) := by
  rintro z (hz | hz)
  · rcases hz with hz | hz
    · simpa using hz ▸ (edgeVertices_fst_mem K (a : Real.Angle)).1
    · rcases Set.mem_iUnion.mp hz with ⟨t, hz⟩
      rcases Set.mem_iUnion.mp hz with ⟨_, hz⟩
      exact hz.1
  · simpa using hz ▸ (edgeVertices_snd_mem K (b : Real.Angle)).1

private theorem segment_fst_inter_convexBoundaryArc
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    segment ℝ (edgeVertices K (a : Real.Angle)).1 (supportingIntersection K a b) ∩
        convexBoundaryArc K a b = {(edgeVertices K (a : Real.Angle)).1} := by
  apply Set.Subset.antisymm
  · intro z hz
    have hz' : z ∈ segment ℝ (edgeVertices K (a : Real.Angle)).1
        (supportingIntersection K a b) ∩ (K : Set Point) :=
      ⟨hz.1, convexBoundaryArc_subset_body K a b hz.2⟩
    simpa [segment_fst_supportingIntersection_inter_body K hab hba hne] using hz'
  · intro z hz
    have hzP : z = (edgeVertices K (a : Real.Angle)).1 := by simpa using hz
    subst z
    exact ⟨left_mem_segment _ _ _, Or.inl (Or.inl rfl)⟩

private theorem segment_snd_inter_convexBoundaryArc
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    segment ℝ (supportingIntersection K a b) (edgeVertices K (b : Real.Angle)).2 ∩
        convexBoundaryArc K a b = {(edgeVertices K (b : Real.Angle)).2} := by
  apply Set.Subset.antisymm
  · intro z hz
    have hz' : z ∈ segment ℝ (supportingIntersection K a b)
        (edgeVertices K (b : Real.Angle)).2 ∩ (K : Set Point) :=
      ⟨hz.1, convexBoundaryArc_subset_body K a b hz.2⟩
    simpa [segment_supportingIntersection_snd_inter_body K hab hba hne] using hz'
  · intro z hz
    have hzQ : z = (edgeVertices K (b : Real.Angle)).2 := by simpa using hz
    subst z
    exact ⟨right_mem_segment _ _ _, Or.inr rfl⟩

private theorem supporting_segments_inter
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi) :
    segment ℝ (edgeVertices K (a : Real.Angle)).1 (supportingIntersection K a b) ∩
      segment ℝ (supportingIntersection K a b) (edgeVertices K (b : Real.Angle)).2 =
        {supportingIntersection K a b} := by
  let P := (edgeVertices K (a : Real.Angle)).1
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)
  have hPa : inner ℝ P (normalVector (a : Real.Angle)) = supportValue K a :=
    (edgeVertices_fst_mem K _).2
  have hOa : inner ℝ O (normalVector (a : Real.Angle)) = supportValue K a :=
    supportingIntersection_inner_left K a b
  have hOb : inner ℝ O (normalVector (b : Real.Angle)) = supportValue K b :=
    supportingIntersection_inner_right K a b hsin.ne'
  have hQb : inner ℝ Q (normalVector (b : Real.Angle)) = supportValue K b :=
    (edgeVertices_snd_mem K _).2
  have inner_eq_of_segment {X Y z v : Point} {c : ℝ}
      (hX : inner ℝ X v = c) (hY : inner ℝ Y v = c)
      (hz : z ∈ segment ℝ X Y) : inner ℝ z v = c := by
    rw [segment_eq_image] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hX, hY]
    ring
  apply Set.Subset.antisymm
  · rintro z ⟨hz₁, hz₂⟩
    have hza : inner ℝ z (normalVector (a : Real.Angle)) = supportValue K a :=
      inner_eq_of_segment hPa hOa hz₁
    have hzb : inner ℝ z (normalVector (b : Real.Angle)) = supportValue K b :=
      inner_eq_of_segment hOb hQb hz₂
    have hna : inner ℝ (z - O) (normalVector (a : Real.Angle)) = 0 := by
      rw [inner_sub_left, hza, hOa, sub_self]
    have hnb : inner ℝ (z - O) (normalVector (b : Real.Angle)) = 0 := by
      rw [inner_sub_left, hzb, hOb, sub_self]
    have hnexp : normalVector (b : Real.Angle) =
        Real.cos (b - a) • normalVector (a : Real.Angle) +
          Real.sin (b - a) • tangentVector (a : Real.Angle) := by
      simpa only [add_sub_cancel] using normalVector_add_real a (b - a)
    have hta : inner ℝ (z - O) (tangentVector (a : Real.Angle)) = 0 := by
      rw [hnexp, inner_add_right, inner_smul_right, inner_smul_right, hna,
        mul_zero, zero_add] at hnb
      exact (mul_eq_zero.mp hnb).resolve_left hsin.ne'
    have hzo : z = O := by
      rw [show z = O + (z - O) by abel, ← inner_normalVector_smul_add_inner_tangentVector_smul
        (z - O) (a : Real.Angle), hna, hta, zero_smul, zero_smul, add_zero]
      simp
    simp [O, hzo]
  · intro z hz
    have hzO : z = O := by simpa [O] using hz
    subst z
    exact ⟨right_mem_segment _ _ _, left_mem_segment _ _ _⟩

private def brokenSupportPath (K : ConvexBody Point) (a b : ℝ) :
    Path (edgeVertices K (a : Real.Angle)).1 (edgeVertices K (b : Real.Angle)).2 :=
  (Path.segment (edgeVertices K (a : Real.Angle)).1 (supportingIntersection K a b)).trans
    (Path.segment (supportingIntersection K a b) (edgeVertices K (b : Real.Angle)).2)

private theorem path_segment_injective {P Q : Point} (hPQ : P ≠ Q) :
    Function.Injective (Path.segment P Q) := by
  intro s t hst
  apply Subtype.ext
  exact AffineMap.lineMap_injective ℝ hPQ (by
    simpa only [Path.segment_apply] using hst)

private theorem brokenSupportPath_injective
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    Function.Injective (brokenSupportPath K a b) := by
  let P := (edgeVertices K (a : Real.Angle)).1
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  obtain ⟨d₀, hd₀, hPO⟩ := supportingIntersection_eq_fst_add_pos_tangent K hab hba hne
  obtain ⟨d₁, hd₁, hQO⟩ := supportingIntersection_eq_snd_sub_pos_tangent K hab hba hne
  change O = P + d₀ • tangentVector (a : Real.Angle) at hPO
  change O = Q - d₁ • tangentVector (b : Real.Angle) at hQO
  have htne (u : Real.Angle) : tangentVector u ≠ 0 := by
    intro hu
    have hone : inner ℝ (tangentVector u) (tangentVector u) = 1 := by
      rw [← u.coe_toReal]
      exact inner_tangentVector_self u.toReal
    rw [hu] at hone
    simp at hone
  have hPOne : P ≠ O := by
    intro h
    have hz : d₀ • tangentVector (a : Real.Angle) = 0 := by
      calc
        d₀ • tangentVector (a : Real.Angle) = O - P := by rw [hPO]; abel
        _ = 0 := by rw [← h, sub_self]
    exact hd₀.ne' ((smul_eq_zero.mp hz).resolve_right (htne _))
  have hOQne : O ≠ Q := by
    intro h
    have hz : d₁ • tangentVector (b : Real.Angle) = 0 := by
      calc
        d₁ • tangentVector (b : Real.Angle) = Q - O := by rw [hQO]; abel
        _ = 0 := by rw [h, sub_self]
    exact hd₁.ne' ((smul_eq_zero.mp hz).resolve_right (htne _))
  intro s t hst
  change ((Path.segment P O).trans (Path.segment O Q)) s =
    ((Path.segment P O).trans (Path.segment O Q)) t at hst
  simp only [Path.trans_apply] at hst
  split_ifs at hst with hs ht ht
  · have heq := path_segment_injective hPOne hst
    apply Subtype.ext
    have := congrArg Subtype.val heq
    norm_num at this ⊢
    linarith

  · have hmem : (Path.segment P O) ⟨2 * (s : ℝ), by constructor <;> linarith
        [s.property.1, s.property.2]⟩ ∈ segment ℝ P O ∩ segment ℝ O Q := by
      constructor
      · rw [← Path.range_segment]
        exact Set.mem_range_self _
      · rw [hst, ← Path.range_segment]
        exact Set.mem_range_self _
    have hO := Set.ext_iff.mp (supporting_segments_inter K hab hba) _ |>.mp hmem
    have hs1 : (2 : ℝ) * s = 1 := by
      have heq := path_segment_injective hPOne (hO.trans (Path.target _).symm)
      exact congrArg Subtype.val heq
    have ht0 : 2 * (t : ℝ) - 1 = 0 := by
      have heq := path_segment_injective hOQne (hst.symm.trans (hO.trans (Path.source _).symm))
      exact congrArg Subtype.val heq
    apply Subtype.ext
    linarith
  · have hmem : (Path.segment P O) ⟨2 * (t : ℝ), by constructor <;> linarith
        [t.property.1, t.property.2]⟩ ∈ segment ℝ P O ∩ segment ℝ O Q := by
      constructor
      · rw [← Path.range_segment]
        exact Set.mem_range_self _
      · rw [← hst, ← Path.range_segment]
        exact Set.mem_range_self _
    have hO := Set.ext_iff.mp (supporting_segments_inter K hab hba) _ |>.mp hmem
    have ht1 : (2 : ℝ) * t = 1 := by
      have heq := path_segment_injective hPOne (hO.trans (Path.target _).symm)
      exact congrArg Subtype.val heq
    have hs0 : 2 * (s : ℝ) - 1 = 0 := by
      have heq := path_segment_injective hOQne (hst.trans (hO.trans (Path.source _).symm))
      exact congrArg Subtype.val heq
    apply Subtype.ext
    linarith
  · have heq := path_segment_injective hOQne hst
    apply Subtype.ext
    have := congrArg Subtype.val heq
    norm_num at this ⊢
    linarith

private theorem brokenSupportPath_range
    (K : ConvexBody Point) (a b : ℝ) :
    Set.range (brokenSupportPath K a b) =
      segment ℝ (edgeVertices K (a : Real.Angle)).1 (supportingIntersection K a b) ∪
      segment ℝ (supportingIntersection K a b) (edgeVertices K (b : Real.Angle)).2 := by
  simp [brokenSupportPath, Path.trans_range, Path.range_segment]

private theorem brokenSupportPath_range_inter_convexBoundaryArc
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    Set.range (brokenSupportPath K a b) ∩ convexBoundaryArc K a b =
      {(edgeVertices K (a : Real.Angle)).1, (edgeVertices K (b : Real.Angle)).2} := by
  rw [brokenSupportPath_range, Set.union_inter_distrib_right,
    segment_fst_inter_convexBoundaryArc K hab hba hne,
    segment_snd_inter_convexBoundaryArc K hab hba hne]
  ext z
  simp [or_comm]

private def arcUnitPath {A : OrientedJordanArc} (p : ArcBVParametrization A) :
    Path A.startPoint A.endPoint where
  toFun := p.path.val ∘ unitParam_jordan p.a p.b p.ordered
  source' := by
    change p.path.val (unitParam_jordan p.a p.b p.ordered 0) = A.startPoint
    rw [show unitParam_jordan p.a p.b p.ordered 0 = ⟨p.a, le_rfl, p.ordered⟩ by
      exact Set.Icc.convexComb_zero _ _]
    exact p.start_eq
  target' := by
    change p.path.val (unitParam_jordan p.a p.b p.ordered 1) = A.endPoint
    rw [show unitParam_jordan p.a p.b p.ordered 1 = ⟨p.b, p.ordered, le_rfl⟩ by
      exact Set.Icc.convexComb_one _ _]
    exact p.end_eq
  continuous_toFun := p.path.property.1.comp (continuous_unitParam_jordan _ _ _)

private theorem arcUnitPath_injective {A : OrientedJordanArc}
    (p : ArcBVParametrization A) (hne : A.startPoint ≠ A.endPoint) :
    Function.Injective (arcUnitPath p) := by
  intro s t hst
  have hpab : p.a < p.b := lt_of_le_of_ne p.ordered fun hab ↦ by
    have heq : (⟨p.a, le_rfl, p.ordered⟩ : Set.Icc p.a p.b) =
        ⟨p.b, p.ordered, le_rfl⟩ := Subtype.ext hab
    exact hne (p.start_eq.symm.trans ((congrArg p.path.val heq).trans p.end_eq))
  have huv := p.injective (by simpa [arcUnitPath, Function.comp_apply] using hst)
  exact (strictMono_convexComb_of_lt _ _ hpab).injective huv

private theorem arcUnitPath_range {A : OrientedJordanArc}
    (p : ArcBVParametrization A) : Set.range (arcUnitPath p) = A.carrier := by
  change Set.range (p.path.val ∘ unitParam_jordan p.a p.b p.ordered) = _
  rw [range_comp_surjective _ _ (surjective_unitParam_jordan _ _ _), p.range_eq]

private theorem isJordanCurve_of_tau {Γ : Set Point} (hΓ : TauCeti.IsJordanCurve Γ) :
    IsJordanCurve Γ := by
  obtain ⟨e⟩ := hΓ
  refine ⟨fun z ↦ (e.symm z : Point), continuous_subtype_val.comp e.symm.continuous,
    fun z w h ↦ e.symm.injective (Subtype.ext h), ?_⟩
  apply Set.Subset.antisymm
  · rintro z ⟨u, rfl⟩
    exact (e.symm u).property
  · intro z hz
    exact ⟨e ⟨z, hz⟩, congrArg Subtype.val (e.symm_apply_apply ⟨z, hz⟩)⟩

private theorem convexArc_broken_isJordanCurve
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2)
    (A : RectifiableOrientedArc) (p : ArcBVParametrization A.val)
    (hA : RealizesConvexArc K a b A) :
    IsJordanCurve (Set.range (brokenSupportPath K a b) ∪ A.val.carrier) := by
  have hmeet : Set.range (brokenSupportPath K a b) ∩ Set.range (arcUnitPath p) =
      {(edgeVertices K (a : Real.Angle)).1, (edgeVertices K (b : Real.Angle)).2} := by
    rw [arcUnitPath_range, hA.1]
    exact brokenSupportPath_range_inter_convexBoundaryArc K hab hba hne
  have hstart : A.val.startPoint = (edgeVertices K (a : Real.Angle)).1 := hA.2.1
  have hend : A.val.endPoint = (edgeVertices K (b : Real.Angle)).2 := hA.2.2
  have hstartend : A.val.startPoint ≠ A.val.endPoint := by simpa [hstart, hend] using hne
  let δ : Path (edgeVertices K (a : Real.Angle)).1
      (edgeVertices K (b : Real.Angle)).2 :=
    (arcUnitPath p).cast hstart.symm hend.symm
  have hδinj : Function.Injective δ := by
    simpa only [δ, Path.cast_coe] using arcUnitPath_injective p hstartend
  have hδrange : Set.range δ = A.val.carrier := by
    simpa only [δ, Path.cast_coe] using arcUnitPath_range p
  have htau := TauCeti.isJordanCurve_range_union_range_of_inter_eq_pair
    (brokenSupportPath_injective K hab hba hne) hδinj (by
      rw [hδrange]
      simpa [hstart, hend, arcUnitPath_range] using hmeet)
  rw [hδrange] at htau
  exact isJordanCurve_of_tau htau

private theorem jordanInterior_subset_closedConvexHull {Γ : Set Point}
    (hΓ : Γ.Nonempty) : jordanInterior Γ ⊆ closedConvexHull ℝ Γ := by
  intro p hp
  exact TauCeti.filledHull_subset_closedConvexHull hΓ hp.2

/-- The region enclosed by a loop inside a closed convex set stays inside that set. -/
theorem jordanInterior_subset_of_subset_closed_convex
    {Γ C : Set Point} (hΓ : Γ.Nonempty) (hsub : Γ ⊆ C)
    (hconv : Convex ℝ C) (hclosed : IsClosed C) : jordanInterior Γ ⊆ C := by
  exact (jordanInterior_subset_closedConvexHull hΓ).trans
    (closedConvexHull_min hsub hconv hclosed)

private theorem isOpen_jordanInterior_of_isJordanCurve {Γ : Set Point}
    (hΓ : IsJordanCurve Γ) : IsOpen (jordanInterior Γ) := by
  obtain ⟨U, V, hUopen, hVopen, hUconn, hVconn, hUbounded, hVunbounded, hdis,
    hcover, hfrontU, hfrontV, hcompU, hcompV⟩ := jordan_separation hΓ
  have heq : jordanInterior Γ = U := by
    ext p
    constructor
    · intro hp
      have hpUV : p ∈ U ∪ V := hcover.symm.subset hp.1
      rcases hpUV with hpU | hpV
      · exact hpU
      · exfalso
        exact hVunbounded (by simpa only [hcompV p hpV] using hp.2)
    · intro hpU
      constructor
      · intro hpΓ
        have hpcompl : p ∈ Γᶜ := hcover ▸ Or.inl hpU
        exact hpcompl hpΓ
      · simpa only [hcompU p hpU] using hUbounded
  rw [heq]
  exact hUopen

private theorem jordanInterior_subset_interior_of_subset_closed_convex
    {Γ C : Set Point} (hJordan : IsJordanCurve Γ) (hΓ : Γ.Nonempty)
    (hsub : Γ ⊆ C) (hconv : Convex ℝ C) (hclosed : IsClosed C) :
    jordanInterior Γ ⊆ interior C := by
  intro p hp
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset
    ((isOpen_jordanInterior_of_isJordanCurve hJordan).mem_nhds hp)
    (jordanInterior_subset_of_subset_closed_convex hΓ hsub hconv hclosed)

private theorem injOn_concatUnitPaths_jordan
    (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩)
    (hclose : q.val ⟨1, by norm_num⟩ = p.val ⟨0, by norm_num⟩)
    (hp : Function.Injective p.val) (hq : Function.Injective q.val)
    (hmeet : Set.range p.val ∩ Set.range q.val =
      {p.val ⟨0, by norm_num⟩, p.val ⟨1, by norm_num⟩}) :
    Set.InjOn (concatUnitPaths_jordan p q hjoin).val {t | (t : ℝ) < 2} := by
  intro s hs t ht hst
  change (s : ℝ) < 2 at hs
  change (t : ℝ) < 2 at ht
  change Function.concatUnitIntervals p.val q.val s =
    Function.concatUnitIntervals p.val q.val t at hst
  unfold Function.concatUnitIntervals at hst
  split_ifs at hst with hs₁ ht₁ ht₁
  · have heq := congrArg Subtype.val (hp hst)
    apply Subtype.ext
    simp only [Set.coe_projIcc] at heq
    rw [min_eq_right hs₁, max_eq_right s.property.1,
      min_eq_right ht₁, max_eq_right t.property.1] at heq
    exact heq
  · have hmem : p.val (Set.projIcc 0 1 (by norm_num) (s : ℝ)) ∈
        Set.range p.val ∩ Set.range q.val :=
      ⟨Set.mem_range_self _, hst ▸ Set.mem_range_self _⟩
    rw [hmeet] at hmem
    rcases hmem with hP | hQ
    · have hs0 := congrArg Subtype.val (hp hP)
      have ht1 := congrArg Subtype.val (hq (hst.symm.trans (hP.trans hclose.symm)))
      simp only [Set.coe_projIcc] at hs0 ht1
      rw [min_eq_right hs₁, max_eq_right s.property.1] at hs0
      rw [min_eq_right (by linarith [t.property.2]),
        max_eq_right (by linarith)] at ht1
      exfalso
      linarith
    · have hs1 := congrArg Subtype.val (hp hQ)
      have ht0 := congrArg Subtype.val (hq (hst.symm.trans (hQ.trans hjoin)))
      simp only [Set.coe_projIcc] at hs1 ht0
      rw [min_eq_right hs₁, max_eq_right s.property.1] at hs1
      rw [min_eq_right (by linarith [t.property.2]),
        max_eq_right (by linarith)] at ht0
      apply Subtype.ext
      linarith
  · have hmem : p.val (Set.projIcc 0 1 (by norm_num) (t : ℝ)) ∈
        Set.range p.val ∩ Set.range q.val :=
      ⟨Set.mem_range_self _, hst.symm ▸ Set.mem_range_self _⟩
    rw [hmeet] at hmem
    rcases hmem with hP | hQ
    · have ht0 := congrArg Subtype.val (hp hP)
      have hs1 := congrArg Subtype.val (hq (hst.trans (hP.trans hclose.symm)))
      simp only [Set.coe_projIcc] at ht0 hs1
      rw [min_eq_right ht₁, max_eq_right t.property.1] at ht0
      rw [min_eq_right (by linarith [s.property.2]),
        max_eq_right (by linarith)] at hs1
      exfalso
      linarith
    · have ht1 := congrArg Subtype.val (hp hQ)
      have hs0 := congrArg Subtype.val (hq (hst.trans (hQ.trans hjoin)))
      simp only [Set.coe_projIcc] at ht1 hs0
      rw [min_eq_right ht₁, max_eq_right t.property.1] at ht1
      rw [min_eq_right (by linarith [s.property.2]),
        max_eq_right (by linarith)] at hs0
      apply Subtype.ext
      linarith
  · have heq := congrArg Subtype.val (hq hst)
    apply Subtype.ext
    simp only [Set.coe_projIcc] at heq
    rw [min_eq_right (by linarith [s.property.2]), max_eq_right (by linarith),
      min_eq_right (by linarith [t.property.2]), max_eq_right (by linarith)] at heq
    linarith

private theorem reparam_support_segments_eq_brokenSupportPath
    (K : ConvexBody Point) (a b : ℝ)
    (h01 : (lineSegmentBVPath (edgeVertices K a).1 (supportingIntersection K a b)).val
      ⟨1, by norm_num⟩ =
      (lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2).val
        ⟨0, by norm_num⟩) :
    (reparamTwoToUnit_jordan (concatUnitPaths_jordan
      (lineSegmentBVPath (edgeVertices K a).1 (supportingIntersection K a b))
      (lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2)
      h01)).val = brokenSupportPath K a b := by
  funext t
  simp only [reparamTwoToUnit_jordan, Function.comp_apply, doubleParam_jordan,
    concatUnitPaths_jordan, lineSegmentBVPath, brokenSupportPath]
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · simp only [Path.trans_apply, dite_eq_left ht]
    unfold Function.concatUnitIntervals
    rw [ite_eq_left (by linarith)]
    congr 1
    apply Subtype.ext
    simp only [Set.coe_projIcc]
    rw [min_eq_right (by linarith [t.property.2]),
      max_eq_right (by linarith [t.property.1])]
  · simp only [Path.trans_apply, dite_eq_right ht]
    unfold Function.concatUnitIntervals
    rw [ite_eq_right (by linarith)]
    congr 1
    apply Subtype.ext
    simp only [Set.coe_projIcc]
    rw [min_eq_right (by linarith [t.property.2]),
      max_eq_right (by linarith [t.property.1])]

private theorem reverseArcUnitPath_injective {A : OrientedJordanArc}
    (p : ArcBVParametrization A) (q : ContinuousBVPaths 0 1)
    (hq : q.val = (reverseArcPath p).val ∘ unitParam_jordan p.a p.b p.ordered)
    (hne : A.startPoint ≠ A.endPoint) : Function.Injective q.val := by
  have hpab : p.a < p.b := lt_of_le_of_ne p.ordered fun hab ↦ by
    have heq : (⟨p.a, le_rfl, p.ordered⟩ : Set.Icc p.a p.b) =
        ⟨p.b, p.ordered, le_rfl⟩ := Subtype.ext hab
    exact hne (p.start_eq.symm.trans ((congrArg p.path.val heq).trans p.end_eq))
  intro s t hst
  rw [hq] at hst
  have hrev := p.injective hst
  apply Subtype.ext
  have hval := congrArg Subtype.val hrev
  simp only [Set.Icc.reverse] at hval
  have huv : (unitParam_jordan p.a p.b p.ordered s : ℝ) =
      unitParam_jordan p.a p.b p.ordered t := by linarith
  exact congrArg Subtype.val
    ((strictMono_convexComb_of_lt _ _ hpab).injective (Subtype.ext huv))

private theorem brokenSupportPath_union_convexArc_subset_endpointHalfPlanes
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (A : RectifiableOrientedArc) (hA : RealizesConvexArc K a b A) :
    Set.range (brokenSupportPath K a b) ∪ A.val.carrier ⊆
      (supportingLineHalfPlane K (a : Real.Angle)).2 ∩
        (supportingLineHalfPlane K (b : Real.Angle)).2 := by
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)
  have hK (t : Real.Angle) : (K : Set Point) ⊆ (supportingLineHalfPlane K t).2 := by
    intro p hp
    exact inner_le_supportValue K hp t
  have hOa : supportingIntersection K a b ∈ (supportingLineHalfPlane K a).2 := by
    exact le_of_eq (supportingIntersection_inner_left K a b)
  have hOb : supportingIntersection K a b ∈ (supportingLineHalfPlane K b).2 := by
    exact le_of_eq (supportingIntersection_inner_right K a b hsin.ne')
  have hconv (t : Real.Angle) : Convex ℝ (supportingLineHalfPlane K t).2 := by
    intro x hx y hy u v hu hv huv
    change inner ℝ x (normalVector t) ≤ supportValue K t at hx
    change inner ℝ y (normalVector t) ≤ supportValue K t at hy
    change inner ℝ (u • x + v • y) (normalVector t) ≤ supportValue K t
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    calc
      u * inner ℝ x (normalVector t) + v * inner ℝ y (normalVector t) ≤
          u * supportValue K t + v * supportValue K t :=
        add_le_add (mul_le_mul_of_nonneg_left hx hu) (mul_le_mul_of_nonneg_left hy hv)
      _ = supportValue K t := by rw [← add_mul, huv, one_mul]
  intro p hp
  rcases hp with hp | hp
  · rw [brokenSupportPath_range] at hp
    rcases hp with hp | hp
    · constructor
      · exact (hconv a).segment_subset
          (hK a (edgeVertices_fst_mem K (a : Real.Angle)).1) hOa hp
      · exact (hconv b).segment_subset
          (hK b (edgeVertices_fst_mem K (a : Real.Angle)).1) hOb hp
    · constructor
      · exact (hconv a).segment_subset hOa
          (hK a (edgeVertices_snd_mem K (b : Real.Angle)).1) hp
      · exact (hconv b).segment_subset hOb
          (hK b (edgeVertices_snd_mem K (b : Real.Angle)).1) hp
  · have hpK : p ∈ K := convexBoundaryArc_subset_body K a b (hA.1 ▸ hp)
    exact ⟨hK a hpK, hK b hpK⟩

private theorem convexBoundaryArc_exists_support_eq
    (K : ConvexBody Point) {a b : ℝ} (hab : a ≤ b) {p : Point}
    (hp : p ∈ convexBoundaryArc K a b) :
    ∃ t ∈ Set.Icc a b,
      inner ℝ p (normalVector (t : Real.Angle)) = supportValue K (t : Real.Angle) := by
  rcases hp with (hp | hp) | hp
  · subst p
    exact ⟨a, ⟨le_rfl, hab⟩, (edgeVertices_fst_mem K (a : Real.Angle)).2⟩
  · simp only [Set.mem_iUnion] at hp
    obtain ⟨t, htab, hp⟩ := hp
    exact ⟨t, ⟨htab.1.le, htab.2.le⟩, hp.2⟩
  · subst p
    exact ⟨b, ⟨hab, le_rfl⟩, (edgeVertices_snd_mem K (b : Real.Angle)).2⟩

private theorem inner_midpoint_normal_pos {a b t : ℝ}
    (_hab : a < b) (hba : b < a + Real.pi) (ht : t ∈ Set.Icc a b) :
    0 < inner ℝ (normalVector (((a + b) / 2 : ℝ) : Real.Angle))
      (normalVector (t : Real.Angle)) := by
  rw [inner_normalVector_normalVector]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [ht.1, ht.2]

private theorem sub_pos_midpoint_normal_inner_lt_support
    (K : ConvexBody Point) {a b r : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    {p : Point}
    (hp : p ∈ ⋂ t ∈ Set.Icc a b,
      (supportingLineHalfPlane K (t : Real.Angle)).2) (hr : 0 < r)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    inner ℝ (p - r • normalVector (((a + b) / 2 : ℝ) : Real.Angle))
        (normalVector (t : Real.Angle)) < supportValue K (t : Real.Angle) := by
  have hple : inner ℝ p (normalVector (t : Real.Angle)) ≤
      supportValue K (t : Real.Angle) := by
    exact Set.mem_iInter₂.mp hp t ht
  rw [inner_sub_left, real_inner_smul_left]
  have hdot := inner_midpoint_normal_pos hab hba ht
  nlinarith

private theorem brokenSupportPath_mem_support_eq
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi) {p : Point}
    (hp : p ∈ Set.range (brokenSupportPath K a b)) :
    inner ℝ p (normalVector (a : Real.Angle)) = supportValue K a ∨
      inner ℝ p (normalVector (b : Real.Angle)) = supportValue K b := by
  have hsin : Real.sin (b - a) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)).ne'
  rw [brokenSupportPath_range] at hp
  rcases hp with hp | hp
  · left
    rw [segment_eq_image] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      (edgeVertices_fst_mem K (a : Real.Angle)).2,
      supportingIntersection_inner_left]
    ring
  · right
    rw [segment_eq_image] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      supportingIntersection_inner_right K a b hsin,
      (edgeVertices_snd_mem K (b : Real.Angle)).2]
    ring

private theorem sub_pos_midpoint_normal_not_mem_boundary_loop
    (K : ConvexBody Point) {a b r : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (A : RectifiableOrientedArc) (hA : RealizesConvexArc K a b A) {p : Point}
    (hp : p ∈ ⋂ t ∈ Set.Icc a b,
      (supportingLineHalfPlane K (t : Real.Angle)).2) (hr : 0 < r) :
    p - r • normalVector (((a + b) / 2 : ℝ) : Real.Angle) ∉
      Set.range (brokenSupportPath K a b) ∪ A.val.carrier := by
  intro hq
  rcases hq with hq | hq
  · rcases brokenSupportPath_mem_support_eq K hab hba hq with hqa | hqb
    · exact (ne_of_lt (sub_pos_midpoint_normal_inner_lt_support K hab hba hp hr a
        ⟨le_rfl, hab.le⟩)) hqa
    · exact (ne_of_lt (sub_pos_midpoint_normal_inner_lt_support K hab hba hp hr b
        ⟨hab.le, le_rfl⟩)) hqb
  · obtain ⟨t, ht, hqt⟩ := convexBoundaryArc_exists_support_eq K hab.le (hA.1 ▸ hq)
    exact (ne_of_lt (sub_pos_midpoint_normal_inner_lt_support K hab hba hp hr t ht)) hqt

private theorem boundaryLoop_component_unbounded_of_mem_supportIntersection
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (A : RectifiableOrientedArc) (hA : RealizesConvexArc K a b A) {p : Point}
    (hpX : p ∈ ⋂ t ∈ Set.Icc a b,
      (supportingLineHalfPlane K (t : Real.Angle)).2)
    (hpΓ : p ∉ Set.range (brokenSupportPath K a b) ∪ A.val.carrier) :
    ¬ Bornology.IsBounded (connectedComponentIn
      (Set.range (brokenSupportPath K a b) ∪ A.val.carrier)ᶜ p) := by
  let n := normalVector (((a + b) / 2 : ℝ) : Real.Angle)
  let f : ℝ → Point := fun r ↦ p - r • n
  have hf : Continuous f := continuous_const.sub (continuous_id.smul continuous_const)
  have hpre : IsPreconnected (f '' Set.Ici 0) :=
    isPreconnected_Ici.image f hf.continuousOn
  have hsub : f '' Set.Ici 0 ⊆
      (Set.range (brokenSupportPath K a b) ∪ A.val.carrier)ᶜ := by
    rintro q ⟨r, hr, rfl⟩
    by_cases hr0 : r = 0
    · simpa [f, hr0] using hpΓ
    · exact sub_pos_midpoint_normal_not_mem_boundary_loop K hab hba A hA hpX
        (lt_of_le_of_ne hr (Ne.symm hr0))
  have hpmem : p ∈ f '' Set.Ici 0 := ⟨0, by simp, by simp [f]⟩
  have hcomp := hpre.subset_connectedComponentIn hpmem hsub
  intro hb
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  have hn : ‖n‖ = 1 := norm_normalVector_real ((a + b) / 2)
  let r := max 0 (C + ‖p‖ + 1)
  have hr : 0 ≤ r := le_max_left _ _
  have hq := hC (f r) (hcomp ⟨r, hr, rfl⟩)
  have hdiff : ‖r • n‖ ≤ C + ‖p‖ := by
    calc
      ‖r • n‖ = ‖p - f r‖ := by simp [f]
      _ ≤ ‖p‖ + ‖f r‖ := norm_sub_le _ _
      _ ≤ C + ‖p‖ := by linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hn, mul_one] at hdiff
  have hlower : C + ‖p‖ + 1 ≤ r := le_max_right _ _
  linarith

private theorem jordanInterior_boundaryLoop_disjoint_supportIntersection
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (A : RectifiableOrientedArc) (hA : RealizesConvexArc K a b A) :
    Disjoint (jordanInterior (Set.range (brokenSupportPath K a b) ∪ A.val.carrier))
      (⋂ t ∈ Set.Icc a b, (supportingLineHalfPlane K (t : Real.Angle)).2) := by
  rw [Set.disjoint_left]
  intro p hpI hpX
  exact boundaryLoop_component_unbounded_of_mem_supportIntersection
    K hab hba A hA hpX hpI.1 hpI.2

private theorem isClosed_supportingLineHalfPlane_lower
    (K : ConvexBody Point) (t : Real.Angle) :
    IsClosed (supportingLineHalfPlane K t).2 := by
  exact isClosed_le (continuous_id.inner continuous_const) continuous_const

private theorem convex_supportingLineHalfPlane_lower
    (K : ConvexBody Point) (t : Real.Angle) :
    Convex ℝ (supportingLineHalfPlane K t).2 := by
  intro x hx y hy u v hu hv huv
  change inner ℝ x (normalVector t) ≤ supportValue K t at hx
  change inner ℝ y (normalVector t) ≤ supportValue K t at hy
  change inner ℝ (u • x + v • y) (normalVector t) ≤ supportValue K t
  rw [inner_add_left, inner_smul_left, inner_smul_left]
  simp only [RCLike.conj_to_real]
  calc
    u * inner ℝ x (normalVector t) + v * inner ℝ y (normalVector t) ≤
        u * supportValue K t + v * supportValue K t :=
      add_le_add (mul_le_mul_of_nonneg_left hx hu) (mul_le_mul_of_nonneg_left hy hv)
    _ = supportValue K t := by rw [← add_mul, huv, one_mul]

private theorem jordanInterior_boundaryLoop_subset_endpointHalfPlanes
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2)
    (A : RectifiableOrientedArc) (p : ArcBVParametrization A.val)
    (hA : RealizesConvexArc K a b A) :
    jordanInterior (Set.range (brokenSupportPath K a b) ∪ A.val.carrier) ⊆
      interior ((supportingLineHalfPlane K a).2 ∩
        (supportingLineHalfPlane K b).2) := by
  apply jordanInterior_subset_interior_of_subset_closed_convex
    (convexArc_broken_isJordanCurve K hab hba hne A p hA)
  · exact (Set.range_nonempty _).inl
  · exact brokenSupportPath_union_convexArc_subset_endpointHalfPlanes K hab hba A hA
  · exact (convex_supportingLineHalfPlane_lower K a).inter
      (convex_supportingLineHalfPlane_lower K b)
  · exact (isClosed_supportingLineHalfPlane_lower K a).inter
      (isClosed_supportingLineHalfPlane_lower K b)

private theorem concatThree_first_image_jordan
    (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩) :
    (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val ''
        Set.Icc (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 2) ⟨1 / 2, by norm_num⟩ =
      Set.range p₀.val := by
  apply Set.Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    have htt : (t : ℝ) ≤ 1 / 2 := by exact_mod_cast ht.2
    let u : Set.Icc (0 : ℝ) 1 := ⟨2 * (t : ℝ), by
      constructor <;> nlinarith [t.property.1, htt]⟩
    refine ⟨u, ?_⟩
    have heq : (⟨(u : ℝ) / 2, by
        constructor <;> nlinarith [u.property.1, u.property.2]⟩ : Set.Icc (0 : ℝ) 2) = t := by
      apply Subtype.ext
      dsimp [u]
      ring
    rw [← heq]
    exact (concatThreeUnitPaths_first_jordan p₀ p₁ p₂ h01 h12 u).symm
  · rintro z ⟨u, rfl⟩
    let t : Set.Icc (0 : ℝ) 2 := ⟨(u : ℝ) / 2, by
      constructor <;> nlinarith [u.property.1, u.property.2]⟩
    refine ⟨t, ⟨by exact Subtype.coe_le_coe.mp t.property.1,
      by change (t : ℝ) ≤ 1 / 2; dsimp [t]; linarith [u.property.2]⟩, ?_⟩
    exact concatThreeUnitPaths_first_jordan p₀ p₁ p₂ h01 h12 u

private theorem concatThree_convexArc_oriented
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2)
    (A : RectifiableOrientedArc) (p : ArcBVParametrization A.val)
    (hA : RealizesConvexArc K a b A)
    (p₂ : ContinuousBVPaths 0 1)
    (hp₂ : p₂.val = (reverseArcPath p).val ∘ unitParam_jordan p.a p.b p.ordered)
    (h01 : (lineSegmentBVPath (edgeVertices K a).1 (supportingIntersection K a b)).val
      ⟨1, by norm_num⟩ =
      (lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2).val
        ⟨0, by norm_num⟩)
    (h12 : (lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2).val
      ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩) :
    IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 2)
      (Set.range (concatThreeUnitPaths_jordan
        (lineSegmentBVPath (edgeVertices K a).1 (supportingIntersection K a b))
        (lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2)
        p₂ h01 h12).val) true
      (concatThreeUnitPaths_jordan
        (lineSegmentBVPath (edgeVertices K a).1 (supportingIntersection K a b))
        (lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2)
        p₂ h01 h12).val := by
  let p₀ := lineSegmentBVPath (edgeVertices K a).1 (supportingIntersection K a b)
  let p₁ := lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2
  let q := concatUnitPaths_jordan p₀ p₁ h01
  let q' := reparamTwoToUnit_jordan q
  let γ := concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12
  have hq' : q'.val = brokenSupportPath K a b :=
    reparam_support_segments_eq_brokenSupportPath K a b h01
  have hpq : Function.Injective q'.val := hq' ▸ brokenSupportPath_injective K hab hba hne
  have hPneQ : A.val.startPoint ≠ A.val.endPoint := by simpa [hA.2.1, hA.2.2] using hne
  have hp₂inj := reverseArcUnitPath_injective p p₂ hp₂ hPneQ
  have hqrange : Set.range q'.val = Set.range (brokenSupportPath K a b) := by rw [hq']
  have hp₂range : Set.range p₂.val = A.val.carrier := range_reverseArcUnitPath p p₂ hp₂
  have hmeet : Set.range q'.val ∩ Set.range p₂.val =
      {q'.val ⟨0, by norm_num⟩, q'.val ⟨1, by norm_num⟩} := by
    rw [hqrange, hp₂range, hA.1,
      brokenSupportPath_range_inter_convexBoundaryArc K hab hba hne, hq']
    simp [brokenSupportPath]
  have hclose : p₂.val ⟨1, by norm_num⟩ = q'.val ⟨0, by norm_num⟩ := by
    rw [hp₂]
    simp [q', hq', brokenSupportPath, reverseArcPath, unitParam_jordan, Set.Icc.reverse,
      hA.2.1, p.start_eq]
  have hjoin : q'.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩ := by
    rw [show q'.val ⟨1, by norm_num⟩ = q.val ⟨2, by norm_num⟩ from
      reparamTwoToUnit_one q]
    exact (concatUnitPaths_jordan_end p₀ p₁ h01).trans h12
  have hinj := injOn_concatUnitPaths_jordan q' p₂ hjoin
    hclose hpq hp₂inj hmeet
  have hrange : Set.range γ.val = Set.range (brokenSupportPath K a b) ∪ A.val.carrier := by
    rw [show γ = concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12 by rfl]
    rw [range_concatThreeUnitPaths_jordan, hp₂range]
    have hq'q : Set.range q'.val = Set.range q.val :=
      range_comp_surjective q.val doubleParam_jordan surjective_doubleParam_jordan
    rw [← Function.range_concatUnitIntervals p₀.val p₁.val h01]
    change Set.range q.val ∪ A.val.carrier = _
    rw [← hq'q, hqrange]
  have hJordan := convexArc_broken_isJordanCurve K hab hba hne A p hA
  obtain ⟨d, hd, hdir⟩ := supportingIntersection_eq_fst_add_pos_tangent K hab hba hne
  have hclosedγ : γ.val ⟨0, by norm_num⟩ = γ.val ⟨2, by norm_num⟩ := by
    simpa [γ, concatThreeUnitPaths_jordan, concatUnitPaths_jordan, q', q] using hclose.symm
  have hinjγ : Set.InjOn γ.val {t | (t : ℝ) < 2} := by
    simpa [γ, concatThreeUnitPaths_jordan, q', q] using hinj
  have hhalfγ (t : Set.Icc (0 : ℝ) 2) :
      γ.val t ∈ normalHalfPlane (a : Real.Angle) (supportValue K a) false false :=
    (brokenSupportPath_union_convexArc_subset_endpointHalfPlanes K hab hba A hA
      (hrange ▸ Set.mem_range_self t)).1
  let s : Set.Icc (0 : ℝ) 2 := ⟨0, by norm_num⟩
  let t : Set.Icc (0 : ℝ) 2 := ⟨1 / 2, by norm_num⟩
  have hs : γ.val s = (edgeVertices K (a : Real.Angle)).1 := by
    simpa [s, γ, p₀, lineSegmentBVPath] using
      concatThreeUnitPaths_first_jordan p₀ p₁ p₂ h01 h12 ⟨0, by norm_num⟩
  have ht : γ.val t = supportingIntersection K a b := by
    simpa [t, γ, p₀, lineSegmentBVPath] using
      concatThreeUnitPaths_first_jordan p₀ p₁ p₂ h01 h12 ⟨1, by norm_num⟩
  exact jordan_counterclockwise_of_supporting_segment 0 2 (by norm_num) γ.val
    γ.property.1 (hrange ▸ hJordan) hclosedγ hinjγ
    (a : Real.Angle) (supportValue K a) hhalfγ s t (by
      change (0 : ℝ) < 1 / 2
      norm_num)
    (by rw [hs]; exact (edgeVertices_fst_mem K (a : Real.Angle)).2)
    d hd (by rw [hs, ht]; exact hdir)
    (by
      rw [hs, ht]
      rw [show γ.val '' Set.Icc s t = Set.range p₀.val by
        simpa [s, t, γ] using concatThree_first_image_jordan p₀ p₁ p₂ h01 h12]
      exact Path.range_segment _ _)

private theorem exists_rectifiableOrientedArc_segment_jordan (P Q : Point) (hPQ : P ≠ Q) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = segment ℝ P Q ∧ A.val.startPoint = P ∧ A.val.endPoint = Q := by
  let Γ : OrientedJordanArc :=
    { carrier := segment ℝ P Q
      startPoint := P
      endPoint := Q
      parametrizable := by
        refine ⟨0, 1, by norm_num, Path.segment P Q,
          (Path.segment P Q).continuous, Path.segment_injective_of_ne hPQ,
          Path.range_segment P Q, ?_, ?_⟩ <;> simp }
  let z : ArcBVParametrization Γ :=
    { a := 0
      b := 1
      ordered := by norm_num
      path := lineSegmentBVPath P Q
      injective := Path.segment_injective_of_ne hPQ
      range_eq := Path.range_segment P Q
      start_eq := by simp [lineSegmentBVPath, Γ]
      end_eq := by simp [lineSegmentBVPath, Γ] }
  let A : RectifiableOrientedArc := ⟨Γ, ⟨z⟩⟩
  exact ⟨A, rfl, rfl, rfl⟩

private theorem exists_rectifiableOrientedArc_convexBoundaryArc_jordan
    (K : ConvexBody Point) (a b : ℝ) (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K a).1 ≠ (edgeVertices K b).2) :
    ∃ A : RectifiableOrientedArc, RealizesConvexArc K a b A := by
  let P := (edgeVertices K (a : Real.Angle)).1
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K a b
  obtain ⟨-, hcut⟩ := convexBoundaryArc_cut K a b hab hba P Q O rfl rfl rfl
  obtain ⟨hncol, t, c, K', hat, htb, hPt, hQt, hcO, hK', hleft, hmiddle,
      hright, hterminal⟩ := hcut hne
  by_cases hInt : (interior (K' : Set Point)).Nonempty
  · obtain ⟨A, hcarrier, hstart, hend⟩ :=
      exists_rectifiableOrientedArc_convexBoundaryArc_of_cut K K' a b t c P Q
        hat htb hba hne hPt hQt rfl rfl hleft hmiddle hright hterminal hInt
    exact ⟨A, hcarrier, hstart, hend⟩
  · have hInt' : interior (K' : Set Point) = ∅ := Set.not_nonempty_iff_eq_empty.mp hInt
    have harc := convexBoundaryArc_eq_segment_of_cut_interior_empty K K' a b t c P Q
      hat htb hba hne hPt hQt rfl rfl hleft hmiddle hright hInt'
    obtain ⟨A, hcarrier, hstart, hend⟩ :=
      exists_rectifiableOrientedArc_segment_jordan P Q hne
    exact ⟨A, hcarrier.trans harc.symm, hstart, hend⟩

/-- The supporting segments and reversed convex boundary arc form a counterclockwise Jordan
curve. -/
theorem convexBoundaryArc_jordan (K : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K a).1 ≠ (edgeVertices K b).2) :
    ∃ (A : RectifiableOrientedArc) (p : ArcBVParametrization A.val)
      (γ : RectifiablePathData) (pieces : Fin 3 → RectifiablePathData),
      RealizesConvexArc K a b A ∧
      IsSegmentTraversal (pieces 0) (edgeVertices K a).1 (supportingIntersection K a b) ∧
      IsSegmentTraversal (pieces 1) (supportingIntersection K a b) (edgeVertices K b).2 ∧
      IsReverseArcTraversal (pieces 2) p ∧ IsPathConcatenation γ pieces ∧
      IsOrientedJordanParametrization γ.ordered (Set.range γ.path.val) true γ.path.val ∧
      jordanInterior (Set.range γ.path.val) ⊆
        interior ((supportingLineHalfPlane K a).2 ∩ (supportingLineHalfPlane K b).2) ∧
      Disjoint (jordanInterior (Set.range γ.path.val))
        (⋂ t ∈ Set.Icc a b, (supportingLineHalfPlane K (t : Real.Angle)).2) := by
  obtain ⟨A, hA⟩ :=
    exists_rectifiableOrientedArc_convexBoundaryArc_jordan K a b hab hba hne
  let p : ArcBVParametrization A.val := Classical.choice A.property
  let P := (edgeVertices K (a : Real.Angle)).1
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K a b
  let p₀ := lineSegmentBVPath P O
  let p₁ := lineSegmentBVPath O Q
  obtain ⟨p₂, hp₂, hp₂rev⟩ := exists_reverseArcUnitPath p
  have h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩ := by
    simp [p₀, p₁, lineSegmentBVPath]
  have h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩ := by
    rw [hp₂]
    change p₁.val ⟨1, by norm_num⟩ =
      (reverseArcPath p).val (unitParam_jordan p.a p.b p.ordered ⟨0, by norm_num⟩)
    rw [show unitParam_jordan p.a p.b p.ordered ⟨0, by norm_num⟩ =
      ⟨p.a, le_rfl, p.ordered⟩ by exact Set.Icc.convexComb_zero _ _]
    rw [reverseArcPath_start]
    simpa [p₁, Q, lineSegmentBVPath, Path.segment_apply,
      AffineMap.lineMap_apply_module'] using hA.2.2.symm
  let γpath := concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12
  let γ : RectifiablePathData :=
    { a := 0, b := 2, ordered := by norm_num, path := γpath }
  let pieces : Fin 3 → RectifiablePathData :=
    ![{ a := 0, b := 1, ordered := by norm_num, path := p₀ },
      { a := 0, b := 1, ordered := by norm_num, path := p₁ },
      { a := 0, b := 1, ordered := by norm_num, path := p₂ }]
  have horient := concatThree_convexArc_oriented K hab hba hne A p hA p₂ hp₂ h01 h12
  have hrange : Set.range γ.path.val =
      Set.range (brokenSupportPath K a b) ∪ A.val.carrier := by
    change Set.range (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val = _
    rw [range_concatThreeUnitPaths_jordan, range_reverseArcUnitPath p p₂ hp₂]
    rw [← Function.range_concatUnitIntervals p₀.val p₁.val h01]
    let q := concatUnitPaths_jordan p₀ p₁ h01
    have hrepr : Set.range (reparamTwoToUnit_jordan q).val = Set.range q.val :=
      range_comp_surjective q.val doubleParam_jordan surjective_doubleParam_jordan
    change Set.range q.val ∪ A.val.carrier = _
    rw [← hrepr, show (reparamTwoToUnit_jordan q).val = brokenSupportPath K a b by
      simpa [q, p₀, p₁, P, Q, O] using
        reparam_support_segments_eq_brokenSupportPath K a b h01]
  refine ⟨A, p, γ, pieces, hA, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [pieces, P, O, Matrix.cons_val_zero] using
      isSegmentTraversal_lineSegmentBVPath P O
  · simpa [pieces, Q, O, Matrix.cons_val_zero, Matrix.cons_val_one] using
      isSegmentTraversal_lineSegmentBVPath O Q
  · simpa [pieces, Matrix.cons_val_zero, Matrix.cons_val_one] using hp₂rev
  · simpa [γ, γpath, pieces] using
      isPathConcatenation_concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12
  · simpa [γ, γpath, p₀, p₁] using horient
  · rw [hrange]
    exact jordanInterior_boundaryLoop_subset_endpointHalfPlanes K hab hba hne A p hA
  · rw [hrange]
    exact jordanInterior_boundaryLoop_disjoint_supportIntersection K hab hba A hA

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Area of the region between a convex arc and its supporting tangents

The loop built from a convex boundary arc and the two tangent segments meeting at the
intersection of the arc's endpoint supporting lines bounds the "Mamikon region" cut off by
those tangents.  The single result here bounds that region's signed area by the measure of any
set that receives it.
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The region between a convex boundary arc and its two supporting tangent segments has area
at most that of any finite-measure set that receives every point of a closed convex carrier of
the body which lies inside both endpoint supporting half-planes but outside the body. -/
theorem convexArc_tangentRegion_area_le (B : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (hba : b < a + Real.pi)
    {C : Set Point} (hconv : Convex ℝ C) (hclosed : IsClosed C)
    (hBC : (B : Set Point) ⊆ C)
    (hOC : supportingIntersection B (a : Real.Angle) (b : Real.Angle) ∈ C)
    {E : Set Point} (hE : MeasureTheory.volume E ≠ ⊤)
    (hsubE : ∀ q ∈ interior ((supportingLineHalfPlane B (a : Real.Angle)).2 ∩
        (supportingLineHalfPlane B (b : Real.Angle)).2),
      q ∈ C → q ∉ (B : Set Point) → q ∈ E) :
    segmentArea (edgeVertices B (a : Real.Angle)).1
        (supportingIntersection B (a : Real.Angle) (b : Real.Angle)) +
      segmentArea (supportingIntersection B (a : Real.Angle) (b : Real.Angle))
        (edgeVertices B (b : Real.Angle)).2 -
      convexArcArea B a b ≤ ClassicalResults.area E := by
  have harea0 : (0 : ℝ) ≤ ClassicalResults.area E := ENNReal.toReal_nonneg
  by_cases hPQ : (edgeVertices B (a : Real.Angle)).1 = (edgeVertices B (b : Real.Angle)).2
  · -- coincident endpoints: the cut lemma collapses the arc and the intersection to one point
    obtain ⟨hO, hcar⟩ := (convexBoundaryArc_cut B a b hab hba _ _ _ rfl rfl rfl).1 hPQ
    obtain ⟨Δ, hΔcar, hΔstart, hΔend, hΔarea⟩ :=
      (segmentArea_jordan_and_frame (edgeVertices B (a : Real.Angle)).1
        (edgeVertices B (a : Real.Angle)).1).1
    have hreal : RealizesConvexArc B a b Δ :=
      ⟨hΔcar.trans ((segment_same ℝ _).trans hcar.symm), hΔstart, hΔend.trans hPQ⟩
    have hzero : segmentArea (edgeVertices B (a : Real.Angle)).1
        (edgeVertices B (a : Real.Angle)).1 = 0 := by
      simp only [segmentArea, planeCrossProduct]
      ring
    rw [convexArcArea_eq_jordanArcArea_of_realizes hreal, hΔarea, hO, ← hPQ, hzero]
    simpa using harea0
  · obtain ⟨A, p, γ, pieces, hA, hs0, hs1, hrev, hconcat, horient, hint, hdisj⟩ :=
      convexBoundaryArc_jordan B a b hab hba hPQ
    have hΓne : (Set.range γ.path.val).Nonempty :=
      ⟨_, ⟨⟨γ.a, le_rfl, γ.ordered⟩, rfl⟩⟩
    have hpiece0 : Set.range (pieces 0).path.val ⊆ C := by
      obtain ⟨φ, τ, -, -, hφs, -, -, -, heq⟩ := hs0
      rintro _ ⟨u, rfl⟩
      obtain ⟨s, hs⟩ := hφs u
      rw [← hs, heq s]
      exact hconv (hBC (edgeVertices_fst_mem B _).1) hOC
        (by linarith [(τ s).property.2]) (τ s).property.1 (by ring)
    have hpiece1 : Set.range (pieces 1).path.val ⊆ C := by
      obtain ⟨φ, τ, -, -, hφs, -, -, -, heq⟩ := hs1
      rintro _ ⟨u, rfl⟩
      obtain ⟨s, hs⟩ := hφs u
      rw [← hs, heq s]
      exact hconv hOC (hBC (edgeVertices_snd_mem B _).1)
        (by linarith [(τ s).property.2]) (τ s).property.1 (by ring)
    have hpiece2 : Set.range (pieces 2).path.val ⊆ C := by
      obtain ⟨φ, ψ, -, -, hφs, -, -, -, heq⟩ := hrev
      rintro _ ⟨u, rfl⟩
      obtain ⟨s, hs⟩ := hφs u
      rw [← hs, heq s]
      have hmem : ∀ v : Set.Icc p.a p.b, p.path.val v ∈ (B : Set Point) := by
        intro v
        have h : p.path.val v ∈ Set.range p.path.val := ⟨v, rfl⟩
        rw [p.range_eq, hA.1] at h
        exact convexBoundaryArc_subset_body B a b h
      exact hBC (hmem _)
    -- the whole loop lies in `C`, hence so does the region it encloses
    have hrangeC : Set.range γ.path.val ⊆ C := by
      refine hconcat.range_subset_iUnion.trans (Set.iUnion_subset ?_)
      intro i
      fin_cases i
      · exact hpiece0
      · exact hpiece1
      · exact hpiece2
    have hRC : jordanInterior (Set.range γ.path.val) ⊆ C :=
      jordanInterior_subset_of_subset_closed_convex hΓne hrangeC hconv hclosed
    -- `B` sits inside all of its supporting half-planes, so the region avoids `B`
    have hRnotB : ∀ q ∈ jordanInterior (Set.range γ.path.val), q ∉ (B : Set Point) := by
      intro q hq hqB
      refine Set.disjoint_left.mp hdisj hq (Set.mem_iInter₂.mpr fun t _ ↦ ?_)
      show inner ℝ q (normalVector (t : Real.Angle)) ≤ supportValue (B : Set Point) _
      exact inner_le_supportValue B hqB _
    have hRE : jordanInterior (Set.range γ.path.val) ⊆ E := fun q hq =>
      hsubE q (hint hq) (hRC hq) (hRnotB q hq)
    -- signed area of the counterclockwise loop is the area it encloses, and path additivity
    -- splits it into the two segments and the reversed arc
    have hloop : curveAreaFunctional γ.path =
        ClassicalResults.area (jordanInterior (Set.range γ.path.val)) :=
      curveArea_eq_jordanInterior_area γ.a γ.b γ.ordered _ γ.path horient
    have hparc : curveAreaFunctional p.path = convexArcArea B a b := by
      rw [convexArcArea_eq_jordanArcArea_of_realizes hA]
      show _ = curveAreaFunctional (Classical.choice A.property).path
      exact (curveArea_reparametrization.2.1 A.val A.val p
        (Classical.choice A.property) rfl).1 rfl rfl
    have hval : segmentArea (edgeVertices B (a : Real.Angle)).1
          (supportingIntersection B (a : Real.Angle) (b : Real.Angle)) +
        segmentArea (supportingIntersection B (a : Real.Angle) (b : Real.Angle))
          (edgeVertices B (b : Real.Angle)).2 - convexArcArea B a b =
        curveAreaFunctional γ.path := by
      rw [curveArea_concatenation γ pieces hconcat, Fin.sum_univ_three,
        hs0.curveAreaFunctional_eq, hs1.curveAreaFunctional_eq,
        hrev.curveAreaFunctional_eq, hparc]
      ring
    rw [hval, hloop]
    have hle : MeasureTheory.volume (jordanInterior (Set.range γ.path.val)) ≤
        MeasureTheory.volume E := MeasureTheory.measure_mono hRE
    exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hE hle) hE).mpr hle

end MovingSofa

end

end

end
