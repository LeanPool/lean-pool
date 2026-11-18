/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3776T1FixedGeometry
public import LeanPool.ApollonianSuperharmonic.P3776T1StarWeights
public import Mathlib.Topology.MetricSpace.HausdorffDistance

-- [TABLET NODE: P3776T1StarWeightsExist]

/-!
# P3776T1StarWeightsExist

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace StarWeightsProof

private theorem hfaceEdge :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (f : P.plane.Face), ∀ (a : ι), ∀ (b : ι),
        P.plane.adjacent a b → (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex f i = a) → (∃ (i : Fin (3
        : ℕ)), P.plane.faceVertex f i = b) → P.plane.edgeArc a b ⊆ closure (P.plane.faceRegion f)
            := by
  classical
  intro ι P f a b hab ha hb
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  have hij : i ≠ j := by
    intro h
    have hab' : a = b := hi.symm.trans ((congrArg (P.plane.faceVertex f) h).trans hj)
    exact P.plane.adjacent_irreflexive a (hab' ▸ hab)
  have heq : P.plane.edgeArc a b = P.plane.edgeArc (P.plane.faceVertex f i)
      (P.plane.faceVertex f j) := by rw [← hi, ← hj]
  have hside : P.plane.edgeArc a b ⊆ frontier (P.plane.faceRegion f) := by
    rw [heq]
    rw [P.plane.face_boundary f]
    fin_cases i <;> fin_cases j
    all_goals
      first
      | exact (hij rfl).elim
      | intro x hx
        first
        | exact Or.inl (Or.inl hx)
        | rw [P.plane.arc_symmetric] at hx
          exact Or.inl (Or.inl hx)
        | exact Or.inl (Or.inr hx)
        | rw [P.plane.arc_symmetric] at hx
          exact Or.inl (Or.inr hx)
        | exact Or.inr hx
        | rw [P.plane.arc_symmetric] at hx
          exact Or.inr hx
  exact Set.Subset.trans hside frontier_subset_closure

private theorem hstarFace :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
    let U : ι → Set (Real × Real) := P3776T1OpenStar P
    (Nontrivial ι ∧ (∀ (f : P.plane.Face), IsCompact (closure (P.plane.faceRegion f))) ∧ (∀ (K :
        Set (ℝ × ℝ)), IsCompact K → {f : P.plane.Face | (K ∩ closure (P.plane.faceRegion
        f)).Nonempty}.Finite) ∧ (∀ (x : ℝ × ℝ), ∃ (f : P.plane.Face), x ∈ closure
        (P.plane.faceRegion f)) ∧ (∀ (a : ι), IsOpen (P3776T1OpenStar P a) ∧ IsCompact (closure
        (P3776T1OpenStar P a))) ∧ (∀ (x : ℝ × ℝ), ∃ (a : ι), x ∈ P3776T1OpenStar P a) ∧ (∀ (u
            : ↥P.lattice), ∀ (a : ι), P3776T1OpenStar P (P.shift u a) = (fun (x : ℝ × ℝ) => x +
        GaussianRealPoint (↑u : GaussianInt)) '' P3776T1OpenStar P a) ∧ ∀ (u : ↥P.lattice), ∀
            (v : ↥P.lattice), ∀ (a : ι), P.shift u a = P.shift v a → u = v) → (∀ [Nontrivial ι],
            (∀ (f : P.plane.Face), ∀ (a : ι), ∀ (b : ι), (P.plane.adjacent a b) → ((∃ i,
        P.plane.faceVertex f i = a) → ((∃ i, P.plane.faceVertex f i = b) → (P.plane.edgeArc a b ⊆
        closure (P.plane.faceRegion f))))) → (∀ (a : ι), ∀ x ∈ U a, ∃ (f : P.plane.Face), x ∈
        closure (P.plane.faceRegion f) ∧ ∃ (i : Fin (3 : ℕ)), P.plane.faceVertex f i = a)) := by
  classical
  intro ι P U hgeom hnontriv hfaceEdge a x hx
  rcases hx with hpos | hedge | hface
  · rw [hpos]
    obtain ⟨f, hxf⟩ := hgeom.2.2.2.1 (P.plane.position a)
    have hnotreg : P.plane.position a ∉ P.plane.faceRegion f := by
      have hdis := (P3767T1FixedFaceComponents P.plane).1 f |>.1
      exact fun h => (Set.disjoint_left.mp hdis) (Or.inl ⟨a, rfl⟩) h
    have hfr : P.plane.position a ∈ frontier (P.plane.faceRegion f) := by
      have hcl : P.plane.position a ∈ closure (P.plane.faceRegion f) := hxf
      rw [frontier, (P.plane.region_open f).interior_eq]
      exact ⟨hcl, hnotreg⟩
    rw [P.plane.face_boundary f] at hfr
    rcases hfr with hfr | hfr
    · rcases hfr with hfr | hfr
      · have hend := (P3767T1VertexEdgeIncidence P.plane a).2
          (P.plane.faceVertex f 0) (P.plane.faceVertex f 1)
          (P.plane.face_edges f 0 1 (by decide)) hfr
        rcases hend with h | h
        · exact ⟨f, hxf, ⟨0, h.symm⟩⟩
        · exact ⟨f, hxf, ⟨1, h.symm⟩⟩
      · have hend := (P3767T1VertexEdgeIncidence P.plane a).2
          (P.plane.faceVertex f 1) (P.plane.faceVertex f 2)
          (P.plane.face_edges f 1 2 (by decide)) hfr
        rcases hend with h | h
        · exact ⟨f, hxf, ⟨1, h.symm⟩⟩
        · exact ⟨f, hxf, ⟨2, h.symm⟩⟩
    · have hend := (P3767T1VertexEdgeIncidence P.plane a).2
        (P.plane.faceVertex f 2) (P.plane.faceVertex f 0)
        (P.plane.face_edges f 2 0 (by decide)) hfr
      rcases hend with h | h
      · exact ⟨f, hxf, ⟨2, h.symm⟩⟩
      · exact ⟨f, hxf, ⟨0, h.symm⟩⟩
  · rcases hedge with ⟨b, hab, hxab, hxa, hxb⟩
    obtain ⟨f, g, hfg, ⟨hfa, hfb⟩, _, hall⟩ :=
      P.plane.every_edge_two_faces a b hab
    refine ⟨f, ?_, hfa⟩
    exact hfaceEdge f a b hab hfa hfb hxab
  · rcases hface with ⟨f, hfa, hxf⟩
    exact ⟨f, subset_closure hxf, hfa⟩

private theorem hpairLabel :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι), ∀ (d : ι),
        P.plane.adjacent a b → P.plane.adjacent c d → ∀ x ∈ P.plane.edgeArc a b ∩ P.plane.edgeArc
        c d, x ≠ P.plane.position a → x ≠ P.plane.position b → a = c ∨ a = d := by
  classical
  intro ι P a b c d hab hcd x hx hxa hxb
  by_cases hsets : ({a, b} : Set ι) = {c, d}
  · have ha : a ∈ ({c, d} : Set ι) := hsets ▸ (by simp)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ha
  · have hintersection := P.plane.arc_intersections a b c d hab hcd hsets
    rw [hintersection] at hx
    obtain ⟨v, hv, hvx⟩ := hx
    have hvab : v = a ∨ v = b := by
      simpa only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] using hv.1
    rcases hvab with h | h
    · subst v
      exact (hxa hvx.symm).elim
    · subst v
      exact (hxb hvx.symm).elim

private theorem hfaceStarLabel :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
    let U : ι → Set (Real × Real) := P3776T1OpenStar P
    ∀ [Nontrivial ι], (∀ (a : ι), ∀ (b : ι), ∀ (c : ι), ∀ (d : ι), (P.plane.adjacent a b) →
        ((P.plane.adjacent c d) → (∀ (x : Real × Real), (x ∈ P.plane.edgeArc a b ∩
        P.plane.edgeArc c d) → ((x ≠ P.plane.position a) → ((x ≠ P.plane.position b) → (a = c ∨ a
        = d)))))) → (∀ (f : P.plane.Face), ∀ x ∈ closure (P.plane.faceRegion f), ∀ (a : ι), x ∈ U
        a → ∃ (i : Fin (3 : ℕ)), P.plane.faceVertex f i = a) := by
  classical
  intro ι P U hnontriv hpairLabel f x hxf a hxa
  have htraceAvoid := (P3767T1FixedFaceComponents P.plane).1 f
  by_cases hregion : x ∈ P.plane.faceRegion f
  · rcases hxa with hpos | hedge | ⟨g, hga, hxg⟩
    · exact False.elim ((Set.disjoint_left.mp htraceAvoid.1)
        (Or.inl ⟨a, hpos.symm⟩) hregion)
    · rcases hedge with ⟨b, hab, hxarc, _, _⟩
      exact False.elim ((Set.disjoint_left.mp htraceAvoid.1)
        (Or.inr ⟨a, b, hab, hxarc⟩) hregion)
    · by_cases hgf : g = f
      · subst g
        exact hga
      · exact False.elim (Set.disjoint_left.mp (P.plane.region_disjoint hgf) hxg hregion)
  · have hfront : x ∈ frontier (P.plane.faceRegion f) := by
      rw [frontier, (P.plane.region_open f).interior_eq]
      exact ⟨hxf, hregion⟩
    have hxtrace := htraceAvoid.2 hfront
    rcases hxa with hpos | hedge | hface
    · rw [hpos] at hfront
      rw [P.plane.face_boundary f] at hfront
      rcases hfront with hrest | h20
      · rcases hrest with h01 | h12
        · have h := (P3767T1VertexEdgeIncidence P.plane a).2
            (P.plane.faceVertex f 0) (P.plane.faceVertex f 1)
            (P.plane.face_edges f 0 1 (by decide)) h01
          rcases h with h | h
          · exact ⟨0, h.symm⟩
          · exact ⟨1, h.symm⟩
        · have h := (P3767T1VertexEdgeIncidence P.plane a).2
            (P.plane.faceVertex f 1) (P.plane.faceVertex f 2)
            (P.plane.face_edges f 1 2 (by decide)) h12
          rcases h with h | h
          · exact ⟨1, h.symm⟩
          · exact ⟨2, h.symm⟩
      · have h : a = P.plane.faceVertex f 2 ∨ a = P.plane.faceVertex f 0 := by
          exact (P3767T1VertexEdgeIncidence P.plane a).2
            (P.plane.faceVertex f 2) (P.plane.faceVertex f 0)
            (P.plane.face_edges f 2 0 (by decide)) h20
        rcases h with h | h
        · exact ⟨2, h.symm⟩
        · exact ⟨0, h.symm⟩
    · rcases hedge with ⟨b, hab, hxab, hxa', hxb'⟩
      rw [P.plane.face_boundary f] at hfront
      rcases hfront with hrest | h20
      · rcases hrest with h01 | h12
        · have hlabel : a = P.plane.faceVertex f 0 ∨ a = P.plane.faceVertex f 1 := by
            exact hpairLabel a b (P.plane.faceVertex f 0) (P.plane.faceVertex f 1)
              hab (P.plane.face_edges f 0 1 (by decide)) x ⟨hxab, h01⟩ hxa' hxb'
          rcases hlabel with h | h
          · exact ⟨0, h.symm⟩
          · exact ⟨1, h.symm⟩
        · have hlabel : a = P.plane.faceVertex f 1 ∨ a = P.plane.faceVertex f 2 := by
            exact hpairLabel a b (P.plane.faceVertex f 1) (P.plane.faceVertex f 2)
              hab (P.plane.face_edges f 1 2 (by decide)) x ⟨hxab, h12⟩ hxa' hxb'
          rcases hlabel with h | h
          · exact ⟨1, h.symm⟩
          · exact ⟨2, h.symm⟩
      · have hlabel : a = P.plane.faceVertex f 2 ∨ a = P.plane.faceVertex f 0 := by
          exact hpairLabel a b (P.plane.faceVertex f 2) (P.plane.faceVertex f 0)
            hab (P.plane.face_edges f 2 0 (by decide)) x ⟨hxab, h20⟩ hxa' hxb'
        rcases hlabel with h | h
        · exact ⟨2, h.symm⟩
        · exact ⟨0, h.symm⟩
    · rcases hface with ⟨g, hga, hxg⟩
      exact False.elim (Set.disjoint_left.mp
        ((P3767T1FixedFaceComponents P.plane).1 g).1 hxtrace hxg)

private theorem hvertexStar :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
    let U : ι → Set (Real × Real) := P3776T1OpenStar P
    ∀ [Nontrivial ι], ∀ (a : ι), ∀ (b : ι), P.plane.position b ∈ U a ↔ a = b := by
  classical
  intro ι P U hnontriv a b
  constructor
  · intro h
    rcases h with hpos | hedge | hface
    · exact (P.plane.position_injective hpos).symm
    · rcases hedge with ⟨c, hac, hbc, hxa, hxb⟩
      have hend := (P3767T1VertexEdgeIncidence P.plane b).2 a c hac hbc
      rcases hend with h | h
      · exact (hxa (congrArg P.plane.position h)).elim
      · exact (hxb (congrArg P.plane.position h)).elim
    · rcases hface with ⟨f, hfa, hfb⟩
      exact False.elim ((Set.disjoint_left.mp
        ((P3767T1FixedFaceComponents P.plane).1 f).1)
        (Or.inl ⟨b, rfl⟩) hfb)
  · rintro rfl
    exact Or.inl rfl

private theorem hEdgeNoOther :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
    let U : ι → Set (Real × Real) := P3776T1OpenStar P
    ∀ [Nontrivial ι], (∀ (a : ι), ∀ (b : ι), ∀ (c : ι), ∀ (d : ι), (P.plane.adjacent a b) →
        ((P.plane.adjacent c d) → (∀ (x : Real × Real), (x ∈ P.plane.edgeArc a b ∩
        P.plane.edgeArc c d) → ((x ≠ P.plane.position a) → ((x ≠ P.plane.position b) → (a = c ∨ a
        = d)))))) → (∀ (a : ι), ∀ (b : ι), P.plane.adjacent a b → ∀ x ∈ P.plane.edgeArc a b, ∀ (c
            : ι), c ≠ a → c ≠ b → x ∉ U c) := by
  classical
  intro ι P U hnontriv hpairLabel a b hab x hx c hca hcb hc
  rcases hc with hpos | hedge | hface
  · rw [hpos] at hx
    have hend := (P3767T1VertexEdgeIncidence P.plane c).2 a b hab hx
    rcases hend with h | h
    · exact hca h
    · exact hcb h
  · rcases hedge with ⟨d', hcd, hxc, hxc', hxd'⟩
    have hlabel := hpairLabel c d' a b hcd hab x ⟨hxc, hx⟩ hxc' hxd'
    rcases hlabel with h | h
    · exact hca h
    · exact hcb h
  · rcases hface with ⟨f, hfa, hxf⟩
    exact (Set.disjoint_left.mp ((P3767T1FixedFaceComponents P.plane).1 f).1)
      (Or.inr ⟨a, b, hab, hx⟩) hxf

private theorem hlf :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
    let U : ι → Set (Real × Real) := P3776T1OpenStar P
    (Nontrivial ι ∧ (∀ (f : P.plane.Face), IsCompact (closure (P.plane.faceRegion f))) ∧ (∀ (K :
        Set (ℝ × ℝ)), IsCompact K → {f : P.plane.Face | (K ∩ closure (P.plane.faceRegion
        f)).Nonempty}.Finite) ∧ (∀ (x : ℝ × ℝ), ∃ (f : P.plane.Face), x ∈ closure
        (P.plane.faceRegion f)) ∧ (∀ (a : ι), IsOpen (P3776T1OpenStar P a) ∧ IsCompact (closure
        (P3776T1OpenStar P a))) ∧ (∀ (x : ℝ × ℝ), ∃ (a : ι), x ∈ P3776T1OpenStar P a) ∧ (∀ (u
            : ↥P.lattice), ∀ (a : ι), P3776T1OpenStar P (P.shift u a) = (fun (x : ℝ × ℝ) => x +
        GaussianRealPoint (↑u : GaussianInt)) '' P3776T1OpenStar P a) ∧ ∀ (u : ↥P.lattice), ∀
            (v : ↥P.lattice), ∀ (a : ι), P.shift u a = P.shift v a → u = v) → ((∀ (a : ι), ∀ (x :
            Real × Real), (x ∈ U a) → (∃ f, x ∈ closure (P.plane.faceRegion f) ∧ ∃ i,
        P.plane.faceVertex f i = a)) → (LocallyFinite U)) := by
  classical
  intro ι P U hgeom hstarFace x
  refine ⟨Metric.ball x (1:Real), Metric.ball_mem_nhds x (by norm_num), ?_⟩
  let K := Metric.closedBall x (1:Real)
  have hKcompact : IsCompact K := isCompact_closedBall x 1
  let F := {f : P.plane.Face | (K ∩ closure (P.plane.faceRegion f)).Nonempty}
  have hF : F.Finite := hgeom.2.2.1 K hKcompact
  let S : Set ι := {a | (U a ∩ Metric.ball x 1).Nonempty}
  have hS : S ⊆ ⋃ f ∈ F, Set.range (P.plane.faceVertex f) := by
    intro a ha
    change (U a ∩ Metric.ball x 1).Nonempty at ha
    obtain ⟨z, ⟨hza, hzB⟩⟩ := ha
    obtain ⟨f, hzf, i, hia⟩ := hstarFace a z hza
    have hzK : z ∈ K := Metric.mem_closedBall.mpr (le_of_lt hzB)
    exact Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨by
      change (K ∩ closure (P.plane.faceRegion f)).Nonempty
      exact ⟨z, hzK, hzf⟩, ⟨i, hia⟩⟩⟩
  have hfinite : S.Finite := by
    exact Set.Finite.subset (hF.biUnion fun f _ => Set.finite_range (P.plane.faceVertex f)) hS
  simpa [S] using hfinite

private theorem hne :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
    let U : ι → Set (Real × Real) := P3776T1OpenStar P
    ∀ [Nontrivial ι], ∀ a, (U a)ᶜ.Nonempty := by
  classical
  intro ι P U hnontriv a
  obtain ⟨b, hba⟩ := exists_ne a
  refine ⟨P.plane.position b, ?_⟩
  intro hb
  rcases hb with hpos | hedge | hface
  · exact hba (P.plane.position_injective hpos)
  · rcases hedge with ⟨c, hac, hbc, hxc, hxd⟩
    have hend := (P3767T1VertexEdgeIncidence P.plane b).2 a c hac hbc
    rcases hend with h | h
    · exact hxc (congrArg P.plane.position h)
    · exact hxd (congrArg P.plane.position h)
  · rcases hface with ⟨f, hfa, hfb⟩
    have hdis := (P3767T1FixedFaceComponents P.plane).1 f |>.1
    exact (Set.disjoint_left.mp hdis) (Or.inl ⟨b, rfl⟩) hfb

private theorem hdistShift :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
    let U : ι → Set (Real × Real) := P3776T1OpenStar P
    (Nontrivial ι ∧ (∀ (f : P.plane.Face), IsCompact (closure (P.plane.faceRegion f))) ∧ (∀ (K :
        Set (ℝ × ℝ)), IsCompact K → {f : P.plane.Face | (K ∩ closure (P.plane.faceRegion
        f)).Nonempty}.Finite) ∧ (∀ (x : ℝ × ℝ), ∃ (f : P.plane.Face), x ∈ closure
        (P.plane.faceRegion f)) ∧ (∀ (a : ι), IsOpen (P3776T1OpenStar P a) ∧ IsCompact (closure
        (P3776T1OpenStar P a))) ∧ (∀ (x : ℝ × ℝ), ∃ (a : ι), x ∈ P3776T1OpenStar P a) ∧ (∀ (u
            : ↥P.lattice), ∀ (a : ι), P3776T1OpenStar P (P.shift u a) = (fun (x : ℝ × ℝ) => x +
        GaussianRealPoint (↑u : GaussianInt)) '' P3776T1OpenStar P a) ∧ ∀ (u : ↥P.lattice), ∀
            (v : ↥P.lattice), ∀ (a : ι), P.shift u a = P.shift v a → u = v) → (
    let d : ι → (Real × Real) → Real := fun a x => Metric.infDist x (U a)ᶜ
    ∀ (u : ↥P.lattice), ∀ (a : ι), ∀ (x : ℝ × ℝ), d (P.shift u a) (x + GaussianRealPoint (↑u :
        GaussianInt)) = d a x) := by
  classical
  intro ι P U hgeom d u a x
  let Φ : (Real × Real) → (Real × Real) := fun y => y + GaussianRealPoint u
  have hIso : Isometry Φ := by
    intro y z
    change edist (y.1 + (GaussianRealPoint u).1, y.2 + (GaussianRealPoint u).2)
      (z.1 + (GaussianRealPoint u).1, z.2 + (GaussianRealPoint u).2) = edist y z
    have h1 : dist (y.1 + (GaussianRealPoint u).1) (z.1 + (GaussianRealPoint u).1) =
        dist y.1 z.1 := by
      rw [Real.dist_eq, Real.dist_eq]
      congr 1; ring
    have h2 : dist (y.2 + (GaussianRealPoint u).2) (z.2 + (GaussianRealPoint u).2) =
        dist y.2 z.2 := by
      rw [Real.dist_eq, Real.dist_eq]
      congr 1; ring
    rw [Prod.edist_eq, Prod.edist_eq, edist_dist, edist_dist, edist_dist, edist_dist,
      h1, h2]
  have hU : U (P.shift u a) = Φ '' U a := hgeom.2.2.2.2.2.2.1 u a
  have hcomp : (U (P.shift u a))ᶜ = Φ '' (U a)ᶜ := by
    ext y
    constructor
    · intro hy
      refine ⟨y - GaussianRealPoint u, ?_, ?_⟩
      · intro hya
        apply hy
        rw [hU]
        exact ⟨y - GaussianRealPoint u, hya, by dsimp [Φ]; simp⟩
      · dsimp [Φ]
        exact sub_add_cancel y (GaussianRealPoint u)
    · rintro ⟨z, hz, rfl⟩ hy
      apply hz
      rw [hU] at hy
      rcases hy with ⟨w, hw, hwy⟩
      have hwz : w = z := add_right_cancel hwy
      simpa [hwz] using hw
  dsimp [d, Φ]
  rw [hcomp]
  exact Metric.infDist_image hIso

private theorem hsuppAt449 :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
    let U : ι → Set (Real × Real) := P3776T1OpenStar P
    (∀ (f : P.plane.Face), ∀ (x : Real × Real), (x ∈ closure (P.plane.faceRegion f)) → (∀ (a :
        ι), (x ∈ U a) → (∃ i, P.plane.faceVertex f i = a))) → (
    let d : ι → (Real × Real) → Real := fun a x => Metric.infDist x (U a)ᶜ
    let D : (Real × Real) → Real := fun x => ∑ᶠ a, d a x
    (∀ (a : ι), ∀ (x : Real × Real), 0 < d a x ↔ x ∈ U a) → (∀ (f : P.plane.Face), ∀ (x : ℝ × ℝ),
        (x ∈ closure (P.plane.faceRegion f)) → (
    let S : Finset ι := @Finset.image (Fin 3) ι (Classical.decEq ι) (P.plane.faceVertex f)
        Finset.univ
    Function.support (fun a => d a x / D x) ⊆ (S : Set ι)))) := by
  classical
  intro ι P U hfaceStarLabel d D hdpos f x hxf S a ha
  change d a x / D x ≠ 0 at ha
  have hda : d a x ≠ 0 := by
    intro hz
    apply ha
    simp [hz]
  have hdaPos : 0 < d a x :=
    (Metric.infDist_nonneg : 0 ≤ d a x).lt_iff_ne'.2 hda
  obtain ⟨i, hi⟩ := hfaceStarLabel f x hxf a ((hdpos a x).mp hdaPos)
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩

end StarWeightsProof

theorem P3776T1StarWeightsExist {ι : Type} (P : PeriodicTileCore ι) :
    Nonempty (P3776T1StarWeights P) := by
-- BODY
  classical
  let U : ι → Set (Real × Real) := P3776T1OpenStar P
  have hgeom := P3776T1FixedGeometry P
  let hnontriv : Nontrivial ι := hgeom.1
  have hfaceEdge (f : P.plane.Face) (a b : ι) (hab : P.plane.adjacent a b)
      (ha : ∃ i, P.plane.faceVertex f i = a)
      (hb : ∃ i, P.plane.faceVertex f i = b) :
      P.plane.edgeArc a b ⊆ closure (P.plane.faceRegion f) := StarWeightsProof.hfaceEdge ι P f a
          b hab ha hb
  have hstarFace (a : ι) (x : Real × Real) (hx : x ∈ U a) :
      ∃ f, x ∈ closure (P.plane.faceRegion f) ∧
        ∃ i, P.plane.faceVertex f i = a := StarWeightsProof.hstarFace ι P hgeom  hfaceEdge a x hx
  have hpairLabel (a b c d : ι) (hab : P.plane.adjacent a b)
      (hcd : P.plane.adjacent c d) (x : Real × Real)
      (hx : x ∈ P.plane.edgeArc a b ∩ P.plane.edgeArc c d)
      (hxa : x ≠ P.plane.position a) (hxb : x ≠ P.plane.position b) :
      a = c ∨ a = d := StarWeightsProof.hpairLabel ι P a b c d hab hcd x hx hxa hxb
  have hfaceStarLabel (f : P.plane.Face) (x : Real × Real)
      (hxf : x ∈ closure (P.plane.faceRegion f)) (a : ι) (hxa : x ∈ U a) :
      ∃ i, P.plane.faceVertex f i = a := StarWeightsProof.hfaceStarLabel ι P  hpairLabel f x hxf
          a hxa
  have hvertexStar (a b : ι) :
      P.plane.position b ∈ U a ↔ a = b := StarWeightsProof.hvertexStar ι P  a b
  have hEdgeNoOther (a b : ι) (hab : P.plane.adjacent a b)
      (x : Real × Real) (hx : x ∈ P.plane.edgeArc a b) (c : ι)
      (hca : c ≠ a) (hcb : c ≠ b) : x ∉ U c := StarWeightsProof.hEdgeNoOther ι P  hpairLabel a b
          hab x hx c hca hcb
  have hlf : LocallyFinite U := StarWeightsProof.hlf ι P hgeom hstarFace
  have hne : ∀ a, (U a)ᶜ.Nonempty := StarWeightsProof.hne ι P
  let d : ι → (Real × Real) → Real := fun a x => Metric.infDist x (U a)ᶜ
  let D : (Real × Real) → Real := fun x => ∑ᶠ a, d a x
  have hdpos (a : ι) (x : Real × Real) : 0 < d a x ↔ x ∈ U a := by
    change 0 < Metric.infDist x (P3776T1OpenStar P a)ᶜ ↔
      x ∈ P3776T1OpenStar P a
    simpa only [Set.notMem_compl_iff] using
      (((hgeom.2.2.2.2.1 a).1).isClosed_compl.notMem_iff_infDist_pos (hne a)).symm
  have hdsupp (a : ι) : Function.support (d a) = U a := by
    ext x
    change d a x ≠ 0 ↔ x ∈ U a
    rw [← (Metric.infDist_nonneg : 0 ≤ d a x).lt_iff_ne']
    exact hdpos a x
  have hld : LocallyFinite (fun a => Function.support (d a)) := by
    simpa only [hdsupp] using hlf
  have hdc (a : ι) : Continuous (d a) := Metric.continuous_infDist_pt _
  have hDc : Continuous D := by
    exact continuous_finsum hdc hld
  have hDpos (x : Real × Real) : 0 < D x := by
    apply finsum_pos (fun a => Metric.infDist_nonneg)
    · obtain ⟨a, ha⟩ := hgeom.2.2.2.2.2.1 x
      exact ⟨a, (hdpos a x).2 ha⟩
    · exact hld.point_finite x
  have hsum (x : Real × Real) : (∑ᶠ a, d a x / D x) = 1 := by
    change (∑ᶠ a, d a x / (∑ᶠ j, d j x)) = 1
    simp_rw [div_eq_mul_inv]
    rw [← finsum_mul (fun a => d a x) ((∑ᶠ j, d j x)⁻¹)]
    exact mul_inv_cancel₀ (ne_of_gt (hDpos x))
  have hweight_cont (a : ι) : Continuous (fun x => d a x / D x) :=
    (hdc a).div hDc (fun x => ne_of_gt (hDpos x))
  have hshiftInv (u : P.lattice) (a : ι) : P.shift (-u) (P.shift u a) = a := by
    rw [← P.shift_add, neg_add_cancel, P.shift_zero]
  have hshiftInv' (u : P.lattice) (a : ι) : P.shift u (P.shift (-u) a) = a := by
    rw [← P.shift_add, add_neg_cancel, P.shift_zero]
  have hshiftBij (u : P.lattice) : Function.Bijective (P.shift u) := by
    constructor
    · intro a b hab
      have h := congrArg (P.shift (-u)) hab
      simpa only [hshiftInv] using h
    · intro b
      exact ⟨P.shift (-u) b, hshiftInv' u b⟩
  have hdistShift (u : P.lattice) (a : ι) (x : Real × Real) :
      d (P.shift u a) (x + GaussianRealPoint u) = d a x := StarWeightsProof.hdistShift ι P hgeom
          u a x
  have hDShift (u : P.lattice) (x : Real × Real) :
      D (x + GaussianRealPoint u) = D x := by
    change (∑ᶠ a, d a (x + GaussianRealPoint u)) = _
    rw [← finsum_comp (P.shift u) (hshiftBij u)]
    simp_rw [hdistShift]
    rfl
  refine ⟨{
    weight := fun a x => d a x / D x
    continuous := hweight_cont
    nonnegative := ?_
    positive_iff := ?_
    face_simplex := ?_
    edge_support := ?_
    vertex_value := ?_
    periodic := ?_
  }⟩
  · intro a x
    exact (div_nonneg (Metric.infDist_nonneg) (le_of_lt (hDpos x)))
  · intro a x
    rw [div_pos_iff_of_pos_right (hDpos x)]
    exact hdpos a x
  · intro f x hxf
    change (∀ i : Fin 3, 0 ≤ d (P.plane.faceVertex f i) x / D x) ∧
      (∑ i : Fin 3, d (P.plane.faceVertex f i) x / D x) = 1
    constructor
    · intro i
      exact div_nonneg Metric.infDist_nonneg (le_of_lt (hDpos x))
    · let S : Finset ι := @Finset.image (Fin 3) ι (Classical.decEq ι) (P.plane.faceVertex f)
        Finset.univ
      have hsupp : Function.support (fun a => d a x / D x) ⊆ (S : Set ι) :=
          StarWeightsProof.hsuppAt449 ι P hfaceStarLabel hdpos f x hxf
      have hinj : Set.InjOn (P.plane.faceVertex f) (↑(Finset.univ : Finset (Fin 3))) := by
        intro i hi j hj hij
        exact (P.plane.face_vertices_distinct f) hij
      have htotal := hsum x
      rw [finsum_eq_sum_of_support_subset _ hsupp] at htotal
      rw [Finset.sum_image hinj] at htotal
      simpa [S] using htotal
  · intro a b hab x hx c hca hcb
    have hn : x ∉ U c := hEdgeNoOther a b hab x hx c hca hcb
    have hnpos : ¬ 0 < d c x := fun hp => hn ((hdpos c x).mp hp)
    have hzero : d c x = 0 := le_antisymm (le_of_not_gt hnpos) Metric.infDist_nonneg
    simp [hzero]
  · intro a b
    by_cases hab : a = b
    · subst b
      have hzero (c : ι) (hca : c ≠ a) : d c (P.plane.position a) = 0 := by
        have hn : ¬ 0 < d c (P.plane.position a) := by
          intro hp
          exact hca ((hvertexStar c a).mp ((hdpos c (P.plane.position a)).mp hp))
        exact le_antisymm (le_of_not_gt hn) Metric.infDist_nonneg
      have hsupp : Function.support (fun c => d c (P.plane.position a) / D (P.plane.position a)) ⊆
          ({a} : Finset ι) := by
        intro c hc
        by_contra hca
        have hca' : c ≠ a := by simpa using hca
        have hz := hzero c hca'
        change d c (P.plane.position a) / D (P.plane.position a) ≠ 0 at hc
        simp [hz] at hc
      have htotal := hsum (P.plane.position a)
      rw [finsum_eq_sum_of_support_subset _ hsupp] at htotal
      simpa using htotal
    · have hzero : d a (P.plane.position b) = 0 := by
        have hn : ¬ 0 < d a (P.plane.position b) := by
          intro hp
          exact hab ((hvertexStar a b).mp ((hdpos a (P.plane.position b)).mp hp))
        exact le_antisymm (le_of_not_gt hn) Metric.infDist_nonneg
      simp [hzero, hab]
  · intro u a x
    rw [hdistShift, hDShift]

end ApollonianSuperharmonic

end
