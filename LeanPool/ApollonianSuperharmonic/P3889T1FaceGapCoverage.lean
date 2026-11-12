/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Positivity

public import LeanPool.ApollonianSuperharmonic.P3861T1FacialDomains
public import LeanPool.ApollonianSuperharmonic.P3889T1TwoRaySectorDecomposition
public import LeanPool.ApollonianSuperharmonic.P3776T1FixedGeometry
public import Mathlib.Analysis.Normed.Module.Connected

-- [TABLET NODE: P3889T1FaceGapCoverage]

/-!
# P3889T1FaceGapCoverage

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FaceGapProof

private theorem hfrontTrace :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D),
        let T := Set.range D.position ∪
          {q | ∃ c d, P.plane.adjacent c d ∧ q ∈ D.edgeArc c d}
        ∀ (f : P.plane.Face), frontier (F.region f) ⊆ T ) := by
  classical
  intro ι P D F T f
  rw [F.region_frontier]
  rintro q ((hq | hq) | hq)
  · exact Or.inr ⟨_, _, P.plane.face_edges f 0 1 (by decide), hq⟩
  · exact Or.inr ⟨_, _, P.plane.face_edges f 1 2 (by decide), hq⟩
  · exact Or.inr ⟨_, _, P.plane.face_edges f 2 0 (by decide), hq⟩

private theorem hfaceFrontier :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), (∀ (c : ι), ∀ (d : ι),
            P.plane.adjacent c d → c ≠ a → d ≠ a → Disjoint (D.edgeArc c d) (Metric.ball
            (D.position a) r)) → (
        let x := D.position a
        let B := Metric.ball x r
        ∀ (f : P.plane.Face), ∀ (i : Fin (3 : ℕ)), P.plane.faceVertex f i = a → ∃ (c : ι) (d :
            ι), c ≠ a ∧ d ≠ a ∧ c ≠ d ∧ P.plane.adjacent a c ∧ P.plane.adjacent a d ∧ (∃ (j : Fin
            (3 : ℕ)), P.plane.faceVertex f j = c) ∧ (∃ (j : Fin (3 : ℕ)), P.plane.faceVertex f j
            = d) ∧ frontier (F.region f) ∩ B = (D.edgeArc a c ∪ D.edgeArc a d) ∩ B) ) := by
  classical
  intro ι P D F a r hforeign x B f i hi
  have hinj := P.plane.face_vertices_distinct f
  have hvertex_ne (j : Fin 3) (hji : j ≠ i) :
      P.plane.faceVertex f j ≠ a := by
    intro h
    exact hji (hinj (h.trans hi.symm))
  fin_cases i
  · refine ⟨P.plane.faceVertex f 1, P.plane.faceVertex f 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hvertex_ne 1 (by decide)
    · exact hvertex_ne 2 (by decide)
    · exact hinj.ne (by decide)
    · rw [← hi]; exact P.plane.face_edges f 0 1 (by decide)
    · rw [← hi]; exact P.plane.face_edges f 0 2 (by decide)
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · rw [← hi, F.region_frontier,
        D.edgeArc_symmetric (P.plane.faceVertex f 2) (P.plane.faceVertex f 0)]
      have h12 : Disjoint (D.edgeArc (P.plane.faceVertex f 1)
          (P.plane.faceVertex f 2)) B := by
        apply hforeign _ _ (P.plane.face_edges f 1 2 (by decide))
        · exact hvertex_ne 1 (by decide)
        · exact hvertex_ne 2 (by decide)
      ext q
      simp only [Set.mem_inter_iff, Set.mem_union]
      constructor
      · rintro ⟨(h01 | h12q) | h20, hqB⟩
        · exact ⟨Or.inl h01, hqB⟩
        · exact (Set.disjoint_left.mp h12 h12q hqB).elim
        · exact ⟨Or.inr h20, hqB⟩
      · rintro ⟨h01 | h20, hqB⟩
        · exact ⟨Or.inl (Or.inl h01), hqB⟩
        · exact ⟨Or.inr h20, hqB⟩
  · refine ⟨P.plane.faceVertex f 0, P.plane.faceVertex f 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hvertex_ne 0 (by decide)
    · exact hvertex_ne 2 (by decide)
    · exact hinj.ne (by decide)
    · rw [← hi]; exact P.plane.face_edges f 1 0 (by decide)
    · rw [← hi]; exact P.plane.face_edges f 1 2 (by decide)
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
    · rw [← hi, F.region_frontier,
        D.edgeArc_symmetric (P.plane.faceVertex f 0) (P.plane.faceVertex f 1)]
      have h02 : Disjoint (D.edgeArc (P.plane.faceVertex f 2)
          (P.plane.faceVertex f 0)) B := by
        apply hforeign _ _ (P.plane.face_edges f 2 0 (by decide))
        · exact hvertex_ne 2 (by decide)
        · exact hvertex_ne 0 (by decide)
      ext q
      simp only [Set.mem_inter_iff, Set.mem_union]
      constructor
      · rintro ⟨(h01 | h12) | h20, hqB⟩
        · exact ⟨Or.inl h01, hqB⟩
        · exact ⟨Or.inr h12, hqB⟩
        · exact (Set.disjoint_left.mp h02 h20 hqB).elim
      · rintro ⟨h01 | h12, hqB⟩
        · exact ⟨Or.inl (Or.inl h01), hqB⟩
        · exact ⟨Or.inl (Or.inr h12), hqB⟩
  · refine ⟨P.plane.faceVertex f 0, P.plane.faceVertex f 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hvertex_ne 0 (by decide)
    · exact hvertex_ne 1 (by decide)
    · exact hinj.ne (by decide)
    · rw [← hi]; exact P.plane.face_edges f 2 0 (by decide)
    · rw [← hi]; exact P.plane.face_edges f 2 1 (by decide)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · rw [← hi, F.region_frontier,
        D.edgeArc_symmetric (P.plane.faceVertex f 1) (P.plane.faceVertex f 2)]
      have h01 : Disjoint (D.edgeArc (P.plane.faceVertex f 0)
          (P.plane.faceVertex f 1)) B := by
        apply hforeign _ _ (P.plane.face_edges f 0 1 (by decide))
        · exact hvertex_ne 0 (by decide)
        · exact hvertex_ne 1 (by decide)
      ext q
      simp only [Set.mem_inter_iff, Set.mem_union]
      constructor
      · rintro ⟨(h01q | h12) | h20, hqB⟩
        · exact (Set.disjoint_left.mp h01 h01q hqB).elim
        · exact ⟨Or.inr h12, hqB⟩
        · exact ⟨Or.inl h20, hqB⟩
      · rintro ⟨h20 | h12, hqB⟩
        · exact ⟨Or.inr h20, hqB⟩
        · exact ⟨Or.inl (Or.inr h12), hqB⟩

private theorem hpNotRays :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a :
            ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ), ((Set.range D.position ∪ {p : ℝ × ℝ | ∃ (c : ι) (d
            : ι), P.plane.adjacent c d ∧ p ∈ D.edgeArc c d}) ∩ Metric.ball (D.position a) r =
            Metric.ball (D.position a) r ∩ {p : ℝ × ℝ | ∃ (c : ι), P.plane.adjacent a c ∧ ∃ (t :
            ℝ), (0 : ℝ) ≤ t ∧ p = D.position a + t • u c}) → (∀ (p : ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        let T := Set.range D.position ∪
          {q | ∃ c d, P.plane.adjacent c d ∧ q ∈ D.edgeArc c d}
        (p ∉ T) → (p ∉ B ∩ {q | ∃ c, P.plane.adjacent a c ∧ ∃ t : Real, 0 ≤ t ∧ q = x + t • u
            c})) ) := by
  classical
  intro ι P D a r u htrace p x B T hpNotT h
  have hpTrace : p ∈ (Set.range D.position ∪
      {q | ∃ c d, P.plane.adjacent c d ∧ q ∈ D.edgeArc c d}) ∩
        Metric.ball (D.position a) r := by
    change p ∈ Metric.ball (D.position a) r ∩
      {q | ∃ c, P.plane.adjacent a c ∧
        ∃ t : Real, 0 ≤ t ∧ q = D.position a + t • u c} at h
    rw [htrace]
    exact h
  apply hpNotT
  change p ∈ Set.range D.position ∪
    {q | ∃ c d, P.plane.adjacent c d ∧ q ∈ D.edgeArc c d}
  exact hpTrace.1

private theorem hpNotRay :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a :
            ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ), ∀ (p : ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        (p ∈ B) → ((p ∉ B ∩ {q | ∃ c, P.plane.adjacent a c ∧ ∃ t : Real, 0 ≤ t ∧ q = x + t • u
            c}) → (∀ (c : ι), P.plane.adjacent a c → p ∉ {q : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ q
            = x + t • u c})) ) := by
  classical
  intro ι P D a r u p x B hpB hpNotRays c hac h
  apply hpNotRays
  refine ⟨hpB, c, hac, ?_⟩
  simpa [x] using h

private theorem hincidentSectorData :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ), (∀ (c : ι),
            P.plane.adjacent a c → D.edgeArc a c ∩ Metric.ball (D.position a) r = Metric.ball
            (D.position a) r ∩ {p : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ p = D.position a + t • u c})
            → ((∀ (c : ι), ∀ (d : ι), P.plane.adjacent a c → P.plane.adjacent a d → c ≠ d →
            Nonempty (P3889T1TwoRaySectorDecomposition (D.position a) r (u c) (u d))) → (
        let x := D.position a
        let B := Metric.ball x r
        (∀ (f : P.plane.Face), ∀ (i : Fin 3), (P.plane.faceVertex f i = a) → (∃ c d, c ≠ a ∧ d ≠
            a ∧ c ≠ d ∧ P.plane.adjacent a c ∧ P.plane.adjacent a d ∧ (∃ j, P.plane.faceVertex f
            j = c) ∧ (∃ j, P.plane.faceVertex f j = d) ∧ frontier (F.region f) ∩ B = (D.edgeArc a
            c ∪ D.edgeArc a d) ∩ B)) → (∀ (f : P.plane.Face), ∀ (i : Fin (3 : ℕ)),
            P.plane.faceVertex f i = a → ∃ (c : ι) (d : ι), c ≠ a ∧ d ≠ a ∧ c ≠ d ∧
            P.plane.adjacent a c ∧ P.plane.adjacent a d ∧ (∃ (j : Fin (3 : ℕ)),
            P.plane.faceVertex f j = c) ∧ (∃ (j : Fin (3 : ℕ)), P.plane.faceVertex f j = d) ∧
            frontier (F.region f) ∩ B = B ∩ {q : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ q = x + t • u
            c} ∪ B ∩ {q : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ q = x + t • u d} ∧ Nonempty
            (P3889T1TwoRaySectorDecomposition x r (u c) (u d))))) ) := by
  classical
  intro ι P D F a r u hedge hsectors x B hfaceFrontier f i hi
  obtain ⟨c, d, hca, hda, hcd, hac, had, hci, hdi, hfront⟩ := hfaceFrontier f i hi
  obtain ⟨S⟩ := hsectors c d hac had hcd
  refine ⟨c, d, hca, hda, hcd, hac, had, hci, hdi, ?_, ⟨S⟩⟩
  rw [hfront, Set.union_inter_distrib_right, hedge c hac, hedge d had]

private theorem hxray :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a :
            ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        ∀ (c : ι), (x ∈ B) → (x ∈ (B ∩ {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c})) ) := by
  classical
  intro ι P D a r u x B c hxB
  refine ⟨hxB, 0, le_rfl, ?_⟩
  simp

private theorem hxfront :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        ∀ (f : P.plane.Face), ∀ (c : ι), ∀ (d : ι), (frontier (F.region f) ∩ B = B ∩ {q : ℝ × ℝ |
            ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ q = x + t • u c} ∪ B ∩ {q : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧
            q = x + t • u d}) → (
        let U := F.region f
        (x ∈ (B ∩ {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c})) → (x ∈ frontier U)) ) := by
  classical
  intro ι P D F a r u x B f c d hfront U hxray
  have hx' : x ∈ frontier U ∩ B := by rw [hfront]; exact Or.inl hxray
  exact hx'.1

private theorem rayFront :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        ∀ (f : P.plane.Face), ∀ (c : ι), ∀ (d : ι), (frontier (F.region f) ∩ B = B ∩ {q : ℝ × ℝ |
            ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ q = x + t • u c} ∪ B ∩ {q : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧
            q = x + t • u d}) → (
        let U := F.region f
        ∀ q ∈ B, q ∈ {q : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ q = x + t • u c} ∪ {q : ℝ × ℝ | ∃ (t :
            ℝ), (0 : ℝ) ≤ t ∧ q = x + t • u d} → q ∈ frontier U) ) := by
  classical
  intro ι P D F a r u x B f c d hfront U q hqB hqRay
  have heq := congrArg (fun s : Set (Real × Real) => q ∈ s) hfront
  have hq' : q ∈ frontier U ∩ B := by
    apply heq.mpr
    rcases hqRay with hqRay | hqRay
    · exact Or.inl ⟨hqB, hqRay⟩
    · exact Or.inr ⟨hqB, hqRay⟩
  exact hq'.1

private theorem hmeetU :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ((0 : ℝ) < r) → (
        let x := D.position a
        let B := Metric.ball x r
        ∀ (f : P.plane.Face),
        let U := F.region f
        (x ∈ frontier U) → ((B ∩ U).Nonempty)) ) := by
  classical
  intro ι P D F a r hr x B f U hxfront
  have hxcl : x ∈ closure U := frontier_subset_closure hxfront
  obtain ⟨q, hq⟩ := (mem_closure_iff_nhds.mp hxcl) B
    (Metric.ball_mem_nhds x hr)
  exact ⟨q, hq⟩

private theorem hxfrontV :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι),
        let x := D.position a
        ∀ (f : P.plane.Face),
        let U := F.region f
        let V := (closure U)ᶜ
        (x ∈ frontier U) → (x ∈ frontier V) ) := by
  classical
  intro ι P D F a x f U V hxfront
  rw [F.exterior_frontier]
  exact hxfront

private theorem hmeetV :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ((0 : ℝ) < r) → (
        let x := D.position a
        let B := Metric.ball x r
        ∀ (f : P.plane.Face),
        let U := F.region f
        let V := (closure U)ᶜ
        (x ∈ frontier V) → ((B ∩ V).Nonempty)) ) := by
  classical
  intro ι P D F a r hr x B f U V hxfrontV
  have hxcl : x ∈ closure V := frontier_subset_closure hxfrontV
  obtain ⟨q, hq⟩ := (mem_closure_iff_nhds.mp hxcl) B
    (Metric.ball_mem_nhds x hr)
  exact ⟨q, hq⟩

private theorem hLsub :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a :
            ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        ∀ (c : ι), ∀ (d : ι), ∀ (S : P3889T1TwoRaySectorDecomposition x r (u c) (u d)), S.left
            ⊆ B \ ({q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c} ∪ {q | ∃ t : Real, 0 ≤ t ∧ q = x + t
            • u d}) ) := by
  classical
  intro ι P D a r u x B c d S
  rw [← S.cover]
  exact Set.subset_union_left

private theorem hRsub :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a :
            ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        ∀ (c : ι), ∀ (d : ι), ∀ (S : P3889T1TwoRaySectorDecomposition x r (u c) (u d)), S.right
            ⊆ B \ ({q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c} ∪ {q | ∃ t : Real, 0 ≤ t ∧ q = x + t
            • u d}) ) := by
  classical
  intro ι P D a r u x B c d S
  rw [← S.cover]
  exact Set.subset_union_right

private theorem hLavoid :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        ∀ (f : P.plane.Face), ∀ (c : ι), ∀ (d : ι), (frontier (F.region f) ∩ B = B ∩ {q : ℝ × ℝ |
            ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ q = x + t • u c} ∪ B ∩ {q : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧
            q = x + t • u d}) → (∀ (S : P3889T1TwoRaySectorDecomposition x r (u c) (u d)),
        let U := F.region f
        (S.left ⊆ B \ ({q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c} ∪ {q | ∃ t : Real, 0 ≤ t ∧ q = x
            + t • u d})) → (Disjoint S.left (frontier U))) ) := by
  classical
  intro ι P D F a r u x B f c d hfront S U hLsub
  apply Set.disjoint_left.mpr
  intro q hq hqf
  have hqB := (hLsub hq).1
  have hqRay : q ∈ ({q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c} ∪
      {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u d}) := by
    have hq' : (q ∈ B ∩ {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c}) ∨
        (q ∈ B ∩ {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u d}) := by
      have heq := congrArg (fun s : Set (Real × Real) => q ∈ s) hfront
      simpa only [Set.mem_union, Set.mem_inter_iff] using heq.mp ⟨hqf, hqB⟩
    rcases hq' with hq' | hq'
    · exact Or.inl hq'.2
    · exact Or.inr hq'.2
  exact (hLsub hq).2 hqRay

private theorem hRavoid :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        ∀ (f : P.plane.Face), ∀ (c : ι), ∀ (d : ι), (frontier (F.region f) ∩ B = B ∩ {q : ℝ × ℝ |
            ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ q = x + t • u c} ∪ B ∩ {q : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧
            q = x + t • u d}) → (∀ (S : P3889T1TwoRaySectorDecomposition x r (u c) (u d)),
        let U := F.region f
        (S.right ⊆ B \ ({q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c} ∪ {q | ∃ t : Real, 0 ≤ t ∧ q =
            x + t • u d})) → (Disjoint S.right (frontier U))) ) := by
  classical
  intro ι P D F a r u x B f c d hfront S U hRsub
  apply Set.disjoint_left.mpr
  intro q hq hqf
  have hqB := (hRsub hq).1
  have hqRay : q ∈ ({q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c} ∪
      {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u d}) := by
    have hq' : (q ∈ B ∩ {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c}) ∨
        (q ∈ B ∩ {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u d}) := by
      have heq := congrArg (fun s : Set (Real × Real) => q ∈ s) hfront
      simpa only [Set.mem_union, Set.mem_inter_iff] using heq.mp ⟨hqf, hqB⟩
    rcases hq' with hq' | hq'
    · exact Or.inl hq'.2
    · exact Or.inr hq'.2
  exact (hRsub hq).2 hqRay

private theorem hLavoidV :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        ∀ (f : P.plane.Face), ∀ (c : ι), ∀ (d : ι), ∀ (S : P3889T1TwoRaySectorDecomposition x r
            (u c) (u d)),
        let U := F.region f
        let V := (closure U)ᶜ
        (Disjoint S.left (frontier U)) → (Disjoint S.left (frontier V)) ) := by
  classical
  intro ι P D F a r u x f c d S U V hLavoid
  rw [F.exterior_frontier]
  exact hLavoid

private theorem hRavoidV :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        ∀ (f : P.plane.Face), ∀ (c : ι), ∀ (d : ι), ∀ (S : P3889T1TwoRaySectorDecomposition x r
            (u c) (u d)),
        let U := F.region f
        let V := (closure U)ᶜ
        (Disjoint S.right (frontier U)) → (Disjoint S.right (frontier V)) ) := by
  classical
  intro ι P D F a r u x f c d S U V hRavoid
  rw [F.exterior_frontier]
  exact hRavoid

private theorem hUV :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (f : P.plane.Face),
        let U := F.region f
        let V := (closure U)ᶜ
        Disjoint U V ) := by
  classical
  intro ι P D F f U V
  apply Set.disjoint_left.mpr
  intro q hqU hqV
  exact hqV (subset_closure hqU)

private theorem hLpart :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        ∀ (f : P.plane.Face), ∀ (c : ι), ∀ (d : ι), ∀ (S : P3889T1TwoRaySectorDecomposition x r
            (u c) (u d)),
        let U := F.region f
        let V := (closure U)ᶜ
        (Disjoint S.left (frontier U)) → ((IsOpen U) → (S.left ⊆ U ∪ V)) ) := by
  classical
  intro ι P D F a r u x f c d S U V hLavoid hUopen q hq
  by_cases hqU : q ∈ U
  · exact Or.inl hqU
  · right
    by_contra hqV
    have hqcl : q ∈ closure U := by simpa [V] using hqV
    have hqf : q ∈ frontier U := by
      rw [frontier, hUopen.interior_eq]
      exact ⟨hqcl, hqU⟩
    exact (Set.disjoint_left.mp hLavoid hq hqf).elim

private theorem hRpart :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        ∀ (f : P.plane.Face), ∀ (c : ι), ∀ (d : ι), ∀ (S : P3889T1TwoRaySectorDecomposition x r
            (u c) (u d)),
        let U := F.region f
        let V := (closure U)ᶜ
        (Disjoint S.right (frontier U)) → ((IsOpen U) → (S.right ⊆ U ∪ V)) ) := by
  classical
  intro ι P D F a r u x f c d S U V hRavoid hUopen q hq
  by_cases hqU : q ∈ U
  · exact Or.inl hqU
  · right
    by_contra hqV
    have hqcl : q ∈ closure U := by simpa [V] using hqV
    have hqf : q ∈ frontier U := by
      rw [frontier, hUopen.interior_eq]
      exact ⟨hqcl, hqU⟩
    exact (Set.disjoint_left.mp hRavoid hq hqf).elim

private theorem hLchoice :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        ∀ (f : P.plane.Face), ∀ (c : ι), ∀ (d : ι), ∀ (S : P3889T1TwoRaySectorDecomposition x r
            (u c) (u d)),
        let U := F.region f
        let V := (closure U)ᶜ
        (Disjoint S.left (frontier U)) → ((Disjoint S.left (frontier V)) → ((IsOpen U) → ((S.left
            ⊆ U ∪ V) → (S.left ⊆ U ∨ S.left ⊆ V)))) ) := by
  classical
  intro ι P D F a r u x f c d S U V hLavoid hLavoidV hUopen hLpart
  by_cases hm : (S.left ∩ U).Nonempty
  · exact Or.inl (P3767T1BarrierRegionMaximal U (frontier U) S.left
      hUopen subset_rfl S.left_connected.isPreconnected hLavoid hm)
  · right
    obtain ⟨q, hqL⟩ := S.left_connected.nonempty
    have hqV : q ∈ V := by
      rcases hLpart hqL with hqU | hqV
      · exact (hm ⟨q, hqL, hqU⟩).elim
      · exact hqV
    exact P3767T1BarrierRegionMaximal V (frontier V) S.left
      isClosed_closure.isOpen_compl subset_rfl S.left_connected.isPreconnected hLavoidV
      ⟨q, hqL, hqV⟩

private theorem hRchoice :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        ∀ (f : P.plane.Face), ∀ (c : ι), ∀ (d : ι), ∀ (S : P3889T1TwoRaySectorDecomposition x r
            (u c) (u d)),
        let U := F.region f
        let V := (closure U)ᶜ
        (Disjoint S.right (frontier U)) → ((Disjoint S.right (frontier V)) → ((IsOpen U) →
            ((S.right ⊆ U ∪ V) → (S.right ⊆ U ∨ S.right ⊆ V)))) ) := by
  classical
  intro ι P D F a r u x f c d S U V hRavoid hRavoidV hUopen hRpart
  by_cases hm : (S.right ∩ U).Nonempty
  · exact Or.inl (P3767T1BarrierRegionMaximal U (frontier U) S.right
      hUopen subset_rfl S.right_connected.isPreconnected hRavoid hm)
  · right
    obtain ⟨q, hqR⟩ := S.right_connected.nonempty
    have hqV : q ∈ V := by
      rcases hRpart hqR with hqU | hqV
      · exact (hm ⟨q, hqR, hqU⟩).elim
      · exact hqV
    exact P3767T1BarrierRegionMaximal V (frontier V) S.right
      isClosed_closure.isOpen_compl subset_rfl S.right_connected.isPreconnected hRavoidV
      ⟨q, hqR, hqV⟩

private theorem hnotUU :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        ∀ (f : P.plane.Face), ∀ (c : ι), ∀ (d : ι), ∀ (S : P3889T1TwoRaySectorDecomposition x r
            (u c) (u d)),
        let U := F.region f
        let V := (closure U)ᶜ
        (∀ (q : Real × Real), (q ∈ B) → ((q ∈ {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c} ∪ {q | ∃
            t : Real, 0 ≤ t ∧ q = x + t • u d}) → (q ∈ frontier U))) → (((B ∩ V).Nonempty) → (¬
            (S.left ⊆ U ∧ S.right ⊆ U))) ) := by
  classical
  intro ι P D F a r u x B f c d S U V rayFront hmeetV
  rintro ⟨hL, hR⟩
  obtain ⟨q, ⟨hqB, hqV⟩⟩ := hmeetV
  have hqNotRay : q ∉ ({q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c} ∪
      {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u d}) := by
    intro hqRay
    have hqf : q ∈ frontier U := rayFront q hqB hqRay
    have hqcl : q ∈ closure U := frontier_subset_closure hqf
    exact hqV hqcl
  have hqsec : q ∈ S.left ∪ S.right := by
    rw [S.cover]
    exact ⟨hqB, hqNotRay⟩
  rcases hqsec with hqL | hqR
  · exact hqV (subset_closure (hL hqL))
  · exact hqV (subset_closure (hR hqR))

private theorem hnotVV :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        ∀ (f : P.plane.Face), ∀ (c : ι), ∀ (d : ι), ∀ (S : P3889T1TwoRaySectorDecomposition x r
            (u c) (u d)),
        let U := F.region f
        let V := (closure U)ᶜ
        (∀ (q : Real × Real), (q ∈ B) → ((q ∈ {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c} ∪ {q | ∃
            t : Real, 0 ≤ t ∧ q = x + t • u d}) → (q ∈ frontier U))) → (((B ∩ U).Nonempty) →
            ((IsOpen U) → ((Disjoint U V) → (¬ (S.left ⊆ V ∧ S.right ⊆ V))))) ) := by
  classical
  intro ι P D F a r u x B f c d S U V rayFront hmeetU hUopen hUV
  rintro ⟨hL, hR⟩
  obtain ⟨q, ⟨hqB, hqU⟩⟩ := hmeetU
  have hqNotRay : q ∉ ({q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c} ∪
      {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u d}) := by
    intro hqRay
    have hqf : q ∈ frontier U := rayFront q hqB hqRay
    have hqnotU : q ∉ U := by
      intro hqU'
      have : q ∈ frontier U := hqf
      rw [frontier, hUopen.interior_eq] at this
      exact this.2 hqU'
    exact hqnotU hqU
  have hqsec : q ∈ S.left ∪ S.right := by
    rw [S.cover]
    exact ⟨hqB, hqNotRay⟩
  rcases hqsec with hqL | hqR
  · exact (Set.disjoint_left.mp hUV hqU (hL hqL))
  · exact (Set.disjoint_left.mp hUV hqU (hR hqR))

private theorem hfill :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        ∀ (f : P.plane.Face), ∀ (c : ι), ∀ (d : ι), ∀ (S : P3889T1TwoRaySectorDecomposition x r
            (u c) (u d)),
        let U := F.region f
        let V := (closure U)ᶜ
        (S.left ⊆ U ∨ S.left ⊆ V) → ((S.right ⊆ U ∨ S.right ⊆ V) → ((¬ (S.left ⊆ U ∧ S.right ⊆
            U)) → ((¬ (S.left ⊆ V ∧ S.right ⊆ V)) → ((S.left ⊆ U ∧ S.right ⊆ V) ∨ (S.right ⊆ U ∧
            S.left ⊆ V))))) ) := by
  classical
  intro ι P D F a r u x f c d S U V hLchoice hRchoice hnotUU hnotVV
  rcases hLchoice with hL | hL <;> rcases hRchoice with hR | hR
  · exact (hnotUU ⟨hL, hR⟩).elim
  · exact Or.inl ⟨hL, hR⟩
  · exact Or.inr ⟨hR, hL⟩
  · exact (hnotVV ⟨hL, hR⟩).elim

private theorem hqNotRayAt457 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        ∀ (f : P.plane.Face), ∀ (c : ι), ∀ (d : ι),
        let U := F.region f
        (∀ (q : Real × Real), (q ∈ B) → ((q ∈ {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c} ∪ {q | ∃
            t : Real, 0 ≤ t ∧ q = x + t • u d}) → (q ∈ frontier U))) → ((IsOpen U) → (∀ (q : ℝ ×
            ℝ), (q ∈ F.region f ∩ B) → (q ∉ ({q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c} ∪ {q | ∃ t
            : Real, 0 ≤ t ∧ q = x + t • u d})))) ) := by
  classical
  intro ι P D F a r u x B f c d U rayFront hUopen q hq hqRay
  have hqf : q ∈ frontier U := rayFront q hq.2 hqRay
  have hqnotU : q ∉ U := by
    intro hqU
    have : q ∈ frontier U := hqf
    rw [frontier, hUopen.interior_eq] at this
    exact this.2 hqU
  exact hqnotU hq.1

private theorem hqsecAt467 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        ∀ (f : P.plane.Face), ∀ (c : ι), ∀ (d : ι), ∀ (S : P3889T1TwoRaySectorDecomposition x r
            (u c) (u d)), ∀ (q : ℝ × ℝ), (q ∈ F.region f ∩ B) → ((q ∉ ({q | ∃ t : Real, 0 ≤ t ∧ q
            = x + t • u c} ∪ {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u d})) → (q ∈ S.left ∪
            S.right)) ) := by
  classical
  intro ι P D F a r u x B f c d S q hq hqNotRay
  rw [S.cover]
  exact ⟨hq.2, hqNotRay⟩

private theorem hqNotRayAt479 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        ∀ (f : P.plane.Face), ∀ (c : ι), ∀ (d : ι),
        let U := F.region f
        (∀ (q : Real × Real), (q ∈ B) → ((q ∈ {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c} ∪ {q | ∃
            t : Real, 0 ≤ t ∧ q = x + t • u d}) → (q ∈ frontier U))) → ((IsOpen U) → (∀ (q : ℝ ×
            ℝ), (q ∈ F.region f ∩ B) → (q ∉ ({q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c} ∪ {q | ∃ t
            : Real, 0 ≤ t ∧ q = x + t • u d})))) ) := by
  classical
  intro ι P D F a r u x B f c d U rayFront hUopen q hq hqRay
  have hqf : q ∈ frontier U := rayFront q hq.2 hqRay
  have hqnotU : q ∉ U := by
    intro hqU
    have : q ∈ frontier U := hqf
    rw [frontier, hUopen.interior_eq] at this
    exact this.2 hqU
  exact hqnotU hq.1

private theorem hqsecAt489 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        ∀ (f : P.plane.Face), ∀ (c : ι), ∀ (d : ι), ∀ (S : P3889T1TwoRaySectorDecomposition x r
            (u c) (u d)), ∀ (q : ℝ × ℝ), (q ∈ F.region f ∩ B) → ((q ∉ ({q | ∃ t : Real, 0 ≤ t ∧ q
            = x + t • u c} ∪ {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u d})) → (q ∈ S.left ∪
            S.right)) ) := by
  classical
  intro ι P D F a r u x B f c d S q hq hqNotRay
  rw [S.cover]
  exact ⟨hq.2, hqNotRay⟩

private theorem hrho :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a :
            ι), ∀ (p : ℝ × ℝ),
        let x := D.position a
        let T := Set.range D.position ∪
          {q | ∃ c d, P.plane.adjacent c d ∧ q ∈ D.edgeArc c d}
        (p ∉ T) → (
        let rho : Real := ‖p - x‖
        0 < rho) ) := by
  classical
  intro ι P D a p x T hpNotT rho
  apply norm_pos_iff.mpr
  intro hpx
  apply hpNotT
  left
  have hpEq : p = x := sub_eq_zero.mp hpx
  exact ⟨a, by simpa [x] using hpEq.symm⟩

private theorem hrho' :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a :
            ι), ∀ (r : ℝ), ∀ (p : ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        (p ∈ B) → (
        let rho : Real := ‖p - x‖
        rho < r) ) := by
  classical
  intro ι P D a r p x B hpB rho
  have hpdist : dist p x < r := by simpa [B, Metric.mem_ball] using hpB
  simpa [rho, dist_eq_norm] using hpdist

private theorem hfinitePick :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι),
        let N : Set ι := {c | P.plane.adjacent a c}
        (N.Finite) → (
        let Nsub := {c : ι // P.plane.adjacent a c}
        let first (c : Nsub) : P.plane.Face :=
          Classical.choose (P.plane.every_edge_two_faces a c.1 c.2)
        let second (c : Nsub) : P.plane.Face :=
          Classical.choose (Classical.choose_spec
            (P.plane.every_edge_two_faces a c.1 c.2))
        let facePick : Nsub × Fin 2 → P.plane.Face := fun z =>
          if z.2 = 0 then first z.1 else second z.1
        (Set.range facePick).Finite) ) := by
  classical
  intro ι P a N hNfinite Nsub first second facePick
  let : Finite Nsub := hNfinite.to_subtype
  exact Set.finite_range facePick

private theorem hIfinite :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι),
        let I : Set P.plane.Face := {f | ∃ i, P.plane.faceVertex f i = a}
        let Nsub := {c : ι // P.plane.adjacent a c}
        let first (c : Nsub) : P.plane.Face :=
          Classical.choose (P.plane.every_edge_two_faces a c.1 c.2)
        let second (c : Nsub) : P.plane.Face :=
          Classical.choose (Classical.choose_spec
            (P.plane.every_edge_two_faces a c.1 c.2))
        let facePick : Nsub × Fin 2 → P.plane.Face := fun z =>
          if z.2 = 0 then first z.1 else second z.1
        ((Set.range facePick).Finite) → (I.Finite) ) := by
  classical
  intro ι P a I Nsub first second facePick hfinitePick
  apply hfinitePick.subset
  intro f hf
  change f ∈ I at hf
  obtain ⟨i, hi⟩ := hf
  obtain ⟨j, hji⟩ := exists_ne i
  have hac : P.plane.adjacent a (P.plane.faceVertex f j) := by
    rw [← hi]
    exact P.plane.face_edges f i j hji.symm
  let c : Nsub := ⟨P.plane.faceVertex f j, hac⟩
  have hspec := Classical.choose_spec (Classical.choose_spec
    (P.plane.every_edge_two_faces a c.1 c.2))
  obtain ⟨hne, ⟨hf₀a, hf₀c⟩, ⟨hf₁a, hf₁c⟩, hexhaust⟩ := hspec
  have hcase := hexhaust f ⟨⟨i, hi⟩, ⟨j, rfl⟩⟩
  rcases hcase with hEq | hEq
  · refine ⟨(c, 0), ?_⟩
    simpa [facePick, first] using hEq.symm
  · refine ⟨(c, 1), ?_⟩
    simpa [facePick, second] using hEq.symm

private theorem faceOtherMatch :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (g : P.plane.Face), ∀ (j : Fin
            (3 : ℕ)), P.plane.faceVertex g j = a → ∀ (e : ι), (∃ (k : Fin (3 : ℕ)),
            P.plane.faceVertex g k = e) → e ≠ a → ∀ (c : ι), ∀ (d : ι), c ≠ a → d ≠ a → c ≠ d →
            (∃ (k : Fin (3 : ℕ)), P.plane.faceVertex g k = c) → (∃ (k : Fin (3 : ℕ)),
            P.plane.faceVertex g k = d) → e = c ∨ e = d ) := by
  classical
  intro ι P a g j hj e he hea c d hca hda hcd hc hd
  obtain ⟨k, hk⟩ := he
  obtain ⟨l, hl⟩ := hc
  obtain ⟨m, hm⟩ := hd
  have hkj : k ≠ j := by
    intro h
    apply hea
    calc
      e = P.plane.faceVertex g k := hk.symm
      _ = P.plane.faceVertex g j := congrArg (P.plane.faceVertex g) h
      _ = a := hj
  have hlj : l ≠ j := by
    intro h
    apply hca
    calc
      c = P.plane.faceVertex g l := hl.symm
      _ = P.plane.faceVertex g j := congrArg (P.plane.faceVertex g) h
      _ = a := hj
  have hmj : m ≠ j := by
    intro h
    apply hda
    calc
      d = P.plane.faceVertex g m := hm.symm
      _ = P.plane.faceVertex g j := congrArg (P.plane.faceVertex g) h
      _ = a := hj
  have hlm : l ≠ m := by
    intro h
    apply hcd
    calc
      c = P.plane.faceVertex g l := hl.symm
      _ = P.plane.faceVertex g m := congrArg (P.plane.faceVertex g) h
      _ = d := hm
  have hkj' : k.val ≠ j.val := fun h => hkj (Fin.ext h)
  have hlj' : l.val ≠ j.val := fun h => hlj (Fin.ext h)
  have hmj' : m.val ≠ j.val := fun h => hmj (Fin.ext h)
  have hlm' : l.val ≠ m.val := fun h => hlm (Fin.ext h)
  have hidx : k.val = l.val ∨ k.val = m.val := by omega
  rcases hidx with h | h
  · left
    calc
      e = P.plane.faceVertex g k := hk.symm
      _ = P.plane.faceVertex g l := congrArg (P.plane.faceVertex g) (Fin.ext h)
      _ = c := hl
  · right
    calc
      e = P.plane.faceVertex g k := hk.symm
      _ = P.plane.faceVertex g m := congrArg (P.plane.faceVertex g) (Fin.ext h)
      _ = d := hm

private theorem hzB :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a :
            ι), ∀ (r : ℝ), ∀ (p : ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        let rho : Real := ‖p - x‖
        (rho < r) → (∀ (z : ℝ × ℝ), (z ∈ Metric.sphere x rho) → (z ∈ B)) ) := by
  classical
  intro ι P D a r p x B rho hrho' z hzS
  have hzdist : dist z x = rho := by
    simpa [dist_eq_norm] using hzS
  change dist z x < r
  rw [hzdist]
  exact hrho'

private theorem hzRays :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        ∀ (z : ℝ × ℝ), ∀ (f : P.plane.Face), (z ∈ frontier (F.region f)) → ((z ∈ B) → (∀ (c : ι),
            ∀ (d : ι), (frontier (F.region f) ∩ B = B ∩ {q : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ q =
            x + t • u c} ∪ B ∩ {q : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ q = x + t • u d}) → ((z ∈ B
            ∩ {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c}) ∨ (z ∈ B ∩ {q | ∃ t : Real, 0 ≤ t ∧ q =
            x + t • u d})))) ) := by
  classical
  intro ι P D F a r u x B z f hzfront hzB c d hfront
  have heq := congrArg (fun s : Set (Real × Real) => z ∈ s) hfront
  simpa only [Set.mem_union, Set.mem_inter_iff] using heq.mp ⟨hzfront, hzB⟩

private theorem localSide :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        (∀ (f : P.plane.Face), ∀ (i : Fin 3), (P.plane.faceVertex f i = a) → (∃ c d, c ≠ a ∧ d ≠
            a ∧ c ≠ d ∧ P.plane.adjacent a c ∧ P.plane.adjacent a d ∧ (∃ j, P.plane.faceVertex f
            j = c) ∧ (∃ j, P.plane.faceVertex f j = d) ∧ ∃ S : P3889T1TwoRaySectorDecomposition
            x r (u c) (u d), F.region f ∩ B = S.left ∨ F.region f ∩ B = S.right)) → ((∀ (g :
            P.plane.Face), ∀ (j : Fin 3), (P.plane.faceVertex g j = a) → (∀ (e : ι), (∃ k,
            P.plane.faceVertex g k = e) → ((e ≠ a) → (∀ (c : ι), ∀ (d : ι), (c ≠ a) → ((d ≠ a) →
            ((c ≠ d) → ((∃ k, P.plane.faceVertex g k = c) → ((∃ k, P.plane.faceVertex g k = d) →
            (e = c ∨ e = d))))))))) → (∀ (z : ℝ × ℝ), ∀ (g : P.plane.Face), ∀ (j : Fin (3 : ℕ)),
            P.plane.faceVertex g j = a → ∀ (e : ι), (∃ (k : Fin (3 : ℕ)), P.plane.faceVertex g k
            = e) → e ≠ a → ∀ (t : ℝ), (0 : ℝ) < t → t < r → z = x + t • u e → ∃ δ > (0 : ℝ),
            Metric.ball z δ ⊆ B ∧ ((∀ q ∈ Metric.ball z δ, (0 : ℝ) < (u e).1 * (q.2 - z.2) - (u
            e).2 * (q.1 - z.1) → q ∈ F.region g) ∨ ∀ q ∈ Metric.ball z δ, (u e).1 * (q.2 - z.2) -
            (u e).2 * (q.1 - z.1) < (0 : ℝ) → q ∈ F.region g))) ) := by
  classical
  intro ι P D F a r u x B hfaceFillsSector faceOtherMatch z g j hj e he hea t ht htr hzeq
  obtain ⟨c', d', hca', hda', hcd', hac', had', hc'i, hd'i,
    S', hfill'⟩ := hfaceFillsSector g j hj
  have hmatch := faceOtherMatch g j hj e he hea c' d' hca' hda' hcd' hc'i hd'i
  rcases hmatch with heq | heq
  · obtain ⟨δ, hδ, hballB, hsides⟩ :=
      S'.sides (u e) (Or.inl (congrArg u heq)) t ht htr
    rcases hsides with ⟨hLp, hRn⟩ | ⟨hRp, hLn⟩
    · refine ⟨δ, hδ, ?_, ?_⟩
      · simpa [hzeq] using hballB
      · rcases hfill' with hfill | hfill
        · left
          intro q hq hsign
          have hq' : q ∈ S'.left ∩ Metric.ball (x + t • u e) δ := by
            rw [hLp]
            exact ⟨by simpa [hzeq] using hq, by simpa [hzeq] using hsign⟩
          have hqU : q ∈ F.region g ∩ B := by rw [hfill]; exact hq'.1
          exact hqU.1
        · right
          intro q hq hsign
          have hq' : q ∈ S'.right ∩ Metric.ball (x + t • u e) δ := by
            rw [hRn]
            exact ⟨by simpa [hzeq] using hq, by simpa [hzeq] using hsign⟩
          have hqU : q ∈ F.region g ∩ B := by rw [hfill]; exact hq'.1
          exact hqU.1
    · refine ⟨δ, hδ, ?_, ?_⟩
      · simpa [hzeq] using hballB
      · rcases hfill' with hfill | hfill
        · right
          intro q hq hsign
          have hq' : q ∈ S'.left ∩ Metric.ball (x + t • u e) δ := by
            rw [hLn]
            exact ⟨by simpa [hzeq] using hq, by simpa [hzeq] using hsign⟩
          have hqU : q ∈ F.region g ∩ B := by rw [hfill]; exact hq'.1
          exact hqU.1
        · left
          intro q hq hsign
          have hq' : q ∈ S'.right ∩ Metric.ball (x + t • u e) δ := by
            rw [hRp]
            exact ⟨by simpa [hzeq] using hq, by simpa [hzeq] using hsign⟩
          have hqU : q ∈ F.region g ∩ B := by rw [hfill]; exact hq'.1
          exact hqU.1
  · obtain ⟨δ, hδ, hballB, hsides⟩ :=
      S'.sides (u e) (Or.inr (congrArg u heq)) t ht htr
    rcases hsides with ⟨hLp, hRn⟩ | ⟨hRp, hLn⟩
    · refine ⟨δ, hδ, ?_, ?_⟩
      · simpa [hzeq] using hballB
      · rcases hfill' with hfill | hfill
        · left
          intro q hq hsign
          have hq' : q ∈ S'.left ∩ Metric.ball (x + t • u e) δ := by
            rw [hLp]
            exact ⟨by simpa [hzeq] using hq, by simpa [hzeq] using hsign⟩
          have hqU : q ∈ F.region g ∩ B := by rw [hfill]; exact hq'.1
          exact hqU.1
        · right
          intro q hq hsign
          have hq' : q ∈ S'.right ∩ Metric.ball (x + t • u e) δ := by
            rw [hRn]
            exact ⟨by simpa [hzeq] using hq, by simpa [hzeq] using hsign⟩
          have hqU : q ∈ F.region g ∩ B := by rw [hfill]; exact hq'.1
          exact hqU.1
    · refine ⟨δ, hδ, ?_, ?_⟩
      · simpa [hzeq] using hballB
      · rcases hfill' with hfill | hfill
        · right
          intro q hq hsign
          have hq' : q ∈ S'.left ∩ Metric.ball (x + t • u e) δ := by
            rw [hLn]
            exact ⟨by simpa [hzeq] using hq, by simpa [hzeq] using hsign⟩
          have hqU : q ∈ F.region g ∩ B := by rw [hfill]; exact hq'.1
          exact hqU.1
        · left
          intro q hq hsign
          have hq' : q ∈ S'.right ∩ Metric.ball (x + t • u e) δ := by
            rw [hRp]
            exact ⟨by simpa [hzeq] using hq, by simpa [hzeq] using hsign⟩
          have hqU : q ∈ F.region g ∩ B := by rw [hfill]; exact hq'.1
          exact hqU.1

private theorem hfg :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), (ι) → (
        let Nsub := {c : ι // P.plane.adjacent a c}
        let first (c : Nsub) : P.plane.Face :=
          Classical.choose (P.plane.every_edge_two_faces a c.1 c.2)
        let second (c : Nsub) : P.plane.Face :=
          Classical.choose (Classical.choose_spec
            (P.plane.every_edge_two_faces a c.1 c.2))
        ∀ (f : P.plane.Face), ∀ (e : ι), ∀ (hae : P.plane.adjacent a e),
        let en : Nsub := ⟨e, hae⟩
        let f0 := first en
        let f1 := second en
        (f0 ≠ f1) → (
        let g := if f = f0 then f1 else f0
        f ≠ g))) := by
  classical
  intro ι P a c Nsub first second f e hae en f0 f1 hne g
  dsimp [g]
  split_ifs with h
  · intro hEq
    exact hne (h.symm.trans hEq)
  · exact h

private theorem hgI :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), (ι) → (
        let Nsub := {c : ι // P.plane.adjacent a c}
        let first (c : Nsub) : P.plane.Face :=
          Classical.choose (P.plane.every_edge_two_faces a c.1 c.2)
        let second (c : Nsub) : P.plane.Face :=
          Classical.choose (Classical.choose_spec
            (P.plane.every_edge_two_faces a c.1 c.2))
        ∀ (f : P.plane.Face), ∀ (e : ι), ∀ (hae : P.plane.adjacent a e),
        let en : Nsub := ⟨e, hae⟩
        let f0 := first en
        let f1 := second en
        (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (f0) i = a) → ((∃ (i : Fin (3 :
            ℕ)), P.plane.faceVertex (f1) i = a) → (
        let g := if f = f0 then f1 else f0
        ∃ j, P.plane.faceVertex g j = a)))) := by
  classical
  intro ι P a c Nsub first second f e hae en f0 f1 hf0a hf1a g
  dsimp [g]
  split_ifs with h
  · exact hf1a
  · exact hf0a

private theorem hgE :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), (ι) → (
        let Nsub := {c : ι // P.plane.adjacent a c}
        let first (c : Nsub) : P.plane.Face :=
          Classical.choose (P.plane.every_edge_two_faces a c.1 c.2)
        let second (c : Nsub) : P.plane.Face :=
          Classical.choose (Classical.choose_spec
            (P.plane.every_edge_two_faces a c.1 c.2))
        ∀ (f : P.plane.Face), ∀ (e : ι), ∀ (hae : P.plane.adjacent a e),
        let en : Nsub := ⟨e, hae⟩
        let f0 := first en
        let f1 := second en
        (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (f0) i = e) → ((∃ (i : Fin (3 :
            ℕ)), P.plane.faceVertex (f1) i = e) → (
        let g := if f = f0 then f1 else f0
        ∃ j, P.plane.faceVertex g j = e)))) := by
  classical
  intro ι P a c Nsub first second f e hae en f0 f1 hf0e hf1e g
  dsimp [g]
  split_ifs with h
  · exact hf1e
  · exact hf0e

private theorem heps₁ :
    (by
      classical
      exact
        ∀ (t : ℝ), ∀ (δ₁ : ℝ), (δ₁ > (0 : ℝ)) → (∀ (δ₂ : ℝ),
        let eps := min δ₁ (min δ₂ t) / 2
        eps < δ₁) ) := by
  classical
  intro t δ₁ hδ₁ δ₂ eps
  have hmin : min δ₁ (min δ₂ t) ≤ δ₁ := min_le_left _ _
  dsimp [eps]
  linarith [hδ₁]

private theorem heps₂ :
    (by
      classical
      exact
        ∀ (t : ℝ), ∀ (δ₁ : ℝ), ∀ (δ₂ : ℝ), (δ₂ > (0 : ℝ)) → (
        let eps := min δ₁ (min δ₂ t) / 2
        eps < δ₂) ) := by
  classical
  intro t δ₁ δ₂ hδ₂ eps
  have hmin : min δ₁ (min δ₂ t) ≤ δ₂ := le_trans (min_le_right _ _) (min_le_left _ _)
  dsimp [eps]
  linarith [hδ₂]

private theorem hepst :
    (by
      classical
      exact
        ∀ (t : ℝ), ((0 : ℝ) < t) → (∀ (δ₁ : ℝ), ∀ (δ₂ : ℝ),
        let eps := min δ₁ (min δ₂ t) / 2
        eps < t) ) := by
  classical
  intro t ht δ₁ δ₂ eps
  have hmin : min δ₁ (min δ₂ t) ≤ t := le_trans (min_le_right _ _) (min_le_right _ _)
  dsimp [eps]
  linarith [ht]

private theorem hball₁' :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a :
            ι), ∀ (r : ℝ),
        let x := D.position a
        let B := Metric.ball x r
        ∀ (z : ℝ × ℝ), ∀ (t : ℝ), ∀ (δ₁ : ℝ), (Metric.ball z δ₁ ⊆ B) → (∀ (δ₂ : ℝ),
        let eps := min δ₁ (min δ₂ t) / 2
        (eps < δ₁) → (Metric.ball z eps ⊆ B)) ) := by
  classical
  intro ι P D a r x B z t δ₁ hball₁ δ₂ eps heps₁ q hq
  exact hball₁ (Metric.ball_subset_ball (le_of_lt heps₁) hq)

private theorem hball₂' :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a :
            ι), ∀ (r : ℝ),
        let x := D.position a
        let B := Metric.ball x r
        ∀ (z : ℝ × ℝ), ∀ (t : ℝ), ∀ (δ₁ : ℝ), ∀ (δ₂ : ℝ), (Metric.ball z δ₂ ⊆ B) → (
        let eps := min δ₁ (min δ₂ t) / 2
        (eps < δ₂) → (Metric.ball z eps ⊆ B)) ) := by
  classical
  intro ι P D a r x B z t δ₁ δ₂ hball₂ eps heps₂ q hq
  exact hball₂ (Metric.ball_subset_ball (le_of_lt heps₂) hq)

private theorem hzeroK :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ), (∀ (c : ι),
            P.plane.adjacent a c → ‖u c‖ = (1 : ℝ)) → (
        let x := D.position a
        let B := Metric.ball x r
        (∀ (f : P.plane.Face), ∀ (i : Fin 3), (P.plane.faceVertex f i = a) → (∃ c d, c ≠ a ∧ d ≠
            a ∧ c ≠ d ∧ P.plane.adjacent a c ∧ P.plane.adjacent a d ∧ (∃ j, P.plane.faceVertex f
            j = c) ∧ (∃ j, P.plane.faceVertex f j = d) ∧ frontier (F.region f) ∩ B = (B ∩ {q | ∃
            t : Real, 0 ≤ t ∧ q = x + t • u c}) ∪ (B ∩ {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u d})
            ∧ Nonempty (P3889T1TwoRaySectorDecomposition x r (u c) (u d)))) → (
        let I : Set P.plane.Face := {f | ∃ i, P.plane.faceVertex f i = a}
        ∀ (c : ι),
        let Nsub := {c : ι // P.plane.adjacent a c}
        let first (c : Nsub) : P.plane.Face :=
          Classical.choose (P.plane.every_edge_two_faces a c.1 c.2)
        let second (c : Nsub) : P.plane.Face :=
          Classical.choose (Classical.choose_spec
            (P.plane.every_edge_two_faces a c.1 c.2))
        (∀ (g : P.plane.Face), ∀ (j : Fin 3), (P.plane.faceVertex g j = a) → (∀ (e : ι), (∃ k,
            P.plane.faceVertex g k = e) → ((e ≠ a) → (∀ (c : ι), ∀ (d : ι), (c ≠ a) → ((d ≠ a) →
            ((c ≠ d) → ((∃ k, P.plane.faceVertex g k = c) → ((∃ k, P.plane.faceVertex g k = d) →
            (e = c ∨ e = d))))))))) → (∀ (f : P.plane.Face),
        let K : Set (Real × Real) := ⋃ f ∈ I, closure (F.region f)
        ∀ (z : ℝ × ℝ), ∀ (i : Fin (3 : ℕ)), (P.plane.faceVertex f i = a) → (∀ (e : ι), (∃ (k :
            Fin (3 : ℕ)), P.plane.faceVertex f k = e) → ((e ≠ a) → (∀ (hae : P.plane.adjacent a
            e), ∀ (t : ℝ), (z = x + t • u e) → (
        let en : Nsub := ⟨e, hae⟩
        let f0 := first en
        let f1 := second en
        let g := if f = f0 then f1 else f0
        (∃ j, P.plane.faceVertex g j = e) → (∀ (j : Fin (3 : ℕ)), (P.plane.faceVertex g j = a) →
            (∀ (δ₁ : ℝ), ∀ (δ₂ : ℝ),
        let eps := min δ₁ (min δ₂ t) / 2
        (eps < t) → ((Metric.ball z eps ⊆ B) → (∀ q ∈ Metric.ball z eps, (u e).1 * (q.2 - z.2) -
            (u e).2 * (q.1 - z.1) = 0 → q ∈ K))))))))))) ) := by
  classical
  intro ι P D F a r u hunit x B hincidentSectorData I c Nsub first second faceOtherMatch f K z i
      hi e he hea hae t hzeq en f0 f1 g hgE j hj δ₁ δ₂ eps hepst hball₁' q hq hdet
  have hu : u e ≠ 0 := by
    intro heq
    have := hunit e hae
    rw [heq, norm_zero] at this
    norm_num at this
  have hvec : ∃ lam : Real, q - z = lam • u e := by
    by_cases hu1 : (u e).1 = 0
    · have hu2 : (u e).2 ≠ 0 := by
        intro h
        apply hu
        ext <;> assumption
      have hq1 : q.1 - z.1 = 0 := by
        rw [hu1] at hdet
        have hmul : (u e).2 * (q.1 - z.1) = 0 := by nlinarith [hdet]
        exact (mul_eq_zero.mp hmul).resolve_left hu2
      refine ⟨(q.2 - z.2) / (u e).2, ?_⟩
      ext <;> simp [hu1, hq1]
      field_simp [hu2]
    · refine ⟨(q.1 - z.1) / (u e).1, ?_⟩
      ext
      · simp
        field_simp [hu1]
      · simp
        field_simp [hu1]
        nlinarith [hdet]
  obtain ⟨lam, hvec_eq⟩ := hvec
  have hLamNorm : ‖q - z‖ = |lam| := by
    rw [hvec_eq, norm_smul, hunit e hae, Real.norm_eq_abs]
    ring
  have hLamLt : |lam| < t := by
    have hdist : dist q z < eps := by
      simpa [Metric.mem_ball] using hq
    rw [dist_eq_norm] at hdist
    rw [hLamNorm] at hdist
    exact hdist.trans hepst
  let s := t + lam
  have hs : 0 < s := by
    dsimp [s]
    have := (abs_lt.mp hLamLt).1
    linarith
  have hqeq : q = x + s • u e := by
    calc
      q = z + (q - z) := by abel
      _ = (x + t • u e) + lam • u e := by rw [hvec_eq, hzeq]
      _ = x + s • u e := by dsimp [s]; module
  obtain ⟨cf, df, hcf, hdf, hcdf, hacf, hadf, hcfi, hdfi, hfrontF⟩ :=
    hincidentSectorData f i hi
  have hfrontF := hfrontF.1
  have hmatchF := faceOtherMatch f i hi e he hea cf df hcf hdf hcdf hcfi hdfi
  have hqBF : q ∈ B := hball₁' hq
  have hqrayF : (q ∈ B ∩ {q | ∃ s : Real, 0 ≤ s ∧ q = x + s • u cf}) ∨
      (q ∈ B ∩ {q | ∃ s : Real, 0 ≤ s ∧ q = x + s • u df}) := by
    rcases hmatchF with hce | hde
    · left
      refine ⟨hqBF, s, le_of_lt hs, ?_⟩
      simpa [hce] using hqeq
    · right
      refine ⟨hqBF, s, le_of_lt hs, ?_⟩
      simpa [hde] using hqeq
  have hqfrontF : q ∈ frontier (F.region f) := by
    have heq := congrArg (fun S : Set (Real × Real) => q ∈ S) hfrontF
    have hmem : q ∈ frontier (F.region f) ∩ B := by
      apply heq.mpr
      simpa only [Set.mem_union, Set.mem_inter_iff] using hqrayF
    exact hmem.1
  obtain ⟨cg, dg, hcg, hdg, hcdg, hacg, hadg, hcgi, hdgi, hfrontG⟩ :=
    hincidentSectorData g j hj
  have hfrontG := hfrontG.1
  have hmatchG := faceOtherMatch g j hj e hgE hea cg dg hcg hdg hcdg hcgi hdgi
  have hqrayG : (q ∈ B ∩ {q | ∃ s : Real, 0 ≤ s ∧ q = x + s • u cg}) ∨
      (q ∈ B ∩ {q | ∃ s : Real, 0 ≤ s ∧ q = x + s • u dg}) := by
    rcases hmatchG with hce | hde
    · left
      refine ⟨hqBF, s, le_of_lt hs, ?_⟩
      simpa [hce] using hqeq
    · right
      refine ⟨hqBF, s, le_of_lt hs, ?_⟩
      simpa [hde] using hqeq
  have hqfrontG : q ∈ frontier (F.region g) := by
    have heq := congrArg (fun S : Set (Real × Real) => q ∈ S) hfrontG
    have hmem : q ∈ frontier (F.region g) ∩ B := by
      apply heq.mpr
      simpa only [Set.mem_union, Set.mem_inter_iff] using hqrayG
    exact hmem.1
  exact Set.mem_iUnion₂.mpr ⟨f, ⟨i, hi⟩, frontier_subset_closure hqfrontF⟩

private theorem memK :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι),
        let I : Set P.plane.Face := {f | ∃ i, P.plane.faceVertex f i = a}
        (P.plane.Face) → (
        let K : Set (Real × Real) := ⋃ f ∈ I, closure (F.region f)
        ∀ (g : P.plane.Face), ∀ (j : Fin (3 : ℕ)), P.plane.faceVertex g j = a → ∀ q ∈ F.region g,
            q ∈ K)) := by
  classical
  intro ι P D F a I f K g j hj q hq
  exact Set.mem_iUnion₂.mpr ⟨g, ⟨j, hj⟩, subset_closure hq⟩

private theorem build :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (u : ι → ℝ × ℝ),
        let I : Set P.plane.Face := {f | ∃ i, P.plane.faceVertex f i = a}
        ∀ (c : ι),
        let Nsub := {c : ι // P.plane.adjacent a c}
        let first (c : Nsub) : P.plane.Face :=
          Classical.choose (P.plane.every_edge_two_faces a c.1 c.2)
        let second (c : Nsub) : P.plane.Face :=
          Classical.choose (Classical.choose_spec
            (P.plane.every_edge_two_faces a c.1 c.2))
        ∀ (f : P.plane.Face),
        let K : Set (Real × Real) := ⋃ f ∈ I, closure (F.region f)
        ∀ (z : ℝ × ℝ), ∀ (i : Fin (3 : ℕ)), (P.plane.faceVertex f i = a) → (∀ (e : ι), ∀ (hae :
            P.plane.adjacent a e), ∀ (t : ℝ),
        let en : Nsub := ⟨e, hae⟩
        let f0 := first en
        let f1 := second en
        let g := if f = f0 then f1 else f0
        ∀ (j : Fin (3 : ℕ)), (P.plane.faceVertex g j = a) → (∀ (δ₁ : ℝ), ∀ (δ₂ : ℝ),
        let eps := min δ₁ (min δ₂ t) / 2
        (∀ q ∈ Metric.ball z eps, (u e).1 * (q.2 - z.2) - (u e).2 * (q.1 - z.1) = 0 → q ∈ K) →
            ((∀ (g : P.plane.Face), ∀ (j : Fin 3), (P.plane.faceVertex g j = a) → (∀ (q : Real ×
            Real), (q ∈ F.region g) → (q ∈ K))) → ((∀ q ∈ Metric.ball z eps, (0 : ℝ) < (u e).1 *
            (q.2 - z.2) - (u e).2 * (q.1 - z.1) → q ∈ F.region f) → (∀ q ∈ Metric.ball z eps, (u
            e).1 * (q.2 - z.2) - (u e).2 * (q.1 - z.1) < (0 : ℝ) → q ∈ F.region g) → Metric.ball
            z eps ⊆ K)))) ) := by
  classical
  intro ι P D F a u I c Nsub first second f K z i hi e hae t en f0 f1 g j hj δ₁ δ₂ eps hzeroK
      memK hpos hneg q hq
  by_cases hqpos : 0 < (u e).1 * (q.2 - z.2) - (u e).2 * (q.1 - z.1)
  · exact memK f i hi q (hpos q hq hqpos)
  · by_cases hqneg : (u e).1 * (q.2 - z.2) - (u e).2 * (q.1 - z.1) < 0
    · exact memK g j hj q (hneg q hq hqneg)
    · have hqzero : (u e).1 * (q.2 - z.2) - (u e).2 * (q.1 - z.1) = 0 := by
        linarith
      exact hzeroK q hq hqzero

private theorem huAt878 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (u : ι → ℝ × ℝ), (∀ (c : ι),
            P.plane.adjacent a c → ‖u c‖ = (1 : ℝ)) → (∀ (e : ι), (P.plane.adjacent a e) → (u e ≠
            0)) ) := by
  classical
  intro ι P a u hunit e hae heq
  have h := hunit e hae
  rw [heq, norm_zero] at h
  norm_num at h

private theorem hsumAt883 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (u : ι → ℝ × ℝ), ∀ (e : ι), (u e ≠ 0) → (0 < (u e).1 ^ 2 + (u e).2 ^ 2) )
            := by
  classical
  intro ι u e hu
  have hne : (u e).1 ^ 2 + (u e).2 ^ 2 ≠ 0 := by
    intro hs
    have h1 : (u e).1 = 0 := by nlinarith [sq_nonneg (u e).1, sq_nonneg (u e).2]
    have h2 : (u e).2 = 0 := by nlinarith [sq_nonneg (u e).1, sq_nonneg (u e).2]
    exact hu (by ext <;> assumption)
  have hnonneg : 0 ≤ (u e).1 ^ 2 + (u e).2 ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

private theorem hqplus1 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (u : ι → ℝ × ℝ), ∀ (z : ℝ × ℝ), ∀ (e : ι), ∀ (t : ℝ), ∀ (δ₁ : ℝ), ∀ (δ₂ :
            ℝ),
        let eps := min δ₁ (min δ₂ t) / 2
        (0 < eps) → ((eps < δ₁) → (
        let v : Real × Real := (-(u e).2, (u e).1)
        (‖v‖ = 1) → (
        let qplus := z + eps • v
        qplus ∈ Metric.ball z δ₁))) ) := by
  classical
  intro ι u z e t δ₁ δ₂ eps heps heps₁ v hvnorm qplus
  have hdist : dist qplus z = eps := by
    dsimp [qplus]
    rw [dist_eq_norm]
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos heps, hvnorm]
  change dist qplus z < δ₁
  rw [hdist]
  exact heps₁

private theorem hqplus2 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (u : ι → ℝ × ℝ), ∀ (z : ℝ × ℝ), ∀ (e : ι), ∀ (t : ℝ), ∀ (δ₁ : ℝ), ∀ (δ₂ :
            ℝ),
        let eps := min δ₁ (min δ₂ t) / 2
        (0 < eps) → ((eps < δ₂) → (
        let v : Real × Real := (-(u e).2, (u e).1)
        (‖v‖ = 1) → (
        let qplus := z + eps • v
        qplus ∈ Metric.ball z δ₂))) ) := by
  classical
  intro ι u z e t δ₁ δ₂ eps heps heps₂ v hvnorm qplus
  have hdist : dist qplus z = eps := by
    dsimp [qplus]
    rw [dist_eq_norm]
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos heps, hvnorm]
  change dist qplus z < δ₂
  rw [hdist]
  exact heps₂

private theorem hdetplus :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (u : ι → ℝ × ℝ), ∀ (z : ℝ × ℝ), ∀ (e : ι), ∀ (t : ℝ), ∀ (δ₁ : ℝ), ∀ (δ₂ :
            ℝ),
        let eps := min δ₁ (min δ₂ t) / 2
        (0 < eps) → (
        let v : Real × Real := (-(u e).2, (u e).1)
        (0 < (u e).1 ^ 2 + (u e).2 ^ 2) → (
        let qplus := z + eps • v
        0 < (u e).1 * (qplus.2 - z.2) - (u e).2 * (qplus.1 - z.1))) ) := by
  classical
  intro ι u z e t δ₁ δ₂ eps heps v hsum qplus
  have heq : (u e).1 * (qplus.2 - z.2) - (u e).2 * (qplus.1 - z.1) =
      eps * ((u e).1 ^ 2 + (u e).2 ^ 2) := by
    simp [qplus, v]
    ring
  rw [heq]
  exact mul_pos heps hsum

private theorem huAt935 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (u : ι → ℝ × ℝ), (∀ (c : ι),
            P.plane.adjacent a c → ‖u c‖ = (1 : ℝ)) → (∀ (e : ι), (P.plane.adjacent a e) → (u e ≠
            0)) ) := by
  classical
  intro ι P a u hunit e hae heq
  have h := hunit e hae
  rw [heq, norm_zero] at h
  norm_num at h

private theorem hsumAt940 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (u : ι → ℝ × ℝ), ∀ (e : ι), (u e ≠ 0) → (0 < (u e).1 ^ 2 + (u e).2 ^ 2) )
            := by
  classical
  intro ι u e hu
  have hne : (u e).1 ^ 2 + (u e).2 ^ 2 ≠ 0 := by
    intro hs
    have h1 : (u e).1 = 0 := by nlinarith [sq_nonneg (u e).1, sq_nonneg (u e).2]
    have h2 : (u e).2 = 0 := by nlinarith [sq_nonneg (u e).1, sq_nonneg (u e).2]
    exact hu (by ext <;> assumption)
  have hnonneg : 0 ≤ (u e).1 ^ 2 + (u e).2 ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

private theorem hqminus1 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (u : ι → ℝ × ℝ), ∀ (z : ℝ × ℝ), ∀ (e : ι), ∀ (t : ℝ), ∀ (δ₁ : ℝ), ∀ (δ₂ :
            ℝ),
        let eps := min δ₁ (min δ₂ t) / 2
        (0 < eps) → ((eps < δ₁) → (
        let v : Real × Real := (-(u e).2, (u e).1)
        (‖v‖ = 1) → (
        let qminus := z + eps • (-v)
        qminus ∈ Metric.ball z δ₁))) ) := by
  classical
  intro ι u z e t δ₁ δ₂ eps heps heps₁ v hvnorm qminus
  have hdist : dist qminus z = eps := by
    dsimp [qminus]
    rw [dist_eq_norm]
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos heps, hvnorm]
  change dist qminus z < δ₁
  rw [hdist]
  exact heps₁

private theorem hqminus2 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (u : ι → ℝ × ℝ), ∀ (z : ℝ × ℝ), ∀ (e : ι), ∀ (t : ℝ), ∀ (δ₁ : ℝ), ∀ (δ₂ :
            ℝ),
        let eps := min δ₁ (min δ₂ t) / 2
        (0 < eps) → ((eps < δ₂) → (
        let v : Real × Real := (-(u e).2, (u e).1)
        (‖v‖ = 1) → (
        let qminus := z + eps • (-v)
        qminus ∈ Metric.ball z δ₂))) ) := by
  classical
  intro ι u z e t δ₁ δ₂ eps heps heps₂ v hvnorm qminus
  have hdist : dist qminus z = eps := by
    dsimp [qminus]
    rw [dist_eq_norm]
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos heps, hvnorm]
  change dist qminus z < δ₂
  rw [hdist]
  exact heps₂

private theorem hdetminus :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (u : ι → ℝ × ℝ), ∀ (z : ℝ × ℝ), ∀ (e : ι), ∀ (t : ℝ), ∀ (δ₁ : ℝ), ∀ (δ₂ :
            ℝ),
        let eps := min δ₁ (min δ₂ t) / 2
        (0 < eps) → (
        let v : Real × Real := (-(u e).2, (u e).1)
        (0 < (u e).1 ^ 2 + (u e).2 ^ 2) → (
        let qminus := z + eps • (-v)
        (u e).1 * (qminus.2 - z.2) - (u e).2 * (qminus.1 - z.1) < 0)) ) := by
  classical
  intro ι u z e t δ₁ δ₂ eps heps v hsum qminus
  have heq : (u e).1 * (qminus.2 - z.2) - (u e).2 * (qminus.1 - z.1) =
      -eps * ((u e).1 ^ 2 + (u e).2 ^ 2) := by
    simp [qminus, v]
    ring
  rw [heq]
  nlinarith [heps, hsum]

private theorem hnormAt978 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (u : ι → ℝ × ℝ), (∀ (c : ι),
            P.plane.adjacent a c → ‖u c‖ = (1 : ℝ)) → (∀ (c : ι), (P.plane.adjacent a c) → (∀ (t
            : ℝ), ((0 : ℝ) ≤ t) → (‖t • u c‖ = t))) ) := by
  classical
  intro ι P a u hunit c hac t ht0
  rw [norm_smul, hunit c hac, Real.norm_eq_abs, abs_of_nonneg ht0]
  ring

private theorem hdistAt981 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a :
            ι), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        ∀ (z : ℝ × ℝ), ∀ (c : ι), ∀ (t : ℝ), (z = x + t • u c) → ((‖t • u c‖ = t) → (dist z x =
            t)) ) := by
  classical
  intro ι P D a u x z c t hzeq hnorm
  have : dist x z = t := by
    rw [dist_eq_norm, hzeq]
    have hsub : x - (x + t • u c) = -(t • u c) := by abel
    rw [hsub, norm_neg, hnorm]
  simpa [dist_comm] using this

private theorem ht'At987 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a :
            ι), ∀ (p : ℝ × ℝ),
        let x := D.position a
        let rho : Real := ‖p - x‖
        ∀ (z : ℝ × ℝ), (z ∈ Metric.sphere x rho) → (∀ (t : ℝ), (dist z x = t) → (t = rho)) ) := by
  classical
  intro ι P D a p x rho z hzS t hdist
  calc t = dist z x := hdist.symm
    _ = rho := by simpa [Metric.mem_sphere, dist_eq_norm] using hzS

private theorem hnormAt994 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (u : ι → ℝ × ℝ), (∀ (c : ι),
            P.plane.adjacent a c → ‖u c‖ = (1 : ℝ)) → (∀ (d : ι), (P.plane.adjacent a d) → (∀ (t
            : ℝ), ((0 : ℝ) ≤ t) → (‖t • u d‖ = t))) ) := by
  classical
  intro ι P a u hunit d had t ht0
  rw [norm_smul, hunit d had, Real.norm_eq_abs, abs_of_nonneg ht0]
  ring

private theorem hdistAt997 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a :
            ι), ∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        ∀ (z : ℝ × ℝ), ∀ (d : ι), ∀ (t : ℝ), (z = x + t • u d) → ((‖t • u d‖ = t) → (dist z x =
            t)) ) := by
  classical
  intro ι P D a u x z d t hzeq hnorm
  have : dist x z = t := by
    rw [dist_eq_norm, hzeq]
    have hsub : x - (x + t • u d) = -(t • u d) := by abel
    rw [hsub, norm_neg, hnorm]
  simpa [dist_comm] using this

private theorem ht'At1003 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a :
            ι), ∀ (p : ℝ × ℝ),
        let x := D.position a
        let rho : Real := ‖p - x‖
        ∀ (z : ℝ × ℝ), (z ∈ Metric.sphere x rho) → (∀ (t : ℝ), (dist z x = t) → (t = rho)) ) := by
  classical
  intro ι P D a p x rho z hzS t hdist
  calc t = dist z x := hdist.symm
    _ = rho := by simpa [Metric.mem_sphere, dist_eq_norm] using hzS

private theorem hSphereConnected :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (a :
            ι), ∀ (p : ℝ × ℝ),
        let x := D.position a
        let rho : Real := ‖p - x‖
        (0 < rho) → (IsConnected (Metric.sphere x rho)) ) := by
  classical
  intro ι P D a p x rho hrho
  have hrank : 1 < Module.rank Real (Real × Real) := by
    rw [rank_prod']
    norm_num [Module.rank_self]
  exact isConnected_sphere hrank x (le_of_lt hrho)

private theorem hAopen :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (p : ℝ × ℝ),
        let x := D.position a
        let rho : Real := ‖p - x‖
        let I : Set P.plane.Face := {f | ∃ i, P.plane.faceVertex f i = a}
        let K : Set (Real × Real) := ⋃ f ∈ I, closure (F.region f)
        (∀ (z : Real × Real), (z ∈ Metric.sphere x rho) → ((z ∈ K) → (∃ δ > 0, Metric.ball z δ ⊆
            K))) → (IsOpen ((Subtype.val : Metric.sphere x rho → Real × Real) ⁻¹' K)) ) := by
  classical
  intro ι P D F a p x rho I K hKlocal
  apply Metric.isOpen_iff.mpr
  intro z hz
  obtain ⟨δ, hδ, hball⟩ := hKlocal z z.property hz
  refine ⟨δ, hδ, ?_⟩
  intro w hw
  change (w : Real × Real) ∈ K
  apply hball
  simpa [Subtype.dist_eq, Metric.mem_ball] using hw

private theorem hAnonempty :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ), (∀ (c : ι),
            P.plane.adjacent a c → ‖u c‖ = (1 : ℝ)) → (∀ (p : ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        (∀ (f : P.plane.Face), ∀ (i : Fin 3), (P.plane.faceVertex f i = a) → (∃ c d, c ≠ a ∧ d ≠
            a ∧ c ≠ d ∧ P.plane.adjacent a c ∧ P.plane.adjacent a d ∧ (∃ j, P.plane.faceVertex f
            j = c) ∧ (∃ j, P.plane.faceVertex f j = d) ∧ frontier (F.region f) ∩ B = (B ∩ {q | ∃
            t : Real, 0 ≤ t ∧ q = x + t • u c}) ∪ (B ∩ {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u d})
            ∧ Nonempty (P3889T1TwoRaySectorDecomposition x r (u c) (u d)))) → (
        let rho : Real := ‖p - x‖
        (0 < rho) → ((rho < r) → (
        let I : Set P.plane.Face := {f | ∃ i, P.plane.faceVertex f i = a}
        let K : Set (Real × Real) := ⋃ f ∈ I, closure (F.region f)
        ((Subtype.val : Metric.sphere x rho → Real × Real) ⁻¹' K).Nonempty)))) ) := by
  classical
  intro ι P D F a r u hunit p x B hincidentSectorData rho hrho hrho' I K
  let Nsub := {c : ι // P.plane.adjacent a c}
  let first (c : Nsub) : P.plane.Face :=
    Classical.choose (P.plane.every_edge_two_faces a c.1 c.2)
  let : Nontrivial ι := (P3776T1FixedGeometry P.toPeriodicTileCore).1
  obtain ⟨c, hac⟩ := (P3767T1VertexEdgeIncidence P.plane a).1
  let c' : Nsub := ⟨c, hac⟩
  let f := first c'
  have hspec := Classical.choose_spec (Classical.choose_spec
    (P.plane.every_edge_two_faces a c hac))
  obtain ⟨_, ⟨hfa, hfc⟩, _, _⟩ := hspec
  obtain ⟨i, hi⟩ := hfa
  obtain ⟨d, _, _, _, _, had, _, _, _, hfront, _⟩ := hincidentSectorData f i hi
  let q := x + rho • u d
  have hqB : q ∈ B := by
    have hnorm : ‖rho • u d‖ = rho := by
      rw [norm_smul, hunit d had, Real.norm_eq_abs, abs_of_pos hrho]
      ring
    have hdist : dist x q = rho := by
      simp [q, dist_eq_norm, hnorm]
    change dist q x < r
    rw [dist_comm, hdist]
    exact hrho'
  have hqSphere : q ∈ Metric.sphere x rho := by
    have hnorm : ‖rho • u d‖ = rho := by
      rw [norm_smul, hunit d had, Real.norm_eq_abs, abs_of_pos hrho]
      ring
    simp [q, hnorm]
  have hqfront : q ∈ frontier (F.region f) := by
    have hqray : q ∈ B ∩ {y | ∃ t : Real, 0 ≤ t ∧ y = x + t • u d} := by
      refine ⟨hqB, rho, le_of_lt hrho, ?_⟩
      rfl
    have hq' : q ∈ frontier (F.region f) ∩ B := by
      rw [hfront]
      exact Or.inl hqray
    exact hq'.1
  have hqK : q ∈ K := by
    exact Set.mem_iUnion₂.mpr ⟨f, ⟨i, hi⟩, frontier_subset_closure hqfront⟩
  exact ⟨⟨q, hqSphere⟩, hqK⟩

private theorem hAall :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (p : ℝ × ℝ),
        let x := D.position a
        let rho : Real := ‖p - x‖
        let I : Set P.plane.Face := {f | ∃ i, P.plane.faceVertex f i = a}
        let K : Set (Real × Real) := ⋃ f ∈ I, closure (F.region f)
        (IsConnected (Metric.sphere x rho)) → ((IsOpen ((Subtype.val : Metric.sphere x rho → Real
            × Real) ⁻¹' K)) → (∀ [IsClosed ((Subtype.val : Metric.sphere x rho → Real
            × Real) ⁻¹' K)], (((Subtype.val : Metric.sphere x rho → Real × Real) ⁻¹' K).Nonempty)
            → ((Subtype.val : Metric.sphere x rho → Real × Real) ⁻¹' K = Set.univ))) ) := by
  classical
  intro ι P D F a p x rho I K hSphereConnected hAopen hAclosed hAnonempty
  have hconn : ConnectedSpace (Metric.sphere x rho) := Subtype.connectedSpace hSphereConnected
  obtain hempty | hall := (connectedSpace_iff_clopen.mp hconn).2 _ ⟨hAclosed, hAopen⟩
  · exact (hAnonempty.ne_empty hempty).elim
  · exact hall

private theorem hpK :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (p : ℝ × ℝ),
        let x := D.position a
        let rho : Real := ‖p - x‖
        (p ∈ Metric.sphere x rho) → (
        let I : Set P.plane.Face := {f | ∃ i, P.plane.faceVertex f i = a}
        let K : Set (Real × Real) := ⋃ f ∈ I, closure (F.region f)
        ((Subtype.val : Metric.sphere x rho → Real × Real) ⁻¹' K = Set.univ) → (p ∈ K)) ) := by
  classical
  intro ι P D F a p x rho hpSphere I K hAall
  have : (⟨p, hpSphere⟩ : Metric.sphere x rho) ∈
      (Subtype.val : Metric.sphere x rho → Real × Real) ⁻¹' K := by
    rw [hAall]
    trivial
  exact this

private theorem hpRegion :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (p : ℝ × ℝ),
        let T := Set.range D.position ∪
          {q | ∃ c d, P.plane.adjacent c d ∧ q ∈ D.edgeArc c d}
        (∀ (f : P.plane.Face), frontier (F.region f) ⊆ T) → ((p ∉ T) → (∀ (f : P.plane.Face), (p
            ∈ closure (F.region f)) → (p ∈ F.region f))) ) := by
  classical
  intro ι P D F p T hfrontTrace hpNotT f hpc
  rw [closure_eq_self_union_frontier] at hpc
  rcases hpc with hpr | hpf
  · exact hpr
  · have hpTrace : p ∈ T := hfrontTrace f hpf
    exact (hpNotT hpTrace).elim

end FaceGapProof

namespace FaceGapSectorGeometry

private theorem hfaceFillsSector :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (a : ι), ∀ (r : ℝ), ((0 : ℝ) < r) → (∀ (u : ι → ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        (∀ (f : P.plane.Face), ∀ (i : Fin (3 : ℕ)), P.plane.faceVertex f i = a → ∃ (c : ι) (d :
            ι), c ≠ a ∧ d ≠ a ∧ c ≠ d ∧ P.plane.adjacent a c ∧ P.plane.adjacent a d ∧ (∃ (j : Fin
            (3 : ℕ)), P.plane.faceVertex f j = c) ∧ (∃ (j : Fin (3 : ℕ)), P.plane.faceVertex f j
            = d) ∧ frontier (F.region f) ∩ Metric.ball (D.position a) r = Metric.ball (D.position
            a) r ∩ {q : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ q = D.position a + t • u c} ∪
            Metric.ball (D.position a) r ∩ {q : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ q = D.position a
            + t • u d} ∧ Nonempty (P3889T1TwoRaySectorDecomposition (D.position a) r (u c) (u
            d))) → (∀ (f : P.plane.Face), ∀ (i : Fin (3 : ℕ)), P.plane.faceVertex f i = a → ∃ (c
            : ι) (d : ι), c ≠ a ∧ d ≠ a ∧ c ≠ d ∧ P.plane.adjacent a c ∧ P.plane.adjacent a d ∧
            (∃ (j : Fin (3 : ℕ)), P.plane.faceVertex f j = c) ∧ (∃ (j : Fin (3 : ℕ)),
            P.plane.faceVertex f j = d) ∧ ∃ (S : P3889T1TwoRaySectorDecomposition x r (u c) (u
            d)), F.region f ∩ B = S.left ∨ F.region f ∩ B = S.right)) ) := by
  classical
  intro ι P D F a r hr u x B hincidentSectorData f i hi
  obtain ⟨c, d, hca, hda, hcd, hac, had, hci, hdi, hfront, ⟨S⟩⟩ :=
    hincidentSectorData f i hi
  let U := F.region f
  let V := (closure U)ᶜ
  have hxB : x ∈ B := by simp [B, Metric.mem_ball_self hr]
  have hxfront := FaceGapProof.hxfront ι P D F a r u f c d hfront (FaceGapProof.hxray ι P D a r
      u c hxB)
  have rayFront (q : Real × Real) (hqB : q ∈ B)
      (hqRay : q ∈ {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u c} ∪
        {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u d}) := FaceGapProof.rayFront ι
            P D F a r u f c d hfront q hqB hqRay
  have hLsub := FaceGapProof.hLsub ι P D a r u c d S
  have hRsub := FaceGapProof.hRsub ι P D a r u c d S
  have hLavoid := FaceGapProof.hLavoid ι P D F a r u f c d
      hfront S hLsub
  have hRavoid := FaceGapProof.hRavoid ι P D F a r u f c d
      hfront S hRsub
  have hUopen : IsOpen U := F.region_open f
  have hUV := FaceGapProof.hUV ι P D F f
  have hfill := FaceGapProof.hfill ι P D F a r u f c d S (FaceGapProof.hLchoice ι P D F a r u f
      c d S hLavoid (FaceGapProof.hLavoidV ι P D F a r u f c d S hLavoid) hUopen
      (FaceGapProof.hLpart ι P D F a r u f c d S hLavoid hUopen)) (FaceGapProof.hRchoice ι P D
      F a r u f c d S hRavoid (FaceGapProof.hRavoidV ι P D F a r u f c d S hRavoid) hUopen
      (FaceGapProof.hRpart ι P D F a r u f c d S hRavoid hUopen))
          (FaceGapProof.hnotUU ι P D F a r u f c d S rayFront (FaceGapProof.hmeetV ι P D F a r
              hr f (FaceGapProof.hxfrontV ι P D F a f hxfront))) (FaceGapProof.hnotVV ι P D F a
              r u f c d S rayFront (FaceGapProof.hmeetU ι P D F a r hr f hxfront) hUopen hUV)
  refine ⟨c, d, hca, hda, hcd, hac, had, hci, hdi, S, ?_⟩
  rcases hfill with ⟨hL, hR⟩ | ⟨hR, hL⟩
  · left
    ext q
    constructor
    · intro hq
      have hqNotRay := FaceGapProof.hqNotRayAt457 ι P D F a r
              u f c d rayFront hUopen q hq
      have hqsec := FaceGapProof.hqsecAt467 ι P D F a r u f c d S q hq
          hqNotRay
      rcases hqsec with hqL | hqR
      · exact hqL
      · exact ((Set.disjoint_left.mp hUV) hq.1 (hR hqR)).elim
    · intro hq
      exact ⟨hL hq, (hLsub hq).1⟩
  · right
    ext q
    constructor
    · intro hq
      have hqNotRay := FaceGapProof.hqNotRayAt479 ι P D F a r
              u f c d rayFront hUopen q hq
      have hqsec := FaceGapProof.hqsecAt489 ι P D F a r u f c d S q hq
          hqNotRay
      rcases hqsec with hqL | hqR
      · exact ((Set.disjoint_left.mp hUV) hq.1 (hL hqL)).elim
      · exact hqR
    · intro hq
      exact ⟨hR hq, (hRsub hq).1⟩

private theorem hKlocal :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), (Pairwise fun (f g : P.plane.Face) => Disjoint (F.region
            f) (F.region g)) → (∀ (a : ι), ∀ (r : ℝ), ∀ (u : ι → ℝ × ℝ), (∀ (c : ι),
            P.plane.adjacent a c → ‖u c‖ = (1 : ℝ)) → (∀ (p : ℝ × ℝ),
        let x := D.position a
        let B := Metric.ball x r
        (∀ (f : P.plane.Face), ∀ (i : Fin (3 : ℕ)), P.plane.faceVertex f i = a → ∃ (c : ι) (d :
            ι), c ≠ a ∧ d ≠ a ∧ c ≠ d ∧ P.plane.adjacent a c ∧ P.plane.adjacent a d ∧ (∃ (j : Fin
            (3 : ℕ)), P.plane.faceVertex f j = c) ∧ (∃ (j : Fin (3 : ℕ)), P.plane.faceVertex f j
            = d) ∧ frontier (F.region f) ∩ Metric.ball (D.position a) r = Metric.ball (D.position
            a) r ∩ {q : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ q = D.position a + t • u c} ∪
            Metric.ball (D.position a) r ∩ {q : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ q = D.position a
            + t • u d} ∧ Nonempty (P3889T1TwoRaySectorDecomposition (D.position a) r (u c) (u
            d))) → ((∀ (f : P.plane.Face), ∀ (i : Fin 3), (P.plane.faceVertex f i = a) → (∃ c d,
            c ≠ a ∧ d ≠ a ∧ c ≠ d ∧ P.plane.adjacent a c ∧ P.plane.adjacent a d ∧ (∃ j,
            P.plane.faceVertex f j = c) ∧ (∃ j, P.plane.faceVertex f j = d) ∧ ∃ S :
            P3889T1TwoRaySectorDecomposition x r (u c) (u d), F.region f ∩ B = S.left ∨
            F.region f ∩ B = S.right)) → (
        let rho : Real := ‖p - x‖
        (
        let rho := ‖p - D.position a‖; (0 : ℝ) < rho) → ((
        let rho := ‖p - D.position a‖; rho < r) → (
        let I : Set P.plane.Face := {f | ∃ i, P.plane.faceVertex f i = a}
        (∀ (g : P.plane.Face), ∀ (j : Fin (3 : ℕ)), P.plane.faceVertex g j = a → ∀ (e : ι), (∃ (k
            : Fin (3 : ℕ)), P.plane.faceVertex g k = e) → e ≠ a → ∀ (c : ι), ∀ (d : ι), c ≠ a → d
            ≠ a → c ≠ d → (∃ (k : Fin (3 : ℕ)), P.plane.faceVertex g k = c) → (∃ (k : Fin (3 :
            ℕ)), P.plane.faceVertex g k = d) → e = c ∨ e = d) → (
        let K : Set (Real × Real) := ⋃ f ∈ I, closure (F.region f)
        ∀ z ∈ Metric.sphere x rho, z ∈ K → ∃ δ > (0 : ℝ), Metric.ball z δ ⊆ K))))))) ) := by
  classical
  intro ι P D F hd a r u hunit p x B hincidentSectorData hfaceFillsSector rho hrho hrho' I
      faceOtherMatch K z hzS hzK
  let Nsub := {c : ι // P.plane.adjacent a c}
  let first (c : Nsub) : P.plane.Face :=
    Classical.choose (P.plane.every_edge_two_faces a c.1 c.2)
  let second (c : Nsub) : P.plane.Face :=
    Classical.choose (Classical.choose_spec
      (P.plane.every_edge_two_faces a c.1 c.2))
  obtain ⟨f, hfI, hzcl⟩ := Set.mem_iUnion₂.mp hzK
  obtain ⟨i, hi⟩ := hfI
  rw [closure_eq_self_union_frontier] at hzcl
  rcases hzcl with hzreg | hzfront
  · obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (F.region_open f) z hzreg
    refine ⟨δ, hδ, ?_⟩
    intro q hq
    exact Set.mem_iUnion₂.mpr ⟨f, ⟨i, hi⟩, subset_closure (hball hq)⟩
  · have hzB : z ∈ B := FaceGapProof.hzB ι P D a r p hrho' z hzS
    obtain ⟨c, d, hca, hda, hcd, hac, had, hci, hdi, hfront, _⟩ :=
      hincidentSectorData f i hi
    have hzRays := FaceGapProof.hzRays ι P D F a r
            u z f hzfront hzB c d hfront
    have localSide (g : P.plane.Face) (j : Fin 3)
        (hj : P.plane.faceVertex g j = a) (e : ι)
        (he : ∃ k, P.plane.faceVertex g k = e) (hea : e ≠ a)
        (t : Real) (ht : 0 < t) (htr : t < r)
        (hzeq : z = x + t • u e) := FaceGapProof.localSide ι P D F a r u hfaceFillsSector
                    faceOtherMatch z g j hj e he hea t ht htr hzeq
    have finishRay (e : ι) (he : ∃ k, P.plane.faceVertex f k = e)
        (hea : e ≠ a) (hae : P.plane.adjacent a e)
        (t : Real) (ht : 0 < t) (htr : t < r)
        (hzeq : z = x + t • u e) :
        ∃ δ > 0, Metric.ball z δ ⊆ K := by
      let en : Nsub := ⟨e, hae⟩
      let f0 := first en
      let f1 := second en
      obtain ⟨hne, hf0, hf1, hexhaust⟩ := (Classical.choose_spec (Classical.choose_spec
          (P.plane.every_edge_two_faces a e hae)))
      obtain ⟨hf0a, hf0e⟩ := hf0
      obtain ⟨hf1a, hf1e⟩ := hf1
      have hcase := hexhaust f ⟨⟨i, hi⟩, he⟩
      let g := if f = f0 then f1 else f0
      have hfg := FaceGapProof.hfg ι P a c f e hae hne
      have hgE := FaceGapProof.hgE ι P a c f e hae hf0e hf1e
      obtain ⟨j, hj⟩ := (FaceGapProof.hgI ι P a c f e hae hf0a hf1a)
      obtain ⟨δ₁, hδ₁, hball₁, hside₁⟩ :=
        localSide f i hi e he hea t ht htr hzeq
      obtain ⟨δ₂, hδ₂, hball₂, hside₂⟩ :=
        localSide g j hj e hgE hea t ht htr hzeq
      let eps := min δ₁ (min δ₂ t) / 2
      have heps : 0 < eps := by dsimp [eps]; positivity
      have heps₁ := FaceGapProof.heps₁ t δ₁ hδ₁ δ₂
      have heps₂ := FaceGapProof.heps₂ t δ₁ δ₂ hδ₂
      have hball₂' := FaceGapProof.hball₂' ι P D a r z t δ₁ δ₂ hball₂
          heps₂
      have hzeroK := FaceGapProof.hzeroK ι P
              D F a r u hunit hincidentSectorData c faceOtherMatch f z i hi e he hea hae t hzeq
              hgE j hj δ₁ δ₂ (FaceGapProof.hepst t ht δ₁ δ₂) (FaceGapProof.hball₁' ι P D a r z
                  t δ₁ hball₁ δ₂ heps₁)
      have memK (g : P.plane.Face) (j : Fin 3)
          (hj : P.plane.faceVertex g j = a) (q : Real × Real)
          (hq : q ∈ F.region g) := FaceGapProof.memK ι P D F a f g j hj q hq
      rcases hside₁ with hpos₁ | hneg₁ <;> rcases hside₂ with hpos₂ | hneg₂
      · exfalso
        let v : Real × Real := (-(u e).2, (u e).1)
        have hvnorm : ‖v‖ = 1 := by
          simpa [v, Prod.norm_def, Real.norm_eq_abs, max_comm] using hunit e hae
        have hu := FaceGapProof.huAt878 ι P a u hunit e hae
        have hsum := FaceGapProof.hsumAt883 ι u e hu
        let qplus := z + eps • v
        have hdetplus := FaceGapProof.hdetplus
                ι u z e t δ₁ δ₂ heps hsum
        exact (Set.disjoint_left.mp (hd hfg) (hpos₁ qplus (FaceGapProof.hqplus1 ι u z e t δ₁ δ₂
            heps heps₁ hvnorm) hdetplus)
          (hpos₂ qplus (FaceGapProof.hqplus2 ι u z e t δ₁ δ₂ heps heps₂ hvnorm) hdetplus))
      · refine ⟨eps, heps, (FaceGapProof.build ι P D F a u c f z i hi e hae t j hj δ₁ δ₂ hzeroK
          memK) ?_ ?_⟩
        · intro q hq hqpos
          exact hpos₁ q (Metric.ball_subset_ball (le_of_lt heps₁) hq) hqpos
        · intro q hq hqneg
          exact hneg₂ q (Metric.ball_subset_ball (le_of_lt heps₂) hq) hqneg
      · refine ⟨eps, heps, ?_⟩
        intro q hq
        by_cases hqpos : 0 < (u e).1 * (q.2 - z.2) - (u e).2 * (q.1 - z.1)
        · exact memK g j hj q (hpos₂ q (Metric.ball_subset_ball (le_of_lt heps₂) hq) hqpos)
        · by_cases hqneg : (u e).1 * (q.2 - z.2) - (u e).2 * (q.1 - z.1) < 0
          · exact memK f i hi q (hneg₁ q (Metric.ball_subset_ball (le_of_lt heps₁) hq) hqneg)
          · exact hzeroK q hq (by linarith)
      · exfalso
        let v : Real × Real := (-(u e).2, (u e).1)
        have hvnorm : ‖v‖ = 1 := by
          simpa [v, Prod.norm_def, Real.norm_eq_abs, max_comm] using hunit e hae
        have hu := FaceGapProof.huAt935 ι P a u hunit e hae
        have hsum := FaceGapProof.hsumAt940 ι u e hu
        let qminus := z + eps • (-v)
        have hdetminus := FaceGapProof.hdetminus ι u z e t δ₁ δ₂ heps hsum
        exact (Set.disjoint_left.mp (hd hfg) (hneg₁ qminus (FaceGapProof.hqminus1 ι u z e t δ₁
            δ₂ heps heps₁ hvnorm) hdetminus)
          (hneg₂ qminus (FaceGapProof.hqminus2 ι u z e t δ₁ δ₂ heps heps₂ hvnorm) hdetminus))
    rcases hzRays with hzc | hzd
    · obtain ⟨t, ht0, hzeq⟩ := hzc.2
      have hnorm := FaceGapProof.hnormAt978 ι P a u hunit c hac t ht0
      have hdist := FaceGapProof.hdistAt981 ι P D a u z c t hzeq hnorm
      have ht' := FaceGapProof.ht'At987 ι P D a p z hzS t hdist
      have htpos : 0 < t := by rw [ht']; exact hrho
      have htr : t < r := by rw [ht']; exact hrho'
      exact finishRay c hci hca hac t htpos htr hzeq
    · obtain ⟨t, ht0, hzeq⟩ := hzd.2
      have hnorm := FaceGapProof.hnormAt994 ι P a u hunit d had t ht0
      have hdist := FaceGapProof.hdistAt997 ι P D a u z d t hzeq hnorm
      have ht' := FaceGapProof.ht'At1003 ι P D a p z hzS t hdist
      have htpos : 0 < t := by rw [ht']; exact hrho
      have htr : t < r := by rw [ht']; exact hrho'
      exact finishRay d hdi hda had t htpos htr hzeq

end FaceGapSectorGeometry

theorem P3889T1FaceGapCoverage :
    ∀ {ι : Type}, ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
        P3861T1FacialDomains P D), (Pairwise (fun f g : P.plane.Face => Disjoint (F.region f)
        (F.region g))) → (∀ (a : ι), ∀ (r : Real), (0 < r) → (∀ (u : ι → Real × Real), (∀ c,
        P.plane.adjacent a c → ‖u c‖ = 1) → ((∀ c, ∀ d, P.plane.adjacent a c → P.plane.adjacent a
        d →
      u c = u d → c = d) → ((∀ c, P.plane.adjacent a c →
      D.edgeArc a c ∩ Metric.ball (D.position a) r =
        Metric.ball (D.position a) r ∩
          {p | ∃ t : Real, 0 ≤ t ∧ p = D.position a + t • u c}) → ((∀ c, ∀ d, P.plane.adjacent c
              d → c ≠ a → d ≠ a →
      Disjoint (D.edgeArc c d) (Metric.ball (D.position a) r)) → (((Set.range D.position ∪
        {p | ∃ c d, P.plane.adjacent c d ∧ p ∈ D.edgeArc c d}) ∩
        Metric.ball (D.position a) r =
      Metric.ball (D.position a) r ∩
        {p | ∃ c, P.plane.adjacent a c ∧
          ∃ t : Real, 0 ≤ t ∧ p = D.position a + t • u c}) → ((∀ c, ∀ d, P.plane.adjacent a c →
              P.plane.adjacent a d → c ≠ d →
      Nonempty (P3889T1TwoRaySectorDecomposition
        (D.position a) r (u c) (u d))) → (∀ p ∈ Metric.ball (D.position a) r,
      p ∉ Set.range D.position ∪
        {q | ∃ c d, P.plane.adjacent c d ∧ q ∈ D.edgeArc c d} →
      ∃ f : P.plane.Face, (∃ i, P.plane.faceVertex f i = a) ∧ p ∈ F.region f)))))))) := by
  intro ι P D F hd a r hr u hunit hinj hedge hforeign htrace hsectors
-- BODY
  classical
  intro p hp hnot
  let x := D.position a
  let B := Metric.ball x r
  let T := Set.range D.position ∪
    {q | ∃ c d, P.plane.adjacent c d ∧ q ∈ D.edgeArc c d}
  have hpB : p ∈ B := hp
  have hpNotT : p ∉ T := hnot
  have hpNotRay (c : ι) (hac : P.plane.adjacent a c) := FaceGapProof.hpNotRay ι P D a r u p hpB
          (FaceGapProof.hpNotRays ι P D a r u htrace p hpNotT) c hac
  let N : Set ι := {c | P.plane.adjacent a c}
  have hincidentSectorData (f : P.plane.Face) (i : Fin 3)
      (hi : P.plane.faceVertex f i = a) := FaceGapProof.hincidentSectorData ι P D F a r u hedge
          hsectors (FaceGapProof.hfaceFrontier ι P D F a r hforeign) f i hi
  have hfaceFillsSector (f : P.plane.Face) (i : Fin 3)
      (hi : P.plane.faceVertex f i = a) :
      ∃ c d, c ≠ a ∧ d ≠ a ∧ c ≠ d ∧ P.plane.adjacent a c ∧
        P.plane.adjacent a d ∧ (∃ j, P.plane.faceVertex f j = c) ∧
        (∃ j, P.plane.faceVertex f j = d) ∧
        ∃ S : P3889T1TwoRaySectorDecomposition x r (u c) (u d),
          F.region f ∩ B = S.left ∨ F.region f ∩ B = S.right :=
              FaceGapSectorGeometry.hfaceFillsSector ι P D F a r hr u hincidentSectorData f i hi
  let rho : Real := ‖p - x‖
  have hrho := FaceGapProof.hrho ι P D a p hpNotT
  have hrho' := FaceGapProof.hrho' ι P D a r p hpB
  have hpSphere : p ∈ Metric.sphere x rho := by
    simp [rho]
  let I : Set P.plane.Face := {f | ∃ i, P.plane.faceVertex f i = a}
  let Nsub := {c : ι // P.plane.adjacent a c}
  let first (c : Nsub) : P.plane.Face :=
    Classical.choose (P.plane.every_edge_two_faces a c.1 c.2)
  let second (c : Nsub) : P.plane.Face :=
    Classical.choose (Classical.choose_spec
      (P.plane.every_edge_two_faces a c.1 c.2))
  let facePick : Nsub × Fin 2 → P.plane.Face := fun z =>
    if z.2 = 0 then first z.1 else second z.1
  have faceOtherMatch (g : P.plane.Face) (j : Fin 3)
      (hj : P.plane.faceVertex g j = a) (e : ι)
      (he : ∃ k, P.plane.faceVertex g k = e) (hea : e ≠ a)
      (c d : ι) (hca : c ≠ a) (hda : d ≠ a) (hcd : c ≠ d)
      (hc : ∃ k, P.plane.faceVertex g k = c)
      (hd : ∃ k, P.plane.faceVertex g k = d) := FaceGapProof.faceOtherMatch ι P a
          g j hj e he hea c d hca hda hcd hc hd
  let K : Set (Real × Real) := ⋃ f ∈ I, closure (F.region f)
  have hKclosed : IsClosed K := by
    exact (FaceGapProof.hIfinite ι P a (FaceGapProof.hfinitePick ι P a (P.plane.locally_finite
        a))).isClosed_biUnion (fun f _ => isClosed_closure)
  have hKlocal (z : Real × Real) (hzS : z ∈ Metric.sphere x rho)
      (hzK : z ∈ K) : ∃ δ > 0, Metric.ball z δ ⊆ K := FaceGapSectorGeometry.hKlocal ι P D F hd a
          r u hunit p hincidentSectorData hfaceFillsSector hrho hrho' faceOtherMatch z hzS hzK
  have hSnonempty : (Metric.sphere x rho).Nonempty := by
    exact ⟨p, hpSphere⟩
  have hAclosed : IsClosed ((Subtype.val : Metric.sphere x rho → Real × Real) ⁻¹' K) :=
    hKclosed.preimage continuous_subtype_val
  obtain ⟨f, hfI, hpc⟩ := Set.mem_iUnion₂.mp (FaceGapProof.hpK ι P D F a p hpSphere
      (FaceGapProof.hAall ι P D F a p (FaceGapProof.hSphereConnected ι P D a p hrho)
      (FaceGapProof.hAopen ι P D F a p hKlocal) (FaceGapProof.hAnonempty ι P D F a r u hunit p
      hincidentSectorData hrho hrho')))
  exact ⟨f, hfI, (FaceGapProof.hpRegion ι P D F p (FaceGapProof.hfrontTrace ι P D F) hpNotT f hpc)⟩

end ApollonianSuperharmonic

end
