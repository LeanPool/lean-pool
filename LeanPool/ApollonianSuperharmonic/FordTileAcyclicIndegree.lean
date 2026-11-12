/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4062T1LiteralReduction
public import LeanPool.ApollonianSuperharmonic.P4062T1OrientationTransport
public import LeanPool.ApollonianSuperharmonic.P4062T1ParentalRestriction
public import LeanPool.ApollonianSuperharmonic.P4062T1OverlapDescent
public import LeanPool.ApollonianSuperharmonic.P4062T1InteriorGeometry
public import LeanPool.ApollonianSuperharmonic.P4062T1ParentGluing
public import LeanPool.ApollonianSuperharmonic.P4062T1RemainderGeometry
public import LeanPool.ApollonianSuperharmonic.P4062T1RankedAttachment
public import LeanPool.ApollonianSuperharmonic.FordLaplacianTable

-- [TABLET NODE: FordTileAcyclicIndegree]

/-!
# FordTileAcyclicIndegree

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem FordTileAcyclicIndegree (P : FordFareyParameter)
    (T : ProtoTile) (h : PartialOdometer) (g : IntegerLatticeFunction)
    (hT : BandPrototile (FordCircleCoordinate P.p P.q) T)
    (hodo : TileOdometer (FordCircleCoordinate P.p P.q) T h)
    (hdom : (h.domain : Set GaussianInt) = FootprintVertices T)
    (hext : GlobalOdometerExtends g h) :
    let D := h.domain.filter fun x =>
      @decide (x ∉ BoundaryFootprintVertices T) (Classical.propDecidable _)
    Nonempty (AcyclicIndegreeOrientation D
      (fun x => 2 + FourNeighborLaplacian g x)) := by
-- BODY
  classical
  have squareCoordinates (q : Nat) (x : GaussianInt) :
      x ∈ P4062T1InteriorSquare q ↔
        1 ≤ x.re ∧ x.re ≤ (q : Int) - 1 ∧
        1 ≤ x.im ∧ x.im ≤ (q : Int) - 1 := by
    unfold P4062T1InteriorSquare
    constructor
    · intro hx
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      exact ⟨(Finset.mem_Icc.mp ha).1, (Finset.mem_Icc.mp ha).2,
        (Finset.mem_Icc.mp hb).1, (Finset.mem_Icc.mp hb).2⟩
    · intro h
      exact Finset.mem_image.mpr ⟨(x.re, x.im),
        Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩,
          Finset.mem_Icc.mpr h.2.2⟩, by cases x; rfl⟩
  have main : ∀ n, ∀ P : FordFareyParameter, P.q = n →
      Nonempty (AcyclicIndegreeOrientation (P4062T1InteriorSquare P.q)
        (fun x => 2 + FourNeighborLaplacian (FordOdometer P) x)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hn
      let σ : GaussianInt → Int := fun x => 2 + FourNeighborLaplacian (FordOdometer P) x
      have empty (D : Finset GaussianInt) (hD : D = ∅) :
          Nonempty (AcyclicIndegreeOrientation D σ) := by
        subst D
        exact ⟨{
          edge := fun _ _ => False
          edge_decidable := fun _ _ => Classical.propDecidable _
          rank := fun _ => 0
          supported := by intro x y he; cases he
          oriented := by intro x hx; simp at hx
          increasing := by intro x y he; cases he
          indegree := by intro x hx; simp at hx }⟩
      by_cases h1 : P.q = 1
      · apply empty
        ext x
        simp only [squareCoordinates, h1, Finset.notMem_empty, iff_false]
        omega
      by_cases h2 : P.q = 2
      · have htwo_data : P.q₁ = 1 ∧ P.q₂ = 1 := by
          have hs := P.sum_q
          have ht := P.q₁_lt
          have hp := P.q₂_pos
          have hd := P.det₁
          rw [h2] at hs ht hd
          by_cases hz : P.q₁ = 0
          · rw [hz] at hd
            norm_num at hd
            omega
          · constructor <;> omega
        let x₀ : GaussianInt := ⟨1, 1⟩
        have hunit : P4062T1InteriorSquare P.q = {x₀} := by
          ext x
          rw [squareCoordinates, Finset.mem_singleton]
          constructor
          · intro hx
            ext <;> dsimp [x₀] <;> omega
          · rintro rfl
            norm_num [x₀, h2]
        have hmult : FordBoundaryMultiplicity P x₀ = 4 := by
          obtain ⟨hqa, hqb⟩ := htwo_data
          unfold FordBoundaryMultiplicity
          have hmem : ∀ i : Fin 4,
              x₀ ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P i) := by
            intro i
            fin_cases i
            · refine ⟨?_, ⟨⟨2, 1⟩, ?_, ?_, ?_⟩⟩
              · simp [FordRecursiveVertexDomains, hqa, hqb, h2, x₀]
              · simp [FordRecursiveVertexDomains, hqa, hqb, h2]
              · norm_num [x₀]
              · norm_num [x₀]
            · refine ⟨?_, ⟨⟨0, 1⟩, ?_, ?_, ?_⟩⟩
              · simp [FordRecursiveVertexDomains, hqa, hqb, h2, x₀]
              · simp [FordRecursiveVertexDomains, hqa, hqb, h2]
              · norm_num [x₀]
              · norm_num [x₀]
            · refine ⟨?_, ⟨⟨1, 2⟩, ?_, ?_, ?_⟩⟩
              · simp [FordRecursiveVertexDomains, hqa, hqb, h2, x₀]
              · simp [FordRecursiveVertexDomains, hqa, hqb, h2]
              · norm_num [x₀]
              · norm_num [x₀]
            · refine ⟨?_, ⟨⟨1, 0⟩, ?_, ?_, ?_⟩⟩
              · simp [FordRecursiveVertexDomains, hqa, hqb, h2, x₀]
              · simp [FordRecursiveVertexDomains, hqa, hqb, h2]
              · norm_num [x₀]
              · norm_num [x₀]
          have hfilter : (Finset.univ.filter fun i : Fin 4 =>
              x₀ ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P i)) =
              Finset.univ := by
            ext i
            simp [hmem i]
          rw [hfilter]
          simp
        have htable := (FordLaplacianTable P).2.2 (by omega) x₀
          (by norm_num [x₀]) (by rw [h2]; norm_num [x₀])
          (by norm_num [x₀]) (by rw [h2]; norm_num [x₀])
        have hlap : FourNeighborLaplacian (FordOdometer P) x₀ = -2 := by
          exact htable.2.2 (by rw [hmult])
        have hsigma : σ x₀ = 0 := by simp [σ, hlap]
        let o₀ : AcyclicIndegreeOrientation {x₀} σ := {
          edge := fun _ _ => False
          edge_decidable := fun _ _ => Classical.propDecidable _
          rank := fun _ => 0
          supported := by intro x y he; cases he
          oriented := by
            intro x hx y hy hadj
            have hx' : x = x₀ := Finset.mem_singleton.mp hx
            have hy' : y = x₀ := Finset.mem_singleton.mp hy
            subst x
            subst y
            rcases hadj with he | he | he | he
            · have hr := congrArg Zsqrtd.re he
              norm_num [x₀] at hr
            · have hr := congrArg Zsqrtd.re he
              norm_num [x₀] at hr
            · have hi := congrArg Zsqrtd.im he
              norm_num [x₀] at hi
            · have hi := congrArg Zsqrtd.im he
              norm_num [x₀] at hi
          increasing := by intro x y he; cases he
          indegree := by
            intro x hx
            have hx' : x = x₀ := Finset.mem_singleton.mp hx
            subst x
            simp [hsigma]
        }
        rw [hunit]
        exact ⟨o₀⟩
      have hbig : 2 < P.q := by have hp := P.q_pos; omega
      let A := P4062T1RecursiveInteriors P
      obtain ⟨P₁, P₂, hp₁, hq₁, hp₂, hq₂, hsmall₁, hsmall₂, hne, hrest⟩ :=
        P4062T1ParentalRestriction P hbig
      have kids : ∀ i, Nonempty (AcyclicIndegreeOrientation (A i) σ) := by
        intro i
        let R := if i.val < 2 then P₁ else P₂
        let u : GaussianInt :=
          ![0, ⟨(P.q₂ : Int), (P.q₂ : Int)⟩,
            ⟨(P.q₁ : Int), 0⟩, ⟨0, (P.q₁ : Int)⟩] i
        have hR : R.q < n := by
          dsimp only [R]
          split <;> omega
        obtain ⟨o⟩ := ih R.q hR R rfl
        have hr := hrest i
        obtain ⟨t, _, _⟩ := P4062T1OrientationTransport
          (P4062T1InteriorSquare R.q) (A i)
          (fun x => 2 + FourNeighborLaplacian (FordOdometer R) x) σ u hr.1
          (by intro x hx; change 2 + _ = 2 + _; rw [hr.2 x hx]) o
        exact ⟨t⟩
      obtain ⟨hsub, hcross, hdis, hsep, hempty₂, hempty₀⟩ :=
        P4062T1InteriorGeometry P hbig
      have desc := P4062T1OverlapDescent P P₁ P₂ hbig hp₁ hq₁ hp₂ hq₂
      have overlaps :
          Nonempty (AcyclicIndegreeOrientation (A 0 ∩ A 1) σ) ∧
          Nonempty (AcyclicIndegreeOrientation (A 2 ∩ A 3) σ) := by
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · obtain ⟨H, hHp, hHq, hHsmall, hPp₁, hPq₁, hPp₂, hPq₂, hset, hlap⟩ :=
            desc.2 hlt
          obtain ⟨oH⟩ := ih H.q (by omega) H rfl
          obtain ⟨t, _, _⟩ := P4062T1OrientationTransport _ (A 2 ∩ A 3)
            (fun x => 2 + FourNeighborLaplacian (FordOdometer H) x) σ
            ⟨(P.q₁ : Int), (P.q₁ : Int)⟩ hset
            (by intro x hx; change 2 + _ = 2 + _; rw [hlap x hx]) oH
          exact ⟨empty _ (hempty₀ hlt), ⟨t⟩⟩
        · obtain ⟨H, hHp, hHq, hHsmall, hPp₁, hPq₁, hPp₂, hPq₂, hset, hlap⟩ :=
            desc.1 hgt
          obtain ⟨oH⟩ := ih H.q (by omega) H rfl
          obtain ⟨t, _, _⟩ := P4062T1OrientationTransport _ (A 0 ∩ A 1)
            (fun x => 2 + FourNeighborLaplacian (FordOdometer H) x) σ
            ⟨(P.q₂ : Int), (P.q₂ : Int)⟩ hset
            (by intro x hx; change 2 + _ = 2 + _; rw [hlap x hx]) oH
          exact ⟨⟨t⟩, empty _ (hempty₂ hgt)⟩
      obtain ⟨oE, hpreserve⟩ := P4062T1ParentGluing P hbig σ
        (fun i => Classical.choice (kids i))
        (Classical.choice overlaps.1) (Classical.choice overlaps.2)
      obtain ⟨hE, hW, hdisW, hsepW, hedges, hcounts, hres, hstrict⟩ :=
        P4062T1RemainderGeometry P hbig
      obtain ⟨t, _⟩ := P4062T1RankedAttachment
        (P4062T1InteriorSquare P.q) _ σ _ hE oE
        (by intro x hx; simpa only [σ] using hres x hx) hstrict
      exact ⟨t⟩
  obtain ⟨u, hD, hlap⟩ := P4062T1LiteralReduction P T h g hT hodo hdom hext
  obtain ⟨o⟩ := main P.q P rfl
  obtain ⟨t, _, _⟩ := P4062T1OrientationTransport _ _
    (fun x => 2 + FourNeighborLaplacian (FordOdometer P) x)
    (fun x => 2 + FourNeighborLaplacian g x) u hD
    (by intro x hx; rw [hlap x hx]) o
  exact ⟨t⟩

end ApollonianSuperharmonic

end
