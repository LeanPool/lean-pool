/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FiniteAcyclicOrientationObstruction
public import LeanPool.ApollonianSuperharmonic.FordExceptionalLattice
public import LeanPool.ApollonianSuperharmonic.FordOdometer
public import LeanPool.ApollonianSuperharmonic.FordPeakMatrix
public import LeanPool.ApollonianSuperharmonic.FourNeighborConnected
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import LeanPool.ApollonianSuperharmonic.P5442T1LaplacianBound
public import LeanPool.ApollonianSuperharmonic.FordTileAcyclicIndegree

-- [TABLET NODE: FordExceptionalMaximality]

/-!
# FordExceptionalMaximality

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem FordExceptionalMaximality (P : FordFareyParameter) :
    (∀ x, FourNeighborLaplacian (FordOdometer P) x <= 1) ∧
    (∀ v, v ∈ FordExceptionalLattice P -> ∃ a : GaussianInt,
      Matrix.mulVec (FordPeakMatrix P.p P.q P.q_pos P.reduced)
        ![(v.re : Real), (v.im : Real)] =
          ![(a.re : Real), (a.im : Real)] ∧
      ∀ x, FordOdometer P (x + v) = FordOdometer P x +
        x.re * a.re + x.im * a.im + FordOdometer P v) ∧
    (∀ X : Set GaussianInt, X.Infinite -> FourNeighborConnected X ->
      (∀ x, FourNeighborLaplacian
        (fun y => FordOdometer P y +
          Set.indicator X (fun _ => (1 : Int)) y) x <= 1) ->
      X = Set.univ) := by
-- BODY
  classical
  refine ⟨P5442T1LaplacianBound P, P5442T1Cocycle P, ?_⟩
  intro X hInf hX hbound
  let g := FordOdometer P
  let t : Int → Int → GaussianInt := fun m n =>
    ⟨n * (P.q : Int), n * (P.q₁ : Int) - m * (P.q : Int)⟩
  let W : Set GaussianInt := {x | ∃ m n : Int,
    x - t m n ∈ LatticeVertexBoundary (FordVertexDomain P.q)}
  obtain ⟨periods, webLap, webConnected, owner⟩ := P5442T1WebGeometry P
  change (∀ m n, t m n ∈ FordExceptionalLattice P ∧
    ∀ x, FourNeighborLaplacian g (x + t m n) = FourNeighborLaplacian g x) at periods
  change (∀ x ∈ W, FourNeighborLaplacian g x = 1) at webLap
  change FourNeighborConnected W at webConnected
  change (∀ x, x ∉ W → ∃ m n : Int, ∀ y,
    Relation.ReflTransGen (fun u z => u ∉ W ∧ z ∉ W ∧ FourNeighborAdjacent u z) x y →
    y - t m n ∈ P4062T1InteriorSquare P.q) at owner
  have connectedReach (S : Set GaussianInt) (hS : FourNeighborConnected S)
      (x : GaussianInt) (hx : x ∈ S) (y : GaussianInt) (hy : y ∈ S) :
      Relation.ReflTransGen (fun u z => u ∈ S ∧ z ∈ S ∧ FourNeighborAdjacent u z) x y := by
    obtain ⟨p, hp, hlast, pall, padj⟩ := hS.2 x hx y hy
    have hc : p.IsChain (fun u z => u ∈ S ∧ z ∈ S ∧ FourNeighborAdjacent u z) := by
      apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
      intro u z l₁ l₂ he
      exact ⟨pall u (by simp [he]), pall z (by simp [he]), padj u z l₁ l₂ he⟩
    cases p with
    | nil => simp at hp
    | cons u p =>
      simp only [List.head?_cons, Option.some.injEq] at hp
      subst u
      exact List.relationReflTransGen_of_exists_isChain_cons p hc
        (List.getLast_of_getLast?_eq_some hlast)
  have adjSymm {x y : GaussianInt} (h : FourNeighborAdjacent x y) :
      FourNeighborAdjacent y x := by
    rcases h with rfl | rfl | rfl | rfl <;>
      simp [FourNeighborAdjacent, add_assoc, add_comm, add_left_comm]
  have meet : ∃ w, w ∈ X ∧ w ∈ W := by
    by_contra hn
    have miss : ∀ x ∈ X, x ∉ W := by
      intro x hx hw
      exact hn ⟨x, hx, hw⟩
    obtain ⟨x, hx⟩ := hX.1
    obtain ⟨m, n, hm⟩ := owner x (miss x hx)
    apply hInf.not_finite
    apply (Finset.finite_toSet
      ((P4062T1InteriorSquare P.q).image (fun y => y + t m n))).subset
    intro y hy
    have reach := connectedReach X hX x hx y hy
    have reach' : Relation.ReflTransGen
        (fun u z => u ∉ W ∧ z ∉ W ∧ FourNeighborAdjacent u z) x y :=
      Relation.ReflTransGen.mono
        (fun u z he => ⟨miss u he.1, miss z he.2.1, he.2.2⟩) x y reach
    exact Finset.mem_image.mpr ⟨y - t m n, hm y reach', sub_add_cancel _ _⟩
  have noEntry (w : GaussianInt) (hw : w ∈ W) (hwX : w ∉ X)
      (y : GaussianInt) (hwy : FourNeighborAdjacent w y) : y ∉ X := by
    intro hy
    have h := hbound w
    change FourNeighborLaplacian
      (fun a => g a + Set.indicator X (fun _ => (1 : Int)) a) w ≤ 1 at h
    have hl := webLap w hw
    unfold FourNeighborLaplacian at h hl
    dsimp only at h
    simp only [Set.indicator_apply, ite_eq_right hwX] at h
    rcases hwy with rfl | rfl | rfl | rfl <;>
      simp only [ite_eq_left hy] at h <;> split_ifs at h <;> omega
  have webIn : W ⊆ X := by
    obtain ⟨w₀, hw₀X, hw₀W⟩ := meet
    intro w hw
    have reach := connectedReach W webConnected w₀ hw₀W w hw
    induction reach with
    | refl => exact hw₀X
    | @tail u v h e ih =>
      by_contra hn
      exact noEntry v e.2.1 hn u (adjSymm e.2.2) (ih e.1)
  obtain ⟨h, hodo, hdom, hval⟩ := FordTileOdometerRestriction P
  have hs := P4062T1CanonicalSupport P.q P.q_pos
  have hfoot : (h.domain : Set GaussianInt) = FootprintVertices (FordTile P.q) :=
    hdom.trans hs.1.symm
  have hext : GlobalOdometerExtends g h := by
    refine ⟨0, ?_⟩
    intro x hx
    simpa only [add_zero] using (hval x hx).symm
  have hD : (h.domain.filter fun x =>
      @decide (x ∉ BoundaryFootprintVertices (FordTile P.q)) (Classical.propDecidable _)) =
      P4062T1InteriorSquare P.q := by
    have hmem (x : GaussianInt) : x ∈ h.domain ↔ x ∈ FordVertexDomain P.q :=
      Set.ext_iff.mp hdom x
    ext x
    simp only [Finset.mem_filter, decide_eq_true_eq, hmem, hs.2,
      FordVertexDomain, Set.mem_ofPred_eq]
    have square : x ∈ P4062T1InteriorSquare P.q ↔
        1 ≤ x.re ∧ x.re ≤ (P.q : Int) - 1 ∧
        1 ≤ x.im ∧ x.im ≤ (P.q : Int) - 1 := by
      constructor
      · intro hx
        obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
        exact ⟨(Finset.mem_Icc.mp ha).1, (Finset.mem_Icc.mp ha).2,
          (Finset.mem_Icc.mp hb).1, (Finset.mem_Icc.mp hb).2⟩
      · intro hx
        exact Finset.mem_image.mpr ⟨(x.re, x.im), Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨hx.1, hx.2.1⟩,
            Finset.mem_Icc.mpr hx.2.2⟩, by cases x; rfl⟩
    rw [square]
    omega
  have ho := FordTileAcyclicIndegree P (FordTile P.q) h g
    (FordTileRecursiveIdentification P).1 hodo hfoot hext
  dsimp only at ho
  rw [hD] at ho
  obtain ⟨o⟩ := ho
  apply Set.eq_univ_of_forall
  intro z
  by_contra hz
  have hzW : z ∉ W := fun h => hz (webIn h)
  obtain ⟨m, n, own⟩ := owner z hzW
  let R : GaussianInt → GaussianInt → Prop :=
    fun u v => u ∉ X ∧ v ∉ X ∧ FourNeighborAdjacent u v
  let E := (P4062T1InteriorSquare P.q).image (fun y => y + t m n)
  let Y := E.filter (fun y => Relation.ReflTransGen R z y)
  have outside (y : GaussianInt) (hr : Relation.ReflTransGen R z y) : y ∉ X := by
    induction hr with
    | refl => exact hz
    | tail _ e _ => exact e.2.1
  have owned (y : GaussianInt) (hr : Relation.ReflTransGen R z y) : y ∈ E := by
    have hr' : Relation.ReflTransGen
        (fun u v => u ∉ W ∧ v ∉ W ∧ FourNeighborAdjacent u v) z y :=
      Relation.ReflTransGen.mono
        (fun u v he => ⟨fun hu => he.1 (webIn hu),
          fun hv => he.2.1 (webIn hv), he.2.2⟩) z y hr
    exact Finset.mem_image.mpr ⟨y - t m n, own y hr', sub_add_cancel _ _⟩
  have hY : Y.Nonempty :=
    ⟨z, Finset.mem_filter.mpr ⟨owned z .refl, Relation.ReflTransGen.refl⟩⟩
  have hσ : ∀ x ∈ E, 2 + FourNeighborLaplacian g x =
      2 + FourNeighborLaplacian g (x - t m n) := by
    intro x _
    have hp := (periods m n).2 (x - t m n)
    rw [sub_add_cancel] at hp
    omega
  obtain ⟨oE, _, _⟩ := P4062T1OrientationTransport
    (P4062T1InteriorSquare P.q) E
    (fun x => 2 + FourNeighborLaplacian g x)
    (fun x => 2 + FourNeighborLaplacian g x)
    (t m n) rfl hσ o
  obtain ⟨y, hy, hbad⟩ := FiniteAcyclicOrientationObstruction E g oE Y hY
    (Finset.filter_subset _ _)
  have hyR : Relation.ReflTransGen R z y := (Finset.mem_filter.mp hy).2
  have hyX : y ∉ X := outside y hyR
  have star (a : GaussianInt) (ha : a = y ∨ FourNeighborAdjacent y a) :
      g a + Set.indicator X (fun _ => (1 : Int)) a =
        (g a - if a ∈ Y then 1 else 0) + 1 := by
    have iffY : a ∉ X ↔ a ∈ Y := by
      constructor
      · intro haX
        rcases ha with rfl | ha
        · exact hy
        · have hr := hyR.tail ⟨hyX, haX, ha⟩
          exact Finset.mem_filter.mpr ⟨owned a hr, hr⟩
      · intro haY
        exact outside a (Finset.mem_filter.mp haY).2
    by_cases haX : a ∈ X
    · have haY : a ∉ Y := fun hh => (iffY.mpr hh) haX
      simp [haX, haY]
    · simp [haX, iffY.mp haX]
  have hlap : FourNeighborLaplacian
      (fun a => g a + Set.indicator X (fun _ => (1 : Int)) a) y =
      FourNeighborLaplacian (fun a => g a - if a ∈ Y then 1 else 0) y := by
    unfold FourNeighborLaplacian
    dsimp only
    rw [star _ (Or.inr (Or.inl rfl)),
      star _ (Or.inr (Or.inr (Or.inl rfl))),
      star _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      star _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), star y (Or.inl rfl)]
    ring
  have hgood := hbound y
  change FourNeighborLaplacian
    (fun a => g a + Set.indicator X (fun _ => (1 : Int)) a) y ≤ 1 at hgood
  rw [hlap] at hgood
  omega

end ApollonianSuperharmonic

end
