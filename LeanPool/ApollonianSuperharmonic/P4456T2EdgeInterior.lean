/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Real

public import LeanPool.ApollonianSuperharmonic.P4397T1UnitEdgeCells
public import LeanPool.ApollonianSuperharmonic.OpenLatticeEdge
public import LeanPool.ApollonianSuperharmonic.TileRealization

-- [TABLET NODE: P4456T2EdgeInterior]

/-!
# P4456T2EdgeInterior

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace EdgeInteriorProof

private theorem hu :
    ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (z : GaussianInt), ∀ (w : GaussianInt), ((x = z +
        (1 : GaussianInt) ∧ y = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ y = z + (1 :
        GaussianInt) ∧ x = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∧ w = z + (1 :
        GaussianInt) ∨ (x = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ y = z + ⟨(0 : ℤ), (1 :
        ℤ)⟩ ∨ y = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ x = z + ⟨(0 : ℤ), (1 : ℤ)⟩) ∧ w =
        z + ⟨(0 : ℤ), (1 : ℤ)⟩) →
    ∀ U : ProtoTile,
      (({x, y} : Finset GaussianInt) ∈ FootprintEdges U ↔ z ∈ U.cells ∨ w ∈ U.cells) ∧
      (z ∈ U.cells ∧ w ∈ U.cells →
        OpenLatticeEdge x y ⊆ interior (TileRealization U)) := by
  intro x y z w hform U
  have h := P4397T1UnitEdgeCells.2 x y z w hform U
  exact ⟨h.1, h.2.2.2.1⟩

private theorem hbase :
    ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ≠ b) → (∀ (z : GaussianInt), ∀ (w :
        GaussianInt), (z = a ∨ w = a) → ((z = b ∨ w = b) → ((a = z ∧ b = w) ∨ (a = w ∧ b = z))))
        := by
  classical
  intro a b hab z w ha' hb'
  rcases ha' with haz | haw <;> rcases hb' with hbz | hbw
  · exact False.elim (hab (haz.symm.trans hbz))
  · exact Or.inl ⟨haz.symm, hbw.symm⟩
  · exact Or.inr ⟨haw.symm, hbz.symm⟩
  · exact False.elim (hab (haw.symm.trans hbw))

private theorem edgeSym :
    ∀ (u : GaussianInt), ∀ (v : GaussianInt), OpenLatticeEdge u v = OpenLatticeEdge v u := by
  classical
  intro u v
  ext p
  constructor <;> rintro ⟨t, ht0, ht1, hp⟩
  · refine ⟨1 - t, by linarith, by linarith, ?_⟩
    rw [hp]
    simp [GaussianRealPoint]
    constructor <;> ring
  · refine ⟨1 - t, by linarith, by linarith, ?_⟩
    rw [hp]
    simp [GaussianRealPoint]
    constructor <;> ring

private theorem vertical :
    ∀ (T : ProtoTile), ∀ (q : GaussianInt), (OpenLatticeEdge (q + 1) (q + 1 + ⟨0, 1⟩) ⊆
        interior (TileRealization T)) → (q ∈ T.cells ∧ q + 1 ∈ T.cells) := by
  classical
  intro T q he
  let m : ℝ × ℝ := ((q.re : ℝ) + 1, (q.im : ℝ) + 1/2)
  have hm : m ∈ OpenLatticeEdge (q + 1) (q + 1 + ⟨0, 1⟩) := by
    change ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      m = (1-t) • GaussianRealPoint (q+1) + t • GaussianRealPoint (q+1+⟨0,1⟩)
    refine ⟨1/2, by norm_num, by norm_num, ?_⟩
    simp [m, GaussianRealPoint, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_one, Zsqrtd.im_one, Int.cast_add, Int.cast_one]
    constructor <;> ring
  have hmI : m ∈ interior (TileRealization T) := he hm
  obtain ⟨r, hr, hball⟩ := (Metric.isOpen_iff.mp isOpen_interior) m hmI
  let ε := min (r/2) (1/4 : ℝ)
  have hε : 0 < ε := by dsimp [ε]; exact lt_min (by linarith) (by norm_num)
  have hεhalf : ε < 1/2 := by
    dsimp [ε]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hεr : ε < r := by
    dsimp [ε]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let pL : ℝ × ℝ := ((q.re : ℝ)+1-ε, (q.im : ℝ)+1/2)
  let pR : ℝ × ℝ := ((q.re : ℝ)+1+ε, (q.im : ℝ)+1/2)
  have hLball : pL ∈ Metric.ball m r := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [Int.reduceNeg, GaussianInt.intCast_re, Real.dist_eq, sub_sub_cancel_left,
        abs_neg, abs_of_pos hε, GaussianInt.intCast_im, one_div, dist_self, max_lt_iff, m, pL]
    exact ⟨hεr, hr⟩
  have hRball : pR ∈ Metric.ball m r := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [Int.reduceNeg, GaussianInt.intCast_re, Real.dist_eq, add_sub_cancel_left,
        abs_of_pos hε, GaussianInt.intCast_im, one_div, dist_self, max_lt_iff, m, pR]
    exact ⟨hεr, hr⟩
  have hpL : pL ∈ TileRealization T := interior_subset (hball hLball)
  have hpR : pR ∈ TileRealization T := interior_subset (hball hRball)
  have getCell (p : ℝ × ℝ) (hp : p ∈ TileRealization T) :
      ∃ c ∈ T.cells, p ∈ ClosedSquareRealization c := by
    change p ∈ ⋃ c ∈ T.cells, ClosedSquareRealization c at hp
    rcases Set.mem_iUnion.mp hp with ⟨c, hc⟩
    rcases Set.mem_iUnion.mp hc with ⟨hc, hp⟩
    exact ⟨c, hc, hp⟩
  obtain ⟨cL, hcL, hsqL⟩ := getCell pL hpL
  obtain ⟨cR, hcR, hsqR⟩ := getCell pR hpR
  have hsL : pL ∈ ClosedSquareRealization cL := hsqL
  have hsR : pR ∈ ClosedSquareRealization cR := hsqR
  simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hsL hsR
  have hleftre : cL.re = q.re := by
    by_contra hne
    have hne' : cL.re ≠ q.re := by omega
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have hcast : (cL.re : ℝ) + 1 ≤ (q.re : ℝ) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hlt)
      dsimp [pL] at hsL
      linarith
    · have hcast : (q.re : ℝ) + 1 ≤ (cL.re : ℝ) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hgt)
      dsimp [pL] at hsL
      linarith
  have hleftim : cL.im = q.im := by
    by_contra hne
    have hne' : cL.im ≠ q.im := by omega
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have hcast : (cL.im : ℝ) + 1 ≤ (q.im : ℝ) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hlt)
      dsimp [pL] at hsL
      linarith
    · have hcast : (q.im : ℝ) + 1 ≤ (cL.im : ℝ) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hgt)
      dsimp [pL] at hsL
      linarith
  have hleft : cL = q := by ext <;> assumption
  have hrightre : cR.re = q.re + 1 := by
    by_contra hne
    have hne' : cR.re ≠ q.re + 1 := by omega
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have hcast : (cR.re : ℝ) + 1 ≤ (q.re : ℝ) + 1 := by
        exact_mod_cast (Int.add_one_le_iff.mpr hlt)
      dsimp [pR] at hsR
      linarith [hsR.2.1]
    · have hcast : (q.re : ℝ) + 2 ≤ (cR.re : ℝ) := by
        have hInt : q.re + 2 ≤ cR.re := by omega
        exact_mod_cast hInt
      dsimp [pR] at hsR
      linarith [hsR.1.1, hεhalf]
  have hrightim : cR.im = q.im := by
    by_contra hne
    have hne' : cR.im ≠ q.im := by omega
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have hcast : (cR.im : ℝ) + 1 ≤ (q.im : ℝ) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hlt)
      dsimp [pR] at hsR
      linarith [hsR.2.2]
    · have hcast : (q.im : ℝ) + 1 ≤ (cR.im : ℝ) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hgt)
      dsimp [pR] at hsR
      linarith [hsR.1.2]
  have hright : cR = q + 1 := by
    ext
    · simpa using hrightre
    · simpa using hrightim
  constructor
  · rw [hleft] at hcL
    exact hcL
  · rw [hright] at hcR
    exact hcR

private theorem horizontal :
    ∀ (T : ProtoTile), ∀ (q : GaussianInt), (OpenLatticeEdge (q + 1 + ⟨0, 1⟩) (q + ⟨0, 1⟩) ⊆
        interior (TileRealization T)) → (q ∈ T.cells ∧ q + ⟨0, 1⟩ ∈ T.cells) := by
  classical
  intro T q he
  let m : ℝ × ℝ := ((q.re : ℝ) + 1/2, (q.im : ℝ) + 1)
  have hm : m ∈ OpenLatticeEdge (q + 1 + ⟨0, 1⟩) (q + ⟨0, 1⟩) := by
    change ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      m = (1-t) • GaussianRealPoint (q+1+⟨0,1⟩) + t • GaussianRealPoint (q+⟨0,1⟩)
    refine ⟨1/2, by norm_num, by norm_num, ?_⟩
    simp [m, GaussianRealPoint, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_one, Zsqrtd.im_one, Int.cast_add, Int.cast_one]
    constructor <;> ring
  have hmI : m ∈ interior (TileRealization T) := he hm
  obtain ⟨r, hr, hball⟩ := (Metric.isOpen_iff.mp isOpen_interior) m hmI
  let ε := min (r/2) (1/4 : ℝ)
  have hε : 0 < ε := by dsimp [ε]; exact lt_min (by linarith) (by norm_num)
  have hεhalf : ε < 1/2 := by
    dsimp [ε]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hεr : ε < r := by
    dsimp [ε]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let pD : ℝ × ℝ := ((q.re : ℝ)+1/2, (q.im : ℝ)+1-ε)
  let pU : ℝ × ℝ := ((q.re : ℝ)+1/2, (q.im : ℝ)+1+ε)
  have hDball : pD ∈ Metric.ball m r := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [Int.reduceNeg, GaussianInt.intCast_re, one_div, dist_self,
        GaussianInt.intCast_im, Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hε,
        max_lt_iff, m, pD]
    exact ⟨hr, hεr⟩
  have hUball : pU ∈ Metric.ball m r := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [Int.reduceNeg, GaussianInt.intCast_re, one_div, dist_self,
        GaussianInt.intCast_im, Real.dist_eq, add_sub_cancel_left, abs_of_pos hε, max_lt_iff,
        m, pU]
    exact ⟨hr, hεr⟩
  have hpD : pD ∈ TileRealization T := interior_subset (hball hDball)
  have hpU : pU ∈ TileRealization T := interior_subset (hball hUball)
  have getCell (p : ℝ × ℝ) (hp : p ∈ TileRealization T) :
      ∃ c ∈ T.cells, p ∈ ClosedSquareRealization c := by
    change p ∈ ⋃ c ∈ T.cells, ClosedSquareRealization c at hp
    rcases Set.mem_iUnion.mp hp with ⟨c, hc⟩
    rcases Set.mem_iUnion.mp hc with ⟨hc, hp⟩
    exact ⟨c, hc, hp⟩
  obtain ⟨cD, hcD, hsqD⟩ := getCell pD hpD
  obtain ⟨cU, hcU, hsqU⟩ := getCell pU hpU
  have hsD : pD ∈ ClosedSquareRealization cD := hsqD
  have hsU : pU ∈ ClosedSquareRealization cU := hsqU
  simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hsD hsU
  have hdownre : cD.re = q.re := by
    by_contra hne
    have hne' : cD.re ≠ q.re := by omega
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have hcast : (cD.re : ℝ) + 1 ≤ (q.re : ℝ) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hlt)
      dsimp [pD] at hsD
      linarith
    · have hcast : (q.re : ℝ) + 1 ≤ (cD.re : ℝ) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hgt)
      dsimp [pD] at hsD
      linarith
  have hdownim : cD.im = q.im := by
    by_contra hne
    have hne' : cD.im ≠ q.im := by omega
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have hcast : (cD.im : ℝ) + 1 ≤ (q.im : ℝ) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hlt)
      dsimp [pD] at hsD
      linarith
    · have hcast : (q.im : ℝ) + 1 ≤ (cD.im : ℝ) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hgt)
      dsimp [pD] at hsD
      linarith
  have hdown : cD = q := by ext <;> assumption
  have hupre : cU.re = q.re := by
    by_contra hne
    have hne' : cU.re ≠ q.re := by omega
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have hcast : (cU.re : ℝ) + 1 ≤ (q.re : ℝ) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hlt)
      dsimp [pU] at hsU
      linarith [hsU.2.1]
    · have hcast : (q.re : ℝ) + 1 ≤ (cU.re : ℝ) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hgt)
      dsimp [pU] at hsU
      linarith [hsU.1.1, hεhalf]
  have hupim : cU.im = q.im + 1 := by
    by_contra hne
    have hne' : cU.im ≠ q.im + 1 := by omega
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have hcast : (cU.im : ℝ) + 1 ≤ (q.im : ℝ) + 1 := by
        exact_mod_cast (Int.add_one_le_iff.mpr hlt)
      dsimp [pU] at hsU
      linarith [hsU.2.2]
    · have hcast : (q.im : ℝ) + 2 ≤ (cU.im : ℝ) := by
        have hInt : q.im + 2 ≤ cU.im := by omega
        exact_mod_cast hInt
      dsimp [pU] at hsU
      linarith [hsU.1.2, hεhalf]
  have hup : cU = q + ⟨0, 1⟩ := by
    ext
    · simpa using hupre
    · simpa using hupim
  constructor
  · rw [hdown] at hcD
    exact hcD
  · rw [hup] at hcU
    exact hcU

end EdgeInteriorProof

theorem P4456T2EdgeInterior (T : ProtoTile) (x y a b : GaussianInt)
    (hxy : FourNeighborAdjacent x y) (hab : a ≠ b)
    (ha : ({x, y} : Finset GaussianInt) ∈ FootprintEdges ⟨{a}, a⟩)
    (hb : ({x, y} : Finset GaussianInt) ∈ FootprintEdges ⟨{b}, b⟩) :
    OpenLatticeEdge x y ⊆ interior (TileRealization T) ↔
      a ∈ T.cells ∧ b ∈ T.cells := by
-- BODY
  classical
  obtain ⟨z, w, hform⟩ := (P4397T1UnitEdgeCells.1 x y hxy)
  have hu := EdgeInteriorProof.hu x y z w hform
  have ha' : z ∈ (⟨{a}, a⟩ : ProtoTile).cells ∨ w ∈ (⟨{a}, a⟩ : ProtoTile).cells :=
      (hu (⟨{a}, a⟩ : ProtoTile)).1.mp ha
  have hb' : z ∈ (⟨{b}, b⟩ : ProtoTile).cells ∨ w ∈ (⟨{b}, b⟩ : ProtoTile).cells :=
      (hu (⟨{b}, b⟩ : ProtoTile)).1.mp hb
  simp only [Finset.mem_singleton] at ha' hb'
  have hbase : (a = z ∧ b = w) ∨ (a = w ∧ b = z) := EdgeInteriorProof.hbase a b hab z w ha' hb'
  have edgeSym (u v : GaussianInt) : OpenLatticeEdge u v = OpenLatticeEdge v u :=
      EdgeInteriorProof.edgeSym u v
  constructor
  · intro he
    have hocc : z ∈ T.cells ∧ w ∈ T.cells := by
      rcases hform with ⟨hcase, hw⟩ | ⟨hcase, hw⟩
      · subst w
        rcases hcase with ⟨hx, hy⟩ | ⟨hy, hx⟩
        · subst x; subst y
          exact EdgeInteriorProof.vertical T z he
        · subst x; subst y
          have hs : OpenLatticeEdge (z + 1) (z + 1 + ⟨0, 1⟩) =
              OpenLatticeEdge (z + 1 + ⟨0, 1⟩) (z + 1) := edgeSym _ _
          rw [← hs] at he
          exact EdgeInteriorProof.vertical T z he
      · subst w
        rcases hcase with ⟨hx, hy⟩ | ⟨hy, hx⟩
        · subst x; subst y
          exact EdgeInteriorProof.horizontal T z he
        · subst x; subst y
          have hs : OpenLatticeEdge (z + 1 + ⟨0, 1⟩) (z + ⟨0, 1⟩) =
              OpenLatticeEdge (z + ⟨0, 1⟩) (z + 1 + ⟨0, 1⟩) := edgeSym _ _
          rw [← hs] at he
          exact EdgeInteriorProof.horizontal T z he
    rcases hbase with ⟨haEq, hbEq⟩ | ⟨haEq, hbEq⟩
    · simpa [haEq, hbEq] using hocc
    · simpa [haEq, hbEq] using ⟨hocc.2, hocc.1⟩
  · rintro ⟨haz, haw⟩
    rcases hform with ⟨hcase, hw⟩ | ⟨hcase, hw⟩
    · subst w
      have hboth : z ∈ T.cells ∧ z + 1 ∈ T.cells := by
        rcases hbase with ⟨haEq, hbEq⟩ | ⟨haEq, hbEq⟩
        · subst a; subst b; exact ⟨haz, haw⟩
        · subst a; subst b; exact ⟨haw, haz⟩
      rcases hcase with ⟨hxy₁, hxy₂⟩ | ⟨hxy₁, hxy₂⟩
      · subst x y
        exact (hu T).2 hboth
      · subst x y
        exact (hu T).2 hboth
    · subst w
      have hboth : z ∈ T.cells ∧ z + ⟨0, 1⟩ ∈ T.cells := by
        rcases hbase with ⟨haEq, hbEq⟩ | ⟨haEq, hbEq⟩
        · subst a; subst b; exact ⟨haz, haw⟩
        · subst a; subst b; exact ⟨haw, haz⟩
      rcases hcase with ⟨hxy₁, hxy₂⟩ | ⟨hxy₁, hxy₂⟩
      · subst x y
        exact (hu T).2 hboth
      · subst x y
        exact (hu T).2 hboth

end ApollonianSuperharmonic

end
