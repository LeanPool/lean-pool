/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5442T1Cocycle
public import LeanPool.ApollonianSuperharmonic.P4062T1InteriorSquare
public import LeanPool.ApollonianSuperharmonic.FordLaplacianTable
public import LeanPool.ApollonianSuperharmonic.FourNeighborConnected

-- [TABLET NODE: P5442T1WebGeometry]

/-!
# P5442T1WebGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FordWebGeometryProof

private theorem boundary :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (x : GaussianInt), x ∈ LatticeVertexBoundary
            (FordVertexDomain P.q) ↔ (0 : ℤ) ≤ x.re ∧ x.re ≤ (↑P.q : ℤ) ∧ (0 : ℤ) ≤ x.im ∧ x.im ≤
            (↑P.q : ℤ) ∧ (x.re = (0 : ℤ) ∨ x.re = (↑P.q : ℤ) ∨ x.im = (0 : ℤ) ∨ x.im = (↑P.q : ℤ))
    ) := by
  classical
  intro P x
  constructor
  · rintro ⟨hx, y, hy, hr, hi⟩
    refine ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2, ?_⟩
    have hr' : |x.re - y.re| ≤ (1 : Int) := by
      rw [← Int.natCast_natAbs]; exact_mod_cast hr
    have hi' : |x.im - y.im| ≤ (1 : Int) := by
      rw [← Int.natCast_natAbs]; exact_mod_cast hi
    have hrb := abs_le.mp hr'
    have hib := abs_le.mp hi'
    change ¬(0 ≤ y.re ∧ y.re ≤ (P.q : Int) ∧
      0 ≤ y.im ∧ y.im ≤ (P.q : Int)) at hy
    change 0 ≤ x.re ∧ x.re ≤ (P.q : Int) ∧
      0 ≤ x.im ∧ x.im ≤ (P.q : Int) at hx
    omega
  · rintro ⟨hr, hr', hi, hi', he⟩
    refine ⟨⟨hr, hr', hi, hi'⟩, ?_⟩
    rcases he with he | he | he | he
    · refine ⟨x-1, ?_, ?_, ?_⟩
      all_goals simp [FordVertexDomain, he]
    · refine ⟨x+1, ?_, ?_, ?_⟩
      · simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_add,
          Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one, he]
        omega
      all_goals simp
    · refine ⟨x-⟨0,1⟩, ?_, ?_, ?_⟩
      all_goals simp [FordVertexDomain, he]
    · refine ⟨x+⟨0,1⟩, ?_, ?_, ?_⟩
      · simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_add, Zsqrtd.im_add, he]
        omega
      all_goals simp

private theorem coords :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (x : GaussianInt), x ∈ P4062T1InteriorSquare P.q ↔ (1 :
            ℤ) ≤ x.re ∧ x.re ≤ (↑P.q : ℤ) - (1 : ℤ) ∧ (1 : ℤ) ≤ x.im ∧ x.im ≤ (↑P.q : ℤ) - (1 : ℤ)
    ) := by
  classical
  intro P x
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

private theorem periods :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let t : Int → Int → GaussianInt := fun m n =>
          ⟨n * (P.q : Int), n * (P.q₁ : Int) - m * (P.q : Int)⟩
  ∀ m, ∀ n, t m n ∈
            FordExceptionalLattice P ∧ ∀ x, FourNeighborLaplacian (FordOdometer P) (x+t m n) =
            FourNeighborLaplacian (FordOdometer P) x
    ) := by
  classical
  intro P t m n
  have hu : (⟨0, -(P.q : Int)⟩ : GaussianInt) ∈ FordExceptionalLattice P :=
    AddSubgroup.subset_closure (Or.inl rfl)
  have hv : (⟨(P.q : Int), (P.q₁ : Int)⟩ : GaussianInt) ∈ FordExceptionalLattice P :=
    AddSubgroup.subset_closure (Or.inr rfl)
  have ht : t m n = m • (⟨0, -(P.q : Int)⟩ : GaussianInt) +
      n • (⟨(P.q : Int), (P.q₁ : Int)⟩ : GaussianInt) := by
    ext <;> simp [t]; ring
  have htL : t m n ∈ FordExceptionalLattice P := by
    rw [ht]
    exact (FordExceptionalLattice P).add_mem
      ((FordExceptionalLattice P).zsmul_mem hu m)
      ((FordExceptionalLattice P).zsmul_mem hv n)
  refine ⟨htL, ?_⟩
  obtain ⟨a, _, ha⟩ := P5442T1Cocycle P (t m n) htL
  intro x
  unfold FourNeighborLaplacian
  rw [show x+t m n+1 = (x+1)+t m n by abel,
    show x+t m n-1 = (x-1)+t m n by abel,
    show x+t m n+⟨0,1⟩ = (x+⟨0,1⟩)+t m n by abel,
    show x+t m n-⟨0,1⟩ = (x-⟨0,1⟩)+t m n by abel,
    ha, ha, ha, ha, ha]
  simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_sub,
    Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]
  ring

private theorem lineMem :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let t : Int → Int → GaussianInt := fun m n =>
          ⟨n * (P.q : Int), n * (P.q₁ : Int) - m * (P.q : Int)⟩
        let W : Set GaussianInt := {x | ∃ m n : Int,
          x - t m n ∈ LatticeVertexBoundary (FordVertexDomain P.q)}
 ( (0 < (P.q :
            Int)) → ((∀ (x : GaussianInt), x ∈ LatticeVertexBoundary (FordVertexDomain P.q) ↔ 0 ≤
            x.re ∧ x.re ≤ (P.q : Int) ∧ 0 ≤ x.im ∧ x.im ≤ (P.q : Int) ∧ (x.re = 0 ∨ x.re = (P.q :
            Int) ∨ x.im = 0 ∨ x.im = (P.q : Int))) → (∀ (n : ℤ), ∀ (b : ℤ), ⟨n * (↑P.q : ℤ), b⟩ ∈
            W)))
    ) := by
  classical
  intro P t W hq boundary n b
  let k := (b - n*(P.q₁ : Int)) / (P.q : Int)
  let s := (b - n*(P.q₁ : Int)) % (P.q : Int)
  have hs : 0 ≤ s := Int.emod_nonneg _ (ne_of_gt hq)
  have hs' : s < (P.q : Int) := Int.emod_lt_of_pos _ hq
  have he := Int.emod_add_mul_ediv (b - n*(P.q₁ : Int)) (P.q : Int)
  refine ⟨-k, n, (boundary _).mpr ?_⟩
  have hi : (⟨n*(P.q : Int), b⟩ - t (-k) n).im = s := by
    dsimp [t, k, s]
    nlinarith only [he]
  simp only [Zsqrtd.re_sub, hi]
  change 0 ≤ n*(P.q : Int)-n*(P.q : Int) ∧ _
  dsimp [t]
  omega

private theorem segment :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let t : Int → Int → GaussianInt := fun m n =>
          ⟨n * (P.q : Int), n * (P.q₁ : Int) - m * (P.q : Int)⟩
        let W : Set GaussianInt := {x | ∃ m n : Int,
          x - t m n ∈ LatticeVertexBoundary (FordVertexDomain P.q)}
 (
        let Q : GaussianInt → GaussianInt → Prop :=
          fun u z => u ∈ W ∧ z ∈ W ∧ FourNeighborAdjacent u z
        ∀ (a : GaussianInt), ∀ (d : GaussianInt), d = (1 : GaussianInt) ∨ d = ⟨(0 : ℤ), (1 : ℤ)⟩
            → ∀ (k : ℕ), (∀ j ≤ k, a + j • d ∈ W) → Relation.ReflTransGen Q a (a + k • d))
    ) := by
  classical
  intro P t W Q a d hd k hm
  induction k with
  | zero => simpa only [zero_nsmul, add_zero] using
      (Relation.ReflTransGen.refl (a := a) (r := Q))
  | succ k ih =>
    have hp := ih (fun j hj => hm j (by omega))
    have he : FourNeighborAdjacent (a+k • d) (a+(k+1) • d) := by
      rcases hd with rfl | rfl
      · left; rw [add_nsmul, one_nsmul, add_assoc]
      · right; right; left; rw [add_nsmul, one_nsmul, add_assoc]
    exact hp.tail ⟨hm k (by omega), hm (k+1) le_rfl, he⟩

private theorem bridge :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let t : Int → Int → GaussianInt := fun m n =>
          ⟨n * (P.q : Int), n * (P.q₁ : Int) - m * (P.q : Int)⟩
        let W : Set GaussianInt := {x | ∃ m n : Int,
          x - t m n ∈ LatticeVertexBoundary (FordVertexDomain P.q)}
 ( (∀ (x :
            GaussianInt), x ∈ LatticeVertexBoundary (FordVertexDomain P.q) ↔ 0 ≤ x.re ∧ x.re ≤
            (P.q : Int) ∧ 0 ≤ x.im ∧ x.im ≤ (P.q : Int) ∧ (x.re = 0 ∨ x.re = (P.q : Int) ∨ x.im =
            0 ∨ x.im = (P.q : Int))) → (
        let Q : GaussianInt → GaussianInt → Prop :=
          fun u z => u ∈ W ∧ z ∈ W ∧ FourNeighborAdjacent u z
        (∀ (a : GaussianInt), ∀ (d : GaussianInt), (d = 1 ∨ d = ⟨0,1⟩) → (∀ (k : Nat), (∀ j :
            Nat, j ≤ k → a + j • d ∈ W) → (Relation.ReflTransGen Q a (a + k • d)))) → ((∀ (j :
            Nat), j • (1 : GaussianInt) = ⟨j,0⟩) → (∀ (n : ℤ), Relation.ReflTransGen Q ⟨n * (↑P.q
            : ℤ), n * (↑P.q₁ : ℤ)⟩ ⟨(n + (1 : ℤ)) * (↑P.q : ℤ), n * (↑P.q₁ : ℤ)⟩))))
    ) := by
  classical
  intro P t W boundary Q segment horizVec n
  have hh := segment ⟨n*(P.q : Int), n*(P.q₁ : Int)⟩ 1 (Or.inl rfl) P.q
    (fun j hj => by
      refine ⟨0, n, (boundary _).mpr ?_⟩
      rw [horizVec]
      dsimp [t]
      omega)
  convert hh using 1
  ext <;> simp; ring

private theorem lineReach :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let t : Int → Int → GaussianInt := fun m n =>
          ⟨n * (P.q : Int), n * (P.q₁ : Int) - m * (P.q : Int)⟩
        let W : Set GaussianInt := {x | ∃ m n : Int,
          x - t m n ∈ LatticeVertexBoundary (FordVertexDomain P.q)}
        let Q : GaussianInt → GaussianInt → Prop :=
          fun u z => u ∈ W ∧ z ∈ W ∧ FourNeighborAdjacent u z
        (∀ {x y}, Relation.ReflTransGen Q x y → Relation.ReflTransGen Q y x) → ((∀ (n : Int),
            Relation.ReflTransGen Q ⟨n*(P.q : Int), 0⟩ ⟨(n+1)*(P.q : Int), 0⟩) → (∀ (n : ℤ),
            Relation.ReflTransGen Q (0 : GaussianInt) ⟨n * (↑P.q : ℤ), (0 : ℤ)⟩))) := by
  classical
  intro P t W Q reverse link n
  induction n using Int.induction_on with
  | zero =>
    have hz : (⟨(0 : Int)*(P.q : Int), 0⟩ : GaussianInt) = 0 := by ext <;> simp
    simpa only [hz] using (Relation.ReflTransGen.refl (a := (0 : GaussianInt)) (r := Q))
  | succ n ih =>
    convert ih.trans (link n) using 1
  | pred n ih =>
    have hh := reverse (link (-(n : Int)-1))
    have he : (⟨(-(n : Int)-1+1)*(P.q : Int), 0⟩ : GaussianInt) =
        ⟨(-(n : Int))*(P.q : Int), 0⟩ := by ext <;> simp
    rw [he] at hh
    exact ih.trans hh

private theorem reach0 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let t : Int → Int → GaussianInt := fun m n =>
          ⟨n * (P.q : Int), n * (P.q₁ : Int) - m * (P.q : Int)⟩
        let W : Set GaussianInt := {x | ∃ m n : Int,
          x - t m n ∈ LatticeVertexBoundary (FordVertexDomain P.q)}
 ( (0 < (P.q :
            Int)) → ((∀ (x : GaussianInt), x ∈ LatticeVertexBoundary (FordVertexDomain P.q) ↔ 0 ≤
            x.re ∧ x.re ≤ (P.q : Int) ∧ 0 ≤ x.im ∧ x.im ≤ (P.q : Int) ∧ (x.re = 0 ∨ x.re = (P.q :
            Int) ∨ x.im = 0 ∨ x.im = (P.q : Int))) → (
        let Q : GaussianInt → GaussianInt → Prop :=
          fun u z => u ∈ W ∧ z ∈ W ∧ FourNeighborAdjacent u z
        (∀ (a : GaussianInt), ∀ (d : GaussianInt), (d = 1 ∨ d = ⟨0,1⟩) → (∀ (k : Nat), (∀ j :
            Nat, j ≤ k → a + j • d ∈ W) → (Relation.ReflTransGen Q a (a + k • d)))) → ((∀ (j :
            Nat), j • (1 : GaussianInt) = ⟨j,0⟩) → ((∀ (n : Int), ∀ (b : Int), ∀ (c : Int),
            Relation.ReflTransGen Q ⟨n*(P.q : Int), b⟩ ⟨n*(P.q : Int), c⟩) → ((∀ (n : Int),
            Relation.ReflTransGen Q 0 ⟨n*(P.q : Int), 0⟩) → (∀ x ∈ W, Relation.ReflTransGen Q 0
            x)))))))
    ) := by
  classical
  intro P t W hq boundary Q segment horizVec vertical lineReach
  rintro x ⟨m, n, hx⟩
  have hc := (boundary _).mp hx
  have leftReach := (lineReach n).trans (vertical n 0 x.im)
  by_cases hleft : x.re = n*(P.q : Int)
  · convert leftReach using 1
    ext <;> simp [hleft]
  by_cases hright : x.re = (n+1)*(P.q : Int)
  · have hh := (lineReach (n+1)).trans (vertical (n+1) 0 x.im)
    convert hh using 1
    ext <;> simp [hright]
  have hr : 0 ≤ x.re-n*(P.q : Int) ∧ x.re-n*(P.q : Int) ≤ (P.q : Int) := by
    simpa [t] using And.intro hc.1 hc.2.1
  have hb : x.im-(t m n).im = 0 ∨ x.im-(t m n).im = (P.q : Int) := by
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub] at hc
    dsimp [t] at hc
    rcases hc.2.2.2.2 with h | h | h | h
    · omega
    · exfalso; apply hright; nlinarith only [h]
    · exact Or.inl h
    · exact Or.inr h
  let k := (x.re-n*(P.q : Int)).toNat
  have hk : (k : Int) = x.re-n*(P.q : Int) := Int.toNat_of_nonneg hr.1
  have hh := segment ⟨n*(P.q : Int), x.im⟩ 1 (Or.inl rfl) k
    (fun j hj => by
      refine ⟨m, n, (boundary _).mpr ?_⟩
      rw [horizVec]
      dsimp [t] at hb ⊢
      rcases hb with hb | hb <;> omega)
  have he : (⟨n*(P.q : Int), x.im⟩ : GaussianInt) + k • 1 = x := by
    ext <;> simp [hk]
  rw [he] at hh
  exact leftReach.trans hh

end FordWebGeometryProof

theorem P5442T1WebGeometry (P : FordFareyParameter) :
    let t : Int → Int → GaussianInt := fun m n =>
      ⟨n * (P.q : Int), n * (P.q₁ : Int) - m * (P.q : Int)⟩
    let W : Set GaussianInt := {x | ∃ m n : Int,
      x - t m n ∈ LatticeVertexBoundary (FordVertexDomain P.q)}
    (∀ m n, t m n ∈ FordExceptionalLattice P ∧
      ∀ x, FourNeighborLaplacian (FordOdometer P) (x + t m n) =
        FourNeighborLaplacian (FordOdometer P) x) ∧
    (∀ x ∈ W, FourNeighborLaplacian (FordOdometer P) x = 1) ∧
    FourNeighborConnected W ∧
    (∀ x, x ∉ W → ∃ m n : Int, ∀ y,
      Relation.ReflTransGen
        (fun u z => u ∉ W ∧ z ∉ W ∧ FourNeighborAdjacent u z) x y →
      y - t m n ∈ P4062T1InteriorSquare P.q) := by
-- BODY
  classical
  intro t W
  have hq : 0 < (P.q : Int) := by exact_mod_cast P.q_pos
  have boundary (x : GaussianInt) :
      x ∈ LatticeVertexBoundary (FordVertexDomain P.q) ↔
        0 ≤ x.re ∧ x.re ≤ (P.q : Int) ∧
        0 ≤ x.im ∧ x.im ≤ (P.q : Int) ∧
        (x.re = 0 ∨ x.re = (P.q : Int) ∨ x.im = 0 ∨ x.im = (P.q : Int)) :=
            FordWebGeometryProof.boundary P x
  have coords (x : GaussianInt) : x ∈ P4062T1InteriorSquare P.q ↔
      1 ≤ x.re ∧ x.re ≤ (P.q : Int) - 1 ∧
      1 ≤ x.im ∧ x.im ≤ (P.q : Int) - 1 := FordWebGeometryProof.coords P x
  have periods : ∀ m n, t m n ∈ FordExceptionalLattice P ∧
      ∀ x, FourNeighborLaplacian (FordOdometer P) (x+t m n) =
        FourNeighborLaplacian (FordOdometer P) x := FordWebGeometryProof.periods P
  refine ⟨periods, ?_, ?_, ?_⟩
  · rintro x ⟨m, n, hx⟩
    have hp := (periods m n).2 (x-t m n)
    rw [sub_add_cancel] at hp
    exact hp.trans ((FordLaplacianTable P).2.1 _ hx)
  · let Q : GaussianInt → GaussianInt → Prop :=
      fun u z => u ∈ W ∧ z ∈ W ∧ FourNeighborAdjacent u z
    have reverse {x y} (h : Relation.ReflTransGen Q x y) :
        Relation.ReflTransGen Q y x := by
      induction h with
      | refl => exact .refl
      | @tail u v h e ih =>
        have hs : FourNeighborAdjacent v u := by
          rcases e.2.2 with he | he | he | he <;> rw [he] <;>
            simp [FourNeighborAdjacent, add_assoc, add_comm, add_left_comm]
        exact (Relation.ReflTransGen.single ⟨e.2.1, e.1, hs⟩).trans ih
    have lineMem (n b : Int) : (⟨n*(P.q : Int), b⟩ : GaussianInt) ∈ W :=
        FordWebGeometryProof.lineMem P hq boundary n b
    have segment (a d : GaussianInt) (hd : d = 1 ∨ d = ⟨0,1⟩)
        (k : Nat) (hm : ∀ j : Nat, j ≤ k → a + j • d ∈ W) :
        Relation.ReflTransGen Q a (a + k • d) := FordWebGeometryProof.segment P a d hd k hm
    have horizVec (j : Nat) : j • (1 : GaussianInt) = ⟨j,0⟩ := by ext <;> simp
    have verticalUp (n b : Int) (k : Nat) :
        Relation.ReflTransGen Q ⟨n*(P.q : Int), b⟩ ⟨n*(P.q : Int), b+k⟩ := by
      have hh := segment ⟨n*(P.q : Int), b⟩ ⟨0,1⟩ (Or.inr rfl) k
        (fun j _ => by simpa using lineMem n (b+j))
      simpa using hh
    have vertical (n b c : Int) :
        Relation.ReflTransGen Q ⟨n*(P.q : Int), b⟩ ⟨n*(P.q : Int), c⟩ := by
      by_cases h : b ≤ c
      · have hh := verticalUp n b (c-b).toNat
        simpa [Int.toNat_of_nonneg (by omega : 0 ≤ c-b)] using hh
      · have hh := reverse (verticalUp n c (b-c).toNat)
        simpa [Int.toNat_of_nonneg (by omega : 0 ≤ b-c)] using hh
    have bridge (n : Int) :
        Relation.ReflTransGen Q ⟨n*(P.q : Int), n*(P.q₁ : Int)⟩
          ⟨(n+1)*(P.q : Int), n*(P.q₁ : Int)⟩ := FordWebGeometryProof.bridge P boundary segment
              horizVec n
    have link (n : Int) : Relation.ReflTransGen Q
        ⟨n*(P.q : Int), 0⟩ ⟨(n+1)*(P.q : Int), 0⟩ :=
      ((vertical n 0 (n*(P.q₁ : Int))).trans (bridge n)).trans
        (vertical (n+1) (n*(P.q₁ : Int)) 0)
    have lineReach (n : Int) : Relation.ReflTransGen Q 0 ⟨n*(P.q : Int), 0⟩ :=
        FordWebGeometryProof.lineReach P reverse link n
    have reach0 : ∀ x ∈ W, Relation.ReflTransGen Q 0 x := FordWebGeometryProof.reach0 P hq
        boundary segment horizVec vertical lineReach
    have zeroW : (0 : GaussianInt) ∈ W := by
      have hz : (⟨(0 : Int)*(P.q : Int), 0⟩ : GaussianInt) = 0 := by ext <;> simp
      exact hz ▸ lineMem 0 0
    refine ⟨⟨0, zeroW⟩, ?_⟩
    intro x hx y hy
    have hr := (reverse (reach0 x hx)).trans (reach0 y hy)
    obtain ⟨p, hc, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen hr
    refine ⟨x::p, rfl, ?_, ?_, ?_⟩
    · rw [List.getLast?_eq_some_getLast (List.cons_ne_nil x p), hlast]
    · exact hc.induction (fun z => z ∈ W) (x::p)
        (fun {u z} he _ => he.2.1) (fun _ => hx)
    · exact List.isChain_iff_forall_rel_of_append_cons_cons.mp
        (hc.imp (fun _ _ he => he.2.2))
  · intro x hx
    let n := x.re / (P.q : Int)
    let m := -((x.im-n*(P.q₁ : Int)) / (P.q : Int))
    let y := x-t m n
    have hyr : y.re = x.re % (P.q : Int) := by
      have he := Int.emod_add_mul_ediv x.re (P.q : Int)
      dsimp [y, t, n]
      nlinarith only [he]
    have hyi : y.im = (x.im-n*(P.q₁ : Int)) % (P.q : Int) := by
      have he := Int.emod_add_mul_ediv (x.im-n*(P.q₁ : Int)) (P.q : Int)
      dsimp [y, t, m]
      nlinarith only [he]
    have hr := Int.emod_nonneg x.re (ne_of_gt hq)
    have hr' := Int.emod_lt_of_pos x.re hq
    have hi := Int.emod_nonneg (x.im-n*(P.q₁ : Int)) (ne_of_gt hq)
    have hi' := Int.emod_lt_of_pos (x.im-n*(P.q₁ : Int)) hq
    have hnb : y ∉ LatticeVertexBoundary (FordVertexDomain P.q) :=
      fun h => hx ⟨m, n, h⟩
    have hy : y ∈ P4062T1InteriorSquare P.q := by
      rw [boundary] at hnb
      apply (coords y).mpr
      omega
    refine ⟨m, n, ?_⟩
    intro z hz
    induction hz with
    | refl => exact hy
    | @tail u v h e ih =>
      have hu := (coords _).mp ih
      have hv : 0 ≤ (v-t m n).re ∧ (v-t m n).re ≤ (P.q : Int) ∧
          0 ≤ (v-t m n).im ∧ (v-t m n).im ≤ (P.q : Int) := by
        rcases e.2.2 with rfl | rfl | rfl | rfl <;>
          simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add,
            Zsqrtd.re_one, Zsqrtd.im_one] at hu ⊢ <;> omega
      have hn : v-t m n ∉ LatticeVertexBoundary (FordVertexDomain P.q) :=
        fun h => e.2.1 ⟨m, n, h⟩
      rw [boundary] at hn
      apply (coords _).mpr
      omega

end ApollonianSuperharmonic

end
