/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.DiamondLaplacianTable
public import LeanPool.ApollonianSuperharmonic.FiniteAcyclicOrientationObstruction
public import LeanPool.ApollonianSuperharmonic.P5435T1Cocycle
public import LeanPool.ApollonianSuperharmonic.P5435T1WebGeometry
public import LeanPool.ApollonianSuperharmonic.P5432T1EdgeLedger

-- [TABLET NODE: DiamondExceptionalMaximality]

/-!
# DiamondExceptionalMaximality

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ExceptionalMaximalityProof

private theorem hgen :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let g := DiamondOdometer K
        let a : GaussianInt := ⟨0, -(2 * K.1 : Int)⟩
        let b : GaussianInt := ⟨(K.1 + 1 : Int), (K.1 : Int)⟩
        ((∀ (x : GaussianInt), FourNeighborLaplacian (DiamondOdometer K) (x + ⟨(0 : ℤ),
            (2 : ℤ) * (↑K.1 : ℤ)⟩) = FourNeighborLaplacian (DiamondOdometer K) x ∧
            FourNeighborLaplacian (DiamondOdometer K) (x + ⟨(↑K.1 : ℤ) + (1 : ℤ), (↑K.1 : ℤ)⟩) =
            FourNeighborLaplacian (DiamondOdometer K) x) ∧ (∀ x ∈ DiamondVertexDomains K false, x
            ∉ DiamondVertexDomains K true → FourNeighborLaplacian (DiamondOdometer K) x = (1 :
            ℤ)) ∧ ∀ x ∈ DiamondVertexDomains K true, FourNeighborLaplacian (DiamondOdometer K) x
            = (if Even (x.re + x.im) then (1 : ℤ) else (-1 : ℤ)) - if x.re = (0 : ℤ) then (1 : ℤ)
            else (0 : ℤ)) → (
        let H : AddSubgroup GaussianInt :=
          { carrier := {v | ∀ x, FourNeighborLaplacian g (x+v) = FourNeighborLaplacian g x}
            zero_mem' := by intro x; simp
            add_mem' := by
              intro u v hu hv x
              rw [← add_assoc, hv, hu]
            neg_mem' := by
              intro v hv x
              have h := hv (x-v)
              rw [sub_add_cancel] at h
              simpa only [sub_eq_add_neg] using h.symm }
        {v : GaussianInt | v = a ∨ v = b} ⊆ H)) := by
  classical
  intro K g a b tab H v hv
  rcases hv with rfl | rfl
  · intro x
    have h := (tab.1 (x+a)).1
    have he : x+a+⟨0, (2*K.1 : Int)⟩ = x := by
      ext <;> simp [a]
    rw [he] at h
    exact h.symm
  · intro x
    exact (tab.1 x).2

private theorem periods :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let g := DiamondOdometer K
        let a : GaussianInt := ⟨0, -(2 * K.1 : Int)⟩
        let b : GaussianInt := ⟨(K.1 + 1 : Int), (K.1 : Int)⟩
        let H : AddSubgroup GaussianInt :=
          { carrier := {v | ∀ x, FourNeighborLaplacian g (x+v) = FourNeighborLaplacian g x}
            zero_mem' := by intro x; simp
            add_mem' := by
              intro u v hu hv x
              rw [← add_assoc, hv, hu]
            neg_mem' := by
              intro v hv x
              have h := hv (x-v)
              rw [sub_add_cancel] at h
              simpa only [sub_eq_add_neg] using h.symm }
        ({v : GaussianInt | v = a ∨ v = b} ⊆ H) → (∀ v ∈ DiamondExceptionalLattice K, ∀ x,
            FourNeighborLaplacian g (x+v) = FourNeighborLaplacian g x) ) := by
  classical
  intro K g a b H hgen v hv
  exact ((AddSubgroup.closure_le H).mpr hgen) hv

private theorem bound :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let g := DiamondOdometer K
        let a : GaussianInt := ⟨0, -(2 * K.1 : Int)⟩
        let b : GaussianInt := ⟨(K.1 + 1 : Int), (K.1 : Int)⟩
        ((∀ (x : GaussianInt), FourNeighborLaplacian (DiamondOdometer K) (x + ⟨(0 : ℤ), (2 : ℤ) *
            (↑K.1 : ℤ)⟩) = FourNeighborLaplacian (DiamondOdometer K) x ∧ FourNeighborLaplacian
            (DiamondOdometer K) (x + ⟨(↑K.1 : ℤ) + (1 : ℤ), (↑K.1 : ℤ)⟩) = FourNeighborLaplacian
            (DiamondOdometer K) x) ∧ (∀ x ∈ DiamondVertexDomains K false, x ∉
            DiamondVertexDomains K true → FourNeighborLaplacian (DiamondOdometer K) x = (1 : ℤ))
            ∧ ∀ x ∈ DiamondVertexDomains K true, FourNeighborLaplacian (DiamondOdometer K) x =
            (if Even (x.re + x.im) then (1 : ℤ) else (-1 : ℤ)) - if x.re = (0 : ℤ) then (1 : ℤ)
            else (0 : ℤ)) → ((a ∈ DiamondExceptionalLattice K) → ((b ∈ DiamondExceptionalLattice
            K) → ((∀ v ∈ DiamondExceptionalLattice K, ∀ x, FourNeighborLaplacian g (x+v) =
            FourNeighborLaplacian g x) → (∀ x, FourNeighborLaplacian g x ≤ 1)))) ) := by
  classical
  intro K g a b tab ha hb periods x
  let D := DiamondVertexDomains K true
  obtain ⟨p, hp, _⟩ := P4818T1Representatives K x
  let v := p.2.1 • a + p.2.2 • b
  have hv : v ∈ DiamondExceptionalLattice K :=
    (DiamondExceptionalLattice K).add_mem
      ((DiamondExceptionalLattice K).zsmul_mem ha _)
      ((DiamondExceptionalLattice K).zsmul_mem hb _)
  have he : x = p.1+v := by
    simpa only [v, a, b, neg_mul, add_assoc] using hp.2
  rw [he, periods v hv]
  have hpT : p.1 ∈ DiamondVertexDomains K false := hp.1.1
  by_cases hi : p.1 ∈ D
  · have h := tab.2.2 p.1 hi
    dsimp [g]
    rw [h]
    split_ifs <;> omega
  · exact le_of_eq (tab.2.1 p.1 hpT hi)

private theorem hweb :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let g := DiamondOdometer K
        let D := DiamondVertexDomains K true
        let S := DiamondVertexDomains K false \ D
        let W : Set GaussianInt :=
          {x | ∃ v ∈ DiamondExceptionalLattice K, x - v ∈ S}
        ((∀ (x : GaussianInt), FourNeighborLaplacian (DiamondOdometer K) (x + ⟨(0 : ℤ), (2 : ℤ) *
            (↑K.1 : ℤ)⟩) = FourNeighborLaplacian (DiamondOdometer K) x ∧ FourNeighborLaplacian
            (DiamondOdometer K) (x + ⟨(↑K.1 : ℤ) + (1 : ℤ), (↑K.1 : ℤ)⟩) = FourNeighborLaplacian
            (DiamondOdometer K) x) ∧ (∀ x ∈ DiamondVertexDomains K false, x ∉
            DiamondVertexDomains K true → FourNeighborLaplacian (DiamondOdometer K) x = (1 : ℤ))
            ∧ ∀ x ∈ DiamondVertexDomains K true, FourNeighborLaplacian (DiamondOdometer K) x =
            (if Even (x.re + x.im) then (1 : ℤ) else (-1 : ℤ)) - if x.re = (0 : ℤ) then (1 : ℤ)
            else (0 : ℤ)) → ((∀ v ∈ DiamondExceptionalLattice K, ∀ x, FourNeighborLaplacian g
            (x+v) = FourNeighborLaplacian g x) → (∀ w ∈ W, FourNeighborLaplacian g w = 1)) ) := by
  classical
  intro K g D S W tab periods
  rintro w ⟨v, hv, hs⟩
  have h := periods v hv (w-v)
  rw [sub_add_cancel] at h
  exact h.trans (tab.2.1 (w-v) hs.1 hs.2)

private theorem finD :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let D := DiamondVertexDomains K true
        D.Finite ) := by
  classical
  intro K D
  let k : Int := K.1
  let box : Finset GaussianInt :=
    ((Finset.Icc (-k) k).product (Finset.Icc 0 (2*k))).image
      (fun p : Int × Int => (⟨p.1, p.2⟩ : GaussianInt))
  apply box.finite_toSet.subset
  intro x hx
  change x.re.natAbs + (x.im-k).natAbs ≤ K.1-1 at hx
  have hr := Int.natCast_natAbs x.re
  have hi := Int.natCast_natAbs (x.im-k)
  have hk : 0 < k := by dsimp [k]; exact_mod_cast K.2
  have hkdef : (K.1 : Int) = k := rfl
  simp only [abs_eq_max_neg] at hr hi
  change x ∈ box
  dsimp only [box]
  apply Finset.mem_image.mpr
  refine ⟨(x.re,x.im), ?_, by ext <;> rfl⟩
  apply Finset.mem_product.mpr
  constructor
  · apply Finset.mem_Icc.mpr
    constructor <;> omega
  · apply Finset.mem_Icc.mpr
    constructor <;> omega

private theorem hD :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let D := DiamondVertexDomains K true
        ∀ (finD : D.Finite),
        let Df := finD.toFinset
        ∀ x, x ∈ Df ↔ x ∈ DiamondVertexDomains K true ) := by
  classical
  intro K D finD Df x
  exact finD.mem_toFinset

private theorem symm :
    (by
      classical
      exact
        ∀ x, ∀ y, FourNeighborAdjacent x y → FourNeighborAdjacent y x ) := by
  classical
  intro x y h
  rcases h with rfl | rfl | rfl | rfl <;>
    simp [FourNeighborAdjacent, add_assoc, add_comm, add_left_comm]

private theorem meet :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let D := DiamondVertexDomains K true
        let S := DiamondVertexDomains K false \ D
        let W : Set GaussianInt :=
          {x | ∃ v ∈ DiamondExceptionalLattice K, x - v ∈ S}
        (FourNeighborConnected W ∧ ∀ x ∉ W, ∃ v ∈ DiamondExceptionalLattice K, ∀ (y :
            GaussianInt), Relation.ReflTransGen (fun (u z : GaussianInt) => u ∉ W ∧ z ∉ W ∧
            FourNeighborAdjacent u z) x y → y - v ∈ D) → ((D.Finite) → (∀ (X : Set GaussianInt),
            (X.Infinite) → ((FourNeighborConnected X) → ((X ∩ W).Nonempty)))) ) := by
  classical
  intro K D S W geom finD X hXin hXconn
  by_contra hn
  have hout : ∀ x ∈ X, x ∉ W := by
    intro x hx hw
    exact hn ⟨x, hx, hw⟩
  obtain ⟨x0, hx0⟩ := hXconn.1
  obtain ⟨v, hv, howner⟩ := geom.2 x0 (hout x0 hx0)
  have hsub : X ⊆ (fun t => t+v) '' D := by
    intro y hy
    obtain ⟨p, hp, hlast, pall, padj⟩ := hXconn.2 x0 hx0 y hy
    have hc : p.IsChain
        (fun u z => u ∉ W ∧ z ∉ W ∧ FourNeighborAdjacent u z) := by
      apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
      intro u z l₁ l₂ he
      refine ⟨hout u (pall u (by simp [he])),
        hout z (pall z (by simp [he])), padj u z l₁ l₂ he⟩
    have hreach : Relation.ReflTransGen
        (fun u z => u ∉ W ∧ z ∉ W ∧ FourNeighborAdjacent u z) x0 y := by
      cases p with
      | nil => simp at hp
      | cons u p =>
        simp only [List.head?_cons, Option.some.injEq] at hp
        subst u
        exact List.relationReflTransGen_of_exists_isChain_cons p hc
          (List.getLast_of_getLast?_eq_some hlast)
    exact ⟨y-v, howner y hreach, sub_add_cancel y v⟩
  exact hXin.not_finite ((finD.image (fun t => t+v)).subset hsub)

private theorem noCross :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let g := DiamondOdometer K
        let D := DiamondVertexDomains K true
        let S := DiamondVertexDomains K false \ D
        let W : Set GaussianInt :=
          {x | ∃ v ∈ DiamondExceptionalLattice K, x - v ∈ S}
        (∀ w ∈ W, FourNeighborLaplacian g w = 1) → (∀ (X : Set GaussianInt), (∀ (x :
            GaussianInt), FourNeighborLaplacian (fun (y : GaussianInt) => DiamondOdometer K y +
            X.indicator ((fun _ : GaussianInt => (1 : ℤ))) y) x ≤ (1 : ℤ)) → (∀ w ∈ W, ∀ z,
                FourNeighborAdjacent w z → z ∈ X → w ∈ X))) := by
  classical
  intro K g D S W hweb X hle w hw z hadj hz
  by_contra hn
  have ht := hweb w hw
  dsimp only [g] at ht
  have hh := hle w
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals
    simp only [FourNeighborLaplacian, Set.indicator_apply] at hh ht
    simp only [ite_eq_left hz, ite_eq_right hn] at hh
    split_ifs at hh <;> omega

private theorem Wsub :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let D := DiamondVertexDomains K true
        let S := DiamondVertexDomains K false \ D
        let W : Set GaussianInt :=
          {x | ∃ v ∈ DiamondExceptionalLattice K, x - v ∈ S}
        (FourNeighborConnected W ∧ ∀ x ∉ W, ∃ v ∈ DiamondExceptionalLattice K, ∀ (y :
            GaussianInt), Relation.ReflTransGen (fun (u z : GaussianInt) => u ∉ W ∧ z ∉ W ∧
            FourNeighborAdjacent u z) x y → y - v ∈ D) → (∀ (X : Set GaussianInt), (∀ x, ∀ y,
            FourNeighborAdjacent x y → FourNeighborAdjacent y x) → (((X ∩ W).Nonempty) → ((∀ w ∈
            W, ∀ z, FourNeighborAdjacent w z → z ∈ X → w ∈ X) → (W ⊆ X)))) ) := by
  classical
  intro K D S W geom X symm meet noCross w hw
  obtain ⟨x0, hx0, hx0W⟩ := meet
  obtain ⟨p, hp, hlast, pall, padj⟩ := geom.1.2 x0 hx0W w hw
  have hc : p.IsChain (fun u z => u ∈ W ∧ z ∈ W ∧ FourNeighborAdjacent u z) := by
    apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro u z l₁ l₂ he
    exact ⟨pall u (by simp [he]), pall z (by simp [he]), padj u z l₁ l₂ he⟩
  have hall : ∀ z ∈ p, z ∈ X :=
    hc.induction (fun z => z ∈ X) p
      (fun {u z} he hu => noCross z he.2.1 u (symm u z he.2.2) hu)
      (by
        intro hn
        have he : p.head hn = x0 := by
          simpa only [List.head?_eq_some_head hn, Option.some.injEq] using hp
        simpa only [he] using hx0)
  exact hall w (by
    rw [← List.getLast_of_getLast?_eq_some hlast]
    exact List.getLast_mem (by intro he; simp [he] at hp))

private theorem Yout :
    (by
      classical
      exact
        ∀ (X : Set GaussianInt), ∀ (z : GaussianInt), (z ∉ X) → (
        let R := fun u t => u ∉ X ∧ t ∉ X ∧ FourNeighborAdjacent u t
        let Y : Set GaussianInt := {y | Relation.ReflTransGen R z y}
        ∀ y ∈ Y, y ∉ X) ) := by
  classical
  intro X z hz R Y y hy
  induction hy with
  | refl => exact hz
  | tail h e ih => exact e.2.1

private theorem Ysub :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let D := DiamondVertexDomains K true
        let S := DiamondVertexDomains K false \ D
        let W : Set GaussianInt :=
          {x | ∃ v ∈ DiamondExceptionalLattice K, x - v ∈ S}
        ∀ (X : Set GaussianInt), (W ⊆ X) → (∀ (z : GaussianInt),
        let R := fun u t => u ∉ X ∧ t ∉ X ∧ FourNeighborAdjacent u t
        let Y : Set GaussianInt := {y | Relation.ReflTransGen R z y}
        ∀ (v : GaussianInt), (∀ (y : GaussianInt), Relation.ReflTransGen (fun (u z : GaussianInt)
            => u ∉ W ∧ z ∉ W ∧ FourNeighborAdjacent u z) z y → y - v ∈ D) → (∀ y ∈ Y, y-v ∈ D)) )
            := by
  classical
  intro K D S W X Wsub z R Y v howner y hy
  apply howner y
  exact Relation.ReflTransGen.mono (fun u t he =>
    ⟨fun hw => he.1 (Wsub hw), fun hw => he.2.1 (Wsub hw), he.2.2⟩) _ _ hy

private theorem Yfin :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let D := DiamondVertexDomains K true
        (D.Finite) → (∀ (X : Set GaussianInt), ∀ (z : GaussianInt),
        let R := fun u t => u ∉ X ∧ t ∉ X ∧ FourNeighborAdjacent u t
        let Y : Set GaussianInt := {y | Relation.ReflTransGen R z y}
        ∀ (v : GaussianInt), (∀ y ∈ Y, y-v ∈ D) → (Y.Finite)) ) := by
  classical
  intro K D finD X z R Y v Ysub
  apply (finD.image (fun t => t+v)).subset
  intro y hy
  exact ⟨y-v, Ysub y hy, sub_add_cancel y v⟩

private theorem Zsub :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
        let D := DiamondVertexDomains K true
        ∀ (finD : D.Finite),
        let Df := finD.toFinset
        ∀ (X : Set GaussianInt), ∀ (z : GaussianInt),
        let R := fun u t => u ∉ X ∧ t ∉ X ∧ FourNeighborAdjacent u t
        let Y : Set GaussianInt := {y | Relation.ReflTransGen R z y}
        ∀ (v : GaussianInt), (∀ y ∈ Y, y-v ∈ D) → (∀ (Yfin : Y.Finite),
        let Z := Yfin.toFinset.image (fun y => y-v)
        Z ⊆ Df) ) := by
  classical
  intro K D finD Df X z R Y v Ysub Yfin Z p hp
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
  exact finD.mem_toFinset.mpr (Ysub y (Yfin.mem_toFinset.mp hy))

private theorem memZ :
    (by
      classical
      exact
        ∀ (X : Set GaussianInt), ∀ (z : GaussianInt),
        let R := fun u t => u ∉ X ∧ t ∉ X ∧ FourNeighborAdjacent u t
        let Y : Set GaussianInt := {y | Relation.ReflTransGen R z y}
        ∀ (v : GaussianInt), ∀ (Yfin : Y.Finite),
        let Z := Yfin.toFinset.image (fun y => y-v)
        ∀ (t : GaussianInt), t ∈ Z ↔ t + v ∈ Y ) := by
  classical
  intro X z R Y v Yfin Z t
  constructor
  · intro ht
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp ht
    have he' : y=t+v := by rw [← he]; abel
    simpa only [he'] using Yfin.mem_toFinset.mp hy
  · intro ht
    exact Finset.mem_image.mpr
      ⟨t+v, Yfin.mem_toFinset.mpr ht, by simp⟩

private theorem localMem :
    (by
      classical
      exact
        ∀ (K : DiamondParameter),
          let g := DiamondOdometer K;
          ∀ (X : Set GaussianInt),
            ∀ (z : GaussianInt),
              let R := fun u t => u ∉ X ∧ t ∉ X ∧ FourNeighborAdjacent u t;
              let Y : Set GaussianInt := {y | Relation.ReflTransGen R z y};
              (∀ y ∈ Y, y ∉ X) →
                ∀ (v : GaussianInt),
                  ∀ (Yfin : Y.Finite),
                    let Z := Yfin.toFinset.image fun y => y - v;
                    ∀ (p : GaussianInt),
                      (2 : ℤ) ≤
                          FourNeighborLaplacian
                            (fun (z : GaussianInt) =>
                              g z - if z ∈ Z then (1 : ℤ) else (0 : ℤ))
                            p →
                        (∀ (t : GaussianInt), t ∈ Z ↔ t + v ∈ Y) →
                          p + v ∈ Y →
                            ∀ t, t = p ∨ FourNeighborAdjacent p t → (t ∈ Z ↔ t + v ∉ X)
    )
            := by
  classical
  intro K g X z R Y Yout v Yfin Z p hobs memZ py t ht
  constructor
  · intro htZ
    exact Yout (t+v) ((memZ t).mp htZ)
  · intro htX
    apply (memZ t).mpr
    rcases ht with rfl | ht
    · exact py
    · apply Relation.ReflTransGen.tail py
      refine ⟨Yout (p+v) py, htX, ?_⟩
      rcases ht with rfl | rfl | rfl | rfl <;>
        simp [FourNeighborAdjacent, sub_eq_add_neg, add_assoc, add_comm]

private theorem value :
    (by
      classical
        exact
          (∀ (X : Set GaussianInt),
            ∀ (z : GaussianInt),
              let R := fun u t => u ∉ X ∧ t ∉ X ∧ FourNeighborAdjacent u t;
              let Y : Set GaussianInt := {y | Relation.ReflTransGen R z y};
              ∀ (v : GaussianInt),
                ∀ (Yfin : Y.Finite),
                  let Z := Yfin.toFinset.image (fun y => y - v);
                  ∀ (p : GaussianInt),
                    (∀ t,
                        (t = p ∨ FourNeighborAdjacent p t) → (t ∈ Z ↔ t + v ∉ X)) →
                      (∀ (t : GaussianInt),
                        t = p ∨ FourNeighborAdjacent p t →
                          (if t ∈ Z then (1 : ℤ) else (0 : ℤ)) +
                              X.indicator (fun _ : GaussianInt => (1 : ℤ)) (t + v) =
                            (1 : ℤ)))) := by
  classical
  intro X z R Y v Yfin Z p localMem t ht
  have hm := localMem t ht
  by_cases h : t ∈ Z
  · simp [h, hm.mp h]
  · have hx : t+v ∈ X := by tauto
    simp [h, hx]

end ExceptionalMaximalityProof

theorem DiamondExceptionalMaximality (K : DiamondParameter) :
    (∀ x, FourNeighborLaplacian (DiamondOdometer K) x <= 1) ∧
    (∀ v, v ∈ DiamondExceptionalLattice K -> ∃ a : GaussianInt,
      Matrix.mulVec (DiamondPeakMatrix K)
        ![(v.re : Real), (v.im : Real)] =
          ![(a.re : Real), (a.im : Real)] ∧
      ∀ x, DiamondOdometer K (x + v) = DiamondOdometer K x +
        x.re * a.re + x.im * a.im + DiamondOdometer K v) ∧
    (∀ X : Set GaussianInt, X.Infinite -> FourNeighborConnected X ->
      (∀ x, FourNeighborLaplacian
        (fun y => DiamondOdometer K y +
          Set.indicator X (fun _ => (1 : Int)) y) x <= 1) ->
      X = Set.univ) := by
-- BODY
  classical
  let g := DiamondOdometer K
  let k : Int := K.1
  let a : GaussianInt := ⟨0, -(2 * K.1 : Int)⟩
  let b : GaussianInt := ⟨(K.1 + 1 : Int), (K.1 : Int)⟩
  let D := DiamondVertexDomains K true
  let S := DiamondVertexDomains K false \ D
  let W : Set GaussianInt :=
    {x | ∃ v ∈ DiamondExceptionalLattice K, x - v ∈ S}
  have tab := DiamondLaplacianTable K
  have ha : a ∈ DiamondExceptionalLattice K :=
    AddSubgroup.subset_closure (Or.inl rfl)
  have hb : b ∈ DiamondExceptionalLattice K :=
    AddSubgroup.subset_closure (Or.inr rfl)
  let H : AddSubgroup GaussianInt :=
    { carrier := {v | ∀ x, FourNeighborLaplacian g (x+v) = FourNeighborLaplacian g x}
      zero_mem' := by intro x; simp
      add_mem' := by
        intro u v hu hv x
        rw [← add_assoc, hv, hu]
      neg_mem' := by
        intro v hv x
        have h := hv (x-v)
        rw [sub_add_cancel] at h
        simpa only [sub_eq_add_neg] using h.symm }
  have hgen := ExceptionalMaximalityProof.hgen K tab
  have periods := ExceptionalMaximalityProof.periods K hgen
  have bound := ExceptionalMaximalityProof.bound K tab ha hb periods
  have hweb := ExceptionalMaximalityProof.hweb K tab periods
  have geom := P5435T1WebGeometry K
  change FourNeighborConnected W ∧
    ∀ x, x ∉ W → ∃ v ∈ DiamondExceptionalLattice K, ∀ y,
      Relation.ReflTransGen
        (fun u z => u ∉ W ∧ z ∉ W ∧ FourNeighborAdjacent u z) x y →
      y-v ∈ D at geom
  have finD := ExceptionalMaximalityProof.finD K
  let Df := finD.toFinset
  have hD := ExceptionalMaximalityProof.hD K finD
  obtain ⟨hsupp, horient, hrank, hcount⟩ := P5432T1EdgeLedger K Df hD
  let o : AcyclicIndegreeOrientation Df (fun x => 2 + FourNeighborLaplacian g x) :=
    { edge := fun x y => x ∈ Df ∧ y ∈ Df ∧ FourNeighborAdjacent x y ∧
        (x.re.natAbs < y.re.natAbs ∨
          (x.re = y.re ∧ ¬ Even (x.re+x.im) ∧ Even (y.re+y.im)))
      edgeDecidable := fun _ _ => Classical.propDecidable _
      rank := fun x => 2*x.re.natAbs + if Even (x.re+x.im) then 1 else 0
      supported := hsupp
      oriented := horient
      increasing := hrank
      indegree := by
        intro x hx
        have hc := hcount x hx
        have hl := tab.2.2 x ((hD x).mp hx)
        change _ = 2 + FourNeighborLaplacian (DiamondOdometer K) x
        rw [hl, hc]
        split_ifs <;> norm_num }
  refine ⟨bound, P5435T1Cocycle K, ?_⟩
  intro X hXin hXconn hle
  have symm : ∀ x y, FourNeighborAdjacent x y → FourNeighborAdjacent y x :=
      ExceptionalMaximalityProof.symm
  have meet := ExceptionalMaximalityProof.meet K geom finD X hXin hXconn
  have noCross := ExceptionalMaximalityProof.noCross K hweb X hle
  have Wsub := ExceptionalMaximalityProof.Wsub K geom X symm meet noCross
  apply Set.eq_univ_of_forall
  intro z
  by_contra hz
  let R := fun u t => u ∉ X ∧ t ∉ X ∧ FourNeighborAdjacent u t
  let Y : Set GaussianInt := {y | Relation.ReflTransGen R z y}
  have zY : z ∈ Y := Relation.ReflTransGen.refl
  have Yout := ExceptionalMaximalityProof.Yout X z hz
  obtain ⟨v, hv, howner⟩ := geom.2 z (fun hw => hz (Wsub hw))
  have Ysub := ExceptionalMaximalityProof.Ysub K X Wsub z v howner
  have Yfin := ExceptionalMaximalityProof.Yfin K finD X z v Ysub
  let Z := Yfin.toFinset.image (fun y => y-v)
  have Zne : Z.Nonempty :=
    ⟨z-v, Finset.mem_image.mpr ⟨z, Yfin.mem_toFinset.mpr zY, rfl⟩⟩
  have Zsub := ExceptionalMaximalityProof.Zsub K finD X z v Ysub Yfin
  obtain ⟨p, hp, hobs⟩ := FiniteAcyclicOrientationObstruction Df g o Z Zne Zsub
  have memZ (t : GaussianInt) := ExceptionalMaximalityProof.memZ X z v Yfin t
  have py : p+v ∈ Y := (memZ p).mp hp
  have localMem := ExceptionalMaximalityProof.localMem K X z Yout v Yfin p hobs memZ py
  have value (t : GaussianInt) (ht : t=p ∨ FourNeighborAdjacent p t) :=
      ExceptionalMaximalityProof.value X z v Yfin p
      localMem t ht
  have e0 := value p (Or.inl rfl)
  have e1 := value (p+1) (Or.inr (Or.inl rfl))
  have e2 := value (p-1) (Or.inr (Or.inr (Or.inl rfl)))
  have e3 := value (p+⟨0,1⟩) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have e4 := value (p-⟨0,1⟩) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hperiod := periods v hv p
  have hh := hle (p+v)
  have c1 : p+1+v=p+v+1 := by abel
  have c2 : p-1+v=p+v-1 := by abel
  have c3 : p+⟨0,1⟩+v=p+v+⟨0,1⟩ := by abel
  have c4 : p-⟨0,1⟩+v=p+v-⟨0,1⟩ := by abel
  rw [c1] at e1
  rw [c2] at e2
  rw [c3] at e3
  rw [c4] at e4
  simp only [FourNeighborLaplacian] at hobs hperiod hh
  change _ ≤ 1 at hh
  linarith only [hobs, hperiod, hh, e0, e1, e2, e3, e4]

end ApollonianSuperharmonic

end
