/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5157T1DiamondStaircaseIntersections
public import LeanPool.ApollonianSuperharmonic.P5157T1AlternatingStaircase
public import LeanPool.ApollonianSuperharmonic.TileReflectionFormulas
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween

-- [TABLET NODE: P5290T1PredecessorPath]

/-!
# P5290T1PredecessorPath

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PredecessorPathProof

private theorem hDsym :
    ∀ (k : Nat),
    let D : ProtoTile := DiamondTile k
    let K : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - 1 - z.im⟩
    (∀ (m : Nat), ∀ (z : GaussianInt), z ∈ DiamondCellDomain m ↔ ⟨z.re, 2 * (m : Int) - 1 - z.im⟩
        ∈ DiamondCellDomain m) → ((∀ (z : GaussianInt), K (K z) = z) → (D.cells.image K =
        D.cells)) := by
  classical
  intro k D K domain_sym k_invol
  change (DiamondCellDomain k).image K = DiamondCellDomain k
  have hdom : (DiamondCellDomain k).image K = DiamondCellDomain k := by
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hs := (domain_sym k w).mp hw
      convert hs using 1
    · intro hz
      exact ⟨K z, by
        have hs := (domain_sym k z).mp hz
        convert hs using 1  ,
        k_invol z⟩
  exact hdom

private theorem hScells :
    ∀ (k : Nat),
    let D : ProtoTile := DiamondTile k
    let S : ProtoTile := TileTranslation (TileReflection D) ⟨0, 2 * (k : Int)⟩
    let K : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - 1 - z.im⟩
    (D.cells.image K = D.cells) → (S.cells = D.cells) := by
  classical
  intro k D S K hDsym
  simp only [S, D, TileTranslation, TileReflection, DiamondTile]
  rw [Finset.image_image]
  change (DiamondCellDomain k).image
    (GaussianTranslation ⟨0, 2 * (k : Int)⟩ ∘
      (fun z => GaussianReflection z - ⟨0, 1⟩)) = DiamondCellDomain k
  rw [show (GaussianTranslation ⟨0, 2 * (k : Int)⟩ ∘
    (fun z => GaussianReflection z - ⟨0, 1⟩)) = K from by
      funext z
      apply Zsqrtd.ext <;> simp [K, GaussianTranslation, GaussianReflection]; ring]
  exact hDsym

private theorem hRimage :
    ∀ (k : Nat),
    let E : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), 1 - (k : Int)⟩
    let R : ProtoTile := TileTranslation (TileReflection E) ⟨0, 2 * (k : Int)⟩
    let K : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - 1 - z.im⟩
    (R.cells = (DiamondCellDomain (k - 1)).image (fun a => ⟨a.re + (k : Int), 3 * (k : Int) - 2 -
        a.im⟩)) → (R.cells = E.cells.image K) := by
  classical
  intro k E R K hRcells
  rw [hRcells]
  change (DiamondCellDomain (k - 1)).image
      (fun a => ⟨a.re + (k : Int), 3 * (k : Int) - 2 - a.im⟩) =
    ((DiamondCellDomain (k - 1)).image
      (GaussianTranslation ⟨(k : Int), 1 - (k : Int)⟩)).image K
  rw [Finset.image_image]
  apply Finset.image_congr
  intro a ha
  apply Zsqrtd.ext <;> simp [K, GaussianTranslation]; ring

private theorem hRedges :
    ∀ (k : Nat),
    let E : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), 1 - (k : Int)⟩
    let R : ProtoTile := TileTranslation (TileReflection E) ⟨0, 2 * (k : Int)⟩
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    BoundaryFootprintEdges R =
      (fun e : Finset GaussianInt => e.image J) '' BoundaryFootprintEdges E := by
  classical
  intro k E R J
  rcases TileReflectionFormulas E with ⟨_, _, _, _, _, _, _, hrv, hre⟩
  rcases TileTranslationFormulas (TileReflection E) ⟨0, 2 * (k : Int)⟩ with
    ⟨_, _, _, _, _, _, _, htv, hte⟩
  rw [hte, hre, Set.image_image]
  apply Set.image_congr
  intro e he
  rw [Finset.image_image]
  apply Finset.image_congr
  intro z hz
  apply Zsqrtd.ext <;> simp [J, GaussianTranslation, GaussianReflection]; ring

private theorem hSedges :
    ∀ (k : Nat),
    let D : ProtoTile := DiamondTile k
    let S : ProtoTile := TileTranslation (TileReflection D) ⟨0, 2 * (k : Int)⟩
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    BoundaryFootprintEdges S =
      (fun e : Finset GaussianInt => e.image J) '' BoundaryFootprintEdges D := by
  classical
  intro k D S J
  rcases TileReflectionFormulas D with ⟨_, _, _, _, _, _, _, hrv, hre⟩
  rcases TileTranslationFormulas (TileReflection D) ⟨0, 2 * (k : Int)⟩ with
    ⟨_, _, _, _, _, _, _, htv, hte⟩
  rw [hte, hre, Set.image_image]
  apply Set.image_congr
  intro e he
  rw [Finset.image_image]
  apply Finset.image_congr
  intro z hz
  apply Zsqrtd.ext <;> simp [J, GaussianTranslation, GaussianReflection]; ring

private theorem hJEinj :
    ∀ (k : Nat),
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    (Function.Injective J) → (
    let JE : Finset GaussianInt → Finset GaussianInt := fun e => e.image J
    Function.Injective JE) := by
  classical
  intro k J hJinj JE e f hef
  change e.image J = f.image J at hef
  ext z
  constructor
  · intro hz
    have hz' : J z ∈ e.image J := Finset.mem_image.mpr ⟨z, hz, rfl⟩
    rw [hef] at hz'
    rcases Finset.mem_image.mp hz' with ⟨w, hw, hzw⟩
    have : w = z := hJinj hzw
    simpa [this] using hw
  · intro hz
    have hz' : J z ∈ f.image J := Finset.mem_image.mpr ⟨z, hz, rfl⟩
    rw [← hef] at hz'
    rcases Finset.mem_image.mp hz' with ⟨w, hw, hzw⟩
    have : w = z := hJinj hzw
    simpa [this] using hw

private theorem hVerticesInter :
    ∀ (k : Nat),
    let D : ProtoTile := DiamondTile k
    let E : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), 1 - (k : Int)⟩
    let Z : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), (k : Int) + 1⟩
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    (Function.Injective J) → ((BoundaryFootprintVertices Z = J '' BoundaryFootprintVertices E) →
        ((BoundaryFootprintVertices D = J '' BoundaryFootprintVertices D) →
        (BoundaryFootprintVertices Z ∩ BoundaryFootprintVertices D =
        J '' (BoundaryFootprintVertices E ∩ BoundaryFootprintVertices D)))) := by
  classical
  intro k D E Z J hJinj hZvertices hDvertices
  have hDvertexInv : J '' BoundaryFootprintVertices D = BoundaryFootprintVertices D :=
    hDvertices.symm
  calc
    BoundaryFootprintVertices Z ∩ BoundaryFootprintVertices D =
        J '' BoundaryFootprintVertices E ∩ BoundaryFootprintVertices D := by
      rw [hZvertices]
    _ = J '' BoundaryFootprintVertices E ∩ J '' BoundaryFootprintVertices D := by
      rw [hDvertexInv]
    _ = J '' (BoundaryFootprintVertices E ∩ BoundaryFootprintVertices D) :=
      (Set.image_inter hJinj).symm

private theorem hEdgesInter :
    ∀ (k : Nat),
    let D : ProtoTile := DiamondTile k
    let E : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), 1 - (k : Int)⟩
    let Z : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), (k : Int) + 1⟩
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    (BoundaryFootprintEdges Z = (fun e : Finset GaussianInt => e.image J) ''
        BoundaryFootprintEdges E) → ((BoundaryFootprintEdges D = (fun e : Finset GaussianInt =>
        e.image J) '' BoundaryFootprintEdges D) → (
    let JE : Finset GaussianInt → Finset GaussianInt := fun e => e.image J
    (Function.Injective JE) → (BoundaryFootprintEdges Z ∩ BoundaryFootprintEdges D =
        JE '' (BoundaryFootprintEdges E ∩ BoundaryFootprintEdges D)))) := by
  classical
  intro k D E Z J hZedges hDedges JE hJEinj
  have hDedgeInv : JE '' BoundaryFootprintEdges D = BoundaryFootprintEdges D :=
    hDedges.symm
  calc
    BoundaryFootprintEdges Z ∩ BoundaryFootprintEdges D =
        JE '' BoundaryFootprintEdges E ∩ BoundaryFootprintEdges D := by
      rw [hZedges]
    _ = JE '' BoundaryFootprintEdges E ∩ JE '' BoundaryFootprintEdges D := by
      rw [hDedgeInv]
    _ = JE '' (BoundaryFootprintEdges E ∩ BoundaryFootprintEdges D) := by
      exact (Set.image_inter hJEinj).symm

private theorem hVerticesExact :
    ∀ (k : Nat),
    let D : ProtoTile := DiamondTile k
    let E : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), 1 - (k : Int)⟩
    let Z : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), (k : Int) + 1⟩
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    (BoundaryFootprintVertices Z ∩ BoundaryFootprintVertices D = J '' (BoundaryFootprintVertices
        E ∩ BoundaryFootprintVertices D)) → (
    let n : Nat := 2 * (k - 1)
    let p : Nat → GaussianInt := P5157T1StaircasePoint 1 false 1
    (BoundaryFootprintVertices (DiamondTile k) ∩ BoundaryFootprintVertices (TileTranslation
        (DiamondTile (k - (1 : ℕ))) ⟨(↑k : ℤ), (1 : ℤ) - (↑k : ℤ)⟩) = {v : GaussianInt | ∃ j ≤ (2
        : ℕ) * (k - (1 : ℕ)), v = P5157T1StaircasePoint (1 : GaussianInt) false (1 : ℤ) j}) →
        (BoundaryFootprintVertices Z ∩ BoundaryFootprintVertices D =
        {v | ∃ j ≤ n, v = J (p j)})) := by
  classical
  intro k D E Z J hVerticesInter n p sourceV
  rw [hVerticesInter, Set.inter_comm, sourceV]
  simp only [n]
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨p j, ⟨j, hj, by simp [p]⟩, rfl⟩

private theorem hEdgesExact :
    ∀ (k : Nat),
    let D : ProtoTile := DiamondTile k
    let E : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), 1 - (k : Int)⟩
    let Z : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), (k : Int) + 1⟩
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    let JE : Finset GaussianInt → Finset GaussianInt := fun e => e.image J
    (BoundaryFootprintEdges Z ∩ BoundaryFootprintEdges D = JE '' (BoundaryFootprintEdges E ∩
        BoundaryFootprintEdges D)) → (
    let n : Nat := 2 * (k - 1)
    let p : Nat → GaussianInt := P5157T1StaircasePoint 1 false 1
    (BoundaryFootprintEdges (DiamondTile k) ∩ BoundaryFootprintEdges (TileTranslation
        (DiamondTile (k - (1 : ℕ))) ⟨(↑k : ℤ), (1 : ℤ) - (↑k : ℤ)⟩) = {e : Finset GaussianInt | ∃
        j < (2 : ℕ) * (k - (1 : ℕ)), e =
        {P5157T1StaircasePoint (1 : GaussianInt) false (1 : ℤ) j,
        P5157T1StaircasePoint (1 : GaussianInt) false (1 : ℤ) (j + (1 : ℕ))}}) →
        (BoundaryFootprintEdges Z ∩ BoundaryFootprintEdges D =
        {e | ∃ j < n, e = {J (p j), J (p (j + 1))}})) := by
  classical
  intro k D E Z J JE hEdgesInter n p sourceE
  rw [hEdgesInter, Set.inter_comm, sourceE]
  ext e
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨j, hj, ?_⟩
    simpa only [p] using (show
      JE {P5157T1StaircasePoint 1 false 1 j,
        P5157T1StaircasePoint 1 false 1 (j + 1)} =
      {J (P5157T1StaircasePoint 1 false 1 j),
        J (P5157T1StaircasePoint 1 false 1 (j + 1))} by
        simp [JE, Finset.image_insert, Finset.image_singleton])
  · rintro ⟨j, hj, rfl⟩
    refine ⟨{p j, p (j + 1)}, ⟨j, hj, rfl⟩, ?_⟩
    simp [JE, p, Finset.image_insert, Finset.image_singleton]

private theorem lverts :
    ∀ (k : Nat),
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    let n : Nat := 2 * (k - 1)
    let p : Nat → GaussianInt := P5157T1StaircasePoint 1 false 1
    let q : Nat → GaussianInt := fun j => J (p j)
    let l : List GaussianInt := List.ofFn (fun i : Fin (n + 1) => q i)
    (l.toFinset : Set GaussianInt) =
      {v | ∃ j ≤ n, v = q j} := by
  classical
  intro k J n p q l
  ext v
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset, l,
    List.mem_ofFn]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j, by omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, by omega⟩, rfl⟩

end PredecessorPathProof

namespace PredecessorPathDetails

private theorem domain_sym :
    ∀ (m : ℕ),
      ∀ (z : GaussianInt),
        z ∈ DiamondCellDomain m ↔
          { re := z.re, im := (2 : ℤ) * (↑m : ℤ) - (1 : ℤ) - z.im } ∈ DiamondCellDomain m := by
  classical
  intro m z
  rw [(P4194T1DiamondCellRows m z).1,
    (P4194T1DiamondCellRows m ⟨z.re, 2 * (m : Int) - 1 - z.im⟩).1]
  simp only
  omega

private theorem dom_sym :
    ∀ (k : Nat), ((1 : ℕ) < k) → (
    let Jc : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - 3 - z.im⟩
    (∀ (m : Nat), ∀ (z : GaussianInt), z ∈ DiamondCellDomain m ↔ ⟨z.re, 2 * (m : Int) - 1 - z.im⟩
        ∈ DiamondCellDomain m) → (∀ (z : GaussianInt), z ∈ DiamondCellDomain (k - (1 : ℕ)) ↔ Jc z
        ∈ DiamondCellDomain (k - (1 : ℕ)))) := by
  classical
  intro k hk Jc domain_sym z
  have hcast : ((k - 1 : Nat) : Int) = (k : Int) - 1 := by omega
  have hcoord : 2 * ((k - 1 : Nat) : Int) - 1 = 2 * (k : Int) - 3 := by
    rw [hcast]
    ring
  simpa [Jc, hcoord] using domain_sym (k - 1) z

private theorem neD :
    ∀ (k : Nat), ((1 : ℕ) < k) → (
    let D : ProtoTile := DiamondTile k
    D.cells.Nonempty) := by
  classical
  intro k hk D
  change (DiamondTile k).cells.Nonempty
  refine ⟨0, ?_⟩
  exact (P4194T1DiamondCellRows k 0).1.mpr (by norm_num; omega)

private theorem nePrev :
    ∀ (k : Nat), ((1 : ℕ) < k) → ((DiamondTile (k - 1)).cells.Nonempty) := by
  classical
  intro k hk
  refine ⟨0, ?_⟩
  exact (P4194T1DiamondCellRows (k - 1) 0).1.mpr (by norm_num; omega)

private theorem neE :
    ∀ (k : Nat),
    let E : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), 1 - (k : Int)⟩
    ((DiamondTile (k - 1)).cells.Nonempty) → (E.cells.Nonempty) := by
  classical
  intro k E nePrev
  change (TileTranslation (DiamondTile (k - 1))
    ⟨(k : Int), 1 - (k : Int)⟩).cells.Nonempty
  rw [(TileTranslationFormulas _ _).1]
  exact nePrev.image _

private theorem hG :
    ∀ (k : Nat),
    let Jc : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - 3 - z.im⟩
    (∀ (z : GaussianInt), z ∈ DiamondCellDomain (k - 1) ↔ Jc z ∈ DiamondCellDomain (k - 1)) → ((∀
        (z : GaussianInt), Jc (Jc z) = z) → ((DiamondCellDomain (k - 1)).image Jc =
        DiamondCellDomain (k - 1))) := by
  classical
  intro k Jc dom_sym g_invol
  ext z
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (dom_sym w).mp hw
  · intro hz
    exact ⟨Jc z, (dom_sym z).mp hz, g_invol z⟩

private theorem hRcells :
    ∀ (k : Nat),
    let E : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), 1 - (k : Int)⟩
    let R : ProtoTile := TileTranslation (TileReflection E) ⟨0, 2 * (k : Int)⟩
    R.cells = (DiamondCellDomain (k - 1)).image
      (fun a => ⟨a.re + (k : Int), 3 * (k : Int) - 2 - a.im⟩) := by
  classical
  intro k E R
  simp only [R, E, TileTranslation, TileReflection, DiamondTile,
    Finset.image_image, GaussianTranslation, GaussianReflection]
  apply Finset.image_congr
  intro a ha
  apply Zsqrtd.ext <;> simp [GaussianTranslation]; ring

private theorem hZcells :
    ∀ (k : Nat),
    let Z : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), (k : Int) + 1⟩
    Z.cells = (DiamondCellDomain (k - 1)).image
      (fun a => ⟨a.re + (k : Int), a.im + (k : Int) + 1⟩) := by
  classical
  intro k Z
  change (DiamondCellDomain (k - 1)).image
    (GaussianTranslation ⟨(k : Int), (k : Int) + 1⟩) = _
  apply Finset.image_congr
  intro a ha
  apply Zsqrtd.ext <;> simp [GaussianTranslation]; ring

private theorem hmaps :
    ∀ (k : Nat),
    let Jc : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - 3 - z.im⟩
    (fun a : GaussianInt =>
      (⟨a.re + (k : Int), 3 * (k : Int) - 2 - a.im⟩ : GaussianInt)) =
      (fun a : GaussianInt =>
        (⟨a.re + (k : Int), (Jc a).im + (k : Int) + 1⟩ : GaussianInt)) := by
  classical
  intro k Jc
  funext a
  apply Zsqrtd.ext <;> simp [Jc]; ring

private theorem cellsRZ :
    ∀ (k : Nat),
    let E : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), 1 - (k : Int)⟩
    let Z : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), (k : Int) + 1⟩
    let R : ProtoTile := TileTranslation (TileReflection E) ⟨0, 2 * (k : Int)⟩
    let Jc : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - 3 - z.im⟩
    ((DiamondCellDomain (k - 1)).image Jc = DiamondCellDomain (k - 1)) → ((R.cells =
        (DiamondCellDomain (k - 1)).image (fun a => ⟨a.re + (k : Int), 3 * (k : Int) - 2 -
        a.im⟩)) → ((Z.cells = (DiamondCellDomain (k - 1)).image (fun a => ⟨a.re + (k : Int), a.im
        + (k : Int) + 1⟩)) → (((fun a : GaussianInt => (⟨a.re + (k : Int), 3 * (k : Int) - 2 -
        a.im⟩ : GaussianInt)) = (fun a : GaussianInt => (⟨a.re + (k : Int), (Jc a).im + (k : Int)
        + 1⟩ : GaussianInt))) → (R.cells = Z.cells)))) := by
  classical
  intro k E Z R Jc hG hRcells hZcells hmaps
  rw [hRcells, hZcells, hmaps]
  simpa only [Finset.image_image, Function.comp_def] using
    congrArg (Finset.image (fun a : GaussianInt =>
      (⟨a.re + (k : Int), a.im + (k : Int) + 1⟩ : GaussianInt))) hG

private theorem k_inj :
    ∀ (k : Nat),
    let K : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - 1 - z.im⟩
    (∀ (z : GaussianInt), K (K z) = z) → (Function.Injective K) := by
  classical
  intro k K k_invol a b hab
  have := congrArg K hab
  simpa only [k_invol] using this

private theorem hReflectDisj :
    ∀ (k : Nat),
    let D : ProtoTile := DiamondTile k
    let E : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), 1 - (k : Int)⟩
    let R : ProtoTile := TileTranslation (TileReflection E) ⟨0, 2 * (k : Int)⟩
    let S : ProtoTile := TileTranslation (TileReflection D) ⟨0, 2 * (k : Int)⟩
    let K : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - 1 - z.im⟩
    (Function.Injective K) → ((Disjoint D.cells E.cells) → (((TileTranslation (TileReflection
        (TileTranslation (DiamondTile (k - (1 : ℕ))) ⟨(↑k : ℤ), (1 : ℤ) - (↑k : ℤ)⟩)) ⟨(0 : ℤ),
        (2 : ℤ) * (↑k : ℤ)⟩).cells = Finset.image (fun (z : GaussianInt) => ⟨z.re, (2 : ℤ) * (↑k
        : ℤ) - (1 : ℤ) - z.im⟩) (TileTranslation (DiamondTile (k - (1 : ℕ))) ⟨(↑k : ℤ), (1 : ℤ) -
        (↑k : ℤ)⟩).cells) → ((S.cells = D.cells.image K) → (Disjoint S.cells R.cells)))) := by
  classical
  intro k D E R S K k_inj hSourceDisj hRimage hSimage
  rw [hSimage, hRimage]
  apply Finset.disjoint_left.mpr
  intro z hzS hzR
  rcases Finset.mem_image.mp hzS with ⟨a, ha, haz⟩
  rcases Finset.mem_image.mp hzR with ⟨b, hb, hbz⟩
  have hab : a = b := k_inj (haz.trans hbz.symm)
  subst b
  exact (Finset.disjoint_left.mp hSourceDisj) ha hb

private theorem neR :
    ∀ (k : Nat),
    let E : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), 1 - (k : Int)⟩
    let R : ProtoTile := TileTranslation (TileReflection E) ⟨0, 2 * (k : Int)⟩
    (E.cells.Nonempty) → (((TileTranslation (TileReflection (TileTranslation (DiamondTile (k - (1
        : ℕ))) ⟨(↑k : ℤ), (1 : ℤ) - (↑k : ℤ)⟩)) ⟨(0 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩).cells =
        Finset.image (fun (z : GaussianInt) => ⟨z.re, (2 : ℤ) * (↑k : ℤ) - (1 : ℤ) - z.im⟩)
        (TileTranslation (DiamondTile (k - (1 : ℕ))) ⟨(↑k : ℤ), (1 : ℤ) - (↑k : ℤ)⟩).cells) →
        (R.cells.Nonempty)) := by
  classical
  intro k E R neE hRimage
  let K : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - 1 - z.im⟩
  rw [hRimage]
  exact neE.image K

private theorem neZ :
    ∀ (k : Nat),
    let E : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), 1 - (k : Int)⟩
    let Z : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), (k : Int) + 1⟩
    let R : ProtoTile := TileTranslation (TileReflection E) ⟨0, 2 * (k : Int)⟩
    (R.cells = Z.cells) → ((R.cells.Nonempty) → (Z.cells.Nonempty)) := by
  classical
  intro k E Z R cellsRZ neR
  rw [← cellsRZ]
  exact neR

private theorem hTargetDisj :
    ∀ (k : Nat),
    let D : ProtoTile := DiamondTile k
    let E : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), 1 - (k : Int)⟩
    let Z : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), (k : Int) + 1⟩
    let R : ProtoTile := TileTranslation (TileReflection E) ⟨0, 2 * (k : Int)⟩
    let S : ProtoTile := TileTranslation (TileReflection D) ⟨0, 2 * (k : Int)⟩
    (R.cells = Z.cells) → (((TileTranslation (TileReflection (DiamondTile k)) ⟨(0 : ℤ), (2 : ℤ) *
        (↑k : ℤ)⟩).cells = (DiamondTile k).cells) → ((Disjoint S.cells R.cells) → (Disjoint
        Z.cells D.cells))) := by
  classical
  intro k D E Z R S cellsRZ hScells hReflectDisj
  rw [← cellsRZ, ← hScells]
  exact hReflectDisj.symm

private theorem hJinj :
    ∀ (k : Nat),
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    Function.Injective J := by
  classical
  intro k J a b hab
  have hre := congrArg Zsqrtd.re hab
  have him := congrArg Zsqrtd.im hab
  simp [J] at hre him
  apply Zsqrtd.ext <;> assumption

private theorem hRvertices :
    ∀ (k : Nat),
    let E : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), 1 - (k : Int)⟩
    let R : ProtoTile := TileTranslation (TileReflection E) ⟨0, 2 * (k : Int)⟩
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    BoundaryFootprintVertices R = J '' BoundaryFootprintVertices E := by
  classical
  intro k E R J
  rcases TileReflectionFormulas E with ⟨_, _, _, _, _, _, _, hrv, hre⟩
  rcases TileTranslationFormulas (TileReflection E) ⟨0, 2 * (k : Int)⟩ with
    ⟨_, _, _, _, _, _, _, htv, hte⟩
  rw [htv, hrv, Set.image_image]
  congr 1
  funext z
  apply Zsqrtd.ext <;> simp [J, GaussianTranslation, GaussianReflection]; ring

private theorem hSvertices :
    ∀ (k : Nat),
    let D : ProtoTile := DiamondTile k
    let S : ProtoTile := TileTranslation (TileReflection D) ⟨0, 2 * (k : Int)⟩
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    BoundaryFootprintVertices S = J '' BoundaryFootprintVertices D := by
  classical
  intro k D S J
  rcases TileReflectionFormulas D with ⟨_, _, _, _, _, _, _, hrv, hre⟩
  rcases TileTranslationFormulas (TileReflection D) ⟨0, 2 * (k : Int)⟩ with
    ⟨_, _, _, _, _, _, _, htv, hte⟩
  rw [htv, hrv, Set.image_image]
  congr 1
  funext z
  apply Zsqrtd.ext <;> simp [J, GaussianTranslation, GaussianReflection]; ring

private theorem hBoundaryE :
    ∀ (T : ProtoTile), ∀ (U : ProtoTile), T.cells = U.cells → BoundaryFootprintEdges T =
        BoundaryFootprintEdges U := by
  classical
  intro T U hc
  unfold BoundaryFootprintEdges
  rw [hc]

private theorem hBoundaryV :
    (∀ (T : ProtoTile), ∀ (U : ProtoTile), (T.cells = U.cells) → (BoundaryFootprintEdges T =
        BoundaryFootprintEdges U)) → (∀ (T : ProtoTile), ∀ (U : ProtoTile), T.cells = U.cells →
    Finset.Nonempty T.cells → Finset.Nonempty U.cells → BoundaryFootprintVertices T =
        BoundaryFootprintVertices U) := by
  classical
  intro hBoundaryE T U hc ht hu
  unfold BoundaryFootprintVertices
  rw [ite_eq_left ht, ite_eq_left hu]
  rw [hBoundaryE T U hc]

private theorem hZedges :
    ∀ (k : Nat),
    let E : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), 1 - (k : Int)⟩
    let Z : ProtoTile := TileTranslation (DiamondTile (k - 1))
      ⟨(k : Int), (k : Int) + 1⟩
    let R : ProtoTile := TileTranslation (TileReflection E) ⟨0, 2 * (k : Int)⟩
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    (R.cells = Z.cells) → ((have E := TileTranslation (DiamondTile (k - (1 : ℕ))) ⟨(↑k : ℤ), (1 :
        ℤ) - (↑k : ℤ)⟩; have R := TileTranslation (TileReflection E) ⟨(0 : ℤ), (2 : ℤ) * (↑k :
        ℤ)⟩; have J := fun (z : GaussianInt) => ⟨z.re, (2 : ℤ) * (↑k : ℤ) - z.im⟩;
        BoundaryFootprintEdges R = (fun (e : Finset GaussianInt) => Finset.image J e) ''
        BoundaryFootprintEdges E) → ((∀ (T : ProtoTile), ∀ (U : ProtoTile), (T.cells = U.cells) →
        (BoundaryFootprintEdges T = BoundaryFootprintEdges U)) → (BoundaryFootprintEdges Z =
      (fun e : Finset GaussianInt => e.image J) '' BoundaryFootprintEdges E))) := by
  classical
  intro k E Z R J cellsRZ hRedges hBoundaryE
  rw [← hBoundaryE R Z cellsRZ, hRedges]

private theorem hDvertices :
    ∀ (k : Nat),
    let D : ProtoTile := DiamondTile k
    let S : ProtoTile := TileTranslation (TileReflection D) ⟨0, 2 * (k : Int)⟩
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    (D.cells.Nonempty) → (((TileTranslation (TileReflection (DiamondTile k)) ⟨(0 : ℤ), (2 : ℤ) *
        (↑k : ℤ)⟩).cells = (DiamondTile k).cells) → ((BoundaryFootprintVertices S = J ''
        BoundaryFootprintVertices D) → ((∀ (T : ProtoTile), ∀ (U : ProtoTile), (T.cells =
        U.cells) → ((T.cells.Nonempty) → ((U.cells.Nonempty) → (BoundaryFootprintVertices T =
        BoundaryFootprintVertices U)))) → (BoundaryFootprintVertices D = J ''
        BoundaryFootprintVertices D)))) := by
  classical
  intro k D S J neD hScells hSvertices hBoundaryV
  calc
    BoundaryFootprintVertices D = BoundaryFootprintVertices S :=
      (hBoundaryV S D hScells (by rw [hScells]; exact neD) neD).symm
    _ = J '' BoundaryFootprintVertices D := hSvertices

private theorem hDedges :
    ∀ (k : Nat),
    let D : ProtoTile := DiamondTile k
    let S : ProtoTile := TileTranslation (TileReflection D) ⟨0, 2 * (k : Int)⟩
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    ((TileTranslation (TileReflection (DiamondTile k)) ⟨(0 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩).cells =
        (DiamondTile k).cells) → ((BoundaryFootprintEdges S =
      (fun e : Finset GaussianInt => e.image J) '' BoundaryFootprintEdges D)) → ((∀ (T :
          ProtoTile), ∀
        (U : ProtoTile), (T.cells = U.cells) → (BoundaryFootprintEdges T = BoundaryFootprintEdges
        U)) → (BoundaryFootprintEdges D =
      (fun e : Finset GaussianInt => e.image J) '' BoundaryFootprintEdges D)) := by
  classical
  intro k D S J hScells hSedges hBoundaryE
  calc
    BoundaryFootprintEdges D = BoundaryFootprintEdges S :=
      (hBoundaryE S D hScells).symm
    _ = (fun e : Finset GaussianInt => e.image J) '' BoundaryFootprintEdges D := hSedges

private theorem qinj :
    ∀ (k : Nat),
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    (Function.Injective J) → (
    let p : Nat → GaussianInt := P5157T1StaircasePoint 1 false 1
    (Function.Injective p) → (
    let q : Nat → GaussianInt := fun j => J (p j)
    Function.Injective q)) := by
  classical
  intro k J hJinj p pinj q a b hab
  apply pinj
  exact hJinj hab

private theorem pstep :
    let p : Nat → GaussianInt := P5157T1StaircasePoint 1 false 1
    ∀ (j : ℕ),
      p (j + (1 : ℕ)) = p j + (1 : GaussianInt) ∨ p (j + (1 : ℕ)) = p j + ⟨(0 : ℤ), (1 : ℤ)⟩ := by
  classical
  intro p j
  simp [p, P5157T1StaircasePoint, Zsqrtd.ext_iff]; omega

private theorem qstep :
    ∀ (k : Nat),
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    let p : Nat → GaussianInt := P5157T1StaircasePoint 1 false 1
    let q : Nat → GaussianInt := fun j => J (p j)
    (∀ (j : Nat), p (j + 1) = p j + 1 ∨ p (j + 1) = p j + ⟨0, 1⟩) → ((∀ (z : GaussianInt), J (z +
        1) = J z + 1) → ((∀ (z : GaussianInt), J (z + ⟨0, 1⟩) = J z - ⟨0, 1⟩) → (∀ (j : ℕ), q (j
        + (1 : ℕ)) = q j + (1 : GaussianInt) ∨ q (j + (1 : ℕ)) = q j - { re := (0 : ℤ), im := (1
        : ℤ) }))) := by
  classical
  intro k J p q pstep Jright Jup j
  rcases pstep j with h | h
  · left
    dsimp [q]
    rw [h, Jright]
  · right
    dsimp [q]
    rw [h, Jup]

private theorem lNodup :
    ∀ (k : Nat),
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    let n : Nat := 2 * (k - 1)
    let p : Nat → GaussianInt := P5157T1StaircasePoint 1 false 1
    let q : Nat → GaussianInt := fun j => J (p j)
    (Function.Injective q) → (
    let l : List GaussianInt := List.ofFn (fun i : Fin (n + 1) => q i)
    l.Nodup) := by
  classical
  intro k J n p q qinj l
  apply List.nodup_ofFn.mpr
  intro i j hij
  exact Fin.ext (qinj hij)

private theorem lchain :
    ∀ (k : Nat),
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    let n : Nat := 2 * (k - 1)
    let p : Nat → GaussianInt := P5157T1StaircasePoint 1 false 1
    let q : Nat → GaussianInt := fun j => J (p j)
    let l : List GaussianInt := List.ofFn (fun i : Fin (n + 1) => q i)
    l.IsChain (fun a b => ∃ j < n, a = q j ∧ b = q (j + 1)) := by
  classical
  intro k J n p q l
  apply List.isChain_ofFn.mpr
  intro j hj
  exact ⟨j, by omega, rfl, rfl⟩

private theorem qn :
    ∀ (k : Nat), ((1 : ℕ) < k) → (
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    let n : Nat := 2 * (k - 1)
    let p : Nat → GaussianInt := P5157T1StaircasePoint 1 false 1
    let q : Nat → GaussianInt := fun j => J (p j)
    q n = ⟨(k : Int), (k : Int) + 1⟩) := by
  classical
  intro k hk J n p q
  simp [q, p, J, P5157T1StaircasePoint, n]
  omega

private theorem lhead :
    ∀ (k : Nat),
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    let n : Nat := 2 * (k - 1)
    let p : Nat → GaussianInt := P5157T1StaircasePoint 1 false 1
    let q : Nat → GaussianInt := fun j => J (p j)
    let l : List GaussianInt := List.ofFn (fun i : Fin (n + 1) => q i)
    (q 0 = ⟨1, 2 * (k : Int)⟩) → (l.head? = some ⟨1, 2 * (k : Int)⟩) := by
  classical
  intro k J n p q l q0
  simp only [l, List.ofFn_succ, List.head?_cons]
  simpa using congrArg some q0

private theorem llast :
    ∀ (k : Nat),
    let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
    let n : Nat := 2 * (k - 1)
    let p : Nat → GaussianInt := P5157T1StaircasePoint 1 false 1
    let q : Nat → GaussianInt := fun j => J (p j)
    let l : List GaussianInt := List.ofFn (fun i : Fin (n + 1) => q i)
    (l.length = n + 1) → ((q n = ⟨(k : Int), (k : Int) + 1⟩) → (l.getLast? = some ⟨(k : Int), (k
        : Int) + 1⟩)) := by
  classical
  intro k J n p q l llength qn
  have hne : l ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [llength] at this
  rw [List.getLast?_eq_getLast_of_ne_nil hne, List.getLast_ofFn_succ]
  simp [q, qn]

end PredecessorPathDetails

theorem P5290T1PredecessorPath (k : Nat) (hk : 1 < k) :
    let D := DiamondTile k
    let Z := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), (k : Int) + 1⟩
    let y : GaussianInt := ⟨1, 2 * (k : Int)⟩
    Z.cells.Nonempty ∧ D.cells.Nonempty ∧ Disjoint Z.cells D.cells ∧
      SimpleGridPathBetween
        (BoundaryFootprintVertices Z ∩ BoundaryFootprintVertices D)
        (BoundaryFootprintEdges Z ∩ BoundaryFootprintEdges D)
        y ⟨(k : Int), (k : Int) + 1⟩ := by
-- BODY
  classical
  dsimp only
  let D : ProtoTile := DiamondTile k
  let E : ProtoTile := TileTranslation (DiamondTile (k - 1))
    ⟨(k : Int), 1 - (k : Int)⟩
  let Z : ProtoTile := TileTranslation (DiamondTile (k - 1))
    ⟨(k : Int), (k : Int) + 1⟩
  let R : ProtoTile := TileTranslation (TileReflection E) ⟨0, 2 * (k : Int)⟩
  let S : ProtoTile := TileTranslation (TileReflection D) ⟨0, 2 * (k : Int)⟩
  let J : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - z.im⟩
  let K : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - 1 - z.im⟩
  let Jc : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (k : Int) - 3 - z.im⟩
  have domain_sym (m : Nat) (z : GaussianInt) :
      z ∈ DiamondCellDomain m ↔
        ⟨z.re, 2 * (m : Int) - 1 - z.im⟩ ∈ DiamondCellDomain m :=
            PredecessorPathDetails.domain_sym m z
  have dom_sym (z : GaussianInt) :
      z ∈ DiamondCellDomain (k - 1) ↔ Jc z ∈ DiamondCellDomain (k - 1) :=
          PredecessorPathDetails.dom_sym k hk domain_sym z
  have neD : D.cells.Nonempty := PredecessorPathDetails.neD k hk
  have nePrev : (DiamondTile (k - 1)).cells.Nonempty := PredecessorPathDetails.nePrev k hk
  have neE : E.cells.Nonempty := PredecessorPathDetails.neE k nePrev
  have g_invol (z : GaussianInt) : Jc (Jc z) = z := by
    apply Zsqrtd.ext <;> simp [Jc]
  have hG : (DiamondCellDomain (k - 1)).image Jc = DiamondCellDomain (k - 1) :=
      PredecessorPathDetails.hG k dom_sym g_invol
  have hRcells : R.cells = (DiamondCellDomain (k - 1)).image
      (fun a => ⟨a.re + (k : Int), 3 * (k : Int) - 2 - a.im⟩) := PredecessorPathDetails.hRcells k
  have hZcells : Z.cells = (DiamondCellDomain (k - 1)).image
      (fun a => ⟨a.re + (k : Int), a.im + (k : Int) + 1⟩) := PredecessorPathDetails.hZcells k
  have hmaps : (fun a : GaussianInt =>
      (⟨a.re + (k : Int), 3 * (k : Int) - 2 - a.im⟩ : GaussianInt)) =
      (fun a : GaussianInt =>
        (⟨a.re + (k : Int), (Jc a).im + (k : Int) + 1⟩ : GaussianInt)) :=
            PredecessorPathDetails.hmaps k
  have cellsRZ : R.cells = Z.cells := PredecessorPathDetails.cellsRZ k hG hRcells hZcells hmaps
  have k_invol (z : GaussianInt) : K (K z) = z := by
    apply Zsqrtd.ext <;> simp [K]
  have hDsym := PredecessorPathProof.hDsym k domain_sym k_invol
  have hScells := PredecessorPathProof.hScells k hDsym
  have k_inj : Function.Injective K := PredecessorPathDetails.k_inj k k_invol
  have source := P5157T1DiamondStaircaseIntersections k hk
  dsimp only at source
  have hSourceDisj : Disjoint D.cells E.cells := source.1.1
  have hRimage := PredecessorPathProof.hRimage k hRcells
  have hSimage : S.cells = D.cells.image K := by
    rw [hScells, hDsym]
  have hReflectDisj : Disjoint S.cells R.cells := PredecessorPathDetails.hReflectDisj k k_inj
      hSourceDisj hRimage hSimage
  have neR : R.cells.Nonempty := PredecessorPathDetails.neR k neE hRimage
  have neZ : Z.cells.Nonempty := PredecessorPathDetails.neZ k cellsRZ neR
  have hTargetDisj : Disjoint Z.cells D.cells := PredecessorPathDetails.hTargetDisj k cellsRZ
      hScells hReflectDisj
  have hJinj : Function.Injective J := PredecessorPathDetails.hJinj k
  have hRvertices : BoundaryFootprintVertices R = J '' BoundaryFootprintVertices E :=
      PredecessorPathDetails.hRvertices k
  have hRedges := PredecessorPathProof.hRedges k
  have hSvertices : BoundaryFootprintVertices S = J '' BoundaryFootprintVertices D :=
      PredecessorPathDetails.hSvertices k
  have hSedges := PredecessorPathProof.hSedges k
  have hBoundaryE (T U : ProtoTile) (hc : T.cells = U.cells) :
      BoundaryFootprintEdges T = BoundaryFootprintEdges U := PredecessorPathDetails.hBoundaryE T
          U hc
  have hBoundaryV (T U : ProtoTile) (hc : T.cells = U.cells)
      (ht : T.cells.Nonempty) (hu : U.cells.Nonempty) :
      BoundaryFootprintVertices T = BoundaryFootprintVertices U :=
          PredecessorPathDetails.hBoundaryV hBoundaryE T U hc ht hu
  have hZvertices : BoundaryFootprintVertices Z = J '' BoundaryFootprintVertices E := by
    rw [← hBoundaryV R Z cellsRZ neR neZ, hRvertices]
  have hZedges : BoundaryFootprintEdges Z =
      (fun e : Finset GaussianInt => e.image J) '' BoundaryFootprintEdges E :=
          PredecessorPathDetails.hZedges k cellsRZ hRedges hBoundaryE
  have hDvertices : BoundaryFootprintVertices D = J '' BoundaryFootprintVertices D :=
      PredecessorPathDetails.hDvertices k neD hScells hSvertices hBoundaryV
  have hDedges : BoundaryFootprintEdges D =
      (fun e : Finset GaussianInt => e.image J) '' BoundaryFootprintEdges D :=
          PredecessorPathDetails.hDedges k hScells hSedges hBoundaryE
  let JE : Finset GaussianInt → Finset GaussianInt := fun e => e.image J
  have hJEinj := PredecessorPathProof.hJEinj k hJinj
  have hVerticesInter := PredecessorPathProof.hVerticesInter k hJinj hZvertices hDvertices
  have hEdgesInter := PredecessorPathProof.hEdgesInter k hZedges hDedges hJEinj
  let n : Nat := 2 * (k - 1)
  let p : Nat → GaussianInt := P5157T1StaircasePoint 1 false 1
  have sourceV := source.1.2.1
  have sourceE := source.1.2.2
  have hVerticesExact := PredecessorPathProof.hVerticesExact k hVerticesInter sourceV
  have hEdgesExact := PredecessorPathProof.hEdgesExact k
            hEdgesInter sourceE
  have hn : 0 < n := by dsimp [n]; omega
  have alt := P5157T1AlternatingStaircase 1 false 1 (Or.inl rfl) n hn
  dsimp only at alt
  have pinj : Function.Injective p := by
    simpa [p] using alt.1
  let q : Nat → GaussianInt := fun j => J (p j)
  have qinj : Function.Injective q := PredecessorPathDetails.qinj k hJinj pinj
  have pstep (j : Nat) : p (j + 1) = p j + 1 ∨
      p (j + 1) = p j + ⟨0, 1⟩ := PredecessorPathDetails.pstep j
  have Jright (z : GaussianInt) : J (z + 1) = J z + 1 := by
    apply Zsqrtd.ext <;> simp [J]
  have Jup (z : GaussianInt) : J (z + ⟨0, 1⟩) = J z - ⟨0, 1⟩ := by
    apply Zsqrtd.ext <;> simp [J]; ring
  have qstep (j : Nat) : q (j + 1) = q j + 1 ∨
      q (j + 1) = q j - ⟨0, 1⟩ := PredecessorPathDetails.qstep k pstep Jright Jup j
  let l : List GaussianInt := List.ofFn (fun i : Fin (n + 1) => q i)
  have lNodup : l.Nodup := PredecessorPathDetails.lNodup k qinj
  have llength : l.length = n + 1 := by simp [l]
  have lchain : l.IsChain (fun a b => ∃ j < n, a = q j ∧ b = q (j + 1)) :=
      PredecessorPathDetails.lchain k
  have consecutive (a b : GaussianInt) (l₁ l₂ : List GaussianInt)
      (heq : l = l₁ ++ a :: b :: l₂) :
      ∃ j < n, a = q j ∧ b = q (j + 1) :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp lchain heq
  have q0 : q 0 = ⟨1, 2 * (k : Int)⟩ := by
    simp [q, p, J, P5157T1StaircasePoint]
  have qn : q n = ⟨(k : Int), (k : Int) + 1⟩ := PredecessorPathDetails.qn k hk
  have lhead : l.head? = some ⟨1, 2 * (k : Int)⟩ := PredecessorPathDetails.lhead k q0
  have llast : l.getLast? = some ⟨(k : Int), (k : Int) + 1⟩ := PredecessorPathDetails.llast k
      llength qn
  have lverts := PredecessorPathProof.lverts k
  refine ⟨neZ, neD, hTargetDisj, ?_⟩
  refine ⟨l, lNodup, ?_, lhead, llast, ?_, ?_, ?_⟩
  · rw [llength]
    omega
  · rw [hVerticesExact]
    simpa [q, l] using lverts.symm
  · intro a b l₁ l₂ heq
    obtain ⟨j, hj, rfl, rfl⟩ := consecutive a b l₁ l₂ heq
    rcases qstep j with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
  · intro e
    rw [hEdgesExact]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hjl : j < l.length := by rw [llength]; omega
      have hjl' : j + 1 < l.length := by rw [llength]; omega
      refine ⟨q j, q (j + 1), l.take j, l.drop (j + 2), ?_, rfl⟩
      have hd := List.getElem_cons_drop hjl
      have hd' := List.getElem_cons_drop hjl'
      have heq : l = l.take j ++ l[j] :: l[j + 1] :: l.drop (j + 2) := by
        rw [show j + 2 = j + 1 + 1 by omega, hd', hd, List.take_append_drop]
      simpa only [l, List.getElem_ofFn] using heq
    · rintro ⟨a, b, l₁, l₂, heq, rfl⟩
      obtain ⟨j, hj, rfl, rfl⟩ := consecutive a b l₁ l₂ heq
      exact ⟨j, hj, rfl⟩

end ApollonianSuperharmonic

end
