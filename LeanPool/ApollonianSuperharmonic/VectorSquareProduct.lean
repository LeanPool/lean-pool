/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandSuccessorClassification
public import LeanPool.ApollonianSuperharmonic.BandVectors
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: VectorSquareProduct]

/-!
# VectorSquareProduct

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace VectorSquareProof

private theorem ii_sq :
    let ii : GaussianInt := ⟨0, 1⟩
    ii^2 = -1 := by
  classical
  intro ii
  decide +kernel

private theorem ii_cube :
    let ii : GaussianInt := ⟨0, 1⟩
    ii^3 = -ii := by
  classical
  intro ii
  decide +kernel

private theorem system :
    RecursiveVectorSystem BandVectors := by
  classical
  simpa [BandVectors] using (Classical.choose_spec RecursiveVectorsExistUnique).1

private theorem reverse :
    let ii : GaussianInt := ⟨0, 1⟩
    (ii^2 = -1) → (
    let v := BandVectors.1
    let a := BandVectors.2
    let E (C D : CircleCoordinates) : Prop :=
      v C D ^ 2 = (D.1 : GaussianInt) * C.2 - (C.1 : GaussianInt) * D.2 ∧
        2 * v C D * a C D = C.2 + D.2
    (∀ (C : CircleCoordinates), ∀ (D : CircleCoordinates), PrimitiveVectorOrientation C D →
        BandVectors.1 D C = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 C D ∧ BandVectors.2 D C = -⟨(0 :
        ℤ), (1 : ℤ)⟩ * BandVectors.2 C D) → (∀ (C : CircleCoordinates), ∀ (D :
        CircleCoordinates), (PrimitiveVectorOrientation C D) → ((E C D) → (E D C)))) := by
  classical
  intro ii ii_sq v a E flipLaw C D ho h
  rcases flipLaw C D ho with ⟨hv, ha⟩
  change v D C = ii * v C D at hv
  change a D C = -ii * a C D at ha
  rcases h with ⟨hs, hp⟩
  constructor
  · rw [hv]
    calc
      (ii * v C D)^2 = -(v C D ^ 2) := by
        ring_nf; simp only [ii_sq]; ring
      _ = _ := by rw [hs]; ring
  · rw [hv, ha]
    calc
      2 * (ii * v C D) * (-ii * a C D) = 2 * v C D * a C D := by
        ring_nf; simp only [ii_sq]; ring
      _ = D.2 + C.2 := by rw [hp]; ring

private theorem rootValues :
    let ii : GaussianInt := ⟨0, 1⟩
    (ii^2 = -1) → (
    let v := BandVectors.1
    let a := BandVectors.2
    let B (z : GaussianInt) : Fin 4 → CircleCoordinates :=
      ![(1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ii), (0, 1), (0, -1)]
    (∀ (z : GaussianInt), have q := ![((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * z), ((1 :
        ℤ), (1 : GaussianInt) + (2 : GaussianInt) * z + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩),
        ((0 : ℤ), (1 : GaussianInt)), ((0 : ℤ), (-1 : GaussianInt))]; BandVectors.1 (q (3 : Fin
        (4 : ℕ))) (q (2 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1 (q (2 : Fin (4 : ℕ)))
        (q (1 : Fin (4 : ℕ))) = (-1 : GaussianInt) ∧ BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (3 :
        Fin (4 : ℕ))) = (1 : GaussianInt) ∧ BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 :
        ℕ))) = (1 : GaussianInt) ∧ BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) =
        (-1 : GaussianInt) - z - ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (3 :
        Fin (4 : ℕ))) = z + ⟨(0 : ℤ), (1 : ℤ)⟩) → ((∀ (C : CircleCoordinates), ∀ (D :
        CircleCoordinates), PrimitiveVectorOrientation C D → BandVectors.1 D C = ⟨(0 : ℤ), (1 :
        ℤ)⟩ * BandVectors.1 C D ∧ BandVectors.2 D C = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 C D) →
        (∀ (z : GaussianInt), (v (B z 3) (B z 2) = 0 ∧ a (B z 3) (B z 2) = 1) ∧
      (v (B z 2) (B z 1) = -1 ∧ a (B z 2) (B z 1) = -1-z-ii) ∧
      (v (B z 3) (B z 1) = -ii ∧ a (B z 3) (B z 1) = ii*z-1) ∧
      (v (B z 1) (B z 0) = 1+ii ∧ a (B z 1) (B z 0) = 1+z-ii*z) ∧
      (v (B z 2) (B z 0) = -1 ∧ a (B z 2) (B z 0) = -1-z) ∧
      (v (B z 3) (B z 0) = -ii ∧ a (B z 3) (B z 0) = ii*z)))) := by
  classical
  intro ii ii_sq v a B baseLaw flipLaw z
  have facts := baseLaw z
  change v (B z 3) (B z 2) = 0 ∧ v (B z 2) (B z 1) = -1 ∧
    v (B z 1) (B z 3) = 1 ∧ a (B z 3) (B z 2) = 1 ∧
    a (B z 2) (B z 1) = -1-z-ii ∧ a (B z 1) (B z 3) = z+ii at facts
  rcases facts with ⟨v32, v21, v13, a32, a21, a13⟩
  have f31 := flipLaw _ _ (PrimitiveVectorOrientation.base31 z)
  change v (B z 1) (B z 3) = ii * v (B z 3) (B z 1) ∧
    a (B z 1) (B z 3) = -ii * a (B z 3) (B z 1) at f31
  have v31 : v (B z 3) (B z 1) = -ii := by
    calc
      _ = -ii * (ii * v (B z 3) (B z 1)) := by
        ring_nf; simp only [ii_sq]; ring
      _ = -ii := by rw [← f31.1, v13]; ring
  have a31 : a (B z 3) (B z 1) = ii*z-1 := by
    calc
      _ = ii * (-ii * a (B z 3) (B z 1)) := by
        ring_nf; simp only [ii_sq]; ring
      _ = ii*z-1 := by
        rw [← f31.2, a13]
        ring_nf; simp only [ii_sq]; ring
  have laws := VectorRecursionLaws (B z) (SemiProperQuadruple.base z)
  have v10 : v (B z 1) (B z 0) = 1+ii := by
    have h : v (B z 1) (B z 0) = v (B z 1) (B z 3) - ii*v (B z 2) (B z 1) :=
      laws.2.2.1
    rw [h, v13, v21]
    ring
  have a10 : a (B z 1) (B z 0) = 1+z-ii*z := by
    have h : a (B z 1) (B z 0) = a (B z 1) (B z 3) + ii*a (B z 2) (B z 1) :=
      laws.2.2.2.1
    rw [h, a13, a21]
    ring_nf; simp only [ii_sq]; ring
  have shift : 1 + 2 * (z-ii) + 2*ii = 1+2*z := by ring
  have shifted := baseLaw (z-ii)
  change v (0,-1) (0,1) = 0 ∧ v (0,1) (1,1+2*(z-ii)+2*ii) = -1 ∧
    v (1,1+2*(z-ii)+2*ii) (0,-1) = 1 ∧ a (0,-1) (0,1) = 1 ∧
    a (0,1) (1,1+2*(z-ii)+2*ii) = -1-(z-ii)-ii ∧
    a (1,1+2*(z-ii)+2*ii) (0,-1) = z-ii+ii at shifted
  rw [shift] at shifted
  have v20 : v (B z 2) (B z 0) = -1 := shifted.2.1
  have a20 : a (B z 2) (B z 0) = -1-z := by
    have h : a (B z 2) (B z 0) = -1-(z-ii)-ii := shifted.2.2.2.2.1
    rw [h]
    ring
  have f30 := flipLaw _ _ (PrimitiveVectorOrientation.base31 (z-ii))
  change v (1,1+2*(z-ii)+2*ii) (0,-1) = ii*v (0,-1) (1,1+2*(z-ii)+2*ii) ∧
    a (1,1+2*(z-ii)+2*ii) (0,-1) = -ii*a (0,-1) (1,1+2*(z-ii)+2*ii) at f30
  rw [shift] at f30
  change v (B z 0) (B z 3) = ii*v (B z 3) (B z 0) ∧
    a (B z 0) (B z 3) = -ii*a (B z 3) (B z 0) at f30
  have v03 : v (B z 0) (B z 3) = 1 := shifted.2.2.1
  have a03 : a (B z 0) (B z 3) = z-ii+ii := shifted.2.2.2.2.2
  have v30 : v (B z 3) (B z 0) = -ii := by
    calc
      _ = -ii * (ii * v (B z 3) (B z 0)) := by
        ring_nf; simp only [ii_sq]; ring
      _ = -ii := by rw [← f30.1, v03]; ring
  have a30 : a (B z 3) (B z 0) = ii*z := by
    calc
      _ = ii * (-ii * a (B z 3) (B z 0)) := by
        ring_nf; simp only [ii_sq]; ring
      _ = ii*z := by rw [← f30.2, a03]; ring
  exact ⟨⟨v32, a32⟩, ⟨v21, a21⟩, ⟨v31, a31⟩, ⟨v10, a10⟩,
    ⟨v20, a20⟩, ⟨v30, a30⟩⟩

private theorem root :
    let ii : GaussianInt := ⟨0, 1⟩
    (ii^2 = -1) → (
    let v := BandVectors.1
    let a := BandVectors.2
    let E (C D : CircleCoordinates) : Prop :=
      v C D ^ 2 = (D.1 : GaussianInt) * C.2 - (C.1 : GaussianInt) * D.2 ∧
        2 * v C D * a C D = C.2 + D.2
    let B (z : GaussianInt) : Fin 4 → CircleCoordinates :=
      ![(1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ii), (0, 1), (0, -1)]
    (∀ (C : CircleCoordinates), ∀ (D : CircleCoordinates), (PrimitiveVectorOrientation C D) → ((E
        C D) → (E D C))) → ((∀ (z : GaussianInt), (v (B z 3) (B z 2) = 0 ∧ a (B z 3) (B z 2) = 1)
        ∧ (v (B z 2) (B z 1) = -1 ∧ a (B z 2) (B z 1) = -1-z-ii) ∧ (v (B z 3) (B z 1) = -ii ∧ a
        (B z 3) (B z 1) = ii*z-1) ∧ (v (B z 1) (B z 0) = 1+ii ∧ a (B z 1) (B z 0) = 1+z-ii*z) ∧
        (v (B z 2) (B z 0) = -1 ∧ a (B z 2) (B z 0) = -1-z) ∧ (v (B z 3) (B z 0) = -ii ∧ a (B z
        3) (B z 0) = ii*z)) → (∀ (z : GaussianInt), ∀ i j : Fin 4, i ≠ j → E (B z i) (B z j))))
        := by
  classical
  intro ii ii_sq v a E B reverse rootValues z
  rcases rootValues z with ⟨⟨v32,a32⟩,⟨v21,a21⟩,⟨v31,a31⟩,
    ⟨v10,a10⟩,⟨v20,a20⟩,⟨v30,a30⟩⟩
  have e32 : E (B z 3) (B z 2) := by
    dsimp only [E]; rw [v32,a32]; simp [B]
  have e21 : E (B z 2) (B z 1) := by
    dsimp only [E]; rw [v21,a21]
    constructor <;> simp [B]; ring_nf
  have e31 : E (B z 3) (B z 1) := by
    dsimp only [E]; rw [v31,a31]
    constructor <;> simp [B] <;> ring_nf <;> simp only [ii_sq]; ring
  have e10 : E (B z 1) (B z 0) := by
    dsimp only [E]; rw [v10,a10]
    constructor <;> simp [B] <;> ring_nf <;> simp only [ii_sq] <;> ring
  have e20 : E (B z 2) (B z 0) := by
    dsimp only [E]; rw [v20,a20]
    constructor <;> simp [B]; ring_nf
  have e30 : E (B z 3) (B z 0) := by
    dsimp only [E]; rw [v30,a30]
    constructor <;> simp [B] <;> ring_nf <;> simp only [ii_sq]; ring
  have e23 := reverse _ _ (PrimitiveVectorOrientation.base32 z) e32
  have e12 := reverse _ _ (PrimitiveVectorOrientation.base21 z) e21
  have e13 := reverse _ _ (PrimitiveVectorOrientation.base31 z) e31
  have e01 := reverse _ _ (PrimitiveVectorOrientation.base10 z) e10
  have shift : 1+2*(z-ii)+2*ii = 1+2*z := by ring
  have o20 : PrimitiveVectorOrientation (B z 2) (B z 0) := by
    have h := PrimitiveVectorOrientation.base21 (z-ii)
    change PrimitiveVectorOrientation (0,1) (1,1+2*(z-ii)+2*ii) at h
    rw [shift] at h
    exact h
  have o30 : PrimitiveVectorOrientation (B z 3) (B z 0) := by
    have h := PrimitiveVectorOrientation.base31 (z-ii)
    change PrimitiveVectorOrientation (0,-1) (1,1+2*(z-ii)+2*ii) at h
    rw [shift] at h
    exact h
  have e02 := reverse _ _ o20 e20
  have e03 := reverse _ _ o30 e30
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact e01
  · exact e02
  · exact e03
  · exact e10
  · exact (hij rfl).elim
  · exact e12
  · exact e13
  · exact e20
  · exact e21
  · exact (hij rfl).elim
  · exact e23
  · exact e30
  · exact e31
  · exact e32
  · exact (hij rfl).elim

private theorem rotateEdges :
    let v := BandVectors.1
    let a := BandVectors.2
    let E (C D : CircleCoordinates) : Prop :=
      v C D ^ 2 = (D.1 : GaussianInt) * C.2 - (C.1 : GaussianInt) * D.2 ∧
        2 * v C D * a C D = C.2 + D.2
    let R (p : Fin 4 → CircleCoordinates) : Fin 4 → CircleCoordinates :=
      ![p 0, p 2, p 3, p 1]
    ∀ (p : Fin 4 → CircleCoordinates), (∀ i j : Fin 4, i ≠ j → E (p i) (p j)) → (∀ i j : Fin 4, i
        ≠ j → E (R p i) (R p j)) := by
  classical
  intro v a E R p ih
  let f : Fin 4 → Fin 4 := ![0,2,3,1]
  have hf : Function.Injective f := by decide +kernel
  have he (k : Fin 4) : R p k = p (f k) := by fin_cases k <;> rfl
  intro i j hij
  rw [he i,he j]
  exact ih (f i) (f j) (fun h => hij (hf h))

private theorem assemble :
    let v := BandVectors.1
    let a := BandVectors.2
    let E (C D : CircleCoordinates) : Prop :=
      v C D ^ 2 = (D.1 : GaussianInt) * C.2 - (C.1 : GaussianInt) * D.2 ∧
        2 * v C D * a C D = C.2 + D.2
    let S (p : Fin 4 → CircleCoordinates) : Fin 4 → CircleCoordinates :=
      ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
          2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
        p 0, p 2, p 3]
    (∀ (C : CircleCoordinates), ∀ (D : CircleCoordinates), (PrimitiveVectorOrientation C D) → ((E
        C D) → (E D C))) → (∀ (p : Fin 4 → CircleCoordinates), (∀ i j : Fin 4, i ≠ j → E (p i) (p
        j)) → ((ProperBandQuadruple (S p)) → ((E (p 0) (S p 0)) → ((E (p 2) (S p 0)) → ((E (p 3)
        (S p 0)) → (∀ i j : Fin 4, i ≠ j → E (S p i) (S p j))))))) := by
  classical
  intro v a E S reverse p ih hs e10 e20 e30
  let f : Fin 3 → Fin 4 := ![0,2,3]
  have hf : Function.Injective f := by decide +kernel
  have he (k : Fin 3) : S p k.succ = p (f k) := by fin_cases k <;> rfl
  have child (k : Fin 3) : E (S p k.succ) (S p 0) := by
    fin_cases k
    · exact e10
    · exact e20
    · exact e30
  have flipped (k : Fin 3) : E (S p 0) (S p k.succ) :=
    reverse _ _ (PrimitiveVectorOrientation.parentChild hs k) (child k)
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ l => exact flipped l
  | succ k =>
      cases j using Fin.cases with
      | zero => exact child k
      | succ l =>
          rw [he k,he l]
          exact ih (f k) (f l) (fun h => hij (congrArg Fin.succ (hf h)))

private theorem properStep :
    let ii : GaussianInt := ⟨0, 1⟩
    (ii^2 = -1) → ((ii^3 = -ii) → (
    let v := BandVectors.1
    let a := BandVectors.2
    let E (C D : CircleCoordinates) : Prop :=
      v C D ^ 2 = (D.1 : GaussianInt) * C.2 - (C.1 : GaussianInt) * D.2 ∧
        2 * v C D * a C D = C.2 + D.2
    let S (p : Fin 4 → CircleCoordinates) : Fin 4 → CircleCoordinates :=
      ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
          2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
        p 0, p 2, p 3]
    (∀ (p : Fin 4 → CircleCoordinates), (∀ i j : Fin 4, i ≠ j → E (p i) (p j)) →
        ((ProperBandQuadruple (S p)) → ((E (p 0) (S p 0)) → ((E (p 2) (S p 0)) → ((E (p 3) (S p
        0)) → (∀ i j : Fin 4, i ≠ j → E (S p i) (S p j))))))) → (∀ (p : Fin 4 →
        CircleCoordinates), (ProperBandQuadruple p) → ((∀ i j : Fin 4, i ≠ j → E (p i) (p j)) →
        (∀ i j : Fin 4, i ≠ j → E (S p i) (S p j)))))) := by
  classical
  intro ii ii_sq ii_cube v a E S assemble p hp ih
  let R (p : Fin 4 → CircleCoordinates) : Fin 4 → CircleCoordinates :=
    ![p 0, p 2, p 3, p 1]
  have hs : ProperBandQuadruple (S p) := by
    rcases BandSuccessorClassification p hp.1 with bad | good
    · have nonneg := (SemiProperForestClassification p hp.1).1
      have h01 : (p 1).1 < (p 0).1 := hp.2 0
      have n1 := nonneg 1
      have n2 := nonneg 2
      have n3 := nonneg 3
      change 2*(p 0).1 + 2*(p 2).1 + 2*(p 3).1 - (p 1).1 = 1 at bad
      omega
    · exact good.1
  let x := v (p 0) (p 3)
  let y := v (p 2) (p 0)
  let t := v (p 3) (p 2)
  let alpha := a (p 0) (p 3)
  let beta := a (p 2) (p 0)
  let gamma := a (p 3) (p 2)
  rcases VectorRecursionLaws (S p) hs.1 with ⟨sumv,suma,new1v,new1a,_⟩
  change t+x+y = 0 at sumv
  change gamma+alpha+beta = 0 at suma
  change v (p 0) (S p 0) = x-ii*y at new1v
  change a (p 0) (S p 0) = alpha+ii*beta at new1a
  have tr : t = -x-y := by linear_combination sumv
  have gr : gamma = -alpha-beta := by linear_combination suma
  have pred := VectorRecursionLaws p hp.1
  have predV := pred.2.2.1
  have predA := pred.2.2.2.1
  change v (p 1) (p 0) = v (p 1) (p 3)-ii*v (p 2) (p 1) at predV
  change a (p 1) (p 0) = a (p 1) (p 3)+ii*a (p 2) (p 1) at predA
  have f14 := pred.2.2.2.2 hp 0
  have f12 := pred.2.2.2.2 hp 1
  have f13 := pred.2.2.2.2 hp 2
  change v (p 0) (p 1) = ii*v (p 1) (p 0) ∧
    a (p 0) (p 1) = -ii*a (p 1) (p 0) at f14
  change v (p 0) (p 2) = ii*v (p 2) (p 0) ∧
    a (p 0) (p 2) = -ii*a (p 2) (p 0) at f12
  change v (p 0) (p 3) = ii*v (p 3) (p 0) ∧
    a (p 0) (p 3) = -ii*a (p 3) (p 0) at f13
  have rot1 := VectorRecursionLaws (R p) (SemiProperQuadruple.rotate hp.1)
  have rot2 := VectorRecursionLaws (R (R p))
    (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hp.1))
  have rot2v : v (p 3) (p 0) = t-ii*v (p 1) (p 3) := rot2.2.2.1
  have rot2a : a (p 3) (p 0) = gamma+ii*a (p 1) (p 3) := rot2.2.2.2.1
  have h24v : v (p 2) (p 1) = y+ii*t := by
    have h := rot1.2.2.1
    change y = v (p 2) (p 1)-ii*t at h
    linear_combination -h
  have h24a : a (p 2) (p 1) = beta-ii*gamma := by
    have h := rot1.2.2.2.1
    change beta = a (p 2) (p 1)+ii*gamma at h
    linear_combination -h
  have h43v : v (p 1) (p 3) = x-ii*t := by
    have h : x = ii*t + v (p 1) (p 3) := by
      change v (p 0) (p 3) = _
      rw [f13.1, rot2v]
      ring_nf; simp only [ii_sq]; ring
    linear_combination -h
  have h43a : a (p 1) (p 3) = alpha+ii*gamma := by
    have h : alpha = -ii*gamma + a (p 1) (p 3) := by
      change a (p 0) (p 3) = _
      rw [f13.2, rot2a]
      ring_nf; simp only [ii_sq]; ring
    linear_combination -h
  -- Both complementary values have the minus sign from equation (12).
  have h14v : v (p 0) (p 1) = -(x+ii*y) := by
    rw [f14.1,predV,h43v,h24v,tr]
    ring_nf; simp only [ii_sq,ii_cube]; ring
  have h14a : a (p 0) (p 1) = -(alpha-ii*beta) := by
    rw [f14.2,predA,h43a,h24a,gr]
    ring_nf; simp only [ii_sq,ii_cube]; ring
  have h12v : v (p 0) (p 2) = ii*y := f12.1
  have h12a : a (p 0) (p 2) = -ii*beta := f12.2
  have new2 := VectorRecursionLaws (R (S p))
    (SemiProperQuadruple.rotate hs.1)
  have new3 := VectorRecursionLaws (R (R (S p)))
    (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hs.1))
  have new2v : v (p 2) (S p 0) = y-ii*t := new2.2.2.1
  have new2a : a (p 2) (S p 0) = beta+ii*gamma := new2.2.2.2.1
  have new3v : v (p 3) (S p 0) = t-ii*x := new3.2.2.1
  have new3a : a (p 3) (S p 0) = gamma+ii*alpha := new3.2.2.2.1
  rcases ih 0 3 (by decide) with ⟨hx,hax⟩
  rcases ih 2 0 (by decide) with ⟨hy,hay⟩
  rcases ih 3 2 (by decide) with ⟨ht,hat⟩
  change x^2 = _ at hx
  change y^2 = _ at hy
  change t^2 = _ at ht
  change 2*x*alpha = _ at hax
  change 2*y*beta = _ at hay
  change 2*t*gamma = _ at hat
  have e10 : E (p 0) (S p 0) := by
    constructor
    · calc
        _ = 2*x^2 + 2*v (p 0) (p 2)^2 - v (p 0) (p 1)^2 := by
          rw [new1v,h12v,h14v]
          ring_nf
        _ = _ := by
          rw [hx,(ih 0 2 (by decide)).1,(ih 0 1 (by decide)).1]
          dsimp [S]
          simp only [Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
          ring
    · calc
        _ = 2*(2*x*alpha) + 2*(2*v (p 0) (p 2)*a (p 0) (p 2)) -
            2*v (p 0) (p 1)*a (p 0) (p 1) := by
          rw [new1v,new1a,h12v,h12a,h14v,h14a]
          ring_nf
        _ = _ := by
          rw [hax,(ih 0 2 (by decide)).2,(ih 0 1 (by decide)).2]
          dsimp [S]
          ring
  have e20 : E (p 2) (S p 0) := by
    constructor
    · calc
        _ = 2*y^2 - 2*t^2 - v (p 2) (p 1)^2 := by
          rw [new2v,h24v]
          ring_nf; simp only [ii_sq]; ring
        _ = _ := by
          rw [hy,ht,(ih 2 1 (by decide)).1]
          dsimp [S]
          simp only [Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
          ring
    · calc
        _ = 2*(2*y*beta) + 2*(2*t*gamma) -
            2*v (p 2) (p 1)*a (p 2) (p 1) := by
          rw [new2v,new2a,h24v,h24a]
          ring_nf; simp only [ii_sq]; ring
        _ = _ := by
          rw [hay,hat,(ih 2 1 (by decide)).2]
          dsimp [S]
          ring
  have e30 : E (p 3) (S p 0) := by
    constructor
    · calc
        _ = 2*t^2 - 2*x^2 + v (p 1) (p 3)^2 := by
          rw [new3v,h43v]
          ring_nf; simp only [ii_sq]; ring
        _ = _ := by
          rw [ht,hx,(ih 1 3 (by decide)).1]
          dsimp [S]
          simp only [Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
          ring
    · calc
        _ = 2*(2*t*gamma) + 2*(2*x*alpha) -
            2*v (p 1) (p 3)*a (p 1) (p 3) := by
          rw [new3v,new3a,h43v,h43a]
          ring_nf; simp only [ii_sq]; ring
        _ = _ := by
          rw [hat,hax,(ih 1 3 (by decide)).2]
          dsimp [S]
          ring
  exact assemble p ih hs e10 e20 e30

private theorem rootStep :
    let ii : GaussianInt := ⟨0, 1⟩
    (ii^2 = -1) → ((ii^3 = -ii) → (
    let v := BandVectors.1
    let a := BandVectors.2
    let E (C D : CircleCoordinates) : Prop :=
      v C D ^ 2 = (D.1 : GaussianInt) * C.2 - (C.1 : GaussianInt) * D.2 ∧
        2 * v C D * a C D = C.2 + D.2
    let B (z : GaussianInt) : Fin 4 → CircleCoordinates :=
      ![(1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ii), (0, 1), (0, -1)]
    let R (p : Fin 4 → CircleCoordinates) : Fin 4 → CircleCoordinates :=
      ![p 0, p 2, p 3, p 1]
    let S (p : Fin 4 → CircleCoordinates) : Fin 4 → CircleCoordinates :=
      ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
          2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
        p 0, p 2, p 3]
    (∀ (C : CircleCoordinates), ∀ (D : CircleCoordinates), PrimitiveVectorOrientation C D →
        BandVectors.1 D C = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 C D ∧ BandVectors.2 D C = -⟨(0 :
        ℤ), (1 : ℤ)⟩ * BandVectors.2 C D) → ((∀ (z : GaussianInt), (v (B z 3) (B z 2) = 0 ∧ a (B
        z 3) (B z 2) = 1) ∧ (v (B z 2) (B z 1) = -1 ∧ a (B z 2) (B z 1) = -1-z-ii) ∧ (v (B z 3)
        (B z 1) = -ii ∧ a (B z 3) (B z 1) = ii*z-1) ∧ (v (B z 1) (B z 0) = 1+ii ∧ a (B z 1) (B z
        0) = 1+z-ii*z) ∧ (v (B z 2) (B z 0) = -1 ∧ a (B z 2) (B z 0) = -1-z) ∧ (v (B z 3) (B z 0)
        = -ii ∧ a (B z 3) (B z 0) = ii*z)) → ((∀ (z : GaussianInt), ∀ i j : Fin 4, i ≠ j → E (B z
        i) (B z j)) → ((∀ (p : Fin 4 → CircleCoordinates), (∀ i j : Fin 4, i ≠ j → E (p i) (p j))
        → (∀ i j : Fin 4, i ≠ j → E (R p i) (R p j))) → ((∀ (p : Fin 4 → CircleCoordinates), (∀ i
        j : Fin 4, i ≠ j → E (p i) (p j)) → ((ProperBandQuadruple (S p)) → ((E (p 0) (S p 0)) →
        ((E (p 2) (S p 0)) → ((E (p 3) (S p 0)) → (∀ i j : Fin 4, i ≠ j → E (S p i) (S p j)))))))
        → (∀ (z : GaussianInt), ∀ (k : Fin 3), ∀ i j : Fin 4, i ≠ j →
        E (S (if k = 0 then B z else if k = 1 then R (B z) else R (R (B z))) i)
          (S (if k = 0 then B z else if k = 1 then R (B z) else R (R (B z))) j)))))))) := by
  classical
  intro ii ii_sq ii_cube v a E B R S flipLaw rootValues root rotateEdges assemble z k
  rcases rootValues z with ⟨⟨v32,a32⟩,⟨v21,a21⟩,⟨v31,a31⟩,
    ⟨v10,a10⟩,⟨v20,a20⟩,⟨v30,a30⟩⟩
  have f01 : v (B z 0) (B z 1) = ii*v (B z 1) (B z 0) ∧
      a (B z 0) (B z 1) = -ii*a (B z 1) (B z 0) :=
    flipLaw _ _ (PrimitiveVectorOrientation.base10 z)
  have f13 : v (B z 1) (B z 3) = ii*v (B z 3) (B z 1) ∧
      a (B z 1) (B z 3) = -ii*a (B z 3) (B z 1) :=
    flipLaw _ _ (PrimitiveVectorOrientation.base31 z)
  have o20 : PrimitiveVectorOrientation (B z 2) (B z 0) := by
    have h := PrimitiveVectorOrientation.base21 (z-ii)
    have shift : 1+2*(z-ii)+2*ii = 1+2*z := by ring
    change PrimitiveVectorOrientation (0,1) (1,1+2*(z-ii)+2*ii) at h
    rw [shift] at h
    exact h
  have f02 : v (B z 0) (B z 2) = ii*v (B z 2) (B z 0) ∧
      a (B z 0) (B z 2) = -ii*a (B z 2) (B z 0) := flipLaw _ _ o20
  fin_cases k
  · change ∀ i j : Fin 4, i ≠ j → E (S (B z) i) (S (B z) j)
    have shift : S (B z) = B (z-ii) := by
      funext l
      fin_cases l <;> simp [S,B] <;> ring
    rw [shift]
    exact root (z-ii)
  · change ∀ i j : Fin 4, i ≠ j → E (S (R (B z)) i) (S (R (B z)) j)
    let Q : Fin 4 → CircleCoordinates :=
      ![(4,1+8*z+4*ii), B z 0, B z 3, B z 1]
    have he : S (R (B z)) = Q := by
      funext l
      fin_cases l <;> simp [S,R,B,Q]; ring
    rw [he]
    have hr : SemiProperQuadruple (R (B z)) :=
      SemiProperQuadruple.rotate (SemiProperQuadruple.base z)
    have hs : ProperBandQuadruple (Q) := by
      rcases BandSuccessorClassification (R (B z)) hr with bad | good
      · simp [R,B] at bad
      · have h : ProperBandQuadruple (S (R (B z))) := good.1
        rw [he] at h
        exact h
    have laws1 := VectorRecursionLaws (Q) hs.1
    have laws2 := VectorRecursionLaws (R (Q))
      (SemiProperQuadruple.rotate hs.1)
    have laws3 := VectorRecursionLaws (R (R (Q)))
      (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hs.1))
    have nv1 : v (B z 0) (Q 0) =
        v (B z 0) (B z 1)-ii*v (B z 3) (B z 0) := laws1.2.2.1
    have na1 : a (B z 0) (Q 0) =
        a (B z 0) (B z 1)+ii*a (B z 3) (B z 0) := laws1.2.2.2.1
    have nv2 : v (B z 3) (Q 0) =
        v (B z 3) (B z 0)-ii*v (B z 1) (B z 3) := laws2.2.2.1
    have na2 : a (B z 3) (Q 0) =
        a (B z 3) (B z 0)+ii*a (B z 1) (B z 3) := laws2.2.2.2.1
    have nv3 : v (B z 1) (Q 0) =
        v (B z 1) (B z 3)-ii*v (B z 0) (B z 1) := laws3.2.2.1
    have na3 : a (B z 1) (Q 0) =
        a (B z 1) (B z 3)+ii*a (B z 0) (B z 1) := laws3.2.2.2.1
    have dv1 : v (B z 0) (Q 0) = -2+ii := by
      rw [nv1,f01.1,v10,v30]
      ring_nf; simp only [ii_sq]; ring
    have da1 : a (B z 0) (Q 0) = -2*z-ii-ii*z := by
      rw [na1,f01.2,a10,a30]
      ring_nf; simp only [ii_sq]; ring
    have dv2 : v (B z 3) (Q 0) = -2*ii := by
      rw [nv2,f13.1,v31,v30]
      ring_nf; simp only [ii_cube]; ring
    have da2 : a (B z 3) (Q 0) = 2*ii*z-1 := by
      rw [na2,f13.2,a31,a30]
      ring_nf; simp only [ii_sq,ii_cube]; ring
    have dv3 : v (B z 1) (Q 0) = 2+ii := by
      rw [nv3,f13.1,f01.1,v31,v10]
      ring_nf; simp only [ii_sq,ii_cube]; ring
    have da3 : a (B z 1) (Q 0) = 1+2*z+ii-ii*z := by
      rw [na3,f13.2,f01.2,a31,a10]
      ring_nf; simp only [ii_sq,ii_cube]; ring
    have e10 : E (B z 0) (Q 0) := by
      dsimp only [E]; rw [dv1,da1]
      constructor <;> simp [Q,B] <;> ring_nf <;> simp only [ii_sq] <;> ring
    have e20 : E (B z 3) (Q 0) := by
      dsimp only [E]; rw [dv2,da2]
      constructor <;> simp [Q,B] <;> ring_nf <;> simp only [ii_sq] <;> ring
    have e30 : E (B z 1) (Q 0) := by
      dsimp only [E]; rw [dv3,da3]
      constructor <;> simp [Q,B] <;> ring_nf <;> simp only [ii_sq] <;> ring
    have result := assemble (R (B z)) (rotateEdges (B z) (root z))
      (by rw [he]; exact hs)
      (by rw [he]; change E (B z 0) (Q 0); exact e10)
      (by rw [he]; change E (B z 3) (Q 0); exact e20)
      (by rw [he]; change E (B z 1) (Q 0); exact e30)
    rw [he] at result
    exact result
  · change ∀ i j : Fin 4, i ≠ j →
      E (S (R (R (B z))) i) (S (R (R (B z))) j)
    let Q : Fin 4 → CircleCoordinates :=
      ![(4,7+8*z+4*ii), B z 0, B z 1, B z 2]
    have he : S (R (R (B z))) = Q := by
      funext l
      fin_cases l <;> simp [S,R,B,Q]; ring
    rw [he]
    have hr : SemiProperQuadruple (R (R (B z))) :=
      SemiProperQuadruple.rotate (SemiProperQuadruple.rotate (SemiProperQuadruple.base z))
    have hs : ProperBandQuadruple (Q) := by
      rcases BandSuccessorClassification (R (R (B z))) hr with bad | good
      · simp [R,B] at bad
      · have h : ProperBandQuadruple (S (R (R (B z)))) := good.1
        rw [he] at h
        exact h
    have laws1 := VectorRecursionLaws (Q) hs.1
    have laws2 := VectorRecursionLaws (R (Q))
      (SemiProperQuadruple.rotate hs.1)
    have laws3 := VectorRecursionLaws (R (R (Q)))
      (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hs.1))
    have nv1 : v (B z 0) (Q 0) =
        v (B z 0) (B z 2)-ii*v (B z 1) (B z 0) := laws1.2.2.1
    have na1 : a (B z 0) (Q 0) =
        a (B z 0) (B z 2)+ii*a (B z 1) (B z 0) := laws1.2.2.2.1
    have nv2 : v (B z 1) (Q 0) =
        v (B z 1) (B z 0)-ii*v (B z 2) (B z 1) := laws2.2.2.1
    have na2 : a (B z 1) (Q 0) =
        a (B z 1) (B z 0)+ii*a (B z 2) (B z 1) := laws2.2.2.2.1
    have nv3 : v (B z 2) (Q 0) =
        v (B z 2) (B z 1)-ii*v (B z 0) (B z 2) := laws3.2.2.1
    have na3 : a (B z 2) (Q 0) =
        a (B z 2) (B z 1)+ii*a (B z 0) (B z 2) := laws3.2.2.2.1
    have dv1 : v (B z 0) (Q 0) = 1-2*ii := by
      rw [nv1,f02.1,v20,v10]
      ring_nf; simp only [ii_sq]; ring
    have da1 : a (B z 0) (Q 0) = z+2*ii+2*ii*z := by
      rw [na1,f02.2,a20,a10]
      ring_nf; simp only [ii_sq]; ring
    have dv2 : v (B z 1) (Q 0) = 1+2*ii := by
      rw [nv2,v10,v21]
      ring
    have da2 : a (B z 1) (Q 0) = 2+z-ii-2*ii*z := by
      rw [na2,a10,a21]
      ring_nf; simp only [ii_sq]; ring
    have dv3 : v (B z 2) (Q 0) = -2 := by
      rw [nv3,f02.1,v21,v20]
      ring_nf; simp only [ii_sq]; ring
    have da3 : a (B z 2) (Q 0) = -2-2*z-ii := by
      rw [na3,f02.2,a21,a20]
      ring_nf; simp only [ii_sq]; ring
    have e10 : E (B z 0) (Q 0) := by
      dsimp only [E]; rw [dv1,da1]
      constructor <;> simp [Q,B] <;> ring_nf <;> simp only [ii_sq] <;> ring
    have e20 : E (B z 1) (Q 0) := by
      dsimp only [E]; rw [dv2,da2]
      constructor <;> simp [Q,B] <;> ring_nf <;> simp only [ii_sq] <;> ring
    have e30 : E (B z 2) (Q 0) := by
      dsimp only [E]; rw [dv3,da3]
      constructor <;> simp [Q,B] <;> ring_nf
    have result := assemble (R (R (B z)))
      (rotateEdges (R (B z)) (rotateEdges (B z) (root z)))
      (by rw [he]; exact hs)
      (by rw [he]; change E (B z 0) (Q 0); exact e10)
      (by rw [he]; change E (B z 1) (Q 0); exact e20)
      (by rw [he]; change E (B z 2) (Q 0); exact e30)
    rw [he] at result
    exact result

end VectorSquareProof

theorem VectorSquareProduct (q : Fin 4 → CircleCoordinates)
    (hq : SemiProperQuadruple q) (i j : Fin 4) (hij : i ≠ j) :
    BandVectors.1 (q i) (q j) ^ 2 =
        (q j).1 • (q i).2 - (q i).1 • (q j).2 ∧
      2 * BandVectors.1 (q i) (q j) * BandVectors.2 (q i) (q j) =
        (q i).2 + (q j).2 := by
-- BODY
  let ii : GaussianInt := ⟨0, 1⟩
  have ii_sq : ii^2 = -1 := VectorSquareProof.ii_sq
  have ii_cube : ii^3 = -ii := VectorSquareProof.ii_cube
  let v := BandVectors.1
  let a := BandVectors.2
  let E (C D : CircleCoordinates) : Prop :=
    v C D ^ 2 = (D.1 : GaussianInt) * C.2 - (C.1 : GaussianInt) * D.2 ∧
      2 * v C D * a C D = C.2 + D.2
  let B (z : GaussianInt) : Fin 4 → CircleCoordinates :=
    ![(1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ii), (0, 1), (0, -1)]
  let R (p : Fin 4 → CircleCoordinates) : Fin 4 → CircleCoordinates :=
    ![p 0, p 2, p 3, p 1]
  let S (p : Fin 4 → CircleCoordinates) : Fin 4 → CircleCoordinates :=
    ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
        2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
      p 0, p 2, p 3]
  have system : RecursiveVectorSystem BandVectors := VectorSquareProof.system
  rcases system with ⟨_, baseLaw, _, flipLaw⟩
  have reverse (C D : CircleCoordinates) (ho : PrimitiveVectorOrientation C D)
      (h : E C D) : E D C := VectorSquareProof.reverse ii_sq flipLaw C D ho h
  have rootValues (z : GaussianInt) :
      (v (B z 3) (B z 2) = 0 ∧ a (B z 3) (B z 2) = 1) ∧
      (v (B z 2) (B z 1) = -1 ∧ a (B z 2) (B z 1) = -1-z-ii) ∧
      (v (B z 3) (B z 1) = -ii ∧ a (B z 3) (B z 1) = ii*z-1) ∧
      (v (B z 1) (B z 0) = 1+ii ∧ a (B z 1) (B z 0) = 1+z-ii*z) ∧
      (v (B z 2) (B z 0) = -1 ∧ a (B z 2) (B z 0) = -1-z) ∧
      (v (B z 3) (B z 0) = -ii ∧ a (B z 3) (B z 0) = ii*z) := VectorSquareProof.rootValues
          ii_sq baseLaw flipLaw z
  have root (z : GaussianInt) : ∀ i j : Fin 4, i ≠ j → E (B z i) (B z j) :=
      VectorSquareProof.root ii_sq reverse rootValues z
  have rotateEdges (p : Fin 4 → CircleCoordinates)
      (ih : ∀ i j : Fin 4, i ≠ j → E (p i) (p j)) :
      ∀ i j : Fin 4, i ≠ j → E (R p i) (R p j) := VectorSquareProof.rotateEdges p ih
  have assemble (p : Fin 4 → CircleCoordinates)
      (ih : ∀ i j : Fin 4, i ≠ j → E (p i) (p j))
      (hs : ProperBandQuadruple (S p))
      (e10 : E (p 0) (S p 0)) (e20 : E (p 2) (S p 0))
      (e30 : E (p 3) (S p 0)) :
      ∀ i j : Fin 4, i ≠ j → E (S p i) (S p j) := VectorSquareProof.assemble reverse p ih hs e10
          e20 e30
  have properStep (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p)
      (ih : ∀ i j : Fin 4, i ≠ j → E (p i) (p j)) :
      ∀ i j : Fin 4, i ≠ j → E (S p i) (S p j) := VectorSquareProof.properStep ii_sq ii_cube
          assemble p hp ih
  have rootStep (z : GaussianInt) (k : Fin 3) :
      ∀ i j : Fin 4, i ≠ j →
        E (S (if k = 0 then B z else if k = 1 then R (B z) else R (R (B z))) i)
          (S (if k = 0 then B z else if k = 1 then R (B z) else R (R (B z))) j) :=
              VectorSquareProof.rootStep ii_sq ii_cube flipLaw rootValues root rotateEdges
              assemble z k
  simp only [zsmul_eq_mul]
  change E (q i) (q j)
  induction hq generalizing i j with
  | base z => exact root z i j hij
  | @rotate p hp ih =>
      exact rotateEdges p ih i j hij
  | @successor p hp ih =>
      change E (S p i) (S p j)
      rcases (SemiProperForestClassification p hp).2 with h | h | h | h
      · rcases h with ⟨z,hz⟩
        change p = B z at hz
        rw [hz]
        have h := rootStep z 0
        change (∀ i j : Fin 4, i ≠ j → E (S (B z) i) (S (B z) j)) at h
        exact h i j hij
      · rcases h with ⟨z,hz⟩
        change p = R (B z) at hz
        rw [hz]
        have h := rootStep z 1
        change (∀ i j : Fin 4, i ≠ j → E (S (R (B z)) i) (S (R (B z)) j)) at h
        exact h i j hij
      · rcases h with ⟨z,hz⟩
        change p = R (R (B z)) at hz
        rw [hz]
        have h := rootStep z 2
        change (∀ i j : Fin 4, i ≠ j → E (S (R (R (B z))) i) (S (R (R (B z))) j)) at h
        exact h i j hij
      · exact properStep p h ih i j hij

end ApollonianSuperharmonic

end
