/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.ProperBandCircleCenterDistance

public import LeanPool.ApollonianSuperharmonic.P4984T1ClosedGap
public import LeanPool.ApollonianSuperharmonic.P4984T1ClosedSubdivision
public import LeanPool.ApollonianSuperharmonic.P4828T1Gap
public import LeanPool.ApollonianSuperharmonic.P4828T1LineSupport
public import LeanPool.ApollonianSuperharmonic.P4828T1ConstructorSupport
public import LeanPool.ApollonianSuperharmonic.P4828T1ParentsDistinct
public import LeanPool.ApollonianSuperharmonic.P5050T1ParentSphereSection
public import LeanPool.ApollonianSuperharmonic.P5050T1OmittedHullSeparation

-- [TABLET NODE: P4984T1IncidentArcs]

/-!
# P4984T1IncidentArcs

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace IncidentArcGeometry

private theorem hparentContactDistance :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (j : Fin 3), ((0 : ℤ) <
            (q j.succ).1) → ((∀ (v : Fin 4 → CircleCoordinates), (ProperBandQuadruple v) → (∀ (i
            : Fin 4), ∀ (k : Fin 4), (i ≠ k) → ((0 < (v i).1) → ((0 < (v k).1) → (dist (((v i).2
            : Complex) / (v i).1) (((v k).2 : Complex) / (v k).1) = 1 / (v i).1 + 1 / (v
            k).1))))) → (dist (((q j.succ).2 : Complex) / ((q j.succ).1 : Real)) (((q 0).2 :
            Complex) / ((q 0).1 : Real)) = 1 / ((q j.succ).1 : Real) + 1 / ((q 0).1 : Real)))) )
            := by
  classical
  intro q hq j hj circleDistance
  exact circleDistance q hq j.succ 0 (Fin.succ_ne_zero j) hj
    (ProperBandCurvatureStructure q hq |>.1)

private theorem hS :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (
        let rad (i : Fin 4) : Real := 1 / ((q i).1 : Real)
        let S := rad 0
        0 < S) ) := by
  classical
  intro q hq rad S
  dsimp [S, rad]
  exact one_div_pos.mpr (by exact_mod_cast (ProperBandCurvatureStructure q hq).1)

private theorem hαmul :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (j : Fin 3),
        let rad (i : Fin 4) : Real := 1 / ((q i).1 : Real)
        let R := rad j.succ
        let S := rad 0
        (0 < R) → ((0 < S) → (
        let α := R / (R + S)
        α * (R + S) = R)) ) := by
  classical
  intro q j rad R S hR hS α
  dsimp [α]
  exact div_mul_cancel₀ R (ne_of_gt (add_pos hR hS))

private theorem hcompmul :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (j : Fin 3),
        let rad (i : Fin 4) : Real := 1 / ((q i).1 : Real)
        let R := rad j.succ
        let S := rad 0
        let α := R / (R + S)
        (α * (R + S) = R) → ((1 - α) * (R + S) = S) ) := by
  classical
  intro q j rad R S α hαmul
  rw [sub_mul, one_mul, hαmul]
  ring

private theorem hta :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (j : Fin 3),
        let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
        let rad (i : Fin 4) : Real := 1 / ((q i).1 : Real)
        let a := p j.succ
        let x := p 0
        let R := rad j.succ
        let S := rad 0
        let α := R / (R + S)
        (0 < α) → ((α * (R + S) = R) → (
        let t := a + α • (x - a)
        (‖x - a‖ = R + S) → (dist t a = R))) ) := by
  classical
  intro q j p rad a x R S α hα hαmul t hnormax
  have hv : t - a = α • (x - a) := by simp [t]
  have hd : dist t a = α * (R + S) := by
    rw [dist_eq_norm, hv, Complex.real_smul, Complex.norm_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hα, hnormax]
  rw [hd]
  exact hαmul

private theorem htx :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (j : Fin 3),
        let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
        let rad (i : Fin 4) : Real := 1 / ((q i).1 : Real)
        let a := p j.succ
        let x := p 0
        let R := rad j.succ
        let S := rad 0
        let α := R / (R + S)
        (α < 1) → (((1 - α) * (R + S) = S) → (
        let t := a + α • (x - a)
        (‖x - a‖ = R + S) → (dist t x = S))) ) := by
  classical
  intro q j p rad a x R S α hαlt hcompmul t hnormax
  have hv : t - x = (1 - α) • (a - x) := by
    apply Complex.ext
    · simp [t]
      ring
    · simp [t]
      ring
  have hd : dist t x = (1 - α) * (R + S) := by
    rw [dist_eq_norm, hv, Complex.real_smul, Complex.norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hαlt)]
    rw [← norm_sub_rev, hnormax]
  rw [hd]
  exact hcompmul

private theorem hxDisk :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
        let rad (i : Fin 4) : Real := 1 / ((q i).1 : Real)
        let x := p 0
        let S := rad 0
        (0 < S) → (x ∈ P4828T1Disk (q 0)) ) := by
  classical
  intro q p rad x S hS
  change dist x x < S
  simpa [x, p, S, rad, P4828T1Disk] using hS

private theorem haPoly :
    (by
      classical
      exact
        ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates), ∀ (j : Fin 3), ((0 : ℤ) < (q j.succ).1) → (
        let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
        let a := p j.succ
        a ∈ P4909T1ParentPolygon L q) ) := by
  classical
  intro L q j hj p a
  change a ∈ convexHull Real {z | ∃ i : Fin 3, 0 < (q i.succ).1 ∧
    (z = p i.succ ∨ ∃ k : Fin 3, (q k.succ).1 = 0 ∧
      z = ⟨if (q k.succ).2 = -1 then L else L + 2, (p i.succ).im⟩)}
  exact subset_convexHull Real _ ⟨j, hj, Or.inl rfl⟩

private theorem htseg :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (j : Fin 3),
        let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
        let rad (i : Fin 4) : Real := 1 / ((q i).1 : Real)
        let a := p j.succ
        let x := p 0
        let R := rad j.succ
        let S := rad 0
        let α := R / (R + S)
        (0 < α) → ((α < 1) → (
        let t := a + α • (x - a)
        t ∈ segment Real a x)) ) := by
  classical
  intro q j p rad a x R S α hα hαlt t
  rw [segment_eq_image_lineMap]
  refine ⟨α, ⟨le_of_lt hα, le_of_lt hαlt⟩, ?_⟩
  dsimp [t]
  rw [AffineMap.lineMap_apply_module']
  simp [Complex.real_smul]
  abel

private theorem hfar :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (j : Fin 3), ((0 : ℤ) <
            (q j.succ).1) → ((∀ (v : Fin 4 → CircleCoordinates), (ProperBandQuadruple v) → (∀ (i
            : Fin 4), ∀ (k : Fin 4), (i ≠ k) → ((0 < (v i).1) → ((0 < (v k).1) → (dist (((v i).2
            : Complex) / (v i).1) (((v k).2 : Complex) / (v k).1) = 1 / (v i).1 + 1 / (v
            k).1))))) → (
        let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
        let rad (i : Fin 4) : Real := 1 / ((q i).1 : Real)
        let a := p j.succ
        let x := p 0
        let R := rad j.succ
        let S := rad 0
        let α := R / (R + S)
        let t := a + α • (x - a)
        (dist t a = R) → (∀ (k : Fin (3 : ℕ)), (0 : ℤ) < (q k.succ).1 → rad k.succ ≤ dist t (p
            k.succ))))) ) := by
  classical
  intro q hq j hj circleDistance p rad a x R S α t hta k hk
  by_cases hkj : k = j
  · subst k
    simpa [rad, R, a, p] using (le_of_eq hta.symm)
  · have hd := circleDistance q hq j.succ k.succ
      (fun h => hkj (Fin.succ_inj.mp h).symm) hj hk
    have htri := dist_triangle a t (p k.succ)
    rw [dist_comm a t, hta] at htri
    have hd' : dist a (p k.succ) = R + rad k.succ := by
      simpa [a, R, rad, p] using hd
    rw [hd'] at htri
    linarith

private theorem htGap :
    (by
      classical
      exact
        ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates), ∀ (j : Fin 3),
        let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
        let rad (i : Fin 4) : Real := 1 / ((q i).1 : Real)
        let a := p j.succ
        let x := p 0
        let R := rad j.succ
        let S := rad 0
        let α := R / (R + S)
        let t := a + α • (x - a)
        (t ∈ P4909T1ParentPolygon L q) → ((∀ (k : Fin 3), (0 < (q k.succ).1) → (rad k.succ ≤
            dist t (p k.succ))) → (t ∈ P4984T1ClosedGap L q)) ) := by
  classical
  intro L q j p rad a x R S α t htPoly hfar
  refine ⟨htPoly, ?_⟩
  intro k hk
  exact hfar k hk

private theorem htA :
    (by
      classical
      exact
        ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates), ∀ (j : Fin 3),
        let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
        let rad (i : Fin 4) : Real := 1 / ((q i).1 : Real)
        let a := p j.succ
        let x := p 0
        let R := rad j.succ
        let S := rad 0
        let α := R / (R + S)
        let t := a + α • (x - a)
        (dist t a = R) → ((t ∈ P4984T1ClosedGap L q) → (t ∈ P4984T1ClosedGap L q ∩
            Metric.sphere a R)) ) := by
  classical
  intro L q j p rad a x R S α t hta htGap
  refine ⟨htGap, Metric.mem_sphere.mpr ?_⟩
  simpa [dist_comm] using hta

private theorem hVsub :
    (by
      classical
      exact
        ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates), ∀ (j : Fin 3), ((0 : ℤ) < (q j.succ).1) → (
        let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
        let foot (i k : Fin 3) : Complex :=
          ⟨if (q k.succ).2 = -1 then L else L + 2, (p i.succ).im⟩
        let V : Set Complex := {z | ∃ i : Fin 3, 0 < (q i.succ).1 ∧
          (z = p i.succ ∨ ∃ k : Fin 3, (q k.succ).1 = 0 ∧ z = foot i k)}
        let f : Fin 3 × Fin 3 → Complex := fun ij =>
          if (q ij.2.succ).1 = 0 then foot ij.1 ij.2 else p ij.1.succ
        V ⊆ Set.range f) ) := by
  classical
  intro L q j hj p foot V f
  rintro z ⟨i, hi, rfl | ⟨k, hk, rfl⟩⟩
  · refine ⟨(i, j), ?_⟩
    simp [f, hj.ne']
  · exact ⟨(i, k), by simp [f, hk, foot]⟩

private theorem hParentClosed :
    (by
      classical
      exact
        ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates),
        let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
        let foot (i k : Fin 3) : Complex :=
          ⟨if (q k.succ).2 = -1 then L else L + 2, (p i.succ).im⟩
        let V : Set Complex := {z | ∃ i : Fin 3, 0 < (q i.succ).1 ∧
          (z = p i.succ ∨ ∃ k : Fin 3, (q k.succ).1 = 0 ∧ z = foot i k)}
        (V.Finite) → (IsClosed (P4909T1ParentPolygon L q)) ) := by
  classical
  intro L q p foot V hVfinite
  change IsClosed (convexHull Real V)
  exact hVfinite.isClosed_convexHull Real

private theorem hClosedGap :
    (by
      classical
      exact
        ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates), ∀ [ IsClosed
            (P4909T1ParentPolygon L q)], IsClosed (P4984T1ClosedGap L q) ) := by
  classical
  intro L q hParentClosed
  change IsClosed (P4909T1ParentPolygon L q ∩
    {z | ∀ k : Fin 3, 0 < (q k.succ).1 →
      1 / ((q k.succ).1 : Real) ≤
        dist z (((q k.succ).2 : Complex) / ((q k.succ).1 : Real))})
  apply hParentClosed.inter
  rw [Set.ofPred_forall]
  apply isClosed_iInter
  intro k
  by_cases hk : 0 < (q k.succ).1
  · simp only [hk, true_implies]
    exact isClosed_Ici.preimage
      (continuous_id.dist continuous_const)
  · simp [not_lt.mp hk]

private theorem slot :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (b : Fin (3 : ℕ)), ∀ (k : Fin (3 : ℕ)),
            P4828T1Step (P4828T1Rotate q b) k.succ = if k = (0 : Fin (3 : ℕ)) then q (0 : Fin
            (4 : ℕ)) else q (k + b).succ ) := by
  classical
  intro q b k
  fin_cases b <;> fin_cases k <;> rfl

private theorem keep :
    (by
      classical
      exact
        ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (j : Fin
            3), ((0 : ℤ) < (q j.succ).1) → ((dist (((q j.succ).2 : Complex) / ((q j.succ).1 :
            Real)) (((q 0).2 : Complex) / ((q 0).1 : Real)) = 1 / ((q j.succ).1 : Real) + 1 / ((q
            0).1 : Real)) → (
        let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
        let rad (i : Fin 4) : Real := 1 / ((q i).1 : Real)
        let a := p j.succ
        let x := p 0
        let R := rad j.succ
        let S := rad 0
        (0 < R) → ((dist a x = R + S) → (
        let α := R / (R + S)
        (0 < α) → ((α < 1) → ((α * (R + S) = R) → (((1 - α) * (R + S) = S) → (
        let t := a + α • (x - a)
        (‖x - a‖ = R + S) → ((dist t a = R) → ((dist t x = S) → ((a ∈ P4909T1ParentPolygon L q)
            → ((t ∈ segment Real a x) → ((t ∈ P4909T1ParentPolygon L q) → ((∀ (k : Fin 3), (0 <
            (q k.succ).1) → (rad k.succ ≤ dist t (p k.succ))) → ((t ∈ P4984T1ClosedGap L q) →
            ((t ∈ P4984T1ClosedGap L q ∩ Metric.sphere a R) → (∀ [ IsClosed
            (P4984T1ClosedGap L q ∩ Metric.sphere a R)], ((P4984T1ClosedGap L q ∩
            Metric.sphere a R).Nonempty) → ((∀ (b : Fin 3), ∀ (k : Fin 3), P4828T1Step
            (P4828T1Rotate q b) k.succ = if k = 0 then q 0 else q ((k + b).succ)) → (∀ (b : Fin
            (3 : ℕ)), b ≠ j ↔ ∃ (k : Fin (3 : ℕ)), P4828T1Step (P4828T1Rotate q b) k.succ = q
            j.succ)))))))))))))))))))) ) := by
  classical
  intro L q hq j hj hparentContactDistance p rad a x R S hR hax α hα hαlt hαmul hcompmul t
      hnormax hta htx haPoly htseg htPoly hfar htGap htA hAclosed hANonempty slot b
  constructor
  · intro hb
    fin_cases b <;> fin_cases j
    all_goals norm_num at hb
    all_goals first | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩
  · rintro ⟨k, hk⟩ hb
    rw [slot] at hk
    split_ifs at hk with hkzero
    · have hroot : (q j.succ).1 < (q 0).1 := hq.2 j
      have heq := congrArg Prod.fst hk
      omega
    · have hkj := (P4828T1ParentsDistinct q hq) hk
      subst j
      have : k = 0 := by
        fin_cases k
        · rfl
        · fin_cases b <;> norm_num at hkj
        · fin_cases b <;> norm_num at hkj
      exact hkzero this

private theorem closedGapOfParent :
    (by
      classical
      exact
        ∀ (L : Real), ∀ (u : Fin (4 : ℕ) → CircleCoordinates), ∀ (m : Fin (3 : ℕ)), (0 : ℤ) < (u
            m.succ).1 → IsClosed (P4984T1ClosedGap L u) ) := by
  classical
  intro L u m hm
  let pu (i : Fin 4) : Complex := (u i).2 / ((u i).1 : Real)
  let fu (i k : Fin 3) : Complex :=
    ⟨if (u k.succ).2 = -1 then L else L + 2, (pu i.succ).im⟩
  let Vu : Set Complex := {z | ∃ i : Fin 3, 0 < (u i.succ).1 ∧
    (z = pu i.succ ∨ ∃ k : Fin 3, (u k.succ).1 = 0 ∧ z = fu i k)}
  let gu : Fin 3 × Fin 3 → Complex := fun ik =>
    if (u ik.2.succ).1 = 0 then fu ik.1 ik.2 else pu ik.1.succ
  have hsub : Vu ⊆ Set.range gu := by
    rintro z ⟨i, hi, rfl | ⟨k, hk, rfl⟩⟩
    · exact ⟨(i, m), by simp [gu, hm.ne']⟩
    · exact ⟨(i, k), by simp [gu, hk, fu]⟩
  have hfinite : Vu.Finite := (Set.finite_range gu).subset hsub
  have hpoly : IsClosed (P4909T1ParentPolygon L u) := by
    change IsClosed (convexHull Real Vu)
    exact hfinite.isClosed_convexHull Real
  change IsClosed (P4909T1ParentPolygon L u ∩
    {z | ∀ k : Fin 3, 0 < (u k.succ).1 →
      1 / ((u k.succ).1 : Real) ≤
        dist z (((u k.succ).2 : Complex) / ((u k.succ).1 : Real))})
  apply hpoly.inter
  rw [Set.ofPred_forall]
  apply isClosed_iInter
  intro k
  by_cases hk : 0 < (u k.succ).1
  · simp only [hk, true_implies]
    exact isClosed_Ici.preimage (continuous_id.dist continuous_const)
  · simp [not_lt.mp hk]

private theorem hchildCover :
    (by
      classical
      exact
        ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) →
            ((P4828T1LineSupport L q) → ((P4828T1Disk (q (0 : Fin (4 : ℕ))) ⊆ P4828T1Gap L
            q) → (∀ (j : Fin 3),
        let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
        let rad (i : Fin 4) : Real := 1 / ((q i).1 : Real)
        let a := p j.succ
        let x := p 0
        let R := rad j.succ
        let S := rad 0
        (dist a x = R + S) → (
        let arc (b : Fin 3) :=
          P4984T1ClosedGap L (P4828T1Step (P4828T1Rotate q b)) ∩
            Metric.sphere a R
        (P4984T1ClosedGap L q ∩ Metric.sphere a R) ⊆ ⋃ b : Fin 3, arc b)))) ) := by
  classical
  intro L q hq hs hi j p rad a x R S hax arc
  have hsubdiv := P4984T1ClosedSubdivision L q hq hs hi
  intro z hz
  have hzUnion : z ∈ Metric.closedBall x S ∪ ⋃ b : Fin 3,
      P4984T1ClosedGap L (P4828T1Step (P4828T1Rotate q b)) := by
    rw [← hsubdiv.2.2.1]
    exact hz.1
  rcases hzUnion with hzball | hzchildren
  · have hza : dist a z = R := by
      have hmem := Metric.mem_sphere.mp hz.2
      simpa only [dist_comm] using hmem
    have htri := dist_triangle a z x
    rw [hax, hza] at htri
    have hzx : S ≤ dist z x := by linarith
    have hrootSphere : z ∈ Metric.sphere x S := by
      rw [Metric.mem_sphere]
      exact le_antisymm (Metric.mem_closedBall.mp hzball) hzx
    have hcovered := hsubdiv.2.2.2.1 hrootSphere
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hcovered
    exact Set.mem_iUnion.mpr ⟨b, hb, hz.2⟩
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hzchildren
    exact Set.mem_iUnion.mpr ⟨b, hb, hz.2⟩

private theorem hchildSub :
    (by
      classical
      exact
        ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) →
            ((P4828T1LineSupport L q) → ((P4828T1Disk (q (0 : Fin (4 : ℕ))) ⊆ P4828T1Gap L
            q) → (∀ (j : Fin 3),
        let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
        let rad (i : Fin 4) : Real := 1 / ((q i).1 : Real)
        let a := p j.succ
        let R := rad j.succ
        let arc (b : Fin 3) :=
          P4984T1ClosedGap L (P4828T1Step (P4828T1Rotate q b)) ∩
            Metric.sphere a R
        ∀ (b : Fin (3 : ℕ)), arc b ⊆ P4984T1ClosedGap L q ∩ Metric.sphere a R))) ) := by
  classical
  intro L q hq hs hi j p rad a R arc b
  have hsubdiv := P4984T1ClosedSubdivision L q hq hs hi
  intro z hz
  exact ⟨hsubdiv.2.1 b hz.1, hz.2⟩

private theorem hAllUnion :
    (by
      classical
      exact
        ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates), ∀ (j : Fin 3),
        let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
        let rad (i : Fin 4) : Real := 1 / ((q i).1 : Real)
        let a := p j.succ
        let R := rad j.succ
        let arc (b : Fin 3) :=
          P4984T1ClosedGap L (P4828T1Step (P4828T1Rotate q b)) ∩
            Metric.sphere a R
        ((P4984T1ClosedGap L q ∩ Metric.sphere a R) ⊆ ⋃ b : Fin 3, arc b) → ((∀ (b : Fin 3),
            arc b ⊆ P4984T1ClosedGap L q ∩ Metric.sphere a R) → (P4984T1ClosedGap L q ∩
            Metric.sphere a R = ⋃ b : Fin 3, arc b)) ) := by
  classical
  intro L q j p rad a R arc hchildCover hchildSub
  apply Set.Subset.antisymm
  · exact hchildCover
  · intro z hz
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hz
    exact hchildSub b hb

private theorem hNotretaining :
    (by
      classical
      exact
        ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) →
            ((P4828T1LineSupport L q) → (∀ (j : Fin 3), ((0 : ℤ) < (q j.succ).1) → (
        let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
        let rad (i : Fin 4) : Real := 1 / ((q i).1 : Real)
        let a := p j.succ
        let R := rad j.succ
        let arc (b : Fin 3) :=
          P4984T1ClosedGap L (P4828T1Step (P4828T1Rotate q b)) ∩
            Metric.sphere a R
        arc j = ∅))) ) := by
  classical
  intro L q hq hs j hj p rad a R arc
  obtain ⟨D, _, hsphere, hhull⟩ :=
    P5050T1OmittedHullSeparation L q hq hs j hj
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hz
  exact (not_lt_of_ge (hsphere z hz.2)) (hhull z hz.1.1)

private theorem hEraseUnion :
    (by
      classical
      exact
        ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates), ∀ (j : Fin 3),
        let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
        let rad (i : Fin 4) : Real := 1 / ((q i).1 : Real)
        let a := p j.succ
        let R := rad j.succ
        let arc (b : Fin 3) :=
          P4984T1ClosedGap L (P4828T1Step (P4828T1Rotate q b)) ∩
            Metric.sphere a R
        (arc j = ∅) → ((⋃ b ∈ Finset.univ.erase j, arc b) = ⋃ b : Fin 3, arc b) ) := by
  classical
  intro L q j p rad a R arc hNotretaining
  ext z
  simp only [Set.mem_iUnion, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨b, hb, hz⟩
    exact ⟨b, hz⟩
  · rintro ⟨b, hz⟩
    by_cases hb : b = j
    · subst b
      rw [hNotretaining] at hz
      simp at hz
    · exact ⟨b, hb, hz⟩

private theorem hchildArcClosed :
    (by
      classical
      exact
        ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates), ∀ (j : Fin 3), ((0 : ℤ) < (q j.succ).1) → (
        let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
        let rad (i : Fin 4) : Real := 1 / ((q i).1 : Real)
        let a := p j.succ
        let R := rad j.succ
        (∀ (b : Fin 3), (b ≠ j ↔ ∃ k : Fin 3, P4828T1Step (P4828T1Rotate q b) k.succ = q
            j.succ)) → ((∀ (u : Fin 4 → CircleCoordinates), ∀ (m : Fin 3), (0 < (u m.succ).1) →
            (IsClosed (P4984T1ClosedGap L u))) → (
        let arc (b : Fin 3) :=
          P4984T1ClosedGap L (P4828T1Step (P4828T1Rotate q b)) ∩
            Metric.sphere a R
        ∀ (b : Fin (3 : ℕ)), b ≠ j → IsClosed (arc b)))) ) := by
  classical
  intro L q j hj p rad a R keep closedGapOfParent arc b hb
  obtain ⟨k, hk⟩ := (keep b).mp hb
  have hkpos : 0 < (P4828T1Step (P4828T1Rotate q b) k.succ).1 := by
    rw [hk]
    exact hj
  exact (closedGapOfParent _ k hkpos).inter Metric.isClosed_sphere

private theorem hchildArcContains :
    (by
      classical
      exact
        ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (j : Fin
            3), ((0 : ℤ) < (q j.succ).1) → (
        let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
        let rad (i : Fin 4) : Real := 1 / ((q i).1 : Real)
        let a := p j.succ
        let x := p 0
        let R := rad j.succ
        let S := rad 0
        let α := R / (R + S)
        let t := a + α • (x - a)
        (dist t a = R) → ((dist t x = S) → ((t ∈ segment Real a x) → ((∀ (k : Fin 3), (0 < (q
            k.succ).1) → (rad k.succ ≤ dist t (p k.succ))) → ((∀ (b : Fin 3), ∀ (k : Fin 3),
            P4828T1Step (P4828T1Rotate q b) k.succ = if k = 0 then q 0 else q ((k + b).succ))
            → ((∀ (b : Fin 3), (b ≠ j ↔ ∃ k : Fin 3, P4828T1Step (P4828T1Rotate q b) k.succ =
            q j.succ)) → (
        let arc (b : Fin 3) :=
          P4984T1ClosedGap L (P4828T1Step (P4828T1Rotate q b)) ∩
            Metric.sphere a R
        ∀ (b : Fin (3 : ℕ)), b ≠ j → t ∈ arc b)))))))) ) := by
  classical
  intro L q hq j hj p rad a x R S α t hta htx htseg hfar slot keep arc b hb
  let u := P4828T1Step (P4828T1Rotate q b)
  obtain ⟨k, hk⟩ := (keep b).mp hb
  have hroot : 0 < (q 0).1 := (ProperBandCurvatureStructure q hq).1
  have hslot0 : u (0 : Fin 3).succ = q 0 := by
    simpa [u] using slot b 0
  have hslotk : u k.succ = q j.succ := by simpa [u] using hk
  have hxchild : x ∈ P4909T1ParentPolygon L u := by
    change x ∈ convexHull Real {z | ∃ i : Fin 3, 0 < (u i.succ).1 ∧
      (z = ((u i.succ).2 : Complex) / ((u i.succ).1 : Real) ∨
        ∃ l : Fin 3, (u l.succ).1 = 0 ∧
          z = ⟨if (u l.succ).2 = -1 then L else L + 2,
            (((u i.succ).2 : Complex) / ((u i.succ).1 : Real)).im⟩)}
    apply subset_convexHull Real _
    refine ⟨0, ?_, Or.inl ?_⟩
    · rw [hslot0]
      exact hroot
    · rw [hslot0]
  have hacenter : a = ((u k.succ).2 : Complex) / ((u k.succ).1 : Real) := by
    rw [hslotk]
  have hapos : 0 < (u k.succ).1 := by rw [hslotk]; exact hj
  have hacChild : a ∈ P4909T1ParentPolygon L u := by
    change a ∈ convexHull Real {z | ∃ i : Fin 3, 0 < (u i.succ).1 ∧
      (z = ((u i.succ).2 : Complex) / ((u i.succ).1 : Real) ∨
        ∃ l : Fin 3, (u l.succ).1 = 0 ∧
          z = ⟨if (u l.succ).2 = -1 then L else L + 2,
            (((u i.succ).2 : Complex) / ((u i.succ).1 : Real)).im⟩)}
    exact subset_convexHull Real _ ⟨k, hapos, Or.inl hacenter⟩
  have htChildPoly : t ∈ P4909T1ParentPolygon L u :=
    (convex_convexHull Real _).segment_subset hacChild hxchild htseg
  have hslotOld (i : Fin 3) (hi : i ≠ 0) : u i.succ = q ((i + b).succ) := by
    dsimp [u]
    rw [slot]
    simp [hi]
  have hparentLower (i : Fin 3) (hcurv : 0 < (u i.succ).1) :
      1 / ((u i.succ).1 : Real) ≤
        dist t (((u i.succ).2 : Complex) / ((u i.succ).1 : Real)) := by
    by_cases hi : i = 0
    · subst i
      rw [hslot0] at hcurv ⊢
      simpa [S, rad, p, x] using (le_of_eq htx.symm)
    · have hslt := hslotOld i hi
      have hpos : 0 < (q (i + b).succ).1 := by rw [← hslt]; exact hcurv
      have hbound := hfar (i + b) hpos
      simpa [hslt, p, rad] using hbound
  have htChildGap : t ∈ P4984T1ClosedGap L u := by
    refine ⟨htChildPoly, ?_⟩
    intro i hi
    exact hparentLower i hi
  have htChildArc : t ∈ P4984T1ClosedGap L u ∩ Metric.sphere a R := by
    refine ⟨htChildGap, Metric.mem_sphere.mpr ?_⟩
    simpa [dist_comm] using hta
  simpa [arc, u] using htChildArc

private theorem hposAt481 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (j : Fin 3), ((0 : ℤ) < (q j.succ).1) → (∀ (b : Fin
            (3 : ℕ)), ∀ (k : Fin (3 : ℕ)), (P4828T1Step (P4828T1Rotate q b) k.succ = q
            j.succ) → (0 < (P4828T1Step (P4828T1Rotate q b) k.succ).1)) ) := by
  classical
  intro q j hj b k hk
  rw [hk]
  exact hj

end IncidentArcGeometry

theorem P4984T1IncidentArcs (L : Real)
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hs : P4828T1LineSupport L q)
    (hi : P4828T1Disk (q 0) ⊆ P4828T1Gap L q)
    (j : Fin 3) (hj : 0 < (q j.succ).1) :
    let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
    let r (i : Fin 4) : Real := 1 / ((q i).1 : Real)
    let A := P4984T1ClosedGap L q ∩ Metric.sphere (p j.succ) (r j.succ)
    let arc (b : Fin 3) :=
      P4984T1ClosedGap L (P4828T1Step (P4828T1Rotate q b)) ∩
        Metric.sphere (p j.succ) (r j.succ)
    IsClosed A ∧ IsPreconnected A ∧ A.Nonempty ∧
    (∀ b : Fin 3, b ≠ j ↔
      ∃ k : Fin 3, P4828T1Step (P4828T1Rotate q b) k.succ = q j.succ) ∧
    ∃ t : Complex,
      A = ⋃ b ∈ (Finset.univ.erase j), arc b ∧
      (∀ b ∈ (Finset.univ.erase j),
        IsClosed (arc b) ∧ IsPreconnected (arc b) ∧ t ∈ arc b) ∧
      dist t (p j.succ) = r j.succ ∧
      dist t (p 0) = r 0 ∧
      dist (p j.succ) (p 0) = r j.succ + r 0 := by
-- BODY
  classical
  have circleDistance (v : Fin 4 → CircleCoordinates)
      (hv : ProperBandQuadruple v) (i k : Fin 4) (hik : i ≠ k)
      (hi : 0 < (v i).1) (hk : 0 < (v k).1) := ProperBandCircleCenterDistance v hv i k hik hi hk
  have hparentContactDistance :
      dist (((q j.succ).2 : Complex) / ((q j.succ).1 : Real))
          (((q 0).2 : Complex) / ((q 0).1 : Real)) =
        1 / ((q j.succ).1 : Real) + 1 / ((q 0).1 : Real) :=
            IncidentArcGeometry.hparentContactDistance q hq j hj circleDistance
  let p (i : Fin 4) : Complex := (q i).2 / ((q i).1 : Real)
  let rad (i : Fin 4) : Real := 1 / ((q i).1 : Real)
  let a := p j.succ
  let x := p 0
  let R := rad j.succ
  let S := rad 0
  have hR : 0 < R := by dsimp [R, rad]; exact one_div_pos.mpr (by exact_mod_cast hj)
  have hS := IncidentArcGeometry.hS q hq
  have hax : dist a x = R + S := by
    simpa [a, x, p, R, S, rad] using hparentContactDistance
  let α := R / (R + S)
  have hα : 0 < α := div_pos hR (add_pos hR hS)
  have hαlt : α < 1 := (div_lt_one (add_pos hR hS)).2 (by linarith)
  have hαmul := IncidentArcGeometry.hαmul q j hR hS
  have hcompmul := IncidentArcGeometry.hcompmul q j hαmul
  let t := a + α • (x - a)
  have hnormax : ‖x - a‖ = R + S := by
    simpa [dist_eq_norm, norm_sub_rev] using hax
  have hta := IncidentArcGeometry.hta q j hα hαmul hnormax
  have htx := IncidentArcGeometry.htx q j hαlt hcompmul hnormax
  have hxDisk := IncidentArcGeometry.hxDisk q hS
  have hxGap := hi hxDisk
  have hxPoly : x ∈ P4909T1ParentPolygon L q :=
    interior_subset (by simpa [P4828T1Gap, x, p] using hxGap.1)
  have haPoly := IncidentArcGeometry.haPoly L q j hj
  have htseg := IncidentArcGeometry.htseg q j hα hαlt
  have htPoly : t ∈ P4909T1ParentPolygon L q :=
    (convex_convexHull Real _).segment_subset haPoly hxPoly htseg
  have hfar (k : Fin 3) (hk : 0 < (q k.succ).1) := IncidentArcGeometry.hfar q hq j hj
      circleDistance hta k hk
  have htGap := IncidentArcGeometry.htGap L q j htPoly hfar
  have htA := IncidentArcGeometry.htA L q j hta htGap
  let foot (i k : Fin 3) : Complex :=
    ⟨if (q k.succ).2 = -1 then L else L + 2, (p i.succ).im⟩
  let V : Set Complex := {z | ∃ i : Fin 3, 0 < (q i.succ).1 ∧
    (z = p i.succ ∨ ∃ k : Fin 3, (q k.succ).1 = 0 ∧ z = foot i k)}
  let f : Fin 3 × Fin 3 → Complex := fun ij =>
    if (q ij.2.succ).1 = 0 then foot ij.1 ij.2 else p ij.1.succ
  have hVsub := IncidentArcGeometry.hVsub L q j hj
  have hVfinite : V.Finite := (Set.finite_range f).subset hVsub
  have hParentClosed := IncidentArcGeometry.hParentClosed L q hVfinite
  have hClosedGap := @IncidentArcGeometry.hClosedGap L q hParentClosed
  have hAclosed : IsClosed (P4984T1ClosedGap L q ∩ Metric.sphere a R) :=
    hClosedGap.inter Metric.isClosed_sphere
  have hANonempty : (P4984T1ClosedGap L q ∩ Metric.sphere a R).Nonempty :=
    ⟨t, htA⟩
  have slot (b k : Fin 3) := IncidentArcGeometry.slot q b k
  have keep (b : Fin 3) := @IncidentArcGeometry.keep L q hq j hj hparentContactDistance hR hax hα
      hαlt hαmul hcompmul hnormax hta htx haPoly htseg htPoly hfar htGap htA hAclosed hANonempty
          slot b
  have closedGapOfParent (u : Fin 4 → CircleCoordinates) (m : Fin 3)
      (hm : 0 < (u m.succ).1) := IncidentArcGeometry.closedGapOfParent L u m hm
  let arc (b : Fin 3) :=
    P4984T1ClosedGap L (P4828T1Step (P4828T1Rotate q b)) ∩
      Metric.sphere a R
  have hchildCover := IncidentArcGeometry.hchildCover L q hq hs hi j hax
  have hchildSub (b : Fin 3) := IncidentArcGeometry.hchildSub L q hq hs hi j b
  have hAllUnion := IncidentArcGeometry.hAllUnion L q j hchildCover hchildSub
  have hNotretaining := IncidentArcGeometry.hNotretaining L q hq hs j hj
  have hEraseUnion := IncidentArcGeometry.hEraseUnion L q j hNotretaining
  have hchildArcClosed (b : Fin 3) (hb : b ≠ j) := IncidentArcGeometry.hchildArcClosed L q j hj
      keep closedGapOfParent b hb
  have hchildArcContains (b : Fin 3) (hb : b ≠ j) := IncidentArcGeometry.hchildArcContains L q hq
      j hj hta htx htseg hfar slot keep b hb
  dsimp only
  refine ⟨hAclosed, ?_, hANonempty, keep, t, ?_, ?_, ?_, ?_⟩
  · exact P5050T1ParentSphereSection L q hq hs j hj
  · exact hAllUnion.trans hEraseUnion.symm
  · intro b hb
    have hb' : b ≠ j := (Finset.mem_erase.mp hb).1
    refine ⟨hchildArcClosed b hb', ?_, hchildArcContains b hb'⟩
    obtain ⟨k, hk⟩ := (keep b).mp hb'
    have hpos := IncidentArcGeometry.hposAt481 q j hj b k hk
    obtain ⟨hproper, hsupport⟩ := P4828T1ConstructorSupport L q hq hs b
    have hc := P5050T1ParentSphereSection L _ hproper hsupport k hpos
    rw [hk] at hc
    exact hc
  · exact hta
  · exact ⟨htx, hparentContactDistance⟩

end ApollonianSuperharmonic

end
