/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Positivity

public import LeanPool.ApollonianSuperharmonic.P4909T1ParentEdges
public import LeanPool.ApollonianSuperharmonic.P4828T1Rotate
public import LeanPool.ApollonianSuperharmonic.P4828T1Step
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Topology.MetricSpace.Lipschitz
public import LeanPool.ApollonianSuperharmonic.P4909T1ParentPolygon
public import Mathlib.Analysis.Complex.Norm

-- [TABLET NODE: P4909T1TriangleFan]

/-!
# P4909T1TriangleFan

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TriangleFanConstruction

private theorem normRealSmul (r : ℝ) (z : ℂ) : ‖r • z‖ = |r| * ‖z‖ := by
  classical
  rw [Complex.real_smul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]

private theorem smallStep (z d : ℂ) (ε : ℝ) (hε : 0 < ε) :
      ∃ t : ℝ, 0 < t ∧ t • d + z ∈ Metric.ball z ε := by
  classical
  have normRealSmul (r : ℝ) (z : ℂ) : ‖r • z‖ = |r| * ‖z‖ := normRealSmul r z
  let t := ε / (‖d‖ + 1)
  have hd : 0 < ‖d‖ + 1 := by positivity
  have ht : 0 < t := div_pos hε hd
  refine ⟨t, ht, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right,
    normRealSmul, abs_of_pos ht]
  dsimp [t]
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hd).mpr
  nlinarith

private theorem contRe : Continuous (fun z : ℂ => z.re) := by
  classical
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.mk_one
  intro z w
  simpa only [Real.dist_eq, ← Complex.sub_re, Complex.dist_eq] using
    Complex.abs_re_le_norm (z - w)

private theorem contIm : Continuous (fun z : ℂ => z.im) := by
  classical
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.mk_one
  intro z w
  simpa only [Real.dist_eq, ← Complex.sub_im, Complex.dist_eq] using
    Complex.abs_im_le_norm (z - w)

private theorem affineContinuous (f : ℂ →ᵃ[ℝ] ℝ) : Continuous f := by
  classical
  have contRe : Continuous (fun z : ℂ => z.re) := contRe
  have contIm : Continuous (fun z : ℂ => z.im) := contIm
  have hf (z : ℂ) : f z = z.re * f.linear 1 + z.im * f.linear Complex.I + f 0 := by
    have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
      apply Complex.ext <;> simp [Complex.real_smul]
    calc
      f z = f.linear z + f 0 := by
        simpa only [vadd_eq_add, add_zero] using f.map_vadd 0 z
      _ = z.re * f.linear 1 + z.im * f.linear Complex.I + f 0 := by
        conv_lhs => arg 1; rw [hz]
        simp only [map_add, map_smul, smul_eq_mul]
  have hc := ((contRe.mul_const (f.linear 1)).add
    (contIm.mul_const (f.linear Complex.I))).add_const (f 0)
  exact (show (fun z => z.re * f.linear 1 + z.im * f.linear Complex.I + f 0) = f
    from funext fun z => (hf z).symm) ▸ hc

private theorem affineShift (f : ℂ →ᵃ[ℝ] ℝ) (z a b : ℂ) (t : ℝ) :
      f (t • (a - b) + z) = t * (f a - f b) + f z := by
  classical
  change f (t • (a -ᵥ b) +ᵥ z) = _
  rw [f.map_vadd, map_smul, f.linear_apply_vsub]
  rfl

private theorem interiorHull (D : AffineBasis (Fin 3) ℝ ℂ) :
      interior (convexHull ℝ (Set.range D)) = {z | ∀ i, 0 < D.coord i z} := by
  classical
  have smallStep (z d : ℂ) (ε : ℝ) (hε : 0 < ε) :
      ∃ t : ℝ, 0 < t ∧ t • d + z ∈ Metric.ball z ε := smallStep z d ε hε
  have affineContinuous (f : ℂ →ᵃ[ℝ] ℝ) : Continuous f := affineContinuous f
  have affineShift (f : ℂ →ᵃ[ℝ] ℝ) (z a b : ℂ) (t : ℝ) :
      f (t • (a - b) + z) = t * (f a - f b) + f z := affineShift f z a b t
  apply Set.Subset.antisymm
  · intro z hz i
    have hc : ∀ i, 0 ≤ D.coord i z :=
      (Set.ext_iff.mp D.convexHull_eq_nonneg_coord z).mp (interior_subset hz)
    by_contra hi
    have hi0 : D.coord i z = 0 := le_antisymm (not_lt.mp hi) (hc i)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
    obtain ⟨j, hji⟩ := exists_ne i
    obtain ⟨t, ht, hstep⟩ := smallStep z (D j - D i) ε hε
    have hnonneg : 0 ≤ D.coord i (t • (D j - D i) + z) :=
      (Set.ext_iff.mp D.convexHull_eq_nonneg_coord _).mp (hball hstep) i
    rw [affineShift, D.coord_apply_ne hji.symm, D.coord_apply_eq, hi0] at hnonneg
    linarith
  · have hop : IsOpen {z | ∀ i, 0 < D.coord i z} := by
      rw [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (affineContinuous _)
    apply interior_maximal _ hop
    intro z hz
    exact (Set.ext_iff.mp D.convexHull_eq_nonneg_coord z).mpr (fun i => (hz i).le)

private theorem spanOfInterior (S : Set ℂ) (x : ℂ)
      (hx : x ∈ interior (convexHull ℝ S)) : affineSpan ℝ S = ⊤ := by
  classical
  have smallStep (z d : ℂ) (ε : ℝ) (hε : 0 < ε) :
      ∃ t : ℝ, 0 < t ∧ t • d + z ∈ Metric.ball z ε := smallStep z d ε hε
  apply top_unique
  intro z _
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  obtain ⟨t, ht, hstep⟩ := smallStep x (z - x) ε hε
  have hxS := convexHull_subset_affineSpan (𝕜 := ℝ) S (interior_subset hx)
  have hyS := convexHull_subset_affineSpan (𝕜 := ℝ) S (hball hstep)
  have hzS := (affineSpan ℝ S).smul_vsub_vadd_mem t⁻¹ hyS hxS hxS
  change t⁻¹ • ((t • (z - x) + x) - x) + x ∈ affineSpan ℝ S at hzS
  simpa only [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ ht.ne', one_smul,
    sub_add_cancel] using hzS

private noncomputable abbrev p (q : Fin 4 → CircleCoordinates) (i : Fin 4) : ℂ := by
  classical
  exact (q i).2 / ((q i).1 : ℝ)

private noncomputable abbrev s (q : Fin 4 → CircleCoordinates) (b : Fin 3) := P4828T1Step
    (P4828T1Rotate q b)

private noncomputable abbrev P (L : ℝ) (q : Fin 4 → CircleCoordinates) := P4909T1ParentPolygon L q

private noncomputable abbrev F (L : ℝ) (q : Fin 4 → CircleCoordinates) (b : Fin 3) :=
    P4909T1ParentPolygon L ((s q) b)

private noncomputable abbrev v (q : Fin 4 → CircleCoordinates) : Fin 3 → ℂ := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  exact fun i => p i.succ

private theorem parentHull (L : ℝ) (t : Fin 4 → CircleCoordinates)
      (ht : ∀ i : Fin 3, 0 < (t i.succ).1) :
      P4909T1ParentPolygon L t =
        convexHull ℝ (Set.range fun i : Fin 3 =>
          ((t i.succ).2 : ℂ) / ((t i.succ).1 : ℝ)) := by
  classical
  apply congrArg (convexHull ℝ)
  ext z
  constructor
  · rintro ⟨i, hi, hz | ⟨k, hk, hz⟩⟩
    · exact ⟨i, hz.symm⟩
    · exact False.elim ((ne_of_gt (ht k)) hk)
  · rintro ⟨i, rfl⟩
    exact ⟨i, ht i, Or.inl rfl⟩

private theorem hP (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q i).1) : (P
    L q) = convexHull ℝ (Set.range (v q)) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let P := P4909T1ParentPolygon L q
  let v : Fin 3 → ℂ := fun i => p i.succ
  have parentHull (t : Fin 4 → CircleCoordinates)
      (ht : ∀ i : Fin 3, 0 < (t i.succ).1) :
      P4909T1ParentPolygon L t =
        convexHull ℝ (Set.range fun i : Fin 3 =>
          ((t i.succ).2 : ℂ) / ((t i.succ).1 : ℝ)) := parentHull L t ht
  change (P = convexHull ℝ (Set.range v))
  exact parentHull q (fun i => hpos i.succ)

private theorem hxmem (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q i).1)
    (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) : (p q) 0 ∈
    interior (convexHull ℝ (Set.range (v q))) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let P := P4909T1ParentPolygon L q
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hP : P = convexHull ℝ (Set.range v) := hP L q hpos
  change (p 0 ∈ interior (convexHull ℝ (Set.range v)))
  rw [← hP]
  exact hinside

private theorem hspan (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q i).1)
    (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) :
    affineSpan ℝ (Set.range (v q)) = ⊤ := by
  classical
  have spanOfInterior (S : Set ℂ) (x : ℂ)
      (hx : x ∈ interior (convexHull ℝ S)) : affineSpan ℝ S = ⊤ := spanOfInterior S x hx
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hxmem : p 0 ∈ interior (convexHull ℝ (Set.range v)) := hxmem L q hpos hinside
  change (affineSpan ℝ (Set.range v) = ⊤)
  exact spanOfInterior (Set.range v) (p 0) hxmem

private theorem hvspan (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q i).1)
    (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) :
    vectorSpan ℝ (Set.range (v q)) = ⊤ := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let P := P4909T1ParentPolygon L q
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hspan : affineSpan ℝ (Set.range v) = ⊤ := hspan L q hpos hinside
  change (vectorSpan ℝ (Set.range v) = ⊤)
  exact AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top
      (k := ℝ) (V := ℂ) (P := ℂ) hspan

private theorem hind (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q i).1)
    (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) :
    AffineIndependent ℝ (v q) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let P := P4909T1ParentPolygon L q
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hvspan : vectorSpan ℝ (Set.range v) = ⊤ := hvspan L q hpos hinside
  change (AffineIndependent ℝ v)
  apply (affineIndependent_iff_finrank_vectorSpan_eq
    (k := ℝ) (V := ℂ) (P := ℂ) v (n := 2) (by norm_num)).2
  rw [hvspan, finrank_top, Complex.finrank_real_complex]

private noncomputable abbrev A (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 <
    (q i).1) (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) :
    AffineBasis (Fin 3) ℝ ℂ := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hspan : affineSpan ℝ (Set.range v) = ⊤ := hspan L q hpos hinside
  have hind : AffineIndependent ℝ v := hind L q hpos hinside
  exact ⟨v, hind, hspan⟩

private theorem hmem (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q i).1)
    (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (z : ℂ) : z
    ∈ (P L q) ↔ ∀ i, 0 ≤ (A L q hpos hinside).coord i z := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let P := P4909T1ParentPolygon L q
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hP : P = convexHull ℝ (Set.range v) := hP L q hpos
  have hspan : affineSpan ℝ (Set.range v) = ⊤ := hspan L q hpos hinside
  have hind : AffineIndependent ℝ v := hind L q hpos hinside
  let A : AffineBasis (Fin 3) ℝ ℂ := ⟨v, hind, hspan⟩
  change (z ∈ P ↔ ∀ i, 0 ≤ A.coord i z)
  rw [hP]
  exact Set.ext_iff.mp A.convexHull_eq_nonneg_coord z

private theorem hint (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q i).1)
    (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (z : ℂ) : z
    ∈ interior (P L q) ↔ ∀ i, 0 < (A L q hpos hinside).coord i z := by
  classical
  have interiorHull (D : AffineBasis (Fin 3) ℝ ℂ) :
      interior (convexHull ℝ (Set.range D)) = {z | ∀ i, 0 < D.coord i z} := interiorHull D
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let P := P4909T1ParentPolygon L q
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hP : P = convexHull ℝ (Set.range v) := hP L q hpos
  have hspan : affineSpan ℝ (Set.range v) = ⊤ := hspan L q hpos hinside
  have hind : AffineIndependent ℝ v := hind L q hpos hinside
  let A : AffineBasis (Fin 3) ℝ ℂ := ⟨v, hind, hspan⟩
  change (z ∈ interior P ↔ ∀ i, 0 < A.coord i z)
  rw [hP]
  exact Set.ext_iff.mp (interiorHull A) z

private noncomputable abbrev alpha (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0
    < (q i).1) (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q))
    (i : Fin 3) : ℝ := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hspan : affineSpan ℝ (Set.range v) = ⊤ := hspan L q hpos hinside
  have hind : AffineIndependent ℝ v := hind L q hpos hinside
  let A : AffineBasis (Fin 3) ℝ ℂ := ⟨v, hind, hspan⟩
  exact A.coord i (p 0)

private theorem alphaPos (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q
    i).1) (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (i :
    Fin 3) : 0 < (alpha L q hpos hinside) i := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let P := P4909T1ParentPolygon L q
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hspan : affineSpan ℝ (Set.range v) = ⊤ := hspan L q hpos hinside
  have hind : AffineIndependent ℝ v := hind L q hpos hinside
  let A : AffineBasis (Fin 3) ℝ ℂ := ⟨v, hind, hspan⟩
  have hint (z : ℂ) : z ∈ interior P ↔ ∀ i, 0 < A.coord i z := hint L q hpos hinside z
  let alpha (i : Fin 3) : ℝ := A.coord i (p 0)
  change (0 < alpha i)
  exact (hint (p 0)).mp hinside i

private noncomputable abbrev u (q : Fin 4 → CircleCoordinates) (b : Fin 3) : Fin 3 → ℂ := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let v : Fin 3 → ℂ := fun i => p i.succ
  exact Function.update v b (p 0)

private theorem huind (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q i).1)
    (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (b : Fin 3)
    : AffineIndependent ℝ ((u q) b) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hspan : affineSpan ℝ (Set.range v) = ⊤ := hspan L q hpos hinside
  have hind : AffineIndependent ℝ v := hind L q hpos hinside
  let A : AffineBasis (Fin 3) ℝ ℂ := ⟨v, hind, hspan⟩
  let alpha (i : Fin 3) : ℝ := A.coord i (p 0)
  have alphaPos (i : Fin 3) : 0 < alpha i := alphaPos L q hpos hinside i
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  change (AffineIndependent ℝ (u b))
  apply hind.affineIndependent_update_of_notMem_affineSpan
  intro hx
  have heq : Set.EqOn (A.coord b) (AffineMap.const ℝ ℂ (0 : ℝ))
      (v '' {i | i ≠ b}) := by
    rintro _ ⟨i, hi, rfl⟩
    exact A.coord_apply_ne hi.symm
  have hz := AffineMap.eqOn_affineSpan heq hx
  exact (ne_of_gt (alphaPos b)) hz

private theorem hutot (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q i).1)
    (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (b : Fin 3)
    : affineSpan ℝ (Set.range ((u q) b)) = ⊤ := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let v : Fin 3 → ℂ := fun i => p i.succ
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  have huind (b : Fin 3) : AffineIndependent ℝ (u b) := huind L q hpos hinside b
  change (affineSpan ℝ (Set.range (u b)) = ⊤)
  apply (huind b).affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  rw [Complex.finrank_real_complex]
  rfl

private noncomputable abbrev B (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 <
    (q i).1) (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (b
    : Fin 3) : AffineBasis (Fin 3) ℝ ℂ := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let v : Fin 3 → ℂ := fun i => p i.succ
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  have huind (b : Fin 3) : AffineIndependent ℝ (u b) := huind L q hpos hinside b
  have hutot (b : Fin 3) : affineSpan ℝ (Set.range (u b)) = ⊤ := hutot L q hpos hinside b
  exact ⟨u b, huind b, hutot b⟩

private theorem hBself (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q i).1)
    (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (b : Fin 3)
    : (B L q hpos hinside) b b = (p q) 0 := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let v : Fin 3 → ℂ := fun i => p i.succ
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  have huind (b : Fin 3) : AffineIndependent ℝ (u b) := huind L q hpos hinside b
  have hutot (b : Fin 3) : affineSpan ℝ (Set.range (u b)) = ⊤ := hutot L q hpos hinside b
  let B (b : Fin 3) : AffineBasis (Fin 3) ℝ ℂ := ⟨u b, huind b, hutot b⟩
  change (B b b = p 0)
  change Function.update v b (p 0) b = p 0
  simp

private theorem hBother (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q i).1)
    (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (b i : Fin
    3) (hi : i ≠ b) : (B L q hpos hinside) b i = (v q) i := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let v : Fin 3 → ℂ := fun i => p i.succ
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  have huind (b : Fin 3) : AffineIndependent ℝ (u b) := huind L q hpos hinside b
  have hutot (b : Fin 3) : affineSpan ℝ (Set.range (u b)) = ⊤ := hutot L q hpos hinside b
  let B (b : Fin 3) : AffineBasis (Fin 3) ℝ ℂ := ⟨u b, huind b, hutot b⟩
  change (B b i = v i)
  change Function.update v b (p 0) i = v i
  simp [hi]

private theorem hparents (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q i).1) (b :
    Fin 3) : ∀ i : Fin 3, 0 < ((s q) b i.succ).1 := by
  classical
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  change (∀ i : Fin 3, 0 < (s b i.succ).1)
  fin_cases b <;> intro i <;> fin_cases i <;> exact hpos _

private theorem hparentPoint (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q
    i).1) (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (b j
    : Fin 3) :
      (((s q) b j.succ).2 : ℂ) / (((s q) b j.succ).1 : ℝ) = (B L q hpos hinside) b (j + b) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let v : Fin 3 → ℂ := fun i => p i.succ
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  have huind (b : Fin 3) : AffineIndependent ℝ (u b) := huind L q hpos hinside b
  have hutot (b : Fin 3) : affineSpan ℝ (Set.range (u b)) = ⊤ := hutot L q hpos hinside b
  let B (b : Fin 3) : AffineBasis (Fin 3) ℝ ℂ := ⟨u b, huind b, hutot b⟩
  change (((s b j.succ).2 : ℂ) / ((s b j.succ).1 : ℝ) = B b (j + b))
  fin_cases b <;> fin_cases j <;> rfl

private theorem hchild (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q i).1)
    (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (b : Fin 3)
    : (F L q) b = convexHull ℝ (Set.range ((B L q hpos hinside) b)) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
  let v : Fin 3 → ℂ := fun i => p i.succ
  have parentHull (t : Fin 4 → CircleCoordinates)
      (ht : ∀ i : Fin 3, 0 < (t i.succ).1) :
      P4909T1ParentPolygon L t =
        convexHull ℝ (Set.range fun i : Fin 3 =>
          ((t i.succ).2 : ℂ) / ((t i.succ).1 : ℝ)) := parentHull L t ht
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  have huind (b : Fin 3) : AffineIndependent ℝ (u b) := huind L q hpos hinside b
  have hutot (b : Fin 3) : affineSpan ℝ (Set.range (u b)) = ⊤ := hutot L q hpos hinside b
  let B (b : Fin 3) : AffineBasis (Fin 3) ℝ ℂ := ⟨u b, huind b, hutot b⟩
  have hparents (b : Fin 3) : ∀ i : Fin 3, 0 < (s b i.succ).1 := hparents q hpos b
  have hparentPoint (b j : Fin 3) :
      ((s b j.succ).2 : ℂ) / ((s b j.succ).1 : ℝ) = B b (j + b) := hparentPoint L q hpos hinside b j
  change (F b = convexHull ℝ (Set.range (B b)))
  rw [show F b = P4909T1ParentPolygon L (s b) from rfl, parentHull (s b) (hparents b)]
  apply congrArg (convexHull ℝ)
  ext z
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j + b, (hparentPoint b j).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i - b, by simpa using hparentPoint b (i - b)⟩

private theorem hBmem (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q i).1)
    (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (b : Fin 3)
    (z : ℂ) : z ∈ (F L q) b ↔ ∀ i, 0 ≤ ((B L q hpos hinside) b).coord i z := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
  let v : Fin 3 → ℂ := fun i => p i.succ
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  have huind (b : Fin 3) : AffineIndependent ℝ (u b) := huind L q hpos hinside b
  have hutot (b : Fin 3) : affineSpan ℝ (Set.range (u b)) = ⊤ := hutot L q hpos hinside b
  let B (b : Fin 3) : AffineBasis (Fin 3) ℝ ℂ := ⟨u b, huind b, hutot b⟩
  have hchild (b : Fin 3) : F b = convexHull ℝ (Set.range (B b)) := hchild L q hpos hinside b
  change (z ∈ F b ↔ ∀ i, 0 ≤ (B b).coord i z)
  rw [hchild]
  exact Set.ext_iff.mp (B b).convexHull_eq_nonneg_coord z

private theorem hBint (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q i).1)
    (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (b : Fin 3)
    (z : ℂ) :
      z ∈ interior ((F L q) b) ↔ ∀ i, 0 < ((B L q hpos hinside) b).coord i z := by
  classical
  have interiorHull (D : AffineBasis (Fin 3) ℝ ℂ) :
      interior (convexHull ℝ (Set.range D)) = {z | ∀ i, 0 < D.coord i z} := interiorHull D
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
  let v : Fin 3 → ℂ := fun i => p i.succ
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  have huind (b : Fin 3) : AffineIndependent ℝ (u b) := huind L q hpos hinside b
  have hutot (b : Fin 3) : affineSpan ℝ (Set.range (u b)) = ⊤ := hutot L q hpos hinside b
  let B (b : Fin 3) : AffineBasis (Fin 3) ℝ ℂ := ⟨u b, huind b, hutot b⟩
  have hchild (b : Fin 3) : F b = convexHull ℝ (Set.range (B b)) := hchild L q hpos hinside b
  change (z ∈ interior (F b) ↔ ∀ i, 0 < (B b).coord i z)
  rw [hchild]
  exact Set.ext_iff.mp (interiorHull (B b)) z

private theorem coordSelf (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q
    i).1) (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (b :
    Fin 3) :
      (A L q hpos hinside).coord b = (alpha L q hpos hinside) b • ((B L q hpos hinside) b).coord
          b := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hspan : affineSpan ℝ (Set.range v) = ⊤ := hspan L q hpos hinside
  have hind : AffineIndependent ℝ v := hind L q hpos hinside
  let A : AffineBasis (Fin 3) ℝ ℂ := ⟨v, hind, hspan⟩
  let alpha (i : Fin 3) : ℝ := A.coord i (p 0)
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  have huind (b : Fin 3) : AffineIndependent ℝ (u b) := huind L q hpos hinside b
  have hutot (b : Fin 3) : affineSpan ℝ (Set.range (u b)) = ⊤ := hutot L q hpos hinside b
  let B (b : Fin 3) : AffineBasis (Fin 3) ℝ ℂ := ⟨u b, huind b, hutot b⟩
  have hBself (b : Fin 3) : B b b = p 0 := hBself L q hpos hinside b
  have hBother (b i : Fin 3) (hi : i ≠ b) : B b i = v i := hBother L q hpos hinside b i hi
  change (A.coord b = alpha b • (B b).coord b)
  apply AffineMap.ext_on (B b).tot
  rintro _ ⟨i, rfl⟩
  change A.coord b (B b i) = alpha b * (B b).coord b (B b i)
  by_cases hi : i = b
  · subst i
    rw [(B b).coord_apply_eq, mul_one, hBself]
  · rw [(B b).coord_apply_ne (Ne.symm hi), mul_zero, hBother b i hi]
    exact A.coord_apply_ne (Ne.symm hi)

private theorem coordOther (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q
    i).1) (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (b i
    : Fin 3) (hi : i ≠ b) :
      (A L q hpos hinside).coord i = (alpha L q hpos hinside) i • ((B L q hpos hinside) b).coord
          b + ((B L q hpos hinside) b).coord i := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hspan : affineSpan ℝ (Set.range v) = ⊤ := hspan L q hpos hinside
  have hind : AffineIndependent ℝ v := hind L q hpos hinside
  let A : AffineBasis (Fin 3) ℝ ℂ := ⟨v, hind, hspan⟩
  let alpha (i : Fin 3) : ℝ := A.coord i (p 0)
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  have huind (b : Fin 3) : AffineIndependent ℝ (u b) := huind L q hpos hinside b
  have hutot (b : Fin 3) : affineSpan ℝ (Set.range (u b)) = ⊤ := hutot L q hpos hinside b
  let B (b : Fin 3) : AffineBasis (Fin 3) ℝ ℂ := ⟨u b, huind b, hutot b⟩
  have hBself (b : Fin 3) : B b b = p 0 := hBself L q hpos hinside b
  have hBother (b i : Fin 3) (hi : i ≠ b) : B b i = v i := hBother L q hpos hinside b i hi
  change (A.coord i = alpha i • (B b).coord b + (B b).coord i)
  apply AffineMap.ext_on (B b).tot
  rintro _ ⟨j, rfl⟩
  change A.coord i (B b j) =
    alpha i * (B b).coord b (B b j) + (B b).coord i (B b j)
  by_cases hj : j = b
  · subst j
    rw [(B b).coord_apply_eq, (B b).coord_apply_ne hi, mul_one, add_zero, hBself]
  · rw [(B b).coord_apply_ne (Ne.symm hj), mul_zero, zero_add,
      (B b).coord_apply, hBother b j hj]
    exact A.coord_apply i j

private theorem coordSelfApply (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 <
    (q i).1) (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (b
    : Fin 3) (z : ℂ) :
      (A L q hpos hinside).coord b z = (alpha L q hpos hinside) b * ((B L q hpos hinside)
          b).coord b z := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hspan : affineSpan ℝ (Set.range v) = ⊤ := hspan L q hpos hinside
  have hind : AffineIndependent ℝ v := hind L q hpos hinside
  let A : AffineBasis (Fin 3) ℝ ℂ := ⟨v, hind, hspan⟩
  let alpha (i : Fin 3) : ℝ := A.coord i (p 0)
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  have huind (b : Fin 3) : AffineIndependent ℝ (u b) := huind L q hpos hinside b
  have hutot (b : Fin 3) : affineSpan ℝ (Set.range (u b)) = ⊤ := hutot L q hpos hinside b
  let B (b : Fin 3) : AffineBasis (Fin 3) ℝ ℂ := ⟨u b, huind b, hutot b⟩
  have coordSelf (b : Fin 3) :
      A.coord b = alpha b • (B b).coord b := coordSelf L q hpos hinside b
  change (A.coord b z = alpha b * (B b).coord b z)
  rw [coordSelf b]
  rfl

private theorem coordOtherApply (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 <
    (q i).1) (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (b
    i : Fin 3) (hi : i ≠ b) (z : ℂ) :
      (A L q hpos hinside).coord i z = (alpha L q hpos hinside) i * ((B L q hpos hinside)
          b).coord b z + ((B L q hpos hinside) b).coord i z := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hspan : affineSpan ℝ (Set.range v) = ⊤ := hspan L q hpos hinside
  have hind : AffineIndependent ℝ v := hind L q hpos hinside
  let A : AffineBasis (Fin 3) ℝ ℂ := ⟨v, hind, hspan⟩
  let alpha (i : Fin 3) : ℝ := A.coord i (p 0)
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  have huind (b : Fin 3) : AffineIndependent ℝ (u b) := huind L q hpos hinside b
  have hutot (b : Fin 3) : affineSpan ℝ (Set.range (u b)) = ⊤ := hutot L q hpos hinside b
  let B (b : Fin 3) : AffineBasis (Fin 3) ℝ ℂ := ⟨u b, huind b, hutot b⟩
  have coordOther (b i : Fin 3) (hi : i ≠ b) :
      A.coord i = alpha i • (B b).coord b + (B b).coord i := coordOther L q hpos hinside b i hi
  change (A.coord i z = alpha i * (B b).coord b z + (B b).coord i z)
  rw [coordOther b i hi]
  rfl

private theorem childSubset (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q
    i).1) (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (b :
    Fin 3) : (F L q) b ⊆ (P L q) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let P := P4909T1ParentPolygon L q
  let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hspan : affineSpan ℝ (Set.range v) = ⊤ := hspan L q hpos hinside
  have hind : AffineIndependent ℝ v := hind L q hpos hinside
  let A : AffineBasis (Fin 3) ℝ ℂ := ⟨v, hind, hspan⟩
  have hmem (z : ℂ) : z ∈ P ↔ ∀ i, 0 ≤ A.coord i z := hmem L q hpos hinside z
  let alpha (i : Fin 3) : ℝ := A.coord i (p 0)
  have alphaPos (i : Fin 3) : 0 < alpha i := alphaPos L q hpos hinside i
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  have huind (b : Fin 3) : AffineIndependent ℝ (u b) := huind L q hpos hinside b
  have hutot (b : Fin 3) : affineSpan ℝ (Set.range (u b)) = ⊤ := hutot L q hpos hinside b
  let B (b : Fin 3) : AffineBasis (Fin 3) ℝ ℂ := ⟨u b, huind b, hutot b⟩
  have hBmem (b : Fin 3) (z : ℂ) : z ∈ F b ↔ ∀ i, 0 ≤ (B b).coord i z := hBmem L q hpos hinside b z
  have coordSelfApply (b : Fin 3) (z : ℂ) :
      A.coord b z = alpha b * (B b).coord b z := coordSelfApply L q hpos hinside b z
  have coordOtherApply (b i : Fin 3) (hi : i ≠ b) (z : ℂ) :
      A.coord i z = alpha i * (B b).coord b z + (B b).coord i z := coordOtherApply L q hpos
          hinside b i hi z
  change (F b ⊆ P)
  intro z hz
  have hc := (hBmem b z).mp hz
  apply (hmem z).mpr
  intro i
  by_cases hi : i = b
  · subst i
    rw [coordSelfApply]
    exact mul_nonneg (alphaPos b).le (hc b)
  · rw [coordOtherApply b i hi]
    exact add_nonneg (mul_nonneg (alphaPos i).le (hc b)) (hc i)

private theorem omittedNotIn (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q
    i).1) (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (b :
    Fin 3) : (p q) b.succ ∉ (F L q) b := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hspan : affineSpan ℝ (Set.range v) = ⊤ := hspan L q hpos hinside
  have hind : AffineIndependent ℝ v := hind L q hpos hinside
  let A : AffineBasis (Fin 3) ℝ ℂ := ⟨v, hind, hspan⟩
  let alpha (i : Fin 3) : ℝ := A.coord i (p 0)
  have alphaPos (i : Fin 3) : 0 < alpha i := alphaPos L q hpos hinside i
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  have huind (b : Fin 3) : AffineIndependent ℝ (u b) := huind L q hpos hinside b
  have hutot (b : Fin 3) : affineSpan ℝ (Set.range (u b)) = ⊤ := hutot L q hpos hinside b
  let B (b : Fin 3) : AffineBasis (Fin 3) ℝ ℂ := ⟨u b, huind b, hutot b⟩
  have hBmem (b : Fin 3) (z : ℂ) : z ∈ F b ↔ ∀ i, 0 ≤ (B b).coord i z := hBmem L q hpos hinside b z
  have coordSelfApply (b : Fin 3) (z : ℂ) :
      A.coord b z = alpha b * (B b).coord b z := coordSelfApply L q hpos hinside b z
  have coordOtherApply (b i : Fin 3) (hi : i ≠ b) (z : ℂ) :
      A.coord i z = alpha i * (B b).coord b z + (B b).coord i z := coordOtherApply L q hpos
          hinside b i hi z
  change (p b.succ ∉ F b)
  intro hz
  have hc := (hBmem b (v b)).mp hz
  obtain ⟨i, hi⟩ := exists_ne b
  have hs := coordSelfApply b (v b)
  have ho := coordOtherApply b i hi (v b)
  rw [show A.coord b (v b) = 1 from A.coord_apply_eq b] at hs
  rw [show A.coord i (v b) = 0 from A.coord_apply_ne hi] at ho
  have hle : (B b).coord b (v b) ≤ 0 := by
    nlinarith [alphaPos i, hc i]
  nlinarith [alphaPos b]

private theorem childCover (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q
    i).1) (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (z :
    ℂ) (hz : z ∈ (P L q)) : ∃ b : Fin 3, z ∈ (F L q) b := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let P := P4909T1ParentPolygon L q
  let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hspan : affineSpan ℝ (Set.range v) = ⊤ := hspan L q hpos hinside
  have hind : AffineIndependent ℝ v := hind L q hpos hinside
  let A : AffineBasis (Fin 3) ℝ ℂ := ⟨v, hind, hspan⟩
  have hmem (z : ℂ) : z ∈ P ↔ ∀ i, 0 ≤ A.coord i z := hmem L q hpos hinside z
  let alpha (i : Fin 3) : ℝ := A.coord i (p 0)
  have alphaPos (i : Fin 3) : 0 < alpha i := alphaPos L q hpos hinside i
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  have huind (b : Fin 3) : AffineIndependent ℝ (u b) := huind L q hpos hinside b
  have hutot (b : Fin 3) : affineSpan ℝ (Set.range (u b)) = ⊤ := hutot L q hpos hinside b
  let B (b : Fin 3) : AffineBasis (Fin 3) ℝ ℂ := ⟨u b, huind b, hutot b⟩
  have hBmem (b : Fin 3) (z : ℂ) : z ∈ F b ↔ ∀ i, 0 ≤ (B b).coord i z := hBmem L q hpos hinside b z
  have coordSelfApply (b : Fin 3) (z : ℂ) :
      A.coord b z = alpha b * (B b).coord b z := coordSelfApply L q hpos hinside b z
  have coordOtherApply (b i : Fin 3) (hi : i ≠ b) (z : ℂ) :
      A.coord i z = alpha i * (B b).coord b z + (B b).coord i z := coordOtherApply L q hpos
          hinside b i hi z
  change (∃ b : Fin 3, z ∈ F b)
  let ratio (i : Fin 3) := A.coord i z / alpha i
  obtain ⟨b, _, hb⟩ := Finset.exists_min_image Finset.univ ratio Finset.univ_nonempty
  refine ⟨b, (hBmem b z).mpr ?_⟩
  have hs := coordSelfApply b z
  have hbpos : 0 ≤ (B b).coord b z := by
    have ha := (hmem z).mp hz b
    nlinarith [alphaPos b]
  intro i
  by_cases hi : i = b
  · simpa [hi] using hbpos
  · have hratio := hb i (Finset.mem_univ i)
    have hmul := (div_le_div_iff₀ (alphaPos b) (alphaPos i)).mp hratio
    have ho := coordOtherApply b i hi z
    rw [hs, ho] at hmul
    have : 0 ≤ alpha b * (B b).coord i z := by nlinarith only [hmul]
    nlinarith [alphaPos b]

private theorem intRatio (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q
    i).1) (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (b :
    Fin 3) (z : ℂ) (hz : z ∈ interior ((F L q) b))
      (i : Fin 3) (hi : i ≠ b) :
      (A L q hpos hinside).coord b z / (alpha L q hpos hinside) b < (A L q hpos hinside).coord i
          z / (alpha L q hpos hinside) i := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hspan : affineSpan ℝ (Set.range v) = ⊤ := hspan L q hpos hinside
  have hind : AffineIndependent ℝ v := hind L q hpos hinside
  let A : AffineBasis (Fin 3) ℝ ℂ := ⟨v, hind, hspan⟩
  let alpha (i : Fin 3) : ℝ := A.coord i (p 0)
  have alphaPos (i : Fin 3) : 0 < alpha i := alphaPos L q hpos hinside i
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  have huind (b : Fin 3) : AffineIndependent ℝ (u b) := huind L q hpos hinside b
  have hutot (b : Fin 3) : affineSpan ℝ (Set.range (u b)) = ⊤ := hutot L q hpos hinside b
  let B (b : Fin 3) : AffineBasis (Fin 3) ℝ ℂ := ⟨u b, huind b, hutot b⟩
  have hBint (b : Fin 3) (z : ℂ) :
      z ∈ interior (F b) ↔ ∀ i, 0 < (B b).coord i z := hBint L q hpos hinside b z
  have coordSelfApply (b : Fin 3) (z : ℂ) :
      A.coord b z = alpha b * (B b).coord b z := coordSelfApply L q hpos hinside b z
  have coordOtherApply (b i : Fin 3) (hi : i ≠ b) (z : ℂ) :
      A.coord i z = alpha i * (B b).coord b z + (B b).coord i z := coordOtherApply L q hpos
          hinside b i hi z
  change (A.coord b z / alpha b < A.coord i z / alpha i)
  apply (div_lt_div_iff₀ (alphaPos b) (alphaPos i)).mpr
  have hs := coordSelfApply b z
  have ho := coordOtherApply b i hi z
  have hp := (hBint b z).mp hz i
  have hprod := mul_pos (alphaPos b) hp
  rw [hs, ho]
  nlinarith only [hprod]

private theorem disjointInt (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q
    i).1) (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (b c
    : Fin 3) (hbc : b ≠ c) :
      Disjoint (interior ((F L q) b)) (interior ((F L q) c)) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hspan : affineSpan ℝ (Set.range v) = ⊤ := hspan L q hpos hinside
  have hind : AffineIndependent ℝ v := hind L q hpos hinside
  let A : AffineBasis (Fin 3) ℝ ℂ := ⟨v, hind, hspan⟩
  let alpha (i : Fin 3) : ℝ := A.coord i (p 0)
  have intRatio (b : Fin 3) (z : ℂ) (hz : z ∈ interior (F b))
      (i : Fin 3) (hi : i ≠ b) :
      A.coord b z / alpha b < A.coord i z / alpha i := intRatio L q hpos hinside b z hz i hi
  change (Disjoint (interior (F b)) (interior (F c)))
  apply Set.disjoint_left.mpr
  intro z hb hc
  exact (lt_asymm (intRatio b z hb c hbc.symm)) (intRatio c z hc b hbc)

private theorem segmentOfZero (D : AffineBasis (Fin 3) ℝ ℂ) (z : ℂ)
      (hnonneg : ∀ i, 0 ≤ D.coord i z) (i : Fin 3) (hi : D.coord i z = 0) :
      ∃ j k : Fin 3, j ≠ k ∧ j ≠ i ∧ k ≠ i ∧ z ∈ segment ℝ (D j) (D k) := by
  classical
  have hs := D.sum_coord_apply_eq_one z
  have hv := D.linear_combination_coord_eq_self z
  simp only [Fin.sum_univ_three] at hs hv
  fin_cases i
  · change D.coord 0 z = 0 at hi
    refine ⟨1, 2, by decide, by decide, by decide,
      D.coord 1 z, D.coord 2 z, hnonneg 1, hnonneg 2, ?_, ?_⟩
    · linarith
    · simpa [hi] using hv
  · change D.coord 1 z = 0 at hi
    refine ⟨0, 2, by decide, by decide, by decide,
      D.coord 0 z, D.coord 2 z, hnonneg 0, hnonneg 2, ?_, ?_⟩
    · linarith
    · simpa [hi] using hv
  · change D.coord 2 z = 0 at hi
    refine ⟨0, 1, by decide, by decide, by decide,
      D.coord 0 z, D.coord 1 z, hnonneg 0, hnonneg 1, ?_, ?_⟩
    · linarith
    · simpa [hi] using hv

private theorem childClosed (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q
    i).1) (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (b :
    Fin 3) : IsClosed ((F L q) b) := by
  classical
  have affineContinuous (f : ℂ →ᵃ[ℝ] ℝ) : Continuous f := affineContinuous f
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
  let v : Fin 3 → ℂ := fun i => p i.succ
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  have huind (b : Fin 3) : AffineIndependent ℝ (u b) := huind L q hpos hinside b
  have hutot (b : Fin 3) : affineSpan ℝ (Set.range (u b)) = ⊤ := hutot L q hpos hinside b
  let B (b : Fin 3) : AffineBasis (Fin 3) ℝ ℂ := ⟨u b, huind b, hutot b⟩
  have hchild (b : Fin 3) : F b = convexHull ℝ (Set.range (B b)) := hchild L q hpos hinside b
  change (IsClosed (F b))
  rw [hchild, (B b).convexHull_eq_nonneg_coord]
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le continuous_const
    (affineContinuous ((B b).coord i))

private theorem childFrontier (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q
    i).1) (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (b :
    Fin 3) : frontier ((F L q) b) ⊆ P4909T1ParentEdges L ((s q) b) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
  let v : Fin 3 → ℂ := fun i => p i.succ
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  have huind (b : Fin 3) : AffineIndependent ℝ (u b) := huind L q hpos hinside b
  have hutot (b : Fin 3) : affineSpan ℝ (Set.range (u b)) = ⊤ := hutot L q hpos hinside b
  let B (b : Fin 3) : AffineBasis (Fin 3) ℝ ℂ := ⟨u b, huind b, hutot b⟩
  have hparents (b : Fin 3) : ∀ i : Fin 3, 0 < (s b i.succ).1 := hparents q hpos b
  have hparentPoint (b j : Fin 3) :
      ((s b j.succ).2 : ℂ) / ((s b j.succ).1 : ℝ) = B b (j + b) := hparentPoint L q hpos hinside b j
  have hBmem (b : Fin 3) (z : ℂ) : z ∈ F b ↔ ∀ i, 0 ≤ (B b).coord i z := hBmem L q hpos hinside b z
  have hBint (b : Fin 3) (z : ℂ) :
      z ∈ interior (F b) ↔ ∀ i, 0 < (B b).coord i z := hBint L q hpos hinside b z
  have segmentOfZero (D : AffineBasis (Fin 3) ℝ ℂ) (z : ℂ)
      (hnonneg : ∀ i, 0 ≤ D.coord i z) (i : Fin 3) (hi : D.coord i z = 0) :
      ∃ j k : Fin 3, j ≠ k ∧ j ≠ i ∧ k ≠ i ∧ z ∈ segment ℝ (D j) (D k) := segmentOfZero D z
          hnonneg i hi
  have childClosed (b : Fin 3) : IsClosed (F b) := childClosed L q hpos hinside b
  change (frontier (F b) ⊆ P4909T1ParentEdges L (s b))
  intro z hz
  rw [(childClosed b).frontier_eq] at hz
  have hc := (hBmem b z).mp hz.1
  have hn : ¬ ∀ i, 0 < (B b).coord i z := by
    intro hp
    exact hz.2 ((hBint b z).mpr hp)
  obtain ⟨i, hi⟩ := not_forall.mp hn
  have heq : (B b).coord i z = 0 := le_antisymm (not_lt.mp hi) (hc i)
  obtain ⟨j, k, hjk, _, _, hseg⟩ := segmentOfZero (B b) z hc i heq
  change (∃ j k : Fin 3, j ≠ k ∧ 0 < (s b j.succ).1 ∧ 0 < (s b k.succ).1 ∧
    z ∈ segment ℝ (((s b j.succ).2 : ℂ) / ((s b j.succ).1 : ℝ))
      (((s b k.succ).2 : ℂ) / ((s b k.succ).1 : ℝ))) ∨ _
  apply Or.inl
  refine ⟨j - b, k - b, ?_, hparents b _, hparents b _, ?_⟩
  · intro he
    apply hjk
    exact (sub_left_inj).mp he
  · simpa only [hparentPoint, sub_add_cancel] using hseg

private theorem offSeam (L : ℝ) (q : Fin 4 → CircleCoordinates) (hpos : ∀ i : Fin 4, 0 < (q i).1)
    (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (z : ℂ) (hz
    : z ∈ interior (P L q))
      (hseam : ∀ i : Fin 4, 0 < (q i).1 → z ∉ segment ℝ ((p q) 0) ((p q) i)) :
      ∃ b, z ∈ interior ((F L q) b) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let P := P4909T1ParentPolygon L q
  let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
  let v : Fin 3 → ℂ := fun i => p i.succ
  have hspan : affineSpan ℝ (Set.range v) = ⊤ := hspan L q hpos hinside
  have hind : AffineIndependent ℝ v := hind L q hpos hinside
  let A : AffineBasis (Fin 3) ℝ ℂ := ⟨v, hind, hspan⟩
  have hint (z : ℂ) : z ∈ interior P ↔ ∀ i, 0 < A.coord i z := hint L q hpos hinside z
  let alpha (i : Fin 3) : ℝ := A.coord i (p 0)
  have alphaPos (i : Fin 3) : 0 < alpha i := alphaPos L q hpos hinside i
  let u (b : Fin 3) : Fin 3 → ℂ := Function.update v b (p 0)
  have huind (b : Fin 3) : AffineIndependent ℝ (u b) := huind L q hpos hinside b
  have hutot (b : Fin 3) : affineSpan ℝ (Set.range (u b)) = ⊤ := hutot L q hpos hinside b
  let B (b : Fin 3) : AffineBasis (Fin 3) ℝ ℂ := ⟨u b, huind b, hutot b⟩
  have hBself (b : Fin 3) : B b b = p 0 := hBself L q hpos hinside b
  have hBother (b i : Fin 3) (hi : i ≠ b) : B b i = v i := hBother L q hpos hinside b i hi
  have hBmem (b : Fin 3) (z : ℂ) : z ∈ F b ↔ ∀ i, 0 ≤ (B b).coord i z := hBmem L q hpos hinside b z
  have hBint (b : Fin 3) (z : ℂ) :
      z ∈ interior (F b) ↔ ∀ i, 0 < (B b).coord i z := hBint L q hpos hinside b z
  have coordSelfApply (b : Fin 3) (z : ℂ) :
      A.coord b z = alpha b * (B b).coord b z := coordSelfApply L q hpos hinside b z
  have childCover (z : ℂ) (hz : z ∈ P) : ∃ b : Fin 3, z ∈ F b := childCover L q hpos hinside z hz
  have segmentOfZero (D : AffineBasis (Fin 3) ℝ ℂ) (z : ℂ)
      (hnonneg : ∀ i, 0 ≤ D.coord i z) (i : Fin 3) (hi : D.coord i z = 0) :
      ∃ j k : Fin 3, j ≠ k ∧ j ≠ i ∧ k ≠ i ∧ z ∈ segment ℝ (D j) (D k) := segmentOfZero D z
          hnonneg i hi
  change (∃ b, z ∈ interior (F b))
  obtain ⟨b, hb⟩ := childCover z (interior_subset hz)
  have hc := (hBmem b z).mp hb
  have hbp : 0 < (B b).coord b z := by
    have ha := (hint z).mp hz b
    have hs := coordSelfApply b z
    nlinarith [alphaPos b]
  refine ⟨b, (hBint b z).mpr ?_⟩
  intro i
  by_contra hi
  have hzero : (B b).coord i z = 0 := le_antisymm (not_lt.mp hi) (hc i)
  have hib : i ≠ b := by
    intro he
    subst i
    linarith
  obtain ⟨j, k, hjk, hji, hki, hseg⟩ := segmentOfZero (B b) z hc i hzero
  have hbjk : b = j ∨ b = k := by omega
  rcases hbjk with rfl | rfl
  · rw [hBself, hBother b k hjk.symm] at hseg
    exact hseam k.succ (hpos k.succ) hseg
  · rw [segment_symm, hBself, hBother b j hjk] at hseg
    exact hseam j.succ (hpos j.succ) hseg

end TriangleFanConstruction

theorem P4909T1TriangleFan (L : ℝ) (q : Fin 4 → CircleCoordinates)
    (hpos : ∀ i : Fin 4, 0 < (q i).1)
    (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) :
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
    let P := P4909T1ParentPolygon L q
    let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
    (∀ b, F b ⊆ P ∧ p b.succ ∉ F b ∧ frontier (F b) ⊆ P4909T1ParentEdges L (s b)) ∧
    (∀ b c, b ≠ c → Disjoint (interior (F b)) (interior (F c))) ∧
    P = ⋃ b, F b ∧
    (∀ z ∈ interior P,
      (∀ i : Fin 4, 0 < (q i).1 → z ∉ segment ℝ (p 0) (p i)) →
      (∀ k : Fin 3, (q k.succ).1 = 0 →
        z ∉ segment ℝ (p 0)
          ⟨if (q k.succ).2 = -1 then L else L + 2, (p 0).im⟩) →
      ∃ b, z ∈ interior (F b)) := by
-- BODY
  classical
  dsimp only
  -- Establish affine-coordinate topology directly from real and imaginary parts.
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let P := P4909T1ParentPolygon L q
  let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
  -- The child basis replaces precisely the omitted parent by the inserted center.
  have childSubset (b : Fin 3) : F b ⊆ P := TriangleFanConstruction.childSubset L q hpos hinside b
  have omittedNotIn (b : Fin 3) : p b.succ ∉ F b := TriangleFanConstruction.omittedNotIn L q hpos
      hinside b
  -- A minimum barycentric ratio makes all child coordinates nonnegative.
  have childCover (z : ℂ) (hz : z ∈ P) : ∃ b : Fin 3, z ∈ F b :=
      TriangleFanConstruction.childCover L q hpos hinside z hz
  have disjointInt (b c : Fin 3) (hbc : b ≠ c) :
      Disjoint (interior (F b)) (interior (F c)) := TriangleFanConstruction.disjointInt L q hpos
          hinside b c hbc
  -- A zero coordinate leaves a convex combination of the other two vertices.
  have childFrontier (b : Fin 3) : frontier (F b) ⊆ P4909T1ParentEdges L (s b) :=
      TriangleFanConstruction.childFrontier L q hpos hinside b
  have offSeam (z : ℂ) (hz : z ∈ interior P)
      (hseam : ∀ i : Fin 4, 0 < (q i).1 → z ∉ segment ℝ (p 0) (p i)) :
      ∃ b, z ∈ interior (F b) := TriangleFanConstruction.offSeam L q hpos hinside z hz hseam
  refine ⟨fun b => ⟨childSubset b, omittedNotIn b, childFrontier b⟩, disjointInt, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro z hz
      exact Set.mem_iUnion.mpr (childCover z hz)
    · intro z hz
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hz
      exact childSubset b hb
  · intro z hz hseam _
    exact offSeam z hz hseam

end ApollonianSuperharmonic

end
