/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.FoldAvoid
public import LeanPool.HyperellipticCurves.Log.Fold.FoldPack
public import LeanPool.HyperellipticCurves.Log.Fold.FoldWitness

import LeanPool.HyperellipticCurves.Log.Fold.GenusOne
import LeanPool.HyperellipticCurves.Log.Ftau.GoodPosition

/-!
# The centre-fold witness

The enlarged common witness `ChabautyColeman.exists_centerFoldWitness` of the point-by-point fold
construction of `F_τ`. It extends the all-genus fold witness (`ChabautyColeman.exists_foldWitness`)
by the three condition families the fold-`F_τ` consumers need beyond the `2g` step conditions:

* nonzero `y`-coordinates (non-Weierstrass points) and avoidance of a prescribed finite
  set by the `x`-coordinates — refuted at honest curve points
  (`ChabautyColeman.not_curveVanishing_X_snd`,
  `ChabautyColeman.not_curveVanishing_X_sub_C`);
* the per-stage Weierstrass-avoidance conditions `IsCoprime Uⱼ (2·Vⱼ)` of the honest
  fold states, through the engine instances of the universal avoidance numerators
  (`ChabautyColeman.curveAvoidNum`): at an honest tuple the instance evaluates to the
  formal-degree resultant of the numerator state
  (`ChabautyColeman.eval_curveAvoidNum`), and its nonvanishing produces a Bézout
  certificate (`Polynomial.exists_bezout_of_isUnit_resultant`); the family
  refutation (`ChabautyColeman.not_curveVanishing_curveAvoidNum`) is the master descent
  (`ChabautyColeman.not_curveVanishing_of_cusp_ne_zero`) at the isobarity and cusp
  certificates of `LeanPool.HyperellipticCurves.Log.Fold.FoldAvoid`.

The file's external interface is `ChabautyColeman.exists_centerFoldPack`, the witness packed
in the form `LeanPool.HyperellipticCurves.Log.Ftau.TauExists` consumes.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

/-! ### The engine instances of the universal avoidance numerators -/

section Engine

variable {κ : Type*} [Field κ] {g : ℕ} {f : κ[X]}

/-- **The engine instances of the universal avoidance numerators**: the per-stage
Weierstrass-avoidance conditions `IsCoprime Uⱼ (2·Vⱼ)` as polynomial conditions on
`g`-tuples of plane points, for the avoidance engine. -/
noncomputable def curveAvoidNum (f : κ[X]) (g j : ℕ) : MvPolynomial (Fin g × Fin 2) κ :=
  MvPolynomial.aeval (curveSpec f g) (univAvoidNum κ g j)

/-- **The engine instances of the avoidance numerators evaluate at an honest tuple to the
resultant of the numerator fold state at the tuple.** -/
theorem eval_curveAvoidNum (hf : f.Monic) (hfdeg : f.natDegree = 2 * g + 1)
    (x y : Fin g → κ) (j : ℕ) :
    MvPolynomial.eval (tupleCoords fun i ↦ (x i, y i)) (curveAvoidNum f g j)
      = ((foldNum f (foldXs x) (foldYs y) (foldBase f x y) j).u).resultant
          ((foldNum f (foldXs x) (foldYs y) (foldBase f x y) j).v) g g := by
  have h := aeval_aeval_curveSpec (f := f) (fun i ↦ (x i, y i)) (univAvoidNum κ g j)
  rw [MvPolynomial.aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_id] at h
  set φ : MvPolynomial (Fin g ⊕ Fin g ⊕ Fin (2 * g + 1)) κ →+* κ :=
    (MvPolynomial.aeval (R := κ) (Sum.elim x (Sum.elim y fun r : Fin (2 * g + 1) ↦
      f.coeff r))).toRingHom with hφdef
  have h2 : φ (univAvoidNum κ g j)
      = ((foldNum f (foldXs x) (foldYs y) (foldBase f x y) j).u).resultant
          ((foldNum f (foldXs x) (foldYs y) (foldBase f x y) j).v) g g := by
    rw [univAvoidNum, ← Polynomial.resultant_map_map _ _ g g φ]
    have hu := congrArg MumfordNum.u (map_foldNum_univ hf hfdeg x y j)
    have hv := congrArg MumfordNum.v (map_foldNum_univ hf hfdeg x y j)
    rw [MumfordNum.map_u] at hu
    rw [MumfordNum.map_v] at hv
    rw [hφdef, hu, hv]
  rw [curveAvoidNum]
  exact h.trans h2

/-- **Nonvanishing of the stage-`j` resultant makes the honest fold state's components
coprime** (with the `2` of the reduction steps included): the resultant of the scaled
numerator state is the honest resultant up to denominators, and a nonzero resultant at
the formal degrees `(g, g)` yields a Bézout certificate. -/
theorem isCoprime_foldChain_of_resultant_ne_zero [NeZero (2 : κ)] (hf : f.Monic)
    (hfdeg : f.natDegree = 2 * g + 1) (hg : 0 < g) {x y : Fin g → κ}
    (hx : Function.Injective x) (hcurve : ∀ i, y i ^ 2 = f.eval (x i)) {j : ℕ}
    (hj : j ≤ 2 * g)
    (hc : ∀ i < j, foldCondNum f (foldXs x) (foldYs y) (foldBase f x y) i ≠ 0)
    (hres : ((foldNum f (foldXs x) (foldYs y) (foldBase f x y) j).u).resultant
      ((foldNum f (foldXs x) (foldYs y) (foldBase f x y) j).v) g g ≠ 0) :
    IsCoprime
      (foldChain f (foldXs x) (foldGenH f (foldXs x) (foldYs y) (tupleU x) (tupleV x y))
        (tupleU x) (tupleV x y) j).1
      (2 * (foldChain f (foldXs x) (foldGenH f (foldXs x) (foldYs y) (tupleU x)
        (tupleV x y)) (tupleU x) (tupleV x y) j).2) := by
  have hbase := isScaledState_foldBase hx hcurve
  have hx₀ : (tupleU x).eval (foldXs x 0) = 0 := by
    rw [foldXs_zero x hg]
    exact eval_tupleU_self x ⟨0, hg⟩
  have hV₀ : (tupleV x y).eval (foldXs x 0) = foldYs y 0 := by
    rw [foldXs_zero x hg, foldYs_zero y hg]
    exact eval_tupleV hx ⟨0, hg⟩
  have hspec := isScaledState_foldNum (m := j) hf hfdeg hbase hx₀ hV₀
    (fun i hi ↦ foldYs_sq hcurve (by lia)) hc
  rw [hspec.u_eq, hspec.v_eq, Polynomial.resultant_C_mul_left,
    Polynomial.resultant_C_mul_right] at hres
  have hres2 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hres).2).2
  obtain ⟨s, t, _, _, hst⟩ := exists_bezout_of_isUnit_resultant
    hspec.state.natDegree_U.le (natDegree_le_iff_degree_le.mpr hspec.state.degree_V.le)
    (.inl hg.ne') (isUnit_iff_ne_zero.mpr hres2)
  have h2u : IsUnit (2 : κ[X]) := by
    rw [← map_ofNat C 2]
    exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (NeZero.ne 2))
  exact (isCoprime_mul_unit_left_right h2u _ _).mpr ⟨s, t, hst⟩

end Engine

/-! ### Refutation of the new conditions at families and honest points -/

section Family

variable {κ : Type*} [Field κ] [IsAlgClosed κ] {g : ℕ} {f : κ[X]}

/-- **No universal avoidance numerator vanishes identically on curve tuples**: the
avoidance numerators are isobaric with nonzero cusp specialization, so the master
refutation applies. -/
theorem not_curveVanishing_curveAvoidNum [NeZero (2 : κ)] (hf : f.Monic)
    (hfdeg : f.natDegree = 2 * g + 1) (hg2 : 2 ≤ g) {j : ℕ} (hj : j ≤ 2 * g) :
    ¬CurveVanishing f g (curveAvoidNum f g j) :=
  not_curveVanishing_of_cusp_ne_zero hf hfdeg (isWeightedHomogeneous_univAvoidNum j)
    (cuspAvoidNum_ne_zero hg2 hj)

/-- The step-condition refutation for every positive genus: the cusp engine at `g ≥ 2`,
the genus-one witness point of `LeanPool.HyperellipticCurves.Log.Fold.GenusOne` (which needs `f`
squarefree — for `f = X³` in characteristic `3` the genus-one conditions genuinely vanish
on all curve points) at `g = 1`. -/
theorem not_curveVanishing_curveCondNum_of_squarefree [NeZero (2 : κ)] (hf : f.Monic)
    (hfdeg : f.natDegree = 2 * g + 1) (hg : 0 < g) (hgen : 2 ≤ g ∨ Squarefree f) {j : ℕ}
    (hj : j < 2 * g) : ¬CurveVanishing f g (curveCondNum f g j) := by
  rcases Nat.lt_or_ge g 2 with hg1 | hg2
  · obtain rfl : g = 1 := by lia
    intro hv
    obtain ⟨x₀, y₀, hcv, -, hconds, -⟩ := exists_genusOnePoint hf (by lia)
      (hgen.resolve_left (by lia))
    have h := hv (fun i ↦ (![x₀] i, ![y₀] i)) fun i ↦ by fin_cases i; simpa
    rw [eval_curveCondNum hf hfdeg] at h
    exact hconds j (by lia) h
  · exact not_curveVanishing_curveCondNum hf hfdeg hg2 hj

/-- The avoidance refutation for every positive genus: the cusp engine at `g ≥ 2`, the
genus-one witness point at `g = 1` (squarefree `f`). -/
theorem not_curveVanishing_curveAvoidNum_of_squarefree [NeZero (2 : κ)] (hf : f.Monic)
    (hfdeg : f.natDegree = 2 * g + 1) (hg : 0 < g) (hgen : 2 ≤ g ∨ Squarefree f) {j : ℕ}
    (hj : j ≤ 2 * g) : ¬CurveVanishing f g (curveAvoidNum f g j) := by
  rcases Nat.lt_or_ge g 2 with hg1 | hg2
  · obtain rfl : g = 1 := by lia
    intro hv
    obtain ⟨x₀, y₀, hcv, -, -, havoids⟩ := exists_genusOnePoint hf (by lia)
      (hgen.resolve_left (by lia))
    have h := hv (fun i ↦ (![x₀] i, ![y₀] i)) fun i ↦ by fin_cases i; simpa
    rw [eval_curveAvoidNum hf hfdeg] at h
    exact havoids j (by lia) h
  · exact not_curveVanishing_curveAvoidNum hf hfdeg hg2 hj

/-- The `y`-coordinate conditions do not vanish identically on curve tuples. -/
theorem not_curveVanishing_X_snd (hf : f ≠ 0) (i : Fin g) :
    ¬CurveVanishing f g (MvPolynomial.X (i, 1)) := by
  intro hv
  obtain ⟨z, hz⟩ := (residue_curve_points_infinite hf).nonempty
  have h := hv (fun _ ↦ z) fun _ ↦ hz.1
  rw [MvPolynomial.eval_X] at h
  exact hz.2 (by simpa [tupleCoords] using h)

/-- The `T`-avoidance conditions on the `x`-coordinates do not vanish identically on
curve tuples. -/
theorem not_curveVanishing_X_sub_C (i : Fin g) (t : κ) :
    ¬CurveVanishing f g (MvPolynomial.X (i, 0) - MvPolynomial.C t) := by
  intro hv
  obtain ⟨a, ha⟩ := exists_ne t
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (f.eval a) (n := 2) two_pos
  have h := hv (fun _ ↦ (a, b)) fun _ ↦ hb
  rw [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C] at h
  have hi : tupleCoords (fun _ : Fin g ↦ (a, b)) (i, 0) = a := by simp [tupleCoords]
  rw [hi, sub_eq_zero] at h
  exact ha h

/-! ### The centre-fold witness -/

/-- **The centre-fold witness**: over an algebraically closed field of characteristic `≠ 2`, for
`f` monic of odd degree `2g + 1` with `g ≥ 1` — squarefree if `g = 1` — and a finite avoidance set
`T`, there is a single tuple of affine curve points — pairwise distinct `x`-coordinates, nonzero
`y`-coordinates, `x`-coordinates avoiding `T` — at which all `2g` step conditions of the fold hold
and every intermediate honest fold state has components with coprime `(Uⱼ, 2·Vⱼ)`. -/
theorem exists_centerFoldWitness [NeZero (2 : κ)] (hf : f.Monic)
    (hfdeg : f.natDegree = 2 * g + 1) (hg : 0 < g) (hgen : 2 ≤ g ∨ Squarefree f)
    {T : Set κ} (hT : T.Finite) :
    ∃ x y : Fin g → κ, (∀ i, y i ^ 2 = f.eval (x i)) ∧ Function.Injective x
      ∧ (∀ i, y i ≠ 0) ∧ (∀ i, ∀ t ∈ T, x i ≠ t)
      ∧ (∀ j < 2 * g, foldCondNum f (foldXs x) (foldYs y) (foldBase f x y) j ≠ 0)
      ∧ (∀ j < 2 * g, foldCond f (foldXs x) (foldYs y) (tupleU x) (tupleV x y) j ≠ 0)
      ∧ ∀ j ≤ 2 * g, IsCoprime
          (foldChain f (foldXs x) (foldGenH f (foldXs x) (foldYs y) (tupleU x)
            (tupleV x y)) (tupleU x) (tupleV x y) j).1
          (2 * (foldChain f (foldXs x) (foldGenH f (foldXs x) (foldYs y) (tupleU x)
            (tupleV x y)) (tupleU x) (tupleV x y) j).2) := by
  classical
  have hodd : Odd f.natDegree := ⟨g, by lia⟩
  obtain ⟨P, hP, hne⟩ := exists_curveTuple_ne_zero hf hodd
    ((Finset.range (2 * g)).image (curveCondNum f g)
      ∪ (Finset.range (2 * g + 1)).image (curveAvoidNum f g)
      ∪ ((Finset.univ.filter fun p : Fin g × Fin g ↦ p.1 ≠ p.2).image
          fun p ↦ MvPolynomial.X (p.1, 0) - MvPolynomial.X (p.2, 0))
      ∪ Finset.univ.image (fun i : Fin g ↦ MvPolynomial.X (i, 1))
      ∪ (Finset.univ ×ˢ hT.toFinset).image
          fun p ↦ MvPolynomial.X (p.1, 0) - MvPolynomial.C p.2)
    (by
      intro F hF
      simp only [Finset.mem_union] at hF
      rcases hF with ((((h | h) | h) | h) | h)
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
        exact not_curveVanishing_curveCondNum_of_squarefree hf hfdeg hg hgen
          (Finset.mem_range.mp hj)
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
        exact not_curveVanishing_curveAvoidNum_of_squarefree hf hfdeg hg hgen
          (by have := Finset.mem_range.mp hj; lia)
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
        exact not_curveVanishing_X_sub_X (Finset.mem_filter.mp hp).2
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
        exact not_curveVanishing_X_snd hf.ne_zero i
      · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp h
        exact not_curveVanishing_X_sub_C p.1 p.2)
  have hxinj : Function.Injective fun i ↦ (P i).1 := by
    intro i j hijeq
    by_contra hij
    have h := hne _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩))))
    rw [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_X] at h
    exact h (by simpa [tupleCoords] using sub_eq_zero.mpr hijeq)
  have hcond : ∀ j < 2 * g, foldCondNum f (foldXs fun i ↦ (P i).1)
      (foldYs fun i ↦ (P i).2)
      (foldBase f (fun i ↦ (P i).1) fun i ↦ (P i).2) j ≠ 0 := by
    intro j hj
    have h := hne _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨j, Finset.mem_range.mpr hj, rfl⟩)))))
    have h2 : MvPolynomial.eval (tupleCoords fun i ↦ ((P i).1, (P i).2))
        (curveCondNum f g j) ≠ 0 := h
    rwa [eval_curveCondNum hf hfdeg] at h2
  have hy : ∀ i, (P i).2 ≠ 0 := by
    intro i
    have h := hne _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
    rw [MvPolynomial.eval_X] at h
    simpa [tupleCoords] using h
  have hxT : ∀ i, ∀ t ∈ T, (P i).1 ≠ t := by
    intro i t ht heq
    have h := hne _ (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨(i, t), Finset.mem_product.mpr ⟨Finset.mem_univ _, hT.mem_toFinset.mpr ht⟩, rfl⟩))
    rw [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C] at h
    exact h (by simpa [tupleCoords] using sub_eq_zero.mpr heq)
  refine ⟨fun i ↦ (P i).1, fun i ↦ (P i).2, hP, hxinj, hy, hxT, hcond,
    fun j hj ↦ foldCond_ne_zero hf hfdeg hg hxinj hP hj fun i hi ↦ hcond i (by lia),
    fun j hj ↦ isCoprime_foldChain_of_resultant_ne_zero hf hfdeg hg hxinj hP hj
      (fun i hi ↦ hcond i (by lia)) ?_⟩
  have h := hne _ (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨j, Finset.mem_range.mpr (by lia), rfl⟩)))))
  have h2 : MvPolynomial.eval (tupleCoords fun i ↦ ((P i).1, (P i).2))
      (curveAvoidNum f g j) ≠ 0 := h
  rwa [eval_curveAvoidNum hf hfdeg] at h2

/-- **The centre-fold pack witness** (the field-level content of `lem:tau-generic`): over
an algebraically closed field of characteristic `≠ 2`, for `f` monic of odd degree
`2g + 1` with `g ≥ 1` — squarefree if `g = 1` — and a finite avoidance set `T`, some
tuple of affine curve points — pairwise distinct `x`-coordinates avoiding `T`, nonzero
`y`-coordinates — carries a valid, Weierstrass-avoiding fold pack at the tuple datum. -/
theorem exists_centerFoldPack [NeZero (2 : κ)] (hf : f.Monic)
    (hfdeg : f.natDegree = 2 * g + 1) (hg : 0 < g) (hgen : 2 ≤ g ∨ Squarefree f)
    {T : Set κ} (hT : T.Finite) :
    ∃ (x y : Fin g → κ) (d : FoldCertData κ g),
      (∀ i, y i ^ 2 = f.eval (x i)) ∧ Function.Injective x
        ∧ (∀ i, y i ≠ 0) ∧ (∀ i, ∀ t ∈ T, x i ≠ t)
        ∧ IsFoldCerts f (foldXs x) (foldYs y) (tupleU x) (tupleV x y) d
        ∧ IsFoldAvoid f (foldXs x) (foldYs y) (tupleU x) (tupleV x y) d := by
  obtain ⟨x, y, hcurve, hxinj, hy0, hxT, hcnum, hcond, hchain⟩ :=
    exists_centerFoldWitness hf hfdeg hg hgen hT
  have hx₀ : (tupleU x).eval (foldXs x 0) = 0 := by
    rw [foldXs_zero x hg]
    exact eval_tupleU_self x ⟨0, hg⟩
  have hV₀ : (tupleV x y).eval (foldXs x 0) = foldYs y 0 := by
    rw [foldXs_zero x hg, foldYs_zero y hg]
    exact eval_tupleV hxinj ⟨0, hg⟩
  have hbase := isScaledState_foldBase hxinj hcurve
  have hstate : ∀ j ≤ 2 * g, IsFoldState g f
      (foldChain f (foldXs x) (foldGenH f (foldXs x) (foldYs y) (tupleU x) (tupleV x y))
        (tupleU x) (tupleV x y) j).1
      (foldChain f (foldXs x) (foldGenH f (foldXs x) (foldYs y) (tupleU x) (tupleV x y))
        (tupleU x) (tupleV x y) j).2 := fun j hj ↦
    (isScaledState_foldNum hf hfdeg hbase hx₀ hV₀
      (fun i hi ↦ foldYs_sq hcurve (by lia)) fun i hi ↦ hcnum i (by lia)).state
  obtain ⟨d, hd, hav⟩ := exists_isFoldCerts_isFoldAvoid hstate hx₀ hV₀
    (fun j hj ↦ foldYs_sq hcurve hj) hcond hchain
  exact ⟨x, y, d, hcurve, hxinj, hy0, hxT, hd, hav⟩

end Family

end ChabautyColeman

end
