/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.FoldCorrect
public import LeanPool.HyperellipticCurves.Log.Fold.FoldUniversal
public import LeanPool.HyperellipticCurves.Log.Witness.CurveTuples
public import LeanPool.HyperellipticCurves.Log.Witness.TupleSeed

import LeanPool.HyperellipticCurves.Log.Fold.CuspInstance
import LeanPool.HyperellipticCurves.Log.Fold.FoldDescent
import LeanPool.HyperellipticCurves.Log.Witness.InfinityFamily

/-!
# The all-genus fold witness

`thm:fold-witness`: over an algebraically closed field of characteristic `≠ 2`, for every
monic `f` of odd degree `2g + 1` (`g ≥ 2`) there is a single `g`-tuple of affine curve
points at which all `2g` step-condition numerators of the numerator fold
(`ChabautyColeman.foldCondNum`) — and with them the honest step conditions of the
point-by-point fold `τ + τ - τ` — are simultaneously nonzero
(`ChabautyColeman.exists_foldWitness`).

The route: each universal condition numerator `𝒩_q` (`ChabautyColeman.univCondNum`)
becomes a polynomial condition on tuples of curve points through the engine
specialization `ChabautyColeman.curveSpec` (coordinates to tuple variables, generic curve
coefficients to the coefficients of `f`). The all-at-infinity Laurent family at the
common descent rates (`ChabautyColeman.exists_infinityPoint` at the rates
`ChabautyColeman.descRate`) is a formal curve tuple at which the engine instance takes a
nonzero value — the master descent statement `ChabautyColeman.aeval_family_ne_zero` fed
with the cuspidal nonvanishing `ChabautyColeman.cuspNum_ne_zero` — so no condition
vanishes identically on curve tuples
(`ChabautyColeman.not_curveVanishing_curveCondNum`). The avoidance engine
(`ChabautyColeman.exists_curveTuple_ne_zero`) then produces one common honest witness
tuple, and the correctness layer (`ChabautyColeman.foldCondNum_eq_den_mul`) converts the
numerator conditions into the honest fold conditions at the tuple.

## Main definitions

* `ChabautyColeman.foldXs`, `ChabautyColeman.foldYs`: the two-phase coordinate sequences
  of the `2g`-step fold at a `g`-tuple (the second phase in reverse order).
* `ChabautyColeman.curveSpec`, `ChabautyColeman.curveCondNum`: the engine instances of
  the universal condition numerators.

## Main statements

* `ChabautyColeman.isScaledState_foldBase`: the numerator base state at an injective
  curve tuple represents the honest interpolating Mumford datum.
* `ChabautyColeman.not_curveVanishing_of_cusp_ne_zero`: the master refutation — the
  engine instance of any weighted-homogeneous universal polynomial with nonzero cusp
  specialization does not vanish identically on curve tuples.
* `ChabautyColeman.not_curveVanishing_curveCondNum`: no condition numerator vanishes
  identically on curve tuples.
* `ChabautyColeman.exists_foldWitness`: the all-genus fold witness (`thm:fold-witness`).
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

/-! ### The two-phase coordinate sequences -/

section Seq

variable {R S : Type*} [CommRing R] [CommRing S] {g : ℕ}

/-- **The two-phase `x`-sequence of the `2g`-step fold** at a `g`-tuple: the second phase
revisits the coordinates of the first in reverse order (the fold adds the conjugate
points, last added first, so it retraces its own states); stages the fold never reaches
are set to `0`. -/
def foldXs (x : Fin g → R) (j : ℕ) : R :=
  if h : j < g then x ⟨j, h⟩ else if h' : j - g < g then x (Fin.rev ⟨j - g, h'⟩) else 0

/-- **The two-phase `y`-sequence of the `2g`-step fold**: the second phase negates the
first, in reverse order. -/
def foldYs (y : Fin g → R) (j : ℕ) : R :=
  if h : j < g then y ⟨j, h⟩ else if h' : j - g < g then -y (Fin.rev ⟨j - g, h'⟩) else 0

/-- The universal `x`-sequence is the two-phase sequence of the coordinate variables. -/
theorem univXs_eq_foldXs (K : Type*) [CommRing K] (g j : ℕ) :
    univXs K g j = foldXs (fun i ↦ MvPolynomial.X (.inl i)) j := rfl

/-- The universal `y`-sequence is the two-phase sequence of the coordinate variables. -/
theorem univYs_eq_foldYs (K : Type*) [CommRing K] (g j : ℕ) :
    univYs K g j = foldYs (fun i ↦ MvPolynomial.X (.inr (.inl i))) j := rfl

theorem map_foldXs (φ : R →+* S) (x : Fin g → R) (j : ℕ) :
    φ (foldXs x j) = foldXs (fun i ↦ φ (x i)) j := by
  rw [foldXs, foldXs]
  split_ifs <;> simp

theorem map_foldYs (φ : R →+* S) (y : Fin g → R) (j : ℕ) :
    φ (foldYs y j) = foldYs (fun i ↦ φ (y i)) j := by
  rw [foldYs, foldYs]
  split_ifs <;> simp

theorem foldXs_zero (x : Fin g → R) (hg : 0 < g) : foldXs x 0 = x ⟨0, hg⟩ := by
  rw [foldXs, dite_eq_left hg]

theorem foldYs_zero (y : Fin g → R) (hg : 0 < g) : foldYs y 0 = y ⟨0, hg⟩ := by
  rw [foldYs, dite_eq_left hg]

/-- The second phase revisits the tuple in reverse order. -/
theorem foldXs_add (x : Fin g → R) {i : ℕ} (hi : i < g) :
    foldXs x (g + i) = x (Fin.rev ⟨i, hi⟩) := by
  rw [foldXs, dite_eq_right (by lia), dite_eq_left (by lia)]
  exact congrArg (x ∘ Fin.rev) (Fin.ext (by simp))

/-- The second phase revisits the tuple in reverse order, with negated `y`. -/
theorem foldYs_add (y : Fin g → R) {i : ℕ} (hi : i < g) :
    foldYs y (g + i) = -y (Fin.rev ⟨i, hi⟩) := by
  rw [foldYs, dite_eq_right (by lia), dite_eq_left (by lia)]
  exact congrArg (fun j ↦ -y (Fin.rev j)) (Fin.ext (by simp))

/-- The two-phase `x`-sequence only depends on the tuple up to an index cast. -/
theorem foldXs_cast {n n' : ℕ} (h : n' = n) (x : Fin n → R) :
    foldXs (fun i : Fin n' ↦ x (Fin.cast h i)) = foldXs x := by
  subst h
  rfl

/-- The two-phase `y`-sequence only depends on the tuple up to an index cast. -/
theorem foldYs_cast {n n' : ℕ} (h : n' = n) (y : Fin n → R) :
    foldYs (fun i : Fin n' ↦ y (Fin.cast h i)) = foldYs y := by
  subst h
  rfl

/-- The two-phase sequences run through curve points as long as the tuple does. -/
theorem foldYs_sq {f : R[X]} {x y : Fin g → R} (hcurve : ∀ i, y i ^ 2 = f.eval (x i))
    {i : ℕ} (hi : i < 2 * g) : foldYs y i ^ 2 = f.eval (foldXs x i) := by
  rw [foldXs, foldYs]
  split_ifs with h1 h2
  · exact hcurve _
  · rw [neg_sq]
    exact hcurve _
  · exact absurd (by lia) h2

end Seq

/-! ### The scaled base pack and the honest conditions at a curve tuple -/

section Base

variable {F : Type*} [Field F] {g : ℕ} {f : F[X]} {x y : Fin g → F}

/-- **The scaled base state of the numerator fold at an injective tuple** represents the
honest interpolating Mumford datum `(tupleU x, tupleV x y)` of a tuple of curve points. -/
theorem isScaledState_foldBase (hx : Function.Injective x)
    (hcurve : ∀ i, y i ^ 2 = f.eval (x i)) :
    IsScaledState g f (foldBase f x y) (tupleU x) (tupleV x y) := by
  have hnd : nodeDen x ≠ 0 := nodeDen_ne_zero hx
  have hint : C (nodeDen x) * tupleV x y = tupleInterp x y := by
    rw [tupleV, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hnd, map_one, one_mul]
  have hdeg : (tupleU x).degree = (g : WithBot ℕ) := by
    rw [degree_eq_natDegree (monic_tupleU x).ne_zero, natDegree_tupleU]
  refine ⟨⟨monic_tupleU x, natDegree_tupleU x, ⟨_, tupleV_sq_sub hx hcurve⟩,
    hdeg ▸ degree_tupleV_lt⟩, pow_ne_zero 2 hnd, rfl, ?_, ?_⟩
  · change C (nodeDen x) * tupleInterp x y = C (nodeDen x ^ 2) * tupleV x y
    rw [← hint, ← mul_assoc, ← map_mul, ← sq]
  · change tupleWNum f x y = C (nodeDen x ^ 2) * cantorCofactor f (tupleU x) (tupleV x y)
    have hspec := cantorCofactor_spec f (monic_tupleU x) ⟨_, tupleV_sq_sub hx hcurve⟩
    rw [tupleWNum]
    refine divByMonic_eq_of_eq_add (monic_tupleU x) (r := 0) ?_ ?_
    · simp only [map_pow]
      rw [← hint]
      linear_combination (C (nodeDen x)) ^ 2 * hspec
    · rw [degree_zero]
      exact bot_lt_iff_ne_bot.mpr fun h ↦ (monic_tupleU x).ne_zero (degree_eq_bot.mp h)

/-- **The honest step conditions at an injective curve tuple are nonzero** once the
step-condition numerators up to the stage are. -/
theorem foldCond_ne_zero (hf : f.Monic) (hfdeg : f.natDegree = 2 * g + 1) (hg : 0 < g)
    (hx : Function.Injective x) (hcurve : ∀ i, y i ^ 2 = f.eval (x i)) {j : ℕ}
    (hj : j < 2 * g)
    (hc : ∀ i ≤ j, foldCondNum f (foldXs x) (foldYs y) (foldBase f x y) i ≠ 0) :
    foldCond f (foldXs x) (foldYs y) (tupleU x) (tupleV x y) j ≠ 0 := by
  have hbase := isScaledState_foldBase hx hcurve
  have hxeval : (tupleU x).eval (foldXs x 0) = 0 := by
    rw [foldXs_zero x hg]
    exact eval_tupleU_self x ⟨0, hg⟩
  have hVeval : (tupleV x y).eval (foldXs x 0) = foldYs y 0 := by
    rw [foldXs_zero x hg, foldYs_zero y hg]
    exact eval_tupleV hx ⟨0, hg⟩
  have heq := foldCondNum_eq_den_mul hf hfdeg hbase hxeval hVeval
    (fun i hi ↦ foldYs_sq hcurve (by lia)) fun i hi ↦ hc i hi.le
  intro h0
  exact hc j le_rfl (by rw [heq, h0, mul_zero])

end Base

/-! ### The engine instances of the universal condition numerators -/

section Engine

variable {κ : Type*} [Field κ] {g : ℕ}

/-- **The engine specialization** of the universal variables: the coordinates become the
variables of a tuple of plane points, the generic curve coefficients become the
coefficients of `f`. -/
noncomputable def curveSpec (f : κ[X]) (g : ℕ) :
    Fin g ⊕ Fin g ⊕ Fin (2 * g + 1) → MvPolynomial (Fin g × Fin 2) κ :=
  Sum.elim (fun i ↦ MvPolynomial.X (i, 0)) <|
    Sum.elim (fun i ↦ MvPolynomial.X (i, 1)) fun r ↦ MvPolynomial.C (f.coeff r)

/-- **The engine instances of the universal step-condition numerators `𝒩_q`**: polynomial
conditions on `g`-tuples of plane points, for the avoidance engine
(`ChabautyColeman.exists_curveTuple_ne_zero`). -/
noncomputable def curveCondNum (f : κ[X]) (g j : ℕ) : MvPolynomial (Fin g × Fin 2) κ :=
  MvPolynomial.aeval (curveSpec f g) (univCondNum κ g j)

variable {f : κ[X]}

/-- Evaluating the engine specialization of any universal polynomial at a (formal) tuple
of points is evaluating the universal polynomial at the coordinates and the coefficients
of `f`. -/
theorem aeval_aeval_curveSpec {A : Type*} [CommRing A] [Algebra κ A] (P : Fin g → A × A)
    (Q : MvPolynomial (Fin g ⊕ Fin g ⊕ Fin (2 * g + 1)) κ) :
    MvPolynomial.aeval (tupleCoords P) (MvPolynomial.aeval (curveSpec f g) Q)
      = MvPolynomial.aeval (Sum.elim (fun i ↦ (P i).1)
          (Sum.elim (fun i ↦ (P i).2) fun r : Fin (2 * g + 1) ↦
            algebraMap κ A (f.coeff r)))
        Q := by
  have hfun : (fun s ↦ MvPolynomial.aeval (tupleCoords P) (curveSpec f g s))
      = Sum.elim (fun i : Fin g ↦ (P i).1)
        (Sum.elim (fun i : Fin g ↦ (P i).2) fun r : Fin (2 * g + 1) ↦
          algebraMap κ A (f.coeff r)) := by
    funext s
    rcases s with i | i | r <;> simp [curveSpec, tupleCoords]
  rw [MvPolynomial.comp_aeval_apply, hfun]

/-- Evaluating an engine instance at a (formal) tuple of points is evaluating the
universal numerator at the coordinates and the coefficients of `f`. -/
theorem aeval_curveCondNum {A : Type*} [CommRing A] [Algebra κ A] (P : Fin g → A × A)
    (j : ℕ) :
    MvPolynomial.aeval (tupleCoords P) (curveCondNum f g j)
      = MvPolynomial.aeval (Sum.elim (fun i ↦ (P i).1)
          (Sum.elim (fun i ↦ (P i).2) fun r : Fin (2 * g + 1) ↦
            algebraMap κ A (f.coeff r)))
        (univCondNum κ g j) :=
  aeval_aeval_curveSpec P (univCondNum κ g j)

-- The coordinate evaluation at an honest tuple sends the universal inputs of the fold to
-- the tuple inputs; the coerced hom is spelled `(aeval …).toRingHom` throughout.
private theorem map_univF_eval (hf : f.Monic) (hfdeg : f.natDegree = 2 * g + 1)
    (x y : Fin g → κ) :
    (univF κ g).map (MvPolynomial.aeval (R := κ) (Sum.elim x
      (Sum.elim y fun r : Fin (2 * g + 1) ↦ f.coeff r))).toRingHom = f := by
  rw [univF, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
  conv_rhs => rw [hf.as_sum, hfdeg]
  rw [← Fin.sum_univ_eq_sum_range fun i ↦ C (f.coeff i) * X ^ i]
  congr 1
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  simp

private theorem univXs_map_eval (x y : Fin g → κ) :
    (fun i ↦ (MvPolynomial.aeval (R := κ) (Sum.elim x
        (Sum.elim y fun r : Fin (2 * g + 1) ↦ f.coeff r))).toRingHom (univXs κ g i))
      = foldXs x := by
  funext i
  rw [univXs_eq_foldXs, map_foldXs]
  congr 1
  funext i
  simp

private theorem univYs_map_eval (x y : Fin g → κ) :
    (fun i ↦ (MvPolynomial.aeval (R := κ) (Sum.elim x
        (Sum.elim y fun r : Fin (2 * g + 1) ↦ f.coeff r))).toRingHom (univYs κ g i))
      = foldYs y := by
  funext i
  rw [univYs_eq_foldYs, map_foldYs]
  congr 1
  funext i
  simp

private theorem map_univBase_eval (hf : f.Monic) (hfdeg : f.natDegree = 2 * g + 1)
    (x y : Fin g → κ) :
    (univBase κ g).map (MvPolynomial.aeval (R := κ) (Sum.elim x
      (Sum.elim y fun r : Fin (2 * g + 1) ↦ f.coeff r))).toRingHom = foldBase f x y := by
  rw [univBase, map_foldBase, map_univF_eval hf hfdeg x y]
  congr 1 <;> funext i <;> simp

/-- **The universal fold state maps to the numerator fold state at an honest tuple**
under the coordinate evaluation. -/
theorem map_foldNum_univ (hf : f.Monic) (hfdeg : f.natDegree = 2 * g + 1)
    (x y : Fin g → κ) (j : ℕ) :
    (foldNum (univF κ g) (univXs κ g) (univYs κ g) (univBase κ g) j).map
        (MvPolynomial.aeval (R := κ) (Sum.elim x (Sum.elim y fun r : Fin (2 * g + 1) ↦
          f.coeff r))).toRingHom
      = foldNum f (foldXs x) (foldYs y) (foldBase f x y) j := by
  rw [map_foldNum, map_univF_eval hf hfdeg x y, univXs_map_eval x y, univYs_map_eval x y,
    map_univBase_eval hf hfdeg x y]

/-- **The engine instances evaluate at an honest tuple to the numerator fold at the
tuple**: naturality of the fold under the coordinate evaluation. -/
theorem eval_curveCondNum (hf : f.Monic) (hfdeg : f.natDegree = 2 * g + 1)
    (x y : Fin g → κ) (j : ℕ) :
    MvPolynomial.eval (tupleCoords fun i ↦ (x i, y i)) (curveCondNum f g j)
      = foldCondNum f (foldXs x) (foldYs y) (foldBase f x y) j := by
  have h := aeval_curveCondNum (f := f) (fun i ↦ (x i, y i)) j
  rw [MvPolynomial.aeval_eq_eval] at h
  rw [h]
  have h2 := map_foldCondNum (f := univF κ g) (xs := univXs κ g) (ys := univYs κ g)
    (s₀ := univBase κ g)
    (MvPolynomial.aeval (R := κ) (Sum.elim x (Sum.elim y fun r : Fin (2 * g + 1) ↦
      f.coeff r))).toRingHom j
  rwa [map_univF_eval hf hfdeg x y, univXs_map_eval x y, univYs_map_eval x y,
    map_univBase_eval hf hfdeg x y] at h2

end Engine

/-! ### Refutation of the conditions at the all-at-infinity family -/

section Family

variable {κ : Type*} [Field κ] [IsAlgClosed κ] {g : ℕ} {f : κ[X]}

/-- **The master refutation of engine conditions**: the engine specialization of a
weighted-homogeneous universal polynomial with nonzero cusp specialization does not
vanish identically on curve tuples — the all-at-infinity Laurent family at the common
descent rates (at a per-condition budget above the weight) is a formal curve tuple at
which it takes a nonzero value. -/
theorem not_curveVanishing_of_cusp_ne_zero [NeZero (2 : κ)] (hf : f.Monic)
    (hfdeg : f.natDegree = 2 * g + 1)
    {Q : MvPolynomial (Fin g ⊕ Fin g ⊕ Fin (2 * g + 1)) κ} {d : ℤ}
    (hQ : Q.IsWeightedHomogeneous (univWt g) d)
    (hcusp : MvPolynomial.aeval (cuspSpec κ g) Q ≠ 0) :
    ¬CurveVanishing f g (MvPolynomial.aeval (curveSpec f g) Q) := by
  have hodd : Odd f.natDegree := ⟨g, by lia⟩
  set D : ℕ := d.toNat + 1
  have hn : ∀ i : Fin g, descRate D (D + 1) g i ≠ 0 := by
    intro i
    have h2 : 0 < D * (D + 1) ^ (g + 1) := by positivity
    lia [le_descRate D (D + 1) g i]
  choose η _ hηsq hηone using fun i : Fin g ↦
    exists_infinityPoint (K := κ) hf (NeZero.ne 2) (hn i)
  have hPcurve : ∀ i : Fin g,
      ((HahnSeries.single (-(2 * (descRate D (D + 1) g i : ℤ))) (1 : κ), η i) :
        LaurentSeries κ × LaurentSeries κ).2 ^ 2
      = Polynomial.aeval (HahnSeries.single (-(2 * (descRate D (D + 1) g i : ℤ)))
          (1 : κ), η i).1 f := by
    intro i
    have h := hηsq i
    rwa [neg_mul] at h
  refine not_curveVanishing_of_aeval_ne_zero f hf hodd hPcurve ?_
  rw [aeval_aeval_curveSpec]
  have hα : ∀ r : Fin (2 * g + 1),
      (0 : WithTop ℤ) ≤ (algebraMap κ (LaurentSeries κ) (f.coeff r)).orderTop := by
    intro r
    rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply]
    exact_mod_cast HahnSeries.orderTop_single_le
  have hη : ∀ i : Fin g, ((2 * (descRate D (D + 1) g i : ℤ)) : WithTop ℤ)
      ≤ (HahnSeries.single ((2 * g + 1) * (descRate D (D + 1) g i : ℤ)) 1 * η i
        - 1).orderTop := by
    intro i
    have h := hηone i
    rwa [show (f.natDegree : ℤ) * (descRate D (D + 1) g i : ℤ)
      = (2 * g + 1) * (descRate D (D + 1) g i : ℤ) by rw [hfdeg]; push_cast; ring] at h
  exact aeval_family_ne_zero hQ hcusp
    ((Int.self_le_toNat d).trans (mod_cast Nat.le_succ _))
    (Nat.succ_pos _) (Nat.lt_succ_self D) hη hα

/-- **No universal condition numerator vanishes identically on curve tuples**
(`thm:fold-witness`, per-condition half). -/
theorem not_curveVanishing_curveCondNum [NeZero (2 : κ)] (hf : f.Monic)
    (hfdeg : f.natDegree = 2 * g + 1) (hg2 : 2 ≤ g) {j : ℕ} (hj : j < 2 * g) :
    ¬CurveVanishing f g (curveCondNum f g j) :=
  not_curveVanishing_of_cusp_ne_zero hf hfdeg (isWeightedHomogeneous_univCondNum j)
    (cuspNum_ne_zero hg2 hj)

/-- The pairwise-distinctness conditions on the `x`-coordinates do not vanish identically
on curve tuples. -/
theorem not_curveVanishing_X_sub_X {i j : Fin g} (hij : i ≠ j) :
    ¬CurveVanishing f g (MvPolynomial.X (i, 0) - MvPolynomial.X (j, 0)) := by
  intro hv
  obtain ⟨a, b, hab⟩ := exists_pair_ne κ
  obtain ⟨ya, hya⟩ := IsAlgClosed.exists_pow_nat_eq (f.eval a) (n := 2) two_pos
  obtain ⟨yb, hyb⟩ := IsAlgClosed.exists_pow_nat_eq (f.eval b) (n := 2) two_pos
  classical
  set P : Fin g → κ × κ := fun t ↦ if t = i then (a, ya) else (b, yb) with hP
  have hPc : IsCurveTuple f P := by
    intro t
    simp only [hP]
    split_ifs <;> simpa
  have h := hv P hPc
  rw [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_X] at h
  have hi : tupleCoords P (i, 0) = a := by simp [tupleCoords, hP]
  have hj : tupleCoords P (j, 0) = b := by simp [tupleCoords, hP, hij.symm]
  rw [hi, hj, sub_eq_zero] at h
  exact hab h

/-! ### The all-genus fold witness -/

/-- **The all-genus fold witness** (`thm:fold-witness`): over an algebraically closed
field of characteristic `≠ 2`, for `f` monic of odd degree `2g + 1` with `g ≥ 2`, there is
a single tuple of affine curve points, with pairwise distinct `x`-coordinates, at which
all `2g` step-condition numerators of the fold — and hence all honest step conditions of
the point-by-point fold `τ + τ - τ` — are simultaneously nonzero.
(Statement-only blueprint anchor for `thm:fold-witness`: the assembly consumes the
avoidance-engine form `ChabautyColeman.exists_centerFoldPack` instead.) -/
theorem exists_foldWitness [NeZero (2 : κ)] (hf : f.Monic)
    (hfdeg : f.natDegree = 2 * g + 1) (hg2 : 2 ≤ g) :
    ∃ x y : Fin g → κ, (∀ i, y i ^ 2 = f.eval (x i)) ∧ Function.Injective x
      ∧ (∀ j < 2 * g, foldCondNum f (foldXs x) (foldYs y) (foldBase f x y) j ≠ 0)
      ∧ ∀ j < 2 * g, foldCond f (foldXs x) (foldYs y) (tupleU x) (tupleV x y) j ≠ 0 := by
  classical
  have hodd : Odd f.natDegree := ⟨g, by lia⟩
  obtain ⟨P, hP, hne⟩ := exists_curveTuple_ne_zero hf hodd
    ((Finset.range (2 * g)).image (curveCondNum f g)
      ∪ ((Finset.univ.filter fun p : Fin g × Fin g ↦ p.1 ≠ p.2).image
        fun p ↦ MvPolynomial.X (p.1, 0) - MvPolynomial.X (p.2, 0)))
    (by
      intro F hF
      rcases Finset.mem_union.mp hF with h | h
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
        exact not_curveVanishing_curveCondNum hf hfdeg hg2 (Finset.mem_range.mp hj)
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
        exact not_curveVanishing_X_sub_X (Finset.mem_filter.mp hp).2)
  have hxinj : Function.Injective fun i ↦ (P i).1 := by
    intro i j hijeq
    by_contra hij
    have h := hne _ (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩))
    rw [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_X] at h
    exact h (by simpa [tupleCoords] using sub_eq_zero.mpr hijeq)
  have hcond : ∀ j < 2 * g, foldCondNum f (foldXs fun i ↦ (P i).1)
      (foldYs fun i ↦ (P i).2)
      (foldBase f (fun i ↦ (P i).1) fun i ↦ (P i).2) j ≠ 0 := by
    intro j hj
    have h2 : MvPolynomial.eval (tupleCoords fun i ↦ ((P i).1, (P i).2))
        (curveCondNum f g j) ≠ 0 :=
      hne _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩))
    rwa [eval_curveCondNum hf hfdeg] at h2
  exact ⟨fun i ↦ (P i).1, fun i ↦ (P i).2, hP, hxinj, hcond,
    fun j hj ↦ foldCond_ne_zero hf hfdeg (by lia) hxinj hP hj fun i hi ↦
      hcond i (by lia)⟩

end Family

end ChabautyColeman

end
