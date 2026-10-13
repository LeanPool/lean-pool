/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.BlockResponse
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Events

/-!
# DescendantLattice

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The descendant enumeration and the lattice enumeration are the same list

ABK26, Section 4.1 writes every per-scale maximum as a maximum over the lattice
translates

```
max_{z in 3^n Z^d cap cu_m}  ( . )(z + cu_n) ,
```

while the proved `(infinity,2)` identity of `d.mathcal.E` runs its maximum over
`descendantsAtScale (cu_m) n`, the triadic descendants of `cu_m` at scale `n`.
This module proves that the two enumerate the *same* cubes, in both directions,
and transfers maxima across the correspondence.

## The arithmetic content

A triadic cube is a scale together with an integer index, and its point set is
the translate of the origin cube of that scale by `3^scale * index`.  The
descendants of `cu_m` at depth `t` are exactly the cubes of scale `m - t` whose
index `v` satisfies the balanced-ternary box condition

```
2 |v_i| < 3^t     for every coordinate `i`,
```

which is proved here by induction on `t` from `childCubes` (each step multiplies
the index by `3` and adds a balanced digit in `{-1,0,1}`; the reverse step
divides by `3`, where oddness of `3^t` supplies the strict inequality).  The
lattice side `3^n Z^d cap cu_m` -- i.e. `Support.latticeCubeSet d n m` -- unfolds
to `|3^n v_i| < 3^m / 2`, the same condition with `t = m - n`.  Hence the
identification, with no geometric hypothesis beyond `n <= m`.

## What is proved

* `mem_descendantsAtDepth_iff` -- the index-box characterization of descendants.
* `mem_latticeCubeSet_iff` -- the same box, read off the Section 4 lattice set.
* `mem_descendantsAtScale_originCube_iff`, `latticeCube_mem_descendantsAtScale`,
  `eq_latticeCube_of_mem_descendantsAtScale` -- the correspondence, both ways.
* `latticeCubeFinset`, `descendantsAtScale_originCube_eq_image` -- the index
  bijection of the descendant enumeration.
* `maxDescendantNormalizedBlockResponse_le_of_lattice_bounds` and
  `eightEss_blockResponse_le_of_lattice_bounds` -- the two targets joined: the
  scale-`n` descendant maximum of the normalized block response is bounded by
  the manuscript's two lattice maxima of the scalar `J`, at the field and at its
  transpose, with constant `1`.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## Integer bookkeeping -/

private theorem two_abs_lt_iff {y K : ℤ} : 2 * |y| < K ↔ (-K < 2 * y ∧ 2 * y < K) := by
  rcases abs_cases y with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> omega

private theorem three_pow_odd (t : ℕ) : ∃ j : ℤ, (3 : ℤ) ^ t = 2 * j + 1 := by
  induction t with
  | zero => exact ⟨0, by norm_num⟩
  | succ t ih =>
      obtain ⟨j, hj⟩ := ih
      refine ⟨3 * j + 1, ?_⟩
      rw [pow_succ, hj]
      ring

/-- One triadic refinement step, in the index coordinate: a balanced digit shifts
the box bound from `K` to `3K`. -/
private theorem child_index_bound {b w K D : ℤ} (hD0 : 0 ≤ D) (hD3 : D < 3)
    (h : 2 * |b - w| < K) :
    2 * |3 * b + D - 1 - 3 * w| < 3 * K := by
  rw [two_abs_lt_iff] at h ⊢
  omega

/-- One triadic coarsening step: the parent index `(a+1)/3` sits in the box of
half the size.  The strict inequality uses that `K = 3^t` is odd. -/
private theorem parent_index_bound {a w K j : ℤ} (hK : K = 2 * j + 1)
    (h : 2 * |a - 3 * w| < 3 * K) :
    2 * |(a + 1) / 3 - w| < K := by
  rw [two_abs_lt_iff] at h ⊢
  omega

/-! ## The index-box characterization of the descendants -/

/-- **The descendants of a triadic cube, in index coordinates.**  The depth-`t`
descendants of `Q` are exactly the scale-`(Q.scale - t)` cubes whose index lies
in the balanced box of radius `3^t / 2` around `3^t Q.index`. -/
theorem mem_descendantsAtDepth_iff (Q R : TriadicCube d) (t : ℕ) :
    R ∈ descendantsAtDepth Q t ↔
      (R.scale = Q.scale - (t : ℤ) ∧
        ∀ i, 2 * |R.index i - 3 ^ t * Q.index i| < 3 ^ t) := by
  induction t generalizing R with
  | zero =>
      constructor
      · intro hR
        rw [descendantsAtDepth_zero, Finset.mem_singleton] at hR
        subst hR
        refine ⟨by simp, ?_⟩
        intro i
        simp
      · rintro ⟨hs, hi⟩
        rw [descendantsAtDepth_zero, Finset.mem_singleton]
        have hidx : ∀ i, R.index i = Q.index i := by
          intro i
          have hii := hi i
          rw [pow_zero, one_mul, two_abs_lt_iff] at hii
          omega
        cases R with
        | mk rs ri =>
            cases Q with
            | mk qs qi =>
                simp only [TriadicCube.mk.injEq]
                refine ⟨?_, funext hidx⟩
                simpa using hs
  | succ t ih =>
      constructor
      · intro hR
        rw [mem_descendantsAtDepth_succ_iff] at hR
        obtain ⟨S, hS, hRS⟩ := hR
        obtain ⟨hSs, hSi⟩ := (ih S).mp hS
        obtain ⟨digits, rfl⟩ := mem_childCubes_iff.mp hRS
        refine ⟨by push_cast; omega, ?_⟩
        intro i
        have hD0 : (0 : ℤ) ≤ ((digits i : ℕ) : ℤ) := Int.natCast_nonneg _
        have hD3 : ((digits i : ℕ) : ℤ) < 3 := by exact_mod_cast (digits i).isLt
        have hstep := child_index_bound (b := S.index i) (w := 3 ^ t * Q.index i)
          (K := 3 ^ t) (D := ((digits i : ℕ) : ℤ)) hD0 hD3 (hSi i)
        have hrw : 3 * S.index i + ((digits i : ℕ) : ℤ) - 1 - 3 * (3 ^ t * Q.index i)
            = 3 * S.index i + ((digits i : ℕ) : ℤ) - 1 - 3 ^ (t + 1) * Q.index i := by
          ring
        have hrw3 : (3 : ℤ) * 3 ^ t = 3 ^ (t + 1) := by ring
        rw [hrw, hrw3] at hstep
        exact hstep
      · rintro ⟨hs, hi⟩
        rw [mem_descendantsAtDepth_succ_iff]
        obtain ⟨j, hj⟩ := three_pow_odd t
        refine ⟨{ scale := Q.scale - (t : ℤ)
                  index := fun i => (R.index i + 1) / 3 }, ?_, ?_⟩
        · refine (ih _).mpr ⟨rfl, ?_⟩
          intro i
          have hii := hi i
          have hrw : (3 : ℤ) ^ (t + 1) * Q.index i = 3 * (3 ^ t * Q.index i) := by ring
          have hrw3 : (3 : ℤ) ^ (t + 1) = 3 * 3 ^ t := by ring
          rw [hrw, hrw3] at hii
          exact parent_index_bound (w := 3 ^ t * Q.index i) hj hii
        · rw [mem_childCubes_iff]
          refine ⟨fun i => ⟨((R.index i + 1) % 3).toNat, ?_⟩, ?_⟩
          · have h0 : 0 ≤ (R.index i + 1) % 3 := Int.emod_nonneg _ (by norm_num)
            have h3 : (R.index i + 1) % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
            omega
          · have hidx : ∀ i, R.index i
                = 3 * ((R.index i + 1) / 3) + (((R.index i + 1) % 3).toNat : ℤ) - 1 := by
              intro i
              have h0 : 0 ≤ (R.index i + 1) % 3 := Int.emod_nonneg _ (by norm_num)
              have hcast : (((R.index i + 1) % 3).toNat : ℤ) = (R.index i + 1) % 3 :=
                Int.toNat_of_nonneg h0
              rw [hcast]
              omega
            cases R with
            | mk rs ri =>
                simp only [TriadicCube.mk.injEq]
                constructor
                · push_cast at hs ⊢
                  omega
                · funext i
                  simpa using hidx i

/-! ## The lattice enumeration -/

/-- The scale-`n` triadic cube based at the lattice point `3^n v`. -/
def latticeCube (n : ℤ) (v : Fin d → ℤ) : TriadicCube d :=
  { scale := n, index := v }

@[simp] theorem latticeCube_scale (n : ℤ) (v : Fin d → ℤ) :
    (latticeCube n v).scale = n := rfl

@[simp] theorem latticeCube_index (n : ℤ) (v : Fin d → ℤ) :
    (latticeCube n v).index = v := rfl

theorem latticeCube_index_self (R : TriadicCube d) :
    latticeCube R.scale R.index = R := rfl

private theorem lattice_coord_iff {A x Kr : ℝ} (hA : 0 < A) :
    ((-(1 / 2) : ℝ) * (A * Kr) < A * x ∧ A * x < (1 / 2 : ℝ) * (A * Kr)) ↔
      2 * |x| < Kr := by
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : A * (-(1 / 2) * Kr) < A * x := by linarith only [h1]
    have h2' : A * x < A * ((1 / 2) * Kr) := by linarith only [h2]
    have hlo : -(1 / 2) * Kr < x := lt_of_mul_lt_mul_left h1' hA.le
    have hhi : x < (1 / 2) * Kr := lt_of_mul_lt_mul_left h2' hA.le
    have hx : |x| < Kr / 2 := abs_lt.mpr ⟨by linarith only [hlo], by linarith only [hhi]⟩
    linarith only [hx]
  · intro h
    have hx : |x| < Kr / 2 := by linarith only [h]
    rcases abs_lt.mp hx with ⟨h1, h2⟩
    have hlo := mul_lt_mul_of_pos_left (show -(1 / 2) * Kr < x by linarith only [h1]) hA
    have hhi := mul_lt_mul_of_pos_left (show x < (1 / 2) * Kr by linarith only [h2]) hA
    exact ⟨by linarith only [hlo], by linarith only [hhi]⟩

/-- **`3^n Z^d cap cu_m`, in index coordinates.**  A scale-`n` lattice point lies
in the open cube `cu_m` exactly when its index lies in the balanced box of
radius `3^{m-n} / 2`. -/
theorem mem_latticeCubeSet_iff {n m : ℤ} (hnm : n ≤ m) (v : Fin d → ℤ) :
    v ∈ latticeCubeSet d n m ↔ ∀ i, 2 * |v i| < 3 ^ (m - n).toNat := by
  have hmn : m = n + ((m - n).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  have hpow : (3 : ℝ) ^ m = (3 : ℝ) ^ n * (3 : ℝ) ^ ((m - n).toNat : ℕ) := by
    rw [hmn, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
    congr 1
    rw [← hmn]
  have hA : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  constructor
  · intro hv i
    have hmem : triadicLatticePoint n v ∈ openCubeSet (originCube d m) := hv
    rw [mem_openCubeSet_originCube_iff] at hmem
    have hi := hmem i
    rw [hpow] at hi
    have hval : triadicLatticePoint n v i = (3 : ℝ) ^ n * ((v i : ℤ) : ℝ) := rfl
    rw [hval] at hi
    have hreal : 2 * |((v i : ℤ) : ℝ)| < (3 : ℝ) ^ ((m - n).toNat : ℕ) :=
      (lattice_coord_iff hA).mp hi
    exact_mod_cast hreal
  · intro hv
    show triadicLatticePoint n v ∈ openCubeSet (originCube d m)
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have hreal : 2 * |((v i : ℤ) : ℝ)| < (3 : ℝ) ^ ((m - n).toNat : ℕ) := by
      exact_mod_cast hv i
    have hval : triadicLatticePoint n v i = (3 : ℝ) ^ n * ((v i : ℤ) : ℝ) := rfl
    rw [hval, hpow]
    exact (lattice_coord_iff hA).mpr hreal

/-! ## The correspondence -/

/-- **The descendants of `cu_m` at scale `n` are the lattice cubes of
`3^n Z^d cap cu_m`.** -/
theorem mem_descendantsAtScale_originCube_iff {n m : ℤ} (hnm : n ≤ m)
    (R : TriadicCube d) :
    R ∈ descendantsAtScale (originCube d m) n ↔
      (R.scale = n ∧ R.index ∈ latticeCubeSet d n m) := by
  have hscale : (originCube d m).scale = m := rfl
  rw [descendantsAtScale_eq_descendantsAtDepth (originCube d m) (by rw [hscale]; exact hnm),
    hscale, mem_descendantsAtDepth_iff, mem_latticeCubeSet_iff hnm]
  have hidx : (originCube d m).index = 0 := rfl
  have htoNat : ((m - n).toNat : ℤ) = m - n := Int.toNat_of_nonneg (by omega)
  constructor
  · rintro ⟨hs, hi⟩
    refine ⟨by omega, ?_⟩
    intro i
    have := hi i
    rw [hidx] at this
    simpa using this
  · rintro ⟨hs, hi⟩
    refine ⟨by omega, ?_⟩
    intro i
    have := hi i
    rw [hidx]
    simpa using this

theorem latticeCube_mem_descendantsAtScale {n m : ℤ} (hnm : n ≤ m) {v : Fin d → ℤ}
    (hv : v ∈ latticeCubeSet d n m) :
    latticeCube n v ∈ descendantsAtScale (originCube d m) n :=
  (mem_descendantsAtScale_originCube_iff hnm _).mpr ⟨rfl, hv⟩

theorem scale_eq_of_mem_descendantsAtScale_originCube {n m : ℤ} (hnm : n ≤ m)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d m) n) :
    R.scale = n :=
  ((mem_descendantsAtScale_originCube_iff hnm R).mp hR).1

theorem index_mem_latticeCubeSet_of_mem_descendantsAtScale {n m : ℤ} (hnm : n ≤ m)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d m) n) :
    R.index ∈ latticeCubeSet d n m :=
  ((mem_descendantsAtScale_originCube_iff hnm R).mp hR).2

/-- Every descendant is the lattice cube at its own base point. -/
theorem eq_latticeCube_of_mem_descendantsAtScale {n m : ℤ} (hnm : n ≤ m)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d m) n) :
    R = latticeCube n R.index := by
  have hs : R.scale = n := scale_eq_of_mem_descendantsAtScale_originCube hnm hR
  rw [← hs]
  exact (latticeCube_index_self R).symm

/-! ## The index bijection and the transfer of maxima -/

/-- The finite index set of `3^n Z^d cap cu_m`. -/
def latticeCubeFinset (d : ℕ) (n m : ℤ) : Finset (Fin d → ℤ) :=
  (descendantsAtScale (originCube d m) n).image TriadicCube.index

theorem mem_latticeCubeFinset_iff {n m : ℤ} (hnm : n ≤ m) (v : Fin d → ℤ) :
    v ∈ latticeCubeFinset d n m ↔ v ∈ latticeCubeSet d n m := by
  constructor
  · intro hv
    obtain ⟨R, hR, hRv⟩ := Finset.mem_image.mp hv
    rw [← hRv]
    exact index_mem_latticeCubeSet_of_mem_descendantsAtScale hnm hR
  · intro hv
    refine Finset.mem_image.mpr ⟨latticeCube n v, ?_, rfl⟩
    exact latticeCube_mem_descendantsAtScale hnm hv

/-- **The index bijection**: the descendant family is the image of the lattice
index set under `v |-> 3^n v + cu_n`. -/
theorem descendantsAtScale_originCube_eq_image {n m : ℤ} (hnm : n ≤ m) :
    descendantsAtScale (originCube d m) n
      = (latticeCubeFinset d n m).image (latticeCube n) := by
  ext R
  constructor
  · intro hR
    refine Finset.mem_image.mpr ⟨R.index, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨R, hR, rfl⟩
    · exact (eq_latticeCube_of_mem_descendantsAtScale hnm hR).symm
  · intro hR
    obtain ⟨v, hv, hvR⟩ := Finset.mem_image.mp hR
    rw [← hvR]
    exact latticeCube_mem_descendantsAtScale hnm ((mem_latticeCubeFinset_iff hnm v).mp hv)

theorem latticeCube_injective (n : ℤ) :
    Function.Injective (latticeCube (d := d) n) := by
  intro v w hvw
  have := congrArg TriadicCube.index hvw
  simpa using this

/-- **The lattice count** `#(3^n Z^d cap cu_m) = 3^{d(m-n)}`, obtained from the
descendant count through the index bijection. -/
theorem latticeCubeFinset_card {n m : ℤ} (hnm : n ≤ m) :
    (latticeCubeFinset d n m).card = ((3 : ℕ) ^ d) ^ (m - n).toNat := by
  classical
  have hscale : (originCube d m).scale = m := rfl
  have hcard : (descendantsAtScale (originCube d m) n).card
      = ((3 : ℕ) ^ d) ^ (m - n).toNat := by
    rw [descendantsAtScale_eq_descendantsAtDepth (originCube d m) (by rw [hscale]; exact hnm),
      descendantsAtDepth_card, hscale]
  rw [descendantsAtScale_originCube_eq_image hnm,
    Finset.card_image_of_injective _ (latticeCube_injective (d := d) n)] at hcard
  exact hcard

/-! ## The two targets joined -/

/-- **The `e.bfJ.general` conversion, at the manuscript's lattice enumeration**
(with the transpose remark).

The scale-`n` descendant maximum of the normalized block response -- the inner
quantity of the `(infinity,2)` error at scale `n` -- is bounded by the sum of the
two lattice maxima of the scalar response, one for the field and one for its
transpose, over `z in 3^n Z^d cap cu_m` and unit loads. -/
theorem maxDescendantNormalizedBlockResponse_le_of_lattice_bounds [NeZero d]
    (F : TriadicCoeffFamily d) {n m : ℤ} (hnm : n ≤ m)
    (sigma : Observable.PositiveScalar) {Jf Jt : ℝ}
    (hfld : ∀ v ∈ latticeCubeSet d n m, ∀ e : Vec d, vecNorm e = 1 →
      responseJ (cubeDomain (latticeCube n v)) (F.coeffOn (latticeCube n v))
        (Observable.inverseSqrtLoad sigma e) (Observable.sqrtLoad sigma e) ≤ Jf)
    (htrn : ∀ v ∈ latticeCubeSet d n m, ∀ e : Vec d, vecNorm e = 1 →
      responseJ (cubeDomain (latticeCube n v)) (F.coeffOn (latticeCube n v)).transpose
        (Observable.inverseSqrtLoad sigma e) (Observable.sqrtLoad sigma e) ≤ Jt) :
    maxDescendantNormalizedBlockResponseAtScale (originCube d m) n F
        (Observable.isotropicComparatorMatrix sigma)
      ≤ Jf + Jt := by
  refine maxDescendantNormalizedBlockResponseAtScale_isotropicComparator_le F
    (originCube d m) (by exact hnm) sigma ?_ ?_
  · intro R hR e he
    rw [eq_latticeCube_of_mem_descendantsAtScale hnm hR]
    exact hfld R.index (index_mem_latticeCubeSet_of_mem_descendantsAtScale hnm hR) e he
  · intro R hR e he
    rw [eq_latticeCube_of_mem_descendantsAtScale hnm hR]
    exact htrn R.index (index_mem_latticeCubeSet_of_mem_descendantsAtScale hnm hR) e he

/-- The same statement in the scale-sum indexing `n = m - l` of the
`(infinity,2)` opening: this is exactly the `hbfJ` slot of the eight-ess display,
at the constant `1`. -/
theorem eightEss_blockResponse_le_of_lattice_bounds [NeZero d]
    (F : TriadicCoeffFamily d) (m : ℤ) (sigma : Observable.PositiveScalar)
    {Jfld Jtrn : ℕ → ℝ}
    (hfld : ∀ l : ℕ, ∀ v ∈ latticeCubeSet d (m - (l : ℤ)) m, ∀ e : Vec d, vecNorm e = 1 →
      responseJ (cubeDomain (latticeCube (m - (l : ℤ)) v))
          (F.coeffOn (latticeCube (m - (l : ℤ)) v))
        (Observable.inverseSqrtLoad sigma e) (Observable.sqrtLoad sigma e) ≤ Jfld l)
    (htrn : ∀ l : ℕ, ∀ v ∈ latticeCubeSet d (m - (l : ℤ)) m, ∀ e : Vec d, vecNorm e = 1 →
      responseJ (cubeDomain (latticeCube (m - (l : ℤ)) v))
          (F.coeffOn (latticeCube (m - (l : ℤ)) v)).transpose
        (Observable.inverseSqrtLoad sigma e) (Observable.sqrtLoad sigma e) ≤ Jtrn l) :
    ∀ l : ℕ,
      maxDescendantNormalizedBlockResponseAtScale (originCube d m) (m - (l : ℤ)) F
          (Observable.isotropicComparatorMatrix sigma)
        ≤ 1 * (Jfld l + Jtrn l) := by
  intro l
  have hnm : m - (l : ℤ) ≤ m := by
    have : (0 : ℤ) ≤ (l : ℤ) := Int.natCast_nonneg l
    omega
  rw [one_mul]
  exact maxDescendantNormalizedBlockResponse_le_of_lattice_bounds F hnm sigma
    (hfld l) (htrn l)

end

end Algsuperdiff.Section4.Provider.Annular
