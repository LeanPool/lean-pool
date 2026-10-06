/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedSubadditivity
public import LeanPool.HighContrastHomogenization.Provider.Response.DomainBridge

/-!
# High-contrast homogenization: Provider.Response.WeakNorm

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The adapted concrete weak norm

The weak-norm estimate for the optimizer state measures the doubled block state
of a response maximizer in the *concrete scale-average seminorm*,

```
[F]_{B^{-s}_{2,1}(U_t)} = Σ_{k = -∞}^{t} 3^{sk}
    ( avsum_{z ∈ 𝒵_{k,t}^q} |(F)_{U_k(z)}|^2 )^{1/2},
```

on the adapted cube `U_t = q□_t` subdivided into the aligned cells
`U_k(z) = z + q□_k`, `z ∈ 𝒵_{k,t}^q = 3^k𝕃_q ∩ U_t`.  This is the concrete
seminorm of [Armstrong–Kuusi, (2.130)], not the negative Besov dual norm: no
duality, no projection, and no cutoff enters, and the only structure the cells
carry is their exact partition of the parent — its count and its equal
volumes.

This module carries the definitions and their defining equations; the way the
cell average meets the metric root and the centering is the companion module.

* `alignedIndex` is `𝒵_{k,t}^q`, the finite label set of the aligned centres;
* `avsum` is the printed normalized average over the aligned children of a cell;
* `blockCellAverage` is `(F)_U` for an `ℝ^{2d}`-valued field;
* `metricBlockNormSq` is `|M_0^{1/2}v|^2` written on the quadratic form of the
  diagonal metric `M_0 = diag(m_0, m_0^{-1})`, which is how its self-duality is
  used;
* `blockAvsumL2` is the inner factor `(avsum_z |·|^2)^{1/2}` of the seminorm;
* `adaptedWeakScaleTerm` is one summand `3^{sk}(avsum_z |(F)_{U_k(z)}|^2)^{1/2}`;
* `adaptedWeakSeminorm` is the seminorm itself.

The `k`-sum runs to `-∞` and is not asserted convergent, so the seminorm is
valued in `ℝ≥0∞`, where the sum of a family of nonnegative terms is always
defined and monotone; the lemma is asserted *"valid when its right side is
infinite"*.  Each summand is a genuine nonnegative real — the inner average is
a normalized sum of squared Euclidean lengths — so no truncation happens below
the level of the `k`-sum, and the real value is recovered on the summable
branch.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The aligned index set -/

open scoped Classical in
/-- The aligned index `𝒵_{j,p}^q = 3^j𝕃_q ∩ ⋄_p^q` of the adapted cells, carried
by the lattice labels of its centres: the labels `w` for which the aligned
centre `3^jqw` lies in the parent cell.  The
set of such labels is finite exactly on the printed range `j ≤ p` of a positive
grid, and there the definition returns it. -/
@[expose]
def alignedIndex (q : Mat d) (j p : ℤ) : Finset (Fin d → ℤ) :=
  if h : {w : Fin d → ℤ | adaptedCellCenter q j w ∈ adaptedCell q p}.Finite then
    h.toFinset
  else ∅

/-- **The defining equation of the aligned index**: on the printed range its
elements are exactly the labels of the aligned centres inside the parent cell. -/
theorem coe_alignedIndex {q : Mat d} (hq : q.PosDef) {j p : ℤ} (hjp : j ≤ p) :
    (alignedIndex q j p : Set (Fin d → ℤ)) =
      {w : Fin d → ℤ | adaptedCellCenter q j w ∈ adaptedCell q p} := by
  classical
  obtain ⟨Z, hZ, _⟩ := Recurrence.exists_finset_adaptedCellCenter_mem hq hjp
  have hfin : {w : Fin d → ℤ | adaptedCellCenter q j w ∈ adaptedCell q p}.Finite :=
    hZ ▸ Z.finite_toSet
  rw [alignedIndex, dite_eq_left hfin, hfin.coe_toFinset]

/-- Membership in the aligned index. -/
theorem mem_alignedIndex_iff {q : Mat d} (hq : q.PosDef) {j p : ℤ} (hjp : j ≤ p)
    {w : Fin d → ℤ} :
    w ∈ alignedIndex q j p ↔ adaptedCellCenter q j w ∈ adaptedCell q p := by
  have h := coe_alignedIndex hq hjp
  constructor
  · intro hw
    have : w ∈ (alignedIndex q j p : Set (Fin d → ℤ)) := Finset.mem_coe.mpr hw
    rwa [h] at this
  · intro hw
    have : w ∈ (alignedIndex q j p : Set (Fin d → ℤ)) := by rw [h]; exact hw
    exact Finset.mem_coe.mp this

/-- **`#𝒵_{j,p}^q = 3^{d(p-j)}`**, the count of the aligned children of a
cell. -/
theorem card_alignedIndex {q : Mat d} (hq : q.PosDef) {j p : ℤ} (hjp : j ≤ p) :
    (alignedIndex q j p).card = 3 ^ (d * (p - j).toNat) :=
  Recurrence.card_alignedIndex hq hjp (coe_alignedIndex hq hjp)

/-- The aligned index is nonempty: it has `3^{d(p-j)}` elements. -/
theorem alignedIndex_nonempty {q : Mat d} (hq : q.PosDef) {j p : ℤ} (hjp : j ≤ p) :
    (alignedIndex q j p).Nonempty := by
  rw [← Finset.card_pos, card_alignedIndex hq hjp]
  positivity

/-- **The aligned cells sit inside the parent cell**: the containment
`U_k(z) ⊆ U_t` of the adapted cells. -/
theorem adaptedCellAt_subset_of_mem_alignedIndex {q : Mat d} (hq : q.PosDef) {j p : ℤ}
    (hjp : j ≤ p) {w : Fin d → ℤ} (hw : w ∈ alignedIndex q j p) :
    adaptedCellAt q j w ⊆ adaptedCell q p :=
  Recurrence.adaptedCellAt_subset_adaptedCell hq hjp ((mem_alignedIndex_iff hq hjp).mp hw)

/-! ## The normalized cell average -/

/-- The printed normalized average `avsum_{z ∈ 𝒵} f(z) = 3^{-d(t-k)}Σ_z f(z)`
over the aligned children of a cell, written with the reciprocal cardinality so
that no count has to be substituted before it is used. -/
@[expose]
def avsum {ι : Type*} (Z : Finset ι) (f : ι → ℝ) : ℝ :=
  ((Z.card : ℝ))⁻¹ * ∑ z ∈ Z, f z

/-- The defining equation of the normalized average. -/
theorem avsum_eq {ι : Type*} (Z : Finset ι) (f : ι → ℝ) :
    avsum Z f = ((Z.card : ℝ))⁻¹ * ∑ z ∈ Z, f z := rfl

/-- A normalized average of nonnegative terms is nonnegative. -/
theorem avsum_nonneg {ι : Type*} {Z : Finset ι} {f : ι → ℝ} (hf : ∀ z ∈ Z, 0 ≤ f z) :
    0 ≤ avsum Z f :=
  mul_nonneg (by positivity) (Finset.sum_nonneg hf)

/-- The normalized average of a constant is that constant. -/
theorem avsum_const {ι : Type*} {Z : Finset ι} (hZ : Z.Nonempty) (c : ℝ) :
    avsum Z (fun _ => c) = c := by
  have hcard : ((Z.card : ℝ)) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hZ).ne'
  rw [avsum_eq, Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- The normalized average is monotone. -/
theorem avsum_le_avsum {ι : Type*} {Z : Finset ι} {f g : ι → ℝ} (h : ∀ z ∈ Z, f z ≤ g z) :
    avsum Z f ≤ avsum Z g :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) (by positivity)

/-- A normalized average is at most a uniform upper bound of its terms. -/
theorem avsum_le_of_forall_le {ι : Type*} {Z : Finset ι} {f : ι → ℝ} {c : ℝ}
    (hZ : Z.Nonempty) (h : ∀ z ∈ Z, f z ≤ c) : avsum Z f ≤ c := by
  calc avsum Z f ≤ avsum Z (fun _ => c) := avsum_le_avsum h
    _ = c := avsum_const hZ c

/-- The normalized average is additive. -/
theorem avsum_add {ι : Type*} (Z : Finset ι) (f g : ι → ℝ) :
    avsum Z (fun z => f z + g z) = avsum Z f + avsum Z g := by
  rw [avsum_eq, avsum_eq, avsum_eq, Finset.sum_add_distrib, mul_add]

/-- A constant factors out of the normalized average. -/
theorem avsum_const_mul {ι : Type*} (Z : Finset ι) (c : ℝ) (f : ι → ℝ) :
    avsum Z (fun z => c * f z) = c * avsum Z f := by
  rw [avsum_eq, avsum_eq, ← Finset.mul_sum]
  ring

/-! ## The cell average of a doubled field -/

/-- The cell average `(F)_U` of an `ℝ^{2d}`-valued field, taken slotwise: this
is the quantity the scale-average seminorm evaluates on every aligned cell. -/
@[expose]
def blockCellAverage (U : Set (Vec d)) (F : Vec d → BlockVec d) : BlockVec d :=
  (volumeAverageVec U fun x => (F x).1, volumeAverageVec U fun x => (F x).2)

/-- The first slot of the cell average. -/
@[simp] theorem blockCellAverage_fst (U : Set (Vec d)) (F : Vec d → BlockVec d) :
    (blockCellAverage U F).1 = volumeAverageVec U fun x => (F x).1 := rfl

/-- The second slot of the cell average. -/
@[simp] theorem blockCellAverage_snd (U : Set (Vec d)) (F : Vec d → BlockVec d) :
    (blockCellAverage U F).2 = volumeAverageVec U fun x => (F x).2 := rfl

/-- **The cell average of the doubled optimizer state**: for
`X(V) = (∇v, a∇v)` the slotwise average is the pair of averages the variational
average identity is written on. -/
theorem blockCellAverage_gradFlux (U : Domain d) (a : CoeffOn U) (v : Solution U a) :
    blockCellAverage (U : Set (Vec d))
        (fun x => ((v.toH1.grad x, matVecMul (a.toCoeffField x) (v.toH1.grad x)) : BlockVec d)) =
      ((Book.Ch02.averageGradient U a v, averageFlux U a v) : BlockVec d) := rfl

/-! ## The metric quadratic form -/

/-- The squared metric length `|M_0^{1/2}v|^2 = v·M_0v` of the diagonal metric
`M_0 = diag(m_0, m_0^{-1})`, read as a quadratic form.  This is the reading of
its self-duality that the weak-norm estimate uses; it needs no matrix root. -/
@[expose]
def metricBlockNormSq (m : Mat d) (v : BlockVec d) : ℝ :=
  blockVecDot v (blockMatVecMul (blockDiag m m⁻¹) v)

/-- The defining equation of the metric quadratic form, slot by slot. -/
theorem metricBlockNormSq_eq (m : Mat d) (v : BlockVec d) :
    metricBlockNormSq m v = vecDot v.1 (matVecMul m v.1) + vecDot v.2 (matVecMul m⁻¹ v.2) := by
  show vecDot v.1 (matVecMul m v.1 + matVecMul 0 v.2) +
      vecDot v.2 (matVecMul 0 v.1 + matVecMul m⁻¹ v.2) = _
  rw [zero_matVecMul, zero_matVecMul, add_zero, zero_add]

/-! ## The seminorm -/

/-- The inner factor `(avsum_{z ∈ 𝒵}|g(z)|^2)^{1/2}` of the scale-average
seminorm: the normalized `ℓ^2` length of a family of
`ℝ^{2d}` vectors indexed by the aligned centres of one scale. -/
@[expose]
def blockAvsumL2 {ι : Type*} (Z : Finset ι) (g : ι → BlockVec d) : ℝ :=
  Real.sqrt (avsum Z fun z => blockVecDot (g z) (g z))

/-- The defining equation of the normalized `ℓ^2` length. -/
theorem blockAvsumL2_eq {ι : Type*} (Z : Finset ι) (g : ι → BlockVec d) :
    blockAvsumL2 Z g = Real.sqrt (avsum Z fun z => blockVecDot (g z) (g z)) := rfl

/-- The squared Euclidean length of a doubled vector is nonnegative. -/
theorem blockVecDot_self_nonneg (v : BlockVec d) : 0 ≤ blockVecDot v v :=
  add_nonneg (vecNormSq_nonneg v.1) (vecNormSq_nonneg v.2)

/-- The normalized `ℓ^2` length is nonnegative. -/
theorem blockAvsumL2_nonneg {ι : Type*} (Z : Finset ι) (g : ι → BlockVec d) :
    0 ≤ blockAvsumL2 Z g := Real.sqrt_nonneg _

/-- One summand `3^{sk}(avsum_z |(F)_{U_k(z)}|^2)^{1/2}` of the scale-average
seminorm, at the scale `k = t - j`. -/
@[expose]
def adaptedWeakScaleTerm (q : Mat d) (t : ℤ) (s : ℝ) (F : Vec d → BlockVec d) (j : ℕ) : ℝ :=
  (3 : ℝ) ^ (s * ((t : ℝ) - (j : ℝ))) *
    blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
      (fun z => blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) F)

/-- The defining equation of one scale summand. -/
theorem adaptedWeakScaleTerm_eq (q : Mat d) (t : ℤ) (s : ℝ) (F : Vec d → BlockVec d) (j : ℕ) :
    adaptedWeakScaleTerm q t s F j =
      (3 : ℝ) ^ (s * ((t : ℝ) - (j : ℝ))) *
        blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
          (fun z => blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) F) := rfl

/-- **The concrete scale-average seminorm `[F]_{B^{-s}_{2,1}(U_t)}`** on the
adapted cube `U_t = q□_t` with its aligned subdivision.  The printed sum runs
over all scales `k ≤ t`, reindexed here by `k = t - j`, `j ∈ ℕ`; it is carried
in
`ℝ≥0∞`, where the sum of a family of nonnegative terms is always defined, so
that the estimate is asserted also when its right side is infinite. -/
@[expose]
def adaptedWeakSeminorm (q : Mat d) (t : ℤ) (s : ℝ) (F : Vec d → BlockVec d) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal (adaptedWeakScaleTerm q t s F j)

/-- **The defining equation of the seminorm**: the sum over all scales `k ≤ t`
of the printed summands. -/
theorem adaptedWeakSeminorm_eq (q : Mat d) (t : ℤ) (s : ℝ) (F : Vec d → BlockVec d) :
    adaptedWeakSeminorm q t s F =
      ∑' j : ℕ, ENNReal.ofReal (adaptedWeakScaleTerm q t s F j) := rfl

end

end Response
end HighContrast
end HCPolySupport
