/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.MeasureSpaces.Scheme
public import LeanPool.FunctionSpaces.ApproximationSpaces.Error
public import LeanPool.FunctionSpaces.Torus.HaarMeasure
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Data.Int.Interval
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Topology.ContinuousMap.Compact

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Trigonometric polynomials on the torus

On the torus `𝕋^d = UnitAddTorus d` the **trigonometric monomial** of frequency `k ∈ ℤ^d` is
`e_k(x) = exp(2πi ⟨k, x⟩)` (Mathlib's `UnitAddTorus.mFourier k`), here as a bounded continuous
function `Torus.trigMonomial k`.  The **degree** of a frequency is `deg k = max_i |k_i|`, and

`trigPoly n = span_ℂ {e_k : deg k < n}`

is the space of trigonometric polynomials of degree `< n` (`Torus.trigPoly`).  It contains the
constants for `n ≥ 1` and is `{0}` for `n = 0`; this strict-degree convention makes the
spaces an approximation scheme, `Torus.trigScheme d`.  A linear map that sends the monomials of
degree `< n` into `trigPoly n` maps `trigPoly n` into `trigPoly n` (`Torus.map_mem_trigPoly`).

The frequencies of degree `< n` form the box `boxLt n ⊆ ℤ^d` with at most `(2n)^d` elements
(`card_boxLt_le`).  Since `e_k e_l = e_{k+l}` and `deg (k + l) ≤ deg k + deg l`, products of
trigonometric polynomials are trigonometric polynomials, `trigPoly m · trigPoly n ⊆
trigPoly (m + n)`, and `T ∈ trigPoly n` has `T^m ∈ trigPoly (m n)`
(`pow_mem_trigPoly`).  This is what the proof of the Nikolskii inequality uses.

The trigonometric polynomials are dense in the bounded continuous functions for the sup norm
(`Torus.dense_iUnion_trigPoly`, from Mathlib's `span_mFourier_closure_eq_top`), so the errors of
best uniform approximation tend to `0` (`Torus.tendsto_approxError_trigScheme`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus
open scoped ENNReal BoundedContinuousFunction TorusHaar Pointwise

namespace Torus

variable {d : Type*} [Fintype d]

/-- The **degree** `max_i |k_i|` of a frequency `k ∈ ℤ^d`. -/
def deg (k : d → ℤ) : ℕ := Finset.univ.sup fun i => (k i).natAbs

/-- `|k_i| ≤ deg k`. -/
theorem natAbs_le_deg (k : d → ℤ) (i : d) : (k i).natAbs ≤ deg k :=
  Finset.le_sup (f := fun i => (k i).natAbs) (Finset.mem_univ i)

/-- `deg k ≤ n` iff `|k_i| ≤ n` for every `i`. -/
theorem deg_le_iff {k : d → ℤ} {n : ℕ} : deg k ≤ n ↔ ∀ i, (k i).natAbs ≤ n := by
  simp [deg, Finset.sup_le_iff]

/-- `deg (k + l) ≤ deg k + deg l`. -/
theorem deg_add_le (k l : d → ℤ) : deg (k + l) ≤ deg k + deg l :=
  deg_le_iff.2 fun i => (Int.natAbs_add_le _ _).trans
    (add_le_add (natAbs_le_deg k i) (natAbs_le_deg l i))

/-- `deg 0 = 0`. -/
@[simp]
theorem deg_zero : deg (0 : d → ℤ) = 0 := by simp [deg]

variable (d) in
open Classical in
/-- The **frequencies of degree `< n`**. -/
noncomputable def boxLt (n : ℕ) : Finset (d → ℤ) :=
  (Fintype.piFinset fun _ => Finset.Ioo (-(n : ℤ)) n).filter fun k => deg k < n

/-- `k` lies in the box of size `n` iff `deg k < n`. -/
theorem mem_boxLt {n : ℕ} {k : d → ℤ} : k ∈ boxLt d n ↔ deg k < n := by
  simp only [boxLt, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Ioo]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  have := (natAbs_le_deg k i).trans_lt h
  omega

/-- The box of size `0` is empty. -/
@[simp]
theorem boxLt_zero : boxLt d 0 = ∅ := by
  ext k; simp [mem_boxLt]

/-- The boxes increase with `n`. -/
theorem boxLt_mono : Monotone (boxLt d) := fun _ _ h _ hk =>
  mem_boxLt.2 ((mem_boxLt.1 hk).trans_le h)

/-- There are at most `(2n)^d` frequencies of degree `< n`. -/
theorem card_boxLt_le (n : ℕ) : (boxLt d n).card ≤ (2 * n) ^ Fintype.card d := by
  classical
  calc (boxLt d n).card ≤ (Fintype.piFinset fun _ : d => Finset.Ioo (-(n : ℤ)) n).card :=
        Finset.card_filter_le _ _
    _ = ∏ _i : d, (Finset.Ioo (-(n : ℤ)) n).card := Fintype.card_piFinset _
    _ = (Finset.Ioo (-(n : ℤ)) n).card ^ Fintype.card d := by
        rw [Finset.prod_const, Finset.card_univ]
    _ ≤ (2 * n) ^ Fintype.card d := by
        gcongr
        rw [Int.card_Ioo]
        omega

/-- The **trigonometric monomial** `e_k(x) = exp(2πi ⟨k, x⟩)`, as a bounded continuous
function on the torus. -/
noncomputable def trigMonomial (k : d → ℤ) : UnitAddTorus d →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact (mFourier k)

/-- The monomial `e_k` as a bounded continuous function is Mathlib's `mFourier k`. -/
@[simp]
theorem trigMonomial_apply (k : d → ℤ) (x : UnitAddTorus d) : trigMonomial k x = mFourier k x :=
  rfl

/-- `e_{k+l} = e_k e_l`. -/
theorem trigMonomial_add (k l : d → ℤ) :
    trigMonomial (k + l) = trigMonomial k * trigMonomial l := by
  ext x; simp [mFourier_add]

/-- `e_0 = 1`. -/
@[simp]
theorem trigMonomial_zero : trigMonomial (0 : d → ℤ) = 1 := by
  ext x; simp [mFourier_zero]

/-- A trigonometric monomial has modulus `1` everywhere. -/
theorem norm_trigMonomial_apply (k : d → ℤ) (x : UnitAddTorus d) : ‖trigMonomial k x‖ = 1 := by
  simp [mFourier, norm_prod, fourier_apply, Circle.norm_coe]

variable (d) in
/-- The **trigonometric polynomials of degree `< n`**, `span_ℂ {e_k : deg k < n}`. -/
noncomputable def trigPoly (n : ℕ) : Submodule ℂ (UnitAddTorus d →ᵇ ℂ) :=
  Submodule.span ℂ (trigMonomial '' (boxLt d n : Set (d → ℤ)))

/-- There are no nonzero trigonometric polynomials of degree `< 0`. -/
@[simp]
theorem trigPoly_zero : trigPoly d 0 = ⊥ := by simp [trigPoly]

/-- The spaces of trigonometric polynomials increase with the degree. -/
theorem trigPoly_mono : Monotone (trigPoly d) := fun _ _ h =>
  Submodule.span_mono (Set.image_mono (by exact_mod_cast boxLt_mono h))

/-- `e_k` has degree `< n` when `deg k < n`. -/
theorem trigMonomial_mem_trigPoly {n : ℕ} {k : d → ℤ} (hk : deg k < n) :
    trigMonomial k ∈ trigPoly d n :=
  Submodule.subset_span ⟨k, by simpa using mem_boxLt.2 hk, rfl⟩

/-- **Linear maps of trigonometric polynomials**: a linear map that sends every monomial `e_k` of
degree `< m` to a trigonometric polynomial of degree `< m` maps every trigonometric polynomial of
degree `< m` to one of degree `< m`, since these polynomials are the span of the monomials
(Mathlib's `Submodule.span_le`). -/
theorem map_mem_trigPoly {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : (UnitAddTorus ι →ᵇ ℂ) →ₗ[ℂ] (UnitAddTorus κ →ᵇ ℂ)) {m : ℕ}
    (hL : ∀ k : ι → ℤ, deg k < m → L (trigMonomial k) ∈ trigPoly κ m)
    {a : UnitAddTorus ι →ᵇ ℂ} (ha : a ∈ trigPoly ι m) : L a ∈ trigPoly κ m :=
  (Submodule.span_le (p := (trigPoly κ m).comap L)).2
    (by rintro _ ⟨k, hk, rfl⟩; exact hL k (mem_boxLt.1 hk)) ha

/-- **Products of trigonometric polynomials**: degrees `< m` and `< n` give degree `< m + n`. -/
theorem trigPoly_mul_le (m n : ℕ) : trigPoly d m * trigPoly d n ≤ trigPoly d (m + n) := by
  rw [trigPoly, trigPoly, Submodule.span_mul_span]
  apply Submodule.span_mono
  rintro _ ⟨_, ⟨k, hk, rfl⟩, _, ⟨l, hl, rfl⟩, rfl⟩
  refine ⟨k + l, ?_, trigMonomial_add k l⟩
  have hk' := mem_boxLt.1 (by simpa using hk)
  have hl' := mem_boxLt.1 (by simpa using hl)
  simpa using mem_boxLt.2 ((deg_add_le k l).trans_lt (by omega))

/-- The product of polynomials of degree `< m` and `< n` has degree `< m + n`. -/
theorem mul_mem_trigPoly {m n : ℕ} {S T : UnitAddTorus d →ᵇ ℂ} (hS : S ∈ trigPoly d m)
    (hT : T ∈ trigPoly d n) : S * T ∈ trigPoly d (m + n) :=
  trigPoly_mul_le m n (Submodule.mul_mem_mul hS hT)

/-- **Powers of trigonometric polynomials**: `T` of degree `< n` gives `T^(m+1)` of degree
`< (m+1) n`. -/
theorem pow_mem_trigPoly {n : ℕ} {T : UnitAddTorus d →ᵇ ℂ} (hT : T ∈ trigPoly d n) (m : ℕ) :
    T ^ (m + 1) ∈ trigPoly d ((m + 1) * n) := by
  induction m with
  | zero => simpa using hT
  | succ m ih =>
    rw [pow_succ, show (m + 1 + 1) * n = (m + 1) * n + n by ring]
    exact mul_mem_trigPoly ih hT

variable (d) in
/-- The **scheme of trigonometric polynomials** on `𝕋^d`: `A n` is the space of trigonometric
polynomials of degree `< n`. -/
noncomputable def trigScheme : FunctionScheme (UnitAddTorus d) :=
  ApproximationScheme.ofSubmodules (fun n => (trigPoly d n).restrictScalars ℝ)
    (by simp) (fun _ _ h => trigPoly_mono h)

/-- The approximants of the trigonometric scheme are the trigonometric polynomials. -/
@[simp]
theorem mem_trigScheme {n : ℕ} {T : UnitAddTorus d →ᵇ ℂ} :
    T ∈ trigScheme d n ↔ T ∈ trigPoly d n := Iff.rfl

section UniformDensity

open Filter Topology

/-! ### Uniform density of the trigonometric polynomials -/

/-- Every element of the span of the characters `e_k` in `C(𝕋^d)`, viewed as a bounded continuous
function, is a trigonometric polynomial of some degree: the image of the span lies in the
supremum `⨆ n, 𝒯_n` of the spaces of trigonometric polynomials. -/
theorem map_span_mFourier_le_iSup_trigPoly :
    (Submodule.span ℂ (Set.range (mFourier (d := d)))).map
        (ContinuousMap.linearIsometryBoundedOfCompact (UnitAddTorus d) ℂ ℂ).toLinearMap ≤
      ⨆ n, trigPoly d n := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  exact Submodule.mem_iSup_of_mem (deg k + 1) (trigMonomial_mem_trigPoly (Nat.lt_succ_self _))

/-- **The trigonometric polynomials are uniformly dense** in the bounded continuous functions on
`𝕋^d`: the image of Mathlib's dense span of the characters (`span_mFourier_closure_eq_top`) under
the isometry `C(𝕋^d) ≅ (𝕋^d →ᵇ ℂ)`. -/
theorem dense_iUnion_trigPoly : Dense (⋃ n, (trigPoly d n : Set (UnitAddTorus d →ᵇ ℂ))) := by
  let L := ContinuousMap.linearIsometryBoundedOfCompact (UnitAddTorus d) ℂ ℂ
  have hS : Dense (Submodule.span ℂ (Set.range (mFourier (d := d))) :
      Set C(UnitAddTorus d, ℂ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2 span_mFourier_closure_eq_top
  rw [← Submodule.coe_iSup_of_directed _ trigPoly_mono.directed_le]
  exact (L.surjective.denseRange.dense_image L.continuous hS).mono
    map_span_mFourier_le_iSup_trigPoly

/-- The errors of best uniform approximation by trigonometric polynomials of degree `< n` tend
to `0`. -/
theorem tendsto_approxError_trigScheme (f : UnitAddTorus d →ᵇ ℂ) :
    Tendsto ((trigScheme d).approxError f) atTop (𝓝 0) :=
  (ApproximationScheme.tendsto_approxError_zero_iff f).2 (dense_iUnion_trigPoly f)

end UniformDensity

end Torus
