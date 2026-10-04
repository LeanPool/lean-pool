/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.Localise.Datum


/-!
# Localising coefficients of finite order on an open set

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 1 (p. 327) assumes
`a^{ij} ∈ C¹(U)` and `b^i, c ∈ L^∞(U)`, and Theorem 2 (p. 332) assumes
`a^{ij}, b^i, c ∈ C^{m+1}(U)`. Neither asks a bound on `a^{ij}` over `U`, and neither asks anything
of a coefficient off `U`. `Localise/LocalOp.lean` blends coefficients smooth on `U` into a
`FullEllipticOp`; this file does the same at finite order, and for lower-order coefficients that
are only essentially bounded and almost everywhere strongly measurable on `U`.

## Blend

For a test function `χ` of `U` valued in `[0, 1]`, the principal part is
`ã = λ I + χ (a − λ I)`, as in `localOp`. At order `m` the product `χ (a − λ I)` is `C^m` on the
whole space with compact support, so every derivative up to order `m` is bounded
(`exists_iteratedFDeriv_bound_of_le`), which is `IsCkCoeff` at order `m`. The lower-order
coefficients are supplied already cut off. For `L^∞(U)` coefficients the cutoff multiplies a
measurable modification (`AEStronglyMeasurable.mk`), which agrees with the coefficient almost
everywhere on `U`; for `C^m(U)` coefficients it multiplies the coefficient itself.

## Main declarations

* `PrincipalOn`: a principal part of class `C^m` on `U`, uniformly elliptic almost everywhere
  on `U`.
* `blendOp`: the blended global operator, with `blendOp_isCkCoeff` and `blendOp_a_eq`.
* `C1OpOn`, `exists_localOp_C1`: the coefficients of Theorem 1 and their localisation.
* `CkOpOn`, `exists_localOp_Ck`: the coefficients of Theorem 2 and their localisation.
* `LocalWeakSol.congr_ae`: the local weak formulation transported along coefficients equal
  almost everywhere.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- A function of class `C^n` on an open `U`, multiplied by a test function supported in `U`,
is of class `C^n` on the whole space. -/
theorem contDiff_mul_of_contDiffOn_of_le {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    {χ g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : IsTestFn U χ) {n : ℕ∞} (hg : ContDiffOn ℝ n g U) :
    ContDiff ℝ n (fun x => χ x * g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact ((hχ.1.of_le (by exact_mod_cast le_top)).contDiffAt).mul
      (hg.contDiffAt (hU.mem_nhds (hχ.2.2 hx)))
  · have h0 : χ =ᶠ[𝓝 x] 0 := (notMem_tsupport_iff_eventuallyEq).1 hx
    have h1 : (fun y => χ y * g y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [h0] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h1

/-- A compactly supported function of class `C^m` has every iterated derivative of order at
most `m` bounded, with a nonnegative bound at each order. -/
theorem exists_iteratedFDeriv_bound_of_le {g : EuclideanSpace ℝ (Fin d) → ℝ} {m : ℕ}
    (hg : ContDiff ℝ m g)
    (hc : HasCompactSupport g) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧ ∀ j, j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ B j := by
  have h : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ C) := by
    intro j
    by_cases hj : j ≤ m
    · obtain ⟨C, hC⟩ := (hc.iteratedFDeriv j).exists_bound_of_continuous
        (hg.continuous_iteratedFDeriv (by exact_mod_cast hj))
      exact ⟨max C 0, le_max_right _ _, fun _ x => (hC x).trans (le_max_left _ _)⟩
    · exact ⟨0, le_rfl, fun h => absurd h hj⟩
  choose B hB0 hB using h
  exact ⟨B, hB0, fun j hj => hB j hj⟩

/-- A compactly supported function of class `C^m` lies in `W^{m,∞}`. -/
theorem nonempty_isWkInfty_of_le {g : EuclideanSpace ℝ (Fin d) → ℝ} {m : ℕ} (hg : ContDiff ℝ m g)
    (hc : HasCompactSupport g) : Nonempty (IsWkInfty g m) := by
  obtain ⟨B, hB0, hB⟩ := exists_iteratedFDeriv_bound_of_le hg hc
  exact ⟨IsWkInfty.ofContDiff hg hB0 hB⟩

/-- A continuous compactly supported function has a nonnegative uniform bound. -/
theorem exists_sup_bound_continuous {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Continuous g)
    (hc : HasCompactSupport g) :
    ∃ C, 0 ≤ C ∧ ∀ x, |g x| ≤ C := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hg
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

/-! ### Principal part of finite order -/

/-- **Principal part of class `C^m` on an open set.** Entries of class `C^m` on `U`, uniformly
elliptic almost everywhere on `U` with constant `lam > 0`, with no bound, no symmetry and nothing
asked off `U`. -/
structure PrincipalOn (d : ℕ) (U : Set (EuclideanSpace ℝ (Fin d))) (m : ℕ) where
  /-- The principal-part coefficient matrix. -/
  a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ
  /-- The ellipticity constant. -/
  lam : ℝ
  /-- The ellipticity constant is strictly positive. -/
  lam_pos : 0 < lam
  /-- Every entry is of class `C^m` on `U`. -/
  contDiffOn : ∀ i j, ContDiffOn ℝ m (fun x => a x i j) U
  /-- Uniform ellipticity almost everywhere on `U`. -/
  elliptic : ∀ᵐ x ∂(volume.restrict U), ∀ ξ : Fin d → ℝ,
    lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j

namespace PrincipalOn

variable {U : Set (EuclideanSpace ℝ (Fin d))} {m : ℕ} (P : PrincipalOn d U m)

/-- The principal part shifted down to `λ I`, cut off by `χ`. -/
def gA (χ : EuclideanSpace ℝ (Fin d) → ℝ) (i j : Fin d) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  χ x * (P.a x i j - P.lam * SmoothOpOn.δ i j)

/-- The blended principal part `λ I + χ (a − λ I)`. -/
def aT (χ : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) (i j : Fin d) : ℝ :=
  P.lam * SmoothOpOn.δ i j + P.gA χ i j x

theorem gA_contDiff (hU : IsOpen U) {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn U χ)
    (i j : Fin d) :
    ContDiff ℝ m (P.gA χ i j) :=
  contDiff_mul_of_contDiffOn_of_le hU hχ (n := (m : ℕ∞))
    ((P.contDiffOn i j).sub contDiffOn_const)

theorem gA_hasCompactSupport {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn U χ) (i j : Fin d) :
    HasCompactSupport (P.gA χ i j) :=
  hasCompactSupport_mul hχ

theorem gA_continuous (hU : IsOpen U) {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn U χ)
    (i j : Fin d) :
    Continuous (P.gA χ i j) :=
  (P.gA_contDiff hU hχ i j).continuous

/-- The quadratic form of the blend, as a convex combination of `λ |ξ|²` and the quadratic form
of `a`. -/
theorem quad_aT (χ : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) (ξ : Fin d → ℝ) :
    ∑ i, ∑ j, P.aT χ x i j * ξ i * ξ j
      = P.lam * ∑ i, ξ i ^ 2
        + χ x * (∑ i, ∑ j, P.a x i j * ξ i * ξ j - P.lam * ∑ i, ξ i ^ 2) := by
  simp only [aT, gA, SmoothOpOn.δ, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring_nf

/-- Uniform ellipticity of the blend on the whole space at the constant `λ`. -/
theorem aT_elliptic {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn U χ)
    (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hUm : MeasurableSet U) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), ∀ ξ : Fin d → ℝ,
      P.lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, P.aT χ x i j * ξ i * ξ j := by
  have h := (ae_restrict_iff' hUm).1 P.elliptic
  filter_upwards [h] with x hx ξ
  rw [P.quad_aT]
  by_cases hxU : x ∈ U
  · have := hx hxU ξ
    have h0 := (hχ01 x).1
    nlinarith
  · have : χ x = 0 := by
      by_contra hne
      exact hxU (hχ.2.2 (subset_tsupport _ hne))
    simp [this]

end PrincipalOn

/-- **Blended operator at finite order.** Principal part `λ I + χ (a − λ I)`, and
lower-order coefficients `b`, `c` supplied measurable and essentially bounded on the whole
space. -/
def blendOp {U : Set (EuclideanSpace ℝ (Fin d))} {m : ℕ} (P : PrincipalOn d U m) (hU : IsOpen U)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn U χ) (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d) → ℝ) {Bs Cs : ℝ}
    (hBs : 0 ≤ Bs) (hCs : 0 ≤ Cs)
    (hbm : ∀ i, Measurable fun x => b x i) (hcm : Measurable c)
    (hbb : ∀ i, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |b x i| ≤ Bs)
    (hcb : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |c x| ≤ Cs) : FullEllipticOp d where
  a := P.aT χ
  lam := P.lam
  Λ := P.lam + ∑ i, ∑ j,
    Classical.choose (exists_sup_bound_continuous (P.gA_continuous hU hχ i j)
      (P.gA_hasCompactSupport hχ i j))
  lam_pos := P.lam_pos
  Λ_nonneg := by
    have := P.lam_pos
    have : 0 ≤ ∑ i, ∑ j, Classical.choose (exists_sup_bound_continuous
        (P.gA_continuous hU hχ i j) (P.gA_hasCompactSupport hχ i j)) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        (Classical.choose_spec (exists_sup_bound_continuous (P.gA_continuous hU hχ i j)
          (P.gA_hasCompactSupport hχ i j))).1
    linarith
  measurable i j := (continuous_const.add (P.gA_continuous hU hχ i j)).measurable
  bdd i j := Filter.Eventually.of_forall fun x => by
    set C := fun i j => Classical.choose (exists_sup_bound_continuous
      (P.gA_continuous hU hχ i j) (P.gA_hasCompactSupport hχ i j)) with hCdef
    have hC : ∀ i j, 0 ≤ C i j ∧ ∀ x, |P.gA χ i j x| ≤ C i j := fun i j =>
      Classical.choose_spec (exists_sup_bound_continuous (P.gA_continuous hU hχ i j)
        (P.gA_hasCompactSupport hχ i j))
    have h1 : C i j ≤ ∑ j', C i j' :=
      Finset.single_le_sum (f := fun j' => C i j') (fun j' _ => (hC i j').1) (Finset.mem_univ j)
    have h2 : ∑ j', C i j' ≤ ∑ i', ∑ j', C i' j' :=
      Finset.single_le_sum (f := fun i' => ∑ j', C i' j')
        (fun i' _ => Finset.sum_nonneg fun j' _ => (hC i' j').1) (Finset.mem_univ i)
    have hδ : |P.lam * SmoothOpOn.δ i j| ≤ P.lam := by
      unfold SmoothOpOn.δ; split_ifs <;> simp [abs_of_pos P.lam_pos, P.lam_pos.le]
    calc |P.aT χ x i j| ≤ |P.lam * SmoothOpOn.δ i j| + |P.gA χ i j x| := abs_add_le _ _
      _ ≤ P.lam + C i j := add_le_add hδ ((hC i j).2 x)
      _ ≤ _ := by linarith
  elliptic := P.aT_elliptic hχ hχ01 hU.measurableSet
  b := b
  c := c
  Bsup := Bs
  Csup := Cs
  Bsup_nonneg := hBs
  Csup_nonneg := hCs
  b_meas := hbm
  c_meas := hcm
  b_bdd := hbb
  c_bdd := hcb

section Blend

variable {U : Set (EuclideanSpace ℝ (Fin d))} {m : ℕ} (P : PrincipalOn d U m) (hU : IsOpen U)
  {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn U χ) (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
  (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d) → ℝ) {Bs Cs : ℝ}
  (hBs : 0 ≤ Bs) (hCs : 0 ≤ Cs) (hbm : ∀ i, Measurable fun x => b x i) (hcm : Measurable c)
  (hbb : ∀ i, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |b x i| ≤ Bs)
  (hcb : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |c x| ≤ Cs)

/-- **`C^m` bundle of the blend.** Each entry is a constant plus a compactly supported function
of class `C^m`, so its derivatives of order `1` to `m` are bounded. -/
theorem blendOp_isCkCoeff :
    Nonempty (IsCkCoeff (blendOp P hU hχ hχ01 b c hBs hCs hbm hcm hbb hcb).toEllipticCoeff m) := by
  have h : ∀ ij : Fin d × Fin d, ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧ ∀ j, 1 ≤ j → j ≤ m → ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => P.lam * SmoothOpOn.δ ij.1 ij.2 + P.gA χ ij.1 ij.2 y) x‖
        ≤ B j := by
    intro ij
    obtain ⟨B, hB0, hB⟩ :=
      exists_iteratedFDeriv_bound_of_le (P.gA_contDiff hU hχ ij.1 ij.2)
        (P.gA_hasCompactSupport hχ ij.1 ij.2)
    refine ⟨B, hB0, fun j hj1 hjm x => ?_⟩
    have hadd : iteratedFDeriv ℝ j (fun y => P.lam * SmoothOpOn.δ ij.1 ij.2 + P.gA χ ij.1 ij.2 y) x
        = iteratedFDeriv ℝ j (fun _ : EuclideanSpace ℝ (Fin d) => P.lam * SmoothOpOn.δ ij.1 ij.2) x
          + iteratedFDeriv ℝ j (P.gA χ ij.1 ij.2) x :=
      iteratedFDeriv_add_apply contDiffAt_const
        (((P.gA_contDiff hU hχ ij.1 ij.2).of_le (by exact_mod_cast hjm)).contDiffAt)
    rw [hadd, iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, zero_add]
    exact hB j hjm x
  choose B hB0 hB using h
  refine ⟨{ contDiff := fun i j => contDiff_const.add (P.gA_contDiff hU hχ i j)
            bound := fun j => ∑ ij, B ij j
            bound_nonneg := fun j => Finset.sum_nonneg fun ij _ => hB0 ij j
            iteratedFDeriv_bdd := fun i j k hk hkm x =>
              (hB (i, j) k hk hkm x).trans
                (Finset.single_le_sum (f := fun ij => B ij k) (fun ij _ => hB0 ij k)
                  (Finset.mem_univ (i, j))) }⟩

/-- The blend is the given principal part wherever the cutoff is one. -/
theorem blendOp_a_eq {x : EuclideanSpace ℝ (Fin d)} (hx : χ x = 1) :
    (blendOp P hU hχ hχ01 b c hBs hCs hbm hcm hbb hcb).a x = P.a x := by
  funext i j
  change P.lam * SmoothOpOn.δ i j + χ x * (P.a x i j - P.lam * SmoothOpOn.δ i j) = _
  rw [hx]; ring

end Blend

/-- The cutoff of `exists_isTestFn_one_nhdsSet_of_isCompact` and the open interior of the set
where it is one, which contains the compact set and sits inside `U`. -/
theorem exists_cutoff_interior_one {U K : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (χ : EuclideanSpace ℝ (Fin d) → ℝ) (_ : IsTestFn U χ) (_ : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
      (W : Set (EuclideanSpace ℝ (Fin d))), IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ ∀ x ∈ W, χ x = 1 := by
  obtain ⟨χ, hχ, hone, hχ01⟩ := exists_isTestFn_one_nhdsSet_of_isCompact hK hU hKU
  refine ⟨χ, hχ, hχ01, interior {x | χ x = 1}, isOpen_interior,
    subset_interior_iff_mem_nhdsSet.2 hone, fun x hx => hχ.2.2 (subset_tsupport _ ?_),
    fun x hx => interior_subset (s := {x | χ x = 1}) hx⟩
  have : χ x = 1 := interior_subset (s := {x | χ x = 1}) hx
  simp [Function.mem_support, this]

/-! ### Coefficients of Theorem 1 -/

/-- **Coefficients of Evans §6.3.1 Theorem 1 on an open set.** `a^{ij} ∈ C¹(U)`, uniformly
elliptic almost everywhere on `U`, and `b^i, c ∈ L^∞(U)`: almost everywhere strongly measurable
and essentially bounded on `U`. Nothing is asked off `U`. -/
structure C1OpOn (d : ℕ) (U : Set (EuclideanSpace ℝ (Fin d))) extends PrincipalOn d U 1 where
  /-- The transport (first-order) coefficients. -/
  b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ
  /-- The zeroth-order coefficient. -/
  c : EuclideanSpace ℝ (Fin d) → ℝ
  /-- The essential bound on the transport coefficients over `U`. -/
  Bsup : ℝ
  /-- The essential bound on the zeroth-order coefficient over `U`. -/
  Csup : ℝ
  /-- Every transport component is almost everywhere strongly measurable on `U`. -/
  b_aesm : ∀ i, AEStronglyMeasurable (fun x => b x i) (volume.restrict U)
  /-- The zeroth-order coefficient is almost everywhere strongly measurable on `U`. -/
  c_aesm : AEStronglyMeasurable c (volume.restrict U)
  /-- Every transport component is essentially bounded on `U`. -/
  b_bdd : ∀ i, ∀ᵐ x ∂(volume.restrict U), |b x i| ≤ Bsup
  /-- The zeroth-order coefficient is essentially bounded on `U`. -/
  c_bdd : ∀ᵐ x ∂(volume.restrict U), |c x| ≤ Csup

/-- A cutoff of `U` times a measurable modification of a function essentially bounded on `U`
is measurable and essentially bounded on the whole space. -/
theorem cutoff_mk_bound {U : Set (EuclideanSpace ℝ (Fin d))} (hUm : MeasurableSet U)
    {χ g : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn U χ)
    (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1) (hg : AEStronglyMeasurable g (volume.restrict U)) {B : ℝ}
    (hB : ∀ᵐ x ∂(volume.restrict U), |g x| ≤ B) :
    Measurable (fun x => χ x * hg.mk g x) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |χ x * hg.mk g x| ≤ max B 0 := by
  refine ⟨hχ.1.continuous.measurable.mul hg.stronglyMeasurable_mk.measurable, ?_⟩
  have h1 : ∀ᵐ x ∂(volume.restrict U), |hg.mk g x| ≤ B := by
    filter_upwards [hB, hg.ae_eq_mk] with x h1 h2
    rwa [← h2]
  filter_upwards [(ae_restrict_iff' hUm).1 h1] with x hx
  by_cases hxU : x ∈ U
  · rw [abs_mul, abs_of_nonneg (hχ01 x).1]
    calc χ x * |hg.mk g x| ≤ 1 * B :=
          mul_le_mul (hχ01 x).2 (hx hxU) (abs_nonneg _) zero_le_one
      _ ≤ max B 0 := by rw [one_mul]; exact le_max_left _ _
  · have : χ x = 0 := by
      by_contra hne
      exact hxU (hχ.2.2 (subset_tsupport _ hne))
    simp [this]

/-- **Localisation of the coefficients of Theorem 1.** For every compact `K ⊆ U` there are a
global operator with `C¹` principal part of bounded derivative and an open `W` with
`K ⊆ W ⊆ U`, on which the principal part agrees with the given one everywhere and the
lower-order coefficients agree with the given ones almost everywhere. -/
theorem exists_localOp_C1 {U : Set (EuclideanSpace ℝ (Fin d))} (P : C1OpOn d U) (hU : IsOpen U)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (Op : FullEllipticOp d) (W : Set (EuclideanSpace ℝ (Fin d))), IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
      Nonempty (IsC1Coeff Op.toEllipticCoeff) ∧ (∀ x ∈ W, Op.a x = P.a x) ∧
      (∀ i, ∀ᵐ x ∂(volume.restrict W), Op.b x i = P.b x i) ∧
      (∀ᵐ x ∂(volume.restrict W), Op.c x = P.c x) := by
  obtain ⟨χ, hχ, hχ01, W, hWo, hKW, hWU, hW1⟩ := exists_cutoff_interior_one hU hK hKU
  have hUm := hU.measurableSet
  have hb := fun i => cutoff_mk_bound hUm hχ hχ01 (P.b_aesm i) (P.b_bdd i)
  have hc := cutoff_mk_bound hUm hχ hχ01 P.c_aesm P.c_bdd
  set Op := blendOp P.toPrincipalOn hU hχ hχ01 (fun x i => χ x * (P.b_aesm i).mk _ x)
    (fun x => χ x * P.c_aesm.mk _ x) (le_max_right P.Bsup 0) (le_max_right P.Csup 0)
    (fun i => (hb i).1) hc.1 (fun i => (hb i).2) hc.2 with hOp
  have hae : ∀ {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : AEStronglyMeasurable g (volume.restrict U)),
      ∀ᵐ x ∂(volume.restrict W), χ x * hg.mk g x = g x := by
    intro g hg
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hWU hg.ae_eq_mk,
      ae_restrict_mem hWo.measurableSet] with x h1 h2
    rw [hW1 x h2, one_mul, h1]
  refine ⟨Op, W, hWo, hKW, hWU, ?_, fun x hx => blendOp_a_eq _ _ _ _ _ _ _ _ _ _ _ _ (hW1 x hx),
    fun i => hae (P.b_aesm i), hae P.c_aesm⟩
  exact ⟨(Classical.choice
    (blendOp_isCkCoeff P.toPrincipalOn hU hχ hχ01 _ _ _ _ _ _ _ _)).toIsC1Coeff le_rfl⟩

/-! ### Coefficients of Theorem 2 -/

/-- **Coefficients of Evans §6.3.1 Theorem 2 on an open set at order `m`.** `a^{ij}, b^i, c`
of class `C^m` on `U`, with `a^{ij}` uniformly elliptic almost everywhere on `U`. Evans's
hypothesis at order `m` is this structure at `m + 1`. Nothing is asked off `U`. -/
structure CkOpOn (d : ℕ) (U : Set (EuclideanSpace ℝ (Fin d))) (m : ℕ)
    extends PrincipalOn d U m where
  /-- The transport (first-order) coefficients. -/
  b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ
  /-- The zeroth-order coefficient. -/
  c : EuclideanSpace ℝ (Fin d) → ℝ
  /-- Every transport component is of class `C^m` on `U`. -/
  b_contDiffOn : ∀ i, ContDiffOn ℝ m (fun x => b x i) U
  /-- The zeroth-order coefficient is of class `C^m` on `U`. -/
  c_contDiffOn : ContDiffOn ℝ m c U

/-- **Localisation of the coefficients of Theorem 2.** For every compact `K ⊆ U` there are a
global operator with every coefficient of class `C^m` with bounded derivatives, packaged as
`IsCkCoeff` and `IsWkInftyLower` at order `m`, and an open `W` with `K ⊆ W ⊆ U` on which it agrees
with the given coefficients. -/
theorem exists_localOp_Ck {U : Set (EuclideanSpace ℝ (Fin d))} {m : ℕ} (P : CkOpOn d U m)
    (hU : IsOpen U) {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (Op : FullEllipticOp d) (W : Set (EuclideanSpace ℝ (Fin d))), IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
      Nonempty (IsCkCoeff Op.toEllipticCoeff m) ∧ Nonempty (IsWkInftyLower Op m) ∧
      (∀ x ∈ W, Op.a x = P.a x) ∧
      (∀ i, ∀ᵐ x ∂(volume.restrict W), Op.b x i = P.b x i) ∧
      (∀ᵐ x ∂(volume.restrict W), Op.c x = P.c x) := by
  obtain ⟨χ, hχ, hχ01, W, hWo, hKW, hWU, hW1⟩ := exists_cutoff_interior_one hU hK hKU
  have hbs : ∀ i, ContDiff ℝ m (fun x => χ x * P.b x i) := fun i =>
    contDiff_mul_of_contDiffOn_of_le hU hχ (n := (m : ℕ∞)) (P.b_contDiffOn i)
  have hcs : ContDiff ℝ m (fun x => χ x * P.c x) :=
    contDiff_mul_of_contDiffOn_of_le hU hχ (n := (m : ℕ∞)) P.c_contDiffOn
  have hbB := fun i => exists_sup_bound_continuous (hbs i).continuous
    (hasCompactSupport_mul (g := fun x => P.b x i) hχ)
  have hcB := exists_sup_bound_continuous hcs.continuous (hasCompactSupport_mul (g := P.c) hχ)
  choose Bi hBi0 hBi using hbB
  obtain ⟨Cc, hCc0, hCc⟩ := hcB
  set Op := blendOp P.toPrincipalOn hU hχ hχ01 (fun x i => χ x * P.b x i)
    (fun x => χ x * P.c x) (Finset.sum_nonneg fun i _ => hBi0 i) hCc0
    (fun i => (hbs i).continuous.measurable) hcs.continuous.measurable
    (fun i => Filter.Eventually.of_forall fun x => (hBi i x).trans
      (Finset.single_le_sum (fun i _ => hBi0 i) (Finset.mem_univ i)))
    (Filter.Eventually.of_forall hCc) with hOp
  have hb : ∀ i, IsWkInfty (fun x => Op.b x i) m := fun i =>
    Classical.choice (nonempty_isWkInfty_of_le (hbs i)
      (hasCompactSupport_mul (g := fun x => P.b x i) hχ))
  have hc : IsWkInfty Op.c m :=
    Classical.choice (nonempty_isWkInfty_of_le hcs (hasCompactSupport_mul (g := P.c) hχ))
  have hae : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ,
      ∀ᵐ x ∂(volume.restrict W), χ x * g x = g x := fun g => by
    filter_upwards [ae_restrict_mem hWo.measurableSet] with x hx
    rw [hW1 x hx, one_mul]
  refine ⟨Op, W, hWo, hKW, hWU, blendOp_isCkCoeff P.toPrincipalOn hU hχ hχ01 _ _ _ _ _ _ _ _,
    ⟨{ bReg := hb, cReg := hc
       bound := fun j => ∑ i, (hb i).bound j + hc.bound j
       bound_nonneg := fun j => add_nonneg
         (Finset.sum_nonneg fun i _ => (hb i).bound_nonneg j) (hc.bound_nonneg j)
       b_le := fun i j => le_add_of_le_of_nonneg
         (Finset.single_le_sum (f := fun i => (hb i).bound j)
           (fun i _ => (hb i).bound_nonneg j) (Finset.mem_univ i)) (hc.bound_nonneg j)
       c_le := fun j => le_add_of_nonneg_left
         (Finset.sum_nonneg fun i _ => (hb i).bound_nonneg j) }⟩,
    fun x hx => blendOp_a_eq _ _ _ _ _ _ _ _ _ _ _ _ (hW1 x hx),
    fun i => hae (fun x => P.b x i), hae P.c⟩

/-! ### Transport of the weak formulation along almost everywhere equal coefficients -/

/-- Coefficients equal on `W` almost everywhere, with a principal part equal everywhere on `W`,
give the same local weak formulation on `W`. -/
theorem LocalWeakSol.congr_ae {W : Set (EuclideanSpace ℝ (Fin d))}
    {a a' : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ}
    {b b' : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c c' f f' u : EuclideanSpace ℝ (Fin d) → ℝ} {G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (ha : ∀ i j, ∀ᵐ x ∂(volume.restrict W), a x i j = a' x i j)
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict W), b x i = b' x i)
    (hc : ∀ᵐ x ∂(volume.restrict W), c x = c' x) (hf : ∀ᵐ x ∂(volume.restrict W), f x = f' x)
    (h : LocalWeakSol W a b c f u G) : LocalWeakSol W a' b' c' f' u G := by
  intro φ hφ hφc hφW
  have e := h φ hφ hφc hφW
  have e1 : ∀ i j, ∫ x in W, a x i j * G i x * partialD j φ x
      = ∫ x in W, a' x i j * G i x * partialD j φ x := fun i j =>
    integral_congr_ae (by filter_upwards [ha i j] with x hx; rw [hx])
  have e2 : ∀ i, ∫ x in W, b x i * G i x * φ x = ∫ x in W, b' x i * G i x * φ x := fun i =>
    integral_congr_ae (by filter_upwards [hb i] with x hx; rw [hx])
  have e3 : ∫ x in W, c x * u x * φ x = ∫ x in W, c' x * u x * φ x :=
    integral_congr_ae (by filter_upwards [hc] with x hx; rw [hx])
  have e4 : ∫ x in W, f x * φ x = ∫ x in W, f' x * φ x :=
    integral_congr_ae (by filter_upwards [hf] with x hx; rw [hx])
  simp only [e1, e2, e3, e4] at e
  exact e

end EllipticPdes.Regularity
