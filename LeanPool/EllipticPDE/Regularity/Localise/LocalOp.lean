/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.Localise.CutoffProduct


/-!
# Localising coefficients smooth on an open set into a global elliptic operator

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 3 states its conclusion for
coefficients and a datum smooth on the whole region `Ω`, with no bound assumed anywhere. The
interior-regularity chain in this development runs on a `FullEllipticOp`, whose coefficients are
global, essentially bounded and measurable, which is a different hypothesis shape. This file
bridges the two: `SmoothOpOn` states coefficients smooth and uniformly elliptic on an open set
`U` with no global bound, and `localOp` blends them against `λ I`, `0`, `0` outside a cutoff to
build a `FullEllipticOp` agreeing with the given coefficients wherever the cutoff is `1`.

## The blend

For a test function `χ` of `U`, valued in `[0, 1]`,

* `ã = λ I + χ (a − λ I) = χ a + (1 − χ) λ I`,
* `b̃ = χ b`,
* `c̃ = χ c`.

Wherever `χ = 1` the blend agrees with `P.a`, `P.b`, `P.c`; wherever `χ = 0` it reduces to the
constant-coefficient Laplacian at level `λ`, which is trivially uniformly elliptic, bounded and
of every regularity class. Ellipticity of the blend follows from ellipticity of `P.a` on `U` and
convexity of the quadratic form in `χ` between the two extremes, needing no symmetry.

## Main declarations

* `SmoothOpOn`: coefficients smooth and uniformly elliptic a.e. on an open set, unbounded.
* `localOp`: the blended global operator.
* `exists_localOp`: for every compact `K ⊆ U` there is a cutoff and an open `W ⊇ K` on which
  `localOp` agrees with the given coefficients and meets every regularity mixin
  `interior_smooth` asks for.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- **Coefficients of Evans §6.3.1, Theorem 3.** Smooth on the open set `U`, uniformly elliptic
almost everywhere on `U`, with no global bound, no measurability asked off `U` and no symmetry
asked anywhere. This is the hypothesis shape the theorem's classical statement supplies, before
it is localised into the global bounded-measurable shape `FullEllipticOp` asks for. -/
structure SmoothOpOn (d : ℕ) (U : Set (EuclideanSpace ℝ (Fin d))) where
  /-- The principal-part coefficient matrix. -/
  a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ
  /-- The transport (first-order) coefficients. -/
  b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ
  /-- The zeroth-order coefficient. -/
  c : EuclideanSpace ℝ (Fin d) → ℝ
  /-- The ellipticity constant. -/
  lam : ℝ
  /-- The ellipticity constant is strictly positive. -/
  lam_pos : 0 < lam
  /-- Every entry of the principal part is smooth on `U`. -/
  a_smooth : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => a x i j) U
  /-- Every transport component is smooth on `U`. -/
  b_smooth : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => b x i) U
  /-- The zeroth-order coefficient is smooth on `U`. -/
  c_smooth : ContDiffOn ℝ (⊤ : ℕ∞) c U
  /-- The principal part is uniformly elliptic almost everywhere on `U`. -/
  elliptic : ∀ᵐ x ∂(volume.restrict U), ∀ ξ : Fin d → ℝ,
    lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j

namespace SmoothOpOn

variable {U : Set (EuclideanSpace ℝ (Fin d))} (P : SmoothOpOn d U)

/-- Kronecker delta as a real number. -/
def δ (i j : Fin d) : ℝ := if i = j then 1 else 0

/-- The principal part shifted down to `λ I`, cut off by `χ`. -/
def gA (χ : EuclideanSpace ℝ (Fin d) → ℝ) (i j : Fin d) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  χ x * (P.a x i j - P.lam * δ i j)

/-- The blended principal part `ã = λ I + χ (a − λ I) = χ a + (1 − χ) λ I`. -/
def aT (χ : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) (i j : Fin d) : ℝ :=
  P.lam * δ i j + P.gA χ i j x

/-- The cut-off transport field. -/
def bT (χ : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) : ℝ :=
  χ x * P.b x i

/-- The cut-off zeroth-order coefficient. -/
def cT (χ : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ := χ x * P.c x

variable (hU : IsOpen U) {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn U χ)
include hU hχ

theorem gA_contDiff (i j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (P.gA χ i j) :=
  contDiff_mul_of_contDiffOn hU hχ ((P.a_smooth i j).sub contDiffOn_const)

omit hU in
theorem gA_hasCompactSupport (i j : Fin d) : HasCompactSupport (P.gA χ i j) :=
  hasCompactSupport_mul hχ

theorem aT_contDiff (i j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (fun x => P.aT χ x i j) :=
  contDiff_const.add (P.gA_contDiff hU hχ i j)

theorem bT_contDiff (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (fun x => P.bT χ x i) :=
  contDiff_mul_of_contDiffOn hU hχ (P.b_smooth i)

theorem cT_contDiff : ContDiff ℝ (⊤ : ℕ∞) (P.cT χ) :=
  contDiff_mul_of_contDiffOn hU hχ P.c_smooth

omit hU hχ in
/-- The quadratic form of the blend, as a convex combination of `λ |ξ|²` and the quadratic form
of `P.a`. -/
theorem quad_aT (x : EuclideanSpace ℝ (Fin d)) (ξ : Fin d → ℝ) :
    ∑ i, ∑ j, P.aT χ x i j * ξ i * ξ j
      = P.lam * ∑ i, ξ i ^ 2
        + χ x * (∑ i, ∑ j, P.a x i j * ξ i * ξ j - P.lam * ∑ i, ξ i ^ 2) := by
  simp only [aT, gA, δ, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring_nf

omit hU in
/-- **Uniform ellipticity of the blend on all of `ℝᵈ`, at the constant `λ`.** Where `χ = 0` the
blend is the constant-coefficient form `λ I`, trivially elliptic at `λ`; where `χ ∈ (0, 1]` and
`x ∈ U`, the quadratic form is a convex combination of `λ |ξ|²` and a quantity at least
`λ |ξ|²` by ellipticity of `P.a`, hence itself at least `λ |ξ|²`. No symmetry of `P.a` enters. -/
theorem aT_elliptic (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1) (hUm : MeasurableSet U) :
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

end SmoothOpOn

open SmoothOpOn

variable {U : Set (EuclideanSpace ℝ (Fin d))}

/-- A smooth compactly supported function has a uniform bound, chosen once and reused. -/
theorem exists_sup_bound {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) : ∃ C, 0 ≤ C ∧ ∀ x, |g x| ≤ C := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hg.continuous
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

/-- **The localised operator.** Global coefficients on `EuclideanSpace ℝ (Fin d)`, equal to
`λ I + χ (a − λ I)`, `χ b`, `χ c`, meeting every hypothesis `FullEllipticOp` asks: measurability
and boundedness come from smoothness plus compact support, and ellipticity from `aT_elliptic`. -/
def localOp (P : SmoothOpOn d U) (hU : IsOpen U) {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : IsTestFn U χ) (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1) : FullEllipticOp d where
  a := P.aT χ
  lam := P.lam
  Λ := P.lam + ∑ i, ∑ j,
    Classical.choose (exists_sup_bound (P.gA_contDiff hU hχ i j) (P.gA_hasCompactSupport hχ i j))
  lam_pos := P.lam_pos
  Λ_nonneg := by
    have := P.lam_pos
    have : 0 ≤ ∑ i, ∑ j, Classical.choose
        (exists_sup_bound (P.gA_contDiff hU hχ i j) (P.gA_hasCompactSupport hχ i j)) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        (Classical.choose_spec (exists_sup_bound (P.gA_contDiff hU hχ i j)
          (P.gA_hasCompactSupport hχ i j))).1
    linarith
  measurable i j := (P.aT_contDiff hU hχ i j).continuous.measurable
  bdd i j := Filter.Eventually.of_forall fun x => by
    set C := fun i j => Classical.choose
      (exists_sup_bound (P.gA_contDiff hU hχ i j) (P.gA_hasCompactSupport hχ i j)) with hCdef
    have hC : ∀ i j, 0 ≤ C i j ∧ ∀ x, |P.gA χ i j x| ≤ C i j := fun i j =>
      Classical.choose_spec
        (exists_sup_bound (P.gA_contDiff hU hχ i j) (P.gA_hasCompactSupport hχ i j))
    have h1 : C i j ≤ ∑ j', C i j' :=
      Finset.single_le_sum (f := fun j' => C i j') (fun j' _ => (hC i j').1) (Finset.mem_univ j)
    have h2 : ∑ j', C i j' ≤ ∑ i', ∑ j', C i' j' :=
      Finset.single_le_sum (f := fun i' => ∑ j', C i' j')
        (fun i' _ => Finset.sum_nonneg fun j' _ => (hC i' j').1) (Finset.mem_univ i)
    have hδ : |P.lam * δ i j| ≤ P.lam := by
      unfold δ; split_ifs <;> simp [abs_of_pos P.lam_pos, P.lam_pos.le]
    calc |P.aT χ x i j| ≤ |P.lam * δ i j| + |P.gA χ i j x| := abs_add_le _ _
      _ ≤ P.lam + C i j := add_le_add hδ ((hC i j).2 x)
      _ ≤ _ := by linarith
  elliptic := P.aT_elliptic hχ hχ01 hU.measurableSet
  b := P.bT χ
  c := P.cT χ
  Bsup := ∑ i, Classical.choose
    (exists_sup_bound (P.bT_contDiff hU hχ i) (hasCompactSupport_mul (g := fun x => P.b x i) hχ))
  Csup := Classical.choose (exists_sup_bound (P.cT_contDiff hU hχ) (hasCompactSupport_mul hχ))
  Bsup_nonneg := Finset.sum_nonneg fun i _ => (Classical.choose_spec
    (exists_sup_bound (P.bT_contDiff hU hχ i)
      (hasCompactSupport_mul (g := fun x => P.b x i) hχ))).1
  Csup_nonneg :=
    (Classical.choose_spec (exists_sup_bound (P.cT_contDiff hU hχ) (hasCompactSupport_mul hχ))).1
  b_meas i := (P.bT_contDiff hU hχ i).continuous.measurable
  c_meas := (P.cT_contDiff hU hχ).continuous.measurable
  b_bdd i := Filter.Eventually.of_forall fun x => by
    have hC : ∀ i, 0 ≤ Classical.choose (exists_sup_bound (P.bT_contDiff hU hχ i)
        (hasCompactSupport_mul (g := fun x => P.b x i) hχ)) ∧ ∀ x, |P.bT χ x i| ≤
        Classical.choose (exists_sup_bound (P.bT_contDiff hU hχ i)
          (hasCompactSupport_mul (g := fun x => P.b x i) hχ)) := fun i =>
      Classical.choose_spec (exists_sup_bound (P.bT_contDiff hU hχ i)
        (hasCompactSupport_mul (g := fun x => P.b x i) hχ))
    exact ((hC i).2 x).trans (Finset.single_le_sum (fun i' _ => (hC i').1) (Finset.mem_univ i))
  c_bdd := Filter.Eventually.of_forall fun x =>
    (Classical.choose_spec (exists_sup_bound (P.cT_contDiff hU hχ)
      (hasCompactSupport_mul hχ))).2 x

variable (P : SmoothOpOn d U) (hU : IsOpen U) {χ : EuclideanSpace ℝ (Fin d) → ℝ}
  (hχ : IsTestFn U χ) (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1)

/-- `Cᵏ` bundle for the localised principal part, at every order: each entry is a constant plus a
smooth compactly supported function, and `exists_iteratedFDeriv_bound_const_add` supplies the
bound. -/
theorem nonempty_isCkCoeff (k : ℕ) :
    Nonempty (IsCkCoeff (localOp P hU hχ hχ01).toEllipticCoeff k) := by
  have h : ∀ ij : Fin d × Fin d, ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧ ∀ m, 1 ≤ m → ∀ x,
      ‖iteratedFDeriv ℝ m (fun y => P.lam * δ ij.1 ij.2 + P.gA χ ij.1 ij.2 y) x‖ ≤ B m :=
    fun ij => exists_iteratedFDeriv_bound_const_add (P.gA_contDiff hU hχ ij.1 ij.2)
      (P.gA_hasCompactSupport hχ ij.1 ij.2) _
  choose B hB0 hB using h
  refine ⟨{ contDiff := fun i j => (P.aT_contDiff hU hχ i j).of_le (by exact_mod_cast le_top)
            bound := fun m => ∑ ij, B ij m
            bound_nonneg := fun m => Finset.sum_nonneg fun ij _ => hB0 ij m
            iteratedFDeriv_bdd := fun i j m hm _ x =>
              (hB (i, j) m hm x).trans
                (Finset.single_le_sum (f := fun ij => B ij m) (fun ij _ => hB0 ij m)
                  (Finset.mem_univ (i, j))) }⟩

/-- The localised principal part meets the `C¹` regularity `interior_smooth` asks for. -/
theorem nonempty_isC1Coeff : Nonempty (IsC1Coeff (localOp P hU hχ hχ01).toEllipticCoeff) :=
  ⟨(Classical.choice (nonempty_isCkCoeff P hU hχ hχ01 1)).toIsC1Coeff le_rfl⟩

/-- The localised principal part lies in `W^{k,∞}` at every order, through the `Cᵏ` bundle. -/
theorem nonempty_isWkInftyCoeff (k : ℕ) :
    Nonempty (IsWkInftyCoeff (localOp P hU hχ hχ01).toEllipticCoeff k) :=
  ⟨(Classical.choice (nonempty_isCkCoeff P hU hχ hχ01 k)).toIsWkInftyCoeff⟩

/-- The localised lower-order coefficients lie in `W^{k,∞}` at every order, uniformly. -/
theorem nonempty_isWkInftyLower (k : ℕ) :
    Nonempty (IsWkInftyLower (localOp P hU hχ hχ01) k) := by
  have hb : ∀ i, IsWkInfty (fun x => (localOp P hU hχ hχ01).b x i) k := fun i =>
    Classical.choice (nonempty_isWkInfty (P.bT_contDiff hU hχ i)
      (hasCompactSupport_mul (g := fun x => P.b x i) hχ) k)
  have hc : IsWkInfty (localOp P hU hχ hχ01).c k :=
    Classical.choice (nonempty_isWkInfty (P.cT_contDiff hU hχ) (hasCompactSupport_mul hχ) k)
  refine ⟨{ bReg := hb, cReg := hc
            bound := fun m => ∑ i, (hb i).bound m + hc.bound m
            bound_nonneg := fun m => add_nonneg
              (Finset.sum_nonneg fun i _ => (hb i).bound_nonneg m) (hc.bound_nonneg m)
            b_le := fun i m => le_add_of_le_of_nonneg
              (Finset.single_le_sum (f := fun i => (hb i).bound m)
                (fun i _ => (hb i).bound_nonneg m) (Finset.mem_univ i)) (hc.bound_nonneg m)
            c_le := fun m => le_add_of_nonneg_left
              (Finset.sum_nonneg fun i _ => (hb i).bound_nonneg m) }⟩

/-! ### Agreement on the region where the cutoff is one -/

theorem eqOn_a {W : Set (EuclideanSpace ℝ (Fin d))} (hW : ∀ x ∈ W, χ x = 1) :
    ∀ x ∈ W, (localOp P hU hχ hχ01).a x = P.a x := by
  intro x hx
  funext i j
  simp [localOp, aT, gA, hW x hx]

theorem eqOn_b {W : Set (EuclideanSpace ℝ (Fin d))} (hW : ∀ x ∈ W, χ x = 1) :
    ∀ x ∈ W, (localOp P hU hχ hχ01).b x = P.b x := by
  intro x hx
  funext i
  simp [localOp, bT, hW x hx]

theorem eqOn_c {W : Set (EuclideanSpace ℝ (Fin d))} (hW : ∀ x ∈ W, χ x = 1) :
    ∀ x ∈ W, (localOp P hU hχ hχ01).c x = P.c x := by
  intro x hx
  simp [localOp, cT, hW x hx]

/-- **Localisation of the coefficients.** For every compact `K ⊆ U` there are a cutoff `χ` and an
open `W ⊇ K`, with `closure W` compact inside `U`, on which the localised operator agrees with
the given coefficients, and the localised operator meets every regularity mixin `interior_smooth`
asks for. The cutoff comes from `exists_isTestFn_one_nhdsSet_of_isCompact` and `W` is the
interior of the region on which it is `1`. -/
theorem exists_localOp {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (χ : EuclideanSpace ℝ (Fin d) → ℝ) (hχ : IsTestFn U χ)
      (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1) (W : Set (EuclideanSpace ℝ (Fin d))),
      IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ (∀ x ∈ W, χ x = 1) ∧
      (localOp P hU hχ hχ01).lam = P.lam ∧
      (∀ x ∈ W, (localOp P hU hχ hχ01).a x = P.a x) ∧
      (∀ x ∈ W, (localOp P hU hχ hχ01).b x = P.b x) ∧
      (∀ x ∈ W, (localOp P hU hχ hχ01).c x = P.c x) ∧
      Nonempty (IsC1Coeff (localOp P hU hχ hχ01).toEllipticCoeff) ∧
      (∀ k, Nonempty (IsWkInftyCoeff (localOp P hU hχ hχ01).toEllipticCoeff k)) ∧
      (∀ k, Nonempty (IsWkInftyLower (localOp P hU hχ hχ01) k)) := by
  obtain ⟨χ, hχ, hone, hχ01⟩ := exists_isTestFn_one_nhdsSet_of_isCompact hK hU hKU
  obtain ⟨W, hWdef⟩ : ∃ W, W = interior {x | χ x = 1} := ⟨_, rfl⟩
  have hW1 : ∀ x ∈ W, χ x = 1 := fun x hx => by
    rw [hWdef] at hx
    exact interior_subset (s := {x | χ x = 1}) hx
  have hWts : W ⊆ tsupport χ := fun x hx =>
    subset_tsupport _ (by simp [hW1 x hx])
  have hclW : closure W ⊆ tsupport χ := closure_minimal hWts (isClosed_tsupport _)
  refine ⟨χ, hχ, hχ01, W, hWdef ▸ isOpen_interior,
    hWdef ▸ subset_interior_iff_mem_nhdsSet.2 hone,
    hχ.2.1.of_isClosed_subset isClosed_closure hclW, hclW.trans hχ.2.2, hW1, rfl,
    eqOn_a P hU hχ hχ01 hW1, eqOn_b P hU hχ hχ01 hW1, eqOn_c P hU hχ hχ01 hW1,
    nonempty_isC1Coeff P hU hχ hχ01, nonempty_isWkInftyCoeff P hU hχ hχ01,
    nonempty_isWkInftyLower P hU hχ hχ01⟩

end EllipticPdes.Regularity
