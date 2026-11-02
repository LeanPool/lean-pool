/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2

/-!
# CubeComparison

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the per-realization comparison layer of the corrector-limit proof

ABK26, Lemma `l.corrector.limit`, works at each fixed realization with the two
cube problems

`-Δ w_D^{(K)} = ∇ · f` in `cu_K`, `w_D^{(K)} = 0` on `∂cu_K`, and
`-Δ w_N^{(K)} = ∇ · f` in `cu_K`, `n · (∇ w_N^{(K)} + f) = 0` on `∂cu_K`.

* `IsPotentialZeroTraceOn U D` together with `IsSolenoidalOn U (D + f)`, and
* `IsPotentialOn U N` together with `IsSolenoidalZeroNormalTraceOn U (N + f)`,

which are literal transcriptions of `e.corrector.limit.pde`: the first pair says
`w_D^{(K)} ∈ H¹₀(cu_K)` and `⨍ (∇w_D^{(K)} + f) · ∇φ = 0` for every `φ ∈
H¹₀(cu_K)`, the second says `w_N^{(K)} ∈ H¹(cu_K)` and the same identity for
every `φ ∈ H¹(cu_K)`, the natural boundary condition.

This file proves, at a single realization and on an arbitrary domain, the two
purely deterministic facts the proof extracts from those formulations:

* `e.ordering.corrector.limit`, the Step-1 ordering `‖∇w_D^{(K)}‖²_{L²} ≤
  ‖∇w_N^{(K)}‖²_{L²}`; and
* the Step-2 comparison against an admissible zero-trace competitor, in the
  sharp form `‖D‖² ≥ -2⟪f, v⟫ - ‖v‖²`, which is the statement that `D` minimizes
  `E(v) = ½‖v‖² + ⟪f, v⟫` over the zero-trace potential fields.

Both are unconditional: no approximation lemma, no stationarity, and no
probability enters here.  The abstract Hilbert-space versions of the same two
facts are in `Algsuperdiff/Section3/Provider/Corrector/VariationalEnergy.lean`;
this file is their concrete counterpart on the CoarseGraining Sobolev carriers,
where the admissible classes are `IsPotentialZeroTraceOn` and `IsPotentialOn`
rather than abstract submodules.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

variable {d : ℕ}

/-! ### Pointwise algebra of the Euclidean dot product -/

/-- The polarization expansion `|a - b|² = |a|² - 2 a · b + |b|²` for the
Euclidean dot product of the project's vector carrier `Vec d`. -/
theorem vecDot_sub_self (a b : Vec d) :
    vecDot (a - b) (a - b) = vecDot a a - 2 * vecDot a b + vecDot b b := by
  simp only [vecDot, Pi.sub_apply]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      show (a i - b i) * (a i - b i) = a i * a i - 2 * (a i * b i) + b i * b i by ring,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- The polarization expansion `|a + b|² = |a|² + 2 a · b + |b|²`. -/
theorem vecDot_add_self (a b : Vec d) :
    vecDot (a + b) (a + b) = vecDot a a + 2 * vecDot a b + vecDot b b := by
  simp only [vecDot, Pi.add_apply]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      show (a i + b i) * (a i + b i) = a i * a i + 2 * (a i * b i) + b i * b i by ring,
    Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The Euclidean dot product of a vector with itself is nonnegative. -/
theorem vecDot_self_nonneg (a : Vec d) : 0 ≤ vecDot a a :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (a i)

/-- The squared-distance polarization identity integrated over any domain. -/
theorem setIntegral_vecDot_sub_self_eq {U : Set (Vec d)} {D v : Vec d → Vec d}
    (hD : MemVectorL2 U D) (hv : MemVectorL2 U v) :
    (∫ x in U, vecDot (D x - v x) (D x - v x)) =
      (∫ x in U, vecDot (D x) (D x)) - 2 * (∫ x in U, vecDot (D x) (v x)) +
        ∫ x in U, vecDot (v x) (v x) := by
  have hDD := integrableOn_vecDot_of_memVectorL2 hD hD
  have hDv := integrableOn_vecDot_of_memVectorL2 hD hv
  have hvv := integrableOn_vecDot_of_memVectorL2 hv hv
  calc
    (∫ x in U, vecDot (D x - v x) (D x - v x)) =
        ∫ x in U, vecDot (D x) (D x) - 2 * vecDot (D x) (v x) + vecDot (v x) (v x) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => vecDot_sub_self _ _)
    _ = _ := by
      have hadd := integral_add (hDD.sub (hDv.const_mul 2)) hvv
      have hsub := integral_sub hDD (hDv.const_mul 2)
      simp only [Pi.sub_apply] at hadd hsub
      rw [hadd, hsub, integral_const_mul]

/-! ### Testing the weak formulations -/

/-- Testing a solenoidal field against a zero-trace potential competitor.  With
`g = ∇w_D^{(K)} + f` this is the first display of
`e.testing.by.vKL.corrector.limit`. -/
theorem setIntegral_vecDot_eq_zero_of_isSolenoidalOn {U : Set (Vec d)}
    {g v : Vec d → Vec d} (hg : IsSolenoidalOn U g)
    (hv : IsPotentialZeroTraceOn U v) :
    ∫ x in U, vecDot (g x) (v x) = 0 := by
  obtain ⟨u, hu⟩ := hv
  have := hg u
  rwa [hu] at this

/-- Testing a solenoidal field with vanishing normal trace against an arbitrary
potential competitor.  With `g = ∇w_N^{(K)} + f` this is the Neumann natural
boundary condition used in Step 3 of ABK26. -/
theorem setIntegral_vecDot_eq_zero_of_isSolenoidalZeroNormalTraceOn {U : Set (Vec d)}
    {g v : Vec d → Vec d} (hg : IsSolenoidalZeroNormalTraceOn U g)
    (hv : IsPotentialOn U v) :
    ∫ x in U, vecDot (g x) (v x) = 0 := by
  obtain ⟨u, hu⟩ := hv
  have := hg u
  rwa [hu] at this

/-- Every zero-trace potential field is a potential field: `H¹₀(U) ⊆ H¹(U)`.
This is the inclusion behind `e.ordering.corrector.limit`. -/
theorem isPotentialOn_of_isPotentialZeroTraceOn {U : Set (Vec d)}
    {v : Vec d → Vec d} (hv : IsPotentialZeroTraceOn U v) : IsPotentialOn U v := by
  obtain ⟨u, hu⟩ := hv
  exact ⟨u.toH1Function, hu⟩

/-- Splitting the tested flux into its two square-integrable halves. -/
theorem setIntegral_vecDot_add_left_split {U : Set (Vec d)} {D F v : Vec d → Vec d}
    (hD : MemVectorL2 U D) (hF : MemVectorL2 U F) (hv : MemVectorL2 U v) :
    ∫ x in U, vecDot (D x + F x) (v x)
      = (∫ x in U, vecDot (D x) (v x)) + ∫ x in U, vecDot (F x) (v x) := by
  rw [← integral_add (integrableOn_vecDot_of_memVectorL2 hD hv)
    (integrableOn_vecDot_of_memVectorL2 hF hv)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => vecDot_add_left _ _ _)

/-- Completing the square bounds the energy from a single tested flux identity. -/
theorem setIntegral_vecDot_self_ge_of_test {U : Set (Vec d)} {D F v : Vec d → Vec d}
    (hD : MemVectorL2 U D) (hF : MemVectorL2 U F) (hv : MemVectorL2 U v)
    (h0 : ∫ x in U, vecDot (D x + F x) (v x) = 0) :
    -2 * (∫ x in U, vecDot (F x) (v x)) - (∫ x in U, vecDot (v x) (v x))
      ≤ ∫ x in U, vecDot (D x) (D x)  := by
  have hsplit := setIntegral_vecDot_add_left_split hD hF hv
  rw [h0] at hsplit
  have hnonneg : 0 ≤ ∫ x in U, vecDot (D x - v x) (D x - v x) :=
    integral_nonneg fun x => vecDot_self_nonneg _
  rw [setIntegral_vecDot_sub_self_eq hD hv] at hnonneg
  linarith only [hsplit, hnonneg]

/-! ### The Step-2 comparison -/

/-- **Step 2 of `l.corrector.limit` at a fixed realization**.

If `D` is the gradient of the `H¹₀(U)` solution of `-Δw = ∇·F`, i.e. `D` is a
zero-trace potential field with `D + F` solenoidal, then for *every* admissible
zero-trace competitor `v`

`-2 ∫_U F · v - ∫_U |v|² ≤ ∫_U |D|²`.

Equivalently `D` minimizes `E(v) = ½∫|v|² + ∫F·v` over the zero-trace potential
fields, which is the variational characterization asserted in Step 1 and used in
Step 2 with `v = ∇v_{K,L}`.

Only the weak formulation and square integrability are used; no boundary
regularity, no approximation lemma and no probability. -/
theorem setIntegral_vecDot_self_ge_of_isSolenoidalOn {U : Set (Vec d)}
    {D F v : Vec d → Vec d} (hD : MemVectorL2 U D) (hF : MemVectorL2 U F)
    (hv : MemVectorL2 U v) (hsol : IsSolenoidalOn U fun x => D x + F x)
    (hvpot : IsPotentialZeroTraceOn U v) :
    -2 * (∫ x in U, vecDot (F x) (v x)) - (∫ x in U, vecDot (v x) (v x))
      ≤ ∫ x in U, vecDot (D x) (D x) := by
  exact setIntegral_vecDot_self_ge_of_test hD hF hv
    (setIntegral_vecDot_eq_zero_of_isSolenoidalOn hsol hvpot)

/-- The flux rewriting of the Step-2 comparison.  Completing the square turns
`-2 ∫ F · v - ∫ |v|²` into `∫ |F|² - ∫ |v + F|²`, which is the form the
corrector-limit proof uses: the competitor enters only through the *flux*
`v + F`, whose stationary limit is `∇w + f`. -/
theorem setIntegral_vecDot_flux_eq {U : Set (Vec d)} {F v : Vec d → Vec d}
    (hF : MemVectorL2 U F) (hv : MemVectorL2 U v) :
    (∫ x in U, vecDot (F x) (F x)) - ∫ x in U, vecDot (v x + F x) (v x + F x)
      = -2 * (∫ x in U, vecDot (F x) (v x)) - ∫ x in U, vecDot (v x) (v x) := by
  have hexp := setIntegral_vecDot_sub_self_eq hv hF.neg
  simp only [Pi.neg_apply, sub_neg_eq_add, vecDot_neg_left, vecDot_neg_right,
    neg_neg, integral_neg] at hexp
  have hcomm : (∫ x in U, vecDot (v x) (F x)) = ∫ x in U, vecDot (F x) (v x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => vecDot_comm _ _)
  rw [hcomm] at hexp
  linarith only [hexp]

/-- **The Step-2 comparison in flux form**.  For every admissible zero-trace
competitor `v`,

`∫_U |F|² - ∫_U |v + F|² ≤ ∫_U |D|²`.

This is the shape consumed in the infinite-volume limit: the left-hand side
converges to `E[|f|²] - E[|f + ∇w|²] = E[|∇w|²]` when `v` approximates `∇w`. -/
theorem setIntegral_vecDot_flux_ge_of_isSolenoidalOn {U : Set (Vec d)}
    {D F v : Vec d → Vec d} (hD : MemVectorL2 U D) (hF : MemVectorL2 U F)
    (hv : MemVectorL2 U v) (hsol : IsSolenoidalOn U fun x => D x + F x)
    (hvpot : IsPotentialZeroTraceOn U v) :
    (∫ x in U, vecDot (F x) (F x)) - (∫ x in U, vecDot (v x + F x) (v x + F x))
      ≤ ∫ x in U, vecDot (D x) (D x) := by
  rw [setIntegral_vecDot_flux_eq hF hv]
  exact setIntegral_vecDot_self_ge_of_isSolenoidalOn hD hF hv hsol hvpot

/-! ### The Step-1 ordering -/

/-- **`e.ordering.corrector.limit`** at a fixed realization: the Dirichlet
gradient carries no more energy than the Neumann gradient,

`∫_U |∇w_D|² ≤ ∫_U |∇w_N|²`.

`D` is the gradient of the `H¹₀(U)` solution and `N` the gradient of the
`H¹(U)` solution of the same equation `-Δw = ∇·F`, the Neumann natural boundary
condition being `IsSolenoidalZeroNormalTraceOn U (N + F)`.  The proof is the
paper's: `H¹₀(U) ⊆ H¹(U)`, so the Neumann energy is the smaller of the two, and
the energy identity converts that into the displayed ordering of the gradient
norms. -/
theorem setIntegral_vecDot_self_le_of_isSolenoidal {U : Set (Vec d)}
    {D N F : Vec d → Vec d} (hD : MemVectorL2 U D) (hN : MemVectorL2 U N)
    (hF : MemVectorL2 U F)
    (hDpot : IsPotentialZeroTraceOn U D) (hDsol : IsSolenoidalOn U fun x => D x + F x)
    (hNsol : IsSolenoidalZeroNormalTraceOn U fun x => N x + F x) :
    (∫ x in U, vecDot (D x) (D x)) ≤ ∫ x in U, vecDot (N x) (N x) := by
  have hDtest := setIntegral_vecDot_eq_zero_of_isSolenoidalOn hDsol hDpot
  have hDself := setIntegral_vecDot_add_left_split hD hF hD
  rw [hDtest] at hDself
  have hcomparison := setIntegral_vecDot_self_ge_of_test hN hF hD
    (setIntegral_vecDot_eq_zero_of_isSolenoidalZeroNormalTraceOn hNsol
      (isPotentialOn_of_isPotentialZeroTraceOn hDpot))
  linarith only [hDself, hcomparison]

end Algsuperdiff.Section3.Provider.Corrector
