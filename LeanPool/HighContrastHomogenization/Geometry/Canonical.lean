/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.SchurData

/-!
# High-contrast homogenization: Geometry.Canonical

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The canonical metric of a positive block

For a positive doubled block `E` the reference text sets, in
`e.scale.selection.canonical.metric`, `M(E) := E # E^♯` and
`𝔡(E) := |M(E)^{-1/2} E M(E)^{-1/2}|^2`.  The facts about the canonical metric
used in `p.global.selection` are that
`M(E)` is self-dual, that it has a unique factorization
`M(E) = G_{-g}^t diag(m, m^{-1}) G_{-g}` with `m` positive and `g` skew, that
`𝔡(E) = |(E^♯)^{-1/2} E (E^♯)^{-1/2}|`, and — when `E^♯ ≤ E` — the balance chain
`E^♯ ≤ M(E) ≤ E ≤ 𝔡(E)^{1/2} M(E)` together with `det M(E) = 1`.

Self-duality is the inverse and congruence clauses of the geometric-mean
toolkit applied to the reflection.  The factorization is self-duality read
through the Schur data: the sharp map sends `(s, s_*, k)` to `(s_*, s, -k^t)`,
so a self-dual block has `s = s_*` and `k` skew.  The imbalance identity is the
observation that the generalized eigenvalues of `E` relative to `E^♯` are those
of `C := M(E)^{-1/2} E M(E)^{-1/2}` relative to `C^{-1}`, that is the
eigenvalues of `C^2`.

The pair `(m, g)` is introduced by the well-definedness-first route: the
uniqueness theorem `existsUnique_canonFactor` comes first, the definition
`canonFactor` is made by choice, and `canonFactor_spec` and `canonFactor_eq`
then characterize it, so that nothing downstream depends on the choice.
-/

namespace HCPolySupport
namespace HighContrast

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

attribute [local instance] Classical.propDecidable

noncomputable section

variable {d : ℕ}

/-- The canonical metric block `M(E) = E # E^♯` of
`e.scale.selection.canonical.metric`. -/
@[expose]
def canonBlock (E : FullBlockMat d) : FullBlockMat d :=
  matGeomMean E (fullBlockSharp E)

/-- The imbalance `𝔡(E) = |M(E)^{-1/2} E M(E)^{-1/2}|^2` of
`e.scale.selection.canonical.metric`. -/
@[expose]
def canonImbalance (E : FullBlockMat d) : ℝ :=
  relSize E (canonBlock E) ^ 2

theorem posDef_canonBlock {E : FullBlockMat d} (hE : E.PosDef) :
    (canonBlock E).PosDef :=
  posDef_matGeomMean hE (posDef_fullBlockSharp hE)

/-! ## Self-duality -/

/-- **The canonical metric is self-dual**. -/
theorem fullBlockSharp_canonBlock {E : FullBlockMat d} (hE : E.PosDef) :
    fullBlockSharp (canonBlock E) = canonBlock E := by
  have hS : (fullBlockSharp E).PosDef := posDef_fullBlockSharp hE
  have hRsymm : (fullBlockRefl d)ᴴ = fullBlockRefl d := conjTranspose_fullBlockRefl
  have hRu : IsUnit (fullBlockRefl d) := isUnit_fullBlockRefl
  have hcong := matGeomMean_conj hE.inv hS.inv hRu
  rw [hRsymm] at hcong
  have hE' : fullBlockRefl d * E⁻¹ * fullBlockRefl d = fullBlockSharp E := rfl
  have hS' : fullBlockRefl d * (fullBlockSharp E)⁻¹ * fullBlockRefl d = E :=
    fullBlockSharp_fullBlockSharp hE
  rw [hE', hS'] at hcong
  calc fullBlockSharp (canonBlock E)
      = fullBlockRefl d * (matGeomMean E (fullBlockSharp E))⁻¹ * fullBlockRefl d := rfl
    _ = fullBlockRefl d * matGeomMean E⁻¹ (fullBlockSharp E)⁻¹ * fullBlockRefl d := by
        rw [matGeomMean_inv hE hS]
    _ = matGeomMean (fullBlockSharp E) E := hcong.symm
    _ = canonBlock E := (matGeomMean_comm hE hS).symm

/-! ## The canonical factorization -/

/-- **The canonical factorization** (`e.scale.selection.canonical.metric`).
There is a unique pair consisting of a positive `m` and a skew `g` with
`M(E) = G_{-g}^t diag(m, m^{-1}) G_{-g}`. -/
theorem existsUnique_canonFactor {E : FullBlockMat d} (hE : E.PosDef) :
    ∃! p : Mat d × Mat d,
      p.1.PosDef ∧ (p.2)ᴴ = -p.2 ∧ canonBlock E = schurBlock p.1 p.1 p.2 := by
  obtain ⟨s, sStar, k, hs, hstar, hform⟩ := exists_schurBlock (posDef_canonBlock hE)
  have hdual : schurBlock sStar s (-kᴴ) = schurBlock s sStar k := by
    rw [← fullBlockSharp_schurBlock hs hstar, ← hform, fullBlockSharp_canonBlock hE, hform]
  obtain ⟨h1, h2, h3⟩ := schurBlock_injective hs hstar hdual
  have hss : s = sStar := h1.symm
  have hskew : kᴴ = -k := neg_eq_iff_eq_neg.mp h3
  refine ⟨(s, k), ⟨hs, hskew, ?_⟩, ?_⟩
  · rw [hform, hss]
  · rintro ⟨m, g⟩ ⟨hm, hg, hmg⟩
    have heq : schurBlock m m g = schurBlock s sStar k := by rw [← hmg, hform]
    obtain ⟨e1, _, e3⟩ := schurBlock_injective hm hstar heq
    exact Prod.ext e1 e3

/-- The hedged existential behind the canonical pair: on positive data it is
`existsUnique_canonFactor`, elsewhere it is a junk witness. -/
theorem canonFactor_exists (E : FullBlockMat d) :
    ∃ p : Mat d × Mat d, E.PosDef →
      (p.1.PosDef ∧ (p.2)ᴴ = -p.2 ∧ canonBlock E = schurBlock p.1 p.1 p.2) := by
  by_cases hE : E.PosDef
  · obtain ⟨p, hp, -⟩ := existsUnique_canonFactor hE
    exact ⟨p, fun _ => hp⟩
  · exact ⟨(1, 0), fun h => absurd h hE⟩

/-- The canonical pair `(m(E), g(E))`, by choice from
`existsUnique_canonFactor`; the junk value on non-positive data is never
used. -/
@[expose]
def canonFactor (E : FullBlockMat d) : Mat d × Mat d :=
  (canonFactor_exists E).choose

/-- The canonical metric `m(E)` of `e.scale.selection.canonical.metric`. -/
@[expose]
def canonMetric (E : FullBlockMat d) : Mat d := (canonFactor E).1

/-- The canonical shear `g(E)` of the canonical factorization. -/
@[expose]
def canonShear (E : FullBlockMat d) : Mat d := (canonFactor E).2

/-- **Specification of the canonical pair.**  `m(E)` is positive, `g(E)` is
skew, and they factor `M(E)` as in `e.scale.selection.canonical.metric`. -/
theorem canonFactor_spec {E : FullBlockMat d} (hE : E.PosDef) :
    (canonMetric E).PosDef ∧ (canonShear E)ᴴ = -canonShear E ∧
      canonBlock E = schurBlock (canonMetric E) (canonMetric E) (canonShear E) :=
  (canonFactor_exists E).choose_spec hE

/-- **The canonical pair is characterized**, not merely chosen: any positive
`m` and skew `g` factoring `M(E)` are `m(E)` and `g(E)`. -/
theorem canonFactor_eq {E : FullBlockMat d} (hE : E.PosDef) {m g : Mat d}
    (hm : m.PosDef) (hg : gᴴ = -g) (hfac : canonBlock E = schurBlock m m g) :
    m = canonMetric E ∧ g = canonShear E := by
  obtain ⟨p, -, huniq⟩ := existsUnique_canonFactor hE
  have h1 : (m, g) = p := huniq (m, g) ⟨hm, hg, hfac⟩
  have h2 : (canonMetric E, canonShear E) = p := huniq _ (canonFactor_spec hE)
  have h3 : (m, g) = (canonMetric E, canonShear E) := h1.trans h2.symm
  exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩

/-- **The lower-right block of the canonical metric** is `m(E)^{-1}`.  This is
what makes the reference text's step "taking the lower-right principal blocks"
in `e.global.selection.metric.loss` and `e.global.selection.metric.comparison` read
as a statement about `m`. -/
theorem toBlocks₂₂_canonBlock {E : FullBlockMat d} (hE : E.PosDef) :
    (canonBlock E).toBlocks₂₂ = (canonMetric E)⁻¹ := by
  obtain ⟨-, -, hfac⟩ := canonFactor_spec hE
  rw [hfac, toBlocks₂₂_schurBlock]

/-- The canonical metric is positive definite, hence so is its inverse. -/
theorem posDef_canonMetric {E : FullBlockMat d} (hE : E.PosDef) :
    (canonMetric E).PosDef := (canonFactor_spec hE).1

/-! ## The imbalance identity -/

/-- **The imbalance identity** `e.response.canonical.imbalance`:
`𝔡(E) = |(E^♯)^{-1/2} E (E^♯)^{-1/2}|`. -/
theorem canonImbalance_eq {E : FullBlockMat d} (hE : E.PosDef) :
    canonImbalance E = relSize E (fullBlockSharp E) := by
  have hM : (canonBlock E).PosDef := posDef_canonBlock hE
  have hS : (fullBlockSharp E).PosDef := posDef_fullBlockSharp hE
  set R : FullBlockMat d := matSqrt (canonBlock E)⁻¹ with hRdef
  have hRsymm : Rᴴ = R := conjTranspose_matSqrt_inv hM
  have hRu : IsUnit R := isUnit_matSqrt_inv hM
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det _).mp hRu
  set C : FullBlockMat d := R * E * R with hCdef
  have hC : C.PosDef := by
    have := posDef_normalize hE hM
    rwa [← hRdef, ← hCdef] at this
  have hCdet : IsUnit C.det := isUnit_det_of_posDef hC
  -- the sharp normalizes to the inverse of `C`
  have hRM : R * canonBlock E * R = 1 := matSqrt_inv_conj hM
  have hRMinv : R * canonBlock E = R⁻¹ := by
    have h := congrArg (fun M : FullBlockMat d => M * R⁻¹) hRM
    rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hRdet, Matrix.mul_one, Matrix.one_mul] at h
  have hMR : canonBlock E * R = R⁻¹ := by
    have h := congrArg (fun M : FullBlockMat d => R⁻¹ * M) hRM
    rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hRdet,
      Matrix.one_mul, Matrix.mul_one] at h
  have hSharpRic : fullBlockSharp E = canonBlock E * E⁻¹ * canonBlock E :=
    (matGeomMean_riccati hE hS).symm
  have hRSR : R * fullBlockSharp E * R = C⁻¹ := by
    have hCinv : C⁻¹ = R⁻¹ * E⁻¹ * R⁻¹ := by
      rw [hCdef, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
      exact (Matrix.mul_assoc _ _ _).symm
    rw [hSharpRic, hCinv]
    calc R * (canonBlock E * E⁻¹ * canonBlock E) * R
        = (R * canonBlock E) * E⁻¹ * (canonBlock E * R) := by noncomm_ring
      _ = R⁻¹ * E⁻¹ * R⁻¹ := by rw [hRMinv, hMR]
  -- transport the relative size through the congruence
  have hcong := relSize_congr (P := E) (Q := fullBlockSharp E) (C := R)
    hE.posSemidef hS hRu
  rw [hRsymm] at hcong
  rw [← hCdef, hRSR] at hcong
  -- the relative size of `C` against its inverse is the square of the norm of `C`
  have hCC : relSize C C⁻¹ = ‖C * C‖ := by
    rw [relSize_def, Matrix.nonsing_inv_nonsing_inv _ hCdet]
    have hsq : matSqrt C * C * matSqrt C = C * C := by
      have h1 : matSqrt C * matSqrt C = C := (matSqrt_spec hC.posSemidef).2
      calc matSqrt C * C * matSqrt C
          = matSqrt C * (matSqrt C * matSqrt C) * matSqrt C := by rw [h1]
        _ = (matSqrt C * matSqrt C) * (matSqrt C * matSqrt C) := by noncomm_ring
        _ = C * C := by rw [h1]
    rw [hsq]
  have hnorm : ‖C * C‖ = ‖C‖ ^ 2 := by
    have hh := CStarRing.norm_star_mul_self (x := C)
    rw [Matrix.star_eq_conjTranspose, hC.isHermitian] at hh
    rw [hh, sq]
  rw [canonImbalance, ← hcong, hCC, hnorm]
  congr 1

/-! ## The balance chain and the determinant -/

/-- The scalar in the balance chain is the relative size of `E` against `M(E)`. -/
theorem sqrt_canonImbalance (E : FullBlockMat d) :
    Real.sqrt (canonImbalance E) = relSize E (canonBlock E) := by
  rw [canonImbalance, Real.sqrt_sq (relSize_nonneg _ _)]

/-- **The canonical balance chain**: the canonical metric lies between a block
and its dual. -/
theorem canonBalance {E : FullBlockMat d} (hE : E.PosDef)
    (hle : fullBlockSharp E ≤ E) :
    fullBlockSharp E ≤ canonBlock E ∧ canonBlock E ≤ E ∧
      E ≤ Real.sqrt (canonImbalance E) • canonBlock E := by
  have hS : (fullBlockSharp E).PosDef := posDef_fullBlockSharp hE
  refine ⟨?_, ?_, ?_⟩
  · have h := matGeomMean_mono hS hE hS hS hle le_rfl
    rwa [matGeomMean_self hS] at h
  · have h := matGeomMean_mono hE hE hS hE le_rfl hle
    rwa [matGeomMean_self hE] at h
  · rw [sqrt_canonImbalance E]
    exact le_relSize_smul hE.posSemidef (posDef_canonBlock hE)

/-- **The canonical metric has unit determinant**. -/
theorem det_canonBlock {E : FullBlockMat d} (hE : E.PosDef) :
    (canonBlock E).det = 1 := by
  have hS : (fullBlockSharp E).PosDef := posDef_fullBlockSharp hE
  have hdetE : (0 : ℝ) < E.det := hE.det_pos
  rw [canonBlock, det_matGeomMean hE hS, det_fullBlockSharp hE,
    mul_inv_cancel₀ (ne_of_gt hdetE), Real.sqrt_one]

end

end HighContrast
end HCPolySupport
