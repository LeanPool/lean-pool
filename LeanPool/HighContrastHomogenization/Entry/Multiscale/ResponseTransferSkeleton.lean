/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Setup.SelectionData
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.ResponseTransferHelpers
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.EccentricityScaleDecay
public import LeanPool.HighContrastHomogenization.Entry.Geometry.CanonicalMetricBounds
public import LeanPool.HighContrastHomogenization.Entry.Response.Transfer.AdaptedResponseAssembly

/-!
# High-contrast homogenization: Entry.Multiscale.ResponseTransferSkeleton

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Inputs for the proof of `p.response.transfer` (`HCPoly/Entry/Statements/ResponseTransfer.lean`)

Decomposition of the printed proof `p.response.transfer` of Proposition
`p.response.transfer` into a DAG of lemmas whose statements are
the content. The assembly itself is `HCPolySupport.HighContrast.Entry.response_transfer`
(`HCPoly/Entry/ResponseTransfer.lean`), which imports this file.

Conventions (following `p.scale.selection` and `HCPoly/Entry/Multiscale/ScaleSelection/`):

* The antecedent clauses on `(P, E, Ψ, K, Src, B, jStar, F, s, t)` of `p.response.transfer`
  are bundled verbatim in the scaffold predicate `RawOutput`; the assembly unpacks its
  own binders into it and adds nothing.
* Every kernel chooses its `Csrc` before `ε`; the assembly takes the maximum of the
  kernel source constants and of the kernel `Bresp`s, which is legitimate because the source
  premise and the `B`-threshold are monotone (`RawOutput.mono`, using `1 < K` from
  `CoarseEllipticityDagger.one_lt_growthWitness`).
* No premise is added anywhere. In particular the gap `obligation.a.CFS`
  (HC Lemma 2.15's extra premise at `p.response.transfer`, never supplied by the paper) is NOT
  added to `persistence_transfer_kernel`; that kernel states exactly what the paper claims.
* The four kernels are the four unproved external inputs of the argument:
  `ext.adapted.response` with Step 3, `ext.persistence.transfer` with HC Lemma 2.15
  and the eccentricity bound, the canonical comparison, and
  near `e.response.canonical.imbalance`. They are assumed, not gaps in the proof.
* Unused hypothesis binders of a statement are underscore-prefixed.
* Printed `𝐀hom_{m,Id}` is `adaptedMean P (1 : Mat d) m`; printed `Θ_m` is `annealedContrast P m`;
  printed `q` is `Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean annealedContrast aspectRatio
  blockContrast blockScale)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder
/-! `RawOutput` was declared here; it is now
declared, verbatim and in this same namespace, in
`HCPoly/Entry/Response/Core/ResponseBlockObjects.lean`, which this file imports.  It had to move so
that the imported files can state their lemmas over
it.  Nothing else about it changed, and R1's statement below is unchanged. -/

/-! ## Auxiliary lemmas -/

/-- Step 1 of `p.response.transfer`: tolerances from `(d, δ)` only.
Hint: `ηiso := δ/60`, `δad := δ/(120 d)`, `ηm := δ/120`, `ηp := ηiso`; Bernoulli for
`(1+δad)^(-d) ≥ 1 - d δad`; `(1+η)^3/(1-η) ≤ 1 + 7 η` for `η ≤ 1/60`. -/
theorem response_tolerances (d : ℕ) (_hd : 2 ≤ d) (δ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ ηiso δad ηp ηm : ℝ,
      ηiso ∈ Set.Ioo (0 : ℝ) 1 ∧ δad ∈ Set.Ioc (0 : ℝ) 1 ∧
      ηp ∈ Set.Ioo (0 : ℝ) 1 ∧ ηm ∈ Set.Ioo (0 : ℝ) 1 ∧
      ηp ≤ ηiso ∧
      1 - ηiso ≤ (1 + δad) ^ (-(d : ℝ)) - ηm ∧
      3 * ((1 + ηiso) ^ 3 / (1 - ηiso) * (1 + δad) - 1) ≤ δ := by
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hdle : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast _hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith only [hdle]
  have hdenpos : (0 : ℝ) < 120 * (d : ℝ) := by positivity
  refine ⟨δ / 60, δ / (120 * d), δ / 60, δ / 120, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by positivity, by linarith only [hδ1]⟩
  · refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hdenpos]
    nlinarith only [hδ1, hdle]
  · exact ⟨by positivity, by linarith only [hδ1]⟩
  · exact ⟨by positivity, by linarith only [hδ1]⟩
  · rfl
  · have hxpos : (0 : ℝ) < 1 + δ / (120 * (d : ℝ)) := by positivity
    have hxle : δ / (120 * (d : ℝ)) ≤ 1 := by
      rw [div_le_iff₀ hdenpos]
      nlinarith only [hδ1, hdle]
    have hbound : (-2 : ℝ) ≤ -(δ / (120 * (d : ℝ))) := by linarith only [hxle]
    have hbern : 1 + (d : ℝ) * (-(δ / (120 * (d : ℝ)))) ≤ (1 - δ / (120 * (d : ℝ))) ^ d := by
      have hb := one_add_mul_le_pow (a := -(δ / (120 * (d : ℝ)))) hbound d
      rw [show (1 : ℝ) + -(δ / (120 * (d : ℝ))) = 1 - δ / (120 * (d : ℝ)) by ring] at hb
      exact hb
    have hsq : (1 - δ / (120 * (d : ℝ))) * (1 + δ / (120 * (d : ℝ))) ≤ 1 := by
      nlinarith only [sq_nonneg (δ / (120 * (d : ℝ)))]
    have hsq_nonneg : 0 ≤ (1 - δ / (120 * (d : ℝ))) * (1 + δ / (120 * (d : ℝ))) :=
      mul_nonneg (by linarith only [hxle]) (by linarith only [hxpos])
    have hmul_pow : (1 - δ / (120 * (d : ℝ))) ^ d * (1 + δ / (120 * (d : ℝ))) ^ d ≤ 1 := by
      have hpow_le : ((1 - δ / (120 * (d : ℝ))) * (1 + δ / (120 * (d : ℝ)))) ^ d ≤ 1 :=
        pow_le_one₀ hsq_nonneg hsq
      rw [mul_pow] at hpow_le
      exact hpow_le
    have hdmul : (d : ℝ) * (δ / (120 * (d : ℝ))) = δ / 120 := by
      field_simp [ne_of_gt hdpos]
    have hstep1 : 1 - δ / 120 ≤ (1 - δ / (120 * (d : ℝ))) ^ d := by
      have heq : 1 + (d : ℝ) * (-(δ / (120 * (d : ℝ)))) = 1 - δ / 120 := by
        rw [mul_neg, hdmul]
        ring
      linarith only [hbern, heq]
    have hpowpos : (0 : ℝ) < (1 + δ / (120 * (d : ℝ))) ^ d := by positivity
    have hstep2 : (1 - δ / 120) * (1 + δ / (120 * (d : ℝ))) ^ d ≤ 1 := by
      calc
        (1 - δ / 120) * (1 + δ / (120 * (d : ℝ))) ^ d
            ≤ (1 - δ / (120 * (d : ℝ))) ^ d * (1 + δ / (120 * (d : ℝ))) ^ d :=
          mul_le_mul_of_nonneg_right hstep1 (le_of_lt hpowpos)
        _ ≤ 1 := hmul_pow
    have hrpow_eq : (1 + δ / (120 * (d : ℝ))) ^ (-(d : ℝ)) = ((1 + δ / (120 * (d : ℝ))) ^ d)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hxpos), Real.rpow_natCast]
    have hinv : 1 - δ / 120 ≤ ((1 + δ / (120 * (d : ℝ))) ^ d)⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ hpowpos]
      exact hstep2
    rw [hrpow_eq]
    linarith only [hinv]
  · have heta1 : (0 : ℝ) < 1 - δ / 60 := by linarith only [hδ1]
    have hetapos : (0 : ℝ) < δ / 60 := by positivity
    have hetale : δ / 60 ≤ (1 : ℝ) / 60 := by linarith only [hδ1]
    have hetasq : (δ / 60) * (δ / 60) ≤ (δ / 60) * (1 / 60) :=
      mul_le_mul_of_nonneg_left hetale hetapos.le
    have hetacube : (δ / 60) * ((δ / 60) * (δ / 60)) ≤ (δ / 60) * ((δ / 60) * (1 / 60)) :=
      mul_le_mul_of_nonneg_left hetasq hetapos.le
    have hA : (1 + δ / 60) ^ 3 ≤ (1 + 7 * (δ / 60)) * (1 - δ / 60) := by
      nlinarith only [hetasq, hetacube, hetale, hetapos]
    have hAdiv : (1 + δ / 60) ^ 3 / (1 - δ / 60) ≤ 1 + 7 * (δ / 60) := by
      rw [div_le_iff₀ heta1]
      exact hA
    have hadbound : δ / (120 * (d : ℝ)) ≤ δ / 240 := by
      rw [div_le_iff₀ hdenpos]
      nlinarith only [hδ0, hdle, mul_nonneg hδ0.le (sub_nonneg.mpr hdle)]
    have hstep : (1 + δ / 60) ^ 3 / (1 - δ / 60) * (1 + δ / (120 * (d : ℝ))) ≤ (1 + 7 * (δ /
      60)) * (1 + δ / (120 * (d : ℝ))) :=
      mul_le_mul_of_nonneg_right hAdiv (by positivity)
    have hcross : (δ / 60) * (δ / (120 * (d : ℝ))) ≤ (δ / 60) * (δ / 240) :=
      mul_le_mul_of_nonneg_left hadbound hetapos.le
    have hδsq : δ * δ ≤ δ := by
      nlinarith only [hδ0, hδ1, mul_nonneg hδ0.le (sub_nonneg.mpr hδ1)]
    have hYbound : (1 + 7 * (δ / 60)) * (1 + δ / (120 * (d : ℝ))) ≤ 1 + δ / 3 := by
      nlinarith only [hadbound, hcross, hδsq, hδ0]
    have hchain : (1 + δ / 60) ^ 3 / (1 - δ / 60) * (1 + δ / (120 * (d : ℝ))) ≤ 1 + δ / 3 :=
      le_trans hstep hYbound
    linarith only [hchain]

/-- The Euclidean adapted cell is the centered cube: `matVecMul 1 = id`. -/
theorem adaptedCell_one (d : ℕ) (j : ℤ) :
    HighContrast.adaptedCell (1 : Mat d) j = HighContrast.centeredCube d j := by
  unfold HighContrast.adaptedCell
  rw [show matVecMul (1 : Mat d) = id by
    funext x
    change Matrix.mulVec (1 : Mat d) x = x
    exact Matrix.one_mulVec x]
  exact Set.image_id (HighContrast.centeredCube d j)

/-- `Θ_m = blockContrast 𝐀hom_{m,Id}` (`HCPoly/Setup/Moments.lean`, `adaptedMean`;
`HCPoly/Entry/Geometry/RoundedGridBasic.lean`, `adaptedCell_one`). -/
theorem annealedContrast_eq (d : ℕ) (P : Measure (CoeffSpace d)) (m : ℤ) :
    annealedContrast P m = blockContrast (adaptedMean P (1 : Mat d) m) := by
  unfold annealedContrast adaptedMean
  rw [adaptedCell_one]

/-- The raw output is monotone in the source constant and the `B`-threshold
(`0 ≤ logb 3 (2K)` since `1 < K`, field `one_lt_growthWitness` of `CoarseEllipticityDagger`). -/
theorem RawOutput.mono {d : ℕ} {γ : ℝ} {S : SelectionData} {ε σ Cglob Cprof Csrc Csrc' : ℝ}
    {H : ℕ} {Bresp Bresp' : ℝ} {P : Measure (CoeffSpace d)} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {Src : CoeffSpace d → ℝ} {B : ℝ} {jStar : ℕ} {F : BlockMat d} {s t : ℤ}
    (hC : Csrc' ≤ Csrc) (hBr : Bresp' ≤ Bresp)
    (h : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ K Src B jStar F s t) :
    RawOutput d γ S ε σ Cglob Cprof Csrc' H Bresp' P E Ψ K Src B jStar F s t := by
  have hL : (0 : ℝ) ≤ Real.logb 3 (2 * K) :=
    Real.logb_nonneg (by norm_num) (by linarith only [h.ell.one_lt_growthWitness])
  refine { h with
    hB := le_trans ?_ h.hB
    hsrc := le_trans (Int.ceil_mono ?_) h.hsrc }
  · exact max_le_iff.mpr ⟨le_max_left _ _, le_trans hBr (le_max_right _ _)⟩
  · simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left (mul_le_mul_of_nonneg_right hC hL)
        (Cglob * (B + 1) * Real.logb 3 (2 + aspectRatio E))

/-- Scalar monotonicity of `blockScale` in the Loewner order on a positive block. -/
theorem blockScale_loewner_mono {d : ℕ} (A : BlockMat d) (hA : Book.Ch02.BlockPosDef A)
    {a b : ℝ} (hab : a ≤ b) :
    BlockMatLoewnerLE (blockScale a A) (blockScale b A) := by
  intro X
  have hquad_nonneg : 0 ≤ blockVecDot X (blockMatVecMul A X) := by
    by_cases hX : X = 0
    · subst X
      change 0 ≤ vecDot (0 : Vec d) (matVecMul A.upperLeft 0 + matVecMul A.upperRight 0) +
        vecDot (0 : Vec d) (matVecMul A.lowerLeft 0 + matVecMul A.lowerRight 0)
      rw [vecDot_zero_left, vecDot_zero_left]
      norm_num
    · exact (hA X hX).le
  have hcoef : 0 ≤ b - a := sub_nonneg.mpr hab
  have hAXa : blockMatVecMul (blockScale a A) X = a • blockMatVecMul A X := by
    ext i <;> simp [blockScale, blockMatVecMul, smul_matVecMul, smul_add]
  have hAXb : blockMatVecMul (blockScale b A) X = b • blockMatVecMul A X := by
    ext i <;> simp [blockScale, blockMatVecMul, smul_matVecMul, smul_add]
  rw [hAXa, hAXb, blockVecDot_smul_right, blockVecDot_smul_right]
  nlinarith only [mul_nonneg hcoef hquad_nonneg]

/-- Transitivity of the Loewner order (may already exist in the CoarseGraining package). -/
theorem loewner_trans {d : ℕ} {A B C : BlockMat d}
    (h₁ : BlockMatLoewnerLE A B) (h₂ : BlockMatLoewnerLE B C) : BlockMatLoewnerLE A C := by
  intro x
  exact le_trans (h₁ x) (h₂ x)

/-- `ℓ ≤ x` in `ℝ` gives `ℓ ≤ ⌈x⌉` in `ℤ` (`Int.le_ceil`, `Int.cast_le`). -/
theorem nat_le_ceil_of_le (ℓ : ℕ) (x : ℝ) (h : (ℓ : ℝ) ≤ x) : (ℓ : ℤ) ≤ ⌈x⌉ := by
  have h1 : (ℓ : ℝ) ≤ ↑⌈x⌉ := le_trans h (Int.le_ceil x)
  have h2 : (↑(ℓ : ℤ) : ℝ) ≤ ↑⌈x⌉ := by simp only [Int.cast_natCast]; exact h1
  exact Int.cast_le.mp h2

/-! ## EccentricityScaleDecay (gated external inputs) -/

/-- **R1** kernel `ext.adapted.response`: the adapted response estimate proper, exactly K1's third
conjunct.  It is the adapted response estimate the paper takes as given at
`e.response.adapted.conclusion`; its proof is not part of this development. -/
theorem adapted_response_core (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (_hS : S.Selects d γ) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 →
      ∀ δad : ℝ, δad ∈ Set.Ioc (0 : ℝ) 1 →
        ∃ H : ℕ, max 4 S.h ≤ H ∧
          ∀ Cprof : ℝ, 0 < Cprof →
            ∃ σ₀ : ℝ, σ₀ ∈ Set.Ioc (0 : ℝ) ε ∧
              ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) σ₀ →
                ∀ Cglob : ℝ, 0 < Cglob →
                  ∃ Bresp : ℝ, 1 ≤ Bresp ∧
                    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
                      (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ),
                      RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ K Src B jStar F s t →
                      canonicalImbalance
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar
                            (explicitCanonicalMetric F)) t) ≤
                          1 + δad := by
  exact adapted_response_core_of_holes d _hd γ _hγ S _hS

/-! The private copy of A12 `blockPosDef_of_toFullBlockMat_posDef` that stood here has been
removed: `HCPoly/Entry/Multiscale/Initial/ScalarBounds.lean` declares it publicly in this same
namespace, and it is now in this file's import graph (through
`HCPoly/Entry/Response/Core/ResponseBlockObjects.lean`), so the private copy was a duplicate
declaration.  K1's proof below is unchanged and now uses the public A12, exactly the
declaration the removed docstring named. -/

/-- **K1** `ext.adapted.response` + Step 3 (`e.response.adapted.conclusion`): the selected
adapted block at `t` is symmetric, positive, and has canonical imbalance `≤ 1 + δad`; `H`,
`σ₀`, `Bresp` are the paper's, chosen in the order the paper states them.  It is an assumed
input: its proof needs the source estimate on adapted subcubes,
`ext.annealed.primal.adjoint`, `ext.reference.block.comparison` and `a.stationarity`, none of
which this development has. -/
theorem adapted_response_kernel (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (_hS : S.Selects d γ) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 →
      ∀ δad : ℝ, δad ∈ Set.Ioc (0 : ℝ) 1 →
        ∃ H : ℕ, max 4 S.h ≤ H ∧
          ∀ Cprof : ℝ, 0 < Cprof →
            ∃ σ₀ : ℝ, σ₀ ∈ Set.Ioc (0 : ℝ) ε ∧
              ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) σ₀ →
                ∀ Cglob : ℝ, 0 < Cglob →
                  ∃ Bresp : ℝ, 1 ≤ Bresp ∧
                    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
                      (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ),
                      RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ K Src B jStar F s t →
                      IsSymmetricBlockMat
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar
                            (explicitCanonicalMetric F)) t) ∧
                        Book.Ch02.BlockPosDef
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar
                            (explicitCanonicalMetric F)) t) ∧
                        canonicalImbalance
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar
                            (explicitCanonicalMetric F)) t) ≤
                          1 + δad := by
  obtain ⟨Csrc, hC, h⟩ := adapted_response_core d _hd γ _hγ S _hS
  refine ⟨Csrc, hC, ?_⟩
  intro ε hε δad hδ
  obtain ⟨H, hH, h⟩ := h ε hε δad hδ
  refine ⟨H, hH, ?_⟩
  intro Cprof hCprof
  obtain ⟨σ₀, hσ₀, h⟩ := h Cprof hCprof
  refine ⟨σ₀, hσ₀, ?_⟩
  intro σ hσ Cglob hCglob
  obtain ⟨Bresp, hBresp, h⟩ := h σ hσ Cglob hCglob
  refine ⟨Bresp, hBresp, ?_⟩
  intro P E Ψ K Src B jStar F s t raw
  have := raw.prob
  let : NeZero d := ⟨by omega⟩
  have hcm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef
    raw.symm raw.pos
  have hfull := HCPolySupport.HighContrast.Annealed.adaptedMean_posDef d _hd P γ E Ψ K Src raw.stat
    raw.ell jStar raw.hj (explicitCanonicalMetric F) hcm t
  exact ⟨isSymmetricBlockMat_annealedBlock _ _,
    blockPosDef_of_toFullBlockMat_posDef _ hfull,
    h P E Ψ K Src B jStar F s t raw⟩

/-- **K2** `ext.persistence.transfer` + HC Lemma 2.15 + `e.global.selection.eccentricity`
(`p.response.transfer`): a Euclidean generation `t + ℓ` with
`1 ≤ ℓ ≤ Cresp log₃(2+Π)` whose block is sandwiched by `((1+δad)^{-d} - ηm) 𝐀hom_{t,q}` and
`(1+ηp) 𝐀hom_{t,q}`.  It is an assumed input: the paper's proof of it uses HC Lemma 2.15,
whose own coarsening premise this development does not supply, and this statement carries no
such premise. -/
theorem persistence_transfer_kernel (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (_hS : S.Selects d γ) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 →
      ∀ δad : ℝ, δad ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ ηp : ℝ, ηp ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ ηm : ℝ, ηm ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ H : ℕ, max 4 S.h ≤ H →
      ∀ Cprof : ℝ, 0 < Cprof →
      ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) ε →
      ∀ Cglob : ℝ, 0 < Cglob →
        ∃ Bresp : ℝ, 1 ≤ Bresp ∧
          ∃ Cresp : ℝ, 0 < Cresp ∧
            ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
              (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ),
              RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ K Src B jStar F s t →
              canonicalImbalance
                  (adaptedMean P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
                    F)) t) ≤ 1 + δad →
              ∃ ℓ : ℕ, 1 ≤ ℓ ∧
                (ℓ : ℝ) ≤ Cresp * Real.logb 3 (2 + aspectRatio E) ∧
                IsSymmetricBlockMat (adaptedMean P (1 : Mat d) (t + ℓ)) ∧
                BlockMatLoewnerLE
                  (blockScale ((1 + δad) ^ (-(d : ℝ)) - ηm)
                    (adaptedMean P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
                      F)) t))
                  (adaptedMean P (1 : Mat d) (t + ℓ)) ∧
                BlockMatLoewnerLE (adaptedMean P (1 : Mat d) (t + ℓ))
                  (blockScale (1 + ηp)
                    (adaptedMean P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
                      F)) t)) := by
  obtain ⟨C1s, C1, hC1s, hC1, hE1⟩ := euclidean_le_adapted_comparison d _hd γ _hγ
  obtain ⟨C2s, C2, hC2s, hC2, hE2⟩ := adapted_le_euclidean_comparison d _hd γ _hγ
  refine ⟨max C1s C2s, lt_of_lt_of_le hC1s (le_max_left _ _), ?_⟩
  intro ε _hε δad hδad ηp hηp ηm hηm H _hH Cprof _hCprof σ _hσ Cglob hCglob
  have hCmax : (0 : ℝ) < max C1 C2 := lt_of_lt_of_le hC1 (le_max_left _ _)
  obtain ⟨Cr1, hCr1, hgap1⟩ := exists_gap_of_eccentricity (max C1 C2) Cglob ηp hCmax hCglob hηp
  obtain ⟨Cr2, _hCr2, hgap2⟩ := exists_gap_of_eccentricity (max C1 C2) Cglob ηm hCmax hCglob hηm
  refine ⟨1, le_rfl, Cr1, hCr1, ?_⟩
  intro P E Ψ K Src B jStar F s t raw himb
  have := raw.prob
  let : NeZero d := ⟨by omega⟩
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef
    raw.symm raw.pos
  have hB1 : (1 : ℝ) ≤ B := le_trans (le_max_right _ _) raw.hB
  have hPi : (1 : ℝ) ≤ aspectRatio E :=
    HCPolySupport.HighContrast.one_le_aspectRatio_of_coarseEllipticityDagger raw.ell
  have hlogPi : (0 : ℝ) ≤ Real.logb 3 (2 + aspectRatio E) :=
    Real.logb_nonneg (by norm_num) (by linarith only [hPi])
  have hlogK : (0 : ℝ) ≤ Real.logb 3 (2 * K) :=
    Real.logb_nonneg (by norm_num) (by linarith only [raw.ell.one_lt_growthWitness])
  have hglob0 : (0 : ℝ) ≤ Cglob * (B + 1) * Real.logb 3 (2 + aspectRatio E) :=
    mul_nonneg (by nlinarith only [hCglob, hB1]) hlogPi
  have hsrc1 : ⌈C1s * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) := by
    refine le_trans (Int.ceil_mono ?_) raw.hsrc
    have h1 : C1s * Real.logb 3 (2 * K) ≤ max C1s C2s * Real.logb 3 (2 * K) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hlogK
    linarith only [h1, hglob0]
  have hsrc2 : ⌈C2s * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) := by
    refine le_trans (Int.ceil_mono ?_) raw.hsrc
    have h1 : C2s * Real.logb 3 (2 * K) ≤ max C1s C2s * Real.logb 3 (2 * K) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hlogK
    linarith only [h1, hglob0]
  have hceil : (0 : ℤ) ≤ ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ :=
    Int.ceil_nonneg (mul_nonneg (by linarith only [hB1]) hlogPi)
  have ht0 : (jStar : ℤ) ≤ t := by
    have h1 := raw.hs_lo
    have h2 := raw.hst
    omega
  have hnn : (0 : ℝ) ≤ ‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖ := by
    positivity
  have hecc : (1 : ℝ) ≤ ‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖ := by
    have hs := HCPolySupport.HighContrast.Source.one_le_source_eccentricity hm
    nlinarith only [hs, hnn, Real.sq_sqrt hnn, Real.sqrt_nonneg (‖explicitCanonicalMetric F‖ *
      ‖(explicitCanonicalMetric F)⁻¹‖)]
  have hmono : ∀ c : ℝ, c ≤ max C1 C2 → ∀ x : ℝ, 0 ≤ x →
      c * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) * x ≤
        max C1 C2 * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric
          F)⁻¹‖) * x := by
    intro c hc x hx
    have hprod : (0 : ℝ) ≤ aspectRatio E * (‖explicitCanonicalMetric F‖ *
      ‖(explicitCanonicalMetric F)⁻¹‖) * x :=
      mul_nonneg (mul_nonneg (by linarith only [hPi]) hnn) hx
    nlinarith only [mul_nonneg (sub_nonneg.mpr hc) hprod]
  obtain ⟨ℓ, hl1, hlEta, hlLe⟩ :=
    hgap1 (aspectRatio E) (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) hPi
      hecc raw.ecc
  obtain ⟨r, hr1, hrEta, -⟩ :=
    hgap2 (aspectRatio E) (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) hPi
      hecc raw.ecc
  have hApos : Book.Ch02.BlockPosDef
      (adaptedMean P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t) :=
    blockPosDef_of_toFullBlockMat_posDef _
      (HCPolySupport.HighContrast.Annealed.adaptedMean_posDef d _hd P γ E Ψ K Src raw.stat
        raw.ell jStar
        raw.hj (explicitCanonicalMetric F) hm t)
  refine ⟨ℓ, hl1, hlLe, isSymmetricBlockMat_annealedBlock _ _, ?_, ?_⟩
  · have hE2' := hE2 P E Ψ K Src raw.stat raw.unit raw.ell jStar raw.hj hsrc2
      (explicitCanonicalMetric F) hm t ht0 raw.cube ℓ r hl1 hr1
    have hP3 := adaptedMean_persistence d _hd P γ E Ψ K Src raw.stat raw.ell jStar raw.hj
      (explicitCanonicalMetric F) hm t (t + (ℓ : ℤ) + (r : ℤ)) ht0 (by omega) hδad.1.le himb
    have hA4 := loewner_scale_sub_of_le _ _ _ hE2' hP3
    refine loewner_trans (blockScale_loewner_mono _ hApos ?_) hA4
    have h1 := hmono C2 (le_max_right _ _) ((3 : ℝ) ^ (-(r : ℝ))) (by positivity)
    linarith only [h1, hrEta]
  · have hE1' := hE1 P E Ψ K Src raw.stat raw.unit raw.ell jStar raw.hj hsrc1
      (explicitCanonicalMetric F) hm t ht0 raw.cube ℓ hl1
    refine loewner_trans hE1' (blockScale_loewner_mono _ hApos ?_)
    have h1 := hmono C1 (le_max_left _ _) ((3 : ℝ) ^ (-(ℓ : ℝ))) (by positivity)
    linarith only [h1, hlEta]

/-- **K3** the canonical comparison (`p.response.transfer`): a Loewner sandwich
`(1-η) A ≤ M ≤ (1+η) A` transfers the canonical imbalance with factor `(1+η)^3/(1-η)`.
Deterministic. -/
theorem canonical_comparison_kernel {d : ℕ} (_hd : 2 ≤ d) (A M : BlockMat d)
    (_hAs : IsSymmetricBlockMat A) (hA : Book.Ch02.BlockPosDef A) (_hMs : IsSymmetricBlockMat M)
    {ηiso δad : ℝ} (hη : ηiso ∈ Set.Ioo (0 : ℝ) 1) (hδ : δad ∈ Set.Ioc (0 : ℝ) 1)
    (hlo : BlockMatLoewnerLE (blockScale (1 - ηiso) A) M)
    (hhi : BlockMatLoewnerLE M (blockScale (1 + ηiso) A))
    (himb : canonicalImbalance A ≤ 1 + δad) :
    canonicalImbalance M ≤ (1 + ηiso) ^ 3 / (1 - ηiso) * (1 + δad) := by
  obtain ⟨hη0, hη1⟩ := hη
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hApos : (toFullBlockMat A).PosDef := posDef_toFullBlockMat _hAs hA
  have hMh : (toFullBlockMat M).IsHermitian :=
    (Analysis.toFullBlockMat_isHermitian_iff M).2 _hMs
  have hsA : ∀ c : ℝ, (toFullBlockMat (blockScale c A)).IsHermitian := fun c =>
    (Analysis.toFullBlockMat_isHermitian_iff _).2 (isSymmetricBlockMat_blockScale c _hAs)
  have hloF : (1 - ηiso) • toFullBlockMat A ≤ toFullBlockMat M := by
    have h := Analysis.matrixOrder_of_blockMatLoewnerLE (hsA (1 - ηiso)) hMh hlo
    rwa [toFullBlockMat_blockScale] at h
  have hhiF : toFullBlockMat M ≤ (1 + ηiso) • toFullBlockMat A := by
    have h := Analysis.matrixOrder_of_blockMatLoewnerLE hMh (hsA (1 + ηiso)) hhi
    rwa [toFullBlockMat_blockScale] at h
  have hMpos : (toFullBlockMat M).PosDef :=
    posDef_of_le (posDef_smul (by linarith only [hη1]) hApos) hMh hloF
  have hAu : IsUnit (toFullBlockMat A).det := (Matrix.isUnit_iff_isUnit_det _).1 hApos.isUnit
  have h1 := le_of_imbalance_le hApos himb
  have h4a : (1 + ηiso)⁻¹ • (toFullBlockMat A)⁻¹ ≤ (toFullBlockMat M)⁻¹ := by
    have h := inv_le_inv_of_le hMpos (posDef_smul (by linarith only [hη0]) hApos) hhiF
    rwa [inv_smul_of_isUnit (by linarith only [hη0] : (1 : ℝ) + ηiso ≠ 0) hAu] at h
  have h4 : (toFullBlockMat A)⁻¹ ≤ (1 + ηiso) • (toFullBlockMat M)⁻¹ := by
    have h := smul_le_smul_left (c := 1 + ηiso) (by linarith only [hη0]) h4a
    rwa [smul_smul, mul_inv_cancel₀ (by linarith only [hη0] : (1 : ℝ) + ηiso ≠ 0), one_smul] at h
  have hRt : (toFullBlockMat (blockSwap d))ᵀ = toFullBlockMat (blockSwap d) := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (swap_hermitian d).eq
  have h5 : toFullBlockMat (blockSwap d) * (toFullBlockMat A)⁻¹ * toFullBlockMat (blockSwap d)
      ≤ (1 + ηiso) • (toFullBlockMat (blockSwap d) * (toFullBlockMat M)⁻¹ *
        toFullBlockMat (blockSwap d)) := by
    have h := Analysis.matrix_congr_le h4 (toFullBlockMat (blockSwap d))
    rwa [hRt, Matrix.mul_smul, Matrix.smul_mul] at h
  have hb : (1 + ηiso) • toFullBlockMat A ≤
      ((1 + ηiso) * (1 + δad)) • (toFullBlockMat (blockSwap d) * (toFullBlockMat A)⁻¹ *
        toFullBlockMat (blockSwap d)) := by
    have h := smul_le_smul_left (c := 1 + ηiso) (by linarith only [hη0]) h1
    rwa [smul_smul] at h
  have hcc : ((1 + ηiso) * (1 + δad)) • (toFullBlockMat (blockSwap d) * (toFullBlockMat A)⁻¹ *
        toFullBlockMat (blockSwap d)) ≤
      ((1 + ηiso) * (1 + δad) * (1 + ηiso)) • (toFullBlockMat (blockSwap d) *
        (toFullBlockMat M)⁻¹ * toFullBlockMat (blockSwap d)) := by
    have h := smul_le_smul_left (c := (1 + ηiso) * (1 + δad)) (by nlinarith only [hη0, hδ0]) h5
    rwa [smul_smul] at h
  have harith : (1 + ηiso) * (1 + δad) * (1 + ηiso) ≤
      (1 + ηiso) ^ 3 / (1 - ηiso) * (1 + δad) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith only [hη1] : (0 : ℝ) < 1 - ηiso)]
    nlinarith only [mul_nonneg (mul_nonneg (sq_nonneg (1 + ηiso))
      (by linarith only [hδ0] : (0 : ℝ) ≤ 1 + δad)) (by linarith only [hη0] : (0 : ℝ) ≤ 2 * ηiso)]
  have hd := smul_le_smul_psd (swapConj_posSemidef hMpos) harith
  have hcnn : (0 : ℝ) ≤ (1 + ηiso) ^ 3 / (1 - ηiso) * (1 + δad) :=
    mul_nonneg (div_nonneg (pow_nonneg (by linarith only [hη0]) 3) (by linarith only [hη1])) (by
      linarith only [hδ0])
  exact imbalance_le_of_le hMpos hcnn (hhiF.trans (hb.trans (hcc.trans hd)))

/-- **K4** the Euclidean contrast bridge (near `e.response.canonical.imbalance`): contrast minus
one is at most three times imbalance minus one; the factor three is the one the tolerances of
Step 1 give.  Deterministic. -/
theorem euclidean_contrast_bridge_kernel {d : ℕ} (_hd : 2 ≤ d) (A : BlockMat d)
    (_hAs : IsSymmetricBlockMat A) (_hA : Book.Ch02.BlockPosDef A) {x : ℝ} (_hx : 0 ≤ x)
    (h : canonicalImbalance A ≤ 1 + x) :
    blockContrast A - 1 ≤ 3 * x := by
  exact blockContrast_sub_one_le_of_canonicalImbalance_le _hAs _hA _hx h


/-- Scalar dilation acts on the entire doubled quadratic form. -/
theorem blockVecDot_blockMatVecMul_blockScale {d : ℕ} (c : ℝ) (A : BlockMat d)
    (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockScale c A) X) =
      c * blockVecDot X (blockMatVecMul A X) := by
  simp only [blockScale, blockMatVecMul, smul_matVecMul, ← smul_add, blockVecDot,
    vecDot_smul_right]
  ring

/-- A positive scalar dilation of a positive block that sits below `M` makes `M` positive. -/
theorem blockPosDef_of_blockScale_le {d : ℕ} {A M : BlockMat d} {c : ℝ} (hc : 0 < c)
    (hA : Book.Ch02.BlockPosDef A) (h : BlockMatLoewnerLE (blockScale c A) M) :
    Book.Ch02.BlockPosDef M := by
  intro X hX
  have h1 := h X
  rw [blockVecDot_blockMatVecMul_blockScale] at h1
  linarith only [h1, mul_pos hc (hA X hX)]


end HCPolySupport.HighContrast.Multiscale
