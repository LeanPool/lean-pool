/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.OptimizerMeanIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.RecenteredResponseIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseBlockObjects
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseCalibrationBundles
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.OptimizerEnergyIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.WeakEstimateAssembly
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CutoffPairingRowSplit
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.StationaryAnnealedErrorScalars
public import LeanPool.HighContrastHomogenization.Entry.Setup.ProjectiveDistance

/-!
# High-contrast homogenization: Entry.Response.Rows.RecentredResponseEnergyBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The centred response as a sheared block energy, and its three-row bound

The response energy of a block under a shear congruence equals the response energy of the original
block at the correspondingly transformed load; specializing this to the recentring shear
`G_g = ((1,0),(g,1))` expresses the two centred responses `Jtilde^-(e)` and `Jtilde^+(e)` of
`e.response.cutoff.estimate`, and their adjoint recentred blocks `Ehat_t^∓`, in swapped and closed
forms, and the adjoint annealed energies of the cutoff rows follow in the same closed block form.
Chaining these identifications expresses each centred response as the annealed energy of the
recentred block at the shifted load minus half the pairing of the two coordinates of the annealed
mean `Y^∓`. The cutoff decomposition of the cutoff pairing exhibits that half-pairing itself as the
cutoff half-energy minus the two cutoff-mean pairings plus half the self-pairing of `Y^∓`, with the
cutoff pairing row bounded by the expected absolute pairing (AK.HC (3.45)-(3.54)); combining the two
identifications gives the three-row bound on `|Jtilde^∓(e)|`, for both signs.
-/

section
/-!
## The adjoint annealed energies of the cutoff rows in closed block form

The adjoint cutoff rows of the response estimate bound the centred response with the two error
scalars `respEJPlus` and `respTauPlus`.  The first is the `P`-expectation of the adjoint recentred
pathwise response at one adapted cell; the second is the defect of that expectation between two
scales.  Under the entrywise integrability of the coarse block carried by the cutoff rows, both are
algebraic functions of the adjoint recentred annealed block `respEhatPlus`: the pathwise response
of `a₊ = aᵗ + g` is the block energy `x · A x / 2 - p · q'`, so its expectation is the same block
energy of the annealed block `E[A]`, and the pairing `p · q'` cancels in the defect.  These are the
closed block forms against which the adjoint cutoff rows are stated (`e.response.cutoff.estimate`).
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The `P`-expectation of the adjoint recentred pathwise response on an adapted cell `U_u` is the
block quadratic `½ x · E[A] x` of the adjoint recentred annealed block `respEhatPlus`, at the load
`x = (-p, q')`, minus the pairing `p · q'`.  This is the integral identity
`integral_respJ_eq_blockResponseEnergy` specialised to the adjoint recentred coefficient
`a₊ = aᵗ + g`, with its three inputs supplied by the coarse-block congruence, the entrywise
transport of integrability across that congruence, and the annealed-block identification
(`e.response.cutoff.estimate`, `e.annealed.schur`). -/
private theorem respIntegral_respCoeffPlus_eq_blockResponseEnergy {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
    (u : ℤ) (p q' : Vec d) (hq : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F u)) :
    (∫ a, respJ (respGrid jStar F) u p q' (respCoeffPlus F a) ∂P)
      = (1 / 2 : ℝ) * blockVecDot (-p, q')
          (blockMatVecMul (respEhatPlus P jStar F u) (-p, q'))
        - vecDot p q' := by
  have hintA : HasIntegrableCoarseBlock P (HighContrast.adaptedCell (respGrid jStar F) u) := hint
  have hpath : ∀ a : CoeffSpace d,
      respJ (respGrid jStar F) u p q' (respCoeffPlus F a)
        = (1 / 2 : ℝ) * blockVecDot (-p, q')
            (blockMatVecMul
              (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) u) (respCoeffPlus
                F a))
              (-p, q'))
          - vecDot p q' :=
    fun a => respJ_respCoeffPlus_eq (respGrid jStar F) hq u F a p q'
  have hint' : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) u) (respCoeffPlus F a))
      α β) P :=
    integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr
      (G := ofFullBlockMat (toFullBlockMat (respG F) * toFullBlockMat (blockD d)))
      (V := HighContrast.adaptedCell (respGrid jStar F) u) (b := respCoeffPlus F) hintA
      (fun a => coarseBlockMatrix_respCoeffPlus_eq_blockCongr (respGrid jStar F) hq u F a)
  have hann : annealedBlockOf P (HighContrast.adaptedCell (respGrid jStar F) u) (respCoeffPlus F)
      = respEhatPlus P jStar F u :=
    annealedBlockOf_respCoeffPlus_eq P jStar F u
      (fun a => hasQuadraticMu_adaptedCell (respGrid jStar F) hq u a) hint
  exact integral_respJ_eq_blockResponseEnergy P (respGrid jStar F) u p q'
    (respCoeffPlus F) (respEhatPlus P jStar F u) hpath hint' hann

/-- **The adjoint annealed energy of the cutoff rows as a block quadratic.**  Under entrywise
integrability of the coarse block, the `P`-expectation of the adjoint recentred pathwise response
`J(U_t, p, q⁺; a₊)` is the quadratic form `½ x · E[A] x` of the adjoint recentred annealed block
`respEhatPlus` at the load `x = (-p, q⁺)`, minus the pairing `p · q⁺`.  This is the closed block
form of the centred adjoint response energy `e.response.cutoff.estimate`. -/
theorem respEJPlus_eq_blockResponseEnergy {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (hq : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) :
    respEJPlus P jStar F t e
      = (1 / 2 : ℝ) * blockVecDot
          (-(respP (respMean P jStar F t) e), respqPlus P jStar F t e)
          (blockMatVecMul (respEhatPlus P jStar F t)
            (-(respP (respMean P jStar F t) e), respqPlus P jStar F t e))
        - vecDot (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) := by
  unfold respEJPlus
  exact respIntegral_respCoeffPlus_eq_blockResponseEnergy P jStar F t
    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) hq hint

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The shear form of the annealed energies of the cutoff rows

The cutoff rows of the response estimate bound the centred response `Jtilde^±(e)` by expressions
in the expectation of the recentred pathwise response, its scale defect, and the source load
(`e.response.cutoff.estimate`, AK.HC (3.45)–(3.54)).  The centred response itself is defined on the
annealed block `E_t` of the original coefficient, while the two energy scalars are the block
energies of the recentred blocks `Ehat_t^∓`.  The two objects are compared only after the algebraic
step recorded here.

The recentring `a_∓ = a ∓ g` is the constant shear `G^t A G` of the doubled block, and the shear
moves the flux load: the block response energy of the shear congruence at a load `(p, r)` is the
response energy of the original block at the load `(p, r - g p)`.  Since `g` is skew, the pairing
`p. g p` vanishes, so the constant `p. q'` of the energy is unchanged and the identity is exact.
This is the algebraic half of the recentring of Step 4 of the response argument, and the first step
that puts the recentred block energies on the same footing as the centred response.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- An auxiliary identity: the quadratic form of a skew matrix vanishes, `ξ. (g ξ) = 0` whenever
`gᵀ = -g`.  This is what makes the shear shift load-independent. -/
private theorem vecDot_matVecMul_skew_self {d : ℕ} {g : Mat d}
    (hg : matTranspose g = -g) (ξ : Vec d) : vecDot ξ (matVecMul g ξ) = 0 := by
  have h1 := _root_.HCPolySupport.vecDot_matVecMul_transpose ξ ξ g
  rw [hg] at h1
  have hneg : matVecMul (-g) ξ = -matVecMul g ξ := neg_matVecMul g ξ
  rw [hneg, vecDot_neg_right, vecDot_comm (matVecMul g ξ) ξ] at h1
  linarith only [h1]

/-- **The shear congruence shifts the flux load in the block response energy.**  For the constant
shear `G = ((1, 0), (g, 1))` with `g` skew and any doubled block `A`, the response energy of the
shear congruence at the load `(p, r)` is the response energy of `A` at the load
`(p, r - g p)`:
`blockResponseEnergy (Gᵀ A G) p r = blockResponseEnergy A p (r - matVecMul g p)`.
The constant `p. r` of the energy is unchanged because `p. (g p) = 0`.  This is the algebraic
content of the recentring of the coefficient in Step 4 of the response argument
(`e.response.cutoff.estimate`). -/
theorem blockResponseEnergy_blockCongr_shear {d : ℕ} (A : BlockMat d) {g : Mat d}
    (hg : matTranspose g = -g) (p r : Vec d) :
    blockResponseEnergy (blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A) p r
      = blockResponseEnergy A p (r - matVecMul g p) := by
  have hpg : vecDot p (matVecMul g p) = 0 := vecDot_matVecMul_skew_self hg p
  have hGx : blockMatVecMul (⟨1, 0, g, 1⟩ : BlockMat d) (-p, r)
      = (-p, r - matVecMul g p) := by
    refine Prod.ext ?_ ?_
    · funext i
      rw [blockMatVecMul_fst]
      change ((1 : Mat d).mulVec (-p) + (0 : Mat d).mulVec r) i = (-p) i
      rw [Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
    · funext i
      rw [blockMatVecMul_snd]
      change (matVecMul g (-p) + (1 : Mat d).mulVec r) i = (r - matVecMul g p) i
      rw [matVecMul_neg, Matrix.one_mulVec]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
      ring
  unfold blockResponseEnergy
  rw [blockVecDot_blockCongr, hGx]
  rw [show vecDot p r = vecDot p (r - matVecMul g p) by
    rw [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right, hpg, neg_zero, add_zero]]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The centred response under the recentring shear

The recentring of the coefficient by a constant skew matrix `g` is the shear congruence `Gᵀ A G`
of the doubled block with `G = ((1, 0), (g, 1))`.  The block response energy of the shear
congruence at the load `(p, r)` is the response energy of the original block at the load
`(p, r - g p)`, and the constant `p. r` of that energy is unchanged because `p. (g p) = 0`.

This file records the corresponding statements for the doubled block-vector multiplication and for
the two terms of the centred response: the block mean of the shear congruence is the block mean of
the original block at the shifted load, with its two slots related by `Y₂ ↦ Y₂ - g Y₁`, so the
centring pairing is shear-invariant because `Y₁. (g Y₁) = 0`.  The centred response therefore
transforms exactly as the block response energy does, which puts the centred responses on the
recentred blocks of `e.response.cutoff.estimate`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The shear congruence `Gᵀ A G` with `G = ((1, 0), (g, 1))` acts on a doubled vector by the
triangular change of variables `(X₁, X₂) ↦ (X₁, g X₁ + X₂)` in the second slot, and then adds the
first slot `gᵀ` times the second slot of the image: the first component of the image is
`(A (X₁, g X₁ + X₂))₁ + gᵀ (A (X₁, g X₁ + X₂))₂` and the second component is
`(A (X₁, g X₁ + X₂))₂`. -/
theorem blockMatVecMul_blockCongr_shear {d : ℕ} (A : BlockMat d) (g : Mat d) (X : BlockVec d) :
    blockMatVecMul (blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A) X
      = ((blockMatVecMul A (X.1, matVecMul g X.1 + X.2)).1
            + matVecMul (matTranspose g) (blockMatVecMul A (X.1, matVecMul g X.1 + X.2)).2,
         (blockMatVecMul A (X.1, matVecMul g X.1 + X.2)).2) := by
  rcases X with ⟨x1, x2⟩
  rw [blockCongr_shear]
  refine Prod.ext ?_ ?_
  · simp only [blockMatVecMul_fst, blockMatVecMul_snd, add_matVecMul, matVecMul_add,
      ← matVecMul_mul]
    abel
  · simp only [blockMatVecMul_snd, add_matVecMul, matVecMul_add, ← matVecMul_mul]
    abel

/-- The centring pairing of the block mean is invariant under the shear congruence
`G = ((1, 0), (g, 1))` with `g` skew.  Writing `Z = A (-p, r - g p)`, the mean of the shear
congruence at the load `(-p, r)` has slots `(-p + Z₂, r + Z₁ + gᵀ Z₂)` while the mean of `A` at the
shifted load `(-p, r - g p)` has slots `(-p + Z₂, r - g p + Z₁)`, and the second slots differ by
`-g (-p + Z₂)`, whose pairing against `-p + Z₂` vanishes because `g` is skew.  This is the
centring half of the recentring of Step 4 of the response argument
(`e.response.cutoff.estimate`). -/
theorem vecDot_blockResponseMean_blockCongr_shear {d : ℕ} (A : BlockMat d) {g : Mat d}
    (hg : matTranspose g = -g) (p r : Vec d) :
    vecDot (blockResponseMean (blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A) (-p, r)).1
        (blockResponseMean (blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A) (-p, r)).2
      = vecDot (blockResponseMean A (-p, r - matVecMul g p)).1
          (blockResponseMean A (-p, r - matVecMul g p)).2 := by
  set Z : BlockVec d := blockMatVecMul A (-p, r - matVecMul g p) with hZ
  have harg : (matVecMul g (-p) + r : Vec d) = r - matVecMul g p := by
    rw [matVecMul_neg]
    abel
  have hW : blockMatVecMul (blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A) (-p, r)
      = (Z.1 + matVecMul (matTranspose g) Z.2, Z.2) := by
    rw [blockMatVecMul_blockCongr_shear]
    simp only [harg, ← hZ]
  have hmeanL : blockResponseMean (blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A) (-p, r)
      = (-p + Z.2, r + Z.1 + matVecMul (matTranspose g) Z.2) := by
    unfold blockResponseMean
    rw [hW]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, blockMatVecMul_blockSwap_fst]
    · simp only [Prod.snd_add, blockMatVecMul_blockSwap_snd, add_assoc]
  have hmeanR : blockResponseMean A (-p, r - matVecMul g p)
      = (-p + Z.2, r - matVecMul g p + Z.1) := by
    unfold blockResponseMean
    rw [← hZ]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, blockMatVecMul_blockSwap_fst]
    · simp only [Prod.snd_add, blockMatVecMul_blockSwap_snd]
  have hskew : ∀ v : Vec d, vecDot v (matVecMul g v) = 0 := by
    intro v
    have h1 : vecDot v (matVecMul (matTranspose g) v) = vecDot (matVecMul g v) v :=
      _root_.HCPolySupport.vecDot_matVecMul_transpose v v g
    rw [hg, neg_matVecMul, vecDot_neg_right, vecDot_comm (matVecMul g v) v] at h1
    linarith only [h1]
  have hM2 : (r + Z.1 + matVecMul (matTranspose g) Z.2 : Vec d)
      = (r - matVecMul g p + Z.1) - matVecMul g ((-p) + Z.2) := by
    rw [hg, neg_matVecMul, matVecMul_add, matVecMul_neg]
    abel
  rw [hmeanL, hmeanR]
  dsimp only
  simp only [hM2, sub_eq_add_neg, vecDot_add_right, vecDot_neg_right, hskew, neg_zero, add_zero]

/-- The centred response is invariant under the shear recentring:
`blockCenteredResponse (Gᵀ A G) p r = blockCenteredResponse A p (r - g p)` for the constant shear
`G = ((1, 0), (g, 1))` with `g` skew.  The energy term transforms by
`blockResponseEnergy_blockCongr_shear` and the centring pairing by shear invariance, so the centred
responses on the recentred blocks and on the original blocks are the same scalar.  This is the
passage from the centred responses to the annealed energies of
`e.response.cutoff.estimate`. -/
theorem blockCenteredResponse_blockCongr_shear {d : ℕ} (A : BlockMat d) {g : Mat d}
    (hg : matTranspose g = -g) (p r : Vec d) :
    blockCenteredResponse (blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A) p r
      = blockCenteredResponse A p (r - matVecMul g p) := by
  unfold blockCenteredResponse
  rw [blockResponseEnergy_blockCongr_shear A hg p r,
    vecDot_blockResponseMean_blockCongr_shear A hg p r]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The centred responses on the recentred blocks, in swap form

The two centred responses `Jtilde^-` and `Jtilde^+` of `e.response.cutoff.estimate` are defined
on the annealed block `E_t = respMean` at the skew-shifted loads.  The recentring shear
`G_g = ((1, 0), (g, 1))` of Step 4 carries that block to `Ehat_t^- = G_gᵀ E_t G_g`, and the
adjoint recentring carries the adjoint block to `Ehat_t^+ = G_{-g}ᵀ (D E_t D) G_{-g}`.  Under the
shear, the centred response is unchanged once the second load is shifted back by `g p`, so each
`Jtilde^±` is the centred response of the *recentred* block `Ehat_t^±` at the recentred load
`q^±`.  Because the reciprocal normalizations give `p. q^± = |e|^2 = 1`, the swap form of the
centred response then collapses each `Jtilde^±` to the closed expression
`-1/2 - (1/4) <Ehat_t^± x^±, R Ehat_t^± x^±>`.  Thus the centred response measures exactly the
failure of the recentred block to be reciprocal along its own load, and it vanishes precisely
when `(1/4) <Ehat x, R Ehat x> = -1/2`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The centred response `Jtilde^-(e)` of `e.response.cutoff.estimate` is the centred response
of the recentred block `Ehat_t^-` at the recentred load `q^-`: the shear congruence
`Ehat_t^- = G_gᵀ E_t G_g` acts on the doubled load by the triangular change of variables
`(X₁, X₂) ↦ (X₁, g X₁ + X₂)`, and since the centred response is shear-invariant the definition
of `respCenteredJMinus` on `E_t` at `(p, q - h_t p)` agrees with the response of `Ehat_t^-` at
`(p, q^-)` with `q^- = q + (g - h_t) p`. -/
theorem respCenteredJMinus_eq_blockCenteredResponse_respEhatMinus {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d) :
    respCenteredJMinus P jStar F t e
      = blockCenteredResponse (respEhatMinus P jStar F t) (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) := by
  rw [respCenteredJMinus, respEhatMinus, respG]
  rw [blockCenteredResponse_blockCongr_shear (respMean P jStar F t) (respg_isSkew F)
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)]
  congr 1
  rw [respqMinus, sub_matVecMul]
  abel

/-- The adjoint centred response `Jtilde^+(e)` of `e.response.cutoff.estimate` is the centred
response of the recentred adjoint block `Ehat_t^+` at the recentred load `q^+`.  The adjoint
recentred block is the `(-g)`-shear congruence `Ehat_t^+ = G_{-g}ᵀ (D E_t D) G_{-g}`, and the
centred response of that congruence at `(p, q^+)` is the response of the adjoint block at
`(p, q^+ + g p)`, which is the definition of `respCenteredJPlus` on the adjoint annealed block
at `(p, q + h_t p)`. -/
theorem respCenteredJPlus_eq_blockCenteredResponse_respEhatPlus {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d) :
    respCenteredJPlus P jStar F t e
      = blockCenteredResponse (respEhatPlus P jStar F t) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) := by
  rw [respCenteredJPlus, respEhatPlus_eq_blockCongr_shear]
  have hgneg : matTranspose (-(respg F)) = -(-(respg F)) := by
    have hT : matTranspose (-(respg F)) = -matTranspose (respg F) := by
      simp only [matTranspose, Matrix.transpose_neg]
    rw [hT, respg_isSkew F]
  rw [blockCenteredResponse_blockCongr_shear (blockAdjoint (respMean P jStar F t)) hgneg
    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)]
  congr 1
  rw [respqPlus, sub_matVecMul, neg_matVecMul]
  abel

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The centred response as the annealed energy minus half the mean pairing

The centred responses `Jtilde^-(e)` and `Jtilde^+(e)` of `e.response.cutoff.estimate` are
defined on the annealed block `E_t = respMean` at the skew-shifted loads.  The recentring shear
`G = respG F` carries that block to the recentred block `Ehat_t^- = respEhatMinus`, and the
adjoint recentring carries the adjoint block to `Ehat_t^+ = respEhatPlus`.  Under that
identification the energy part of the centred response is the `P`-expectation of the recentred
pathwise response, and its remaining term is half the pairing of the two coordinates of the
annealed mean `Y^±` of AK.HC (2.32).  The two identities below record the resulting closed form
of the centred response as the annealed energy `E[J_t^±]` minus that pairing, which is the form
in which the cutoff decomposition of `e.response.cutoff.estimate` consumes it.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The centred response `Jtilde^-(e)` of `e.response.cutoff.estimate` is the annealed energy
`E[J_t^-] = respEJMinus` of the recentred coefficient `a_- = a - g` minus half the pairing of
the two coordinates of the annealed mean `Y^- = (I_{2d} + R Ehat_t^-) x^-` of AK.HC (2.32),
with `x^- = (-p, q^-)` the doubled recentred load.  The energy part is the block quadratic of the
recentred annealed block `Ehat_t^- = respEhatMinus` at that load, so the two sides agree
definitionally once the annealed energy is put in closed block form. -/
theorem respCenteredJMinus_eq_respEJMinus_sub {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (hq : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) :
    respCenteredJMinus P jStar F t e
      = respEJMinus P jStar F t e
        - (1 / 2 : ℝ) * vecDot (respYMinus P jStar F t e).1 (respYMinus P jStar F t e).2 := by
  rw [respCenteredJMinus_eq_blockCenteredResponse_respEhatMinus,
    respEJMinus_eq_blockResponseEnergy P jStar F t e hq hint]
  rfl

/-- The adjoint centred response `Jtilde^+(e)` of `e.response.cutoff.estimate` is the adjoint
annealed energy `E[J_t^+] = respEJPlus` of the recentred coefficient `a_+ = a^t + g` minus half
the pairing of the two coordinates of the annealed mean `Y^+ = (I_{2d} + R Ehat_t^+) x^+` of
AK.HC (2.32), with `x^+ = (-p, q^+)` the doubled recentred load.  This is the adjoint twin of
`respCenteredJMinus_eq_respEJMinus_sub`, and the two sides agree definitionally once the adjoint
annealed energy is put in closed block form. -/
theorem respCenteredJPlus_eq_respEJPlus_sub {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (hq : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) :
    respCenteredJPlus P jStar F t e
      = respEJPlus P jStar F t e
        - (1 / 2 : ℝ) * vecDot (respYPlus P jStar F t e).1 (respYPlus P jStar F t e).2 := by
  rw [respCenteredJPlus_eq_blockCenteredResponse_respEhatPlus,
    respEJPlus_eq_blockResponseEnergy P jStar F t e hq hint]
  rfl

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cutoff pairing row against the absolute pairing (AK.HC (3.45)-(3.54))

The half-pairing `(1 / 2) * cutoffPairingOnCellAux` is the cutoff pairing row of the centred
decomposition of `e.response.cutoff.estimate`.  Its expectation is bounded by one half of the
expected absolute pairing, and a fortiori by the whole expected absolute pairing, which is the
last summand carried by the cutoff estimate.

Neither bound needs integrability: when the pairing is not integrable the Bochner integral takes
the junk value zero, so the inequalities read `0 ≤ 0` and `0 ≤` a nonnegative integral.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The cutoff pairing row `(1 / 2) * cutoffPairingOnCellAux` is bounded in absolute value by
half of the expected absolute pairing.  No integrability of the pairing is assumed: both sides are
read through the Bochner integral. -/
theorem abs_integral_half_cutoffPairingOnCell_le {d : ℕ}
    (P : Measure (CoeffSpace d)) (U : Set (Vec d)) (φ : Vec d → ℝ) (Y : BlockVec d)
    (c : CoeffSpace d → CoeffField d) (v : (a : CoeffSpace d) → AHarmonicFunction (c a) U) :
    |∫ a, (1 / 2 : ℝ) * cutoffPairingOnCellAux U φ Y (c a) (v a) ∂P|
      ≤ (1 / 2 : ℝ) * ∫ a, |cutoffPairingOnCellAux U φ Y (c a) (v a)| ∂P := by
  rw [integral_const_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by norm_num)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The centred three-row form of the integrated cutoff decomposition (AK.HC (3.45)-(3.54))

The cutoff pairing at a sample coefficient expands pathwise into the cutoff half-energy, the two
cutoff-mean pairings and half the self-pairing of the annealed mean `Y`.  Integrating that
expansion against the law `P` and rearranging gives the identity

`∫J - (1/2) Y₁ · Y₂ = ∫A - ∫(E - J) + (1/2) <∫M₁ - Y₁, Y₂> + (1/2) <Y₁, ∫M₂ - Y₂>`,

whose three rows are the cutoff pairing, the cutoff energy defect and the CENTRED cutoff-mean
row.  Centring the mean row is the mean cancellation of AK.HC (3.45)-(3.54): when the cutoff has
cell average one and the inserted loads are the actual annealed means, `∫M - Y` is the annealed
`(φ - 1)`-weighted mean and is small, whereas the uncentred row is not.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The integral of `vecDot (M a) Y` over `P` is the dot product of `Y` with the vector of
coordinate integrals of `M`: the Fubini step identifying one mean pairing of the integrated
cutoff decomposition of `e.response.cutoff.estimate` (AK.HC (3.45)-(3.54)). -/
theorem integral_vecDot_coord {d : ℕ} {α : Type*} [MeasurableSpace α]
    (P : Measure α) (M : α → Vec d) (Y : Vec d)
    (hM : ∀ i, Integrable (fun a => M a i) P) :
    (∫ a, vecDot (M a) Y ∂P) = vecDot (fun i => ∫ a, M a i ∂P) Y := by
  simp only [vecDot]
  rw [integral_finsetSum Finset.univ (fun i _ => (hM i).mul_const (Y i))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_mul_const]

/-- **The centred three-row integrated cutoff decomposition** (`e.response.cutoff.estimate`,
AK.HC (3.45)-(3.54)).  If the half-pairing `A` is pathwise the affine combination
`E - (1/2) M₁ · Y₂ - (1/2) Y₁ · M₂ + (1/2) Y₁ · Y₂` of the half-energy `E`, the cutoff-mean
coordinates `M₁, M₂`, the annealed mean `Y` and the constant `(1/2) Y₁ · Y₂`, then integrating
against the probability law `P` and identifying the integrated mean pairings by Fubini bounds the
centred response `∫J - (1/2) Y₁ · Y₂` by the absolute cutoff pairing `|∫A|`, the absolute cutoff
energy defect `|∫(E - J)|` and the CENTRED cutoff-mean row
`(1/2) |<∫M₁ - Y₁, Y₂> + <Y₁, ∫M₂ - Y₂>|`. -/
theorem abs_integral_sub_half_vecDot_le_centred {d : ℕ} {α : Type*} [MeasurableSpace α]
    (P : Measure α) [IsProbabilityMeasure P] (Y1 Y2 : Vec d)
    (A E : α → ℝ) (M1 M2 : α → Vec d) (J : α → ℝ)
    (hJ : Integrable J P) (hA : Integrable A P)
    (hW : Integrable (fun a => E a - J a) P)
    (hM1 : ∀ i, Integrable (fun a => M1 a i) P)
    (hM2 : ∀ i, Integrable (fun a => M2 a i) P)
    (hid : ∀ a, A a = E a - (1 / 2 : ℝ) * vecDot (M1 a) Y2
        - (1 / 2 : ℝ) * vecDot Y1 (M2 a) + (1 / 2 : ℝ) * vecDot Y1 Y2) :
    |(∫ a, J a ∂P) - (1 / 2 : ℝ) * vecDot Y1 Y2|
      ≤ |∫ a, A a ∂P| + |∫ a, (E a - J a) ∂P|
        + (1 / 2 : ℝ) * |vecDot ((fun i => ∫ a, M1 a i ∂P) - Y1) Y2
            + vecDot Y1 ((fun i => ∫ a, M2 a i ∂P) - Y2)| := by
  classical
  have _ := hA
  have hE : Integrable E P := by
    refine (hW.add hJ).congr ?_
    filter_upwards with a
    simp only [Pi.add_apply]
    ring
  have hIntM1 : Integrable (fun a => vecDot (M1 a) Y2) P := by
    simp only [vecDot]
    exact integrable_finsetSum Finset.univ (fun i _ => (hM1 i).mul_const (Y2 i))
  have hIntM2 : Integrable (fun a => vecDot Y1 (M2 a)) P := by
    simp only [vecDot]
    exact integrable_finsetSum Finset.univ (fun i _ => (hM2 i).const_mul (Y1 i))
  have hT1 : Integrable (fun a => (1 / 2 : ℝ) * vecDot (M1 a) Y2) P :=
    hIntM1.const_mul _
  have hT2 : Integrable (fun a => (1 / 2 : ℝ) * vecDot Y1 (M2 a)) P :=
    hIntM2.const_mul _
  have hCint : Integrable (fun _ : α => (1 / 2 : ℝ) * vecDot Y1 Y2) P :=
    integrable_const _
  have hAint : (∫ a, A a ∂P)
      = (∫ a, E a ∂P)
        - (1 / 2 : ℝ) * vecDot (fun i => ∫ a, M1 a i ∂P) Y2
        - (1 / 2 : ℝ) * vecDot Y1 (fun i => ∫ a, M2 a i ∂P)
        + (1 / 2 : ℝ) * vecDot Y1 Y2 := by
    have h1 : (∫ a, A a ∂P)
        = ∫ a, (E a - (1 / 2 : ℝ) * vecDot (M1 a) Y2
            - (1 / 2 : ℝ) * vecDot Y1 (M2 a)
            + (1 / 2 : ℝ) * vecDot Y1 Y2) ∂P := by
      refine integral_congr_ae ?_
      filter_upwards with a
      exact hid a
    rw [h1]
    have h2 : (∫ a, (E a - (1 / 2 : ℝ) * vecDot (M1 a) Y2
          - (1 / 2 : ℝ) * vecDot Y1 (M2 a)
          + (1 / 2 : ℝ) * vecDot Y1 Y2) ∂P)
        = (∫ a, (E a - (1 / 2 : ℝ) * vecDot (M1 a) Y2
              - (1 / 2 : ℝ) * vecDot Y1 (M2 a)) ∂P)
          + (∫ a, (1 / 2 : ℝ) * vecDot Y1 Y2 ∂P) :=
      integral_add ((hE.sub hT1).sub hT2) hCint
    rw [h2]
    have h3 : (∫ a, (E a - (1 / 2 : ℝ) * vecDot (M1 a) Y2
          - (1 / 2 : ℝ) * vecDot Y1 (M2 a)) ∂P)
        = (∫ a, (E a - (1 / 2 : ℝ) * vecDot (M1 a) Y2) ∂P)
          - (∫ a, (1 / 2 : ℝ) * vecDot Y1 (M2 a) ∂P) :=
      integral_sub (hE.sub hT1) hT2
    rw [h3]
    have h4 : (∫ a, (E a - (1 / 2 : ℝ) * vecDot (M1 a) Y2) ∂P)
        = (∫ a, E a ∂P) - (∫ a, (1 / 2 : ℝ) * vecDot (M1 a) Y2 ∂P) :=
      integral_sub hE hT1
    rw [h4]
    have h5 : (∫ a, (1 / 2 : ℝ) * vecDot (M1 a) Y2 ∂P)
        = (1 / 2 : ℝ) * vecDot (fun i => ∫ a, M1 a i ∂P) Y2 := by
      rw [integral_const_mul, integral_vecDot_coord P M1 Y2 hM1]
    have h6 : (∫ a, (1 / 2 : ℝ) * vecDot Y1 (M2 a) ∂P)
        = (1 / 2 : ℝ) * vecDot Y1 (fun i => ∫ a, M2 a i ∂P) := by
      rw [integral_const_mul]
      congr 1
      simp only [vecDot]
      rw [integral_finsetSum Finset.univ (fun i _ => (hM2 i).const_mul (Y1 i))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_const_mul]
    have h7 : (∫ a, (1 / 2 : ℝ) * vecDot Y1 Y2 ∂P) = (1 / 2 : ℝ) * vecDot Y1 Y2 := by
      rw [integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
    rw [h5, h6, h7]
  have hWint : (∫ a, (E a - J a) ∂P) = (∫ a, E a ∂P) - (∫ a, J a ∂P) :=
    integral_sub hE hJ
  have hsub_left : ∀ x y z : Vec d, vecDot (x - y) z = vecDot x z - vecDot y z := by
    intro x y z
    rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, sub_eq_add_neg]
  have hsub_right : ∀ x y z : Vec d, vecDot x (y - z) = vecDot x y - vecDot x z := by
    intro x y z
    rw [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right, sub_eq_add_neg]
  have hId : (∫ a, J a ∂P) - (1 / 2 : ℝ) * vecDot Y1 Y2
      = (∫ a, A a ∂P) - (∫ a, (E a - J a) ∂P)
        + (1 / 2 : ℝ) * (vecDot ((fun i => ∫ a, M1 a i ∂P) - Y1) Y2
            + vecDot Y1 ((fun i => ∫ a, M2 a i ∂P) - Y2)) := by
    rw [hAint, hWint, hsub_left, hsub_right]
    ring
  have hXZ : |(1 / 2 : ℝ) * (vecDot ((fun i => ∫ a, M1 a i ∂P) - Y1) Y2
        + vecDot Y1 ((fun i => ∫ a, M2 a i ∂P) - Y2))|
      = (1 / 2 : ℝ) * |vecDot ((fun i => ∫ a, M1 a i ∂P) - Y1) Y2
          + vecDot Y1 ((fun i => ∫ a, M2 a i ∂P) - Y2)| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2))]
  calc
    |(∫ a, J a ∂P) - (1 / 2 : ℝ) * vecDot Y1 Y2|
        = |(∫ a, A a ∂P) - (∫ a, (E a - J a) ∂P)
            + (1 / 2 : ℝ) * (vecDot ((fun i => ∫ a, M1 a i ∂P) - Y1) Y2
                + vecDot Y1 ((fun i => ∫ a, M2 a i ∂P) - Y2))| := by rw [hId]
    _ ≤ |(∫ a, A a ∂P) - (∫ a, (E a - J a) ∂P)|
          + |(1 / 2 : ℝ) * (vecDot ((fun i => ∫ a, M1 a i ∂P) - Y1) Y2
                + vecDot Y1 ((fun i => ∫ a, M2 a i ∂P) - Y2))| :=
        abs_add_le _ _
    _ ≤ (|∫ a, A a ∂P| + |∫ a, (E a - J a) ∂P|)
          + |(1 / 2 : ℝ) * (vecDot ((fun i => ∫ a, M1 a i ∂P) - Y1) Y2
                + vecDot Y1 ((fun i => ∫ a, M2 a i ∂P) - Y2))| := by
        refine add_le_add ?_ (le_refl _)
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (∫ a, A a ∂P) (-(∫ a, (E a - J a) ∂P))
    _ = |∫ a, A a ∂P| + |∫ a, (E a - J a) ∂P|
          + (1 / 2 : ℝ) * |vecDot ((fun i => ∫ a, M1 a i ∂P) - Y1) Y2
              + vecDot Y1 ((fun i => ∫ a, M2 a i ∂P) - Y2)| := by
        rw [hXZ]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The centred response against its three cutoff rows (AK.HC (3.45)-(3.54))

The centred responses `Jtilde^±(e)` of `e.response.cutoff.estimate` are the annealed energies at
the recentred loads minus half the pairing of the two coordinates of the annealed mean `Y^±`.  The
cutoff decomposition of the cutoff pairing exhibits the half-pairing as the cutoff half-energy
minus the two cutoff-mean pairings plus half the self-pairing of `Y^±`, so integrating against the
law and bounding the result reduces the centred response to three rows: the expected absolute
cutoff pairing, the absolute cutoff energy defect `E[cutoffHalfEnergy - J]`, and the CENTRED
cutoff-mean row, in which the integrated cutoff means appear only through their difference from the
annealed mean.  These are the `e4`, `e1` and `e2 + e3` of the printed variational calculation.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The centred response against its three cutoff rows** (`e.response.cutoff.estimate`,
AK.HC (3.45)-(3.54)), minus carriers.  If the half-pairing
`(1/2) * cutoffPairingOnCellAux` is pathwise the affine combination of the cutoff half-energy,
the two cutoff-mean coordinates and half the self-pairing of the annealed mean `Y^-`, then the
centred response `|Jtilde^-(e)|` is bounded by the sum of the expected absolute cutoff pairing, the
absolute cutoff energy defect `E[cutoffHalfEnergy - J]`, and the CENTRED cutoff-mean row
`(1/2) |<E[M₁] - Y₁^-, Y₂^-> + <Y₁^-, E[M₂] - Y₂^->|`. -/
theorem abs_respCenteredJMinus_le_three_rows {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (φ : Vec d → ℝ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hq : IsUnit (respGrid jStar F))
    (hblk : HasIntegrableCoarseBlock P (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hA : Integrable (fun a => (1 / 2 : ℝ) *
      cutoffPairingOnCellAux (respCell jStar F t) φ (respYMinus P jStar F t e)
        (respCoeffMinus F a) (uM a)) P)
    (hW : Integrable (fun a =>
      cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hM1 : ∀ i, Integrable (fun a =>
      (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).1 i) P)
    (hM2 : ∀ i, Integrable (fun a =>
      (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).2 i) P)
    (hid : ∀ a, (1 / 2 : ℝ) *
        cutoffPairingOnCellAux (respCell jStar F t) φ (respYMinus P jStar F t e)
          (respCoeffMinus F a) (uM a)
      = cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
        - (1 / 2 : ℝ) * vecDot
            (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).1
            (respYMinus P jStar F t e).2
        - (1 / 2 : ℝ) * vecDot (respYMinus P jStar F t e).1
            (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).2
        + (1 / 2 : ℝ) * vecDot (respYMinus P jStar F t e).1 (respYMinus P jStar F t e).2) :
    |respCenteredJMinus P jStar F t e|
      ≤ (1 / 2 : ℝ) * (∫ a, |cutoffPairingOnCellAux (respCell jStar F t) φ
            (respYMinus P jStar F t e) (respCoeffMinus F a) (uM a)| ∂P)
        + |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
            - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
                (respqMinus P jStar F t e) (respCoeffMinus F a)) ∂P|
        + (1 / 2 : ℝ) * |vecDot
              ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
                (respCoeffMinus F a) (uM a)).1 i ∂P) - (respYMinus P jStar F t e).1)
              (respYMinus P jStar F t e).2
            + vecDot (respYMinus P jStar F t e).1
              ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
                (respCoeffMinus F a) (uM a)).2 i ∂P) - (respYMinus P jStar F t e).2)| := by
  rw [respCenteredJMinus_eq_respEJMinus_sub P jStar F t e hq hblk]
  have hmain := abs_integral_sub_half_vecDot_le_centred P
    (respYMinus P jStar F t e).1 (respYMinus P jStar F t e).2
    (fun a => (1 / 2 : ℝ) * cutoffPairingOnCellAux (respCell jStar F t) φ
      (respYMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (fun a => cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a))
    (fun a => (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).1)
    (fun a => (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).2)
    (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a))
    hJ hA hW hM1 hM2 hid
  have hpair := abs_integral_half_cutoffPairingOnCell_le P (respCell jStar F t) φ
    (respYMinus P jStar F t e) (respCoeffMinus F) uM
  simp only [respEJMinus] at hmain ⊢
  linarith only [hmain, hpair]

/-- **The centred response against its three cutoff rows** (`e.response.cutoff.estimate`,
AK.HC (3.45)-(3.54)), plus carriers.  If the half-pairing
`(1/2) * cutoffPairingOnCellAux` is pathwise the affine combination of the cutoff half-energy,
the two cutoff-mean coordinates and half the self-pairing of the annealed mean `Y^+`, then the
centred response `|Jtilde^+(e)|` is bounded by the sum of the expected absolute cutoff pairing, the
absolute cutoff energy defect `E[cutoffHalfEnergy - J]`, and the CENTRED cutoff-mean row
`(1/2) |<E[M₁] - Y₁^+, Y₂^+> + <Y₁^+, E[M₂] - Y₂^+>|`. -/
theorem abs_respCenteredJPlus_le_three_rows {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (φ : Vec d → ℝ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hq : IsUnit (respGrid jStar F))
    (hblk : HasIntegrableCoarseBlock P (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hA : Integrable (fun a => (1 / 2 : ℝ) *
      cutoffPairingOnCellAux (respCell jStar F t) φ (respYPlus P jStar F t e)
        (respCoeffPlus F a) (uP a)) P)
    (hW : Integrable (fun a =>
      cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hM1 : ∀ i, Integrable (fun a =>
      (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).1 i) P)
    (hM2 : ∀ i, Integrable (fun a =>
      (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).2 i) P)
    (hid : ∀ a, (1 / 2 : ℝ) *
        cutoffPairingOnCellAux (respCell jStar F t) φ (respYPlus P jStar F t e)
          (respCoeffPlus F a) (uP a)
      = cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
        - (1 / 2 : ℝ) * vecDot
            (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).1
            (respYPlus P jStar F t e).2
        - (1 / 2 : ℝ) * vecDot (respYPlus P jStar F t e).1
            (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).2
        + (1 / 2 : ℝ) * vecDot (respYPlus P jStar F t e).1 (respYPlus P jStar F t e).2) :
    |respCenteredJPlus P jStar F t e|
      ≤ (1 / 2 : ℝ) * (∫ a, |cutoffPairingOnCellAux (respCell jStar F t) φ
            (respYPlus P jStar F t e) (respCoeffPlus F a) (uP a)| ∂P)
        + |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
            - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
                (respqPlus P jStar F t e) (respCoeffPlus F a)) ∂P|
        + (1 / 2 : ℝ) * |vecDot
              ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
                (respCoeffPlus F a) (uP a)).1 i ∂P) - (respYPlus P jStar F t e).1)
              (respYPlus P jStar F t e).2
            + vecDot (respYPlus P jStar F t e).1
              ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
                (respCoeffPlus F a) (uP a)).2 i ∂P) - (respYPlus P jStar F t e).2)| := by
  rw [respCenteredJPlus_eq_respEJPlus_sub P jStar F t e hq hblk]
  have hmain := abs_integral_sub_half_vecDot_le_centred P
    (respYPlus P jStar F t e).1 (respYPlus P jStar F t e).2
    (fun a => (1 / 2 : ℝ) * cutoffPairingOnCellAux (respCell jStar F t) φ
      (respYPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (fun a => cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a))
    (fun a => (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).1)
    (fun a => (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).2)
    (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a))
    hJ hA hW hM1 hM2 hid
  have hpair := abs_integral_half_cutoffPairingOnCell_le P (respCell jStar F t) φ
    (respYPlus P jStar F t e) (respCoeffPlus F) uP
  simp only [respEJPlus] at hmain ⊢
  linarith only [hmain, hpair]

end

end HCPolySupport.HighContrast.Multiscale
end
