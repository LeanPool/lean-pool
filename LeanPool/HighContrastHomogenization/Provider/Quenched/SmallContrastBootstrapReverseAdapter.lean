/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBootstrapSmallness
public import LeanPool.HighContrastHomogenization.Provider.Selection.EnclosureGeometry

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastBootstrapReverseAdapter

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The reverse Euclidean adapter with a decaying absorbed size

The endgame runs the adapted-to-Euclidean adapter in the *reverse* direction:
the annealed block of the outer cube `□_m` is compared with the adapted mean at
the corrected halfway scale `n`, and the comparison error must decay in `m − n`
with a constant that does not move with the generation.

Two ingredients make the absorbed size `c·|𝐄 : E_n^q|` uniform.  The first is
the reference ratio at the selection grid: the Dagger envelope on the adapted
cell, the sharp reversal, and `𝐄 ≤ κ_𝐄 𝐄_#` bound `|𝐄 : E_n^q|` by
`κ_𝐄 · C(K) · B_q · 3^{gG}`, where `G` is the grid's enclosure enlargement —
the same chain the bootstrap uses on the Euclidean grid, at a general witness
and a general enlargement.  The second is the source gauge, bounded at every
nonnegative scale by its value at scale zero.

The result is the pair of inputs the corrected tilt transfer consumes: the Loewner adapter itself
and a decaying bound
`c·|𝐄 : E_n^q| ≤ CB · factor · 3^{−(m−n)}` on the absorbed size.  Taking
`m − n` large enough turns the second into the unit cap `η ≤ 1`; taking
`A ≥ (9/2)·CB·factor` turns it into the error clause.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The reference ratio at a rounded selection grid whose adapted cells are
enclosed with enlargement `G`. -/
@[expose]
def gridReferenceRatio (Cd g K : ℝ) (E : BlockMat d) (mAl : Mat d) (G : ℕ) : ℝ :=
  kappaRef E *
    (sourceMomentOne K * boundaryConst Cd g mAl * (3 : ℝ) ^ (g * (G : ℝ)))

/-- **The absorbed size of the reference against the adapted mean of a rounded
selection grid** is bounded by the grid reference ratio, uniformly in the
generation past the source burn. -/
theorem blockSize_reference_adaptedMean_le [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l) {mAl : Mat d} (hmAl : mAl.PosDef)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK) {G : ℕ}
    (hqnorm : ‖roundedGrid l mAl‖ * Real.sqrt d ≤ (3 : ℝ) ^ G)
    {n : ℤ} (hDelta : 0 ≤ n + (G : ℤ) - 1 - sK) :
    (1 : ℝ) ≤ gridReferenceRatio Cd g K E mAl G ∧
      blockSize E (adaptedMean P (roundedGrid l mAl) n) ≤
        gridReferenceRatio Cd g K E mAl G := by
  classical
  have hsub : adaptedCell (roundedGrid l mAl) n ⊆ centeredCube d (n + (G : ℤ)) :=
    Selection.adaptedCell_subset_centeredCube_add (by omega) hqnorm
  have hint : HasFiniteAdaptedMean P (roundedGrid l mAl) n :=
    (finite_adaptedMean_of_coarseEllipticityDagger hdag
      (Recurrence.posDef_roundedGrid hl hmAl) n).1
  obtain ⟨hone, hquad⟩ := terminal_reference_comparability hd hg hdag hl hCd
    hmAl hsK n (G := G) hDelta hsub hint
  have hcast : (((n + (G : ℤ) : ℤ) : ℝ) - (n : ℝ)) = (G : ℝ) := by
    push_cast
    ring
  rw [hcast] at hone hquad
  have hle : BlockMatLoewnerLE E
      (blockScale (gridReferenceRatio Cd g K E mAl G)
        (adaptedMean P (roundedGrid l mAl) n)) := by
    intro X
    rw [Sharp.blockVecDot_blockMatVecMul_blockScale]
    have := hquad X
    rw [gridReferenceRatio]
    linarith only [this]
  refine ⟨hone, ?_⟩
  exact Transport.blockSize_le_of_blockMatLoewnerLE_blockScale
    hdag.refBlock_isSymm
    (posDef_toFullBlockMat hdag.refBlock_isSymm hdag.refBlock_posDef).posSemidef
    (Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid l mAl) n)
    (Recurrence.blockPosDef_adaptedMean (Recurrence.posDef_roundedGrid hl hmAl) n hint)
    (by rw [gridReferenceRatio]; linarith only [hone]) hle

/-- The law-side factor of the reverse adapter error: the grid eccentricity,
the source-gauge cap and the grid reference ratio. -/
@[expose]
def reverseAdapterFactor (Cd g K : ℝ) (E : BlockMat d) (mAl : Mat d)
    (G : ℕ) : ℝ :=
  witnessEccentricity mAl *
    ((1 + K ^ 2) ^ g * gridReferenceRatio Cd g K E mAl G)

/-- **The reverse Euclidean adapter with a decaying absorbed size.**  At every
admissible triple of scales the reverse comparison holds with a coefficient
whose absorbed size against the adapted mean is bounded by a generation-free
law factor times `3^{−(m−n)}`. -/
theorem exists_reverse_adapter_error_bound (d : ℕ) (hd : 2 ≤ d) (g : ℝ)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    ∃ CB : ℝ, 0 < CB ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P → HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∀ Cd : ℝ, max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd →
          ∀ sK : ℤ, 0 ≤ sK → growthBar K ≤ (3 : ℝ) ^ sK →
            ∀ l : ℤ, (kZero d : ℤ) ≤ l → ∀ mAl : Mat d, mAl.PosDef →
              ∀ G : ℕ, ‖roundedGrid l mAl‖ * Real.sqrt d ≤ (3 : ℝ) ^ G →
                ∀ k n m : ℤ, 0 ≤ k → k < n → n < m → l ≤ n →
                  0 ≤ n + (G : ℤ) - 1 - sK →
                  ∃ c : ℝ, 0 ≤ c ∧
                    BlockMatLoewnerLE
                      (blockSub (annealedBlock P (centeredCube d m))
                        (adaptedMean P (roundedGrid l mAl) n))
                      (blockScale c E) ∧
                    c * blockSize E (adaptedMean P (roundedGrid l mAl) n) ≤
                      CB * reverseAdapterFactor Cd g K E mAl G *
                        (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ))) := by
  classical
  obtain ⟨CAE, hCAE0, hCAE⟩ := Entry.exists_euclidean_adapter d hd g hg
  have hgpos : (0 : ℝ) < 1 - g := by linarith only [hg.2]
  refine ⟨CAE * (1 - g)⁻¹, mul_pos hCAE0 (inv_pos.mpr hgpos), ?_⟩
  intro P E Ψ K S hP hstat hunit hdag Cd hCd sK hsK0 hsK l hl mAl hmAl G hqnorm
    k n m hk0 hkn hnm hln hDelta
  have : NeZero d := ⟨by omega⟩
  have := hP
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hn0 : (0 : ℤ) ≤ n := by omega
  obtain ⟨-, hrev⟩ := hCAE P E Ψ K S hP hstat hunit hdag l hl mAl hmAl
    k n m hk0 hkn hnm
  obtain ⟨hone, hsize⟩ :=
    blockSize_reference_adaptedMean_le hd hg hdag hCd hl hmAl hsK hqnorm hDelta
  have hecc1 : (1 : ℝ) ≤ witnessEccentricity mAl :=
    Initialization.one_le_witnessEccentricity hmAl
  have hecc0 : (0 : ℝ) ≤ witnessEccentricity mAl := by linarith only [hecc1]
  have hR0 : (0 : ℝ) ≤ gridReferenceRatio Cd g K E mAl G := by
    linarith only [hone]
  have hTG0 : (0 : ℝ) < transferGauge g K n := by
    rw [transferGauge]
    have hb : (0 : ℝ) < 1 + K ^ 2 * (3 : ℝ) ^ (-n) := by positivity
    exact mul_pos (inv_pos.mpr hgpos) (Real.rpow_pos_of_pos hb g)
  have hgauge := transferGauge_le_bar (K := K) hg hn0
  have hp0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hae0 : (0 : ℝ) ≤ CAE * witnessEccentricity mAl :=
    mul_nonneg hCAE0.le hecc0
  have hc0 : (0 : ℝ) ≤
      CAE * witnessEccentricity mAl * transferGauge g K n *
        (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ))) :=
    mul_nonneg (mul_nonneg hae0 hTG0.le) hp0
  refine ⟨CAE * witnessEccentricity mAl * transferGauge g K n *
    (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ))), hc0, hrev hln, ?_⟩
  have hstep1 : CAE * witnessEccentricity mAl * transferGauge g K n ≤
      CAE * witnessEccentricity mAl * ((1 - g)⁻¹ * (1 + K ^ 2) ^ g) :=
    mul_le_mul_of_nonneg_left hgauge hae0
  have hstep2 :
      CAE * witnessEccentricity mAl * transferGauge g K n *
          (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ))) ≤
        CAE * witnessEccentricity mAl * ((1 - g)⁻¹ * (1 + K ^ 2) ^ g) *
          (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ))) :=
    mul_le_mul_of_nonneg_right hstep1 hp0
  have hstep3 :
      CAE * witnessEccentricity mAl * transferGauge g K n *
            (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ))) *
          gridReferenceRatio Cd g K E mAl G ≤
        CAE * witnessEccentricity mAl * ((1 - g)⁻¹ * (1 + K ^ 2) ^ g) *
            (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ))) *
          gridReferenceRatio Cd g K E mAl G :=
    mul_le_mul_of_nonneg_right hstep2 hR0
  have hid :
      CAE * witnessEccentricity mAl * ((1 - g)⁻¹ * (1 + K ^ 2) ^ g) *
            (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ))) *
          gridReferenceRatio Cd g K E mAl G =
        CAE * (1 - g)⁻¹ * reverseAdapterFactor Cd g K E mAl G *
          (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ))) := by
    rw [reverseAdapterFactor]
    ring
  have hleft := mul_le_mul_of_nonneg_left hsize hc0
  rw [hid] at hstep3
  linarith only [hleft, hstep3]

end

end HCPolySupport.HighContrast.Quenched
