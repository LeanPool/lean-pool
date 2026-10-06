/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.PositiveGapClosure
public import LeanPool.HighContrastHomogenization.Setup.TransportObjects
public import LeanPool.HighContrastHomogenization.Provider.Transport.NearIsometry
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneySquareWeights
public import LeanPool.HighContrastHomogenization.Provider.Transport.DiscreteConvolution
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.MajorizationSup
public import LeanPool.HighContrastHomogenization.Annealed.SchattenDefinedness
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.RecurrenceAssembly
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.MajorizationSize
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.CheckpointMoment

/-!
# High-contrast homogenization: Provider.Transport.CenteredSplit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The fresh/inherited decomposition of the centred filling

The combined bound for the transported fluctuations charges the centred response
of one target cell of the new grid to two different objects: the sources strictly
above the checkpoint are summed by discrete Young convolution against the centred
moments `v_r^q`, giving the contribution of the fluctuations at the new
scales, while the sources at or below it are *not restarted* — they are
grouped by their scale-`b` ancestor and read off the single statistic `X_B` that
stationarity compares with the centred history at the checkpoint
(`e.two.grid.old.history.factor`).

The per-target-cell estimate `Transport.cell_moment_le_of_gap` produces one real
number: the mixed `L^Q(S_Q)` size of the *whole* centred filling.  This file
splits that number along the two regimes, in the carriers the two downstream
estimates consume.

*The triangle inequality.*  The Schatten size is a norm, but the repository
carries it only through its spectrum, so the triangle inequality is taken in the
crude dimensional form the transport can afford: the Hilbert–Schmidt comparison
`|H|_{S_Q} ≤ (Σ_{αβ}H_{αβ}²)^{1/2}` of `l.fixed.geometry.matrix.averaging` and
the entrywise bound `|H_{αβ}| ≤ |H|_{S_Q}` give
`|A + B|_{S_Q} ≤ 2d(|A|_{S_Q} + |B|_{S_Q})`, and Minkowski in `L^Q` carries it to
the mixed norm.  The dimensional factor is a `C(d,Q)`, which is what the printed
constants are.

*The inherited leg.*  Below the checkpoint the estimate leaves the Schatten
dialect at once: the return route `PortableHistory.schattenSize_le_blockSize` puts the
sum back on the scalar size, which is subadditive because it is the spectral norm
of the normalized block.  Each cell is then renormalized from the checkpoint at
the cost `3^{ρ_max(b-r)}` and dominated by the statistic of its own scale-`b`
ancestor; the passage back to the `Q`-th power is the printed max-to-sum, taken
here through `sup ≤ (Σ (·)^Q)^{1/Q}`, so the ancestor count enters at the first
power exactly as `e.two.grid.old.history.factor` binds it.

*The normalization bridge.*  The fresh half is estimated at the old terminal
normalization `E_t^q` and read at the new one `E_n^{q'}`; the same two spectral
comparisons exchange the two, and the scale factor they cost is exactly the lower
bridge clause `(1-η_x)E_t^q ≤ E_n^{q'}` of `p.two.grid.transport`.

The grouping map itself is not produced here: it is data of the filling, and the
consumer supplies it together with the weight budget of the row sum inside an
ancestor at the checkpoint generation.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The Schatten triangle inequality with the dimensional constant -/

/-- **The Schatten size is subadditive up to `2d`.**  The Hilbert–Schmidt
comparison bounds the size of the sum by its Frobenius norm, and each of the
`4d²` entries of the sum is at most the sum of the two sizes. -/
theorem schattenNorm_add_le {Q : ℝ} (hQ : 2 ≤ Q) {A B C : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hB : IsSymmetricBlockMat B) (hC : IsSymmetricBlockMat C)
    (hsum : toFullBlockMat C = toFullBlockMat A + toFullBlockMat B) :
    schattenNorm Q C ≤ 2 * (d : ℝ) * (schattenNorm Q A + schattenNorm Q B) := by
  have hQ0 : (0 : ℝ) < Q := by linarith only [hQ]
  have hSA : (0 : ℝ) ≤ schattenNorm Q A := Recurrence.zero_le_schattenNorm hA Q
  have hSB : (0 : ℝ) ≤ schattenNorm Q B := Recurrence.zero_le_schattenNorm hB Q
  have hdR : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  set S : ℝ := schattenNorm Q A + schattenNorm Q B with hSdef
  have hS0 : (0 : ℝ) ≤ S := by rw [hSdef]; linarith only [hSA, hSB]
  have hentry : ∀ α β : BlockCoord d, |toFullBlockMat C α β| ≤ S := by
    intro α β
    rw [hsum, Matrix.add_apply, hSdef]
    exact le_trans (abs_add_le _ _) (add_le_add
      (Recurrence.abs_toFullBlockMat_le_schattenNorm hA hQ0 α β)
      (Recurrence.abs_toFullBlockMat_le_schattenNorm hB hQ0 α β))
  have hcard : (Fintype.card (BlockCoord d) : ℝ) = 2 * (d : ℝ) := by
    simp [BlockCoord, Fintype.card_sum, two_mul]
  have hsq : ∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat C α β ^ 2 ≤
      (2 * (d : ℝ) * S) ^ 2 := by
    have hrow : ∀ α : BlockCoord d,
        ∑ β : BlockCoord d, toFullBlockMat C α β ^ 2 ≤ 2 * (d : ℝ) * S ^ 2 := by
      intro α
      calc ∑ β : BlockCoord d, toFullBlockMat C α β ^ 2
          ≤ ∑ _β : BlockCoord d, S ^ 2 := by
            refine Finset.sum_le_sum fun β _ => ?_
            have h := hentry α β
            nlinarith only [h, abs_nonneg (toFullBlockMat C α β),
              sq_abs (toFullBlockMat C α β)]
        _ = 2 * (d : ℝ) * S ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    calc ∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat C α β ^ 2
        ≤ ∑ _α : BlockCoord d, 2 * (d : ℝ) * S ^ 2 := Finset.sum_le_sum fun α _ => hrow α
      _ = 2 * (d : ℝ) * (2 * (d : ℝ) * S ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
      _ = (2 * (d : ℝ) * S) ^ 2 := by ring
  have hy0 : (0 : ℝ) ≤ 2 * (d : ℝ) * S := by positivity
  have hfin : ((2 * (d : ℝ) * S) ^ 2) ^ (2⁻¹ : ℝ) = 2 * (d : ℝ) * S := by
    rw [← Real.rpow_natCast (2 * (d : ℝ) * S) 2, ← Real.rpow_mul hy0]
    norm_num
  refine le_trans (Recurrence.schattenNorm_le_sum_sq_rpow hC hQ) ?_
  have hnn : (0 : ℝ) ≤ ∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat C α β ^ 2 :=
    Finset.sum_nonneg fun α _ => Finset.sum_nonneg fun β _ => sq_nonneg _
  calc (∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat C α β ^ 2) ^ (2⁻¹ : ℝ)
      ≤ ((2 * (d : ℝ) * S) ^ 2) ^ (2⁻¹ : ℝ) := Real.rpow_le_rpow hnn hsq (by norm_num)
    _ = 2 * (d : ℝ) * S := hfin

/-- The same at a fixed normalization: normalization is real-linear, so the
Schatten *size* inherits the dimensional triangle inequality. -/
theorem schattenSize_add_le {Q : ℝ} (hQ : 2 ≤ Q) {A B C F : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hB : IsSymmetricBlockMat B) (hC : IsSymmetricBlockMat C)
    (hsum : toFullBlockMat C = toFullBlockMat A + toFullBlockMat B) :
    schattenSize Q C F ≤ 2 * (d : ℝ) * (schattenSize Q A F + schattenSize Q B F) := by
  refine schattenNorm_add_le hQ (isSymmetricBlockMat_normalizedBlock hA)
    (isSymmetricBlockMat_normalizedBlock hB) (isSymmetricBlockMat_normalizedBlock hC) ?_
  rw [Recurrence.toFullBlockMat_normalizedBlock, Recurrence.toFullBlockMat_normalizedBlock,
    Recurrence.toFullBlockMat_normalizedBlock, hsum, Matrix.mul_add, Matrix.add_mul]

/-! ## The mixed norm of a sum -/

/-- The Schatten size of a random block at a fixed normalization is a measurable
statistic at an even exponent. -/
theorem aestronglyMeasurable_schattenSize {P : Measure (CoeffSpace d)}
    {A : CoeffSpace d → BlockMat d} {F : BlockMat d} {Q : ℕ} (hQeven : Even Q)
    (hA : ∀ a, IsSymmetricBlockMat (A a))
    (hAm : ∀ α β : BlockCoord d,
      AEStronglyMeasurable (fun a => toFullBlockMat (A a) α β) P) :
    AEStronglyMeasurable (fun a => schattenSize (Q : ℝ) (A a) F) P := by
  refine Recurrence.aestronglyMeasurable_schattenNorm
    (H := fun a => normalizedBlock (A a) F)
    (fun a => isSymmetricBlockMat_normalizedBlock (hA a)) hQeven fun α β => ?_
  have hfun : (fun a => toFullBlockMat (normalizedBlock (A a) F) α β) =
      fun a => (matSqrt (toFullBlockMat F)⁻¹ * toFullBlockMat (A a) *
        matSqrt (toFullBlockMat F)⁻¹) α β := by
    funext a
    rw [Recurrence.toFullBlockMat_normalizedBlock]
  rw [hfun]
  exact Recurrence.aestronglyMeasurable_entry_conj _ hAm α β

/-- The `Q`-th power of the mixed norm is the `Q`-th moment of the Schatten
size. -/
theorem lqSchattenSize_rpow_eq {P : Measure (CoeffSpace d)} {Q : ℝ} (hQ : 0 < Q)
    {A : CoeffSpace d → BlockMat d} (hA : ∀ a, IsSymmetricBlockMat (A a))
    (F : BlockMat d) (hAm : AEStronglyMeasurable (fun a => schattenSize Q (A a) F) P) :
    lqSchattenSize P Q A F ^ Q =
      ∫⁻ a, ENNReal.ofReal (schattenSize Q (A a) F) ^ Q ∂P := by
  have hp0 : (ENNReal.ofReal Q) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hQ
  rw [lqSchattenSize, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hAm,
    ENNReal.toReal_ofReal hQ.le, ← ENNReal.rpow_mul, one_div,
    inv_mul_cancel₀ (ne_of_gt hQ), ENNReal.rpow_one]
  refine lintegral_congr fun a => ?_
  have h0 : (0 : ℝ) ≤ schattenSize Q (A a) F :=
    Recurrence.zero_le_schattenNorm (isSymmetricBlockMat_normalizedBlock (hA a)) Q
  rw [Real.enorm_eq_ofReal h0]

/-! ## The scalar size of a filling sum -/

/-- **The scalar size of a filling sum is subadditive.**  The normalized block is
real-linear in its argument and the scalar size is the spectral norm of the
normalized block. -/
theorem blockSize_filling_sum_le {F : BlockMat d} (hF : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F) {R : Finset ℤ} {Z : ℤ → Finset (Fin d → ℤ)}
    {c : ℤ → ℝ} (hc : ∀ r ∈ R, 0 ≤ c r) {H : ℤ → (Fin d → ℤ) → BlockMat d}
    (hH : ∀ r w, IsSymmetricBlockMat (H r w)) :
    blockSize (ofFullBlockMat (∑ r ∈ R, ∑ w ∈ Z r, c r • toFullBlockMat (H r w))) F ≤
      ∑ r ∈ R, ∑ w ∈ Z r, c r * blockSize (H r w) F := by
  have hSsym : IsSymmetricBlockMat
      (ofFullBlockMat (∑ r ∈ R, ∑ w ∈ Z r, c r • toFullBlockMat (H r w))) := by
    refine isSymmetricBlockMat_of_isSymm ?_
    ext γ δ
    simp only [Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun w _ =>
      congrArg _ ((isSymm_toFullBlockMat_of_isSymmetricBlockMat (hH r w)).apply γ δ)
  rw [PortableHistory.blockSize_eq_norm hSsym hF hFpd, Recurrence.toFullBlockMat_normalizedBlock,
    toFullBlockMat_ofFullBlockMat]
  have hexp : matSqrt (toFullBlockMat F)⁻¹ *
        (∑ r ∈ R, ∑ w ∈ Z r, c r • toFullBlockMat (H r w)) *
        matSqrt (toFullBlockMat F)⁻¹ =
      ∑ r ∈ R, ∑ w ∈ Z r, c r • (matSqrt (toFullBlockMat F)⁻¹ *
        toFullBlockMat (H r w) * matSqrt (toFullBlockMat F)⁻¹) := by
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hexp]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun r hr => ?_)
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun w _ => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hc r hr),
    PortableHistory.blockSize_eq_norm (hH r w) hF hFpd, Recurrence.toFullBlockMat_normalizedBlock]

/-! ## The inherited leg -/

/-! ## The decomposition -/

/-! ## The inherited leg at the centred history -/

/-! ## The normalization bridge -/

/-- **The normalization exchange at a scale factor.**  If the old reference block
is below `λ` times the new one, then the mixed `L^Q(S_Q)` size at the new
normalization is at most `(2d)^{1/Q}λ` times the size at the old one.

The Schatten dialect is left and re-entered through the two spectral comparisons
`PortableHistory.schattenSize_le_blockSize` and `PortableHistory.blockSize_le_schattenSize`; in
between the
exchange is `PortableHistory.blockSize_le_mul_blockSize`, which is where the scale factor
enters and is the only inequality that is not dimension-free. -/
theorem lqSchattenSize_le_of_smul_le [NeZero d] {P : Measure (CoeffSpace d)}
    {Ej Ep : BlockMat d}
    (hEjs : IsSymmetricBlockMat Ej) (hEjpd : Book.Ch02.BlockPosDef Ej)
    (hEps : IsSymmetricBlockMat Ep) (hEppd : Book.Ch02.BlockPosDef Ep)
    {lam : ℝ} (hlam : 0 ≤ lam) (hle : toFullBlockMat Ej ≤ lam • toFullBlockMat Ep)
    {W : CoeffSpace d → BlockMat d} (hW : ∀ a, IsSymmetricBlockMat (W a)) {Q : ℝ}
    (hQ : 0 < Q) (hWm : AEStronglyMeasurable (fun a => schattenSize Q (W a) Ep) P) :
    lqSchattenSize P Q W Ep ≤
      ENNReal.ofReal ((2 * (d : ℝ)) ^ Q⁻¹ * lam) * lqSchattenSize P Q W Ej := by
  set K : ℝ := (2 * (d : ℝ)) ^ Q⁻¹ * lam with hK
  have hK1 : (0 : ℝ) ≤ (2 * (d : ℝ)) ^ Q⁻¹ := Real.rpow_nonneg (by positivity) _
  have hK0 : (0 : ℝ) ≤ K := mul_nonneg hK1 hlam
  have hptwise : ∀ a : CoeffSpace d, ‖schattenSize Q (W a) Ep‖ ≤
      ‖(K • fun b => schattenSize Q (W b) Ej) a‖ := by
    intro a
    have hp : (0 : ℝ) ≤ schattenSize Q (W a) Ep :=
      Recurrence.zero_le_schattenNorm (isSymmetricBlockMat_normalizedBlock (hW a)) Q
    have hj : (0 : ℝ) ≤ schattenSize Q (W a) Ej :=
      Recurrence.zero_le_schattenNorm (isSymmetricBlockMat_normalizedBlock (hW a)) Q
    have h1 := PortableHistory.schattenSize_le_blockSize (X := W a) (F := Ep) (hW a) hEps hEppd hQ
    have h2 := PortableHistory.blockSize_le_mul_blockSize (hW a) hEjs hEjpd hEps hEppd hlam hle
    have h3 := PortableHistory.blockSize_le_schattenSize (hW a) hEjs hEjpd hQ
    have hle' : schattenSize Q (W a) Ep ≤ K * schattenSize Q (W a) Ej := by
      have hstep : (2 * (d : ℝ)) ^ Q⁻¹ * blockSize (W a) Ep ≤
          (2 * (d : ℝ)) ^ Q⁻¹ * (lam * schattenSize Q (W a) Ej) :=
        mul_le_mul_of_nonneg_left
          (le_trans h2 (mul_le_mul_of_nonneg_left h3 hlam)) hK1
      have hassoc : (2 * (d : ℝ)) ^ Q⁻¹ * (lam * schattenSize Q (W a) Ej) =
          K * schattenSize Q (W a) Ej := by rw [hK]; ring
      linarith only [h1, hstep, hassoc]
    simpa [Real.norm_of_nonneg hp, Real.norm_of_nonneg (mul_nonneg hK0 hj)] using hle'
  calc lqSchattenSize P Q W Ep
      ≤ eLpNorm (K • fun b => schattenSize Q (W b) Ej) (ENNReal.ofReal Q) P :=
        eLpNorm_mono hWm hptwise
    _ = ‖K‖ₑ * lqSchattenSize P Q W Ej := eLpNorm_const_smul K _ _ _
    _ = ENNReal.ofReal K * lqSchattenSize P Q W Ej := by rw [Real.enorm_eq_ofReal hK0]

/-- **The bridge normalization exchange.**  The lower bridge clause
`(1-η_x)E_t^q ≤ E_n^{q'}` of `p.two.grid.transport` transports the
fresh centred rows from the old terminal normalization to the new one at the cost
`(2d)^{1/Q}(1-η_x)^{-1}`, which on the printed box `0 ≤ η_x ≤ 1/4` is at most
`(2d)^{1/Q}·4/3`. -/
theorem lqSchattenSize_bridge_le [NeZero d] {P : Measure (CoeffSpace d)} {q q' : Mat d}
    {t n : ℤ}
    {etaX : ℝ} (heta1 : etaX < 1)
    (hEts : IsSymmetricBlockMat (adaptedMean P q t))
    (hEtpd : Book.Ch02.BlockPosDef (adaptedMean P q t))
    (hEns : IsSymmetricBlockMat (adaptedMean P q' n))
    (hEnpd : Book.Ch02.BlockPosDef (adaptedMean P q' n))
    (hlo : BlockMatLoewnerLE (blockScale (1 - etaX) (adaptedMean P q t))
      (adaptedMean P q' n))
    {W : CoeffSpace d → BlockMat d} (hW : ∀ a, IsSymmetricBlockMat (W a)) {Q : ℝ}
    (hQ : 0 < Q)
    (hWm : AEStronglyMeasurable (fun a => schattenSize Q (W a) (adaptedMean P q' n)) P) :
    lqSchattenSize P Q W (adaptedMean P q' n) ≤
      ENNReal.ofReal ((2 * (d : ℝ)) ^ Q⁻¹ * (1 - etaX)⁻¹) *
        lqSchattenSize P Q W (adaptedMean P q t) := by
  have hpos : (0 : ℝ) < 1 - etaX := by linarith only [heta1]
  have hscale : toFullBlockMat (adaptedMean P q t) ≤
      (1 - etaX)⁻¹ • toFullBlockMat (adaptedMean P q' n) := by
    have h := le_of_blockMatLoewnerLE (isSymmetricBlockMat_blockScale _ hEts) hEns hlo
    rw [toFullBlockMat_blockScale] at h
    have h' := smul_le_smul_of_le (c := (1 - etaX)⁻¹) (inv_nonneg.mpr hpos.le) h
    rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hpos), one_smul] at h'
  exact lqSchattenSize_le_of_smul_le hEts hEtpd hEns hEnpd
    (inv_nonneg.mpr hpos.le) hscale hW hQ hWm

end

end Transport
end HighContrast
end HCPolySupport
