/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRowEnvelope

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastRowCapIsotropy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The split primal row cap

The row is split at a scale `k₀`:

* **above the split** the cells are charged to the isotropy comparison, at
  the *constant* envelope `1 + cIso`.  The raw row weight `3^{(3/2)(k-s)}` is
  then summed on its own, at ratio `3^{-3/2}` — no `g` is consumed, because the
  envelope no longer grows with depth;
* **below the split** the cells are charged to the coarse ellipticity envelope;
  `g` of the weight's `3/2` is consumed by the envelope's
  growth and the residual ratio is `3^{-(3/2-g)}`, summable for every `g < 3/2`
  and so on the whole frozen range.  The deep leg carries the extra factor
  `3^{(3/2-g)((k₀-1)-s)}`, which is the `tiltGap`-shaped discount: it can be made
  smaller than any prescribed tolerance by taking `s - k₀` past a threshold
  logarithmic in `boundaryConst·3^{gG}`.

The per-cell argument is identical in the two regions and is factored out as
`row_term_le` at an abstract cell envelope.

The isotropy hypothesis is stated as the family it is used as; its producer is
`annealedBlock_adaptedCellAt_le_isotropy`, which supplies
exactly this shape uniformly in the aligned index.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- The parametric geometric row sum, at an arbitrary base. -/
private theorem sum_geom_Icc_le_base {a : ℝ} (ha : 0 < a) (Klo b : ℤ) :
    ∑ k ∈ Finset.Icc Klo b, (3 : ℝ) ^ (a * ((k : ℝ) - (b : ℝ))) ≤
      1 / (1 - (3 : ℝ) ^ (-a)) := by
  have hset : Finset.Icc Klo b = Finset.Ico Klo (b + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hbase := PortableHistory.sum_geom_Ico_le (a := a) ha Klo (b + 1)
  rw [hset]
  refine le_trans (le_of_eq ?_) hbase
  refine Finset.sum_congr rfl ?_
  intro k _hk
  congr 1
  push_cast
  ring

private theorem blockQuad_nonneg' {H : BlockMat d} (hpos : BlockPosDef H)
    (X : BlockVec d) : 0 ≤ blockVecDot X (blockMatVecMul H X) := by
  by_cases hX : X = 0
  · subst X
    simp [blockMatVecMul, blockVecDot, vecDot]
  · exact (hpos X hX).le

/-- The per-scale row term at an abstract cell envelope.  The argument bounds
the Schur load by twice the quadratic load and then applies the
congruence transport — with the envelope left abstract, so that the two regions
of the split can share it. -/
private theorem row_term_le {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {E : BlockMat d} {q : Mat d} (hq : q.PosDef)
    (hposE : BlockPosDef E)
    {h0 : Mat d} {Pcen Qcen : Vec d} {k s : ℤ} {ck : ℝ} (hck0 : 0 ≤ ck)
    (hint : ∀ w ∈ Response.alignedIndex q k s,
      HasIntegrableCoarseBlock P (adaptedCellAt q k w))
    (henv : ∀ w ∈ Response.alignedIndex q k s,
      BlockMatLoewnerLE (annealedBlock P (adaptedCellAt q k w))
        (blockScale ck E)) :
    Response.profileRowWeight k s *
        Response.avsum (Response.alignedIndex q k s) (fun w =>
          Response.profileSchurLoad
            (Response.profileHattedBlock h0
              (annealedBlock P (adaptedCellAt q k w))) Pcen Qcen) ≤
      Response.profileRowWeight k s *
        (2 * ck * Response.profileQuadraticLoad (Response.profileHattedBlock h0 E)
          Pcen Qcen) := by
  have hw : ∀ w ∈ Response.alignedIndex q k s,
      Response.profileSchurLoad
        (Response.profileHattedBlock h0
          (annealedBlock P (adaptedCellAt q k w))) Pcen Qcen ≤
      2 * ck * Response.profileQuadraticLoad (Response.profileHattedBlock h0 E)
        Pcen Qcen := by
    intro w hwmem
    have hposcell : BlockPosDef (annealedBlock P (adaptedCellAt q k w)) :=
      blockPosDef_annealedBlock (hint w hwmem)
        (fun a => Recurrence.blockPosDef_coarseBlock_adaptedCellAt hq k w a)
    have hsymcell : IsSymmetricBlockMat (annealedBlock P (adaptedCellAt q k w)) :=
      Recurrence.isSymmetricBlockMat_annealedBlock P _
    have hschur := Response.profileSchurLoad_le_two_mul_profileQuadraticLoad
      (H := Response.profileHattedBlock h0 (annealedBlock P (adaptedCellAt q k w)))
      (by
        rw [Response.profileHattedBlock]
        exact Response.isSymmetricBlockMat_skewBlockCongr (g := h0) hsymcell)
      (by
        rw [Response.profileHattedBlock]
        exact Response.blockPosDef_skewBlockCongr (g := h0) hposcell)
      Pcen Qcen
    refine le_trans hschur ?_
    have hone : ∀ X : BlockVec d,
        blockVecDot X (blockMatVecMul
          (Response.profileHattedBlock h0
            (annealedBlock P (adaptedCellAt q k w))) X) ≤
        ck * blockVecDot X (blockMatVecMul (Response.profileHattedBlock h0 E) X) := by
      intro X
      rw [Response.profileHattedBlock, Response.profileHattedBlock,
        Response.blockQuadratic_skewBlockCongr, Response.blockQuadratic_skewBlockCongr]
      have hcell := henv w hwmem (X.1, matVecMul h0 X.1 + X.2)
      rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at hcell
      linarith only [hcell]
    have hquad : Response.profileQuadraticLoad
        (Response.profileHattedBlock h0
          (annealedBlock P (adaptedCellAt q k w))) Pcen Qcen ≤
        ck * Response.profileQuadraticLoad (Response.profileHattedBlock h0 E) Pcen Qcen := by
      rw [Response.profileQuadraticLoad, Response.profileQuadraticLoad, mul_add]
      exact add_le_add (hone _) (hone _)
    calc
      2 * Response.profileQuadraticLoad
          (Response.profileHattedBlock h0
            (annealedBlock P (adaptedCellAt q k w))) Pcen Qcen ≤
          2 * (ck * Response.profileQuadraticLoad
            (Response.profileHattedBlock h0 E) Pcen Qcen) := by
        linarith only [hquad]
      _ = 2 * ck * Response.profileQuadraticLoad
          (Response.profileHattedBlock h0 E) Pcen Qcen := by ring
  have hweight0 : 0 ≤ Response.profileRowWeight k s :=
    (Response.profileRowWeight_pos k s).le
  refine mul_le_mul_of_nonneg_left ?_ hweight0
  refine le_trans (Response.avsum_le_avsum hw) ?_
  rcases Finset.eq_empty_or_nonempty (Response.alignedIndex q k s) with hEm | hNE
  · rw [hEm, Response.avsum]
    simp only [Finset.card_empty, Finset.sum_empty, mul_zero]
    have hL : 0 ≤ Response.profileQuadraticLoad (Response.profileHattedBlock h0 E)
        Pcen Qcen := by
      rw [Response.profileQuadraticLoad]
      have hhat : BlockPosDef (Response.profileHattedBlock h0 E) := by
        rw [Response.profileHattedBlock]
        exact Response.blockPosDef_skewBlockCongr (g := h0) hposE
      exact add_nonneg (blockQuad_nonneg' hhat _) (blockQuad_nonneg' hhat _)
    positivity
  · exact le_of_eq (Response.avsum_const hNE _)

/-! ## The split row cap -/

/-- **The split row cap (primal).**  Above the split scale `k₀` the cells are
charged to the isotropy envelope `1 + cIso` against the raw weight, at ratio
`3^{-3/2}`; below it they use the coarse ellipticity envelope at ratio
`3^{-(3/2-g)}`, and the deep leg carries the discount
`3^{(3/2-g)((k₀-1)-s)}`.

The first summand of the conclusion is `Π`-free.  The second retains
`boundaryConst·3^{g((t+G)-s)}`, multiplied by a factor that the gap `s - k₀`
drives below any prescribed tolerance. -/
theorem profilePrimalHattedEarlierRow_le_isotropy_split [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {n : Mat d} (hn : n.PosDef)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    (t : ℤ) {G : ℕ} (hDelta : 0 ≤ t + (G : ℤ) - 1 - sK)
    (hentry : sourceMomentTwo K ≤ (3 : ℝ) ^ (t + (G : ℤ) - sK))
    {s : ℤ} (hst : s ≤ t)
    (hgeom : ∀ k : ℤ, k ≤ s →
      ∀ w ∈ Response.alignedIndex (roundedGrid l n) k s,
        adaptedCellAt (roundedGrid l n) k w ⊆ centeredCube d (t + (G : ℤ)))
    {k0 : ℤ} {cIso : ℝ} (hcIso : 0 ≤ cIso)
    (hiso : ∀ k : ℤ, k0 ≤ k → k ≤ s →
      ∀ w ∈ Response.alignedIndex (roundedGrid l n) k s,
        BlockMatLoewnerLE (annealedBlock P (adaptedCellAt (roundedGrid l n) k w))
          (blockScale (1 + cIso) E))
    (h0 : Mat d) (Pcen Qcen : Vec d) :
    Response.profilePrimalHattedEarlierRow P (roundedGrid l n) h0 s Pcen Qcen ≤
      ENNReal.ofReal
        (2 * (1 + cIso) * (1 / (1 - (3 : ℝ) ^ (-(3 / 2 : ℝ)))) *
            Response.profileQuadraticLoad (Response.profileHattedBlock h0 E) Pcen Qcen +
          2 * (2 * boundaryConst Cd g n *
              (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (s : ℝ)))) *
            ((3 : ℝ) ^ ((3 / 2 - g) * (((k0 - 1 : ℤ) : ℝ) - (s : ℝ))) *
              (1 / (1 - (3 : ℝ) ^ (-(3 / 2 - g))))) *
            Response.profileQuadraticLoad (Response.profileHattedBlock h0 E) Pcen Qcen) := by
  classical
  set q : Mat d := roundedGrid l n with hqdef
  have hq : q.PosDef := Recurrence.posDef_roundedGrid hl hn
  have hCd1 : (1 : ℝ) ≤ Cd := (le_max_left _ _).trans hCd
  have hbC0 : 0 < boundaryConst Cd g n :=
    Transport.zero_lt_boundaryConst (by linarith only [hCd1]) hg.2 hn
  have hEhatpos : BlockPosDef (Response.profileHattedBlock h0 E) := by
    rw [Response.profileHattedBlock]
    exact Response.blockPosDef_skewBlockCongr (g := h0) hdag.refBlock_posDef
  set L : ℝ := Response.profileQuadraticLoad (Response.profileHattedBlock h0 E) Pcen Qcen
    with hLdef
  have hL0 : 0 ≤ L := by
    rw [hLdef, Response.profileQuadraticLoad]
    exact add_nonneg (blockQuad_nonneg' hEhatpos _) (blockQuad_nonneg' hEhatpos _)
  set cDeepBase : ℝ := 2 * boundaryConst Cd g n *
    (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (s : ℝ))) with hcDeep
  have hcDeep0 : 0 ≤ cDeepBase := by
    rw [hcDeep]
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (s : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hb := hbC0.le
    positivity
  have hrateD : (0 : ℝ) < 3 / 2 - g := by linarith only [hg.2]
  refine iSup_le fun Klo => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Response.profilePrimalHattedRowPartial]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc Klo s)
    (fun k => k ≤ k0 - 1), add_comm]
  refine add_le_add ?_ ?_
  · -- the shallow leg, at the constant isotropy envelope
    have hbound : ∀ k ∈ (Finset.Icc Klo s).filter (fun k => ¬ k ≤ k0 - 1),
        Response.profileRowWeight k s *
            Response.avsum (Response.alignedIndex q k s) (fun w =>
              Response.profileSchurLoad
                (Response.profileHattedBlock h0
                  (annealedBlock P (adaptedCellAt q k w))) Pcen Qcen) ≤
          (3 : ℝ) ^ (3 / 2 * ((k : ℝ) - (s : ℝ))) * (2 * (1 + cIso) * L) := by
      intro k hkmem
      simp only [Finset.mem_filter, Finset.mem_Icc, not_le] at hkmem
      obtain ⟨⟨_hKlo, hks⟩, hk0k⟩ := hkmem
      have hk0k' : k0 ≤ k := by omega
      have hint : ∀ w ∈ Response.alignedIndex q k s,
          HasIntegrableCoarseBlock P (adaptedCellAt q k w) := fun w hwmem =>
        Response.FixedGrid.alignedCellsIntegrable_of_dagger hdag hq s t hks hst
          (Or.inl rfl) hwmem
      have hterm := row_term_le (E := E) hq hdag.refBlock_posDef
        (h0 := h0) (Pcen := Pcen) (Qcen := Qcen)
        (by linarith only [hcIso] : (0 : ℝ) ≤ 1 + cIso) hint
        (fun w hwmem => hiso k hk0k' hks w hwmem)
      refine le_trans hterm (le_of_eq ?_)
      rw [Response.profileRowWeight]
    refine le_trans (Finset.sum_le_sum hbound) ?_
    rw [← Finset.sum_mul]
    have hsub : (Finset.Icc Klo s).filter (fun k => ¬ k ≤ k0 - 1) ⊆
        Finset.Icc Klo s := Finset.filter_subset _ _
    have hsum : ∑ k ∈ (Finset.Icc Klo s).filter (fun k => ¬ k ≤ k0 - 1),
        (3 : ℝ) ^ (3 / 2 * ((k : ℝ) - (s : ℝ))) ≤
        1 / (1 - (3 : ℝ) ^ (-(3 / 2 : ℝ))) := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
      · intro k _ _
        exact Real.rpow_nonneg (by norm_num) _
      · exact sum_geom_Icc_le_base (by norm_num) Klo s
    refine le_trans (mul_le_mul_of_nonneg_right hsum ?_) (le_of_eq ?_)
    · have h1 : (0 : ℝ) ≤ 1 + cIso := by linarith only [hcIso]
      positivity
    · ring
  · -- the deep leg, at the Dagger envelope, with its geometric discount
    have hbound : ∀ k ∈ (Finset.Icc Klo s).filter (fun k => k ≤ k0 - 1),
        Response.profileRowWeight k s *
            Response.avsum (Response.alignedIndex q k s) (fun w =>
              Response.profileSchurLoad
                (Response.profileHattedBlock h0
                  (annealedBlock P (adaptedCellAt q k w))) Pcen Qcen) ≤
          (3 : ℝ) ^ ((3 / 2 - g) * ((k : ℝ) - (s : ℝ))) * (2 * cDeepBase * L) := by
      intro k hkmem
      simp only [Finset.mem_filter, Finset.mem_Icc] at hkmem
      obtain ⟨⟨_hKlo, hks⟩, _hkk0⟩ := hkmem
      have hint : ∀ w ∈ Response.alignedIndex q k s,
          HasIntegrableCoarseBlock P (adaptedCellAt q k w) := fun w hwmem =>
        Response.FixedGrid.alignedCellsIntegrable_of_dagger hdag hq s t hks hst
          (Or.inl rfl) hwmem
      have hck0 : (0 : ℝ) ≤ 2 * boundaryConst Cd g n *
          (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ))) := by
        have h3 : (0 : ℝ) ≤
            (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ))) :=
          Real.rpow_nonneg (by norm_num) _
        have hb := hbC0.le
        positivity
      have henv : ∀ w ∈ Response.alignedIndex q k s,
          BlockMatLoewnerLE (annealedBlock P (adaptedCellAt q k w))
            (blockScale (2 * boundaryConst Cd g n *
              (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ)))) E) := by
        intro w hwmem
        exact annealedBlock_adaptedCell_le_scaled_entry hd hg hdag hl hCd hn hsK
          t hDelta hentry (hgeom k hks w hwmem) (hint w hwmem)
      have hterm := row_term_le (E := E) hq hdag.refBlock_posDef
        (h0 := h0) (Pcen := Pcen) (Qcen := Qcen) hck0 hint henv
      refine le_trans hterm (le_of_eq ?_)
      rw [Response.profileRowWeight, hcDeep]
      have hkey := rowWeight_mul_envelope g (k : ℝ) (s : ℝ)
        (((t + (G : ℤ) : ℤ) : ℝ))
      linear_combination (4 * boundaryConst Cd g n * L) * hkey
    refine le_trans (Finset.sum_le_sum hbound) ?_
    rw [← Finset.sum_mul]
    have hsubD : (Finset.Icc Klo s).filter (fun k => k ≤ k0 - 1) ⊆
        Finset.Icc Klo (k0 - 1) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
      omega
    have hsum : ∑ k ∈ (Finset.Icc Klo s).filter (fun k => k ≤ k0 - 1),
        (3 : ℝ) ^ ((3 / 2 - g) * ((k : ℝ) - (s : ℝ))) ≤
        (3 : ℝ) ^ ((3 / 2 - g) * (((k0 - 1 : ℤ) : ℝ) - (s : ℝ))) *
          (1 / (1 - (3 : ℝ) ^ (-(3 / 2 - g)))) := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubD ?_) ?_
      · intro k _ _
        exact Real.rpow_nonneg (by norm_num) _
      have hfac : ∀ k : ℤ,
          (3 : ℝ) ^ ((3 / 2 - g) * ((k : ℝ) - (s : ℝ))) =
            (3 : ℝ) ^ ((3 / 2 - g) * (((k0 - 1 : ℤ) : ℝ) - (s : ℝ))) *
              (3 : ℝ) ^ ((3 / 2 - g) * ((k : ℝ) - ((k0 - 1 : ℤ) : ℝ))) := by
        intro k
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 1
        ring
      rw [Finset.sum_congr rfl (fun k _ => hfac k), ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
      exact sum_geom_Icc_le_base hrateD Klo (k0 - 1)
    refine le_trans (mul_le_mul_of_nonneg_right hsum ?_) (le_of_eq ?_)
    · positivity
    · ring

end

end HCPolySupport.HighContrast.Quenched
