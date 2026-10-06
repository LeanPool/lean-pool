/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Entry.StandardCellMean
public import LeanPool.HighContrastHomogenization.Provider.Entry.AdapterSeries
public import LeanPool.HighContrastHomogenization.Provider.Entry.AdapterQuadratic

/-!
# High-contrast homogenization: Provider.Entry.AdapterMajorant

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The crude majorant of the adapted-to-Euclidean comparison

The comparison between adapted and Euclidean cubes fills a target cell with the
cells of the other grid and reads the resulting rows.  The rows of a *finite*
range of scales carry the printed estimate; what remains is the tail of scales
below any cutoff, and the printed proof lets the cutoff descend.  The exhaustion
of `l.two.grid.whitney` is consumed against a majorant valid for
every partial sum, so the tail has to be paid pathwise, by an estimate that is
crude in its constant but summable in the scale.

Two ingredients do that.

*The widened cell bound.*  `e.coarse.ellipticity` discounts a standard cube
by `3^{g(m-k)}` only when the cube's centre lies in the macroscopic cube `□_m`.
The cubes of a filling lie wherever the target lies, so the bound of
`StandardCellMean` — which reads at centres in the unit cube — is widened here to
centres in `□_M` at any generation `M`: the same argument at the macroscopic
scale `max{M, k+l}` gives `𝐀(z+□_k) ≤ (1 + (3^M + 3S)3^{-k})^g𝐄`.

*The tail series.*  Weighted by the cross-grid row `3^{r-n}` that
`e.two.grid.whitney.volumes` supplies, those bounds sum below a cutoff
`J` to `2(1-g)^{-1}(3^J+3^M+3S)3^{-n}3^{J(1-g)}`, which is affine in the source
scale — so its mean is the source moment — and tends to zero as the cutoff
descends.  The cutoff is then chosen once and for all by the archimedean step on
`3^{J(1-g)}`; no limit is taken.  The printed gauge `Γ_{g,S}` is compared with
the geometric series it is built from at the end of the file.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Entry

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## A macroscopic cube containing a target cell -/

/-- **Every adapted cell sits inside a macroscopic cube.**  A translated adapted
cell is a bounded domain, and a triadic generation above its bound encloses it. -/
theorem exists_containing_centeredCube {q : Mat d} (hq : q.PosDef) (n : ℤ) (y : Vec d) :
    ∃ M : ℤ, 1 ≤ M ∧ adaptedCellTranslate q n y ⊆ centeredCube d M := by
  obtain ⟨R, hR, hRW⟩ := Transport.isBoundedDomain_adaptedCellTranslate hq n y
  obtain ⟨l, hl1, -⟩ := exists_pow_three_bracket (x := R) hR.le
  refine ⟨max 1 ((l : ℤ) + 1), le_max_left _ _, ?_⟩
  intro x hx
  rw [Recurrence.mem_centeredCube_iff]
  intro i
  have hxi : |x i| ≤ R := hRW x hx i
  have hstep : (3 : ℝ) ^ (((l : ℕ) : ℤ) + 1) ≤ (3 : ℝ) ^ (max 1 ((l : ℤ) + 1)) :=
    zpow_le_zpow_right₀ (by norm_num) (le_max_right _ _)
  have hval : (3 : ℝ) ^ (((l : ℕ) : ℤ) + 1) = 3 * (3 : ℝ) ^ ((l : ℕ) : ℤ) := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    ring
  rw [hval] at hstep
  have hpos : (0 : ℝ) < (3 : ℝ) ^ ((l : ℕ) : ℤ) := by positivity
  rw [abs_le] at hxi
  constructor <;> linarith only [hxi.1, hxi.2, hl1, hstep, hpos]

/-! ## The widened cell bound -/

/-- **The Euclidean cell bound at a centre in a macroscopic cube.**  The
random-source ellipticity of `e.coarse.ellipticity`, read at the macroscopic
generation `max{M, k+l}` where `3^l` brackets `3^{-k}S`: a standard aligned cube
whose centre lies in `□_M` is inside every macroscopic cube of generation at
least `M`, so only the fixed generation `M` — not the target's own — is paid.
The bound holds simultaneously at every cube, the ellipticity being one
almost-sure statement quantified over all of them. -/
theorem ae_coarseBlock_standardCell_le_of_mem {P : Measure (CoeffSpace d)} {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (M : ℤ) :
    ∀ᵐ a ∂P, ∀ (k : ℤ) (v : Fin d → ℤ), standardCellCenter k v ∈ centeredCube d M →
      BlockMatLoewnerLE (coarseBlock (standardCell d k v) a)
        (blockScale ((1 + ((3 : ℝ) ^ M + 3 * S a) * (3 : ℝ) ^ (-k)) ^ g) E) := by
  filter_upwards [hdag.coarse_bound] with a ha
  intro k v hv
  have hS0 : 0 ≤ S a := hdag.source_nonneg a
  have hu0 : 0 ≤ (3 : ℝ) ^ (-k) * S a := by positivity
  obtain ⟨l, hl1, hl2⟩ := exists_pow_three_bracket hu0
  set m : ℤ := max M (k + (l : ℤ)) with hmdef
  have hkm : k ≤ m := le_max_of_le_right (by omega)
  have hMm : M ≤ m := le_max_left _ _
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have hSle : S a ≤ (3 : ℝ) ^ m := by
    have hmul := mul_le_mul_of_nonneg_left hl1 h3k.le
    rw [← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), add_neg_cancel,
      zpow_zero, one_mul, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)] at hmul
    exact hmul.trans (zpow_le_zpow_right₀ (by norm_num) (le_max_right _ _))
  have hMle : (3 : ℝ) ^ M ≤ (3 : ℝ) ^ m := zpow_le_zpow_right₀ (by norm_num) hMm
  have hcenter : standardCellCenter k v ∈ centeredCube d m := by
    rw [Recurrence.mem_centeredCube_iff] at hv ⊢
    intro i
    have hi := hv i
    exact ⟨by linarith only [hi.1, hMle], by linarith only [hi.2, hMle]⟩
  have hb := ha m hSle k hkm v hcenter
  refine Persistence.blockMatLoewnerLE_blockScale_mono (isSymmetricBlockMat_coarseBlock _ a)
    hdag.refBlock_isSymm hdag.refBlock_posDef ?_ hb
  have hexp : (3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ))) = ((3 : ℝ) ^ (m - k)) ^ g := by
    rw [← Real.rpow_intCast (3 : ℝ) (m - k), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    push_cast
    ring_nf
  rw [hexp]
  refine Real.rpow_le_rpow (by positivity) ?_ hdag.g_mem.1
  have hsplit : (3 : ℝ) ^ (m - k) ≤ (3 : ℝ) ^ (M - k) + (3 : ℝ) ^ ((l : ℕ) : ℤ) := by
    rcases max_cases M (k + (l : ℤ)) with ⟨hm, -⟩ | ⟨hm, -⟩
    · rw [hmdef, hm]
      have : (0 : ℝ) < (3 : ℝ) ^ ((l : ℕ) : ℤ) := by positivity
      linarith only [this]
    · rw [hmdef, hm, show k + (l : ℤ) - k = ((l : ℕ) : ℤ) by ring]
      have : (0 : ℝ) < (3 : ℝ) ^ (M - k) := by positivity
      linarith only [this]
  have hMsub : (3 : ℝ) ^ (M - k) = (3 : ℝ) ^ M * (3 : ℝ) ^ (-k) := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), sub_eq_add_neg]
  rw [hMsub] at hsplit
  have hexpand : 1 + ((3 : ℝ) ^ M + 3 * S a) * (3 : ℝ) ^ (-k)
      = (3 : ℝ) ^ M * (3 : ℝ) ^ (-k) + (1 + 3 * ((3 : ℝ) ^ (-k) * S a)) := by ring
  rw [hexpand]
  linarith only [hsplit, hl2]

/-- The same bound for cubes contained in the macroscopic cube: a cube contains
its own centre. -/
theorem ae_coarseBlock_standardCell_le_of_subset {P : Measure (CoeffSpace d)} {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (M : ℤ) :
    ∀ᵐ a ∂P, ∀ (k : ℤ) (v : Fin d → ℤ), standardCell d k v ⊆ centeredCube d M →
      BlockMatLoewnerLE (coarseBlock (standardCell d k v) a)
        (blockScale ((1 + ((3 : ℝ) ^ M + 3 * S a) * (3 : ℝ) ^ (-k)) ^ g) E) := by
  filter_upwards [ae_coarseBlock_standardCell_le_of_mem hdag M] with a ha
  exact fun k v hv => ha k v (hv (Recurrence.standardCellCenter_mem_standardCell k v))

/-! ## The tail of the cross-grid series -/

/-- The cross-grid row weight against the widened cell bound, in real powers. -/
theorem zpow_mul_rpow_neg (n r : ℤ) (g : ℝ) :
    (3 : ℝ) ^ (r - n) * ((3 : ℝ) ^ (-r)) ^ g
      = (3 : ℝ) ^ (-n) * (3 : ℝ) ^ ((r : ℝ) * (1 - g)) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [← Real.rpow_intCast (3 : ℝ) (r - n), ← Real.rpow_intCast (3 : ℝ) (-r),
    ← Real.rpow_intCast (3 : ℝ) (-n), ← Real.rpow_mul h3.le, ← Real.rpow_add h3,
    ← Real.rpow_add h3]
  congr 1
  push_cast
  ring

/-- **The crude tail of the cross-grid series.**  Below a cutoff `J ≤ 0` the
widened cell bounds, weighted by the cross-grid row `3^{r-n}`, total at most an
affine function of the source scale times `3^{-n}3^{J(1-g)}`; the bound does not
depend on the lower end of the sum, and the last factor tends to zero as the
cutoff descends. -/
theorem sum_crude_below_le {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1) {M : ℤ} (hM : 0 ≤ M) {s : ℝ}
    (hs : 0 ≤ s) (n J J' : ℤ) :
    ∑ r ∈ Finset.Ico J' J, (3 : ℝ) ^ (r - n) * (1 + ((3 : ℝ) ^ M + 3 * s) * (3 : ℝ) ^ (-r)) ^ g ≤
      2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * s) *
        ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))) := by
  have hg1' : (0 : ℝ) < 1 - g := by linarith only [hg1]
  have hM1 : (1 : ℝ) ≤ (3 : ℝ) ^ M := by
    have := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hM
    rwa [zpow_zero] at this
  have hbase : (1 : ℝ) ≤ (3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * s := by
    have h1 : (0 : ℝ) < (3 : ℝ) ^ J := by positivity
    linarith only [h1, hs, hM1]
  have hterm : ∀ r ∈ Finset.Ico J' J,
      (3 : ℝ) ^ (r - n) * (1 + ((3 : ℝ) ^ M + 3 * s) * (3 : ℝ) ^ (-r)) ^ g ≤
        ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * s) *
          ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)) *
            (3 : ℝ) ^ (-(1 - g) * ((J : ℝ) - (r : ℝ)))) := by
    intro r hr
    have hrJ : r < J := (Finset.mem_Ico.mp hr).2
    have h3r : (0 : ℝ) < (3 : ℝ) ^ (-r) := by positivity
    have hrJle : (3 : ℝ) ^ r ≤ (3 : ℝ) ^ J :=
      zpow_le_zpow_right₀ (by norm_num) (le_of_lt hrJ)
    have hcancel : (3 : ℝ) ^ (-r) * (3 : ℝ) ^ r = 1 := by
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), neg_add_cancel, zpow_zero]
    have hin : 1 + ((3 : ℝ) ^ M + 3 * s) * (3 : ℝ) ^ (-r) ≤
        (3 : ℝ) ^ (-r) * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * s) := by
      nlinarith only [h3r, hrJle, hcancel]
    have hpow : (1 + ((3 : ℝ) ^ M + 3 * s) * (3 : ℝ) ^ (-r)) ^ g ≤
        ((3 : ℝ) ^ (-r)) ^ g * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * s) := by
      refine le_trans (Real.rpow_le_rpow (by positivity) hin hg0) ?_
      rw [Real.mul_rpow (by positivity) (by linarith only [hbase])]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) g)
      have := Real.rpow_le_rpow_of_exponent_le hbase hg1.le
      rwa [Real.rpow_one] at this
    have hmul := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (r - n))
    refine hmul.trans (le_of_eq ?_)
    have hsplit : (3 : ℝ) ^ ((r : ℝ) * (1 - g))
        = (3 : ℝ) ^ ((J : ℝ) * (1 - g)) * (3 : ℝ) ^ (-(1 - g) * ((J : ℝ) - (r : ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    rw [← mul_assoc, zpow_mul_rpow_neg, hsplit]
    ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hser := Transport.sum_geom_below_le hg1' J (Finset.Ico J' J)
    fun r hr => le_of_lt (Finset.mem_Ico.mp hr).2
  have hz : (1 : ℝ) / (1 - (3 : ℝ) ^ (-(1 - g))) = zetaG g := by rw [zetaG, one_div]
  rw [hz] at hser
  have hzeta := zetaG_le_two_div hg0 hg1
  have hfac : (0 : ℝ) ≤ ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * s) *
      ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))) := by positivity
  have hstep := mul_le_mul_of_nonneg_left (hser.trans hzeta) hfac
  calc ∑ r ∈ Finset.Ico J' J, ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * s) *
          ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)) *
            (3 : ℝ) ^ (-(1 - g) * ((J : ℝ) - (r : ℝ))))
      = ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * s) *
            ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))) *
          ∑ r ∈ Finset.Ico J' J, (3 : ℝ) ^ (-(1 - g) * ((J : ℝ) - (r : ℝ))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by ring
    _ ≤ ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * s) *
            ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))) * (2 / (1 - g)) := hstep
    _ = 2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * s) *
          ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))) := by
        rw [div_eq_inv_mul]
        ring

/-- `3^{-n}3^{n(1-g)}` is the real power `(3^{-n})^g`. -/
theorem zpow_neg_mul_rpow (n : ℤ) (g : ℝ) :
    (3 : ℝ) ^ (-n) * (3 : ℝ) ^ ((n : ℝ) * (1 - g)) = ((3 : ℝ) ^ (-n)) ^ g := by
  rw [← Real.rpow_intCast (3 : ℝ) (-n), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  push_cast
  ring

/-- **The crude tail of the cross-grid series in the adapted regime.**  The
weights `3^{r-m}` against the real powers `(3^{-r})^g` total, below a cutoff, at
most `2(1-g)^{-1}3^{-m}3^{J(1-g)}`, uniformly in the lower end of the sum. -/
theorem sum_crude_zpow_below_le {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1) (m J J' : ℤ) :
    ∑ r ∈ Finset.Ico J' J, (3 : ℝ) ^ (r - m) * ((3 : ℝ) ^ (-r)) ^ g ≤
      2 * (1 - g)⁻¹ * ((3 : ℝ) ^ (-m) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))) := by
  have hg1' : (0 : ℝ) < 1 - g := by linarith only [hg1]
  have hterm : ∀ r ∈ Finset.Ico J' J,
      (3 : ℝ) ^ (r - m) * ((3 : ℝ) ^ (-r)) ^ g
        = (3 : ℝ) ^ (-m) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)) *
          (3 : ℝ) ^ (-(1 - g) * ((J : ℝ) - (r : ℝ))) := by
    intro r _
    rw [zpow_mul_rpow_neg]
    have hsplit : (3 : ℝ) ^ ((r : ℝ) * (1 - g))
        = (3 : ℝ) ^ ((J : ℝ) * (1 - g)) * (3 : ℝ) ^ (-(1 - g) * ((J : ℝ) - (r : ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    rw [hsplit, mul_assoc]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hser := Transport.sum_geom_below_le hg1' J (Finset.Ico J' J)
    fun r hr => le_of_lt (Finset.mem_Ico.mp hr).2
  have hz : (1 : ℝ) / (1 - (3 : ℝ) ^ (-(1 - g))) = zetaG g := by rw [zetaG, one_div]
  rw [hz] at hser
  have hzeta := zetaG_le_two_div hg0 hg1
  have hfac : (0 : ℝ) ≤ (3 : ℝ) ^ (-m) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)) := by positivity
  have hstep := mul_le_mul_of_nonneg_left (hser.trans hzeta) hfac
  refine hstep.trans (le_of_eq ?_)
  rw [div_eq_inv_mul]
  ring

/-! ## The archimedean choice of cutoff -/

/-- **The cutoff of the tail, chosen explicitly.**  For every positive tolerance
there is a cutoff below both zero and a prescribed generation at which the tail
factor `3^{J(1-g)}` is under the tolerance; no limit is taken. -/
theorem exists_tail_cutoff {g : ℝ} (hg1 : g < 1) {eps : ℝ} (heps : 0 < eps) (k : ℤ) :
    ∃ J : ℤ, J ≤ 0 ∧ J ≤ k ∧ (3 : ℝ) ^ ((J : ℝ) * (1 - g)) ≤ eps := by
  have hg1' : (0 : ℝ) < 1 - g := by linarith only [hg1]
  have hb1 : (3 : ℝ) ^ (-(1 - g)) < 1 := by
    have h := Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ)) (by norm_num)
      (by linarith only [hg1'] : -(1 - g) < 0)
    exact h
  have hb0 : (0 : ℝ) < (3 : ℝ) ^ (-(1 - g)) := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one heps hb1
  refine ⟨min 0 (min k (-(N : ℤ))), min_le_left _ _, le_trans (min_le_right _ _) (min_le_left _ _),
    ?_⟩
  set J : ℤ := min 0 (min k (-(N : ℤ))) with hJdef
  have hJN : J ≤ -(N : ℤ) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hJNR : (J : ℝ) ≤ -(N : ℝ) := by exact_mod_cast hJN
  have hmono : (3 : ℝ) ^ ((J : ℝ) * (1 - g)) ≤ (3 : ℝ) ^ ((-(N : ℝ)) * (1 - g)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right hJNR hg1'.le)
  refine hmono.trans (le_of_lt (lt_of_le_of_lt (le_of_eq ?_) hN))
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 - g))) N, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- **The cutoff chosen against a prescribed bound.**  For every positive bound
there is a cutoff below both zero and a prescribed generation at which a
prescribed multiple of the tail factor is under the bound. -/
theorem exists_cutoff_mul_le {g : ℝ} (hg1 : g < 1) (U : ℝ) {V : ℝ} (hV : 0 < V) (k : ℤ) :
    ∃ J : ℤ, J ≤ 0 ∧ J ≤ k ∧ U * (3 : ℝ) ^ ((J : ℝ) * (1 - g)) ≤ V := by
  obtain ⟨J, hJ0, hJk, hJeps⟩ := exists_tail_cutoff hg1 (eps := V / (|U| + 1)) (by positivity) k
  refine ⟨J, hJ0, hJk, ?_⟩
  have hpow : (0 : ℝ) < (3 : ℝ) ^ ((J : ℝ) * (1 - g)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hU : U ≤ |U| := le_abs_self U
  have habs : (0 : ℝ) < |U| + 1 := by positivity
  have h1 : (|U| + 1) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)) ≤ V := by
    have hmul := mul_le_mul_of_nonneg_left hJeps habs.le
    rwa [mul_div_cancel₀ _ habs.ne'] at hmul
  nlinarith only [h1, hU, hpow]

/-! ## The printed gauge against the geometric series -/

/-- The printed gauge `Γ_{g,S}` is at least one. -/
theorem one_le_transferGauge {g K : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1) (k : ℤ) :
    1 ≤ transferGauge g K k := by
  have hgpos : (0 : ℝ) < 1 - g := by linarith only [hg1]
  have hbase : (1 : ℝ) ≤ 1 + K ^ 2 * (3 : ℝ) ^ (-k) := by
    have h1 : (0 : ℝ) ≤ K ^ 2 * (3 : ℝ) ^ (-k) := by positivity
    linarith only [h1]
  have hpow : (1 : ℝ) ≤ (1 + K ^ 2 * (3 : ℝ) ^ (-k)) ^ g := Real.one_le_rpow hbase hg0
  have hinv : (1 : ℝ) ≤ (1 - g)⁻¹ := by
    rw [le_inv_comm₀ one_pos hgpos]
    linarith only [hg0]
  rw [transferGauge]
  nlinarith only [hpow, hinv]

/-- The printed gauge dominates the geometric series it is built from. -/
theorem inv_le_transferGauge {g K : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1) (k : ℤ) :
    (1 - g)⁻¹ ≤ transferGauge g K k := by
  have hgpos : (0 : ℝ) < 1 - g := by linarith only [hg1]
  have hinv0 : (0 : ℝ) ≤ (1 - g)⁻¹ := inv_nonneg.mpr hgpos.le
  have hbase : (1 : ℝ) ≤ 1 + K ^ 2 * (3 : ℝ) ^ (-k) := by
    have h1 : (0 : ℝ) ≤ K ^ 2 * (3 : ℝ) ^ (-k) := by positivity
    linarith only [h1]
  have hpow : (1 : ℝ) ≤ (1 + K ^ 2 * (3 : ℝ) ^ (-k)) ^ g := Real.one_le_rpow hbase hg0
  have hmul := mul_le_mul_of_nonneg_left hpow hinv0
  rw [transferGauge]
  rwa [mul_one] at hmul

end

end Entry
end HighContrast
end HCPolySupport
