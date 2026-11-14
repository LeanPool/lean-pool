/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ArithmeticHeights.AdaptedBasis
public import LeanPool.CCDN.ArithmeticHeights.QuotientFubini
public import LeanPool.CCDN.ArithmeticHeights.SuccessiveMinima
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Disintegration
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Minkowski's second theorem

For a lattice `L` in a finite-dimensional real normed space `E` of dimension `n` and a symmetric
convex body `B`, Minkowski's second theorem is the pair of inequalities

```text
2 ^ n / n !  *  covolume L  ≤  (∏ i < n, λ i) * volume B  ≤  2 ^ n * covolume L,
```

with `λ i` the successive minima of Layer 4.1. This file proves both, and the two pieces of
Cassels' route that are statements in their own right.

## Main results

* `ZLattice.covolume_le_prod_successiveMinimum_mul_measure`: the lower bound. The independent
  lattice vectors realizing the minima, divided by their minima, span a cross-polytope inside `B`
  of volume `2 ^ n / n !` times the covolume of the lattice they generate, divided by `∏ i, λ i`;
  and that covolume is a positive integer multiple of the covolume of `L`.
* `ZLattice.prod_successiveMinimum_mul_measure_le`: the upper bound, the substantial half — the
  direction Layer 5 and 6.3 consume. Weyl's proof, through Cassels' Theorem IV, which is
  `ZLattice.pow_mul_measure_inter_add_le` of `ArithmeticHeights/QuotientFubini.lean`: the measure
  of the image of the open dilate `{gauge B < t}` in `E ⧸ L` is scaled up one minimum at a time,
  from `t = λ 0 / 2` — where the dilate injects into the quotient — to `t = λ (n - 1) / 2`, where
  it is bounded by the covolume.
* `ZLattice.pow_successiveMinimum_zero_mul_measure_le`: `λ 0 ^ n * volume B ≤ 2 ^ n * covolume L`,
  which is Minkowski's first theorem read homogeneously. It is the upper bound with `∏ i < n, λ i`
  weakened to `λ 0 ^ n`, and it is everything the first theorem gives.
* `ZLattice.exists_basis_mem_span_int_of_gauge_lt`: Cassels' Chapter VIII, Lemma 2 — a `ℤ`-basis
  of `L` against which every lattice point of gauge below the `j`-th minimum is an *integer*
  combination of the first `j` members. Layer 4.6 consumes it; the upper bound below does not.

## Implementation notes

⚠ **The reduction that would make the upper bound easy is false.** The worked example at the end
of this file machine-checks that shrinking one coordinate of a symmetric convex body can leave the
body. The linear map sending the realizing vector `v i` to `(λ i / λ (n - 1)) • v i` has
determinant `∏ λ i / λ (n - 1) ^ n` and nondecreasing coordinate factors in `(0, 1]`, which is
exactly the shape that example refutes: such a map need not send the body into itself, so the
upper bound is not the statement that some one set is a packing, and no rescaling of the body
makes it one. Weyl's proof replaces the set inclusion by a measure estimate in the quotient
`E ⧸ L`, and is a genuinely different argument.

⚠ **Neither inequality needs the body closed, bounded away from nothing, or compact.** The lower
bound uses the vectors through `gauge B (v i) = λ i` and meets the body through
`mem_smul_of_gauge_lt`, the half of the gauge dictionary that holds for any body. The upper bound
is chained on the *open* dilates `{gauge B < t}`, which is what lets the separation hypothesis of
Cassels' Theorem IV hold at `2 t = λ J` rather than only below it; the body and its interior have
the same measure because a convex set has null frontier. Only
`ZLattice.pow_successiveMinimum_zero_mul_measure_le` carries `IsCompact B`, and only because
Mathlib's form of Minkowski's first theorem does.

⚠ **Cassels' Lemma 2 is not on the path to the upper bound.** He needs the adapted basis because
he works in coordinates, where the integrality of the first `J` coordinates is how one sees that
the translation stays inside the sublattice. Coordinate-free the sublattice
`L ∩ span (v 0, …, v (J - 1))` is at hand, and the only thing the estimate wants of it is its
`ℤ`-rank, which is the `ℝ`-dimension of its span by `ZLattice.finrank_int_eq_finrank_real`. The
lemma stays in this file because Layer 4.6 does want the basis.

## References

J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer (1959), Chapter VIII §4,
Theorem V: both inequalities, as (12) and (13) of VIII.1. The lower bound is the cross-polytope
computation on p. 218; `pow_successiveMinimum_zero_mul_measure_le` is the inequality (11) there;
the upper bound is Weyl's argument of §4.2, whose kernel is Cassels' Theorem IV.
E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Appendix C.2.

This is Layer 4.2 of the `ArithmeticHeights` roadmap.
-/

public section

open Metric Module MeasureTheory Set

open scoped ENNReal Pointwise Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E}

namespace ZLattice

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {L : Submodule ℤ E}

/-! ### The lower bound -/

/-- The cross-polytope on a basis: the points whose coordinates have `ℓ¹`-norm less than one. -/
private def crossPolytope {n : ℕ} (b : Basis (Fin n) ℝ E) : Set E :=
  b.equivFun ⁻¹' {x : Fin n → ℝ | ∑ i, |x i| < 1}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The cross-polytope on a basis of vectors of gauge one lies inside the body. This is where the
gauge dictionary is used, in the half that needs no closedness. -/
private theorem crossPolytope_subset {n : ℕ} (b : Basis (Fin n) ℝ E) (hB₀ : Convex ℝ B)
    (h₀ : B ∈ 𝓝 (0 : E)) (hB₁ : ∀ x ∈ B, -x ∈ B) (hb : ∀ j, gauge B (b j) = 1) :
    crossPolytope b ⊆ B := by
  have hbal : Balanced ℝ B := (balanced_iff_neg_mem hB₀).2 fun x hx ↦ hB₁ x hx
  intro x hx
  have hx' : ∑ i, |b.repr x i| < 1 := hx
  have hg : gauge B x ≤ ∑ i, |b.repr x i| := by
    conv_lhs => rw [← b.sum_repr x]
    refine (gauge_sum_le hB₀ (absorbent_nhds_zero h₀) _ _).trans
      (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [gauge_smul hbal, hb i, mul_one, Real.norm_eq_abs]
  simpa using mem_smul_of_gauge_lt hB₀ h₀ (hg.trans_lt hx')

/-- The cross-polytope on a basis has measure `2 ^ n / n !` times the fundamental domain of that
basis: both are preimages under the coordinate map of standard sets in `Fin n → ℝ`, and any two
additive Haar measures there are proportional. -/
private theorem measure_crossPolytope {n : ℕ} (b : Basis (Fin n) ℝ E) (μ : Measure E)
    [μ.IsAddHaarMeasure] :
    μ (crossPolytope b) =
      ENNReal.ofReal (2 ^ n / Nat.factorial n) * μ (ZSpan.fundamentalDomain b) := by
  classical
  set K : Set (Fin n → ℝ) := {x : Fin n → ℝ | ∑ i, |x i| < 1} with hK
  set Q : Set (Fin n → ℝ) := Set.univ.pi fun _ ↦ Set.Ico (0 : ℝ) 1 with hQ
  have hmK : MeasurableSet K := by
    have : Continuous fun x : Fin n → ℝ ↦ ∑ i, |x i| := by fun_prop
    exact this.measurable measurableSet_Iio
  have hmQ : MeasurableSet Q := MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico
  have hmeas : Measurable (b.equivFun : E → (Fin n → ℝ)) :=
    (b.equivFun.toLinearMap.continuous_of_finiteDimensional).measurable
  obtain ⟨c, _, hc⟩ := b.equivFun.toLinearMap.exists_map_addHaar_eq_smul_addHaar μ volume
    b.equivFun.surjective
  have hpre : ∀ S : Set (Fin n → ℝ), MeasurableSet S →
      μ ((b.equivFun : E → (Fin n → ℝ)) ⁻¹' S) = c * volume S := by
    intro S hS
    rw [← Measure.map_apply hmeas hS]
    change (Measure.map (b.equivFun.toLinearMap : E → (Fin n → ℝ)) μ) S = _
    rw [hc, Measure.smul_apply, smul_eq_mul]
  have hfd : ZSpan.fundamentalDomain b = (b.equivFun : E → (Fin n → ℝ)) ⁻¹' Q := by
    ext x
    simp [ZSpan.fundamentalDomain, hQ, Basis.equivFun_apply]
  have hvolQ : volume Q = 1 := by
    rw [hQ, volume_pi_pi]
    simp
  have hvolK : volume K = ENNReal.ofReal (2 ^ n / Nat.factorial n) := by
    have hKeq : K = {x : Fin n → ℝ | ∑ i, |x i| ^ (1 : ℝ) < 1} := by
      simp only [hK, Real.rpow_one]
    have hΓ2 : Real.Gamma 2 = 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one one_ne_zero, Real.Gamma_one,
        mul_one]
    rw [hKeq, MeasureTheory.volume_sum_rpow_lt_one (Fin n) (p := 1) le_rfl]
    norm_num [hΓ2, Real.Gamma_nat_eq_factorial n]
  rw [crossPolytope, hpre _ hmK, hfd, hpre _ hmQ, hvolK, hvolQ, mul_one]
  ring

/-- **Minkowski's second theorem, the lower bound** (Cassels, Chapter VIII, Theorem V, the
inequality (13) of VIII.1). The independent lattice vectors `v i` realizing the successive minima,
scaled to gauge one, span a cross-polytope of volume `2 ^ n / n !` times `|det v|` inside the body,
and `|det v|` is an integer multiple of the covolume of `L`.

⚠ No closedness or compactness of the body is needed. -/
theorem covolume_le_prod_successiveMinimum_mul_measure (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (μ : Measure E) [μ.IsAddHaarMeasure] (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B) :
    2 ^ finrank ℝ E / (Nat.factorial (finrank ℝ E)) * covolume L μ ≤
      (∏ i ∈ Finset.range (finrank ℝ E), successiveMinimum L B i) * (μ B).toReal := by
  classical
  set n := finrank ℝ E with hn
  have h₀ : B ∈ 𝓝 (0 : E) := hB₀.mem_nhds_zero_of_symmetric hB₁ hB₂
  obtain ⟨v, hvL, hvind, hvg⟩ :=
    exists_linearIndependent_gauge_eq_successiveMinimum L hB₀ hB₁ hB₂ hB₃
  have hpos : ∀ j : Fin n, 0 < successiveMinimum L B (j : ℕ) :=
    fun j ↦ successiveMinimum_pos L hB₀ hB₁ hB₂ hB₃ j.isLt
  have hcard : Fintype.card (Fin n) = finrank ℝ E := by simp [hn]
  -- the scaled family, a basis of vectors of gauge one
  set w : Fin n → E := fun j ↦ (successiveMinimum L B (j : ℕ))⁻¹ • v j with hw
  have hwind : LinearIndependent ℝ w :=
    hvind.units_smul fun j : Fin n ↦
      Units.mk0 ((successiveMinimum L B (j : ℕ))⁻¹) (inv_ne_zero (hpos j).ne')
  set b₀ : Basis (Fin n) ℝ E := basisOfLinearIndependentOfCardEqFinrank' w hwind hcard with hb₀
  have hb₀c : ⇑b₀ = w := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have hgw : ∀ j, gauge B (b₀ j) = 1 := by
    intro j
    rw [hb₀c, hw, gauge_smul_of_nonneg (inv_nonneg.2 (hpos j).le), hvg j, smul_eq_mul,
      inv_mul_cancel₀ (hpos j).ne']
  -- the two bases of `E` coming from the lattice and from the minima
  have hcardL : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = n := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L, hn]
  set bZ : Basis (Fin n) ℤ L :=
    (Module.Free.chooseBasis ℤ L).reindex (Fintype.equivFinOfCardEq hcardL) with hbZ
  set bR : Basis (Fin n) ℝ E := bZ.ofZLatticeBasis ℝ L with hbR
  set bv : Basis (Fin n) ℝ E := basisOfLinearIndependentOfCardEqFinrank' v hvind hcard with hbv
  have hbvc : ⇑bv = v := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  -- the determinant of the realizing family in the scaled basis is the product of the minima
  have hprod : b₀.det ⇑bv = ∏ j : Fin n, successiveMinimum L B (j : ℕ) := by
    have hsm : ⇑bv = fun j : Fin n ↦ successiveMinimum L B (j : ℕ) • b₀ j := by
      funext j
      rw [hbvc, hb₀c, hw, smul_smul, mul_inv_cancel₀ (hpos j).ne', one_smul]
    rw [hsm, b₀.det.map_smul_univ, Basis.det_self, smul_eq_mul, mul_one]
  -- the determinant of the realizing family in a lattice basis is a nonzero integer
  have hint : ∃ m : ℤ, bR.det ⇑bv = (m : ℝ) := by
    refine ⟨bZ.det fun j ↦ (⟨v j, hvL j⟩ : L), ?_⟩
    have hmat : bR.toMatrix ⇑bv
        = (bZ.toMatrix fun j ↦ (⟨v j, hvL j⟩ : L)).map ((↑) : ℤ → ℝ) := by
      ext i j
      rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply, hbvc]
      exact bZ.ofZLatticeBasis_repr_apply ℝ L ⟨v j, hvL j⟩ i
    rw [Basis.det_apply, hmat, Basis.det_apply]
    exact (RingHom.map_det (Int.castRingHom ℝ) _).symm
  obtain ⟨m, hm⟩ := hint
  have hne : bR.det ⇑bv ≠ 0 := by
    intro h
    have := Basis.det_mul_det bR bv bR
    rw [h, zero_mul, Basis.det_self] at this
    exact one_ne_zero this.symm
  have hone : (1 : ℝ) ≤ |bR.det ⇑bv| := by
    rw [hm, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (by simpa [hm] using hne)
  -- the change of basis, and the bound on the determinant of the lattice basis
  have hchain : b₀.det ⇑bR * bR.det ⇑bv = ∏ j : Fin n, successiveMinimum L B (j : ℕ) := by
    rw [Basis.det_mul_det, hprod]
  have hprodpos : 0 < ∏ j : Fin n, successiveMinimum L B (j : ℕ) :=
    Finset.prod_pos fun j _ ↦ hpos j
  have hdetle : |b₀.det ⇑bR| ≤ ∏ j : Fin n, successiveMinimum L B (j : ℕ) := by
    have h1 : |b₀.det ⇑bR| * |bR.det ⇑bv| = ∏ j : Fin n, successiveMinimum L B (j : ℕ) := by
      rw [← abs_mul, hchain, abs_of_pos hprodpos]
    nlinarith [abs_nonneg (b₀.det ⇑bR)]
  -- the covolume against the fundamental domain of the scaled basis
  have hcov : covolume L μ = |b₀.det ((↑) ∘ bZ)| * μ.real (ZSpan.fundamentalDomain b₀) :=
    covolume_eq_det_mul_measureReal L μ bZ b₀
  have hcoe : ((↑) ∘ bZ : Fin n → E) = ⇑bR := by
    funext j
    rw [hbR, Function.comp_apply, Basis.ofZLatticeBasis_apply]
  -- the cross-polytope inside the body
  have hBfin : μ B ≠ ⊤ := hB₃.measure_lt_top.ne
  have hfdfin : μ (ZSpan.fundamentalDomain b₀) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded b₀).measure_lt_top.ne
  have hCB : μ.real (crossPolytope b₀) ≤ μ.real B :=
    measureReal_mono (crossPolytope_subset b₀ hB₀ h₀ hB₁ hgw) hBfin
  have hCvol : μ.real (crossPolytope b₀)
      = 2 ^ n / (Nat.factorial n) * μ.real (ZSpan.fundamentalDomain b₀) := by
    rw [measureReal_def, measureReal_def, measure_crossPolytope b₀ μ, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
  have hfdnn : 0 ≤ μ.real (ZSpan.fundamentalDomain b₀) := measureReal_nonneg
  have hkey : 2 ^ n / (Nat.factorial n : ℝ) * μ.real (ZSpan.fundamentalDomain b₀) ≤ μ.real B := by
    rw [← hCvol]; exact hCB
  rw [Fin.prod_univ_eq_prod_range (fun i ↦ successiveMinimum L B i) n] at hdetle hprodpos
  have hfac : (0 : ℝ) < 2 ^ n / (Nat.factorial n) := by positivity
  have hstep : |b₀.det ⇑bR| * (2 ^ n / (Nat.factorial n : ℝ) *
      μ.real (ZSpan.fundamentalDomain b₀)) ≤
      (∏ i ∈ Finset.range n, successiveMinimum L B i) * μ.real B :=
    le_trans (mul_le_mul_of_nonneg_right hdetle (mul_nonneg hfac.le hfdnn))
      (mul_le_mul_of_nonneg_left hkey hprodpos.le)
  rw [hcov, hcoe, ← measureReal_def]
  refine le_trans (le_of_eq ?_) hstep
  ring

/-! ### The upper bound for the zeroth minimum -/

/-- **Minkowski's first theorem, read homogeneously** (Cassels, Chapter VIII, the inequality (11)
of VIII.1): the zeroth minimum obeys `λ 0 ^ n * volume B ≤ 2 ^ n * covolume L`. This is the upper
bound of Minkowski's second theorem with `∏ i < n, λ i` weakened to `λ 0 ^ n`, and it is all that
the first theorem gives: the substantial half of Layer 4.2 is a different argument. -/
theorem pow_successiveMinimum_zero_mul_measure_le [Nontrivial E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (μ : Measure E) [μ.IsAddHaarMeasure] (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₅ : IsCompact B) :
    successiveMinimum L B 0 ^ finrank ℝ E * (μ B).toReal ≤
      2 ^ finrank ℝ E * covolume L μ := by
  set n := finrank ℝ E with hn
  have hn0 : n ≠ 0 := by
    rw [hn]
    exact (Module.finrank_pos (R := ℝ) (M := E)).ne'
  have hOpenPos : μ.IsOpenPosMeasure := inferInstance
  have hBpos : 0 < μ.real B := by
    obtain ⟨x, hx⟩ := hB₂
    have : 0 < μ (interior B) := (isOpen_interior).measure_pos μ ⟨x, hx⟩
    have hle : μ (interior B) ≤ μ B := measure_mono interior_subset
    have : 0 < μ B := lt_of_lt_of_le this hle
    rw [measureReal_def]
    exact ENNReal.toReal_pos this.ne' hB₅.measure_lt_top.ne
  have hcovpos : 0 < covolume L μ := covolume_pos L μ
  set c : ℝ := (2 ^ n * covolume L μ / μ.real B) ^ ((n : ℝ)⁻¹) with hc
  have hbase : 0 < 2 ^ n * covolume L μ / μ.real B := by positivity
  have hcpos : 0 < c := Real.rpow_pos_of_pos hbase _
  have hcn : c ^ n = 2 ^ n * covolume L μ / μ.real B :=
    Real.rpow_inv_natCast_pow hbase.le hn0
  -- apply Minkowski's first theorem to the dilated body
  have hmeas : μ.real (c • B) = c ^ n * μ.real B := by
    rw [measureReal_def, measureReal_def, Measure.addHaar_smul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_of_nonneg (by positivity), hn]
  have hle : 2 ^ n * covolume L μ ≤ (μ (c • B)).toReal := by
    rw [← measureReal_def, hmeas, hcn, div_mul_cancel₀ _ hBpos.ne']
  have hmin := successiveMinimum_zero_le_one L μ (hB₀.smul c)
    (fun x hx ↦ by
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨-y, hB₁ y hy, by simp⟩)
    (hB₅.smul c) (by rw [← hn]; exact hle)
  rw [successiveMinimum_smul L B 0 hcpos] at hmin
  have hlec : successiveMinimum L B 0 ≤ c := by
    rw [inv_mul_le_iff₀ hcpos] at hmin
    simpa using hmin
  have h0 : 0 ≤ successiveMinimum L B 0 :=
    le_of_lt (successiveMinimum_pos L hB₀ hB₁ hB₂ hB₅.isBounded Module.finrank_pos)
  calc successiveMinimum L B 0 ^ n * (μ B).toReal
      ≤ c ^ n * (μ B).toReal :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hlec n) ENNReal.toReal_nonneg
    _ = 2 ^ n * covolume L μ := by
        rw [hcn, ← measureReal_def, div_mul_cancel₀ _ hBpos.ne']

/-! ### Cassels' Lemma 2: a basis adapted to the minima -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Cassels' Chapter VIII, Lemma 2.** Some `ℤ`-basis `b` of `L` has, for every `j`, every lattice
point of gauge below the `j`-th minimum an *integer* combination of `b 0, …, b (j - 1)`.

This is the first of the two pieces Weyl's proof of the upper bound needs, and it is exactly the
combination of two things proved elsewhere: the dependence half of Cassels' Lemma 1
(`ZLattice.mem_span_of_gauge_lt_successiveMinimum`, Layer 4.1), which puts such a point in the
`ℝ`-span of the first `j` vectors realizing the minima, and the adapted basis
(`ZLattice.exists_basis_mem_span_int_of_mem_span_real`), which makes the lattice points of that
span the *integer* combinations of the first `j` basis vectors. Cassels proves the second by his
Chapter I, Theorem I; neither half is in Mathlib.

⚠ The basis is not the family realizing the minima, and in general cannot be: Layer 4.6 is the
statement of how far apart the two can be. What survives is the flag. -/
theorem exists_basis_mem_span_int_of_gauge_lt (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty)
    (hB₃ : Bornology.IsBounded B) :
    ∃ b : Basis (Fin (finrank ℝ E)) ℤ L, ∀ (j : ℕ) (x : E), x ∈ L →
      gauge B x < successiveMinimum L B j →
        x ∈ Submodule.span ℤ
          ((fun i ↦ ((b i : L) : E)) '' {i : Fin (finrank ℝ E) | (i : ℕ) < j}) := by
  obtain ⟨v, hvL, hvind, hvg⟩ :=
    exists_linearIndependent_gauge_eq_successiveMinimum L hB₀ hB₁ hB₂ hB₃
  obtain ⟨b, hb⟩ := exists_basis_mem_span_int_of_mem_span_real L rfl (fun i ↦ hvL i) hvind
  exact ⟨b, fun j x hxL hgx ↦ hb j x hxL
    (mem_span_of_gauge_lt_successiveMinimum L hB₀ hB₁ hB₂ hvL hvind hvg hxL hgx)⟩

/-! ### The upper bound

Weyl's argument, as Cassels carries it: the measure of the image of the open dilate
`{gauge B < t}` in `E ⧸ L` grows at least like `s ^ (n - J)` when `t` is scaled by `s ≥ 1` inside
the range where congruence modulo `L` is congruence modulo `L ∩ span (v 0, …, v (J - 1))`, and
chaining that from the first minimum to the last multiplies the measure of the body by the product
of the minima. The estimate itself is `ZLattice.pow_mul_measure_inter_add_le` of
`ArithmeticHeights/QuotientFubini.lean`; what is here is the chain and the gauge bookkeeping. -/

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Transporting the defining property of a fundamental domain along an equality of lattices. -/
private theorem existsUnique_of_eq {M N : Submodule ℤ E} (h : M = N) {F : Set E} {x : E}
    (hM : ∃! v : M, (v : E) + x ∈ F) : ∃! v : N, (v : E) + x ∈ F := by
  obtain ⟨u, hu, huq⟩ := hM
  refine ⟨⟨(u : E), h ▸ u.2⟩, hu, fun w hw ↦ ?_⟩
  have hwm : (w : E) ∈ M := h ▸ w.2
  have hwu : (⟨(w : E), hwm⟩ : M) = u := huq _ hw
  exact Subtype.ext (congrArg (fun z : M ↦ (z : E)) hwu)

/-- A fundamental domain for `L` in the exact form the quotient-measure estimates ask for —
`∀ x, ∃! v, ↑v + x ∈ F`, not the almost-everywhere `MeasureTheory.IsAddFundamentalDomain` —
together with the two facts that make it usable: it has finite measure, and that measure is the
covolume. The domain is the fundamental parallelepiped of a `ℤ`-basis. -/
private theorem exists_fundamentalDomain (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∃ F : Set E, MeasurableSet F ∧ (∀ x : E, ∃! v : L, (v : E) + x ∈ F) ∧ μ F ≠ ⊤ ∧
      (μ F).toReal = covolume L μ := by
  have hfin : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  have hfree : Module.Free ℤ L := ZLattice.module_free ℝ L
  set bZ := Module.Free.chooseBasis ℤ L with hbZ
  set bR := bZ.ofZLatticeBasis ℝ L with hbR
  have key : ∀ x : E, ∃! w : L, (w : E) + x ∈ ZSpan.fundamentalDomain bR := fun x ↦
    existsUnique_of_eq (bZ.ofZLatticeBasis_span ℝ)
      (ZSpan.exist_unique_vadd_mem_fundamentalDomain bR x)
  refine ⟨ZSpan.fundamentalDomain bR, ZSpan.fundamentalDomain_measurableSet bR, key,
    (ZSpan.fundamentalDomain_isBounded bR).measure_lt_top.ne, ?_⟩
  rw [covolume_eq_measure_fundamentalDomain L μ (F := ZSpan.fundamentalDomain bR)
    (MeasureTheory.IsAddFundamentalDomain.mk'
      (ZSpan.fundamentalDomain_measurableSet bR).nullMeasurableSet key), measureReal_def]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The span of the first `j` members of a family has dimension at most `j`. This is the whole of
what the chain needs about the flag, and it is why Cassels' Lemma 2 does not appear below. -/
private theorem finrank_span_image_lt_le {m : ℕ} (v : Fin m → E) (j : ℕ) :
    finrank ℝ (Submodule.span ℝ (v '' {i : Fin m | (i : ℕ) < j})) ≤ j := by
  classical
  have himg : v '' {i : Fin m | (i : ℕ) < j}
      = (((Finset.univ.filter (fun i : Fin m ↦ (i : ℕ) < j)).image v : Finset E) : Set E) := by
    ext x
    simp [Set.mem_image]
  rw [himg]
  refine le_trans (finrank_span_finset_le_card _) (le_trans Finset.card_image_le ?_)
  refine le_trans (Finset.card_le_card_of_injOn (fun i : Fin m ↦ (i : ℕ))
    (fun i hi ↦ Finset.mem_range.2 (by simpa using hi)) Fin.val_injective.injOn) ?_
  simp

/-- A weighted lower bound propagates through successive ratios of a positive sequence. -/
private theorem successiveMinimum_measure_chain (n : ℕ) (hnpos : 0 < n)
    (lam : ℕ → ℝ) (hpos : ∀ i, i < n → 0 < lam i)
    (bodyMeasure : ℝ≥0∞) (M : ℕ → ℝ≥0∞)
    (hbase : M 0 = ENNReal.ofReal ((lam 0 / 2) ^ n) * bodyMeasure)
    (hstep : ∀ j, 1 ≤ j → j < n →
      ENNReal.ofReal ((lam j / lam (j - 1)) ^ (n - j)) * M (j - 1) ≤ M j) :
    ∀ j, j < n →
      ENNReal.ofReal ((∏ i ∈ Finset.range (j + 1), lam i) * lam j ^ (n - 1 - j)) *
          bodyMeasure ≤ ENNReal.ofReal (2 ^ n) * M j := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : 0 < lam 0 := hpos 0 hnpos
    have hlhs : lam 0 * lam 0 ^ (n - 1 - 0)
        = 2 ^ n * (lam 0 / 2) ^ n := by
      rw [Nat.sub_zero, ← pow_succ', show n - 1 + 1 = n from by omega,
        div_pow]
      field_simp
    rw [hbase, Finset.prod_range_one, hlhs, ENNReal.ofReal_mul (by positivity), mul_assoc]
  | succ k ih =>
    intro hk
    have hkn : k < n := by omega
    have hkpos : 0 < lam k := hpos k hkn
    have hk1pos : 0 < lam (k + 1) := hpos (k + 1) hk
    have hprodnn : (0:ℝ) ≤ ∏ i ∈ Finset.range (k + 1), lam i :=
      Finset.prod_nonneg fun i hi ↦ (hpos i (by have := Finset.mem_range.1 hi; omega)).le
    have e2 : n - 1 - (k + 1) + 1 = n - (k + 1) := by omega
    have hL2 : (∏ i ∈ Finset.range (k + 1 + 1), lam i) *
          lam (k + 1) ^ (n - 1 - (k + 1))
        = (∏ i ∈ Finset.range (k + 1), lam i) * lam (k + 1) ^ (n - (k + 1)) := by
      rw [Finset.prod_range_succ, mul_assoc, ← pow_succ', e2]
    have hR2 : ((∏ i ∈ Finset.range (k + 1), lam i) * lam k ^ (n - 1 - k)) *
          (lam (k + 1) / lam k) ^ (n - (k + 1))
        = (∏ i ∈ Finset.range (k + 1), lam i) * lam (k + 1) ^ (n - (k + 1)) := by
      rw [show n - 1 - k = n - (k + 1) from by omega, div_pow]
      field_simp
    have hQ : (∏ i ∈ Finset.range (k + 1 + 1), lam i) *
          lam (k + 1) ^ (n - 1 - (k + 1))
        = ((∏ i ∈ Finset.range (k + 1), lam i) * lam k ^ (n - 1 - k)) *
          (lam (k + 1) / lam k) ^ (n - (k + 1)) := hL2.trans hR2.symm
    have hstep' : ENNReal.ofReal ((lam (k + 1) / lam k) ^ (n - (k + 1))) * M k
        ≤ M (k + 1) := by simpa using hstep (k + 1) (by omega) hk
    calc ENNReal.ofReal ((∏ i ∈ Finset.range (k + 1 + 1), lam i) *
            lam (k + 1) ^ (n - 1 - (k + 1))) * bodyMeasure
        = ENNReal.ofReal ((lam (k + 1) / lam k) ^ (n - (k + 1))) *
            (ENNReal.ofReal ((∏ i ∈ Finset.range (k + 1), lam i) *
              lam k ^ (n - 1 - k)) * bodyMeasure) := by
          rw [hQ, ENNReal.ofReal_mul (by positivity)]
          ring
      _ ≤ ENNReal.ofReal ((lam (k + 1) / lam k) ^ (n - (k + 1))) *
            (ENNReal.ofReal (2 ^ n) * M k) := mul_le_mul_right (ih hkn) _
      _ = ENNReal.ofReal (2 ^ n) *
            (ENNReal.ofReal ((lam (k + 1) / lam k) ^ (n - (k + 1))) * M k) := by ring
      _ ≤ ENNReal.ofReal (2 ^ n) * M (k + 1) := mul_le_mul_right hstep' _

/-- **Minkowski's second theorem, the upper bound** (Cassels, Chapter VIII, Theorem V, the
inequality (12) of VIII.1): `(∏ i < n, λ i) * volume B ≤ 2 ^ n * covolume L`. This is the
substantial half, the one Layer 5 and 6.3 consume.

The proof is Weyl's, through Cassels' Theorem IV, which is
`ZLattice.pow_mul_measure_inter_add_le`. Write `S t` for the image of the open dilate
`{gauge B < t}` in `E ⧸ L`. At `t = λ 0 / 2` the dilate injects into the quotient, so
`m (S t) = t ^ n * volume B`; and for `1 ≤ J < n` and `s = λ J / λ (J - 1)` the estimate gives
`m (S (s t)) ≥ s ^ (n - J) * m (S t)` at `t = λ (J - 1) / 2`, because there congruence modulo `L`
inside the dilate is congruence modulo `L ∩ span (v 0, …, v (J - 1))`, a sublattice of `ℤ`-rank at
most `J`. Chaining and bounding `m (S (λ (n - 1) / 2))` by the covolume multiplies `volume B` by
the telescoping product `λ 0 ^ n * ∏_{J = 1}^{n - 1} (λ J / λ (J - 1)) ^ (n - J) = ∏ i < n, λ i`.

⚠ **The chain runs on open dilates, and that is what removes closedness.** For a closed body the
dilate contains points of gauge exactly `t`, and the separation hypothesis would hold only for
`2 t < λ J` strictly; for `{gauge B < t}` it holds at `2 t = λ J`, which is where the chain needs
it. The body and its interior have the same measure because a convex set has null frontier.

⚠ **Cassels' Lemma 2 is not used.** He needs the adapted basis because he works in coordinates:
the integrality of the first `J` coordinates is how he sees that the translation stays in the
sublattice. Coordinate-free the sublattice `L ∩ span (v 0, …, v (J - 1))` is at hand and the only
thing wanted of it is its rank, which is the `ℝ`-dimension of its span by
`ZLattice.finrank_int_eq_finrank_real`. -/
theorem prod_successiveMinimum_mul_measure_le (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (μ : Measure E) [μ.IsAddHaarMeasure] (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B) :
    (∏ i ∈ Finset.range (finrank ℝ E), successiveMinimum L B i) * (μ B).toReal ≤
      2 ^ finrank ℝ E * covolume L μ := by
  classical
  obtain ⟨FL, hFLm, hFLfd, hFLfin, hFLcov⟩ := exists_fundamentalDomain L μ
  have h₀ : B ∈ 𝓝 (0 : E) := hB₀.mem_nhds_zero_of_symmetric hB₁ hB₂
  obtain ⟨v, hvL, hvind, hvg⟩ :=
    exists_linearIndependent_gauge_eq_successiveMinimum L hB₀ hB₁ hB₂ hB₃
  set lam : ℕ → ℝ := successiveMinimum L B
  rcases Nat.eq_zero_or_pos (finrank ℝ E) with hn0 | hnpos
  · -- a zero-dimensional space: the body and the fundamental domain are both the whole of `E`
    have hsub : Subsingleton E := by
      rw [← Module.finrank_zero_iff (R := ℝ)]
      exact hn0
    obtain ⟨w, hw, -⟩ := hFLfd 0
    have h0F : (0 : E) ∈ FL := by
      rwa [show (w : E) + (0 : E) = 0 from Subsingleton.elim _ _] at hw
    have hBF : B ⊆ FL := fun x _ ↦ by
      rwa [show x = (0 : E) from Subsingleton.elim _ _]
    rw [hn0]
    simp only [Finset.range_zero, Finset.prod_empty, one_mul, pow_zero]
    rw [← hFLcov]
    exact ENNReal.toReal_mono hFLfin (measure_mono hBF)
  -- the open body, its dilates, and its measure
  have hCm : MeasurableSet (interior B) := isOpen_interior.measurableSet
  have hCc : Convex ℝ (interior B) := hB₀.interior
  have hmemC : ∀ t : ℝ, 0 < t → ∀ x : E, x ∈ t • interior B ↔ gauge B x < t := by
    intro t ht x
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne', ← gauge_lt_one_iff_mem_interior hB₀ h₀,
      gauge_smul_of_nonneg (inv_nonneg.2 ht.le), smul_eq_mul, inv_mul_lt_one₀ ht]
  have hvol : μ (interior B) = μ B := by
    refine le_antisymm (measure_mono interior_subset) ?_
    calc μ B ≤ μ (interior B ∪ frontier B) :=
          measure_mono fun x hx ↦ (em (x ∈ interior B)).imp id fun h ↦ ⟨subset_closure hx, h⟩
      _ ≤ μ (interior B) + μ (frontier B) := measure_union_le _ _
      _ = μ (interior B) := by rw [hB₀.addHaar_frontier μ, add_zero]
  have hAm : ∀ t : ℝ, MeasurableSet (t • interior B) := fun t ↦ hCm.const_smul₀ t
  -- positivity and monotonicity of the minima
  have hpos : ∀ i, i < finrank ℝ E → 0 < lam i :=
    fun i hi ↦ successiveMinimum_pos L hB₀ hB₁ hB₂ hB₃ hi
  have hmono : ∀ i j : ℕ, i ≤ j → j < finrank ℝ E → lam i ≤ lam j :=
    fun i j hij hj ↦ successiveMinimum_le_of_le hij hj hB₀ hB₁ hB₂
  -- the sublattices cut out by the flag of the family realizing the minima
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℕ → Submodule ℤ E, ∀ j, Λ j =
      L ⊓ (Submodule.span ℝ (v '' {i : Fin (finrank ℝ E) | (i : ℕ) < j})).restrictScalars ℤ :=
    ⟨_, fun _ ↦ rfl⟩
  have hΛle : ∀ j, Λ j ≤ L := fun j ↦ (hΛ j).le.trans inf_le_left
  have hΛdisc : ∀ j, DiscreteTopology (Λ j) := fun j ↦ discreteTopology_of_le (hΛle j)
  have hΛrank : ∀ j, finrank ℤ (Λ j) ≤ j := by
    intro j
    rw [finrank_int_eq_finrank_real (hΛle j)]
    refine le_trans (Submodule.finrank_mono ?_) (finrank_span_image_lt_le v j)
    refine Submodule.span_le.2 fun x hx ↦ ?_
    rw [hΛ j] at hx
    exact (Submodule.mem_inf.1 hx).2
  have hΛ0 : Λ 0 = ⊥ := by
    rw [hΛ 0]
    simp
  -- the separation hypothesis, straight from the dependence half of Cassels' Lemma 1
  have hsep : ∀ (j : ℕ) (t : ℝ), 0 < t → 2 * t ≤ lam j →
      ∀ x ∈ t • interior B, ∀ y ∈ t • interior B, x - y ∈ L → x - y ∈ Λ j := by
    intro j t ht hlt x hx y hy hxy
    have hgx : gauge B x < t := (hmemC t ht x).1 hx
    have hgy : gauge B y < t := (hmemC t ht y).1 hy
    have hadd := gauge_add_le hB₀ (absorbent_nhds_zero h₀) x (-y)
    rw [gauge_neg hB₁] at hadd
    have hg : gauge B (x - y) < lam j := by
      rw [sub_eq_add_neg]
      linarith
    have hspan : x - y ∈ Submodule.span ℝ (v '' {i : Fin (finrank ℝ E) | (i : ℕ) < j}) :=
      mem_span_of_gauge_lt_successiveMinimum L hB₀ hB₁ hB₂ hvL hvind hvg (j := j) hxy hg
    rw [hΛ j]
    exact Submodule.mem_inf.2 ⟨hxy, (Submodule.restrictScalars_mem ℤ _ _).2 hspan⟩
  -- the quotient measure of the dilates, one per minimum
  have hLcount : Countable L := countable_of_discreteTopology L
  obtain ⟨M, hM⟩ : ∃ M : ℕ → ℝ≥0∞, ∀ j,
      M j = μ (FL ∩ ((lam j / 2) • interior B + (L : Set E))) := ⟨_, fun _ ↦ rfl⟩
  have hbotfd : ∀ x : E, ∃! w : (⊥ : Submodule ℤ E), (w : E) + x ∈ (univ : Set E) :=
    fun _ ↦ ⟨0, Set.mem_univ _, fun _ _ ↦ Subsingleton.elim _ _⟩
  -- the base: below the first minimum the dilate injects into the quotient
  have hbase : M 0 = ENNReal.ofReal ((lam 0 / 2) ^ finrank ℝ E) * μ (interior B) := by
    have h0 : 0 < lam 0 := hpos 0 hnpos
    have hsep0 : ∀ x ∈ (lam 0 / 2) • interior B, ∀ y ∈ (lam 0 / 2) • interior B,
        x - y ∈ L → x - y ∈ (⊥ : Submodule ℤ E) := by
      intro x hx y hy hxy
      rw [← hΛ0]
      exact hsep 0 (lam 0 / 2) (by positivity) (by linarith) x hx y hy hxy
    have heq := measure_inter_add_eq_of_separated μ (bot_le : (⊥ : Submodule ℤ E) ≤ L)
      hbotfd hFLfd MeasurableSet.univ hFLm hFLfin (hAm (lam 0 / 2)) hsep0
    have hz : (lam 0 / 2) • interior B + ((⊥ : Submodule ℤ E) : Set E)
        = (lam 0 / 2) • interior B := by simp
    rw [hM, ← heq, Set.univ_inter, hz, Measure.addHaar_smul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (lam 0 / 2) ^ finrank ℝ E)]
  -- the inductive step: Cassels' Theorem IV applied at the `j`-th minimum
  have hstep : ∀ j, 1 ≤ j → j < finrank ℝ E →
      ENNReal.ofReal ((lam j / lam (j - 1)) ^ (finrank ℝ E - j)) * M (j - 1) ≤ M j := by
    intro j hj1 hjn
    have hjm : j - 1 < finrank ℝ E := by omega
    have hp1 : 0 < lam (j - 1) := hpos _ hjm
    have hpj : 0 < lam j := hpos _ hjn
    have hle : lam (j - 1) ≤ lam j := hmono _ _ (by omega) hjn
    have hs1 : 1 ≤ lam j / lam (j - 1) := (one_le_div hp1).2 hle
    have hsA : (lam j / lam (j - 1)) • ((lam (j - 1) / 2) • interior B)
        = (lam j / 2) • interior B := by
      rw [smul_smul]
      congr 1
      field_simp
    have hd : DiscreteTopology (Λ j) := hΛdisc j
    have hsepA : ∀ x ∈ (lam (j - 1) / 2) • interior B, ∀ y ∈ (lam (j - 1) / 2) • interior B,
        x - y ∈ L → x - y ∈ Λ j :=
      hsep j (lam (j - 1) / 2) (by positivity) (by linarith)
    have hsepB : ∀ x ∈ (lam j / lam (j - 1)) • ((lam (j - 1) / 2) • interior B),
        ∀ y ∈ (lam j / lam (j - 1)) • ((lam (j - 1) / 2) • interior B),
        x - y ∈ L → x - y ∈ Λ j := by
      rw [hsA]
      exact hsep j (lam j / 2) (by positivity) (by linarith)
    have hkey := pow_mul_measure_inter_add_le μ (hΛle j) hFLfd hFLm hFLfin
      (hAm (lam (j - 1) / 2)) (hCc.smul _) hs1 hsepA hsepB
    rw [hsA] at hkey
    rw [hM (j - 1), hM j]
    refine le_trans (mul_le_mul_left ?_ _) hkey
    have hrk := hΛrank j
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ hs1 (by omega))
  -- the chain, carrying `λ 0 ⋯ λ j * λ j ^ (n - 1 - j)` up the minima
  have hchain := successiveMinimum_measure_chain (finrank ℝ E) hnpos lam hpos
    (μ (interior B)) M hbase hstep
  -- reading the chain off at the last minimum, against the covolume
  have hfin := hchain (finrank ℝ E - 1) (by omega)
  rw [show finrank ℝ E - 1 + 1 = finrank ℝ E from by omega, Nat.sub_self, pow_zero, mul_one] at hfin
  have hMle : M (finrank ℝ E - 1) ≤ μ FL := by
    rw [hM]
    exact measure_mono Set.inter_subset_left
  have hprodnn : (0:ℝ) ≤ ∏ i ∈ Finset.range (finrank ℝ E), lam i :=
    Finset.prod_nonneg fun i hi ↦ (hpos i (Finset.mem_range.1 hi)).le
  have hle2 : ENNReal.ofReal (∏ i ∈ Finset.range (finrank ℝ E), lam i) * μ B
      ≤ ENNReal.ofReal (2 ^ finrank ℝ E) * μ FL := by
    rw [← hvol]
    exact le_trans hfin (mul_le_mul_right hMle _)
  have hBfin : μ B ≠ ⊤ := hB₃.measure_lt_top.ne
  have hcalc := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFLfin) hle2
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hprodnn,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 2 ^ finrank ℝ E), hFLcov] at hcalc
  exact hcalc

end ZLattice

/-! ### Why the upper bound is not a packing statement

The upper bound of Minkowski's second theorem would follow at once from the following false
statement: for a symmetric convex body `B` and `0 < c ≤ 1`, shrinking one coordinate of a point
of `B` — in the basis realizing the minima, and shrinking the *earlier* coordinates, whose minima
are the smaller ones — keeps it inside `B`. It fails already in the plane. -/

section Examples

/-- ⚠ **Shrinking a coordinate can leave a symmetric convex body**, so the linear map whose
determinant is the product of the minima does not map the body into itself. The body here is the
thin parallelogram `|x| ≤ 1`, `|19 x - 20 y| ≤ 1` along the diagonal: it contains `(1, 19/20)`,
but not `(9/10, 19/20)`, which the segment to `(0, 19/20)` has already left. -/
example : ∃ (B : Set (ℝ × ℝ)) (x : ℝ × ℝ) (c : ℝ), Convex ℝ B ∧ (∀ y ∈ B, -y ∈ B) ∧
    Bornology.IsBounded B ∧ (interior B).Nonempty ∧ 0 < c ∧ c < 1 ∧ x ∈ B ∧
    ((c * x.1, x.2) : ℝ × ℝ) ∉ B := by
  have combo : ∀ {a b s t r : ℝ}, |a| ≤ r → |b| ≤ r → 0 ≤ s → 0 ≤ t → s + t = 1 →
      |s * a + t * b| ≤ r := by
    intro a b s t r ha hb hs ht hst
    calc |s * a + t * b| ≤ |s * a| + |t * b| := abs_add_le _ _
      _ = s * |a| + t * |b| := by rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      _ ≤ s * r + t * r := by nlinarith
      _ = r := by rw [← add_mul, hst, one_mul]
  refine ⟨{p : ℝ × ℝ | |p.1| ≤ 1 ∧ |19 * p.1 - 20 * p.2| ≤ 1}, (1, 19 / 20), 9 / 10, ?_, ?_, ?_,
    ?_, by norm_num, by norm_num, by norm_num, by norm_num [abs_le]⟩
  · rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ s t hs ht hst
    refine ⟨?_, ?_⟩
    · change |s * x.1 + t * y.1| ≤ 1
      exact combo hx1 hy1 hs ht hst
    · change |19 * (s * x.1 + t * y.1) - 20 * (s * x.2 + t * y.2)| ≤ 1
      have h : 19 * (s * x.1 + t * y.1) - 20 * (s * x.2 + t * y.2)
          = s * (19 * x.1 - 20 * x.2) + t * (19 * y.1 - 20 * y.2) := by ring
      rw [h]
      exact combo hx2 hy2 hs ht hst
  · rintro y ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · change |(-y.1 : ℝ)| ≤ 1
      simpa using hy1
    · change |19 * (-y.1) - 20 * (-y.2)| ≤ 1
      have h : 19 * (-y.1) - 20 * (-y.2) = -(19 * y.1 - 20 * y.2) := by ring
      rw [h, abs_neg]
      exact hy2
  · refine Bornology.IsBounded.subset
      (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := 1)) ?_
    rintro p ⟨h1, h2⟩
    rw [abs_le] at h1 h2
    obtain ⟨h1a, h1b⟩ := h1
    obtain ⟨h2a, h2b⟩ := h2
    rw [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff,
      abs_le, abs_le]
    refine ⟨⟨h1a, h1b⟩, ?_, ?_⟩ <;> linarith
  · refine ⟨0, ?_⟩
    have hsub : ∀ p : ℝ × ℝ, p ∈ Metric.ball (0 : ℝ × ℝ) (1 / 39) →
        p ∈ {p : ℝ × ℝ | |p.1| ≤ 1 ∧ |19 * p.1 - 20 * p.2| ≤ 1} := by
      intro p hp
      rw [mem_ball_zero_iff, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_lt_iff] at hp
      obtain ⟨hp1, hp2⟩ := hp
      rw [abs_lt] at hp1 hp2
      obtain ⟨h1a, h1b⟩ := hp1
      obtain ⟨h2a, h2b⟩ := hp2
      exact ⟨by rw [abs_le]; constructor <;> linarith,
        by rw [abs_le]; constructor <;> linarith⟩
    exact interior_maximal hsub Metric.isOpen_ball (Metric.mem_ball_self (by norm_num))

end Examples
