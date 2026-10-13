/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.ClusterEventTwo
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.TranslatedCrossing

/-!
# DiameterTwo

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The maximal diameter bound for distance-two crossings

It proves a local scale-induction result `e.Ck.indy.hyp` and the final union
bound for distance-two paths, delivering conclusion (3) of
`l.percolation.bound.general` — the maximal diameter bound `e.diameter.bound` —
for the crossing event whose paths step by two.

## The gate constant does not grow

The distance-two layer is proved under **exactly** the threshold of the
distance-one layer,

`16 d exp(40 (1 - b)^{-1}) ≤ T² b`

The reason the constant survives is arithmetic, and is worth recording.  The
step size enters the induction only through

* the union-bound weight `3 ^ (d (k + h + 2))` instead of `3 ^ (d (k + h + 1))`
  (one extra `3 ^ d` from the wider localisation box `locBox₂`), and
* the corresponding `3 ^ (d (k + 2))`, `3 ^ (d (k + 3))` in the final union
  bound,

whereas the number `3 ^ (h - 3)` of separated sites extracted from a long path is
unchanged (`LatticeTwo.exists_separated_subpaths₂`).  In the scalar inequalities
this replaces the hypothesis `h + 1 ≤ 3 ^ h` by `h + 2 ≤ 3 ^ h` and the entropy
`d (j + h + 1)` by `d (j + h + 2)`, both of which are absorbed by the slack
already present at `3 ^ h ≥ 27`.  No constant in the gate or in the conclusion
moves.

## Main definitions

* `crossingEvent₂`, `crossingEvent₂At`: the crossing event of `e.diameter.bound`
  with distance-two paths, at the origin and at an arbitrary base site.

## Main results

* `measure_clusterEvent₂_le_exp`: the induction `e.Ck.indy.hyp`.
* `measure_crossingEvent₂_le_exp`: `e.diameter.bound` for distance-two
  crossings.
* `measure_crossingEvent₂At_le_exp`: the same at an arbitrary base site.

## References

* ABK26, `l.percolation.bound.general`, Step 3.
-/

namespace Algsuperdiff.Section3.Provider.Percolation

open MeasureTheory ProbabilityTheory

variable {d : ℕ} {Ω : Type*}

/-! ### An elementary count -/

/-- `n + 2 ≤ 3 ^ n` for `n ≥ 1`: the distance-two replacement for
`succ_le_three_pow`. -/
private theorem add_two_le_three_pow (n : ℕ) (hn : 1 ≤ n) : n + 2 ≤ 3 ^ n := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have h := succ_le_three_pow p
  have hstep : (3 : ℕ) ^ (p + 1) = 3 ^ p * 3 := pow_succ 3 p
  have hpos : 0 < (3 : ℕ) ^ p := three_pow_pos p
  omega

/-! ### The scalar inequalities driving the induction -/

/-- The gain produced by the `3 ^ (h - 3)` separated sites; identical to the
distance-one layer, because the count of separated sites is unchanged. -/
private theorem separated_gain₂ {b : ℝ} {h j : ℕ} (hh : 3 ≤ h)
    (hgain : 8 ≤ (1 - b) * (h : ℝ)) :
    243 * (3 : ℝ) ^ (b * (j : ℝ))
      ≤ ((3 ^ (h - 3) : ℕ) : ℝ) * (3 : ℝ) ^ (b * ((j : ℝ) - (h : ℝ))) := by
  have hMrpow : ((3 ^ (h - 3) : ℕ) : ℝ) = (3 : ℝ) ^ ((h : ℝ) - 3) := by
    have hcast : ((h : ℝ) - 3) = ((h - 3 : ℕ) : ℝ) := by rw [Nat.cast_sub hh]; norm_num
    rw [hcast, Real.rpow_natCast]
    push_cast; ring
  have hexp : b * (j : ℝ) + 5 ≤ ((h : ℝ) - 3) + b * ((j : ℝ) - (h : ℝ)) := by
    linarith only [hgain]
  have h243 : (243 : ℝ) = (3 : ℝ) ^ (5 : ℝ) := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  calc 243 * (3 : ℝ) ^ (b * (j : ℝ))
      = (3 : ℝ) ^ (5 : ℝ) * (3 : ℝ) ^ (b * (j : ℝ)) := by rw [← h243]
    _ = (3 : ℝ) ^ (b * (j : ℝ) + 5) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]; ring_nf
    _ ≤ (3 : ℝ) ^ (((h : ℝ) - 3) + b * ((j : ℝ) - (h : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = ((3 ^ (h - 3) : ℕ) : ℝ) * (3 : ℝ) ^ (b * ((j : ℝ) - (h : ℝ))) := by
        rw [hMrpow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]

/-- The threshold `16 d 9^h ≤ T² b` puts `h` well below `T²/2`. -/
private theorem scale_le_half_sq₂ {D E hr T b : ℝ} (hD1 : 1 ≤ D) (hE27 : 27 ≤ E)
    (hEh : hr + 2 ≤ E) (hTb : 16 * D * (E * E) ≤ T ^ 2 * b) (hb1 : b ≤ 1)
    (hT2 : 0 < T ^ 2) : hr ≤ T ^ 2 / 2 := by
  have hEpos : (0 : ℝ) < E := by linarith only [hE27]
  have hDE : (0 : ℝ) ≤ D * E :=
    mul_nonneg (by linarith only [hD1]) (by linarith only [hE27])
  have hbig : 16 * (D * E) * E ≤ T ^ 2 := by
    linarith only [hTb, mul_nonneg (le_of_lt hT2) (by linarith only [hb1] : (0 : ℝ) ≤ 1 - b)]
  linarith only [hbig, hEh, hEpos,
    mul_nonneg hDE (by linarith only [hE27] : (0 : ℝ) ≤ E - 27),
    mul_nonneg (by linarith only [hE27] : (0 : ℝ) ≤ E)
      (by linarith only [hD1] : (0 : ℝ) ≤ D - 1)]

/-- The exponent estimate for the separated-sites term of the distance-two
iteration inequality.  Against the distance-one layer only the entropy changes,
from `D (jr + hr + 1)` to `D (jr + hr + 2)`, and the requirement `hr + 1 ≤ E`
to `hr + 2 ≤ E`. -/
private theorem exp_step_one₂ {D E Mr nr S R jr hr T b : ℝ}
    (hD1 : 1 ≤ D) (hE27 : 27 ≤ E) (hMr27 : Mr * 27 = E) (hMr0 : 0 ≤ Mr)
    (hhr : 3 ≤ hr) (hEh : hr + 2 ≤ E) (hjr : 0 ≤ jr) (hnr : nr = D * (jr + hr + 2))
    (hL2 : Real.log 3 ≤ 2) (hTb : 16 * D * (E * E) ≤ T ^ 2 * b) (hT2 : 0 < T ^ 2)
    (hb1 : b ≤ 1) (hMR : 243 * S ≤ Mr * R) (hS1 : 1 + b * jr ≤ S) :
    Mr * (nr * Real.log 3 + -(T ^ 2 * R / 2)) + 1 ≤ -(T ^ 2 * S / 2) := by
  have hEpos : (0 : ℝ) < E := by linarith only [hE27]
  have hD0 : (0 : ℝ) < D := by linarith only [hD1]
  have hnr0 : (0 : ℝ) ≤ nr := by
    rw [hnr]
    exact mul_nonneg (by linarith only [hD1]) (by linarith only [hjr, hhr])
  have hMlog : Mr * Real.log 3 ≤ E := by
    linarith only [hMr27, hMr0,
      mul_nonneg hMr0 (by linarith only [hL2] : (0 : ℝ) ≤ 2 - Real.log 3)]
  have hA : nr ≤ D * (jr + E) := by
    rw [hnr]
    linarith only [mul_nonneg (le_of_lt hD0)
      (by linarith only [hEh] : (0 : ℝ) ≤ E - hr - 2)]
  have hB1 : Mr * (nr * Real.log 3) ≤ E * nr := by
    linarith only [mul_nonneg
      (by linarith only [hMlog] : (0 : ℝ) ≤ E - Mr * Real.log 3) hnr0]
  have hB2 : E * nr ≤ E * (D * (jr + E)) := by
    linarith only [mul_nonneg (le_of_lt hEpos)
      (by linarith only [hA] : (0 : ℝ) ≤ D * (jr + E) - nr)]
  have hED : E * D ≤ D * (E * E) := by
    linarith only [mul_nonneg (mul_nonneg (le_of_lt hD0) (le_of_lt hEpos))
      (by linarith only [hE27] : (0 : ℝ) ≤ E - 1)]
  have hEE : (729 : ℝ) ≤ E * E := by linarith only [hE27, sq_nonneg (E - 27)]
  have hDEE : (729 : ℝ) ≤ D * (E * E) := by
    linarith only [hEE, mul_nonneg (by linarith only [hD1] : (0 : ℝ) ≤ D - 1)
      (by linarith only [hEE] : (0 : ℝ) ≤ E * E)]
  have hC1 : E * D * jr ≤ D * (E * E) * jr := by
    linarith only [mul_nonneg
      (by linarith only [hED] : (0 : ℝ) ≤ D * (E * E) - E * D) hjr]
  have hC3 : D * (E * E) * jr ≤ 16 * (D * (E * E)) * jr := by
    linarith only [mul_nonneg (by linarith only [hDEE] : (0 : ℝ) ≤ D * (E * E)) hjr]
  have hC4 : 16 * (D * (E * E)) * jr ≤ T ^ 2 * b * jr := by
    linarith only [mul_nonneg
      (by linarith only [hTb] : (0 : ℝ) ≤ T ^ 2 * b - 16 * D * (E * E)) hjr]
  have hC5 : 16 * (D * (E * E)) ≤ T ^ 2 := by
    linarith only [hTb,
      mul_nonneg (le_of_lt hT2) (by linarith only [hb1] : (0 : ℝ) ≤ 1 - b)]
  have hchain : Mr * (nr * Real.log 3) + 1 ≤ T ^ 2 * b * jr + T ^ 2 := by
    linarith only [hB1, hB2, hC1, hC3, hC4, hC5, hDEE]
  have hkey : Mr * (nr * Real.log 3) + 1 ≤ 121 * (T ^ 2 * S) := by
    linarith only [hchain, hT2, hC3, hC4,
      mul_nonneg (le_of_lt hT2) (by linarith only [hS1] : (0 : ℝ) ≤ S - 1 - b * jr)]
  have hRS : 243 * (T ^ 2 * S) ≤ Mr * (T ^ 2 * R) := by
    linarith only [mul_nonneg (le_of_lt hT2)
      (by linarith only [hMR] : (0 : ℝ) ≤ Mr * R - 243 * S)]
  linarith only [hkey, hRS]

/-- The exponent estimate for the large-scale term of the distance-two iteration
inequality. -/
private theorem exp_step_two₂ {D E nr S U jr hr T a b : ℝ}
    (hD1 : 1 ≤ D) (hE27 : 27 ≤ E) (hhr : 3 ≤ hr) (hEh : hr + 2 ≤ E) (hjr : 0 ≤ jr)
    (hnr : nr = D * (jr + hr + 2)) (hL2 : Real.log 3 ≤ 2)
    (hTb : 16 * D * (E * E) ≤ T ^ 2 * b) (hT2 : 0 < T ^ 2) (hb1 : b ≤ 1) (hba : b ≤ a)
    (hU1 : 1 + a * jr ≤ U) (hSU : S ≤ U) :
    nr * Real.log 3 + hr + -(T ^ 2 * U) + 1 ≤ -(T ^ 2 * S / 2) := by
  have hEpos : (0 : ℝ) < E := by linarith only [hE27]
  have hD0 : (0 : ℝ) < D := by linarith only [hD1]
  have hDE : (0 : ℝ) ≤ D * E :=
    mul_nonneg (by linarith only [hD1]) (by linarith only [hE27])
  have hnr0 : (0 : ℝ) ≤ nr := by
    rw [hnr]
    exact mul_nonneg (by linarith only [hD1]) (by linarith only [hjr, hhr])
  have hnrlog : nr * Real.log 3 ≤ 2 * (D * (jr + hr + 2)) := by
    rw [← hnr]
    linarith only [mul_nonneg hnr0 (by linarith only [hL2] : (0 : ℝ) ≤ 2 - Real.log 3)]
  have hC5 : 16 * (D * (E * E)) ≤ T ^ 2 := by
    linarith only [hTb,
      mul_nonneg (le_of_lt hT2) (by linarith only [hb1] : (0 : ℝ) ≤ 1 - b)]
  have hcst : 2 * D * (hr + 2) + hr + 1 ≤ T ^ 2 / 2 := by
    have h1 : 2 * D * (hr + 2) ≤ 2 * (D * E) := by
      linarith only [mul_nonneg (le_of_lt hD0)
        (by linarith only [hEh] : (0 : ℝ) ≤ E - hr - 2)]
    have h2 : hr + 1 ≤ D * E := by
      linarith only [hEh, mul_nonneg (by linarith only [hE27] : (0 : ℝ) ≤ E)
        (by linarith only [hD1] : (0 : ℝ) ≤ D - 1)]
    have h3 : 3 * (D * E) ≤ T ^ 2 / 2 := by
      linarith only [hC5,
        mul_nonneg hDE (by linarith only [hE27] : (0 : ℝ) ≤ 16 * E - 6)]
    linarith only [h1, h2, h3]
  have hlin : 2 * D * jr ≤ T ^ 2 * a * jr / 2 := by
    have hEE : (1 : ℝ) ≤ E * E := by linarith only [hE27, sq_nonneg (E - 27)]
    have hab : T ^ 2 * b ≤ T ^ 2 * a := by
      linarith only [mul_nonneg (le_of_lt hT2)
        (by linarith only [hba] : (0 : ℝ) ≤ a - b)]
    have h4D : 4 * D ≤ T ^ 2 * a := by
      linarith only [hTb, hab, hD0, mul_nonneg (le_of_lt hD0)
        (by linarith only [hEE] : (0 : ℝ) ≤ E * E - 1)]
    linarith only [mul_nonneg
      (by linarith only [h4D] : (0 : ℝ) ≤ T ^ 2 * a - 4 * D) hjr]
  have hUT : T ^ 2 * (1 + a * jr) ≤ T ^ 2 * U := by
    linarith only [mul_nonneg (le_of_lt hT2)
      (by linarith only [hU1] : (0 : ℝ) ≤ U - 1 - a * jr)]
  have hSUT : T ^ 2 * S ≤ T ^ 2 * U := by
    linarith only [mul_nonneg (le_of_lt hT2)
      (by linarith only [hSU] : (0 : ℝ) ≤ U - S)]
  linarith only [hnrlog, hcst, hlin, hUT, hSUT]

/-- The base-case scalar inequality; identical to the distance-one layer. -/
private theorem base_real_bound₂ {b T mr hr : ℝ} (hmh : mr ≤ hr) (hb0 : 0 < b)
    (hT2 : 0 < T ^ 2) (hmT : mr ≤ T ^ 2 / 2) :
    (mr + 1) * Real.exp (-(T ^ 2)) ≤ Real.exp (-(T ^ 2 * (3 : ℝ) ^ (b * (mr - hr)) / 2)) := by
  have hR : (3 : ℝ) ^ (b * (mr - hr)) ≤ 1 :=
    three_rpow_le_one (by
      linarith only [mul_nonneg hb0.le (by linarith only [hmh] : (0 : ℝ) ≤ hr - mr)])
  have hcount : mr + 1 ≤ Real.exp (T ^ 2 / 2) :=
    le_trans (Real.add_one_le_exp mr) (Real.exp_le_exp.mpr hmT)
  have hsplit : Real.exp (T ^ 2 / 2) * Real.exp (-(T ^ 2)) = Real.exp (-(T ^ 2 / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hmono : Real.exp (-(T ^ 2 / 2))
      ≤ Real.exp (-(T ^ 2 * (3 : ℝ) ^ (b * (mr - hr)) / 2)) := by
    refine Real.exp_le_exp.mpr ?_
    linarith only [mul_nonneg (le_of_lt hT2)
      (by linarith only [hR] : (0 : ℝ) ≤ 1 - (3 : ℝ) ^ (b * (mr - hr)))]
  have hpos := Real.exp_pos (-(T ^ 2))
  linarith only [hsplit, hmono,
    mul_nonneg (by linarith only [hcount] : (0 : ℝ) ≤ Real.exp (T ^ 2 / 2) - (mr + 1))
      (le_of_lt hpos)]

/-! ### The base case -/

/-- The base case of the induction: for `m ≤ h` the union bound over the scales
`L ≤ m` already gives the asserted bound (ABK26). -/
private theorem measure_clusterEvent₂_base [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℕ → (Fin d → ℤ) → Set Ω} {a b T : ℝ} {h m : ℕ}
    (hm : m ≤ h) (ha0 : 0 ≤ a) (hb0 : 0 < b) (hT2 : 0 < T ^ 2) (hmT : (m : ℝ) ≤ T ^ 2 / 2)
    (hB : ∀ (L : ℕ) (w : Fin d → ℤ),
      μ (B L w) ≤ ENNReal.ofReal (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * (L : ℝ))))))
    (w : Fin d → ℤ) :
    μ (clusterEvent₂ B m w)
      ≤ ENNReal.ofReal (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (b * ((m : ℝ) - (h : ℝ))) / 2))) := by
  have hsub : clusterEvent₂ B m w ⊆ scaleUnion B m w := by
    rintro ω ⟨N, x, h0, -, -, hbad⟩
    have hstart := hbad 0 (Nat.zero_le N)
    rwa [h0] at hstart
  have hrw : scaleUnion B m w = ⋃ L ∈ Finset.range (m + 1), B L w := by
    ext ω
    simp only [scaleUnion, Set.mem_iUnion, Set.mem_Iic, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨L, hL, hmem⟩; exact ⟨L, by omega, hmem⟩
    · rintro ⟨L, hL, hmem⟩; exact ⟨L, by omega, hmem⟩
  have hterm : ∀ L ∈ Finset.range (m + 1),
      μ (B L w) ≤ ENNReal.ofReal (Real.exp (-(T ^ 2))) := by
    intro L _
    refine le_trans (hB L w) (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (a * (L : ℝ)) :=
      one_le_three_rpow (mul_nonneg ha0 (Nat.cast_nonneg L))
    have h2 : T ^ 2 * 1 ≤ T ^ 2 * (3 : ℝ) ^ (a * (L : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 hT2.le
    linarith only [h2]
  have hmhR : (m : ℝ) ≤ (h : ℝ) := by exact_mod_cast hm
  calc μ (clusterEvent₂ B m w) ≤ μ (scaleUnion B m w) := measure_mono hsub
    _ = μ (⋃ L ∈ Finset.range (m + 1), B L w) := by rw [hrw]
    _ ≤ ∑ L ∈ Finset.range (m + 1), μ (B L w) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _L ∈ Finset.range (m + 1), ENNReal.ofReal (Real.exp (-(T ^ 2))) :=
        Finset.sum_le_sum hterm
    _ = ((m + 1 : ℕ) : ENNReal) * ENNReal.ofReal (Real.exp (-(T ^ 2))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ENNReal.ofReal (((m : ℝ) + 1) * Real.exp (-(T ^ 2))) := by
        rw [ENNReal.ofReal_mul (by positivity), show (((m : ℝ) + 1)) = ((m + 1 : ℕ) : ℝ) by
          push_cast; ring, ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (base_real_bound₂ hmhR hb0 hT2 hmT)

/-! ### The induction -/

/-- **The induction `e.Ck.indy.hyp` of ABK26, for distance-two paths.**

Under the finite-range independence hypothesis of `l.percolation.bound.general`
— literally the hypothesis the proved distance-one layer consumes — and the
tail bound `e.badevent.upperbound.appendix`, every distance-two cluster event
obeys `μ(𝒞_k(z)) ≤ exp(-½ T² 3^{b(k-h)})`.

The hypotheses, including the threshold `16 d 9^h ≤ T² b`, are identical to the
distance-one `measure_clusterEvent_le_exp`. -/
theorem measure_clusterEvent₂_le_exp [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℕ → (Fin d → ℤ) → Set Ω} {a b T : ℝ} {h : ℕ}
    (hd : 1 ≤ d) (hh : 3 ≤ h)
    (hb0 : 0 < b) (hb1 : b ≤ 1) (hba : b ≤ a)
    (hgain : 8 ≤ (1 - b) * (h : ℝ))
    (hT : 16 * (d : ℝ) * 9 ^ h ≤ T ^ 2 * b)
    (hindep : ∀ (l : ℕ) (S S' : Set (Fin d → ℤ)),
      (∀ u ∈ S, ∀ v ∈ S', 3 ^ l < latDist u v) →
        Indep (siteSigma B S l) (siteSigma B S' l) μ)
    (hB : ∀ (L : ℕ) (w : Fin d → ℤ),
      μ (B L w) ≤ ENNReal.ofReal (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * (L : ℝ))))))
    (k : ℕ) (z : Fin d → ℤ) :
    μ (clusterEvent₂ B k z)
      ≤ ENNReal.ofReal (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (b * ((k : ℝ) - (h : ℝ))) / 2))) := by
  classical
  have hL2 : Real.log 3 ≤ 2 := log_three_le_two
  have ha0 : 0 < a := lt_of_lt_of_le hb0 hba
  have hD1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hE27 : (27 : ℝ) ≤ (3 : ℝ) ^ h := by
    have hnat : (27 : ℕ) ≤ 3 ^ h := by
      calc (27 : ℕ) = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ h := Nat.pow_le_pow_right (by omega) hh
    exact_mod_cast hnat
  have hEh : (h : ℝ) + 2 ≤ (3 : ℝ) ^ h := by
    have hnat : h + 2 ≤ 3 ^ h := add_two_le_three_pow h (by omega)
    exact_mod_cast hnat
  have hhr : (3 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hTb : 16 * (d : ℝ) * ((3 : ℝ) ^ h * (3 : ℝ) ^ h) ≤ T ^ 2 * b := by
    rw [show (3 : ℝ) ^ h * (3 : ℝ) ^ h = (9 : ℝ) ^ h by
      rw [show (9 : ℝ) = 3 * 3 by norm_num, mul_pow]]
    exact hT
  have hDEEpos : (0 : ℝ) < (d : ℝ) * ((3 : ℝ) ^ h * (3 : ℝ) ^ h) :=
    mul_pos (by linarith only [hD1])
      (mul_pos (by linarith only [hE27]) (by linarith only [hE27]))
  have hT2bpos : (0 : ℝ) < T ^ 2 * b :=
    lt_of_lt_of_le (by linarith only [hDEEpos]) hTb
  have hT2 : (0 : ℝ) < T ^ 2 := by
    rcases lt_or_eq_of_le (sq_nonneg T) with hlt | heq
    · exact hlt
    · exfalso; rw [← heq] at hT2bpos; simp at hT2bpos
  have hhalf : (h : ℝ) ≤ T ^ 2 / 2 := scale_le_half_sq₂ hD1 hE27 hEh hTb hb1 hT2
  have main : ∀ K m : ℕ, m ≤ K → ∀ w : Fin d → ℤ,
      μ (clusterEvent₂ B m w)
        ≤ ENNReal.ofReal (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (b * ((m : ℝ) - (h : ℝ))) / 2))) := by
    intro K
    induction K with
    | zero =>
        intro m hm w
        have hmh : m ≤ h := by omega
        refine measure_clusterEvent₂_base hmh ha0.le hb0 hT2 ?_ hB w
        have hmhR : (m : ℝ) ≤ (h : ℝ) := by exact_mod_cast hmh
        linarith only [hmhR, hhalf]
    | succ K ihK =>
        intro m hm w
        by_cases hmh : m ≤ h
        · refine measure_clusterEvent₂_base hmh ha0.le hb0 hT2 ?_ hB w
          have hmR : (m : ℝ) ≤ (h : ℝ) := by exact_mod_cast hmh
          linarith only [hmR, hhalf]
        · push Not at hmh
          obtain ⟨j, rfl⟩ : ∃ j, m = j + h := ⟨m - h, by omega⟩
          have hjK : j ≤ K := by omega
          have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
          have hp : ∀ v : Fin d → ℤ,
              μ (clusterEvent₂ B j v)
                ≤ ENNReal.ofReal
                    (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (b * ((j : ℝ) - (h : ℝ))) / 2))) :=
            fun v => ihK j hjK v
          have hq : ∀ (l : ℕ) (v : Fin d → ℤ), j + 1 ≤ l → l ≤ j + h →
              μ (B l v)
                ≤ ENNReal.ofReal (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * ((j : ℝ) + 1))))) := by
            intro l v hl1 _
            refine le_trans (hB l v) (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
            have hlR : (j : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hl1
            have hmono : (3 : ℝ) ^ (a * ((j : ℝ) + 1)) ≤ (3 : ℝ) ^ (a * (l : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num)
                (mul_le_mul_of_nonneg_left hlR ha0.le)
            have hTmono : T ^ 2 * (3 : ℝ) ^ (a * ((j : ℝ) + 1))
                ≤ T ^ 2 * (3 : ℝ) ^ (a * (l : ℝ)) :=
              mul_le_mul_of_nonneg_left hmono hT2.le
            linarith only [hTmono]
          have hiter := measure_clusterEvent₂_add_le (μ := μ) (B := B) (k := j) (h := h)
            hh (hindep j) hp hq w
          have hcast : (((j + h : ℕ) : ℝ) - (h : ℝ)) = (j : ℝ) := by push_cast; ring
          have hnr : ((d * (j + h + 2) : ℕ) : ℝ)
              = (d : ℝ) * ((j : ℝ) + (h : ℝ) + 2) := by push_cast; ring
          have hMr27 : ((3 ^ (h - 3) : ℕ) : ℝ) * 27 = (3 : ℝ) ^ h := by
            have hnat : (3 : ℕ) ^ (h - 3) * 27 = 3 ^ h := by
              rw [show (27 : ℕ) = 3 ^ 3 from rfl, ← pow_add,
                show h - 3 + 3 = h from by omega]
            exact_mod_cast hnat
          have hstep1 := exp_step_one₂ (D := (d : ℝ)) (E := (3 : ℝ) ^ h)
            (Mr := ((3 ^ (h - 3) : ℕ) : ℝ)) (nr := ((d * (j + h + 2) : ℕ) : ℝ))
            (S := (3 : ℝ) ^ (b * (j : ℝ)))
            (R := (3 : ℝ) ^ (b * ((j : ℝ) - (h : ℝ)))) (jr := (j : ℝ)) (hr := (h : ℝ))
            (T := T) (b := b) hD1 hE27 hMr27 (Nat.cast_nonneg _) hhr hEh hj0 hnr hL2 hTb hT2
            hb1 (separated_gain₂ hh hgain)
            (one_add_le_three_rpow (mul_nonneg hb0.le hj0))
          have hstep2 := exp_step_two₂ (D := (d : ℝ)) (E := (3 : ℝ) ^ h)
            (nr := ((d * (j + h + 2) : ℕ) : ℝ)) (S := (3 : ℝ) ^ (b * (j : ℝ)))
            (U := (3 : ℝ) ^ (a * ((j : ℝ) + 1))) (jr := (j : ℝ)) (hr := (h : ℝ))
            (T := T) (a := a) (b := b) hD1 hE27 hhr hEh hj0 hnr hL2 hTb hT2 hb1 hba
            (by
              have h1 := one_add_le_three_rpow (x := a * (j : ℝ)) (mul_nonneg ha0.le hj0)
              have h2 : (3 : ℝ) ^ (a * (j : ℝ)) ≤ (3 : ℝ) ^ (a * ((j : ℝ) + 1)) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [ha0])
              linarith only [h1, h2])
            (Real.rpow_le_rpow_of_exponent_le (by norm_num)
              (by linarith only [ha0, mul_le_mul_of_nonneg_right hba hj0]))
          calc μ (clusterEvent₂ B (j + h) w)
              ≤ ((3 : ENNReal) ^ (d * (j + h + 2))
                    * ENNReal.ofReal
                        (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (b * ((j : ℝ) - (h : ℝ))) / 2))))
                      ^ (3 ^ (h - 3))
                  + (3 : ENNReal) ^ (d * (j + h + 2)) * (h : ENNReal)
                    * ENNReal.ofReal
                        (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * ((j : ℝ) + 1))))) := hiter
            _ ≤ ENNReal.ofReal (Real.exp (((3 ^ (h - 3) : ℕ) : ℝ)
                    * (((d * (j + h + 2) : ℕ) : ℝ) * Real.log 3
                      + -(T ^ 2 * (3 : ℝ) ^ (b * ((j : ℝ) - (h : ℝ))) / 2))))
                  + ENNReal.ofReal (Real.exp (((d * (j + h + 2) : ℕ) : ℝ) * Real.log 3
                      + (h : ℝ) + -(T ^ 2 * (3 : ℝ) ^ (a * ((j : ℝ) + 1))))) := by
                refine add_le_add (le_of_eq ?_) (enn_three_pow_mul_natCast_mul_le _ _ _)
                rw [enn_mul_ofReal_exp, enn_pow_ofReal_exp]
            _ = ENNReal.ofReal (Real.exp (((3 ^ (h - 3) : ℕ) : ℝ)
                    * (((d * (j + h + 2) : ℕ) : ℝ) * Real.log 3
                      + -(T ^ 2 * (3 : ℝ) ^ (b * ((j : ℝ) - (h : ℝ))) / 2)))
                  + Real.exp (((d * (j + h + 2) : ℕ) : ℝ) * Real.log 3
                      + (h : ℝ) + -(T ^ 2 * (3 : ℝ) ^ (a * ((j : ℝ) + 1))))) :=
                (ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)).symm
            _ ≤ ENNReal.ofReal (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (b * (j : ℝ)) / 2))) :=
                ENNReal.ofReal_le_ofReal (exp_add_exp_le hstep1 hstep2)
            _ = ENNReal.ofReal
                  (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (b * (((j + h : ℕ) : ℝ) - (h : ℝ))) / 2))) := by
                rw [hcast]
  exact main k k le_rfl z

/-! ### The distance-two crossing event -/

/-- The event of ABK26 `e.diameter.bound` with distance-two paths: some
distance-two lattice path from `ℤ^d ∩ □_k` to `ℤ^d \ □_{k+1}` has `B(z) = ⋃_L
B_L(z)` occurring at each site. -/
def crossingEvent₂ (B : ℕ → (Fin d → ℤ) → Set Ω) (k : ℕ) : Set Ω :=
  {ω | ∃ (z : Fin d → ℤ) (N : ℕ) (x : ℕ → Fin d → ℤ), z ∈ cubeAt k 0 ∧ x 0 = z ∧
    IsLatticePath₂ x N ∧ x N ∉ cubeAt (k + 1) 0 ∧ ∀ i, i ≤ N → ω ∈ ⋃ L : ℕ, B L (x i)}


/-- **The union bound of ABK26, for distance-two paths.** -/
theorem crossingEvent₂_subset (B : ℕ → (Fin d → ℤ) → Set Ω) (k : ℕ) :
    crossingEvent₂ B k ⊆
      (⋃ z ∈ locBox₂ k (0 : Fin d → ℤ), clusterEvent₂ B k z)
        ∪ ⋃ z' ∈ locBox₂ (k + 1) (0 : Fin d → ℤ), ⋃ (j : ℕ) (_ : k < j), B j z' := by
  classical
  rintro ω ⟨z, N, x, hz, h0, hpath, hout, hbad⟩
  have hzc : 2 * latDist (0 : Fin d → ℤ) z < 3 ^ k := mem_cubeAt_iff.mp hz
  have hsucc : (3 : ℕ) ^ (k + 1) = 3 ^ k * 3 := by rw [pow_succ]
  have hxout : x N ∉ cubeAt k z := by
    obtain ⟨j, hj⟩ : ∃ j, ¬ 2 * (x N j - (0 : Fin d → ℤ) j).natAbs < 3 ^ (k + 1) := by
      by_contra hcon
      exact hout fun j => by
        by_contra hcon2
        exact hcon ⟨j, hcon2⟩
    have hjz : (z j - (0 : Fin d → ℤ) j).natAbs ≤ latDist (0 : Fin d → ℤ) z := by
      have := coord_le_latDist (0 : Fin d → ℤ) z j
      omega
    intro hmem
    have := hmem j
    omega
  obtain ⟨M₀, hM₀N, hM₀out, hM₀loc⟩ := exists_truncated_path₂ h0 hpath hxout
  have hbig : ∀ i, i ≤ M₀ → x i ∈ locBox₂ (k + 1) (0 : Fin d → ℤ) := by
    intro i hi
    have htri : latDist (0 : Fin d → ℤ) (x i)
        ≤ latDist (0 : Fin d → ℤ) z + latDist z (x i) := latDist_triangle _ _ _
    have := hM₀loc i hi
    exact mem_locBox₂_iff.mpr (by omega)
  by_cases hcase : ∃ i, i ≤ M₀ ∧ ∃ j, k < j ∧ ω ∈ B j (x i)
  · obtain ⟨i, hi, j, hj, hmem⟩ := hcase
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨x i, hbig i hi,
      Set.mem_iUnion₂.mpr ⟨j, hj, hmem⟩⟩)
  · push Not at hcase
    refine Or.inl (Set.mem_iUnion₂.mpr ⟨z, mem_locBox₂_iff.mpr (by omega), ?_⟩)
    refine ⟨M₀, x, h0, hpath.mono hM₀N, hM₀out, fun i hi => ?_⟩
    obtain ⟨L, hmem⟩ := Set.mem_iUnion.mp (hbad i (le_trans hi hM₀N))
    refine mem_scaleUnion_iff.mpr ⟨L, ?_, hmem⟩
    by_contra hcon
    exact absurd hmem (hcase i hi L (by omega))

/-! ### The geometric tail over the large scales -/

/-- A geometric series bound: exponentials whose exponents decrease by at least
one unit per step sum to at most twice the first term. -/
private theorem tsum_ofReal_exp_sub_natCast_le₂ (A : ℝ) :
    ∑' i : ℕ, ENNReal.ofReal (Real.exp (A - i)) ≤ ENNReal.ofReal (2 * Real.exp A) := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  have hprod : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  have hexpneg : Real.exp (-1) ≤ 1 / 2 := by
    linarith only [hprod, mul_nonneg (by linarith only [he2] : (0 : ℝ) ≤ Real.exp 1 - 2)
      (Real.exp_pos (-1)).le]
  have hgeom : ∀ i : ℕ, Real.exp (A - i) = Real.exp A * Real.exp (-1) ^ i := by
    intro i
    rw [← exp_natMul, ← Real.exp_add]
    congr 1
    ring
  have hpow : ∀ i : ℕ, Real.exp (-1) ^ i ≤ (1 / 2 : ℝ) ^ i := by
    intro i
    induction i with
    | zero => norm_num
    | succ n ih =>
        have h0 : (0 : ℝ) ≤ Real.exp (-1) ^ n := pow_nonneg (Real.exp_nonneg _) n
        rw [pow_succ, pow_succ]
        linarith only
          [mul_nonneg h0 (by linarith only [hexpneg] : (0 : ℝ) ≤ 1 / 2 - Real.exp (-1)),
           mul_nonneg (by linarith only [ih] : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n - Real.exp (-1) ^ n)
             (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))]
  have hbound : ∀ i : ℕ, Real.exp (A - i) ≤ Real.exp A * (1 / 2 : ℝ) ^ i := by
    intro i
    rw [hgeom i]
    linarith only [mul_nonneg (Real.exp_pos A).le
      (by linarith only [hpow i] : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ i - Real.exp (-1) ^ i)]
  have hsummable2 : Summable fun i : ℕ => Real.exp A * (1 / 2 : ℝ) ^ i :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hsummable : Summable fun i : ℕ => Real.exp (A - i) :=
    hsummable2.of_nonneg_of_le (fun i => (Real.exp_pos _).le) hbound
  have hsum : ∑' i : ℕ, Real.exp (A - i) ≤ 2 * Real.exp A := by
    refine le_trans (hsummable.tsum_le_tsum hbound hsummable2) ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
    linarith only []
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => (Real.exp_pos _).le) hsummable]
  exact ENNReal.ofReal_le_ofReal hsum

/-- The tail `⋃_{j > k} B_j(z)` of the bad events at a fixed site
(ABK26). -/
private theorem measure_iUnion_gt_le₂ [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℕ → (Fin d → ℤ) → Set Ω} {a T : ℝ} (ha0 : 0 < a) (hT2 : 0 < T ^ 2)
    (hTa : 1 ≤ T ^ 2 * a)
    (hB : ∀ (L : ℕ) (w : Fin d → ℤ),
      μ (B L w) ≤ ENNReal.ofReal (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * (L : ℝ))))))
    (k : ℕ) (z : Fin d → ℤ) :
    μ (⋃ (j : ℕ) (_ : k < j), B j z)
      ≤ ENNReal.ofReal (2 * Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * ((k : ℝ) + 1))))) := by
  have hrw : (⋃ (j : ℕ) (_ : k < j), B j z) = ⋃ i : ℕ, B (k + 1 + i) z := by
    ext ω
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨j, hj, hmem⟩
      exact ⟨j - (k + 1), by rwa [show k + 1 + (j - (k + 1)) = j from by omega]⟩
    · rintro ⟨i, hmem⟩
      exact ⟨k + 1 + i, by omega, hmem⟩
  have hV : (1 : ℝ) ≤ (3 : ℝ) ^ (a * ((k : ℝ) + 1)) :=
    one_le_three_rpow (mul_nonneg ha0.le (by positivity))
  have hVpos : (0 : ℝ) ≤ (3 : ℝ) ^ (a * ((k : ℝ) + 1)) := by positivity
  have hterm : ∀ i : ℕ, μ (B (k + 1 + i) z)
      ≤ ENNReal.ofReal
          (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * ((k : ℝ) + 1))) - i)) := by
    intro i
    refine le_trans (hB _ z) (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    have hsplit : (3 : ℝ) ^ (a * ((k + 1 + i : ℕ) : ℝ))
        = (3 : ℝ) ^ (a * ((k : ℝ) + 1)) * (3 : ℝ) ^ (a * (i : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      push_cast; ring
    have hW : 1 + a * (i : ℝ) ≤ (3 : ℝ) ^ (a * (i : ℝ)) :=
      one_add_le_three_rpow (mul_nonneg ha0.le (Nat.cast_nonneg i))
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have h1 := mul_nonneg (mul_nonneg hT2.le hVpos)
      (by linarith only [hW] : (0 : ℝ) ≤ (3 : ℝ) ^ (a * (i : ℝ)) - 1 - a * (i : ℝ))
    have h2a := mul_nonneg (mul_nonneg hT2.le ha0.le)
      (by linarith only [hV] : (0 : ℝ) ≤ (3 : ℝ) ^ (a * ((k : ℝ) + 1)) - 1)
    have h2b := mul_nonneg
      (by linarith only [hTa, h2a] :
        (0 : ℝ) ≤ T ^ 2 * a * (3 : ℝ) ^ (a * ((k : ℝ) + 1)) - 1) hi0
    rw [hsplit]
    linarith only [h1, h2b]
  calc μ (⋃ (j : ℕ) (_ : k < j), B j z) = μ (⋃ i : ℕ, B (k + 1 + i) z) := by rw [hrw]
    _ ≤ ∑' i : ℕ, μ (B (k + 1 + i) z) := measure_iUnion_le _
    _ ≤ ∑' i : ℕ,
          ENNReal.ofReal (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * ((k : ℝ) + 1))) - i)) :=
        ENNReal.tsum_le_tsum hterm
    _ ≤ _ := tsum_ofReal_exp_sub_natCast_le₂ _

/-! ### The scalar inequalities of the final union bound -/

/-- The exponent estimate for the cluster-event term of the final union bound;
the entropy is `D (kr + 2)` instead of the distance-one `D (kr + 1)`. -/
private theorem crossing_exp_one₂ {D Eh nr S R γ kr T b : ℝ}
    (hD1 : 1 ≤ D) (hE27 : 27 ≤ Eh) (hnr : nr = D * (kr + 2)) (hkr : 0 ≤ kr)
    (hL2 : Real.log 3 ≤ 2) (hTb : 16 * D * (Eh * Eh) ≤ T ^ 2 * b) (hT2 : 0 < T ^ 2)
    (hb1 : b ≤ 1) (hS1 : 1 + b * kr ≤ S) (hSR : S ≤ Eh * R) (hR0 : 0 ≤ R)
    (hγ : 8 * Eh * γ ≤ T ^ 2 * S) :
    nr * Real.log 3 + -(T ^ 2 * R / 2) + 1 ≤ -γ := by
  have hEhpos : (0 : ℝ) < Eh := by linarith only [hE27]
  have hA : nr * Real.log 3 ≤ 2 * (D * (kr + 2)) := by
    rw [hnr]
    linarith only [mul_nonneg (mul_nonneg (by linarith only [hD1] : (0 : ℝ) ≤ D)
      (by linarith only [hkr] : (0 : ℝ) ≤ kr + 2))
      (by linarith only [hL2] : (0 : ℝ) ≤ 2 - Real.log 3)]
  have h1 : 8 * Eh * (nr * Real.log 3 + 1) ≤ 8 * Eh * (2 * (D * (kr + 2)) + 1) := by
    linarith only [mul_nonneg (by linarith only [hE27] : (0 : ℝ) ≤ 8 * Eh)
      (by linarith only [hA] : (0 : ℝ) ≤ 2 * (D * (kr + 2)) + 1 - (nr * Real.log 3 + 1))]
  have h2 : 16 * (D * Eh) * kr ≤ 16 * (D * (Eh * Eh)) * kr := by
    linarith only [mul_nonneg (mul_nonneg (mul_nonneg
      (by linarith only [hD1] : (0 : ℝ) ≤ 16 * D)
      (by linarith only [hE27] : (0 : ℝ) ≤ Eh))
      (by linarith only [hE27] : (0 : ℝ) ≤ Eh - 1)) hkr]
  have h3 : 32 * (D * Eh) + 8 * Eh ≤ 16 * (D * (Eh * Eh)) := by
    linarith only [mul_nonneg (mul_nonneg (by linarith only [hD1] : (0 : ℝ) ≤ D)
        (by linarith only [hE27] : (0 : ℝ) ≤ Eh))
        (by linarith only [hE27] : (0 : ℝ) ≤ 16 * Eh - 40),
      mul_nonneg (by linarith only [hE27] : (0 : ℝ) ≤ Eh)
        (by linarith only [hD1] : (0 : ℝ) ≤ D - 1)]
  have h5 : 16 * (D * (Eh * Eh)) ≤ T ^ 2 := by
    linarith only [hTb, mul_nonneg hT2.le (by linarith only [hb1] : (0 : ℝ) ≤ 1 - b)]
  have h6 : 16 * (D * (Eh * Eh)) * kr ≤ T ^ 2 * b * kr := by
    linarith only [mul_nonneg
      (by linarith only [hTb] : (0 : ℝ) ≤ T ^ 2 * b - 16 * D * (Eh * Eh)) hkr]
  have h4 : T ^ 2 + T ^ 2 * b * kr ≤ T ^ 2 * S := by
    linarith only [mul_nonneg hT2.le (by linarith only [hS1] : (0 : ℝ) ≤ S - 1 - b * kr)]
  have hent : 8 * Eh * (nr * Real.log 3 + 1) ≤ T ^ 2 * S := by
    linarith only [h1, h2, h3, h4, h5, h6]
  have hX : T ^ 2 * S ≤ 2 * Eh * (T ^ 2 * R) := by
    linarith only [mul_nonneg hT2.le (by linarith only [hSR] : (0 : ℝ) ≤ Eh * R - S),
      mul_nonneg (mul_nonneg (by linarith only [hE27] : (0 : ℝ) ≤ Eh) hT2.le) hR0]
  have hcomb : Eh * (8 * (nr * Real.log 3 + 1 + γ)) ≤ Eh * (4 * (T ^ 2 * R)) := by
    linarith only [hent, hγ, hX]
  linarith only [le_of_mul_le_mul_left hcomb hEhpos]

/-- The exponent estimate for the large-scale term of the final union bound. -/
private theorem crossing_exp_two₂ {D Eh nr2 S U γ kr T a b : ℝ}
    (hD1 : 1 ≤ D) (hE27 : 27 ≤ Eh) (hnr2 : nr2 = D * (kr + 3)) (hkr : 0 ≤ kr)
    (hL2 : Real.log 3 ≤ 2) (hTb : 16 * D * (Eh * Eh) ≤ T ^ 2 * b) (hT2 : 0 < T ^ 2)
    (hb1 : b ≤ 1) (hba : b ≤ a) (hU1 : 1 + a * kr ≤ U) (hSU : S ≤ U)
    (hγ0 : 0 ≤ γ) (hγ : 8 * Eh * γ ≤ T ^ 2 * S) :
    nr2 * Real.log 3 + (-(T ^ 2 * U) + 1) + 1 ≤ -γ := by
  have hA2 : nr2 * Real.log 3 ≤ 2 * (D * (kr + 3)) := by
    rw [hnr2]
    linarith only [mul_nonneg (mul_nonneg (by linarith only [hD1] : (0 : ℝ) ≤ D)
      (by linarith only [hkr] : (0 : ℝ) ≤ kr + 3))
      (by linarith only [hL2] : (0 : ℝ) ≤ 2 - Real.log 3)]
  have hTa : T ^ 2 * b ≤ T ^ 2 * a := by
    linarith only [mul_nonneg hT2.le (by linarith only [hba] : (0 : ℝ) ≤ a - b)]
  have h5 : 16 * (D * (Eh * Eh)) ≤ T ^ 2 := by
    linarith only [hTb, mul_nonneg hT2.le (by linarith only [hb1] : (0 : ℝ) ≤ 1 - b)]
  have h6 : 16 * (D * (Eh * Eh)) * kr ≤ T ^ 2 * a * kr := by
    linarith only [mul_nonneg
      (by linarith only [hTb, hTa] : (0 : ℝ) ≤ T ^ 2 * a - 16 * D * (Eh * Eh)) hkr]
  have h4 : T ^ 2 + T ^ 2 * a * kr ≤ T ^ 2 * U := by
    linarith only [mul_nonneg hT2.le (by linarith only [hU1] : (0 : ℝ) ≤ U - 1 - a * kr)]
  have hEE : (729 : ℝ) ≤ Eh * Eh := by linarith only [hE27, sq_nonneg (Eh - 27)]
  have hcst : 12 * D + 4 ≤ 16 * (D * (Eh * Eh)) := by
    linarith only [hD1, mul_nonneg (by linarith only [hD1] : (0 : ℝ) ≤ D)
      (by linarith only [hEE] : (0 : ℝ) ≤ Eh * Eh - 1)]
  have hkterm : 4 * D * kr ≤ 16 * (D * (Eh * Eh)) * kr := by
    linarith only [mul_nonneg (mul_nonneg (by linarith only [hD1] : (0 : ℝ) ≤ D)
      (by linarith only [hEE] : (0 : ℝ) ≤ 16 * (Eh * Eh) - 4)) hkr]
  have hmain : 2 * (nr2 * Real.log 3 + 2) ≤ T ^ 2 * U := by
    linarith only [hA2, hkterm, h6, hcst, h5, h4]
  have hγU : 8 * γ ≤ T ^ 2 * U := by
    have hg1 : 8 * γ ≤ 8 * Eh * γ := by
      linarith only [mul_nonneg hγ0 (by linarith only [hE27] : (0 : ℝ) ≤ Eh - 1)]
    have hg2 : T ^ 2 * S ≤ T ^ 2 * U := by
      linarith only [mul_nonneg hT2.le (by linarith only [hSU] : (0 : ℝ) ≤ U - S)]
    linarith only [hg1, hg2, hγ]
  linarith only [hmain, hγU, hγ0]

/-! ### The distance-two diameter bound -/

/-- **The maximal diameter bound for distance-two crossings, with the scale `h`
and the target exponent `γ` left explicit.** -/
theorem measure_crossingEvent₂_le_exp_of_scale [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℕ → (Fin d → ℤ) → Set Ω} {a b T γ : ℝ} {h : ℕ}
    (hd : 1 ≤ d) (hh : 3 ≤ h) (hb0 : 0 < b) (hb1 : b ≤ 1) (hba : b ≤ a)
    (hgain : 8 ≤ (1 - b) * (h : ℝ))
    (hT : 16 * (d : ℝ) * 9 ^ h ≤ T ^ 2 * b)
    (hindep : ∀ (l : ℕ) (S S' : Set (Fin d → ℤ)),
      (∀ u ∈ S, ∀ v ∈ S', 3 ^ l < latDist u v) →
        Indep (siteSigma B S l) (siteSigma B S' l) μ)
    (hB : ∀ (L : ℕ) (w : Fin d → ℤ),
      μ (B L w) ≤ ENNReal.ofReal (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * (L : ℝ))))))
    (k : ℕ) (hγ0 : 0 ≤ γ)
    (hγ : 8 * (3 : ℝ) ^ h * γ ≤ T ^ 2 * (3 : ℝ) ^ (b * (k : ℝ))) :
    μ (crossingEvent₂ B k) ≤ ENNReal.ofReal (Real.exp (-γ)) := by
  classical
  have hL2 : Real.log 3 ≤ 2 := log_three_le_two
  have ha0 : 0 < a := lt_of_lt_of_le hb0 hba
  have hD1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hE27 : (27 : ℝ) ≤ (3 : ℝ) ^ h := by
    have hnat : (27 : ℕ) ≤ 3 ^ h := by
      calc (27 : ℕ) = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ h := Nat.pow_le_pow_right (by omega) hh
    exact_mod_cast hnat
  have hTb : 16 * (d : ℝ) * ((3 : ℝ) ^ h * (3 : ℝ) ^ h) ≤ T ^ 2 * b := by
    rw [show (3 : ℝ) ^ h * (3 : ℝ) ^ h = (9 : ℝ) ^ h by
      rw [show (9 : ℝ) = 3 * 3 by norm_num, mul_pow]]
    exact hT
  have hDEEpos : (0 : ℝ) < (d : ℝ) * ((3 : ℝ) ^ h * (3 : ℝ) ^ h) :=
    mul_pos (by linarith only [hD1])
      (mul_pos (by linarith only [hE27]) (by linarith only [hE27]))
  have hT2bpos : (0 : ℝ) < T ^ 2 * b :=
    lt_of_lt_of_le (by linarith only [hDEEpos]) hTb
  have hT2 : (0 : ℝ) < T ^ 2 := by
    rcases lt_or_eq_of_le (sq_nonneg T) with hlt | heq
    · exact hlt
    · exfalso; rw [← heq] at hT2bpos; simp at hT2bpos
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hfirst : μ (⋃ z ∈ locBox₂ k (0 : Fin d → ℤ), clusterEvent₂ B k z)
      ≤ ENNReal.ofReal (Real.exp (((d * (k + 2) : ℕ) : ℝ) * Real.log 3
          + -(T ^ 2 * (3 : ℝ) ^ (b * ((k : ℝ) - (h : ℝ))) / 2))) := by
    have hc : ((locBox₂ k (0 : Fin d → ℤ)).card : ENNReal)
        ≤ (3 : ENNReal) ^ (d * (k + 2)) := by
      calc ((locBox₂ k (0 : Fin d → ℤ)).card : ENNReal)
          ≤ ((3 ^ (d * (k + 2)) : ℕ) : ENNReal) :=
            Nat.cast_le.mpr (card_locBox₂_le k (0 : Fin d → ℤ))
        _ = (3 : ENNReal) ^ (d * (k + 2)) := by push_cast; ring
    calc μ (⋃ z ∈ locBox₂ k (0 : Fin d → ℤ), clusterEvent₂ B k z)
        ≤ ∑ z ∈ locBox₂ k (0 : Fin d → ℤ), μ (clusterEvent₂ B k z) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _z ∈ locBox₂ k (0 : Fin d → ℤ),
            ENNReal.ofReal
              (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (b * ((k : ℝ) - (h : ℝ))) / 2))) :=
          Finset.sum_le_sum fun z _ =>
            measure_clusterEvent₂_le_exp hd hh hb0 hb1 hba hgain hT hindep hB k z
      _ = ((locBox₂ k (0 : Fin d → ℤ)).card : ENNReal)
            * ENNReal.ofReal
              (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (b * ((k : ℝ) - (h : ℝ))) / 2))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (3 : ENNReal) ^ (d * (k + 2))
            * ENNReal.ofReal
              (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (b * ((k : ℝ) - (h : ℝ))) / 2))) := by
          gcongr
      _ = _ := enn_mul_ofReal_exp _ _
  have hsecond : μ (⋃ z' ∈ locBox₂ (k + 1) (0 : Fin d → ℤ), ⋃ (j : ℕ) (_ : k < j), B j z')
      ≤ ENNReal.ofReal (Real.exp (((d * (k + 1 + 2) : ℕ) : ℝ) * Real.log 3
          + (-(T ^ 2 * (3 : ℝ) ^ (a * ((k : ℝ) + 1))) + 1))) := by
    have hTa : 1 ≤ T ^ 2 * a := by
      have hEE : (729 : ℝ) ≤ (3 : ℝ) ^ h * (3 : ℝ) ^ h := by
        linarith only [hE27, sq_nonneg ((3 : ℝ) ^ h - 27)]
      have hab : T ^ 2 * b ≤ T ^ 2 * a := by
        linarith only [mul_nonneg hT2.le (by linarith only [hba] : (0 : ℝ) ≤ a - b)]
      linarith only [hTb, hab, hD1, mul_nonneg (by linarith only [hD1] : (0 : ℝ) ≤ (d : ℝ))
        (by linarith only [hEE] : (0 : ℝ) ≤ (3 : ℝ) ^ h * (3 : ℝ) ^ h - 1)]
    have hc : ((locBox₂ (k + 1) (0 : Fin d → ℤ)).card : ENNReal)
        ≤ (3 : ENNReal) ^ (d * (k + 1 + 2)) := by
      calc ((locBox₂ (k + 1) (0 : Fin d → ℤ)).card : ENNReal)
          ≤ ((3 ^ (d * (k + 1 + 2)) : ℕ) : ENNReal) :=
            Nat.cast_le.mpr (card_locBox₂_le (k + 1) (0 : Fin d → ℤ))
        _ = (3 : ENNReal) ^ (d * (k + 1 + 2)) := by push_cast; ring
    have hdouble : ENNReal.ofReal
        (2 * Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * ((k : ℝ) + 1)))))
          ≤ ENNReal.ofReal
              (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * ((k : ℝ) + 1))) + 1)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.exp_add]
      have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
      linarith only [mul_nonneg (Real.exp_pos (-(T ^ 2 * (3 : ℝ) ^ (a * ((k : ℝ) + 1))))).le
        (by linarith only [he2] : (0 : ℝ) ≤ Real.exp 1 - 2)]
    calc μ (⋃ z' ∈ locBox₂ (k + 1) (0 : Fin d → ℤ), ⋃ (j : ℕ) (_ : k < j), B j z')
        ≤ ∑ z' ∈ locBox₂ (k + 1) (0 : Fin d → ℤ), μ (⋃ (j : ℕ) (_ : k < j), B j z') :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _z' ∈ locBox₂ (k + 1) (0 : Fin d → ℤ),
            ENNReal.ofReal
              (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * ((k : ℝ) + 1))) + 1)) :=
          Finset.sum_le_sum fun z' _ =>
            le_trans (measure_iUnion_gt_le₂ ha0 hT2 hTa hB k z') hdouble
      _ = ((locBox₂ (k + 1) (0 : Fin d → ℤ)).card : ENNReal)
            * ENNReal.ofReal
              (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * ((k : ℝ) + 1))) + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (3 : ENNReal) ^ (d * (k + 1 + 2))
            * ENNReal.ofReal
              (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * ((k : ℝ) + 1))) + 1)) := by gcongr
      _ = _ := enn_mul_ofReal_exp _ _
  have hnr : ((d * (k + 2) : ℕ) : ℝ) = (d : ℝ) * ((k : ℝ) + 2) := by push_cast; ring
  have hnr2 : ((d * (k + 1 + 2) : ℕ) : ℝ) = (d : ℝ) * ((k : ℝ) + 3) := by push_cast; ring
  have hSR : (3 : ℝ) ^ (b * (k : ℝ))
      ≤ (3 : ℝ) ^ h * (3 : ℝ) ^ (b * ((k : ℝ) - (h : ℝ))) := by
    rw [← Real.rpow_natCast 3 h, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    linarith only [mul_nonneg (Nat.cast_nonneg h : (0 : ℝ) ≤ (h : ℝ))
      (by linarith only [hb1] : (0 : ℝ) ≤ 1 - b)]
  have hstep1 := crossing_exp_one₂ (D := (d : ℝ)) (Eh := (3 : ℝ) ^ h)
    (nr := ((d * (k + 2) : ℕ) : ℝ)) (S := (3 : ℝ) ^ (b * (k : ℝ)))
    (R := (3 : ℝ) ^ (b * ((k : ℝ) - (h : ℝ)))) (γ := γ) (kr := (k : ℝ)) (T := T) (b := b)
    hD1 hE27 hnr hk0 hL2 hTb hT2 hb1
    (one_add_le_three_rpow (mul_nonneg hb0.le hk0)) hSR (by positivity) hγ
  have hstep2 := crossing_exp_two₂ (D := (d : ℝ)) (Eh := (3 : ℝ) ^ h)
    (nr2 := ((d * (k + 1 + 2) : ℕ) : ℝ)) (S := (3 : ℝ) ^ (b * (k : ℝ)))
    (U := (3 : ℝ) ^ (a * ((k : ℝ) + 1))) (γ := γ) (kr := (k : ℝ)) (T := T) (a := a) (b := b)
    hD1 hE27 hnr2 hk0 hL2 hTb hT2 hb1 hba
    (by
      have h1 := one_add_le_three_rpow (x := a * (k : ℝ)) (mul_nonneg ha0.le hk0)
      have h2 : (3 : ℝ) ^ (a * (k : ℝ)) ≤ (3 : ℝ) ^ (a * ((k : ℝ) + 1)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [ha0])
      linarith only [h1, h2])
    (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by linarith only [ha0, mul_le_mul_of_nonneg_right hba hk0])) hγ0 hγ
  refine le_trans (measure_mono (crossingEvent₂_subset B k))
    (le_trans (measure_union_le _ _) ?_)
  refine le_trans (add_le_add hfirst hsecond) ?_
  rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (exp_add_exp_le hstep1 hstep2)

/-- **ABK26, `l.percolation.bound.general`, conclusion (3), `e.diameter.bound`,
for distance-two crossings.**

Hypotheses and constants are *identical* to the proved distance-one
`measure_crossingEvent_le_exp`: the threshold `16 d exp(40 (1-b)^{-1}) ≤ T² b`
and the conclusion `exp(-½ exp(-40 (1-b)^{-1}) T² 3^{bk})` with the same
explicit `C = 40`. -/
theorem measure_crossingEvent₂_le_exp [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℕ → (Fin d → ℤ) → Set Ω} {a b T : ℝ}
    (hd : 1 ≤ d) (hb0 : 0 < b) (hb1 : b < 1) (hba : b ≤ a)
    (hT : 16 * (d : ℝ) * Real.exp (40 / (1 - b)) ≤ T ^ 2 * b)
    (hindep : ∀ (l : ℕ) (S S' : Set (Fin d → ℤ)),
      (∀ u ∈ S, ∀ v ∈ S', 3 ^ l < latDist u v) →
        Indep (siteSigma B S l) (siteSigma B S' l) μ)
    (hB : ∀ (L : ℕ) (w : Fin d → ℤ),
      μ (B L w) ≤ ENNReal.ofReal (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * (L : ℝ))))))
    (k : ℕ) :
    μ (crossingEvent₂ B k)
      ≤ ENNReal.ofReal (Real.exp
          (-(Real.exp (-(40 / (1 - b))) * T ^ 2 * (3 : ℝ) ^ (b * (k : ℝ)) / 2))) := by
  have hbb : (0 : ℝ) < 1 - b := by linarith only [hb1]
  have hmul : (1 - b) * (1 - b)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hbb)
  have hvpos : (0 : ℝ) < (1 - b)⁻¹ := inv_pos.mpr hbb
  have hv1 : (1 : ℝ) ≤ (1 - b)⁻¹ := by
    linarith only [hmul, mul_nonneg hvpos.le hb0.le]
  have hd8 : (8 : ℝ) / (1 - b) = 8 * (1 - b)⁻¹ := div_eq_mul_inv 8 (1 - b)
  have hd40 : (40 : ℝ) / (1 - b) = 40 * (1 - b)⁻¹ := div_eq_mul_inv 40 (1 - b)
  obtain ⟨h, hhdef⟩ : ∃ h : ℕ, h = ⌈(8 : ℝ) / (1 - b)⌉₊ := ⟨_, rfl⟩
  have hceil : (8 : ℝ) / (1 - b) ≤ (h : ℝ) := by rw [hhdef]; exact Nat.le_ceil _
  have hceil' : (h : ℝ) < 8 / (1 - b) + 1 := by
    rw [hhdef]; exact Nat.ceil_lt_add_one (div_nonneg (by norm_num) hbb.le)
  rw [hd8] at hceil hceil'
  have hh8 : 8 ≤ h := by
    have hR : (8 : ℝ) ≤ (h : ℝ) := by linarith only [hceil, hv1]
    exact_mod_cast hR
  have hh : 3 ≤ h := by omega
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hgain : 8 ≤ (1 - b) * (h : ℝ) := by
    linarith only [hmul, mul_nonneg hbb.le
      (by linarith only [hceil] : (0 : ℝ) ≤ (h : ℝ) - 8 * (1 - b)⁻¹)]
  have hlog3 : Real.log 3 ≤ 2 := log_three_le_two
  have hhlog : (h : ℝ) * Real.log 3 ≤ 2 * (h : ℝ) := by
    linarith only [mul_nonneg hh0 (by linarith only [hlog3] : (0 : ℝ) ≤ 2 - Real.log 3)]
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  have h3h : (3 : ℝ) ^ h = Real.exp ((h : ℝ) * Real.log 3) := (exp_natMul_log_three h).symm
  have h9le : (9 : ℝ) ^ h ≤ Real.exp (40 / (1 - b)) := by
    rw [show (9 : ℝ) = 3 * 3 by norm_num, mul_pow, h3h, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [hd40]
    linarith only [hhlog, hceil', hv1]
  have h4le : 4 * (3 : ℝ) ^ h ≤ Real.exp (40 / (1 - b)) := by
    have hexp2 : (4 : ℝ) ≤ Real.exp 2 := by
      have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have hsq : (2 : ℝ) * 2 ≤ Real.exp 1 * Real.exp 1 :=
        mul_le_mul hexp1 hexp1 (by norm_num) (by linarith only [hexp1])
      rw [he]
      linarith only [hsq]
    calc 4 * (3 : ℝ) ^ h ≤ Real.exp 2 * Real.exp ((h : ℝ) * Real.log 3) := by
          rw [← h3h]
          linarith only [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) h)
            (by linarith only [hexp2] : (0 : ℝ) ≤ Real.exp 2 - 4)]
      _ = Real.exp (2 + (h : ℝ) * Real.log 3) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (40 / (1 - b)) := by
          refine Real.exp_le_exp.mpr ?_
          rw [hd40]
          linarith only [hhlog, hceil', hv1]
  have hT' : 16 * (d : ℝ) * 9 ^ h ≤ T ^ 2 * b := by
    refine le_trans ?_ hT
    have hd0 : (0 : ℝ) ≤ 16 * (d : ℝ) := by positivity
    linarith only [mul_nonneg hd0
      (by linarith only [h9le] : (0 : ℝ) ≤ Real.exp (40 / (1 - b)) - 9 ^ h)]
  have hγ0 : (0 : ℝ)
      ≤ Real.exp (-(40 / (1 - b))) * T ^ 2 * (3 : ℝ) ^ (b * (k : ℝ)) / 2 := by positivity
  have hγ : 8 * (3 : ℝ) ^ h
        * (Real.exp (-(40 / (1 - b))) * T ^ 2 * (3 : ℝ) ^ (b * (k : ℝ)) / 2)
      ≤ T ^ 2 * (3 : ℝ) ^ (b * (k : ℝ)) := by
    have hprod : Real.exp (-(40 / (1 - b))) * Real.exp (40 / (1 - b)) = 1 := by
      rw [← Real.exp_add]; norm_num
    have hexppos : (0 : ℝ) < Real.exp (-(40 / (1 - b))) := Real.exp_pos _
    have hkey : 4 * (3 : ℝ) ^ h * Real.exp (-(40 / (1 - b))) ≤ 1 := by
      linarith only [hprod, mul_nonneg hexppos.le
        (by linarith only [h4le] : (0 : ℝ) ≤ Real.exp (40 / (1 - b)) - 4 * (3 : ℝ) ^ h)]
    have hTS : (0 : ℝ) ≤ T ^ 2 * (3 : ℝ) ^ (b * (k : ℝ)) := by positivity
    linarith only [mul_nonneg hTS
      (by linarith only [hkey] :
        (0 : ℝ) ≤ 1 - 4 * (3 : ℝ) ^ h * Real.exp (-(40 / (1 - b))))]
  exact measure_crossingEvent₂_le_exp_of_scale hd hh hb0 (le_of_lt hb1) hba hgain hT'
    hindep hB k hγ0 hγ

/-! ### The distance-two crossing event at an arbitrary base site -/

/-- The crossing event of ABK26 `e.diameter.bound` at an arbitrary base site `w`,
with distance-two paths. -/
def crossingEvent₂At (B : ℕ → (Fin d → ℤ) → Set Ω) (k : ℕ) (w : Fin d → ℤ) :
    Set Ω :=
  {ω | ∃ (z : Fin d → ℤ) (N : ℕ) (x : ℕ → Fin d → ℤ), z ∈ cubeAt k w ∧ x 0 = z ∧
    IsLatticePath₂ x N ∧ x N ∉ cubeAt (k + 1) w ∧ ∀ i, i ≤ N → ω ∈ ⋃ L : ℕ, B L (x i)}


/-- **The reindexing identity.**  The distance-two crossing event of `B` at base
site `w` is the origin-centred distance-two crossing event of the reindexed
family `shiftFamily B w`. -/
theorem crossingEvent₂At_eq_crossingEvent₂_shiftFamily
    (B : ℕ → (Fin d → ℤ) → Set Ω) (k : ℕ) (w : Fin d → ℤ) :
    crossingEvent₂At B k w = crossingEvent₂ (shiftFamily B w) k := by
  ext ω
  constructor
  · rintro ⟨z, N, x, hz, h0, hpath, hout, hbad⟩
    refine ⟨z - w, N, fun i => x i - w, mem_cubeAt_sub_zero.mpr hz, ?_, ?_, ?_, ?_⟩
    · show x 0 - w = z - w
      rw [h0]
    · intro i hi
      show latDist (x i - w) (x (i + 1) - w) ≤ 2
      rw [latDist_sub_right]
      exact hpath i hi
    · intro hmem
      exact hout (mem_cubeAt_sub_zero.mp hmem)
    · intro i hi
      obtain ⟨L, hL⟩ := Set.mem_iUnion.mp (hbad i hi)
      refine Set.mem_iUnion.2 ⟨L, ?_⟩
      show ω ∈ B L (x i - w + w)
      rwa [sub_add_cancel]
  · rintro ⟨z, N, x, hz, h0, hpath, hout, hbad⟩
    refine ⟨z + w, N, fun i => x i + w, ?_, ?_, ?_, ?_, ?_⟩
    · refine mem_cubeAt_sub_zero.mp ?_
      rwa [add_sub_cancel_right]
    · show x 0 + w = z + w
      rw [h0]
    · intro i hi
      show latDist (x i + w) (x (i + 1) + w) ≤ 2
      rw [latDist_add_right]
      exact hpath i hi
    · intro hmem
      refine hout ?_
      have h : x N + w - w ∈ cubeAt (k + 1) (0 : Fin d → ℤ) :=
        mem_cubeAt_sub_zero.mpr hmem
      rwa [add_sub_cancel_right] at h
    · intro i hi
      obtain ⟨L, hL⟩ := Set.mem_iUnion.mp (hbad i hi)
      exact Set.mem_iUnion.2 ⟨L, hL⟩

/-- **ABK26, `e.diameter.bound`, for distance-two crossings at an arbitrary base
site.**  Identical hypotheses and identical constants as
`measure_crossingEvent₂_le_exp`; only the centre of the annulus moves. -/
theorem measure_crossingEvent₂At_le_exp [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℕ → (Fin d → ℤ) → Set Ω} {a b T : ℝ}
    (hd : 1 ≤ d) (hb0 : 0 < b) (hb1 : b < 1) (hba : b ≤ a)
    (hT : 16 * (d : ℝ) * Real.exp (40 / (1 - b)) ≤ T ^ 2 * b)
    (hindep : ∀ (l : ℕ) (S S' : Set (Fin d → ℤ)),
      (∀ u ∈ S, ∀ v ∈ S', 3 ^ l < latDist u v) →
        Indep (siteSigma B S l) (siteSigma B S' l) μ)
    (hB : ∀ (L : ℕ) (w : Fin d → ℤ),
      μ (B L w) ≤ ENNReal.ofReal (Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * (L : ℝ))))))
    (k : ℕ) (w : Fin d → ℤ) :
    μ (crossingEvent₂At B k w)
      ≤ ENNReal.ofReal (Real.exp
          (-(Real.exp (-(40 / (1 - b))) * T ^ 2 * (3 : ℝ) ^ (b * (k : ℝ)) / 2))) := by
  rw [crossingEvent₂At_eq_crossingEvent₂_shiftFamily]
  exact measure_crossingEvent₂_le_exp hd hb0 hb1 hba hT
    (fun l S S' hsep => indep_siteSigma_shiftFamily hindep w l S S' hsep)
    (measure_shiftFamily_le hB w) k

end Algsuperdiff.Section3.Provider.Percolation
