/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Lipschitz.GraphParametrization
public import LeanPool.FunctionSpaces.Domains.Extension.LocalExtension

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Traces on Lipschitz graph domains

The **trace** of `f` on the boundary `Γ` of a Lipschitz graph domain `Ω`, a function on the
hyperplane `H = e^⊥` through the graph map `γ`, is the series of the restrictions of the terms of
Rychkov's extension (`Rd.LipschitzGraph.trace`):

`Tr f = ∑_j (η_j ⋆ h_j) ∘ γ`,  `h_j = 1_Ω (k_j ⋆ f)`,

with the local means `k_j` and dual kernels `η_j` of the cone bump; by the support principle only
`f` on `Ω` enters. More generally `Rd.LipschitzGraph.traceSeries` restricts `∑_j η_j ⋆ h_j` for
any `h_j ∈ L_p(V)`.

**The trace estimate on the whole Lipschitz epigraph** (`Rd.LipschitzGraph.modNorm_trace_le`)
is a graph-domain variant of Schneider–Vybíral, Theorem 4.2, for bounded Lipschitz domains.
For `1 ≤ p < ∞`, `0 < s < 1` and `1 ≤ q ≤ ∞`,

`‖Tr f‖_{L_p(H)} + ‖(2^(ks) ω_1(Tr f, 2^(-k))_p)_k‖_{ℓ_q}
  ≤ K (‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q})`.

The proof follows Schneider–Vybíral with atoms: the cell atoms `a_{j,m}` of `η_j ⋆ h_j`
(`Rd.cellAtom`) satisfy pointwise Lipschitz bounds, so their restrictions `a_{j,m} ∘ γ` are
regular atoms of order and exponent `1` on `H` (`Rd.LipschitzGraph.isRegularAtom_comp_graphMap`),
centred at the projections of the cell centres. Only the cells whose atoms meet the graph count
(`Rd.LipschitzGraph.traceCoef`); their centres lie within `ρ 2^(-j)` of `Γ`, so they have bounded
overlap on `H` (`Rd.LipschitzGraph.exists_trace_atoms`). With `‖λ_{j,·}‖_{ℓ_p} ≤ 2^(jn/p) ‖h_j‖_p`
the coefficient quasi-norm on `H` is at most `‖(2^(j(s+1/p)) ‖h_j‖_p)_j‖_{ℓ_q}`, since
`s - (n-1)/p = (s + 1/p) - n/p`, and the atomic synthesis on `H` (`Rd.modNorm_le_coeffNorm`)
concludes (`Rd.LipschitzGraph.modNorm_traceSeries_le`). This last step holds for trace atoms of
every order `r > s` (`Rd.LipschitzGraph.modNorm_traceSeries_le_of_atoms`), which gives the traces
of every order on the half-space.

The trace is linear (`Rd.LipschitzGraph.trace_sub`, `Rd.LipschitzGraph.trace_smul`) and bounded
by the intrinsic norm of `B^{1/p}_{p,1}` on `Ω` (`Rd.LipschitzGraph.enorm_trace_le_modNormOn`), so
by the norm of `B^{1/p}_{p,1}` on `V` (`Rd.LipschitzGraph.enorm_trace_le`), hence continuous
along sequences that converge in this norm (`Rd.LipschitzGraph.tendsto_trace_of_modNorm_sub_le`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

namespace LipschitzGraph

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (Ω : LipschitzGraph V)

/-! ### Traces of the terms -/

section Terms

variable (b : LocalMeansBump V)

/-- The **trace of a term**: `x' ↦ (η_j ⋆ h)(γ x')`. -/
noncomputable def traceFun (L j : ℕ) (h : V → ℂ) (x' : Ω.hyperplane) : ℂ :=
  conv (b.dual L j) h volume (Ω.graphMap x')

open Classical in
/-- The **coefficients of the trace atoms**: `λ_{j,m}` for the cells whose atoms meet the graph,
`0` for the others. -/
noncomputable def traceCoef (p : ℝ≥0∞) (L j : ℕ) (h : V → ℂ) (m : Fin (finrank ℝ V) → ℤ) : ℂ :=
  if ∃ y', cellAtom p (b.dual L j) j h m (Ω.graphMap y') ≠ 0 then cellCoef p j h m else 0

/-- The trace of a term is continuous. -/
theorem continuous_traceFun {p : ℝ≥0∞} (hp1 : 1 ≤ p) (L j : ℕ) {h : V → ℂ}
    (hh : MemLp h p volume) : Continuous (Ω.traceFun b L j h) :=
  ((b.hasCompactSupport_dual L j).continuous_convolution_left (ContinuousLinearMap.mul ℂ ℂ)
    (b.continuous_dual L j) (hh.locallyIntegrable hp1)).comp Ω.continuous_graphMap

/-- **The trace of a term is the sum of the traces of its cell atoms**:
`(η_j ⋆ h)(γ x') = ∑_m λ'_{j,m} a_{j,m}(γ x')` with the coefficients of the cells meeting the
graph. -/
theorem traceFun_eq_tsum {p : ℝ≥0∞} (hp1 : 1 ≤ p) (L j : ℕ) {h : V → ℂ}
    (hh : MemLp h p volume) (x' : Ω.hyperplane) :
    Ω.traceFun b L j h x' =
      ∑' m, Ω.traceCoef b p L j h m * (cellAtom p (b.dual L j) j h m ∘ Ω.graphMap) x' := by
  have hρ : 0 ≤ 2 * (L : ℝ) * b.radius / 2 ^ j :=
    div_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg L)) b.radius_nonneg)
      (by positivity)
  rw [traceFun, conv_eq_tsum_cellAtom hp1 (b.continuous_dual L j) hρ
    (fun y hy => b.dual_eq_zero_of_lt L j hy) hh j]
  refine tsum_congr fun m => ?_
  rw [Function.comp_apply, traceCoef]
  split_ifs with hm
  · rfl
  · push Not at hm
    rw [hm x', mul_zero, mul_zero]

/-- `|λ'_{j,m}| ≤ |λ_{j,m}|`. -/
theorem enorm_traceCoef_le (p : ℝ≥0∞) (L j : ℕ) (h : V → ℂ) (m : Fin (finrank ℝ V) → ℤ) :
    ‖Ω.traceCoef b p L j h m‖ₑ ≤ ‖cellCoef p j h m‖ₑ := by
  rw [traceCoef]
  split_ifs
  · exact le_rfl
  · rw [eNorm_zero]
    exact zero_le

/-- `‖λ'_{j,·}‖_{ℓ_p} ≤ 2^(jn/p) ‖h‖_p`. -/
theorem levelNorm_traceCoef_le {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (L j : ℕ) {h : V → ℂ}
    (hh : MemLp h p volume) :
    levelNorm p (Ω.traceCoef b p L j h) ≤
      dyadicWeight (finrank ℝ V / p.toReal) j * eLpNorm h p volume :=
  (levelNorm_mono p (Ω.enorm_traceCoef_le b p L j h)).trans_eq (levelNorm_cellCoef hp0 hp hh j)

/-- **The centres of the trace atoms lie near the graph**: if the cell atom `a_{j,m}` of `K ⋆ g`,
`K = 0` outside `B(0, ρ 2^(-j))`, does not vanish on the graph and the projection of its centre lies
within `(d + t) 2^(-j)` of `x'`, `d = ρ + n`, then the centre lies within
`(d + (1 + M)(2d + t)) 2^(-j)` of `γ x'`. -/
theorem norm_graphMap_sub_cellCenter_le {p : ℝ≥0∞} {K g : V → ℂ} {ρ t : ℝ} {j : ℕ}
    (hK : ∀ y, ρ / 2 ^ j < ‖y‖ → K y = 0) {m : Fin (finrank ℝ V) → ℤ}
    (hne : ∃ y', cellAtom p K j g m (Ω.graphMap y') ≠ 0) {x' : Ω.hyperplane}
    (hdist : ‖x' - Ω.proj (cellCenter j m)‖ ≤ (ρ + finrank ℝ V + t) / 2 ^ j) :
    ‖Ω.graphMap x' - cellCenter j m‖ ≤
      (ρ + finrank ℝ V + (1 + Ω.M) * (2 * (ρ + finrank ℝ V) + t)) / 2 ^ j := by
  set d := ρ + finrank ℝ V
  obtain ⟨y', hy'⟩ := hne
  have h1 : ‖Ω.graphMap y' - cellCenter j m‖ ≤ d / 2 ^ j :=
    not_lt.1 fun hlt => hy' (cellAtom_eq_zero hK m hlt)
  have h2 : ‖y' - Ω.proj (cellCenter j m)‖ ≤ d / 2 ^ j := (Ω.norm_sub_proj_le y' _).trans h1
  have h3 : ‖x' - y'‖ ≤ (2 * d + t) / 2 ^ j := by
    calc ‖x' - y'‖ = ‖(x' - Ω.proj (cellCenter j m)) - (y' - Ω.proj (cellCenter j m))‖ := by
          congr 1
          abel
      _ ≤ ‖x' - Ω.proj (cellCenter j m)‖ + ‖y' - Ω.proj (cellCenter j m)‖ := norm_sub_le _ _
      _ ≤ (d + t) / 2 ^ j + d / 2 ^ j := add_le_add hdist h2
      _ = (2 * d + t) / 2 ^ j := by ring
  calc ‖Ω.graphMap x' - cellCenter j m‖
      = ‖(Ω.graphMap x' - Ω.graphMap y') + (Ω.graphMap y' - cellCenter j m)‖ := by
        congr 1
        abel
    _ ≤ ‖Ω.graphMap x' - Ω.graphMap y'‖ + ‖Ω.graphMap y' - cellCenter j m‖ := norm_add_le _ _
    _ ≤ (1 + Ω.M) * ((2 * d + t) / 2 ^ j) + d / 2 ^ j :=
        add_le_add ((Ω.norm_graphMap_sub_le x' y').trans
          (mul_le_mul_of_nonneg_left h3 (by linarith [Ω.M_nonneg]))) h1
    _ = (d + (1 + Ω.M) * (2 * d + t)) / 2 ^ j := by ring

/-- **The trace atoms**: there are a radius factor `d`, a constant `C < ∞` and an overlap bound
`N` such that for every level `j` and `h ∈ L_p` the restrictions `a_{j,m} ∘ γ` of the cell atoms
of `η_j ⋆ h` are regular atoms of order and exponent `1` on `H` centred at `P c_{j,m}`, and the
centres of the cells meeting the graph have overlap at most `N`: such a centre lies within
`(d + (1 + M)(2d + 1)) 2^(-j)` of `γ x'` whenever its projection lies within `(d + 1) 2^(-j)` of
`x'`. -/
theorem exists_trace_atoms {p : ℝ≥0∞} (hp1 : 1 ≤ p) (L : ℕ) :
    ∃ (d : ℝ) (C : ℝ≥0∞) (N : ℕ), 0 ≤ d ∧ C ≠ ∞ ∧ ∀ (j : ℕ) {h : V → ℂ}, MemLp h p volume →
      (∀ m, IsRegularAtom p 1 1 d C j (Ω.proj (cellCenter j m))
        (cellAtom p (b.dual L j) j h m ∘ Ω.graphMap)) ∧
      ∀ x' (S : Finset (Fin (finrank ℝ V) → ℤ)),
        (∀ m ∈ S, Ω.traceCoef b p L j h m ≠ 0 ∧ ‖x' - Ω.proj (cellCenter j m)‖ ≤ (d + 1) / 2 ^ j) →
          S.card ≤ N := by
  obtain ⟨A, hA, hb⟩ := b.exists_higherDiff_dual_bound L 1
  have ht : 0 ≤ 1 - 1 / p.toReal := one_sub_one_div_toReal_nonneg hp1
  set ρ := 2 * (L : ℝ) * b.radius
  have hρ : 0 ≤ ρ := mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg L)) b.radius_nonneg
  set d := ρ + finrank ℝ V
  have hd : 0 ≤ d := add_nonneg hρ (Nat.cast_nonneg _)
  set A1 := 2 ^ (1 : ℕ) * A * (ENNReal.ofReal ((ρ + 1) ^ finrank ℝ V) *
    volume (ball (0 : V) 1)) ^ (1 - 1 / p.toReal)
  have hA1 : A1 ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hA)
    (ENNReal.rpow_ne_top_of_nonneg ht (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      measure_ball_lt_top.ne))
  set ρ' := d + (1 + Ω.M) * (2 * d + 1)
  have hρ' : 0 ≤ ρ' := add_nonneg hd (mul_nonneg (by linarith [Ω.M_nonneg]) (by linarith))
  have hKρ : ∀ j y, ρ / 2 ^ j < ‖y‖ → b.dual L j y = 0 := fun j y hy => b.dual_eq_zero_of_lt L j hy
  refine ⟨d, ENNReal.ofReal (1 + Ω.M) * A1 * (((1 + 1 : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (d ^ finrank ℝ Ω.hyperplane) * volume (ball (0 : Ω.hyperplane) 1))) ^
        (1 / p.toReal), ⌈(2 * ρ' + 2) ^ finrank ℝ V⌉₊, hd, ?_, fun j h hh => ⟨fun m => ?_,
      fun x' S hS => ?_⟩⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA1)
      (ENNReal.rpow_ne_top_of_nonneg (div_nonneg zero_le_one ENNReal.toReal_nonneg)
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)))
  · have hK : ∀ y, ‖b.dual L j y‖ₑ ≤ A * dyadicWeight (finrank ℝ V) j := fun y => by
      simpa using hb 0 (Nat.zero_le 1) j 0 y
    refine Ω.isRegularAtom_comp_graphMap hd (continuous_cellAtom hp1 (b.continuous_dual L j)
      (b.hasCompactSupport_dual L j) hh j m) (fun x hx => cellAtom_eq_zero (hKρ j) m hx)
      (fun x => ?_) (fun v x => ?_)
    · refine (enorm_cellAtom_le hp1 hh m hK hρ (hKρ j) x).trans ?_
      have hXY : (ENNReal.ofReal (ρ ^ finrank ℝ V) * volume (ball (0 : V) 1)) ^
          (1 - 1 / p.toReal) ≤ (ENNReal.ofReal ((ρ + 1) ^ finrank ℝ V) *
            volume (ball (0 : V) 1)) ^ (1 - 1 / p.toReal) :=
        ENNReal.rpow_le_rpow (mul_le_mul' (ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ hρ (by linarith) _)) le_rfl) ht
      calc A * (ENNReal.ofReal (ρ ^ finrank ℝ V) * volume (ball (0 : V) 1)) ^ (1 - 1 / p.toReal)
          ≤ 1 * (A * (ENNReal.ofReal ((ρ + 1) ^ finrank ℝ V) * volume (ball (0 : V) 1)) ^
              (1 - 1 / p.toReal)) := by
            rw [one_mul]
            exact mul_le_mul' le_rfl hXY
        _ ≤ A1 := by
            simp only [A1]
            rw [mul_assoc]
            exact mul_le_mul' (by norm_num) le_rfl
    · have h1 := enorm_higherDiff_cellAtom_le hp1 (b.continuous_dual L j) hh m hK
        (hb 1 le_rfl j) hρ (hKρ j) v x
      rw [Nat.cast_one, ENNReal.rpow_one] at h1
      simpa only [Function.iterate_one, fwdDiff] using h1
  · refine card_le_of_norm_sub_cellCenter_le j hρ' (Ω.graphMap x') S fun m hm => ?_
    obtain ⟨hcoef, hdist⟩ := hS m hm
    have hex : ∃ y', cellAtom p (b.dual L j) j h m (Ω.graphMap y') ≠ 0 := by
      by_contra hcon
      exact hcoef (by simp [traceCoef, hcon])
    exact Ω.norm_graphMap_sub_cellCenter_le (hKρ j) hex hdist

omit [MeasurableSpace V] [BorelSpace V] in
/-- `dim H = n - 1` as a real number. -/
theorem finrank_hyperplane_eq : (finrank ℝ Ω.hyperplane : ℝ) = finrank ℝ V - 1 := by
  have h := Ω.finrank_hyperplane_add_one
  rw [← h]
  push_cast
  ring

/-- **The traces of the terms are in `L_p(H)`**: `‖(η_j ⋆ h) ∘ γ‖_{L_p(H)} ≤ K 2^(j/p) ‖h‖_p`, by
the level sums of the trace atoms (`Rd.eLpNorm_levelSum_le` on `H`). -/
theorem eLpNorm_traceFun_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) (L : ℕ) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ j {h : V → ℂ}, MemLp h p volume →
      eLpNorm (Ω.traceFun b L j h) p (volume : Measure Ω.hyperplane) ≤
        K * dyadicWeight (1 / p.toReal) j * eLpNorm h p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  obtain ⟨d, C, N, hd, hC, hatoms⟩ := Ω.exists_trace_atoms b hp1 L
  have hexp : 0 ≤ 1 - 1 / p.toReal := one_sub_one_div_toReal_nonneg hp1
  refine ⟨(N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * C, ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hexp (ENNReal.natCast_ne_top N)) hC, fun j h hh => ?_⟩
  obtain ⟨hat, hN⟩ := hatoms j hh
  have hlev := eLpNorm_levelSum_le hp1 hp (fun m => Ω.proj (cellCenter j m))
    (fun m => cellAtom p (b.dual L j) j h m ∘ Ω.graphMap) (Ω.traceCoef b p L j h)
    (fun x' S hS => hN x' S fun m hm => ⟨(hS m hm).1, by simpa only [Nat.cast_one] using (hS m
      hm).2⟩)
    hat
    (Ω.continuous_traceFun b hp1 L j hh).aestronglyMeasurable
    (Eventually.of_forall (Ω.traceFun_eq_tsum b hp1 L j hh))
  refine hlev.trans ?_
  calc (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) *
        (C * dyadicWeight (-(finrank ℝ Ω.hyperplane / p.toReal)) j) *
        levelNorm p (Ω.traceCoef b p L j h)
      ≤ (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) *
          (C * dyadicWeight (-(finrank ℝ Ω.hyperplane / p.toReal)) j) *
          (dyadicWeight (finrank ℝ V / p.toReal) j * eLpNorm h p volume) :=
        mul_le_mul' le_rfl (Ω.levelNorm_traceCoef_le b hp0 hp L j hh)
    _ = (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * C *
          (dyadicWeight (-(finrank ℝ Ω.hyperplane / p.toReal)) j *
            dyadicWeight (finrank ℝ V / p.toReal) j) * eLpNorm h p volume := by ring
    _ = (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * C * dyadicWeight (1 / p.toReal) j *
          eLpNorm h p volume := by
        rw [← ENNReal.dyadicWeight_add, Ω.finrank_hyperplane_eq]
        congr 3
        ring

/-- The traces of the terms are in `L_p(H)`. -/
theorem memLp_traceFun {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) (L j : ℕ) {h : V → ℂ}
    (hh : MemLp h p volume) : MemLp (Ω.traceFun b L j h) p (volume : Measure Ω.hyperplane) := by
  obtain ⟨K, hK, hle⟩ := Ω.eLpNorm_traceFun_le b hp1 hp L
  exact memLp_iff.2 ((hle j hh).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hK.lt_top (ENNReal.dyadicWeight_lt_top _ _))
      hh.eLpNorm_lt_top))

end Terms

/-! ### The trace of a series -/

section Series

variable (b : LocalMeansBump V) {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The trace of the `j`-th term `η_j ⋆ h` in `L_p(H)`. -/
noncomputable def traceTerm (hp : p ≠ ∞) (L j : ℕ) (h : Lp ℂ p (volume : Measure V)) :
    Lp ℂ p (volume : Measure Ω.hyperplane) :=
  (Ω.memLp_traceFun b Fact.out hp L j (Lp.memLp h)).toLp _

/-- The trace of a term agrees with `(η_j ⋆ h) ∘ γ` almost everywhere. -/
theorem traceTerm_ae (hp : p ≠ ∞) (L j : ℕ) (h : Lp ℂ p (volume : Measure V)) :
    Ω.traceTerm b hp L j h =ᵐ[volume] Ω.traceFun b L j h :=
  MemLp.coeFn_toLp _

/-- The **trace of a series** `∑_j η_j ⋆ h_j`: `∑_j (η_j ⋆ h_j) ∘ γ` in `L_p(H)`. -/
noncomputable def traceSeries (hp : p ≠ ∞) (L : ℕ) (h : ℕ → Lp ℂ p (volume : Measure V)) :
    Lp ℂ p (volume : Measure Ω.hyperplane) :=
  ∑' j, Ω.traceTerm b hp L j (h j)

/-- **The trace series converges absolutely** for `s > 0` and
`X = ‖(2^(j(s+1/p)) ‖h_j‖_p)_j‖_{ℓ_q} < ∞`: `‖(η_j ⋆ h_j) ∘ γ‖_{L_p(H)} ≤ K 2^(j/p) ‖h_j‖_p ≤
K X 2^(-js)`. -/
theorem summable_traceTerm (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {h : ℕ → Lp ℂ p (volume : Measure V)}
    (hX : lqNorm q (fun j => dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ) < ∞) :
    Summable fun j => Ω.traceTerm b hp L j (h j) := by
  have hp1 : 1 ≤ p := Fact.out
  obtain ⟨K, hK, hle⟩ := Ω.eLpNorm_traceFun_le b hp1 hp L
  set X := lqNorm q (fun j => dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ)
  have hterm : ∀ j, ‖Ω.traceTerm b hp L j (h j)‖ₑ ≤ K * X * dyadicWeight (-s) j := fun j => by
    have hXj : dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ ≤ X :=
      ENNReal.le_lqNorm (zero_lt_one.trans_le hq).ne'
        (fun j => dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ) j
    have hw : dyadicWeight (1 / p.toReal) j =
        dyadicWeight (s + 1 / p.toReal) j * dyadicWeight (-s) j := by
      rw [← ENNReal.dyadicWeight_add]
      congr 1
      ring
    rw [Lp.eNorm_def, eLpNorm_congr_ae (Ω.traceTerm_ae b hp L j (h j))]
    refine (hle j (Lp.memLp (h j))).trans ?_
    rw [← Lp.eNorm_def, hw]
    calc K * (dyadicWeight (s + 1 / p.toReal) j * dyadicWeight (-s) j) * ‖h j‖ₑ
        = K * (dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ) * dyadicWeight (-s) j := by ring
      _ ≤ K * X * dyadicWeight (-s) j := by gcongr
  refine Summable.of_eNorm (ne_top_of_le_ne_top ?_ (tsum_le_tsum hterm))
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_dyadicWeight_neg]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hK hX.ne)
    (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs)

/-- The partial sums of the trace series converge to it. -/
theorem tendsto_sum_traceTerm (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {h : ℕ → Lp ℂ p (volume : Measure V)}
    (hX : lqNorm q (fun j => dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ) < ∞) :
    Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), Ω.traceTerm b hp L j (h j)) atTop
      (𝓝 (Ω.traceSeries b hp L h)) :=
  ((Ω.summable_traceTerm b hp L hs hq hX).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)

/-- **The trace of a series from trace atoms of order `r`**: let `0 < s < r`, and let the
restrictions `a_{j,m} ∘ γ` of the cell atoms of `η_j ⋆ h`, for every level `j` and `h ∈ L_p`, be
regular atoms on `H` of order and exponent `r` with radius factor `d` and constant `C < ∞`,
centred at `P c_{j,m}`, and for every `x' ∈ H` let at most `N` of the centres `P c_{j,m}` with
nonzero coefficient `λ'_{j,m}` lie within `(d + r) 2^(-j)` of `x'`. Then
there is `K < ∞` such that the trace `Tr = ∑_j (η_j ⋆ h_j) ∘ γ` has
`‖Tr‖_{L_p(H)} + ‖(2^(ks) ω_r(Tr, 2^(-k))_p)_k‖_{ℓ_q} ≤ K ‖(2^(j(s+1/p)) ‖h_j‖_p)_j‖_{ℓ_q}`,
by the atomic synthesis on `H` (`Rd.modNorm_le_coeffNorm`) and
`2^(j(s-(n-1)/p)) ‖λ'_{j,·}‖_{ℓ_p} ≤ 2^(j(s+1/p)) ‖h_j‖_p`. -/
theorem modNorm_traceSeries_le_of_atoms (hp : p ≠ ∞) (L : ℕ) {r : ℕ} {s : ℝ} (hs : 0 < s)
    (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) {d : ℝ} {C : ℝ≥0∞} {N : ℕ} (hC : C ≠ ∞)
    (hatoms : ∀ (j : ℕ) {h : V → ℂ}, MemLp h p volume →
      (∀ m, IsRegularAtom p r r d C j (Ω.proj (cellCenter j m))
        (cellAtom p (b.dual L j) j h m ∘ Ω.graphMap)) ∧
      ∀ x' (S : Finset (Fin (finrank ℝ V) → ℤ)),
        (∀ m ∈ S, Ω.traceCoef b p L j h m ≠ 0 ∧ ‖x' - Ω.proj (cellCenter j m)‖ ≤ (d + r) / 2 ^ j) →
          S.card ≤ N) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ h : ℕ → Lp ℂ p (volume : Measure V),
      lqNorm q (fun j => dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ) < ∞ →
      ‖Ω.traceSeries b hp L h‖ₑ +
          lqNorm q (fun k => dyadicWeight s k * lpModulus p r (Ω.traceSeries b hp L h) k) ≤
        K * lqNorm q (fun j => dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ) := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  refine ⟨atomSynthConst p N C r s r, atomSynthConst_ne_top hp1 N hC r hs hsr, fun h hX => ?_⟩
  have hsyn := modNorm_le_coeffNorm hp (fun j m => Ω.proj (cellCenter j m))
    (fun j m => cellAtom p (b.dual L j) j (h j) m ∘ Ω.graphMap)
    (fun j => Ω.traceCoef b p L j (h j))
    (fun j x' S hS => (hatoms j (Lp.memLp (h j))).2 x' S hS)
    (fun j m => (hatoms j (Lp.memLp (h j))).1 m)
    (fun j => (Ω.traceTerm_ae b hp L j (h j)).mono fun x' hx' =>
      hx'.trans (Ω.traceFun_eq_tsum b hp1 L j (Lp.memLp (h j)) x'))
    (Ω.tendsto_sum_traceTerm b hp L hs hq hX) hs hsr hq
  refine hsyn.trans (mul_le_mul' le_rfl ?_)
  rw [coeffNorm]
  refine ENNReal.lqNorm_mono fun j => ?_
  calc dyadicWeight (s - finrank ℝ Ω.hyperplane / p.toReal) j *
        levelNorm p (Ω.traceCoef b p L j (h j))
      ≤ dyadicWeight (s - finrank ℝ Ω.hyperplane / p.toReal) j *
          (dyadicWeight (finrank ℝ V / p.toReal) j * eLpNorm (h j) p volume) :=
        mul_le_mul' le_rfl (Ω.levelNorm_traceCoef_le b hp0 hp L j (Lp.memLp (h j)))
    _ = dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ := by
        rw [← mul_assoc, ← ENNReal.dyadicWeight_add, Lp.eNorm_def, Ω.finrank_hyperplane_eq]
        congr 2
        ring

/-- **The trace of a series** on a Lipschitz graph. For `0 < s < 1` there is `K < ∞` such that
the trace `Tr = ∑_j (η_j ⋆ h_j) ∘ γ` has
`‖Tr‖_{L_p(H)} + ‖(2^(ks) ω_1(Tr, 2^(-k))_p)_k‖_{ℓ_q} ≤ K ‖(2^(j(s+1/p)) ‖h_j‖_p)_j‖_{ℓ_q}`,
by the atomic synthesis on `H` with the trace atoms of order `1`
(`Rd.LipschitzGraph.exists_trace_atoms`, `Rd.LipschitzGraph.modNorm_traceSeries_le_of_atoms`). -/
theorem modNorm_traceSeries_le (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ h : ℕ → Lp ℂ p (volume : Measure V),
      lqNorm q (fun j => dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ) < ∞ →
      ‖Ω.traceSeries b hp L h‖ₑ +
          lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 (Ω.traceSeries b hp L h) k) ≤
        K * lqNorm q (fun j => dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ) := by
  obtain ⟨d, C, N, -, hC, hatoms⟩ := Ω.exists_trace_atoms b (Fact.out : 1 ≤ p) L
  exact Ω.modNorm_traceSeries_le_of_atoms b hp L (r := 1) hs (by exact_mod_cast hs1) hq hC
    fun j h hh => ⟨fun m => by simpa only [Nat.cast_one] using (hatoms j hh).1 m,
      fun x' S hS => (hatoms j hh).2 x' S fun m hm =>
        ⟨(hS m hm).1, by simpa only [Nat.cast_one] using (hS m hm).2⟩⟩

end Series

/-! ### The trace on a Lipschitz graph domain -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The **trace** on the boundary of the Lipschitz graph domain `Ω`, a function on `H`:
`Tr f = ∑_j (η_j ⋆ 1_Ω (k_j ⋆ f)) ∘ γ` with the kernels of the cone bump; only `f` on `Ω`
enters. -/
noncomputable def trace (hp : p ≠ ∞) (L : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    Lp ℂ p (volume : Measure Ω.hyperplane) :=
  Ω.traceSeries Ω.coneBump hp L fun j => Ω.cutoff (Ω.coneBump.localMean hp L j f)

/-- **The trace estimate on Lipschitz graph domains**. For `1 ≤ p < ∞`, `0 < s < 1` and
`1 ≤ q ≤ ∞` there is `K < ∞` with
`‖Tr f‖_{L_p(H)} + ‖(2^(ks) ω_1(Tr f, 2^(-k))_p)_k‖_{ℓ_q} ≤
K (‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q})`. -/
theorem modNorm_trace_le (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞}
    (hq : 1 ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V),
      modNormOn Ω.measurableSet_domain L (s + 1 / p.toReal) q f < ∞ →
      ‖Ω.trace hp L f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 (Ω.trace hp L f) k) ≤
        K * modNormOn Ω.measurableSet_domain L (s + 1 / p.toReal) q f := by
  obtain ⟨K, hK, hle⟩ := Ω.modNorm_traceSeries_le Ω.coneBump hp L hs hs1 hq
  refine ⟨K * Ω.intrinsicConst L, ENNReal.mul_ne_top hK (Ω.intrinsicConst_ne_top L),
    fun f hf => ?_⟩
  have hX := Ω.intrinsicNorm_lt_top hp L (s + 1 / p.toReal) hq hf
  rw [mul_assoc]
  exact (hle (fun j => Ω.cutoff (Ω.coneBump.localMean hp L j f)) hX).trans
    (mul_le_mul' le_rfl (Ω.intrinsicNorm_le hp L (s + 1 / p.toReal) hq f))

/-! ### The trace of continuous functions -/

/-- **The partial sums of the trace at a boundary point**:
`∑_{j ≤ J} (η_j ⋆ 1_Ω (k_j ⋆ f))(γ x') = (m_{2^J} ⋆ (m_{2^J} ⋆ f))(γ x')`: at boundary points the
cut-off does not matter (the kernels are supported in `-K` and `γ x' + K ⊆ Ω`), and the partial
sums of the reproducing formula are `m_{2^J} ⋆ m_{2^J} ⋆ f` at every point. -/
theorem sum_traceFun_eq_conv (hp : p ≠ ∞) (L J : ℕ) (f : Lp ℂ p (volume : Measure V))
    (x' : Ω.hyperplane) :
    ∑ j ∈ Finset.range (J + 1),
        Ω.traceFun Ω.coneBump L j (Ω.cutoff (Ω.coneBump.localMean hp L j f)) x' =
      conv (Ω.coneBump.scaled L J) (convLp hp (Ω.coneBump.integrable_scaled L J) f) volume
        (Ω.graphMap x') := by
  have hcut : ∀ j, Ω.traceFun Ω.coneBump L j (Ω.cutoff (Ω.coneBump.localMean hp L j f)) x' =
      conv (Ω.coneBump.dual L j) (Ω.coneBump.localMean hp L j f) volume (Ω.graphMap x') :=
    fun j => by
      rw [traceFun, conv_congr_ae (Ω.cutoff_apply_ae _),
        conv_indicator_eq_of_forall _ (fun z hz => ?_) volume]
      rw [sub_eq_add_neg]
      exact Ω.graphMap_add_mem x' (Ω.coneSupported_dual L j z hz)
  simp_rw [hcut]
  rw [Ω.coneBump.sum_conv_dual_localMean_apply hp L J f]

/-- The partial sums of the trace for a representative `G` of `f`:
`(m_{2^J} ⋆ (m_{2^J} ⋆ G))(γ x')`. -/
theorem sum_traceFun_eq (hp : p ≠ ∞) (L J : ℕ) {f : Lp ℂ p (volume : Measure V)} {G : V → ℂ}
    (hfG : (f : V → ℂ) =ᵐ[volume] G) (x' : Ω.hyperplane) :
    ∑ j ∈ Finset.range (J + 1),
        Ω.traceFun Ω.coneBump L j (Ω.cutoff (Ω.coneBump.localMean hp L j f)) x' =
      conv (Ω.coneBump.scaled L J) (conv (Ω.coneBump.scaled L J) G volume) volume
        (Ω.graphMap x') := by
  rw [Ω.sum_traceFun_eq_conv hp L J f]
  have hG : ⇑(convLp hp (Ω.coneBump.integrable_scaled L J) f) =ᵐ[volume]
      conv (Ω.coneBump.scaled L J) G volume :=
    (convLp_apply_ae hp _ f).trans (Filter.EventuallyEq.of_eq (conv_congr_ae hfG))
  rw [conv_congr_ae hG]

/-- **The trace is an almost everywhere limit of mollified restrictions**: for a finite intrinsic
norm of smoothness `s + 1/p`, `s > 0`, a subsequence of `(m_{2^J} ⋆ (m_{2^J} ⋆ f))(γ x')` converges
to `Tr f(x')` for almost every `x'`, since the partial sums of the trace series converge in
`L_p(H)`. -/
theorem exists_subseq_tendsto_trace (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)}
    (hX : Ω.intrinsicNorm hp L (s + 1 / p.toReal) q f < ∞) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x' ∂(volume : Measure Ω.hyperplane),
      Tendsto (fun k => conv (Ω.coneBump.scaled L (ns k))
        (convLp hp (Ω.coneBump.integrable_scaled L (ns k)) f) volume (Ω.graphMap x')) atTop
          (𝓝 (Ω.trace hp L f x')) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hS := Ω.tendsto_sum_traceTerm Ω.coneBump hp L hs hq
    (h := fun j => Ω.cutoff (Ω.coneBump.localMean hp L j f)) hX
  have hSae : ∀ᵐ x' ∂(volume : Measure Ω.hyperplane), ∀ J,
      (∑ j ∈ Finset.range (J + 1), Ω.traceTerm Ω.coneBump hp L j
        (Ω.cutoff (Ω.coneBump.localMean hp L j f))) x' =
      conv (Ω.coneBump.scaled L J) (convLp hp (Ω.coneBump.integrable_scaled L J) f) volume
        (Ω.graphMap x') := by
    rw [ae_all_iff]
    intro J
    have h1 := Lp.coeFn_fun_finsetSum (Finset.range (J + 1))
      (fun j => Ω.traceTerm Ω.coneBump hp L j (Ω.cutoff (Ω.coneBump.localMean hp L j f)))
    have h2 : ∀ᵐ x' ∂(volume : Measure Ω.hyperplane), ∀ j,
        Ω.traceTerm Ω.coneBump hp L j (Ω.cutoff (Ω.coneBump.localMean hp L j f)) x' =
          Ω.traceFun Ω.coneBump L j (Ω.cutoff (Ω.coneBump.localMean hp L j f)) x' :=
      ae_all_iff.2 fun j => Ω.traceTerm_ae Ω.coneBump hp L j _
    filter_upwards [h1, h2] with x' hx1 hx2
    rw [hx1, ← Ω.sum_traceFun_eq_conv hp L J f x']
    exact Finset.sum_congr rfl fun j _ => hx2 j
  obtain ⟨ns, hns, hns_ae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm hp0
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hS)).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hSae, hns_ae] with x' hx1 hx2
  simp only [hx1] at hx2
  exact hx2

/-- **The trace of continuous functions**: if `f ∈ L_p(V)` has a continuous representative `G`
and a finite intrinsic `B^{s+1/p}_{p,q}`-norm on `Ω`, then `Tr f = G ∘ γ` almost everywhere on
`H`: the mollified restrictions converge at every point to `G(γ x')`
(`Rd.conv_dilate_near`, twice), and a subsequence converges almost everywhere to `Tr f`. -/
theorem trace_ae_eq_comp_graphMap (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s)
    {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)}
    (hf : modNormOn Ω.measurableSet_domain L (s + 1 / p.toReal) q f < ∞)
    {G : V → ℂ} (hG : Continuous G) (hfG : (f : V → ℂ) =ᵐ[volume] G) :
    Ω.trace hp L f =ᵐ[volume] G ∘ Ω.graphMap := by
  obtain ⟨ns, hns, hae⟩ := Ω.exists_subseq_tendsto_trace hp L hs hq
    (Ω.intrinsicNorm_lt_top hp L (s + 1 / p.toReal) hq hf)
  have hΦ := integrable_momentKernel Ω.coneBump.integrable L
  have hone := integral_momentKernel Ω.coneBump.integrable Ω.coneBump.integral_eq_one hL
  have hR : 0 ≤ (L : ℝ) * Ω.coneBump.radius :=
    mul_nonneg (Nat.cast_nonneg L) Ω.coneBump.radius_nonneg
  have hΦR : ∀ w, L * Ω.coneBump.radius < ‖w‖ → momentKernel Ω.coneBump.toFun L w = 0 :=
    fun w hw => Ω.coneBump.momentKernel_eq_zero L hw
  have hlim : ∀ y : V, Tendsto (fun J => conv (Ω.coneBump.scaled L J)
      (conv (Ω.coneBump.scaled L J) G volume) volume y) atTop (𝓝 (G y)) := fun y => by
    have hG1 := conv_dilate_near hΦ hone hR hΦR (F := fun _ => G)
      (fun _ => hG.aestronglyMeasurable) (y := y) (z₀ := G y) fun ε hε => by
        obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.1 hG.continuousAt ε hε
        exact ⟨0, δ, hδ, fun J _ z hz => by
          rw [← dist_eq_norm]
          exact hδG (by rwa [dist_eq_norm])⟩
    have hG2 := conv_dilate_near hΦ hone hR hΦR
      (F := fun J => conv (Ω.coneBump.scaled L J) G volume)
      (fun J => ((Ω.coneBump.hasCompactSupport_scaled L J).continuous_convolution_left
        (ContinuousLinearMap.mul ℂ ℂ) (Ω.coneBump.continuous_scaled L J)
          hG.locallyIntegrable).aestronglyMeasurable) hG1
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨J₀, δ, hδ, hJ⟩ := hG2 ε hε
    exact ⟨J₀, fun J hJ0 => by
      rw [dist_eq_norm]
      exact hJ J hJ0 y (by simpa using hδ)⟩
  filter_upwards [hae] with x' hx
  refine tendsto_nhds_unique hx ?_
  have hJ : ∀ J, conv (Ω.coneBump.scaled L J) (convLp hp (Ω.coneBump.integrable_scaled L J) f)
      volume (Ω.graphMap x') = conv (Ω.coneBump.scaled L J)
        (conv (Ω.coneBump.scaled L J) G volume) volume (Ω.graphMap x') := fun J => by
    rw [conv_congr_ae ((convLp_apply_ae hp _ f).trans
      (Filter.EventuallyEq.of_eq (conv_congr_ae hfG)))]
  simp_rw [hJ]
  exact (hlim (Ω.graphMap x')).comp hns.tendsto_atTop

/-! ### Linearity and continuity of the trace -/

/-- The traces of the terms are linear in `h`. -/
theorem traceTerm_sub (b : LocalMeansBump V) (hp : p ≠ ∞) (L j : ℕ)
    (h₁ h₂ : Lp ℂ p (volume : Measure V)) :
    Ω.traceTerm b hp L j (h₁ - h₂) = Ω.traceTerm b hp L j h₁ - Ω.traceTerm b hp L j h₂ := by
  have hp1 : 1 ≤ p := Fact.out
  have hint : ∀ (h : Lp ℂ p (volume : Measure V)) (y : V),
      Integrable (fun z => b.dual L j z * h (y - z)) volume := fun h y => by
    simpa using integrable_translate_mul_of_locallyIntegrable (b.continuous_dual L j)
      (b.hasCompactSupport_dual L j) ((Lp.memLp h).locallyIntegrable hp1) 0 y
  refine Lp.ext ?_
  filter_upwards [Ω.traceTerm_ae b hp L j (h₁ - h₂), Ω.traceTerm_ae b hp L j h₁,
    Ω.traceTerm_ae b hp L j h₂, Lp.coeFn_sub (Ω.traceTerm b hp L j h₁)
      (Ω.traceTerm b hp L j h₂)] with x' hx hx₁ hx₂ hxs
  rw [hx, hxs, Pi.sub_apply, hx₁, hx₂, traceFun, traceFun, traceFun,
    conv_congr_ae (Lp.coeFn_sub h₁ h₂), conv_apply, conv_apply, conv_apply,
    ← integral_sub (hint h₁ _) (hint h₂ _)]
  congr 1
  funext z
  simp only [Pi.sub_apply]
  ring

/-- **The trace is linear** on the functions with a finite intrinsic norm of smoothness `> 1/p`. -/
theorem trace_sub (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f₁ f₂ : Lp ℂ p (volume : Measure V)}
    (h₁ : Ω.intrinsicNorm hp L (s + 1 / p.toReal) q f₁ < ∞)
    (h₂ : Ω.intrinsicNorm hp L (s + 1 / p.toReal) q f₂ < ∞) :
    Ω.trace hp L (f₁ - f₂) = Ω.trace hp L f₁ - Ω.trace hp L f₂ := by
  simp only [trace, traceSeries, map_sub]
  simp_rw [Ω.traceTerm_sub]
  exact Summable.tsum_sub (Ω.summable_traceTerm Ω.coneBump hp L hs hq
      (h := fun j => Ω.cutoff (Ω.coneBump.localMean hp L j f₁)) h₁)
    (Ω.summable_traceTerm Ω.coneBump hp L hs hq
      (h := fun j => Ω.cutoff (Ω.coneBump.localMean hp L j f₂)) h₂)

/-- The traces of the terms commute with complex scalars, since convolution does
(`Rd.conv_smul`). -/
theorem traceTerm_smul (b : LocalMeansBump V) (hp : p ≠ ∞) (L j : ℕ) (c : ℂ)
    (h : Lp ℂ p (volume : Measure V)) :
    Ω.traceTerm b hp L j (c • h) = c • Ω.traceTerm b hp L j h := by
  refine Lp.ext ?_
  filter_upwards [Ω.traceTerm_ae b hp L j (c • h), Ω.traceTerm_ae b hp L j h,
    Lp.coeFn_smul c (Ω.traceTerm b hp L j h)] with x' h1 h2 h3
  rw [h1, h3, Pi.smul_apply, h2, traceFun, traceFun, conv_congr_ae (Lp.coeFn_smul c h), conv_smul]
  rfl

/-- **The trace commutes with complex scalars**: `Tr (c f) = c Tr f` for every `f ∈ L_p(V)`, since
every term of the trace series does and `∑' j, c x_j = c ∑' j, x_j` (Mathlib's
`tsum_const_smul''`). With `Rd.LipschitzGraph.trace_sub` the trace is linear on the functions of
finite intrinsic norm. -/
theorem trace_smul (hp : p ≠ ∞) (L : ℕ) (c : ℂ) (f : Lp ℂ p (volume : Measure V)) :
    Ω.trace hp L (c • f) = c • Ω.trace hp L f := by
  simp only [trace, traceSeries, map_smul]
  simp_rw [Ω.traceTerm_smul]
  exact tsum_const_smul'' c

/-- **The trace is bounded by the intrinsic norm of `B^{1/p}_{p,1}`**:
`‖Tr f‖_{L_p(H)} ≤ K (‖f‖_{L_p(Ω)} + ∑_k 2^(k/p) ω_L(f, 2^(-k), Ω)_p)`, by the bounds of the terms
(`Rd.LipschitzGraph.eLpNorm_traceFun_le`) and the comparison of the intrinsic local means with the
moduli on `Ω`. -/
theorem enorm_trace_le_modNormOn (hp : p ≠ ∞) (L : ℕ) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V),
      ‖Ω.trace hp L f‖ₑ ≤ K * modNormOn Ω.measurableSet_domain L (1 / p.toReal) 1 f := by
  obtain ⟨K, hK, hle⟩ := Ω.eLpNorm_traceFun_le Ω.coneBump Fact.out hp L
  refine ⟨K * Ω.intrinsicConst L, ENNReal.mul_ne_top hK (Ω.intrinsicConst_ne_top L),
    fun f => ?_⟩
  calc ‖Ω.trace hp L f‖ₑ ≤ ∑' j, ‖Ω.traceTerm Ω.coneBump hp L j
        (Ω.cutoff (Ω.coneBump.localMean hp L j f))‖ₑ := eNorm_tsum_le_tsum_eNorm
    _ ≤ ∑' j, K * (dyadicWeight (1 / p.toReal) j *
          ‖Ω.cutoff (Ω.coneBump.localMean hp L j f)‖ₑ) :=
        tsum_le_tsum fun j => by
          rw [Lp.eNorm_def, eLpNorm_congr_ae (Ω.traceTerm_ae Ω.coneBump hp L j _)]
          refine (hle j (Lp.memLp _)).trans ?_
          rw [← Lp.eNorm_def, mul_assoc]
    _ = K * Ω.intrinsicNorm hp L (1 / p.toReal) 1 f := by
        rw [ENNReal.tsum_mul_left, intrinsicNorm_def, ENNReal.lqNorm_one]
    _ ≤ K * (Ω.intrinsicConst L * modNormOn Ω.measurableSet_domain L (1 / p.toReal) 1 f) :=
        mul_le_mul' le_rfl (Ω.intrinsicNorm_le hp L _ le_rfl f)
    _ = _ := by ring

/-- **The trace in `L_p(H)` is bounded by the `B^{1/p}_{p,1}`-norm**:
`‖Tr f‖_{L_p(H)} ≤ K (‖f‖_p + ∑_k 2^(k/p) ω_L(f, 2^(-k))_p)`, since the intrinsic quantity of
`Rd.LipschitzGraph.enorm_trace_le_modNormOn` is at most this one
(`Rd.LipschitzGraph.modNormOn_le_modNorm`). -/
theorem enorm_trace_le (hp : p ≠ ∞) (L : ℕ) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V),
      ‖Ω.trace hp L f‖ₑ ≤
        K * (‖f‖ₑ + lqNorm 1 (fun k => dyadicWeight (1 / p.toReal) k * lpModulus p L f k)) := by
  obtain ⟨K, hK, hle⟩ := Ω.enorm_trace_le_modNormOn hp L
  exact ⟨K, hK, fun f => (hle f).trans (mul_le_mul' le_rfl (Ω.modNormOn_le_modNorm L _ 1 rfl))⟩

/-- **The trace along a convergent sequence**: if `F` and the `F_J` have finite intrinsic norms of
smoothness `s + 1/p`, `s > 0`, and `‖F - F_J‖_p + ‖(2^(k/p) ω_L(F - F_J, 2^(-k))_p)_k‖_{ℓ_1} ≤ b_J`
with `b_J < ∞` and `b_J → 0`, then `Tr F_J → Tr F`: the trace is linear
(`Rd.LipschitzGraph.trace_sub`) and bounded by the norm of `B^{1/p}_{p,1}`
(`Rd.LipschitzGraph.enorm_trace_le`). -/
theorem tendsto_trace_of_modNorm_sub_le (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {F : Lp ℂ p (volume : Measure V)} {FJ : ℕ → Lp ℂ p (volume : Measure V)}
    (hF : Ω.intrinsicNorm hp L (s + 1 / p.toReal) q F < ∞)
    (hFJ : ∀ J, Ω.intrinsicNorm hp L (s + 1 / p.toReal) q (FJ J) < ∞) {b : ℕ → ℝ≥0∞}
    (hb : Tendsto b atTop (𝓝 0)) (hbtop : ∀ J, b J ≠ ∞)
    (hle : ∀ J, ‖F - FJ J‖ₑ +
      lqNorm 1 (fun k => dyadicWeight (1 / p.toReal) k * lpModulus p L (F - FJ J) k) ≤ b J) :
    Tendsto (fun J => Ω.trace hp L (FJ J)) atTop (𝓝 (Ω.trace hp L F)) := by
  obtain ⟨KT, hKT, hTle⟩ := Ω.enorm_trace_le hp L
  have hKb0 : Tendsto (fun J => KT * b J) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hb (Or.inr hKT)
  have hKb : Tendsto (fun J => (KT * b J).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hKb0
    rwa [ENNReal.toReal_zero] at h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun J => norm_nonneg _) (fun J => ?_) hKb
  rw [norm_sub_rev, ← Ω.trace_sub hp L hs hq hF (hFJ J), ← toReal_eNorm]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hKT (hbtop J))
    ((hTle _).trans (mul_le_mul' le_rfl (hle J)))

end LipschitzGraph

end Rd
