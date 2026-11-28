/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Lipschitz.HalfSpace
public import LeanPool.FunctionSpaces.Domains.Traces.GraphTraceCharts

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Traces of every order on the half-space

For the flat graph domain `Ω = {x : 0 < ⟪x, e⟫}` (`Rd.LipschitzGraph.flat`) the graph map is the
inclusion of `H = e^⊥` (`Rd.LipschitzGraph.flat_graphMap`), so the restrictions of smooth atoms
to `H` are smooth atoms of the same order (`Rd.LipschitzGraph.isSmoothAtom_comp_graphMap_flat`).
The trace atoms are therefore regular atoms of every order and exponent
(`Rd.LipschitzGraph.exists_trace_atoms_flat`), and the trace theorem holds for every `s > 0`:

`‖Tr f‖_{L_p(H)} + ‖(2^(ks) ω_r(Tr f, 2^(-k))_p)_k‖_{ℓ_q}
  ≤ K (‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q})`   (`r > s`)

(`Rd.LipschitzGraph.modNorm_trace_le_flat`), where the Lipschitz case allows only `s < 1`.

**The extension of every order.** The extension `A(x) = a(Px) χ(2^j ⟪x, e⟫)` of a smooth atom on
`H` is a smooth atom on `V` of the same order
(`Rd.LipschitzGraph.exists_isSmoothAtom_extendAtom_flat`; for the flat graph the vertical cut-off
is `χ(2^j ⟪x, e⟫)`, `Rd.LipschitzGraph.vertCutoff_flat`).
The extended atoms therefore form packages of extended atoms of every order
(`Rd.LipschitzGraph.exists_flat_extension_atoms`). With the terms `g_j = η_j ⋆ (k_j ⋆ g)` of the
reproducing formula on `H` of moment order `Lh`, the extension of the graph domain
(`Rd.LipschitzGraph.graphExtension`) is `E g = ∑_j g_j(Px) χ(2^j ⟪x, e⟫)` and satisfies, for
`s > 0` and `s + 1/p < r`,

`‖E g‖_p + ‖(2^(k(s+1/p)) ω_r(E g, 2^(-k))_p)_k‖_{ℓ_q}
  ≤ K (‖g‖_{L_p(H)} + ‖(2^(ks) ω_{Lh}(g, 2^(-k))_p)_k‖_{ℓ_q})`

(`Rd.LipschitzGraph.modNorm_flatExtension_le`), and `Tr (E g) = g`
(`Rd.LipschitzGraph.trace_flatExtension`). Hence `B^s_{p,q}(H)` is the trace space of
`B^{s+1/p}_{p,q}` of the half-space for every `s > 0`
(`Rd.LipschitzGraph.exists_trace_eq_iff_flat`). The extension of the Lipschitz case uses moment
order `1` on `H` and reaches only `s < 1`; here the moment order `Lh > s` matches the smoothness.

**Functions continuous on the closed half-space** have their restrictions as traces
(`Rd.trace_ae_eq_of_continuousOn`): the folding `x ↦ x + (|⟪x, e⟫| - ⟪x, e⟫) e`
(`Rd.foldHalfSpace`) extends them continuously to `V`.
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric Set
open scoped ENNReal NNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

/-- **Derivatives of a composition with a linear map**:
`‖D^i (f ∘ L)(x)‖ ≤ ‖D^i f(L x)‖ ‖L‖^i`. -/
theorem norm_iteratedFDeriv_comp_clm_le {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : G →L[ℝ] E) {f : E → F} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (x : G) {i : ℕ}
    (hi : (i : WithTop ℕ∞) ≤ n) :
    ‖iteratedFDeriv ℝ i (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ i f (L x)‖ * ‖L‖ ^ i := by
  rw [L.iteratedFDeriv_comp_right hf x hi]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_eq ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

namespace LipschitzGraph

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (e : V) (he : ‖e‖ = 1)

/-! ### Restrictions of smooth atoms to the hyperplane -/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The graph map of the flat graph is the inclusion of `H = e^⊥`. -/
theorem flat_graphMap (x' : (flat e he).hyperplane) : (flat e he).graphMap x' = x' := by
  simp [graphMap, flat]

/-- **Restrictions of smooth atoms to the hyperplane**: for the flat graph, a smooth atom on `V`
of order `K` with centre `c` restricts to a smooth atom on `H` of order `K` with centre `P c`,
the same radius factor and the same constant. -/
theorem isSmoothAtom_comp_graphMap_flat {K : ℕ} {d A : ℝ} {j : ℕ} {c : V}
    {a : V → ℂ} (ha : IsSmoothAtom Set.univ K d A j c a) :
    IsSmoothAtom Set.univ K d A j ((flat e he).proj c) (a ∘ (flat e he).graphMap) := by
  set Ω := flat e he
  set ι : Ω.hyperplane →L[ℝ] V := Ω.hyperplane.subtypeL
  have hγ : Ω.graphMap = ι := funext (flat_graphMap e he)
  have hι : ‖ι‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp [ι]
  have hac : ContDiff ℝ K a := contDiffOn_univ.1 ha.contDiffOn
  have hc : ContDiff ℝ K (a ∘ Ω.graphMap) := by
    rw [hγ]
    exact hac.comp ι.contDiff
  refine ⟨hc.continuous.aestronglyMeasurable,
    fun x' hx' => ha.eq_zero _ (hx'.trans_le (Ω.norm_sub_proj_le x' c)), hc.contDiffOn,
    fun l hl y _ => ?_⟩
  rw [iteratedFDerivWithin_univ, hγ]
  refine (norm_iteratedFDeriv_comp_clm_le ι hac y (by exact_mod_cast hl)).trans ?_
  have h1 := ha.norm_iteratedFDerivWithin_le l hl (ι y) (mem_univ _)
  rw [iteratedFDerivWithin_univ] at h1
  calc ‖iteratedFDeriv ℝ l a (ι y)‖ * ‖ι‖ ^ l ≤ (A * 2 ^ (j * l)) * 1 :=
        mul_le_mul h1 (pow_le_one₀ (ContinuousLinearMap.opNorm_nonneg ι) hι) (by positivity)
          ((norm_nonneg _).trans h1)
    _ = A * 2 ^ (j * l) := mul_one _

/-! ### The trace of every order -/

/-- **The trace atoms of every order** on the flat graph: for every order `r ≥ 1` there are a
radius factor `d`, a constant `C < ∞` and an overlap bound `N` such that the restrictions
`a_{j,m} ∘ γ` of the cell atoms of `η_j ⋆ h` are regular atoms on `H` of order and exponent `r`
centred at `P c_{j,m}`, and the centres of the cells meeting `H` have overlap at most `N`
(`Rd.LipschitzGraph.norm_graphMap_sub_cellCenter_le` with `t = r`). -/
theorem exists_trace_atoms_flat (b : LocalMeansBump V) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (L : ℕ) {r : ℕ}
    (hr : 1 ≤ r) :
    ∃ (d : ℝ) (C : ℝ≥0∞) (N : ℕ), 0 ≤ d ∧ C ≠ ∞ ∧ ∀ (j : ℕ) {h : V → ℂ}, MemLp h p volume →
      (∀ m, IsRegularAtom p r r d C j ((flat e he).proj (cellCenter j m))
        (cellAtom p (b.dual L j) j h m ∘ (flat e he).graphMap)) ∧
      ∀ x' (S : Finset (Fin (finrank ℝ V) → ℤ)),
        (∀ m ∈ S, (flat e he).traceCoef b p L j h m ≠ 0 ∧
          ‖x' - (flat e he).proj (cellCenter j m)‖ ≤ (d + r) / 2 ^ j) → S.card ≤ N := by
  set Ω := flat e he
  obtain ⟨A, hA, hsm⟩ := b.exists_isSmoothAtom_cellAtom hp1 L r
  set d := 2 * (L : ℝ) * b.radius + finrank ℝ V with hd_def
  have hd : 0 ≤ d :=
    add_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg L)) b.radius_nonneg)
      (Nat.cast_nonneg _)
  have hint : (interior (Set.univ : Set Ω.hyperplane)).Nonempty := by
    rw [interior_univ]
    exact univ_nonempty
  refine ⟨d, ENNReal.ofReal (2 ^ r * (r : ℝ) ^ (r + 1) * A) *
      (((r + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (d ^ finrank ℝ Ω.hyperplane) *
        volume (ball (0 : Ω.hyperplane) 1))) ^ (1 / p.toReal),
    ⌈(2 * (d + (1 + Ω.M) * (2 * d + r)) + 2) ^ finrank ℝ V⌉₊, hd, ?_,
    fun j h hh => ⟨fun m => ?_, fun x' S hS => ?_⟩⟩
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)))
  · exact isRegularAtomOn_of_isSmoothAtom convex_univ MeasurableSet.univ hint hr le_rfl hd hA
      (isSmoothAtom_comp_graphMap_flat e he (hsm j hh m))
  · refine card_le_of_norm_sub_cellCenter_le j
      (add_nonneg hd (mul_nonneg (by linarith [Ω.M_nonneg]) (by positivity))) (Ω.graphMap x') S
      fun m hm => ?_
    obtain ⟨hcoef, hdist⟩ := hS m hm
    have hex : ∃ y', cellAtom p (b.dual L j) j h m (Ω.graphMap y') ≠ 0 := by
      by_contra hcon
      exact hcoef (by simp [traceCoef, hcon])
    exact Ω.norm_graphMap_sub_cellCenter_le (fun y hy => b.dual_eq_zero_of_lt L j hy) hex hdist

/-- **The trace of a series, of every order**: on the flat graph, for `0 < s < r` there is
`K < ∞` with `‖Tr‖_{L_p(H)} + ‖(2^(ks) ω_r(Tr, 2^(-k))_p)_k‖_{ℓ_q} ≤
K ‖(2^(j(s+1/p)) ‖h_j‖_p)_j‖_{ℓ_q}` for the trace `Tr = ∑_j (η_j ⋆ h_j) ∘ γ`, from the trace
atoms of order `r` (`Rd.LipschitzGraph.exists_trace_atoms_flat`,
`Rd.LipschitzGraph.modNorm_traceSeries_le_of_atoms`). -/
theorem modNorm_traceSeries_le_flat (b : LocalMeansBump V) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (L : ℕ) {r : ℕ} (hr : 1 ≤ r) {s : ℝ} (hs : 0 < s) (hsr : s < r) {q : ℝ≥0∞}
    (hq : 1 ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ h : ℕ → Lp ℂ p (volume : Measure V),
      lqNorm q (fun j => dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ) < ∞ →
      ‖(flat e he).traceSeries b hp L h‖ₑ + lqNorm q (fun k =>
          dyadicWeight s k * lpModulus p r ((flat e he).traceSeries b hp L h) k) ≤
        K * lqNorm q (fun j => dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ) := by
  obtain ⟨d, C, N, -, hC, hatoms⟩ := exists_trace_atoms_flat e he b (Fact.out : 1 ≤ p) L hr
  exact (flat e he).modNorm_traceSeries_le_of_atoms b hp L hs hsr hq hC hatoms

/-- **The trace theorem of every order on the half-space**: for `1 ≤ p < ∞`, `0 < s < r` and
`1 ≤ q ≤ ∞` there is `K < ∞` with
`‖Tr f‖_{L_p(H)} + ‖(2^(ks) ω_r(Tr f, 2^(-k))_p)_k‖_{ℓ_q} ≤
K (‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q})`. -/
theorem modNorm_trace_le_flat {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) (L : ℕ) {r : ℕ}
    (hr : 1 ≤ r) {s : ℝ} (hs : 0 < s) (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V),
      modNormOn (flat e he).measurableSet_domain L (s + 1 / p.toReal) q f < ∞ →
      ‖(flat e he).trace hp L f‖ₑ +
          lqNorm q (fun k => dyadicWeight s k * lpModulus p r ((flat e he).trace hp L f) k) ≤
        K * modNormOn (flat e he).measurableSet_domain L (s + 1 / p.toReal) q f := by
  set Ω := flat e he
  obtain ⟨K, hK, hle⟩ := modNorm_traceSeries_le_flat e he Ω.coneBump hp L hr hs hsr hq
  refine ⟨K * Ω.intrinsicConst L, ENNReal.mul_ne_top hK (Ω.intrinsicConst_ne_top L),
    fun f hf => ?_⟩
  have hX := Ω.intrinsicNorm_lt_top hp L (s + 1 / p.toReal) hq hf
  rw [mul_assoc]
  exact (hle (fun j => Ω.cutoff (Ω.coneBump.localMean hp L j f)) hX).trans
    (mul_le_mul' le_rfl (Ω.intrinsicNorm_le hp L (s + 1 / p.toReal) hq f))

/-! ### Extended atoms of every order -/

/-- The mollified graph of the flat graph vanishes. -/
theorem smoothGraph_flat (j : ℕ) (x' : (flat e he).hyperplane) :
    (flat e he).smoothGraph j x' = 0 := by
  have h : (flat e he).graphFun = 0 := funext fun x' => by simp [graphFun, flat]
  simp [smoothGraph, h, conv, convolution_zero]

/-- The vertical cut-off of the flat graph is `v_j(x) = χ(2^j ⟪x, e⟫)`. -/
theorem vertCutoff_flat (j : ℕ) (x : V) :
    (flat e he).vertCutoff j x = (flat e he).profile (2 ^ j * inner ℝ x e) := by
  rw [vertCutoff, vertCoord, smoothGraph_flat, sub_zero]
  rfl

/-- **Extended atoms of every order**: for the flat graph and every order `K` there is `B ≥ 0`
such that the extension `A(x) = a(Px) χ(2^j ⟪x, e⟫)` of a smooth atom `a` on `H` of order `K`,
level `j`, radius factor `d` and constant `A` is a smooth atom on `V` of order `K` with radius
factor `extendRadius d`, constant `2^K B A` and centre `c'`, by Leibniz's rule. -/
theorem exists_isSmoothAtom_extendAtom_flat (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {d A : ℝ} {j : ℕ} {c' : (flat e he).hyperplane}
      {a : (flat e he).hyperplane → ℂ}, 0 ≤ A → IsSmoothAtom Set.univ K d A j c' a →
      IsSmoothAtom Set.univ K ((flat e he).extendRadius d) (2 ^ K * B * A) j
        ((flat e he).extendCenter j c') ((flat e he).extendAtom j a) := by
  set Ω := flat e he
  obtain ⟨B₀, hB₀⟩ := exists_iteratedFDeriv_bound Ω.contDiff_profile Ω.hasCompactSupport_profile K
  refine ⟨|B₀|, abs_nonneg _, fun {d A j c' a} hA ha => ?_⟩
  set P : V →L[ℝ] Ω.hyperplane := Ω.proj
  set ℓ : V →L[ℝ] ℝ := (2 ^ j : ℝ) • innerSL ℝ e
  have hℓx : ∀ x, ℓ x = 2 ^ j * inner ℝ x e := fun x => by
    simp [ℓ, real_inner_comm]
  have hext : Ω.extendAtom j a = fun x => (a ∘ P) x * (Ω.profile ∘ ℓ) x := funext fun x => by
    rw [extendAtom, vertCutoff_flat, Function.comp_apply, Function.comp_apply, hℓx]
  have hP : ‖P‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]
    exact Ω.norm_proj_le x
  have hℓ : ‖ℓ‖ ≤ 2 ^ j := ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => by
    rw [hℓx, norm_mul, Real.norm_of_nonneg (by positivity)]
    gcongr
    exact (norm_inner_le_norm x e).trans (by rw [he, mul_one])
  have hac : ContDiff ℝ K a := contDiffOn_univ.1 ha.contDiffOn
  have h1 : ContDiff ℝ K (a ∘ P) := hac.comp P.contDiff
  have h2 : ContDiff ℝ K (Ω.profile ∘ ℓ) :=
    (Ω.contDiff_profile.of_le (by exact_mod_cast le_top)).comp ℓ.contDiff
  have hc : ContDiff ℝ K (Ω.extendAtom j a) := by
    rw [hext]
    exact h1.mul h2
  refine ⟨hc.continuous.aestronglyMeasurable, fun x hx => Ω.extendAtom_eq_zero j ha.eq_zero hx,
    hc.contDiffOn, fun l hl y _ => ?_⟩
  have hu : ∀ i ≤ K, ‖iteratedFDeriv ℝ i (a ∘ P) y‖ ≤ A * 2 ^ (j * i) := fun i hi => by
    refine (norm_iteratedFDeriv_comp_clm_le P hac y (by exact_mod_cast hi)).trans ?_
    have h := ha.norm_iteratedFDerivWithin_le i hi (P y) (mem_univ _)
    rw [iteratedFDerivWithin_univ] at h
    calc ‖iteratedFDeriv ℝ i a (P y)‖ * ‖P‖ ^ i ≤ (A * 2 ^ (j * i)) * 1 :=
          mul_le_mul h (pow_le_one₀ (ContinuousLinearMap.opNorm_nonneg P) hP) (by positivity)
            ((norm_nonneg _).trans h)
      _ = A * 2 ^ (j * i) := mul_one _
  have hv : ∀ i ≤ K, ‖iteratedFDeriv ℝ i (Ω.profile ∘ ℓ) y‖ ≤ |B₀| * 2 ^ (j * i) := fun i hi => by
    refine (norm_iteratedFDeriv_comp_clm_le ℓ Ω.contDiff_profile y
      (by exact_mod_cast le_top)).trans ?_
    rw [pow_mul]
    exact mul_le_mul ((hB₀ i hi (ℓ y)).trans (le_abs_self _))
      (pow_le_pow_left₀ (ContinuousLinearMap.opNorm_nonneg ℓ) hℓ i) (by positivity)
      (abs_nonneg _)
  rw [iteratedFDerivWithin_univ, hext]
  refine (norm_iteratedFDeriv_mul_le h1 h2 y (by exact_mod_cast hl)).trans ?_
  calc ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * ‖iteratedFDeriv ℝ i (a ∘ P) y‖ *
        ‖iteratedFDeriv ℝ (l - i) (Ω.profile ∘ ℓ) y‖
      ≤ ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * (A * |B₀| * 2 ^ (j * l)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hil : i ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        calc ‖iteratedFDeriv ℝ i (a ∘ P) y‖ * ‖iteratedFDeriv ℝ (l - i) (Ω.profile ∘ ℓ) y‖
            ≤ (A * 2 ^ (j * i)) * (|B₀| * 2 ^ (j * (l - i))) :=
              mul_le_mul (hu i (hil.trans hl)) (hv (l - i) ((Nat.sub_le l i).trans hl))
                (norm_nonneg _) (by positivity)
          _ = A * |B₀| * 2 ^ (j * l) := by
              rw [show j * l = j * i + j * (l - i) by rw [← Nat.mul_add, Nat.add_sub_cancel' hil],
                pow_add]
              ring
    _ = 2 ^ l * (A * |B₀| * 2 ^ (j * l)) := by
        rw [← Finset.sum_mul]
        have hsum : ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) = 2 ^ l := by
          exact_mod_cast Nat.sum_range_choose l
        rw [hsum]
    _ ≤ 2 ^ K * (A * |B₀| * 2 ^ (j * l)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hl) (by positivity)
    _ = 2 ^ K * |B₀| * A * 2 ^ (j * l) := by ring

/-! ### The extension of every order -/

section Extension

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The extended atoms of every order**: for the flat graph, every moment order `Lh` and every
order `r ≥ 1` there are a radius factor `d`, a constant `C < ∞` and an overlap bound `N` such that
the extensions of the cell atoms on `H` form a package of extended atoms of order `r`
(`Rd.LipschitzGraph.HasExtensionAtoms`): the cell atoms are smooth of order `r`, and so are their
extensions (`Rd.LipschitzGraph.exists_isSmoothAtom_extendAtom_flat`). -/
theorem exists_flat_extension_atoms (Lh : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    ∃ (d : ℝ) (C : ℝ≥0∞) (N : ℕ), C ≠ ∞ ∧ (flat e he).HasExtensionAtoms p Lh r d C N := by
  set Ω := flat e he
  have hp1 : 1 ≤ p := Fact.out
  obtain ⟨A, hA, hsm⟩ := Ω.graphBump.exists_isSmoothAtom_cellAtom hp1 Lh r
  obtain ⟨B, hB, hext⟩ := exists_isSmoothAtom_extendAtom_flat e he r
  set d := Ω.extendRadius (Ω.extRadiusH Lh)
  have hd : 0 ≤ d := Ω.extendRadius_nonneg (Ω.extRadiusH_nonneg Lh)
  have hBA : 0 ≤ 2 ^ r * B * A := by positivity
  have hint : (interior (Set.univ : Set V)).Nonempty := by
    rw [interior_univ]
    exact univ_nonempty
  refine ⟨d, ENNReal.ofReal (2 ^ r * (r : ℝ) ^ (r + 1) * (2 ^ r * B * A)) *
      (((r + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (d ^ finrank ℝ V) * volume (ball (0 : V) 1))) ^
        (1 / p.toReal), ⌈(2 * (d + r) + 2) ^ finrank ℝ Ω.hyperplane⌉₊,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne))),
    fun j h hh => ⟨fun m => ?_, fun x S hS => ?_⟩⟩
  · exact isRegularAtomOn_of_isSmoothAtom convex_univ MeasurableSet.univ hint hr le_rfl hd hBA
      (hext hA (hsm j hh m))
  · refine card_le_of_norm_sub_cellCenter_le j (by positivity) (Ω.proj x) S fun m hm => ?_
    calc ‖Ω.proj x - cellCenter j m‖ = ‖Ω.proj (x - Ω.extendCenter j (cellCenter j m))‖ := by
          rw [map_sub, Ω.proj_extendCenter]
      _ ≤ ‖x - Ω.extendCenter j (cellCenter j m)‖ := Ω.norm_proj_le _
      _ ≤ (d + r) / 2 ^ j := (hS m hm).2

/-- **The extension of every order is bounded by the local means**: for the flat graph, `s > 0`
and `s + 1/p < r` there is `K < ∞` with
`‖E g‖_p + ‖(2^(k(s+1/p)) ω_r(E g, 2^(-k))_p)_k‖_{ℓ_q} ≤ K ‖(2^(js) ‖k_j ⋆ g‖_p)_j‖_{ℓ_q}` for the
extension `E g` of moment order `Lh` (`Rd.LipschitzGraph.graphExtension`), from the extended atoms
of order `r` (`Rd.LipschitzGraph.modNorm_graphExtension_le_localMeansNorm`). -/
theorem modNorm_flatExtension_le_localMeansNorm (hp : p ≠ ∞) (Lh : ℕ) {r : ℕ} {s : ℝ}
    (hs : 0 < s) (hsr : s + 1 / p.toReal < r) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ g : Lp ℂ p (volume : Measure (flat e he).hyperplane),
      (flat e he).graphBump.localMeansNorm hp Lh s q g < ∞ →
      ‖(flat e he).graphExtension hp Lh g‖ₑ + lqNorm q (fun k => dyadicWeight (s + 1 / p.toReal) k *
          lpModulus p r ((flat e he).graphExtension hp Lh g) k) ≤
        K * (flat e he).graphBump.localMeansNorm hp Lh s q g := by
  obtain ⟨d, C, N, hC, hat⟩ := exists_flat_extension_atoms e he (p := p) Lh
    (one_le_of_add_one_div_toReal_lt hs hsr)
  exact ⟨_, atomSynthConst_ne_top Fact.out N hC r (by positivity) hsr, fun g hX =>
    (flat e he).modNorm_graphExtension_le_localMeansNorm hp Lh hat hs hsr hq hX⟩

/-- **The extension of every order, bounded by the moduli of `g`**: for the flat graph, `s > 0`
and `s + 1/p < r` there is `K < ∞` with
`‖E g‖_p + ‖(2^(k(s+1/p)) ω_r(E g, 2^(-k))_p)_k‖_{ℓ_q} ≤
K (‖g‖_{L_p(H)} + ‖(2^(ks) ω_{Lh}(g, 2^(-k))_p)_k‖_{ℓ_q})` for the extension of moment order `Lh`
(`Rd.LipschitzGraph.modNorm_graphExtension_le_of_atoms`). -/
theorem modNorm_flatExtension_le (hp : p ≠ ∞) (Lh : ℕ) {r : ℕ} {s : ℝ} (hs : 0 < s)
    (hsr : s + 1 / p.toReal < r) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ g : Lp ℂ p (volume : Measure (flat e he).hyperplane),
      ‖g‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p Lh g k) < ∞ →
      ‖(flat e he).graphExtension hp Lh g‖ₑ + lqNorm q (fun k => dyadicWeight (s + 1 / p.toReal) k *
          lpModulus p r ((flat e he).graphExtension hp Lh g) k) ≤
        K * (‖g‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p Lh g k)) := by
  obtain ⟨d, C, N, hC, hat⟩ := exists_flat_extension_atoms e he (p := p) Lh
    (one_le_of_add_one_div_toReal_lt hs hsr)
  exact ⟨_, ENNReal.mul_ne_top (atomSynthConst_ne_top Fact.out N hC r (by positivity) hsr)
    ((flat e he).graphBump.upperConst_ne_top Lh s), fun g hg =>
      (flat e he).modNorm_graphExtension_le_of_atoms hp Lh hat hs hsr hq hg⟩

/-- **The trace of the extension of every order**: for the flat graph, `L ≥ 2`, `Lh ≥ 1`, `s > 0`
with `s + 1/p < L` and `g ∈ L_p(H)` with a finite local means quasi-norm
`‖(2^(js) ‖k_j ⋆ g‖_p)_j‖_{ℓ_q}`, the extension of moment order `Lh` has `Tr (E g) = g`, from the
extended atoms of order `L` (`Rd.LipschitzGraph.trace_graphExtension_of_atoms`). -/
theorem trace_flatExtension (hp : p ≠ ∞) {L : ℕ} (hL : 2 ≤ L) {Lh : ℕ} (hLh : 1 ≤ Lh) {s : ℝ}
    (hs : 0 < s) (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {g : Lp ℂ p (volume : Measure (flat e he).hyperplane)}
    (hX : (flat e he).graphBump.localMeansNorm hp Lh s q g < ∞) :
    (flat e he).trace hp L ((flat e he).graphExtension hp Lh g) = g := by
  obtain ⟨d, C, N, hC, hat⟩ := exists_flat_extension_atoms e he (p := p) Lh (r := L) (by omega)
  exact (flat e he).trace_graphExtension_of_atoms hp hLh le_rfl hC hat hs hsL hq hX

/-- **The trace space of the half-space, for every smoothness**: for `1 ≤ p < ∞`, `s > 0`,
`1 ≤ q ≤ ∞`, `L ≥ 2` with `s + 1/p < L`, and `r > s`, `g ∈ L_p(H)` is the trace of some `f` with
`‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞` iff
`‖g‖_p + ‖(2^(ks) ω_r(g, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. The trace is bounded
(`Rd.LipschitzGraph.modNorm_trace_le_flat`), and the extension of moment order `r` is such an `f`
(`Rd.LipschitzGraph.trace_flatExtension`). -/
theorem exists_trace_eq_iff_flat (hp : p ≠ ∞) {L : ℕ} (hL : 2 ≤ L) {r : ℕ} {s : ℝ} (hs : 0 < s)
    (hsr : s < r) (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (g : Lp ℂ p (volume : Measure (flat e he).hyperplane)) :
    (∃ f : Lp ℂ p (volume : Measure V),
        modNormOn (flat e he).measurableSet_domain L (s + 1 / p.toReal) q f < ∞ ∧
          (flat e he).trace hp L f = g) ↔
      ‖g‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r g k) < ∞ := by
  have hr : 1 ≤ r := Nat.cast_pos.1 (hs.trans hsr)
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨K, hK, hle⟩ := modNorm_trace_le_flat e he hp L hr hs hsr hq
    exact (hle f hf).trans_lt (ENNReal.mul_lt_top hK.lt_top hf)
  · intro hg
    have hX : (flat e he).graphBump.localMeansNorm hp r s q g < ∞ :=
      ((flat e he).graphBump.localMeansNorm_le hp r s hq g).trans_lt
        (ENNReal.mul_lt_top ((flat e he).graphBump.upperConst_ne_top r s).lt_top hg)
    obtain ⟨K, hK, hle⟩ := modNorm_flatExtension_le_localMeansNorm e he hp r hs hsL hq
    exact ⟨(flat e he).graphExtension hp r g, ((flat e he).intrinsicNorm_lt_top_of_modNorm hp L
      hq ((hle g hX).trans_lt (ENNReal.mul_lt_top hK.lt_top hX))).1,
      trace_flatExtension e he hp hL hr hs hsL hq hX⟩

end Extension

end LipschitzGraph

/-! ### Traces of functions continuous on the closed half-space -/

section Fold

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (e : V)

/-- The **folding** onto the closed half-space, `x ↦ x + (|⟪x, e⟫| - ⟪x, e⟫) e`: it reflects
`{x : ⟪x, e⟫ < 0}` in `e^⊥` and fixes the closed half-space. -/
noncomputable def foldHalfSpace (x : V) : V := x + (|inner ℝ x e| - inner ℝ x e) • e

/-- The folding is continuous. -/
theorem continuous_foldHalfSpace : Continuous (foldHalfSpace e) :=
  continuous_id.add ((((continuous_id.inner continuous_const).abs).sub
    (continuous_id.inner continuous_const)).smul continuous_const)

/-- The folding fixes the closed half-space. -/
theorem foldHalfSpace_of_nonneg {x : V} (hx : 0 ≤ inner ℝ x e) : foldHalfSpace e x = x := by
  rw [foldHalfSpace, abs_of_nonneg hx, sub_self, zero_smul, add_zero]

variable {e} (he : ‖e‖ = 1)
include he

/-- `⟪F x, e⟫ = |⟪x, e⟫|` for the folding `F`. -/
theorem inner_foldHalfSpace (x : V) : inner ℝ (foldHalfSpace e x) e = |inner ℝ x e| := by
  rw [foldHalfSpace, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]
  ring

/-- The folding maps into the closed half-space. -/
theorem foldHalfSpace_mem (x : V) : foldHalfSpace e x ∈ closedHalfSpace e := by
  change 0 ≤ inner ℝ (foldHalfSpace e x) e
  rw [inner_foldHalfSpace he]
  exact abs_nonneg _

/-- The folding preserves the norm: `‖x + c e‖² = ‖x‖² + c (2⟪x, e⟫ + c)` vanishes in the second
term for `c = |⟪x, e⟫| - ⟪x, e⟫`. -/
theorem norm_foldHalfSpace (x : V) : ‖foldHalfSpace e x‖ = ‖x‖ := by
  have h : ‖foldHalfSpace e x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [foldHalfSpace, norm_add_sq_real, norm_smul, he, mul_one, real_inner_smul_right,
      Real.norm_eq_abs, sq_abs]
    rw [show ‖x‖ ^ 2 + 2 * ((|inner ℝ x e| - inner ℝ x e) * inner ℝ x e) +
        (|inner ℝ x e| - inner ℝ x e) ^ 2 = ‖x‖ ^ 2 + (|inner ℝ x e| ^ 2 - inner ℝ x e ^ 2) by
      ring, sq_abs, sub_self, add_zero]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h


variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Traces of functions continuous on the closed half-space**: let `f ∈ L_p(V)` have a finite
intrinsic quasi-norm of smoothness `s + 1/p`, `s > 0`, on the open half-space, and let `G` be
continuous on the closed half-space, vanish there outside a compact set, and agree with `f` almost
everywhere on the open half-space. Then `Tr f = G` almost everywhere on `e^⊥`. The folded `G ∘ F`
is continuous with compact support and agrees with `f` on the half-space, and traces of continuous
functions are restrictions (`Rd.LipschitzGraph.trace_ae_eq_comp_graphMap`). -/
theorem trace_ae_eq_of_continuousOn (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s)
    {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)}
    (hf : modNormOn (LipschitzGraph.flat e he).measurableSet_domain L (s + 1 / p.toReal) q f < ∞)
    {G : V → ℂ} (hG : ContinuousOn G (closedHalfSpace e)) {K : Set V} (hK : IsCompact K)
    (hGK : ∀ x ∈ closedHalfSpace e, x ∉ K → G x = 0)
    (hfG : ∀ᵐ x ∂volume, x ∈ (LipschitzGraph.flat e he).domain → f x = G x) :
    (LipschitzGraph.flat e he).trace hp L f =ᵐ[volume] fun x' => G x' := by
  set Ω := LipschitzGraph.flat e he
  set G' := G ∘ foldHalfSpace e
  have hG'c : Continuous G' :=
    hG.comp_continuous (continuous_foldHalfSpace e) (foldHalfSpace_mem he)
  have hG's : HasCompactSupport G' := by
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    refine HasCompactSupport.intro (isCompact_closedBall (0 : V) R) fun x hx => ?_
    have hfx : foldHalfSpace e x ∉ K := fun h => hx (by
      have h' := hR h
      rw [mem_closedBall_zero_iff, norm_foldHalfSpace he] at h'
      exact mem_closedBall_zero_iff.2 h')
    exact hGK _ (foldHalfSpace_mem he x) hfx
  have hmem : MemLp G' p volume := hG'c.memLp_of_hasCompactSupport hG's
  have hFG : (hmem.toLp G' : V → ℂ) =ᵐ[volume] G' := hmem.coeFn_toLp
  have hcut : Ω.cutoff (hmem.toLp G') = Ω.cutoff f := by
    refine Lp.ext ?_
    filter_upwards [Ω.cutoff_apply_ae (hmem.toLp G'), Ω.cutoff_apply_ae f, hFG, hfG]
      with x h1 h2 h3 h4
    rw [h1, h2]
    by_cases hx : x ∈ Ω.domain
    · rw [indicator_of_mem hx, indicator_of_mem hx, h3, h4 hx]
      change G (foldHalfSpace e x) = G x
      rw [foldHalfSpace_of_nonneg e (le_of_lt (show 0 < inner ℝ x e from hx))]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  have hFfin : modNormOn Ω.measurableSet_domain L (s + 1 / p.toReal) q (hmem.toLp G') < ∞ :=
    (modNormOn_congr Ω.measurableSet_domain hcut).trans_lt hf
  rw [← Ω.trace_congr hp L hcut]
  filter_upwards [Ω.trace_ae_eq_comp_graphMap hp hL hs hq hFfin hG'c hFG] with x' hx'
  have hx'0 : inner ℝ (x' : V) e = 0 := by
    have h := x'.2
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm] at h
    exact h
  rw [hx', Function.comp_apply, LipschitzGraph.flat_graphMap]
  change G (foldHalfSpace e x') = G x'
  rw [foldHalfSpace_of_nonneg e hx'0.ge]

end Fold

end Rd
