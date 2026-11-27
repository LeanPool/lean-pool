/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Manifolds.BesovAtlas

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Besov spaces on compact manifolds

Let `M` be a compact manifold with model `I` whose range `Ω = range I` is a Besov domain (the
half-space for manifolds with boundary, the quadrant `{y : ∀ i, 0 ≤ y_i}` for manifolds with
corners, `E` for manifolds without boundary), `μ` a smooth measure and `1 ≤ p < ∞`. For a
Besov atlas `A` with charts `κ_i` and partition of unity `ψ_i`, the **Besov quasi-norm** of
`f ∈ L_p(μ)` is the sum of the intrinsic quasi-norms of the chart pieces
(`Manifold.BesovAtlas.besovNorm`):

`‖f‖_{A, r, s, q} = ∑_i N_Ω((ψ_i f) ∘ κ_i⁻¹)`,
`N_Ω(G) = ‖1_Ω G‖_p + ‖(2^(ks) ω_r(G, 2^(-k), Ω)_p)_k‖_{ℓ_q}`.

Each term `N_Ω((ψ_i f) ∘ κ_i⁻¹)` is at most `‖f‖_{A, r, s, q}`
(`Manifold.BesovAtlas.modNormOn_pieceLp_le_besovNorm`).

**Independence of the atlas** (`Manifold.BesovAtlas.besovNorm_le_besovNorm`): for two Besov
atlases and `0 < s < r` there is `C < ∞` with `‖f‖_{A} ≤ C ‖f‖_{A'}`. The pieces of `A` are
finite sums of the pieces of `A'` transported by the changes of charts with cut-offs
(`Manifold.BesovAtlas.pieceLp_eq_sum`), the intrinsic quasi-norm is subadditive
(`Rd.modNormOn_finsetSum_le`), and the changes of charts are bounded on the Besov domain `Ω`
(`Rd.CutoffDiffeo.modNormOn_applyLp_le_modNormOn`). The order `r > s` does not matter either
(`Manifold.BesovAtlas.memBesov_iff_besovNorm_lt_top`), so the **Besov space**
`B^s_{p,q}(M) = {f : ‖f‖_{A, ⌊s⌋+1, s, q} < ∞}` (`Manifold.MemBesov`) depends on no choice
(`Manifold.memBesov_iff`).

Membership is a condition on each piece: `f ∈ B^s_{p,q}` for `A` iff every piece has a finite
intrinsic quasi-norm (`Manifold.BesovAtlas.memBesov_iff_forall_modNormOn_lt_top`).

**Lifts from a chart**: the lift `L_k F = θ_k · F ∘ κ_k` is linear on `L_p(E)`
(`Manifold.BesovAtlas.chartLiftLp_add`, `Manifold.BesovAtlas.chartLiftLp_smul`), and for
`F ∈ B^s_{p,q}(E)` it lies in `B^s_{p,q}(M)` (`Manifold.BesovAtlas.memBesov_chartLiftLp`), since
its pieces are the images `T_{ik} F` under the changes of charts
(`Manifold.BesovAtlas.pieceLp_chartLiftLp`).

**Manifolds with corners**: the range of Mathlib's model `modelWithCornersEuclideanQuadrant n` is a
Besov domain (`Rd.BesovDomain.range_euclideanQuadrant` in
`FunctionSpaces.Domains.Lipschitz.BesovDomains`), so all of this holds for compact manifolds with
corners modelled on the quadrant.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal Manifold ContDiff

open ENNReal (lqNorm dyadicWeight)

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] {μ : Measure M} [IsSmoothMeasure I μ]
  [hB : Rd.BesovDomain (range I)] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)

namespace BesovAtlas

variable (A : BesovAtlas I M)

/-! ### Linearity of the pieces -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] [CompactSpace M] hB in
/-- The pieces are additive. -/
theorem piece_add (i : Fin A.n) (g₁ g₂ : M → ℂ) :
    A.piece i (g₁ + g₂) = A.piece i g₁ + A.piece i g₂ := by
  funext y
  by_cases hy : y ∈ (A.ext i).target
  · simp only [piece, indicator_of_mem hy, Pi.add_apply, mul_add]
  · simp only [piece, indicator_of_notMem hy, Pi.add_apply, add_zero]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] [CompactSpace M] hB in
/-- The pieces are homogeneous. -/
theorem piece_smul (i : Fin A.n) (c : ℂ) (g : M → ℂ) : A.piece i (c • g) = c • A.piece i g := by
  funext y
  by_cases hy : y ∈ (A.ext i).target
  · simp only [piece, indicator_of_mem hy, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [piece, indicator_of_notMem hy, Pi.smul_apply, smul_zero]

omit hB in
/-- **The pieces see only classes**: if `g₁ = g₂` `μ`-almost everywhere, their pieces agree
almost everywhere, by the `L_1` bound of the pieces of `g₁ - g₂`. -/
theorem piece_ae_eq (i : Fin A.n) {g₁ g₂ : M → ℂ} (h₁ : StronglyMeasurable g₁)
    (h₂ : StronglyMeasurable g₂) (h : g₁ =ᵐ[μ] g₂) : A.piece i g₁ =ᵐ[volume] A.piece i g₂ := by
  obtain ⟨C, -, hle⟩ := A.exists_eLpNorm_piece_le μ i one_ne_zero ENNReal.one_ne_top
  have hsub : A.piece i (g₁ + (-1 : ℂ) • g₂) = A.piece i g₁ + (-1 : ℂ) • A.piece i g₂ := by
    rw [piece_add, piece_smul]
  have h0 : eLpNorm (g₁ + (-1 : ℂ) • g₂) 1 μ = 0 := by
    rw [eLpNorm_congr_ae (g := 0) (by filter_upwards [h] with x hx; simp [hx]), eLpNorm_zero]
  have hm : StronglyMeasurable (g₁ + (-1 : ℂ) • g₂) := h₁.add (h₂.const_smul _)
  have hz : A.piece i (g₁ + (-1 : ℂ) • g₂) =ᵐ[volume] 0 :=
    (eLpNorm_eq_zero_iff one_ne_zero).1
      (le_antisymm ((hle _ hm).trans_eq (by rw [h0, mul_zero])) zero_le)
  filter_upwards [hz] with y hy
  rw [hsub, Pi.add_apply, Pi.smul_apply, Pi.zero_apply] at hy
  linear_combination hy

omit hB in
/-- The pieces in `L_p` are additive. -/
theorem pieceLp_add (i : Fin A.n) (f g : Lp ℂ p μ) :
    A.pieceLp μ hp i (f + g) = A.pieceLp μ hp i f + A.pieceLp μ hp i g := by
  refine Lp.ext ?_
  have h := A.piece_ae_eq i (Lp.stronglyMeasurable (f + g))
    ((Lp.stronglyMeasurable f).add (Lp.stronglyMeasurable g)) (Lp.coeFn_add f g)
  filter_upwards [A.pieceLp_ae μ hp i (f + g), A.pieceLp_ae μ hp i f, A.pieceLp_ae μ hp i g,
    Lp.coeFn_add (A.pieceLp μ hp i f) (A.pieceLp μ hp i g), h] with y h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h2, h3, h5, piece_add, Pi.add_apply]

omit hB in
/-- The pieces in `L_p` are homogeneous. -/
theorem pieceLp_smul (i : Fin A.n) (c : ℂ) (f : Lp ℂ p μ) :
    A.pieceLp μ hp i (c • f) = c • A.pieceLp μ hp i f := by
  refine Lp.ext ?_
  have h := A.piece_ae_eq i (Lp.stronglyMeasurable (c • f))
    ((Lp.stronglyMeasurable f).const_smul c) (Lp.coeFn_smul c f)
  filter_upwards [A.pieceLp_ae μ hp i (c • f), A.pieceLp_ae μ hp i f,
    Lp.coeFn_smul c (A.pieceLp μ hp i f), h] with y h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, h2, h4, piece_smul, Pi.smul_apply]

omit hB in
/-- The pieces of `0` vanish. -/
theorem pieceLp_zero (i : Fin A.n) : A.pieceLp μ hp i 0 = 0 := by
  simpa using A.pieceLp_smul hp i 0 0

omit hB in
/-- The pieces in `L_p` of a finite sum are the sums of the pieces. -/
theorem pieceLp_finsetSum (i : Fin A.n) {ι : Type*} (t : Finset ι) (f : ι → Lp ℂ p μ) :
    A.pieceLp μ hp i (∑ j ∈ t, f j) = ∑ j ∈ t, A.pieceLp μ hp i (f j) := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, A.pieceLp_zero hp i]
  | insert j t hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, A.pieceLp_add hp i, ih]

/-- The **Besov quasi-norm of a Besov atlas**: the sum over the charts of the intrinsic
quasi-norms on `range I` of the chart pieces `(ψ_i f) ∘ κ_i⁻¹`, with differences of order `r`. -/
noncomputable def besovNorm (r : ℕ) (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p μ) : ℝ≥0∞ :=
  ∑ i, Rd.modNormOn (Rd.BesovDomain.measurableSet (range I)) r s q (A.pieceLp μ hp i f)

/-- **One piece is at most the whole**: the intrinsic quasi-norm of the `i`-th chart piece is at
most the Besov quasi-norm of the atlas, one term of its sum (Mathlib's `Finset.single_le_sum`). -/
theorem modNormOn_pieceLp_le_besovNorm (r : ℕ) (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p μ) (i : Fin A.n) :
    Rd.modNormOn (Rd.BesovDomain.measurableSet (range I)) r s q (A.pieceLp μ hp i f) ≤
      A.besovNorm hp r s q f :=
  Finset.single_le_sum (f := fun i =>
    Rd.modNormOn (Rd.BesovDomain.measurableSet (range I)) r s q (A.pieceLp μ hp i f))
    (fun _ _ => zero_le) (Finset.mem_univ i)

/-- **Independence of the atlas**: for two Besov atlases `A, A'`, `0 < s < r` and `1 ≤ q ≤ ∞`
there is `C < ∞` with `‖f‖_{A, r, s, q} ≤ C ‖f‖_{A', r, s, q}` for all `f ∈ L_p(μ)`. -/
theorem besovNorm_le_besovNorm [IsManifold I ∞ M] (A' : BesovAtlas I M) {r : ℕ} (hr : 1 ≤ r)
    {s : ℝ} (hs : 0 < s) (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : Lp ℂ p μ,
      A.besovNorm hp r s q f ≤ C * A'.besovNorm hp r s q f := by
  set Ω := range I
  set hΩ := Rd.BesovDomain.measurableSet Ω
  choose C hC hT using fun ij : Fin A.n × Fin A'.n =>
    (A.transition A' ij.1 ij.2).modNormOn_applyLp_le_modNormOn hp hr hs hsr hq
  set S := ∑ ij, C ij
  have hS : S ≠ ⊤ := ENNReal.sum_ne_top.2 fun ij _ => hC ij
  have hCS : ∀ ij, C ij ≤ S := fun ij =>
    Finset.single_le_sum (f := C) (fun _ _ => zero_le) (Finset.mem_univ ij)
  refine ⟨1 + A.n * S, ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hS⟩, fun f => ?_⟩
  by_cases hfin : A'.besovNorm hp r s q f = ⊤
  · rw [hfin, ENNReal.mul_top (by simp)]
    exact le_top
  set N : Fin A'.n → ℝ≥0∞ := fun j => Rd.modNormOn hΩ r s q (A'.pieceLp μ hp j f)
  have hN : ∀ j, N j < ⊤ := fun j => (Finset.single_le_sum (f := N) (fun _ _ => zero_le)
    (Finset.mem_univ j)).trans_lt (lt_top_iff_ne_top.2 hfin)
  have hterm : ∀ i j, Rd.modNormOn hΩ r s q ((A.transition A' i j).applyLp hB.convex
      hB.interior_nonempty hΩ hp (A'.pieceLp μ hp j f)) ≤ S * N j := fun i j =>
    (hT (i, j) _ (hN j)).trans (mul_le_mul' (hCS (i, j)) le_rfl)
  calc A.besovNorm hp r s q f
      = ∑ i, Rd.modNormOn hΩ r s q (∑ j, (A.transition A' i j).applyLp hB.convex
          hB.interior_nonempty hΩ hp (A'.pieceLp μ hp j f)) := by
        simp only [besovNorm]
        exact Finset.sum_congr rfl fun i _ => by rw [A.pieceLp_eq_sum A' μ hp i f]
    _ ≤ ∑ i : Fin A.n, ∑ j, S * N j := Finset.sum_le_sum fun i _ =>
        (Rd.modNormOn_finsetSum_le hΩ r s hq _ _).trans (Finset.sum_le_sum fun j _ => hterm i j)
    _ = A.n * S * A'.besovNorm hp r s q f := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
          mul_assoc]
        rfl
    _ ≤ (1 + A.n * S) * A'.besovNorm hp r s q f := mul_le_mul' le_add_self le_rfl

/-- **The Besov quasi-norm is subadditive** for `q ≥ 1`. -/
theorem besovNorm_add_le (r : ℕ) (s : ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q) (f g : Lp ℂ p μ) :
    A.besovNorm hp r s q (f + g) ≤ A.besovNorm hp r s q f + A.besovNorm hp r s q g := by
  simp only [besovNorm, pieceLp_add, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Rd.modNormOn_add_le _ r s hq _ _

/-- **The Besov quasi-norm is homogeneous**: `‖c f‖ = |c| ‖f‖`. -/
theorem besovNorm_const_smul (r : ℕ) (s : ℝ) (q : ℝ≥0∞) (c : ℂ) (f : Lp ℂ p μ) :
    A.besovNorm hp r s q (c • f) = ‖c‖ₑ * A.besovNorm hp r s q f := by
  simp only [besovNorm, pieceLp_smul, Rd.modNormOn_const_smul, Finset.mul_sum]

/-- **The Besov quasi-norm bounds the `L_p` norm**: `‖f‖_{L_p(μ)} ≤ C ‖f‖_{A, r, s, q}`, since
`f = ∑_i ψ_i f`, the `L_p` norms of `ψ_i f` on `M` and of its piece in the chart are comparable,
and the pieces live on `range I`. -/
theorem exists_enorm_le_besovNorm (r : ℕ) (s : ℝ) (q : ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : Lp ℂ p μ, ‖f‖ₑ ≤ C * A.besovNorm hp r s q f := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hΩ := Rd.BesovDomain.measurableSet (range I)
  -- the chart bound for each piece
  have hchart : ∀ i, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ g : M → ℂ, StronglyMeasurable g →
      eLpNorm (fun x => (A.psi i x : ℂ) * g x) p μ ≤ C * eLpNorm (A.piece i g) p volume := by
    intro i
    obtain ⟨_, C, -, hC, hcmp⟩ := IsSmoothMeasure.exists_eLpNorm_chart_le (I := I) μ
      (A.chart_mem i) (isClosed_tsupport _).isCompact (A.tsupport_psi_subset i) hp0 hp (F := ℂ)
    exact ⟨C, hC, fun g hg => (hcmp (fun x => (A.psi i x : ℂ) * g x)
      ((A.contMDiff_psi i).continuous.measurable.complex_ofReal.mul
        hg.measurable).stronglyMeasurable
      fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero, zero_mul]).2⟩
  choose C hC hle using hchart
  set Cmax := ∑ i, C i
  have hCmax : ∀ i, C i ≤ Cmax := fun i =>
    Finset.single_le_sum (f := C) (fun _ _ => zero_le) (Finset.mem_univ i)
  refine ⟨Cmax, ENNReal.sum_ne_top.2 fun i _ => hC i, fun f => ?_⟩
  -- `f = ∑_i ψ_i f`
  have hsum : (f : M → ℂ) = ∑ i, fun x => (A.psi i x : ℂ) * f x := by
    funext x
    rw [Finset.sum_apply, ← Finset.sum_mul, ← Complex.ofReal_sum, A.sum_psi, Complex.ofReal_one,
      one_mul]
  -- the pieces live on `range I`
  have hpiece : ∀ i, eLpNorm (A.piece i f) p volume ≤
      Rd.modNormOn hΩ r s q (A.pieceLp μ hp i f) := fun i => by
    have h : eLpNorm (A.piece i f) p volume = ‖Rd.indicatorLp hΩ (A.pieceLp μ hp i f)‖ₑ := by
      rw [Lp.eNorm_def]
      refine eLpNorm_congr_ae ?_
      filter_upwards [Rd.indicatorLp_apply_ae hΩ (A.pieceLp μ hp i f), A.pieceLp_ae μ hp i f]
        with y h1 h2
      rw [h1]
      by_cases hy : y ∈ range I
      · rw [indicator_of_mem hy, h2]
      · rw [indicator_of_notMem hy, piece, indicator_of_notMem fun h =>
          hy ((A.chart i).extend_target_subset_range h)]
    rw [h]
    exact le_add_right le_rfl
  calc ‖f‖ₑ = eLpNorm (∑ i, fun x => (A.psi i x : ℂ) * f x) p μ := by
        rw [Lp.eNorm_def, ← hsum]
    _ ≤ ∑ i, eLpNorm (fun x => (A.psi i x : ℂ) * f x) p μ :=
        eLpNorm_sum_le hp1
    _ ≤ ∑ i, Cmax * Rd.modNormOn hΩ r s q (A.pieceLp μ hp i f) :=
        Finset.sum_le_sum fun i _ => (hle i f (Lp.stronglyMeasurable f)).trans
          (mul_le_mul' (hCmax i) (hpiece i))
    _ = Cmax * A.besovNorm hp r s q f := by rw [← Finset.mul_sum]; rfl

/-- The **Besov space of a Besov atlas**: `f ∈ L_p(μ)` with a finite Besov quasi-norm of order
`⌊s⌋ + 1`. -/
def MemBesov (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p μ) : Prop :=
  A.besovNorm hp (⌊s⌋₊ + 1) s q f < ⊤

/-- **The order does not matter**: for `0 < s < r`, `f ∈ B^s_{p,q}` iff its Besov quasi-norm of
order `r` is finite (`Rd.BesovDomain.modNormOn_order_le` piece by piece). -/
theorem memBesov_iff_besovNorm_lt_top {r : ℕ} {s : ℝ} (hs : 0 < s) (hsr : s < r) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p μ) :
    A.MemBesov hp s q f ↔ A.besovNorm hp r s q f < ⊤ := by
  set Ω := range I
  set hΩ := Rd.BesovDomain.measurableSet Ω
  have hs1 : s < ((⌊s⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one s
  -- the comparison of two orders, piece by piece
  have hcmp : ∀ {r₁ r₂ : ℕ}, s < r₁ → s < r₂ → A.besovNorm hp r₁ s q f < ⊤ →
      A.besovNorm hp r₂ s q f < ⊤ := fun {r₁ r₂} h1 h2 hfin => by
    refine ENNReal.sum_lt_top.2 fun i _ => ?_
    obtain ⟨C, hC, hle⟩ := Rd.BesovDomain.modNormOn_order_le (Ω := Ω) hp hs h1 h2 hq
    have hi : Rd.modNormOn hΩ r₁ s q (A.pieceLp μ hp i f) < ⊤ :=
      (A.modNormOn_pieceLp_le_besovNorm hp r₁ s q f i).trans_lt hfin
    exact (hle _ hi).trans_lt (ENNReal.mul_lt_top hC.lt_top hi)
  exact ⟨hcmp hs1 hsr, hcmp hsr hs1⟩

/-- **The pieces of `f ∈ B^s_{p,q}` have finite intrinsic quasi-norms** of every order `r > s` on
`range I`. -/
theorem MemBesov.modNormOn_pieceLp_lt_top {r : ℕ} {s : ℝ} (hs : 0 < s) (hsr : s < r) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {f : Lp ℂ p μ} (hf : A.MemBesov hp s q f) (i : Fin A.n) :
    Rd.modNormOn (Rd.BesovDomain.measurableSet (range I)) r s q (A.pieceLp μ hp i f) < ⊤ :=
  (A.modNormOn_pieceLp_le_besovNorm hp r s q f i).trans_lt
    ((A.memBesov_iff_besovNorm_lt_top hp hs hsr hq f).1 hf)

/-- **`B^s_{p,q}` of an atlas by the pieces**: for `0 < s < r` and `1 ≤ q ≤ ∞`, `f ∈ B^s_{p,q}`
for the atlas `A` iff every piece `P_i f` has a finite intrinsic quasi-norm of order `r` on
`range I` (`Manifold.BesovAtlas.memBesov_iff_besovNorm_lt_top`, Mathlib's `ENNReal.sum_lt_top`). -/
theorem memBesov_iff_forall_modNormOn_lt_top {r : ℕ} {s : ℝ} (hs : 0 < s) (hsr : s < r)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p μ) :
    A.MemBesov hp s q f ↔ ∀ i,
      Rd.modNormOn (Rd.BesovDomain.measurableSet (range I)) r s q (A.pieceLp μ hp i f) < ⊤ := by
  rw [A.memBesov_iff_besovNorm_lt_top hp hs hsr hq, besovNorm, ENNReal.sum_lt_top]
  simp only [Finset.mem_univ, forall_const]

/-- **The Besov space does not depend on the atlas**: `f ∈ B^s_{p,q}` for `A` iff for `A'`. -/
theorem memBesov_iff_memBesov [IsManifold I ∞ M] (A' : BesovAtlas I M) {s : ℝ} (hs : 0 < s)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p μ) :
    A.MemBesov hp s q f ↔ A'.MemBesov hp s q f := by
  have hr : 1 ≤ ⌊s⌋₊ + 1 := Nat.le_add_left 1 _
  have hs1 : s < ((⌊s⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one s
  obtain ⟨C, hC, hle⟩ := A.besovNorm_le_besovNorm (μ := μ) hp A' hr hs hs1 hq
  obtain ⟨C', hC', hle'⟩ := A'.besovNorm_le_besovNorm (μ := μ) hp A hr hs hs1 hq
  exact ⟨fun h => (hle' f).trans_lt (ENNReal.mul_lt_top hC'.lt_top h),
    fun h => (hle f).trans_lt (ENNReal.mul_lt_top hC.lt_top h)⟩

/-- `B^s_{p,q}` of an atlas is closed under addition. -/
theorem MemBesov.add {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q) {f g : Lp ℂ p μ} (hf : A.MemBesov hp s q f)
    (hg : A.MemBesov hp s q g) : A.MemBesov hp s q (f + g) :=
  (A.besovNorm_add_le hp _ s hq f g).trans_lt (ENNReal.add_lt_top.2 ⟨hf, hg⟩)

/-- `B^s_{p,q}` of an atlas is closed under scalar multiplication. -/
theorem MemBesov.const_smul {s : ℝ} {q : ℝ≥0∞} (c : ℂ) {f : Lp ℂ p μ}
    (hf : A.MemBesov hp s q f) : A.MemBesov hp s q (c • f) := by
  rw [MemBesov, besovNorm_const_smul]
  exact ENNReal.mul_lt_top eNorm_lt_top hf

/-- `0 ∈ B^s_{p,q}`. -/
theorem MemBesov.zero (s : ℝ) (q : ℝ≥0∞) : A.MemBesov hp s q (0 : Lp ℂ p μ) := by
  have h := A.besovNorm_const_smul hp (⌊s⌋₊ + 1) s q 0 (0 : Lp ℂ p μ)
  rw [zero_smul, eNorm_zero, zero_mul] at h
  rw [MemBesov, h]
  exact ENNReal.zero_lt_top

/-- `B^s_{p,q}` of an atlas is closed under finite sums. -/
theorem MemBesov.finsetSum {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q) {ι : Type*} (t : Finset ι)
    {f : ι → Lp ℂ p μ} (hf : ∀ i ∈ t, A.MemBesov hp s q (f i)) :
    A.MemBesov hp s q (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact MemBesov.zero hp A s q
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact MemBesov.add hp A hq (hf i (Finset.mem_insert_self i t))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-! ### Functions from a chart -/

omit hB in
variable (μ) in
/-- The **lift from the `k`-th chart** of `F ∈ L_p(E)` to `L_p(μ)`: `θ_k · F ∘ κ_k`
(`Manifold.chartLift`). -/
noncomputable def chartLiftLp (k : Fin A.n) (F : Lp ℂ p (volume : Measure E)) : Lp ℂ p μ :=
  (memLp_chartLift (I := I) μ (A.chart_mem k) (A.contMDiff_theta k).continuous
    (A.tsupport_theta_subset k) (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
    (Lp.stronglyMeasurable F) (Lp.memLp F)).toLp _

omit hB in
/-- The lift from the `k`-th chart in `L_p(μ)` is `θ_k · F ∘ κ_k` almost everywhere. -/
theorem chartLiftLp_ae (k : Fin A.n) (F : Lp ℂ p (volume : Measure E)) :
    A.chartLiftLp μ hp k F =ᵐ[μ] chartLift I (A.chart k) (A.theta k) F :=
  MemLp.coeFn_toLp _

omit hB in
/-- The lifts from a chart are additive. -/
theorem chartLiftLp_add (k : Fin A.n) (F G : Lp ℂ p (volume : Measure E)) :
    A.chartLiftLp μ hp k (F + G) = A.chartLiftLp μ hp k F + A.chartLiftLp μ hp k G := by
  refine Lp.ext ?_
  filter_upwards [A.chartLiftLp_ae hp k (F + G), A.chartLiftLp_ae hp k F,
    A.chartLiftLp_ae hp k G, Lp.coeFn_add (A.chartLiftLp μ hp k F) (A.chartLiftLp μ hp k G),
    chartLift_ae_eq (I := I) (μ := μ) (A.chart_mem k) (A.tsupport_theta_subset k)
      (Lp.coeFn_add F G)]
    with x h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h2, h3, h5, chartLift_add, Pi.add_apply]

omit hB in
/-- The lifts from a chart are homogeneous. -/
theorem chartLiftLp_smul (k : Fin A.n) (c : ℂ) (F : Lp ℂ p (volume : Measure E)) :
    A.chartLiftLp μ hp k (c • F) = c • A.chartLiftLp μ hp k F := by
  refine Lp.ext ?_
  filter_upwards [A.chartLiftLp_ae hp k (c • F), A.chartLiftLp_ae hp k F,
    Lp.coeFn_smul c (A.chartLiftLp μ hp k F),
    chartLift_ae_eq (I := I) (μ := μ) (A.chart_mem k) (A.tsupport_theta_subset k)
      (Lp.coeFn_smul c F)]
    with x h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, h2, h4, chartLift_smul, Pi.smul_apply]

/-- **The pieces of a lift from a chart in `L_p`**: `piece_i (θ_k · F ∘ κ_k) = T_{ik} F`. -/
theorem pieceLp_chartLiftLp [IsManifold I ∞ M] (i k : Fin A.n)
    (F : Lp ℂ p (volume : Measure E)) :
    A.pieceLp μ hp i (A.chartLiftLp μ hp k F) = (A.transition A i k).applyLp hB.convex
      hB.interior_nonempty (Rd.BesovDomain.measurableSet (range I)) hp F := by
  refine Lp.ext ?_
  have h := A.piece_ae_eq i (Lp.stronglyMeasurable _) (stronglyMeasurable_chartLift (A.chart k)
    (A.contMDiff_theta k).continuous (Lp.stronglyMeasurable F))
    (A.chartLiftLp_ae (μ := μ) hp k F)
  filter_upwards [A.pieceLp_ae μ hp i (A.chartLiftLp μ hp k F), h,
    (A.transition A i k).applyLp_ae hB.convex hB.interior_nonempty
      (Rd.BesovDomain.measurableSet (range I)) hp F] with y h1 h2 h3
  rw [h1, h2, h3, piece_chartLift]

/-- **Lifts from a chart are in `B^σ_{p,q}(M)`**: for `F ∈ L_p(E)` with
`‖F‖_p + ‖(2^(kσ) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞`, `0 < σ < r`, the lift `θ_k · F ∘ κ_k` lies in
`B^σ_{p,q}(M)`: its pieces are `T_{ik} F`, bounded on `range I`
(`Rd.CutoffDiffeo.modNormOn_applyLp_le`). -/
theorem memBesov_chartLiftLp [IsManifold I ∞ M] (k : Fin A.n) {r : ℕ} (hr : 1 ≤ r) {σ : ℝ}
    (hσ : 0 < σ) (hσr : σ < r) {q : ℝ≥0∞} (hq : 1 ≤ q) {F : Lp ℂ p (volume : Measure E)}
    (hF : ‖F‖ₑ + lqNorm q (fun j => dyadicWeight σ j * Rd.lpModulus p r F j) < ⊤) :
    A.MemBesov hp σ q (A.chartLiftLp μ hp k F) := by
  rw [A.memBesov_iff_besovNorm_lt_top hp hσ hσr hq]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  obtain ⟨C, hC, hle⟩ := (A.transition A i k).modNormOn_applyLp_le hB.convex
    hB.interior_nonempty (Rd.BesovDomain.measurableSet (range I)) hp hr hσ hσr hq
  rw [A.pieceLp_chartLiftLp hp i k F]
  exact (hle F).trans_lt (ENNReal.mul_lt_top hC.lt_top hF)

end BesovAtlas

variable (I μ) [T2Space M] [IsManifold I ∞ M]

/-- The **Besov space** `B^s_{p,q}(M)` of a compact manifold with a smooth measure: `f ∈ L_p(μ)`
with a finite Besov quasi-norm for a chosen Besov atlas. For `s > 0` and `1 ≤ q ≤ ∞` every Besov
atlas gives the same space (`Manifold.memBesov_iff`). -/
def MemBesov (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p μ) : Prop :=
  (Classical.choice (BesovAtlas.nonempty I M)).MemBesov hp s q f

/-- **Every Besov atlas describes `B^s_{p,q}(M)`**: for `s > 0` and `1 ≤ q ≤ ∞`. -/
theorem memBesov_iff (A : BesovAtlas I M) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ p μ) : MemBesov I μ hp s q f ↔ A.MemBesov hp s q f :=
  BesovAtlas.memBesov_iff_memBesov hp _ A hs hq f

end Manifold
