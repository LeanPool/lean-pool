/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.EuclideanConvolutionIdentities

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The periodic lift

A function `g` on the torus `𝕋^d` lifts to the `ℤ^d`-periodic function `g ∘ π` on `ℝ^d`, with the
quotient map `π` (`Torus.proj`). This file compares integrals of lifts with integrals on the torus.

* The **period boxes** `P_a = {x : a_i < x_i ≤ a_i + 1}` (`Torus.periodBox`) are fundamental
  domains: `∫_{P_a} g(π x) dx = ∫_{𝕋^d} g` (`Torus.lintegral_periodBox`, from Mathlib's
  `UnitAddTorus.lintegral_preimage`), so `π` maps the Lebesgue measure on `P_a` to the Haar
  measure (`Torus.measurePreserving_proj_periodBox`), `|P_a| = 1` and
  `‖F ∘ π‖_{L_p(P_a)} = ‖F‖_{L_p(𝕋^d)}` (`Torus.volume_periodBox`,
  `Torus.eLpNorm_comp_proj_periodBox`). Hence a bound `F(π x) ≤ A(x) + G(π x)` for almost every
  `x ∈ P_0` gives `‖F‖_{L_p(𝕋^d)} ≤ ‖A‖_{L_p(ℝ^d)} + ‖G‖_{L_p(𝕋^d)}`
  (`Torus.eLpNorm_le_of_comp_proj_le`). The boxes `P_m`, `m ∈ ℤ^d`, partition `ℝ^d`, hence `π`
  maps null sets back to null sets (`Torus.quasiMeasurePreserving_proj`) and almost everywhere
  statements on the torus lift (`Torus.ae_comp_proj`).
* Convolutions and differences on the torus are those of the lift:
  `(Φ ⋆ h)(π x) = (Φ ⋆ (h ∘ π))(x)` (`Torus.econv_proj`) and
  `Δ^L_{π h} f(π x) = Δ^L_h (f ∘ π)(x)` (`Torus.higherDiff_comp_proj`).
* **Counting boxes**: a ball of radius `r` meets at most `(2r + 2)^d` boxes, so
  `∫_{B(x,r)} g(π y) dy ≤ (2r + 2)^d ∫_{𝕋^d} g` (`Torus.setLIntegral_ball_comp_proj_le`), lifts
  of integrable functions are locally integrable (`Torus.locallyIntegrable_comp_proj`, for `L_p`
  classes `Torus.locallyIntegrable_comp_proj_Lp`), balls of
  radius `r ≤ 1` around points of `P_0` lie in the box `(-1, 2]^d` of side `3`
  (`Torus.ball_subset_tripleBox`), `‖y‖ ≥ 1` whenever `x ∈ P_0` and `x - y ∉ (-1, 2]^d`
  (`Torus.one_le_norm_of_sub_notMem_tripleBox`), and `∫_{(-1,2]^d} g(π y) dy = 3^d ∫_{𝕋^d} g`
  (`Torus.setLIntegral_tripleBox`); hence
  `‖1_{(-1,2]^d} (F ∘ π)‖_{L_p(ℝ^d)} = 3^{d/p} ‖F‖_{L_p(𝕋^d)}`
  (`Torus.eLpNorm_indicator_tripleBox_comp_proj`, `Torus.eLpNorm_indicator_tripleBox`,
  `Torus.memLp_indicator_tripleBox_comp_proj`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus Set Filter Metric
open scoped ENNReal TorusHaar

namespace Torus

variable {d : Type*} [Fintype d]

/-! ### Period boxes -/

/-- The **period box** `P_a = {x ∈ ℝ^d : a_i < x_i ≤ a_i + 1 for every i}`, a fundamental domain
of the lattice `ℤ^d`. -/
def periodBox (a : d → ℝ) : Set (EuclideanSpace ℝ d) :=
  {x | ∀ i, x i ∈ Ioc (a i) (a i + 1)}

/-- The box `(-1, 2]^d` of side `3`, the union of the `3^d` period boxes around `(0, 1]^d`. -/
def tripleBox : Set (EuclideanSpace ℝ d) :=
  {y | ∀ i, y i ∈ Ioc (-1 : ℝ) 2}

omit [Fintype d] in
/-- Period boxes are measurable. -/
theorem measurableSet_periodBox [Finite d] (a : d → ℝ) : MeasurableSet (periodBox a) := by
  let := Fintype.ofFinite d
  have h : periodBox a = ⋂ i, (fun x : EuclideanSpace ℝ d => x i) ⁻¹' Ioc (a i) (a i + 1) := by
    ext x
    simp [periodBox]
  rw [h]
  exact MeasurableSet.iInter fun i => (PiLp.continuous_apply 2 _ i).measurable measurableSet_Ioc

omit [Fintype d] in
/-- The box `(-1, 2]^d` is measurable. -/
theorem measurableSet_tripleBox [Finite d] : MeasurableSet (tripleBox (d := d)) := by
  let := Fintype.ofFinite d
  have h : tripleBox (d := d) =
      ⋂ i, (fun x : EuclideanSpace ℝ d => x i) ⁻¹' Ioc (-1 : ℝ) 2 := by
    ext x
    simp [tripleBox]
  rw [h]
  exact MeasurableSet.iInter fun i => (PiLp.continuous_apply 2 _ i).measurable measurableSet_Ioc

omit [Fintype d] in
/-- `x` lies in the period box of an integer vector `m` iff `⌈x_i⌉ = m_i + 1` for every `i`. -/
theorem mem_periodBox_intCast_iff (m : d → ℤ) (x : EuclideanSpace ℝ d) :
    x ∈ periodBox (fun i => (m i : ℝ)) ↔ ∀ i, ⌈x i⌉ = m i + 1 := by
  refine forall_congr' fun i => ?_
  rw [Int.ceil_eq_iff, mem_Ioc]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

omit [Fintype d] in
/-- Every point `x` lies in the period box of the integer vector `(⌈x_i⌉ - 1)_i`. -/
theorem mem_periodBox_ceil (x : EuclideanSpace ℝ d) :
    x ∈ periodBox (fun i => ((⌈x i⌉ - 1 : ℤ) : ℝ)) :=
  (mem_periodBox_intCast_iff _ x).2 fun i => by ring

omit [Fintype d] in
/-- Period boxes of distinct integer vectors are disjoint. -/
theorem pairwise_disjoint_periodBox :
    Pairwise fun m m' : d → ℤ =>
      Disjoint (periodBox (fun i => (m i : ℝ))) (periodBox (fun i => (m' i : ℝ))) := by
  intro m m' hmm'
  refine Set.disjoint_left.2 fun x hx hx' => hmm' (funext fun i => ?_)
  have h := ((mem_periodBox_intCast_iff m x).1 hx i).symm.trans
    ((mem_periodBox_intCast_iff m' x).1 hx' i)
  omega

/-- **The period boxes are fundamental domains**: `∫_{P_a} g(π x) dx = ∫_{𝕋^d} g` for every
`g : 𝕋^d → [0, ∞]` (Mathlib's `UnitAddTorus.lintegral_preimage`, carried from `d → ℝ` to
`ℝ^d` by the volume-preserving identification). -/
theorem lintegral_periodBox (a : d → ℝ) (g : UnitAddTorus d → ℝ≥0∞) :
    ∫⁻ x in periodBox a, g (proj x) = ∫⁻ t, g t := by
  rw [UnitAddTorus.lintegral_preimage g a]
  exact MeasurePreserving.setLIntegral_comp_preimage_emb
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp d)
    (MeasurableEquiv.toLp 2 (d → ℝ)).symm.measurableEmbedding (fun x => g fun i => x i)
    {x : d → ℝ | ∀ i, x i ∈ Ioc (a i) (a i + 1)}

/-- **The quotient map preserves measure on a period box**: `π` maps the Lebesgue measure on
`P_a` to the Haar measure of the torus. -/
theorem measurePreserving_proj_periodBox (a : d → ℝ) :
    MeasurePreserving proj (volume.restrict (periodBox a)) volume := by
  refine ⟨measurable_proj, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply measurable_proj hs, ← lintegral_indicator_one (measurable_proj hs),
    ← lintegral_indicator_one hs, ← lintegral_periodBox a]
  rfl

/-- A period box has volume `1`. -/
theorem volume_periodBox (a : d → ℝ) : volume (periodBox a) = 1 := by
  have h := (measurePreserving_proj_periodBox a).measure_preimage
    (MeasurableSet.univ (α := UnitAddTorus d)).nullMeasurableSet
  rwa [preimage_univ, Measure.restrict_apply_univ, measure_univ] at h

/-- `L_p` norms of lifts on a period box are `L_p` norms on the torus:
`‖F ∘ π‖_{L_p(P_a)} = ‖F‖_{L_p(𝕋^d)}`. -/
theorem eLpNorm_comp_proj_periodBox {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    (a : d → ℝ) {F : UnitAddTorus d → ε} (hF : AEStronglyMeasurable F volume) (p : ℝ≥0∞) :
    eLpNorm (F ∘ proj) p (volume.restrict (periodBox a)) = eLpNorm F p volume :=
  eLpNorm_comp_measurePreserving hF (measurePreserving_proj_periodBox a)

/-- **From the period box to the torus**: for `1 ≤ p`, almost everywhere measurable
`F, G : 𝕋^d → [0, ∞]` and `A : ℝ^d → [0, ∞]` with `F(π x) ≤ A(x) + G(π x)` for almost every
`x ∈ P_0`, `‖F‖_{L_p(𝕋^d)} ≤ ‖A‖_{L_p(ℝ^d)} + ‖G‖_{L_p(𝕋^d)}`, since `L_p` norms on the torus are
`L_p` norms of lifts on `P_0` (`Torus.eLpNorm_comp_proj_periodBox`). -/
theorem eLpNorm_le_of_comp_proj_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) {F G : UnitAddTorus d → ℝ≥0∞}
    (hF : AEMeasurable F volume) (hG : AEMeasurable G volume) {A : EuclideanSpace ℝ d → ℝ≥0∞}
    (h : ∀ᵐ x ∂volume.restrict (periodBox 0), F (proj x) ≤ A x + G (proj x)) :
    eLpNorm F p volume ≤ eLpNorm A p volume + eLpNorm G p volume :=
  calc eLpNorm F p volume = eLpNorm (F ∘ proj) p (volume.restrict (periodBox 0)) :=
        (eLpNorm_comp_proj_periodBox 0 hF.aestronglyMeasurable p).symm
    _ ≤ eLpNorm (A + G ∘ proj) p (volume.restrict (periodBox 0)) :=
        eLpNorm_mono_eNorm_ae (hF.aestronglyMeasurable.comp_measurePreserving
          (measurePreserving_proj_periodBox 0)) (h.mono fun x hx => by
            simpa only [eNorm_eq_self, Pi.add_apply, Function.comp_apply] using hx)
    _ ≤ eLpNorm A p (volume.restrict (periodBox 0)) +
          eLpNorm (G ∘ proj) p (volume.restrict (periodBox 0)) := eLpNorm_add_le hp1
    _ ≤ eLpNorm A p volume + eLpNorm G p volume :=
        add_le_add (eLpNorm_mono_measure _ Measure.restrict_le_self)
          (eLpNorm_comp_proj_periodBox 0 hG.aestronglyMeasurable p).le

/-! ### Null sets and almost everywhere statements -/

/-- **The quotient map pulls null sets back to null sets**: the period boxes `P_m`, `m ∈ ℤ^d`,
cover `ℝ^d`, and on each of them `π` preserves measure. -/
theorem quasiMeasurePreserving_proj :
    QuasiMeasurePreserving (proj : EuclideanSpace ℝ d → UnitAddTorus d) volume volume := by
  refine ⟨measurable_proj.aemeasurable, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply measurable_proj hs]
  have hcover : proj ⁻¹' s ⊆
      ⋃ m : d → ℤ, proj ⁻¹' s ∩ periodBox (fun i => (m i : ℝ)) := fun x hx =>
    mem_iUnion.2 ⟨fun i => ⌈x i⌉ - 1, hx, mem_periodBox_ceil x⟩
  refine measure_mono_null hcover (measure_iUnion_null fun m => ?_)
  rw [← Measure.restrict_apply (measurable_proj hs),
    (measurePreserving_proj_periodBox _).measure_preimage hs.nullMeasurableSet, h0]

/-- **Almost everywhere statements lift**: if `P(t)` holds for almost every `t ∈ 𝕋^d`, then
`P(π x)` holds for almost every `x ∈ ℝ^d`. -/
theorem ae_comp_proj {P : UnitAddTorus d → Prop} (h : ∀ᵐ t ∂volume, P t) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ d)), P (proj x) :=
  quasiMeasurePreserving_proj.ae h

/-! ### Convolutions and differences of lifts -/

/-- **Convolution commutes with the lift**: `(Φ ⋆ h)(π x) = (Φ ⋆ (h ∘ π))(x)`, a convolution on
`ℝ^d` on the right. -/
theorem econv_proj (Φ : EuclideanSpace ℝ d → ℂ) (h : UnitAddTorus d → ℂ)
    (x : EuclideanSpace ℝ d) : econv Φ h (proj x) = Rd.conv Φ (h ∘ proj) volume x := by
  rw [Rd.conv_apply]
  simp only [econv, Function.comp_apply, map_sub]

omit [Fintype d] in
/-- **Differences commute with the lift**: `Δ^L_{π h} f(π x) = Δ^L_h (f ∘ π)(x)`. -/
theorem higherDiff_comp_proj (f : UnitAddTorus d → ℂ) (L : ℕ) (h x : EuclideanSpace ℝ d) :
    (fwdDiff (proj h))^[L] f (proj x) = (fwdDiff h)^[L] (f ∘ proj) x := by
  simp only [fwdDiff_iter_eq_sum_shift, Function.comp_apply, map_add, map_nsmul]

/-! ### Counting boxes -/

/-- A ball `B(x, r)` lies in the union of the period boxes `P_m` with
`⌈x_i - r⌉ - 1 ≤ m_i ≤ ⌈x_i + r⌉ - 1`. -/
theorem ball_subset_iUnion_periodBox (x : EuclideanSpace ℝ d) (r : ℝ) :
    ball x r ⊆ ⋃ (m : d → ℤ) (_ : ∀ i, m i ∈ Finset.Icc (⌈x i - r⌉ - 1) (⌈x i + r⌉ - 1)),
      periodBox (fun i => (m i : ℝ)) := by
  intro y hy
  refine mem_iUnion₂.2 ⟨fun i => ⌈y i⌉ - 1, fun i => ?_, mem_periodBox_ceil y⟩
  have hi : |y i - x i| < r := by
    simpa [Real.dist_eq] using (PiLp.dist_apply_le y x i).trans_lt (mem_ball.1 hy)
  rw [abs_lt] at hi
  rw [Finset.mem_Icc]
  exact ⟨by linarith [Int.ceil_mono (show x i - r ≤ y i by linarith)],
    by linarith [Int.ceil_mono (show y i ≤ x i + r by linarith)]⟩

/-- For `r ≥ 0`, the interval `[⌈a - r⌉ - 1, ⌈a + r⌉ - 1]` of integers has at most `2r + 2`
elements. -/
theorem card_Icc_ceil_le (a r : ℝ) (hr : 0 ≤ r) :
    ((Finset.Icc (⌈a - r⌉ - 1) (⌈a + r⌉ - 1)).card : ℝ) ≤ 2 * r + 2 := by
  rw [Int.card_Icc]
  have h1 : (⌈a + r⌉ : ℝ) < a + r + 1 := Int.ceil_lt_add_one _
  have h2 : a - r ≤ (⌈a - r⌉ : ℝ) := Int.le_ceil _
  have h : (((⌈a + r⌉ - 1 + 1 - (⌈a - r⌉ - 1)).toNat : ℤ) : ℝ) ≤ 2 * r + 2 := by
    rw [Int.toNat_eq_max]
    push_cast
    exact max_le (by linarith) (by linarith)
  exact_mod_cast h

/-- **Counting boxes**: `∫_{B(x,r)} g(π y) dy ≤ (2r + 2)^d ∫_{𝕋^d} g` for every
`g : 𝕋^d → [0, ∞]` and `r ∈ ℝ`: the ball meets at most `(2r + 2)^d` period boxes, and each
contributes `∫_{𝕋^d} g`; for `r ≤ 0` the ball is empty. -/
theorem setLIntegral_ball_comp_proj_le (g : UnitAddTorus d → ℝ≥0∞) (x : EuclideanSpace ℝ d)
    (r : ℝ) :
    ∫⁻ y in ball x r, g (proj y) ≤
      ENNReal.ofReal (2 * r + 2) ^ Fintype.card d * ∫⁻ t, g t := by
  classical
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr, Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le
  set M : Finset (d → ℤ) := Fintype.piFinset fun i => Finset.Icc (⌈x i - r⌉ - 1) (⌈x i + r⌉ - 1)
  have hsub : ball x r ⊆ ⋃ m ∈ M, periodBox (fun i => (m i : ℝ)) := by
    refine (ball_subset_iUnion_periodBox x r).trans fun y hy => ?_
    obtain ⟨m, hm, hy⟩ := mem_iUnion₂.1 hy
    exact mem_iUnion₂.2 ⟨m, Fintype.mem_piFinset.2 hm, hy⟩
  have hcard : (M.card : ℝ≥0∞) ≤ ENNReal.ofReal (2 * r + 2) ^ Fintype.card d := by
    rw [Fintype.card_piFinset, Nat.cast_prod, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_le_prod fun i _ => ?_
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (card_Icc_ceil_le (x i) r hr.le)
  calc ∫⁻ y in ball x r, g (proj y)
      ≤ ∫⁻ y in ⋃ m ∈ M, periodBox (fun i => (m i : ℝ)), g (proj y) := lintegral_mono_set hsub
    _ = ∑ m ∈ M, ∫⁻ y in periodBox (fun i => (m i : ℝ)), g (proj y) :=
        lintegral_biUnion_finset (fun m _ m' _ h => pairwise_disjoint_periodBox h)
          (fun m _ => measurableSet_periodBox _) _
    _ = M.card * ∫⁻ t, g t := by
        simp only [lintegral_periodBox, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by gcongr

/-- **Lifts of integrable functions are locally integrable**: by counting boxes every ball has
finite integral. -/
theorem locallyIntegrable_comp_proj {h : UnitAddTorus d → ℂ} (hh : Integrable h volume) :
    LocallyIntegrable (h ∘ proj) volume := fun x => by
  refine ⟨ball x 1, ball_mem_nhds x one_pos, ?_, ?_⟩
  · exact (hh.aestronglyMeasurable.comp_quasiMeasurePreserving
      quasiMeasurePreserving_proj).restrict
  · refine (setLIntegral_ball_comp_proj_le (fun t => ‖h t‖ₑ) x 1).trans_lt ?_
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hh.2

section Lp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The lift `h ∘ π` of `h ∈ L_p(𝕋^d)`, `1 ≤ p`, is locally integrable on `ℝ^d`. -/
theorem locallyIntegrable_comp_proj_Lp (h : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    LocallyIntegrable (⇑h ∘ proj) volume :=
  locallyIntegrable_comp_proj ((Lp.memLp h).integrable Fact.out)

end Lp

omit [Fintype d] in
/-- The box `(-1, 2]^d` is the union of the period boxes `P_m` with `m ∈ {-1, 0, 1}^d`. -/
theorem tripleBox_eq_biUnion :
    tripleBox (d := d) = ⋃ (m : d → ℤ) (_ : ∀ i, -1 ≤ m i ∧ m i ≤ 1),
      periodBox (fun i => (m i : ℝ)) := by
  ext y
  simp only [mem_iUnion, exists_prop]
  constructor
  · intro hy
    refine ⟨fun i => ⌈y i⌉ - 1, fun i => ?_, mem_periodBox_ceil y⟩
    obtain ⟨h1, h2⟩ := hy i
    have h3 : (0 : ℤ) ≤ ⌈y i⌉ := Int.ceil_nonneg_of_neg_one_lt h1
    have h4 : ⌈y i⌉ ≤ 2 := Int.ceil_le.2 (by exact_mod_cast h2)
    exact ⟨by simp only; omega, by simp only; omega⟩
  · rintro ⟨m, hm, hy⟩ i
    obtain ⟨h1, h2⟩ := hy i
    have hm1 : (-1 : ℝ) ≤ m i := by exact_mod_cast (hm i).1
    have hm2 : (m i : ℝ) ≤ 1 := by exact_mod_cast (hm i).2
    exact ⟨by linarith, by linarith⟩

/-- At a point of `P_0 = (0, 1]^d`, every ball of radius `r ≤ 1` lies in the box `(-1, 2]^d`. -/
theorem ball_subset_tripleBox {x : EuclideanSpace ℝ d} (hx : x ∈ periodBox 0) {r : ℝ}
    (hr : r ≤ 1) : ball x r ⊆ tripleBox := by
  intro y hy i
  have hi : |y i - x i| < 1 := by
    simpa [Real.dist_eq] using ((PiLp.dist_apply_le y x i).trans_lt (mem_ball.1 hy)).trans_le hr
  rw [abs_lt] at hi
  obtain ⟨h1, h2⟩ := hx i
  simp only [Pi.zero_apply, zero_add] at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- **Points outside the box are far**: if `x ∈ P_0 = (0, 1]^d` and `x - y ∉ (-1, 2]^d`, then
`‖y‖ ≥ 1`, since some coordinate has `y_i ≥ x_i + 1 > 1` or `y_i < x_i - 2 ≤ -1`. -/
theorem one_le_norm_of_sub_notMem_tripleBox {x y : EuclideanSpace ℝ d} (hx : x ∈ periodBox 0)
    (h : x - y ∉ tripleBox) : 1 ≤ ‖y‖ := by
  simp only [tripleBox, mem_ofPred_eq, not_forall] at h
  obtain ⟨i, hi⟩ := h
  obtain ⟨h1, h2⟩ := hx i
  simp only [Pi.zero_apply, zero_add] at h1 h2
  rw [PiLp.sub_apply, mem_Ioc, not_and_or, not_lt, not_le] at hi
  have hyi : 1 ≤ |y i| := by
    rcases hi with hi | hi
    · rw [abs_of_pos (by linarith)]
      linarith
    · rw [abs_of_neg (by linarith)]
      linarith
  exact hyi.trans (by rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le y i)

/-- **The box of side `3`**: `∫_{(-1,2]^d} g(π y) dy = 3^d ∫_{𝕋^d} g`, since `(-1, 2]^d` is the
disjoint union of `3^d` period boxes. -/
theorem setLIntegral_tripleBox (g : UnitAddTorus d → ℝ≥0∞) :
    ∫⁻ y in tripleBox, g (proj y) = 3 ^ Fintype.card d * ∫⁻ t, g t := by
  classical
  have h : tripleBox (d := d) = ⋃ m ∈ Fintype.piFinset fun _ : d => Finset.Icc (-1 : ℤ) 1,
      periodBox (fun i => (m i : ℝ)) := by
    simp only [tripleBox_eq_biUnion, Fintype.mem_piFinset, Finset.mem_Icc]
  rw [h, lintegral_biUnion_finset
    (fun m _ m' _ h => pairwise_disjoint_periodBox h) (fun m _ => measurableSet_periodBox _)]
  simp only [lintegral_periodBox, Finset.sum_const, nsmul_eq_mul, Fintype.card_piFinset,
    Int.card_Icc, Finset.prod_const, Finset.card_univ]
  norm_num

/-! ### `L_p` norms on the box `(-1, 2]^d` -/

/-- `L_p` norms on the box `(-1, 2]^d`:
`‖1_{(-1,2]^d} (F ∘ π)‖_{L_p(ℝ^d)} = 3^{d/p} ‖F‖_{L_p(𝕋^d)}` for `0 < p < ∞` and every almost
everywhere strongly measurable `F` on `𝕋^d` with values in a space with an extended norm, such as
`ℂ` or `[0, ∞]` (`Torus.setLIntegral_tripleBox` for `|F|^p`). -/
theorem eLpNorm_indicator_tripleBox_comp_proj {ε : Type*} [TopologicalSpace ε]
    [ESeminormedAddMonoid ε] {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {F : UnitAddTorus d → ε}
    (hF : AEStronglyMeasurable F volume) :
    eLpNorm (tripleBox.indicator (F ∘ proj)) p volume =
      3 ^ ((Fintype.card d : ℝ) / p.toReal) * eLpNorm F p volume := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_tripleBox.nullMeasurableSet,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp
      (hF.comp_quasiMeasurePreserving quasiMeasurePreserving_proj).restrict,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hF, Function.comp_def,
    setLIntegral_tripleBox (fun t => ‖F t‖ₑ ^ p.toReal),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    mul_one_div]

/-- `L_p` norms on the box `(-1, 2]^d` for functions with values in `[0, ∞]`:
`‖1_{(-1,2]^d} (G ∘ π)‖_{L_p(ℝ^d)} = 3^{d/p} ‖G‖_{L_p(𝕋^d)}` for `0 < p < ∞` and almost everywhere
measurable `G : 𝕋^d → [0, ∞]` (`Torus.eLpNorm_indicator_tripleBox_comp_proj`). -/
theorem eLpNorm_indicator_tripleBox {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    {G : UnitAddTorus d → ℝ≥0∞} (hG : AEMeasurable G volume) :
    eLpNorm (tripleBox.indicator fun y => G (proj y)) p volume =
      3 ^ ((Fintype.card d : ℝ) / p.toReal) * eLpNorm G p volume :=
  eLpNorm_indicator_tripleBox_comp_proj hp0 hp hG.aestronglyMeasurable

/-- The part `1_{(-1,2]^d} (f ∘ π)` of the lift of `f ∈ L_p(𝕋^d)`, `0 < p < ∞`, lies in
`L_p(ℝ^d)`. -/
theorem memLp_indicator_tripleBox_comp_proj {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    {f : UnitAddTorus d → ℂ} (hf : MemLp f p volume) :
    MemLp (tripleBox.indicator (f ∘ proj)) p volume := by
  rw [memLp_iff, eLpNorm_indicator_tripleBox_comp_proj hp0 hp hf.aestronglyMeasurable]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) (by norm_num)) hf

end Torus
