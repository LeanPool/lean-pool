/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalSlotLinear
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalMeasureInvariance
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ManifoldPluripolar

/-!
# Diagonal scaling of global mixed measures

Three consequences of one-slot positive linearity of global mixed measures
(`Pending.GlobalSlotLinear`).

* Positive combinations of raw theta-PSH potentials are raw theta-PSH for the
  combined form: in a chart, the combined smooth potential is the same
  combination of the two smooth potentials, and the corrected germ is a positive
  combination of PSH germs.
* The pole set of a nondegenerate quasi-PSH potential is null for every global
  mixed measure, because it is locally pluripolar.
* For a bounded potential `c` in a semipositive background `θ`, the diagonal
  measure of `(1 - ε) c - K` dominates `(1 - ε)ⁿ` times that of `c`. Since
  `θ = (1 - ε) • θ + ε • θ` and `0` is `θ`-PSH, the scaled potential is
  `(1 - ε) c + ε 0`; linearity in one slot at a time, dropping the `0`-term,
  gives the factor `(1 - ε)` per slot, and constants do not change the measure.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling

open FirstPass FirstPass.GlobalPotentialTransforms FirstPass.PositiveClasses
open GlobalNonPluripolar BoundedGlobalProduct

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Positive combinations of raw theta-PSH potentials.** If `a` is `α`-PSH and `b`
is `β`-PSH, then `s a + r b` is `(s • α + r • β)`-PSH for `s, r > 0`. -/
theorem thetaPlurisubharmonic_add_smul {α β : ClosedRealOneOneForm n M} {a b : M → EReal}
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (ha : ThetaPlurisubharmonic α.val a) (hb : ThetaPlurisubharmonic β.val b) :
    ThetaPlurisubharmonic (s • α + r • β).val
      (fun p => (s : EReal) * a p + (r : EReal) * b p) := by
  intro e z hz
  obtain ⟨Wa, ρa, hzWa, hρa, hpa⟩ := ha e z hz
  obtain ⟨Wb, ρb, hzWb, hρb, hpb⟩ := hb e z hz
  have hWo : IsOpen (Wa ∩ Wb) := hρa.1.inter hρb.1
  have hla := hρa.mono hWo inter_subset_left
  have hlb := hρb.mono hWo inter_subset_right
  refine ⟨Wa ∩ Wb, fun y => s * ρa y + r * ρb y, ⟨hzWa, hzWb⟩, ?_, ?_⟩
  · have hsα : ContDiffOn ℝ ∞ (fun y => s • ρa y) (Wa ∩ Wb) := hla.2.2.1.const_smul s
    have hrβ : ContDiffOn ℝ ∞ (fun y => r • ρb y) (Wa ∩ Wb) := hlb.2.2.1.const_smul r
    refine ⟨hWo, hla.2.1, hsα.add hrβ, ?_⟩
    intro y hy
    change smoothDDC (fun w => s • ρa w + r • ρb w) y = _
    rw [smoothDDC_add hWo hsα hrβ hy, smoothDDC_smul hWo hla.2.2.1 s hy,
      smoothDDC_smul hWo hlb.2.2.1 r hy, hla.2.2.2 hy, hlb.2.2.2 hy,
      ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
      ClosedRealOneOneForm.coeff_smul]
  · have h := ((hpa.mono inter_subset_left).const_mul hs).add
      ((hpb.mono inter_subset_right).const_mul hr)
    have key : (fun y => chartFunction (fun p => (s : EReal) * a p + (r : EReal) * b p) e y +
        ((s * ρa y + r * ρb y : ℝ) : EReal)) =
        (fun y => (s : EReal) * (chartFunction a e y + (ρa y : EReal)) +
          (r : EReal) * (chartFunction b e y + (ρb y : EReal))) :=
      funext fun y => GlobalSlotLinear.ereal_linear_add_coe hs hr _ _ _ _
    rw [key]
    exact h

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [BorelSpace M] in
/-- Equal form tuples and equal potential tuples give equal global mixed measures. -/
theorem globalMixedMeasure_congr {θ θ' : Fin n → ClosedRealOneOneForm n M}
    {u u' : Fin n → M → EReal} (eθ : θ = θ') (eu : u = u')
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (hu' : ∀ i, ThetaPlurisubharmonic (θ' i).val (u' i)) :
    globalMixedMeasure θ u hu = globalMixedMeasure θ' u' hu' := by
  subst eθ eu
  rfl

/-- **Poles of nondegenerate quasi-PSH potentials are globally null.** -/
theorem globalMixedMeasure_pole_null_of_quasiPsh {θ : Fin n → ClosedRealOneOneForm n M}
    {u : Fin n → M → EReal} (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    {v : M → EReal} (hv : IsGlobalQuasiPshPotential (n := n) v) :
    globalMixedMeasure θ u hu {p | v p = ⊥} = 0 :=
  globalMixedMeasure_doesNotChargeManifoldPluripolar hu _
    (quasiPsh_poles_manifoldLocallyPluripolar hv)

/-- **Poles of theta-PSH potentials are globally null.** -/
theorem globalMixedMeasure_pole_null_of_nondegenerate {θ : Fin n → ClosedRealOneOneForm n M}
    {u : Fin n → M → EReal} (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    {η : SmoothRealForm n M 2} {v : M → EReal} (hv : IsThetaPshPotential η v) :
    globalMixedMeasure θ u hu {p | v p = ⊥} = 0 :=
  globalMixedMeasure_pole_null_of_quasiPsh hu ⟨hv.1.quasiPlurisubharmonic, hv.2⟩

/-- **Diagonal scaling in a semipositive background.** For a bounded `θ`-PSH
potential `c` and `0 < ε < 1`, the diagonal measure of `(1 - ε) c - K` dominates
`(1 - ε)ⁿ` times the diagonal measure of `c`. -/
theorem globalMixedMeasure_diagonal_scale {θ : ClosedRealOneOneForm n M}
    (hθ : θ.val.IsSemipositive) {c : M → EReal} (hc : ThetaPlurisubharmonic θ.val c)
    (hcb : IsBoundedPotential c) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (K : ℝ) :
    ∃ hd : ThetaPlurisubharmonic θ.val (fun p => (((1 - ε) * (c p).toReal - K : ℝ) : EReal)),
      ∀ S : Set M, ENNReal.ofReal ((1 - ε) ^ n) *
          globalMixedMeasure (fun _ => θ) (fun _ => c) (fun _ => hc) S ≤
        globalMixedMeasure (fun _ => θ)
          (fun _ => fun p => (((1 - ε) * (c p).toReal - K : ℝ) : EReal)) (fun _ => hd) S := by
  have hs : 0 < 1 - ε := sub_pos.mpr hε1
  have hθeq : (1 - ε) • θ + ε • θ = θ := by rw [← add_smul, sub_add_cancel, one_smul]
  have h0 : ThetaPlurisubharmonic θ.val (fun _ : M => (0 : EReal)) := by
    simpa using thetaPlurisubharmonic_const θ hθ 0
  set d : M → EReal := fun p =>
    ((1 - ε : ℝ) : EReal) * c p + ((ε : ℝ) : EReal) * (fun _ : M => (0 : EReal)) p with hd_def
  have hdθ : ThetaPlurisubharmonic θ.val d := by
    have h := thetaPlurisubharmonic_add_smul hs hε0 hc h0
    rwa [hθeq] at h
  -- The tuples whose first `m` slots carry `d` and the others `c`.
  let x : ℕ → Fin n → M → EReal := fun m i => if (i : ℕ) < m then d else c
  have hx : ∀ m i, ThetaPlurisubharmonic ((fun _ : Fin n => θ) i).val (x m i) := by
    intro m i
    by_cases h : (i : ℕ) < m
    · simpa only [x, h, ite_true] using hdθ
    · simpa only [x, h, ite_false] using hc
  have step : ∀ m, m ≤ n → ∀ S : Set M, ENNReal.ofReal ((1 - ε) ^ m) *
      globalMixedMeasure (fun _ => θ) (fun _ => c) (fun _ => hc) S ≤
      globalMixedMeasure (fun _ => θ) (x m) (hx m) S := by
    intro m
    induction m with
    | zero =>
      intro _ S
      have e : x 0 = fun _ => c := by funext i; simp [x]
      rw [pow_zero, ENNReal.ofReal_one, one_mul,
        globalMixedMeasure_congr rfl e (hx 0) (fun _ => hc)]
    | succ m ih =>
      intro hm S
      have hmn : m < n := hm
      set i₀ : Fin n := ⟨m, hmn⟩ with hi₀
      have e1 : x (m + 1) = Function.update (x m) i₀ d := by
        funext i
        by_cases h : i = i₀
        · rw [h, Function.update_self]; simp [x, i₀]
        · rw [Function.update_of_ne h]
          have him : (i : ℕ) ≠ m := fun h' => h (Fin.ext h')
          simp only [x]
          split_ifs <;> first | rfl | omega
      have e2 : Function.update (x m) i₀ c = x m := by
        funext i
        by_cases h : i = i₀
        · rw [h, Function.update_self]; simp [x, i₀]
        · rw [Function.update_of_ne h]
      have eθ : Function.update (fun _ : Fin n => θ) i₀ θ = fun _ => θ :=
        Function.update_eq_self i₀ _
      have hc' : ∀ i, ThetaPlurisubharmonic ((fun _ : Fin n => θ) i).val
          (Function.update (x m) i₀ d i) := by
        rw [← e1]; exact hx (m + 1)
      have ha' : ∀ i, ThetaPlurisubharmonic (Function.update (fun _ : Fin n => θ) i₀ θ i).val
          (Function.update (x m) i₀ c i) := by
        rw [eθ, e2]; exact hx m
      have hb' : ∀ i, ThetaPlurisubharmonic (Function.update (fun _ : Fin n => θ) i₀ θ i).val
          (Function.update (x m) i₀ (fun _ : M => (0 : EReal)) i) := by
        intro i
        rw [eθ]
        by_cases h : i = i₀
        · rw [h, Function.update_self]; exact h0
        · rw [Function.update_of_ne h]; exact hx m i
      have hpa : globalMixedMeasure _ _ hb' {p | c p = ⊥} = 0 := by
        have : {p | c p = ⊥} = ∅ := eq_empty_of_forall_notMem fun p hp => hcb.ne_bot p hp
        rw [this, measure_empty]
      have hpb : globalMixedMeasure _ _ ha' {p | (fun _ : M => (0 : EReal)) p = ⊥} = 0 := by
        have : {p | (fun _ : M => (0 : EReal)) p = ⊥} = ∅ :=
          eq_empty_of_forall_notMem fun p hp => EReal.zero_ne_bot hp
        rw [this, measure_empty]
      have hlin := GlobalSlotLinear.globalMixedMeasure_update_add_smul (θ := fun _ => θ) i₀
        hs hε0 hθeq.symm hc' ha' hb' hpa hpb
      have hA : globalMixedMeasure (Function.update (fun _ => θ) i₀ θ)
          (Function.update (x m) i₀ c) ha' = globalMixedMeasure (fun _ => θ) (x m) (hx m) :=
        globalMixedMeasure_congr eθ e2 _ _
      have hC : globalMixedMeasure (fun _ => θ) (x (m + 1)) (hx (m + 1)) =
          globalMixedMeasure (fun _ => θ) (Function.update (x m) i₀ d) hc' :=
        globalMixedMeasure_congr rfl e1 _ _
      rw [hC, hlin, hA, add_apply, smul_apply, smul_eq_mul]
      calc ENNReal.ofReal ((1 - ε) ^ (m + 1)) *
            globalMixedMeasure (fun _ => θ) (fun _ => c) (fun _ => hc) S
          = ENNReal.ofReal (1 - ε) * (ENNReal.ofReal ((1 - ε) ^ m) *
            globalMixedMeasure (fun _ => θ) (fun _ => c) (fun _ => hc) S) := by
            rw [pow_succ', ENNReal.ofReal_mul hs.le, mul_assoc]
        _ ≤ ENNReal.ofReal (1 - ε) * globalMixedMeasure (fun _ => θ) (x m) (hx m) S := by
            gcongr
            exact ih (Nat.le_of_succ_le hm) S
        _ ≤ _ := le_self_add
  have hfull : x n = fun _ => d := by funext i; simp [x, i.isLt]
  have hdK : ThetaPlurisubharmonic θ.val (fun p => d p - (K : EReal)) :=
    thetaPlurisubharmonic_sub_const hdθ K
  have efin : (fun p => (((1 - ε) * (c p).toReal - K : ℝ) : EReal)) =
      fun p => d p - (K : EReal) := by
    funext p
    have hcp : c p = ((c p).toReal : EReal) :=
      (EReal.coe_toReal (hcb.ne_top p) (hcb.ne_bot p)).symm
    simp only [d]
    conv_rhs => rw [hcp]
    rw [mul_zero, add_zero, ← EReal.coe_mul, ← EReal.coe_sub]
  refine ⟨efin ▸ hdK, fun S => ?_⟩
  have hsub := GlobalMeasureInvariance.globalMixedMeasure_sub_const (θ := fun _ => θ)
    (u := fun _ => d) (fun _ => hdθ) (fun _ => K)
  calc ENNReal.ofReal ((1 - ε) ^ n) *
        globalMixedMeasure (fun _ => θ) (fun _ => c) (fun _ => hc) S
      ≤ globalMixedMeasure (fun _ => θ) (x n) (hx n) S := step n le_rfl S
    _ = globalMixedMeasure (fun _ => θ) (fun _ => d) (fun _ => hdθ) S := by
        rw [globalMixedMeasure_congr rfl hfull (hx n) (fun _ => hdθ)]
    _ = _ := by
        rw [← hsub]
        exact congrArg (fun μ : Measure M => μ S)
          (globalMixedMeasure_congr rfl (by funext i; exact efin.symm) _ _)

end

end SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling
