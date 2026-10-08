/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatCriticalFive
public import LeanPool.EscauriazaSereginSverak.PartV.HeatCriticalDensity

/-!
# The critical heat estimate

This file proves `lem:pv-heat-critical`: for `b ∈ L³`,
`‖S(·)b‖_{L⁵(Q_τ)} ≤ C‖b‖₃`, and for `b ∈ L² ∩ L³`,
`‖S(·)b‖_{L⁴(Q_τ)} ≤ C(‖b‖₂ + ‖b‖₃)`, with `C` independent of `τ`.  The
smooth compact case is `heatOrbit_five_smooth` and
`heatOrbit_tenThirds_smooth`; approximation in `Lᵖ` extends both, and the
`L⁴` bound follows by Hölder interpolation on `Q_τ`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat


noncomputable section

namespace ESS

private theorem vec3_norm_le_sum_abs (v : Vec3) : ‖v‖ ≤ ∑ i : Fin 3, |v i| := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).2 ?_
  intro i
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun k => |v k|) (fun k _ => abs_nonneg _)
    (Finset.mem_univ i)

/-- Every `Lᵖ` vector field, `1 ≤ p < ∞`, is an `Lᵖ` limit of smooth compactly
supported vector fields. -/
theorem exists_smooth_compact_vec3_tendsto_eLpNorm {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ∞) {b : Vec3 → Vec3} (hb : MemLp b p volume) :
    ∃ bs : ℕ → Vec3 → Vec3,
      (∀ n i, ContDiff ℝ (⊤ : ℕ∞) (fun x => bs n x i)) ∧
      (∀ n i, HasCompactSupport (fun x => bs n x i)) ∧
      Tendsto (fun n => eLpNorm (bs n - b) p volume) atTop (nhds 0) := by
  choose g hg hglim using fun i : Fin 3 =>
    exists_smooth_compact_tendsto_eLpNorm hp1 hp (memLp_pi_iff.1 hb i)
  refine ⟨fun n x i => g i n x, fun n i => (hg i n).1, fun n i => (hg i n).2, ?_⟩
  have hbound (n : ℕ) : eLpNorm ((fun x i => g i n x) - b) p volume ≤
      ∑ i : Fin 3, eLpNorm (g i n - fun x => b x i) p volume := by
    have hmeas (i : Fin 3) : AEStronglyMeasurable (g i n - fun x => b x i) volume :=
      (hg i n).1.continuous.aestronglyMeasurable.sub (memLp_pi_iff.1 hb i).aestronglyMeasurable
    calc
      eLpNorm ((fun x i => g i n x) - b) p volume ≤
          eLpNorm (∑ i : Fin 3, fun x => |(g i n - fun y => b y i) x|) p volume := by
        refine eLpNorm_mono_ae ?_ (Filter.Eventually.of_forall fun x => ?_)
        · exact (continuous_pi fun i => (hg i n).1.continuous).aestronglyMeasurable.sub
            hb.aestronglyMeasurable
        · rw [Finset.sum_apply, Real.norm_eq_abs,
            abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)]
          exact vec3_norm_le_sum_abs _
      _ ≤ ∑ i : Fin 3, eLpNorm (fun x => |(g i n - fun y => b y i) x|) p volume :=
        eLpNorm_sum_le hp1
      _ = ∑ i : Fin 3, eLpNorm (g i n - fun x => b x i) p volume := by
        apply Finset.sum_congr rfl
        intro i _
        have h := eLpNorm_norm (p := p) (μ := volume) _ (hmeas i)
        simpa only [Real.norm_eq_abs] using h
  have hsum : Tendsto (fun n => ∑ i : Fin 3, eLpNorm (g i n - fun x => b x i) p volume)
      atTop (nhds 0) := by
    simpa using tendsto_finsetSum (s := Finset.univ) fun i _ => hglim i
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) hbound

/-- Approximation step of `lem:pv-heat-critical`: a space-time bound for smooth
compact data in terms of the `Lᵖ` norm extends to every `Lᵖ` datum, together
with the measurability of its heat orbit on `Q_τ`. -/
theorem heatOrbit_eLpNorm_le_of_smooth {p q : ℝ} (hpq : p.HolderConjugate q)
    {r : ℝ≥0∞} {C τ : ℝ}
    (hsmooth : ∀ b' : Vec3 → Vec3,
      (∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b' x i)) →
      (∀ i : Fin 3, HasCompactSupport (fun x => b' x i)) →
      eLpNorm (heatOrbit b') r
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
        ENNReal.ofReal C * eLpNorm b' (ENNReal.ofReal p) volume)
    {b : Vec3 → Vec3} (hb : MemLp b (ENNReal.ofReal p) volume) :
    AEStronglyMeasurable (heatOrbit b)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
      eLpNorm (heatOrbit b) r
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
        ENNReal.ofReal C * eLpNorm b (ENNReal.ofReal p) volume := by
  set Q := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa using hpq.lt.le
  obtain ⟨bs, hs, hc, hlim⟩ :=
    exists_smooth_compact_vec3_tendsto_eLpNorm hp1 ENNReal.ofReal_ne_top hb
  have hbsMem (n : ℕ) : MemLp (bs n) (ENNReal.ofReal p) volume :=
    memLp_pi_iff.2 fun i => (hs n i).continuous.memLp_of_hasCompactSupport (hc n i)
  have hQ : MeasurableSet Q := MeasurableSet.univ.prod measurableSet_Ioo
  have hpt : ∀ᵐ z ∂(volume.restrict Q),
      Tendsto (fun n => heatOrbit (bs n) z) atTop (nhds (heatOrbit b z)) := by
    filter_upwards [ae_restrict_mem hQ] with z hz
    obtain ⟨x, t⟩ := z
    have ht : 0 < t := hz.2.1
    set A := eLpNorm (fun y : Vec3 => heatKernel y t) (ENNReal.ofReal q) volume
    have hA : A ≠ ∞ := (heatKernel_memLp ht hpq.symm.lt.le).eLpNorm_ne_top
    have hbd : Tendsto (fun n => A * eLpNorm (bs n - b) (ENNReal.ofReal p) volume)
        atTop (nhds 0) := by
      simpa using ENNReal.Tendsto.const_mul hlim (Or.inr hA)
    rw [tendsto_iff_edist_tendsto_0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbd
      (fun _ => bot_le) fun n => ?_
    rw [edist_eq_enorm_sub]
    exact heatOrbit_sub_enorm_le hpq (hbsMem n) hb ht
  have hmeasSeq (n : ℕ) : AEStronglyMeasurable (heatOrbit (bs n)) (volume.restrict Q) :=
    heatOrbit_aestronglyMeasurable_smooth (hs n) (hc n) τ
  have hmeas : AEStronglyMeasurable (heatOrbit b) (volume.restrict Q) :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeasSeq hpt
  refine ⟨hmeas, ?_⟩
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := r) hmeasSeq (heatOrbit b) hmeas hpt
  have hnorm (n : ℕ) : eLpNorm (bs n) (ENNReal.ofReal p) volume ≤
      eLpNorm b (ENNReal.ofReal p) volume + eLpNorm (bs n - b) (ENNReal.ofReal p) volume := by
    have hsplit : bs n = b + (bs n - b) := by abel
    conv_lhs => rw [hsplit]
    exact eLpNorm_add_le hp1
  have hR : Tendsto (fun n => ENNReal.ofReal C * (eLpNorm b (ENNReal.ofReal p) volume +
      eLpNorm (bs n - b) (ENNReal.ofReal p) volume)) atTop
      (nhds (ENNReal.ofReal C * eLpNorm b (ENNReal.ofReal p) volume)) := by
    have h := ENNReal.Tendsto.const_mul
      ((tendsto_const_nhds (x := eLpNorm b (ENNReal.ofReal p) volume)).add hlim)
      (Or.inr (ENNReal.ofReal_ne_top (r := C)))
    simpa using h
  calc
    eLpNorm (heatOrbit b) r (volume.restrict Q) ≤
        Filter.liminf (fun n => eLpNorm (heatOrbit (bs n)) r (volume.restrict Q)) atTop :=
      hfatou
    _ ≤ Filter.liminf (fun n => ENNReal.ofReal C * (eLpNorm b (ENNReal.ofReal p) volume +
          eLpNorm (bs n - b) (ENNReal.ofReal p) volume)) atTop := by
      refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n => ?_)
      exact (hsmooth (bs n) (hs n) (hc n)).trans (by gcongr; exact hnorm n)
    _ = ENNReal.ofReal C * eLpNorm b (ENNReal.ofReal p) volume := hR.liminf_eq

/-- Hölder interpolation `‖f‖₄ ≤ ‖f‖_{10/3}^{1/2} ‖f‖₅^{1/2}` on any measure
space; the constant is one. -/
theorem eLpNorm_four_le_tenThirds_mul_five {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {f : α → E} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 4 μ ≤ eLpNorm f (ENNReal.ofReal (10 / 3 : ℝ)) μ ^ (1 / 2 : ℝ) *
      eLpNorm f 5 μ ^ (1 / 2 : ℝ) := by
  let w : α → ℝ := fun x => ‖f x‖ ^ (1 / 2 : ℝ)
  have hw : AEStronglyMeasurable w μ :=
    (hf.norm.aemeasurable.pow_const _).aestronglyMeasurable
  have htriple : ENNReal.HolderTriple (ENNReal.ofReal (20 / 3 : ℝ)) (ENNReal.ofReal 10) 4 := by
    refine ⟨?_⟩
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 20 / 3),
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 10),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4)]
    norm_num
  have hholder : eLpNorm (fun x => w x * w x) 4 μ ≤
      eLpNorm w (ENNReal.ofReal (20 / 3 : ℝ)) μ * eLpNorm w (ENNReal.ofReal 10) μ := by
    simpa [ENNReal.smul_def, one_mul] using
      (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (μ := μ) (p := ENNReal.ofReal (20 / 3 : ℝ))
        (q := ENNReal.ofReal 10) (r := 4) (fun a b : ℝ => a * b) 1 continuous_mul hw hw
        (Filter.Eventually.of_forall fun x => by simp [Real.norm_eq_abs, one_mul]))
  have hprod : (fun x => w x * w x) = fun x => ‖f x‖ := by
    funext x
    change ‖f x‖ ^ (1 / 2 : ℝ) * ‖f x‖ ^ (1 / 2 : ℝ) = ‖f x‖
    rw [← Real.rpow_add' (norm_nonneg _) (by norm_num)]
    norm_num
  have hw1 : eLpNorm w (ENNReal.ofReal (20 / 3 : ℝ)) μ =
      eLpNorm f (ENNReal.ofReal (10 / 3 : ℝ)) μ ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_norm_rpow f hf (by norm_num : (0 : ℝ) < 1 / 2),
      ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hw2 : eLpNorm w (ENNReal.ofReal 10) μ = eLpNorm f 5 μ ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_norm_rpow f hf (by norm_num : (0 : ℝ) < 1 / 2),
      ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [hprod, eLpNorm_norm f hf, hw1, hw2] at hholder
  exact hholder

private theorem holderConjugate_three : (3 : ℝ).HolderConjugate (3 / 2) := by
  rw [Real.holderConjugate_iff]
  norm_num

private theorem holderConjugate_two : (2 : ℝ).HolderConjugate 2 := by
  rw [Real.holderConjugate_iff]
  norm_num

/-- The heat orbit of an `L³` datum is almost everywhere strongly measurable on
every slab `Q_τ`, and satisfies the critical `L⁵` bound with the constant of
`heatOrbit_five_smooth`. -/
theorem heatOrbit_five_of_memLp_three {C : ℝ}
    (hC : ∀ (b : Vec3 → Vec3),
      (∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i)) →
      (∀ i : Fin 3, HasCompactSupport (fun x => b x i)) → ∀ τ : ℝ, 0 < τ →
      eLpNorm (heatOrbit b) 5
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
        ENNReal.ofReal C * eLpNorm b 3 volume)
    {b : Vec3 → Vec3} (hb : MemLp b 3 volume) {τ : ℝ} (hτ : 0 < τ) :
    AEStronglyMeasurable (heatOrbit b)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
      eLpNorm (heatOrbit b) 5
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
        ENNReal.ofReal C * eLpNorm b 3 volume := by
  have h := heatOrbit_eLpNorm_le_of_smooth holderConjugate_three (r := 5) (C := C)
    (τ := τ) (fun b' hs hc => by simpa using hC b' hs hc τ hτ) (by simpa using hb)
  exact ⟨h.1, by simpa using h.2⟩

/-- `lem:pv-heat-critical`: for `b ∈ L³` and `τ > 0`,
`‖S(·)b‖_{L⁵(Q_τ)} ≤ C‖b‖₃`, and if also `b ∈ L²`, then
`‖S(·)b‖_{L⁴(Q_τ)} ≤ C(‖b‖₂ + ‖b‖₃)`; the constant does not depend on `τ`. -/
theorem pvHeatCritical : ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Vec3 → Vec3), MemLp b 3 volume →
    ∀ τ : ℝ, 0 < τ →
    eLpNorm (heatOrbit b) 5
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
      ENNReal.ofReal C * eLpNorm b 3 volume ∧
    (MemLp b 2 volume → eLpNorm (heatOrbit b) 4
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
      ENNReal.ofReal C * (eLpNorm b 2 volume + eLpNorm b 3 volume)) := by
  obtain ⟨C5, hC5, h5⟩ := heatOrbit_five_smooth
  obtain ⟨C10, hC10, h10⟩ := heatOrbit_tenThirds_smooth
  refine ⟨C5 + C10, by positivity, ?_⟩
  intro b hb3 τ hτ
  obtain ⟨hmeas, hfive⟩ := heatOrbit_five_of_memLp_three h5 hb3 hτ
  have hC5le : ENNReal.ofReal C5 ≤ ENNReal.ofReal (C5 + C10) :=
    ENNReal.ofReal_le_ofReal (by linarith only [hC10])
  have hC10le : ENNReal.ofReal C10 ≤ ENNReal.ofReal (C5 + C10) :=
    ENNReal.ofReal_le_ofReal (by linarith only [hC5])
  refine ⟨hfive.trans (by gcongr), ?_⟩
  intro hb2
  have hten := heatOrbit_eLpNorm_le_of_smooth holderConjugate_two
    (r := ENNReal.ofReal (10 / 3 : ℝ)) (C := C10) (τ := τ)
    (fun b' hs hc => by simpa using h10 b' hs hc τ hτ) (by simpa using hb2)
  have hten' : eLpNorm (heatOrbit b) (ENNReal.ofReal (10 / 3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
      ENNReal.ofReal C10 * eLpNorm b 2 volume := by
    simpa using hten.2
  set X := eLpNorm b 2 volume
  set Y := eLpNorm b 3 volume
  set D := ENNReal.ofReal (C5 + C10)
  have hA : ENNReal.ofReal C10 * X ≤ D * (X + Y) := by
    gcongr
    exact le_self_add
  have hB : ENNReal.ofReal C5 * Y ≤ D * (X + Y) := by
    gcongr
    exact le_add_self
  calc
    eLpNorm (heatOrbit b) 4
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
        eLpNorm (heatOrbit b) (ENNReal.ofReal (10 / 3 : ℝ))
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ^ (1 / 2 : ℝ) *
          eLpNorm (heatOrbit b) 5
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ^ (1 / 2 : ℝ) :=
      eLpNorm_four_le_tenThirds_mul_five hmeas
    _ ≤ (ENNReal.ofReal C10 * X) ^ (1 / 2 : ℝ) * (ENNReal.ofReal C5 * Y) ^ (1 / 2 : ℝ) := by
      gcongr
    _ ≤ (D * (X + Y)) ^ (1 / 2 : ℝ) * (D * (X + Y)) ^ (1 / 2 : ℝ) := by
      gcongr
    _ = D * (X + Y) := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num

/-- The heat orbit of an `L³` datum lies in `L⁵(Q_τ)`, as used by the
local solution of `sec:pv-trace`. -/
theorem heatOrbit_memLp_five {b : Vec3 → Vec3} (hb : MemLp b 3 volume) {τ : ℝ}
    (hτ : 0 < τ) :
    MemLp (heatOrbit b) 5
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) := by
  obtain ⟨C, _, h5⟩ := heatOrbit_five_smooth
  obtain ⟨-, hbound⟩ := heatOrbit_five_of_memLp_three h5 hb hτ
  rw [memLp_iff]
  exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hb.eLpNorm_lt_top)

/-- The heat orbit of an `L² ∩ L³` datum lies in `L⁴(Q_τ)`, as used by the
local solution of `sec:pv-trace`. -/
theorem heatOrbit_memLp_four {b : Vec3 → Vec3} (hb2 : MemLp b 2 volume)
    (hb3 : MemLp b 3 volume) {τ : ℝ} (hτ : 0 < τ) :
    MemLp (heatOrbit b) 4
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) := by
  obtain ⟨C, _, h⟩ := pvHeatCritical
  have hbound := (h b hb3 τ hτ).2 hb2
  rw [memLp_iff]
  exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.add_lt_top.2 ⟨hb2.eLpNorm_lt_top, hb3.eLpNorm_lt_top⟩))

end ESS

end
