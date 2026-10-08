/-
Copyright (c) 2026 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

public import LeanPool.AbstractLinearControl.Examples.ExoticMean


/-!
# Periodization and the invariant functional `J` (Step 1 of Proposition 3.3)

Let `m` be a positive, normalized, translation-invariant mean on `L^∞_per` (Lemma 3.2).
For a bounded measurable `f` vanishing outside a bounded interval (`TestFunction`), its
periodization `P f (r) = Σ_{k ∈ ℤ} f (r + k)` is a finite sum for every `r`, and
`J(f) = m(P f)` is linear, positive and translation invariant. This file proves:

* `mean_interval` : `J(1_{(a,b]}) = b - a` (equation `eq:J-intervals`);
* `mean_support_bound` : `|J(f)| ≤ (b - a) ‖f‖_∞` if `f` vanishes outside `(a, b]`
  (equation `eq:J-bound`);
* `periodize_shifted`, `periodize_add`, `periodize_smul`, `raw_cell_recovery` : the
  compatibility of `P` with translations, sums, scalars and periodic functions.

All identities involving representatives hold almost everywhere; `ae_shifts` handles
the countably many integer translates of a null set at once. The paper uses intervals
`[a, b)`; here they are `(a, b]`, which only changes null sets.
-/

namespace AbstractLinearControl

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators

namespace ExoticMean.Periodization

/-- A bounded measurable function `ℝ → ℝ` vanishing outside a bounded interval. -/
structure TestFunction where
  /-- The bounded measurable test function. -/
  val : ℝ → ℝ
  measurable : StronglyMeasurable val
  supported : ∃ n : ℕ, ∀ x, x ∉ Icc (-(n : ℝ)) n → val x = 0
  bounded : ∃ C : ℝ, ∀ᵐ x ∂volume, ‖val x‖ ≤ C

/-- The periodization `P f (r) = Σ_{k ∈ ℤ} f (r + k)` (raw formula). -/
def raw (f : ℝ → ℝ) (r : ℝ) : ℝ := ∑' k : ℤ, f (r + (k : ℝ))

/-- The integers `k` with `r + k ∈ [-n, n]`. -/
def window (n : ℕ) (r : ℝ) : Finset ℤ :=
  Finset.Icc ⌈-(n : ℝ) - r⌉ ⌊(n : ℝ) - r⌋

lemma outside_window (f : TestFunction) {n : ℕ}
    (hn : ∀ x, x ∉ Icc (-(n : ℝ)) n → f.val x = 0)
    (r : ℝ) (k : ℤ) (hk : k ∉ window n r) : f.val (r + k) = 0 := by
  apply hn
  intro hx
  apply hk
  simp only [window, Finset.mem_Icc]
  exact ⟨Int.ceil_le.mpr (by linarith [hx.1]),
    Int.le_floor.mpr (by linarith [hx.2])⟩

lemma finite_shifts (f : TestFunction) (r : ℝ) :
    Function.HasFiniteSupport (fun k : ℤ => f.val (r + k)) := by
  obtain ⟨n, hn⟩ := f.supported
  apply (window n r).finite_toSet.subset
  intro k hk
  by_contra h
  exact hk (outside_window f hn r k h)

lemma TestFunction.summable_shifts (f : TestFunction) (r : ℝ) :
    Summable (fun k : ℤ => f.val (r + k)) :=
  summable_of_hasFiniteSupport (finite_shifts f r)

lemma raw_eq_sum (f : TestFunction) {n : ℕ}
    (hn : ∀ x, x ∉ Icc (-(n : ℝ)) n → f.val x = 0) (r : ℝ) :
    raw f.val r = ∑ k ∈ window n r, f.val (r + k) :=
  tsum_eq_sum (outside_window f hn r)

lemma window_card_le (n : ℕ) (r : ℝ) : (window n r).card ≤ 2 * n + 1 := by
  have h : ⌊(n : ℝ) - r⌋ + 1 - ⌈-(n : ℝ) - r⌉ ≤ (2 * n + 1 : ℤ) := by
    have hreal : (⌊(n : ℝ) - r⌋ : ℝ) + 1 - (⌈-(n : ℝ) - r⌉ : ℝ) ≤
        (2 * n + 1 : ℝ) := by
      linarith [Int.floor_le ((n : ℝ) - r), Int.le_ceil (-(n : ℝ) - r)]
    exact_mod_cast hreal
  simp only [window, Int.card_Icc]
  omega

lemma raw_int_shift (f : ℝ → ℝ) (r : ℝ) (j : ℤ) :
    raw f (r + j) = raw f r := by
  unfold raw
  convert (Equiv.addLeft j).tsum_eq (fun k : ℤ => f (r + k)) using 1
  congr 1
  funext k
  congr 1
  change r + (j : ℝ) + (k : ℝ) = r + ((j + k : ℤ) : ℝ)
  push_cast
  ring

lemma TestFunction.raw_measurable (f : TestFunction) : StronglyMeasurable (raw f.val) := by
  apply StronglyMeasurable.tsum
  intro k
  exact f.measurable.comp_measurable (measurable_id.add measurable_const)

/-- A single exceptional set covers all integer translates. -/
lemma ae_shifts {p : ℝ → Prop} (hp : ∀ᵐ r ∂volume, p r) :
    ∀ᵐ r ∂volume, ∀ k : ℤ, p (r + k) := by
  apply ae_all_iff.mpr
  intro k
  exact (measurePreserving_add_right (volume : Measure ℝ) (k : ℝ)).quasiMeasurePreserving.ae hp

lemma raw_bound (f : TestFunction) : ∃ C : ℝ, ∀ᵐ r ∂volume, ‖raw f.val r‖ ≤ C := by
  obtain ⟨n, hn⟩ := f.supported
  obtain ⟨C, hC⟩ := f.bounded
  have hC0 : 0 ≤ C := by
    obtain ⟨r, hr⟩ := hC.exists
    exact (norm_nonneg _).trans hr
  refine ⟨(2 * n + 1 : ℕ) * C, ?_⟩
  filter_upwards [ae_shifts hC] with r hr
  rw [raw_eq_sum f hn]
  calc
    ‖∑ k ∈ window n r, f.val (r + k)‖ ≤
        ∑ k ∈ window n r, ‖f.val (r + k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ window n r, C := Finset.sum_le_sum (fun k _ => hr k)
    _ = (window n r).card * C := by simp
    _ ≤ (2 * n + 1 : ℕ) * C :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast window_card_le n r) hC0

lemma TestFunction.raw_memLp (f : TestFunction) : MemLp (raw f.val) ∞ volume := by
  obtain ⟨C, hC⟩ := raw_bound f
  exact memLp_top_of_bound f.raw_measurable.aestronglyMeasurable C hC

/-- The periodization `P f`, as an element of `L^∞_per`. -/
def periodize (f : TestFunction) : LinftyPer :=
  ⟨f.raw_memLp.toLp (raw f.val), by
    apply Lp.ext
    have hf := f.raw_memLp.coeFn_toLp
    have hs := (measurePreserving_add_left (volume : Measure ℝ) (-1)).quasiMeasurePreserving.ae hf
    filter_upwards [shift_ae 1 (f.raw_memLp.toLp (raw f.val)), hf, hs] with r h1 h2 h3
    rw [h1, h2, h3]
    simpa [add_comm] using raw_int_shift f.val r (-1)⟩

lemma TestFunction.periodize_ae (f : TestFunction) : ⇑(periodize f).val =ᵐ[volume] raw f.val :=
  f.raw_memLp.coeFn_toLp

lemma periodize_congr (f g : TestFunction) (heq : f.val =ᵐ[volume] g.val) :
    periodize f = periodize g := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [f.periodize_ae, g.periodize_ae, ae_shifts heq] with r hf hg hr
  rw [hf, hg]
  exact tsum_congr hr

lemma periodize_add (f g h : TestFunction)
    (heq : f.val =ᵐ[volume] fun r => g.val r + h.val r) :
    periodize f = periodize g + periodize h := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [f.periodize_ae, g.periodize_ae, h.periodize_ae,
    Lp.coeFn_add (periodize g).val (periodize h).val, ae_shifts heq] with r hf hg hh ha he
  change (periodize f).val r = ((periodize g).val + (periodize h).val) r
  simp only [Pi.add_apply] at ha
  rw [ha, hf, hg, hh]
  unfold raw
  rw [tsum_congr he, (g.summable_shifts r).tsum_add (h.summable_shifts r)]

lemma periodize_smul (f g : TestFunction) (c : ℝ)
    (heq : f.val =ᵐ[volume] fun r => c * g.val r) :
    periodize f = c • periodize g := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [f.periodize_ae, g.periodize_ae,
    Lp.coeFn_smul c (periodize g).val, ae_shifts heq] with r hf hg hs he
  change (periodize f).val r = (c • (periodize g).val) r
  simp only [Pi.smul_apply] at hs
  rw [hf, hs, hg]
  unfold raw
  rw [tsum_congr he, tsum_mul_left]
  rfl

lemma periodize_le (f g : TestFunction)
    (hle : ∀ᵐ r ∂volume, f.val r ≤ g.val r) :
    ∀ᵐ r ∂volume, (periodize f).val r ≤ (periodize g).val r := by
  filter_upwards [f.periodize_ae, g.periodize_ae, ae_shifts hle] with r hf hg hr
  rw [hf, hg]
  exact (f.summable_shifts r).tsum_le_tsum hr (g.summable_shifts r)

lemma mean_le (m : LinftyPer →L[ℝ] ℝ) (hpos : Positive m.toLinearMap)
    (f g : TestFunction) (hle : ∀ᵐ r ∂volume, f.val r ≤ g.val r) :
    m (periodize f) ≤ m (periodize g) := by
  have hp : ∀ᵐ r ∂volume, 0 ≤ (periodize g - periodize f).val r := by
    filter_upwards [periodize_le f g hle,
      Lp.coeFn_sub (periodize g).val (periodize f).val] with r hr hs
    exact hs.symm ▸ sub_nonneg.mpr hr
  have hm := hpos (periodize g - periodize f) hp
  change 0 ≤ m (periodize g - periodize f) at hm
  rw [map_sub] at hm
  linarith

/-- `1_{(a,b]} f`, for `f` bounded on `(a, b]`. -/
def supportedInterval (a b : ℝ) (f : ℝ → ℝ) (hf : StronglyMeasurable f)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᵐ r ∂volume, r ∈ Ioc a b → ‖f r‖ ≤ C) : TestFunction where
  val := (Ioc a b).indicator f
  measurable := hf.indicator measurableSet_Ioc
  supported := by
    obtain ⟨n, hn⟩ := exists_nat_gt (max |a| |b|)
    refine ⟨n, ?_⟩
    intro r hr
    apply indicator_of_notMem
    intro hab
    apply hr
    have ha : |a| < (n : ℝ) := (le_max_left _ _).trans_lt hn
    have hb : |b| < (n : ℝ) := (le_max_right _ _).trans_lt hn
    exact ⟨by linarith [neg_abs_le a, hab.1], by linarith [le_abs_self b, hab.2]⟩
  bounded := by
    refine ⟨C, ?_⟩
    filter_upwards [hbound] with r hr
    by_cases hab : r ∈ Ioc a b
    · simpa [hab] using hr hab
    · simpa [hab] using hC

/-- The constant `c` on `(a, b]`, zero elsewhere. -/
def interval (a b c : ℝ) : TestFunction :=
  supportedInterval a b (fun _ => c) stronglyMeasurable_const ‖c‖ (norm_nonneg _)
    (Eventually.of_forall (fun _ _ => le_rfl))

/-- The translate `f (· - a)`. -/
def shifted (a : ℝ) (f : TestFunction) : TestFunction where
  val r := f.val (-a + r)
  measurable := f.measurable.comp_measurable (measurable_const.add measurable_id)
  supported := by
    obtain ⟨n, hn⟩ := f.supported
    obtain ⟨N, hN⟩ := exists_nat_gt ((n : ℝ) + |a|)
    refine ⟨N, ?_⟩
    intro r hr
    apply hn
    intro hx
    apply hr
    exact ⟨by linarith [neg_abs_le a, hx.1], by linarith [le_abs_self a, hx.2]⟩
  bounded := by
    obtain ⟨C, hC⟩ := f.bounded
    exact ⟨C, (measurePreserving_add_left (volume : Measure ℝ) (-a)).quasiMeasurePreserving.ae hC⟩

lemma periodize_shifted (a : ℝ) (f : TestFunction) :
    periodize (shifted a f) = translate a (periodize f) := by
  apply Subtype.ext
  apply Lp.ext
  have hs := (measurePreserving_add_left (volume : Measure ℝ) (-a)).quasiMeasurePreserving.ae
      f.periodize_ae
  filter_upwards [(shifted a f).periodize_ae, shift_ae a (periodize f).val, hs]
    with r hf hg hh
  change (periodize (shifted a f)).val r = (shift a (periodize f).val) r
  rw [hf, hg, hh]
  unfold raw
  apply tsum_congr
  intro k
  change f.val (-a + (r + k)) = f.val ((-a + r) + k)
  rw [add_assoc]

lemma periodize_interval_shift (a b : ℝ) :
    periodize (interval a b 1) = translate a (periodize (interval 0 (b - a) 1)) := by
  rw [← periodize_shifted]
  apply periodize_congr
  apply Eventually.of_forall
  intro r
  change (Ioc a b).indicator (fun _ => (1 : ℝ)) r =
    (Ioc 0 (b - a)).indicator (fun _ => (1 : ℝ)) (-a + r)
  have heq : (-a + r ∈ Ioc 0 (b - a)) ↔ r ∈ Ioc a b := by
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [Set.indicator, heq]

lemma interval_split (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    (interval a c 1).val =ᵐ[volume]
      fun r => (interval a b 1).val r + (interval b c 1).val r := by
  apply Eventually.of_forall
  intro r
  change (Ioc a c).indicator (fun _ => (1 : ℝ)) r =
    (Ioc a b).indicator (fun _ => (1 : ℝ)) r +
      (Ioc b c).indicator (fun _ => (1 : ℝ)) r
  by_cases h1 : a < r <;> by_cases h2 : r ≤ b <;> by_cases h3 : r ≤ c <;>
    simp [Set.indicator, h1, h2, h3] <;> linarith

lemma periodize_unit : periodize (interval 0 1 1) = one := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [(interval 0 1 1).periodize_ae, one_ae] with r hr h1
  rw [hr, h1]
  obtain ⟨k, hk, huniq⟩ := existsUnique_add_zsmul_mem_Ioc (by norm_num : (0 : ℝ) < 1) r 0
  have hk' : r + (k : ℝ) ∈ Ioc (0 : ℝ) 1 := by simpa using hk
  unfold raw
  rw [tsum_eq_single k]
  · change (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (r + k) = 1
    exact indicator_of_mem hk' _
  · intro j hj
    change (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (r + j) = 0
    apply indicator_of_notMem
    intro hjmem
    apply hj
    apply huniq
    simpa using hjmem

lemma raw_cell_recovery (f : ℝ → ℝ) (hf : Function.Periodic f 1) (r : ℝ) :
    raw ((Ioc (0 : ℝ) 1).indicator f) r = f r := by
  obtain ⟨k, hk, huniq⟩ := existsUnique_add_zsmul_mem_Ioc (by norm_num : (0 : ℝ) < 1) r 0
  have hk' : r + (k : ℝ) ∈ Ioc (0 : ℝ) 1 := by simpa using hk
  unfold raw
  rw [tsum_eq_single k]
  · rw [indicator_of_mem hk']
    simpa using hf.int_mul k r
  · intro j hj
    apply indicator_of_notMem
    intro hjmem
    exact hj (huniq j (by simpa using hjmem))

/-- Interval calibration `J(1_{(a,b]}) = b - a` (equation `eq:J-intervals`), where
`J = m ∘ P`. The function `q(t) = J(1_{(0,t]})` is additive and monotone with `q(1) = 1`;
squeezing between integers gives `q(t) = t`. -/
theorem mean_interval (m : LinftyPer →L[ℝ] ℝ) (hpos : Positive m.toLinearMap)
    (h1 : m one = 1) (hT : ∀ a f, m (translate a f) = m f)
    (a b : ℝ) (hab : a ≤ b) : m (periodize (interval a b 1)) = b - a := by
  let q : ℝ → ℝ := fun t => m (periodize (interval 0 t 1))
  have q0 : q 0 = 0 := by
    have hz : periodize (interval 0 0 1) = 0 := by
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [(interval 0 0 1).periodize_ae, Lp.coeFn_zero ℝ ∞ volume] with r hr hz
      change (periodize (interval 0 0 1)).val r = (0 : Ambient) r
      rw [hr, hz]
      simp [raw, interval, supportedInterval]
    simp [q, hz]
  have q1 : q 1 = 1 := by simpa [q, periodize_unit] using h1
  have qadd (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) : q (s + t) = q s + q t := by
    have hp := periodize_add (interval 0 (s + t) 1) (interval 0 s 1)
      (interval s (s + t) 1) (interval_split 0 s (s + t) hs (by linarith))
    dsimp [q]
    rw [hp, map_add, periodize_interval_shift s (s + t), hT]
    simp
  have qmono {s t : ℝ} (hst : s ≤ t) : q s ≤ q t := by
    apply mean_le m hpos
    apply Eventually.of_forall
    intro r
    change (Ioc 0 s).indicator (fun _ => (1 : ℝ)) r ≤
      (Ioc 0 t).indicator (fun _ => (1 : ℝ)) r
    by_cases hr : r ∈ Ioc 0 s
    · have ht : r ∈ Ioc 0 t := ⟨hr.1, hr.2.trans hst⟩
      simp [hr, ht]
    · simp [hr, indicator_nonneg (fun _ _ => zero_le_one)]
  have qmul (t : ℝ) (ht : 0 ≤ t) (n : ℕ) : q ((n : ℝ) * t) = n * q t := by
    induction n with
    | zero => simpa using q0
    | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        qadd _ _ (mul_nonneg (Nat.cast_nonneg _) ht) ht, ih]
      ring
  have qnat (n : ℕ) : q n = n := by simpa [q1] using qmul 1 (by norm_num) n
  have qeq (t : ℝ) (ht : 0 ≤ t) : q t = t := by
    have squeeze (n : ℕ) : |q t - t| * n ≤ 1 := by
      let k := ⌊(n : ℝ) * t⌋₊
      have hlow : (k : ℝ) ≤ (n : ℝ) * q t := by
        rw [← qnat k, ← qmul t ht n]
        exact qmono (Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) ht))
      have hupp : (n : ℝ) * q t ≤ (k : ℝ) + 1 := by
        rw [← qmul t ht n, ← Nat.cast_succ k, ← qnat (k + 1)]
        apply qmono
        simpa [k] using (Nat.lt_floor_add_one ((n : ℝ) * t)).le
      have hk1 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) ht)
      have hk2 := Nat.lt_floor_add_one ((n : ℝ) * t)
      change (k : ℝ) ≤ (n : ℝ) * t at hk1
      change (n : ℝ) * t < (k : ℝ) + 1 at hk2
      have heq : |q t - t| * (n : ℝ) = |(q t - t) * n| := by
        rw [abs_mul, abs_of_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)]
      rw [heq]
      rw [sub_mul]
      exact abs_le.mpr ⟨by linarith only [hlow, hk2], by linarith only [hupp, hk1]⟩
    by_contra hne
    have hd : 0 < |q t - t| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / |q t - t|)
    have hlarge := (div_lt_iff₀ hd).mp hn
    have hsmall := squeeze n
    linarith only [hlarge, hsmall]
  rw [periodize_interval_shift, hT]
  exact qeq (b - a) (sub_nonneg.mpr hab)

/-- The support bound `eq:J-bound`: if `|f| ≤ C` on `(a, b]` and `f = 0` elsewhere,
then `|J(f)| ≤ (b - a) C`. -/
theorem mean_support_bound (m : LinftyPer →L[ℝ] ℝ) (hpos : Positive m.toLinearMap)
    (h1 : m one = 1) (hT : ∀ a f, m (translate a f) = m f)
    (f : TestFunction) (a b C : ℝ) (hab : a ≤ b) (_hC : 0 ≤ C)
    (hf : ∀ᵐ r ∂volume, ‖f.val r‖ ≤ (Ioc a b).indicator (fun _ => C) r) :
    ‖m (periodize f)‖ ≤ (b - a) * C := by
  have scaling (c : ℝ) : m (periodize (interval a b c)) = c * (b - a) := by
    have heq := periodize_smul (interval a b c) (interval a b 1) c
      (Eventually.of_forall (fun r => by
        change (Ioc a b).indicator (fun _ => c) r =
          c * (Ioc a b).indicator (fun _ => (1 : ℝ)) r
        by_cases hr : r ∈ Ioc a b <;> simp [hr]))
    rw [heq, map_smul, mean_interval m hpos h1 hT a b hab]
    rfl
  have hlo : m (periodize (interval a b (-C))) ≤ m (periodize f) := by
    apply mean_le m hpos
    filter_upwards [hf] with r hr
    change (Ioc a b).indicator (fun _ => -C) r ≤ f.val r
    rw [Real.norm_eq_abs] at hr
    by_cases hm : r ∈ Ioc a b
    · simpa [hm] using (abs_le.mp hr).1
    · simp only [indicator_of_notMem hm] at *
      simpa using (abs_le.mp hr).1
  have hhi : m (periodize f) ≤ m (periodize (interval a b C)) := by
    apply mean_le m hpos
    filter_upwards [hf] with r hr
    exact (le_abs_self _).trans hr
  rw [scaling] at hlo hhi
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> nlinarith

end ExoticMean.Periodization

end
end

end AbstractLinearControl
