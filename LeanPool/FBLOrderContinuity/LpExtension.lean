/-
Copyright (c) 2026 Raúl E. Pariente-Martín, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raúl E. Pariente-Martín, Pedro Tradacete
-/

module

public import LeanPool.FBLOrderContinuity.Model
public import Mathlib.Analysis.Convex.Gauge



/-!
# Finite-dimensional operator extension from a free-norm bound

The finite-coordinate tensor gauge in Pisier's regular-operator extension argument
turns a lower bound for a lattice embedding into an extension estimate. `tensorBall`
consists of families dominated by a positive free element and nonnegative scalar
coefficients with bounded conjugate-exponent norm.

The proof combines scalar p-sum estimates, the gauge of the convex hull of this ball,
and Hahn–Banach. `extend_latticeOperator` extends finite-dimensional lattice-valued
data to a bounded linear map. `extend_of_free_norm_bound` restricts that extension to
the generators and gives the finite-ell-p operator-extension property with the same
constant. These results supply the converse implications in `Extension.lean`.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set
universe u v
namespace FBLOrderContinuousLH.FiniteLpExtension

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The elementary finite-coordinate tensor ball: each coordinate is dominated by
a nonnegative scalar multiple of one positive free element of norm at most one,
and the scalars have q-sum at most one. In the extension argument q is conjugate
to p; the gauge of the convex hull gives the required domination estimate. -/
def tensorBall (p q : Exponent) (n : ℕ) : Set (Fin n → Free p E) :=
  {x | ∃ a : Fin n → ℝ, (∀ i, 0 ≤ a i) ∧ scalarPSum q a ≤ 1 ∧
    ∃ z : Free p E, 0 ≤ z ∧ ‖z‖ ≤ 1 ∧ ∀ i, |x i| ≤ a i • z}

private theorem scalarPSum_rpow (p : Exponent) (hp : p.IsFinite)
    {n : ℕ} (a : Fin n → ℝ) :
    (scalarPSum p a) ^ p.1.toReal = ∑ i, |a i| ^ p.1.toReal := by
  rw [scalarPSum, ite_eq_right (ne_of_lt hp), one_div]
  exact Real.rpow_inv_rpow (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _))
    (ENNReal.toReal_pos_iff.mpr ⟨zero_lt_one.trans_le p.2, hp⟩).ne'

private theorem scalarPSum_exchange (p : Exponent) (hp : p.IsFinite)
    {m n : ℕ} (a : Fin m → Fin n → ℝ) :
    scalarPSum p (fun i => scalarPSum p (a i)) =
      scalarPSum p (fun j => scalarPSum p (fun i => a i j)) := by
  apply (Real.rpow_left_inj (scalarPSum_nonneg _ _) (scalarPSum_nonneg _ _)
    (ENNReal.toReal_pos_iff.mpr ⟨zero_lt_one.trans_le p.2, hp⟩).ne').mp
  simp_rw [scalarPSum_rpow p hp, abs_of_nonneg (scalarPSum_nonneg _ _),
    scalarPSum_rpow p hp]
  exact Finset.sum_comm

private theorem scalarPSum_weighted_two (p : Exponent) (hp : p.IsFinite)
    {a b t s : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) :
    scalarPSum p ![t ^ (1 / p.1.toReal) * a, s ^ (1 / p.1.toReal) * b] ≤ 1 := by
  have hp0 : 0 < p.1.toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨zero_lt_one.trans_le p.2, hp⟩
  apply (Real.rpow_le_rpow_iff (scalarPSum_nonneg _ _) zero_le_one hp0).mp
  rw [scalarPSum_rpow p hp, Real.one_rpow]
  have hpow (r : ℝ) (hr : 0 ≤ r) :
      (r ^ (1 / p.1.toReal)) ^ p.1.toReal = r := by
    simpa only [one_div] using Real.rpow_inv_rpow hr hp0.ne'
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    abs_mul, abs_of_nonneg (Real.rpow_nonneg ht _),
    abs_of_nonneg (Real.rpow_nonneg hs _),
    Real.mul_rpow (Real.rpow_nonneg ht _) (abs_nonneg a),
    Real.mul_rpow (Real.rpow_nonneg hs _) (abs_nonneg b), hpow t ht, hpow s hs]
  have hap : |a| ^ p.1.toReal ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (abs_nonneg a) ha hp0.le
  have hbp : |b| ^ p.1.toReal ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (abs_nonneg b) hb hp0.le
  nlinarith [mul_le_mul_of_nonneg_left hap ht, mul_le_mul_of_nonneg_left hbp hs]

private theorem weighted_holder (p q : Exponent) (hp : p.IsFinite) (hq : q.IsFinite)
    (hpq : p.1.toReal.HolderConjugate q.1.toReal)
    {t s a b c d : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    t * a * c + s * b * d ≤
      scalarPSum q ![t ^ (1 / q.1.toReal) * a, s ^ (1 / q.1.toReal) * b] *
      scalarPSum p ![t ^ (1 / p.1.toReal) * c, s ^ (1 / p.1.toReal) * d] := by
  have hinv : 1 / q.1.toReal + 1 / p.1.toReal = 1 := by
    simpa only [one_div] using hpq.symm.inv_add_inv_eq_one
  have hprod (r : ℝ) (hr : 0 ≤ r) :
      r ^ (1 / q.1.toReal) * r ^ (1 / p.1.toReal) = r := by
    rw [← Real.rpow_add' hr (by rw [hinv]; exact one_ne_zero), hinv, Real.rpow_one]
  have h := Real.inner_le_Lp_mul_Lq Finset.univ
    ![t ^ (1 / q.1.toReal) * a, s ^ (1 / q.1.toReal) * b]
    ![t ^ (1 / p.1.toReal) * c, s ^ (1 / p.1.toReal) * d] hpq.symm
  have hpair (r : ℝ) (hr : 0 ≤ r) (a b : ℝ) :
      (r ^ (1 / q.1.toReal) * a) * (r ^ (1 / p.1.toReal) * b) = r * a * b := by
    calc
      _ = (r ^ (1 / q.1.toReal) * r ^ (1 / p.1.toReal)) * (a * b) := by ring
      _ = r * a * b := by rw [hprod r hr]; ring
  simpa only [scalarPSum, ite_eq_right (ne_of_lt hp), ite_eq_right (ne_of_lt hq),
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hpair t ht, hpair s hs] using h

private theorem tensorBall_convex_finite (p q : Exponent) (hp : p.IsFinite)
    (hq : q.IsFinite) (hpq : p.1.toReal.HolderConjugate q.1.toReal) (n : ℕ) :
    Convex ℝ (tensorBall (E := E) p q n) := by
  rintro x ⟨a, ha, hanorm, z, hz, hznorm, hx⟩
    y ⟨b, hb, hbnorm, w, hw, hwnorm, hy⟩ t s ht hs hts
  let c (i : Fin n) := scalarPSum q
    ![t ^ (1 / q.1.toReal) * a i, s ^ (1 / q.1.toReal) * b i]
  let v : Free p E := latticePSum p
    ![t ^ (1 / p.1.toReal) • z, s ^ (1 / p.1.toReal) • w]
  refine ⟨c, fun i => scalarPSum_nonneg _ _, ?_, v, ?_, ?_, ?_⟩
  · have heq : scalarPSum q c = scalarPSum q
        ![t ^ (1 / q.1.toReal) * scalarPSum q a,
          s ^ (1 / q.1.toReal) * scalarPSum q b] := by
      refine (scalarPSum_exchange q hq (fun i =>
        ![t ^ (1 / q.1.toReal) * a i, s ^ (1 / q.1.toReal) * b i])).trans ?_
      congr 1
      funext j
      fin_cases j <;> simp [scalarPSum_smul, abs_of_nonneg (Real.rpow_nonneg ht _),
        abs_of_nonneg (Real.rpow_nonneg hs _)]
    rw [heq]
    exact scalarPSum_weighted_two q hq
      (by simpa only [abs_of_nonneg (scalarPSum_nonneg q a)] using hanorm)
      (by simpa only [abs_of_nonneg (scalarPSum_nonneg q b)] using hbnorm) ht hs hts
  · intro φ
    change 0 ≤ v φ
    exact (latticePSum_apply p p _ φ).symm ▸ scalarPSum_nonneg _ _
  · have h := (free_pConvex (E := E) p).2 2
      ![t ^ (1 / p.1.toReal) • z, s ^ (1 / p.1.toReal) • w]
    have heq : (fun i => ‖![t ^ (1 / p.1.toReal) • z,
        s ^ (1 / p.1.toReal) • w] i‖) =
        ![t ^ (1 / p.1.toReal) * ‖z‖, s ^ (1 / p.1.toReal) * ‖w‖] := by
      funext i
      fin_cases i <;> simp [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg ht _), abs_of_nonneg (Real.rpow_nonneg hs _)]
    rw [one_mul, heq] at h
    exact h.trans (scalarPSum_weighted_two p hp
      (by simpa only [abs_of_nonneg (norm_nonneg z)] using hznorm)
      (by simpa only [abs_of_nonneg (norm_nonneg w)] using hwnorm) ht hs hts)
  · intro i φ
    change |t * x i φ + s * y i φ| ≤ c i * v φ
    have hxi : |x i φ| ≤ a i * z φ := hx i φ
    have hyi : |y i φ| ≤ b i * w φ := hy i φ
    calc
      |t * x i φ + s * y i φ| ≤ t * |x i φ| + s * |y i φ| := by
        simpa only [abs_mul, abs_of_nonneg ht, abs_of_nonneg hs] using
          abs_add_le (t * x i φ) (s * y i φ)
      _ ≤ t * (a i * z φ) + s * (b i * w φ) :=
        add_le_add (mul_le_mul_of_nonneg_left hxi ht) (mul_le_mul_of_nonneg_left hyi hs)
      _ ≤ c i * v φ := by
        have hh := weighted_holder p q hp hq hpq (a := a i) (b := b i)
          (c := z φ) (d := w φ) ht hs
        have hv : v φ = scalarPSum p
            ![t ^ (1 / p.1.toReal) * z φ, s ^ (1 / p.1.toReal) * w φ] := by
          exact (latticePSum_apply p p _ φ).trans
            (congrArg (scalarPSum p) (by funext j; fin_cases j <;> rfl))
        calc
          t * (a i * z φ) + s * (b i * w φ) =
              t * a i * z φ + s * b i * w φ := by ring
          _ ≤ _ := hh
          _ = c i * v φ := congrArg (c i * ·) hv.symm

private theorem scalarPSum_coord_le (p : Exponent) {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    |a i| ≤ scalarPSum p a := by
  rw [scalarPSum_eq_piLp_norm]
  exact PiLp.norm_apply_le (WithLp.toLp p.1 a) i

private theorem scalarPSum_infinity_one_le (n : ℕ) :
    scalarPSum Exponent.infinity (fun _ : Fin n => (1 : ℝ)) ≤ 1 := by
  rw [scalarPSum_eq_piLp_norm]
  change ‖WithLp.toLp ⊤ (fun _ : Fin n => (1 : ℝ))‖ ≤ 1
  rw [PiLp.norm_toLp]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun _ => by norm_num)

private theorem tensorBall_convex_infinity (p : Exponent) (n : ℕ) :
    Convex ℝ (tensorBall (E := E) p Exponent.infinity n) := by
  rintro x ⟨a, ha, hanorm, z, hz, hznorm, hx⟩
    y ⟨b, hb, hbnorm, w, hw, hwnorm, hy⟩ t s ht hs hts
  refine ⟨fun _ => 1, fun _ => zero_le_one, scalarPSum_infinity_one_le n,
    t • z + s • w, add_nonneg (smul_nonneg ht hz) (smul_nonneg hs hw), ?_, ?_⟩
  · calc
      ‖t • z + s • w‖ ≤ ‖t • z‖ + ‖s • w‖ := norm_add_le _ _
      _ = t * ‖z‖ + s * ‖w‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, abs_of_nonneg hs]
      _ ≤ t + s := add_le_add (mul_le_of_le_one_right ht hznorm)
        (mul_le_of_le_one_right hs hwnorm)
      _ = 1 := hts
  · intro i φ
    have hai := (le_abs_self (a i)).trans ((scalarPSum_coord_le _ a i).trans hanorm)
    have hbi := (le_abs_self (b i)).trans ((scalarPSum_coord_le _ b i).trans hbnorm)
    have hx' : |x i φ| ≤ z φ := (hx i φ).trans (mul_le_of_le_one_left (hz φ) hai)
    have hy' : |y i φ| ≤ w φ := (hy i φ).trans (mul_le_of_le_one_left (hw φ) hbi)
    change |t * x i φ + s * y i φ| ≤ 1 * (t * z φ + s * w φ)
    rw [one_mul]
    calc
      _ ≤ t * |x i φ| + s * |y i φ| := by
        simpa only [abs_mul, abs_of_nonneg ht, abs_of_nonneg hs] using
          abs_add_le (t * x i φ) (s * y i φ)
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx' ht)
        (mul_le_mul_of_nonneg_left hy' hs)

private theorem tensorBall_smul_mem (p q : Exponent) {n : ℕ}
    {x : Fin n → Free p E} (hx : x ∈ tensorBall p q n) {r : ℝ} (hr : |r| ≤ 1) :
    r • x ∈ tensorBall p q n := by
  obtain ⟨a, ha, hanorm, z, hz, hznorm, hx⟩ := hx
  refine ⟨a, ha, hanorm, z, hz, hznorm, fun i φ => ?_⟩
  change |r * x i φ| ≤ a i * z φ
  rw [abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) hr).trans (hx i φ)

private theorem tensorBall_normalize (p q : Exponent) {n : ℕ}
    (x : Fin n → Free p E) (a : Fin n → ℝ) (z : Free p E)
    (ha : ∀ i, 0 ≤ a i) (hz : 0 ≤ z) (hx : ∀ i, |x i| ≤ a i • z)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hanorm : scalarPSum q a ≤ A) (hznorm : ‖z‖ ≤ D) :
    (A * D)⁻¹ • x ∈ tensorBall p q n := by
  refine ⟨fun i => A⁻¹ * a i, fun i => mul_nonneg (inv_nonneg.mpr hA.le) (ha i),
    ?_, D⁻¹ • z, smul_nonneg (inv_nonneg.mpr hD.le) hz, ?_, ?_⟩
  · rw [scalarPSum_smul, abs_of_pos (inv_pos.mpr hA)]
    exact (mul_le_mul_of_nonneg_left hanorm (inv_nonneg.mpr hA.le)).trans_eq
      (inv_mul_cancel₀ hA.ne')
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hD)]
    exact (mul_le_mul_of_nonneg_left hznorm (inv_nonneg.mpr hD.le)).trans_eq
      (inv_mul_cancel₀ hD.ne')
  · intro i φ
    change |(A * D)⁻¹ * x i φ| ≤ (A⁻¹ * a i) * (D⁻¹ * z φ)
    rw [abs_mul, abs_of_pos (inv_pos.mpr (mul_pos hA hD))]
    calc
      _ ≤ (A * D)⁻¹ * (a i * z φ) :=
        mul_le_mul_of_nonneg_left (hx i φ) (inv_nonneg.mpr (mul_pos hA hD).le)
      _ = _ := by rw [mul_inv]; ring

private theorem tensorBall_absorbent (p q : Exponent) (n : ℕ) :
    Absorbent ℝ (tensorBall (E := E) p q n) := by
  intro x
  let z : Free p E := ∑ i, |x i|
  have hz : 0 ≤ z := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hx (i : Fin n) : |x i| ≤ (1 : ℝ) • z := by
    simpa only [one_smul] using Finset.single_le_sum
      (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
  let A := scalarPSum q (fun _ : Fin n => (1 : ℝ)) + 1
  let D := ‖z‖ + 1
  have hA : 0 < A := add_pos_of_nonneg_of_pos (scalarPSum_nonneg _ _) zero_lt_one
  have hD : 0 < D := add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
  have hm := tensorBall_normalize p q x (fun _ => 1) z (fun _ => zero_le_one) hz hx hA hD
    (le_add_of_nonneg_right zero_le_one) (le_add_of_nonneg_right zero_le_one)
  apply Absorbs.of_norm
  refine ⟨A * D, fun r hr => ?_⟩
  intro y hy
  have hy' : y = x := Set.mem_singleton_iff.mp hy
  subst y
  have hr0 : r ≠ 0 := norm_pos_iff.mp ((mul_pos hA hD).trans_le hr)
  refine ⟨r⁻¹ • x, ?_, by simp [hr0]⟩
  have hscale : |(A * D) / r| ≤ 1 := by
    rw [abs_div, abs_of_pos (mul_pos hA hD)]
    exact (div_le_one (abs_pos.mpr hr0)).mpr hr
  have hh := tensorBall_smul_mem p q hm hscale
  have heq : (A * D / r) * (A * D)⁻¹ = r⁻¹ := by
    field_simp
  simpa only [smul_smul, heq] using hh

private theorem tensorGauge_le (p q : Exponent) {n : ℕ}
    (x : Fin n → Free p E) (a : Fin n → ℝ) (z : Free p E)
    (ha : ∀ i, 0 ≤ a i) (hz : 0 ≤ z) (hx : ∀ i, |x i| ≤ a i • z) :
    gauge (tensorBall p q n) x ≤ scalarPSum q a * ‖z‖ := by
  have happrox (ε : ℝ) (hε : 0 < ε) :
      gauge (tensorBall p q n) x ≤ (scalarPSum q a + ε) * (‖z‖ + ε) := by
    have hA := add_pos_of_nonneg_of_pos (scalarPSum_nonneg q a) hε
    have hD := add_pos_of_nonneg_of_pos (norm_nonneg z) hε
    apply gauge_le_of_mem (mul_pos hA hD).le
    exact ⟨_, tensorBall_normalize p q x a z ha hz hx hA hD
      (le_add_of_nonneg_right hε.le) (le_add_of_nonneg_right hε.le),
      by simp only [smul_smul, mul_inv_cancel₀ (mul_pos hA hD).ne', one_smul]⟩
  have hlim : Filter.Tendsto (fun ε : ℝ => (scalarPSum q a + ε) * (‖z‖ + ε))
      (𝓝[>] 0) (𝓝 (scalarPSum q a * ‖z‖)) := by
    have hc : Continuous (fun ε : ℝ => (scalarPSum q a + ε) * (‖z‖ + ε)) := by fun_prop
    simpa only [add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact happrox ε hε

private theorem tensorGauge_rankOne (p q : Exponent) {n : ℕ}
    (a : Fin n → ℝ) (z : Free p E) :
    gauge (tensorBall p q n) (fun i => a i • z) ≤ scalarPSum q a * ‖z‖ := by
  have h := tensorGauge_le p q (fun i => a i • z) (fun i => |a i|) |z|
    (fun i => abs_nonneg _) (abs_nonneg _) (fun i => by
      intro φ
      change |a i * z φ| ≤ |a i| * |z φ|
      exact (abs_mul _ _).le)
  simpa only [scalarPSum_abs, norm_abs_eq_norm] using h

private theorem extend_tensorGauge (p q : Exponent) {n : ℕ}
    (hc : Convex ℝ (tensorBall (E := E) p q n))
    (W : Submodule ℝ (Fin n → Free p E)) (l : W →ₗ[ℝ] ℝ) {D : ℝ} (hD : 0 < D)
    (hl : ∀ x : W, (x : Fin n → Free p E) ∈ tensorBall p q n → l x ≤ D) :
    ∃ G : (Fin n → Free p E) →ₗ[ℝ] ℝ,
      (∀ x : W, G x = l x) ∧ ∀ x, G x ≤ D * gauge (tensorBall p q n) x := by
  have hbound (x : W) : l x ≤ D * gauge (tensorBall p q n) (x : Fin n → Free p E) := by
    suffices h : l x / D ≤ gauge (tensorBall p q n) (x : Fin n → Free p E) by
      simpa only [mul_comm] using (div_le_iff₀ hD).mp h
    rw [gauge_def]
    apply le_csInf ((tensorBall_absorbent p q n).gauge_set_nonempty)
    rintro r ⟨hr, hxr⟩
    have hh := hl (r⁻¹ • x) ((mem_smul_set_iff_inv_smul_mem₀ hr.ne' _ _).mp hxr)
    rw [map_smul, smul_eq_mul] at hh
    apply (div_le_iff₀ hD).mpr
    have hh' := mul_le_mul_of_nonneg_left hh hr.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] using hh'
  apply exists_extension_of_le_sublinear (⟨W, l⟩ : (Fin n → Free p E) →ₗ.[ℝ] ℝ)
    (fun x => D * gauge (tensorBall p q n) x)
  · intro r hr x
    rw [gauge_smul_of_nonneg hr.le, smul_eq_mul]
    ring
  · intro x y
    exact (mul_le_mul_of_nonneg_left
      (gauge_add_le hc (tensorBall_absorbent p q n) x y) hD.le).trans_eq (mul_add ..)
  · exact hbound

/-- Hölder conjugacy of convexity exponents, including the pair one and infinity. -/
def Conjugate (p q : Exponent) : Prop :=
  (p = Exponent.one ∧ q = Exponent.infinity) ∨
    (p.IsFinite ∧ q.IsFinite ∧ p.1.toReal.HolderConjugate q.1.toReal)

private theorem exists_conjugate (p : Exponent) (hp : p.IsFinite) :
    ∃ q, Conjugate p q := by
  by_cases h : p = Exponent.one
  · exact ⟨Exponent.infinity, Or.inl ⟨h, rfl⟩⟩
  have hp1 : 1 < p.1 := lt_of_le_of_ne p.2 (fun heq => h (Subtype.ext heq.symm))
  have hp1' : 1 < p.1.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hp)).mpr hp1
  have hc := Real.HolderConjugate.conjExponent hp1'
  let q : Exponent := ⟨ENNReal.ofReal p.1.toReal.conjExponent,
    ENNReal.one_le_ofReal.mpr (Real.holderConjugate_iff.mp hc.symm).1.le⟩
  refine ⟨q, Or.inr ⟨hp, ENNReal.ofReal_lt_top, ?_⟩⟩
  simpa only [q, ENNReal.toReal_ofReal hc.symm.nonneg] using hc

private theorem tensorBall_convex (p q : Exponent) (hpq : Conjugate p q) (n : ℕ) :
    Convex ℝ (tensorBall (E := E) p q n) := by
  rcases hpq with ⟨rfl, rfl⟩ | ⟨hp, hq, hpq⟩
  · exact tensorBall_convex_infinity _ _
  · exact tensorBall_convex_finite p q hp hq hpq n

private theorem sum_mul_le (p q : Exponent) (hpq : Conjugate p q)
    {n : ℕ} (a b : Fin n → ℝ) :
    ∑ i, a i * b i ≤ scalarPSum q a * scalarPSum p b := by
  rcases hpq with ⟨rfl, rfl⟩ | ⟨hp, hq, hpq⟩
  · calc
      _ ≤ ∑ i, scalarPSum Exponent.infinity a * |b i| := by
        apply Finset.sum_le_sum
        intro i _
        exact (le_abs_self _).trans ((abs_mul _ _).le.trans
          (mul_le_mul_of_nonneg_right (scalarPSum_coord_le _ _ i) (abs_nonneg _)))
      _ = _ := by simp [scalarPSum, Exponent.one, Finset.mul_sum]
  · simpa only [scalarPSum, ite_eq_right (ne_of_lt hp), ite_eq_right (ne_of_lt hq)] using
      Real.inner_le_Lp_mul_Lq Finset.univ a b hpq.symm

private theorem exists_norming (p q : Exponent) (hpq : Conjugate p q)
    {n : ℕ} (b : Fin n → ℝ) :
    ∃ a : Fin n → ℝ, scalarPSum q a ≤ 1 ∧ ∑ i, a i * b i = scalarPSum p b := by
  classical
  rcases hpq with ⟨rfl, rfl⟩ | ⟨hp, hq, hpq⟩
  · refine ⟨fun i => if 0 ≤ b i then 1 else -1, ?_, ?_⟩
    · apply (scalarPSum_mono_abs _ _ (fun _ => 1) (fun i => ?_)).trans
        (scalarPSum_infinity_one_le n)
      split_ifs <;> norm_num
    · simp only [scalarPSum, Exponent.one]
      norm_num only [ENNReal.one_ne_top, ite_false, ENNReal.toReal_one, div_one, Real.rpow_one]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with hi
      · simp [abs_of_nonneg hi]
      · simp [abs_of_neg (lt_of_not_ge hi)]
  · obtain ⟨g, hg, heq⟩ := (NNReal.isGreatest_Lp Finset.univ
      (fun i => (⟨|b i|, abs_nonneg _⟩ : ℝ≥0)) hpq).1
    have habs (i : Fin n) :
        |if 0 ≤ b i then (g i : ℝ) else -(g i : ℝ)| = g i := by
      split_ifs <;> simp only [abs_neg, abs_of_nonneg (g i).coe_nonneg]
    refine ⟨fun i => if 0 ≤ b i then (g i : ℝ) else -(g i : ℝ), ?_, ?_⟩
    · apply (Real.rpow_le_rpow_iff (scalarPSum_nonneg _ _) zero_le_one hpq.symm.pos).mp
      rw [scalarPSum_rpow q hq, Real.one_rpow]
      simp_rw [habs]
      exact_mod_cast hg
    · have heq' : ∑ i, |b i| * (g i : ℝ) = scalarPSum p b := by
        have hh := congrArg ((↑) : ℝ≥0 → ℝ) heq
        simp only [NNReal.coe_sum, NNReal.coe_rpow] at hh
        rw [scalarPSum, ite_eq_right (ne_of_lt hp)]
        exact hh
      rw [← heq']
      apply Finset.sum_congr rfl
      intro i _
      dsimp only
      split_ifs with hi
      · simp [abs_of_nonneg hi, mul_comm]
      · simp [abs_of_neg (lt_of_not_ge hi), mul_comm]

variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem sum_lift_le_of_mem_tensorBall (p q : Exponent) (hpq : Conjugate p q)
    (J : LatticeOperator (Free p F) (Free p E)) (hJ : Function.Injective J)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ f, ‖f‖ ≤ C * ‖J f‖)
    {n : ℕ} (T : LatticeOperator (Free p F) (PiLp p.1 (fun _ : Fin (n + 1) => ℝ)))
    (f : Fin (n + 1) → Free p F)
    (hf : (fun i => J (f i)) ∈ tensorBall p q (n + 1)) :
    ∑ i, T (f i) i ≤ C * ‖T.toContinuousLinearMap‖ := by
  classical
  obtain ⟨a, ha, hanorm, z, hz, hznorm, hf⟩ := hf
  let ρ : Free p F := Finset.univ.sup' Finset.univ_nonempty (fun i => (a i)⁻¹ • |f i|)
  have hρpos : 0 ≤ ρ := (smul_nonneg (inv_nonneg.mpr (ha 0)) (abs_nonneg (f 0))).trans
    (Finset.le_sup' (fun i => (a i)⁻¹ • |f i|) (Finset.mem_univ 0))
  have hJρ : J ρ ≤ z := by
    change J.toVecLatHom ρ ≤ z
    dsimp only [ρ]
    rw [map_finset_sup']
    apply Finset.sup'_le
    intro i _
    simp only [Function.comp_apply, map_smul, VecLatHom.map_abs]
    intro φ
    change (a i)⁻¹ * |J (f i) φ| ≤ z φ
    by_cases hai : a i = 0
    · simp only [hai, inv_zero, zero_mul]
      exact hz φ
    · have hh0 : |J (f i) φ| ≤ a i * z φ := hf i φ
      have hh := mul_le_mul_of_nonneg_left hh0 (inv_nonneg.mpr (ha i))
      simpa only [← mul_assoc, inv_mul_cancel₀ hai, one_mul] using hh
  have hρnorm : ‖ρ‖ ≤ C := by
    have hjpos : 0 ≤ J ρ := J.toVecLatHom.map_nonneg hρpos
    have hjnorm : ‖J ρ‖ ≤ ‖z‖ := norm_le_norm_of_abs_le_abs (by
      rw [abs_of_nonneg hjpos, abs_of_nonneg hz]
      exact hJρ)
    exact (hbound ρ).trans ((mul_le_mul_of_nonneg_left (hjnorm.trans hznorm) hC).trans_eq
      (mul_one C))
  have hfi (i : Fin (n + 1)) : |f i| ≤ a i • ρ := by
    by_cases hai : a i = 0
    · apply J.toVecLatHom.le_of_map_le hJ
      rw [map_smul, VecLatHom.map_abs, hai, zero_smul]
      have hh : |J (f i)| ≤ 0 := by simpa only [hai, zero_smul] using hf i
      exact hh
    · intro ψ
      have hh : (a i)⁻¹ * |f i ψ| ≤ ρ ψ :=
        (Finset.le_sup' (fun i => (a i)⁻¹ • |f i|) (Finset.mem_univ i)) ψ
      have hh' := mul_le_mul_of_nonneg_left hh (ha i)
      change |f i ψ| ≤ a i * ρ ψ
      simpa only [← mul_assoc, mul_inv_cancel₀ hai, one_mul] using hh'
  calc
    _ ≤ ∑ i, a i * T ρ i := by
      apply Finset.sum_le_sum
      intro i _
      have hh := T.toVecLatHom.monotone ((le_abs_self (f i)).trans (hfi i))
      rw [map_smul] at hh
      exact hh i
    _ ≤ scalarPSum q a * scalarPSum p (fun i => T ρ i) := sum_mul_le p q hpq _ _
    _ = scalarPSum q a * ‖T ρ‖ := by rw [scalarPSum_eq_piLp_norm p]
    _ ≤ ‖T ρ‖ := mul_le_of_le_one_left (norm_nonneg _) hanorm
    _ ≤ ‖T.toContinuousLinearMap‖ * ‖ρ‖ := T.toContinuousLinearMap.le_opNorm ρ
    _ ≤ ‖T.toContinuousLinearMap‖ * C := mul_le_mul_of_nonneg_left hρnorm (norm_nonneg _)
    _ = C * ‖T.toContinuousLinearMap‖ := mul_comm _ _

private theorem extend_latticeOperator_succ (p q : Exponent) (hpq : Conjugate p q)
    (J : LatticeOperator (Free p F) (Free p E)) (hJ : Function.Injective J)
    {C : ℝ} (hC : 0 < C) (hbound : ∀ f, ‖f‖ ≤ C * ‖J f‖)
    {n : ℕ} (T : LatticeOperator (Free p F) (PiLp p.1 (fun _ : Fin (n + 1) => ℝ))) :
    ∃ S : Free p E →L[ℝ] PiLp p.1 (fun _ : Fin (n + 1) => ℝ),
      S.comp J.toContinuousLinearMap = T.toContinuousLinearMap ∧
        ‖S‖ ≤ C * ‖T.toContinuousLinearMap‖ := by
  classical
  by_cases hT : T.toContinuousLinearMap = 0
  · exact ⟨0, by simp [hT], by simp [hT]⟩
  let B : (Fin (n + 1) → Free p F) →ₗ[ℝ] (Fin (n + 1) → Free p E) :=
    LinearMap.pi (fun i => J.toContinuousLinearMap.toLinearMap.comp (LinearMap.proj i))
  have hB : Function.Injective B := by
    intro f g hfg
    funext i
    exact hJ (congrFun hfg i)
  let e := LinearEquiv.ofInjective B hB
  let τ : (Fin (n + 1) → Free p F) →ₗ[ℝ] ℝ :=
    ∑ i, (PiLp.proj p.1 (fun _ : Fin (n + 1) => ℝ) i).toLinearMap.comp
      (T.toContinuousLinearMap.toLinearMap.comp (LinearMap.proj i))
  have hτ (f : Fin (n + 1) → Free p F) : τ f = ∑ i, T (f i) i := by
    simp [τ]
  let l : B.range →ₗ[ℝ] ℝ := τ.comp e.symm.toLinearMap
  have hD : 0 < C * ‖T.toContinuousLinearMap‖ := mul_pos hC (norm_pos_iff.mpr hT)
  obtain ⟨G, hG, hGbound⟩ := extend_tensorGauge p q (tensorBall_convex p q hpq (n + 1))
    B.range l hD (by
      intro x hx
      have heq : B (e.symm x) = (x : Fin (n + 1) → Free p E) :=
        congrArg Subtype.val (e.apply_symm_apply x)
      have hmem : (fun i => J (e.symm x i)) ∈ tensorBall p q (n + 1) := by
        change B (e.symm x) ∈ _
        rw [heq]
        exact hx
      change τ (e.symm x) ≤ _
      rw [hτ]
      exact sum_lift_le_of_mem_tensorBall p q hpq J hJ hC.le hbound T (e.symm x) hmem)
  let S₀ : Free p E →ₗ[ℝ] PiLp p.1 (fun _ : Fin (n + 1) => ℝ) :=
    (WithLp.linearEquiv p.1 ℝ (Fin (n + 1) → ℝ)).symm.toLinearMap.comp
      (LinearMap.pi (fun i => G.comp (LinearMap.single ℝ (fun _ : Fin (n + 1) => Free p E) i)))
  have hsum (a : Fin (n + 1) → ℝ) (x : Free p E) :
      ∑ i, a i * G (Pi.single i x) = G (fun i => a i • x) := by
    calc
      _ = G (∑ i, a i • Pi.single i x) := by simp [map_sum, map_smul, smul_eq_mul]
      _ = _ := congrArg G (by
        simp_rw [← Pi.single_smul]
        exact Finset.univ_sum_single _)
  have hnorm (x : Free p E) : ‖S₀ x‖ ≤ C * ‖T.toContinuousLinearMap‖ * ‖x‖ := by
    obtain ⟨a, ha, heq⟩ := exists_norming p q hpq (fun i => G (Pi.single i x))
    calc
      _ = scalarPSum p (fun i => G (Pi.single i x)) := (scalarPSum_eq_piLp_norm p _).symm
      _ = G (fun i => a i • x) := heq.symm.trans (hsum a x)
      _ ≤ C * ‖T.toContinuousLinearMap‖ * gauge (tensorBall p q (n + 1)) (fun i => a i • x) :=
        hGbound _
      _ ≤ C * ‖T.toContinuousLinearMap‖ * (scalarPSum q a * ‖x‖) :=
        mul_le_mul_of_nonneg_left (tensorGauge_rankOne p q a x) hD.le
      _ ≤ C * ‖T.toContinuousLinearMap‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg x) ha) hD.le
  let S := S₀.mkContinuous (C * ‖T.toContinuousLinearMap‖) hnorm
  refine ⟨S, ?_, S.opNorm_le_bound hD.le hnorm⟩
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro i
  change G (Pi.single i (J f)) = T f i
  have hh := hG (e (Pi.single i f))
  change G (B (Pi.single i f)) = τ (e.symm (e (Pi.single i f))) at hh
  rw [e.symm_apply_apply, hτ] at hh
  have hsingle : B (Pi.single i f) = Pi.single i (J f) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [B]
    · simp [B, Pi.single_eq_of_ne hji]
  rw [hsingle] at hh
  convert hh using 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

/-- Extend a lattice homomorphism into finite-dimensional ell-p across a bounded
lattice operator J with inverse norm bound C. The extension is a continuous linear
map on the ambient free lattice, agrees with the original map along J, and has
norm at most C times the original norm. The tensor gauge and Hahn–Banach prove
this for every finite p, including p = 1. -/
theorem extend_latticeOperator (p : Exponent) (hp : p.IsFinite)
    (J : LatticeOperator (Free p F) (Free p E))
    {C : ℝ} (hC : 0 < C) (hbound : ∀ f, ‖f‖ ≤ C * ‖J f‖)
    (n : ℕ) (T : LatticeOperator (Free p F) (PiLp p.1 (fun _ : Fin n => ℝ))) :
    ∃ S : Free p E →L[ℝ] PiLp p.1 (fun _ : Fin n => ℝ),
      S.comp J.toContinuousLinearMap = T.toContinuousLinearMap ∧
        ‖S‖ ≤ C * ‖T.toContinuousLinearMap‖ := by
  have hJ : Function.Injective J :=
    (injective_iff_map_eq_zero J.toContinuousLinearMap).mpr (by
      intro f hf
      apply norm_eq_zero.mp
      have hh := hbound f
      rw [hf, norm_zero, mul_zero] at hh
      exact le_antisymm hh (norm_nonneg f))
  cases n with
  | zero =>
    exact ⟨0, Subsingleton.elim _ _, by simp [mul_nonneg hC.le (norm_nonneg _)]⟩
  | succ n =>
    obtain ⟨q, hpq⟩ := exists_conjugate p hp
    exact extend_latticeOperator_succ p q hpq J hJ hC hbound T

/-- A lower bound `‖f‖ ≤ C * ‖induced p M.subtypeL f‖` extends every bounded linear
map from M into a finite-dimensional ell-p space to E with norm at most C times
its original norm. Lift to the free lattice, apply `extend_latticeOperator`, and
restrict to the evaluation generators. The same constant works for every dimension. -/
theorem extend_of_free_norm_bound (p : Exponent) (hp : p.IsFinite) (M : Submodule ℝ E)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ f : Free p M, ‖f‖ ≤ C * ‖induced p M.subtypeL f‖)
    (n : ℕ) (R : M →L[ℝ] PiLp p.1 (fun _ : Fin n => ℝ)) :
    ∃ S : E →L[ℝ] PiLp p.1 (fun _ : Fin n => ℝ),
      S.comp M.subtypeL = R ∧ ‖S‖ ≤ C * ‖R‖ := by
  obtain ⟨T, hT, hTnorm, _⟩ := universal_property_piLp p n R
  obtain ⟨A, hA, hAnorm⟩ := extend_latticeOperator p hp (induced p M.subtypeL) hC hbound n T
  let S : E →L[ℝ] PiLp p.1 (fun _ : Fin n => ℝ) :=
    A.comp (delta p).toContinuousLinearMap
  refine ⟨S, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    change A (delta p (M.subtypeL x)) = R x
    rw [← (induced_norm_generators p M.subtypeL).2 x]
    exact (congrArg (fun L : Free p M →L[ℝ] PiLp p.1 (fun _ : Fin n => ℝ) =>
      L (delta p x)) hA).trans (hT x)
  · apply S.opNorm_le_bound (mul_nonneg hC.le (norm_nonneg R))
    intro x
    calc
      ‖S x‖ ≤ ‖A‖ * ‖delta p x‖ := A.le_opNorm _
      _ ≤ (C * ‖T.toContinuousLinearMap‖) * ‖x‖ := by
        rw [(delta p).norm_map]
        exact mul_le_mul_of_nonneg_right hAnorm (norm_nonneg x)
      _ ≤ (C * ‖R‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTnorm hC.le) (norm_nonneg x)

end FBLOrderContinuousLH.FiniteLpExtension
