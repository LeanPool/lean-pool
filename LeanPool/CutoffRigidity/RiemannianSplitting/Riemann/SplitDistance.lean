/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitIsometry
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianTangentMetricMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-! # The distance identity `d(x,y)² = |s(x)-s(y)|² + d(π x, π y)²` -/

@[expose] public section

open Bundle MeasureTheory Set Filter Manifold
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace CutCur

theorem sq_le_of_forall_unit {P D L : ℝ≥0∞} (hL : L ≠ ⊤)
    (h : ∀ α β : ℝ≥0, α ^ 2 + β ^ 2 = 1 → (α : ℝ≥0∞) * P + β * D ≤ L) :
    P ^ 2 + D ^ 2 ≤ L ^ 2 := by
  have hP : P ≤ L := by simpa using h 1 0 (by norm_num)
  have hD : D ≤ L := by simpa using h 0 1 (by norm_num)
  have hP' : P ≠ ⊤ := ne_top_of_le_ne_top hL hP
  have hD' : D ≠ ⊤ := ne_top_of_le_ne_top hL hD
  lift P to ℝ≥0 using hP'
  lift D to ℝ≥0 using hD'
  lift L to ℝ≥0 using hL
  rw [← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_add,
      ENNReal.coe_le_coe]
  by_cases h0 : P ^ 2 + D ^ 2 = 0
  · rw [h0]; exact bot_le
  set R := NNReal.sqrt (P ^ 2 + D ^ 2) with hR
  have hR2 : R ^ 2 = P ^ 2 + D ^ 2 := NNReal.sq_sqrt _
  have hRpos : 0 < R := by
    rcases (bot_le : (0:ℝ≥0) ≤ R).eq_or_lt with h' | h'
    · exfalso; apply h0; rw [← hR2, ← h']; simp
    · exact h'
  have h1 := h (P / R) (D / R) (by
    rw [div_pow, div_pow, ← add_div, ← hR2, div_self (pow_ne_zero 2 hRpos.ne')])
  rw [← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_add, ENNReal.coe_le_coe] at h1
  have h2 : P / R * P + D / R * D = R := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← sq, ← sq, ← hR2, sq, mul_div_assoc,
      div_self hRpos.ne', mul_one]
  rw [h2] at h1
  rw [← hR2]
  exact pow_le_pow_left₀ bot_le h1 2
theorem le_sq_of_forall_gt {c b : ℝ≥0∞} (h : ∀ r, b < r → c ≤ r ^ 2) : c ≤ b ^ 2 := by
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp
  by_contra hlt
  rw [not_le] at hlt
  have hcont : ContinuousAt (fun r : ℝ≥0∞ => r ^ 2) b := (ENNReal.continuous_pow 2).continuousAt
  have h1 : ∀ᶠ r in 𝓝 b, r ^ 2 < c := hcont.eventually (gt_mem_nhds hlt)
  have : (𝓝[>] b).NeBot := nhdsGT_neBot_of_exists_gt ⟨⊤, hb.lt_top⟩
  have h2 : ∀ᶠ r in 𝓝[>] b, r ^ 2 < c ∧ b < r :=
    (eventually_nhdsWithin_of_eventually_nhds h1).and self_mem_nhdsWithin
  obtain ⟨r, hr1, hr2⟩ := h2.exists
  exact absurd (h r hr2) (not_le.mpr hr1)

section
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

omit [FiniteDimensional ℝ F] in
theorem continuous_norm_mfderiv_curve {σ : ℝ → M} (hσ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 σ) :
    Continuous fun τ => ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) σ τ 1‖ := by
  let : IsContinuousRiemannianBundle F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := 𝓘(ℝ, F)) (n := ∞)
  exact continuousOn_univ.mp (hσ.contMDiffOn.continuousOn_norm_mfderiv le_rfl isOpen_univ 1)

end

namespace Frame

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] {k : ℕ} (fr : Frame F M k)

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem deriv_curve_sv {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 γ) (τ : ℝ) :
    deriv (fun τ => fr.sv (γ τ)) τ = fr.dsv (γ τ) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1) := by
  have h := mfderiv_comp τ (fr.mdiff_sv (γ τ)) ((hγ.mdifferentiable one_ne_zero) τ)
  have h2 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (fun τ => fr.sv (γ τ)) τ 1 =
      fr.dsv (γ τ) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1) := congrArg (fun L => L 1) h
  have h3 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (fun τ => fr.sv (γ τ)) τ =
      fderiv ℝ (fun τ => fr.sv (γ τ)) τ := mfderiv_eq_fderiv
  rw [h3] at h2
  rw [deriv]
  exact h2

theorem mfderiv_curve_retr {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 γ) (τ : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun τ => fr.retr (γ τ)) τ 1 =
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr (γ τ) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1) := by
  have h := mfderiv_comp τ (fr.contMDiff_retr_mdiff (γ τ)) ((hγ.mdifferentiable one_ne_zero) τ)
  exact congrArg (fun L => L 1) h

theorem norm_sq_curve {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 γ) (τ : ℝ) :
    ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1‖ ^ 2 =
      ‖deriv (fun τ => fr.sv (γ τ)) τ‖ ^ 2 +
      ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun τ => fr.retr (γ τ)) τ 1‖ ^ 2 := by
  rw [fr.deriv_curve_sv hγ, fr.mfderiv_curve_retr hγ]
  exact fr.norm_sq_split (γ τ) _

/-- Pointwise Cauchy–Schwarz for the Pythagorean splitting of the speed. -/
theorem enorm_curve_ge {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 γ) (τ : ℝ) (α β : ℝ≥0)
    (hαβ : α ^ 2 + β ^ 2 = 1) :
    (α : ℝ≥0∞) * ‖deriv (fun τ => fr.sv (γ τ)) τ‖ₑ +
      β * ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun τ => fr.retr (γ τ)) τ 1‖ₑ ≤
      ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1‖ₑ := by
  set a := ‖deriv (fun τ => fr.sv (γ τ)) τ‖ with ha
  set b := ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun τ => fr.retr (γ τ)) τ 1‖ with hb
  set v := ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1‖ with hv
  have hsq : v ^ 2 = a ^ 2 + b ^ 2 := fr.norm_sq_curve hγ τ
  have hαβ' : (α : ℝ) ^ 2 + (β : ℝ) ^ 2 = 1 := by exact_mod_cast hαβ
  have hreal : (α : ℝ) * a + β * b ≤ v := by
    have h1 : ((α : ℝ) * a + β * b) ^ 2 ≤ v ^ 2 := by
      rw [hsq]
      nlinarith [sq_nonneg ((α : ℝ) * b - β * a)]
    exact le_of_sq_le_sq h1 (norm_nonneg _) |>.trans (le_refl _)
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm]
  rw [← ENNReal.ofReal_coe_nnreal (p := α), ← ENNReal.ofReal_coe_nnreal (p := β)]
  rw [← ENNReal.ofReal_mul α.coe_nonneg, ← ENNReal.ofReal_mul β.coe_nonneg,
    ← ENNReal.ofReal_add (mul_nonneg α.coe_nonneg (norm_nonneg _))
      (mul_nonneg β.coe_nonneg (norm_nonneg _))]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Lower bound for the squared distance. -/
theorem edist_ge {x y : M} {r : ℝ≥0∞} (hr : edist x y < r) :
    edist (fr.sv x) (fr.sv y) ^ 2 + edist (fr.retr x) (fr.retr y) ^ 2 ≤ r ^ 2 := by
  rcases eq_or_ne r ⊤ with rfl | hrtop
  · simp
  have hr' : riemannianEDist 𝓘(ℝ, F) x y < r := by
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, F)) x y]; exact hr
  obtain ⟨γ, hγx, hγy, hγ, hlen, -, -⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hr' zero_lt_one
  have hL : pathELength 𝓘(ℝ, F) γ 0 1 ≠ ⊤ := (hlen.trans hrtop.lt_top).ne
  refine (sq_le_of_forall_unit hL ?_).trans (pow_le_pow_left' hlen.le 2)
  intro α β hαβ
  -- the two curves
  have hT : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 1 (fun τ => fr.sv (γ τ)) :=
    (fr.contMDiff_sv.of_le (by simp)).comp hγ
  have hY : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 (fun τ => fr.retr (γ τ)) :=
    (fr.contMDiff_retr.of_le (by simp)).comp hγ
  have hTd : ContDiff ℝ 1 (fun τ => fr.sv (γ τ)) := contMDiff_iff_contDiff.mp hT
  have hP : edist (fr.sv x) (fr.sv y) ≤
      ∫⁻ τ in Icc (0 : ℝ) 1, ‖deriv (fun τ => fr.sv (γ τ)) τ‖ₑ := by
    have := eNorm_sub_le_lintegral_deriv_of_contDiffOn_Icc (a := 0) (b := 1)
      (f := fun τ => fr.sv (γ τ)) hTd.contDiffOn
    simp only [hγx, hγy] at this
    rw [edist_comm, eDist_eq_eNorm_sub]
    exact this zero_le_one
  have hD : edist (fr.retr x) (fr.retr y) ≤ pathELength 𝓘(ℝ, F) (fun τ => fr.retr (γ τ)) 0 1 := by
    rw [IsRiemannianManifold.out (I := 𝓘(ℝ, F)) (fr.retr x) (fr.retr y)]
    apply riemannianEDist_le_pathELength hY.contMDiffOn
    · simp [hγx]
    · simp [hγy]
    · exact zero_le_one
  rw [pathELength_eq_lintegral_mfderiv_Icc] at hD ⊢
  set A : ℝ≥0∞ := ∫⁻ τ in Icc (0 : ℝ) 1, ‖deriv (fun τ => fr.sv (γ τ)) τ‖ₑ with hA
  set B : ℝ≥0∞ := ∫⁻ τ in Icc (0 : ℝ) 1,
    ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun τ => fr.retr (γ τ)) τ 1‖ₑ with hB
  have h1 : (α : ℝ≥0∞) * A + β * B ≤
      ∫⁻ τ in Icc (0 : ℝ) 1, ((α : ℝ≥0∞) * ‖deriv (fun τ => fr.sv (γ τ)) τ‖ₑ +
        β * ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun τ => fr.retr (γ τ)) τ 1‖ₑ) := by
    calc (α : ℝ≥0∞) * A + β * B
        = (∫⁻ τ in Icc (0 : ℝ) 1, (α : ℝ≥0∞) * ‖deriv (fun τ => fr.sv (γ τ)) τ‖ₑ) +
          ∫⁻ τ in Icc (0 : ℝ) 1, (β : ℝ≥0∞) *
            ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun τ => fr.retr (γ τ)) τ 1‖ₑ := by
          rw [hA, hB, lintegral_const_mul' _ _ ENNReal.coe_ne_top,
            lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      _ ≤ _ := le_lintegral_add _ _
  calc (α : ℝ≥0∞) * edist (fr.sv x) (fr.sv y) + β * edist (fr.retr x) (fr.retr y)
      ≤ (α : ℝ≥0∞) * A + β * B :=
        add_le_add (mul_le_mul' le_rfl hP) (mul_le_mul' le_rfl hD)
    _ ≤ _ := h1
    _ ≤ _ := lintegral_mono fun τ => fr.enorm_curve_ge hγ τ α β hαβ

/-- Upper bound for the distance, from near-optimal paths in the level. -/
theorem edist_le_aux {x y : M} {r : ℝ≥0∞} (hr : edist (fr.retr x) (fr.retr y) < r)
    (hrtop : r ≠ ⊤) {θ : ℝ} (hθ : 0 < θ) :
    edist x y ≤ ENNReal.ofReal (Real.sqrt (‖fr.sv x - fr.sv y‖ ^ 2 + (r.toReal + θ) ^ 2)) := by
  have hr' : riemannianEDist 𝓘(ℝ, F) (fr.retr x) (fr.retr y) < r := by
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, F)) (fr.retr x) (fr.retr y)]; exact hr
  obtain ⟨c, hcx, hcy, hc, hlen, -, -⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hr' zero_lt_one
  -- the projected path
  set c' : ℝ → M := fun τ => fr.retr (c τ) with hc'
  have hc'1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 c' := (fr.contMDiff_retr.of_le (by simp)).comp hc
  set g : ℝ → ℝ := fun τ => ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) c' τ 1‖ with hg
  have hgc : Continuous g := continuous_norm_mfderiv_curve hc'1
  have hg0 : ∀ τ, 0 ≤ g τ := fun τ => norm_nonneg _
  set ℓ : ℝ := ∫ τ in (0 : ℝ)..1, g τ with hℓ
  have hℓ0 : 0 ≤ ℓ := intervalIntegral.integral_nonneg zero_le_one (fun τ _ => hg0 τ)
  -- length of the projected path is bounded by that of `c`
  have hℓr : ℓ ≤ r.toReal := by
    have hN : ∀ (z : M) (v : TangentSpace 𝓘(ℝ, F) z),
        ‖mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr z v‖ ≤ ‖v‖ := by
      intro z v
      have h := fr.norm_sq_split z v
      nlinarith [norm_nonneg (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr z v), norm_nonneg v,
        sq_nonneg ‖fr.dsv z v‖]
    have h1 : pathELength 𝓘(ℝ, F) c' 0 1 ≤ pathELength 𝓘(ℝ, F) c 0 1 :=
      CutoffRigidity.pathELength_comp_le_of_norm_mfderiv_le_between
        (fr.contMDiff_retr.of_le (by simp)) hN hc 0 1
    have hint : IntegrableOn g (Icc (0 : ℝ) 1) := hgc.integrableOn_Icc
    have h2 : ENNReal.ofReal ℓ = pathELength 𝓘(ℝ, F) c' 0 1 := by
      rw [pathELength_eq_lintegral_mfderiv_Icc, hℓ, intervalIntegral.integral_of_le zero_le_one,
        ← integral_Icc_eq_integral_Ioc, ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall hg0)]
      congr 1
      funext τ
      rw [hg, ofReal_norm]
    rw [← ENNReal.ofReal_le_iff_le_toReal hrtop, h2]
    exact (h1.trans hlen.le)
  set p : ℝ := ‖fr.sv x - fr.sv y‖ with hp
  set S : ℝ := Real.sqrt (p ^ 2 + (ℓ + θ) ^ 2) with hS
  set Δ : EuclideanSpace ℝ (Fin k) := fr.sv y - fr.sv x with hΔ
  have hΔn : ‖Δ‖ = p := by rw [hΔ, hp, norm_sub_rev]
  have hℓθ : 0 < ℓ + θ := by linarith
  set Gint : ℝ → ℝ := fun τ => ∫ s in (0 : ℝ)..τ, g s with hGint
  have hGd : ∀ τ, HasDerivAt Gint (g τ) τ := fun τ =>
    (hgc.integral_hasStrictDerivAt 0 τ).hasDerivAt
  set lam : ℝ → ℝ := fun τ => (Gint τ + θ * τ) / (ℓ + θ) with hlam
  have hlamd : ∀ τ, HasDerivAt lam ((g τ + θ) / (ℓ + θ)) τ := by
    intro τ
    have h1 := ((hGd τ).add ((hasDerivAt_id τ).const_mul θ)).div_const (ℓ + θ)
    simpa using h1
  have hlam0 : lam 0 = 0 := by simp [hlam, hGint]
  have hlam1 : lam 1 = 1 := by
    simp only [hlam, hGint, ← hℓ]
    field_simp
  set t : ℝ → EuclideanSpace ℝ (Fin k) := fun τ => fr.sv x + lam τ • Δ with ht
  have htd : ∀ τ, HasDerivAt t (((g τ + θ) / (ℓ + θ)) • Δ) τ := by
    intro τ
    exact ((hlamd τ).smul_const Δ).const_add (fr.sv x)
  have ht1 : ContDiff ℝ 1 t := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun τ => (htd τ).differentiableAt, ?_⟩
    have : deriv t = fun τ => ((g τ + θ) / (ℓ + θ)) • Δ := funext fun τ => (htd τ).deriv
    rw [this]
    exact ((hgc.add continuous_const).div_const _).smul continuous_const
  have ht1m : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 1 t := ht1.contMDiff
  set γt : ℝ → M := fun τ => fr.comp (List.finRange k) (t τ) (c' τ) with hγt
  have hγt1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 γt :=
    ((fr.contMDiff_comp (List.finRange k)).of_le (by simp)).comp (ht1m.prodMk hc'1)
  have hγ0 : γt 0 = x := by
    have h1 : c' 0 = fr.retr x := by
      simp only [hc', hcx]
      exact fr.retr_of_level (fr.sv_retr x)
    simp only [hγt, ht, hlam0, h1, zero_smul, add_zero]
    exact fr.comp_retr x
  have hγ1 : γt 1 = y := by
    have h1 : c' 1 = fr.retr y := by
      simp only [hc', hcy]
      exact fr.retr_of_level (fr.sv_retr y)
    simp only [hγt, ht, hlam1, h1, one_smul, hΔ, add_sub_cancel]
    exact fr.comp_retr y
  have hnorm : ∀ τ, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γt τ 1‖ ^ 2 = ‖deriv t τ‖ ^ 2 + g τ ^ 2 := by
    intro τ
    have hΓ : MDifferentiableAt (𝓘(ℝ, EuclideanSpace ℝ (Fin k)).prod 𝓘(ℝ, F)) 𝓘(ℝ, F)
        (fun p : EuclideanSpace ℝ (Fin k) × M => fr.comp (List.finRange k) p.1 p.2) (t τ, c' τ) :=
      ((fr.contMDiff_comp (List.finRange k)).mdifferentiable (by simp)) _
    have htm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) t τ :=
      (ht1m.mdifferentiable one_ne_zero) τ
    have hcm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) c' τ := (hc'1.mdifferentiable one_ne_zero) τ
    have hpair := htm.prodMk hcm
    have h1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γt τ =
        (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin k)).prod 𝓘(ℝ, F)) 𝓘(ℝ, F)
          (fun p : EuclideanSpace ℝ (Fin k) × M => fr.comp (List.finRange k) p.1 p.2)
          (t τ, c' τ)).comp
          (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, EuclideanSpace ℝ (Fin k)).prod 𝓘(ℝ, F))
            (fun τ => (t τ, c' τ)) τ) := mfderiv_comp τ hΓ hpair
    have h2 := mfderiv_prodMk htm hcm
    have h3 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) t τ 1 = deriv t τ := by
      have : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) t τ = fderiv ℝ t τ :=
        mfderiv_eq_fderiv
      rw [this, deriv]
      rfl
    have h4 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γt τ 1 =
        mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin k)).prod 𝓘(ℝ, F)) 𝓘(ℝ, F)
          (fun p : EuclideanSpace ℝ (Fin k) × M => fr.comp (List.finRange k) p.1 p.2)
          (t τ, c' τ) (deriv t τ, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) c' τ 1) := by
      rw [h1, h2, ← h3]
      rfl
    have h5 := fr.mfderiv_comp_joint (List.finRange k) (t τ) (c' τ) (deriv t τ)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) c' τ 1)
    have hu : ∀ i, inner ℝ (fr.X i (c' τ)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) c' τ 1) = 0 := by
      intro i
      rw [hc', fr.mfderiv_curve_retr hc τ]
      exact fr.inner_X_dretr i (c τ) _
    have h6 := fr.norm_sq_action (t τ) (c' τ) (deriv t τ) _ hu
    rw [h4, h5]
    rw [← Fin.sum_univ_def]
    exact h6
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  set lam' : ℝ → ℝ := fun τ => (g τ + θ) / (ℓ + θ) with hlam'
  have hlam'0 : ∀ τ, 0 ≤ lam' τ := fun τ => div_nonneg (by linarith [hg0 τ]) hℓθ.le
  have hlam'c : Continuous lam' := (hgc.add continuous_const).div_const _
  have hpt : ∀ τ, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γt τ 1‖ ≤ lam' τ * S := by
    intro τ
    have hdt : deriv t τ = lam' τ • Δ := (htd τ).deriv
    have hn : ‖deriv t τ‖ = lam' τ * p := by
      rw [hdt, norm_smul, hΔn, Real.norm_of_nonneg (hlam'0 τ)]
    have hkey : lam' τ * (ℓ + θ) = g τ + θ := by
      simp only [hlam']; field_simp
    have h1 : ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γt τ 1‖ ^ 2 ≤ (lam' τ * S) ^ 2 := by
      rw [hnorm τ, hn, mul_pow, mul_pow, hS, Real.sq_sqrt (by positivity)]
      have : g τ ^ 2 ≤ (lam' τ * (ℓ + θ)) ^ 2 := by
        rw [hkey]
        nlinarith [hg0 τ]
      nlinarith [this]
    exact le_of_sq_le_sq h1 (mul_nonneg (hlam'0 τ) hS0)
  have hlen_le : pathELength 𝓘(ℝ, F) γt 0 1 ≤ ENNReal.ofReal S := by
    rw [pathELength_eq_lintegral_mfderiv_Icc]
    calc ∫⁻ τ in Icc (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γt τ 1‖ₑ
        ≤ ∫⁻ τ in Icc (0 : ℝ) 1, ENNReal.ofReal (lam' τ * S) := by
          refine lintegral_mono fun τ => ?_
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hpt τ)
      _ = ENNReal.ofReal (∫ τ in Icc (0 : ℝ) 1, lam' τ * S) := by
          exact (ofReal_integral_eq_lintegral_ofReal
            (show Continuous fun τ => lam' τ * S from hlam'c.mul continuous_const).integrableOn_Icc
            (Filter.Eventually.of_forall fun τ => mul_nonneg (hlam'0 τ) hS0)).symm
      _ = ENNReal.ofReal S := by
          congr 1
          rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
          have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
            (f := fun τ => lam τ * S) (f' := fun τ => lam' τ * S)
            (fun τ _ => (hlamd τ).mul_const S)
            ((hlam'c.mul continuous_const).intervalIntegrable _ _)
          rw [this]
          simp [hlam0, hlam1]
  have hedist : edist x y ≤ pathELength 𝓘(ℝ, F) γt 0 1 := by
    rw [IsRiemannianManifold.out (I := 𝓘(ℝ, F)) x y]
    exact riemannianEDist_le_pathELength hγt1.contMDiffOn hγ0 hγ1 zero_le_one
  refine hedist.trans (hlen_le.trans (ENNReal.ofReal_le_ofReal ?_))
  rw [hS]
  apply Real.sqrt_le_sqrt
  have : ℓ + θ ≤ r.toReal + θ := by linarith
  nlinarith [hℓθ.le]

/-- **Distance identity**: `d(x,y)² = |s(x) - s(y)|² + d(π x, π y)²`. -/
theorem edist_sq (x y : M) :
    edist x y ^ 2 = edist (fr.sv x) (fr.sv y) ^ 2 + edist (fr.retr x) (fr.retr y) ^ 2 := by
  apply le_antisymm
  · -- upper bound
    rcases eq_or_ne (edist (fr.retr x) (fr.retr y)) ⊤ with hD | hD
    · rw [hD]; simp
    set d : ℝ := (edist (fr.retr x) (fr.retr y)).toReal with hd
    set p : ℝ := ‖fr.sv x - fr.sv y‖ with hp
    have hdD : edist (fr.retr x) (fr.retr y) = ENNReal.ofReal d := by
      rw [hd, ENNReal.ofReal_toReal hD]
    have hb : ∀ δ : ℝ, 0 < δ → edist x y ≤
        ENNReal.ofReal (Real.sqrt (p ^ 2 + (d + 2 * δ) ^ 2)) := by
      intro δ hδ
      have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
      have hr : edist (fr.retr x) (fr.retr y) < ENNReal.ofReal (d + δ) := by
        rw [hdD]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
      have := fr.edist_le_aux hr ENNReal.ofReal_ne_top hδ
      rw [ENNReal.toReal_ofReal (by linarith)] at this
      convert this using 4
      ring
    have hlim : Tendsto (fun δ : ℝ => ENNReal.ofReal (Real.sqrt (p ^ 2 + (d + 2 * δ) ^ 2)))
        (𝓝[>] 0) (𝓝 (ENNReal.ofReal (Real.sqrt (p ^ 2 + d ^ 2)))) := by
      have hc : Continuous fun δ : ℝ => ENNReal.ofReal (Real.sqrt (p ^ 2 + (d + 2 * δ) ^ 2)) :=
        ENNReal.continuous_ofReal.comp (Real.continuous_sqrt.comp (by fun_prop))
      have := hc.tendsto 0
      simp only [mul_zero, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h1 : edist x y ≤ ENNReal.ofReal (Real.sqrt (p ^ 2 + d ^ 2)) :=
      ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => hb δ hδ)
    calc edist x y ^ 2 ≤ ENNReal.ofReal (Real.sqrt (p ^ 2 + d ^ 2)) ^ 2 := pow_le_pow_left' h1 2
      _ = ENNReal.ofReal (p ^ 2 + d ^ 2) := by
          rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
      _ = _ := by
          have hP : edist (fr.sv x) (fr.sv y) = ENNReal.ofReal p := by
            rw [eDist_eq_eNorm_sub, ← ofReal_norm]
          have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
          rw [hP, hdD, ENNReal.ofReal_add (sq_nonneg p) (sq_nonneg d),
            ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow hd0]
  · exact le_sq_of_forall_gt fun r hr => fr.edist_ge hr

end Frame

end CutCur
