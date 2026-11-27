/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.ZeroSet

/-!
# Quasiconvexity does not depend on the domain

For a Borel, locally bounded `f`, quasiconvexity at `A` on the unit cube is equivalent to
quasiconvexity at `A` on any nonempty bounded open set (`quasiconvexAtOn_iff`); the direction from
the cube holds on every bounded measurable set (`quasiconvexAtOn_of_unitCube`).

This is Proposition 5.11 of B. Dacorogna, *Direct Methods in the Calculus of Variations*, 2nd ed.,
Springer, 2008 ([D08], pp. 172–173), and Lemma 5.2 (i) of F. Rindler, *Calculus of Variations*, 2nd
ed., Graduate Texts in Mathematics 310, Springer, 2026 ([R2], p. 106; Lipschitz domains), with their
argument (also Remark 2 after Definition 4.2 in S. Müller, *Variational models for microstructure
and phase transitions*, lecture notes, MPI MiS Leipzig, 1998): extend the test map by zero, put a
translated and scaled copy of its domain inside the other domain, and compute the energy of the
copy, the rest contributing `f (A)` times its measure. Here the unit cube is the intermediate
domain.

The computation uses that the gradient of the extended map vanishes almost everywhere outside the
domain of the test map. In [D08] this is immediate, since `W^{1,∞}_0 (E)` is there
`W^{1,∞} (E) ∩ W^{1,1}_0 (E)` (Definition 12.9 (iv)), and in [R2] and Müller because the domains are
Lipschitz, respectively `|∂U| = 0`. For the test maps of this package (Lipschitz, vanishing outside
the domain) on an arbitrary bounded open set it is the vanishing of the gradient of a Lipschitz map
almost everywhere on its zero set (`Lipschitz.ZeroSet`). [D08] does not say that the first domain is
nonempty; for the empty set the proposition is false (its hypothesis is void).
-/

@[expose] public section

open Metric Set MeasureTheory Filter Topology
open scoped Pointwise

namespace CalculusOfVariations

variable {d m : ℕ}

/-- **From the cube to any bounded set**: quasiconvexity at `A` on the unit cube gives it on
every bounded measurable `Ω` (in particular on every bounded open set). Put `Ω` in a cube
`Q_R = x₀ + R (0, 1)^m`; a test map `φ` on `Ω`, rescaled to the unit cube, gives
`R^m f (A) ≤ ∫_{Q_R} f (A + ∇φ)`; on `Q_R ∖ Ω` the map vanishes, so its gradient vanishes almost
everywhere (`rd_ae_grad_eq_zero`), and the inequality becomes `|Ω| f (A) ≤ ∫_Ω f (A + ∇φ)`. -/
theorem quasiconvexAtOn_of_unitCube {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : Measurable f) (hbdd : IsLocallyBounded f) {A : Matrix (Fin d) (Fin m) ℝ}
    {Ω : Set (Fin m → ℝ)} (hb : Bornology.IsBounded Ω) (hΩm : MeasurableSet Ω)
    (h : QuasiconvexAtOn (unitCube m) f A) : QuasiconvexAtOn Ω f A := by
  intro φ K hφ h0 _
  obtain ⟨ρ, hρ⟩ := hb.subset_closedBall 0
  set a : ℝ := |ρ| + 1 with ha_def
  have ha : 1 ≤ a := by have := abs_nonneg ρ; linarith
  set R : ℝ := 2 * a with hR_def
  have hR : 0 < R := by linarith
  set x₀ : Fin m → ℝ := fun _ => -a
  set T : (Fin m → ℝ) → Fin m → ℝ := fun y => x₀ + R • y
  set ψ : (Fin m → ℝ) → Fin d → ℝ := fun y => R⁻¹ • φ (T y)
  have hT : LipschitzWith ‖R‖₊ T := LipschitzWith.of_dist_le_mul fun y z => by
    simp only [T, dist_add_left]; exact (lipschitzWith_smul R).dist_le_mul y z
  have hψ : LipschitzWith (‖R⁻¹‖₊ * (K * ‖R‖₊)) ψ := (lipschitzWith_smul R⁻¹).comp (hφ.comp hT)
  have hent : ∀ x ∈ Ω, ∀ i, |x i| ≤ ρ := fun x hx i => by
    have := hρ hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm x i).trans this
  have hρa : ρ ≤ a - 1 := by rw [ha_def]; linarith [le_abs_self ρ]
  have hTΩ : ∀ y, T y ∈ Ω → y ∈ unitCube m := by
    intro y hy i _
    have := abs_le.1 (hent _ hy i)
    simp only [T, x₀, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    constructor
    · by_contra hneg; push Not at hneg; nlinarith
    · by_contra hneg; push Not at hneg; nlinarith
  have hψ0 : ∀ y ∉ unitCube m, ψ y = 0 := fun y hy => by
    simp only [ψ, h0 _ fun h => hy (hTΩ y h), smul_zero]
  have hgrad : ∀ y, grad ψ y = grad φ (T y) := by
    intro y
    ext i k
    simp only [grad, Matrix.of_apply, ψ, T, Pi.smul_apply, smul_eq_mul]
    have e1 : (fun z => R⁻¹ * φ (x₀ + R • z) i) =
        R⁻¹ • ((fun w => (fun u => φ u i) (x₀ + w)) <| R • ·) := rfl
    have h2 := fderiv_comp_smul (𝕜 := ℝ) (f := fun w => (fun u => φ u i) (x₀ + w)) (x := y) R
    rw [e1, fderiv_const_smul_field, Pi.smul_apply]
    erw [h2]
    have h3 := fderiv_comp_add_left (𝕜 := ℝ) (f := fun u => φ u i) (x := R • y) x₀
    erw [h3]
    simp only [smul_apply, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
  have hvolQ : volume (unitCube m) < ⊤ := by rw [rd_volume_unitCube]; exact ENNReal.one_lt_top
  have hq := h ψ _ hψ hψ0 (rd_integrableOn hf hbdd A hψ hvolQ)
  rw [rd_volume_unitCube, ENNReal.toReal_one, one_mul] at hq
  simp only [hgrad] at hq
  -- change of variables `x = x₀ + R y`
  set G : (Fin m → ℝ) → ℝ := fun x => f (A + grad φ x)
  set QR : Set (Fin m → ℝ) := Set.pi univ fun _ => Ioo (-a) a
  have hfin : Module.finrank ℝ (Fin m → ℝ) = m := by simp
  have hcv : ∫ y in unitCube m, G (T y) = (R ^ m)⁻¹ * ∫ x in QR, G x := by
    have h1 := Measure.setIntegral_comp_smul_of_pos volume (fun z => G (x₀ + z)) (unitCube m) hR
    have h2 := (measurePreserving_add_left volume x₀).setIntegral_preimage_emb
      (measurableEmbedding_addLeft x₀) G QR
    have hset : R • unitCube m = (fun z => x₀ + z) ⁻¹' QR := by
      ext z
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ hR.ne']
      simp only [unitCube, QR, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo,
        Set.mem_preimage, Pi.smul_apply, smul_eq_mul, Pi.add_apply, x₀]
      refine forall_congr' fun i => ?_
      rw [← div_eq_inv_mul, div_pos_iff_of_pos_right hR, div_lt_one hR, hR_def]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    simp only [T] at h1 ⊢
    rw [h1, hset, h2, hfin, smul_eq_mul]
  have hQRvol : volume QR = ENNReal.ofReal (R ^ m) := by
    simp only [QR, Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← ENNReal.ofReal_pow (by linarith), hR_def]
    congr 2
    ring
  have hQRfin : volume QR < ⊤ := by rw [hQRvol]; exact ENNReal.ofReal_lt_top
  have hΩQR : Ω ⊆ QR := fun x hx i _ => by
    have := abs_le.1 (hent x hx i)
    exact ⟨by linarith, by linarith⟩
  have hΩfin : volume Ω < ⊤ := (measure_mono hΩQR).trans_lt hQRfin
  have hint : IntegrableOn G QR := rd_integrableOn hf hbdd A hφ hQRfin
  have hsplit := integral_inter_add_sdiff hΩm hint
  rw [Set.inter_eq_right.2 hΩQR] at hsplit
  -- on `Q_R ∖ Ω` the gradient vanishes almost everywhere
  have hout : ∫ x in QR \ Ω, G x = volume.real (QR \ Ω) * f A := by
    rw [setIntegral_congr_ae (g := fun _ => f A) ((MeasurableSet.univ_pi fun _ =>
      measurableSet_Ioo).diff hΩm) ?_, setIntegral_const, smul_eq_mul]
    filter_upwards [rd_ae_grad_eq_zero hφ] with x hx hxs
    simp only [G, hx (h0 x hxs.2), add_zero]
  have hvol : volume.real (QR \ Ω) = R ^ m - volume.real Ω := by
    rw [Measure.real, measure_sdiff hΩQR hΩm.nullMeasurableSet hΩfin.ne, hQRvol,
      ENNReal.toReal_sub_of_le ((measure_mono hΩQR).trans_eq hQRvol) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity), Measure.real]
  rw [hcv, ← hsplit, hout, hvol] at hq
  have hRm : 0 < R ^ m := by positivity
  rw [← mul_le_mul_iff_of_pos_left hRm, ← mul_assoc, mul_inv_cancel₀ hRm.ne', one_mul] at hq
  rw [← Measure.real]
  nlinarith


/-- Quasiconvexity on `Ω₁` gives it on every measurable `Ω₂ ⊆ Ω₁`: a test map on `Ω₂` is one on
`Ω₁`, and its gradient vanishes almost everywhere on `Ω₁ ∖ Ω₂`. -/
private lemma rd_quasiconvexAtOn_mono {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : Measurable f) (hbdd : IsLocallyBounded f) {A : Matrix (Fin d) (Fin m) ℝ}
    {Ω₁ Ω₂ : Set (Fin m → ℝ)} (hsub : Ω₂ ⊆ Ω₁) (h₁ : MeasurableSet Ω₁) (h₂ : MeasurableSet Ω₂)
    (hfin : volume Ω₁ < ⊤) (h : QuasiconvexAtOn Ω₁ f A) : QuasiconvexAtOn Ω₂ f A := by
  intro φ K hφ h0 _
  have hq := h φ K hφ (fun x hx => h0 x fun h => hx (hsub h)) (rd_integrableOn hf hbdd A hφ hfin)
  have hint : IntegrableOn (fun x => f (A + grad φ x)) Ω₁ := rd_integrableOn hf hbdd A hφ hfin
  have hsplit := integral_inter_add_sdiff h₂ hint
  rw [Set.inter_eq_right.2 hsub] at hsplit
  have hout : ∫ x in Ω₁ \ Ω₂, f (A + grad φ x) = volume.real (Ω₁ \ Ω₂) * f A := by
    rw [setIntegral_congr_ae (g := fun _ => f A) (h₁.diff h₂) ?_, setIntegral_const, smul_eq_mul]
    filter_upwards [rd_ae_grad_eq_zero hφ] with x hx hxs
    simp only [hx (h0 x hxs.2), add_zero]
  have hvol : volume.real (Ω₁ \ Ω₂) = volume.real Ω₁ - volume.real Ω₂ := by
    rw [Measure.real, measure_sdiff hsub h₂.nullMeasurableSet
      ((measure_mono hsub).trans_lt hfin).ne,
      ENNReal.toReal_sub_of_le (measure_mono hsub) hfin.ne, Measure.real, Measure.real]
  rw [← hsplit, hout, hvol] at hq
  change volume.real Ω₁ * f A ≤ _ at hq
  rw [← Measure.real]
  linarith

/-- Quasiconvexity on a nonempty open `Ω` gives it on the unit cube. `Ω` contains a cube
`Q' = x₀ + R (0, 1)^m`, on which `f` is quasiconvex at `A` (`rd_quasiconvexAtOn_mono`); a test map
on the unit cube, rescaled to `Q'`, gives the inequality. -/
private lemma rd_unitCube_of_quasiconvexAtOn {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : Measurable f) (hbdd : IsLocallyBounded f) {A : Matrix (Fin d) (Fin m) ℝ}
    {Ω : Set (Fin m → ℝ)} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (h : QuasiconvexAtOn Ω f A) : QuasiconvexAtOn (unitCube m) f A := by
  obtain ⟨x₁, hx₁⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ x₁ hx₁
  set R : ℝ := ε
  set x₀ : Fin m → ℝ := fun i => x₁ i - ε / 2
  set Q' : Set (Fin m → ℝ) := Set.pi univ fun i => Ioo (x₀ i) (x₀ i + R)
  have hQ'Ω : Q' ⊆ Ω := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    have := hx i (Set.mem_univ _)
    simp only [x₀, R, Set.mem_Ioo] at this
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hΩfin : volume Ω < ⊤ := hb.measure_lt_top
  have hQ' : QuasiconvexAtOn Q' f A := rd_quasiconvexAtOn_mono hf hbdd hQ'Ω hΩ.measurableSet
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo) hΩfin h
  intro φ K hφ h0 _
  have hR : 0 < R := hε
  set S : (Fin m → ℝ) → Fin m → ℝ := fun x => R⁻¹ • (x - x₀)
  set ψ : (Fin m → ℝ) → Fin d → ℝ := fun x => R • φ (S x)
  have hS : LipschitzWith ‖R⁻¹‖₊ S := LipschitzWith.of_dist_le_mul fun y z => by
    simp only [S]
    rw [dist_smul₀, dist_sub_right]
    rfl
  have hψ : LipschitzWith (‖R‖₊ * (K * ‖R⁻¹‖₊)) ψ := (lipschitzWith_smul R).comp (hφ.comp hS)
  have hSQ : ∀ x, S x ∈ unitCube m → x ∈ Q' := by
    intro x hx i _
    have := hx i (Set.mem_univ _)
    simp only [S, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Set.mem_Ioo] at this
    rw [← div_eq_inv_mul, div_pos_iff_of_pos_right hR, div_lt_one hR] at this
    exact ⟨by linarith, by linarith⟩
  have hψ0 : ∀ x ∉ Q', ψ x = 0 := fun x hx => by
    simp only [ψ, h0 _ fun h => hx (hSQ x h), smul_zero]
  have hgrad : ∀ x, grad ψ x = grad φ (S x) := by
    intro x
    ext i k
    simp only [grad, Matrix.of_apply, ψ, S, Pi.smul_apply, smul_eq_mul]
    have e1 : (fun z => R * φ (R⁻¹ • (z - x₀)) i) =
        R • ((fun w => (fun u => φ u i) (R⁻¹ • w)) ∘ fun z => z - x₀) := rfl
    rw [e1, fderiv_const_smul_field, Pi.smul_apply]
    have h2 : fderiv ℝ ((fun w => (fun u => φ u i) (R⁻¹ • w)) ∘ fun z => z - x₀) x =
        fderiv ℝ (fun w => (fun u => φ u i) (R⁻¹ • w)) (x - x₀) := by
      exact fderiv_comp_sub (𝕜 := ℝ) (f := fun w => (fun u => φ u i) (R⁻¹ • w)) (x := x) x₀
    rw [h2]
    have h3 := fderiv_comp_smul (𝕜 := ℝ) (f := fun u => φ u i) (x := x - x₀) R⁻¹
    erw [h3]
    simp only [smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
  have hQ'fin : volume Q' < ⊤ := (measure_mono hQ'Ω).trans_lt hΩfin
  have hq := hQ' ψ _ hψ hψ0 (rd_integrableOn hf hbdd A hψ hQ'fin)
  simp only [hgrad] at hq
  -- change of variables `y = R⁻¹ (x − x₀)`
  set G : (Fin m → ℝ) → ℝ := fun y => f (A + grad φ y)
  have hfin : Module.finrank ℝ (Fin m → ℝ) = m := by simp
  have hcv : ∫ x in Q', G (S x) = R ^ m * ∫ y in unitCube m, G y := by
    have h1 := (measurePreserving_sub_right volume x₀).setIntegral_preimage_emb
      (measurableEmbedding_subRight x₀) (fun z => G (R⁻¹ • z)) (R • unitCube m)
    have h4 := Measure.setIntegral_comp_smul_of_pos volume G (R • unitCube m) (inv_pos.2 hR)
    rw [inv_smul_smul₀ hR.ne'] at h4
    have hset : (fun z => z - x₀) ⁻¹' (R • unitCube m) = Q' := by
      ext z
      rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem₀ hR.ne']
      simp only [unitCube, Q', Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo,
        Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      refine forall_congr' fun i => ?_
      rw [← div_eq_inv_mul, div_pos_iff_of_pos_right hR, div_lt_one hR]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    simp only [S]
    rw [← hset, h1, h4, hfin, smul_eq_mul, inv_pow, inv_inv]
  have hQ'vol : volume.real Q' = R ^ m := by
    simp only [Q', Measure.real, Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, add_sub_cancel_left]
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hR.le]
  rw [hcv, ← Measure.real, hQ'vol] at hq
  rw [rd_volume_unitCube, ENNReal.toReal_one, one_mul]
  have hRm : 0 < R ^ m := by positivity
  exact le_of_mul_le_mul_left hq hRm

/-- **Quasiconvexity does not depend on the domain**: for a Borel, locally bounded `f`,
quasiconvexity at `A` on the unit cube is equivalent to quasiconvexity at `A` on any nonempty
bounded open `Ω`. (For `Ω = ∅` the condition holds for every `f`: the only test map is
`0`, and both sides vanish.)

Proof: the argument of [D08], Proposition 5.11, and [R2], Lemma 5.2 (i), with the unit cube as the
intermediate domain. Quasiconvexity on the unit cube is quasiconvexity on every cube
`x₀ + R (0, 1)^m`, by the change of variables `x = x₀ + R y`, and quasiconvexity on a set passes to
its measurable subsets, because a test map on the subset vanishes on the rest, so its gradient
vanishes almost everywhere there (`rd_quasiconvexAtOn_mono`, from `rd_ae_fderiv_eq_zero`: at a
density point of the zero set of a Lipschitz map, its derivative is `0`; no condition on the
boundary is needed). "⇒": `Ω` lies in a large cube (`quasiconvexAtOn_of_unitCube`); "⇐": `Ω`
contains a small cube (`rd_unitCube_of_quasiconvexAtOn`). -/
theorem quasiconvexAtOn_iff {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Measurable f)
    (hbdd : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ) {Ω : Set (Fin m → ℝ)}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    QuasiconvexAtOn (unitCube m) f A ↔ QuasiconvexAtOn Ω f A :=
  ⟨quasiconvexAtOn_of_unitCube hf hbdd hb hΩ.measurableSet,
    rd_unitCube_of_quasiconvexAtOn hf hbdd hΩ hb hne⟩

end CalculusOfVariations
