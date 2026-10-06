/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatRoughGradient

/-!
# The zero-data forced heat response of a rough tensor

For a tensor `G ∈ L^{5/2}(Q_τ) ∩ L²(Q_τ)` vanishing outside the slab
`Q_τ = ℝ³ × (0,τ)`, the forced heat response `Z = forcedHeat G` (the kernel
formula) has a weak spatial gradient in `L²(Q_τ)` with the energy bound, and
satisfies the weak componentwise heat equation
`∫∫ -Z_i ∂_t φ + ∑_j ∂_j Z_i ∂_j φ + ∑_j G_ij ∂_j φ = 0`
against smooth tests compactly supported in the slab. With
`forcedHeat_rough_bounds` this is the analytic core of `lem:pv-stokes`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A continuous compactly supported function on `Vec3 × ℝ` is square integrable
on the slab. -/
private theorem memLp_two_slab_of_continuous {f : ParabolicPoint → ℝ}
    (hf : Continuous (fun p : Vec3 × ℝ => f p)) (hfc : HasCompactSupport (fun p : Vec3 × ℝ => f p))
    (τ : ℝ) :
    MemLp f 2 (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) :=
  (hf.memLp_of_hasCompactSupport (μ := (volume : Measure (Vec3 × ℝ))) hfc).restrict _

/-- A continuous compactly supported function on `Vec3 × ℝ` is integrable on the
slab. -/
private theorem integrable_slab_of_continuous {f : ParabolicPoint → ℝ}
    (hf : Continuous (fun p : Vec3 × ℝ => f p)) (hfc : HasCompactSupport (fun p : Vec3 × ℝ => f p))
    (τ : ℝ) :
    Integrable f (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) :=
  (hf.integrable_of_hasCompactSupport (μ := (volume : Measure (Vec3 × ℝ))) hfc).restrict

/-- The weak identities of the rough forced heat response along a smooth
approximation whose spatial gradients converge in `L²(Q_τ)`: for every smooth test
`φ` compactly supported in `Q_τ`, `∫ Z_i ∂_j φ = -∫ DZ_ij φ` and
`∫ -Z_i ∂_t φ + ∑_j DZ_ij ∂_j φ + ∑_j G_ij ∂_j φ = 0` on `Q_τ`. -/
theorem forcedHeat_rough_weak_of_gradient {τ : ℝ} (hτ : 0 < τ)
    {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ} (hG2 : ∀ i j, MemLp (G i j) 2 volume)
    (hGsupp : ∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0)
    {Gs : ℕ → Fin 3 → Fin 3 → ParabolicPoint → ℝ} {DZ : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hGs : ∀ k i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => Gs k i j p))
    (hGsc : ∀ k i j, HasCompactSupport (fun p : Vec3 × ℝ => Gs k i j p))
    (hGspos : ∀ k i j, tsupport (fun p : Vec3 × ℝ => Gs k i j p) ⊆ {p | 0 < p.2})
    (hGsconv : ∀ i j, Tendsto (fun k => eLpNorm (fun p : Vec3 × ℝ => Gs k i j p - G i j p) 2
      volume) atTop (𝓝 0))
    (hDZsmem : ∀ k i j, MemLp (fun z => CKN.spatialPartial (fun w => forcedHeat (Gs k) w i) j z)
      2 (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))))
    (hDZmem : ∀ i j, MemLp (DZ i j) 2
      (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))))
    (hDZlim : ∀ i j, Tendsto (fun k => eLpNorm
      ((fun z => CKN.spatialPartial (fun w => forcedHeat (Gs k) w i) j z) - DZ i j) 2
        (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) atTop (𝓝 0))
    (φ : ParabolicPoint → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => φ p))
    (hφc : HasCompactSupport (fun p : Vec3 × ℝ => φ p))
    (hφQ : tsupport (fun p : Vec3 × ℝ => φ p) ⊆ (Set.univ : Set Vec3) ×ˢ Ioo 0 τ) :
    (∀ i j, ∫ z in CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
        forcedHeat G z i * CKN.spatialPartial φ j z =
      -∫ z in CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ), DZ i j z * φ z) ∧
    ∀ i, ∫ z in CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
      (-(forcedHeat G z i * CKN.timePartial φ z) +
        ∑ j : Fin 3, DZ i j z * CKN.spatialPartial φ j z +
        ∑ j : Fin 3, G i j z * CKN.spatialPartial φ j z) = 0 := by

  set Q : Set ParabolicPoint := CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)
  set μQ : Measure ParabolicPoint := volume.restrict Q
  let ψ : Vec3 × ℝ → ℝ := fun p => φ p
  let g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j p => G i j p
  let gs : ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun k i j p => Gs k i j p
  have hg2 (i j : Fin 3) : MemLp (g i j) 2 volume := hG2 i j
  have hgsupp (i j : Fin 3) (z : Vec3 × ℝ) (hz : g i j z ≠ 0) : 0 < z.2 := by
    by_contra hneg
    apply hz
    apply hGsupp i j z
    intro hmem
    exact hneg hmem.2.1
  have hconv (i j : Fin 3) : Tendsto (fun k => eLpNorm (gs k i j - g i j) 2 volume) atTop
      (𝓝 0) := hGsconv i j
  -- derivatives of the test function
  have hDφ (j : Fin 3) (z : ParabolicPoint) :
      CKN.spatialPartial φ j z = fderiv ℝ ψ z (CKN.basisVec j, 0) :=
    spatialPartial_eq_fderiv_apply hφ j z.1 z.2
  have hTφ (z : ParabolicPoint) : CKN.timePartial φ z = fderiv ℝ ψ z (0, 1) :=
    timePartial_eq_fderiv_apply hφ z.1 z.2
  have hDψc (v : Vec3 × ℝ) : Continuous (fun p => fderiv ℝ ψ p v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDψs (v : Vec3 × ℝ) : HasCompactSupport (fun p => fderiv ℝ ψ p v) :=
    hφc.fderiv_apply (𝕜 := ℝ) v
  have hSφc (j : Fin 3) : Continuous (fun p : Vec3 × ℝ => CKN.spatialPartial φ j p) :=
    (hDψc (CKN.basisVec j, 0)).congr fun p => (hDφ j p).symm
  have hSφs (j : Fin 3) : HasCompactSupport (fun p : Vec3 × ℝ => CKN.spatialPartial φ j p) := by
    have heq : (fun p : Vec3 × ℝ => CKN.spatialPartial φ j p) =
        fun p => fderiv ℝ ψ p (CKN.basisVec j, 0) := funext fun p => hDφ j p
    rw [heq]
    exact hDψs (CKN.basisVec j, 0)
  have hTφc : Continuous (fun p : Vec3 × ℝ => CKN.timePartial φ p) :=
    (hDψc (0, 1)).congr fun p => (hTφ p).symm
  have hTφs : HasCompactSupport (fun p : Vec3 × ℝ => CKN.timePartial φ p) := by
    have heq : (fun p : Vec3 × ℝ => CKN.timePartial φ p) = fun p => fderiv ℝ ψ p (0, 1) :=
      funext fun p => hTφ p
    rw [heq]
    exact hDψs (0, 1)
  have hφ2 : MemLp φ 2 μQ := memLp_two_slab_of_continuous hφ.continuous hφc τ
  have hSφ2 (j : Fin 3) : MemLp (fun z => CKN.spatialPartial φ j z) 2 μQ :=
    memLp_two_slab_of_continuous (hSφc j) (hSφs j) τ
  -- the smooth identities
  have hsmoothid (k : ℕ) (i : Fin 3) := forcedHeat_smooth_weak_slab (hGs k) (hGsc k) hφ hφc hφQ i
  -- the response terms converge
  have hresp (i : Fin 3) (f : Vec3 × ℝ → ℝ) (hf : Continuous f) (hfs : HasCompactSupport f) :=
    kernelResponse_integral_tendsto hτ hg2 hgsupp (gn := gs) (fun k => hGs k) (fun k => hGsc k)
      (fun k => hGspos k) hconv hf hfs i
  -- the gradient terms converge
  have hgradlim (i j : Fin 3) (f : ParabolicPoint → ℝ) (hf : MemLp f 2 μQ) :
      Tendsto (fun k => ∫ z in Q, CKN.spatialPartial (fun w => forcedHeat (Gs k) w i) j z * f z)
        atTop (𝓝 (∫ z in Q, DZ i j z * f z)) :=
    tendsto_integral_mul_of_eLpNorm_two (fun k => hDZsmem k i j) (hDZmem i j) hf (hDZlim i j)
  constructor
  · intro i j
    obtain ⟨_, hlimZ⟩ := hresp i _ (hSφc j) (hSφs j)
    have hlimD := (hgradlim i j φ hφ2).neg
    have hseq : (fun k => ∫ z in Q, forcedHeat (Gs k) z i * CKN.spatialPartial φ j z) =
        fun k => -∫ z in Q, CKN.spatialPartial (fun w => forcedHeat (Gs k) w i) j z * φ z :=
      funext fun k => (hsmoothid k i).1 j
    have hlimZ' : Tendsto (fun k => ∫ z in Q, forcedHeat (Gs k) z i * CKN.spatialPartial φ j z)
        atTop (𝓝 (∫ z in Q, forcedHeat G z i * CKN.spatialPartial φ j z)) := hlimZ
    rw [hseq] at hlimZ'
    exact tendsto_nhds_unique hlimZ' hlimD
  · intro i
    have hsplit3 (a : ParabolicPoint → ℝ) (b c : Fin 3 → ParabolicPoint → ℝ)
        (ha : Integrable a μQ) (hb : ∀ j, Integrable (b j) μQ) (hc : ∀ j, Integrable (c j) μQ) :
        ∫ z in Q, (-(a z) + ∑ j : Fin 3, b j z + ∑ j : Fin 3, c j z) =
          -(∫ z in Q, a z) + (∑ j : Fin 3, ∫ z in Q, b j z) + ∑ j : Fin 3, ∫ z in Q, c j z := by
      have hB : Integrable (fun z => ∑ j : Fin 3, b j z) μQ := integrable_finsetSum _ fun j _ => hb j
      have hC : Integrable (fun z => ∑ j : Fin 3, c j z) μQ := integrable_finsetSum _ fun j _ => hc j
      have hna : Integrable (fun z => -(a z)) μQ := ha.neg
      have hAB : Integrable (fun z => -(a z) + ∑ j : Fin 3, b j z) μQ := hna.add hB
      rw [integral_add hAB hC, integral_add hna hB, integral_neg,
        integral_finsetSum _ fun j _ => hb j, integral_finsetSum _ fun j _ => hc j]
    -- integrability on the slab
    have hGsQ (k : ℕ) (j : Fin 3) : MemLp (Gs k i j) 2 μQ :=
      memLp_two_slab_of_continuous (hGs k i j).continuous (hGsc k i j) τ
    have hGQ (j : Fin 3) : MemLp (G i j) 2 μQ := (hG2 i j).restrict _
    have hZkint (k : ℕ) : Integrable (fun z => forcedHeat (Gs k) z i * CKN.timePartial φ z) μQ :=
      integrable_slab_of_continuous
        ((forcedHeat_contDiff (hGs k) (hGsc k) i).continuous.mul hTφc) hTφs.mul_left τ
    obtain ⟨hZint, hlimA⟩ := hresp i _ hTφc hTφs
    have hsmooth0 (k : ℕ) : -(∫ z in Q, forcedHeat (Gs k) z i * CKN.timePartial φ z) +
        (∑ j : Fin 3, ∫ z in Q, CKN.spatialPartial (fun w => forcedHeat (Gs k) w i) j z *
          CKN.spatialPartial φ j z) +
        ∑ j : Fin 3, ∫ z in Q, Gs k i j z * CKN.spatialPartial φ j z = 0 := by
      rw [← hsplit3 _ (fun j z => CKN.spatialPartial (fun w => forcedHeat (Gs k) w i) j z *
          CKN.spatialPartial φ j z) (fun j z => Gs k i j z * CKN.spatialPartial φ j z)
        (hZkint k) (fun j => (hDZsmem k i j).integrable_mul (hSφ2 j))
        (fun j => (hGsQ k j).integrable_mul (hSφ2 j))]
      exact (hsmoothid k i).2
    refine (hsplit3 (fun z => forcedHeat G z i * CKN.timePartial φ z)
      (fun j z => DZ i j z * CKN.spatialPartial φ j z)
      (fun j z => G i j z * CKN.spatialPartial φ j z) hZint
      (fun j => (hDZmem i j).integrable_mul (hSφ2 j))
      (fun j => (hGQ j).integrable_mul (hSφ2 j))).trans ?_
    have hlimB (j : Fin 3) := hgradlim i j _ (hSφ2 j)
    have hlimC (j : Fin 3) : Tendsto (fun k => ∫ z in Q, Gs k i j z * CKN.spatialPartial φ j z)
        atTop (𝓝 (∫ z in Q, G i j z * CKN.spatialPartial φ j z)) := by
      refine tendsto_integral_mul_of_eLpNorm_two (fun k => hGsQ k j) (hGQ j) (hSφ2 j) ?_
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hGsconv i j)
        (fun k => bot_le) fun k => eLpNorm_mono_measure _ Measure.restrict_le_self
    have hlim := ((hlimA.neg.add (tendsto_finsetSum Finset.univ fun j _ => hlimB j)).add
      (tendsto_finsetSum Finset.univ fun j _ => hlimC j))
    have hzero : Tendsto (fun k => -(∫ z in Q, forcedHeat (Gs k) z i * CKN.timePartial φ z) +
        (∑ j : Fin 3, ∫ z in Q, CKN.spatialPartial (fun w => forcedHeat (Gs k) w i) j z *
          CKN.spatialPartial φ j z) +
        ∑ j : Fin 3, ∫ z in Q, Gs k i j z * CKN.spatialPartial φ j z) atTop (𝓝 0) := by
      simp only [hsmooth0]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim hzero

/-- The weak spatial gradient and the weak heat equation for the forced heat
response of a tensor in `L^{5/2} ∩ L²` supported in `Q_τ`: the gradient lies in
`L²(Q_τ)` with `‖∇Z‖_{L²(Q_τ)} ≤ C ‖G‖_{L²(Q_τ)}`, and for every smooth test `φ`
compactly supported in `Q_τ`, `∫ Z_i ∂_j φ = -∫ ∂_j Z_i φ` and
`∫ -Z_i ∂_t φ + ∑_j ∂_j Z_i ∂_j φ + ∑_j G_ij ∂_j φ = 0` on `Q_τ`. -/
theorem forcedHeat_rough_weak :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∀ G : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
      (∀ i j, MemLp (G i j) (ENNReal.ofReal (5 / 2)) volume) →
      (∀ i j, MemLp (G i j) 2 volume) →
      (∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0) →
      ∃ DZ : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
        (∀ i j, MemLp (DZ i j) 2
          (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
        eLpNorm (fun z => fun i j => DZ i j z) 2
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
          ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) 2
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        ∀ φ : ParabolicPoint → ℝ, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => φ p) →
          HasCompactSupport (fun p : Vec3 × ℝ => φ p) →
          tsupport (fun p : Vec3 × ℝ => φ p) ⊆ (Set.univ : Set Vec3) ×ˢ Ioo 0 τ →
          (∀ i j, ∫ z in CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
              forcedHeat G z i * CKN.spatialPartial φ j z =
            -∫ z in CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ), DZ i j z * φ z) ∧
          ∀ i, ∫ z in CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
            (-(forcedHeat G z i * CKN.timePartial φ z) +
              ∑ j : Fin 3, DZ i j z * CKN.spatialPartial φ j z +
              ∑ j : Fin 3, G i j z * CKN.spatialPartial φ j z) = 0 := by
  obtain ⟨C, hC, hgrad⟩ := forcedHeat_rough_gradient
  refine ⟨C, hC, fun τ hτ G hG52 hG2 hGsupp => ?_⟩
  obtain ⟨Gs, DZ, hGs, hGsc, hGspos, hGsconv, hDZsmem, hDZmem, hDZlim, henergy⟩ :=
    hgrad τ hτ G hG52 hG2 hGsupp
  refine ⟨DZ, hDZmem, henergy, fun φ hφ hφc hφQ => ?_⟩
  exact forcedHeat_rough_weak_of_gradient hτ hG2 hGsupp hGs hGsc hGspos hGsconv hDZsmem hDZmem
    hDZlim φ hφ hφc hφQ

/-- The zero-data forced heat estimates for a tensor `G ∈ L^{5/2} ∩ L²` supported in
`Q_τ`, with one absolute constant `C`: the kernel response `Z = forcedHeat G` lies in
`L⁵(Q_τ) ∩ L⁴(Q_τ)` with `‖Z‖₅ ≤ C ‖G‖_{5/2}` and `‖Z‖₄ ≤ C (‖G‖_{5/2} + ‖G‖₂)`; for
almost every `t ∈ (0,τ)`, `‖Z(t)‖₃ ≤ C ‖G‖_{5/2}` and `‖Z(t)‖₂ ≤ C ‖G‖₂`; and `Z` has a
weak spatial gradient in `L²(Q_τ)` with `‖∇Z‖₂ ≤ C ‖G‖₂` for which the weak
componentwise heat equation holds against smooth tests compactly supported in
`Q_τ`. This is the analytic core of `lem:pv-stokes`. -/
theorem forcedHeat_rough_estimates :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∀ G : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
      (∀ i j, MemLp (G i j) (ENNReal.ofReal (5 / 2)) volume) →
      (∀ i j, MemLp (G i j) 2 volume) →
      (∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0) →
      MemLp (forcedHeat G) 5
          (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
      MemLp (forcedHeat G) 4
          (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
      eLpNorm (forcedHeat G) 5
          (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
        ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) (ENNReal.ofReal (5 / 2))
          (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
      eLpNorm (forcedHeat G) 4
          (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
        ENNReal.ofReal C *
          (eLpNorm (fun z => fun i j => G i j z) (ENNReal.ofReal (5 / 2))
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) +
          eLpNorm (fun z => fun i j => G i j z) 2
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo 0 τ)),
        eLpNorm (fun x : Vec3 => forcedHeat G (x, t)) 3 volume ≤
          ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) (ENNReal.ofReal (5 / 2))
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo 0 τ)),
        eLpNorm (fun x : Vec3 => forcedHeat G (x, t)) 2 volume ≤
          ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) 2
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
      ∃ DZ : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
        (∀ i j, MemLp (DZ i j) 2
          (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
        eLpNorm (fun z => fun i j => DZ i j z) 2
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
          ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) 2
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        ∀ φ : ParabolicPoint → ℝ, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => φ p) →
          HasCompactSupport (fun p : Vec3 × ℝ => φ p) →
          tsupport (fun p : Vec3 × ℝ => φ p) ⊆ (Set.univ : Set Vec3) ×ˢ Ioo 0 τ →
          (∀ i j, ∫ z in CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
              forcedHeat G z i * CKN.spatialPartial φ j z =
            -∫ z in CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ), DZ i j z * φ z) ∧
          ∀ i, ∫ z in CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
            (-(forcedHeat G z i * CKN.timePartial φ z) +
              ∑ j : Fin 3, DZ i j z * CKN.spatialPartial φ j z +
              ∑ j : Fin 3, G i j z * CKN.spatialPartial φ j z) = 0 := by
  obtain ⟨C₁, hC₁, hbounds⟩ := forcedHeat_rough_bounds
  obtain ⟨C₂, hC₂, hweak⟩ := forcedHeat_rough_weak
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun τ hτ G hG52 hG2 hGsupp => ?_⟩
  obtain ⟨h5, h4, h3, h2⟩ := hbounds τ hτ G hG52 hG2 hGsupp
  obtain ⟨DZ, hDZ, hen, hid⟩ := hweak τ hτ G hG52 hG2 hGsupp
  set μQ : Measure ParabolicPoint :=
    volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))
  have hC₁le : ENNReal.ofReal C₁ ≤ ENNReal.ofReal (C₁ + C₂) :=
    ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hC₂)
  have hC₂le : ENNReal.ofReal C₂ ≤ ENNReal.ofReal (C₁ + C₂) :=
    ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left hC₁)
  have hfin (p : ℝ≥0∞) (hp : 1 ≤ p) (hGp : ∀ i j, MemLp (G i j) p volume) :
      eLpNorm (fun z => fun i j => G i j z) p μQ < ∞ := by
    refine lt_of_le_of_lt (eLpNorm_tensor_le_sum hp _ fun i j =>
      (hGp i j).aestronglyMeasurable.restrict) ?_
    exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.sum_lt_top.2 fun j _ =>
      ((hGp i j).restrict _).eLpNorm_lt_top
  have hp52 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (5 / 2) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hf52 := hfin _ hp52 hG52
  have hf2 := hfin 2 (by norm_num) hG2
  refine ⟨memLp_iff.2 (lt_of_le_of_lt h5 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf52)),
    memLp_iff.2 (lt_of_le_of_lt h4 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.2 ⟨hf52, hf2⟩))),
    h5.trans (mul_le_mul_left hC₁le _), h4.trans (mul_le_mul_left hC₁le _), ?_, ?_,
    DZ, hDZ, hen.trans (mul_le_mul_left hC₂le _), hid⟩
  · filter_upwards [h3] with t ht
    exact ht.trans (mul_le_mul_left hC₁le _)
  · filter_upwards [h2] with t ht
    exact ht.trans (mul_le_mul_left hC₁le _)

end ESS

end
