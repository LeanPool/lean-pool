/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomBridgeDataEmbedding
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BesovBridge

/-!
# HomStepThreeData

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5: the residues `M1`, `M2`, `M3`

## What Step 2 hands forward

The Step-2a display prices the §4.5 energy by `CoarseGraining`'s Besov data
quantities `B_g`, `B_h`.  Converting those to the printed `3^{m/2}` runs
through the bridge
`ExcessDecay.scaleNormalizedPositiveBesovVectorSeminormTwo_le_gagliardo`
composed with the embedding
`HomBridgeDataEmbedding`'s pinned data embedding.  The bridge has two
side conditions that existed nowhere, and its `∇h` leg carries a MEAN term that
a Hölder seminorm alone cannot price.  Those were `M1`, `M2`, `M3`.  All three
are settled here.

* **(M1)** `MemLp g 2 (normalizedCubeMeasure □_m)` from a Hölder-`1/2` bound on
  the open cube (`memLp_two_normalizedCubeMeasure_of_holderHalf`).  Route: the
  Hölder bound gives `ContinuousOn` (hence `AEStronglyMeasurable` on the
  restricted measure) and, against ANY one point of the cube, the pointwise
  bound `‖g x‖ ≤ ‖g 0‖ + K √(3^m)`; a bounded function on a finite measure is
  `L^∞`, hence `L²`.  This is the essential-sup route of the Step-5 data
  layer, run here at the `L²` exponent.
* **(M2)** `Gagliardo.MemWsp □_m t 2 g` (`memWsp_of_holderHalf`).  Its
  `eSeminorm < ⊤` half is the embedding atom read through
  `ExcessDecay.normalizedGagliardoESeminormOn_openCubeSet`; the genuinely new
  half is `AEStronglyMeasurable (gagliardoKernel t 2 g)` for the Gagliardo
  PRODUCT measure, which is obtained by the `BoundsEaL`-style measure algebra
  (`normalizedGagliardoMeasureOn A = (vol A)⁻¹ • (volume.prod volume).restrict
  (A ×ˢ A)`, the own rewrite) plus `CoarseGraining`'s own kernel-measurability idiom
  (`measurable_dist.pow measurable_const`, the scalar factor is GLOBALLY
  measurable; only the vector factor needs the window).
* **(M1)+(M2)** discharge `ForceBesovRegularity` — the hypothesis of the coarse-graining right-hand
side
  itself — at the §4.5 data (`forceBesovRegularity_of_holderHalf`,
  `forceBesovRegularity_neg_of_holderHalf`), and give the printed data legs
  `B_g, B_h ≤ C 3^{m/2}`.

## (M3): the `∇h` leg

The `∇h` leg's norm

```
  ‖∇h‖ = √|⨍_{□_m} ∇h|² + [∇h]_{B^t_{2,2}(□_m)}
```

prices against the frozen root's OWN binders.  The root
`generator_renormalization` carries, besides the seminorm binder `Kh`
(`HolderSeminormBoundOn (openCubeSet □_m) (1/2) Kh h.grad`), the SUP binder

```
  ∀ x ∈ openCubeSet □_m, ‖h.grad x‖ ≤ KhInf
```

and its conclusion displays the `∇h` leg as `(KhInf + 3^{m/2} Kh)` — the NORM,
`L^∞` half plus seminorm half, exactly.  The mean term is priced by `KhInf`
alone: `‖⨍_Q ∇h‖ ≤ √d · KhInf` (`sqrt_vecNormSq_ cubeAverageVec_le`; the `√d` is
the ambient sup-norm-versus-Euclidean conversion of `vecNormSq`, the standing
convention, NOT a new datum).  The composed display's right-hand side is the
root's own bracket.

**M3 is therefore NOT a statement-level item and no new binder is needed.**  The
carrier finding stands (a Hölder SEMINORM alone does not control the mean); what
that reading missed is that the root already carries the missing sup datum.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.Regularity

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 1. Hölder-`1/2` data are continuous and bounded on the window -/

omit [NormedSpace ℝ E] in
/-- **A Hölder-`1/2` field is continuous on its window.**  The `δ = (ε/(K+1))²`
modulus; no measurability, no completeness, no compactness is used. -/
theorem continuousOn_of_holderHalf {U : Set (Vec d)} {K : ℝ} {f : Vec d → E}
    (hK : 0 ≤ K) (hf : Support.HolderSeminormBoundOn U (1 / 2) K f) :
    ContinuousOn f U := by
  rw [Metric.continuousOn_iff]
  intro b hb eps heps
  have hK1 : (0 : ℝ) < K + 1 := by linarith only [hK]
  have hquot : (0 : ℝ) < eps / (K + 1) := div_pos heps hK1
  refine ⟨(eps / (K + 1)) ^ (2 : ℕ), pow_pos hquot 2, ?_⟩
  intro a ha hdist
  have hstep := hf a ha b hb
  have hnorm : ‖a - b‖ = dist a b := (dist_eq_norm a b).symm
  have hsqrt : Real.sqrt (dist a b) < eps / (K + 1) := by
    have hlt : Real.sqrt (dist a b) < Real.sqrt ((eps / (K + 1)) ^ (2 : ℕ)) :=
      Real.sqrt_lt_sqrt dist_nonneg hdist
    rwa [Real.sqrt_sq hquot.le] at hlt
  have hrpow : ‖a - b‖ ^ (1 / 2 : ℝ) = Real.sqrt (dist a b) := by
    rw [hnorm, ← Real.sqrt_eq_rpow]
  have hlast : K * (eps / (K + 1)) < eps := by
    have hmul : K * (eps / (K + 1)) < (eps / (K + 1)) * (K + 1) := by
      linarith only [hquot]
    have heq : (eps / (K + 1)) * (K + 1) = eps := by
      field_simp
    linarith only [hmul, heq]
  rw [dist_eq_norm]
  calc ‖f a - f b‖ ≤ K * ‖a - b‖ ^ (1 / 2 : ℝ) := hstep
    _ = K * Real.sqrt (dist a b) := by rw [hrpow]
    _ ≤ K * (eps / (K + 1)) := mul_le_mul_of_nonneg_left hsqrt.le hK
    _ < eps := hlast

omit [NormedSpace ℝ E] in
/-- **A Hölder-`1/2` field is bounded on a bounded window.**  Against any base
point `x₀ ∈ U` inside a sup-ball of radius `R`. -/
theorem norm_le_of_holderHalf_of_ball {U : Set (Vec d)} {K R : ℝ} {f : Vec d → E}
    (hK : 0 ≤ K) (hf : Support.HolderSeminormBoundOn U (1 / 2) K f) {x0 : Vec d}
    (hx0 : x0 ∈ U) (hball : U ⊆ Metric.ball x0 R) :
    ∀ x ∈ U, ‖f x‖ ≤ ‖f x0‖ + K * Real.sqrt R := by
  intro x hx
  have hstep := hf x hx x0 hx0
  have hd : dist x x0 < R := Metric.mem_ball.mp (hball hx)
  have hrpow : ‖x - x0‖ ^ (1 / 2 : ℝ) = Real.sqrt (dist x x0) := by
    rw [← dist_eq_norm, ← Real.sqrt_eq_rpow]
  have hsq : Real.sqrt (dist x x0) ≤ Real.sqrt R :=
    Real.sqrt_le_sqrt hd.le
  have hsplit : ‖f x‖ ≤ ‖f x0‖ + ‖f x - f x0‖ := by
    have heq : f x0 + (f x - f x0) = f x := by abel
    have h := norm_add_le (f x0) (f x - f x0)
    rwa [heq] at h
  have hmul : K * ‖x - x0‖ ^ (1 / 2 : ℝ) ≤ K * Real.sqrt R := by
    rw [hrpow]
    exact mul_le_mul_of_nonneg_left hsq hK
  linarith only [hsplit, hstep, hmul]

omit [NormedSpace ℝ E] in
/-- The §4.5 instance: on `□_m` (open realization) the base point is the origin
and the sup-radius is the side length `3^m`. -/
theorem norm_le_of_holderHalf_originCube {m : ℤ} {K : ℝ} {f : Vec d → E} (hK : 0 ≤ K)
    (hf : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K f) :
    ∀ x ∈ openCubeSet (originCube d m),
      ‖f x‖ ≤ ‖f 0‖ + K * Real.sqrt ((3 : ℝ) ^ m) :=
  norm_le_of_holderHalf_of_ball hK hf (Regularity.zero_mem_openCubeSet_originCube d m)
    (Regularity.openCubeSet_subset_ball (Regularity.zero_mem_openCubeSet_originCube d m))

/-! ## 2. `M1`: the `L²` half of the data regularity -/

omit [NormedSpace ℝ E] in
/-- **`M1`.**  A Hölder-`1/2` datum on `□_m` is `L²` for the normalized cube
measure.  (`normalizedCubeMeasure □_m` is a probability measure; the datum is
bounded on the cube by §1, and continuous there, so it is `L^∞` and a fortiori
`L²`.) -/
theorem memLp_two_normalizedCubeMeasure_of_holderHalf {m : ℤ} {K : ℝ} {f : Vec d → E}
    (hK : 0 ≤ K)
    (hf : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K f) :
    MemLp f 2 (normalizedCubeMeasure (originCube d m)) := by
  have hset : MeasurableSet (openCubeSet (originCube d m)) :=
    (isOpen_openCubeSet _).measurableSet
  have : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d m))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact volume_openCubeSet_lt_top _
  have haes : AEStronglyMeasurable f (volume.restrict (openCubeSet (originCube d m))) :=
    (continuousOn_of_holderHalf hK hf).aestronglyMeasurable hset
  have htop : MemLp f ⊤ (volume.restrict (openCubeSet (originCube d m))) :=
    memLp_top_of_bound haes (‖f 0‖ + K * Real.sqrt ((3 : ℝ) ^ m))
      (ae_restrict_of_forall_mem hset (norm_le_of_holderHalf_originCube hK hf))
  have htwo : MemLp f 2 (volume.restrict (openCubeSet (originCube d m))) :=
    htop.mono_exponent le_top
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact htwo.smul_measure ENNReal.ofReal_ne_top

/-! ## 3. `M2`: the fractional half of the data regularity -/

/-- The Gagliardo product measure on `□_m`, written as a scalar multiple of the
plain product measure restricted to `□_m × □_m`.  (the rewrite, at the open
realization `CoarseGraining`'s `gagliardoCubeMeasure` agrees with.) -/
theorem gagliardoCubeMeasure_eq_smul_restrict (Q : TriadicCube d) :
    Gagliardo.gagliardoCubeMeasure Q =
      (volume (openCubeSet Q))⁻¹ •
        ((volume.prod volume).restrict (openCubeSet Q ×ˢ openCubeSet Q)) := by
  rw [← normalizedGagliardoMeasureOn_openCubeSet,
    Support.normalizedGagliardoMeasureOn_def, Support.normalizedVolumeMeasureOn_def,
    Measure.prod_smul_left, Measure.prod_restrict]

/-- **The kernel is a.e. strongly measurable on the Gagliardo product
measure.**  The scalar factor `|z₁-z₂|^{-(s+d/2)}` is GLOBALLY measurable
(`CoarseGraining`'s own idiom); only the vector factor `f(z₁) - f(z₂)` needs the window, and
there it is continuous. -/
theorem aestronglyMeasurable_gagliardoKernel_of_holderHalf {Q : TriadicCube d} {K s : ℝ}
    {f : Vec d → E} (hK : 0 ≤ K)
    (hf : Support.HolderSeminormBoundOn (openCubeSet Q) (1 / 2) K f) :
    AEStronglyMeasurable (Gagliardo.gagliardoKernel s 2 f)
      (Gagliardo.gagliardoCubeMeasure Q) := by
  have hset : MeasurableSet (openCubeSet Q) := (isOpen_openCubeSet _).measurableSet
  have hcont := continuousOn_of_holderHalf hK hf
  rw [gagliardoCubeMeasure_eq_smul_restrict Q]
  refine AEStronglyMeasurable.smul_measure ?_ _
  have hscal : AEStronglyMeasurable
      (fun z : Vec d × Vec d => dist z.1 z.2 ^ (-(Gagliardo.kernelExponent d s 2)))
      ((volume.prod volume).restrict (openCubeSet Q ×ˢ openCubeSet Q)) :=
    (measurable_dist.pow measurable_const).aestronglyMeasurable
  have hfst : ContinuousOn (fun z : Vec d × Vec d => f z.1) (openCubeSet Q ×ˢ openCubeSet Q) :=
    hcont.comp continuous_fst.continuousOn fun _ hz => hz.1
  have hsnd : ContinuousOn (fun z : Vec d × Vec d => f z.2) (openCubeSet Q ×ˢ openCubeSet Q) :=
    hcont.comp continuous_snd.continuousOn fun _ hz => hz.2
  have hvec : AEStronglyMeasurable (fun z : Vec d × Vec d => f z.1 - f z.2)
      ((volume.prod volume).restrict (openCubeSet Q ×ˢ openCubeSet Q)) :=
    (hfst.sub hsnd).aestronglyMeasurable (hset.prod hset)
  exact hscal.smul hvec

/-- **`M2`.**  A Hölder-`1/2` datum on `□_m` lies in `W^{s,2}(□_m)` for every
`0 < s < 1/2`.  The strict inequality `s < 1/2` is load-bearing: at `s = 1/2` the Gagliardo integral
diverges. -/
theorem memWsp_of_holderHalf {m : ℤ} {K s : ℝ} {f : Vec d → E} (hd : 1 ≤ d)
    (hs0 : 0 < s) (hs : s < 1 / 2) (hK : 0 ≤ K)
    (hf : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K f) :
    Gagliardo.MemWsp (originCube d m) s 2 f := by
  have hid := normalizedGagliardoESeminormOn_openCubeSet (originCube d m) s f
  have hbound := normalizedGagliardoESeminormOn_cube_le (E := E) hd hs0 hs hK hf
  change eLpNorm (Gagliardo.gagliardoKernel s 2 f) 2
    (Gagliardo.gagliardoCubeMeasure (originCube d m)) < ⊤
  rw [← Gagliardo.Internal.cubeGagliardoESeminorm_def, ← hid]
  exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top

/-! ## 4. `M1` + `M2`: `ForceBesovRegularity` at the §4.5 data -/

omit [NormedSpace ℝ E] in
/-- The Hölder seminorm bound is invariant under negation. -/
theorem holderSeminormBoundOn_neg {U : Set (Vec d)} {alpha K : ℝ} {f : Vec d → E}
    (hf : Support.HolderSeminormBoundOn U alpha K f) :
    Support.HolderSeminormBoundOn U alpha K (fun x => -f x) := by
  intro x hx y hy
  have h := hf x hx y hy
  have hnorm : ‖(-f x) - (-f y)‖ = ‖f x - f y‖ := by
    rw [show (-f x) - (-f y) = -(f x - f y) by abel, norm_neg]
  rw [hnorm]
  exact h

/-- **`ForceBesovRegularity` from the §4.5 Hölder normalization.**  This is the
hypothesis the coarse-graining right-hand side itself carries, discharged at the frozen root's own
data
binders. -/
theorem forceBesovRegularity_of_holderHalf [NeZero d] {m : ℤ} {K s : ℝ}
    {g : Vec d → Vec d} (hd : 1 ≤ d) (hs0 : 0 < s) (hs : s < 1 / 2) (hK : 0 ≤ K)
    (hg : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K g) :
    ForceBesovRegularity (originCube d m) s g :=
  forceBesovRegularity_of_memWsp (originCube d m) g hs0 (by linarith only [hs])
    (memLp_two_normalizedCubeMeasure_of_holderHalf hK hg)
    (memWsp_of_holderHalf hd hs0 hs hK hg)

/-- The same for the NEGATED force, which is the forcing convention and the
shape the Step-2a display consumes. -/
theorem forceBesovRegularity_neg_of_holderHalf [NeZero d] {m : ℤ} {K s : ℝ}
    {g : Vec d → Vec d} (hd : 1 ≤ d) (hs0 : 0 < s) (hs : s < 1 / 2) (hK : 0 ≤ K)
    (hg : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K g) :
    ForceBesovRegularity (originCube d m) s (fun x => -g x) :=
  forceBesovRegularity_of_holderHalf hd hs0 hs hK (holderSeminormBoundOn_neg hg)

/-! ## 6. `M3`: the mean term of the `∇h` leg, priced by the root's `KhInf` -/

/-- Each coordinate average of a sup-bounded field is bounded by the same
constant.  (`cubeAverage` is the volume-normalized restricted Bochner integral;
no integrability side condition is needed — the bound is the `‖∫‖ ≤ C · vol`
estimate, valid with the junk value `0` as well.) -/
theorem abs_cubeAverage_le_of_bound {Q : TriadicCube d} {f : Vec d → ℝ} {K : ℝ}
    (hf : ∀ x ∈ openCubeSet Q, |f x| ≤ K) :
    |cubeAverage Q f| ≤ K := by
  have hset : MeasurableSet (openCubeSet Q) := (isOpen_openCubeSet _).measurableSet
  have : IsFiniteMeasure (volume.restrict (cubeSet Q)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact volume_cubeSet_lt_top _
  have hae : ∀ᵐ x ∂(volume.restrict (cubeSet Q)), ‖f x‖ ≤ K := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact ae_restrict_of_forall_mem hset hf
  have hint : ‖∫ x in cubeSet Q, f x ∂volume‖ ≤
      K * (volume.restrict (cubeSet Q)).real Set.univ :=
    norm_integral_le_of_norm_le_const hae
  have hvol : (volume.restrict (cubeSet Q)).real Set.univ = cubeVolume Q := by
    rw [Measure.real, Measure.restrict_apply_univ, volume_cubeSet_toReal]
  rw [hvol] at hint
  have hVpos : 0 < cubeVolume Q := cubeVolume_pos Q
  rw [cubeAverage, abs_mul, abs_of_pos (inv_pos.mpr hVpos)]
  have hbound : |∫ x in cubeSet Q, f x ∂volume| ≤ K * cubeVolume Q := hint
  calc (cubeVolume Q)⁻¹ * |∫ x in cubeSet Q, f x ∂volume|
      ≤ (cubeVolume Q)⁻¹ * (K * cubeVolume Q) :=
        mul_le_mul_of_nonneg_left hbound (inv_pos.mpr hVpos).le
    _ = K := by field_simp

/-- **`M3`, the mean term.**  `‖⨍_{□} ∇h‖ ≤ √d · K_∞` whenever `‖∇h‖ ≤ K_∞`
pointwise on the cube — the root's `KhInf` binder verbatim.  The `√d` is the
`vecNormSq`-versus-supremum-norm conversion, the standing ambient
convention. -/
theorem sqrt_vecNormSq_cubeAverageVec_le {Q : TriadicCube d} {F : Vec d → Vec d} {K : ℝ}
    (hK : 0 ≤ K) (hF : ∀ x ∈ openCubeSet Q, ‖F x‖ ≤ K) :
    Real.sqrt (vecNormSq (cubeAverageVec Q F)) ≤ Real.sqrt (d : ℝ) * K := by
  have hcoord : ∀ i : Fin d, |cubeAverage Q (fun x => F x i)| ≤ K := by
    intro i
    refine abs_cubeAverage_le_of_bound ?_
    intro x hx
    refine le_trans ?_ (hF x hx)
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm (F x) i
  have hsum : vecNormSq (cubeAverageVec Q F) ≤ (d : ℝ) * K ^ (2 : ℕ) := by
    have hterm : ∀ i : Fin d,
        cubeAverageVec Q F i * cubeAverageVec Q F i ≤ K ^ (2 : ℕ) := by
      intro i
      have h := hcoord i
      have hsq : |cubeAverage Q (fun x => F x i)| ^ (2 : ℕ) ≤ K ^ (2 : ℕ) :=
        pow_le_pow_left₀ (abs_nonneg _) h 2
      have habs : |cubeAverage Q (fun x => F x i)| ^ (2 : ℕ) =
          cubeAverageVec Q F i * cubeAverageVec Q F i := by
        rw [sq_abs]
        rw [cubeAverageVec]
        ring
      linarith only [hsq, habs]
    have hle : ∑ _i : Fin d, K ^ (2 : ℕ) = (d : ℝ) * K ^ (2 : ℕ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [vecNormSq, vecDot]
    calc ∑ i : Fin d, cubeAverageVec Q F i * cubeAverageVec Q F i
        ≤ ∑ _i : Fin d, K ^ (2 : ℕ) := Finset.sum_le_sum fun i _ => hterm i
      _ = (d : ℝ) * K ^ (2 : ℕ) := hle
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  calc Real.sqrt (vecNormSq (cubeAverageVec Q F))
      ≤ Real.sqrt ((d : ℝ) * K ^ (2 : ℕ)) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (d : ℝ) * K := by
        rw [Real.sqrt_mul hdnn, Real.sqrt_sq hK]

end

end Algsuperdiff.Section4.Provider.Homogenization
