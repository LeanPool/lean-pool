/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityWeakGradientProduct
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalProductMemLp
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalGradientLp
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityComponentConvergence
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalVelocityLp
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Stability S1Weak Gradient

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- The weak-gradient clause of (S1) is preserved by the convergences in
`thm:stability`; it need not be assumed for the limit. -/
theorem stability_s1_weak_gradient_on_localBox
    {Ω Ω' : Set Vec3} {I J : Set ℝ} {q : ℝ}
    (u : ℕ → ParabolicPoint → Vec3)
    (Du : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (p : ℕ → ParabolicPoint → ℝ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (hsol : ∀ n, IsSuitableWeakSolution Ω I q (u n) (Du n) (p n) 0)
    (hbox : localBox Ω I Ω' J)
    (huConv : Tendsto
      (fun n => eLpNorm (u n - v) 3
        (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0))
    (hDv : MemLp Dv 2 (volume.restrict (spaceTimeSet Ω' J)))
    (hDuWeak : ∀ i j : Fin 3, ∀ w : Vec3 × ℝ → ℝ,
      MemLp w 2 ((volume.restrict Ω').prod (volume.restrict J)) →
      Tendsto (fun n => ∫ z, Du n (z.1, z.2) i j * w z
        ∂(volume.restrict Ω').prod (volume.restrict J)) atTop
        (nhds (∫ z, Dv (z.1, z.2) i j * w z
          ∂(volume.restrict Ω').prod (volume.restrict J)))) :
    ∀ i : Fin 3, ∀ᵐ t ∂(volume.restrict J),
      HasWeakGradientOn Ω' (fun x => v (x, t) i)
        (fun x => Dv (x, t) i) := by
  have hboxCopy := hbox
  obtain ⟨hΩopen, hΩcompact, _hΩsub, _hJconn, hJcompact, _hJsub⟩ := hboxCopy
  have hΩfinite : (volume : Measure Vec3) Ω' < ⊤ :=
    lt_of_le_of_lt (measure_mono subset_closure) hΩcompact.measure_lt_top
  have hJfinite : (volume : Measure ℝ) J < ⊤ :=
    lt_of_le_of_lt (measure_mono subset_closure) hJcompact.measure_lt_top
  have huN (n : ℕ) : MemLp (u n) 3
      (volume.restrict (spaceTimeSet Ω' J)) :=
    stability_velocity_memLp_three_on_localBox (hsol n) hbox
  have hv : MemLp v 3 (volume.restrict (spaceTimeSet Ω' J)) :=
    Lp.memLp_of_cauchy_tendsto (by norm_num) huN v huConv
  have huProd (n : ℕ) : MemLp
      (fun z : Vec3 × ℝ => u n (z.1, z.2)) 3
      ((volume.restrict Ω').prod (volume.restrict J)) :=
    stability_memLp_localBox_prod hbox (huN n)
  have hDProd (n : ℕ) : MemLp
      (fun z : Vec3 × ℝ => Du n (z.1, z.2)) 2
      ((volume.restrict Ω').prod (volume.restrict J)) :=
    stability_memLp_localBox_prod hbox
      (stability_gradient_memLp_two_on_localBox (hsol n) hbox)
  have hdProd : MemLp
      (fun z : Vec3 × ℝ => Dv (z.1, z.2)) 2
      ((volume.restrict Ω').prod (volume.restrict J)) :=
    stability_memLp_localBox_prod hbox hDv
  have hconvProd := stability_eLpNorm_tendsto_localBox_prod hbox 3 u v
    (fun n => (huN n).aestronglyMeasurable) hv.aestronglyMeasurable huConv
  intro i
  have hconvI := stability_tendsto_eLpNorm_component_three
    ((volume.restrict Ω').prod (volume.restrict J))
    (fun n z => u n (z.1, z.2)) (fun z => v (z.1, z.2)) huProd hconvProd i
  have hgradN (n : ℕ) (j : Fin 3) :
      ∀ᵐ t ∂(volume.restrict J),
        HasWeakPartialDerivOn Ω' j (fun x => u n (x, t) i)
          (fun x => Du n (x, t) i j) := by
    have hdata := (isSuitableWeakSolution_iff_integrable.mp (hsol n)).toData
    filter_upwards [hdata.hasWeakGradientOn_slice hbox i] with t ht
    exact ht j
  have hpartial (j : Fin 3) :
      ∀ᵐ t ∂(volume.restrict J),
        HasWeakPartialDerivOn Ω' j (fun x => v (x, t) i)
          (fun x => Dv (x, t) i j) := by
    have huI (n : ℕ) : MemLp (fun z : Vec3 × ℝ => u n (z.1, z.2) i) 3
        ((volume.restrict Ω').prod (volume.restrict J)) :=
      (memLp_pi_iff.mp (huProd n)) i
    have hDI (n : ℕ) : MemLp (fun z : Vec3 × ℝ => Du n (z.1, z.2) i j) 2
        ((volume.restrict Ω').prod (volume.restrict J)) :=
      (memLp_pi_iff.mp ((memLp_pi_iff.mp (hDProd n)) i)) j
    have hdI : MemLp (fun z : Vec3 × ℝ => Dv (z.1, z.2) i j) 2
        ((volume.restrict Ω').prod (volume.restrict J)) :=
      (memLp_pi_iff.mp ((memLp_pi_iff.mp hdProd) i)) j
    exact stability_weak_partial_on_localBox_of_product_limits
      hΩopen hΩfinite hJfinite
      (fun n z => u n (z.1, z.2) i)
      (fun n z => Du n (z.1, z.2) i j)
      (fun z => v (z.1, z.2) i)
      (fun z => Dv (z.1, z.2) i j) j
      huI hDI hdI hconvI (hDuWeak i j) (fun n => hgradN n j)
  change ∀ᵐ t ∂(volume.restrict J), ∀ j : Fin 3,
    HasWeakPartialDerivOn Ω' j (fun x => v (x, t) i)
      (fun x => Dv (x, t) i j)
  rw [ae_all_iff]
  intro j
  exact hpartial j

end CKN
