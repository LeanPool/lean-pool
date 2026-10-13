/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderExistence

/-!
# CubeSchauderCore

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the zero-datum core and the assembly at the frozen brackets

`ZeroDatumCubeSchauder d C0` is the **zero-datum, unit-diffusivity** interior +
boundary `C^{1,1/2}` statement on the origin cubes: for a `C^{0,1/2}` forcing
`G` there is an `H¹₀(□_m)` solution of `-Δw = ∇·G` whose own gradient
representative satisfies

```text
  ‖∇w‖_{L^∞(□_m)} ≤ C0 · 3^{m/2} · [G]_{C^{0,1/2}(□_m)} ,
  [∇w]_{C^{0,1/2}(□_m)} ≤ C0 · [G]_{C^{0,1/2}(□_m)} .
```

`cube_schauder_of_zeroDatumCubeSchauder` derives from it the **byte-exact
body** of the frozen external `Algsuperdiff.Frozen.External.cube_schauder`,
with `C(d,s) = 2· + 1` produced before the scale, the diffusivity and the data.
The three reductions performed here are the route's steps (b), (e) and the `s ≤
1/2` interpolation:

* *diffusivity* (linearity): `-sigma Δ v = ∇·g` is `-Δ v = ∇·(sigma⁻¹ g)`;
* *datum* (affine shift): `w := v - h` solves the zero-datum problem at the
  forcing `G := sigma⁻¹ g + ∇h`, whose `C^{0,1/2}` seminorm is at most
  `sigma⁻¹ Kg + Kh`;
* *exponent*: on a set of diameter `3^m`, `[·]_{C^{0,s}} ≤ 3^{(1/2-s)m}
  [·]_{C^{0,1/2}}`, which is exactly the weight the frozen gauge carries.

The scale uniformity is **not** reduced away: `ZeroDatumCubeSchauder` quantifies
over all `m : ℤ` with one constant, because the interior/boundary proof is
naturally scale-aware on the triadic carriers.

## References

* ABK26; `Algsuperdiff/Frozen/External/CubeSchauder.lean`.
* Armstrong--Kuusi, *Elliptic Regularity* (`ellipticregularity.tex`),
  Proposition `p.Schauder.C1alpha` — the interior route the residual core follows.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section4.Support

variable {d : ℕ}

/-! ## 1. The residual core -/

/-- **The zero-datum, unit-diffusivity cube Schauder core.**

For every scale `m` and every `C^{0,1/2}` forcing `G` on `□_m` there is an
`H¹₀(□_m)` weak solution of `-Δ w = ∇·G` whose own gradient representative is
bounded · 3^{m/2} · KG` and `C^{0,1/2}` with constant · KG`.

This is the interior + boundary estimate of the author's route (steps (c), (d)):
interior `C^{1,α}` off the pointwise `C^{1,1}` estimates for harmonic functions,
boundary by odd reflection across the met faces, corners by iterated partial
reflections.  It is stated for all `m` with one constant, so scale uniformity is
part of the core rather than a separate reduction. -/
def ZeroDatumCubeSchauder (d : ℕ) (C0 : ℝ) : Prop :=
  ∀ (m : ℤ) (G : Vec d → Vec d) (KG : ℝ),
    HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G →
      ∃ w : H10Function (openCubeSet (originCube d m)),
        IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
            (openCubeSet (originCube d m)) w.toH1Function G ∧
          (∀ x ∈ openCubeSet (originCube d m),
              ‖w.toH1Function.grad x‖ ≤ C0 * Real.rpow 3 ((m : ℝ) / 2) * KG) ∧
          HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) (C0 * KG)
            w.toH1Function.grad

/-! ## 2. The `rpow` identities of the gauge -/

theorem rpow_three_neg (t : ℝ) : Real.rpow 3 (-t) = (Real.rpow 3 t)⁻¹ :=
  Real.rpow_neg (by norm_num) t

/-- The gauge weight factorizes: `3^{(1/2-s)m} = 3^{m/2} · (3^{sm})⁻¹`. -/
theorem rpow_three_half_sub (s : ℝ) (m : ℤ) :
    Real.rpow 3 ((1 / 2 - s) * (m : ℝ))
      = Real.rpow 3 ((m : ℝ) / 2) * (Real.rpow 3 (s * (m : ℝ)))⁻¹ := by
  have h1 : ((3 : ℝ) ^ (s * (m : ℝ)))⁻¹ = (3 : ℝ) ^ (-(s * (m : ℝ))) :=
    (Real.rpow_neg (by norm_num) _).symm
  show (3 : ℝ) ^ ((1 / 2 - s) * (m : ℝ))
    = (3 : ℝ) ^ ((m : ℝ) / 2) * ((3 : ℝ) ^ (s * (m : ℝ)))⁻¹
  rw [h1, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-! ## 3. The assembly -/

/-- **The frozen cube Schauder conclusion, off the zero-datum core.**

The constant `C(d,s) = 2· + 1` is produced before the scale `m`, the
diffusivity `sigma` and the data, so the consumer's constant scope is the
frozen statement's own.  Nothing but `ZeroDatumCubeSchauder d and `0 ≤ is
assumed. -/
theorem cube_schauder_of_zeroDatumCubeSchauder {C0 : ℝ} (hC0 : 0 ≤ C0)
    (hcore : ZeroDatumCubeSchauder d C0) (dimension : 2 ≤ d)
    (s : ℝ) (s_pos : 0 < s) (s_le : s ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℤ) (sigma : ℝ), 0 < sigma →
        ∀ (g : Vec d → Vec d) (h : H1Function (openCubeSet (originCube d m)))
          (Kg KhInf Kh : ℝ),
          HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
          (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
          HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
          ∃ v : H1Function (openCubeSet (originCube d m)),
            IsDirichletSolutionOn (fun _ => sigma • (1 : Mat d)) (originCube d m) v h g ∧
            ∃ Ksup KHol : ℝ, 0 ≤ Ksup ∧ 0 ≤ KHol ∧
              (∀ x ∈ openCubeSet (originCube d m), ‖v.grad x‖ ≤ Ksup) ∧
              HolderSeminormBoundOn (openCubeSet (originCube d m)) s KHol v.grad ∧
              Real.rpow 3 (-(s * (m : ℝ))) * Ksup + KHol ≤
                C * (Real.rpow 3 (s * (m : ℝ)))⁻¹ *
                  (sigma⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
                    (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) := by
  have hd : 0 < d := by omega
  refine ⟨2 * C0 + 1, by linarith only [hC0], ?_⟩
  intro m sigma hsigma g h Kg KhInf Kh hKg hKhInf hKh
  -- signs of the data constants
  have hKg0 : 0 ≤ Kg := holderSeminormBoundOn_nonneg_openCubeSet hd hKg
  have hKh0 : 0 ≤ Kh := holderSeminormBoundOn_nonneg_openCubeSet hd hKh
  have hKhInf0 : 0 ≤ KhInf :=
    le_trans (norm_nonneg _) (hKhInf 0 (zero_mem_openCubeSet_originCube m))
  have hsinv : (0 : ℝ) ≤ sigma⁻¹ := inv_nonneg.2 hsigma.le
  have hKG0 : 0 ≤ sigma⁻¹ * Kg + Kh := by
    have hmul : 0 ≤ sigma⁻¹ * Kg := mul_nonneg hsinv hKg0
    linarith only [hmul, hKh0]
  -- the reduced forcing and its Hölder bound
  have hKGhol : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2)
      (sigma⁻¹ * Kg + Kh) (fun x => sigma⁻¹ • g x + h.grad x) :=
    holderSeminormBoundOn_add (holderSeminormBoundOn_smul_nonneg hKg hsinv) hKh
  obtain ⟨w, hweq, hwsup, hwhol⟩ :=
    hcore m (fun x => sigma⁻¹ • g x + h.grad x) (sigma⁻¹ * Kg + Kh) hKGhol
  -- square integrability of the pieces
  have hgL2 : MemVectorL2 (openCubeSet (originCube d m)) g :=
    memVectorL2_of_holderSeminormBoundOn hKg0 (by norm_num) hKg
  have hsgL2 : MemVectorL2 (openCubeSet (originCube d m)) (fun x => sigma⁻¹ • g x) :=
    hgL2.const_smul sigma⁻¹
  have hhgL2 : MemVectorL2 (openCubeSet (originCube d m)) h.grad := h.grad_memVectorL2
  have hshL2 : MemVectorL2 (openCubeSet (originCube d m)) (fun x => sigma • h.grad x) :=
    hhgL2.const_smul sigma
  have hswL2 : MemVectorL2 (openCubeSet (originCube d m))
      (fun x => sigma • w.toH1Function.grad x) :=
    w.toH1Function.grad_memVectorL2.const_smul sigma
  have hvgrad : ∀ x, (h + w.toH1Function).grad x = h.grad x + w.toH1Function.grad x :=
    fun x => by rw [H1Function.add_grad]
  -- the equation
  have hsol : IsDirichletSolutionOn (fun _ => sigma • (1 : Mat d)) (originCube d m)
      (h + w.toH1Function) h g := by
    refine ⟨⟨w, fun x => by rw [H1Function.add_toFun], hvgrad⟩, ?_⟩
    intro φ
    have hflux : ∀ x, matVecMul ((fun _ => sigma • (1 : Mat d)) x)
        ((h + w.toH1Function).grad x)
        = (fun x => sigma • h.grad x) x + (fun x => sigma • w.toH1Function.grad x) x := by
      intro x
      show matVecMul (sigma • (1 : Mat d)) ((h + w.toH1Function).grad x)
        = sigma • h.grad x + sigma • w.toH1Function.grad x
      rw [hvgrad x, matVecMul_smul_one, smul_add]
    rw [integral_vecDot_add_split hshL2 hswL2 hflux φ, integral_vecDot_smul_split,
      integral_vecDot_smul_split]
    have hcw := hweq φ
    have hcongr : (∫ x in openCubeSet (originCube d m),
        vecDot (matVecMul ((fun _ => (1 : Mat d)) x) (w.toH1Function.grad x))
          (φ.toH1Function.grad x) ∂volume)
        = ∫ x in openCubeSet (originCube d m),
          vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x) ∂volume :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        show vecDot (matVecMul (1 : Mat d) (w.toH1Function.grad x)) (φ.toH1Function.grad x)
          = vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x)
        rw [matVecMul_one])
    rw [hcongr, integral_vecDot_add_split (F := fun x => sigma⁻¹ • g x) (G := h.grad)
      (H := fun x => sigma⁻¹ • g x + h.grad x) hsgL2 hhgL2 (fun _ => rfl) φ,
      integral_vecDot_smul_split] at hcw
    rw [hcw]
    have hexp : ∀ A B : ℝ, sigma * B + sigma * -(sigma⁻¹ * A + B) = -A := by
      intro A B
      have hid : sigma * B + sigma * -(sigma⁻¹ * A + B) = -((sigma * sigma⁻¹) * A) := by ring
      rw [hid, mul_inv_cancel₀ (ne_of_gt hsigma), one_mul]
    exact hexp _ _
  -- the two constants
  have hQ0 : (0 : ℝ) < Real.rpow 3 ((m : ℝ) / 2) := rpow_three_pos _
  have hR0 : (0 : ℝ) < (Real.rpow 3 (s * (m : ℝ)))⁻¹ := inv_pos.2 (rpow_three_pos _)
  have hwlow := holderSeminormBoundOn_lower_exponent_originCube hwhol
    (mul_nonneg hC0 hKG0) s_pos s_le
  have hhlow := holderSeminormBoundOn_lower_exponent_originCube hKh hKh0 s_pos s_le
  rw [rpow_three_half_sub] at hwlow hhlow
  have hvhol : HolderSeminormBoundOn (openCubeSet (originCube d m)) s
      (Kh * (Real.rpow 3 ((m : ℝ) / 2) * (Real.rpow 3 (s * (m : ℝ)))⁻¹) +
        C0 * (sigma⁻¹ * Kg + Kh) *
          (Real.rpow 3 ((m : ℝ) / 2) * (Real.rpow 3 (s * (m : ℝ)))⁻¹))
      (h + w.toH1Function).grad := by
    intro x hx y hy
    rw [hvgrad x, hvgrad y]
    exact holderSeminormBoundOn_add hhlow hwlow x hx y hy
  have hvsup : ∀ x ∈ openCubeSet (originCube d m),
      ‖(h + w.toH1Function).grad x‖
        ≤ C0 * Real.rpow 3 ((m : ℝ) / 2) * (sigma⁻¹ * Kg + Kh) + KhInf := by
    intro x hx
    rw [hvgrad x]
    have h1 := hKhInf x hx
    have h2 := hwsup x hx
    have h3 : ‖h.grad x + w.toH1Function.grad x‖
        ≤ ‖h.grad x‖ + ‖w.toH1Function.grad x‖ := norm_add_le _ _
    linarith only [h1, h2, h3]
  refine ⟨h + w.toH1Function, hsol, _, _, ?_, ?_, hvsup, hvhol, ?_⟩
  · have hmul : 0 ≤ C0 * Real.rpow 3 ((m : ℝ) / 2) * (sigma⁻¹ * Kg + Kh) :=
      mul_nonneg (mul_nonneg hC0 hQ0.le) hKG0
    linarith only [hmul, hKhInf0]
  · have hQR : (0 : ℝ) ≤ Real.rpow 3 ((m : ℝ) / 2) * (Real.rpow 3 (s * (m : ℝ)))⁻¹ :=
      mul_nonneg hQ0.le hR0.le
    have h1 := mul_nonneg hKh0 hQR
    have h2 := mul_nonneg (mul_nonneg hC0 hKG0) hQR
    linarith only [h1, h2]
  · rw [rpow_three_neg]
    have hdiff : (2 * C0 + 1) * (Real.rpow 3 (s * (m : ℝ)))⁻¹ *
          (sigma⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
            (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh))
        - ((Real.rpow 3 (s * (m : ℝ)))⁻¹ *
              (C0 * Real.rpow 3 ((m : ℝ) / 2) * (sigma⁻¹ * Kg + Kh) + KhInf)
            + (Kh * (Real.rpow 3 ((m : ℝ) / 2) * (Real.rpow 3 (s * (m : ℝ)))⁻¹) +
              C0 * (sigma⁻¹ * Kg + Kh) *
                (Real.rpow 3 ((m : ℝ) / 2) * (Real.rpow 3 (s * (m : ℝ)))⁻¹)))
        = (Real.rpow 3 (s * (m : ℝ)))⁻¹ *
            (sigma⁻¹ * Kg * Real.rpow 3 ((m : ℝ) / 2) + 2 * C0 * KhInf) := by
      ring
    have hnn : (0 : ℝ) ≤ (Real.rpow 3 (s * (m : ℝ)))⁻¹ *
        (sigma⁻¹ * Kg * Real.rpow 3 ((m : ℝ) / 2) + 2 * C0 * KhInf) := by
      have h1 : (0 : ℝ) ≤ sigma⁻¹ * Kg * Real.rpow 3 ((m : ℝ) / 2) :=
        mul_nonneg (mul_nonneg hsinv hKg0) hQ0.le
      have h2 : (0 : ℝ) ≤ 2 * C0 * KhInf :=
        mul_nonneg (mul_nonneg (by norm_num) hC0) hKhInf0
      have h3 : (0 : ℝ) ≤ sigma⁻¹ * Kg * Real.rpow 3 ((m : ℝ) / 2) + 2 * C0 * KhInf := by
        linarith only [h1, h2]
      exact mul_nonneg hR0.le h3
    linarith only [hdiff, hnn]

end Algsuperdiff.Section4.Provider.Schauder
