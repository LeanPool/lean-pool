/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Regularity.TopBoundaryEpsilon
public import LeanPool.CIVAxisymmetric.Regularity.TopCylinderSmallness
public import LeanPool.CIVAxisymmetric.Statements.BoundedNearOrigin

/-!
# From interior smallness below the top slice to boundedness at the origin

Three closing facts for the Gustafson–Kang–Tsai criterion used at the end of the proof of
`lem:aniso:closure`: the finite halving recursion used to iterate the pressure decay; the passage
from bounds on the interior cylinders `Q_r(0, s)`, `s ∈ (-σ, 0)`, to the Theorem A integrand on
the backward cylinder `B_r × (-r², 0)` (monotone convergence in the top time, with the force
term controlled by a pointwise bound); and the conclusion `BoundedNearOrigin` from smallness of
that integrand, by the top-boundary form of CKN's Theorem A and continuity of `u` inside `Q`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- A finite halving recursion `a_{n+1} ≤ a_n / 2 + b` for `n < N` gives `a_N ≤ 2^{-N} a_0 + 2b`. -/
theorem gkt_le_half_pow_of_forall_lt {a : ℕ → ℝ} {b : ℝ} {N : ℕ} (hb : 0 ≤ b)
    (hrec : ∀ n < N, a (n + 1) ≤ (1 / 2 : ℝ) * a n + b) :
    a N ≤ (1 / 2 : ℝ) ^ N * a 0 + 2 * b := by
  have key : ∀ m, m ≤ N → a m ≤ (1 / 2 : ℝ) ^ m * a 0 + (2 - 2 * (1 / 2 : ℝ) ^ m) * b := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (Nat.le_of_succ_le hk)
      have h2 := hrec k (Nat.lt_of_succ_le hk)
      rw [pow_succ]
      nlinarith only [h1, h2, hb]
  have h := key N le_rfl
  have hp : 0 ≤ (1 / 2 : ℝ) ^ N * b := by positivity
  nlinarith only [h, hp]

/-- If the velocity and pressure integrals over `Q_r(0, s)` are at most `τ r²` for every `s ∈
(-σ, 0)`, `σ ≤ r²`, then the Theorem A integrand over the backward cylinder `B_r × (-r², 0)` is
at most `(2τ + (4π/3) M_f^q r^{3q}) r²`, where `M_f` bounds the force on `Q`. -/
theorem gkt_topCylinder_small_of_interior {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMbound : ∀ z ∈ unitCylinder, vec3EuclideanNorm (f z) ≤ Mf)
    {r σ τ : ℝ} (hτ : 0 ≤ τ) (hr : 0 < r) (hr2 : r ≤ 1 / 2) (hσ : 0 < σ) (hσr : σ ≤ r ^ 2)
    (hsmall : ∀ s ∈ Ioo (-σ) 0,
        (∫⁻ z in parabolicCylinder (0 : Vec3) s r,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ)) ≤ ENNReal.ofReal (τ * r ^ 2) ∧
        (∫⁻ z in parabolicCylinder (0 : Vec3) s r,
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)) ≤ ENNReal.ofReal (τ * r ^ 2)) :
    (∫⁻ z in vec3Ball (0 : Vec3) r ×ˢ Ioo (-(r ^ 2)) 0,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (r ^ (3 * q - 3)) * ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
      ENNReal.ofReal ((2 * τ + 4 * Real.pi / 3 * Mf ^ q * r ^ (3 * q)) * r ^ 2) := by
  have hq : (0 : ℝ) < q := lt_trans (by norm_num) hsol.2.2.2.1
  refine lintegral_topCylinder_le_of_forall_lt 0 r σ hσ _ _ ?_
  intro s hs
  obtain ⟨hvel, hpr⟩ := hsmall s hs
  have hs0 : s < 0 := hs.2
  have hr1 : r < 1 := by linarith only [hr2]
  have hlow : -1 < s - r ^ 2 := by
    have h1 := hs.1
    nlinarith only [h1, hσr, hr, hr2]
  have hclo : closure (parabolicCylinder (0 : Vec3) s r) ⊆
      spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0) :=
    closure_parabolicCylinder_subset_unitCylinder 0 s r hr hs0 hlow
      (fun _ hy => lt_of_le_of_lt hy hr1)
  have hsubU : parabolicCylinder (0 : Vec3) s r ⊆ unitCylinder :=
    subset_closure.trans hclo
  have hmeasQ : MeasurableSet (parabolicCylinder (0 : Vec3) s r) :=
    measurableSet_parabolicCylinder _ _ _
  calc (∫⁻ z in vec3Ball (0 : Vec3) r ×ˢ Ioo (-(r ^ 2)) s,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (r ^ (3 * q - 3)) * ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q)
      ≤ ∫⁻ z in parabolicCylinder (0 : Vec3) s r,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (r ^ (3 * q - 3)) * ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q :=
        lintegral_mono_set (topSlice_subset_parabolicCylinder 0 s r hs0.le)
    _ = (∫⁻ z in parabolicCylinder (0 : Vec3) s r,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ)) +
        (∫⁻ z in parabolicCylinder (0 : Vec3) s r, ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)) +
        (∫⁻ z in parabolicCylinder (0 : Vec3) s r, ENNReal.ofReal (r ^ (3 * q - 3)) *
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) :=
        lintegral_velocity_pressure_force_split
          (aestronglyMeasurable_velocity_of_closure_subset hsol hr hclo)
          (aestronglyMeasurable_pressure_of_subset henergy hsubU)
    _ ≤ ENNReal.ofReal (τ * r ^ 2) + ENNReal.ofReal (τ * r ^ 2) +
        ENNReal.ofReal (r ^ (3 * q - 3) * Mf ^ q) * volume (parabolicCylinder (0 : Vec3) s r) := by
        gcongr
        exact lintegral_force_term_le hMf0 hMbound hmeasQ hsubU hr.le hq
    _ = ENNReal.ofReal ((2 * τ + 4 * Real.pi / 3 * Mf ^ q * r ^ (3 * q)) * r ^ 2) := by
        rw [volume_parabolicCylinder_eq 0 s r hr.le,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by
            positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have h := force_scale_real_fixed (q := q) hr
        linear_combination Mf ^ q * h

/-- The top-boundary Theorem A in the form used here: there is `ε₀ > 0`, depending only on `q`,
such that smallness `≤ ε₀ r²` of the Theorem A integrand on one backward cylinder `B_r × (-r²,
0)`, `r ≤ 1/2`, makes `(0, 0)` a regular point, for a velocity continuous inside `Q`. -/
theorem gkt_boundedNearOrigin_of_top_small (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3) (r : ℝ), 0 < r → r ≤ 1 / 2 →
        IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f →
        ContinuousOn (fun z : Vec3 × ℝ => u z) unitCylinder →
        (∫⁻ z in vec3Ball (0 : Vec3) r ×ˢ Ioo (-(r ^ 2)) 0,
            ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
              ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
              ENNReal.ofReal (r ^ (3 * q - 3)) *
                ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
          ENNReal.ofReal (ε₀ * r ^ 2) →
        BoundedNearOrigin u := by
  obtain ⟨ε₀, hε₀, K, -, hmain⟩ := norm_le_of_small_L3_top_of_continuousOn q hq
  refine ⟨ε₀, hε₀, ?_⟩
  intro u Du p f r hr hr2 hsol hu hsm
  have hQ : vec3Ball (0 : Vec3) r ×ˢ Ioo (-(r ^ 2)) 0 ⊆
      spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    refine ⟨?_, ?_, ht.2⟩
    · have hx' : vec3EuclideanNorm (x - 0) < r := hx
      change vec3EuclideanNorm (x - 0) < 1
      linarith only [hx', hr2]
    · have hr1 : r ^ 2 < 1 := by nlinarith only [hr, hr2]
      linarith only [ht.1, hr1]
  have hcont : ContinuousOn (fun z : Vec3 × ℝ => u z)
      (vec3Ball 0 (r / 2) ×ˢ Ioo (-(r ^ 2) / 4) 0) := by
    refine hu.mono ?_
    intro z hz
    refine hQ ⟨vec3Ball_mono (by linarith only [hr]) hz.1, ?_, hz.2.2⟩
    have := hz.2.1
    nlinarith only [this, hr]
  have hb := hmain (vec3Ball 0 1) (Ioo (-1) 0) u Du p f 0 r hr hsol hQ hsm hcont
  refine ⟨r / 2, r ^ 2 / 4, K / r, by positivity, by positivity, ?_⟩
  intro x hx t ht
  refine hb (x, t) ⟨hx, ?_, ht.2⟩
  have := ht.1
  linarith only [this]

end CIV
