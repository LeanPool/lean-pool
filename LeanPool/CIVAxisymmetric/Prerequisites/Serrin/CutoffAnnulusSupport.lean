/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.CutoffProfiles
public import LeanPool.CIVAxisymmetric.Statements.MultiPartial
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian

/-!
# Support and smoothness of a cutoff's spatial multi-index derivatives

The ball cutoff `serrinBallCutoff x ρ`, lifted to a time-independent function of
`ParabolicPoint`, is constant (`1` near `x`, `0` past radius `ρ`) on the two open sets flanking
the annulus `ρ/2 ≤ |y - x| ≤ ρ`, so every nonzero spatial multi-index derivative of it vanishes
there and is supported in that compact annulus; every such derivative, including the zeroth, is
globally smooth. These are the facts that make the cutoff-times-kernel product in the interior
estimates of
`lem:aniso:annulus` a smooth, compactly supported function away from the Newtonian kernel's
singularity, ready for integration by parts.
-/

public section

open Set Filter
open CKN.Foundation.Parabolic CKN

noncomputable section



namespace CIV

/-! ## Part 1: peeling one derivative off a multi-index -/

private theorem multiPartial_peel0 {γ : Fin 3 → ℕ} (h : 0 < γ 0) (g : ParabolicPoint → ℝ) :
    multiPartial g γ = spatialPartial (multiPartial g (Function.update γ 0 (γ 0 - 1))) 0 := by
  have hγ0 : γ 0 = (γ 0 - 1) + 1 := by omega
  have hu1 : Function.update γ 0 (γ 0 - 1) 1 = γ 1 := Function.update_of_ne (by decide) _ _
  have hu2 : Function.update γ 0 (γ 0 - 1) 2 = γ 2 := Function.update_of_ne (by decide) _ _
  have hu0 : Function.update γ 0 (γ 0 - 1) 0 = γ 0 - 1 := Function.update_self 0 _ γ
  unfold multiPartial
  rw [hu0, hu1, hu2]
  conv_lhs => rw [hγ0]
  rw [Function.iterate_succ']
  rfl

private theorem multiPartial_peel1 {γ : Fin 3 → ℕ} (h0 : γ 0 = 0) (h1 : 0 < γ 1)
    (g : ParabolicPoint → ℝ) :
    multiPartial g γ = spatialPartial (multiPartial g (Function.update γ 1 (γ 1 - 1))) 1 := by
  have hγ1 : γ 1 = (γ 1 - 1) + 1 := by omega
  have hu0 : Function.update γ 1 (γ 1 - 1) 0 = γ 0 := Function.update_of_ne (by decide) _ _
  have hu1 : Function.update γ 1 (γ 1 - 1) 1 = γ 1 - 1 := Function.update_self 1 _ γ
  have hu2 : Function.update γ 1 (γ 1 - 1) 2 = γ 2 := Function.update_of_ne (by decide) _ _
  unfold multiPartial
  rw [hu0, hu1, hu2, h0]
  conv_lhs => rw [hγ1]
  rw [Function.iterate_succ']
  simp

private theorem multiPartial_peel2 {γ : Fin 3 → ℕ} (h0 : γ 0 = 0) (h1 : γ 1 = 0) (h2 : 0 < γ 2)
    (g : ParabolicPoint → ℝ) :
    multiPartial g γ = spatialPartial (multiPartial g (Function.update γ 2 (γ 2 - 1))) 2 := by
  have hγ2 : γ 2 = (γ 2 - 1) + 1 := by omega
  have hu0 : Function.update γ 2 (γ 2 - 1) 0 = γ 0 := Function.update_of_ne (by decide) _ _
  have hu1 : Function.update γ 2 (γ 2 - 1) 1 = γ 1 := Function.update_of_ne (by decide) _ _
  have hu2 : Function.update γ 2 (γ 2 - 1) 2 = γ 2 - 1 := Function.update_self 2 _ γ
  unfold multiPartial
  rw [hu0, hu1, hu2, h0, h1]
  conv_lhs => rw [hγ2]
  rw [Function.iterate_succ']
  simp

/-- A nonzero spatial multi-index derivative peels one derivative off the outermost
nonvanishing exponent. -/
theorem multiPartial_peel {γ : Fin 3 → ℕ} (hγ : γ 0 + γ 1 + γ 2 ≠ 0) (g : ParabolicPoint → ℝ) :
    ∃ (j : Fin 3) (γ' : Fin 3 → ℕ), γ' 0 + γ' 1 + γ' 2 + 1 = γ 0 + γ 1 + γ 2 ∧
      multiPartial g γ = spatialPartial (multiPartial g γ') j := by
  by_cases h0 : γ 0 = 0
  · by_cases h1 : γ 1 = 0
    · have h2 : 0 < γ 2 := by omega
      exact ⟨2, Function.update γ 2 (γ 2 - 1), by
        simp [Function.update_of_ne, Function.update_self, h0, h1]; omega,
        multiPartial_peel2 h0 h1 h2 g⟩
    · have h1' : 0 < γ 1 := Nat.pos_of_ne_zero h1
      exact ⟨1, Function.update γ 1 (γ 1 - 1), by
        simp [Function.update_of_ne, Function.update_self, h0]; omega,
        multiPartial_peel1 h0 h1' g⟩
  · have h0' : 0 < γ 0 := Nat.pos_of_ne_zero h0
    exact ⟨0, Function.update γ 0 (γ 0 - 1), by
      simp [Function.update_of_ne, Function.update_self]; omega,
      multiPartial_peel0 h0' g⟩

/-! ## Part 2: the cutoff's derivatives vanish off the annulus -/

private theorem multiPartial_lifted_cutoff_inner {x : Vec3} {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ n : ℕ, ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = n → ∀ t : ℝ, ∀ y : Vec3,
      vec3EuclideanNorm (y - x) < ρ / 2 →
      multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (y, t) =
        if n = 0 then 1 else 0 := by
  intro n
  induction n with
  | zero =>
    intro γ hγ t y hy
    have h0 : γ 0 = 0 := by omega
    have h1 : γ 1 = 0 := by omega
    have h2 : γ 2 = 0 := by omega
    simp only [multiPartial, h0, h1, h2, Function.iterate_zero, id_eq]
    change serrinBallCutoff x ρ y = 1
    exact (serrinBallCutoff_support x hρ y).1 hy.le
  | succ n ih =>
    intro γ hγ t y hy
    obtain ⟨j, γ', hγ'ord, hpeel⟩ := multiPartial_peel (γ := γ) (by omega)
      (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1)
    have hγ'n : γ' 0 + γ' 1 + γ' 2 = n := by omega
    have hconst : Set.EqOn (fun w : Vec3 => multiPartial
        (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ' (w, t))
        (fun _ => if n = 0 then (1 : ℝ) else 0) (vec3Ball x (ρ / 2)) :=
      fun w hw => ih γ' hγ'n t w hw
    have heq := Filter.eventuallyEq_of_mem ((isOpen_vec3Ball x (ρ / 2)).mem_nhds hy) hconst
    rw [hpeel]
    unfold spatialPartial
    rw [heq.fderiv_eq]
    simp

private theorem multiPartial_lifted_cutoff_outer {x : Vec3} {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ n : ℕ, ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = n → ∀ t : ℝ, ∀ y : Vec3,
      ρ < vec3EuclideanNorm (y - x) →
      multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (y, t) = 0 := by
  intro n
  induction n with
  | zero =>
    intro γ hγ t y hy
    have h0 : γ 0 = 0 := by omega
    have h1 : γ 1 = 0 := by omega
    have h2 : γ 2 = 0 := by omega
    simp only [multiPartial, h0, h1, h2, Function.iterate_zero, id_eq]
    exact (serrinBallCutoff_support x hρ y).2.1 hy.le
  | succ n ih =>
    intro γ hγ t y hy
    obtain ⟨j, γ', hγ'ord, hpeel⟩ := multiPartial_peel (γ := γ) (by omega)
      (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1)
    have hγ'n : γ' 0 + γ' 1 + γ' 2 = n := by omega
    have hopen : IsOpen {z : Vec3 | ρ < vec3EuclideanNorm (z - x)} := by
      have hcont : Continuous (fun z : Vec3 => vec3EuclideanNorm (z - x)) := by
        unfold vec3EuclideanNorm; fun_prop
      exact isOpen_lt continuous_const hcont
    have hconst : Set.EqOn (fun w : Vec3 => multiPartial
        (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ' (w, t))
        (fun _ => (0 : ℝ)) {z : Vec3 | ρ < vec3EuclideanNorm (z - x)} :=
      fun w hw => ih γ' hγ'n t w hw
    have heq := Filter.eventuallyEq_of_mem (hopen.mem_nhds hy) hconst
    rw [hpeel]
    unfold spatialPartial
    rw [heq.fderiv_eq]
    simp

/-! ## Part 3: compact support of a nonzero cutoff derivative -/

/-- A nonzero derivative of the lifted cutoff is supported in the closed annulus
`ρ/2 ≤ |y - x| ≤ ρ`. -/
theorem support_multiPartial_cutoff_subset {x : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {γ : Fin 3 → ℕ}
    (hγ : γ 0 + γ 1 + γ 2 ≠ 0) (t : ℝ) :
    Function.support (fun y : Vec3 => multiPartial
        (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (y, t)) ⊆
      {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧ vec3EuclideanNorm (y - x) ≤ ρ} := by
  intro y hy
  by_contra hcon
  simp only [Set.mem_ofPred_eq, not_and_or, not_le] at hcon
  apply hy
  rcases hcon with h | h
  · have := multiPartial_lifted_cutoff_inner hρ (γ 0 + γ 1 + γ 2) γ rfl t y h
    rwa [ite_eq_right hγ] at this
  · exact multiPartial_lifted_cutoff_outer hρ (γ 0 + γ 1 + γ 2) γ rfl t y h

/-- The compact annulus that carries a nonzero cutoff derivative. -/
theorem isCompact_cutoffAnnulus {x : Vec3} {ρ : ℝ} (hρ : 0 < ρ) :
    IsCompact {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧ vec3EuclideanNorm (y - x) ≤ ρ} := by
  have hsub : {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧ vec3EuclideanNorm (y - x) ≤ ρ} ⊆
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} := fun y hy => hy.2
  have hclosed : IsClosed
      {y : Vec3 | ρ / 2 ≤ vec3EuclideanNorm (y - x) ∧ vec3EuclideanNorm (y - x) ≤ ρ} := by
    have hcont : Continuous (fun y : Vec3 => vec3EuclideanNorm (y - x)) := by
      unfold vec3EuclideanNorm; fun_prop
    exact (isClosed_le continuous_const hcont).inter (isClosed_le hcont continuous_const)
  have hcompactBall : IsCompact {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} := by
    rw [← closure_vec3Ball hρ]
    exact isCompact_closure_vec3Ball hρ
  exact IsCompact.of_isClosed_subset hcompactBall hclosed hsub

/-- A nonzero derivative of the lifted cutoff has compact support. -/
theorem hasCompactSupport_multiPartial_cutoff {x : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {γ : Fin 3 → ℕ}
    (hγ : γ 0 + γ 1 + γ 2 ≠ 0) (t : ℝ) :
    HasCompactSupport (fun y : Vec3 => multiPartial
      (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (y, t)) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_cutoffAnnulus hρ)
    (support_multiPartial_cutoff_subset hρ hγ t)

/-! ## Part 4: global smoothness of a cutoff derivative -/

private theorem contDiff_multiPartial_cutoff_aux {x : Vec3} {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ n : ℕ, ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = n → ∀ t : ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => multiPartial
        (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (y, t)) := by
  intro n
  induction n with
  | zero =>
    intro γ hγ t
    have h0 : γ 0 = 0 := by omega
    have h1 : γ 1 = 0 := by omega
    have h2 : γ 2 = 0 := by omega
    simp only [multiPartial, h0, h1, h2, Function.iterate_zero, id_eq]
    exact (serrinBallCutoff_support x hρ 0).2.2
  | succ n ih =>
    intro γ hγ t
    obtain ⟨j, γ', hγ'ord, hpeel⟩ := multiPartial_peel (γ := γ) (by omega)
      (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1)
    have hγ'n : γ' 0 + γ' 1 + γ' 2 = n := by omega
    have hIH := ih γ' hγ'n t
    have heq : (fun y : Vec3 => multiPartial (fun z : ParabolicPoint =>
        serrinBallCutoff x ρ z.1) γ (y, t)) =
        fun y : Vec3 => spatialPartial (multiPartial (fun z : ParabolicPoint =>
          serrinBallCutoff x ρ z.1) γ') j (y, t) := by
      funext y; rw [hpeel]
    rw [heq]
    unfold spatialPartial
    exact contDiff_spatialDeriv_smooth hIH j

/-- Every spatial multi-index derivative of the lifted cutoff is smooth. -/
theorem contDiff_multiPartial_cutoff (x : Vec3) {ρ : ℝ} (hρ : 0 < ρ) (γ : Fin 3 → ℕ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => multiPartial
      (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (y, t)) :=
  contDiff_multiPartial_cutoff_aux hρ (γ 0 + γ 1 + γ 2) γ rfl t

end CIV
