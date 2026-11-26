/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Print.Shows

/-! # Uniform bounds for a printer with one physical state -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print.Printer.Signal
open Coloring Assembly Rounds Surface Surface.Local
open MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout (Alphabet Key Place Sharing item)

variable {F K N X Z J I : Type} [Field F] {x y : Wire} {m d h ℓ M r t q D k n u j z : ℕ}
  {T b c g w σ : ℕ} {W : ℝ} {P : Input F x y h D T (c * b) g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} {left : Order.Exterior Q.left} {right : Order.Exterior Q.right}
  {U : Printer F K N m d h ℓ M r t q D k n u j z}
  {a : Atlas P.Occupied P.grid.Seam m d h} {π : Palette a w q}
  {β : P.Occupied ⊕ ℕ → K} {R₀ : Reference J I N P.Occupied P.grid.Seam Z X}
  {G : Record F (M * r) (M * t) P.Occupied P.grid.Seam K N}
  {hm : Matches R₀.world β s G} {index : ∀ v, Y.state v ↪ ℕ} {size : P.Occupied → ℕ}
  {ext : P.Occupied → Option N → Bool → ℕ} {old : P.V ↪ B m}
  {data : U.rows.obj} {status : (Children.Header m d).obj}
  (H : U.Signal Q left right a π β R₀ G hm index size ext old data status)

open SphereScale (Scales depth)

include H in
open scoped Classical in
theorem capacity (bound : P.FinalBounds Q σ j) (sc : Scales g σ D T j b c)
    (ha : M * r = c * b) (hb : M * t = c) (hM : M = SphereScale.chunks σ D) (hk : k
      = Sharing.allocation g σ)
    (hu : u * D ^ (Input.terminalExponent g σ) ≤ T)
    (hc : Input.terminalExponent g σ * D * T ≤ u * U.cap) (hz : depth σ D g j (c * b) < 2 ^ z) :
    ∃ (G₀ : (Key.share s Q).Geo P k) (B : U.Physical G₀ π old data status),
      B.rules.left = left ∧ B.rules.right = right ∧
      ∀ p : Layout.Profile s.scene.cell s.scene.level,
        Concentrated P (B.term p) (Input.terminalExponent g σ) n σ ∧
          ∀ i, Diagram.padWidth u (((Key.share s Q).backdrop.emitted p j).width i) / u ≤ U.cap := by
  subst M k
  let steer := H.parents.steer U.degree
  let G₀ := {bound.geometry sc with steer := steer}
  have hr := (bound.raw sc hb).with_steer steer
  have hs := hr.budgets sc ha hb rfl le_rfl n
  obtain ⟨B, hl, hr⟩ := H.physical G₀ (fun _ => rfl) rfl rfl (fun i
    => (bound.shape_bound sc i).trans_lt hz)
  refine ⟨G₀, B, hl, hr, fun p => ?_⟩
  have hC : 1 ≤ Input.terminalExponent g σ := by
    have := (Layout.Fanout.exponent_bounds (c := Sharing.radius (Sharing.allocation g σ)) (ℓ
      := σ) le_rfl).1
    exact le_trans (by omega) this
  have he := G₀.concentrated U.dyadic U.large hs p j U.pos le_rfl hu
  exact ⟨B.concentrated p he, Sharing.Geo.capacity U.dyadic U.large U.pos p he hC hc⟩

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print.Printer.Signal
end
