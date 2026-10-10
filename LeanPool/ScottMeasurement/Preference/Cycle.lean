/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import Mathlib.Order.Defs.Unbundled

/-!
# Local reductions in Scott's cycle argument

These lemmas are the three local moves used on pp. 8--9 of Scott (1964).
They are kept separate from the linear-inequality interface so that the
finite-array cancellation proof does not depend on names in §1.
-/

@[expose] public section

namespace Scott1964.MeasurementStructures

theorem preference_transitive_of_quadA {A : Type u} {P : A → A → Prop}
    (hirr : ∀ x, ¬ P x x)
    (hquad : ∀ x y z w, P x y → P z w → P x w ∨ P z y) :
    IsTrans A P := by
  constructor
  intro x y z hxy hyz
  rcases hquad x y y z hxy hyz with hxz | hyy
  · exact hxz
  · exact (hirr y hyy).elim

/-- Scott's first shortening move, for `z P x P y Q w`.
Here `y Q w` abbreviates `¬ w P y`. -/
theorem preference_shorten_ppq {A : Type u} {P : A → A → Prop}
    (hquad : ∀ x y z w, P x y → P z x → P w y ∨ P z w) {z x y w : A}
    (hzx : P z x) (hxy : P x y) (hyw : ¬ P w y) :
    P z w := by
  rcases hquad x y z w hxy hzx with hwy | hzw
  · exact (hyw hwy).elim
  · exact hzw

/-- The rotated form of Scott's first shortening move, for `w Q z P x P y`.
Here `w Q z` abbreviates `¬ z P w`. -/
theorem preference_shorten_qpp {A : Type u} {P : A → A → Prop}
    (hquad : ∀ x y z w, P x y → P z x → P w y ∨ P z w) {w z x y : A}
    (hwz : ¬ P z w) (hzx : P z x) (hxy : P x y) :
    P w y := by
  rcases hquad x y z w hxy hzx with hwy | hzw
  · exact hwy
  · exact (hwz hzw).elim

/-- Scott's alternating shortening move, for `x P y Q z P w`.
Here `y Q z` abbreviates `¬ z P y`. -/
theorem preference_shorten_pqp {A : Type u} {P : A → A → Prop}
    (hquad : ∀ x y z w, P x y → P z w → P x w ∨ P z y) {x y z w : A}
    (hxy : P x y) (hyz : ¬ P z y) (hzw : P z w) :
    P x w := by
  rcases hquad x y z w hxy hzw with hxw | hzy
  · exact hxw
  · exact (hyz hzy).elim

end Scott1964.MeasurementStructures
