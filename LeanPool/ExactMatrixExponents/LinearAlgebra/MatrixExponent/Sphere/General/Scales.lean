/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Layout.Squares
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coloring.Vector
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transcript.Seats
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rounds.Local
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Panel.Terminal
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Control.Initial
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Print.Children.Correct
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Compute
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Matching
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Prepare.Parcel
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Print.Shows
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Prepare.Status
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Panel.Shapes

/-! # Number of directed bundles at an input station -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
open Coloring Packing Finset

variable {F : Type} {a b : Wire} {h D T R g : ℕ} {W : ℝ} (P : Input F a b h D T R g W)

open scoped Classical in
/-- Only these stations can meet `v` at an internal wire. -/
abbrev region (v : P.diagram.V) :=
  {w : P.diagram.V // (P.place w).2 = (P.place v).2 ∧
    (P.place w).1 ∈ insert (P.place v).1 (P.adj (P.place v).1)}

open scoped Classical in
theorem region_bound (v : P.diagram.V) : Fintype.card (P.region v) ≤ (g + 1) * (100 * D) := by
  let N := insert (P.place v).1 (P.adj (P.place v).1)
  have hn : N.card ≤ g + 1 := (card_insert_le _ _).trans (Nat.add_le_add_right (P.degree _) _)
  let fiber (j : N) := {w // P.place w = (j.val, (P.place v).2)}
  let f (w : P.region v) : Σ j, fiber j :=
    ⟨⟨(P.place w.val).1, w.property.2⟩, w.val, Prod.ext rfl w.property.1⟩
  have hf : Function.Injective f := fun _ _ he => Subtype.ext (congrArg (fun x => x.2.val) he)
  calc
    _ ≤ Fintype.card (Σ j, fiber j) := Fintype.card_le_of_injective f hf
    _ = ∑ j, Fintype.card (fiber j) := Fintype.card_sigma
    _ ≤ ∑ _ : N, 100 * D := sum_le_sum fun _ _ => P.count _
    _ ≤ _ := by simpa using Nat.mul_le_mul_right (100 * D) hn

open scoped Classical in
/-- The least binary width whose power of two reaches the stated size. -/
def inputBits (g D : ℕ) := Nat.clog 2 (2 * ((g + 1) * (100 * D) + 1))

open scoped Classical in
/-- Reserve a direction bit and one additional remote name for the exterior. -/
theorem bundleCount (v : P.diagram.V) :
    Nonempty (Bool × Option (P.region v) ↪ B (inputBits g D)) := by
  apply Function.Embedding.nonempty_of_card_le
  rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_option, Fintype.card_fin]
  exact (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (P.region_bound v) 1)).trans
    (Nat.le_pow_clog (by decide) _)

open scoped Classical in
theorem width_cap (v : P.diagram.V) : P.diagram.arity v < 2 ^ (Nat.clog 2 (100 * D * T + 1)) := by
  have hv : (P.diagram.arity v : ℝ) ≤ (100 : ℝ) * D * T := by
    refine le_trans ?_ (P.mass (P.place v))
    unfold push
    simpa only [ite_true] using single_le_sum
      (f := fun w => if P.place w = P.place v then (P.diagram.arity w : ℝ) else 0)
      (fun _ _ => by positivity) (mem_univ v)
  have hh : P.diagram.arity v ≤ 100 * D * T := by exact_mod_cast hv
  exact (Nat.lt_succ_of_le hh).trans_le (Nat.le_pow_clog (by decide) _)

open scoped Classical in
theorem channel_cap {ℓ : ℕ} (hD : 2 * SphereScale.budget g ≤ D) :
    2 ^ (Nat.clog 2 (g + 1) + 1) ≤ D ^ (Sphere.Layout.Sharing.allocation g ℓ) + 1 := by
  have hb : 4 * (g + 1) ≤ D := by
    have h := Nat.le_mul_of_pos_right (10000000 * (1 + 4 * g)) (by omega : 0
      < Routing.Private.energyConstant + 1)
    unfold SphereScale.budget at hD
    omega
  calc
    _ ≤ 4 * (g + 1) := by
      rw [pow_succ]
      have := Transcript.pow_clog_le_twice (by omega : 0 < g + 1)
      omega
    _ ≤ D := hb
    _ ≤ _ := (Nat.le_self_pow (by unfold Sphere.Layout.Sharing.allocation; omega) _).trans
      (Nat.le_add_right _ _)

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
end

/- # The empty host needs no movement, labels or selectors -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
open Packing Finset

variable {F : Type} {x y : Wire} {h D T r g : ℕ} {W : ℝ}
  (P : Input F x y h D T r g W) [IsEmpty P.V]

open scoped Classical in
theorem noStations : IsEmpty P.diagram.V := ⟨fun v => isEmptyElim (P.place v).1⟩
open scoped Classical in
theorem noWires : IsEmpty P.diagram.E := ⟨fun e => isEmptyElim (P.place (P.diagram.source e)).1⟩

include P in
open scoped Classical in
theorem noExterior : IsEmpty (slots x ⊕ slots y) :=
  ⟨fun i => isEmptyElim (P.place (portEnd P.diagram i)).1⟩

open scoped Classical in
/-- Builds `LocalTerm F x y h u where V` with the specified `diagram`, `freeze`, `frame`,
`place`. -/
abbrev emptyTerm (u : ℕ) : LocalTerm F x y h u where
  V := P.V
  diagram := P.diagram
  freeze := ⟨fun _ => True, fun _ => trivial, fun e => isEmptyElim (P.place (P.diagram.source e)).1⟩
  frame := {
    place := P.place, frozen := fun _ => True, keep := fun _ => Iff.rfl
    N := P.adj, C := P.adj, ns := P.sym, cs := P.sym, sub := fun _ => Finset.Subset.refl _
    group := fun e => (P.edge e).1.symm
    edge := fun e => isEmptyElim (P.place (P.diagram.source e.val)).1
    full := fun e => isEmptyElim (P.place (P.diagram.source e)).1 }
  one v := isEmptyElim (P.place v).1
  width v := isEmptyElim (P.place v).1
  charge _ := 0
  cover v := isEmptyElim (P.place v).1
  floor v := isEmptyElim (P.place v).1

open scoped Classical in
theorem emptyConcentrated (u C d ℓ : ℕ) : Concentrated P (P.emptyTerm u) C d ℓ := by
  have hW := (show 0 ≤ (univ.image P.place).card * (D : ℝ) * T by positivity).trans P.occupied
  let _ : IsEmpty (P.emptyTerm u).freeze.Fixed := ⟨fun t => isEmptyElim (P.place t.val).1⟩
  let _ : IsEmpty (P.emptyTerm u).freeze.Core := ⟨fun t => isEmptyElim (P.place t.val).1⟩
  refine ⟨?_, fun v => isEmptyElim v, fun v => isEmptyElim v, ?_, ?_, ?_, ?_, ?_⟩
  · change Fintype.card P.V ≤ _; simp
  · simp only [Fintype.card_eq_zero, Nat.cast_zero, zero_mul]; positivity
  · exact fun v => isEmptyElim v
  · simp only [univ_eq_empty, sum_empty]; positivity
  · exact fun v => isEmptyElim v
  · simp only [univ_eq_empty, sum_empty]; positivity

open scoped Classical in
theorem emptyExpansion [Field F] (u C d ℓ A : ℕ) : LocalExpansion P u C d ℓ A :=
  ⟨Unit, inferInstance, fun _ => P.emptyTerm u, fun _ => 1,
    by simpa using Nat.one_le_pow _ 2 (by decide),
    fun _ _ => by simp, fun _ => P.emptyConcentrated ..⟩

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
end

/- # Locating a frozen collector by its short station name -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
open Coloring Assembly Sphere Surface Surface.Local Routing.Private
open Sphere.Layout (Place item)

variable {F K J : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
  {h D T b d g m ℓ H U : ℕ} {W : ℝ} (P : Input F x y h D T (d * b) g W)
  (p : P.Tools K ℓ m) (s : P.Occupied → Shape (SphereScale.probes ℓ D) b d)
  {z : P.Configuration p} (hz : (P.plant p s).Reach m (2 * g) H U z)
  {S : Scheme F} {r : S.format.obj} {portal : S.Presentation r P.diagram}
  {loc : P.Occupied ↪ B S.m × B S.h} {tone : B S.m → ℕ} {mobile : S.Vtx → Bool}
  (placed : P.Placed portal loc tone mobile)
  {β : P.Occupied ⊕ ℕ → J} {G : Record F (d * b) d P.Occupied P.grid.Seam J (B S.k)}
  (hm : Matches (P.reference p (finiteName S.k ∘ P.stationRank)).world β z G)
include placed

theorem namedKeeps (e : slots x ⊕ slots y) :
    let v := Packing.portEnd P.diagram e
    ∃ i : Place z.scene.cell, loc i.1 = ((portal.vertex v).1, (portal.vertex v).2.1) ∧
      (P.inputPorts p s hz).ports i = P.diagram.extLeft v ∧
      (P.outputPorts p s hz).ports i = P.diagram.extRight v ∧
      (hm.row i).name = some (portal.vertex v).2.2 ∧
      ∀ j, j.1 = i.1 → (hm.row j).name = (hm.row i).name → j = i := by
  intro v
  let i := P.draw p s hz e
  have pos (j : Place z.scene.cell) (w : P.diagram.V)
      (hn : (item z.scene.cell j).label.name = some w) :
      loc j.1 = ((portal.vertex w).1, (portal.vertex w).2.1) := by
    rw [← (P.reached_name p s hz (List.get_mem _ j.2) hn).2, placed.location]
  have row (j : Place z.scene.cell) :
      (hm.row j).name = (item z.scene.cell j).label.name.map (fun w => (portal.vertex w).2.2) := by
    have name : finiteName S.k ∘ P.stationRank = fun w => (portal.vertex w).2.2 := by
      funext w
      rw [Function.comp_apply, placed.name]
      exact Fin.ext (Nat.mod_eq_of_lt (portal.vertex w).2.2.isLt)
    rw [← name]
    exact (hm.represents j).name.symm
  have hn : (item z.scene.cell i).label.name = some v := P.draw_name p s hz e
  have hi : (hm.row i).name = some (portal.vertex v).2.2 := by rw [row, hn]; rfl
  refine ⟨i, pos i v hn, ?_, ?_, hi, ?_⟩
  · exact congrArg (fun a => a.elim [] P.diagram.extLeft) hn
  · exact congrArg (fun a => a.elim [] P.diagram.extRight) hn
  · intro j eq he
    rw [row j, hi] at he
    obtain ⟨w, hw, hs⟩ := Option.map_eq_some_iff.mp he
    have hl := (pos j w hw).symm.trans ((congrArg loc eq).trans (pos i v hn))
    obtain ⟨ha, hb⟩ := Prod.mk.inj hl
    have hv : w = v := portal.vertex.injective (Prod.ext ha (Prod.ext hb hs))
    exact (P.draw_eq p s hz e j (hw.trans (congrArg some hv))).symm

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
end

/- # Address widths for ordered input dictionaries -/

namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input

/-- The least binary width whose power of two reaches `100 * D + 1`. -/
abbrev stationBits (D : ℕ) := Nat.clog 2 (100 * D + 1)

/-- The least binary width whose power of two reaches `g + 1`. -/
abbrev channelBits (g : ℕ) := Nat.clog 2 (g + 1)

/-- The least binary width whose power of two reaches `100 * D * T + 1`. -/
abbrev widthBits (D T : ℕ) := Nat.clog 2 (100 * D * T + 1)

theorem widthBits_le (D T : ℕ) : widthBits D T ≤ stationBits D + Nat.clog 2 (T + 1) := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  exact (show 100 * D * T + 1 ≤ (100 * D + 1) * (T + 1) by ring_nf; omega).trans
    (Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _))

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input

/- # Dyadic and packet scales of the binary controller -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
open SphereScale

/-- Rounds the size up to the least power of two. -/
abbrev rounded (D : ℕ) := 2 ^ Nat.clog 2 D
/-- The quantity computed by `(2 * T) / (rounded D) ^ terminalExponent g (ℓ + 1)`. -/
abbrev unitSize (g ℓ D T : ℕ) := (2 * T) / (rounded D) ^ terminalExponent g (ℓ + 1)

/-- The quantity computed by `2 * budget g + 400 * (g + 1)`. -/
def threshold (g : ℕ) := 2 * budget g + 400 * (g + 1)

variable {D T g : ℕ}

theorem threshold_large (hD : threshold g ≤ D) : 2 ≤ D := by
  unfold threshold at hD
  omega

theorem threshold_packet (hD : threshold g ≤ D) : 400 * (g + 1) ≤ rounded D :=
  (Nat.le_add_left ..).trans (hD.trans (Nat.le_pow_clog (by decide) D))

theorem threshold_scales (hD : threshold g ≤ D) : 2 * budget g ≤ rounded D :=
  (Nat.le_add_right ..).trans (hD.trans (Nat.le_pow_clog (by decide) D))

theorem inputBits_round (g D : ℕ) : inputBits g D ≤ inputBits g (rounded D) := by
  unfold inputBits
  gcongr
  exact Nat.le_pow_clog (by decide) _

theorem doubled_log (T a B : ℕ) :
    B * (1 + a + Nat.clog 2 (2 * T + 1)) ≤ (2 * B) * (1 + a + Nat.clog 2 (T + 1)) := by
  have he : Nat.clog 2 (2 * T + 1) ≤ Nat.clog 2 (T + 1) + 1 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_succ]
    have := Nat.le_pow_clog (by decide : 1 < 2) (T + 1)
    omega
  rw [mul_comm 2 B, mul_assoc]
  exact Nat.mul_le_mul_left _ (by omega)

theorem packet_unit {ℓ : ℕ} (hD : 2 ≤ D) (hT : (rounded D) ^ terminalExponent g (ℓ + 1) ≤ 2 * T) :
    0 < unitSize g ℓ D T ∧ T ≤ unitSize g ℓ D T * D ^ (2 * terminalExponent g (ℓ + 1)) := by
  let C := terminalExponent g (ℓ + 1)
  let a := (rounded D) ^ C
  let u := unitSize g ℓ D T
  obtain ⟨hu, _, ht⟩ := floor_units (B := a) (pow_pos (by unfold rounded; positivity) _) hT
  have hd : rounded D ≤ D ^ 2 := (Transcript.pow_clog_le_twice (by omega : 0 < D)).trans
    (by rw [pow_two]; exact Nat.mul_le_mul_right _ hD)
  have ha : a ≤ D ^ (2 * C) := by rw [pow_mul]; exact Nat.pow_le_pow_left hd C
  have hb : 2 * T ≤ 2 * (u * a) := ht.trans_eq (mul_assoc ..)
  exact ⟨hu, (show T ≤ u * a by omega).trans (Nat.mul_le_mul_left _ ha)⟩

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
end

/- # Agreement between the terminal records and the printer -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere SphereScale Surface Surface.Local

variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
    {g ℓ D T b d p l j : ℕ} {W : ℝ} {S : Scheme F}
    (P : Input F x y S.h D T (d * b) g W)
    {z : S.format.obj} (A : P.HostChart S z)
    (sc : Scales g ℓ D T (p ^ l) b d) (hK : Ready K ℓ D g (p ^ l) b d)
    (s : P.Occupied → Shape (probes ℓ D) b d)

local notation "kit" => P.kit sc hK
local notation "world" => P.localWorld A sc hK s
local notation "Cfg" => design S g ℓ D b d p l

open scoped Classical in
theorem printSignal (pres : S.Presentation z P.diagram) {tone : B S.m → ℕ} {mobile : S.Vtx → Bool}
    (h : P.Placed pres A.coord tone mobile) (hd : pres.Directed)
    {menu : (Cfg).Menu F (B S.k) (B S.ℓ) j} (c : (world).Code (Cfg).waves menu)
    {M r t k n u j' e : ℕ}
    (U : Print.Printer F (panelKeys Cfg) (B S.k) S.m S.d S.h j M r t (Cfg).R D k n u j' e)
    (ha : d * b = M * r) (hb : d = M * t) (hm : U.menu = printMenu S menu ha hb)
    (status : (Print.Children.Header S.m S.d).obj)
    (loc : ∀ v, A.coord v = (A.host v.val.1, cellIndex S.h v.val.2))
    (parents : Print.Children.Shows P.adj A.host (A.graph, status)) :
    let f := c.frame
    let Q := P.finalSource A sc hK s f
    let left := P.inputPorts kit s f.reach
    let right := P.outputPorts kit s f.reach
    U.Signal Q left right (world).atlas (world).π f.address (world).ref f.record f.match'
      (P.panelIndex sc hK) (world).size (P.panelExt A) A.host c.tape status ∧
      Print.Keeps Q left right pres A.coord := by
  intro f Q left right
  refine ⟨?_, P.keeps kit s f.reach h⟩
  refine ⟨Nat.le_add_left _ _, rfl, rfl, ⟨_, f.layout⟩, ?_, loc, parents, c.host, ?_, ?_,
    fun _ _ _ _ => rfl, ?_, fun _ => rfl⟩
  · have he := f.clean.distinct
    change Distinct ((world).atlas.near (horizon _ (Cfg).waves (Cfg).waves)) _ _ at he
    simp only [horizon, Nat.sub_self, mul_zero, zero_add] at he
    exact he
  · intro i
    rw [hm]
    apply HEq.trans (cast_heq _ _)
    apply heq_of_eq
    refine (P.panel_read A sc hK s c i).trans ?_
    refine congrArg (fun z => (world).atlas.fill z i) (funext fun v => ?_)
    simp only [panelFace, Print.Printer.faces, Frame.info, f]
    congr 4
    exact Subsingleton.elim _ _
  · intro i w
    erw [← (f.match'.represents i).name]
    exact P.portsWidth kit s f.reach h hd i w
  · intro i a b w
    let j := (Layout.item f.stage.scene.cell i).label.name
    change P.external kit j ((a, b), w) =
      ((j.elim [] P.diagram.extLeft).map (bits x a), (j.elim [] P.diagram.extRight).map (bits y b))
    cases j <;> rfl

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input

namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.Template.Binning.Trial
open Sphere.Print

variable {F : Type} [Field F] {x y : Wire} {D : Template F}
    {a H T R : ℕ} {θ L : ℝ} {b : D.Binning a H T R θ}
    {r : D.format.obj} {P : Rounds.Board F x y D.scheme.h} {p : D.Presents r P}
    (t : b.Trial p L) (q : ℕ)

theorem parents : Children.Shows (t.normal q).adj (t.atlas q).host ((t.atlas q).graph, b.status r)
    :=
  ⟨t.live_status q, t.closed q, (t.atlas q).reciprocal, t.edge_status q⟩

theorem directed_order : t.order.Directed := by
  unfold Scheme.Presentation.Directed
  rw [t.post.ordered_ends]
  exact t.directed

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.Template.Binning.Trial
end

/- # Common dimensions of the printer for a grouped layer -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Layer
open Assembly Coloring Sphere SphereScale
variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
    {s : Rounds.Plan} {a T b d : ℕ} {θ L : ℝ}
    (P : Layer F x y) (B : P.template.Binning a s.D T (d * b) θ)

local notation "g" => ((4 * 5) ^ 300 : ℕ)

open scoped Classical in
/-- The construction uses `Input.design B.target g 10 s.D b d p l` for its intermediate `cfg`. -/
abbrev motionWidth (p l k : ℕ) :=
  let cfg := Input.design B.target g 10 s.D b d p l
  cfg.widthAt (Input.panelQuery B.target g 10 s.D b d p l k).width k cfg.waves

open scoped Classical in
/-- The construction uses `Input.design B.target g 10 s.D b d p l` for its intermediate `cfg`. -/
abbrev Printer (p l k r t z f : ℕ) :=
  let cfg := Input.design B.target g 10 s.D b d p l
  Print.Printer F (Input.panelKeys cfg) (Coloring.B B.target.k) B.target.m B.target.d B.target.h
    (P.motionWidth B p l k) (chunks 10 s.D) r t cfg.R s.D
    (Sphere.Layout.Sharing.allocation g 10) s.d (s.b * z) (p ^ l) f

variable [Fintype F] {p l k r t z f : ℕ} [ExpChar F p]
    (trials : ∀ i, B.Trial (P.presents i) L)
    (sc : Scales g 10 s.D T (p ^ l) b d) (hK : SphereScale.Ready K 10 s.D g (p ^ l) b d)
    (hF : room 10 s.D g * (2 * depth 10 s.D g (p ^ l) (d * b) + 1) < Fintype.card F)
    (U : P.Printer B p l k r t z f)

open scoped Classical in
/-- The releases used in the `Layer` construction. -/
abbrev Releases := ∀ i : (P.moved B trials sc hK hF k).state,
  U.Release (P := (trials i.1.1).normal (panelRadius s.D)) (trials i.1.1).order
    i.2.tape (B.status (P.data i.1.1)) ((P.moved B trials sc hK hF k).eval i) 10

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Layer
end
