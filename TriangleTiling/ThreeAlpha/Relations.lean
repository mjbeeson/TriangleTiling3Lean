/-
Relations between the sides of the tile, and Laczkovich's graph `Γ_a`, for M. Beeson, *Triangle
tiling: the case 3α + 2β = π* (arXiv 1206.2229v4): `definition:essentialedgerelation` (i),
`definition:relationlattice`, `lemma:noboundarylink`. (`lemma:relationlattice`, about the rank of
`L`, is in `RelLattice.lean`.)

`Γ_a` is the isosceles paper's formalization of `definition:Gamma` (`IsLink`, with the `a` edges,
those opposite the angle `α`, as marked edges); "the tiling witnesses no `a`-relation" is
`¬ HasRelation` for the `a` edges, as there.
-/
import TriangleTiling.ThreeAlpha.Defs
import TriangleTiling.Tiling.Degree
import TriangleTiling.Isosceles.MarkedCount
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry

/-- **Definition `definition:essentialedgerelation` (i)**, `a`-relation: `j a = p b + q c` with
nonnegative integers `j, p, q` and `j > 0`. -/
def ARelation (a b c : ℝ) : Prop :=
  ∃ j p q : ℕ, 0 < j ∧ (j : ℝ) * a = p * b + q * c

/-- **Definition `definition:relationlattice`.** The relation lattice of the tile with sides
`a, b, c`: `L = {(P, Q, R) ∈ ℤ³ : P a + Q b + R c = 0}`. -/
def relLattice (a b c : ℝ) : Submodule ℤ (Fin 3 → ℤ) where
  carrier := {v | (v 0 : ℝ) * a + v 1 * b + v 2 * c = 0}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Pi.add_apply, Int.cast_add] at *
    linear_combination hx + hy
  zero_mem' := by simp
  smul_mem' := by
    intro k x hx
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, Int.cast_mul] at *
    linear_combination (k : ℝ) * hx

/-- **Lemma `lemma:noboundarylink`.** No link of `Γ_a` terminates at a point of the boundary of
`ABC`. (True of the links of any marked class of edges, in any dissection.) -/
theorem noboundarylink {N : ℕ} (D : CongruentDissection N) (φ : ℝ) {X Y : Plane}
    (h : IsLink D.toDissection (edgeType D φ) X Y) : Y ∉ frontier D.target.carrier := by
  obtain ⟨g, c, hl⟩ := h
  exact fun hf => hf.2 hl.end_interior

end TriangleTiling.ThreeAlpha
