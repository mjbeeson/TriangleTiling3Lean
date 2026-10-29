/-
Lengths along a wall.

Bonfioli's `Dissection.wall_partition` says that the tile edges on one side of a wall segment
`UV` (the chain `lineChain f c`) cover `UV` exactly once, measured by one-dimensional Hausdorff
measure. If each chain edge either lies inside `UV` or meets it in at most one point, the lengths
of the edges inside `UV` add up to `|UV|`.
-/
import Erdos634.WallChain

namespace TriangleTiling

open Erdos634.Geometry MeasureTheory

open Classical in
theorem wall_sum {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    {U V : Plane} (hUV : U ≠ V) (hS : segment ℝ U V ⊆ {y | f y = c})
    (hint : openSegment ℝ U V ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ U V, ∀ i, y ∉ interior (D.tile i).carrier)
    (hdich : ∀ e ∈ D.lineChain f c, (D.tile e.1).edge e.2 ⊆ segment ℝ U V ∨
      ((D.tile e.1).edge e.2 ∩ segment ℝ U V).Subsingleton) :
    ∑ e ∈ (D.lineChain f c).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ U V),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = dist U V := by
  classical
  haveI : NoAtoms (Measure.hausdorffMeasure (1 : ℝ) : Measure Plane) :=
    Measure.noAtoms_hausdorff _ one_pos
  have hp := D.wall_partition f c hf hUV hS hint hwall
  rw [← Finset.sum_filter_add_sum_filter_not (D.lineChain f c)
    (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ U V)] at hp
  have h0 : ∑ e ∈ (D.lineChain f c).filter
      (fun e => ¬ (D.tile e.1).edge e.2 ⊆ segment ℝ U V),
      (Measure.hausdorffMeasure 1 : Measure Plane) ((D.tile e.1).edge e.2 ∩ segment ℝ U V)
      = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    obtain ⟨he, hns⟩ := Finset.mem_filter.mp he
    exact ((hdich e he).resolve_left hns).measure_zero _
  have h1 : ∀ e ∈ (D.lineChain f c).filter
      (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ U V),
      (Measure.hausdorffMeasure 1 : Measure Plane) ((D.tile e.1).edge e.2 ∩ segment ℝ U V)
      = edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
    intro e he
    rw [Set.inter_eq_left.mpr (Finset.mem_filter.mp he).2, Tri.hausdorff_edge]
  rw [h0, add_zero, Finset.sum_congr rfl h1, hausdorffMeasure_segment] at hp
  have := congrArg ENNReal.toReal hp
  rw [ENNReal.toReal_sum (fun e _ => edist_ne_top _ _)] at this
  simpa [← dist_edist] using this

end TriangleTiling
