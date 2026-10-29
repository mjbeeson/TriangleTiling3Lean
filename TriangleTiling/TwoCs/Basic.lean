/-
Small facts for `lemma:twocs`: the edge opposite a corner, tile vertices in the target, and angle
sums at a point bounded by `2π`.
-/
import TriangleTiling.TwoCs.PRSetup

namespace TriangleTiling.TwoCs

open Erdos634.Geometry EuclideanGeometry Set

/-- The edge of a tile opposite its corner `j` joins the other two corners. -/
theorem dist_opp (T : Tri) {j j' j'' : Fin 3} (h1 : j' ≠ j) (h2 : j'' ≠ j) (h3 : j' ≠ j'') :
    dist (T.pts (j + 1)) (T.pts (j + 2)) = dist (T.pts j') (T.pts j'') := by
  have : (j' = j + 1 ∧ j'' = j + 2) ∨ (j' = j + 2 ∧ j'' = j + 1) := by
    revert h1 h2 h3; fin_cases j <;> fin_cases j' <;> fin_cases j'' <;> simp
  rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact dist_comm _ _

/-- Tile vertices are in the target. -/
theorem pts_mem_target {N : ℕ} (D : Dissection N) (i : Fin N) (j : Fin 3) :
    (D.tile i).pts j ∈ D.target.carrier := by
  have : (D.tile i).pts j ∈ (D.tile i).carrier := subset_convexHull ℝ _ ⟨j, rfl⟩
  rw [← D.covers]; exact Set.mem_iUnion.mpr ⟨i, this⟩

variable {N : ℕ} (D : CongruentDissection N)

/-- Local angles at a point add up to at most `2π`. -/
theorem sum_two_le {i j : Fin N} (hij : i ≠ j) (p : Plane) :
    (D.tile i).localAngle p + (D.tile j).localAngle p ≤ 2 * Real.pi := by
  have := sum_ge_two D.toDissection hij p
  rw [D.sum_localAngle_eq] at this
  linarith [Tri.localAngle_le_two_pi D.target p]

theorem sum_three_le {i j k : Fin N} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (p : Plane) :
    (D.tile i).localAngle p + (D.tile j).localAngle p + (D.tile k).localAngle p
      ≤ 2 * Real.pi := by
  have := sum_ge_three D.toDissection hij hik hjk p
  rw [D.sum_localAngle_eq] at this
  linarith [Tri.localAngle_le_two_pi D.target p]

end TriangleTiling.TwoCs
