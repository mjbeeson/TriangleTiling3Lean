/-
Scaling a tiling.

Multiplying every point by a nonzero real `κ` turns an `N`-tiling into an `N`-tiling of the scaled
triangle by the scaled tile: angles are unchanged and lengths are multiplied by `|κ|`.
-/
import Erdos634.SssCongruent

namespace TriangleTiling

open Erdos634.Geometry Set EuclideanGeometry
open scoped Pointwise

/-- The triangle `T` scaled by `κ ≠ 0` about the origin. -/
noncomputable def Tri.scale (T : Tri) (κ : ℝ) (hκ : κ ≠ 0) : Tri where
  pts k := κ • T.pts k
  indep := by
    have h := T.indep.map' (LinearEquiv.smulOfNeZero ℝ Plane κ hκ).toLinearMap.toAffineMap
      (LinearEquiv.smulOfNeZero ℝ Plane κ hκ).injective
    convert h using 1

theorem Tri.scale_carrier (T : Tri) (κ : ℝ) (hκ : κ ≠ 0) :
    (Tri.scale T κ hκ).carrier = κ • T.carrier := by
  show convexHull ℝ (Set.range fun k => κ • T.pts k) = κ • convexHull ℝ (Set.range T.pts)
  rw [← convexHull_smul, ← Set.range_smul]

theorem dist_smul_smul (κ : ℝ) (x y : Plane) : dist (κ • x) (κ • y) = |κ| * dist x y := by
  rw [dist_smul₀, Real.norm_eq_abs]

theorem smul_mem_openSegment (κ : ℝ) {x y z : Plane} (h : z ∈ openSegment ℝ x y) :
    κ • z ∈ openSegment ℝ (κ • x) (κ • y) := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := h
  exact ⟨s, t, hs, ht, hst, by rw [smul_add, smul_comm s κ x, smul_comm t κ y]⟩

theorem angle_smul_smul' {κ : ℝ} (hκ : κ ≠ 0) (x y z : Plane) :
    ∠ (κ • x) (κ • y) (κ • z) = ∠ x y z := by
  simp only [EuclideanGeometry.angle, vsub_eq_sub, ← smul_sub]
  exact InnerProductGeometry.angle_smul_smul hκ _ _

/-- The tiling scaled by `κ ≠ 0`. -/
noncomputable def CongruentDissection.scale {N : ℕ} (D : CongruentDissection N) (κ : ℝ)
    (hκ : κ ≠ 0) : CongruentDissection N where
  target := Tri.scale D.target κ hκ
  tile i := Tri.scale (D.tile i) κ hκ
  covers := by
    simp only [Tri.scale_carrier]
    rw [← Set.smul_set_iUnion, D.covers]
  interiors_disjoint := by
    intro i j hij
    simp only [Tri.scale_carrier, interior_smul₀ hκ]
    rw [← Set.image_smul, ← Set.image_smul]
    exact (Set.disjoint_image_iff (smul_right_injective Plane hκ)).mpr (D.interiors_disjoint hij)
  model := Tri.scale D.model κ hκ
  tiles_congruent := by
    intro i
    obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).dist_eq
    refine Erdos634.SssCongruent.congruent_of_dist_perm σ fun a b => ?_
    show dist (κ • (D.tile i).pts a) (κ • (D.tile i).pts b) =
      dist (κ • D.model.pts (σ a)) (κ • D.model.pts (σ b))
    rw [dist_smul_smul, dist_smul_smul, hσ]

namespace CongruentDissection

variable {N : ℕ} (D : CongruentDissection N) {κ : ℝ} (hκ : κ ≠ 0)

theorem scale_tile_pts (i : Fin N) (k : Fin 3) :
    ((CongruentDissection.scale D κ hκ).tile i).pts k = κ • (D.tile i).pts k := rfl

theorem scale_target_pts (k : Fin 3) :
    (CongruentDissection.scale D κ hκ).target.pts k = κ • D.target.pts k := rfl

theorem scale_model_pts (k : Fin 3) :
    (CongruentDissection.scale D κ hκ).model.pts k = κ • D.model.pts k := rfl

end CongruentDissection

end TriangleTiling
