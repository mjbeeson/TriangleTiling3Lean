/-
Rays in the plane: two rays from a point, on the same side of a line through it, that make the
same angle with that line are the same ray.
-/
import Erdos634.EdgeChain
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

theorem inner_plane (u v : Plane) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

theorem norm_sq_plane (v : Plane) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two]

/-- **Same angle, same side, same ray.** If `v, w` make the same angle with `u ≠ 0` and lie
strictly on the same side of it (`cross u v` and `cross u w` have the same sign), then `v` is a
positive multiple of `w`. -/
theorem same_ray_of_angle_eq {u v w : Plane} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hang : InnerProductGeometry.angle u v = InnerProductGeometry.angle u w)
    (hside : 0 < cross u v * cross u w) : ∃ t : ℝ, 0 < t ∧ v = t • w := by
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hcos := congrArg Real.cos hang
  rw [InnerProductGeometry.cos_angle, InnerProductGeometry.cos_angle] at hcos
  have h1 : ‖w‖ * inner ℝ u v = ‖v‖ * inner ℝ u w := by
    field_simp at hcos; linarith
  rw [inner_plane, inner_plane] at h1
  have hlv : (u 0 * v 0 + u 1 * v 1) ^ 2 + cross u v ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_sq_plane, norm_sq_plane]; simp only [cross]; ring
  have hlw : (u 0 * w 0 + u 1 * w 1) ^ 2 + cross u w ^ 2 = ‖u‖ ^ 2 * ‖w‖ ^ 2 := by
    rw [norm_sq_plane, norm_sq_plane]; simp only [cross]; ring
  -- The two crosses, scaled, have equal squares and the same sign, hence are equal.
  have hsq : (‖w‖ * cross u v) ^ 2 = (‖v‖ * cross u w) ^ 2 := by
    linear_combination ‖w‖ ^ 2 * hlv - ‖v‖ ^ 2 * hlw
      - ((‖w‖ * (u 0 * v 0 + u 1 * v 1)) + ‖v‖ * (u 0 * w 0 + u 1 * w 1)) * h1
  have hc : ‖w‖ * cross u v = ‖v‖ * cross u w := by
    have hpos : 0 < (‖w‖ * cross u v) * (‖v‖ * cross u w) := by
      have := mul_pos hnw hnv
      nlinarith
    have h0 : (‖w‖ * cross u v - ‖v‖ * cross u w) * (‖w‖ * cross u v + ‖v‖ * cross u w) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · nlinarith
  simp only [cross] at hc
  -- `p = ‖w‖ v - ‖v‖ w` has zero inner product and zero cross with `u`, so `p = 0`.
  have hu2 : 0 < u 0 ^ 2 + u 1 ^ 2 := by rw [← norm_sq_plane]; positivity
  have hp0 : ‖w‖ * v 0 - ‖v‖ * w 0 = 0 := by
    have : (u 0 ^ 2 + u 1 ^ 2) * (‖w‖ * v 0 - ‖v‖ * w 0) = 0 := by
      linear_combination u 0 * h1 - u 1 * hc
    exact (mul_eq_zero.mp this).resolve_left hu2.ne'
  have hp1 : ‖w‖ * v 1 - ‖v‖ * w 1 = 0 := by
    have : (u 0 ^ 2 + u 1 ^ 2) * (‖w‖ * v 1 - ‖v‖ * w 1) = 0 := by
      linear_combination u 1 * h1 + u 0 * hc
    exact (mul_eq_zero.mp this).resolve_left hu2.ne'
  refine ⟨‖v‖ / ‖w‖, by positivity, ?_⟩
  ext i
  fin_cases i
  · simp only [PiLp.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue]
    rw [div_mul_eq_mul_div, eq_div_iff hnw.ne']; linear_combination hp0
  · simp only [PiLp.smul_apply, smul_eq_mul, Fin.mk_one, Fin.isValue]
    rw [div_mul_eq_mul_div, eq_div_iff hnw.ne']; linear_combination hp1

end TriangleTiling
