/-
The area equation for a right-angled tile (in the proofs of `lemma:isosceleshelper2` and
`lemma:isosceleshelper3`).

Let the isosceles triangle `ABC` with base angles `β` (at `A` and `C`) be `N`-tiled by a tile with
a right angle, angle `β`, and sides `a, b, c` (`c` the hypotenuse, `a` adjacent to `β`). Then
`|BC| = |AB| = X`, `c |AC| = 2 a X`, and `2 X² = N c²`.
-/
import TriangleTiling.Isosceles.AreaEquation

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

/-- **The area equation for a right-angled tile.** -/
theorem right_area_core {N : ℕ} (D : CongruentDissection N) {a b c X Y : ℝ}
    (ha : dist (D.model.pts 1) (D.model.pts 2) = a)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = b)
    (hc : dist (D.model.pts 0) (D.model.pts 1) = c)
    (hX : dist (D.target.pts 0) (D.target.pts 1) = X)
    (hY : dist (D.target.pts 2) (D.target.pts 0) = Y)
    (hright : ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.model.pts 2) (D.model.pts 1) (D.model.pts 0))
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) =
      ∠ (D.model.pts 2) (D.model.pts 1) (D.model.pts 0)) :
    dist (D.target.pts 1) (D.target.pts 2) = X ∧ c * Y = 2 * a * X ∧
      2 * X ^ 2 = N * c ^ 2 := by
  set M := D.model.pts with hM
  set T := D.target.pts with hT
  set X' := dist (T 1) (T 2) with hX'
  set k := Real.cos (∠ (M 2) (M 1) (M 0)) with hk
  obtain ⟨m1, m2, m3⟩ := strict_triangle_ineqs (tri_indep D.model)
  rw [ha, hb, hc] at m1 m2 m3
  obtain ⟨t1, t2, t3⟩ := strict_triangle_ineqs (tri_indep D.target)
  rw [hX, hY] at t1 t2 t3
  rw [← hX'] at t1 t2 t3
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hY0 : 0 < Y := by linarith
  -- The tile: Pythagoras, and `a = c cos β`.
  have hpyth : c ^ 2 = a ^ 2 + b ^ 2 := by
    have := law_cos (M 0) (M 2) (M 1)
    rw [hright, Real.cos_pi_div_two, dist_comm (M 0) (M 2), hb, ha, hc] at this
    linear_combination this
  have hak : a = c * k := by
    have := law_cos (M 2) (M 1) (M 0)
    rw [← hk, dist_comm (M 2) (M 1), ha, hc, hb] at this
    have h : 2 * a * (a - c * k) = 0 := by linear_combination -this - hpyth
    have := (mul_eq_zero.mp h).resolve_left (by positivity)
    linarith
  -- The target: `|BC| = |AB|` and `|AC| = 2 |AB| cos β`.
  have eA : X' ^ 2 = X ^ 2 + Y ^ 2 - 2 * X * Y * k := by
    have := law_cos (T 1) (T 0) (T 2)
    rw [hA, ← hk, dist_comm (T 1) (T 0), hX, hY] at this
    linear_combination this
  have eC : X ^ 2 = X' ^ 2 + Y ^ 2 - 2 * X' * Y * k := by
    have := law_cos (T 1) (T 2) (T 0)
    rw [hC, ← hk, dist_comm (T 1) (T 0), hX, dist_comm (T 0) (T 2), hY] at this
    linear_combination this
  have hk0 : 0 < k := by
    have : 0 < c * k := hak ▸ ha0
    exact pos_of_mul_pos_right this hc0.le
  have hXX : X' = X := by
    have h0 : (X' - X) * (X' + X - Y * k) = 0 := by linear_combination (eA - eC) / 2
    have h1 : X' + X - Y * k ≠ 0 := by nlinarith
    have := (mul_eq_zero.mp h0).resolve_right h1
    linarith
  have hYk : Y = 2 * X * k := by
    rw [hXX] at eA
    have : Y * (Y - 2 * X * k) = 0 := by linear_combination -eA
    have := (mul_eq_zero.mp this).resolve_left hY0.ne'
    linarith
  refine ⟨hXX, by rw [hYk, hak]; ring, ?_⟩
  -- Heron: `N² · 4 a² b² = 16 X⁴ k² (1 - k²)`, with `k = a/c` and `1 - k² = b²/c²`.
  have hH := area_heron D
  rw [ha, hb, hc, ← hX', hXX, hY, hX] at hH
  have hH1 : heron16 a b c = 4 * a ^ 2 * b ^ 2 := by
    unfold heron16
    have h4 : c ^ 4 = (a ^ 2 + b ^ 2) ^ 2 := by rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, hpyth]
    rw [h4, hpyth]; ring
  have hH2 : heron16 X Y X = 16 * X ^ 4 * k ^ 2 * (1 - k ^ 2) := by
    unfold heron16; rw [hYk]; ring
  rw [hH1, hH2] at hH
  have hk2 : c ^ 2 * (1 - k ^ 2) = b ^ 2 := by
    have : c ^ 2 * k ^ 2 = a ^ 2 := by rw [hak]; ring
    linarith
  -- `N² a² b² c⁴ = 4 X⁴ a² b²`.
  have h4 : a ^ 2 * b ^ 2 * (((N : ℝ) * c ^ 2) ^ 2 - (2 * X ^ 2) ^ 2) = 0 := by
    have e : c ^ 4 * ((N : ℝ) ^ 2 * (4 * a ^ 2 * b ^ 2)) =
        c ^ 4 * (16 * X ^ 4 * k ^ 2 * (1 - k ^ 2)) := by rw [hH]
    have e2 : c ^ 4 * (16 * X ^ 4 * k ^ 2 * (1 - k ^ 2)) = 16 * X ^ 4 * a ^ 2 * b ^ 2 := by
      have : c ^ 4 * (k ^ 2 * (1 - k ^ 2)) = a ^ 2 * b ^ 2 := by
        rw [← hk2]; rw [hak]; ring
      linear_combination 16 * X ^ 4 * this
    linear_combination (e.trans e2) / 4
  have h5 := (mul_eq_zero.mp h4).resolve_left (by positivity)
  have h6 : ((N : ℝ) * c ^ 2 - 2 * X ^ 2) * ((N : ℝ) * c ^ 2 + 2 * X ^ 2) = 0 := by
    linear_combination h5
  have h7 : 0 < (N : ℝ) * c ^ 2 + 2 * X ^ 2 := by
    have : 0 < X := by linarith
    positivity
  have := (mul_eq_zero.mp h6).resolve_right h7.ne'
  linarith

end TriangleTiling
