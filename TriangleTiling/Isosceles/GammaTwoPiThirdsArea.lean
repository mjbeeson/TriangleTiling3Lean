/-
The area equation and the necessary condition for tilings with `γ = 2π/3`, from Section 11 of
M. Beeson, *Tilings of an isosceles triangle*.

Lean names follow the TeX labels, made into Lean identifiers: `lemma:2pi/3area` is
`two_pi_div_three_area`, and `lemma:2b+adividesN` is `two_b_add_a_dvd_N`.

Conventions as in `TriangleTiling.Isosceles.AreaEquation`: target `ABC = target.pts 0, 1, 2`
with base `AC`; model tile with angles `α, β, γ` at `model.pts 0, 1, 2` and opposite sides
`a, b, c`.
-/
import TriangleTiling.Isosceles.NotPrime
import TriangleTiling.Isosceles.GammaTwoPiThirds

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

/-- **The isosceles area relation**, for any tile. If the base angles of `ABC` at `A` and `C`
both equal the tile's angle `α` at `model.pts 0`, and `k = cos α`, then `|BC| = |AB| = X`,
`|AC| = 2 X k`, and `N b c = 2 X² k`. -/
theorem isosceles_core {N : ℕ} (D : CongruentDissection N) {a b c X : ℝ}
    (ha : dist (D.model.pts 1) (D.model.pts 2) = a)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = b)
    (hc : dist (D.model.pts 0) (D.model.pts 1) = c)
    (hX : dist (D.target.pts 0) (D.target.pts 1) = X)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2)) :
    dist (D.target.pts 1) (D.target.pts 2) = X ∧
    dist (D.target.pts 2) (D.target.pts 0) =
      2 * X * Real.cos (∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2)) ∧
    N * b * c = 2 * X ^ 2 * Real.cos (∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2)) := by
  set M := D.model.pts with hM
  set T := D.target.pts with hT
  set X' := dist (T 1) (T 2) with hX'
  set Y := dist (T 2) (T 0) with hY
  set k := Real.cos (∠ (M 1) (M 0) (M 2)) with hk
  obtain ⟨m1, m2, m3⟩ := strict_triangle_ineqs (tri_indep D.model)
  rw [ha, hb, hc] at m1 m2 m3
  obtain ⟨t1, t2, t3⟩ := strict_triangle_ineqs (tri_indep D.target)
  rw [hX] at t1 t2 t3
  rw [← hX', ← hY] at t1 t2 t3
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hα : 2 * b * c * k = b ^ 2 + c ^ 2 - a ^ 2 := by
    have := law_cos (M 1) (M 0) (M 2)
    rw [ha, dist_comm (M 1) (M 0), hc, hb, ← hk] at this
    linear_combination this
  have eA : X' ^ 2 = X ^ 2 + Y ^ 2 - 2 * X * Y * k := by
    have := law_cos (T 1) (T 0) (T 2)
    rw [hA, ← hk, dist_comm (T 1) (T 0), hX, ← hY] at this
    linear_combination this
  have eC : X ^ 2 = X' ^ 2 + Y ^ 2 - 2 * X' * Y * k := by
    have := law_cos (T 1) (T 2) (T 0)
    rw [hC, ← hk, dist_comm (T 1) (T 0), hX, dist_comm (T 0) (T 2), ← hY] at this
    linear_combination this
  have p1 : (0 : ℝ) < a - b + c := by linarith
  have p2 : (0 : ℝ) < a + b - c := by linarith
  have p3 : (0 : ℝ) < b + c - a := by linarith
  have p4 : (0 : ℝ) < a + b + c := by linarith
  have e1 : 2 * b * c * (1 - k) = (a - b + c) * (a + b - c) := by linear_combination -hα
  have e2 : 2 * b * c * (1 + k) = (b + c - a) * (a + b + c) := by linear_combination hα
  have hbc : 0 < 2 * b * c := by positivity
  have hk1 : k < 1 := by nlinarith [mul_pos p1 p2]
  have hk1' : -1 < k := by nlinarith [mul_pos p3 p4]
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
  refine ⟨hXX, hYk, ?_⟩
  have hk0 : 0 < k := by
    have : 0 < 2 * X * k := hYk ▸ hY0
    exact pos_of_mul_pos_right this (by positivity)
  -- Heron: `N² · 4b²c²(1 - k²) = 16 X⁴ k² (1 - k²)`.
  have hH := area_heron D
  rw [ha, hb, hc, ← hX', hXX, ← hY, hX] at hH
  have hH1 : heron16 a b c = 4 * b ^ 2 * c ^ 2 * (1 - k ^ 2) := by
    unfold heron16; linear_combination (2 * b * c * k + (b ^ 2 + c ^ 2 - a ^ 2)) * hα
  have hH2 : heron16 X Y X = 16 * X ^ 4 * k ^ 2 * (1 - k ^ 2) := by
    unfold heron16; rw [hYk]; ring
  rw [hH1, hH2] at hH
  have hpos : 0 < 1 - k ^ 2 := by
    have := mul_pos (sub_pos.mpr hk1) (show (0 : ℝ) < 1 + k by linarith)
    linarith [show (1 - k) * (1 + k) = 1 - k ^ 2 by ring]
  have h4 : (N * b * c - 2 * X ^ 2 * k) * (N * b * c + 2 * X ^ 2 * k) = 0 := by
    have : (1 - k ^ 2) * (4 * ((N * b * c - 2 * X ^ 2 * k) * (N * b * c + 2 * X ^ 2 * k))) = 0 := by
      linear_combination hH
    have := (mul_eq_zero.mp this).resolve_left hpos.ne'
    linarith
  have h5 : 0 < (N : ℝ) * b * c + 2 * X ^ 2 * k := by positivity
  exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_right h5.ne')

/-- In a triangle with angle `2π/3` at `C`: `c² = a² + b² + ab`, where `c = |AB|`. -/
theorem sq_eq_of_angle_two_pi_div_three {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {A B C : P} {a b c : ℝ}
    (ha : dist B C = a) (hb : dist C A = b) (hc : dist A B = c)
    (hγ : ∠ A C B = 2 * Real.pi / 3) : c ^ 2 = a ^ 2 + b ^ 2 + a * b := by
  have := law_cos A C B
  have hcos : Real.cos (∠ A C B) = -1 / 2 := by
    rw [hγ, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]; ring
  rw [hcos, hc, dist_comm A C, hb, ha] at this
  linear_combination this

/-- **Lemma `lemma:2pi/3area`.** Let the isosceles triangle `ABC` with base angles `α` be
`N`-tiled by a tile with angles `(α, β, 2π/3)` and sides `(a, b, c)`. Let `X = |AB|` and
`Y = |AC|`. Then `X² (2b + a) = N b c²` and `X Y = N b c`.

(The paper also assumes `α` is not a rational multiple of `π`; the proof does not use it.) -/
theorem two_pi_div_three_area {N : ℕ} (D : CongruentDissection N) {a b c X Y : ℝ}
    (ha : dist (D.model.pts 1) (D.model.pts 2) = a)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = b)
    (hc : dist (D.model.pts 0) (D.model.pts 1) = c)
    (hX : dist (D.target.pts 0) (D.target.pts 1) = X)
    (hY : dist (D.target.pts 0) (D.target.pts 2) = Y)
    (hγ : ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = 2 * Real.pi / 3)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2)) :
    X ^ 2 * (2 * b + a) = N * b * c ^ 2 ∧ X * Y = N * b * c := by
  obtain ⟨-, hYk, hN⟩ := isosceles_core D ha hb hc hX hA hC
  set k := Real.cos (∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2)) with hk
  rw [dist_comm, hY] at hYk
  have hcab := sq_eq_of_angle_two_pi_div_three ha hb hc hγ
  -- `cos α = (2b + a) / (2c)`, from the law of cosines at the tile's `α` vertex.
  have hα : 2 * b * c * k = b ^ 2 + c ^ 2 - a ^ 2 := by
    have := law_cos (D.model.pts 1) (D.model.pts 0) (D.model.pts 2)
    rw [ha, dist_comm (D.model.pts 1) (D.model.pts 0), hc, hb, ← hk] at this
    linear_combination this
  obtain ⟨m1, -, -⟩ := strict_triangle_ineqs (tri_indep D.model)
  rw [ha, hb, hc] at m1
  have hb0 : 0 < b := by
    have := dist_pos.mpr (D.model.indep.injective.ne (show (2 : Fin 3) ≠ 0 by decide))
    simpa [hb] using this
  have hck : 2 * c * k = 2 * b + a := by
    have : b * (2 * c * k - (2 * b + a)) = 0 := by linear_combination hα + hcab
    have := (mul_eq_zero.mp this).resolve_left hb0.ne'
    linarith
  refine ⟨?_, ?_⟩
  · linear_combination -c * hN - X ^ 2 * hck
  · rw [hYk]; linear_combination -hN

/-- **Lemma `lemma:2b+adividesN`.** Let the isosceles triangle `ABC` with base angles `α` be
`N`-tiled by a tile with angles `(α, β, 2π/3)` and integer sides `(a, b, c)` with no common
factor. Then

* (i) `2b + a` divides `N`, and `N b / (2b + a)` is a square `m²`, and
* (ii) the side and base of `ABC` are `X = m c` and `Y = m (2b + a)`.

(The paper also assumes `α` is not a rational multiple of `π`; the proof does not use it.) -/
theorem two_b_add_a_dvd_N {N : ℕ} (D : CongruentDissection N) {a b c : ℕ}
    (ha : dist (D.model.pts 1) (D.model.pts 2) = a)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = b)
    (hc : dist (D.model.pts 0) (D.model.pts 1) = c)
    (hcop : Nat.gcd (Nat.gcd a b) c = 1)
    (hγ : ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = 2 * Real.pi / 3)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2)) :
    (2 * b + a) ∣ N ∧ ∃ m : ℕ, N * b = (2 * b + a) * m ^ 2 ∧
      dist (D.target.pts 0) (D.target.pts 1) = m * c ∧
      dist (D.target.pts 0) (D.target.pts 2) = m * (2 * b + a) := by
  obtain ⟨hX2, hXY⟩ := two_pi_div_three_area D ha hb hc rfl rfl hγ hA hC
  -- The side `AB` has integer length `Xn = P a + Q b + R c`.
  have habc : ∀ (j : Fin N) (k : Fin 3),
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = (a : ℝ) ∨
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = (b : ℝ) ∨
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = (c : ℝ) := by
    intro j k; rw [← ha, ← hb, ← hc]; exact edge_len_mem D j k
  obtain ⟨P, Q, R, hPQR, -⟩ := D.toDissection.side_walk_abc 0 a b c habc
  have h01 : (0 : Fin 3) + 1 = 1 := rfl
  rw [h01] at hPQR
  set Xn : ℕ := P * a + Q * b + R * c with hXn
  have hXr : dist (D.target.pts 0) (D.target.pts 1) = (Xn : ℝ) := by
    rw [← hPQR, hXn]; push_cast; rfl
  rw [hXr] at hX2 hXY
  have hcab : c ^ 2 = a ^ 2 + b ^ 2 + a * b := by
    have := sq_eq_of_angle_two_pi_div_three ha hb hc hγ
    exact_mod_cast this
  obtain ⟨hab2, hab2c, -⟩ := two_b_add_a hcab hcop
  have hX2n : Xn ^ 2 * (2 * b + a) = N * b * c ^ 2 := by exact_mod_cast hX2
  -- `2b + a` is coprime to `b c²`, so it divides `N`.
  have hdvd : (2 * b + a) ∣ N := by
    have h1 : (2 * b + a) ∣ N * (b * c ^ 2) := ⟨Xn ^ 2, by rw [← mul_assoc, ← hX2n]; ring⟩
    exact (Nat.Coprime.mul_right hab2 (Nat.Coprime.pow_right 2 hab2c)).dvd_of_dvd_mul_right h1
  obtain ⟨q, hq⟩ := hdvd
  have hpos : 0 < 2 * b + a := by
    have := dist_pos.mpr (D.model.indep.injective.ne (show (2 : Fin 3) ≠ 0 by decide))
    rw [hb] at this
    have : 0 < b := by exact_mod_cast this
    omega
  -- `X² = q b c²`, so `c ∣ X`; write `X = c m`, then `m² = q b`.
  have hXq : Xn ^ 2 = q * b * c ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [mul_comm, hX2n, hq]; ring
  have hc0 : 0 < c := by
    have := dist_pos.mpr (D.model.indep.injective.ne (show (0 : Fin 3) ≠ 1 by decide))
    rw [hc] at this
    exact_mod_cast this
  have hcX : c ∣ Xn := (Nat.pow_dvd_pow_iff two_ne_zero).mp ⟨q * b, by rw [hXq]; ring⟩
  obtain ⟨m, hm⟩ := hcX
  have hmq : m ^ 2 = q * b := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < c ^ 2 by positivity)
    calc c ^ 2 * m ^ 2 = (c * m) ^ 2 := by ring
      _ = q * b * c ^ 2 := by rw [← hm, hXq]
      _ = c ^ 2 * (q * b) := by ring
  refine ⟨⟨q, hq⟩, m, by rw [hq, hmq]; ring, by rw [hXr, hm]; push_cast; ring, ?_⟩
  -- `Y`: from `X Y = N b c` with `X = m c` and `N = (2b + a) q`, `m² = q b`.
  have hm0 : (0 : ℝ) < m := by
    have : 0 < Xn := by
      have := dist_pos.mpr (D.target.indep.injective.ne (show (0 : Fin 3) ≠ 1 by decide))
      rw [hXr] at this
      exact_mod_cast this
    have : 0 < m := by rw [hm] at this; exact Nat.pos_of_mul_pos_left this
    exact_mod_cast this
  have hc0' : (0 : ℝ) < c := by exact_mod_cast hc0
  have hmqR : (m : ℝ) ^ 2 = q * b := by exact_mod_cast hmq
  have hqR : (N : ℝ) = (2 * b + a) * q := by exact_mod_cast hq
  have hmR : (Xn : ℝ) = c * m := by exact_mod_cast hm
  rw [hmR, hqR] at hXY
  have : (m : ℝ) * c * (dist (D.target.pts 0) (D.target.pts 2) - m * (2 * b + a)) = 0 := by
    linear_combination hXY - (2 * b + a) * c * hmqR
  have := (mul_eq_zero.mp this).resolve_left (by positivity)
  linarith

end TriangleTiling
