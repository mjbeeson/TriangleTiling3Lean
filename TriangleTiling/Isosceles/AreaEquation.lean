/-
The area equations for tilings with `γ = 2α`, from Section 10 of M. Beeson,
*Tilings of an isosceles triangle*.

Lean names follow the TeX labels: `lemma:areaequation` is `areaequation`,
`lemma:areaequation2` is `areaequation2`.

Conventions. A tiling is Bonfioli's `CongruentDissection N`. Its target `ABC` has vertices
`A, B, C = target.pts 0, 1, 2`, with base `AC`. Its model tile has vertices
`model.pts 0, 1, 2`, with angles `α, β, γ` there and opposite sides
`a = |pts 1 pts 2|`, `b = |pts 2 pts 0|`, `c = |pts 0 pts 1|`.
-/
import TriangleTiling.Isosceles.GammaTwoAlpha
import Erdos634.AreaDet

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry MeasureTheory

/-- The three strict triangle inequalities for affinely independent points. -/
theorem strict_triangle_ineqs {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {A B C : P} (h : AffineIndependent ℝ ![A, B, C]) :
    dist B C < dist C A + dist A B ∧ dist C A < dist A B + dist B C ∧
      dist A B < dist B C + dist C A := by
  have hcol := affineIndependent_iff_not_collinear_set.mp h
  have t1 := dist_lt_dist_add_dist_of_not_collinear hcol
  have t2 := dist_lt_dist_add_dist_of_not_collinear (A := B) (B := A) (C := C)
    (by rwa [Set.insert_comm])
  have t3 := dist_lt_dist_add_dist_of_not_collinear (A := A) (B := C) (C := B)
    (by rwa [Set.pair_comm])
  rw [dist_comm A C] at t1
  rw [dist_comm B A, dist_comm A C] at t2
  rw [dist_comm A C, dist_comm C B] at t3
  exact ⟨by linarith, t1, by linarith⟩

/-- The vertices of a `Tri`, in the form `![p₀, p₁, p₂]`. -/
theorem tri_indep (T : Tri) : AffineIndependent ℝ ![T.pts 0, T.pts 1, T.pts 2] := by
  convert T.indep using 1
  ext i; fin_cases i <;> rfl

/-! ### Areas via Heron's formula

Adapted from Bonfioli's `Erdos634.ARA` (`ARAGeom.lean`), restated with distances so as not to
import that module's heavy dependencies. -/

/-- `16 · (area)²` of a triangle with side lengths `a, b, c` (Heron's formula, squared). -/
noncomputable def heron16 (a b c : ℝ) : ℝ :=
  2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2 - a ^ 4 - b ^ 4 - c ^ 4

theorem dist_sq_plane (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem four_detTri_sq (T : Tri) :
    4 * Erdos634.AreaDet.detTri T ^ 2 =
      heron16 (dist (T.pts 1) (T.pts 2)) (dist (T.pts 2) (T.pts 0)) (dist (T.pts 0) (T.pts 1)) := by
  rw [Erdos634.AreaDet.detTri_eq, heron16]
  have e0 := dist_sq_plane (T.pts 1) (T.pts 2)
  have e1 := dist_sq_plane (T.pts 2) (T.pts 0)
  have e2 := dist_sq_plane (T.pts 0) (T.pts 1)
  have q : ∀ x : ℝ, x ^ 4 = (x ^ 2) ^ 2 := fun x => by ring
  simp only [q, e0, e1, e2]
  simp only [PiLp.sub_apply]
  ring

/-- **Area relation in Heron form.** For a tiling by `N` congruent tiles,
`N² · 16 (area of tile)² = 16 (area of target)²`. (Bonfioli's `area_heron`.) -/
theorem area_heron {N : ℕ} (D : CongruentDissection N) :
    (N : ℝ) ^ 2 * heron16 (dist (D.model.pts 1) (D.model.pts 2))
        (dist (D.model.pts 2) (D.model.pts 0)) (dist (D.model.pts 0) (D.model.pts 1)) =
      heron16 (dist (D.target.pts 1) (D.target.pts 2))
        (dist (D.target.pts 2) (D.target.pts 0)) (dist (D.target.pts 0) (D.target.pts 1)) := by
  have hv := Erdos634.CongruentArea.congruentDissection_volume_target D
  rw [Erdos634.AreaDet.volume_eq_det_mul, Erdos634.AreaDet.volume_eq_det_mul] at hv
  have hM := D.model.volume_pos
  rw [Erdos634.AreaDet.volume_eq_det_mul] at hM
  have hc0 : volume Erdos634.AreaDet.stdCarrier ≠ 0 := by
    intro h; rw [h, mul_zero] at hM; exact lt_irrefl _ hM
  have hct : volume Erdos634.AreaDet.stdCarrier ≠ ⊤ :=
    (Erdos634.AreaDet.isCompact_stdCarrier.measure_lt_top).ne
  rw [← mul_assoc] at hv
  have h2 := (ENNReal.mul_left_inj hc0 hct).1 hv
  have h3 : ENNReal.ofReal |Erdos634.AreaDet.detTri D.target| =
      ENNReal.ofReal ((N : ℝ) * |Erdos634.AreaDet.detTri D.model|) := by
    rw [h2, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  have h4 := (ENNReal.ofReal_eq_ofReal_iff (abs_nonneg _) (by positivity)).1 h3
  rw [← four_detTri_sq, ← four_detTri_sq]
  have : Erdos634.AreaDet.detTri D.target ^ 2 =
      ((N : ℝ) * |Erdos634.AreaDet.detTri D.model|) ^ 2 := by
    rw [← h4, sq_abs]
  rw [this, mul_pow, sq_abs]; ring

/-! ### The area equations -/

/-- The common core of `lemma:areaequation` and `lemma:areaequation2`: under their hypotheses,
`|BC| = |AB|`, `a |AC| = c |AB|`, and `|AB|² = N a b`. -/
theorem areaequation_core {N : ℕ} (D : CongruentDissection N) {a b c X Y : ℝ}
    (ha : dist (D.model.pts 1) (D.model.pts 2) = a)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = b)
    (hc : dist (D.model.pts 0) (D.model.pts 1) = c)
    (hX : dist (D.target.pts 0) (D.target.pts 1) = X)
    (hY : dist (D.target.pts 2) (D.target.pts 0) = Y)
    (hγ : ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) =
      2 * ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2)) :
    dist (D.target.pts 1) (D.target.pts 2) = X ∧ a * Y = c * X ∧ X ^ 2 = N * a * b := by
  set M := D.model.pts with hM
  set T := D.target.pts with hT
  set X' := dist (T 1) (T 2) with hX'
  set k := Real.cos (∠ (M 1) (M 0) (M 2)) with hk
  -- The tile: `c² = a² + ab` (`lemma:twoalphatiles`) and the strict triangle inequalities.
  have hcab : c ^ 2 = a ^ 2 + a * b := (twoalphatiles (tri_indep D.model) ha hb hc).mp hγ
  obtain ⟨m1, m2, m3⟩ := strict_triangle_ineqs (tri_indep D.model)
  rw [ha, hb, hc] at m1 m2 m3
  obtain ⟨t1, t2, t3⟩ := strict_triangle_ineqs (tri_indep D.target)
  rw [hX, hY] at t1 t2 t3
  rw [← hX'] at t1 t2 t3
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hY0 : 0 < Y := by linarith
  -- The law of cosines at the tile's `α` vertex, and at `A` and `C`.
  have hα : 2 * b * c * k = b ^ 2 + c ^ 2 - a ^ 2 := by
    have := law_cos (M 1) (M 0) (M 2)
    rw [ha, dist_comm (M 1) (M 0), hc, hb, ← hk] at this
    linear_combination this
  have eA : X' ^ 2 = X ^ 2 + Y ^ 2 - 2 * X * Y * k := by
    have := law_cos (T 1) (T 0) (T 2)
    rw [hA, ← hk, dist_comm (T 1) (T 0), hX, hY] at this
    linear_combination this
  have eC : X ^ 2 = X' ^ 2 + Y ^ 2 - 2 * X' * Y * k := by
    have := law_cos (T 1) (T 2) (T 0)
    rw [hC, ← hk, dist_comm (T 1) (T 0), hX, dist_comm (T 0) (T 2), hY] at this
    linear_combination this
  -- `-1 < k < 1`, from the strict triangle inequalities of the tile.
  have p1 : (0 : ℝ) < a - b + c := by linarith
  have p2 : (0 : ℝ) < a + b - c := by linarith
  have p3 : (0 : ℝ) < b + c - a := by linarith
  have p4 : (0 : ℝ) < a + b + c := by linarith
  have e1 : 2 * b * c * (1 - k) = (a - b + c) * (a + b - c) := by linear_combination -hα
  have e2 : 2 * b * c * (1 + k) = (b + c - a) * (a + b + c) := by linear_combination hα
  have hbc : 0 < 2 * b * c := by positivity
  have hk1 : k < 1 := by nlinarith [mul_pos p1 p2]
  have hk1' : -1 < k := by nlinarith [mul_pos p3 p4]
  -- The equal base angles force `|BC| = |AB|`.
  have hXX : X' = X := by
    have h0 : (X' - X) * (X' + X - Y * k) = 0 := by linear_combination (eA - eC) / 2
    have h1 : X' + X - Y * k ≠ 0 := by nlinarith
    have := (mul_eq_zero.mp h0).resolve_right h1
    linarith
  -- Hence `|AC| = 2 |AB| cos α`, and `cos α = c / (2a)` in the tile.
  have hYk : Y = 2 * X * k := by
    rw [hXX] at eA
    have : Y * (Y - 2 * X * k) = 0 := by linear_combination -eA
    have := (mul_eq_zero.mp this).resolve_left hY0.ne'
    linarith
  have hak : 2 * a * k = c := by
    have h1 : b * (2 * c * k - (a + b)) = 0 := by linear_combination hα + hcab
    have h2 := (mul_eq_zero.mp h1).resolve_left hb0.ne'
    have h3 : c * (2 * a * k - c) = 0 := by linear_combination a * h2 - hcab
    have := (mul_eq_zero.mp h3).resolve_left hc0.ne'
    linarith
  refine ⟨hXX, by rw [hYk, ← hak]; ring, ?_⟩
  -- Heron: `N² · 4b²c²(1 - k²) = 16 X⁴ k² (1 - k²)`.
  have hH := area_heron D
  rw [ha, hb, hc, ← hX', hXX, hY, hX] at hH
  have hH1 : heron16 a b c = 4 * b ^ 2 * c ^ 2 * (1 - k ^ 2) := by
    unfold heron16; linear_combination (2 * b * c * k + (b ^ 2 + c ^ 2 - a ^ 2)) * hα
  have hH2 : heron16 X Y X = 16 * X ^ 4 * k ^ 2 * (1 - k ^ 2) := by
    unfold heron16; rw [hYk]; ring
  rw [hH1, hH2] at hH
  have hpos : 0 < 1 - k ^ 2 := by
    have := mul_pos (sub_pos.mpr hk1) (show (0 : ℝ) < 1 + k by linarith)
    linarith [show (1 - k) * (1 + k) = 1 - k ^ 2 by ring]
  have h4 : (N : ℝ) ^ 2 * b ^ 2 * c ^ 2 = 4 * X ^ 4 * k ^ 2 := by
    have : (1 - k ^ 2) * (4 * ((N : ℝ) ^ 2 * b ^ 2 * c ^ 2 - 4 * X ^ 4 * k ^ 2)) = 0 := by
      linear_combination hH
    have := (mul_eq_zero.mp this).resolve_left hpos.ne'
    linarith
  -- Multiply by `a²` and use `2ak = c`: `N² a² b² c² = X⁴ c²`, so `(X²)² = (Nab)²`.
  have h5 : c ^ 2 * (((N : ℝ) * a * b) ^ 2 - (X ^ 2) ^ 2) = 0 := by
    linear_combination a ^ 2 * h4 + (X ^ 4 * (2 * a * k + c)) * hak
  have h6 := (mul_eq_zero.mp h5).resolve_left (by positivity)
  have h7 : (X ^ 2 - N * a * b) * (X ^ 2 + N * a * b) = 0 := by linear_combination -h6
  have h8 : 0 < X ^ 2 + N * a * b := by
    have : 0 < X := by linarith
    positivity
  exact sub_eq_zero.mp ((mul_eq_zero.mp h7).resolve_right h8.ne')

/-- **Lemma `lemma:areaequation`.** Suppose the isosceles triangle `ABC`, with base angles
`α` at `A` and `C`, is `N`-tiled by a tile with sides `(a, b, c)` and angles `(α, β, 2α)`.
Let `X = |AB|`. Then `X² = N a b`. -/
theorem areaequation {N : ℕ} (D : CongruentDissection N) {a b c X : ℝ}
    (ha : dist (D.model.pts 1) (D.model.pts 2) = a)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = b)
    (hc : dist (D.model.pts 0) (D.model.pts 1) = c)
    (hX : dist (D.target.pts 0) (D.target.pts 1) = X)
    (hγ : ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) =
      2 * ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2)) :
    X ^ 2 = N * a * b :=
  (areaequation_core D ha hb hc hX rfl hγ hA hC).2.2

/-- **Lemma `lemma:areaequation2`.** Under the hypotheses of `lemma:areaequation`, with
`X = |AB|` and `Y = |AC|`: `X Y = N b c` and `Y = (c / a) X`. -/
theorem areaequation2 {N : ℕ} (D : CongruentDissection N) {a b c X Y : ℝ}
    (ha : dist (D.model.pts 1) (D.model.pts 2) = a)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = b)
    (hc : dist (D.model.pts 0) (D.model.pts 1) = c)
    (hX : dist (D.target.pts 0) (D.target.pts 1) = X)
    (hY : dist (D.target.pts 0) (D.target.pts 2) = Y)
    (hγ : ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) =
      2 * ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2)) :
    X * Y = N * b * c ∧ Y = c / a * X := by
  obtain ⟨-, h2, h3⟩ :=
    areaequation_core D (Y := Y) ha hb hc hX (by rw [dist_comm]; exact hY) hγ hA hC
  obtain ⟨m1, m2, m3⟩ := strict_triangle_ineqs (tri_indep D.model)
  rw [ha, hb, hc] at m1 m2 m3
  have ha0 : 0 < a := by linarith
  have hY' : Y = c / a * X := by
    rw [div_mul_eq_mul_div, eq_div_iff ha0.ne']; linear_combination h2
  refine ⟨?_, hY'⟩
  -- `X Y = X² c / a = N a b c / a = N b c`.
  rw [hY']
  field_simp
  linear_combination c * h3
