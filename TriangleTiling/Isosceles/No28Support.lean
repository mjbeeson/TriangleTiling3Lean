/-
Support for `lemma:no28` (Section 10 of M. Beeson, *Tilings of an isosceles triangle*):
segments, the side coordinate, angle counts at points of a side, the corner of a tile at the end of
an edge, edge length against opposite angle, and arithmetic of `(a, b, c)`.

Conventions as in `TriangleTiling.Isosceles.AreaEquation`.
-/
import TriangleTiling.Isosceles.N4Helper
import TriangleTiling.Tiling.Chord
import TriangleTiling.Tiling.Rays
import TriangleTiling.Tiling.Local

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

/-! ### Segments -/

theorem dist_le_of_mem_segment₂ {P Q u v : Plane} (hu : u ∈ segment ℝ P Q)
    (hv : v ∈ segment ℝ P Q) : dist u v ≤ dist P Q := by
  rw [segment_eq_image_lineMap] at hu hv
  obtain ⟨s, hs, rfl⟩ := hu
  obtain ⟨t, ht, rfl⟩ := hv
  rw [dist_lineMap_lineMap, Real.dist_eq]
  have : |s - t| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1, ht.2], by linarith [hs.2, ht.1]⟩
  nlinarith [dist_nonneg (x := P) (y := Q), abs_nonneg (s - t)]

/-- A sub-segment of `PQ` as long as `PQ` is `PQ` itself. -/
theorem endpoints_of_full_subsegment {P Q u v : Plane} (hPQ : P ≠ Q)
    (hu : u ∈ segment ℝ P Q) (hv : v ∈ segment ℝ P Q) (hd : dist u v = dist P Q) :
    (u = P ∧ v = Q) ∨ (u = Q ∧ v = P) := by
  rw [segment_eq_image_lineMap] at hu hv
  obtain ⟨s, hs, rfl⟩ := hu
  obtain ⟨t, ht, rfl⟩ := hv
  rw [dist_lineMap_lineMap, Real.dist_eq] at hd
  have hd0 : 0 < dist P Q := dist_pos.mpr hPQ
  have h1 : |s - t| = 1 := by
    have := mul_right_cancel₀ hd0.ne' (hd.trans (one_mul _).symm); exact this
  rcases abs_eq (zero_le_one) |>.mp h1 with h | h
  · right
    have hs1 : s = 1 := by linarith [hs.2, ht.1]
    have ht0 : t = 0 := by linarith [hs.2, ht.1]
    rw [hs1, ht0, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero]; exact ⟨rfl, rfl⟩
  · left
    have hs0 : s = 0 := by linarith [hs.1, ht.2]
    have ht1 : t = 1 := by linarith [hs.1, ht.2]
    rw [hs0, ht1, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero]; exact ⟨rfl, rfl⟩

/-! ### The side coordinate -/

/-- `cross (B - A) (X - A)` is the coordinate of `X` at `C`, times its value at `C`. -/
theorem cross_eq_coord (T : Tri) (X : Plane) :
    cross (T.pts 1 - T.pts 0) (X - T.pts 0)
      = T.basis.coord 2 X * cross (T.pts 1 - T.pts 0) (T.pts 2 - T.pts 0) := by
  have h := T.basis.linear_combination_coord_eq_self X
  rw [Fin.sum_univ_three] at h
  have hs := Tri.coord_sum T X
  have h0 : X 0 = T.basis.coord 0 X * T.pts 0 0 + T.basis.coord 1 X * T.pts 1 0
      + T.basis.coord 2 X * T.pts 2 0 := by
    have := congrArg (fun Y : Plane => Y 0) h
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at this
    exact this.symm
  have h1 : X 1 = T.basis.coord 0 X * T.pts 0 1 + T.basis.coord 1 X * T.pts 1 1
      + T.basis.coord 2 X * T.pts 2 1 := by
    have := congrArg (fun Y : Plane => Y 1) h
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at this
    exact this.symm
  simp only [cross, PiLp.sub_apply]
  rw [h0, h1]
  have hc0 : T.basis.coord 0 X = 1 - T.basis.coord 1 X - T.basis.coord 2 X := by linarith
  rw [hc0]; ring

/-- A point on side `AB` (index `0 → 1`) has coordinate `0` at `C`. -/
theorem coord_two_of_mem_side (T : Tri) {X : Plane} (hX : X ∈ segment ℝ (T.pts 0) (T.pts 1)) :
    T.basis.coord 2 X = 0 := by
  rw [segment_eq_image_lineMap] at hX
  obtain ⟨t, -, rfl⟩ := hX
  rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]; simp

/-- A point of the triangle with coordinate `0` at `C` lies on side `AB`. -/
theorem mem_side_of_coord_two (T : Tri) {X : Plane} (hX : X ∈ T.carrier)
    (h2 : T.basis.coord 2 X = 0) : X ∈ segment ℝ (T.pts 0) (T.pts 1) := by
  have hc := (Tri.mem_carrier_iff_coord T X).mp hX
  have h := T.basis.linear_combination_coord_eq_self X
  rw [Fin.sum_univ_three] at h
  have hs := Tri.coord_sum T X
  rw [segment_eq_image_lineMap]
  refine ⟨T.basis.coord 1 X, ⟨hc 1, by linarith [hc 0]⟩, ?_⟩
  rw [AffineMap.lineMap_apply_module]
  calc (1 - T.basis.coord 1 X) • T.pts 0 + T.basis.coord 1 X • T.pts 1
      = T.basis.coord 0 X • T.basis 0 + T.basis.coord 1 X • T.basis 1
          + T.basis.coord 2 X • T.basis 2 := by
        rw [h2, zero_smul, add_zero, show (1 - T.basis.coord 1 X) = T.basis.coord 0 X by linarith]
        rfl
    _ = X := h

/-- Angles at a point `P` of a line `AB`, toward two other points of the line, from a point `R`:
equal (same side of `P`) or supplementary (opposite sides). -/
theorem angle_on_line' {A B R : Plane} {s x y : ℝ} (hx : x ≠ s) (hy : y ≠ s) :
    ∠ R (AffineMap.lineMap A B s) (AffineMap.lineMap A B x)
        = ∠ R (AffineMap.lineMap A B s) (AffineMap.lineMap A B y) ∨
      ∠ R (AffineMap.lineMap A B s) (AffineMap.lineMap A B x)
        = Real.pi - ∠ R (AffineMap.lineMap A B s) (AffineMap.lineMap A B y) := by
  have hv : ∀ r : ℝ, AffineMap.lineMap A B r -ᵥ AffineMap.lineMap A B s = (r - s) • (B -ᵥ A) := by
    intro r
    simp only [AffineMap.lineMap_apply_module', vsub_eq_sub, sub_smul]
    abel
  simp only [EuclideanGeometry.angle, hv]
  have hx' : x - s ≠ 0 := sub_ne_zero.mpr hx
  have hy' : y - s ≠ 0 := sub_ne_zero.mpr hy
  rcases lt_or_gt_of_ne hx' with h1 | h1 <;> rcases lt_or_gt_of_ne hy' with h2 | h2
  · left
    rw [InnerProductGeometry.angle_smul_right_of_neg _ _ h1,
      InnerProductGeometry.angle_smul_right_of_neg _ _ h2]
  · right
    rw [InnerProductGeometry.angle_smul_right_of_neg _ _ h1,
      InnerProductGeometry.angle_smul_right_of_pos _ _ h2, InnerProductGeometry.angle_neg_right]
  · right
    rw [InnerProductGeometry.angle_smul_right_of_pos _ _ h1,
      InnerProductGeometry.angle_smul_right_of_neg _ _ h2, InnerProductGeometry.angle_neg_right]
    ring
  · left
    rw [InnerProductGeometry.angle_smul_right_of_pos _ _ h1,
      InnerProductGeometry.angle_smul_right_of_pos _ _ h2]

/-! ### Angle counts -/

section Counts

variable {N : ℕ} (D : CongruentDissection N)

theorem angleCount_pos {P : Plane} {θ : ℝ} {i : Fin N} (hi : (D.tile i).localAngle P = θ) :
    1 ≤ angleCount D P θ :=
  Finset.card_pos.mpr ⟨i, by simp [hi]⟩

theorem eq_of_angleCount_le_one {P : Plane} {θ : ℝ} (h : angleCount D P θ ≤ 1) {i j : Fin N}
    (hi : (D.tile i).localAngle P = θ) (hj : (D.tile j).localAngle P = θ) : i = j :=
  Finset.card_le_one.mp h i (by simp [hi]) j (by simp [hj])

theorem ne_of_angleCount_zero {P : Plane} {θ : ℝ} (h : angleCount D P θ = 0) (i : Fin N) :
    (D.tile i).localAngle P ≠ θ := fun hi => by
  have := angleCount_pos D hi; omega

variable (hγ : tileγ D = 2 * tileα D) (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
include hγ hirr

/-- At a point inside a side of `ABC` where some tile has its `γ`, there is exactly one tile
with each of `α, β, γ`, and no other. -/
theorem counts_at_side {V : Plane} (hV : V ∈ frontier D.target.carrier)
    (hVc : V ∉ Set.range D.target.pts) (h1 : 1 ≤ angleCount D V (tileγ D)) :
    angleCount D V (tileα D) = 1 ∧ angleCount D V (tileβ D) = 1 ∧
      angleCount D V (tileγ D) = 1 ∧ angleCount D V Real.pi = 0 ∧
        angleCount D V (2 * Real.pi) = 0 := by
  have hloc : D.target.localAngle V = (0 : ℤ) * tileα D + (1 : ℤ) * Real.pi := by
    rw [D.target.localAngle_frontier hV hVc]; push_cast; ring
  have := vertex_relations D hγ hirr V 0 1 hloc
  omega

/-- At a point inside a side of `ABC`, at most one tile has its `β`, and at most one its `γ`. -/
theorem counts_at_side_le {V : Plane} (hV : V ∈ frontier D.target.carrier)
    (hVc : V ∉ Set.range D.target.pts) :
    angleCount D V (tileβ D) ≤ 1 ∧ angleCount D V (tileγ D) ≤ 1 := by
  have hloc : D.target.localAngle V = (0 : ℤ) * tileα D + (1 : ℤ) * Real.pi := by
    rw [D.target.localAngle_frontier hV hVc]; push_cast; ring
  have := vertex_relations D hγ hirr V 0 1 hloc
  omega

variable (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
  (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
include hA hC

/-- At the corners `A` and `C` only an `α` occurs; at `B` an `α` and at most one `β`. -/
theorem counts_at_corners :
    angleCount D (D.target.pts 0) (tileβ D) = 0 ∧ angleCount D (D.target.pts 0) (tileγ D) = 0 ∧
    angleCount D (D.target.pts 2) (tileβ D) = 0 ∧ angleCount D (D.target.pts 2) (tileγ D) = 0 ∧
    angleCount D (D.target.pts 1) (tileβ D) ≤ 1 ∧ angleCount D (D.target.pts 1) (tileγ D) = 0 ∧
    angleCount D (D.target.pts 0) (tileα D) = 1 ∧ angleCount D (D.target.pts 1) (tileα D) ≤ 1 := by
  have hTsum := cornerAngle_sum D.target
  have eA : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D := hA
  have eC : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = tileα D := by
    rw [cornerAngle, angle_comm]; exact hC
  have h0 : D.target.localAngle (D.target.pts 0) = (1 : ℤ) * tileα D + (0 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = _
    push_cast; linarith
  have h1 : D.target.localAngle (D.target.pts 1) = (-2 : ℤ) * tileα D + (1 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = _
    push_cast; linarith
  have h2 : D.target.localAngle (D.target.pts 2) = (1 : ℤ) * tileα D + (0 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = _
    push_cast; linarith
  have r0 := vertex_relations D hγ hirr _ 1 0 h0
  have r1 := vertex_relations D hγ hirr _ (-2) 1 h1
  have r2 := vertex_relations D hγ hirr _ 1 0 h2
  have hb1 : angleCount D (D.target.pts 1) (tileβ D) ≤ 1 := by omega
  refine ⟨by omega, by omega, by omega, by omega, hb1, ?_, by omega, ?_⟩
  · interval_cases h : angleCount D (D.target.pts 1) (tileβ D) <;> omega
  · interval_cases h : angleCount D (D.target.pts 1) (tileβ D) <;> omega

end Counts

/-! ### Corners of a single tile -/

section Corners

variable {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
  (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
include hγ hirr

/-- A tile has its angle `θ` (one of `α, β, γ`) at exactly one vertex. -/
theorem corner_unique (i : Fin N) {θ : ℝ} (hθ : θ = tileα D ∨ θ = tileβ D ∨ θ = tileγ D)
    {j j' : Fin 3} (hj : (D.tile i).localAngle ((D.tile i).pts j) = θ)
    (hj' : (D.tile i).localAngle ((D.tile i).pts j') = θ) : j = j' := by
  rw [Tri.localAngle_vertex] at hj hj'
  have hcnt := tile_angle_count D hγ hirr i
  have hcard : (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
      ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = θ).card ≤ 1 := by
    rcases hθ with rfl | rfl | rfl
    · exact hcnt.1.le
    · exact hcnt.2.1.le
    · exact hcnt.2.2.le
  exact Finset.card_le_one.mp hcard j (by simp [hj]) j' (by simp [hj'])

/-- A tile has its angle `θ` (one of `α, β, γ`) at some vertex. -/
theorem corner_exists (i : Fin N) {θ : ℝ} (hθ : θ = tileα D ∨ θ = tileβ D ∨ θ = tileγ D) :
    ∃ j : Fin 3, (D.tile i).localAngle ((D.tile i).pts j) = θ := by
  have hcnt := tile_angle_count D hγ hirr i
  have hcard : (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
      ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = θ).card = 1 := by
    rcases hθ with rfl | rfl | rfl
    · exact hcnt.1
    · exact hcnt.2.1
    · exact hcnt.2.2
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have : j ∈ Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
      ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = θ := by rw [hj]; simp
  exact ⟨j, by rw [Tri.localAngle_vertex]; exact (Finset.mem_filter.mp this).2⟩

/-- If a tile's angle opposite edge `k` is not `θ`, its `θ` is at an end of edge `k`. -/
theorem corner_at_endpoint (i : Fin N) (k : Fin 3) {θ : ℝ}
    (hθ : θ = tileα D ∨ θ = tileβ D ∨ θ = tileγ D)
    (hopp : (D.tile i).localAngle ((D.tile i).pts (k + 2)) ≠ θ) :
    (D.tile i).localAngle ((D.tile i).pts k) = θ ∨
      (D.tile i).localAngle ((D.tile i).pts (k + 1)) = θ := by
  obtain ⟨j, hj⟩ := corner_exists D hγ hirr i hθ
  have : j = k ∨ j = k + 1 ∨ j = k + 2 := by fin_cases j <;> fin_cases k <;> simp
  rcases this with rfl | rfl | rfl
  · exact Or.inl hj
  · exact Or.inr hj
  · exact absurd hj hopp

end Corners

/-! ### Arithmetic of the integer tile -/

/-- For integer sides `(a, b, c)` with no common factor and `c² = a² + ab` (and the triangle
inequalities): `a < c`, `a ≠ b`, and `b` does not divide `a`. -/
theorem int_tile_facts {a b c : ℕ} (hcop : Nat.gcd (Nat.gcd a b) c = 1)
    (hcab : c ^ 2 = a ^ 2 + a * b) (h1 : a < b + c) (h2 : b < a + c) (h3 : c < a + b) :
    a < c ∧ a ≠ b ∧ ¬ b ∣ a := by
  obtain ⟨k, m, hkm, hlt, h2k, rfl, rfl, rfl⟩ := (luthar a b c).mp ⟨hcop, hcab, h1, h2, h3⟩
  have hk2 : 2 ≤ k := by omega
  have hle : k ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hlt.le 2
  refine ⟨?_, ?_, ?_⟩
  · have : k * k < k * m := Nat.mul_lt_mul_of_pos_left hlt (by omega)
    nlinarith
  · intro h
    -- `m² = 2k²` contradicts `gcd(k, m) = 1`.
    have hm2 : m ^ 2 = 2 * k ^ 2 := by omega
    have h2m : 2 ∣ m := Nat.prime_two.dvd_of_dvd_pow (n := 2) ⟨k ^ 2, hm2⟩
    obtain ⟨m', rfl⟩ := h2m
    have hk2' : 2 ∣ k := Nat.prime_two.dvd_of_dvd_pow (n := 2) ⟨m' ^ 2, by nlinarith⟩
    have := Nat.dvd_gcd hk2' (dvd_mul_right 2 m')
    rw [hkm] at this
    omega
  · intro hdvd
    have hcop' : Nat.Coprime (k ^ 2) (m ^ 2 - k ^ 2) := by
      have h1 : Nat.Coprime (k ^ 2) (m ^ 2) := Nat.Coprime.pow 2 2 hkm
      rw [Nat.coprime_comm, Nat.Coprime]
      have : Nat.gcd (m ^ 2 - k ^ 2) (k ^ 2) ∣ m ^ 2 := by
        have := Nat.dvd_add (Nat.gcd_dvd_left (m ^ 2 - k ^ 2) (k ^ 2))
          (Nat.gcd_dvd_right (m ^ 2 - k ^ 2) (k ^ 2))
        rwa [Nat.sub_add_cancel hle] at this
      have h3 := Nat.dvd_gcd (Nat.gcd_dvd_right (m ^ 2 - k ^ 2) (k ^ 2)) this
      rw [h1.gcd_eq_one] at h3
      exact Nat.dvd_one.mp h3
    have hb1 : m ^ 2 - k ^ 2 = 1 := Nat.Coprime.eq_one_of_dvd hcop'.symm hdvd
    have : (k + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hlt 2
    nlinarith

end TriangleTiling
