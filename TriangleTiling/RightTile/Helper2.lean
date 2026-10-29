/-
`lemma:isosceleshelper2` (Section 6 of M. Beeson, *Tilings of an isosceles triangle*).

Let the isosceles triangle `ABC` with base angles `β` (at `A` and `C`) be `N`-tiled by a tile with
angles `(α, β, π/2)` and sides `(a, b, c)` (`c` the hypotenuse). If `β ≠ π/6` and `λ = √(N/2)` is
irrational, then `a/c` and `b/c` lie in `ℚ(λ)`.

This file first collects the facts about the tile and the sides that the proof uses.
-/
import TriangleTiling.RightTile.Area
import TriangleTiling.RightTile.QuadField
import TriangleTiling.RightTile.AllC
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry Polynomial

variable {N : ℕ} (D : CongruentDissection N)

/-- The tile's legs: `a = c cos β` and `b = c cos α`. -/
theorem right_trig (hright : tileγ D = Real.pi / 2) :
    dist (D.model.pts 1) (D.model.pts 2) =
        Real.cos (tileβ D) * dist (D.model.pts 0) (D.model.pts 1) ∧
      dist (D.model.pts 2) (D.model.pts 0) =
        Real.cos (tileα D) * dist (D.model.pts 0) (D.model.pts 1) := by
  have h1 : ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = Real.pi / 2 := hright
  have h2 : ∠ (D.model.pts 1) (D.model.pts 2) (D.model.pts 0) = Real.pi / 2 := by
    rw [angle_comm]; exact h1
  constructor
  · exact (cos_angle_mul_dist_of_angle_eq_pi_div_two h1).symm
  · have := cos_angle_mul_dist_of_angle_eq_pi_div_two h2
    have e : ∠ (D.model.pts 2) (D.model.pts 0) (D.model.pts 1) = tileα D := angle_comm _ _ _
    rw [e, dist_comm (D.model.pts 1) (D.model.pts 0)] at this
    rw [dist_comm (D.model.pts 2) (D.model.pts 0)]
    exact this.symm

theorem tileα_pos : 0 < tileα D := Erdos634.MarchFlank.cornerAngle_pos D.model 0

theorem tileβ_pos : 0 < tileβ D := Erdos634.MarchFlank.cornerAngle_pos D.model 1

/-- With `α ≠ β`, the angle values of a right-angled tile are distinct and nonzero. -/
theorem anglesSep_right' (hright : tileγ D = Real.pi / 2) (hαβ : tileα D ≠ tileβ D) :
    AnglesSep D := by
  have hβ := right_beta D hright
  have hα0 := tileα_pos D
  have hβ0 := tileβ_pos D
  have hpi := Real.pi_pos
  refine ⟨fun j => ?_, fun i j h => ?_⟩
  · fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, ne_eq] <;>
      first | exact hα0.ne' | exact hβ0.ne' | (rw [hright]; positivity) | positivity
  · fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h ⊢ <;>
      first
      | rfl
      | exact absurd h hαβ
      | exact absurd h.symm hαβ
      | (exfalso; rw [hright] at h; linarith)
      | (exfalso; rw [hβ] at h; linarith)
      | (exfalso; linarith)

/-- Equal legs exactly when the acute angles are equal. -/
theorem legs_eq_iff (hright : tileγ D = Real.pi / 2) :
    dist (D.model.pts 1) (D.model.pts 2) = dist (D.model.pts 2) (D.model.pts 0) →
      tileα D = tileβ D := by
  intro h
  obtain ⟨ha, hb⟩ := right_trig D hright
  have hc : 0 < dist (D.model.pts 0) (D.model.pts 1) :=
    dist_pos.mpr fun e => by have := D.model.indep.injective e; exact absurd this (by decide)
  rw [ha, hb] at h
  have hcos := mul_right_cancel₀ hc.ne' h
  have hβ := right_beta D hright
  have hα0 := tileα_pos D
  have hβ0 := tileβ_pos D
  exact (Real.injOn_cos ⟨hβ0.le, by linarith [Real.pi_pos]⟩
    ⟨hα0.le, by linarith [Real.pi_pos]⟩ hcos).symm

/-- **Congruence data**: one permutation matches corner angles and distances. -/
theorem corner_perm_dist {T U : Tri} (h : T.Congruent U) :
    ∃ σ : Equiv.Perm (Fin 3), (∀ k : Fin 3,
      cornerAngle (U.pts (σ k + 1)) (U.pts (σ k)) (U.pts (σ k + 2))
        = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))) ∧
      ∀ j k, dist (T.pts j) (T.pts k) = dist (U.pts (σ j)) (U.pts (σ k)) := by
  obtain ⟨f, σ, hf⟩ := h
  refine ⟨σ, fun k => ?_, fun j k => by rw [← hf j, ← hf k, f.dist_eq]⟩
  have hmap : cornerAngle (U.pts (σ (k + 1))) (U.pts (σ k)) (U.pts (σ (k + 2)))
      = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by
    rw [← hf (k + 1), ← hf k, ← hf (k + 2)]
    rw [Erdos634.Geometry.cornerAngle, Erdos634.Geometry.cornerAngle]
    rw [show (f : Plane → Plane) = f.toRealAffineIsometryEquiv from
      (IsometryEquiv.coeFn_toRealAffineIsometryEquiv f).symm]
    exact f.toRealAffineIsometryEquiv.toAffineIsometry.angle_map _ _ _
  have hidx : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z →
      (y = x + 1 ∧ z = x + 2) ∨ (y = x + 2 ∧ z = x + 1) := by decide
  have hne : ∀ x : Fin 3, x ≠ x + 1 ∧ x ≠ x + 2 ∧ x + 1 ≠ x + 2 := by decide
  obtain ⟨h1, h2, h12⟩ := hne k
  rcases hidx (σ k) (σ (k + 1)) (σ (k + 2))
      (fun he => h1 (σ.injective he)) (fun he => h2 (σ.injective he))
      (fun he => h12 (σ.injective he)) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [← ha, ← hb]; exact hmap
  · rw [← ha, ← hb]
    rw [Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]
    exact hmap

/-- The model's corner angles, by index. -/
theorem model_corner (k : Fin 3) :
    cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) =
      ![tileα D, tileβ D, tileγ D] k := by
  fin_cases k <;> rfl

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- **The angles at the ends of an `a` edge** are `β` or `π/2` (when `a` is shorter than `c`, and
`a = b` only if `α = β`). -/
theorem a_edge_end_angles (hab : dist (D.model.pts 1) (D.model.pts 2) =
      dist (D.model.pts 2) (D.model.pts 0) → tileα D = tileβ D)
    (hac : dist (D.model.pts 1) (D.model.pts 2) ≠ dist (D.model.pts 0) (D.model.pts 1))
    (i : Fin N) (k : Fin 3)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) =
      dist (D.model.pts 1) (D.model.pts 2)) (j : Fin 3) (hj : j = k ∨ j = k + 1) :
    (D.tile i).localAngle ((D.tile i).pts j) = tileβ D ∨
      (D.tile i).localAngle ((D.tile i).pts j) = tileγ D := by
  obtain ⟨σ, hang, hd⟩ := corner_perm_dist (D.tiles_congruent i)
  rw [Tri.localAngle_vertex, ← hang, model_corner]
  rw [hd] at hlen
  have hne : σ k ≠ σ (k + 1) := σ.injective.ne (by fin_cases k <;> decide)
  rcases hj with rfl | rfl
  · generalize σ (j + 1) = v at hne hlen ⊢
    generalize σ j = u at hne hlen ⊢
    fin_cases u <;> fin_cases v <;> simp at hne hlen ⊢ <;>
      first
      | exact Or.inl rfl | exact Or.inr rfl
      | exact absurd hlen.symm hac | exact absurd hlen hac
      | (rw [dist_comm] at hlen; exact absurd hlen.symm hac)
      | (rw [dist_comm] at hlen; exact absurd hlen hac)
      | (left; exact hab hlen.symm) | (left; exact hab hlen)
      | (rw [dist_comm] at hlen; left; exact hab hlen.symm)
      | (rw [dist_comm] at hlen; left; exact hab hlen)
  · generalize σ (k + 1) = v at hne hlen ⊢
    generalize σ k = u at hne hlen ⊢
    fin_cases u <;> fin_cases v <;> simp at hne hlen ⊢ <;>
      first
      | exact Or.inl rfl | exact Or.inr rfl
      | exact absurd hlen.symm hac | exact absurd hlen hac
      | (rw [dist_comm] at hlen; exact absurd hlen.symm hac)
      | (rw [dist_comm] at hlen; exact absurd hlen hac)
      | (left; exact hab hlen.symm) | (left; exact hab hlen)
      | (rw [dist_comm] at hlen; left; exact hab hlen.symm)
      | (rw [dist_comm] at hlen; left; exact hab hlen)

/-- **The Cramer step.** With `l` irrational, `l² ∈ ℚ`, `l = p a + q b + r` and
`2 a l = s a + t b + u` (natural coefficients), either `a, b ∈ ℚ(l)`, or `q = r = s = t = 0` and
`l = p a` with `p ≠ 0`. -/
theorem cramer {l : ℝ} {d : ℚ} (hl : l ^ 2 = d) (hirr : ¬ ∃ q : ℚ, l = q) {a b : ℝ}
    {p q r s t u : ℕ} (h1 : l = p * a + q * b + r) (h2 : 2 * a * l = s * a + t * b + u) :
    (InQ l a ∧ InQ l b) ∨ (q = 0 ∧ r = 0 ∧ s = 0 ∧ t = 0 ∧ p ≠ 0 ∧ l = p * a) := by
  set Dt : ℝ := ((p * t - q * s : ℚ) : ℝ) + ((2 * q : ℚ) : ℝ) * l with hDt
  by_cases hD : Dt = 0
  · right
    obtain ⟨hq2, hpt⟩ := InQ.indep hirr (x := 2 * q) (y := p * t - q * s) (by rw [← hD]; ring)
    have hq : q = 0 := by
      have : (q : ℚ) = 0 := by linarith
      exact_mod_cast this
    subst hq
    simp only [Nat.cast_zero, zero_mul, add_zero, sub_zero] at hpt h1
    have hp : p ≠ 0 := by
      rintro rfl
      exact hirr ⟨r, by rw [h1]; simp⟩
    have ht : t = 0 := by
      have : (p : ℚ) * t = 0 := hpt
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (by exact_mod_cast h) hp
      · exact_mod_cast h
    subst ht
    simp only [Nat.cast_zero, zero_mul, add_zero] at h2
    -- `2 (l - r) l = s (l - r) + p u`.
    have hpa : (p : ℝ) * a = l - r := by linarith
    have key : (((-(2 * r + s)) : ℚ) : ℝ) * l + ((2 * d + s * r - p * u : ℚ) : ℝ) = 0 := by
      have e : 2 * ((p : ℝ) * a) * l = s * ((p : ℝ) * a) + p * u := by
        linear_combination (p : ℝ) * h2
      rw [hpa] at e
      push_cast
      linear_combination e - 2 * hl
    obtain ⟨h3, -⟩ := InQ.indep hirr key
    have hrs : (2 * r + s : ℚ) = 0 := by linarith
    have hr : r = 0 := by
      have : (r : ℚ) = 0 := by
        have : (0 : ℚ) ≤ r := Nat.cast_nonneg r
        have : (0 : ℚ) ≤ s := Nat.cast_nonneg s
        linarith
      exact_mod_cast this
    have hs : s = 0 := by
      have : (s : ℚ) = 0 := by
        have : (0 : ℚ) ≤ r := Nat.cast_nonneg r
        have : (0 : ℚ) ≤ s := Nat.cast_nonneg s
        linarith
      exact_mod_cast this
    subst hr hs
    exact ⟨rfl, rfl, rfl, rfl, hp, by simpa using h1⟩
  · left
    have hDin : InQ l Dt := ⟨2 * q, p * t - q * s, by rw [hDt]; ring⟩
    have ea : a = (t * (l - r) + q * u) / Dt := by
      rw [eq_div_iff hD, hDt]; push_cast; linear_combination (-(t : ℝ)) * h1 + (q : ℝ) * h2
    have eb : b = (-(p * u) - (s - 2 * l) * (l - r)) / Dt := by
      rw [eq_div_iff hD, hDt]; push_cast
      linear_combination ((s : ℝ) - 2 * l) * h1 - (p : ℝ) * h2
    have hlr : InQ l (l - r) := InQ.self.sub (InQ.rat r)
    refine ⟨?_, ?_⟩
    · rw [ea]
      refine InQ.div hl hirr ?_ hDin hD
      have h := ((InQ.rat (t : ℚ)).mul hl hlr).add (InQ.rat (q * u : ℚ) (l := l))
      obtain ⟨x, y, hxy⟩ := h
      exact ⟨x, y, by rw [← hxy]; push_cast; ring⟩
    · rw [eb]
      refine InQ.div hl hirr ?_ hDin hD
      have h := (InQ.rat (-(p * u) : ℚ) (l := l)).sub
        (((InQ.rat (s : ℚ)).sub ((InQ.rat 2).mul hl InQ.self)).mul hl hlr)
      obtain ⟨x, y, hxy⟩ := h
      exact ⟨x, y, by rw [← hxy]; push_cast; ring⟩

open Classical in
/-- **A side as a sum of edges.** Side `i` is covered by tile edges with total length
`P a + Q b + R c`; if `Q = R = 0`, all of them are `a` edges. -/
theorem side_rel (i : Fin 3) : ∃ part : Finset (Fin N × Fin 3),
    (⋃ e ∈ part, (D.tile e.1).edge e.2) = segment ℝ (D.target.pts i) (D.target.pts (i + 1)) ∧
    ∃ P Q R : ℕ, dist (D.target.pts i) (D.target.pts (i + 1)) =
      P * dist (D.model.pts 1) (D.model.pts 2) + Q * dist (D.model.pts 2) (D.model.pts 0)
        + R * dist (D.model.pts 0) (D.model.pts 1) ∧
      (Q = 0 → R = 0 → ∀ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
        dist (D.model.pts 1) (D.model.pts 2)) := by
  obtain ⟨part, hcov, -, hsum⟩ := D.toDissection.side_walk i
  set a := dist (D.model.pts 1) (D.model.pts 2)
  set b := dist (D.model.pts 2) (D.model.pts 0)
  set c := dist (D.model.pts 0) (D.model.pts 1)
  set len := fun e : Fin N × Fin 3 => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
  set PA := part.filter fun e => len e = a
  set QB := part.filter fun e => len e ≠ a ∧ len e = b
  set RC := part.filter fun e => len e ≠ a ∧ len e ≠ b
  refine ⟨part, hcov, PA.card, QB.card, RC.card, ?_, ?_⟩
  · rw [← hsum]
    change ∑ e ∈ part, len e = _
    rw [← Finset.sum_filter_add_sum_filter_not part (fun e => len e = a)]
    rw [← Finset.sum_filter_add_sum_filter_not (part.filter fun e => ¬ len e = a)
      (fun e => len e = b), Finset.filter_filter, Finset.filter_filter]
    have h1 : ∑ e ∈ PA, len e = PA.card * a := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2), Finset.sum_const,
        nsmul_eq_mul]
    have h2 : ∑ e ∈ QB, len e = QB.card * b := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2.2), Finset.sum_const,
        nsmul_eq_mul]
    have h3 : ∑ e ∈ RC, len e = RC.card * c := by
      rw [Finset.sum_congr rfl (fun e he => ?_), Finset.sum_const, nsmul_eq_mul]
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp he).2
      rcases edge_len_mem D e.1 e.2 with h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact h
    rw [← h1, ← h2, ← h3]
    rw [add_assoc]
  · intro hQ hR e he
    by_contra hne
    rcases edge_len_mem D e.1 e.2 with h | h | h
    · exact hne h
    · have : e ∈ QB := Finset.mem_filter.mpr ⟨he, hne, h⟩
      rw [Finset.card_eq_zero.mp hQ] at this
      simp at this
    · by_cases hb : len e = b
      · have : e ∈ QB := Finset.mem_filter.mpr ⟨he, hne, hb⟩
        rw [Finset.card_eq_zero.mp hQ] at this
        simp at this
      · have : e ∈ RC := Finset.mem_filter.mpr ⟨he, hne, hb⟩
        rw [Finset.card_eq_zero.mp hR] at this
        simp at this

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- **An `a` edge is opposite the `α` corner**, when `a` differs from `b` and `c`. -/
theorem a_edge_opp_alpha (hab : dist (D.model.pts 1) (D.model.pts 2) ≠
      dist (D.model.pts 2) (D.model.pts 0))
    (hac : dist (D.model.pts 1) (D.model.pts 2) ≠ dist (D.model.pts 0) (D.model.pts 1))
    (i : Fin N) (k : Fin 3)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) =
      dist (D.model.pts 1) (D.model.pts 2)) :
    (D.tile i).localAngle ((D.tile i).pts (k + 2)) = tileα D := by
  obtain ⟨σ, hang, hd⟩ := corner_perm_dist (D.tiles_congruent i)
  rw [Tri.localAngle_vertex, ← hang, model_corner]
  rw [hd] at hlen
  have h1 : σ (k + 2) ≠ σ k := σ.injective.ne (by fin_cases k <;> decide)
  have h2 : σ (k + 2) ≠ σ (k + 1) := σ.injective.ne (by fin_cases k <;> decide)
  have h3 : σ k ≠ σ (k + 1) := σ.injective.ne (by fin_cases k <;> decide)
  generalize σ (k + 2) = w at h1 h2 ⊢
  generalize σ (k + 1) = v at h2 h3 hlen
  generalize σ k = u at h1 h3 hlen
  fin_cases u <;> fin_cases v <;> fin_cases w <;> simp at h1 h2 h3 hlen ⊢ <;>
    first
    | exact absurd hlen.symm hac | exact absurd hlen hac
    | exact absurd hlen.symm hab | exact absurd hlen hab
    | (rw [dist_comm] at hlen; exact absurd hlen.symm hac)
    | (rw [dist_comm] at hlen; exact absurd hlen hac)
    | (rw [dist_comm] at hlen; exact absurd hlen.symm hab)
    | (rw [dist_comm] at hlen; exact absurd hlen hab)

/-- Pythagoras for the tile. -/
theorem right_pyth (hright : tileγ D = Real.pi / 2) :
    dist (D.model.pts 0) (D.model.pts 1) ^ 2 =
      dist (D.model.pts 1) (D.model.pts 2) ^ 2 + dist (D.model.pts 2) (D.model.pts 0) ^ 2 := by
  have h1 : ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = Real.pi / 2 := hright
  have := law_cos (D.model.pts 0) (D.model.pts 2) (D.model.pts 1)
  rw [h1, Real.cos_pi_div_two, dist_comm (D.model.pts 0) (D.model.pts 2)] at this
  linear_combination this

open Classical in
/-- **The tiles at the apex.** If both equal sides consist of `a` edges and `α ≠ β`, then
`2α = m β` for some `m ≥ 2`. -/
theorem corner_B (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D)
    (hαβ : tileα D ≠ tileβ D) {part0 part1 : Finset (Fin N × Fin 3)}
    (hcov0 : (⋃ e ∈ part0, (D.tile e.1).edge e.2) = segment ℝ (D.target.pts 0) (D.target.pts 1))
    (hcov1 : (⋃ e ∈ part1, (D.tile e.1).edge e.2) = segment ℝ (D.target.pts 1) (D.target.pts 2))
    (ha0 : ∀ e ∈ part0, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      dist (D.model.pts 1) (D.model.pts 2))
    (ha1 : ∀ e ∈ part1, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      dist (D.model.pts 1) (D.model.pts 2)) :
    ∃ m : ℕ, 2 ≤ m ∧ 2 * tileα D = m * tileβ D := by
  have hsep := anglesSep_right' D hright hαβ
  have hβ := right_beta D hright
  have hα0 := tileα_pos D
  have hβ0 := tileβ_pos D
  set B := D.target.pts 1
  -- The legs and the hypotenuse.
  have hab : dist (D.model.pts 1) (D.model.pts 2) ≠ dist (D.model.pts 2) (D.model.pts 0) :=
    fun h => hαβ (legs_eq_iff D hright h)
  have hpos : 0 < dist (D.model.pts 2) (D.model.pts 0) :=
    dist_pos.mpr fun e => by have := D.model.indep.injective e; exact absurd this (by decide)
  have hac : dist (D.model.pts 1) (D.model.pts 2) ≠ dist (D.model.pts 0) (D.model.pts 1) := by
    intro h
    have := right_pyth D hright
    rw [← h] at this
    nlinarith
  have hab' : dist (D.model.pts 1) (D.model.pts 2) = dist (D.model.pts 2) (D.model.pts 0) →
      tileα D = tileβ D := fun h => absurd h hab
  -- An edge of each equal side ends at `B`, and its tile has `β` or `π/2` there.
  have hedge : ∀ (part : Finset (Fin N × Fin 3)) (P Q : Plane),
      (⋃ e ∈ part, (D.tile e.1).edge e.2) = segment ℝ P Q → (B = P ∨ B = Q) →
      (∀ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
        dist (D.model.pts 1) (D.model.pts 2)) →
      ∃ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ P Q ∧
        ((D.tile e.1).pts e.2 = B ∨ (D.tile e.1).pts (e.2 + 1) = B) ∧
        ((D.tile e.1).localAngle B = tileβ D ∨ (D.tile e.1).localAngle B = tileγ D) := by
    intro part P Q hcov hB hlen
    have hBs : B ∈ segment ℝ P Q := by
      rcases hB with h | h
      · rw [h]; exact left_mem_segment _ _ _
      · rw [h]; exact right_mem_segment _ _ _
    rw [← hcov] at hBs
    obtain ⟨e, he, hBe⟩ := Set.mem_iUnion₂.mp hBs
    have hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ P Q := by
      rw [← hcov]; intro z hz; exact Set.mem_iUnion₂.mpr ⟨e, he, hz⟩
    have hu := hsub (left_mem_segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
    have hv := hsub (right_mem_segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
    have hend : (D.tile e.1).pts e.2 = B ∨ (D.tile e.1).pts (e.2 + 1) = B := by
      rcases hB with h | h
      · rw [← h] at hu hv
        rcases eq_endpoint_of_mem_segment hu hv hBe with h' | h'
        · exact Or.inl h'.symm
        · exact Or.inr h'.symm
      · rw [segment_symm] at hu hv
        rw [← h] at hu hv
        rcases eq_endpoint_of_mem_segment hu hv hBe with h' | h'
        · exact Or.inl h'.symm
        · exact Or.inr h'.symm
    refine ⟨e, he, hsub, hend, ?_⟩
    rcases hend with h | h
    · rw [← h]; exact a_edge_end_angles D hab' hac e.1 e.2 (hlen e he) e.2 (Or.inl rfl)
    · rw [← h]; exact a_edge_end_angles D hab' hac e.1 e.2 (hlen e he) (e.2 + 1) (Or.inr rfl)
  obtain ⟨e0, he0, hs0, hB0, hφ0⟩ := hedge part0 _ _ hcov0 (Or.inr rfl) ha0
  obtain ⟨e1, he1, hs1, hB1, hφ1⟩ := hedge part1 _ _ hcov1 (Or.inl rfl) ha1
  -- The two tiles are different.
  have hdiff : e0.1 ≠ e1.1 := by
    intro hsame
    have hα0' := a_edge_opp_alpha D hab hac e0.1 e0.2 (ha0 e0 he0)
    have hα1' := a_edge_opp_alpha D hab hac e1.1 e1.2 (ha1 e1 he1)
    rw [← hsame] at hα1'
    have hcnt := (tile_angle_count_sep D hsep e0.1).1
    simp only [← Tri.localAngle_vertex] at hcnt
    have hk : e0.2 + 2 = e1.2 + 2 :=
      Finset.card_le_one.mp hcnt.le _ (by simp [hα0']) _ (by simp [hα1'])
    have hk' : e0.2 = e1.2 := by simpa using hk
    have he : e0 = e1 := Prod.ext hsame hk'
    rw [← he] at hs1
    have m1 : ∀ x, x ∈ (D.tile e0.1).edge e0.2 → x = B := by
      intro x hx
      have h1 := hs1 hx
      have h0 := hs0 hx
      exact sides_meet D.target 1 h1 (by simpa using h0)
    exact tri_pts_succ_ne _ e0.2 ((m1 _ (left_mem_segment _ _ _)).trans
      (m1 _ (right_mem_segment _ _ _)).symm)
  -- The angle at `B` is `2α`.
  have hloc : D.target.localAngle B = 2 * tileα D := by
    rw [Tri.localAngle_vertex]
    have hsum := cornerAngle_sum D.target
    have e1 : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = tileβ D := by
      rw [cornerAngle, angle_comm]; exact hC
    have e0 : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D := hA
    show cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = _
    linarith
  -- Counting the angles at `B`.
  obtain ⟨hv0, hinj⟩ := hsep
  have hf : ∀ i, (∃ j, (D.tile i).localAngle B =
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] j) ∨ (D.tile i).localAngle B = 0 := by
    intro i
    rcases localAngle_mem D B i with h | h | h | h | h | h
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · exact Or.inl ⟨2, h⟩
    · exact Or.inl ⟨3, h⟩
    · exact Or.inl ⟨4, h⟩
    · exact Or.inr h
  have hcount := sum_eq_counts (fun i => (D.tile i).localAngle B) _ hv0 hinj hf
  rw [D.toDissection.sum_localAngle_eq B, Fin.sum_univ_five, hloc] at hcount
  have hcount' : (angleCount D B (tileα D) : ℝ) * tileα D
      + (angleCount D B (tileβ D) : ℝ) * tileβ D + (angleCount D B (tileγ D) : ℝ) * tileγ D
      + (angleCount D B Real.pi : ℝ) * Real.pi
      + (angleCount D B (2 * Real.pi) : ℝ) * (2 * Real.pi) = 2 * tileα D := hcount.symm
  set nα := angleCount D B (tileα D)
  set nβ := angleCount D B (tileβ D)
  set nγ := angleCount D B (tileγ D)
  set nπ := angleCount D B Real.pi
  set n2 := angleCount D B (2 * Real.pi)
  rw [hright] at hcount'
  have key : ((nα + nγ + 2 * nπ + 4 * n2 : ℕ) : ℝ) * tileα D
      + ((nβ + nγ + 2 * nπ + 4 * n2 : ℕ) : ℝ) * tileβ D = 2 * tileα D := by
    push_cast
    have hpi : Real.pi = 2 * tileα D + 2 * tileβ D := by linarith
    rw [hpi] at hcount'
    linarith
  have hB1 : 1 ≤ nβ + nγ := by
    rcases hφ0 with h | h
    · have := angleCount_pos D h; omega
    · have := angleCount_pos D h; omega
  -- `(nα + nγ + 2nπ + 4n₂ - 2) α + (nβ + nγ + 2nπ + 4n₂) β = 0` with the second coefficient
  -- positive: the first is `-1` or `-2`.
  have hlt : nα + nγ + 2 * nπ + 4 * n2 < 2 := by
    by_contra h
    push Not at h
    have h1 : (2 : ℝ) ≤ ((nα + nγ + 2 * nπ + 4 * n2 : ℕ) : ℝ) := by exact_mod_cast h
    have h2 : (1 : ℝ) ≤ ((nβ + nγ + 2 * nπ + 4 * n2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    nlinarith
  rcases Nat.lt_succ_iff.mp hlt |>.lt_or_eq with h0 | h1
  · -- No `α`, `π/2`, `π`, `2π` at `B`: `2α = nβ β`, and both edge tiles have `β`.
    have hz : nα = 0 ∧ nγ = 0 ∧ nπ = 0 ∧ n2 = 0 := by omega
    obtain ⟨h1, h2, h3, h4⟩ := hz
    have hb0 : (D.tile e0.1).localAngle B = tileβ D := by
      rcases hφ0 with h | h
      · exact h
      · have := angleCount_pos D h; omega
    have hb1 : (D.tile e1.1).localAngle B = tileβ D := by
      rcases hφ1 with h | h
      · exact h
      · have := angleCount_pos D h; omega
    have h2le : 2 ≤ nβ := by
      have : ({e0.1, e1.1} : Finset (Fin N)) ⊆
          Finset.univ.filter fun i => (D.tile i).localAngle B = tileβ D := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [hb0, hb1]
      have := Finset.card_le_card this
      rw [Finset.card_pair hdiff] at this
      exact this
    refine ⟨nβ, h2le, ?_⟩
    rw [h1, h2, h3, h4] at key
    push_cast at key
    linarith
  · -- One `α` or `π/2` at `B`: `α = (nβ + nγ) β`.
    have hz : nπ = 0 ∧ n2 = 0 ∧ nα + nγ = 1 := by omega
    refine ⟨2 * (nβ + nγ), by omega, ?_⟩
    obtain ⟨h3, h4, h5⟩ := hz
    have : ((nα + nγ + 2 * nπ + 4 * n2 : ℕ) : ℝ) = 1 := by rw [h3, h4]; exact_mod_cast h5
    rw [this, h3, h4] at key
    push_cast at key ⊢
    linarith

/-- `cos (π/5) = (1 + √5)/4` is not `λ/p` with `λ² = N/2`: else `√5` would be rational. -/
theorem sqrt5_of_cos {l : ℝ} {N P : ℕ} (hP : (P : ℝ) ≠ 0) (hl : l ^ 2 = (N : ℝ) / 2)
    (h : (1 + Real.sqrt 5) / 4 = l / P) : Real.sqrt 5 = ((4 * N / P ^ 2 - 3 : ℚ) : ℝ) := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h2 : ((1 + Real.sqrt 5) / 4) ^ 2 = l ^ 2 / (P : ℝ) ^ 2 := by rw [h, div_pow]
  rw [hl] at h2
  have h3 : (1 + Real.sqrt 5) ^ 2 = 8 * N / (P : ℝ) ^ 2 := by
    field_simp at h2 ⊢; linarith
  have h4 : (1 + Real.sqrt 5) ^ 2 = 6 + 2 * Real.sqrt 5 := by
    have : (1 + Real.sqrt 5) ^ 2 = 1 + 2 * Real.sqrt 5 + Real.sqrt 5 ^ 2 := by ring
    rw [this, hsq]; ring
  push_cast
  have h5 : 4 * (N : ℝ) / (P : ℝ) ^ 2 = (8 * N / (P : ℝ) ^ 2) / 2 := by ring
  rw [h5, ← h3, h4]
  ring

/-- **Lemma `lemma:isosceleshelper2`.** Let the isosceles triangle `ABC` with base angles `β` (at
`A` and `C`) be `N`-tiled by a tile with angles `(α, β, π/2)` and sides `(a, b, c)`. If
`β ≠ π/6` and `λ = √(N/2)` is irrational, then `a/c` and `b/c` belong to `ℚ(λ)`. -/
theorem isosceleshelper2 (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D)
    (hβ6 : tileβ D ≠ Real.pi / 6) (hirrl : ¬ ∃ q : ℚ, Real.sqrt ((N : ℝ) / 2) = q) :
    InQ (Real.sqrt ((N : ℝ) / 2))
        (dist (D.model.pts 1) (D.model.pts 2) / dist (D.model.pts 0) (D.model.pts 1)) ∧
      InQ (Real.sqrt ((N : ℝ) / 2))
        (dist (D.model.pts 2) (D.model.pts 0) / dist (D.model.pts 0) (D.model.pts 1)) := by
  set a := dist (D.model.pts 1) (D.model.pts 2) with hadef
  set b := dist (D.model.pts 2) (D.model.pts 0) with hbdef
  set c := dist (D.model.pts 0) (D.model.pts 1) with hcdef
  set l := Real.sqrt ((N : ℝ) / 2) with hldef
  have hl : l ^ 2 = (((N : ℚ) / 2 : ℚ) : ℝ) := by
    rw [hldef, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hc0 : 0 < c := dist_pos.mpr fun e => by
    have := D.model.indep.injective e; exact absurd this (by decide)
  have hl0 : 0 ≤ l := Real.sqrt_nonneg _
  -- The area equation: `|AB| = |BC| = λ c` and `|AC| = 2 λ a`.
  obtain ⟨hXX, hcY, hN⟩ := right_area_core D rfl rfl rfl rfl rfl hright hA hC
  set X := dist (D.target.pts 0) (D.target.pts 1)
  set Y := dist (D.target.pts 2) (D.target.pts 0)
  have hXl : X = l * c := by
    have h1 : X ^ 2 = (l * c) ^ 2 := by
      rw [mul_pow, hl]; push_cast; linarith
    exact (pow_left_inj₀ dist_nonneg (by positivity) two_ne_zero).mp h1
  have hYl : Y = 2 * a * l := by
    have : c * Y = c * (2 * a * l) := by rw [hcY, hXl]; ring
    exact mul_left_cancel₀ hc0.ne' this
  -- The three sides as sums of edges.
  obtain ⟨part0, hcov0, P0, Q0, R0, hs0, hall0⟩ := side_rel D 0
  obtain ⟨part1, hcov1, P1, Q1, R1, hs1, hall1⟩ := side_rel D 1
  obtain ⟨part2, -, P2, Q2, R2, hs2, -⟩ := side_rel D 2
  have i01 : (0 : Fin 3) + 1 = 1 := rfl
  have i12 : (1 : Fin 3) + 1 = 2 := rfl
  have i20 : (2 : Fin 3) + 1 = 0 := rfl
  rw [i01] at hcov0 hs0
  rw [i12] at hcov1 hs1
  rw [i20] at hs2
  have e0 : l = P0 * (a / c) + Q0 * (b / c) + R0 := by
    field_simp; rw [← hXl]; linarith
  have e1 : l = P1 * (a / c) + Q1 * (b / c) + R1 := by
    field_simp; rw [← hXl, ← hXX]; linarith
  have e2 : 2 * (a / c) * l = P2 * (a / c) + Q2 * (b / c) + R2 := by
    field_simp; rw [← hs2.symm.trans hYl]; ring
  rcases cramer hl hirrl e0 e2 with h | ⟨hQ0, hR0, -, -, hP0, hlP⟩
  · exact h
  rcases cramer hl hirrl e1 e2 with h | ⟨hQ1, hR1, -, -, -, -⟩
  · exact h
  have hla : a / c = l / P0 := by
    have hP0' : (P0 : ℝ) ≠ 0 := by exact_mod_cast hP0
    rw [hlP, mul_div_cancel_left₀ _ hP0']
  have hina : InQ l (a / c) := ⟨1 / P0, 0, by rw [hla]; push_cast; ring⟩
  obtain ⟨hab, hbc⟩ := right_trig D hright
  change a = Real.cos (tileβ D) * c at hab
  change b = Real.cos (tileα D) * c at hbc
  by_cases hαβ : tileα D = tileβ D
  · -- Equal legs.
    refine ⟨hina, ?_⟩
    have : b = a := by rw [hab, hbc, hαβ]
    rw [this]; exact hina
  exfalso
  -- The tiles at `B`: `2α = m β` with `m ≥ 2`.
  obtain ⟨m, hm2, hmα⟩ := corner_B D hright hA hC hαβ hcov0 hcov1 (hall0 hQ0 hR0) (hall1 hQ1 hR1)
  have hβ := right_beta D hright
  have hβm : tileβ D = 2 * Real.pi * (1 : ℕ) / ((2 * m + 4 : ℕ) : ℝ) := by
    push_cast
    field_simp
    linarith
  -- `cos β = a/c ∈ ℚ(λ)`: `lemma:euler`.
  have hcos : Real.cos (tileβ D) = a / c := by
    rw [hab]; field_simp
  obtain ⟨P, hP, hPdeg, hProot⟩ := hina.quadratic hl
  rw [← hcos, hβm] at hProot
  have hn := euler (by omega) (Nat.coprime_one_left _) hP hPdeg hProot
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  have hm : m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases hm with rfl | rfl | rfl
  · -- `m = 2`: `α = β`.
    apply hαβ; push_cast at hmα; linarith
  · -- `m = 3`: `β = π/5`, and `cos² (π/5)` is irrational.
    have hβ5 : tileβ D = Real.pi / 5 := by rw [hβm]; push_cast; ring
    rw [hβ5, Real.cos_pi_div_five, hla] at hcos
    have hP0' : (P0 : ℝ) ≠ 0 := by exact_mod_cast hP0
    have hl' : l ^ 2 = (N : ℝ) / 2 := by rw [hl]; push_cast; ring
    have h5 := sqrt5_of_cos hP0' hl' hcos
    have hirr5 := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
    push_cast at hirr5
    exact hirr5 ⟨_, h5.symm⟩
  · -- `m = 4`: `β = π/6`.
    apply hβ6; rw [hβm]; push_cast; ring

end TriangleTiling

