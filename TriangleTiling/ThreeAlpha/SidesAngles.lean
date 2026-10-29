/-
Angles of a triangle from its side lengths, and Niven's theorem for the tile, for the
constructions of M. Beeson, *Triangle tiling: the case 3α + 2β = π* (arXiv 1206.2229v4).
-/
import Erdos634.Draft.FluxTurn
import Erdos634.Congruence
import Mathlib.NumberTheory.Niven
import Mathlib.Geometry.Euclidean.Triangle

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry EuclideanGeometry

theorem fin3_succ : ∀ k : Fin 3, k + 1 + 1 = k + 2 ∧ k + 1 + 2 = k ∧ k + 2 + 1 = k ∧
    k + 2 + 2 = k + 1 := by decide

/-- **Law of cosines** at vertex `k`, in terms of the sides opposite the vertices. -/
theorem cos_angleAt (T : Tri) (k : Fin 3) :
    T.oppLen k ^ 2 = T.oppLen (k + 1) ^ 2 + T.oppLen (k + 2) ^ 2 -
      2 * T.oppLen (k + 1) * T.oppLen (k + 2) * Real.cos (T.angleAt k) := by
  obtain ⟨h1, h2, h3, h4⟩ := fin3_succ k
  have := EuclideanGeometry.law_cos (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))
  unfold Tri.oppLen Tri.angleAt cornerAngle
  rw [h1, h2, h3, h4, dist_comm (T.pts k) (T.pts (k + 1))]
  nlinarith [this]

theorem angleAt_mem (T : Tri) (k : Fin 3) : 0 ≤ T.angleAt k ∧ T.angleAt k ≤ Real.pi :=
  ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩

theorem oppLen_pos (T : Tri) (k : Fin 3) : 0 < T.oppLen k :=
  dist_pos.mpr (T.indep.injective.ne (by obtain ⟨h1, -⟩ := fin3_succ k; revert k; decide))

/-- The angle at `k` is the one whose cosine the side lengths give. -/
theorem angleAt_eq_of_cos (T : Tri) (k : Fin 3) {x : ℝ} (hx0 : 0 ≤ x) (hxπ : x ≤ Real.pi)
    (hcos : T.oppLen k ^ 2 = T.oppLen (k + 1) ^ 2 + T.oppLen (k + 2) ^ 2 -
      2 * T.oppLen (k + 1) * T.oppLen (k + 2) * Real.cos x) :
    T.angleAt k = x := by
  have h := cos_angleAt T k
  have hp := mul_pos (oppLen_pos T (k + 1)) (oppLen_pos T (k + 2))
  have hc : Real.cos (T.angleAt k) = Real.cos x := by
    have : 2 * T.oppLen (k + 1) * T.oppLen (k + 2) * (Real.cos (T.angleAt k) - Real.cos x) = 0 := by
      linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · nlinarith
    · linarith
  exact Real.injOn_cos (angleAt_mem T k) ⟨hx0, hxπ⟩ hc

/-- The relabelled triangle has the same sides, relabelled. -/
theorem oppLen_relabel (T : Tri) (ρ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (T.relabel ρ).oppLen k = T.oppLen (ρ k) := by
  unfold Tri.oppLen
  simp only [Tri.relabel_pts]
  have : ∀ ρ : Equiv.Perm (Fin 3), ∀ k, (ρ (k + 1) = ρ k + 1 ∧ ρ (k + 2) = ρ k + 2) ∨
      (ρ (k + 1) = ρ k + 2 ∧ ρ (k + 2) = ρ k + 1) := by decide
  rcases this ρ k with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
  exact dist_comm _ _

theorem angleAt_relabel (T : Tri) (ρ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (T.relabel ρ).angleAt k = T.angleAt (ρ k) := by
  unfold Tri.angleAt cornerAngle
  simp only [Tri.relabel_pts]
  have : ∀ ρ : Equiv.Perm (Fin 3), ∀ k, (ρ (k + 1) = ρ k + 1 ∧ ρ (k + 2) = ρ k + 2) ∨
      (ρ (k + 1) = ρ k + 2 ∧ ρ (k + 2) = ρ k + 1) := by decide
  rcases this ρ k with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
  exact EuclideanGeometry.angle_comm _ _ _

/-- **Niven.** An angle in `(0, π/3)` with rational cosine is not a rational multiple of `π`. -/
theorem irrPi_of_cos_rat {α : ℝ} (h0 : 0 < α) (h3 : α < Real.pi / 3) (hq : ∃ q : ℚ, Real.cos α = q) :
    ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi := by
  intro hr
  have hn := niven hr hq
  have hlt : Real.cos α < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [Real.pi_pos]) h0
  have hgt : 1 / 2 < Real.cos α := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi h0.le (by linarith [Real.pi_pos]) h3
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with h | h | h | h | h <;> rw [h] at hlt hgt <;> linarith

end TriangleTiling.ThreeAlpha
