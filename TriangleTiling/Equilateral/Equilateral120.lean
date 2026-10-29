/-
"Possible values of N in tilings with commensurable angles", from Section 9 of M. Beeson,
*Tilings of an isosceles triangle*.

Lean names follow the TeX labels: `lemma:equilateral120` is `equilateral120`.

Conventions: target `ABC = target.pts 0, 1, 2`; model tile with angles at `model.pts 0, 1, 2`.
-/
import TriangleTiling.Isosceles.NotSquarefree
import Mathlib.NumberTheory.Real.Irrational

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

/-- **Lemma `lemma:equilateral120`.** If an equilateral triangle is `N`-tiled by a tile with
angles `(π/6, π/6, 2π/3)`, then `N` is three times a square.

The proof is the paper's. With legs `L` and base `√3 L`, the area gives `|AB|² = N L²`, and
`|AB| = (p + q√3) L` where `AB` carries `p` legs and `q` bases; so `N = p² + 3q² + 2pq√3` and
`pq = 0`. If `q = 0`, each tile on `AB` has its `2π/3` angle at an endpoint of its edge strictly
inside `AB` (the corners have angle `π/3`), at most one per point (as `4π/3 > π`); but `p` edges
meet at only `p - 1` points inside `AB`. Hence `p = 0` and `N = 3q²`. -/
theorem equilateral120 {N : ℕ} (D : CongruentDissection N)
    (hM0 : ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = Real.pi / 6)
    (hM1 : ∠ (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = Real.pi / 6)
    (hT0 : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = Real.pi / 3)
    (hT1 : ∠ (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = Real.pi / 3) :
    ∃ q : ℕ, N = 3 * q ^ 2 := by
  classical
  set M := D.model.pts with hMdef
  set T := D.target.pts with hTdef
  have hpi := Real.pi_pos
  -- The tile: angle `2π/3` at `M 2`, legs `L`, base `√3 L`.
  have hM2 : ∠ (M 0) (M 2) (M 1) = 2 * Real.pi / 3 := by
    have h := cornerAngle_sum D.model
    have e0 : cornerAngle (M 1) (M 0) (M 2) = Real.pi / 6 := hM0
    have e1 : cornerAngle (M 2) (M 1) (M 0) = Real.pi / 6 := hM1
    have e2 : cornerAngle (M 0) (M 2) (M 1) = ∠ (M 0) (M 2) (M 1) := rfl
    linarith
  set L := dist (M 2) (M 0) with hLdef
  have hleg : dist (M 1) (M 2) = L := by
    have := dist_eq_of_angle_eq_angle_of_angle_ne_pi (p₁ := M 2) (p₂ := M 0) (p₃ := M 1)
      (by rw [angle_comm (M 2) (M 0) (M 1), hM0, hM1])
      (by rw [hM2]; intro h; linarith)
    rw [dist_comm]; exact this.symm
  have hL0 : 0 < L := dist_pos.mpr (D.model.indep.injective.ne (by decide))
  have hbase2 : dist (M 0) (M 1) ^ 2 = 3 * L ^ 2 := by
    have := law_cos (M 0) (M 2) (M 1)
    have hcos : Real.cos (∠ (M 0) (M 2) (M 1)) = -1 / 2 := by
      rw [hM2, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
        Real.cos_pi_div_three]; ring
    rw [hcos, dist_comm (M 0) (M 2), ← hLdef, hleg] at this
    linear_combination this
  set s := Real.sqrt 3 with hs
  have hs2 : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs2; norm_num at hs2
  have hbase : dist (M 0) (M 1) = s * L := by
    have h1 : dist (M 0) (M 1) ^ 2 = (s * L) ^ 2 := by rw [hbase2, mul_pow, hs2]
    exact (sq_eq_sq₀ dist_nonneg (by positivity)).mp h1
  -- The target is equilateral with side `X`.
  have hT2 : ∠ (T 0) (T 2) (T 1) = Real.pi / 3 := by
    have h := cornerAngle_sum D.target
    have e0 : cornerAngle (T 1) (T 0) (T 2) = Real.pi / 3 := hT0
    have e1 : cornerAngle (T 2) (T 1) (T 0) = Real.pi / 3 := hT1
    have e2 : cornerAngle (T 0) (T 2) (T 1) = ∠ (T 0) (T 2) (T 1) := rfl
    linarith
  set X := dist (T 0) (T 1) with hXdef
  have hX12 : dist (T 1) (T 2) = X := by
    have := dist_eq_of_angle_eq_angle_of_angle_ne_pi (p₁ := T 1) (p₂ := T 0) (p₃ := T 2)
      (by rw [hT0, angle_comm, hT2]) (by rw [angle_comm, hT1]; intro h; linarith)
    rw [← this, dist_comm]
  have hX20 : dist (T 2) (T 0) = X := by
    have := dist_eq_of_angle_eq_angle_of_angle_ne_pi (p₁ := T 2) (p₂ := T 0) (p₃ := T 1)
      (by rw [angle_comm (T 2) (T 0) (T 1), hT0, hT1]) (by rw [hT2]; intro h; linarith)
    rw [this, dist_comm, hX12]
  have hX0 : 0 < X := dist_pos.mpr (D.target.indep.injective.ne (by decide))
  -- The area: `X² = N L²`.
  have hXN : X ^ 2 = N * L ^ 2 := by
    have hH := area_heron D
    rw [hleg, ← hLdef, hX12, hX20, ← hXdef] at hH
    have hH1 : heron16 L L (dist (M 0) (M 1)) = 3 * L ^ 4 := by
      unfold heron16
      rw [show dist (M 0) (M 1) ^ 4 = (dist (M 0) (M 1) ^ 2) ^ 2 by ring, hbase2]; ring
    have hH2 : heron16 X X X = 3 * X ^ 4 := by unfold heron16; ring
    rw [hH1, hH2] at hH
    have h1 : (X ^ 2 - N * L ^ 2) * (X ^ 2 + N * L ^ 2) = 0 := by linear_combination -hH / 3
    have h2 : 0 < X ^ 2 + N * L ^ 2 := by positivity
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right h2.ne')
  -- The side `AB` as a chain of `p` legs and `q` bases.
  obtain ⟨part, hcov, hdisj, hsum⟩ := D.toDissection.side_walk 0
  have h01 : (0 : Fin 3) + 1 = 1 := rfl
  rw [h01] at hcov hsum
  set len : Fin N × Fin 3 → ℝ := fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
  have hlen : ∀ e, len e = L ∨ len e = s * L := by
    intro e
    rcases edge_len_mem D e.1 e.2 with h | h | h
    · exact Or.inl (h.trans hleg)
    · exact Or.inl h
    · exact Or.inr (h.trans hbase)
  have hLsL : L ≠ s * L := by
    intro h; apply hs1; field_simp at h; linarith
  set p := (part.filter fun e => len e = L).card
  set q := (part.filter fun e => len e = s * L).card
  have hXpq : X = (p + s * q) * L := by
    have hpt : ∀ e ∈ part, len e = (if len e = L then L else 0) + (if len e = s * L then s * L else 0) := by
      intro e _
      rcases hlen e with h | h
      · rw [if_pos h, if_neg (h ▸ hLsL), h]; ring
      · rw [if_neg (h ▸ hLsL.symm), if_pos h, h]; ring
    rw [hXdef, ← hsum]
    show ∑ e ∈ part, len e = _
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
      Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    ring
  -- `N = p² + 3q² + 2pq√3`, so `pq = 0`.
  have hN : (N : ℝ) = p ^ 2 + 3 * q ^ 2 + 2 * p * q * s := by
    have : (N : ℝ) * L ^ 2 = (p ^ 2 + 3 * q ^ 2 + 2 * p * q * s) * L ^ 2 := by
      rw [← hXN, hXpq]; linear_combination (q : ℝ) ^ 2 * L ^ 2 * hs2
    exact mul_right_cancel₀ (by positivity) this
  have hpq : p = 0 ∨ q = 0 := by
    by_contra h
    push Not at h
    have hirr : Irrational s := by simpa using Nat.prime_three.irrational_sqrt
    apply hirr.ne_rat (((N : ℚ) - p ^ 2 - 3 * q ^ 2) / (2 * p * q))
    have hp : (p : ℝ) ≠ 0 := by exact_mod_cast h.1
    have hq : (q : ℝ) ≠ 0 := by exact_mod_cast h.2
    push_cast
    field_simp
    linarith
  rcases hpq with hp | hq
  · -- `p = 0`: `N = 3q²`.
    refine ⟨q, ?_⟩
    rw [hp] at hN
    push_cast at hN
    exact_mod_cast (by linarith : (N : ℝ) = 3 * (q : ℝ) ^ 2)
  · -- `q = 0`: impossible, by the side pigeonhole on the `2π/3` angles.
    exfalso
    have hq' : ∀ e ∈ part, len e = L := by
      intro e he
      rcases hlen e with h | h
      · exact h
      · have : e ∈ part.filter fun e => len e = s * L := Finset.mem_filter.mpr ⟨he, h⟩
        rw [Finset.card_eq_zero.mp hq] at this
        simp at this
    set θ := 2 * Real.pi / 3
    -- The local angles at points of `AB`: `π/3` at `A, B`, `π` inside.
    have hloc : ∀ P ∈ segment ℝ (T 0) (T 1), D.target.localAngle P ≤ Real.pi := by
      intro P hP
      by_cases hv : P ∈ Set.range T
      · obtain ⟨k, rfl⟩ := hv
        rw [Tri.localAngle_vertex]
        have hall : ∀ k : Fin 3, cornerAngle (T (k + 1)) (T k) (T (k + 2)) = Real.pi / 3 := by
          intro k; fin_cases k
          · exact hT0
          · exact hT1
          · exact hT2
        rw [hall k]; linarith
      · rw [D.target.localAngle_frontier (tri_side_subset_frontier D.target 0 hP) hv]
    have hnn : ∀ (P : Plane) (i : Fin N), 0 ≤ (D.tile i).localAngle P :=
      fun P i => (D.tile i).localAngle_nonneg P
    have hle : ∀ (P : Plane) (i : Fin N), (D.tile i).localAngle P ≤ D.target.localAngle P := by
      intro P i
      rw [← D.toDissection.sum_localAngle_eq P]
      exact Finset.single_le_sum (fun j _ => hnn P j) (Finset.mem_univ i)
    have hcornerAB : ∀ k : Fin 3, ∀ i, (D.tile i).localAngle (T k) ≠ θ := by
      intro k i h
      have h1 := hle (T k) i
      rw [h, Tri.localAngle_vertex] at h1
      have hall : cornerAngle (T (k + 1)) (T k) (T (k + 2)) = Real.pi / 3 := by
        fin_cases k
        · exact hT0
        · exact hT1
        · exact hT2
      rw [hall] at h1
      simp only [θ] at h1
      linarith
    refine side_pigeonhole D θ 0 part hcov hdisj ?_ (fun e _ _ => hcornerAB 0 e.1)
      (fun e _ _ => hcornerAB 1 e.1) ?_
    · -- Each tile on `AB` has its `2π/3` corner at an endpoint of its edge.
      intro e he
      obtain ⟨k, hk⟩ := congruent_corner_angles (D.tiles_congruent e.1) 2
      have hkθ : (D.tile e.1).localAngle ((D.tile e.1).pts k) = θ := by
        rw [Tri.localAngle_vertex, ← hk]; exact hM2
      have hk2 : k ≠ e.2 + 2 := by
        rintro rfl
        obtain ⟨j, hj, hd⟩ := congruent_corner_opp (D.tiles_congruent e.1) (e.2 + 2)
        rw [← hk] at hj
        have hj2 : j = 2 := by
          fin_cases j
          · have hj' : cornerAngle (M 0) (M 2) (M 1) = cornerAngle (M 1) (M 0) (M 2) := hj
            have e0 : cornerAngle (M 1) (M 0) (M 2) = Real.pi / 6 := hM0
            have h2 : cornerAngle (M 0) (M 2) (M 1) = 2 * Real.pi / 3 := hM2
            exfalso; rw [h2, e0] at hj'; linarith
          · have hj' : cornerAngle (M 0) (M 2) (M 1) = cornerAngle (M 2) (M 1) (M 0) := hj
            have e1 : cornerAngle (M 2) (M 1) (M 0) = Real.pi / 6 := hM1
            have h2 : cornerAngle (M 0) (M 2) (M 1) = 2 * Real.pi / 3 := hM2
            exfalso; rw [h2, e1] at hj'; linarith
          · rfl
        subst hj2
        rw [fin3_add_two_add_one, fin3_add_two_add_two] at hd
        have h1 : len e = L := hq' e he
        have h2 : len e = dist (M (2 + 1)) (M (2 + 2)) := hd
        have h3 : dist (M (2 + 1)) (M (2 + 2)) = s * L := hbase
        exact hLsL (h1.symm.trans (h2.trans h3))
      have : k = e.2 ∨ k = e.2 + 1 := by
        obtain ⟨_, j⟩ := e
        fin_cases j <;> fin_cases k <;> simp at hk2 ⊢
      rcases this with rfl | rfl
      · exact Or.inl hkθ
      · exact Or.inr hkθ
    · -- At most one tile has angle `2π/3` at a point of `AB`, as `4π/3 > π`.
      intro P hP
      by_contra hc
      push Not at hc
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      have h2 : (D.tile i).localAngle P + (D.tile j).localAngle P ≤ D.target.localAngle P := by
        rw [← D.toDissection.sum_localAngle_eq P]
        have hsub := Finset.sum_le_sum_of_subset_of_nonneg
          (f := fun k => (D.tile k).localAngle P) (Finset.subset_univ {i, j})
          (fun k _ _ => hnn P k)
        rw [Finset.sum_pair hij] at hsub
        exact hsub
      rw [hi, hj] at h2
      have := hloc P hP
      simp only [θ] at h2
      linarith

end TriangleTiling
