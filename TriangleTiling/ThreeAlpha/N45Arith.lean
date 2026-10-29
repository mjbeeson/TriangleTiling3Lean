/-
The arithmetic of `theorem:N45` (M. Beeson, *Triangle tiling: the case 3α + 2β = π*, arXiv
1206.2229v4): the tile `(pq, q² - p², q²)`, legs `M(p + q)q`, base `Mp(p + q)`.
-/
import Mathlib

namespace TriangleTiling.ThreeAlpha

/-- If `N(q - p) = M²(q + p)`, a leg `M(p + q)q` contains at least `q` edges `b = q² - p²` and two
edges `c = q²`, and the base `Mp(p + q)` contains two edges `c` among edges `a, b, c`, then
`N ≥ 45`. -/
theorem n45_arith (p q M N : ℕ) (hp : 0 < p) (hpq : p < q) (hM : 0 < M)
    (hN : N * (q - p) = M ^ 2 * (q + p))
    (uL vL wL : ℕ) (hleg : M * (p + q) * q = uL * (p * q) + vL * (q * q - p * p) + wL * (q * q))
    (hvL : q ≤ vL) (hwL : 2 ≤ wL)
    (uB vB wB : ℕ) (hbase : M * p * (p + q) = uB * (p * q) + vB * (q * q - p * p) + wB * (q * q))
    (hwB : 2 ≤ wB) : 45 ≤ N := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨d, rfl⟩ : ∃ d, q = p + d := ⟨q - p, by omega⟩
  have hd : 0 < d := by omega
  have hb : (p + d) * (p + d) - p * p = d * (2 * p + d) := by
    rw [show (p + d) * (p + d) = p * p + d * (2 * p + d) by ring]; omega
  rw [hb] at hleg hbase
  rw [show p + d - p = d by omega, show p + d + p = 2 * p + d by ring] at hN
  -- the leg: `M (2p + d) ≥ d (2p + d) + 2 (p + d)`, so `M ≥ d + 2`
  obtain ⟨X, hX⟩ : ∃ X, X = d * (2 * p + d) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (p + d) * (p + d) := ⟨_, rfl⟩
  rw [← hX, ← hY] at hleg
  rw [← hX, ← hY] at hbase
  have h1 : (X + 2 * (p + d)) * (p + d) ≤ M * (p + (p + d)) * (p + d) := by
    rw [hleg, show (X + 2 * (p + d)) * (p + d) = (p + d) * X + 2 * Y by rw [hY]; ring]
    have e1 := Nat.mul_le_mul_right X hvL
    have e2 := Nat.mul_le_mul_right Y hwL
    have e3 := Nat.zero_le (uL * (p * (p + d)))
    omega
  have h2 : X + 2 * (p + d) ≤ M * (2 * p + d) := by
    have := Nat.le_of_mul_le_mul_right h1 (by omega : 0 < p + d)
    rw [show p + (p + d) = 2 * p + d by ring] at this; exact this
  have hM2 : d + 2 ≤ M := by
    by_contra h; push_neg at h
    have e1 : M * (2 * p + d) ≤ (d + 1) * (2 * p + d) := Nat.mul_le_mul_right _ (by omega)
    have e2 : (d + 1) * (2 * p + d) = X + (2 * p + d) := by rw [hX]; ring
    omega
  -- `44 d ≥ N d = M² (2p + d) ≥ (d + 2)² (2p + d)`, so `d ≤ 3`, `p ≤ 2`, `M ≤ 6`
  have h3 : (d + 2) ^ 2 * (2 * p + d) ≤ 44 * d := by
    calc (d + 2) ^ 2 * (2 * p + d) ≤ M ^ 2 * (2 * p + d) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hM2 2)
      _ = N * d := hN.symm
      _ ≤ 44 * d := Nat.mul_le_mul_right _ (by omega)
  have hd3 : d ≤ 3 := by
    by_contra h; push_neg at h
    have e1 : (d + 2) ^ 2 * 6 ≤ (d + 2) ^ 2 * (2 * p + d) := Nat.mul_le_mul_left _ (by omega)
    have e2 : 4 * d ≤ d * d := Nat.mul_le_mul_right _ (by omega)
    have e3 : (d + 2) ^ 2 = d * d + 4 * d + 4 := by ring
    omega
  have hp2 : p ≤ 2 := by
    interval_cases d <;> (norm_num at h3; omega)
  have hM6 : M ≤ 6 := by
    by_contra h; push_neg at h
    have e1 : 7 ^ 2 * 3 ≤ M ^ 2 * (2 * p + d) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left h 2) (by omega)
    have e2 : N * d ≤ 44 * 3 := Nat.mul_le_mul (by omega) hd3
    omega
  interval_cases p <;> interval_cases d <;> interval_cases M <;>
    first | omega | (subst hX hY; norm_num at hN hbase hleg ⊢; omega)

end TriangleTiling.ThreeAlpha
