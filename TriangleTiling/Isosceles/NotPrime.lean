/-
"The non-primality of N", from Section 10 of M. Beeson,
*Tilings of an isosceles triangle*.

Lean names follow the TeX labels: `lemma:notprimehelper` is `notprimehelper`.

Conventions as in `TriangleTiling.Isosceles.AreaEquation`: target `ABC = target.pts 0, 1, 2`
with base `AC`; model tile with angles `α, β, γ` at `model.pts 0, 1, 2` and opposite sides
`a, b, c`.
-/
import TriangleTiling.Isosceles.AreaEquation
import Erdos634.EdgeChain

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

/-- Every edge of every tile has one of the three side lengths of the model tile. -/
theorem edge_len_mem {N : ℕ} (D : CongruentDissection N) (j : Fin N) (k : Fin 3) :
    dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = dist (D.model.pts 1) (D.model.pts 2) ∨
    dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = dist (D.model.pts 2) (D.model.pts 0) ∨
    dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = dist (D.model.pts 0) (D.model.pts 1) := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent j).dist_eq
  rw [hσ]
  have hne : σ k ≠ σ (k + 1) := σ.injective.ne (by fin_cases k <;> decide)
  generalize σ k = u at hne
  generalize σ (k + 1) = v at hne
  fin_cases u <;> fin_cases v <;>
    first
    | exact absurd rfl hne
    | (left; rfl) | (left; exact dist_comm _ _)
    | (right; left; rfl) | (right; left; exact dist_comm _ _)
    | (right; right; rfl) | (right; right; exact dist_comm _ _)

/-- **Lemma `lemma:notprimehelper`.** Let the isosceles triangle `ABC` with base angles `α` be
`N`-tiled by a tile with angles `(α, β, 2α)` and integer sides `(a, b, c)` with no common
factor. Then `N b` is a perfect square; equivalently, `N` and `b` have the same squarefree
part, so the squarefree part of each divides the other. If `N` is squarefree, then
`b = N ℓ²` for some integer `ℓ`.

The paper also assumes that `α` is not a rational multiple of `π`; the proof does not use
it. The proof follows the paper: by the area equations, `|AC|² = N b m²` where
`(a, b, c) = (k², m² - k², km)` (`lemma:luthar`), and `|AC|` is an integer because the base
is made of whole tile edges (Bonfioli's `side_walk_abc`). -/
theorem notprimehelper {N : ℕ} (D : CongruentDissection N) {a b c : ℕ}
    (ha : dist (D.model.pts 1) (D.model.pts 2) = a)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = b)
    (hc : dist (D.model.pts 0) (D.model.pts 1) = c)
    (hcop : Nat.gcd (Nat.gcd a b) c = 1)
    (hγ : ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) =
      2 * ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2)) :
    (∃ s : ℕ, N * b = s ^ 2) ∧ (Squarefree N → ∃ ℓ : ℕ, b = N * ℓ ^ 2) := by
  obtain ⟨-, hYX, hX2⟩ := areaequation_core D ha hb hc rfl rfl hγ hA hC
  set X := dist (D.target.pts 0) (D.target.pts 1)
  -- The base `AC` has integer length `Yn = P a + Q b + R c`.
  have habc : ∀ (j : Fin N) (k : Fin 3),
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = (a : ℝ) ∨
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = (b : ℝ) ∨
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = (c : ℝ) := by
    intro j k; rw [← ha, ← hb, ← hc]; exact edge_len_mem D j k
  obtain ⟨P, Q, R, hPQR, -⟩ := D.toDissection.side_walk_abc 2 a b c habc
  have h20 : (2 : Fin 3) + 1 = 0 := rfl
  rw [h20] at hPQR
  set Yn : ℕ := P * a + Q * b + R * c with hYn
  have hY : dist (D.target.pts 2) (D.target.pts 0) = (Yn : ℝ) := by
    rw [← hPQR, hYn]; push_cast; ring
  rw [hY] at hYX
  -- The tile in ℕ: `c² = a² + ab` and the triangle inequalities, hence `lemma:luthar`.
  have hcab : c ^ 2 = a ^ 2 + a * b := by
    have := (twoalphatiles (tri_indep D.model) ha hb hc).mp hγ
    exact_mod_cast this
  obtain ⟨m1, m2, m3⟩ := strict_triangle_ineqs (tri_indep D.model)
  rw [ha, hb, hc] at m1 m2 m3
  have m1' : a < b + c := by exact_mod_cast m1
  have m2' : b < c + a := by exact_mod_cast m2
  have m3' : c < a + b := by exact_mod_cast m3
  obtain ⟨k, m, -, hkm, -, hak, -, hck⟩ :=
    (luthar a b c).mp ⟨hcop, hcab, m1', by omega, m3'⟩
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at hak; omega
    · exact h
  have hm0 : 0 < m := by omega
  -- `a Y² = N b c²` from `a Y = c X` and `X² = N a b`.
  have ha0 : (0 : ℝ) < a := by have : 0 < a := by rw [hak]; positivity
                               exact_mod_cast this
  have hreal : (a : ℝ) * (Yn : ℝ) ^ 2 = N * b * (c : ℝ) ^ 2 := by
    have h1 : (a : ℝ) * ((a : ℝ) * (Yn : ℝ) ^ 2 - N * b * (c : ℝ) ^ 2) = 0 := by
      linear_combination (a * Yn + c * X) * hYX + c ^ 2 * hX2
    have := (mul_eq_zero.mp h1).resolve_left ha0.ne'
    linarith
  have hnat : k ^ 2 * Yn ^ 2 = k ^ 2 * (N * b * m ^ 2) := by
    have : a * Yn ^ 2 = N * b * c ^ 2 := by exact_mod_cast hreal
    rw [hak, hck] at this
    rw [this]; ring
  have h1 : Yn ^ 2 = N * b * m ^ 2 := Nat.eq_of_mul_eq_mul_left (by positivity) hnat
  -- So `m ∣ Yn`, and `N b = (Yn / m)²`.
  have hmY : m ∣ Yn := (Nat.pow_dvd_pow_iff two_ne_zero).mp ⟨N * b, by rw [h1]; ring⟩
  obtain ⟨t, ht⟩ := hmY
  have hNb : N * b = t ^ 2 := by
    rw [ht] at h1
    have : m ^ 2 * (N * b) = m ^ 2 * t ^ 2 :=
      calc m ^ 2 * (N * b) = N * b * m ^ 2 := by ring
        _ = (m * t) ^ 2 := h1.symm
        _ = m ^ 2 * t ^ 2 := by ring
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) this)
  refine ⟨⟨t, hNb⟩, fun hsq => ?_⟩
  -- If `N` is squarefree, then `N ∣ t² ⟹ N ∣ t`, and `b = N (t / N)²`.
  have hN0 : 0 < N := Nat.pos_of_ne_zero (fun h => by subst h; exact not_squarefree_zero hsq)
  obtain ⟨u, hu⟩ := (hsq.dvd_pow_iff_dvd two_ne_zero).mp ⟨b, hNb.symm⟩
  refine ⟨u, Nat.eq_of_mul_eq_mul_left hN0 ?_⟩
  rw [hNb, hu]; ring

end TriangleTiling
