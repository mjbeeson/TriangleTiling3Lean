/-
`theorem:rationalisosceles` (Section 6 of M. Beeson, *Tilings of an isosceles triangle*).

Let the isosceles triangle `ABC` with base angles `β` (at `A` and `C`) be `N`-tiled by the tile
`(α, β, π/2)`, with `α` a rational multiple of `π`. Then `N` is twice a square; or `N` is a square
and `β = π/4`; or `N` is six times a square and the tile is a 30-60-90 triangle.
-/
import TriangleTiling.RightTile.Helper3

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

/-- If `√(N/2)` is rational, then `N` is twice a square. -/
theorem two_sq_of_sqrt_rat {N : ℕ} (h : ∃ q : ℚ, Real.sqrt ((N : ℝ) / 2) = q) :
    ∃ m : ℕ, N = 2 * m ^ 2 := by
  obtain ⟨q, hq⟩ := h
  have hsq : ¬ Irrational (Real.sqrt ((2 * N : ℕ) : ℝ)) := by
    intro hi
    apply hi
    refine ⟨2 * q, ?_⟩
    rw [show ((2 * N : ℕ) : ℝ) = (2 * Real.sqrt ((N : ℝ) / 2)) ^ 2 by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; push_cast; ring,
      Real.sqrt_sq (by positivity), hq]
    push_cast; ring
  rw [irrational_sqrt_natCast_iff, not_not] at hsq
  obtain ⟨m, hm⟩ := hsq
  have h2 : 2 ∣ m := by
    have : 2 ∣ m * m := ⟨N, hm.symm⟩
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp this with h | h <;> exact h
  obtain ⟨k, rfl⟩ := h2
  exact ⟨k, by ring_nf at hm; linarith⟩

/-- In `ℚ(s)`, `s² = d` with `s` irrational: if `(U + V s)²` is rational, then `U V = 0`. -/
theorem quad_split {s : ℝ} {d : ℕ} (hs : s ^ 2 = d) (hirr : Irrational s) {U V M : ℚ}
    (h : ((U : ℝ) + V * s) ^ 2 = M) : U * V = 0 := by
  by_contra hUV
  apply hirr
  have h2 : (2 : ℚ) * U * V ≠ 0 := by rw [mul_assoc]; exact mul_ne_zero two_ne_zero hUV
  refine ⟨(M - U ^ 2 - V ^ 2 * d) / (2 * U * V), ?_⟩
  have h2' : (2 : ℝ) * U * V ≠ 0 := by exact_mod_cast h2
  push_cast
  rw [div_eq_iff h2']
  linear_combination -h + (V : ℝ) ^ 2 * hs

/-- If `2 λ = m √2 + n` with `λ = √(N/2)` irrational, then `N = m²`. -/
theorem sq_of_sqrt2 {N m n : ℕ} {l : ℝ} (hl : l ^ 2 = (N : ℝ) / 2) (hirr : ¬ ∃ q : ℚ, l = q)
    (h : 2 * l = m * Real.sqrt 2 + n) : N = m ^ 2 := by
  have hs : Real.sqrt 2 ^ 2 = ((2 : ℕ) : ℝ) := by rw [Real.sq_sqrt (by norm_num)]; norm_num
  have hsq : (((n : ℚ) : ℝ) + ((m : ℚ) : ℝ) * Real.sqrt 2) ^ 2 = ((2 * N : ℚ) : ℝ) := by
    push_cast; rw [add_comm, ← h]; linear_combination 4 * hl
  have h0 := quad_split hs irrational_sqrt_two hsq
  rcases mul_eq_zero.mp h0 with hn | hm
  · have hn : n = 0 := by exact_mod_cast hn
    subst hn
    simp only [Nat.cast_zero, Rat.cast_zero, zero_add] at hsq
    have : ((N : ℝ)) = (m : ℝ) ^ 2 := by
      rw [mul_pow, hs] at hsq; push_cast at hsq; linarith
    exact_mod_cast this
  · have hm : m = 0 := by exact_mod_cast hm
    subst hm
    simp only [Nat.cast_zero, zero_mul, zero_add] at h
    exact absurd ⟨n / 2, by push_cast; linarith⟩ hirr

/-- If `2 λ = m √3 + n` with `λ = √(N/2)` irrational, then `N` is six times a square. -/
theorem six_sq_of_sqrt3 {N m n : ℕ} {l : ℝ} (hl : l ^ 2 = (N : ℝ) / 2) (hirr : ¬ ∃ q : ℚ, l = q)
    (h : 2 * l = m * Real.sqrt 3 + n) : ∃ k : ℕ, N = 6 * k ^ 2 := by
  have hs : Real.sqrt 3 ^ 2 = ((3 : ℕ) : ℝ) := by rw [Real.sq_sqrt (by norm_num)]; norm_num
  have hsq : (((n : ℚ) : ℝ) + ((m : ℚ) : ℝ) * Real.sqrt 3) ^ 2 = ((2 * N : ℚ) : ℝ) := by
    push_cast; rw [add_comm, ← h]; linear_combination 4 * hl
  have hirr3 : Irrational (Real.sqrt 3) := by
    have := Nat.Prime.irrational_sqrt (show Nat.Prime 3 by norm_num)
    exact_mod_cast this
  have h0 := quad_split hs hirr3 hsq
  rcases mul_eq_zero.mp h0 with hn | hm
  · have hn : n = 0 := by exact_mod_cast hn
    subst hn
    simp only [Nat.cast_zero, Rat.cast_zero, zero_add] at hsq
    have hR : (2 * N : ℝ) = 3 * (m : ℝ) ^ 2 := by
      rw [mul_pow, hs] at hsq; push_cast at hsq; linarith
    have hN : 2 * N = 3 * m ^ 2 := by exact_mod_cast hR
    have h2 : 2 ∣ m := by
      have : 2 ∣ 3 * (m * m) := ⟨N, by rw [← sq]; exact hN.symm⟩
      have : 2 ∣ m * m := (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this)
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp this with h | h <;> exact h
    obtain ⟨k, rfl⟩ := h2
    exact ⟨k, by ring_nf at hN; linarith⟩
  · have hm : m = 0 := by exact_mod_cast hm
    subst hm
    simp only [Nat.cast_zero, zero_mul, zero_add] at h
    exact absurd ⟨n / 2, by push_cast; linarith⟩ hirr

/-- **Theorem `theorem:rationalisosceles`.** Let the isosceles triangle `ABC` with base angles `β`
(at `A` and `C`) be `N`-tiled by the tile `(α, β, π/2)`, with `α` a rational multiple of `π`. Then
(i) `N` is twice a square, or (ii) `N` is a square and `β = π/4`, or (iii) `N` is six times a
square and `(β, α)` is `(π/6, π/3)` or `(π/3, π/6)`. -/
theorem rationalisosceles {N : ℕ} (D : CongruentDissection N) (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D)
    (hrat : ∃ r : ℚ, tileα D = r * Real.pi) :
    (∃ m : ℕ, N = 2 * m ^ 2) ∨
    ((∃ m : ℕ, N = m ^ 2) ∧ tileβ D = Real.pi / 4) ∨
    ((∃ m : ℕ, N = 6 * m ^ 2) ∧
      ((tileβ D = Real.pi / 6 ∧ tileα D = Real.pi / 3) ∨
        (tileβ D = Real.pi / 3 ∧ tileα D = Real.pi / 6))) := by
  by_cases hq : ∃ q : ℚ, Real.sqrt ((N : ℝ) / 2) = q
  · exact Or.inl (two_sq_of_sqrt_rat hq)
  set a := dist (D.model.pts 1) (D.model.pts 2) with hadef
  set b := dist (D.model.pts 2) (D.model.pts 0) with hbdef
  set c := dist (D.model.pts 0) (D.model.pts 1) with hcdef
  set l := Real.sqrt ((N : ℝ) / 2) with hldef
  have hlQ : l ^ 2 = (((N : ℚ) / 2 : ℚ) : ℝ) := by
    rw [hldef, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hlR : l ^ 2 = (N : ℝ) / 2 := by rw [hlQ]; push_cast; ring
  have hc0 : 0 < c := dist_pos.mpr fun e => by
    have := D.model.indep.injective e; exact absurd this (by decide)
  have hβ := right_beta D hright
  obtain ⟨hab, -⟩ := right_trig D hright
  change a = Real.cos (tileβ D) * c at hab
  have hbs : b = Real.sin (tileβ D) * c := right_sin D hright
  have hcos : Real.cos (tileβ D) = a / c := by rw [hab]; field_simp
  have hsin : Real.sin (tileβ D) = b / c := by rw [hbs]; field_simp
  -- `β` is `π/6`, `π/4` or `π/3`.
  have hβcases : tileβ D = Real.pi / 6 ∨ tileβ D = Real.pi / 4 ∨ tileβ D = Real.pi / 3 := by
    by_cases h6 : tileβ D = Real.pi / 6
    · exact Or.inl h6
    obtain ⟨hina, hinb⟩ := isosceleshelper2 D hright hA hC h6 hq
    by_contra hne
    push Not at hne
    obtain ⟨r, hr⟩ := hrat
    exact beta_irrational_of_quadratic D hright hlQ (hcos ▸ hina) (hsin ▸ hinb) h6 hne.2.1
      hne.2.2 ⟨1 / 2 - r, by rw [hβ, hr]; push_cast; ring⟩
  -- The area equation: `|AB| = λ c`; so `λ = P cos β + Q sin β + R`.
  obtain ⟨-, -, hN⟩ := right_area_core D rfl rfl rfl rfl rfl hright hA hC
  set X := dist (D.target.pts 0) (D.target.pts 1)
  have hXl : X = l * c := by
    have h1 : X ^ 2 = (l * c) ^ 2 := by
      rw [mul_pow, hlR]; linarith
    exact (pow_left_inj₀ dist_nonneg (by positivity) two_ne_zero).mp h1
  obtain ⟨-, -, P, Q, R, hs0, -⟩ := side_rel D 0
  have i01 : (0 : Fin 3) + 1 = 1 := rfl
  rw [i01] at hs0
  have e0 : l = P * Real.cos (tileβ D) + Q * Real.sin (tileβ D) + R := by
    rw [hcos, hsin]; field_simp; rw [← hXl]; linarith
  rcases hβcases with h | h | h
  · -- `β = π/6`, `α = π/3`: `2 λ = P √3 + (Q + 2R)`.
    rw [h, Real.cos_pi_div_six, Real.sin_pi_div_six] at e0
    have e : 2 * l = (P : ℝ) * Real.sqrt 3 + ((Q + 2 * R : ℕ) : ℝ) := by
      rw [e0]; push_cast; ring
    exact Or.inr (Or.inr ⟨six_sq_of_sqrt3 hlR hq e, Or.inl ⟨h, by linarith⟩⟩)
  · -- `β = π/4`: `2 λ = (P + Q) √2 + 2R`.
    rw [h, Real.cos_pi_div_four, Real.sin_pi_div_four] at e0
    have e : 2 * l = ((P + Q : ℕ) : ℝ) * Real.sqrt 2 + ((2 * R : ℕ) : ℝ) := by
      rw [e0]; push_cast; ring
    exact Or.inr (Or.inl ⟨⟨_, sq_of_sqrt2 hlR hq e⟩, h⟩)
  · -- `β = π/3`, `α = π/6`: `2 λ = Q √3 + (P + 2R)`.
    rw [h, Real.cos_pi_div_three, Real.sin_pi_div_three] at e0
    have e : 2 * l = (Q : ℝ) * Real.sqrt 3 + ((P + 2 * R : ℕ) : ℝ) := by
      rw [e0]; push_cast; ring
    exact Or.inr (Or.inr ⟨six_sq_of_sqrt3 hlR hq e, Or.inr ⟨h, by linarith⟩⟩)

end TriangleTiling
