/-
`lemma:notprime` (Section 6 of M. Beeson, *Tilings of an isosceles triangle*): if an isosceles
triangle is `N`-tiled by a right triangle and `N > 2`, then `N` is not prime, and `N` is not twice
a prime `p ≡ 3 (mod 4)` unless `N = 6`.
-/
import TriangleTiling.RightTile.Isosceles2

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

/-- A sum of two squares is not `3` modulo `4`. -/
theorem sum_sq_mod_four (x y : ℕ) : (x ^ 2 + y ^ 2) % 4 ≠ 3 := by
  have h : ∀ z : ℕ, z ^ 2 % 4 = 0 ∨ z ^ 2 % 4 = 1 := by
    intro z
    rcases Nat.even_or_odd z with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · left; ring_nf; omega
    · right; ring_nf; omega
  rcases h x with hx | hx <;> rcases h y with hy | hy <;> omega

theorem not_prime_sq (m : ℕ) : ¬ (m ^ 2).Prime := by
  rw [sq]; intro h
  rcases Nat.prime_mul_iff.mp h with ⟨hm, rfl⟩ | ⟨hm, rfl⟩ <;> exact Nat.not_prime_one hm

/-- **The arithmetic of `lemma:notprime`**: the conclusions of `theorem:isosceles2` exclude primes
`N > 2` and `N = 2p` with `p ≡ 3 (mod 4)` prime, `N ≠ 6`. -/
theorem notprime_arith {N : ℕ} (hN2 : 2 < N)
    (h : (∃ m : ℕ, N = m ^ 2) ∨ (∃ m : ℕ, N = 2 * m ^ 2) ∨ (∃ k : ℕ, N = 6 * k ^ 2) ∨
      (Even N ∧ ∃ x y : ℕ, N / 2 = x ^ 2 + y ^ 2)) :
    ¬ N.Prime ∧ ∀ p : ℕ, p.Prime → p % 4 = 3 → N = 2 * p → N = 6 := by
  constructor
  · intro hp
    rcases h with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨k, rfl⟩ | ⟨he, -⟩
    · exact not_prime_sq m hp
    · have := (Nat.prime_mul_iff.mp hp)
      rcases this with ⟨-, h1⟩ | ⟨-, h1⟩
      · simp at h1; subst h1; norm_num at hN2
      · simp at h1
    · have := (Nat.prime_mul_iff.mp hp)
      rcases this with ⟨h6, -⟩ | ⟨-, h1⟩
      · norm_num at h6
      · omega
    · exact (Nat.Prime.even_iff hp).mp he ▸ hN2 |>.false
  · intro p hp hp3 hNp
    subst hNp
    rcases h with ⟨m, hm⟩ | ⟨m, hm⟩ | ⟨k, hk⟩ | ⟨-, x, y, hxy⟩
    · -- `2p = m²`: `2 ∣ m`, so `2 ∣ p`, so `p = 2`.
      exfalso
      have h2 : 2 ∣ m := (Nat.Prime.dvd_mul Nat.prime_two).mp ⟨p, by rw [← sq, ← hm]⟩ |>.elim id id
      obtain ⟨j, rfl⟩ := h2
      have hpj : p = 2 * j ^ 2 := by ring_nf at hm; omega
      rcases Nat.prime_mul_iff.mp (hpj ▸ hp) with ⟨-, hj⟩ | ⟨h2, -⟩
      · rw [hj] at hpj; omega
      · exact not_prime_sq j h2
    · -- `p = m²` is not prime.
      exfalso
      have : p = m ^ 2 := by omega
      exact not_prime_sq m (this ▸ hp)
    · -- `p = 3k²`, so `k = 1`.
      have : p = 3 * k ^ 2 := by omega
      have h1 := Nat.prime_mul_iff.mp (this ▸ hp)
      rcases h1 with ⟨-, hk1⟩ | ⟨h3, -⟩
      · rw [hk1] at this; omega
      · exact absurd h3 (not_prime_sq k)
    · exfalso
      have : (2 * p) / 2 = p := by omega
      rw [this] at hxy
      exact sum_sq_mod_four x y (by omega)

variable {N : ℕ} (D : CongruentDissection N)

/-- **Corollary `lemma:notprime`, with `lemma:baseangles` as a hypothesis** (unconditional:
`notprime`, in `Laczkovich/BaseAngles.lean`). Let the isosceles triangle `ABC` be `N`-tiled by a right
triangle (base angles `α` or `β`, `lemma:baseangles`, a hypothesis here), with `N > 2`. Then `N`
is not prime, and `N` is not twice a prime `p ≡ 3 (mod 4)` unless `N = 6`. -/
theorem notprime_of_baseangles (hright : tileγ D = Real.pi / 2)
    (hbase : (∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D ∧
        ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D) ∨
      (∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D ∧
        ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D))
    (hN2 : 2 < N) :
    ¬ N.Prime ∧ ∀ p : ℕ, p.Prime → p % 4 = 3 → N = 2 * p → N = 6 := by
  apply notprime_arith hN2
  rcases isosceles2_of_baseangles D hright hbase with ⟨h, -⟩ | h | ⟨h, -⟩ | ⟨he, -, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨he, h⟩))

end TriangleTiling
