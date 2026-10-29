/-
`theorem:isosceles2` (Section 6 of M. Beeson, *Tilings of an isosceles triangle*).

Let the isosceles triangle `ABC` (base `AC`) be `N`-tiled by a tile with angles `(α, β, π/2)`.
Then `N` is a square and `α = β = π/4`; or `N` is twice a square; or `N = 6k²` and `β` or `α` is
`π/6`; or `N` is even, and both `N` and `N/2` are sums of two squares.

The paper derives that the base angles are `α` or `β` from Laczkovich's classification
(`lemma:baseangles`); here that is a hypothesis (`isosceles2_of_baseangles`). The theorem without
it, `isosceles2`, is in `Laczkovich/BaseAngles.lean`, where `lemma:baseangles` is proved.
-/
import TriangleTiling.RightTile.Parity
import TriangleTiling.RightTile.RationalIsosceles
import Mathlib.NumberTheory.SumTwoSquares

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

/-! ### Arithmetic -/

/-- A natural number that is a sum of two rational squares is a sum of two squares
(`lemma:rationalsquares`). -/
theorem nat_sum_sq_of_rat {n : ℕ} {u v : ℚ} (h : (n : ℚ) = u ^ 2 + v ^ 2) :
    ∃ x y : ℕ, n = x ^ 2 + y ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, 0, rfl⟩
  set d := u.den * v.den with hd
  have hd0 : 0 < d := Nat.mul_pos u.den_pos v.den_pos
  have hA : (u.num * v.den : ℤ) = u * d := by
    rw [hd]; push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  have hB : (v.num * u.den : ℤ) = v * d := by
    rw [hd]; push_cast
    rw [mul_comm (u.den : ℚ), ← mul_assoc, Rat.mul_den_eq_num]
  have hnd : n * d ^ 2 = (u.num * v.den).natAbs ^ 2 + (v.num * u.den).natAbs ^ 2 := by
    have : ((n * d ^ 2 : ℕ) : ℤ) = (u.num * v.den) ^ 2 + (v.num * u.den) ^ 2 := by
      have hq : ((n * d ^ 2 : ℕ) : ℚ) = ((u.num * v.den : ℤ) : ℚ) ^ 2 + ((v.num * u.den : ℤ) : ℚ) ^ 2 := by
        rw [hA, hB]; push_cast; rw [h]; ring
      exact_mod_cast hq
    have h2 : ((n * d ^ 2 : ℕ) : ℤ) = (((u.num * v.den).natAbs ^ 2 +
        (v.num * u.den).natAbs ^ 2 : ℕ) : ℤ) := by
      rw [this]; push_cast; rw [sq_abs, sq_abs]
    exact_mod_cast h2
  have key := Nat.eq_sq_add_sq_iff.mp ⟨_, _, hnd⟩
  apply Nat.eq_sq_add_sq_iff.mpr
  intro q hq hq3
  have hqn : q ∈ (n * d ^ 2).primeFactors :=
    Nat.primeFactors_mono (dvd_mul_right n _) (by positivity) hq
  have hev := key q hqn hq3
  haveI := Fact.mk (Nat.prime_of_mem_primeFactors hq)
  rw [padicValNat.mul (by omega) (by positivity), padicValNat.pow _ (by omega)] at hev
  obtain ⟨k, hk⟩ := hev
  exact ⟨k - padicValNat q d, by omega⟩

/-- If `g² (p² + q²) N = 2 h²` with `N` odd and `p, q` and `g, h` coprime, then `p, q` are odd. -/
theorem odd_legs {N p q g h : ℕ} (hN : Odd N) (hpq : Nat.Coprime p q) (hgh : Nat.Coprime g h)
    (heq : g ^ 2 * (p ^ 2 + q ^ 2) * N = 2 * h ^ 2) : Odd p ∧ Odd q := by
  by_contra hn
  have hE : Even (g ^ 2 * (p ^ 2 + q ^ 2) * N) := ⟨h ^ 2, by rw [heq]; ring⟩
  rcases Nat.even_mul.mp hE with hE | hE
  swap
  · exact (Nat.not_even_iff_odd.mpr hN) hE
  rcases Nat.even_mul.mp hE with hg | hpq2
  · -- `g` even, then `h` even.
    have hg' : Even g := (Nat.even_pow' two_ne_zero).mp hg
    obtain ⟨g', rfl⟩ := hg'
    have hh : Even (h ^ 2) := ⟨g' ^ 2 * (p ^ 2 + q ^ 2) * N, by ring_nf at heq ⊢; linarith⟩
    have hh' : Even h := (Nat.even_pow' two_ne_zero).mp hh
    have h2 : 2 ∣ Nat.gcd (g' + g') h :=
      Nat.dvd_gcd ⟨g', by ring⟩ (even_iff_two_dvd.mp hh')
    rw [hgh] at h2
    exact absurd h2 (by norm_num)
  · -- `p² + q²` even: `p, q` both even, contradicting coprimality.
    rw [Nat.even_add, Nat.even_pow' two_ne_zero, Nat.even_pow' two_ne_zero] at hpq2
    have hpe : Even p := by
      by_contra hp
      have hq : ¬ Even q := fun hq => hp (hpq2.mpr hq)
      exact hn ⟨Nat.not_even_iff_odd.mp hp, Nat.not_even_iff_odd.mp hq⟩
    have hqe : Even q := hpq2.mp hpe
    have h2 : 2 ∣ Nat.gcd p q := Nat.dvd_gcd (even_iff_two_dvd.mp hpe) (even_iff_two_dvd.mp hqe)
    rw [hpq] at h2
    exact absurd h2 (by norm_num)

/-! ### Relabelling the tile -/

variable {N : ℕ}

/-- The same tiling, with the model tile's vertices relabelled. -/
noncomputable def relabelModel (D : CongruentDissection N) (τ : Equiv.Perm (Fin 3)) :
    CongruentDissection N where
  toDissection := D.toDissection
  model := D.model.relabel τ
  tiles_congruent := fun i => (D.tiles_congruent i).trans (D.model.congruent_relabel τ)

theorem swap_angles (D : CongruentDissection N) :
    tileα (relabelModel D (Equiv.swap 0 1)) = tileβ D ∧
      tileβ (relabelModel D (Equiv.swap 0 1)) = tileα D ∧
      tileγ (relabelModel D (Equiv.swap 0 1)) = tileγ D := by
  have e0 : (relabelModel D (Equiv.swap 0 1)).model.pts 0 = D.model.pts 1 := rfl
  have e1 : (relabelModel D (Equiv.swap 0 1)).model.pts 1 = D.model.pts 0 := rfl
  have e2 : (relabelModel D (Equiv.swap 0 1)).model.pts 2 = D.model.pts 2 := rfl
  simp only [tileα, tileβ, tileγ, e0, e1, e2]
  exact ⟨angle_comm _ _ _, angle_comm _ _ _, angle_comm _ _ _⟩

/-! ### The theorem -/

variable (D : CongruentDissection N)

/-- **`theorem:isosceles2`, with base angles `β`.** -/
theorem isosceles2_beta (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D) :
    ((∃ m : ℕ, N = m ^ 2) ∧ tileα D = Real.pi / 4 ∧ tileβ D = Real.pi / 4) ∨
    (∃ m : ℕ, N = 2 * m ^ 2) ∨
    ((∃ k : ℕ, N = 6 * k ^ 2) ∧ (tileβ D = Real.pi / 6 ∨ tileα D = Real.pi / 6)) ∨
    (Even N ∧ (∃ x y : ℕ, N = x ^ 2 + y ^ 2) ∧ ∃ x y : ℕ, N / 2 = x ^ 2 + y ^ 2) := by
  have hβ := right_beta D hright
  by_cases hrat : ∃ r : ℚ, tileα D = r * Real.pi
  · rcases rationalisosceles D hright hA hC hrat with h | ⟨h, hβ4⟩ | ⟨h, hab⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl ⟨h, by linarith, hβ4⟩
    · refine Or.inr (Or.inr (Or.inl ⟨h, ?_⟩))
      rcases hab with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact Or.inl h1
      · exact Or.inr h2
  by_cases hq : ∃ q : ℚ, Real.sqrt ((N : ℝ) / 2) = q
  · exact Or.inr (Or.inl (two_sq_of_sqrt_rat hq))
  right; right; right
  have hβk : ∀ k : ℕ, tileβ D ≠ Real.pi / k := fun k h =>
    hrat ⟨1 / 2 - 1 / k, by
      push_cast
      rw [show ((1 : ℝ) / 2 - 1 / k) * Real.pi = Real.pi / 2 - Real.pi / k by ring, ← h]
      linarith⟩
  obtain ⟨⟨x, z, hx, hz⟩, hAC, -⟩ := isosceleshelper3 D hright hA hC
    (by exact_mod_cast hβk 6) (by exact_mod_cast hβk 4) (by exact_mod_cast hβk 3) hq
  set a := dist (D.model.pts 1) (D.model.pts 2) with hadef
  set b := dist (D.model.pts 2) (D.model.pts 0) with hbdef
  set c := dist (D.model.pts 0) (D.model.pts 1) with hcdef
  set l := Real.sqrt ((N : ℝ) / 2) with hldef
  have hl2 : l ^ 2 = (N : ℝ) / 2 := by rw [hldef, Real.sq_sqrt (by positivity)]
  have hpos : ∀ i j : Fin 3, i ≠ j → 0 < dist (D.model.pts i) (D.model.pts j) := fun i j hij =>
    dist_pos.mpr fun h => hij (D.model.indep.injective h)
  have ha0 : 0 < a := hpos 1 2 (by decide)
  have hb0 : 0 < b := hpos 2 0 (by decide)
  have hc0 : 0 < c := hpos 0 1 (by decide)
  have hl0 : 0 < l := by
    rcases (Real.sqrt_nonneg ((N : ℝ) / 2)).lt_or_eq with h | h
    · exact h
    · exact absurd ⟨0, by rw [hldef, ← h]; simp⟩ hq
  have hx0 : (0 : ℚ) < x := by
    have : (0 : ℝ) < x * l := hx ▸ div_pos ha0 hc0
    exact_mod_cast pos_of_mul_pos_left this hl0.le
  have hz0 : (0 : ℚ) < z := by
    have : (0 : ℝ) < z * l := hz ▸ div_pos hb0 hc0
    exact_mod_cast pos_of_mul_pos_left this hl0.le
  -- `(x² + z²) N/2 = 1`.
  have hxzR : ((x : ℝ) ^ 2 + (z : ℝ) ^ 2) * ((N : ℝ) / 2) = 1 := by
    have hp := right_pyth D hright
    rw [← hl2]
    have : (a / c) ^ 2 + (b / c) ^ 2 = 1 := by
      field_simp; linarith
    rw [hx, hz] at this
    linear_combination this
  have hxz : (x ^ 2 + z ^ 2) * ((N : ℚ) / 2) = 1 := by
    have : (((x ^ 2 + z ^ 2) * ((N : ℚ) / 2) : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by push_cast; exact hxzR
    exact Rat.cast_injective this
  -- `a : b = p : q` in lowest terms; `x = p s`, `z = q s`.
  set r : ℚ := x / z with hr
  have hr0 : 0 < r := div_pos hx0 hz0
  set p := r.num.natAbs
  set q := r.den
  have hpq : ((p : ℚ) / q) = r := by
    have h1 : (((p : ℤ) : ℚ)) = (r.num : ℚ) := by
      simp only [p, Int.natCast_natAbs, abs_of_pos (Rat.num_pos.mpr hr0)]
    rw [Int.cast_natCast] at h1
    rw [h1]; exact Rat.num_div_den r
  have hcop : Nat.Coprime p q := r.reduced
  have hq0 : (0 : ℚ) < q := by exact_mod_cast r.den_pos
  have hp0 : 0 < p := Int.natAbs_pos.mpr (Rat.num_pos.mpr hr0).ne'
  set s : ℚ := z / q
  have hs0 : 0 < s := div_pos hz0 hq0
  have hxs : x = p * s := by
    have : x = r * z := by rw [hr]; field_simp
    rw [this, ← hpq]; simp only [s]; field_simp
  have hzs : z = q * s := by simp only [s]; field_simp
  clear_value s
  have hratio : a * q = b * p := by
    have ha : a = c * (x * l) := by rw [← hx]; field_simp
    have hb : b = c * (z * l) := by rw [← hz]; field_simp
    rw [ha, hb, hxs, hzs]; push_cast; ring
  have hcirr : ¬ ∃ r' : ℚ, c = r' * a := by
    rintro ⟨r', hr'⟩
    have ha : a = c * (x * l) := by rw [← hx]; field_simp
    have h1 : (r' : ℝ) * x * l = 1 := by
      have : c * 1 = c * (r' * x * l) := by rw [mul_one]; nth_rewrite 1 [hr', ha]; ring
      exact (mul_left_cancel₀ hc0.ne' this).symm
    have hrx : (r' * x : ℚ) ≠ 0 := by
      intro h0
      have : ((r' * x : ℚ) : ℝ) = 0 := by exact_mod_cast h0
      push_cast at this; rw [this] at h1; simp at h1
    apply hq
    refine ⟨1 / (r' * x), ?_⟩
    have : ((r' * x : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hrx
    push_cast at this ⊢
    rw [eq_div_iff this]
    linear_combination h1
  -- `s² (p² + q²) N = 2`.
  have hsN : s ^ 2 * ((p : ℚ) ^ 2 + (q : ℚ) ^ 2) * N = 2 := by
    rw [hxs, hzs] at hxz; linear_combination 2 * hxz
  -- `N` is even.
  have hEven : Even N := by
    by_contra hodd
    have hN : Odd N := Nat.not_even_iff_odd.mp hodd
    set g := s.num.natAbs
    set h := s.den
    have hgs : ((g : ℚ) / h) = s := by
      have h1 : (((g : ℤ) : ℚ)) = (s.num : ℚ) := by
        simp only [g, Int.natCast_natAbs, abs_of_pos (Rat.num_pos.mpr hs0)]
      rw [Int.cast_natCast] at h1
      rw [h1]; exact Rat.num_div_den s
    have hh0 : (h : ℚ) ≠ 0 := by exact_mod_cast s.den_pos.ne'
    have heq : g ^ 2 * (p ^ 2 + q ^ 2) * N = 2 * h ^ 2 := by
      have : ((g : ℚ)) ^ 2 * ((p : ℚ) ^ 2 + (q : ℚ) ^ 2) * N = 2 * (h : ℚ) ^ 2 := by
        rw [← hgs] at hsN; field_simp at hsN; linear_combination hsN
      exact_mod_cast this
    obtain ⟨hpo, hqo⟩ := odd_legs hN hcop s.reduced heq
    exact hodd (parity_even D hright hA hC hrat hpo hqo hratio hcirr hAC)
  -- `N/2 = (p t)² + (q t)²` with `t = 1 / ((p² + q²) s)`.
  obtain ⟨M, hM⟩ := hEven
  have hM2 : N / 2 = M := by omega
  set t : ℚ := 1 / (((p : ℚ) ^ 2 + (q : ℚ) ^ 2) * s)
  have hpq2 : (0 : ℚ) < (p : ℚ) ^ 2 + (q : ℚ) ^ 2 := by positivity
  have hK : (M : ℚ) * (s ^ 2 * ((p : ℚ) ^ 2 + (q : ℚ) ^ 2)) = 1 := by
    have : (N : ℚ) = 2 * M := by rw [hM]; push_cast; ring
    rw [this] at hsN; linear_combination hsN / 2
  have hs2 : s ^ 2 * ((p : ℚ) ^ 2 + (q : ℚ) ^ 2) ≠ 0 := by positivity
  have hMt : (M : ℚ) = (p * t) ^ 2 + (q * t) ^ 2 := by
    have : (p * t) ^ 2 + (q * t) ^ 2 = 1 / (s ^ 2 * ((p : ℚ) ^ 2 + (q : ℚ) ^ 2)) := by
      have := hpq2.ne'; have := hs0.ne'
      simp only [t]; field_simp
    rw [this, eq_div_iff hs2, hK]
  obtain ⟨u, v, huv⟩ := nat_sum_sq_of_rat hMt
  refine ⟨⟨M, hM⟩, ⟨u + v, ((u : ℤ) - v).natAbs, ?_⟩, ⟨u, v, by rw [hM2, huv]⟩⟩
  have : (N : ℤ) = ((u + v : ℕ) : ℤ) ^ 2 + (((u : ℤ) - v).natAbs : ℤ) ^ 2 := by
    rw [Int.natAbs_sq, hM, huv]; push_cast; ring
  exact_mod_cast this

/-- **Theorem `theorem:isosceles2`, with `lemma:baseangles` as a hypothesis** (the unconditional
version is `isosceles2`, in `Laczkovich/BaseAngles.lean`). Let the isosceles triangle `ABC` (base `AC`) be `N`-tiled by
a tile with angles `(α, β, π/2)`, and let its base angles be `β` or `α` (`lemma:baseangles`, from
Laczkovich's classification; a hypothesis here). Then

(i) `N` is a square and `α = β = π/4`, or
(ii) `N` is twice a square, or
(iii) `N = 6k²` and `β = π/6` or `α = π/6`, or
(iv) `N` is even, and `N` and `N/2` are sums of two squares. -/
theorem isosceles2_of_baseangles (hright : tileγ D = Real.pi / 2)
    (hbase : (∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D ∧
        ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D) ∨
      (∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D ∧
        ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)) :
    ((∃ m : ℕ, N = m ^ 2) ∧ tileα D = Real.pi / 4 ∧ tileβ D = Real.pi / 4) ∨
    (∃ m : ℕ, N = 2 * m ^ 2) ∨
    ((∃ k : ℕ, N = 6 * k ^ 2) ∧ (tileβ D = Real.pi / 6 ∨ tileα D = Real.pi / 6)) ∨
    (Even N ∧ (∃ x y : ℕ, N = x ^ 2 + y ^ 2) ∧ ∃ x y : ℕ, N / 2 = x ^ 2 + y ^ 2) := by
  rcases hbase with ⟨hA, hC⟩ | ⟨hA, hC⟩
  · exact isosceles2_beta D hright hA hC
  · obtain ⟨eα, eβ, eγ⟩ := swap_angles D
    have h := isosceles2_beta (relabelModel D (Equiv.swap 0 1)) (by rw [eγ]; exact hright)
      (by rw [eβ]; exact hA) (by rw [eβ]; exact hC)
    rw [eα, eβ] at h
    rcases h with ⟨h1, h2, h3⟩ | h | ⟨h1, h2⟩ | h
    · exact Or.inl ⟨h1, h3, h2⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2.symm⟩))
    · exact Or.inr (Or.inr (Or.inr h))

end TriangleTiling
