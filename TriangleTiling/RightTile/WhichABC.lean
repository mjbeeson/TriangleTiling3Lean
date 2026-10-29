/-
`theorem:whichABC` (Section 6 of M. Beeson, *Tilings of an isosceles triangle*): the necessary
conditions.

The theorem lists which isosceles triangles can be `N`-tiled by a right-angled tile. Its "can be
tiled" halves need explicit tilings (quadratic and biquadratic), which are not formalized here.
This file proves the "only if" halves:

* (ii): if `N/2` is a sum of two squares but not a square, and `ABC` with base angles `β` is
  `N`-tiled by `(α, β, π/2)`, then `tan β = r/p` with `N/2 = r² + p²` (`whichABC_ii`);
* (iv): if `N = 6k²` (`k > 0`), the tile is the 30-60-90 triangle, and `ABC` has base angles
  `π/6`, or is equilateral (`whichABC_iv`; the paper omits the equilateral case);
* (v): every `N`-tiling falls under one of the cases (`whichABC_v`).
-/
import TriangleTiling.RightTile.NotPrime

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

/-! ### Arithmetic -/

/-- `c m²` with `v₃(c) = 1` and `m > 0` is not a sum of two squares. -/
theorem not_sum_sq_of_val3 {c m : ℕ} (hc0 : 0 < c) (hc : padicValNat 3 c = 1) (hm : 0 < m) :
    ¬ ∃ x y : ℕ, c * m ^ 2 = x ^ 2 + y ^ 2 := by
  intro h
  have key := Nat.eq_sq_add_sq_iff.mp (by obtain ⟨x, y, hxy⟩ := h; exact ⟨x, y, hxy⟩)
  haveI := Fact.mk Nat.prime_three
  have h3 : 3 ∈ (c * m ^ 2).primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨Nat.prime_three, ?_, by positivity⟩
    have : 3 ∣ c := by
      by_contra hn
      rw [padicValNat.eq_zero_of_not_dvd hn] at hc; omega
    exact dvd_mul_of_dvd_left this _
  have hev := key 3 h3 (by norm_num)
  rw [padicValNat.mul (by omega) (by positivity), padicValNat.pow _ (by omega), hc] at hev
  obtain ⟨k, hk⟩ := hev
  omega

/-- The divisibility step of `whichABC` (ii): if `(p² + q²) N = 2 K²` and `(p² + q²) u = 2 p K`
with `p, q` coprime and `N` even, then `p² + q²` divides `K`. -/
theorem w_dvd_K {p q K u N : ℕ} (hpq : Nat.Coprime p q) (hN : Even N)
    (hK : (p ^ 2 + q ^ 2) * N = 2 * K ^ 2) (hu : (p ^ 2 + q ^ 2) * u = 2 * p * K) :
    (p ^ 2 + q ^ 2) ∣ K := by
  set w := p ^ 2 + q ^ 2 with hw
  have hcop : Nat.Coprime w p := by
    have : Nat.Coprime p (q ^ 2) := hpq.pow_right 2
    rw [hw, show p ^ 2 + q ^ 2 = q ^ 2 + p * p by ring]
    exact (Nat.coprime_add_mul_right_left _ _ _).mpr this.symm
  have h2K : w ∣ 2 * K := by
    have : w ∣ p * (2 * K) := ⟨u, by rw [hu]; ring⟩
    exact hcop.dvd_of_dvd_mul_left this
  obtain ⟨m, hm⟩ := h2K
  rcases Nat.even_or_odd m with ⟨j, rfl⟩ | hmo
  · have : 2 * K = 2 * (w * j) := by rw [hm]; ring
    exact ⟨j, by omega⟩
  · exfalso
    -- `w m = 2K` with `m` odd: `w = 2 w'` with `w'` odd, and then `N = w' m²` is odd.
    have hwe : Even w := by
      have : Even (w * m) := ⟨K, by omega⟩
      rcases Nat.even_mul.mp this with h | h
      · exact h
      · exact absurd h (Nat.not_even_iff_odd.mpr hmo)
    have hpo : Odd p ∧ Odd q := by
      rw [hw, Nat.even_add, Nat.even_pow' two_ne_zero, Nat.even_pow' two_ne_zero] at hwe
      by_contra hn
      have hpe : Even p := by
        by_contra hp
        exact hn ⟨Nat.not_even_iff_odd.mp hp,
          Nat.not_even_iff_odd.mp fun hq => hp (hwe.mpr hq)⟩
      have h2 : 2 ∣ Nat.gcd p q :=
        Nat.dvd_gcd (even_iff_two_dvd.mp hpe) (even_iff_two_dvd.mp (hwe.mp hpe))
      rw [hpq] at h2; exact absurd h2 (by norm_num)
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hpo
    obtain ⟨w', hw'⟩ : ∃ w', w = 2 * (2 * w' + 1) := ⟨a ^ 2 + a + b ^ 2 + b, by rw [hw]; ring⟩
    obtain ⟨i, rfl⟩ := hmo
    have hK' : K = (2 * w' + 1) * (2 * i + 1) := by rw [hw'] at hm; linarith
    rw [hw', hK'] at hK
    have : N = (2 * w' + 1) * (2 * i + 1) ^ 2 := by
      have h0 : 0 < 2 * (2 * w' + 1) := by omega
      apply Nat.eq_of_mul_eq_mul_left h0
      linear_combination hK
    rw [this] at hN
    exact (Nat.not_even_iff_odd.mpr (by
      exact Odd.mul (by exact ⟨w', rfl⟩) (Odd.pow ⟨i, rfl⟩))) hN

variable {N : ℕ} (D : CongruentDissection N)

open Classical in
/-- **`theorem:whichABC` (ii), "only if".** Let `N/2 = x² + y²` but `N/2` not a square, and let
`ABC` with base angles `β` be `N`-tiled by `(α, β, π/2)`. Then `tan β = b/a = r/p` with
`N/2 = r² + p²`. -/
theorem whichABC_ii (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D)
    (hsum : ∃ x y : ℕ, N = 2 * (x ^ 2 + y ^ 2)) (hns : ¬ ∃ m : ℕ, N = 2 * m ^ 2) :
    ∃ r p : ℕ, 0 < p ∧ N = 2 * (r ^ 2 + p ^ 2) ∧
      dist (D.model.pts 2) (D.model.pts 0) * p = dist (D.model.pts 1) (D.model.pts 2) * r := by
  have hβ := right_beta D hright
  obtain ⟨hab, hbc⟩ := right_trig D hright
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact absurd ⟨0, by rw [h]; ring⟩ hns
    · exact h
  obtain ⟨x0, y0, hxy0⟩ := hsum
  by_cases hrat : ∃ r : ℚ, tileα D = r * Real.pi
  · rcases rationalisosceles D hright hA hC hrat with h | ⟨⟨m, hm⟩, hβ4⟩ | ⟨⟨m, hm⟩, -⟩
    · exact absurd h hns
    · -- `N = m²` and `β = π/4`: `m = 2k`, `N/2 = k² + k²`, and `a = b`.
      have h2 : 2 ∣ m := by
        have : 2 ∣ m * m := ⟨x0 ^ 2 + y0 ^ 2, by rw [← sq, ← hm, hxy0]⟩
        exact (Nat.Prime.dvd_mul Nat.prime_two).mp this |>.elim id id
      obtain ⟨k, rfl⟩ := h2
      have hk : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h] at hm; simp at hm; omega
        · exact h
      have hα4 : tileα D = Real.pi / 4 := by linarith
      refine ⟨k, k, hk, by rw [hm]; ring, ?_⟩
      rw [hab, hbc, hα4, hβ4]
    · -- `N = 6m²`: then `3m² = x² + y²`, impossible.
      exfalso
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h] at hm; omega
        · exact h
      exact not_sum_sq_of_val3 (c := 3) (m := m) (by norm_num) (by simp) hm0 ⟨x0, y0, by omega⟩
  -- `α ∉ ℚπ`: `λ` is irrational, and `isosceleshelper3` applies.
  have hq : ¬ ∃ q : ℚ, Real.sqrt ((N : ℝ) / 2) = q := fun h => hns (two_sq_of_sqrt_rat h)
  have hβk : ∀ k : ℕ, tileβ D ≠ Real.pi / k := fun k h =>
    hrat ⟨1 / 2 - 1 / k, by
      push_cast
      rw [show ((1 : ℝ) / 2 - 1 / k) * Real.pi = Real.pi / 2 - Real.pi / k by ring, ← h]
      linarith⟩
  obtain ⟨⟨x, z, hx, hz⟩, hAC, hAB⟩ := isosceleshelper3 D hright hA hC
    (by exact_mod_cast hβk 6) (by exact_mod_cast hβk 4) (by exact_mod_cast hβk 3) hq
  have hsep := anglesSep_right D hright hrat
  have hα0 := tileα_pos D
  have hβ0 := tileβ_pos D
  have hαγ : tileα D ≠ tileγ D := by rw [hright]; linarith
  have hβγ : tileβ D ≠ tileγ D := by rw [hright]; linarith
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
  have hxzR : ((x : ℝ) ^ 2 + (z : ℝ) ^ 2) * ((N : ℝ) / 2) = 1 := by
    have hp := right_pyth D hright
    rw [← hl2]
    have : (a / c) ^ 2 + (b / c) ^ 2 = 1 := by field_simp; linarith
    rw [hx, hz] at this
    linear_combination this
  -- `a : b = p : q` in lowest terms.
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
  have ha : a = c * (p * s * l) := by
    have := hx; rw [hxs] at this; push_cast at this; rw [← this]; field_simp
  have hb : b = c * (q * s * l) := by
    have := hz; rw [hzs] at this; push_cast at this; rw [← this]; field_simp
  -- The area equation: `|AB| = λ c`, `|AC| = 2 a λ`.
  obtain ⟨-, hcY, hNe⟩ := right_area_core D rfl rfl rfl rfl rfl hright hA hC
  have hXl : dist (D.target.pts 0) (D.target.pts 1) = l * c := by
    have h1 : dist (D.target.pts 0) (D.target.pts 1) ^ 2 = (l * c) ^ 2 := by
      rw [mul_pow, hl2]; linarith
    exact (pow_left_inj₀ dist_nonneg (by positivity) two_ne_zero).mp h1
  have hYl : dist (D.target.pts 2) (D.target.pts 0) = 2 * a * l := by
    have : c * dist (D.target.pts 2) (D.target.pts 0) = c * (2 * a * l) := by rw [hcY, hXl]; ring
    exact mul_left_cancel₀ hc0.ne' this
  -- `AB` has no `c` edges: `|AB| = nₐ a + n_b b`, so `s K = 1` with `K = nₐ p + n_b q`.
  obtain ⟨part0, hcov0, hs0'⟩ := typed_side D hsep 0
  obtain ⟨part2, hcov2, hs2'⟩ := typed_side D hsep 2
  have i01 : (0 : Fin 3) + 1 = 1 := rfl
  have i20 : (2 : Fin 3) + 1 = 0 := rfl
  rw [i01] at hcov0 hs0'
  rw [i20] at hcov2 hs2'
  have hsub : ∀ {P Q : Plane} {part : Finset (Fin N × Fin 3)},
      (⋃ e ∈ part, (D.tile e.1).edge e.2) = segment ℝ P Q →
        ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ P Q := by
    intro P Q part hcov e he y hy; rw [← hcov]; exact Set.mem_iUnion₂.mpr ⟨e, he, hy⟩
  have hγ0 : (part0.filter (edgeType D (tileγ D))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun e he => hAB e (Or.inl (hsub hcov0 e he))
  have hzero : ∀ φ, φ ≠ tileγ D → (part2.filter (edgeType D φ)).card = 0 := by
    intro φ hφ
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun e he hφe => hφ (hφe.symm.trans (hAC e (hsub hcov2 e he)))
  rw [hγ0, Nat.cast_zero, zero_mul, add_zero, hXl] at hs0'
  rw [hzero _ hαγ, hzero _ hβγ, Nat.cast_zero, zero_mul, zero_mul, zero_add, zero_add, hYl] at hs2'
  set na := (part0.filter (edgeType D (tileα D))).card
  set nb := (part0.filter (edgeType D (tileβ D))).card
  set u := (part2.filter (edgeType D (tileγ D))).card
  set K := na * p + nb * q
  have hsK : s * K = 1 := by
    have h1 : l * c = (na : ℝ) * a + nb * b := hs0'
    rw [ha, hb] at h1
    have h2 : c * l * (1 - s * K) = 0 := by
      simp only [K]; push_cast; linear_combination h1
    have := (mul_eq_zero.mp h2).resolve_left (by positivity)
    have : ((s * K : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by push_cast; linarith
    exact Rat.cast_injective this
  have hK0 : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h] at hsK; simp at hsK
    · exact h
  -- `|AC| = u c`, so `u K = p N`; and `(p² + q²) N = 2 K²`.
  have huN : (u : ℚ) * K = p * N := by
    have h1 : 2 * a * l = (u : ℝ) * c := hs2'
    rw [ha] at h1
    have h2 : c * ((u : ℝ) - 2 * p * s * l ^ 2) = 0 := by linear_combination -h1
    have h3 := (mul_eq_zero.mp h2).resolve_left hc0.ne'
    rw [hl2] at h3
    have h4 : ((u : ℚ) : ℝ) = ((p * s * N : ℚ) : ℝ) := by push_cast; linarith
    have h5 := Rat.cast_injective h4
    rw [h5]
    linear_combination (p : ℚ) * N * hsK
  have hwN : ((p : ℚ) ^ 2 + (q : ℚ) ^ 2) * N = 2 * (K : ℚ) ^ 2 := by
    have hxz : (x ^ 2 + z ^ 2) * ((N : ℚ) / 2) = 1 := by
      have : (((x ^ 2 + z ^ 2) * ((N : ℚ) / 2) : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
        push_cast; exact hxzR
      exact Rat.cast_injective this
    rw [hxs, hzs] at hxz
    linear_combination 2 * (K : ℚ) ^ 2 * hxz - ((p : ℚ) ^ 2 + (q : ℚ) ^ 2) * N * (s * K + 1) * hsK
  have hK' : (p ^ 2 + q ^ 2) * N = 2 * K ^ 2 := by exact_mod_cast hwN
  have hu' : (p ^ 2 + q ^ 2) * u = 2 * p * K := by
    have hK0' : (K : ℚ) ≠ 0 := by exact_mod_cast hK0.ne'
    have : ((p : ℚ) ^ 2 + (q : ℚ) ^ 2) * u = 2 * p * K := by
      apply mul_right_cancel₀ hK0'
      linear_combination ((p : ℚ) ^ 2 + (q : ℚ) ^ 2) * huN + (p : ℚ) * hwN
    exact_mod_cast this
  have hNe' : Even N := ⟨x0 ^ 2 + y0 ^ 2, by omega⟩
  obtain ⟨t, ht⟩ := w_dvd_K hcop hNe' hK' hu'
  have hw0 : 0 < p ^ 2 + q ^ 2 := by positivity
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h] at ht; omega
    · exact h
  refine ⟨t * q, t * p, Nat.mul_pos ht0 hp0, ?_, ?_⟩
  · rw [ht] at hK'
    apply Nat.eq_of_mul_eq_mul_left hw0
    linear_combination hK'
  · rw [ha, hb]; push_cast; ring

/-- **`theorem:whichABC` (iv), "only if", with `lemma:baseangles` as a hypothesis** (unconditional:
`whichABC_iv`, in `Laczkovich/BaseAngles.lean`). If `N = 6k²` with `k > 0` and `ABC` (base angles `β` or
`α`) is `N`-tiled by a right triangle, then the tile is the 30-60-90 triangle and `ABC` has base
angles `π/6` or is equilateral. -/
theorem whichABC_iv_of_baseangles (hright : tileγ D = Real.pi / 2)
    (hbase : (∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D ∧
        ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D) ∨
      (∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D ∧
        ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D))
    {k : ℕ} (hk : 0 < k) (hN : N = 6 * k ^ 2) :
    (tileβ D = Real.pi / 6 ∧ tileα D = Real.pi / 3) ∨
      (tileβ D = Real.pi / 3 ∧ tileα D = Real.pi / 6) := by
  have hβ := right_beta D hright
  have h6 : padicValNat 3 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 by rfl]
    haveI := Fact.mk Nat.prime_three
    rw [padicValNat.mul (by norm_num) (by norm_num)]; simp
  rcases isosceles2_of_baseangles D hright hbase with ⟨⟨m, hm⟩, -⟩ | ⟨m, hm⟩ | ⟨-, h⟩ | ⟨-, ⟨x, y, hxy⟩, -⟩
  · -- `6k² = m²`: impossible.
    exfalso
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h] at hm; rw [hm] at hN; simp at hN; omega
      · exact h
    exact not_sum_sq_of_val3 (c := 6) (by norm_num) h6 hk ⟨m, 0, by rw [← hN, hm]; ring⟩
  · -- `6k² = 2m²`: `m² = 3k²`, impossible.
    exfalso
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h] at hm; rw [hm] at hN; simp at hN; omega
      · exact h
    exact not_sum_sq_of_val3 (c := 3) (by norm_num) (by simp) hk ⟨m, 0, by omega⟩
  · rcases h with h | h
    · exact Or.inl ⟨h, by linarith⟩
    · exact Or.inr ⟨by linarith, h⟩
  · exfalso
    exact not_sum_sq_of_val3 (c := 6) (by norm_num) h6 hk ⟨x, y, by rw [← hN, hxy]⟩

/-- **`theorem:whichABC` (v), with `lemma:baseangles` as a hypothesis** (unconditional:
`whichABC_v`, in `Laczkovich/BaseAngles.lean`). Every `N`-tiling of an isosceles triangle by a right triangle falls
under one of the cases (i)–(iv): `N/2` is a square, `N/2` is a sum of two squares, `N` is a square
(with the right isosceles `ABC`), or `N` is six times a square. -/
theorem whichABC_v_of_baseangles (hright : tileγ D = Real.pi / 2)
    (hbase : (∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D ∧
        ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D) ∨
      (∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D ∧
        ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)) :
    (∃ m : ℕ, N = 2 * m ^ 2) ∨ (∃ x y : ℕ, N = 2 * (x ^ 2 + y ^ 2)) ∨
      ((∃ m : ℕ, N = m ^ 2) ∧ tileα D = Real.pi / 4 ∧ tileβ D = Real.pi / 4) ∨
      ∃ k : ℕ, N = 6 * k ^ 2 := by
  rcases isosceles2_of_baseangles D hright hbase with h | h | ⟨h, -⟩ | ⟨⟨M, hM⟩, -, x, y, hxy⟩
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inl ⟨x, y, by omega⟩)

end TriangleTiling
