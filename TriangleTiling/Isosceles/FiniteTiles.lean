/-
`theorem:finitetiles`, from the subsection "N determines a finite set of tiles and ABC" of
M. Beeson, *Tilings of an isosceles triangle* (it replaced `lemma:abcbound` and the subsection with
`lemma:N/4` in the rewrite of October 2026): given `N`, an `N`-tiling of the isosceles triangle `ABC` with base
angles `α ∉ ℚπ` by a tile `(α, β, 2α)` has, after scaling, the tile `(k², m² - k², km)` and the
triangle with sides `ks, ks, ms` (`s² = N (m² - k²)`), for a pair `(k, m)` in the finite set
`tilePairs N` (the set `T_N` of the draft).

Conventions as in `TriangleTiling.Isosceles.AreaEquation`.
-/
import TriangleTiling.Isosceles.N45
import TriangleTiling.Isosceles.Scaling

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

/-- The set `T_N`: pairs `(k, m)` with `2 ≤ k < m < 2k`, `gcd(k, m) = 1`, `m ≤ N + N²`, and
`N (m² - k²)` a perfect square. -/
def tilePairs (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 2 (N + N ^ 2) ×ˢ Finset.Icc 2 (N + N ^ 2)).filter fun km =>
    km.1 < km.2 ∧ km.2 < 2 * km.1 ∧ Nat.Coprime km.1 km.2 ∧
      IsSquare (N * (km.2 ^ 2 - km.1 ^ 2))

/-- **The arithmetic of `theorem:finitetiles`.** For the tile `(k², m² - k², km)` and a side
relation `X = p k² + q (m² - k²) + r km` with `p + q + r ≤ N`, `X > 0`, and
`X² = N k² (m² - k²)`: `m` divides `N + (p - q)²`, so `m ≤ N + N²`. -/
theorem finitetiles_arith (N k m p q r X : ℕ) (hkm : k < m) (hcop : Nat.Coprime k m)
    (hX : X = p * k ^ 2 + q * (m ^ 2 - k ^ 2) + r * (k * m))
    (hX2 : X ^ 2 = N * k ^ 2 * (m ^ 2 - k ^ 2)) (hpqr : p + q + r ≤ N) (hX0 : 0 < X) :
    m ≤ N + N ^ 2 := by
  have hk2m2 : k ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hkm.le 2
  have hXz : (X : ℤ) = p * k ^ 2 + q * ((m : ℤ) ^ 2 - k ^ 2) + r * (k * m) := by
    rw [hX]; push_cast [Nat.cast_sub hk2m2]; ring
  have hX2z : (X : ℤ) ^ 2 = N * k ^ 2 * ((m : ℤ) ^ 2 - k ^ 2) := by
    rw [← Nat.cast_pow, hX2]; push_cast [Nat.cast_sub hk2m2]; ring
  set d : ℤ := (p : ℤ) - q with hd
  have h1 : (m : ℤ) ∣ X - d * k ^ 2 := ⟨q * m + r * k, by rw [hXz, hd]; ring⟩
  have h2 : (m : ℤ) ∣ (X : ℤ) ^ 2 - d ^ 2 * k ^ 4 := by
    rw [show (X : ℤ) ^ 2 - d ^ 2 * k ^ 4 = (X - d * k ^ 2) * (X + d * k ^ 2) by ring]
    exact dvd_mul_of_dvd_left h1 _
  have h3 : (m : ℤ) ∣ (N + d ^ 2) * (k : ℤ) ^ 4 := by
    rw [show (N + d ^ 2) * (k : ℤ) ^ 4 = m * (N * k ^ 2 * m) - ((X : ℤ) ^ 2 - d ^ 2 * k ^ 4) by
      rw [hX2z]; ring]
    exact dvd_sub (dvd_mul_right _ _) h2
  have hcopz : IsCoprime (m : ℤ) ((k : ℤ) ^ 4) :=
    (Nat.isCoprime_iff_coprime.mpr hcop.symm).pow_right
  have h4 : (m : ℤ) ∣ N + d ^ 2 := hcopz.dvd_of_dvd_mul_right h3
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h] at hX2; simp at hX2; omega
    · exact h
  have h5 : (m : ℤ) ≤ N + d ^ 2 := Int.le_of_dvd (by positivity) h4
  have h6 : d ^ 2 ≤ (N : ℤ) ^ 2 := by
    have hpq : (p : ℤ) + q ≤ N := by exact_mod_cast (show p + q ≤ N by omega)
    have hp : (0 : ℤ) ≤ p := by positivity
    have hq : (0 : ℤ) ≤ q := by positivity
    rw [hd]; nlinarith
  have : (m : ℤ) ≤ N + N ^ 2 := by linarith
  exact_mod_cast this

/-- A triangle has at most one edge on a side of the target, so the edges on a side belong to
distinct tiles: at most `N` of them. -/
theorem side_part_card_le {N : ℕ} (D : CongruentDissection N) {A B : Plane}
    (part : Finset (Fin N × Fin 3))
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) = segment ℝ A B) :
    part.card ≤ N := by
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ A B := by
    intro e he x hx
    rw [← hcov]
    exact Set.mem_biUnion he hx
  have hinj : Set.InjOn Prod.fst (part : Set (Fin N × Fin 3)) := by
    intro e he e' he' h
    by_contra hne
    have h2 : e.2 ≠ e'.2 := fun h2 => hne (Prod.ext h h2)
    have hs' := hsub e' he'
    rw [← h] at hs'
    exact tri_two_edges_on_segment (D.tile e.1) h2 (hsub e he) hs'
  calc part.card = (part.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ _
    _ = N := Finset.card_fin N

/-- **Theorem `theorem:finitetiles`, for a tile with integer sides** (the general form is
`finitetiles`). -/
theorem finitetiles_int {N : ℕ} (D : CongruentDissection N) {a b c : ℕ}
    (ha : dist (D.model.pts 1) (D.model.pts 2) = a)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = b)
    (hc : dist (D.model.pts 0) (D.model.pts 1) = c)
    (hcop : Nat.gcd (Nat.gcd a b) c = 1) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D) :
    ∃ km ∈ tilePairs N, ∃ s : ℕ, s ^ 2 = N * (km.2 ^ 2 - km.1 ^ 2) ∧
      a = km.1 ^ 2 ∧ b = km.2 ^ 2 - km.1 ^ 2 ∧ c = km.1 * km.2 ∧
      dist (D.target.pts 0) (D.target.pts 1) = km.1 * s ∧
      dist (D.target.pts 1) (D.target.pts 2) = km.1 * s ∧
      dist (D.target.pts 0) (D.target.pts 2) = km.2 * s := by
  classical
  obtain ⟨part, hcov, -, hsum⟩ := D.toDissection.side_walk 0
  have h01 : (0 : Fin 3) + 1 = 1 := rfl
  rw [h01] at hcov hsum
  obtain ⟨hBC, hY, hX2⟩ := areaequation_core D ha hb hc rfl rfl hγ hA hC
  have hw := side_walk_counts D hγ hirr part _ hsum
  rw [ha, hb, hc] at hw
  set p := (part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
    = tileα D).card with hp
  set q := (part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
    = tileβ D).card with hq
  set r := (part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
    = tileγ D).card with hr
  -- `p + q + r ≤ N`: the three filters are disjoint, and the edges are on distinct tiles.
  have hpqr : p + q + r ≤ N := by
    obtain ⟨-, hinj⟩ := anglesSep_of_two_alpha D hγ hirr
    have hαβ : tileα D ≠ tileβ D := hinj.ne (show (0 : Fin 5) ≠ 1 by decide)
    have hαγ : tileα D ≠ tileγ D := hinj.ne (show (0 : Fin 5) ≠ 2 by decide)
    have hβγ : tileβ D ≠ tileγ D := hinj.ne (show (1 : Fin 5) ≠ 2 by decide)
    have hsum3 : p + q + r = ∑ e ∈ part,
        ((if (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileα D then 1 else 0) +
          (if (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileβ D then 1 else 0) +
          (if (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileγ D then 1 else 0)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hp, hq, hr, Finset.card_filter,
        Finset.card_filter, Finset.card_filter]
    have hle : ∑ e ∈ part,
        ((if (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileα D then 1 else 0) +
          (if (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileβ D then 1 else 0) +
          (if (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileγ D then 1 else 0))
        ≤ part.card * 1 := by
      apply Finset.sum_le_card_nsmul
      intro e _
      split_ifs with h1 h2 h3 h3 h2 h3 h3 <;> simp_all
    have := side_part_card_le D part hcov
    omega
  -- The tile `(k², m² - k², km)`.
  have hcab : c ^ 2 = a ^ 2 + a * b := by
    have := (twoalphatiles (tri_indep D.model) ha hb hc).mp hγ
    exact_mod_cast this
  obtain ⟨n1, n2, n3⟩ := strict_triangle_ineqs (tri_indep D.model)
  rw [ha, hb, hc] at n1 n2 n3
  have n1' : a < b + c := by exact_mod_cast n1
  have n2' : b < c + a := by exact_mod_cast n2
  have n3' : c < a + b := by exact_mod_cast n3
  obtain ⟨k, m, hkm_cop, hkm, hm2k, hak, hbk, hck⟩ :=
    (luthar a b c).mp ⟨hcop, hcab, n1', by omega, n3'⟩
  have hk0 : 0 < k := by omega
  -- `|AB|` is the integer `p a + q b + r c`.
  set Xn := p * a + q * b + r * c with hXn
  have hXr : dist (D.target.pts 0) (D.target.pts 1) = (Xn : ℝ) := by
    rw [hw, hXn]; push_cast; ring
  have hX0 : 0 < Xn := by
    have : (0 : ℝ) < Xn := by
      rw [← hXr]; exact dist_pos.mpr fun e => absurd (D.target.indep.injective e) (by decide)
    exact_mod_cast this
  rw [hXr] at hX2
  have hX2n : Xn ^ 2 = N * a * b := by exact_mod_cast hX2
  rw [hak, hbk, hck] at hXn
  rw [hak, hbk] at hX2n
  have hm := finitetiles_arith N k m p q r Xn hkm hkm_cop hXn (by rw [hX2n]) hpqr hX0
  -- `X = k s` with `s² = N (m² - k²)`.
  have hkX : k ∣ Xn := (Nat.pow_dvd_pow_iff two_ne_zero).mp ⟨N * (m ^ 2 - k ^ 2), by
    rw [hX2n]; ring⟩
  obtain ⟨s, hs⟩ := hkX
  have hs2 : s ^ 2 = N * (m ^ 2 - k ^ 2) := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < k ^ 2 by positivity)
    calc k ^ 2 * s ^ 2 = Xn ^ 2 := by rw [hs]; ring
      _ = k ^ 2 * (N * (m ^ 2 - k ^ 2)) := by rw [hX2n]; ring
  have hXks : dist (D.target.pts 0) (D.target.pts 1) = k * s := by
    rw [hXr, hs]; push_cast; ring
  refine ⟨(k, m), ?_, s, hs2, hak, hbk, hck, hXks, hBC.trans hXks, ?_⟩
  · simp only [tilePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, hm⟩⟩, hkm, hm2k, hkm_cop, ⟨s, by rw [← hs2]; ring⟩⟩
  · -- `a |AC| = c |AB|`, i.e. `k² Y = k m · k s`.
    rw [hXks, hak, hck] at hY
    rw [dist_comm]
    have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    push_cast at hY
    apply mul_left_cancel₀ hk2.ne'
    linear_combination hY

/-- **Theorem `theorem:finitetiles`.** Let the isosceles triangle `ABC` with base angles `α`
(`α` not a rational multiple of `π`) be `N`-tiled by a triangle with angles `(α, β, 2α)`. Then
there is a pair `(k, m) ∈ T_N` (`tilePairs N`) such that, after scaling, the tile has sides
`a = k²`, `b = m² - k²`, `c = km` (opposite `α`, `β`, `2α`) and `ABC` has sides
`|AB| = |BC| = ks`, `|AC| = ms`, where `s² = N (m² - k²)`. -/
theorem finitetiles {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D) :
    ∃ km ∈ tilePairs N, ∃ (κ : ℝ) (hκ : κ ≠ 0) (s : ℕ), s ^ 2 = N * (km.2 ^ 2 - km.1 ^ 2) ∧
      dist ((CongruentDissection.scale D κ hκ).model.pts 1)
        ((CongruentDissection.scale D κ hκ).model.pts 2) = ((km.1 ^ 2 : ℕ) : ℝ) ∧
      dist ((CongruentDissection.scale D κ hκ).model.pts 2)
        ((CongruentDissection.scale D κ hκ).model.pts 0) = ((km.2 ^ 2 - km.1 ^ 2 : ℕ) : ℝ) ∧
      dist ((CongruentDissection.scale D κ hκ).model.pts 0)
        ((CongruentDissection.scale D κ hκ).model.pts 1) = ((km.1 * km.2 : ℕ) : ℝ) ∧
      dist ((CongruentDissection.scale D κ hκ).target.pts 0)
        ((CongruentDissection.scale D κ hκ).target.pts 1) = km.1 * s ∧
      dist ((CongruentDissection.scale D κ hκ).target.pts 1)
        ((CongruentDissection.scale D κ hκ).target.pts 2) = km.1 * s ∧
      dist ((CongruentDissection.scale D κ hκ).target.pts 0)
        ((CongruentDissection.scale D κ hκ).target.pts 2) = km.2 * s := by
  obtain ⟨κ, hκ, a, b, c, ha, hb, hc, hcop⟩ := exists_int_scale D hγ hirr hA hC
  obtain ⟨hγ', hirr', hA', hC'⟩ := scale_hyps D hκ hγ hirr hA hC
  obtain ⟨km, hkm, s, hs, rfl, rfl, rfl, h1, h2, h3⟩ :=
    finitetiles_int _ ha hb hc hcop hγ' hirr' hA' hC'
  exact ⟨km, hkm, κ, hκ, s, hs, ha, hb, hc, h1, h2, h3⟩

end TriangleTiling

#print axioms TriangleTiling.finitetiles
